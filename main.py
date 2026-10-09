#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ربات چت ناشناس تلگرام — تک‌فایل، فقط کتابخانه‌های استاندارد پایتون (بدون pip)
اجرا در Termux:
    pkg install python -y
    python anon_chat_bot.py
بار اول توکن ربات و شناسه عددی مالک را می‌پرسد و در config.json ذخیره می‌کند.

ساختار فایل:
    1) تنظیمات و ابزارها     2) رمزنگاری   3) زمان تهران و تقویم شمسی
    4) دیتابیس و تنظیمات      5) فیلتر کلمات ممنوعه
    6) API تلگرام             7) منطق چت (اتصال/ارسال/پایان)
    8) پنل مدیریت مالک (+ سوئیچ به پنل کاربر)   9) کد Cloudflare Worker   10) حلقه‌ی اصلی
"""
import os, sys, re, json, time, uuid, base64, hmac, hashlib, secrets, sqlite3, threading, random
import urllib.request, urllib.error
from datetime import datetime, timezone, timedelta
from concurrent.futures import ThreadPoolExecutor

# ───────────────────────── 1) تنظیمات ─────────────────────────
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.environ.get("CONFIG_PATH", os.path.join(BASE_DIR, "config.json"))
DB_PATH = os.environ.get("DB_PATH", os.path.join(BASE_DIR, "anonchat.db"))
KEY_PATH = os.environ.get("KEY_PATH", os.path.join(BASE_DIR, "secret.key"))
WORKER_FILE = os.path.join(BASE_DIR, "worker.js")

BOT_TOKEN = ""
OWNER_ID = 0
CFG_WORKER = ""         # آدرس Worker از config.json یا متغیر WORKER_URL
LOCK = threading.RLock()
DB = None
WAITING = []            # صف انتظار چت تصادفی
ADMIN_STATE = {}        # وضعیت ورودی‌های پنل مالک
_user_locks = {}
_processed_updates = set()
_processed_updates_lock = threading.Lock()
_MAX_PROCESSED_UPDATES = 4096


def load_config():
    """توکن و شناسه مالک: متغیر محیطی ← config.json ← پرسش از کاربر."""
    token = os.environ.get("BOT_TOKEN", "")
    owner = os.environ.get("OWNER_ID", "")
    cfg = {}
    if os.path.exists(CONFIG_PATH):
        with open(CONFIG_PATH, encoding="utf-8") as f:
            cfg = json.load(f)
    token = token or cfg.get("token", "")
    owner = owner or str(cfg.get("owner", ""))
    if not token:
        token = input("توکن ربات (از BotFather): ").strip()
    if not owner.isdigit():
        owner = input("شناسه عددی مالک (از @userinfobot): ").strip()
    global CFG_WORKER
    CFG_WORKER = (os.environ.get("WORKER_URL") or cfg.get("worker_url") or "").strip().rstrip("/")
    cfg.update({"token": token, "owner": int(owner)})
    with open(CONFIG_PATH, "w", encoding="utf-8") as f:
        json.dump(cfg, f, ensure_ascii=False, indent=2)
    return token, int(owner)


# ───────────────────────── 2) رمزنگاری ─────────────────────────
# توجه: ربات واسطه‌ی پیام‌هاست و تلگرام برای ربات‌ها چت سرتاسری (Secret Chat) ندارد؛
# پس E2E واقعی ممکن نیست. اینجا شناسه‌ی طرف مقابل در دیتابیس رمز می‌شود
# (جریان خنثی + احراز یکپارچگی با HMAC) و هیچ متن پیامی ذخیره نمی‌شود.
def _load_key():
    if os.path.exists(KEY_PATH):
        with open(KEY_PATH, "rb") as f:
            return f.read()
    k = secrets.token_bytes(32)
    with open(KEY_PATH, "wb") as f:
        f.write(k)
    try:
        os.chmod(KEY_PATH, 0o600)
    except Exception:
        pass
    return k


_KEY = None


def _keys():
    global _KEY
    if _KEY is None:
        _KEY = _load_key()
    return hashlib.sha256(_KEY + b"enc").digest(), hashlib.sha256(_KEY + b"mac").digest()


def _stream(k, nonce, n):
    out, c = b"", 0
    while len(out) < n:
        out += hashlib.sha256(k + nonce + c.to_bytes(8, "big")).digest()
        c += 1
    return out[:n]


def seal(text):
    ek, mk = _keys()
    data = text.encode()
    nonce = secrets.token_bytes(12)
    ct = bytes(a ^ b for a, b in zip(data, _stream(ek, nonce, len(data))))
    tag = hmac.new(mk, nonce + ct, hashlib.sha256).digest()[:16]
    return base64.urlsafe_b64encode(nonce + tag + ct).decode()


def unseal(s):
    ek, mk = _keys()
    raw = base64.urlsafe_b64decode(s.encode())
    nonce, tag, ct = raw[:12], raw[12:28], raw[28:]
    if not hmac.compare_digest(tag, hmac.new(mk, nonce + ct, hashlib.sha256).digest()[:16]):
        raise ValueError("bad tag")
    return bytes(a ^ b for a, b in zip(ct, _stream(ek, nonce, len(ct)))).decode()


# ───────────────────────── 3) زمان تهران و شمسی ─────────────────────────
TEHRAN = timezone(timedelta(hours=3, minutes=30))   # ایران از ۱۴۰۱ ساعت تابستانی ندارد
J_MONTHS = ["فروردین", "اردیبهشت", "خرداد", "تیر", "مرداد", "شهریور",
            "مهر", "آبان", "آذر", "دی", "بهمن", "اسفند"]
J_DAYS = ["دوشنبه", "سه‌شنبه", "چهارشنبه", "پنجشنبه", "جمعه", "شنبه", "یکشنبه"]


def now():
    return datetime.now(TEHRAN)


def gregorian_to_jalali(gy, gm, gd):
    g_d_m = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    gy2 = gy + 1 if gm > 2 else gy
    days = 355666 + 365 * gy + (gy2 + 3) // 4 - (gy2 + 99) // 100 + (gy2 + 399) // 400 + gd + g_d_m[gm - 1]
    jy = -1595 + 33 * (days // 12053)
    days %= 12053
    jy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        jy += (days - 1) // 365
        days = (days - 1) % 365
    if days < 186:
        jm, jd = 1 + days // 31, 1 + days % 31
    else:
        jm, jd = 7 + (days - 186) // 30, 1 + (days - 186) % 30
    return jy, jm, jd


def jalali_str(dt=None):
    dt = dt or now()
    jy, jm, jd = gregorian_to_jalali(dt.year, dt.month, dt.day)
    return f"{J_DAYS[dt.weekday()]} {jd} {J_MONTHS[jm - 1]} {jy} — ساعت {dt:%H:%M}"


def _hm(s):
    h, m = s.split(":")
    return int(h) * 60 + int(m)


def valid_hm(s):
    return bool(re.fullmatch(r"([01]?\d|2[0-3]):[0-5]\d", s.strip()))


def in_window(start, end, dt=None):
    dt = dt or now()
    s, e, m = _hm(start), _hm(end), dt.hour * 60 + dt.minute
    if s == e:
        return True
    return s <= m < e if s < e else (m >= s or m < e)


# ───────────────────────── 4) دیتابیس و تنظیمات ─────────────────────────
# رنگ واقعی دکمه‌ها با فیلد رسمی «style» در Bot API تلگرام (نسخه 9.4 به بعد).
# تلگرام فقط این سه رنگ را پشتیبانی می‌کند: primary=آبی، success=سبز، danger=قرمز
# (none = رنگ پیش‌فرض اپ). روی نسخه‌های قدیمی اپ، دکمه بدون رنگ نمایش داده می‌شود.
STYLES = {"success": "سبز", "danger": "قرمز", "primary": "آبی", "none": "بی‌رنگ"}
STYLE_ORDER = list(STYLES)
_OLD_COLORS = {"green": "success", "red": "danger", "blue": "primary"}

DEFAULT_PRIVACY = """🔒 سیاست حفظ حریم خصوصی

• هویت شما برای طرف مقابل کاملاً ناشناس است؛ نام، نام‌کاربری و عکس شما نمایش داده نمی‌شود.
• متن و محتوای پیام‌ها در ربات ذخیره نمی‌شود؛ فقط از شما به طرف مقابل عبور می‌کند.
• شناسه‌ی طرف مقابل در دیتابیس به‌صورت رمزشده نگهداری می‌شود.
• توجه: این ربات چت سرتاسری (E2E) تلگرام نیست؛ پیام‌ها از سرور ربات عبور می‌کنند.
• برای حفظ امنیت، فحاشی به‌صورت خودکار شناسایی می‌شود و باعث اخطار و در صورت تکرار مسدودی می‌گردد.
• ممکن است پشتیبانی یا مدیریت ربات برای نظارت و پشتیبانی در گفتگوها حضور پیدا کند.
• اطلاعات شخصی (شماره، آدرس، رمز و...) را با غریبه‌ها به اشتراک نگذارید.

با استفاده از ربات، این شرایط را می‌پذیرید."""

DEFAULT_WELCOME = "👋 سلام {name}! به ربات چت ناشناس خوش آمدی.\nبا دکمه‌ی «جستجوی چت تصادفی» به یک نفر وصل شو."

DEFAULTS = {
    "bot_on": "1", "sched_on": "0", "sched_mode": "active",
    "sched_start": "08:00", "sched_end": "23:00",
    "max_warns": "3", "priv_show": "1", "priv_text": DEFAULT_PRIVACY,
    "welcome_text": DEFAULT_WELCOME, "owner_mode": "admin",
    "color_chat": "success", "color_next": "primary", "color_end": "danger", "color_priv": "primary",
    "worker_url": "", "worker_enabled": "0", "worker_auto_recover": "1",
}
_SETTINGS = {}
START_TIME = time.time()


def init_db():
    global DB
    DB = sqlite3.connect(DB_PATH, check_same_thread=False)
    DB.execute("PRAGMA journal_mode=WAL")
    DB.executescript("""
        CREATE TABLE IF NOT EXISTS users(uid INTEGER PRIMARY KEY, partner TEXT, warns INTEGER DEFAULT 0,
                                         banned INTEGER DEFAULT 0, joined TEXT, last_seen TEXT);
        CREATE TABLE IF NOT EXISTS settings(k TEXT PRIMARY KEY, v TEXT);
        CREATE TABLE IF NOT EXISTS words(id INTEGER PRIMARY KEY AUTOINCREMENT, word TEXT UNIQUE);
        CREATE TABLE IF NOT EXISTS counters(k TEXT PRIMARY KEY, v INTEGER DEFAULT 0);
    """)
    cols = {r[1] for r in DB.execute("PRAGMA table_info(users)")}
    if "last_seen" not in cols:                      # مهاجرت دیتابیس نسخه‌ی قبلی
        DB.execute("ALTER TABLE users ADD COLUMN last_seen TEXT")
    _SETTINGS.clear()
    _SETTINGS.update(DEFAULTS)
    for k, v in DB.execute("SELECT k,v FROM settings"):
        _SETTINGS[k] = v
    if DB.execute("SELECT COUNT(*) FROM words").fetchone()[0] == 0:
        for w in dict.fromkeys(x.strip() for x in BAD_WORDS_SEED.splitlines() if x.strip()):
            DB.execute("INSERT OR IGNORE INTO words(word) VALUES(?)", (w,))
    DB.commit()
    for k in ("color_chat", "color_next", "color_end", "color_priv"):   # تبدیل رنگ‌های ایموجی قدیمی
        if S(k) not in STYLES:
            set_S(k, _OLD_COLORS.get(S(k), DEFAULTS[k]))
    if not S("worker_url") and CFG_WORKER:
        set_S("worker_url", CFG_WORKER)
    set_S("owner_mode", "admin")                      # بعد از ری‌استارت همیشه پنل ادمین
    reload_words()


def S(k):
    return _SETTINGS.get(k, DEFAULTS.get(k, ""))


def set_S(k, v):
    with LOCK:
        _SETTINGS[k] = str(v)
        DB.execute("INSERT INTO settings(k,v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v", (k, str(v)))
        DB.commit()


def bump(k, n=1):
    with LOCK:
        DB.execute("INSERT INTO counters(k,v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=v+excluded.v", (k, n))
        DB.commit()


def get_user(uid, create=True):
    with LOCK:
        r = DB.execute("SELECT partner,warns,banned FROM users WHERE uid=?", (uid,)).fetchone()
        if not r:
            if not create:
                return None
            t = now().isoformat()
            DB.execute("INSERT INTO users(uid,partner,warns,banned,joined,last_seen) VALUES(?,?,?,?,?,?)",
                       (uid, None, 0, 0, t, t))
            DB.commit()
            return {"uid": uid, "partner": None, "warns": 0, "banned": 0}
        p = None
        if r[0]:
            try:
                p = int(unseal(r[0]))
            except Exception:
                p = None
        return {"uid": uid, "partner": p, "warns": r[1], "banned": r[2]}


_last_touch = {}


def touch(uid):
    """ثبت آخرین فعالیت (حداکثر هر ۶۰ ثانیه یک‌بار در دیتابیس)."""
    t = time.time()
    if t - _last_touch.get(uid, 0) < 60:
        return
    _last_touch[uid] = t
    get_user(uid)
    with LOCK:
        DB.execute("UPDATE users SET last_seen=? WHERE uid=?", (now().isoformat(), uid))
        DB.commit()


def set_partner(uid, pid):
    with LOCK:
        DB.execute("UPDATE users SET partner=? WHERE uid=?", (seal(str(pid)) if pid else None, uid))
        DB.commit()


def set_field(uid, field, val):
    assert field in ("warns", "banned")
    with LOCK:
        get_user(uid)
        DB.execute(f"UPDATE users SET {field}=? WHERE uid=?", (val, uid))
        DB.commit()


def user_lock(uid):
    with LOCK:
        return _user_locks.setdefault(uid, threading.Lock())


# ───────────────────────── 5) کلمات ممنوعه ─────────────────────────
BAD_WORDS_SEED = """
کیر
کیری
کیرم
کیرمو
کیرتو
کیر تو
کیر خر
کیر سگ
کیرشو
کیرخور
کیر خور
کص
کصکش
کسکش
کس کش
کسخل
کصخل
کس خل
کسشر
کصشر
کس شر
کس ننت
کص ننت
کس مادرت
کس مادر
کس ننه
کس خواهرت
کس خواهر
کس عمت
کس زنت
کس مامانت
کس مادرتو
کس ننتو
کس خارت
کس دهنت
کس کثافت
کسده
کصده
کس ده
خارکسه
خارکسده
خارکصده
خار کسته
خارکسته
خارکصه
کون
کونی
کونده
کون ده
کونکش
کون کش
کون گشاد
کونگشاد
کونت
کونتو
کون تو
کون خر
کون لق
جنده
جندع
جنده خانه
جنده زاده
جنده بازی
مادر جنده
مادرجنده
ننه جنده
ننه جندع
خواهر جنده
خواهرجنده
زن جنده
جاکش
جاکشی
جاکش بازی
جاکش مادر
قحبه
قحبه خانه
قحبه زاده
مادر قحبه
مادرقحبه
پدر قحبه
پدر سگ
پدرسگ
پدر سوخته
پدرسوخته
پدر جنده
پدر کثافت
حرومزاده
حرام زاده
حروم زاده
حرومی
حرومزادگی
حرام لقمه
توله سگ
تخم سگ
تخم حرام
ننه سگ
سگ پدر
سگ مادر
سگ ننه
مادر سگ
ننه کثافت
گایید
گاییدم
گاییدن
گاییدمت
گاییدیم
میگایم
می گایم
میگامت
می گامت
میگام
می گام
بگامت
بگام
بگایم
بگایمت
گاییده
گاییدی
جق
جقی
جق زدن
جق میزنی
جقول
جق زن
گوه
گوه نخور
گوه خوردی
گوهی
گه خوردی
گه نخور
گوز
گوزو
گوزی
خایه
خایه مال
خایمال
خایه مالی
خایه خور
خایه هات
بیناموس
بی ناموس
بی شرف
بی غیرت
دیوث
دیوس
دیوثی
بیشعور
بی شعور
بی پدر
بی مادر
بی پدر مادر
عوضی
عوضی ها
عوضی بازی
هرزه
فاحشه
روسپی
لاشی
لاشی بازی
لاشخور
پفیوز
پفیوزی
کثافت
کثافت کار
عنتر
اوسکول
اسکل
اسگل
احمق
کودن
نفهم
آشغال
زباله
عقده ای
رذل
فرومایه
پست فطرت
کله پوک
مادر تو
مادرتو
ننتو
خواهرتو
ناموستو
ناموست
زنتو
مادر خراب
مادرخراب
خواهر خراب
ننه خراب
fuck
fucker
fucking
motherfucker
mother fucker
shit
bullshit
bitch
bitches
asshole
bastard
dick
dickhead
pussy
cunt
whore
slut
wanker
douche
douchebag
dumbass
jackass
cock
cocksucker
kir
kiri
kire khar
kir khar
kos
kose
kos nanat
kose nanat
kosnanat
koskesh
kos kesh
kosekesh
kooni
kon khar
jende
jendeh
jakesh
jakesh bazi
madar jende
madar jendeh
madarjende
madar ghahbe
madar ghabe
madar kharab
pedar sag
pedarsag
pedar sookhte
haroomzade
haroomzadeh
harmzade
haram zade
gayidam
gaidam
gahyidam
goh nakhor
goh khordi
khayemal
khayeh mal
bi namoos
binamoos
bi sharaf
bi gheirat
divooth
diyus
divus
oskol
ashghal
lashi
lashikhor
harzeh
fahesheh
ghahbeh
ghahbe
ghahbeh khoone
kosdeh
kosde
kharkosde
khar kose
khar koseh
tokhm sag
toole sag
"""

_TR = str.maketrans({"ي": "ی", "ى": "ی", "ك": "ک", "ۀ": "ه", "ة": "ه", "أ": "ا", "إ": "ا",
                     "آ": "ا", "ؤ": "و", "ئ": "ی"})
_WORDS = []


def normalize(s):
    s = (s or "").translate(_TR).lower()
    s = re.sub(r"[\u064B-\u065F\u0670\u0640]", "", s)            # اعراب و کشیده
    s = re.sub(r"[\u200c\u200d\u200b\u200e\u200f]", " ", s)       # نیم‌فاصله
    s = s.replace("_", " ")
    s = re.sub(r"[^\w]+", " ", s)
    s = re.sub(r"(.)\1+", r"\1", s)                                # کییییر → کیر
    return s.strip()


def _join_singles(n):
    out, run = [], []
    for t in n.split():
        if len(t) == 1:
            run.append(t)
        else:
            if run:
                out.append("".join(run))
                run = []
            out.append(t)
    if run:
        out.append("".join(run))
    return " ".join(out)


def reload_words():
    with LOCK:
        rows = DB.execute("SELECT word FROM words").fetchall()
    _WORDS[:] = sorted({normalize(r[0]) for r in rows if normalize(r[0])})


def find_bad_word(text):
    n = normalize(text)
    if not n:
        return None
    for cand in {n, _join_singles(n)}:          # حالت «ک ی ر» هم گرفته می‌شود
        padded = f" {cand} "
        for w in _WORDS:
            if f" {w} " in padded:
                return w
    return None


# ───────────────────────── 6) API تلگرام ─────────────────────────
TG_DIRECT = "https://api.telegram.org"
UA = {"User-Agent": "Mozilla/5.0 (anonchat-bot)"}
POLL_LOCK = threading.Lock()
POLL_OFFSET = None
LAST_POLL_OK_AT = None
LAST_POLL_LATENCY_MS = None
_last_worker_probe = 0.0
_worker_failures = 0
_worker_probe_lock = threading.Lock()


def api_base():
    if S("worker_enabled") == "1" and (S("worker_url") or CFG_WORKER):
        return (S("worker_url") or CFG_WORKER).rstrip("/")
    return TG_DIRECT


def _post(url, data, headers, timeout):
    req = urllib.request.Request(url, data=data, headers={**UA, **headers})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.loads(r.read().decode())
    except urllib.error.HTTPError as e:
        body = e.read().decode(errors="replace")
        try:
            out = json.loads(body)
            out["_http_status"] = e.code
            out["_net"] = e.code >= 500
            return out
        except Exception:
            detail = body[:300].replace("\n", " ").strip()
            return {"ok": False, "description": detail or f"HTTP {e.code}", "_http_status": e.code,
                    "_net": e.code >= 500}
    except Exception as e:
        return {"ok": False, "description": str(e), "_net": True}


def api(method, params=None, timeout=35):
    """Worker-first with circuit breaker; avoid duplicate retries for writes."""
    global _worker_failures, _last_worker_probe
    data = json.dumps(params or {}).encode()
    hdr = {"Content-Type": "application/json"}
    base = api_base()
    recovery_wait = min(300, 30 * (2 ** min(_worker_failures, 3)))
    should_probe = False
    if base == TG_DIRECT and S("worker_auto_recover") == "1" and S("worker_url"):
        with _worker_probe_lock:
            if time.monotonic() - _last_worker_probe >= recovery_wait:
                _last_worker_probe = time.monotonic()
                should_probe = True
    if should_probe:
        healthy, _ = worker_probe(S("worker_url"))
        if healthy:
            set_S("worker_enabled", "1")
            _worker_failures = 0
            base = S("worker_url").rstrip("/")
            report_worker_state("☁️ Worker بازیابی شد؛ اتصال دوباره از Cloudflare انجام می‌شود.")
        else:
            _worker_failures = min(_worker_failures + 1, 4)
    r = _post(f"{base}/bot{BOT_TOKEN}/{method}", data, hdr, timeout)
    failed_worker = base != TG_DIRECT and (
        r.get("_net") or r.get("_http_status") in (403, 404, 429, 500, 502, 503, 504)
    )
    if failed_worker:
        _worker_failures += 1
        was_enabled = S("worker_enabled") == "1"
        set_S("worker_enabled", "0")
        if was_enabled:
            report_worker_state("⚠️ ارتباط با Cloudflare قطع شد؛ ربات به اتصال مستقیم برگشت. "
                                "پیام جاری در صورت خطای مبهم دوباره ارسال نمی‌شود.")
        safe_retry = method in {"getMe", "getUpdates", "deleteWebhook", "setMyCommands",
                                "getChat", "getChatMember", "getFile"}
        if safe_retry:
            r = _post(f"{TG_DIRECT}/bot{BOT_TOKEN}/{method}", data, hdr, timeout)
        with _worker_probe_lock:
            _last_worker_probe = time.monotonic()
    elif base != TG_DIRECT and r.get("ok"):
        _worker_failures = 0
    r.pop("_net", None)
    r.pop("_http_status", None)
    return r


def report_worker_state(message):
    """Best-effort owner notification sent directly, bypassing the failed Worker."""
    print(message, file=sys.stderr)
    if BOT_TOKEN and OWNER_ID:
        _post(f"{TG_DIRECT}/bot{BOT_TOKEN}/sendMessage",
              json.dumps({"chat_id": OWNER_ID, "text": message}).encode(),
              {"Content-Type": "application/json"}, 8)


def _strip_styles(kb):
    for key in ("inline_keyboard", "keyboard"):
        for row in kb.get(key, []):
            for b in row:
                if isinstance(b, dict):
                    b.pop("style", None)
    return kb


def _with_kb(method, p, kb):
    if kb:
        p["reply_markup"] = kb
    r = api(method, p)
    # اگر سرور/کلاینت style را نپذیرفت، همان پیام بدون رنگ ارسال می‌شود تا ربات از کار نیفتد
    if not r.get("ok") and kb and "style" in json.dumps(kb) and "markup" in str(r.get("description", "")).lower():
        p["reply_markup"] = _strip_styles(json.loads(json.dumps(kb)))
        r = api(method, p)
    return r


def send(chat, text, kb=None):
    return _with_kb("sendMessage", {"chat_id": chat, "text": text[:4096]}, kb)


def edit(chat, mid, text, kb=None):
    return _with_kb("editMessageText", {"chat_id": chat, "message_id": mid, "text": text[:4096]}, kb)


def send_document(chat, filename, content, caption=""):
    if isinstance(content, str):
        content = content.encode("utf-8")
    b = uuid.uuid4().hex
    body = b""
    for name, val in (("chat_id", str(chat)), ("caption", caption[:1024])):
        body += f'--{b}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{val}\r\n'.encode()
    body += (f'--{b}\r\nContent-Disposition: form-data; name="document"; filename="{filename}"\r\n'
             f'Content-Type: text/plain; charset=utf-8\r\n\r\n').encode() + content + f"\r\n--{b}--\r\n".encode()
    hdr = {"Content-Type": f"multipart/form-data; boundary={b}"}
    base = api_base()
    r = _post(f"{base}/bot{BOT_TOKEN}/sendDocument", body, hdr, 60)
    if r.get("_net") and base != TG_DIRECT:
        r = _post(f"{TG_DIRECT}/bot{BOT_TOKEN}/sendDocument", body, hdr, 60)
    r.pop("_net", None)
    return r


def btn(text, data, style=None):
    b = {"text": text, "callback_data": data}
    if style in ("primary", "success", "danger"):
        b["style"] = style
    return b


def ikb(rows):
    """هر دکمه: (متن، داده) یا (متن، داده، رنگ) — رنگ: primary / success / danger"""
    return {"inline_keyboard": [[btn(*x) for x in row] for row in rows if row]}


# ───────────────────────── 7) منطق چت ─────────────────────────
L_SEARCH, L_NEXT, L_END, L_PRIV = "جستجوی چت تصادفی", "چت بعدی", "پایان چت", "حریم خصوصی"
L_ADMIN = "بازگشت به پنل ادمین"
ICONS = {"chat": "🔍", "next": "⏭", "end": "🚪", "priv": "🔒"}
MSG_LEFT = "🚪 طرف مقابل چت را ترک کرد."
MSG_CONNECTED = "✅ به یک نفر ناشناس وصل شدی! سلام کن 👋\nبرای پایان: «پایان چت»"


def owner_is_user():
    return S("owner_mode") == "user"


def is_direct(a, b):
    """چت مستقیم مالک (از پنل ادمین)؛ در حالت تست کاربر عادی، مالک مثل بقیه رفتار می‌شود."""
    return OWNER_ID in (a, b) and not owner_is_user()


def kbtn(label, key):
    b = {"text": f"{ICONS[key]} {label}"}
    st = S("color_" + key)
    if st in ("primary", "success", "danger"):
        b["style"] = st
    return b


def main_kb(uid=None):
    rows = [[kbtn(L_SEARCH, "chat")], [kbtn(L_NEXT, "next"), kbtn(L_END, "end")]]
    if S("priv_show") == "1":
        rows.append([kbtn(L_PRIV, "priv")])
    if uid == OWNER_ID:
        rows.append([{"text": f"🛠 {L_ADMIN}", "style": "primary"}])
    return {"keyboard": rows, "resize_keyboard": True}


def is_active():
    if S("bot_on") != "1":
        return False
    if S("sched_on") == "1":
        inside = in_window(S("sched_start"), S("sched_end"))
        return inside if S("sched_mode") == "active" else not inside
    return True


def off_message():
    m = "⛔ ربات در حال حاضر خاموش است."
    if S("sched_on") == "1":
        kind = "فعال" if S("sched_mode") == "active" else "غیرفعال"
        m += f"\n🕒 بازه‌ی {kind} بودن: {S('sched_start')} تا {S('sched_end')} (به وقت تهران)"
    return m


def end_chat(uid, notify=True):
    """چت را قطع می‌کند و طرف مقابل را مطلع می‌سازد. شناسه‌ی طرف مقابل را برمی‌گرداند."""
    with LOCK:
        if uid in WAITING:
            WAITING.remove(uid)
        p = get_user(uid)["partner"]
        if not p:
            return None
        set_partner(uid, None)
        if get_user(p)["partner"] == uid:
            set_partner(p, None)
    if notify:
        if p == OWNER_ID and not owner_is_user():
            send(p, "🚪 کاربر (چت مستقیم) چت را ترک کرد.")
        else:
            send(p, MSG_LEFT, main_kb(p))
    return p


def search_partner(uid):
    with LOCK:
        if get_user(uid)["partner"]:
            return ("in_chat", None)
        if uid in WAITING:
            return ("waiting", None)
        cand = None
        while WAITING:
            c = WAITING.pop(0)
            cu = get_user(c)
            if c == OWNER_ID and not owner_is_user():
                continue
            if c != uid and not cu["banned"] and cu["partner"] is None:
                cand = c
                break
        if cand:
            set_partner(uid, cand)
            set_partner(cand, uid)
            return ("matched", cand)
        WAITING.append(uid)
        return ("queued", None)


def do_search(uid):
    bump("searches")
    st, other = search_partner(uid)
    if st == "matched":
        bump("matches")
        send(uid, MSG_CONNECTED, main_kb(uid))
        send(other, MSG_CONNECTED, main_kb(other))
    elif st == "queued":
        send(uid, "⏳ در حال جستجو برای یک نفر... (برای لغو «پایان چت»)", main_kb(uid))
    elif st == "waiting":
        send(uid, "⏳ هنوز در صف انتظارید...", main_kb(uid))
    else:
        send(uid, "⚠️ شما الان در چت هستید. اول «پایان چت» یا «چت بعدی».", main_kb(uid))


def owner_connect(target):
    """چت مستقیم و کاملاً ناشناس مالک با یک کاربر (برای کاربر شبیه یک غریبه‌ی عادی است)."""
    with LOCK:
        if target == OWNER_ID:
            return "self"
        if get_user(target, create=False) is None:
            return "unknown"
        if owner_is_user():
            set_S("owner_mode", "admin")
        end_chat(OWNER_ID)
        end_chat(target)
        set_partner(OWNER_ID, target)
        set_partner(target, OWNER_ID)
    send(target, MSG_CONNECTED, main_kb(target))
    return "ok"


def apply_warn(uid, word):
    if uid == OWNER_ID:      # حالت تست مالک: فقط نمایش، بدون اخطار واقعی
        send(uid, f"🧪 حالت تست: این پیام به‌خاطر کلمه‌ی «{word}» برای کاربر عادی اخطار می‌گرفت و ارسال نشد.")
        return
    with LOCK:
        u = get_user(uid)
        n = u["warns"] + 1
        mx = int(S("max_warns"))
        set_field(uid, "warns", n)
        banned = n >= mx
        if banned:
            set_field(uid, "banned", 1)
    if word:
        bump("blocked_msgs")
    if banned:
        bump("auto_bans" if word else "manual_bans")
        end_chat(uid)
        send(uid, f"🚫 به دلیل {'فحاشی و ' if word else ''}رسیدن به سقف اخطار ({n}/{mx}) مسدود شدید.",
             {"remove_keyboard": True})
        send(OWNER_ID, f"🚫 کاربر {uid} بن شد (اخطار {n}/{mx}).")
    elif word:
        send(uid, f"⚠️ پیام شما حاوی کلمه‌ی ممنوعه بود و ارسال نشد.\nاخطار {n} از {mx}")
    else:
        send(uid, f"⚠️ از طرف مدیریت اخطار گرفتید.\nاخطار {n} از {mx}")


def relay(m, u):
    uid, partner = u["uid"], u["partner"]
    if not is_direct(uid, partner):       # پیام‌های چت مستقیم مالک فیلتر نمی‌شود
        txt = m.get("text") or m.get("caption") or ""
        w = find_bad_word(txt)
        if w:
            apply_warn(uid, w)
            return
    r = api("copyMessage", {"chat_id": partner, "from_chat_id": m["chat"]["id"], "message_id": m["message_id"]})
    if r.get("ok"):
        bump("msgs")
    else:
        end_chat(uid, notify=False)
        send(uid, "⚠️ ارسال ممکن نبود؛ احتمالاً طرف مقابل رفته است. چت پایان یافت.", main_kb(uid))


def show_privacy(chat):
    send(chat, S("priv_text"), main_kb(chat))


def welcome_text(m):
    name = (m.get("from") or {}).get("first_name") or "دوست من"
    return S("welcome_text").replace("{name}", name)


def on_user_message(m):
    uid, chat = m["from"]["id"], m["chat"]["id"]
    u = get_user(uid)
    if u["banned"] and uid != OWNER_ID:
        send(chat, "🚫 دسترسی شما توسط مدیریت مسدود شده است.")
        return
    if not is_active():
        send(chat, off_message() + ("\n🧪 (حالت تست مالک)" if uid == OWNER_ID else ""),
             main_kb(uid) if uid == OWNER_ID else None)
        return
    text = (m.get("text") or "").strip()
    short = len(text) < 40
    if text.startswith("/start") or text.startswith("/help"):
        send(chat, welcome_text(m), main_kb(uid))
        return
    if text.startswith("/privacy") or (L_PRIV in text and S("priv_show") == "1" and short):
        if S("priv_show") == "1":
            show_privacy(chat)
        return
    if text.startswith("/end") or (L_END in text and short):
        p = end_chat(uid)
        send(chat, "✅ چت پایان یافت." if p else "ℹ️ شما در چت نیستید.", main_kb(uid))
        return
    if text.startswith("/next") or (L_NEXT in text and short):
        end_chat(uid)
        do_search(uid)
        return
    if text.startswith("/search") or (L_SEARCH in text and short):
        do_search(uid)
        return
    if u["partner"]:
        relay(m, u)
    else:
        send(chat, "برای شروع «جستجوی چت تصادفی» را بزن 👇", main_kb(uid))


# ───────────────────────── 8) پنل مدیریت مالک ─────────────────────────
HOME_BTN = [("🏠 منوی اصلی", "a:home")]
BCAST = {"mid": None, "running": False}


def fmt_dt(iso):
    if not iso:
        return "—"
    try:
        return jalali_str(datetime.fromisoformat(iso).astimezone(TEHRAN))
    except Exception:
        return iso


def fmt_uptime():
    s = int(time.time() - START_TIME)
    d, s = divmod(s, 86400)
    h, s = divmod(s, 3600)
    return f"{d} روز و {h} ساعت و {s // 60} دقیقه"


def set_owner_mode(mode):
    end_chat(OWNER_ID)
    ADMIN_STATE.pop(OWNER_ID, None)
    set_S("owner_mode", mode)
    if mode == "user":
        send(OWNER_ID, "👤 وارد پنل کاربر عادی شدی (حالت تست).\nهمه‌چیز دقیقاً مثل یک کاربر معمولی کار می‌کند؛ "
                       "فیلتر کلمات فقط هشدار تستی می‌دهد و اخطار واقعی ثبت نمی‌شود.\n"
                       f"برای برگشت: دکمه‌ی «{L_ADMIN}» یا /panel", main_kb(OWNER_ID))
    else:
        send(OWNER_ID, "🛠 به پنل ادمین برگشتی.", {"remove_keyboard": True})
        show(OWNER_ID, None, panel_home())


def panel_home():
    st = "🟢 روشن" if is_active() else "🔴 خاموش"
    text = f"🛠 پنل مدیریت\n📅 {jalali_str()}\nوضعیت ربات: {st}"
    kb = ikb([
        [("📊 آمار کامل", "a:stats", "primary"), ("📤 خروجی آمار (txt)", "a:export", "primary")],
        [("📢 پیام همگانی", "a:bc", "success"), ("🔎 جست‌وجوی کاربر", "a:find", "primary")],
        [("🚷 بن‌شده‌ها", "a:bl:0", "danger"), ("💬 چت‌های فعال", "a:ac:0", "success")],
        [("👋 پیام خوش‌آمد", "a:wel"), ("🔌 روشن/خاموش", "a:power", "success" if S("bot_on") == "1" else "danger")],
        [("⏰ زمان‌بندی", "a:sched"), ("🚫 کلمات ممنوعه", "a:words:0")],
        [("⚠️ اخطار و بن", "a:warn"), ("🎨 رنگ دکمه‌ها", "a:colors")],
        [("🔒 حریم خصوصی", "a:priv"), ("🔗 چت مستقیم با کاربر", "a:connect")],
        [("☁️ Cloudflare Worker", "a:cf")],
        [("👤 ورود به پنل کاربر عادی (تست)", "a:mode:user", "success")],
    ])
    return text, kb


# ── ۱) آمار کامل ──
def compute_stats():
    n = now()
    day0 = n.replace(hour=0, minute=0, second=0, microsecond=0).isoformat()
    d1, d7 = (n - timedelta(days=1)).isoformat(), (n - timedelta(days=7)).isoformat()
    with LOCK:
        q = lambda sql, *a: DB.execute(sql, a).fetchone()[0]
        st = {
            "total": q("SELECT COUNT(*) FROM users"),
            "new_today": q("SELECT COUNT(*) FROM users WHERE joined>=?", day0),
            "new_7d": q("SELECT COUNT(*) FROM users WHERE joined>=?", d7),
            "act_24h": q("SELECT COUNT(*) FROM users WHERE last_seen>=?", d1),
            "act_7d": q("SELECT COUNT(*) FROM users WHERE last_seen>=?", d7),
            "banned": q("SELECT COUNT(*) FROM users WHERE banned=1"),
            "warned": q("SELECT COUNT(*) FROM users WHERE warns>0 AND banned=0"),
            "words": q("SELECT COUNT(*) FROM words"),
        }
        st["c"] = dict(DB.execute("SELECT k,v FROM counters").fetchall())
    st["pairs"] = len(active_pairs())
    st["queue"] = len(WAITING)
    return st


def stats_text(st):
    c = st["c"].get
    return (f"📊 آمار کامل ربات\n📅 {jalali_str()}\n"
            f"وضعیت: {'🟢 روشن' if is_active() else '🔴 خاموش'} | مدت روشن بودن: {fmt_uptime()}\n\n"
            f"👥 کل کاربران: {st['total']}\n🆕 عضو جدید امروز: {st['new_today']} | ۷ روز اخیر: {st['new_7d']}\n"
            f"🔥 فعال ۲۴ ساعت: {st['act_24h']} | فعال ۷ روز: {st['act_7d']}\n\n"
            f"💬 چت‌های فعال: {st['pairs']} (نفر در چت: {st['pairs'] * 2})\n⏳ در صف انتظار: {st['queue']}\n"
            f"🔍 تعداد جست‌وجو: {c('searches', 0)} | اتصال موفق: {c('matches', 0)}\n"
            f"✉️ پیام‌های ردوبدل‌شده: {c('msgs', 0)}\n\n"
            f"🚫 بن‌شده: {st['banned']} | ⚠️ دارای اخطار: {st['warned']}\n"
            f"🧹 پیام فیلترشده: {c('blocked_msgs', 0)} | بن خودکار: {c('auto_bans', 0)}\n"
            f"📝 کلمات ممنوعه: {st['words']}\n📢 پیام همگانی ارسال‌شده: {c('broadcasts', 0)}")


def screen_stats():
    return stats_text(compute_stats()), ikb([[("🔄 بروزرسانی", "a:stats", "primary"),
                                              ("📤 خروجی txt", "a:export", "success")], HOME_BTN])


# ── ۷) خروجی آمار در فایل متنی ──
def build_report():
    st = compute_stats()
    with LOCK:
        banned = DB.execute("SELECT uid,warns,joined FROM users WHERE banned=1 ORDER BY uid").fetchall()
        warned = DB.execute("SELECT uid,warns FROM users WHERE warns>0 AND banned=0 ORDER BY warns DESC").fetchall()
    lines = ["گزارش آمار ربات چت ناشناس", "=" * 40, stats_text(st), "",
             "تنظیمات", "-" * 40,
             f"زمان‌بندی: {'فعال' if S('sched_on') == '1' else 'غیرفعال'} ({S('sched_start')} تا {S('sched_end')}، حالت {S('sched_mode')})",
             f"حداکثر اخطار: {S('max_warns')}", f"Worker: {S('worker_url') or '-'}",
             f"رنگ دکمه‌ها: جستجو={STYLES[S('color_chat')]}، بعدی={STYLES[S('color_next')]}، "
             f"پایان={STYLES[S('color_end')]}، حریم={STYLES[S('color_priv')]}", "",
             f"کاربران بن‌شده ({len(banned)})", "-" * 40]
    lines += [f"{u}\tاخطار {w}\tعضویت {fmt_dt(j)}" for u, w, j in banned] or ["-"]
    lines += ["", f"کاربران دارای اخطار ({len(warned)})", "-" * 40]
    lines += [f"{u}\tاخطار {w}" for u, w in warned] or ["-"]
    lines += ["", f"چت‌های فعال ({st['pairs']})", "-" * 40]
    lines += [f"{a} <-> {b}" for a, b in active_pairs()] or ["-"]
    lines += ["", f"صف انتظار ({len(WAITING)})", "-" * 40, " ".join(map(str, WAITING)) or "-"]
    return "\n".join(lines)


def send_report(chat):
    send_document(chat, f"anonchat_stats_{now():%Y%m%d_%H%M}.txt", build_report(), f"📤 گزارش آمار — {jalali_str()}")


# ── ۲) پیام همگانی ──
def broadcast_worker(chat, mid):
    with LOCK:
        uids = [r[0] for r in DB.execute("SELECT uid FROM users WHERE banned=0 AND uid!=?", (OWNER_ID,))]
    ok = fail = 0
    prog = send(chat, f"📢 در حال ارسال برای {len(uids)} کاربر...")
    pmid = (prog.get("result") or {}).get("message_id")
    for i, u in enumerate(uids, 1):
        for _ in range(3):
            r = api("copyMessage", {"chat_id": u, "from_chat_id": chat, "message_id": mid})
            if r.get("ok"):
                ok += 1
                break
            ra = (r.get("parameters") or {}).get("retry_after")
            if ra:
                time.sleep(int(ra) + 1)
                continue
            # Other failures are ambiguous for copyMessage. Retrying can
            # duplicate a message that Telegram already accepted.
            fail += 1
            break
        time.sleep(0.04)                      # حدود ۲۵ پیام در ثانیه (محدودیت تلگرام)
        if pmid and i % 50 == 0:
            edit(chat, pmid, f"📢 در حال ارسال... {i}/{len(uids)}")
    BCAST["running"] = False
    bump("broadcasts")
    send(chat, f"✅ پیام همگانی تمام شد.\nموفق: {ok}\nناموفق (ربات را بلاک کرده‌اند): {fail}",
         ikb([HOME_BTN]))


# ── ۳) جست‌وجوی کاربر ──
def screen_user(t, note=""):
    with LOCK:
        r = DB.execute("SELECT warns,banned,joined,last_seen FROM users WHERE uid=?", (t,)).fetchone()
    if not r:
        return (f"{note}\n❌ کاربری با شناسه‌ی {t} در ربات ثبت نشده (هنوز ربات را استارت نکرده).".strip(),
                ikb([[("🔎 جست‌وجوی دوباره", "a:find", "primary")], HOME_BTN]))
    warns, banned, joined, seen = r
    info = api("getChat", {"chat_id": t}).get("result") or {}
    name = " ".join(x for x in (info.get("first_name"), info.get("last_name")) if x) or "—"
    uname = "@" + info["username"] if info.get("username") else "—"
    p = get_user(t)["partner"]
    where = "💬 در چت" + (" (با مالک)" if p == OWNER_ID else "") if p else ("⏳ در صف" if t in WAITING else "💤 آزاد")
    txt = (f"{note}\n👤 اطلاعات کاربر {t}\nنام: {name}\nیوزرنیم: {uname}\n"
           f"وضعیت: {'🚫 بن‌شده' if banned else '✅ فعال'} | {where}\n"
           f"⚠️ اخطار: {warns} از {S('max_warns')}\n🗓 عضویت: {fmt_dt(joined)}\n🕒 آخرین فعالیت: {fmt_dt(seen)}").strip()
    rows = [[("⚠️ اخطار", f"a:u:warn:{t}"), ("♻️ ریست اخطار", f"a:u:reset:{t}", "primary")],
            [("✅ آنبن", f"a:u:unban:{t}", "success") if banned else ("🚫 بن", f"a:u:ban:{t}", "danger"),
             ("🔗 چت مستقیم", f"a:u:conn:{t}", "primary")]]
    if p:
        rows.append([("⛔ قطع چت فعلی", f"a:u:end:{t}", "danger")])
    rows += [[("🔄 بروزرسانی", f"a:u:view:{t}"), ("🔎 کاربر دیگر", "a:find")], HOME_BTN]
    return txt, ikb(rows)


def user_action(key, t):
    """اقدام مدیریتی روی یک کاربر؛ متن نتیجه را برمی‌گرداند."""
    if get_user(t, create=False) is None:
        return f"❌ کاربری با شناسه‌ی {t} در ربات ثبت نشده."
    if t == OWNER_ID:
        return "❌ روی مالک قابل اعمال نیست."
    if key == "warn":
        apply_warn(t, None)
        return "✅ اخطار ثبت شد."
    if key == "reset":
        set_field(t, "warns", 0)
        return "✅ اخطارها ریست شد."
    if key == "ban":
        set_field(t, "banned", 1)
        end_chat(t)
        bump("manual_bans")
        send(t, "🚫 دسترسی شما توسط مدیریت مسدود شد.", {"remove_keyboard": True})
        return "✅ بن شد."
    if key == "unban":
        set_field(t, "banned", 0)
        set_field(t, "warns", 0)
        send(t, "✅ دسترسی شما بازگردانده شد. /start")
        return "✅ آنبن شد."
    if key == "end":
        p = end_chat(t, notify=False)
        if not p:
            return "ℹ️ این کاربر در چت نیست."
        for x in (t, p):
            if x != OWNER_ID or owner_is_user():
                send(x, "⛔ این چت توسط مدیریت پایان یافت.", main_kb(x))
        return "✅ چت قطع شد."
    if key == "conn":
        return {"ok": "🔗 وصل شدید. پیام‌ها مستقیم به کاربر می‌رسد (او شما را یک غریبه‌ی عادی می‌بیند). پایان: /end",
                "self": "❌ نمی‌توانید به خودتان وصل شوید.",
                "unknown": "❌ این کاربر هرگز ربات را استارت نکرده است."}[owner_connect(t)]
    return ""


# ── ۴) مدیریت بن‌شده‌ها ──
def screen_banned(page):
    per = 8
    with LOCK:
        total = DB.execute("SELECT COUNT(*) FROM users WHERE banned=1").fetchone()[0]
        rows = DB.execute("SELECT uid,warns FROM users WHERE banned=1 ORDER BY uid LIMIT ? OFFSET ?",
                          (per, page * per)).fetchall()
    pages = max(1, (total + per - 1) // per)
    page = min(page, pages - 1)
    t = f"🚷 کاربران بن‌شده ({total}) — صفحه {page + 1}/{pages}\nبرای آنبن روی هر کاربر بزنید، برای جزئیات روی 👤."
    kb = [[(f"✅ آنبن {u} (اخطار {w})", f"a:ub:{u}:{page}", "success"), ("👤", f"a:u:view:{u}")] for u, w in rows]
    nav = []
    if page > 0:
        nav.append(("◀️ قبلی", f"a:bl:{page - 1}"))
    if page + 1 < pages:
        nav.append(("بعدی ▶️", f"a:bl:{page + 1}"))
    kb += [nav, [("➕ بن با شناسه", "a:warn:ban", "danger"), ("✅ آنبن با شناسه", "a:warn:unban", "success")]]
    if total:
        kb.append([("♻️ آنبن همه", "a:uball", "danger")])
    return t, ikb(kb + [HOME_BTN])


# ── ۵) چت‌های فعال ──
def active_pairs():
    with LOCK:
        rows = DB.execute("SELECT uid,partner FROM users WHERE partner IS NOT NULL").fetchall()
    seen, pairs = set(), []
    for uid, enc in rows:
        try:
            p = int(unseal(enc))
        except Exception:
            continue
        key = tuple(sorted((uid, p)))
        if key not in seen:
            seen.add(key)
            pairs.append(key)
    return pairs


def screen_active(page):
    per = 8
    pairs = active_pairs()
    pages = max(1, (len(pairs) + per - 1) // per)
    page = min(page, pages - 1)
    chunk = pairs[page * per:(page + 1) * per]
    lab = lambda x: "👑مالک" if x == OWNER_ID else str(x)
    body = "\n".join(f"{page * per + i}. {lab(a)} ⇄ {lab(b)}" for i, (a, b) in enumerate(chunk, 1)) or "— چت فعالی نیست —"
    q = " ، ".join(map(str, WAITING[:20])) or "—"
    t = f"💬 چت‌های فعال ({len(pairs)}) — صفحه {page + 1}/{pages}\n\n{body}\n\n⏳ صف انتظار ({len(WAITING)}): {q}"
    kb = [[(f"⛔ قطع چت {page * per + i}", f"a:ace:{a}:{page}", "danger"), ("👤", f"a:u:view:{a}")]
          for i, (a, b) in enumerate(chunk, 1)]
    nav = []
    if page > 0:
        nav.append(("◀️ قبلی", f"a:ac:{page - 1}"))
    if page + 1 < pages:
        nav.append(("بعدی ▶️", f"a:ac:{page + 1}"))
    kb += [nav, [("🔄 بروزرسانی", f"a:ac:{page}", "primary")]]
    if pairs:
        kb.append([("⛔ قطع همه‌ی چت‌ها", "a:acall", "danger")])
    return t, ikb(kb + [HOME_BTN])


# ── ۶) پیام خوش‌آمدگویی ──
def screen_welcome():
    t = f"👋 پیام خوش‌آمدگویی فعلی:\n\n{S('welcome_text')}\n\n(می‌توانید از {{name}} برای نام کاربر استفاده کنید)"
    return t, ikb([[("✏️ تغییر متن", "a:wel:set", "primary"), ("👁 پیش‌نمایش", "a:wel:pre")],
                   [("♻️ بازگشت به پیش‌فرض", "a:wel:def", "danger")], HOME_BTN])


def confirm_kb(yes_data, back_data):
    return ikb([[("✅ بله، انجام بده", yes_data, "danger"), ("↩️ نه، برگرد", back_data, "primary")]])


# ── سایر صفحه‌ها ──
def screen_power():
    on = S("bot_on") == "1"
    t = (f"🔌 روشن/خاموش دستی\nوضعیت دستی: {'🟢 روشن' if on else '🔴 خاموش'}\n"
         f"وضعیت نهایی (با زمان‌بندی): {'🟢 روشن' if is_active() else '🔴 خاموش'}")
    return t, ikb([[("خاموش کن", "a:power:t", "danger") if on else ("روشن کن", "a:power:t", "success")], HOME_BTN])


def screen_sched():
    on = S("sched_on") == "1"
    mode = "فعال" if S("sched_mode") == "active" else "غیرفعال"
    t = (f"⏰ زمان‌بندی (وقت تهران)\nزمان‌بندی: {'🟢 فعال' if on else '⚪ غیرفعال'}\n"
         f"در بازه‌ی {S('sched_start')} تا {S('sched_end')} ربات «{mode}» است.\n📅 {jalali_str()}")
    return t, ikb([
        [("🔁 غیرفعال کردن زمان‌بندی", "a:sched:t", "danger") if on else ("🔁 فعال کردن زمان‌بندی", "a:sched:t", "success")],
        [("🔄 تغییر نوع بازه (فعال/غیرفعال)", "a:sched:m", "primary")],
        [("✏️ ساعت شروع", "a:sched:s"), ("✏️ ساعت پایان", "a:sched:e")], HOME_BTN])


def screen_words(page):
    per = 20
    with LOCK:
        total = DB.execute("SELECT COUNT(*) FROM words").fetchone()[0]
        rows = DB.execute("SELECT id,word FROM words ORDER BY id LIMIT ? OFFSET ?", (per, page * per)).fetchall()
    pages = max(1, (total + per - 1) // per)
    body = "\n".join(f"{i}. {w}" for i, w in rows) or "—"
    t = f"🚫 کلمات ممنوعه ({total}) — صفحه {page + 1}/{pages}\n\n{body}"
    nav = []
    if page > 0:
        nav.append(("◀️ قبلی", f"a:words:{page - 1}"))
    if page + 1 < pages:
        nav.append(("بعدی ▶️", f"a:words:{page + 1}"))
    return t, ikb([nav, [("➕ افزودن", "a:w:add", "success"), ("🗑 حذف با شماره", "a:w:del", "danger")],
                   [("📤 خروجی txt", "a:w:exp", "primary")], HOME_BTN])


def screen_warn():
    t = f"⚠️ اخطار و بن\nحداکثر اخطار مجاز: {S('max_warns')}"
    return t, ikb([[("✏️ تعداد حداکثر اخطار", "a:warn:max", "primary")],
                   [("⚠️ اخطار دستی", "a:warn:warn"), ("♻️ ریست اخطار", "a:warn:reset")],
                   [("🚫 بن", "a:warn:ban", "danger"), ("✅ آنبن", "a:warn:unban", "success")],
                   [("📋 مدیریت بن‌شده‌ها", "a:bl:0")], HOME_BTN])


COLOR_NAMES = {"chat": L_SEARCH, "next": L_NEXT, "end": L_END, "priv": L_PRIV}


def screen_colors():
    rows = [[(f"{ICONS[k]} {v} ← {STYLES[S('color_' + k)]}", f"a:col:{k}", S("color_" + k))]
            for k, v in COLOR_NAMES.items()]
    t = ("🎨 رنگ دکمه‌های کاربران\nهر دکمه همین حالا با رنگ واقعی خودش نمایش داده شده؛ با زدن روی آن رنگ عوض می‌شود "
         "(سبز ← قرمز ← آبی ← بی‌رنگ).\nℹ️ رنگ دکمه‌ها از نسخه‌های جدید اپ تلگرام (بهمن ۱۴۰۴ به بعد) نمایش داده می‌شود.\n"
         "برای دیدن نتیجه در کیبورد اصلی، وارد «پنل کاربر عادی» شوید.")
    return t, ikb(rows + [[("👤 تست در پنل کاربر", "a:mode:user", "success")], HOME_BTN])


def screen_priv():
    shown = S("priv_show") == "1"
    t = f"🔒 تنظیمات حریم خصوصی\nنمایش دکمه: {'🟢 بله' if shown else '🔴 خیر'}\n\n{S('priv_text')}"
    return t, ikb([[("✏️ تغییر متن", "a:priv:text", "primary")],
                   [(f"🎨 رنگ دکمه: {STYLES[S('color_priv')]}", "a:col:priv", S("color_priv"))],
                   [("👁 مخفی کردن دکمه", "a:priv:t", "danger") if shown else ("👁 نمایش دکمه", "a:priv:t", "success")],
                   HOME_BTN])


def screen_cf():
    u = S("worker_url") or "— تنظیم نشده (اتصال مستقیم به تلگرام) —"
    mode = "☁️ Cloudflare فعال" if S("worker_enabled") == "1" else "🔌 اتصال مستقیم فعال"
    t = (f"☁️ Cloudflare Worker\nآدرس فعلی: {u}\nوضعیت: {mode}\n\n"
         "کاربرد: اگر api.telegram.org روی اینترنت شما باز نمی‌شود، Worker مثل یک واسطه‌ی امن درخواست‌های ربات را "
         "به تلگرام می‌رساند.\n"
         "۱) «دریافت worker.js» را بزنید (کد کامل و آماده با شناسه‌ی همین ربات ساخته می‌شود)\n"
         "۲) dash.cloudflare.com ← Workers & Pages ← Create ← Hello World ← Deploy ← Edit code\n"
         "۳) کل کد را جایگزین کنید و Deploy بزنید\n۴) آدرس ‎*.workers.dev را اینجا ثبت کنید.\n"
         "🔎 تست سریع بدون Termux: آدرس Worker را در مرورگر باز کنید؛ /health باید پاسخ سبز بدهد.\n"
         "تست کامل /health و getMe و getUpdates کوتاه از داخل ربات انجام می‌شود؛ توکن در لینک عمومی قرار نمی‌گیرد.")
    rows = [[("📄 دریافت worker.js", "a:cf:file", "success")],
            [("✏️ ثبت آدرس Worker", "a:cf:set", "primary"), ("🩺 بررسی سلامت", "a:cf:chk")],
            [("☁️ فعال‌سازی Cloudflare", "a:cf:on", "success"),
             ("🔌 اتصال مستقیم", "a:cf:off", "danger")]]
    if S("worker_url"):
        rows.append([("🗑 حذف آدرس (اتصال مستقیم)", "a:cf:del", "danger")])
    return t, ikb(rows + [HOME_BTN])


def worker_probe(url):
    """Light recovery probe, deliberately not competing with active long-poll."""
    url = url.rstrip("/")
    try:
        with urllib.request.urlopen(urllib.request.Request(url + "/health", headers=UA), timeout=8) as r:
            health = json.loads(r.read().decode())
            if r.status != 200 or not health.get("ok"):
                return False, f"/health پاسخ سالم نداد: {health}"
        me = _post(f"{url}/bot{BOT_TOKEN}/getMe", b"{}",
                   {"Content-Type": "application/json"}, 10)
        return bool(me.get("ok")), me.get("description", "getMe ناموفق بود")
    except Exception as e:
        return False, str(e)


def health_check(url):
    """Full active test: health, getMe, and one serialized short getUpdates."""
    global POLL_OFFSET
    url = url.rstrip("/")
    started = time.monotonic()
    try:
        req = urllib.request.Request(url + "/health", headers=UA)
        with urllib.request.urlopen(req, timeout=10) as r:
            status, raw = r.status, r.read().decode()
        try:
            health = json.loads(raw)
        except json.JSONDecodeError:
            return False, f"پاسخ /health JSON نیست (HTTP {status}); آدرس Worker یا deployment را بررسی کنید."
        if status != 200 or not health.get("ok"):
            return False, f"/health ناموفق است (HTTP {status}): {health.get('description') or health}"
        t0 = time.monotonic()
        me = _post(f"{url}/bot{BOT_TOKEN}/getMe", b"{}",
                   {"Content-Type": "application/json"}, 12)
        me_ms = int((time.monotonic() - t0) * 1000)
        if not me.get("ok"):
            code, desc = me.get("error_code"), me.get("description", "پاسخ نامشخص")
            if "1102" in str(desc) or "CPU time" in str(desc).lower():
                return False, "Cloudflare خطای 1102/CPU Limit داده است؛ زمان اجرای Worker یا تنظیمات پلن را بررسی کنید."
            if me.get("_http_status") == 429:
                return False, "Worker یا Cloudflare درخواست‌ها را rate-limit کرده است (429)."
            if code == 401:
                return False, "Worker پاسخ می‌دهد ولی توکن ربات نامعتبر است (401)."
            if code == 403:
                return False, "403: شناسه‌ی ربات در Worker با توکن فعلی نمی‌خواند یا درخواست رد شده است."
            if code == 404:
                return False, "404: آدرس ثبت‌شده باید آدرس پایه‌ی Worker باشد، نه /health یا مسیر اضافی."
            if code in (502, 503, 504) or me.get("_net"):
                return False, f"Worker reachable است اما upstream تلگرام خطا داد ({code or 'timeout'}): {desc}"
            return False, f"getMe ناموفق بود ({code or 'خطا'}): {desc}"

        poll_params = {"timeout": 1, "allowed_updates": ["message", "callback_query"]}
        if POLL_OFFSET is not None:
            poll_params["offset"] = POLL_OFFSET
        updates = []
        with POLL_LOCK:
            t0 = time.monotonic()
            poll = _post(f"{url}/bot{BOT_TOKEN}/getUpdates",
                         json.dumps(poll_params).encode(),
                         {"Content-Type": "application/json"}, 8)
            poll_ms = int((time.monotonic() - t0) * 1000)
            if poll.get("ok"):
                updates = poll.get("result") or []
                if updates:
                    POLL_OFFSET = max(u["update_id"] for u in updates) + 1
        # Do not drop updates fetched by the health probe.
        for update in updates:
            handle_update(update)
        if not poll.get("ok"):
            reason = poll.get("description", "خطای نامشخص")
            if poll.get("error_code") == 409:
                reason = "409 Conflict: poll دیگری با همین توکن فعال است."
            return False, (f"✅ /health موفق\n✅ getMe موفق ({me_ms}ms)\n"
                           f"❌ getUpdates ناموفق: {reason}")
        elapsed = int((time.monotonic() - started) * 1000)
        return True, (f"✅ /health موفق\n✅ getMe موفق: @{me['result'].get('username', '?')} ({me_ms}ms)\n"
                      f"✅ getUpdates کوتاه موفق ({poll_ms}ms)\n⚡ latency کل: {elapsed}ms")
    except urllib.error.HTTPError as e:
        if e.code in (404, 405):
            return False, f"آدرس Worker پیدا نشد یا مسیر /health فعال نیست (HTTP {e.code})."
        return False, f"Worker با خطای HTTP {e.code} پاسخ داد."
    except urllib.error.URLError as e:
        return False, f"اتصال به Worker برقرار نشد: {e.reason}"
    except TimeoutError:
        return False, "Timeout: پاسخ Worker/upstream تلگرام بیش از زمان مجاز طول کشید."
    except Exception as e:
        return False, f"خطای بررسی Worker: {e}"


def show(chat, mid, screen):
    text, kb = screen
    if mid:
        r = edit(chat, mid, text, kb)
        if r.get("ok") or "not modified" in str(r.get("description", "")):
            return
    send(chat, text, kb)


PROMPTS = {
    "w_add": "➕ کلمه(ها) را بفرستید (هر کلمه در یک خط).",
    "w_del": "🗑 شماره‌ی کلمه(ها) را بفرستید (با فاصله یا ویرگول جدا کنید).",
    "max": "✏️ حداکثر تعداد اخطار را بفرستید (عدد ۱ تا ۲۰).",
    "warn": "⚠️ شناسه‌ی عددی کاربر را برای «اخطار» بفرستید.",
    "reset": "♻️ شناسه‌ی عددی کاربر را برای «ریست اخطار» بفرستید.",
    "ban": "🚫 شناسه‌ی عددی کاربر را برای «بن» بفرستید.",
    "unban": "✅ شناسه‌ی عددی کاربر را برای «آنبن» بفرستید.",
    "connect": "🔗 شناسه‌ی عددی کاربر را بفرستید. چت کاملاً ناشناس است. پایان: /end",
    "find": "🔎 شناسه‌ی عددی کاربر را بفرستید.",
    "bcast": "📢 پیامی که باید برای همه ارسال شود را بفرستید (متن، عکس، ویدیو، فایل، استیکر و...).",
    "welcome": "✏️ متن جدید پیام خوش‌آمدگویی را بفرستید. ({name} = نام کاربر)",
    "sched_s": "✏️ ساعت شروع را به شکل HH:MM بفرستید (مثلاً 08:30).",
    "sched_e": "✏️ ساعت پایان را به شکل HH:MM بفرستید (مثلاً 23:00).",
    "priv_text": "✏️ متن جدید سیاست حفظ حریم خصوصی را بفرستید.",
    "cf_url": "✏️ آدرس Worker را بفرستید (مثال: https://my-bot.username.workers.dev).",
}


def ask(chat, key):
    ADMIN_STATE[chat] = key
    send(chat, PROMPTS[key] + "\n(لغو: /cancel)")


def send_worker_file(chat):
    code = worker_code()
    try:
        with open(WORKER_FILE, "w", encoding="utf-8") as f:
            f.write(code)
    except Exception:
        pass
    r = send_document(chat, "worker.js", code,
                      "📄 کد کامل Cloudflare Worker (آماده‌ی استفاده، با شناسه‌ی همین ربات)\n"
                      "Cloudflare ← Workers & Pages ← Create ← Hello World ← Edit code ← جایگزینی کد ← Deploy")
    if not r.get("ok"):                       # اگر ارسال فایل ممکن نبود، کد به‌صورت متن فرستاده می‌شود
        for i in range(0, len(code), 3800):
            send(chat, code[i:i + 3800])


def on_callback(cb):
    uid = cb["from"]["id"]
    chat, mid = cb["message"]["chat"]["id"], cb["message"]["message_id"]
    if uid != OWNER_ID:
        api("answerCallbackQuery", {"callback_query_id": cb["id"], "text": "⛔ دسترسی ندارید"})
        return
    api("answerCallbackQuery", {"callback_query_id": cb["id"]})
    p = cb["data"].split(":")
    a = p[1] if len(p) > 1 else "home"
    sub = p[2] if len(p) > 2 else ""
    ADMIN_STATE.pop(chat, None)

    if a == "home":
        show(chat, mid, panel_home())
    elif a == "mode":
        set_owner_mode("user" if sub == "user" else "admin")
    elif a == "stats":
        show(chat, mid, screen_stats())
    elif a == "export":
        send_report(chat)
    elif a == "bc":
        if sub == "go" and BCAST["mid"] and not BCAST["running"]:
            BCAST["running"] = True
            m_id, BCAST["mid"] = BCAST["mid"], None
            edit(chat, mid, "📢 ارسال شروع شد...")
            threading.Thread(target=broadcast_worker, args=(chat, m_id), daemon=True).start()
        elif sub == "no":
            BCAST["mid"] = None
            show(chat, mid, ("❌ پیام همگانی لغو شد.", ikb([HOME_BTN])))
        elif BCAST["running"]:
            send(chat, "⏳ یک پیام همگانی در حال ارسال است؛ صبر کنید تا تمام شود.")
        else:
            ask(chat, "bcast")
    elif a == "find":
        ask(chat, "find")
    elif a == "u":
        act, t = sub, int(p[3]) if len(p) > 3 and p[3].isdigit() else 0
        note = "" if act == "view" else user_action(act, t)
        show(chat, mid, screen_user(t, note))
    elif a == "bl":
        show(chat, mid, screen_banned(int(sub or 0)))
    elif a == "ub":
        user_action("unban", int(sub))
        show(chat, mid, screen_banned(int(p[3]) if len(p) > 3 else 0))
    elif a == "uball":
        if sub == "yes":
            with LOCK:
                ids = [r[0] for r in DB.execute("SELECT uid FROM users WHERE banned=1")]
            for t in ids:
                user_action("unban", t)
            show(chat, mid, (f"✅ {len(ids)} کاربر آنبن شد.", ikb([[("🚷 بن‌شده‌ها", "a:bl:0")], HOME_BTN])))
        else:
            show(chat, mid, ("⚠️ همه‌ی کاربران بن‌شده آزاد شوند؟", confirm_kb("a:uball:yes", "a:bl:0")))
    elif a == "ac":
        show(chat, mid, screen_active(int(sub or 0)))
    elif a == "ace":
        user_action("end", int(sub))
        show(chat, mid, screen_active(int(p[3]) if len(p) > 3 else 0))
    elif a == "acall":
        if sub == "yes":
            pairs = active_pairs()
            for x, _ in pairs:
                user_action("end", x) if x != OWNER_ID else end_chat(OWNER_ID)
            show(chat, mid, (f"✅ {len(pairs)} چت قطع شد.", ikb([[("💬 چت‌های فعال", "a:ac:0")], HOME_BTN])))
        else:
            show(chat, mid, ("⚠️ همه‌ی چت‌های فعال قطع شوند؟", confirm_kb("a:acall:yes", "a:ac:0")))
    elif a == "wel":
        if sub == "set":
            ask(chat, "welcome")
            return
        if sub == "pre":
            send(chat, welcome_text(cb))
            return
        if sub == "def":
            set_S("welcome_text", DEFAULT_WELCOME)
        show(chat, mid, screen_welcome())
    elif a == "power":
        if sub == "t":
            set_S("bot_on", "0" if S("bot_on") == "1" else "1")
        show(chat, mid, screen_power())
    elif a == "sched":
        if sub == "t":
            set_S("sched_on", "0" if S("sched_on") == "1" else "1")
        elif sub == "m":
            set_S("sched_mode", "inactive" if S("sched_mode") == "active" else "active")
        elif sub in ("s", "e"):
            ask(chat, "sched_" + sub)
            return
        show(chat, mid, screen_sched())
    elif a == "words":
        show(chat, mid, screen_words(int(sub or 0)))
    elif a == "w":
        if sub == "add":
            ask(chat, "w_add")
        elif sub == "del":
            ask(chat, "w_del")
        elif sub == "exp":
            with LOCK:
                rows = DB.execute("SELECT id,word FROM words ORDER BY id").fetchall()
            data = "\n".join(f"{i}\t{w}" for i, w in rows)
            send_document(chat, "banned_words.txt", data, f"📤 {len(rows)} کلمه")
    elif a == "warn":
        if sub == "list":
            show(chat, mid, screen_banned(0))
        elif sub:
            ask(chat, sub)
        else:
            show(chat, mid, screen_warn())
    elif a == "colors":
        show(chat, mid, screen_colors())
    elif a == "col":
        k = sub
        cur = S("color_" + k)
        set_S("color_" + k, STYLE_ORDER[(STYLE_ORDER.index(cur) + 1) % len(STYLE_ORDER)])
        show(chat, mid, screen_priv() if k == "priv" else screen_colors())
    elif a == "priv":
        if sub == "t":
            set_S("priv_show", "0" if S("priv_show") == "1" else "1")
        elif sub == "text":
            ask(chat, "priv_text")
            return
        show(chat, mid, screen_priv())
    elif a == "connect":
        ask(chat, "connect")
    elif a == "cf":
        if sub == "set":
            ask(chat, "cf_url")
        elif sub == "del":
            set_S("worker_url", "")
            set_S("worker_enabled", "0")
            set_S("worker_auto_recover", "0")
            show(chat, mid, screen_cf())
        elif sub == "off":
            set_S("worker_enabled", "0")
            set_S("worker_auto_recover", "0")
            send(chat, "🔌 اتصال مستقیم فعال شد؛ بازگشت خودکار به Worker خاموش است.", ikb([HOME_BTN]))
        elif sub == "on":
            url = S("worker_url")
            if not url:
                send(chat, "⚠️ ابتدا آدرس Worker را ثبت کنید.")
            else:
                ok, info = health_check(url)
                set_S("worker_auto_recover", "1")
                set_S("worker_enabled", "1" if ok else "0")
                send(chat, ("☁️ Cloudflare فعال شد.\n" if ok else
                            "❌ فعال‌سازی نشد؛ اتصال مستقیم حفظ شد.\n") + str(info)[:700],
                     ikb([HOME_BTN]))
        elif sub == "chk":
            url = S("worker_url")
            if not url:
                send(chat, "⚠️ ابتدا آدرس Worker را ثبت کنید.")
            else:
                ok, info = health_check(url)
                send(chat, ("✅ Worker سالم است.\n" if ok else "❌ Worker پاسخ سالم نداد.\n") + str(info)[:700])
        elif sub == "file":
            send_worker_file(chat)
        else:
            show(chat, mid, screen_cf())


def _ints(text):
    return [int(x) for x in re.findall(r"\d+", text)]


def on_owner_input(chat, text):
    """پاسخ متنی مالک به پرسش‌های پنل."""
    key = ADMIN_STATE.pop(chat, None)
    if key == "w_add":
        n = 0
        with LOCK:
            for w in dict.fromkeys(x.strip() for x in text.splitlines() if x.strip()):
                if normalize(w):
                    n += DB.execute("INSERT OR IGNORE INTO words(word) VALUES(?)", (w,)).rowcount
            DB.commit()
        reload_words()
        send(chat, f"✅ {n} کلمه‌ی جدید اضافه شد.", ikb([[("🚫 کلمات ممنوعه", "a:words:0")], HOME_BTN]))
    elif key == "w_del":
        ids = _ints(text)
        with LOCK:
            n = sum(DB.execute("DELETE FROM words WHERE id=?", (i,)).rowcount for i in ids)
            DB.commit()
        reload_words()
        send(chat, f"✅ {n} کلمه حذف شد.", ikb([[("🚫 کلمات ممنوعه", "a:words:0")], HOME_BTN]))
    elif key == "max":
        v = _ints(text)
        if v and 1 <= v[0] <= 20:
            set_S("max_warns", v[0])
            send(chat, f"✅ حداکثر اخطار: {v[0]}")
        else:
            send(chat, "❌ عدد معتبر ۱ تا ۲۰ بفرستید.")
    elif key in ("warn", "reset", "ban", "unban"):
        v = _ints(text)
        if not v:
            send(chat, "❌ یک شناسه‌ی عددی بفرستید.")
            return
        show(chat, None, screen_user(v[0], user_action(key, v[0])))
    elif key == "find":
        v = _ints(text)
        if not v:
            send(chat, "❌ یک شناسه‌ی عددی بفرستید.")
            return
        show(chat, None, screen_user(v[0]))
    elif key == "connect":
        v = _ints(text)
        send(chat, user_action("conn", v[0]) if v else "❌ یک شناسه‌ی عددی بفرستید.")
    elif key == "welcome":
        set_S("welcome_text", text.strip())
        show(chat, None, screen_welcome())
    elif key in ("sched_s", "sched_e"):
        if valid_hm(text):
            h, m = text.strip().split(":")
            set_S("sched_start" if key == "sched_s" else "sched_end", f"{int(h):02d}:{m}")
            send(chat, "✅ ثبت شد.", ikb([[("⏰ زمان‌بندی", "a:sched")], HOME_BTN]))
        else:
            send(chat, "❌ قالب باید HH:MM باشد.")
    elif key == "priv_text":
        set_S("priv_text", text.strip())
        send(chat, "✅ متن سیاست حفظ حریم خصوصی تغییر کرد.")
    elif key == "cf_url":
        u = text.strip().rstrip("/")
        if re.fullmatch(r"https://[\w.-]+(:\d+)?(/[\w./-]*)?", u):
            ok, info = health_check(u)
            set_S("worker_url", u)
            set_S("worker_auto_recover", "1")
            set_S("worker_enabled", "1" if ok else "0")
            send(chat, ("✅ آدرس ثبت و Cloudflare فعال شد.\n" if ok else
                        "⚠️ آدرس ثبت شد، اما تست شکست خورد و اتصال مستقیم حفظ شد.\n") + str(info)[:700])
        else:
            send(chat, "❌ آدرس باید با https:// شروع شود.")


def on_owner_message(m):
    chat = m["chat"]["id"]
    text = (m.get("text") or "").strip()
    if text == "/cancel":
        ADMIN_STATE.pop(chat, None)
        BCAST["mid"] = None
        send(chat, "لغو شد.", ikb([HOME_BTN]))
        return
    if ADMIN_STATE.get(chat) == "bcast":
        ADMIN_STATE.pop(chat, None)
        with LOCK:
            n = DB.execute("SELECT COUNT(*) FROM users WHERE banned=0 AND uid!=?", (OWNER_ID,)).fetchone()[0]
        BCAST["mid"] = m["message_id"]
        send(chat, f"📢 پیام بالا برای {n} کاربر ارسال شود؟",
             ikb([[(f"✅ ارسال برای {n} نفر", "a:bc:go", "success"), ("❌ لغو", "a:bc:no", "danger")]]))
        return
    if text in ("/start", "/panel", "/admin"):
        ADMIN_STATE.pop(chat, None)
        show(chat, None, panel_home())
        return
    if text in ("/user", "/test"):
        set_owner_mode("user")
        return
    if text == "/stats":
        show(chat, None, screen_stats())
        return
    if text == "/end":
        p = end_chat(OWNER_ID)
        send(chat, "✅ چت مستقیم پایان یافت." if p else "ℹ️ چت مستقیمی فعال نیست.")
        return
    if text.startswith("/connect"):
        v = _ints(text)
        if v:
            send(chat, user_action("conn", v[0]))
        else:
            ask(chat, "connect")
        return
    if chat in ADMIN_STATE and text:
        on_owner_input(chat, text)
        return
    u = get_user(OWNER_ID)
    if u["partner"]:
        relay(m, u)
    else:
        send(chat, "برای باز کردن پنل: /panel")


# ───────────────────────── 9) کد Cloudflare Worker ─────────────────────────
WORKER_TEMPLATE = r"""/**
 * Cloudflare Worker — پراکسی امن API تلگرام برای ربات چت ناشناس
 * ----------------------------------------------------------------
 * نصب: dash.cloudflare.com ← Workers & Pages ← Create ← Hello World ← Deploy
 *       ← Edit code ← کل این کد را جایگزین کنید ← Deploy
 * سپس آدرس https://<name>.<account>.workers.dev را در پنل ربات (☁️ Cloudflare) ثبت کنید.
 *
 * مسیرها:
 *   GET  /            و  /health        → بررسی سلامت  {"ok": true, ...}
 *   ANY  /bot<TOKEN>/<method>           → عبور به api.telegram.org
 *   GET  /file/bot<TOKEN>/<path>        → دانلود فایل‌های تلگرام
 */

// فقط همین ربات اجازه‌ی استفاده از Worker را دارد (عدد قبل از «:» در توکن).
// اگر خالی بماند، هر رباتی می‌تواند از این Worker عبور کند.
const ALLOWED_BOT_ID = "__BOT_ID__";

const TELEGRAM_API = "https://api.telegram.org";
const VERSION = "2.2.0";
// Bot long-poll is capped at 10s; keep upstream wall time below 13s.
const UPSTREAM_TIMEOUT_MS = 13000;

export default {
  async fetch(request) {
    const url = new URL(request.url);
    const path = url.pathname.replace(/\/{2,}/g, "/");

    if (request.method === "OPTIONS") {
      return new Response(null, { status: 204, headers: corsHeaders() });
    }

    if (path === "/" || path === "/health") {
      return json({
        ok: true,
        service: "anonchat-telegram-proxy",
        version: VERSION,
        restricted: Boolean(ALLOWED_BOT_ID),
        time: new Date().toISOString(),
      });
    }

    const m = path.match(/^\/(file\/)?bot(\d+):([A-Za-z0-9_-]+)(\/.*)?$/);
    if (!m) {
      return json({ ok: false, error_code: 400, description: "Bad path. Use /bot<TOKEN>/<method>" }, 400);
    }
    if (ALLOWED_BOT_ID && m[2] !== ALLOWED_BOT_ID) {
      return json({ ok: false, error_code: 403, description: "This proxy is locked to another bot" }, 403);
    }

    const headers = new Headers();
    const ct = request.headers.get("content-type");
    if (ct) headers.set("content-type", ct);

    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), UPSTREAM_TIMEOUT_MS);
    const init = {
      method: request.method,
      headers,
      redirect: "follow",
      signal: controller.signal,
    };
    if (request.method !== "GET" && request.method !== "HEAD") {
      // Forward the request stream instead of buffering uploads in Worker memory.
      init.body = request.body;
    }

    try {
      const upstream = await fetch(TELEGRAM_API + path + url.search, init);
      const out = new Headers(corsHeaders());
      out.set("cache-control", "no-store, no-cache, must-revalidate");
      const uct = upstream.headers.get("content-type");
      if (uct) out.set("content-type", uct);
      const ud = upstream.headers.get("content-disposition");
      if (ud) out.set("content-disposition", ud);
      const retryAfter = upstream.headers.get("retry-after");
      if (retryAfter) out.set("retry-after", retryAfter);
      return new Response(upstream.body, { status: upstream.status, headers: out });
    } catch (err) {
      const aborted = err && err.name === "AbortError";
      return json({
        ok: false,
        error_code: aborted ? 504 : 502,
        description: aborted
          ? "Telegram upstream timeout"
          : "Upstream error: " + String(err),
      }, aborted ? 504 : 502);
    } finally {
      clearTimeout(timer);
    }
  },
};

function corsHeaders() {
  return {
    "access-control-allow-origin": "*",
    "access-control-allow-methods": "GET, POST, OPTIONS",
    "access-control-allow-headers": "content-type",
  };
}

function json(obj, status = 200) {
  return new Response(JSON.stringify(obj), {
    status,
    headers: {
      "content-type": "application/json; charset=utf-8",
      "cache-control": "no-store, no-cache, must-revalidate",
      ...corsHeaders(),
    },
  });
}
"""


def worker_code():
    """کد کامل Worker با شناسه‌ی همین ربات؛ همیشه از داخل خود برنامه ساخته می‌شود (نیازی به فایل جدا نیست)."""
    bot_id = BOT_TOKEN.split(":")[0] if ":" in BOT_TOKEN else ""
    return WORKER_TEMPLATE.replace("__BOT_ID__", bot_id)


# ───────────────────────── 10) حلقه‌ی اصلی ─────────────────────────
def handle_update(upd):
    update_id = upd.get("update_id")
    if update_id is not None:
        with _processed_updates_lock:
            if update_id in _processed_updates:
                return
            _processed_updates.add(update_id)
            if len(_processed_updates) > _MAX_PROCESSED_UPDATES:
                _processed_updates.pop()
    try:
        if "callback_query" in upd:
            on_callback(upd["callback_query"])
        elif "message" in upd:
            m = upd["message"]
            if m.get("chat", {}).get("type") != "private" or "from" not in m:
                return
            uid = m["from"]["id"]
            touch(uid)
            with user_lock(uid):               # ترتیب پیام‌های هر کاربر حفظ می‌شود
                if uid == OWNER_ID:
                    t = (m.get("text") or "").strip()
                    if owner_is_user():
                        if t in ("/panel", "/admin") or (L_ADMIN in t and len(t) < 40):
                            set_owner_mode("admin")
                        else:
                            on_user_message(m)
                    else:
                        on_owner_message(m)
                else:
                    on_user_message(m)
    except Exception as e:
        print("handler error:", repr(e), file=sys.stderr)


def main():
    global BOT_TOKEN, OWNER_ID, POLL_OFFSET, LAST_POLL_OK_AT, LAST_POLL_LATENCY_MS
    BOT_TOKEN, OWNER_ID = load_config()
    init_db()
    try:                                       # worker.js همیشه کنار ربات ساخته/به‌روز می‌شود
        with open(WORKER_FILE, "w", encoding="utf-8") as f:
            f.write(worker_code())
    except Exception:
        pass
    startup_failures = 0
    while True:
        me = api("getMe", timeout=12)
        if me.get("ok"):
            break
        if me.get("error_code") == 401:
            print("❌ توکن ربات نامعتبر است (401). BOT_TOKEN/config.json را بررسی کنید.")
            sys.exit(1)
        startup_failures = min(startup_failures + 1, 6)
        delay = min(60, 2 ** startup_failures) + random.uniform(0, 1)
        print(f"اتصال تلگرام برقرار نشد؛ تلاش دوباره تا {delay:.1f} ثانیه دیگر: "
              f"{me.get('description')}", file=sys.stderr)
        time.sleep(delay)
    api("deleteWebhook")                       # حالت polling (Termux)
    api("setMyCommands", {"commands": [
        {"command": "start", "description": "شروع"}, {"command": "search", "description": "جستجوی چت"},
        {"command": "next", "description": "چت بعدی"}, {"command": "end", "description": "پایان چت"}]})
    print(f"✅ ربات @{me['result']['username']} آماده است — {jalali_str()} — مسیر API: {api_base()}")
    offset = None
    failures = 0
    with ThreadPoolExecutor(max_workers=16) as pool:
        while True:
            # Short long-poll leaves headroom under Worker request limits.
            t0 = time.monotonic()
            with POLL_LOCK:
                if POLL_OFFSET is not None and (offset is None or POLL_OFFSET > offset):
                    offset = POLL_OFFSET
                r = api("getUpdates", {"timeout": 10, "offset": offset,
                                       "allowed_updates": ["message", "callback_query"]}, timeout=18)
                LAST_POLL_LATENCY_MS = int((time.monotonic() - t0) * 1000)
            if not r.get("ok"):
                failures = min(failures + 1, 6)
                delay = min(30, 2 ** failures) + random.uniform(0, 0.75)
                print(f"getUpdates error; retrying in {delay:.1f}s: {r.get('description')}", file=sys.stderr)
                time.sleep(delay)
                continue
            failures = 0
            LAST_POLL_OK_AT = time.time()
            for upd in r["result"]:
                offset = upd["update_id"] + 1
                POLL_OFFSET = offset
                pool.submit(handle_update, upd)


if __name__ == "__main__":
    main()
