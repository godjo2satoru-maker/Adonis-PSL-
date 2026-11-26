import base64
import gc
import html
import io
import itertools
import math
import os
import queue
import re
import sqlite3
import threading
import time
from contextlib import contextmanager
from urllib.parse import quote

from PIL import Image, ImageDraw, ImageFont, ImageOps
import requests
import telebot
from telebot.types import (
    BotCommand,
    BotCommandScopeChat,
    BotCommandScopeDefault,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    LabeledPrice,
)

from adonis_config import (
    build_adult_prompt,
    calibrate_single_score,
    category_by_score,
    evaluate_mediapipe_metrics,
    get_gender_config,
    get_growth_plan_prompt,
    get_profile_prompt,
    get_scale_html,
    get_visual_prop_specs,
    is_female_hash,
    is_profile_hash,
    is_valid_photo_hash,
    make_photo_hash,
    normalize_gender,
)
from adonis_features import (
    CryptoInvoicePoller,
    CryptoPayClient,
    compute_battle_result,
    deserialize_metrics,
    extract_metrics_fallback,
    render_battle_card,
    render_share_card,
    serialize_metrics,
)

Image.MAX_IMAGE_PIXELS = 25_000_000

try:
    import numpy as np
except ImportError:
    np = None

try:
    import mediapipe as mp
except ImportError:
    mp = None


def _load_dotenv(filepath=".env"):
    full_path = os.path.join(os.getcwd(), filepath)
    if not os.path.isfile(full_path):
        return
    try:
        with open(full_path, "r", encoding="utf-8") as f:
            for raw_line in f:
                line = raw_line.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                key, val = line.split("=", 1)
                key = key.strip()
                val = val.strip().strip('"').strip("'")
                if key:
                    os.environ.setdefault(key, val)
    except Exception as e:
        print(f"[ENV] Не удалось прочитать {filepath}: {e}")


_load_dotenv()

_ENV_KEYS = os.getenv("GEMINI_API_KEYS", "").strip()
API_KEYS = [k.strip() for k in _ENV_KEYS.split(",") if k.strip()]

GEMINI_BASE_URL = (
    os.getenv("GEMINI_BASE_URL", "https://adonis-bot.godjo2satoru.workers.dev")
    .strip()
    .rstrip("/")
)

DEFAULT_MODELS = ["gemini-3.5-flash-lite"]
PRESET_MODELS = [
    "gemini-3.5-flash-lite",
    "gemini-3.1-flash-lite",
    "gemini-3.6-flash",
]

_ENV_MODELS = os.getenv("GEMINI_MODELS", "").strip()
_models_lock = threading.Lock()
_active_models = (
    [m.strip() for m in _ENV_MODELS.split(",") if m.strip()]
    if _ENV_MODELS
    else list(DEFAULT_MODELS)
)

TELEGRAM_BOT_TOKEN = (
    os.getenv("BOT_TOKEN", "").strip()
    or os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
)

_ENV_ADMINS = os.getenv("ADMIN_IDS", "6484073364").strip() or "6484073364"
ADMIN_IDS = [
    int(x.strip())
    for x in _ENV_ADMINS.split(",")
    if x.strip().isdigit()
]

ADMIN_CONTACT = os.getenv("ADMIN_CONTACT", "").strip()

CRYPTOBOT_TOKEN = os.getenv("CRYPTOBOT_TOKEN", "").strip()
CRYPTOBOT_TESTNET = os.getenv("CRYPTOBOT_TESTNET", "0").strip().lower() in ("1", "true", "yes")
CRYPTO_INVOICE_TTL = 1800

crypto_client = CryptoPayClient(CRYPTOBOT_TOKEN, testnet=CRYPTOBOT_TESTNET)

_RAW_CHANNEL_ID = os.getenv("CHANNEL_ID", "").strip()
CHANNEL_URL = os.getenv("CHANNEL_URL", "").strip()

if _RAW_CHANNEL_ID.startswith(("https://t.me/", "http://t.me/", "t.me/")):
    _ch_slug = _RAW_CHANNEL_ID.split("t.me/", 1)[1].strip("/").split("?", 1)[0]
    if _ch_slug.startswith("+") or _ch_slug.startswith("joinchat"):
        print(
            "[ENV] ВНИМАНИЕ: в CHANNEL_ID указана invite-ссылка. "
            "Для приватного канала укажи числовой ID (-100...) в CHANNEL_ID, а ссылку — в CHANNEL_URL."
        )
        if not CHANNEL_URL:
            CHANNEL_URL = _RAW_CHANNEL_ID
        CHANNEL_ID = ""
    elif _ch_slug:
        CHANNEL_ID = f"@{_ch_slug}"
    else:
        CHANNEL_ID = ""
else:
    CHANNEL_ID = _RAW_CHANNEL_ID

CHANNEL_SUB_BONUS = 1

DEFAULT_FREE_LIMIT = 0
REFERRAL_BONUS = 1
PRO30_DAILY_LIMIT = 15
PRO_LIFE_DAILY_LIMIT = 20
PRO30_DAYS = 30
PROFILE_WAIT_TTL = 1800
PROMO_WAIT_TTL = 600
BATTLE_WAIT_TTL = 900
BATTLE_SCAN_COST = 2

REF_MILESTONES = [
    (3, 1),
    (10, 7),
    (25, 30),
]

PLANS = {
    "pack5": {
        "title": "⚡ 5 сканов",
        "desc": "Пакет из 5 сканов внешности (не сгорают)",
        "stars": 30,
        "rub": 50,
        "type": "pack",
        "amount": 5,
    },
    "pack15": {
        "title": "🔥 15 сканов",
        "desc": "Выгодный пакет из 15 сканов внешности (не сгорают)",
        "stars": 70,
        "rub": 129,
        "type": "pack",
        "amount": 15,
    },
    "pro30": {
        "title": f"👑 PRO на {PRO30_DAYS} дней",
        "desc": f"До {PRO30_DAILY_LIMIT} сканов/день, анализ профиля и приоритет в очереди на {PRO30_DAYS} дней",
        "stars": 250,
        "rub": 500,
        "type": "pro30",
        "amount": PRO30_DAYS,
    },
    "pro_life": {
        "title": "💎 PRO Навсегда",
        "desc": f"До {PRO_LIFE_DAILY_LIMIT} сканов/день, анализ профиля, топ-приоритет и все будущие функции",
        "stars": 1000,
        "rub": 2000,
        "type": "pro_life",
        "amount": 0,
    },
}

MAX_IMAGE_FILE_SIZE = 15 * 1024 * 1024
SCAN_WORKERS = 3
MAX_SCAN_QUEUE_SIZE = 60

FACE_LANDMARKER_MODEL_URL = (
    "https://storage.googleapis.com/mediapipe-models/face_landmarker/"
    "face_landmarker/float16/1/face_landmarker.task"
)
FACE_LANDMARKER_MODEL_PATH = os.path.join(os.getcwd(), "face_landmarker.task")

if not TELEGRAM_BOT_TOKEN:
    raise SystemExit(
        "❌ Не задан BOT_TOKEN (или TELEGRAM_BOT_TOKEN). Укажи его в переменных окружения или файле .env."
    )
if not API_KEYS:
    raise SystemExit(
        "❌ Не задан GEMINI_API_KEYS. Укажи ключи через запятую в переменных окружения или файле .env."
    )

bot = telebot.TeleBot(TELEGRAM_BOT_TOKEN, num_threads=6)

DB_PATH = os.getenv("DB_PATH", "").strip() or os.path.join(os.getcwd(), "looksmax_bot.db")

_busy_users = set()
_busy_lock = threading.Lock()
_bot_username = None
_bot_username_lock = threading.Lock()
_admin_username_cache = None
_admin_username_lock = threading.Lock()
_awaiting_profile = {}
_profile_lock = threading.Lock()
_awaiting_battle = {}
_battle_lock = threading.Lock()
_battle_album_lock = threading.Lock()
_battle_album_buf = {}
_broadcast_state = {}
_broadcast_lock = threading.Lock()
_awaiting_model = set()
_awaiting_model_lock = threading.Lock()
_awaiting_promo = {}
_promo_wait_lock = threading.Lock()
_growth_busy = set()
_growth_busy_lock = threading.Lock()
_share_busy = set()
_share_busy_lock = threading.Lock()
_rate_lock = threading.Lock()
_rate_buckets = {}
_rate_last_prune = 0.0

_scan_queue = queue.PriorityQueue()
_scan_seq = itertools.count()


def get_today_str():
    return time.strftime("%Y-%m-%d")


def format_date_from_ts(ts):
    return time.strftime("%d.%m.%Y", time.localtime(ts))


def format_datetime_from_ts(ts):
    return time.strftime("%d.%m.%Y %H:%M", time.localtime(ts))


def format_time_left(expires_at):
    if not expires_at:
        return "бессрочно"
    rem = int(expires_at - time.time())
    if rem <= 0:
        return "истёк"
    days, rem = divmod(rem, 86400)
    hours, rem = divmod(rem, 3600)
    mins = max(1, rem // 60)
    if days > 0:
        return f"{days}д {hours}ч"
    if hours > 0:
        return f"{hours}ч {mins}м"
    return f"{mins}м"


def is_channel_bonus_enabled():
    if not CHANNEL_ID:
        return False
    valid_id = (
        CHANNEL_ID.startswith("@")
        or (CHANNEL_ID.startswith("-") and CHANNEL_ID[1:].isdigit())
        or CHANNEL_ID.isdigit()
    )
    return bool(valid_id and (CHANNEL_URL or CHANNEL_ID.startswith("@")))


def get_channel_chat_id():
    if CHANNEL_ID.startswith("-") and CHANNEL_ID[1:].isdigit():
        return int(CHANNEL_ID)
    if CHANNEL_ID.isdigit():
        return int(CHANNEL_ID)
    return CHANNEL_ID


def get_channel_url():
    if CHANNEL_URL:
        return CHANNEL_URL
    if CHANNEL_ID.startswith("@"):
        return f"https://t.me/{CHANNEL_ID.lstrip('@')}"
    return ""


def log_error(err_msg):
    print(f"[LOG] {err_msg}")


def is_admin(user_id):
    return user_id in ADMIN_IDS


def check_rate_limit(user_id, action, min_interval=1.5, max_per_min=18):
    global _rate_last_prune
    if is_admin(user_id):
        return True
    now = time.time()
    key = (user_id, action)
    with _rate_lock:
        if now - _rate_last_prune > 300:
            cutoff = now - 60.0
            stale = [k for k, ts_list in _rate_buckets.items() if not ts_list or ts_list[-1] < cutoff]
            for k in stale:
                del _rate_buckets[k]
            _rate_last_prune = now

        history = [t for t in _rate_buckets.get(key, []) if now - t < 60.0]
        if history and (now - history[-1]) < min_interval:
            _rate_buckets[key] = history
            return False
        if len(history) >= max_per_min:
            _rate_buckets[key] = history
            return False
        history.append(now)
        _rate_buckets[key] = history
        return True


def get_bot_username():
    global _bot_username
    with _bot_username_lock:
        if _bot_username:
            return _bot_username
        try:
            me = bot.get_me()
            _bot_username = me.username
        except Exception as e:
            log_error(f"Не удалось получить username бота: {e}")
        return _bot_username


def get_support_url():
    contact = ADMIN_CONTACT.strip()
    if contact:
        if contact.startswith(("http://", "https://", "tg://")):
            return contact
        return f"https://t.me/{contact.lstrip('@')}"

    if not ADMIN_IDS:
        return None

    admin_id = ADMIN_IDS[0]
    global _admin_username_cache
    with _admin_username_lock:
        if _admin_username_cache is None:
            try:
                chat = bot.get_chat(admin_id)
                _admin_username_cache = chat.username or ""
            except Exception as e:
                log_error(f"Не удалось получить username админа {admin_id}: {e}")
                return f"tg://user?id={admin_id}"
        uname = _admin_username_cache

    if uname:
        return f"https://t.me/{uname}"
    return f"tg://user?id={admin_id}"


def acquire_user(user_id):
    with _busy_lock:
        if user_id in _busy_users:
            return False
        _busy_users.add(user_id)
        return True


def release_user(user_id):
    with _busy_lock:
        _busy_users.discard(user_id)


def set_awaiting_profile(user_id, gender="m"):
    with _profile_lock:
        _awaiting_profile[user_id] = {
            "ts": time.time(),
            "gender": normalize_gender(gender),
        }


def pop_awaiting_profile(user_id):
    with _profile_lock:
        item = _awaiting_profile.pop(user_id, None)
    if not item:
        return False, False, "m"
    if (time.time() - item["ts"]) > PROFILE_WAIT_TTL:
        return False, True, item.get("gender", "m")
    return True, False, item.get("gender", "m")


def clear_awaiting_profile(user_id):
    with _profile_lock:
        return _awaiting_profile.pop(user_id, None) is not None


def is_awaiting_profile(user_id):
    with _profile_lock:
        item = _awaiting_profile.get(user_id)
    return bool(item and (time.time() - item["ts"] <= PROFILE_WAIT_TTL))


def set_awaiting_battle(user_id, gender="m", msg1=None):
    with _battle_lock:
        _awaiting_battle[user_id] = {
            "ts": time.time(),
            "gender": normalize_gender(gender),
            "msg1": msg1,
        }


def get_awaiting_battle(user_id):
    with _battle_lock:
        item = _awaiting_battle.get(user_id)
        if not item:
            return None, False
        if (time.time() - item["ts"]) > BATTLE_WAIT_TTL:
            _awaiting_battle.pop(user_id, None)
            return None, True
        return dict(item), False


def pop_awaiting_battle(user_id):
    with _battle_lock:
        item = _awaiting_battle.pop(user_id, None)
    if not item:
        return None, False
    if (time.time() - item["ts"]) > BATTLE_WAIT_TTL:
        return None, True
    return item, False


def clear_awaiting_battle(user_id):
    with _battle_lock:
        return _awaiting_battle.pop(user_id, None) is not None


def is_awaiting_battle(user_id):
    item, _ = get_awaiting_battle(user_id)
    return item is not None


def clear_broadcast_state(user_id):
    with _broadcast_lock:
        _broadcast_state.pop(user_id, None)


def set_awaiting_model(user_id):
    with _awaiting_model_lock:
        _awaiting_model.add(user_id)


def clear_awaiting_model(user_id):
    with _awaiting_model_lock:
        _awaiting_model.discard(user_id)


def is_awaiting_model(user_id):
    with _awaiting_model_lock:
        return user_id in _awaiting_model


def is_awaiting_broadcast(user_id):
    with _broadcast_lock:
        return _broadcast_state.get(user_id, {}).get("step") == "await_content"


def set_awaiting_promo(user_id):
    with _promo_wait_lock:
        _awaiting_promo[user_id] = time.time()


def clear_awaiting_promo(user_id):
    with _promo_wait_lock:
        return _awaiting_promo.pop(user_id, None) is not None


def is_awaiting_promo(user_id):
    with _promo_wait_lock:
        ts = _awaiting_promo.get(user_id)
    return bool(ts is not None and (time.time() - ts <= PROMO_WAIT_TTL))


def clear_pending_modes(user_id):
    clear_awaiting_profile(user_id)
    clear_awaiting_battle(user_id)
    clear_broadcast_state(user_id)
    clear_awaiting_model(user_id)
    clear_awaiting_promo(user_id)


def get_db():
    return sqlite3.connect(DB_PATH, timeout=20)


@contextmanager
def db_conn():
    conn = get_db()
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def init_db():
    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute("PRAGMA journal_mode=WAL")

        cursor.execute(
            f"""
            CREATE TABLE IF NOT EXISTS users (
                user_id INTEGER PRIMARY KEY,
                username TEXT DEFAULT '',
                first_name TEXT DEFAULT '',
                free_limit INTEGER DEFAULT {DEFAULT_FREE_LIMIT},
                is_premium INTEGER DEFAULT 0,
                pro_tier INTEGER DEFAULT 0,
                pro_until INTEGER DEFAULT 0,
                is_adult INTEGER DEFAULT 0,
                is_banned INTEGER DEFAULT 0,
                referred_by INTEGER DEFAULT NULL,
                referrals_count INTEGER DEFAULT 0,
                daily_used INTEGER DEFAULT 0,
                daily_reset_date TEXT DEFAULT '',
                scans_count INTEGER DEFAULT 0,
                best_score REAL DEFAULT 0.0,
                last_score REAL DEFAULT 0.0,
                prev_score REAL DEFAULT 0.0,
                active_promo TEXT DEFAULT '',
                ref_milestone_claimed INTEGER DEFAULT 0,
                channel_bonus_claimed INTEGER DEFAULT 0,
                gender TEXT DEFAULT 'm',
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """
        )

        cursor.execute(
            """
            CREATE TABLE IF NOT EXISTS photo_cache (
                photo_hash TEXT PRIMARY KEY,
                scores_text TEXT,
                full_text TEXT,
                card_image BLOB DEFAULT NULL,
                card_file_id TEXT DEFAULT '',
                growth_plan TEXT DEFAULT '',
                share_file_id TEXT DEFAULT '',
                metrics_json TEXT DEFAULT '',
                source_file_id TEXT DEFAULT '',
                last_used TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """
        )
        cursor.execute(
            "CREATE INDEX IF NOT EXISTS idx_photo_cache_last_used ON photo_cache(last_used DESC)"
        )

        cursor.execute(
            """
            CREATE TABLE IF NOT EXISTS payment_requests (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                plan_id TEXT NOT NULL,
                promo_code TEXT DEFAULT '',
                rub_amount INTEGER DEFAULT 0,
                status TEXT DEFAULT 'pending',
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """
        )

        cursor.execute(
            """
            CREATE TABLE IF NOT EXISTS crypto_payments (
                invoice_id INTEGER PRIMARY KEY,
                user_id INTEGER NOT NULL,
                plan_id TEXT NOT NULL,
                promo_code TEXT DEFAULT '',
                rub_amount INTEGER NOT NULL,
                status TEXT DEFAULT 'active',
                pay_url TEXT DEFAULT '',
                expires_at INTEGER DEFAULT 0,
                created_at INTEGER DEFAULT 0,
                paid_at INTEGER DEFAULT 0
            )
            """
        )
        cursor.execute(
            "CREATE INDEX IF NOT EXISTS idx_crypto_payments_status ON crypto_payments(status, expires_at)"
        )
        cursor.execute(
            "CREATE INDEX IF NOT EXISTS idx_crypto_payments_user ON crypto_payments(user_id, status)"
        )

        cursor.execute(
            """
            CREATE TABLE IF NOT EXISTS stars_payments (
                charge_id TEXT PRIMARY KEY,
                user_id INTEGER NOT NULL,
                plan_id TEXT NOT NULL,
                amount INTEGER NOT NULL,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """
        )

        cursor.execute(
            """
            CREATE TABLE IF NOT EXISTS bot_settings (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            )
            """
        )

        cursor.execute(
            """
            CREATE TABLE IF NOT EXISTS promocodes (
                code TEXT PRIMARY KEY,
                promo_type TEXT NOT NULL,
                value INTEGER NOT NULL,
                max_uses INTEGER DEFAULT 0,
                used_count INTEGER DEFAULT 0,
                expires_at INTEGER DEFAULT 0,
                is_active INTEGER DEFAULT 1,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """
        )

        cursor.execute(
            """
            CREATE TABLE IF NOT EXISTS promo_uses (
                code TEXT NOT NULL,
                user_id INTEGER NOT NULL,
                used_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                PRIMARY KEY (code, user_id)
            )
            """
        )

        cursor.execute(
            """
            CREATE TABLE IF NOT EXISTS daily_stats (
                day TEXT PRIMARY KEY,
                scans INTEGER DEFAULT 0
            )
            """
        )


def load_active_models_from_db():
    global _active_models
    try:
        with db_conn() as conn:
            c = conn.cursor()
            c.execute("SELECT value FROM bot_settings WHERE key = 'gemini_models'")
            row = c.fetchone()
        if row and row[0].strip():
            parsed = [m.strip() for m in row[0].split(",") if m.strip()]
            if parsed:
                with _models_lock:
                    _active_models = parsed
                print(f"[Models] Загружены из БД: {', '.join(parsed)}")
                return
    except Exception as e:
        log_error(f"Не удалось загрузить модели из БД: {e}")

    with _models_lock:
        print(f"[Models] Активные модели: {', '.join(_active_models)}")


def get_active_models():
    with _models_lock:
        return list(_active_models)


def parse_models_input(raw_text):
    tokens = [t.strip() for t in re.split(r"[,;\s]+", (raw_text or "").strip()) if t.strip()]
    valid = []
    for tok in tokens:
        if re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._\-]{1,63}", tok) and tok not in valid:
            valid.append(tok)
    return valid


def set_active_models(models_list):
    global _active_models
    cleaned = [m.strip() for m in models_list if m.strip()]
    if not cleaned:
        cleaned = list(DEFAULT_MODELS)

    with db_conn() as conn:
        conn.cursor().execute(
            "INSERT OR REPLACE INTO bot_settings (key, value) VALUES ('gemini_models', ?)",
            (",".join(cleaned),),
        )

    with _models_lock:
        _active_models = list(cleaned)

    reset_model_cooldowns()
    return cleaned


def reset_model_cooldowns():
    with _key_lock:
        _model_blocked_until.clear()
        _pair_blocked_until.clear()


def ensure_user_columns():
    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute("PRAGMA table_info(users)")
        existing = {row[1] for row in cursor.fetchall()}

        migrations = [
            ("username", "TEXT DEFAULT ''"),
            ("first_name", "TEXT DEFAULT ''"),
            ("is_adult", "INTEGER DEFAULT 0"),
            ("is_banned", "INTEGER DEFAULT 0"),
            ("referred_by", "INTEGER DEFAULT NULL"),
            ("referrals_count", "INTEGER DEFAULT 0"),
            ("daily_used", "INTEGER DEFAULT 0"),
            ("daily_reset_date", "TEXT DEFAULT ''"),
            ("pro_tier", "INTEGER DEFAULT 0"),
            ("pro_until", "INTEGER DEFAULT 0"),
            ("scans_count", "INTEGER DEFAULT 0"),
            ("best_score", "REAL DEFAULT 0.0"),
            ("last_score", "REAL DEFAULT 0.0"),
            ("prev_score", "REAL DEFAULT 0.0"),
            ("active_promo", "TEXT DEFAULT ''"),
            ("ref_milestone_claimed", "INTEGER DEFAULT 0"),
            ("channel_bonus_claimed", "INTEGER DEFAULT 0"),
            ("gender", "TEXT DEFAULT 'm'"),
        ]
        for col, col_def in migrations:
            if col not in existing:
                cursor.execute(f"ALTER TABLE users ADD COLUMN {col} {col_def}")

        cursor.execute(
            """
            UPDATE users
            SET pro_tier = 2, pro_until = 0
            WHERE is_premium = 1 AND COALESCE(pro_tier, 0) = 0
            """
        )

        cursor.execute("PRAGMA table_info(photo_cache)")
        cache_cols = {row[1] for row in cursor.fetchall()}
        cache_migrations = [
            ("card_image", "BLOB DEFAULT NULL"),
            ("card_file_id", "TEXT DEFAULT ''"),
            ("growth_plan", "TEXT DEFAULT ''"),
            ("share_file_id", "TEXT DEFAULT ''"),
            ("metrics_json", "TEXT DEFAULT ''"),
            ("source_file_id", "TEXT DEFAULT ''"),
        ]
        for col, col_def in cache_migrations:
            if col not in cache_cols:
                cursor.execute(f"ALTER TABLE photo_cache ADD COLUMN {col} {col_def}")

        cursor.execute(
            "CREATE INDEX IF NOT EXISTS idx_photo_cache_last_used ON photo_cache(last_used DESC)"
        )

        cursor.execute("PRAGMA table_info(payment_requests)")
        pay_cols = {row[1] for row in cursor.fetchall()}
        if "promo_code" not in pay_cols:
            cursor.execute(
                "ALTER TABLE payment_requests ADD COLUMN promo_code TEXT DEFAULT ''"
            )
        if "rub_amount" not in pay_cols:
            cursor.execute(
                "ALTER TABLE payment_requests ADD COLUMN rub_amount INTEGER DEFAULT 0"
            )


def ensure_user(user_id, username="", first_name=""):
    uname = (username or "").lstrip("@").lower()
    fname = (first_name or "")[:64]
    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute(
            """
            INSERT OR IGNORE INTO users (
                user_id, username, first_name, free_limit, is_premium,
                pro_tier, pro_until, is_adult, is_banned, referrals_count, gender
            )
            VALUES (?, ?, ?, ?, 0, 0, 0, 0, 0, 0, 'm')
            """,
            (user_id, uname, fname, DEFAULT_FREE_LIMIT),
        )
        if uname or fname:
            cursor.execute(
                """
                UPDATE users
                SET username = CASE WHEN ? != '' THEN ? ELSE username END,
                    first_name = CASE WHEN ? != '' THEN ? ELSE first_name END
                WHERE user_id = ?
                """,
                (uname, uname, fname, fname, user_id),
            )


def touch_user(tg_user):
    if not tg_user:
        return
    ensure_user(
        tg_user.id,
        username=getattr(tg_user, "username", "") or "",
        first_name=getattr(tg_user, "first_name", "") or "",
    )


def get_user_gender(user_id):
    with db_conn() as conn:
        c = conn.cursor()
        c.execute("SELECT COALESCE(gender, 'm') FROM users WHERE user_id = ?", (user_id,))
        row = c.fetchone()
    return normalize_gender(row[0] if row else "m")


def set_user_gender(user_id, gender):
    g = normalize_gender(gender)
    ensure_user(user_id)
    with db_conn() as conn:
        conn.cursor().execute(
            "UPDATE users SET gender = ? WHERE user_id = ?",
            (g, user_id),
        )
    return g


def register_user_if_new(tg_user, referrer_id=None):
    user_id = tg_user.id
    uname = (getattr(tg_user, "username", "") or "").lstrip("@").lower()
    fname = (getattr(tg_user, "first_name", "") or "")[:64]
    now = int(time.time())

    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute("SELECT 1 FROM users WHERE user_id = ?", (user_id,))
        if cursor.fetchone():
            cursor.execute(
                """
                UPDATE users
                SET username = CASE WHEN ? != '' THEN ? ELSE username END,
                    first_name = CASE WHEN ? != '' THEN ? ELSE first_name END
                WHERE user_id = ?
                """,
                (uname, uname, fname, fname, user_id),
            )
            return None, ""

        valid_referrer = None
        if referrer_id and referrer_id != user_id:
            cursor.execute(
                "SELECT 1 FROM users WHERE user_id = ? AND COALESCE(is_banned, 0) = 0",
                (referrer_id,),
            )
            if cursor.fetchone():
                valid_referrer = referrer_id

        cursor.execute(
            """
            INSERT OR IGNORE INTO users (
                user_id, username, first_name, free_limit, is_premium,
                pro_tier, pro_until, is_adult, is_banned, referred_by, referrals_count, gender
            )
            VALUES (?, ?, ?, ?, 0, 0, 0, 0, 0, ?, 0, 'm')
            """,
            (user_id, uname, fname, DEFAULT_FREE_LIMIT, valid_referrer),
        )

        if cursor.rowcount > 0 and valid_referrer is not None:
            cursor.execute(
                """
                UPDATE users
                SET free_limit = free_limit + ?,
                    referrals_count = COALESCE(referrals_count, 0) + 1
                WHERE user_id = ?
                """,
                (REFERRAL_BONUS, valid_referrer),
            )
            cursor.execute(
                """
                SELECT COALESCE(referrals_count, 0), COALESCE(ref_milestone_claimed, 0),
                       COALESCE(pro_tier, 0), COALESCE(pro_until, 0)
                FROM users WHERE user_id = ?
                """,
                (valid_referrer,),
            )
            row = cursor.fetchone()
            milestone_notes = []
            if row:
                new_refs, claimed, cur_tier, cur_until = row
                new_claimed = claimed
                for req_refs, pro_days in REF_MILESTONES:
                    if new_refs >= req_refs and claimed < req_refs:
                        new_claimed = req_refs
                        if cur_tier >= 2:
                            bonus_scans = max(2, pro_days)
                            cursor.execute(
                                "UPDATE users SET free_limit = free_limit + ? WHERE user_id = ?",
                                (bonus_scans, valid_referrer),
                            )
                            milestone_notes.append(
                                f"🏆 Ступень <b>{req_refs} друзей</b>: +{bonus_scans} доп. сканов (у тебя уже PRO Навсегда)!"
                            )
                        else:
                            base = max(now, cur_until) if cur_tier == 1 else now
                            cur_until = base + pro_days * 86400
                            cur_tier = 1
                            cursor.execute(
                                "UPDATE users SET is_premium = 1, pro_tier = 1, pro_until = ? WHERE user_id = ?",
                                (cur_until, valid_referrer),
                            )
                            milestone_notes.append(
                                f"🏆 Ступень <b>{req_refs} друзей</b>: активирован <b>PRO на {pro_days} дн.</b> (до {format_date_from_ts(cur_until)})!"
                            )
                if new_claimed > claimed:
                    cursor.execute(
                        "UPDATE users SET ref_milestone_claimed = ? WHERE user_id = ?",
                        (new_claimed, valid_referrer),
                    )
            return valid_referrer, "\n".join(milestone_notes)

        return None, ""


def resolve_target_user(identifier):
    raw = (identifier or "").strip()
    if not raw:
        return None
    if raw.isdigit():
        return int(raw)

    uname = raw.lstrip("@").lower()
    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute(
            "SELECT user_id FROM users WHERE LOWER(username) = ? LIMIT 1",
            (uname,),
        )
        row = cursor.fetchone()
        return row[0] if row else None


def is_user_banned(user_id):
    if is_admin(user_id):
        return False
    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute(
            "SELECT COALESCE(is_banned, 0) FROM users WHERE user_id = ?",
            (user_id,),
        )
        row = cursor.fetchone()
        return bool(row and row[0])


def record_user_scan_stats(user_id, score=None, scan_increment=1):
    today = get_today_str()
    delta = None
    inc = max(1, int(scan_increment))
    with db_conn() as conn:
        cursor = conn.cursor()
        if score is not None:
            new_score = round(float(score), 1)
            cursor.execute(
                "SELECT COALESCE(last_score, 0.0), COALESCE(best_score, 0.0) FROM users WHERE user_id = ?",
                (user_id,),
            )
            row = cursor.fetchone()
            prev_last = float(row[0]) if row else 0.0
            if prev_last <= 0.0 and row and float(row[1]) > 0.0:
                prev_last = float(row[1])
            if prev_last > 0.0:
                delta = round(new_score - prev_last, 1)

            cursor.execute(
                """
                UPDATE users
                SET scans_count = COALESCE(scans_count, 0) + ?,
                    prev_score = ?,
                    last_score = ?,
                    best_score = MAX(COALESCE(best_score, 0.0), ?)
                WHERE user_id = ?
                """,
                (inc, prev_last, new_score, new_score, user_id),
            )
        else:
            cursor.execute(
                "UPDATE users SET scans_count = COALESCE(scans_count, 0) + ? WHERE user_id = ?",
                (inc, user_id),
            )
        cursor.execute(
            """
            INSERT INTO daily_stats (day, scans) VALUES (?, ?)
            ON CONFLICT(day) DO UPDATE SET scans = scans + ?
            """,
            (today, inc, inc),
        )
    return delta


def get_user_profile_stats(user_id):
    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute(
            """
            SELECT COALESCE(scans_count, 0), COALESCE(best_score, 0.0),
                   COALESCE(referrals_count, 0), COALESCE(username, ''),
                   COALESCE(first_name, ''), COALESCE(is_banned, 0),
                   COALESCE(last_score, 0.0), COALESCE(prev_score, 0.0)
            FROM users WHERE user_id = ?
            """,
            (user_id,),
        )
        row = cursor.fetchone()
        if not row:
            return 0, 0.0, 0, "", "", False, 0.0, 0.0
        return row[0], row[1], row[2], row[3], row[4], bool(row[5]), row[6], row[7]


def get_user_access(user_id):
    now = int(time.time())
    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute(
            """
            SELECT free_limit, COALESCE(pro_tier, 0), COALESCE(pro_until, 0), is_adult, is_premium
            FROM users WHERE user_id = ?
            """,
            (user_id,),
        )
        row = cursor.fetchone()

        if not row:
            cursor.execute(
                """
                INSERT OR IGNORE INTO users (
                    user_id, free_limit, is_premium, pro_tier, pro_until, is_adult, referrals_count, gender
                )
                VALUES (?, ?, 0, 0, 0, 0, 0, 'm')
                """,
                (user_id, DEFAULT_FREE_LIMIT),
            )
            return DEFAULT_FREE_LIMIT, 0, 0, False

        free_limit, pro_tier, pro_until, is_adult, is_premium = row

        if pro_tier == 0 and is_premium == 1:
            pro_tier = 2
            cursor.execute(
                "UPDATE users SET pro_tier = 2, pro_until = 0 WHERE user_id = ?",
                (user_id,),
            )

        if pro_tier == 1 and pro_until > 0 and now >= pro_until:
            pro_tier = 0
            pro_until = 0
            cursor.execute(
                "UPDATE users SET is_premium = 0, pro_tier = 0, pro_until = 0 WHERE user_id = ?",
                (user_id,),
            )

        return free_limit, pro_tier, pro_until, bool(is_adult)


def get_pro_daily_limit_for_tier(pro_tier):
    if pro_tier >= 2:
        return PRO_LIFE_DAILY_LIMIT
    if pro_tier == 1:
        return PRO30_DAILY_LIMIT
    return 0


def get_pro_remaining_today(user_id, pro_tier):
    limit = get_pro_daily_limit_for_tier(pro_tier)
    if limit <= 0:
        return 0
    today = get_today_str()
    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute(
            "SELECT daily_used, daily_reset_date FROM users WHERE user_id = ?",
            (user_id,),
        )
        row = cursor.fetchone()
        if not row or (row[1] or "") != today:
            return limit
        return max(0, limit - (row[0] or 0))


def set_user_adult(user_id):
    ensure_user(user_id)
    with db_conn() as conn:
        conn.cursor().execute(
            "UPDATE users SET is_adult = 1 WHERE user_id = ?",
            (user_id,),
        )


def apply_plan_to_user(user_id, plan_id):
    plan = PLANS[plan_id]
    ensure_user(user_id)
    now = int(time.time())

    with db_conn() as conn:
        cursor = conn.cursor()
        if plan["type"] == "pro_life":
            cursor.execute(
                "UPDATE users SET is_premium = 1, pro_tier = 2, pro_until = 0 WHERE user_id = ?",
                (user_id,),
            )
        elif plan["type"] == "pro30":
            cursor.execute(
                "SELECT COALESCE(pro_tier, 0), COALESCE(pro_until, 0) FROM users WHERE user_id = ?",
                (user_id,),
            )
            row = cursor.fetchone()
            cur_tier = row[0] if row else 0
            cur_until = row[1] if row else 0
            if cur_tier >= 2:
                return
            base = max(now, cur_until) if cur_tier == 1 else now
            new_until = base + plan["amount"] * 86400
            cursor.execute(
                "UPDATE users SET is_premium = 1, pro_tier = 1, pro_until = ? WHERE user_id = ?",
                (new_until, user_id),
            )
        else:
            cursor.execute(
                "UPDATE users SET free_limit = free_limit + ? WHERE user_id = ?",
                (plan["amount"], user_id),
            )


def save_crypto_invoice(invoice_id, user_id, plan_id, promo_code, rub_amount, pay_url, expires_at):
    now = int(time.time())
    with db_conn() as conn:
        conn.cursor().execute(
            """
            INSERT OR REPLACE INTO crypto_payments (
                invoice_id, user_id, plan_id, promo_code, rub_amount,
                status, pay_url, expires_at, created_at, paid_at
            )
            VALUES (?, ?, ?, ?, ?, 'active', ?, ?, ?, 0)
            """,
            (
                int(invoice_id),
                int(user_id),
                plan_id,
                (promo_code or "").strip().upper(),
                int(rub_amount),
                pay_url or "",
                int(expires_at),
                now,
            ),
        )


def get_crypto_invoice_by_id(invoice_id):
    with db_conn() as conn:
        c = conn.cursor()
        c.execute(
            """
            SELECT invoice_id, user_id, plan_id, COALESCE(promo_code, ''), rub_amount,
                   status, COALESCE(pay_url, ''), COALESCE(expires_at, 0)
            FROM crypto_payments
            WHERE invoice_id = ?
            """,
            (int(invoice_id),),
        )
        return c.fetchone()


def get_active_crypto_invoices_for_user(user_id):
    now = int(time.time())
    with db_conn() as conn:
        c = conn.cursor()
        c.execute(
            """
            SELECT invoice_id, plan_id, COALESCE(promo_code, ''), rub_amount,
                   COALESCE(pay_url, ''), COALESCE(expires_at, 0)
            FROM crypto_payments
            WHERE user_id = ? AND status = 'active' AND expires_at > ?
            ORDER BY created_at DESC
            """,
            (user_id, now),
        )
        return c.fetchall()


def fetch_active_crypto_invoices_for_poller():
    with db_conn() as conn:
        c = conn.cursor()
        c.execute(
            """
            SELECT invoice_id, COALESCE(expires_at, 0)
            FROM crypto_payments
            WHERE status = 'active'
            ORDER BY created_at ASC
            LIMIT 200
            """
        )
        return c.fetchall()


def mark_crypto_invoice_paid(invoice_id):
    now = int(time.time())
    with db_conn() as conn:
        c = conn.cursor()
        c.execute(
            """
            SELECT user_id, plan_id, COALESCE(promo_code, ''), rub_amount
            FROM crypto_payments
            WHERE invoice_id = ? AND status = 'active'
            """,
            (int(invoice_id),),
        )
        row = c.fetchone()
        if not row:
            return None
        c.execute(
            """
            UPDATE crypto_payments
            SET status = 'paid', paid_at = ?
            WHERE invoice_id = ? AND status = 'active'
            """,
            (now, int(invoice_id)),
        )
        if c.rowcount == 0:
            return None
        return row[0], row[1], row[2], row[3]


def mark_crypto_invoice_status(invoice_id, new_status):
    with db_conn() as conn:
        c = conn.cursor()
        c.execute(
            "UPDATE crypto_payments SET status = ? WHERE invoice_id = ? AND status = 'active'",
            (new_status, int(invoice_id)),
        )
        return c.rowcount > 0


def record_stars_payment(charge_id, user_id, plan_id, amount):
    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute(
            """
            INSERT OR IGNORE INTO stars_payments (charge_id, user_id, plan_id, amount)
            VALUES (?, ?, ?, ?)
            """,
            (charge_id, user_id, plan_id, amount),
        )
        return cursor.rowcount > 0


def try_consume_scan(user_id):
    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute(
            """
            UPDATE users
            SET free_limit = free_limit - 1
            WHERE user_id = ?
              AND COALESCE(pro_tier, 0) = 0
              AND free_limit > 0
            """,
            (user_id,),
        )
        return cursor.rowcount > 0


def try_consume_extra_scan(user_id):
    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute(
            """
            UPDATE users
            SET free_limit = free_limit - 1
            WHERE user_id = ?
              AND free_limit > 0
            """,
            (user_id,),
        )
        return cursor.rowcount > 0


def refund_scan(user_id, count=1):
    amt = max(1, int(count))
    with db_conn() as conn:
        conn.cursor().execute(
            "UPDATE users SET free_limit = free_limit + ? WHERE user_id = ?",
            (amt, user_id),
        )


def try_consume_pro_scan(user_id, daily_limit):
    today = get_today_str()
    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute(
            """
            UPDATE users
            SET daily_used = CASE
                    WHEN COALESCE(daily_reset_date, '') = ? THEN COALESCE(daily_used, 0) + 1
                    ELSE 1
                END,
                daily_reset_date = ?
            WHERE user_id = ?
              AND COALESCE(pro_tier, 0) > 0
              AND (COALESCE(daily_reset_date, '') != ? OR COALESCE(daily_used, 0) < ?)
            """,
            (today, today, user_id, today, daily_limit),
        )
        return cursor.rowcount > 0


def refund_pro_scan(user_id, count=1):
    today = get_today_str()
    amt = max(1, int(count))
    with db_conn() as conn:
        conn.cursor().execute(
            """
            UPDATE users
            SET daily_used = MAX(0, COALESCE(daily_used, 0) - ?)
            WHERE user_id = ? AND COALESCE(daily_reset_date, '') = ?
            """,
            (amt, user_id, today),
        )


def try_consume_battle_scans(user_id, pro_tier, daily_limit, cost=BATTLE_SCAN_COST):
    cost = max(1, int(cost))
    today = get_today_str()
    with db_conn() as conn:
        c = conn.cursor()
        if pro_tier <= 0:
            c.execute(
                """
                UPDATE users
                SET free_limit = free_limit - ?
                WHERE user_id = ?
                  AND COALESCE(pro_tier, 0) = 0
                  AND free_limit >= ?
                """,
                (cost, user_id, cost),
            )
            if c.rowcount > 0:
                return True, 0, cost
            return False, 0, 0

        c.execute(
            "SELECT free_limit, COALESCE(daily_used, 0), COALESCE(daily_reset_date, '') FROM users WHERE user_id = ?",
            (user_id,),
        )
        row = c.fetchone()
        if not row:
            return False, 0, 0
        free_lim, d_used, d_date = row
        used_today = d_used if d_date == today else 0
        pro_rem = max(0, daily_limit - used_today)
        take_pro = min(pro_rem, cost)
        take_extra = cost - take_pro
        if free_lim < take_extra:
            return False, 0, 0

        c.execute(
            """
            UPDATE users
            SET daily_used = CASE
                    WHEN COALESCE(daily_reset_date, '') = ? THEN COALESCE(daily_used, 0) + ?
                    ELSE ?
                END,
                daily_reset_date = CASE WHEN ? > 0 THEN ? ELSE daily_reset_date END,
                free_limit = free_limit - ?
            WHERE user_id = ?
              AND COALESCE(pro_tier, 0) > 0
              AND free_limit >= ?
              AND (CASE WHEN COALESCE(daily_reset_date, '') = ? THEN COALESCE(daily_used, 0) ELSE 0 END) + ? <= ?
            """,
            (
                today,
                take_pro,
                take_pro,
                take_pro,
                today,
                take_extra,
                user_id,
                take_extra,
                today,
                take_pro,
                daily_limit,
            ),
        )
        if c.rowcount > 0:
            return True, take_pro, take_extra
        return False, 0, 0


def refund_battle_scans(user_id, consumed_pro, consumed_extra):
    if consumed_pro > 0:
        refund_pro_scan(user_id, count=consumed_pro)
    if consumed_extra > 0:
        refund_scan(user_id, count=consumed_extra)


def cache_get(photo_hash):
    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute(
            """
            SELECT scores_text, full_text, card_image, COALESCE(card_file_id, ''),
                   COALESCE(growth_plan, ''), COALESCE(share_file_id, ''),
                   COALESCE(metrics_json, ''), COALESCE(source_file_id, '')
            FROM photo_cache WHERE photo_hash = ?
            """,
            (photo_hash,),
        )
        row = cursor.fetchone()
        if not row:
            return None
        cursor.execute(
            "UPDATE photo_cache SET last_used = CURRENT_TIMESTAMP WHERE photo_hash = ?",
            (photo_hash,),
        )
        return row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[7]


def cache_put(
    photo_hash,
    scores_text,
    full_text,
    card_image=None,
    card_file_id="",
    metrics_json="",
    source_file_id="",
):
    stored_blob = None if card_file_id else card_image
    with db_conn() as conn:
        cursor = conn.cursor()
        cursor.execute(
            """
            INSERT OR REPLACE INTO photo_cache (
                photo_hash, scores_text, full_text, card_image, card_file_id,
                growth_plan, share_file_id, metrics_json, source_file_id, last_used
            )
            VALUES (
                ?, ?, ?, ?, ?,
                COALESCE((SELECT growth_plan FROM photo_cache WHERE photo_hash = ?), ''),
                COALESCE((SELECT share_file_id FROM photo_cache WHERE photo_hash = ?), ''),
                ?,
                CASE WHEN ? != '' THEN ? ELSE COALESCE((SELECT source_file_id FROM photo_cache WHERE photo_hash = ?), '') END,
                CURRENT_TIMESTAMP
            )
            """,
            (
                photo_hash,
                scores_text,
                full_text,
                stored_blob,
                card_file_id or "",
                photo_hash,
                photo_hash,
                metrics_json or "",
                source_file_id or "",
                source_file_id or "",
                photo_hash,
            ),
        )
        cursor.execute(
            """
            DELETE FROM photo_cache
            WHERE photo_hash NOT IN (
                SELECT photo_hash
                FROM photo_cache
                ORDER BY last_used DESC
                LIMIT 400
            )
            """
        )


def cache_set_growth_plan(photo_hash, growth_plan):
    with db_conn() as conn:
        conn.cursor().execute(
            "UPDATE photo_cache SET growth_plan = ?, last_used = CURRENT_TIMESTAMP WHERE photo_hash = ?",
            (growth_plan, photo_hash),
        )


def cache_set_share_file_id(photo_hash, share_file_id):
    with db_conn() as conn:
        conn.cursor().execute(
            "UPDATE photo_cache SET share_file_id = ?, last_used = CURRENT_TIMESTAMP WHERE photo_hash = ?",
            (share_file_id, photo_hash),
        )


def cache_set_card_file_id(photo_hash, card_file_id):
    if not card_file_id:
        return
    with db_conn() as conn:
        conn.cursor().execute(
            "UPDATE photo_cache SET card_file_id = ?, card_image = NULL, last_used = CURRENT_TIMESTAMP WHERE photo_hash = ?",
            (card_file_id, photo_hash),
        )


def calc_discounted_price(amount, discount_pct):
    if discount_pct <= 0:
        return int(amount)
    return max(1, int(round(amount * (100 - discount_pct) / 100.0)))


def parse_promo_reward_token(tok):
    s = (tok or "").strip().lower()
    m_pct = re.fullmatch(r"(\d{1,2})%", s)
    if m_pct:
        val = int(m_pct.group(1))
        return ("discount", val) if 1 <= val <= 90 else (None, 0)

    m_scans = re.fullmatch(r"(\d{1,4})(?:скан(?:а|ов)?|scans?|s)", s)
    if m_scans:
        val = int(m_scans.group(1))
        return ("scans", val) if 1 <= val <= 1000 else (None, 0)

    m_pro = re.fullmatch(r"(\d{1,4})(?:pro|про|дн(?:я|ей)?|d)", s)
    if m_pro:
        val = int(m_pro.group(1))
        return ("pro_days", val) if 1 <= val <= 3650 else (None, 0)

    return None, 0


def parse_promo_duration_token(tok):
    s = (tok or "").strip().lower()
    m = re.fullmatch(r"(\d{1,5})(м|мин|m|min|ч|час|часа|часов|h|hr|д|дн|дня|дней|d|day|days)", s)
    if not m:
        return None
    val = int(m.group(1))
    unit = m.group(2)
    if val <= 0:
        return None
    if unit in ("м", "мин", "m", "min"):
        secs = val * 60
    elif unit in ("ч", "час", "часа", "часов", "h", "hr"):
        secs = val * 3600
    else:
        secs = val * 86400
    return min(secs, 3650 * 86400)


def format_promo_reward(promo_type, value):
    if promo_type == "discount":
        return f"скидка {value}%"
    if promo_type == "scans":
        return f"+{value} сканов"
    return f"PRO на {value} дн."


def create_promocode_db(code, promo_type, value, max_uses=0, duration_sec=0):
    code_up = code.strip().upper()
    expires_at = int(time.time()) + duration_sec if duration_sec > 0 else 0
    with db_conn() as conn:
        c = conn.cursor()
        c.execute("DELETE FROM promo_uses WHERE code = ?", (code_up,))
        c.execute(
            """
            INSERT OR REPLACE INTO promocodes (
                code, promo_type, value, max_uses, used_count, expires_at, is_active, created_at
            )
            VALUES (?, ?, ?, ?, 0, ?, 1, CURRENT_TIMESTAMP)
            """,
            (code_up, promo_type, int(value), int(max_uses), expires_at),
        )
    return expires_at


def deactivate_promocode_db(code):
    code_up = code.strip().upper()
    with db_conn() as conn:
        c = conn.cursor()
        c.execute("UPDATE promocodes SET is_active = 0 WHERE code = ?", (code_up,))
        updated = c.rowcount > 0
        c.execute("UPDATE users SET active_promo = '' WHERE active_promo = ?", (code_up,))
        return updated


def list_promocodes_db(limit=25):
    with db_conn() as conn:
        c = conn.cursor()
        c.execute(
            """
            SELECT code, promo_type, value, max_uses, used_count, expires_at, is_active
            FROM promocodes
            ORDER BY is_active DESC, created_at DESC
            LIMIT ?
            """,
            (limit,),
        )
        return c.fetchall()


def validate_discount_promo_for_user(user_id, code, ignore_active_crypto=False):
    code_up = (code or "").strip().upper()
    if not code_up:
        return 0
    now = int(time.time())
    with db_conn() as conn:
        c = conn.cursor()
        c.execute(
            """
            SELECT promo_type, value, max_uses, used_count, expires_at, is_active
            FROM promocodes WHERE code = ?
            """,
            (code_up,),
        )
        row = c.fetchone()
        if not row:
            return 0
        ptype, val, max_uses, used_cnt, exp_at, is_act = row
        if not is_act or ptype != "discount":
            return 0
        if exp_at > 0 and now >= exp_at:
            return 0
        if max_uses > 0 and used_cnt >= max_uses:
            return 0
        c.execute("SELECT 1 FROM promo_uses WHERE code = ? AND user_id = ?", (code_up, user_id))
        if c.fetchone():
            return 0
        if not ignore_active_crypto:
            c.execute(
                """
                SELECT 1 FROM crypto_payments
                WHERE user_id = ?
                  AND promo_code = ?
                  AND status = 'active'
                  AND expires_at > ?
                LIMIT 1
                """,
                (user_id, code_up, now),
            )
            if c.fetchone():
                return 0
        return int(val)


def get_promo_discount_value_raw(code):
    code_up = (code or "").strip().upper()
    if not code_up:
        return 0
    with db_conn() as conn:
        c = conn.cursor()
        c.execute("SELECT promo_type, value FROM promocodes WHERE code = ?", (code_up,))
        row = c.fetchone()
        if row and row[0] == "discount":
            return int(row[1])
        return 0


def get_user_active_discount(user_id, ignore_active_crypto=False):
    now = int(time.time())
    with db_conn() as conn:
        c = conn.cursor()
        c.execute("SELECT COALESCE(active_promo, '') FROM users WHERE user_id = ?", (user_id,))
        row = c.fetchone()
        code = (row[0] if row else "").strip().upper()
    if not code:
        return "", 0
    pct = validate_discount_promo_for_user(
        user_id, code, ignore_active_crypto=ignore_active_crypto
    )
    if pct <= 0:
        with db_conn() as conn:
            c = conn.cursor()
            c.execute(
                """
                SELECT 1 FROM crypto_payments
                WHERE user_id = ? AND promo_code = ? AND status = 'active' AND expires_at > ?
                LIMIT 1
                """,
                (user_id, code, now),
            )
            if not c.fetchone():
                c.execute("UPDATE users SET active_promo = '' WHERE user_id = ?", (user_id,))
        return "", 0
    return code, pct


def get_plan_pricing(plan_id, user_id=None, explicit_promo=None, ignore_active_crypto=False):
    plan = PLANS[plan_id]
    promo_code, pct = "", 0
    if explicit_promo is not None:
        if explicit_promo and user_id is not None:
            pct = validate_discount_promo_for_user(
                user_id, explicit_promo, ignore_active_crypto=ignore_active_crypto
            )
            if pct > 0:
                promo_code = explicit_promo.strip().upper()
    elif user_id is not None:
        promo_code, pct = get_user_active_discount(
            user_id, ignore_active_crypto=ignore_active_crypto
        )

    return {
        "stars": calc_discounted_price(plan["stars"], pct),
        "rub": calc_discounted_price(plan["rub"], pct),
        "orig_stars": plan["stars"],
        "orig_rub": plan["rub"],
        "promo_code": promo_code,
        "discount_pct": pct,
    }


def consume_discount_promo(user_id, code):
    code_up = (code or "").strip().upper()
    if not code_up:
        return
    with db_conn() as conn:
        c = conn.cursor()
        c.execute("INSERT OR IGNORE INTO promo_uses (code, user_id) VALUES (?, ?)", (code_up, user_id))
        if c.rowcount > 0:
            c.execute("UPDATE promocodes SET used_count = used_count + 1 WHERE code = ?", (code_up,))
        c.execute("UPDATE users SET active_promo = '' WHERE user_id = ? AND active_promo = ?", (user_id, code_up))


def activate_promocode_for_user(user_id, raw_code):
    code = (raw_code or "").strip().upper()
    if not re.fullmatch(r"[A-Z0-9_\-]{2,24}", code):
        return False, "", "⚠️ Некорректный формат промокода. Используй только латиницу и цифры."

    ensure_user(user_id)
    now = int(time.time())

    with db_conn() as conn:
        c = conn.cursor()
        c.execute(
            """
            SELECT promo_type, value, max_uses, used_count, expires_at, is_active
            FROM promocodes WHERE code = ?
            """,
            (code,),
        )
        row = c.fetchone()
        if not row:
            return False, "", "❌ Промокод не найден."

        ptype, val, max_uses, used_cnt, exp_at, is_act = row
        if not is_act:
            return False, "", "❌ Этот промокод больше не активен."
        if exp_at > 0 and now >= exp_at:
            return False, "", "⏳ Срок действия этого промокода истёк."
        if max_uses > 0 and used_cnt >= max_uses:
            return False, "", "⏳ Лимит активаций этого промокода исчерпан."

        c.execute("SELECT 1 FROM promo_uses WHERE code = ? AND user_id = ?", (code, user_id))
        if c.fetchone():
            return False, "", "ℹ️ Ты уже использовал этот промокод ранее."

        if ptype == "discount":
            c.execute("UPDATE users SET active_promo = ? WHERE user_id = ?", (code, user_id))
            exp_note = f"\nДействует: <b>{format_time_left(exp_at)}</b>" if exp_at > 0 else ""
            return (
                True,
                "discount",
                f"🎉 Промокод <code>{html.escape(code)}</code> применён!\n"
                f"Скидка <b>{val}%</b> активирована на следующую покупку в /buy.{exp_note}",
            )

        if ptype == "scans":
            c.execute("INSERT INTO promo_uses (code, user_id) VALUES (?, ?)", (code, user_id))
            c.execute("UPDATE promocodes SET used_count = used_count + 1 WHERE code = ?", (code,))
            c.execute("UPDATE users SET free_limit = free_limit + ? WHERE user_id = ?", (val, user_id))
            return (
                True,
                "scans",
                f"🎉 Промокод <code>{html.escape(code)}</code> активирован!\n"
                f"На баланс начислено <b>+{val} сканов</b>.",
            )

        if ptype == "pro_days":
            c.execute(
                "SELECT COALESCE(pro_tier, 0), COALESCE(pro_until, 0) FROM users WHERE user_id = ?",
                (user_id,),
            )
            urow = c.fetchone()
            cur_tier = urow[0] if urow else 0
            cur_until = urow[1] if urow else 0
            if cur_tier >= 2:
                return False, "", "💎 У тебя уже активен <b>PRO Навсегда</b> — этот промокод не нужен."

            base = max(now, cur_until) if cur_tier == 1 else now
            new_until = base + val * 86400
            c.execute("INSERT INTO promo_uses (code, user_id) VALUES (?, ?)", (code, user_id))
            c.execute("UPDATE promocodes SET used_count = used_count + 1 WHERE code = ?", (code,))
            c.execute(
                "UPDATE users SET is_premium = 1, pro_tier = 1, pro_until = ? WHERE user_id = ?",
                (new_until, user_id),
            )
            return (
                True,
                "pro_days",
                f"🎉 Промокод <code>{html.escape(code)}</code> активирован!\n"
                f"Выдан <b>PRO на {val} дн.</b> (до {format_date_from_ts(new_until)}).",
            )

    return False, "", "⚠️ Не удалось активировать промокод."


def is_channel_bonus_claimed(user_id):
    with db_conn() as conn:
        c = conn.cursor()
        c.execute("SELECT COALESCE(channel_bonus_claimed, 0) FROM users WHERE user_id = ?", (user_id,))
        row = c.fetchone()
        return bool(row and row[0])


def claim_channel_bonus(user_id):
    ensure_user(user_id)
    with db_conn() as conn:
        c = conn.cursor()
        c.execute(
            """
            UPDATE users
            SET channel_bonus_claimed = 1,
                free_limit = free_limit + ?
            WHERE user_id = ? AND COALESCE(channel_bonus_claimed, 0) = 0
            """,
            (CHANNEL_SUB_BONUS, user_id),
        )
        return c.rowcount > 0


_mp_lock = threading.Lock()
_mp_mode = None
_mp_detector = None


def _init_mediapipe():
    global _mp_mode, _mp_detector
    if _mp_mode is not None:
        return _mp_mode != "unavailable"

    if mp is None or np is None:
        _mp_mode = "unavailable"
        log_error("MediaPipe или NumPy не установлены (режим визуальной оценки).")
        return False

    try:
        if hasattr(mp, "solutions") and hasattr(mp.solutions, "face_mesh"):
            _mp_detector = mp.solutions.face_mesh.FaceMesh(
                static_image_mode=True,
                max_num_faces=1,
                refine_landmarks=True,
                min_detection_confidence=0.45,
            )
            _mp_mode = "solutions"
            print("[MediaPipe] Активен режим FaceMesh (478 3D-точек).")
            return True
    except Exception as e:
        log_error(f"MediaPipe FaceMesh не запустился, пробую Tasks API: {e}")

    try:
        from mediapipe.tasks import python as mp_python
        from mediapipe.tasks.python import vision as mp_vision

        if not os.path.exists(FACE_LANDMARKER_MODEL_PATH):
            print("[MediaPipe] Скачиваю модель face_landmarker.task...")
            resp = requests.get(FACE_LANDMARKER_MODEL_URL, timeout=30)
            resp.raise_for_status()
            with open(FACE_LANDMARKER_MODEL_PATH, "wb") as f:
                f.write(resp.content)

        base_options = mp_python.BaseOptions(model_asset_path=FACE_LANDMARKER_MODEL_PATH)
        options = mp_vision.FaceLandmarkerOptions(
            base_options=base_options,
            running_mode=mp_vision.RunningMode.IMAGE,
            num_faces=1,
            min_face_detection_confidence=0.45,
            min_face_presence_confidence=0.45,
            output_facial_transformation_matrixes=True,
        )
        _mp_detector = mp_vision.FaceLandmarker.create_from_options(options)
        _mp_mode = "tasks"
        print("[MediaPipe] Активен режим FaceLandmarker Tasks API (478 точек + 3D-матрица).")
        return True
    except Exception as e:
        _mp_mode = "unavailable"
        log_error(f"MediaPipe Tasks API недоступен: {e}")
        return False


def is_mediapipe_available():
    with _mp_lock:
        return _init_mediapipe()


def _detect_face_landmarks(img_rgb_np):
    with _mp_lock:
        if not _init_mediapipe():
            return None, None
        try:
            if _mp_mode == "solutions":
                res = _mp_detector.process(img_rgb_np)
                if not res.multi_face_landmarks:
                    return None, None
                lms_3d = [(lm.x, lm.y, lm.z) for lm in res.multi_face_landmarks[0].landmark]
                return lms_3d, None

            if _mp_mode == "tasks":
                mp_img = mp.Image(
                    image_format=mp.ImageFormat.SRGB,
                    data=np.ascontiguousarray(img_rgb_np),
                )
                res = _mp_detector.detect(mp_img)
                if not res.face_landmarks:
                    return None, None
                lms_3d = [(lm.x, lm.y, lm.z) for lm in res.face_landmarks[0]]
                t_mat = None
                if getattr(res, "facial_transformation_matrixes", None):
                    t_mat = np.array(res.facial_transformation_matrixes[0], dtype=np.float64)
                return lms_3d, t_mat
        except Exception as e:
            log_error(f"Ошибка MediaPipe: {e}")
            return None, None
    return None, None


def _classify_face_shape(w_forehead, w_cheek, w_jaw, h_face):
    if w_cheek <= 1:
        return "Овальное"
    ratio_hw = h_face / w_cheek
    jaw_to_cheek = w_jaw / w_cheek
    forehead_to_cheek = w_forehead / w_cheek

    if ratio_hw >= 1.52:
        return "Прямоугольное" if jaw_to_cheek >= 0.78 else "Вытянутое"
    if ratio_hw <= 1.24:
        return "Квадратное" if jaw_to_cheek >= 0.80 else "Круглое"
    if forehead_to_cheek > jaw_to_cheek + 0.11 and jaw_to_cheek < 0.74:
        return "Сердцевидное"
    if jaw_to_cheek < 0.74 and forehead_to_cheek < 0.86:
        return "Ромбовидное"
    if jaw_to_cheek >= 0.82 and forehead_to_cheek >= 0.84:
        return "Квадратное" if ratio_hw < 1.38 else "Прямоугольное"
    return "Овальное"


def _align_landmarks_3d(lms_3d, w, h, transform_matrix=None):
    pts3 = np.array([(x * w, y * h, z * w) for (x, y, z) in lms_3d], dtype=np.float64)

    if len(pts3) >= 478:
        re3, le3 = pts3[468], pts3[473]
    else:
        re3 = (pts3[33] + pts3[133]) * 0.5
        le3 = (pts3[362] + pts3[263]) * 0.5

    origin = (re3 + le3) * 0.5

    vx_lm = (
        (pts3[454] - pts3[234]) * 0.45
        + (pts3[263] - pts3[33]) * 0.35
        + (pts3[362] - pts3[133]) * 0.20
    )
    nx_lm = float(np.linalg.norm(vx_lm))
    if nx_lm < 1e-6:
        return None
    ex_lm = vx_lm / nx_lm

    vy_lm_raw = ((pts3[152] + pts3[17]) * 0.5) - ((pts3[10] + pts3[9]) * 0.5)
    vy_lm = vy_lm_raw - np.dot(vy_lm_raw, ex_lm) * ex_lm
    ny_lm = float(np.linalg.norm(vy_lm))
    if ny_lm < 1e-6:
        return None
    ey_lm = vy_lm / ny_lm

    ex, ey = ex_lm, ey_lm
    if transform_matrix is not None:
        try:
            mat = np.asarray(transform_matrix, dtype=np.float64)
            if mat.shape == (4, 4):
                u, _, vt = np.linalg.svd(mat[:3, :3])
                rot_m = u @ vt
                if np.linalg.det(rot_m) < 0:
                    u[:, -1] *= -1.0
                    rot_m = u @ vt
                ex_mat = np.array([rot_m[0, 0], -rot_m[1, 0], -rot_m[2, 0]], dtype=np.float64)
                ey_mat = np.array([-rot_m[0, 1], rot_m[1, 1], rot_m[2, 1]], dtype=np.float64)
                ex_mat /= max(1e-9, float(np.linalg.norm(ex_mat)))
                ey_mat = ey_mat - np.dot(ey_mat, ex_mat) * ex_mat
                ey_mat /= max(1e-9, float(np.linalg.norm(ey_mat)))
                if np.dot(ex_mat, ex_lm) > 0.65 and np.dot(ey_mat, ey_lm) > 0.65:
                    ex, ey = ex_mat, ey_mat
        except Exception as e:
            log_error(f"3D matrix alignment fallback: {e}")

    yaw_deg = math.degrees(math.atan2(-ex[2], max(1e-6, ex[0])))
    pitch_deg = math.degrees(math.atan2(-ey[2], max(1e-6, ey[1])))
    roll_deg = math.degrees(math.atan2(ex[1], max(1e-6, ex[0])))

    rel = pts3 - origin
    x_proj = rel @ ex
    y_proj = rel @ ey

    re_rel = re3 - origin
    le_rel = le3 - origin
    re_2d = (float(np.dot(re_rel, ex)), float(np.dot(re_rel, ey)))
    le_2d = (float(np.dot(le_rel, ex)), float(np.dot(le_rel, ey)))

    res_roll = math.atan2(le_2d[1] - re_2d[1], le_2d[0] - re_2d[0])
    cos_r, sin_r = math.cos(-res_roll), math.sin(-res_roll)

    x_final = x_proj * cos_r - y_proj * sin_r
    y_final = x_proj * sin_r + y_proj * cos_r
    rpts = list(zip(x_final.tolist(), y_final.tolist()))

    re_c = (re_2d[0] * cos_r - re_2d[1] * sin_r, re_2d[0] * sin_r + re_2d[1] * cos_r)
    le_c = (le_2d[0] * cos_r - le_2d[1] * sin_r, le_2d[0] * sin_r + le_2d[1] * cos_r)

    pose = {
        "yaw": round(yaw_deg, 1),
        "pitch": round(pitch_deg, 1),
        "roll": round(roll_deg, 1),
    }
    return rpts, re_c, le_c, pose


def analyze_face_geometry(image_bytes, gender="m"):
    if np is None or mp is None:
        return None
    try:
        with io.BytesIO(image_bytes) as bio, Image.open(bio) as pil_img:
            rgb_img = pil_img.convert("RGB")
            w, h = rgb_img.size
            img_np = np.array(rgb_img)
    except Exception as e:
        log_error(f"analyze_face_geometry open error: {e}")
        return None

    lms_3d, transform_matrix = _detect_face_landmarks(img_np)
    if not lms_3d or len(lms_3d) < 468:
        return None

    lms_norm = [(x, y) for (x, y, _) in lms_3d]

    aligned = _align_landmarks_3d(lms_3d, w, h, transform_matrix=transform_matrix)
    if not aligned:
        return None
    rpts, re_c, le_c, pose = aligned

    if abs(pose["yaw"]) > 34.0:
        return None

    ipd = abs(le_c[0] - re_c[0])
    bizygomatic = abs(rpts[454][0] - rpts[234][0])
    if ipd < 5 or bizygomatic < 15:
        return None

    eye_line_y = (re_c[1] + le_c[1]) * 0.5
    upper_lip_y = rpts[0][1]
    subnasale_y = rpts[2][1]
    lower_lip_y = rpts[17][1]
    chin_y = rpts[152][1]
    glabella_y = rpts[9][1]
    forehead_y = rpts[10][1]

    r_brow_low_y = (rpts[52][1] + rpts[65][1]) * 0.5
    l_brow_low_y = (rpts[282][1] + rpts[295][1]) * 0.5
    upper_eyelid_y = (rpts[159][1] + rpts[386][1]) * 0.5

    midface_ratio = ipd / max(1.0, upper_lip_y - eye_line_y)
    fwhr = bizygomatic / max(1.0, upper_lip_y - upper_eyelid_y)

    r_tilt = math.degrees(math.atan2(rpts[133][1] - rpts[33][1], max(1.0, rpts[133][0] - rpts[33][0])))
    l_tilt = math.degrees(math.atan2(rpts[362][1] - rpts[263][1], max(1.0, rpts[263][0] - rpts[362][0])))
    canthal_tilt = (r_tilt + l_tilt) * 0.5

    esr = ipd / bizygomatic
    chin_philtrum = max(1.0, chin_y - lower_lip_y) / max(1.0, upper_lip_y - subnasale_y)
    mid_to_lower = max(1.0, subnasale_y - glabella_y) / max(1.0, chin_y - subnasale_y)

    nose_w = abs(rpts[278][0] - rpts[48][0])
    nose_intercanthal = nose_w / max(1.0, abs(rpts[362][0] - rpts[133][0]))

    mouth_w = max(1.0, abs(rpts[291][0] - rpts[61][0]))
    nose_mouth = nose_w / mouth_w
    lip_fullness = max(1.0, lower_lip_y - upper_lip_y) / mouth_w

    eye_w = max(1.0, (abs(rpts[133][0] - rpts[33][0]) + abs(rpts[263][0] - rpts[362][0])) * 0.5)
    r_lid_ref_y = rpts[27][1] * 0.72 + rpts[159][1] * 0.28
    l_lid_ref_y = rpts[257][1] * 0.72 + rpts[386][1] * 0.28
    brow_to_eye = ((max(0.0, r_lid_ref_y - r_brow_low_y) + max(0.0, l_lid_ref_y - l_brow_low_y)) * 0.5) / eye_w

    raw_values = {
        "midface_ratio": midface_ratio,
        "fwhr": fwhr,
        "canthal_tilt": canthal_tilt,
        "esr": esr,
        "chin_philtrum": chin_philtrum,
        "mid_to_lower": mid_to_lower,
        "nose_intercanthal": nose_intercanthal,
        "nose_mouth": nose_mouth,
        "lip_fullness": lip_fullness,
        "brow_to_eye": brow_to_eye,
    }
    metrics = evaluate_mediapipe_metrics(raw_values, gender=gender)

    sym_pairs = [
        (33, 263), (133, 362), (159, 386), (105, 334), (48, 278),
        (61, 291), (234, 454), (172, 397), (150, 379),
    ]
    mid_x = sum(rpts[idx][0] for idx in (168, 1, 2, 0, 152)) / 5.0

    yaw_abs = abs(pose["yaw"])
    x_err_weight = max(0.55, 1.0 - max(0.0, yaw_abs - 10.0) * 0.025)

    errs = []
    for li, ri in sym_pairs:
        err_x = abs(abs(mid_x - rpts[li][0]) - abs(rpts[ri][0] - mid_x)) / bizygomatic
        err_y = abs(rpts[li][1] - rpts[ri][1]) / bizygomatic
        errs.append(math.hypot(err_x * x_err_weight, err_y))

    symmetry_pct = max(70.0, min(97.5, 100.0 - (sum(errs) / len(errs)) * 460.0))
    if symmetry_pct >= 95.0:
        sym_status, sym_tone = "Идеал", "green"
    elif symmetry_pct >= 89.0:
        sym_status, sym_tone = "В норме", "blue"
    elif symmetry_pct >= 83.0:
        sym_status, sym_tone = "Умеренная", "amber"
    else:
        sym_status, sym_tone = "Асимметрия", "red"

    forehead_w = abs(rpts[284][0] - rpts[54][0])
    jaw_w = abs(rpts[397][0] - rpts[172][0])
    face_h = max(1.0, (chin_y - forehead_y) * 1.12)
    face_shape = _classify_face_shape(forehead_w, bizygomatic, jaw_w, face_h)

    xs = [p[0] for p in lms_norm]
    ys = [p[1] for p in lms_norm]
    face_bbox = (min(xs), min(ys), max(xs), max(ys))

    return {
        "source": "mediapipe",
        "metrics": metrics,
        "symmetry_pct": round(symmetry_pct, 1),
        "symmetry_status": sym_status,
        "symmetry_tone": sym_tone,
        "face_shape": face_shape,
        "face_bbox": face_bbox,
        "landmarks_norm": lms_norm,
        "pose": pose,
    }


def _normalize_visual_status(raw_status):
    s = (raw_status or "").strip().lower()
    if "идеал" in s and "далек" not in s and "близк" not in s:
        return "Идеал", "green"
    if "близк" in s:
        return "Близко к идеалу", "green"
    if "норм" in s or "выше" in s:
        return "В норме", "blue"
    if "зон" in s or "рост" in s or "ниже" in s:
        return "Зона роста", "amber"
    if "далек" in s or "асимм" in s:
        return "Далеко от идеала", "red"
    return "В норме", "blue"


def extract_visual_geometry(text, gender="m"):
    metrics = []
    for name, norm in get_visual_prop_specs(gender):
        pat = rf"(?im)^\s*(?:PROP\s*\|\s*)?{re.escape(name)}\s*(?:\||:)\s*(.+)$"
        m = re.search(pat, text)
        if m:
            raw_val = m.group(1).strip().strip("[]")
            status, tone = _normalize_visual_status(raw_val)
            metrics.append({
                "name": name,
                "norm": norm,
                "value": None,
                "display": "",
                "status": status,
                "tone": tone,
            })

    if len(metrics) < 5:
        return None

    m_shape = re.search(r"(?im)^\s*Форма\s+лица\s*[:|]\s*([А-Яа-яЁё\- ]+)", text)
    face_shape = m_shape.group(1).strip().capitalize()[:24] if m_shape else ""

    m_sym = re.search(r"(?im)^\s*Симметрия\s*[:|]\s*(\d{2,3})\s*%?", text)
    sym_pct = max(70.0, min(97.0, float(m_sym.group(1)))) if m_sym else 90.0

    if sym_pct >= 95.0:
        sym_status, sym_tone = "Идеал", "green"
    elif sym_pct >= 89.0:
        sym_status, sym_tone = "В норме", "blue"
    elif sym_pct >= 83.0:
        sym_status, sym_tone = "Умеренная", "amber"
    else:
        sym_status, sym_tone = "Асимметрия", "red"

    return {
        "source": "visual",
        "metrics": metrics,
        "symmetry_pct": round(sym_pct, 1),
        "symmetry_status": sym_status,
        "symmetry_tone": sym_tone,
        "face_shape": face_shape,
        "face_bbox": None,
        "landmarks_norm": None,
    }


def format_geometry_for_prompt(geom):
    if not geom:
        return ""
    lines = [
        "СПРАВОЧНЫЕ ЗАМЕРЫ ПО 468 ТОЧКАМ С 3D-ВЫРАВНИВАНИЕМ ГОЛОВЫ (MediaPipe — НЕ измеряют 3D-рельеф скул, посадку глаз и углы челюсти):",
    ]
    for m in geom["metrics"]:
        lines.append(f"- {m['name']} ({m['norm']}): {m['display']}")
    lines.append(f"- Выровненная симметрия: {geom['symmetry_pct']:.1f}%")
    lines.append(f"- Форма лица: {geom['face_shape']}")
    if geom.get("pose"):
        p = geom["pose"]
        lines.append(
            f"- Поворот головы на фото (скомпенсирован в замерах): "
            f"yaw {p['yaw']:+.1f}°, pitch {p['pitch']:+.1f}°, roll {p['roll']:+.1f}°"
        )
    lines.append(
        "ВАЖНО: ровные 2D-пропорции без выраженного 3D-рельефа — это обычная норма (3.5–4.2), не завышай за них балл. "
        "Но если на фото реально видна сильная 3D-костная структура и гармония (высокие скулы, чёткий контур, выразительная зона глаз) — "
        "не занижай оценку, смело используй диапазон 5.5–7.7."
    )
    return "\n".join(lines)


_FONT_CACHE = {}
_FONT_LOCK = threading.Lock()
_RESOLVED_FONTS = None

_FONT_REGULAR_CANDIDATES = [
    os.path.join(os.getcwd(), "fonts", "DejaVuSans.ttf"),
    os.path.join(os.getcwd(), "fonts", "Roboto-Regular.ttf"),
    "/system/fonts/Roboto-Regular.ttf",
    "/system/fonts/Roboto-Medium.ttf",
    "/system/fonts/NotoSans-Regular.ttf",
    "/system/fonts/DroidSans.ttf",
    "/data/data/com.termux/files/usr/share/fonts/TTF/DejaVuSans.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf",
    "/usr/share/fonts/truetype/noto/NotoSans-Regular.ttf",
    "/usr/share/fonts/truetype/ubuntu/Ubuntu-R.ttf",
    "/usr/share/fonts/truetype/freefont/FreeSans.ttf",
    "C:/Windows/Fonts/segoeui.ttf",
    "C:/Windows/Fonts/arial.ttf",
    "/System/Library/Fonts/Supplemental/Arial.ttf",
]

_FONT_BOLD_CANDIDATES = [
    os.path.join(os.getcwd(), "fonts", "DejaVuSans-Bold.ttf"),
    os.path.join(os.getcwd(), "fonts", "Roboto-Bold.ttf"),
    "/system/fonts/Roboto-Bold.ttf",
    "/system/fonts/Roboto-Medium.ttf",
    "/system/fonts/NotoSans-Bold.ttf",
    "/system/fonts/DroidSans-Bold.ttf",
    "/data/data/com.termux/files/usr/share/fonts/TTF/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
    "/usr/share/fonts/truetype/noto/NotoSans-Bold.ttf",
    "/usr/share/fonts/truetype/ubuntu/Ubuntu-B.ttf",
    "/usr/share/fonts/truetype/freefont/FreeSansBold.ttf",
    "C:/Windows/Fonts/segoeuib.ttf",
    "C:/Windows/Fonts/arialbd.ttf",
    "/System/Library/Fonts/Supplemental/Arial Bold.ttf",
]


def _font_supports_cyrillic(path):
    if not path or not os.path.isfile(path):
        return False
    try:
        font = ImageFont.truetype(path, size=24)
        missing_mask = bytes(font.getmask("\u0378"))
        for ch in ("А", "Ж", "Я"):
            ch_mask = bytes(font.getmask(ch))
            if not ch_mask or ch_mask == missing_mask:
                return False
        return True
    except Exception:
        return False


def _scan_system_cyrillic_fonts():
    reg_found, bold_found = None, None
    search_dirs = [
        "/system/fonts",
        "/usr/share/fonts",
        "/usr/local/share/fonts",
        os.path.join(os.getcwd(), "fonts"),
    ]
    preferred_names = ("roboto", "noto", "dejavu", "inter", "liberation", "ubuntu", "droid", "sans")
    for base in search_dirs:
        if not os.path.isdir(base):
            continue
        for root, _, files in os.walk(base):
            for fname in sorted(files):
                low = fname.lower()
                if not low.endswith((".ttf", ".otf")):
                    continue
                if any(bad in low for bad in ("emoji", "mono", "italic", "condensed", "thin", "light", "clock")):
                    continue
                if not any(pref in low for pref in preferred_names):
                    continue
                full_path = os.path.join(root, fname)
                if not _font_supports_cyrillic(full_path):
                    continue
                if "bold" in low or "medium" in low:
                    if not bold_found:
                        bold_found = full_path
                else:
                    if not reg_found:
                        reg_found = full_path
                if reg_found and bold_found:
                    return reg_found, bold_found
    return reg_found, bold_found


def _ensure_font_paths():
    global _RESOLVED_FONTS
    if _RESOLVED_FONTS is not None:
        return _RESOLVED_FONTS

    reg = next((p for p in _FONT_REGULAR_CANDIDATES if _font_supports_cyrillic(p)), None)
    bold = next((p for p in _FONT_BOLD_CANDIDATES if _font_supports_cyrillic(p)), None)

    if not reg or not bold:
        s_reg, s_bold = _scan_system_cyrillic_fonts()
        reg = reg or s_reg
        bold = bold or s_bold

    if not reg or not bold:
        fonts_dir = os.path.join(os.getcwd(), "fonts")
        os.makedirs(fonts_dir, exist_ok=True)
        download_sources = {
            "DejaVuSans.ttf": [
                "https://cdn.jsdelivr.net/npm/dejavu-fonts-ttf@2.37.3/ttf/DejaVuSans.ttf",
                "https://raw.githubusercontent.com/googlefonts/roboto/main/src/hinted/Roboto-Regular.ttf",
            ],
            "DejaVuSans-Bold.ttf": [
                "https://cdn.jsdelivr.net/npm/dejavu-fonts-ttf@2.37.3/ttf/DejaVuSans-Bold.ttf",
                "https://raw.githubusercontent.com/googlefonts/roboto/main/src/hinted/Roboto-Bold.ttf",
            ],
        }
        for fname, urls in download_sources.items():
            target = os.path.join(fonts_dir, fname)
            if _font_supports_cyrillic(target):
                continue
            for url in urls:
                try:
                    r = requests.get(url, timeout=15)
                    if r.status_code == 200 and len(r.content) > 40000:
                        with open(target, "wb") as f:
                            f.write(r.content)
                        if _font_supports_cyrillic(target):
                            break
                        try:
                            os.remove(target)
                        except OSError:
                            pass
                except Exception as e:
                    log_error(f"Не удалось скачать шрифт {fname}: {e}")

        reg = reg or next((p for p in _FONT_REGULAR_CANDIDATES if _font_supports_cyrillic(p)), None)
        bold = bold or next((p for p in _FONT_BOLD_CANDIDATES if _font_supports_cyrillic(p)), None)

    if reg or bold:
        _RESOLVED_FONTS = (reg or bold, bold or reg)
        print(f"[Fonts] Используются шрифты: regular={_RESOLVED_FONTS[0]}, bold={_RESOLVED_FONTS[1]}")
        return _RESOLVED_FONTS

    log_error("Не найден ни один кириллический TTF-шрифт!")
    return None, None


def _get_font(size, bold=False):
    key = (size, bold)
    with _FONT_LOCK:
        if key in _FONT_CACHE:
            return _FONT_CACHE[key]
        reg_path, bold_path = _ensure_font_paths()
        path = bold_path if bold else reg_path
        try:
            if path:
                font = ImageFont.truetype(path, size=size)
            else:
                try:
                    font = ImageFont.load_default(size=size)
                except TypeError:
                    font = ImageFont.load_default()
        except Exception:
            font = ImageFont.load_default()
        _FONT_CACHE[key] = font
        return font


def _tone_colors(tone):
    if tone == "green":
        return (16, 52, 40, 255), (26, 94, 68, 255), (52, 211, 153, 255)
    if tone == "blue":
        return (20, 41, 74, 255), (38, 79, 138, 255), (96, 165, 250, 255)
    if tone == "amber":
        return (56, 40, 18, 255), (104, 73, 28, 255), (251, 191, 36, 255)
    return (58, 24, 30, 255), (112, 42, 52, 255), (248, 113, 113, 255)


def _calc_percentile(score):
    z = (score - 3.95) / 0.95
    pct = 0.5 * (1.0 + math.erf(z / math.sqrt(2.0))) * 100.0
    return max(1, min(99, int(round(pct))))


def _wrap_text_px(draw, text, font, max_width, max_lines=2):
    words = text.split()
    lines = []
    cur = ""
    truncated = False
    for word in words:
        candidate = f"{cur} {word}".strip()
        if draw.textlength(candidate, font=font) <= max_width:
            cur = candidate
        else:
            if cur:
                lines.append(cur)
                if len(lines) >= max_lines:
                    truncated = True
                    cur = ""
                    break
            cur = word
    if cur and len(lines) < max_lines:
        lines.append(cur)
    elif cur:
        truncated = True

    if lines and (truncated or draw.textlength(lines[-1], font=font) > max_width):
        last = lines[-1].rstrip(" ,.;:-")
        ell = "…"
        while last and draw.textlength(last + ell, font=font) > max_width:
            last = last[:-1].rstrip(" ,.;:-")
        lines[-1] = (last + ell) if last else ell
    return lines


def _draw_card_box(draw, xy, radius=20, fill=(17, 20, 28, 255), outline=(30, 36, 51, 255)):
    draw.rounded_rectangle(xy, radius=radius, fill=fill, outline=outline, width=1)


def _draw_pill_badge(draw, x, y, w, h, text, tone="green", font_size=12):
    bg, border, fg = _tone_colors(tone)
    draw.rounded_rectangle((x, y, x + w, y + h), radius=h // 2, fill=bg, outline=border, width=1)
    font = _get_font(font_size, bold=True)
    bbox = draw.textbbox((0, 0), text, font=font)
    tw = bbox[2] - bbox[0]
    th = bbox[3] - bbox[1]
    tx = x + (w - tw) / 2
    ty = y + (h - th) / 2 - bbox[1]
    draw.text((tx, ty), text, font=font, fill=fg)


def _draw_ring_gauge(draw, cx, cy, radius, ratio, center_text, label_text, accent=(76, 141, 255, 255)):
    ratio = max(0.0, min(1.0, ratio))
    bbox = (cx - radius, cy - radius, cx + radius, cy + radius)
    draw.arc(bbox, start=0, end=360, fill=(30, 38, 56, 255), width=7)
    if ratio > 0.01:
        end_deg = -90 + int(360 * ratio)
        draw.arc(bbox, start=-90, end=end_deg, fill=accent, width=7)

    f_val = _get_font(19 if len(center_text) <= 5 else 15, bold=True)
    vb = draw.textbbox((0, 0), center_text, font=f_val)
    vw, vh = vb[2] - vb[0], vb[3] - vb[1]
    draw.text((cx - vw / 2, cy - vh / 2 - vb[1]), center_text, font=f_val, fill=(243, 244, 246, 255))

    f_lbl = _get_font(13, bold=False)
    lb = draw.textbbox((0, 0), label_text, font=f_lbl)
    lw = lb[2] - lb[0]
    draw.text((cx - lw / 2, cy + radius + 12), label_text, font=f_lbl, fill=(139, 149, 169, 255))


def _draw_radar_chart(base_img, cx, cy, radius, items):
    overlay = Image.new("RGBA", base_img.size, (0, 0, 0, 0))
    odraw = ImageDraw.Draw(overlay)
    n = len(items)
    if n < 3:
        return base_img

    for frac in (0.33, 0.66, 1.0):
        ring_pts = []
        for i in range(n):
            ang = -math.pi / 2 + 2 * math.pi * i / n
            ring_pts.append((cx + radius * frac * math.cos(ang), cy + radius * frac * math.sin(ang)))
        odraw.polygon(ring_pts, outline=(36, 45, 66, 200))

    f_lbl = _get_font(12, bold=False)
    data_pts = []
    for i, (label, val) in enumerate(items):
        ang = -math.pi / 2 + 2 * math.pi * i / n
        cos_a, sin_a = math.cos(ang), math.sin(ang)
        odraw.line((cx, cy, cx + radius * cos_a, cy + radius * sin_a), fill=(36, 45, 66, 180), width=1)

        frac = max(0.12, min(1.0, val / 8.0))
        data_pts.append((cx + radius * frac * cos_a, cy + radius * frac * sin_a))

        lb = odraw.textbbox((0, 0), label, font=f_lbl)
        lw, lh = lb[2] - lb[0], lb[3] - lb[1]
        lx = cx + (radius + 14) * cos_a
        ly = cy + (radius + 16) * sin_a

        if cos_a < -0.35:
            tx = lx - lw
        elif cos_a > 0.35:
            tx = lx
        else:
            tx = lx - lw / 2
        ty = ly - lh / 2 - lb[1]
        odraw.text((tx, ty), label, font=f_lbl, fill=(148, 163, 184, 255))

    odraw.polygon(data_pts, fill=(76, 141, 255, 72), outline=(96, 165, 250, 235))
    for px, py in data_pts:
        odraw.ellipse((px - 3, py - 3, px + 3, py + 3), fill=(147, 197, 253, 255))

    return Image.alpha_composite(base_img, overlay)


_FACE_CONTOUR_CHAINS = [
    [10, 338, 297, 332, 284, 251, 389, 356, 454, 323, 361, 288, 397, 365, 379, 378, 400, 377, 152, 148, 176, 149, 150, 136, 172, 58, 132, 93, 234, 127, 162, 21, 54, 103, 67, 109, 10],
    [33, 7, 163, 144, 145, 153, 154, 155, 133, 173, 157, 158, 159, 160, 161, 246, 33],
    [362, 382, 381, 380, 374, 373, 390, 249, 263, 466, 388, 387, 386, 385, 384, 398, 362],
    [70, 63, 105, 66, 107, 55, 65, 52, 53, 46],
    [300, 293, 334, 296, 336, 285, 295, 282, 283, 276],
    [168, 6, 197, 195, 5, 4, 1, 19, 94, 2],
    [48, 115, 220, 45, 4, 275, 440, 344, 278],
    [98, 97, 2, 326, 327],
    [61, 185, 40, 39, 37, 0, 267, 269, 270, 409, 291, 375, 321, 405, 314, 17, 84, 181, 91, 146, 61],
    [78, 191, 80, 81, 82, 13, 312, 311, 310, 415, 308, 324, 318, 402, 317, 14, 87, 178, 88, 95, 78],
]

_FACE_KEY_ANCHORS = (
    10, 152, 234, 454, 172, 397, 33, 133, 362, 263,
    159, 386, 52, 65, 282, 295, 168, 1, 2, 48, 278,
    0, 17, 61, 291,
)


def _build_mesh_edges_fast(mapped, edge_max):
    n_pts = len(mapped)
    edge_max_sq = edge_max * edge_max
    drawn_edges = set()

    if np is not None and n_pts > 4:
        pts_arr = np.asarray(mapped, dtype=np.float32)
        diff = pts_arr[:, None, :] - pts_arr[None, :, :]
        d2 = diff[:, :, 0] ** 2 + diff[:, :, 1] ** 2
        np.fill_diagonal(d2, np.inf)
        k = min(4, n_pts - 1)
        nearest_idx = np.argpartition(d2, kth=k - 1, axis=1)[:, :k]
        for i in range(n_pts):
            row_d2 = d2[i]
            for j in nearest_idx[i]:
                j_int = int(j)
                if row_d2[j_int] <= edge_max_sq:
                    edge = (i, j_int) if i < j_int else (j_int, i)
                    drawn_edges.add(edge)
        return drawn_edges

    for i in range(n_pts):
        x1p, y1p = mapped[i]
        neighbors = []
        for j in range(n_pts):
            if i == j:
                continue
            dx = x1p - mapped[j][0]
            if abs(dx) > edge_max:
                continue
            dy = y1p - mapped[j][1]
            if abs(dy) > edge_max:
                continue
            d2_val = dx * dx + dy * dy
            if d2_val <= edge_max_sq:
                neighbors.append((d2_val, j))
        neighbors.sort(key=lambda item: item[0])
        for _, j in neighbors[:4]:
            edge = (i, j) if i < j else (j, i)
            drawn_edges.add(edge)
    return drawn_edges


def _crop_portrait_with_mesh(image_bytes, target_size, geom=None):
    with io.BytesIO(image_bytes) as bio, Image.open(bio) as src:
        img = src.convert("RGBA")
        w, h = img.size

        if geom and geom.get("face_bbox"):
            x0, y0, x1, y1 = geom["face_bbox"]
            fcx = (x0 + x1) * 0.5 * w
            fcy = (y0 + y1) * 0.48 * h
            face_span = max((x1 - x0) * w, (y1 - y0) * h)
            side = min(w, h, max(face_span * 1.95, min(w, h) * 0.55))
        else:
            fcx, fcy = w * 0.5, h * 0.45
            side = min(w, h)

        left = max(0, min(w - side, fcx - side * 0.5))
        top = max(0, min(h - side, fcy - side * 0.46))
        crop_box = (int(left), int(top), int(left + side), int(top + side))
        cropped = img.crop(crop_box).resize((target_size, target_size), Image.Resampling.LANCZOS)

        if geom and geom.get("landmarks_norm"):
            mesh_layer = Image.new("RGBA", (target_size, target_size), (0, 0, 0, 0))
            mdraw = ImageDraw.Draw(mesh_layer)
            scale_x = target_size / max(1.0, (crop_box[2] - crop_box[0]))
            scale_y = target_size / max(1.0, (crop_box[3] - crop_box[1]))

            mapped = [
                ((nx * w - crop_box[0]) * scale_x, (ny * h - crop_box[1]) * scale_y)
                for nx, ny in geom["landmarks_norm"][:468]
            ]
            n_pts = len(mapped)
            face_px_w = abs(mapped[454][0] - mapped[234][0]) if n_pts > 454 else target_size * 0.45
            edge_max = max(8.0, face_px_w * 0.115)

            for i, j in _build_mesh_edges_fast(mapped, edge_max):
                mdraw.line(
                    (mapped[i][0], mapped[i][1], mapped[j][0], mapped[j][1]),
                    fill=(86, 165, 255, 58),
                    width=1,
                )

            for chain in _FACE_CONTOUR_CHAINS:
                if max(chain) < n_pts:
                    poly = [mapped[idx] for idx in chain]
                    mdraw.line(poly, fill=(110, 185, 255, 138), width=1)

            for px, py in mapped[::2]:
                mdraw.ellipse((px - 1.0, py - 1.0, px + 1.0, py + 1.0), fill=(175, 220, 255, 175))

            for idx in _FACE_KEY_ANCHORS:
                if idx < n_pts:
                    px, py = mapped[idx]
                    mdraw.ellipse((px - 1.8, py - 1.8, px + 1.8, py + 1.8), fill=(215, 240, 255, 235))

            cropped = Image.alpha_composite(cropped, mesh_layer)

        mask = Image.new("L", (target_size, target_size), 0)
        ImageDraw.Draw(mask).rounded_rectangle((0, 0, target_size, target_size), radius=16, fill=255)
        out = Image.new("RGBA", (target_size, target_size), (0, 0, 0, 0))
        out.paste(cropped, (0, 0), mask)
        return out


def render_front_report_card(
    image_bytes,
    params_dict,
    final_score,
    category,
    verdict,
    geom,
    bot_username=None,
    gender="m",
):
    cfg = get_gender_config(gender)
    W, H = 1080, 1360
    canvas = Image.new("RGBA", (W, H), (9, 11, 16, 255))
    draw = ImageDraw.Draw(canvas)

    f_brand = _get_font(22, bold=True)
    f_sub = _get_font(15, bold=False)
    draw.text((34, 28), "ADONIS PSL", font=f_brand, fill=(243, 244, 246, 255))
    badge_w = int(draw.textlength(cfg["badge"], font=_get_font(11, bold=True))) + 28
    _draw_pill_badge(draw, 192, 28, max(132, badge_w), 26, cfg["badge"], tone="blue", font_size=11)

    wm = f"@{bot_username}" if bot_username else "ADONIS PSL BOT"
    wm_w = draw.textlength(wm, font=f_sub)
    draw.text((W - 34 - wm_w, 32), wm, font=f_sub, fill=(100, 116, 139, 255))

    _draw_card_box(draw, (32, 80, 412, 460))
    portrait = _crop_portrait_with_mesh(image_bytes, 356, geom=geom)
    canvas.alpha_composite(portrait, (44, 92))
    draw = ImageDraw.Draw(canvas)

    if geom and geom.get("face_shape"):
        shape_txt = geom["face_shape"]
        f_shape = _get_font(14, bold=True)
        sw = int(draw.textlength(shape_txt, font=f_shape)) + 28
        draw.rounded_rectangle(
            (58, 404, 58 + sw, 434),
            radius=15, fill=(10, 14, 22, 215), outline=(56, 70, 96, 220), width=1,
        )
        draw.text((72, 410), shape_txt, font=f_shape, fill=(241, 245, 249, 255))

    _draw_card_box(draw, (432, 80, 1048, 460))
    f_sec = _get_font(13, bold=True)
    draw.text((458, 100), "ОБЩАЯ ОЦЕНКА", font=f_sec, fill=(139, 149, 169, 255))

    f_big = _get_font(58, bold=True)
    f_slash = _get_font(26, bold=False)
    score_str = f"{final_score:.1f}"
    draw.text((458, 118), score_str, font=f_big, fill=(248, 250, 252, 255))
    score_w = draw.textlength(score_str, font=f_big)
    draw.text((462 + score_w, 146), "/8", font=f_slash, fill=(100, 116, 139, 255))

    cat_font = _get_font(16, bold=True)
    cat_w = int(draw.textlength(category.upper(), font=cat_font)) + 34
    cat_x = int(462 + score_w + 54)
    _draw_pill_badge(draw, min(cat_x, 1024 - cat_w), 136, cat_w, 34, category.upper(), tone="blue", font_size=15)

    pct = _calc_percentile(final_score)
    draw.text((458, 192), f"Выше, чем у {pct} из 100", font=_get_font(15, bold=True), fill=(96, 165, 250, 255))

    param_count = len(cfg["param_rules"])
    verdict_text = verdict or f"Объективный индекс рассчитан по {param_count} ключевым параметрам внешности."
    f_verd = _get_font(15, bold=False)
    for idx, line in enumerate(_wrap_text_px(draw, verdict_text, f_verd, max_width=560, max_lines=2)):
        draw.text((458, 220 + idx * 22), line, font=f_verd, fill=(203, 213, 225, 255))

    draw.line((458, 278, 1022, 278), fill=(30, 36, 51, 255), width=1)

    skin_vals = [params_dict[k] for k in ("Текстура кожи", "Тон кожи", "Тёмные круги") if k in params_dict]
    skin_avg = sum(skin_vals) / len(skin_vals) if skin_vals else final_score
    harmony_val = params_dict.get("Гармония", final_score)
    sym_label = f"{geom['symmetry_pct']:.0f}%" if geom else "—"
    sym_ratio = geom["symmetry_pct"] / 100.0 if geom else 0.0

    _draw_ring_gauge(draw, 545, 354, 42, sym_ratio, sym_label, "Симметрия", accent=(76, 141, 255, 255))
    _draw_ring_gauge(draw, 740, 354, 42, skin_avg / 8.0, f"{skin_avg:.1f}", "Состояние кожи", accent=(56, 189, 248, 255))
    _draw_ring_gauge(draw, 935, 354, 42, harmony_val / 8.0, f"{harmony_val:.1f}", "Гармония черт", accent=(129, 140, 248, 255))

    _draw_card_box(draw, (32, 480, 516, 1304))
    draw.text((56, 502), "ОЦЕНКИ ПО ЧЕРТАМ", font=f_sec, fill=(139, 149, 169, 255))

    ordered_keys = cfg["ordered_card_keys"]
    f_row, f_num = _get_font(16, bold=False), _get_font(16, bold=True)
    y_cursor = 540
    row_step = 57 if len(ordered_keys) >= 13 else 62

    for key in ordered_keys:
        if key == "__SYMMETRY__":
            draw.text((56, y_cursor), "Симметрия", font=f_row, fill=(226, 232, 240, 255))
            if geom:
                draw.text((238, y_cursor), f"{geom['symmetry_pct']:.0f}%", font=f_num, fill=(96, 165, 250, 255))
                _draw_pill_badge(draw, 306, y_cursor - 2, 184, 26, geom["symmetry_status"], tone=geom["symmetry_tone"], font_size=12)
            else:
                _draw_pill_badge(draw, 306, y_cursor - 2, 184, 26, "По фото анфас", tone="blue", font_size=12)
            y_cursor += row_step
            continue

        val = params_dict.get(key, final_score)
        draw.text((56, y_cursor), key, font=f_row, fill=(226, 232, 240, 255))
        draw.text((242, y_cursor), f"{val:.1f}", font=f_num, fill=(96, 165, 250, 255))

        bar_x0, bar_x1 = 306, 490
        draw.rounded_rectangle((bar_x0, y_cursor + 6, bar_x1, y_cursor + 15), radius=5, fill=(28, 35, 51, 255))
        fill_w = max(8, int((bar_x1 - bar_x0) * (val / 8.0)))
        bar_color = (52, 211, 153, 255) if val >= 5.5 else (76, 141, 255, 255)
        draw.rounded_rectangle((bar_x0, y_cursor + 6, bar_x0 + fill_w, y_cursor + 15), radius=5, fill=bar_color)
        y_cursor += row_step

    _draw_card_box(draw, (536, 480, 1048, 1038))
    prop_title = "ПРОПОРЦИИ (468 ТОЧЕК)" if (geom and geom.get("source") == "mediapipe") else "ПРОПОРЦИИ"
    draw.text((560, 502), prop_title, font=f_sec, fill=(139, 149, 169, 255))

    if geom and geom.get("metrics"):
        f_mname, f_mnorm, f_mval = _get_font(14, bold=True), _get_font(11, bold=False), _get_font(15, bold=True)
        py = 534
        for m in geom["metrics"]:
            draw.text((560, py), m["name"], font=f_mname, fill=(226, 232, 240, 255))
            draw.text((560, py + 19), m["norm"], font=f_mnorm, fill=(100, 116, 139, 255))
            if m.get("display"):
                vw = draw.textlength(m["display"], font=f_mval)
                draw.text((854 - vw, py + 7), m["display"], font=f_mval, fill=(241, 245, 249, 255))
            _draw_pill_badge(draw, 870, py + 5, 156, 25, m["status"], tone=m["tone"], font_size=11)
            py += 49
    else:
        f_empty = _get_font(15, bold=False)
        for idx, line in enumerate(_wrap_text_px(
            draw,
            "Точные геометрические замеры недоступны для этого кадра. Отправь чёткое фото анфас без сильного поворота головы.",
            f_empty, max_width=440, max_lines=3,
        )):
            draw.text((560, 720 + idx * 24), line, font=f_empty, fill=(148, 163, 184, 255))

    _draw_card_box(draw, (536, 1058, 1048, 1304))
    draw.text((560, 1076), "ГАРМОНИЯ", font=f_sec, fill=(139, 149, 169, 255))
    radar_items = [
        ("Глаза", params_dict.get("Глаза", final_score)),
        ("Брови", params_dict.get("Брови", final_score)),
        ("Губы", params_dict.get("Губы", final_score)),
        ("Нос", params_dict.get("Нос", final_score)),
        ("Пропорции", params_dict.get("Пропорции", final_score)),
        ("Скулы", params_dict.get("Скулы", final_score)),
        ("Подбородок", params_dict.get("Подбородок", final_score)),
        ("Кожа", skin_avg),
    ]
    canvas = _draw_radar_chart(canvas, 792, 1188, 72, radar_items)
    draw = ImageDraw.Draw(canvas)

    footer = f"ADONIS PSL  •  BIOMETRIC FACE ANALYSIS  •  {wm}"
    f_foot = _get_font(13, bold=False)
    fw = draw.textlength(footer, font=f_foot)
    draw.text(((W - fw) / 2, 1324), footer, font=f_foot, fill=(71, 85, 105, 255))

    with io.BytesIO() as out_buf:
        canvas.convert("RGB").save(out_buf, format="JPEG", quality=92, subsampling=0)
        return out_buf.getvalue()


def _profile_param_status(val):
    if val >= 6.5:
        return "Идеал", "green"
    if val >= 5.5:
        return "Сильно", "green"
    if val >= 4.4:
        return "В норме", "blue"
    if val >= 3.4:
        return "Зона роста", "amber"
    return "Слабо", "red"


def render_profile_report_card(image_bytes, profile_data, bot_username=None, gender="m"):
    cfg = get_gender_config(gender)
    W, H = 1080, 860
    canvas = Image.new("RGBA", (W, H), (9, 11, 16, 255))
    draw = ImageDraw.Draw(canvas)

    f_brand = _get_font(22, bold=True)
    f_sub = _get_font(15, bold=False)
    f_sec = _get_font(13, bold=True)
    draw.text((34, 26), "ADONIS PSL", font=f_brand, fill=(243, 244, 246, 255))
    p_badge = cfg["profile_badge"]
    p_badge_w = int(draw.textlength(p_badge, font=_get_font(11, bold=True))) + 28
    _draw_pill_badge(draw, 192, 26, max(152, p_badge_w), 26, p_badge, tone="blue", font_size=11)

    wm = f"@{bot_username}" if bot_username else "ADONIS PSL BOT"
    wm_w = draw.textlength(wm, font=f_sub)
    draw.text((W - 34 - wm_w, 30), wm, font=f_sub, fill=(100, 116, 139, 255))

    _draw_card_box(draw, (32, 76, 1048, 294))
    thumb = _crop_portrait_with_mesh(image_bytes, 182, geom=None)
    canvas.alpha_composite(thumb, (52, 94))
    draw = ImageDraw.Draw(canvas)

    score = profile_data["overall_score"]
    category = profile_data["category"]
    draw.text((262, 96), "ОЦЕНКА БОКОВОГО ПРОФИЛЯ", font=f_sec, fill=(139, 149, 169, 255))

    f_pbig = _get_font(56, bold=True)
    f_slash = _get_font(26, bold=False)
    s_txt = f"{score:.1f}"
    draw.text((262, 118), s_txt, font=f_pbig, fill=(248, 250, 252, 255))
    s_w = draw.textlength(s_txt, font=f_pbig)
    draw.text((266 + s_w, 146), "/8", font=f_slash, fill=(100, 116, 139, 255))

    cat_font = _get_font(15, bold=True)
    cat_w = int(draw.textlength(category.upper(), font=cat_font)) + 32
    _draw_pill_badge(draw, int(266 + s_w + 54), 136, cat_w, 32, category.upper(), tone="blue", font_size=14)

    verdict = profile_data.get("verdict") or "Структурная оценка костного каркаса, проекций и баланса профиля."
    f_verd = _get_font(15, bold=False)
    for idx, line in enumerate(_wrap_text_px(draw, verdict, f_verd, max_width=750, max_lines=2)):
        draw.text((262, 200 + idx * 24), line, font=f_verd, fill=(195, 206, 222, 255))

    _draw_card_box(draw, (32, 316, 1048, 796))
    draw.text((58, 338), "СТРУКТУРНЫЙ РАЗБОР ПРОФИЛЯ", font=f_sec, fill=(139, 149, 169, 255))

    f_row = _get_font(17, bold=True)
    f_num = _get_font(18, bold=True)
    sy = 382
    step = 66

    for item in profile_data["params"]:
        label = item["name"]
        val = item["score"]
        status = item["status"]
        tone = item["tone"]

        draw.text((58, sy), label, font=f_row, fill=(235, 240, 248, 255))
        draw.text((374, sy), f"{val:.1f}/8", font=f_num, fill=(96, 165, 250, 255))

        bar_x0, bar_x1 = 456, 826
        draw.rounded_rectangle((bar_x0, sy + 7, bar_x1, sy + 18), radius=6, fill=(28, 35, 51, 255))
        fill_w = max(10, int((bar_x1 - bar_x0) * (val / 8.0)))
        bar_col = (52, 211, 153, 255) if val >= 5.5 else ((76, 141, 255, 255) if val >= 4.4 else (251, 191, 36, 255))
        draw.rounded_rectangle((bar_x0, sy + 7, bar_x0 + fill_w, sy + 18), radius=6, fill=bar_col)

        _draw_pill_badge(draw, 850, sy - 2, 168, 30, status, tone=tone, font_size=13)
        sy += step

    footer = f"ADONIS PSL  •  SIDE PROFILE STRUCTURAL ANALYSIS  •  {wm}"
    f_foot = _get_font(13, bold=False)
    fw = draw.textlength(footer, font=f_foot)
    draw.text(((W - fw) / 2, 818), footer, font=f_foot, fill=(71, 85, 105, 255))

    with io.BytesIO() as out_buf:
        canvas.convert("RGB").save(out_buf, format="JPEG", quality=92, subsampling=0)
        return out_buf.getvalue()
def _extract_param_score(text, patterns):
    for pattern in patterns:
        m = re.search(
            rf"(?im)^[\s•\-]*(?:\d+[.)]\s*)?{pattern}[^0-9\n]*?(\d+(?:[.,]\d+)?)\s*/\s*8",
            text,
        )
        if m:
            try:
                return max(1.0, min(8.0, float(m.group(1).replace(",", "."))))
            except ValueError:
                continue
    return None


def extract_all_param_scores(text, gender="m"):
    cfg = get_gender_config(gender)
    result = {}
    for label, patterns in cfg["param_rules"]:
        value = _extract_param_score(text, patterns)
        if value is not None:
            result[label] = round(value, 1)
    return result if len(result) >= cfg["min_params_valid"] else None


def extract_final_score(text):
    for pattern in (
        r"Итоговая оценка[^0-9\n]*?(\d+(?:[.,]\d+)?)\s*/\s*8",
        r"Оценка профиля[^0-9\n]*?(\d+(?:[.,]\d+)?)\s*/\s*8",
        r"Общий потенциал[^0-9\n]*?(\d+(?:[.,]\d+)?)\s*/\s*8",
    ):
        m = re.search(pattern, text, flags=re.IGNORECASE)
        if m:
            try:
                return max(1.0, min(8.0, float(m.group(1).replace(",", "."))))
            except ValueError:
                continue
    return None


def extract_verdict(text):
    m = re.search(r"(?im)^Вердикт[:\s]+(.+)$", text)
    if not m:
        return ""
    verdict = m.group(1).strip()
    verdict = re.sub(r"https?://\S+|t\.me/\S+|@\w+", "", verdict, flags=re.IGNORECASE)
    verdict = re.sub(r"[\r\n\t]+", " ", verdict)
    verdict = re.sub(r"\s{2,}", " ", verdict).strip()
    return verdict[:170]


def normalize_adult_scores(scores_text, gender="m"):
    g = normalize_gender(gender)
    cfg = get_gender_config(g)
    verdict = extract_verdict(scores_text)
    raw_params = extract_all_param_scores(scores_text, gender=g)
    if raw_params:
        params = {k: calibrate_single_score(v) for k, v in raw_params.items()}
        ordered = [(label, params[label]) for label, _ in cfg["param_rules"] if label in params]
        weights = cfg["param_weights"]
        weighted_sum = sum(val * weights.get(label, 0.05) for label, val in ordered)
        total_weight = sum(weights.get(label, 0.05) for label, _ in ordered)
        final_score = round(weighted_sum / total_weight, 1) if total_weight > 0 else 3.8

        core_vals = [params[k] for k in cfg["core_bone_keys"] if k in params]
        if core_vals:
            core_avg = sum(core_vals) / len(core_vals)
            final_score = min(final_score, round(core_avg + 0.4, 1))

        final_score = max(1.0, min(8.0, final_score))
        category = category_by_score(final_score, gender=g)

        lines = [f"{label} {val:.1f}/8" for label, val in ordered]
        lines.append(f"Итоговая оценка: {final_score:.1f}/8")
        lines.append(f"Категория: {category}")
        if verdict:
            lines.append(f"Вердикт: {verdict}")
        return "\n".join(lines), params, final_score, category

    score = extract_final_score(scores_text)
    if score is None:
        return None, None, None, None

    score = max(1.0, min(8.0, calibrate_single_score(score)))
    category = category_by_score(score, gender=g)
    text = scores_text.strip()
    if re.search(r"(?im)^Итоговая оценка[:\s]", text):
        text = re.sub(r"(?im)^Итоговая оценка.*$", f"Итоговая оценка: {score:.1f}/8", text)
    else:
        text += f"\nИтоговая оценка: {score:.1f}/8"
    if re.search(r"(?im)^Категория[:\s]", text):
        text = re.sub(r"(?im)^Категория.*$", f"Категория: {category}", text)
    else:
        text += f"\nКатегория: {category}"
    return text[:3000], {}, score, category


def split_model_response(raw_response):
    if "===SPLIT===" in raw_response:
        parts = raw_response.split("===SPLIT===", 1)
        return parts[0].strip(), parts[1].strip()
    m = re.search(r"(?im)^(?:ЧАСТЬ\s*2[:\s]*|Глаза,\s*брови\s*и\s*т[её]мн)", raw_response)
    if m:
        idx = m.start()
        full_part = re.sub(r"(?im)^ЧАСТЬ\s*2[:\s]*\n?", "", raw_response[idx:].strip()).strip()
        return raw_response[:idx].strip(), full_part
    return raw_response.strip(), ""


def parse_profile_response(raw_response, gender="m"):
    if not raw_response or re.search(r"\bNOT_PROFILE\b", raw_response, flags=re.IGNORECASE):
        return None, ""

    g = normalize_gender(gender)
    cfg = get_gender_config(g)
    part1, part2 = split_model_response(raw_response)
    params = []
    w_sum, w_total = 0.0, 0.0

    for label, pat, weight in cfg["profile_param_rules"]:
        m = re.search(rf"(?im){pat}[^0-9\n]*?(\d+(?:[.,]\d+)?)(?:\s*/\s*8)?", part1)
        if not m:
            log_error(f"Profile parse failed ({g}): не найден параметр '{label}'")
            return None, ""
        try:
            raw_val = float(m.group(1).replace(",", "."))
            val = calibrate_single_score(raw_val)
        except ValueError:
            return None, ""
        status, tone = _profile_param_status(val)
        params.append({"name": label, "score": val, "status": status, "tone": tone})
        w_sum += val * weight
        w_total += weight

    overall_score = max(1.0, min(8.0, round(w_sum / w_total, 1)))
    category = category_by_score(overall_score, gender=g)
    verdict = extract_verdict(part1)

    lines = [f"{p['name']}: {p['score']:.1f}/8 ({p['status']})" for p in params]
    lines.append(f"Оценка профиля: {overall_score:.1f}/8")
    lines.append(f"Категория: {category}")
    if verdict:
        lines.append(f"Вердикт: {verdict}")

    profile_data = {
        "overall_score": overall_score,
        "category": category,
        "verdict": verdict,
        "params": params,
        "summary_text": "\n".join(lines),
    }
    return profile_data, part2


class GeminiAPIError(Exception):
    def __init__(self, message, code=None):
        super().__init__(message)
        self.code = code


_http_local = threading.local()
_key_lock = threading.Lock()
_key_blocked_until = {}
_pair_blocked_until = {}
_model_blocked_until = {}
_key_rr = itertools.count()
_alert_last_sent = {}

KEY_COOLDOWN_QUOTA = 60
KEY_COOLDOWN_BAD = 3600
MODEL_COOLDOWN_404 = 3600
ALERT_COOLDOWN = 600
PIPELINE_DEADLINE = 120


def _get_http_session():
    sess = getattr(_http_local, "session", None)
    if sess is None:
        sess = requests.Session()
        _http_local.session = sess
    return sess


def clean_model_text(text):
    text = text.replace("\r\n", "\n")
    text = re.sub(r"\*\*|__|`", "", text)
    text = re.sub(r"(?m)^[ \t]*#{1,6}[ \t]*", "", text)
    text = re.sub(r"(?m)^([ \t]*)[*\-][ \t]+", r"\1• ", text)
    return text.strip()


def notify_admins_once(alert_key, text):
    now = time.time()
    with _key_lock:
        if now - _alert_last_sent.get(alert_key, 0) < ALERT_COOLDOWN:
            return
        _alert_last_sent[alert_key] = now

    for admin_id in ADMIN_IDS:
        try:
            bot.send_message(admin_id, text)
        except Exception as e:
            log_error(f"Не удалось уведомить админа {admin_id}: {e}")


def call_gemini_api(api_key, model_name, image_bytes, prompt):
    url = f"{GEMINI_BASE_URL}/v1beta/models/{model_name}:generateContent"
    headers = {"Content-Type": "application/json", "x-goog-api-key": api_key.strip()}
    parts = [{"text": prompt}]
    if image_bytes is not None:
        parts.append(
            {
                "inline_data": {
                    "mime_type": "image/jpeg",
                    "data": base64.b64encode(image_bytes).decode("utf-8"),
                }
            }
        )
    payload = {
        "contents": [{"parts": parts}],
        "generationConfig": {
            "temperature": 0.2 if image_bytes is not None else 0.35,
        },
        "safetySettings": [
            {"category": "HARM_CATEGORY_HARASSMENT", "threshold": "BLOCK_ONLY_HIGH"},
            {"category": "HARM_CATEGORY_HATE_SPEECH", "threshold": "BLOCK_ONLY_HIGH"},
            {"category": "HARM_CATEGORY_SEXUALLY_EXPLICIT", "threshold": "BLOCK_ONLY_HIGH"},
            {"category": "HARM_CATEGORY_DANGEROUS_CONTENT", "threshold": "BLOCK_ONLY_HIGH"},
        ],
    }

    try:
        response = _get_http_session().post(url, json=payload, headers=headers, timeout=(8, 45))
    except requests.exceptions.RequestException as req_err:
        raise GeminiAPIError(f"Сетевая ошибка: {type(req_err).__name__}", 503)

    code = response.status_code
    if code == 200:
        try:
            resp_parts = response.json()["candidates"][0]["content"]["parts"]
            text = "".join(p.get("text", "") for p in resp_parts if not p.get("thought"))
        except (ValueError, KeyError, IndexError, TypeError, AttributeError):
            raise GeminiAPIError("Пустой ответ от модели или блокировка.", None)
        if not text.strip():
            raise GeminiAPIError("Модель вернула пустой текст.", None)
        return text

    if code == 429:
        raise GeminiAPIError("HTTP 429: исчерпан лимит модели.", 429)
    if code in (401, 403):
        raise GeminiAPIError(f"HTTP {code}: ключ недействителен.", code)
    if code == 404:
        raise GeminiAPIError(f"HTTP 404: модель {model_name} не найдена.", 404)
    if code == 400 and ("API_KEY_INVALID" in response.text or "API key not valid" in response.text):
        raise GeminiAPIError("HTTP 400: ключ недействителен.", 401)
    if code in (500, 502, 503, 504):
        raise GeminiAPIError(f"HTTP {code}: сервер перегружен.", 503)
    raise GeminiAPIError(f"HTTP {code}: {response.text[:300]}", code)


def run_gemini_pipeline(processed_bytes, prompt):
    errors = []
    skipped_by_429 = False
    skipped_by_404 = False
    skipped_by_bad_key = False
    deadline = time.time() + PIPELINE_DEADLINE
    num_keys = len(API_KEYS)
    start_idx = next(_key_rr) % num_keys
    models = get_active_models()

    for model_name in models:
        now = time.time()
        if now >= deadline:
            errors.append((504, "Превышено общее время ожидания."))
            break
        with _key_lock:
            if _model_blocked_until.get(model_name, 0) > now:
                skipped_by_404 = True
                continue

        for offset in range(num_keys):
            now = time.time()
            if now >= deadline:
                errors.append((504, "Превышено общее время ожидания."))
                return None, errors

            idx = (start_idx + offset) % num_keys
            with _key_lock:
                if _key_blocked_until.get(idx, 0) > now:
                    skipped_by_bad_key = True
                    continue
                if _pair_blocked_until.get((idx, model_name), 0) > now:
                    skipped_by_429 = True
                    continue

            try:
                raw_text = call_gemini_api(API_KEYS[idx], model_name, processed_bytes, prompt)
                return clean_model_text(raw_text), errors
            except GeminiAPIError as err:
                log_error(f"Ключ #{idx + 1} ({model_name}): {err}")
                errors.append((err.code, str(err)))
                if err.code == 400:
                    return None, errors
                with _key_lock:
                    if err.code == 429:
                        _pair_blocked_until[(idx, model_name)] = time.time() + KEY_COOLDOWN_QUOTA
                    elif err.code in (401, 403):
                        _key_blocked_until[idx] = time.time() + KEY_COOLDOWN_BAD
                        notify_admins_once(f"bad_key_{idx}", f"⚠️ Gemini API ключ #{idx + 1} вернул {err.code} и отключён.")
                    elif err.code == 404:
                        _model_blocked_until[model_name] = time.time() + MODEL_COOLDOWN_404
                        notify_admins_once(
                            f"model_404_{model_name}",
                            f"⚠️ Модель {model_name} вернула HTTP 404. Поменяй модель командой: . модель",
                        )
                        break
            except Exception as exc:
                log_error(f"Ошибка ключа #{idx + 1} ({model_name}): {exc}")
                errors.append((None, str(exc)))

    if not errors:
        if skipped_by_429:
            errors.append((429, "Все ключи временно находятся в паузе лимита 429."))
        elif skipped_by_404:
            errors.append((404, "Все активные модели временно отключены (404)."))
        elif skipped_by_bad_key:
            errors.append((401, "Все ключи временно отключены (401/403)."))

    if errors and all(code == 429 for code, _ in errors):
        notify_admins_once("all_keys_429", "⚠️ Все активные ключи Gemini упёрлись в лимит 429.")
    return None, errors


def run_gemini_text_pipeline(prompt):
    return run_gemini_pipeline(None, prompt)


def format_api_failure(api_errors):
    codes = {code for code, _ in (api_errors or [])}
    if 429 in codes:
        return "⏳ <b>Серверы анализа временно перегружены.</b>\nСкан возвращён на баланс — попробуй через 1 минуту."
    if 401 in codes or 403 in codes or 404 in codes:
        return "⚠️ <b>Временная ошибка подключения к нейросети.</b>\nСкан возвращён на баланс, администратор уведомлён."
    return "⏳ <b>Не удалось получить ответ от сервера анализа.</b>\nСкан возвращён на баланс — попробуй ещё раз."


_media_group_lock = threading.Lock()
_seen_media_groups = {}


def _is_duplicate_media_group(user_id, media_group_id):
    if not media_group_id:
        return False
    now = time.time()
    key = (user_id, str(media_group_id))
    with _media_group_lock:
        if len(_seen_media_groups) > 500:
            cutoff = now - 60.0
            stale = [k for k, ts in _seen_media_groups.items() if ts < cutoff]
            for k in stale:
                del _seen_media_groups[k]
        if key in _seen_media_groups and (now - _seen_media_groups[key]) < 30.0:
            return True
        _seen_media_groups[key] = now
        return False


def send_status_safe(message, text):
    try:
        return bot.reply_to(message, text)
    except Exception:
        try:
            return bot.send_message(message.chat.id, text)
        except Exception as e:
            log_error(f"Не удалось отправить статус: {e}")
            return None


def delete_status_safe(chat_id, status_msg):
    if not status_msg:
        return
    try:
        bot.delete_message(chat_id, status_msg.message_id)
    except Exception:
        pass


def safe_answer(call_id, text=None, show_alert=False):
    try:
        bot.answer_callback_query(call_id, text, show_alert=show_alert)
    except Exception as e:
        log_error(f"answer_callback_query: {e}")


def edit_or_send(chat_id, text, reply_markup=None, message_id=None, parse_mode="HTML"):
    if message_id:
        try:
            bot.edit_message_text(
                text,
                chat_id=chat_id,
                message_id=message_id,
                parse_mode=parse_mode,
                reply_markup=reply_markup,
                disable_web_page_preview=True,
            )
            return
        except Exception as e:
            if "message is not modified" in str(e).lower():
                return
    bot.send_message(
        chat_id,
        text,
        parse_mode=parse_mode,
        reply_markup=reply_markup,
        disable_web_page_preview=True,
    )


def send_long_html(chat_id, title, text, limit=3500):
    chunks, current = [], ""
    for line in text.split("\n"):
        while len(line) > limit:
            if current:
                chunks.append(current)
                current = ""
            chunks.append(line[:limit])
            line = line[limit:]
        if current and len(current) + len(line) + 1 > limit:
            chunks.append(current)
            current = line
        else:
            current = f"{current}\n{line}" if current else line
    if current:
        chunks.append(current)

    for i, chunk in enumerate(chunks):
        header = f"<b>{html.escape(title)}</b>\n\n" if i == 0 else ""
        try:
            bot.send_message(chat_id, header + html.escape(chunk), parse_mode="HTML")
        except Exception:
            plain = f"{title}\n\n{chunk}" if i == 0 else chunk
            bot.send_message(chat_id, plain, parse_mode=None)


def is_image_document(message):
    doc = getattr(message, "document", None)
    if not doc:
        return False
    mime = (doc.mime_type or "").lower()
    fname = (doc.file_name or "").lower()
    return mime.startswith("image/") or fname.endswith((".jpg", ".jpeg", ".png", ".webp", ".bmp"))


def get_message_media_file_id(message):
    if getattr(message, "photo", None):
        return message.photo[-1].file_id
    if getattr(message, "document", None):
        return message.document.file_id
    return ""


def download_and_process_file_id(file_id, known_size=0):
    if not file_id:
        raise ValueError("Файл изображения не найден.")
    if (known_size or 0) > MAX_IMAGE_FILE_SIZE:
        raise ValueError("Файл слишком большой (максимум 15 МБ).")

    file_info = bot.get_file(file_id)
    if (file_info.file_size or 0) > MAX_IMAGE_FILE_SIZE:
        raise ValueError("Файл слишком большой (максимум 15 МБ).")

    raw_bytes = bot.download_file(file_info.file_path)
    try:
        with io.BytesIO(raw_bytes) as in_buf, Image.open(in_buf) as img:
            img = ImageOps.exif_transpose(img)
            if img.width < 64 or img.height < 64:
                raise ValueError("Изображение слишком маленькое. Пришли чёткое фото лица.")
            rgb = img.convert("RGB")
            rgb.thumbnail((1280, 1280), Image.Resampling.LANCZOS)
            with io.BytesIO() as out_buf:
                rgb.save(out_buf, format="JPEG", quality=90, optimize=True)
                return out_buf.getvalue()
    except ValueError:
        raise
    except Image.DecompressionBombError:
        raise ValueError("Изображение имеет слишком высокое разрешение.")
    except Exception:
        raise ValueError("Не удалось прочитать изображение. Пришли обычный JPG или PNG.")


def download_and_process_photo(message):
    if message.photo:
        file_obj = message.photo[-1]
    elif message.document:
        file_obj = message.document
    else:
        raise ValueError("Пришли фото лица.")
    return download_and_process_file_id(file_obj.file_id, getattr(file_obj, "file_size", 0) or 0)


def setup_bot_commands():
    default_commands = [
        BotCommand("start", "Главное меню"),
        BotCommand("buy", "Тарифы и сканы"),
        BotCommand("ref", "Пригласить друга (+1 скан)"),
        BotCommand("scale", "Шкала PSL 1.0–8.0"),
        BotCommand("paysupport", "Поддержка"),
    ]
    admin_commands = default_commands + [
        BotCommand("admin", "Шпаргалка по админке"),
        BotCommand("model", "Сменить модель Gemini"),
    ]
    try:
        bot.set_my_commands(default_commands, scope=BotCommandScopeDefault())
        for admin_id in ADMIN_IDS:
            bot.set_my_commands(admin_commands, scope=BotCommandScopeChat(chat_id=admin_id))
    except Exception as e:
        log_error(f"Не удалось выставить меню команд: {e}")


def format_user_status_short(user_id):
    free_limit, pro_tier, pro_until, _ = get_user_access(user_id)
    if is_admin(user_id):
        return "👑 <b>Администратор</b> • без лимитов"
    extra_str = f" (+{free_limit} доп.)" if free_limit > 0 else ""
    if pro_tier >= 2:
        left = get_pro_remaining_today(user_id, pro_tier)
        return f"💎 <b>PRO Навсегда</b> • сегодня {left}/{PRO_LIFE_DAILY_LIMIT}{extra_str}"
    if pro_tier == 1:
        left = get_pro_remaining_today(user_id, pro_tier)
        until_str = format_date_from_ts(pro_until) if pro_until > 0 else "—"
        return f"👑 <b>PRO до {until_str}</b> • сегодня {left}/{PRO30_DAILY_LIMIT}{extra_str}"
    return f"⚡ <b>Базовый</b> • доступно сканов: <b>{free_limit}</b>"


def format_score_delta(delta):
    if delta is None:
        return ""
    if delta > 0.05:
        return f"📈 +{delta:.1f} к прошлому скану"
    if delta < -0.05:
        return f"📉 {delta:.1f} к прошлому скану"
    return "➖ без изменений к прошлому скану"


def preview_score_delta(user_id, new_score):
    if new_score is None:
        return None
    _, best_score, _, _, _, _, last_score, _ = get_user_profile_stats(user_id)
    ref_score = last_score if last_score > 0.0 else best_score
    if ref_score <= 0.0:
        return None
    return round(float(new_score) - float(ref_score), 1)


def fulfill_crypto_payment(invoice_id, invoice_data=None, notify_user=True):
    resolved = mark_crypto_invoice_paid(invoice_id)
    if not resolved:
        return False, ""
    user_id, plan_id, promo_code, rub_amount = resolved
    plan = PLANS.get(plan_id)
    if not plan:
        return False, ""

    if promo_code:
        consume_discount_promo(user_id, promo_code)
    apply_plan_to_user(user_id, plan_id)

    if notify_user:
        try:
            bot.send_message(
                user_id,
                f"✅ <b>Оплата через @CryptoBot подтверждена!</b>\n"
                f"Активировано: <b>{html.escape(plan['title'])}</b>.",
                parse_mode="HTML",
            )
        except Exception as e:
            log_error(f"Не удалось уведомить юзера {user_id} об оплате CryptoBot: {e}")

    _, _, _, uname, _, _, _, _ = get_user_profile_stats(user_id)
    username = f"@{uname}" if uname else "без юзернейма"
    promo_str = f" (промокод {html.escape(promo_code)})" if promo_code else ""
    asset_info = ""
    if isinstance(invoice_data, dict) and invoice_data.get("paid_asset"):
        asset_info = f" [{invoice_data.get('paid_amount', '')} {invoice_data.get('paid_asset', '')}]"

    for admin_id in ADMIN_IDS:
        try:
            bot.send_message(
                admin_id,
                f"💎 <b>Оплата @CryptoBot</b>\n"
                f"Счёт: <code>#{invoice_id}</code>\n"
                f"Юзер: <code>{user_id}</code> ({html.escape(username)})\n"
                f"Тариф: {html.escape(plan['title'])} — <b>{rub_amount} ₽</b>{html.escape(asset_info)}{promo_str}",
                parse_mode="HTML",
            )
        except Exception:
            pass

    return True, plan["title"]


def on_crypto_invoice_expired(invoice_id):
    mark_crypto_invoice_status(invoice_id, "expired")


crypto_poller = CryptoInvoicePoller(
    crypto_client,
    fetch_active_fn=fetch_active_crypto_invoices_for_poller,
    on_paid_fn=lambda inv_id, item: fulfill_crypto_payment(inv_id, item, notify_user=True),
    on_expired_fn=on_crypto_invoice_expired,
    interval=25,
    log_fn=log_error,
)


def build_main_menu_view(user_id):
    free_limit, pro_tier, _, _ = get_user_access(user_id)
    status_line = format_user_status_short(user_id)
    scans_cnt, best_score, _, _, _, _, last_score, prev_score = get_user_profile_stats(user_id)
    best_line = f" • Лучший балл: <b>{best_score:.1f}/8</b>" if best_score > 0 else ""
    delta_line = ""
    if last_score > 0 and prev_score > 0:
        d_txt = format_score_delta(round(last_score - prev_score, 1))
        if d_txt:
            delta_line = f"\nПоследний скан: <b>{last_score:.1f}/8</b> ({d_txt})"

    sub_hint = ""
    if (
        not is_admin(user_id)
        and pro_tier == 0
        and free_limit <= 0
        and is_channel_bonus_enabled()
        and not is_channel_bonus_claimed(user_id)
    ):
        sub_hint = (
            f"\n\n🎁 <b>Получи +{CHANNEL_SUB_BONUS} бесплатный скан:</b> "
            "подпишись на наш канал кнопкой ниже!"
        )

    text = (
        "<b>ADONIS PSL • Биометрия лица</b>\n\n"
        f"<blockquote>{status_line}\n"
        f"Сканов выполнено: <b>{scans_cnt}</b>{best_line}{delta_line}</blockquote>\n\n"
        "Выбери режим ниже — анализ анфас (мужская/женская шкала), "
        f"боковой профиль PRO или <b>Баттл 1 на 1</b>.{sub_hint}"
    )

    markup = InlineKeyboardMarkup(row_width=2)
    markup.add(
        InlineKeyboardButton("📸 Анализ анфас", callback_data="scan_front_tip"),
        InlineKeyboardButton("📐 Профиль (PRO)", callback_data="profile_scan"),
    )
    markup.add(
        InlineKeyboardButton("⚔️ Баттл 1 на 1", callback_data="battle_start"),
        InlineKeyboardButton("👤 Мой профиль", callback_data="my_profile"),
    )
    markup.add(
        InlineKeyboardButton("💎 Тарифы и сканы", callback_data="buy_menu"),
        InlineKeyboardButton("🤝 Пригласить друга", callback_data="get_ref"),
    )
    if is_channel_bonus_enabled() and not is_channel_bonus_claimed(user_id):
        markup.add(
            InlineKeyboardButton("📖 Шкала PSL", callback_data="psl_scale"),
            InlineKeyboardButton(
                f"📢 +{CHANNEL_SUB_BONUS} скан за подписку",
                callback_data="channel_bonus",
            ),
        )
        markup.add(InlineKeyboardButton("🆘 Поддержка", callback_data="support_menu"))
    else:
        markup.add(
            InlineKeyboardButton("📖 Шкала PSL", callback_data="psl_scale"),
            InlineKeyboardButton("🆘 Поддержка", callback_data="support_menu"),
        )
    return text, markup


def build_psl_scale_view(gender="m"):
    g = normalize_gender(gender)
    text = get_scale_html(g)
    markup = InlineKeyboardMarkup(row_width=2)
    if g == "m":
        markup.add(InlineKeyboardButton("👩 Женская шкала", callback_data="scale_f"))
    else:
        markup.add(InlineKeyboardButton("👨 Мужская шкала", callback_data="scale_m"))
    markup.add(
        InlineKeyboardButton("📸 Сделать скан", callback_data="scan_front_tip"),
        InlineKeyboardButton("👤 Мой профиль", callback_data="my_profile"),
    )
    markup.add(InlineKeyboardButton("⬅️ Назад в меню", callback_data="main_menu"))
    return text, markup


def build_profile_cabinet_view(user_id):
    status_line = format_user_status_short(user_id)
    scans_cnt, best_score, ref_count, _, _, _, last_score, prev_score = get_user_profile_stats(user_id)
    g = get_user_gender(user_id)
    cfg = get_gender_config(g)
    best_str = (
        f"<b>{best_score:.1f}/8</b> ({category_by_score(best_score, gender=g)})"
        if best_score > 0
        else "ещё нет"
    )

    last_line = ""
    if last_score > 0:
        delta_txt = format_score_delta(round(last_score - prev_score, 1)) if prev_score > 0 else ""
        delta_part = f" • {delta_txt}" if delta_txt else ""
        last_line = f"\nПоследний скан: <b>{last_score:.1f}/8</b>{delta_part}"

    promo_code, discount_pct = get_user_active_discount(user_id)
    promo_line = (
        f"\nАктивный промокод: <code>{html.escape(promo_code)}</code> (<b>-{discount_pct}%</b>)"
        if promo_code
        else ""
    )

    uname = get_bot_username()
    ref_block = (
        f"\n🔗 Реф-ссылка:\n<code>https://t.me/{uname}?start=ref_{user_id}</code>"
        if uname
        else ""
    )

    text = (
        "<b>👤 Мой профиль</b>\n\n"
        f"<blockquote>{status_line}\n"
        f"ID: <code>{user_id}</code>\n"
        f"Шкала по умолчанию: <b>{cfg['label_short']}</b>\n"
        f"Всего сканов: <b>{scans_cnt}</b>\n"
        f"Лучший результат: {best_str}{last_line}\n"
        f"Приглашено друзей: <b>{ref_count}</b>{promo_line}</blockquote>"
        f"{ref_block}"
    )

    markup = InlineKeyboardMarkup(row_width=2)
    markup.add(
        InlineKeyboardButton("💎 Пополнить / PRO", callback_data="buy_menu"),
        InlineKeyboardButton("🎁 Промокод", callback_data="enter_promo"),
    )
    markup.add(
        InlineKeyboardButton("🤝 Рефералка", callback_data="get_ref"),
        InlineKeyboardButton("📖 Шкала PSL", callback_data="psl_scale"),
    )
    markup.add(InlineKeyboardButton("⬅️ Назад в меню", callback_data="main_menu"))
    return text, markup


def build_buy_menu_view(user_id=None):
    promo_code, discount_pct = get_user_active_discount(user_id) if user_id is not None else ("", 0)
    promo_banner = (
        f"🎁 <b>Активна скидка -{discount_pct}%</b> по промокоду <code>{html.escape(promo_code)}</code>!\n\n"
        if promo_code
        else ""
    )

    lines = []
    has_crypto = crypto_client.is_enabled()
    for plan_id, plan in PLANS.items():
        pr = get_plan_pricing(plan_id, user_id=user_id)
        if has_crypto:
            if pr["discount_pct"] > 0:
                price_txt = (
                    f"<s>{pr['orig_stars']} ⭐</s> <b>{pr['stars']} ⭐</b> / "
                    f"<s>{pr['orig_rub']} ₽</s> <b>{pr['rub']} ₽</b>"
                )
            else:
                price_txt = f"{pr['stars']} ⭐ / {pr['rub']} ₽"
        else:
            if pr["discount_pct"] > 0:
                price_txt = f"<s>{pr['orig_stars']} ⭐</s> <b>{pr['stars']} ⭐</b>"
            else:
                price_txt = f"{pr['stars']} ⭐"

        if plan_id == "pack15":
            lines.append(f"• <b>{html.escape(plan['title'])}</b> — {price_txt} <i>(выгоднее)</i>")
        elif plan_id == "pro30":
            lines.append(
                f"• <b>{html.escape(plan['title'])}</b> — {price_txt}\n"
                f"  <i>{PRO30_DAILY_LIMIT} сканов/день + профиль + план роста + приоритет</i>"
            )
        elif plan_id == "pro_life":
            lines.append(
                f"• <b>{html.escape(plan['title'])}</b> — {price_txt}\n"
                f"  <i>{PRO_LIFE_DAILY_LIMIT} сканов/день + профиль + план роста + топ-приоритет</i>"
            )
        else:
            lines.append(f"• <b>{html.escape(plan['title'])}</b> — {price_txt}")

    pay_note = (
        "Оплата через <b>Telegram Stars</b> и <b>@CryptoBot</b> (USDT, TON и др.) активируется автоматически."
        if has_crypto
        else "Оплата через <b>Telegram Stars</b> активируется мгновенно."
    )

    text = (
        "<b>💎 Тарифы и сканы</b>\n\n"
        f"{promo_banner}"
        "<blockquote>" + "\n".join(lines) + "</blockquote>\n\n"
        f"{pay_note}"
    )
    markup = InlineKeyboardMarkup(row_width=1)
    for plan_id, plan in PLANS.items():
        pr = get_plan_pricing(plan_id, user_id=user_id)
        disc_tag = f" (-{pr['discount_pct']}%)" if pr["discount_pct"] > 0 else ""
        btn_price = f"{pr['stars']} ⭐ / {pr['rub']} ₽" if has_crypto else f"{pr['stars']} ⭐"
        markup.add(
            InlineKeyboardButton(
                f"{plan['title']} — {btn_price}{disc_tag}",
                callback_data=f"plan_{plan_id}",
            )
        )
    markup.add(InlineKeyboardButton("🎁 Ввести промокод", callback_data="enter_promo"))
    markup.add(InlineKeyboardButton("⬅️ Назад в меню", callback_data="main_menu"))
    return text, markup


def build_crypto_invoice_view(plan_id, invoice_id, rub_amount, pay_url, expires_at, promo_code="", discount_pct=0):
    plan = PLANS[plan_id]
    promo_note = (
        f"\nПромокод: <code>{html.escape(promo_code)}</code> (<b>-{discount_pct}%</b>)"
        if promo_code and discount_pct > 0
        else (f"\nПромокод: <code>{html.escape(promo_code)}</code>" if promo_code else "")
    )
    ttl_str = format_time_left(expires_at)
    text = (
        f"<b>💎 Оплата через @CryptoBot: {html.escape(plan['title'])}</b>\n\n"
        f"<blockquote>Счёт: <code>#{invoice_id}</code>\n"
        f"Сумма: <b>{rub_amount} ₽</b> (оплата в USDT / TON / др. по курсу CryptoBot){promo_note}\n"
        f"Действителен: <b>{ttl_str}</b></blockquote>\n\n"
        "1. Нажми <b>«Оплатить в @CryptoBot»</b> и проведи платёж.\n"
        "2. После оплаты нажми <b>«Проверить оплату»</b> (или дождись авто-зачисления в течение 30 сек)."
    )
    markup = InlineKeyboardMarkup(row_width=1)
    if pay_url:
        markup.add(InlineKeyboardButton("💎 Оплатить в @CryptoBot", url=pay_url))
    markup.add(InlineKeyboardButton("🔄 Проверить оплату", callback_data=f"cryptochk_{invoice_id}"))
    markup.add(InlineKeyboardButton("❌ Отменить счёт", callback_data=f"cryptocancel_{invoice_id}"))
    markup.add(InlineKeyboardButton("⬅️ К тарифам", callback_data="buy_menu"))
    return text, markup


def _build_progress_bar(current, target, width=10):
    ratio = max(0.0, min(1.0, current / max(1, target)))
    filled = int(round(ratio * width))
    return "█" * filled + "░" * (width - filled)


def build_ref_view(user_id):
    username = get_bot_username()
    if not username:
        return "⏳ Не удалось сформировать ссылку. Попробуй через пару секунд.", InlineKeyboardMarkup()

    _, _, ref_count, _, _, _, _, _ = get_user_profile_stats(user_id)
    ref_link = f"https://t.me/{username}?start=ref_{user_id}"
    share_text = "Оцени внешность по 8-балльной шкале в Adonis PSL:"
    share_url = f"https://t.me/share/url?url={quote(ref_link)}&text={quote(share_text)}"

    ladder_lines = []
    next_target = None
    for req_refs, pro_days in REF_MILESTONES:
        if ref_count >= req_refs:
            ladder_lines.append(f"✅ <b>{req_refs} друзей</b> → PRO на {pro_days} дн.")
        else:
            if next_target is None:
                next_target = (req_refs, pro_days)
            ladder_lines.append(f"🔒 <b>{req_refs} друзей</b> → PRO на {pro_days} дн.")

    if next_target:
        req_refs, pro_days = next_target
        bar = _build_progress_bar(ref_count, req_refs, width=10)
        left = req_refs - ref_count
        progress_txt = (
            f"\nДо <b>PRO на {pro_days} дн.</b>: <code>[{bar}]</code> "
            f"<b>{ref_count}/{req_refs}</b> (осталось {left})"
        )
    else:
        progress_txt = "\n🏆 <b>Все ступени реферальной лестницы пройдены!</b>"

    text = (
        "<b>🤝 Пригласить друга</b>\n\n"
        f"<blockquote>За каждого нового пользователя по твоей ссылке начисляется "
        f"<b>+{REFERRAL_BONUS} бесплатный скан</b>.\n"
        f"Приглашено друзей: <b>{ref_count}</b>{progress_txt}</blockquote>\n\n"
        "<b>🏆 Реферальная лестница:</b>\n"
        + "\n".join(ladder_lines)
        + f"\n\nТвоя ссылка (нажми, чтобы скопировать):\n<code>{html.escape(ref_link)}</code>"
    )
    markup = InlineKeyboardMarkup(row_width=1)
    markup.add(InlineKeyboardButton("📤 Поделиться ссылкой", url=share_url))
    markup.add(InlineKeyboardButton("⬅️ Назад в меню", callback_data="main_menu"))
    return text, markup


def build_channel_bonus_view():
    url = get_channel_url()
    text = (
        f"<b>📢 Бонус +{CHANNEL_SUB_BONUS} бесплатный скан</b>\n\n"
        "<blockquote>Подпишись на наш официальный Telegram-канал с обновлениями, разборами и промокодами, "
        "затем нажми кнопку проверки ниже.</blockquote>"
    )
    markup = InlineKeyboardMarkup(row_width=1)
    if url:
        markup.add(InlineKeyboardButton("📣 Перейти в канал", url=url))
    markup.add(InlineKeyboardButton("✅ Проверить подписку", callback_data="check_sub"))
    markup.add(InlineKeyboardButton("⬅️ Назад в меню", callback_data="main_menu"))
    return text, markup


def build_support_view():
    support_url = get_support_url()
    text = (
        "<b>🆘 Поддержка</b>\n\n"
        "<blockquote>Оплата через <b>Telegram Stars</b> и <b>@CryptoBot</b> начисляется автоматически. "
        "Если оплата через @CryptoBot не зачислилась сразу, нажми кнопку «Проверить оплату» под счётом.</blockquote>\n\n"
        "Если возник вопрос по оплате или работе бота — напиши напрямую администратору:"
    )
    markup = InlineKeyboardMarkup(row_width=1)
    if support_url:
        markup.add(InlineKeyboardButton("💬 Написать администратору", url=support_url))
    markup.add(InlineKeyboardButton("⬅️ Назад в меню", callback_data="main_menu"))
    return text, markup


def send_adult_confirm(chat_id):
    markup = InlineKeyboardMarkup()
    markup.add(InlineKeyboardButton("✅ Мне есть 18 лет", callback_data="confirm_18"))
    bot.send_message(
        chat_id,
        "Доступ к оценке внешности разрешён только пользователям 18+.\n"
        "Подтверди свой возраст кнопкой ниже:",
        reply_markup=markup,
    )


def parse_referrer_id(text):
    parts = (text or "").split(maxsplit=1)
    if len(parts) < 2:
        return None
    m = re.match(r"^ref_(\d+)$", parts[1].strip())
    return int(m.group(1)) if m else None


def parse_start_promo(text):
    parts = (text or "").split(maxsplit=1)
    if len(parts) < 2:
        return None
    m = re.match(r"^promo_([A-Za-z0-9_\-]{2,24})$", parts[1].strip())
    return m.group(1).upper() if m else None


@bot.message_handler(commands=["start"])
def cmd_start(message):
    user_id = message.from_user.id
    clear_pending_modes(user_id)
    if is_user_banned(user_id):
        bot.send_message(message.chat.id, "⛔ Доступ к боту ограничен.")
        return
    if not check_rate_limit(user_id, "cmd", min_interval=1.0, max_per_min=15):
        return

    referrer_id = parse_referrer_id(message.text)
    start_promo = parse_start_promo(message.text)
    rewarded_referrer, milestone_msg = register_user_if_new(message.from_user, referrer_id=referrer_id)
    if rewarded_referrer:
        try:
            ref_notice = (
                f"🎉 По твоей ссылке присоединился новый пользователь!\n"
                f"Начислен бонус: <b>+{REFERRAL_BONUS} бесплатный скан</b>."
            )
            if milestone_msg:
                ref_notice += f"\n\n{milestone_msg}"
            bot.send_message(rewarded_referrer, ref_notice, parse_mode="HTML")
        except Exception as e:
            log_error(f"Не удалось уведомить реферера {rewarded_referrer}: {e}")

    if start_promo:
        _, _, promo_msg = activate_promocode_for_user(user_id, start_promo)
        bot.send_message(message.chat.id, promo_msg, parse_mode="HTML")

    _, _, _, is_adult = get_user_access(user_id)
    text, markup = build_main_menu_view(user_id)
    bot.send_message(message.chat.id, text, parse_mode="HTML", reply_markup=markup)

    if not is_adult and not is_admin(user_id):
        send_adult_confirm(message.chat.id)


@bot.message_handler(commands=["buy"])
def cmd_buy(message):
    touch_user(message.from_user)
    if is_user_banned(message.from_user.id):
        return
    if not check_rate_limit(message.from_user.id, "cmd", min_interval=1.0, max_per_min=15):
        return
    clear_pending_modes(message.from_user.id)
    text, markup = build_buy_menu_view(message.from_user.id)
    bot.send_message(message.chat.id, text, parse_mode="HTML", reply_markup=markup)


@bot.message_handler(commands=["ref"])
def cmd_ref(message):
    touch_user(message.from_user)
    if is_user_banned(message.from_user.id):
        return
    if not check_rate_limit(message.from_user.id, "cmd", min_interval=1.0, max_per_min=15):
        return
    clear_pending_modes(message.from_user.id)
    text, markup = build_ref_view(message.from_user.id)
    bot.send_message(message.chat.id, text, parse_mode="HTML", reply_markup=markup)


@bot.message_handler(commands=["scale"])
def cmd_scale(message):
    touch_user(message.from_user)
    if is_user_banned(message.from_user.id):
        return
    if not check_rate_limit(message.from_user.id, "cmd", min_interval=1.0, max_per_min=15):
        return
    clear_pending_modes(message.from_user.id)
    text, markup = build_psl_scale_view(get_user_gender(message.from_user.id))
    bot.send_message(message.chat.id, text, parse_mode="HTML", reply_markup=markup)


@bot.message_handler(commands=["paysupport"])
def cmd_paysupport(message):
    touch_user(message.from_user)
    if is_user_banned(message.from_user.id):
        return
    if not check_rate_limit(message.from_user.id, "cmd", min_interval=1.0, max_per_min=15):
        return
    clear_pending_modes(message.from_user.id)
    text, markup = build_support_view()
    bot.send_message(message.chat.id, text, parse_mode="HTML", reply_markup=markup)


def get_admin_help_text():
    return (
        "<b>👑 Админ-команды (через точку)</b>\n\n"
        "<blockquote>"
        "• <code>. создать промокод 10% ADONIS 50 24ч</code> — создать промо\n"
        "  <i>Награда: 10% / 2скана / 3pro | лимит и время (30м/24ч/7д) опц.</i>\n"
        "• <code>. промокоды</code> — список промокодов и активаций\n"
        "• <code>. удалить промокод ADONIS</code> — отключить промокод\n"
        "• <code>. выдать всем 1</code> — выдать +N сканов всем пользователям\n"
        "• <code>. забрать у всех 1</code> / <code>все</code> — списать N (или все) сканы у всех\n"
        "• <code>. забрать стартовый</code> — забрать 1 неиспользованный старт-скан у новичков\n"
        "• <code>. выдать сканы @user 10</code> / <code>. забрать сканы @user 5</code>\n"
        "• <code>. выдать премиум @user 30</code> / <code>навсегда</code>\n"
        "• <code>. забрать премиум @user</code> — снять PRO\n"
        "• <code>. модель</code> — меню смены модели Gemini (или <code>. модель имя</code>)\n"
        "• <code>. стата</code> — сводка по боту (+ сканы и CryptoBot)\n"
        "• <code>. юзеры [15]</code> — последние пользователи и их активность\n"
        "• <code>. инфо @user</code> — досье по юзеру\n"
        "• <code>. рассылка</code> — рассылка с предпросмотром\n"
        "• <code>. бан @user</code> / <code>. разбан @user</code>\n"
        "• <code>. очистить кэш</code> — сбросить кэш фото\n"
        "• <code>. админ</code> — эта шпаргалка"
        "</blockquote>\n\n"
        "Вместо <code>@user</code> можно указывать числовой <code>ID</code>."
    )


def build_model_manager_view():
    active = get_active_models()
    active_str = "\n".join(f"• <code>{html.escape(m)}</code>" for m in active)
    text = (
        "<b>🤖 Управление моделью Gemini</b>\n\n"
        f"<blockquote>Активная сейчас:\n{active_str}</blockquote>\n\n"
        "Выбери быстрый пресет кнопкой ниже, введи свою модель вручную "
        "или напиши команду:\n"
        "<code>. модель gemini-3.5-flash-lite</code>\n"
        "<i>Можно указать несколько через запятую (запасной фолбэк).</i>"
    )
    markup = InlineKeyboardMarkup(row_width=1)
    for preset in PRESET_MODELS:
        prefix = "✅ " if active == [preset] else ""
        markup.add(InlineKeyboardButton(f"{prefix}{preset}", callback_data=f"setmodel_{preset}"))
    markup.add(InlineKeyboardButton("✏️ Ввести свою модель", callback_data="model_custom"))
    markup.add(InlineKeyboardButton("🔄 Сбросить паузу 404/429", callback_data="model_reset_cd"))
    markup.add(InlineKeyboardButton("🏠 Главное меню", callback_data="main_menu"))
    return text, markup


def get_bot_stats_text():
    now = int(time.time())
    today = get_today_str()
    with db_conn() as conn:
        c = conn.cursor()
        c.execute("SELECT COUNT(*) FROM users")
        total = c.fetchone()[0]
        c.execute("SELECT COUNT(*) FROM users WHERE date(created_at, 'localtime') = ?", (today,))
        new_today = c.fetchone()[0]
        c.execute("SELECT COUNT(*) FROM users WHERE COALESCE(pro_tier, 0) = 1 AND pro_until > ?", (now,))
        pro30_cnt = c.fetchone()[0]
        c.execute("SELECT COUNT(*) FROM users WHERE COALESCE(pro_tier, 0) >= 2")
        pro_life_cnt = c.fetchone()[0]
        c.execute("SELECT COUNT(*) FROM users WHERE COALESCE(is_banned, 0) = 1")
        banned_cnt = c.fetchone()[0]
        c.execute("SELECT COALESCE(SUM(scans_count), 0), COALESCE(SUM(referrals_count), 0) FROM users")
        total_scans, total_refs = c.fetchone()
        c.execute("SELECT COUNT(*), COALESCE(SUM(amount), 0) FROM stars_payments")
        stars_cnt, stars_sum = c.fetchone()
        c.execute("SELECT COUNT(*), COALESCE(SUM(rub_amount), 0) FROM crypto_payments WHERE status = 'paid'")
        crypto_cnt, crypto_sum = c.fetchone()
        c.execute("SELECT COUNT(*) FROM payment_requests WHERE status = 'approved'")
        legacy_card_cnt = c.fetchone()[0]
        c.execute("SELECT COUNT(*) FROM photo_cache")
        cached = c.fetchone()[0]
        c.execute("SELECT COALESCE(scans, 0) FROM daily_stats WHERE day = ?", (today,))
        row_today = c.fetchone()
        scans_today = row_today[0] if row_today else 0
        c.execute(
            """
            SELECT COUNT(*) FROM promocodes
            WHERE is_active = 1
              AND (expires_at = 0 OR expires_at > ?)
              AND (max_uses = 0 OR used_count < max_uses)
            """,
            (now,),
        )
        active_promos = c.fetchone()[0]

    mp_status = "✅ активен" if is_mediapipe_available() else "⚠️ визуальный режим"
    cb_status = (
        ("✅ тестнет" if CRYPTOBOT_TESTNET else "✅ активен")
        if crypto_client.is_enabled()
        else "⚪ выключен"
    )
    models_str = ", ".join(get_active_models())
    return (
        "<b>📊 Статистика ADONIS PSL</b>\n\n"
        "<blockquote>"
        f"Пользователей: <b>{total}</b> (новых сегодня: <b>+{new_today}</b>)\n"
        f"PRO 30д: <b>{pro30_cnt}</b> | PRO Навсегда: <b>{pro_life_cnt}</b> | Бан: <b>{banned_cnt}</b>\n"
        f"Всего сканов: <b>{total_scans}</b> (сегодня: <b>+{scans_today}</b>) | Рефералов: <b>{total_refs}</b>\n"
        f"Stars: <b>{stars_cnt}</b> ({stars_sum} ⭐) | CryptoBot: <b>{crypto_cnt}</b> ({crypto_sum} ₽)\n"
        f"Архив карт: <b>{legacy_card_cnt}</b> | CryptoBot: <b>{cb_status}</b>\n"
        f"Очередь: <b>{_scan_queue.qsize()}</b> | Кэш фото: <b>{cached}</b> | Промо: <b>{active_promos}</b>\n"
        f"Модели: <code>{html.escape(models_str)}</code>\n"
        f"MediaPipe 468 точек: <b>{mp_status}</b>"
        "</blockquote>"
    )


def build_user_dossier_text(target_id):
    free_limit, pro_tier, pro_until, is_adult = get_user_access(target_id)
    scans_cnt, best_score, ref_count, uname, fname, banned, last_score, prev_score = get_user_profile_stats(target_id)
    g_label = get_gender_config(get_user_gender(target_id))["label_short"]

    extra_str = f" + {free_limit} доп." if free_limit > 0 else ""
    if pro_tier >= 2:
        tier_str = f"💎 PRO Навсегда (сегодня {get_pro_remaining_today(target_id, pro_tier)}/{PRO_LIFE_DAILY_LIMIT}{extra_str})"
    elif pro_tier == 1:
        tier_str = f"👑 PRO до {format_date_from_ts(pro_until)} (сегодня {get_pro_remaining_today(target_id, pro_tier)}/{PRO30_DAILY_LIMIT}{extra_str})"
    else:
        tier_str = f"⚡ Базовый (сканов: {free_limit})"

    uname_str = f"@{uname}" if uname else "нет"
    ban_str = "⛔ Забанен" if banned else "✅ Активен"
    best_str = f"{best_score:.1f}/8" if best_score > 0 else "—"
    last_str = f"{last_score:.1f}/8" if last_score > 0 else "—"
    if last_score > 0 and prev_score > 0:
        d = round(last_score - prev_score, 1)
        last_str += f" ({d:+.1f})"

    return (
        "<b>🗂 Досье пользователя</b>\n\n"
        "<blockquote>"
        f"ID: <code>{target_id}</code>\n"
        f"Username: {html.escape(uname_str)}\n"
        f"Имя: {html.escape(fname or '—')}\n"
        f"Статус: {ban_str} | 18+: {'да' if is_adult else 'нет'} | Шкала: {g_label}\n"
        f"Тариф: {tier_str}\n"
        f"Сканов всего: <b>{scans_cnt}</b> | Лучший: <b>{best_str}</b> | Последний: <b>{last_str}</b>\n"
        f"Рефералов: <b>{ref_count}</b>"
        "</blockquote>"
    )


@bot.message_handler(commands=["admin"])
def cmd_admin_slash(message):
    if is_admin(message.from_user.id):
        bot.reply_to(message, get_admin_help_text(), parse_mode="HTML")


@bot.message_handler(commands=["model", "models"])
def cmd_model_slash(message):
    if not is_admin(message.from_user.id):
        return
    clear_pending_modes(message.from_user.id)
    parts = (message.text or "").split(maxsplit=1)
    if len(parts) == 2 and parts[1].strip():
        arg = parts[1].strip()
        if arg.lower() in ("сброс", "reset", "default"):
            saved = set_active_models(DEFAULT_MODELS)
            bot.reply_to(
                message,
                f"✅ Модель сброшена на стандартную: <code>{html.escape(', '.join(saved))}</code>",
                parse_mode="HTML",
            )
            return
        parsed = parse_models_input(arg)
        if not parsed:
            bot.reply_to(
                message,
                "⚠️ Некорректное имя модели. Пример: <code>/model gemini-3.5-flash-lite</code>",
                parse_mode="HTML",
            )
            return
        saved = set_active_models(parsed)
        bot.reply_to(
            message,
            f"✅ Активная модель обновлена:\n<code>{html.escape(', '.join(saved))}</code>",
            parse_mode="HTML",
        )
        return

    text, markup = build_model_manager_view()
    bot.reply_to(message, text, parse_mode="HTML", reply_markup=markup)


@bot.message_handler(commands=["stats"])
def cmd_stats_slash(message):
    if is_admin(message.from_user.id):
        bot.reply_to(message, get_bot_stats_text(), parse_mode="HTML")


@bot.message_handler(commands=["clear_cache"])
def cmd_clear_cache_slash(message):
    if not is_admin(message.from_user.id):
        return
    with db_conn() as conn:
        conn.cursor().execute("DELETE FROM photo_cache")
    bot.reply_to(message, "✅ Кэш фото очищен.")


@bot.message_handler(
    func=lambda m: bool(
        m.text
        and m.text.lstrip().startswith(".")
        and is_admin(m.from_user.id)
        and not is_awaiting_broadcast(m.from_user.id)
        and not is_awaiting_model(m.from_user.id)
        and not is_awaiting_promo(m.from_user.id)
    ),
    content_types=["text"],
)
def handle_admin_dot_commands(message):
    user_id = message.from_user.id
    body = re.sub(r"\s+", " ", message.text.lstrip()[1:].strip())
    low = body.lower()

    if low in ("админ", "admin", "помощь", "help"):
        bot.reply_to(message, get_admin_help_text(), parse_mode="HTML")
        return

    if low in ("стата", "статистика", "stats"):
        bot.reply_to(message, get_bot_stats_text(), parse_mode="HTML")
        return

    m_users = re.match(r"^(?:юзеры|пользователи|users)(?:\s+(\d+))?$", body, flags=re.IGNORECASE)
    if m_users:
        lim = max(1, min(30, int(m_users.group(1)))) if m_users.group(1) else 15
        with db_conn() as conn:
            c = conn.cursor()
            c.execute(
                """
                SELECT user_id, COALESCE(username, ''), COALESCE(first_name, ''),
                       COALESCE(free_limit, 0), COALESCE(pro_tier, 0),
                       COALESCE(scans_count, 0), COALESCE(best_score, 0.0)
                FROM users
                ORDER BY created_at DESC, user_id DESC
                LIMIT ?
                """,
                (lim,),
            )
            rows = c.fetchall()
        if not rows:
            bot.reply_to(message, "Пользователей пока нет.")
            return
        lines = []
        for uid, uname, fname, flim, ptier, scnt, bscore in rows:
            tag = f"@{uname}" if uname else (fname or str(uid))
            tier_icon = "💎" if ptier >= 2 else ("👑" if ptier == 1 else "⚡")
            score_part = f" | max {bscore:.1f}" if bscore > 0 else ""
            lines.append(
                f"{tier_icon} <code>{uid}</code> ({html.escape(tag[:20])}) — "
                f"баланс: <b>{flim}</b> | сканов: <b>{scnt}</b>{score_part}"
            )
        bot.reply_to(
            message,
            f"<b>👥 Последние {len(rows)} пользователей</b>\n\n<blockquote>" + "\n".join(lines) + "</blockquote>",
            parse_mode="HTML",
        )
        return

    m_give_all = re.match(
        r"^выдать\s+всем(?:\s+(?:сканы|сканов|рейты|рейтов))?\s+(\d+)$",
        body,
        flags=re.IGNORECASE,
    )
    if m_give_all:
        amount = int(m_give_all.group(1))
        if amount <= 0 or amount > 1000:
            bot.reply_to(message, "⚠️ Укажи число от 1 до 1000.")
            return
        with db_conn() as conn:
            c = conn.cursor()
            c.execute(
                "UPDATE users SET free_limit = free_limit + ? WHERE COALESCE(is_banned, 0) = 0",
                (amount,),
            )
            affected = c.rowcount
        bot.reply_to(
            message,
            f"✅ Выдано <b>+{amount} сканов</b> всем активным пользователям (затронуто: <b>{affected}</b>).",
            parse_mode="HTML",
        )
        return

    m_take_all = re.match(
        r"^(?:забрать\s+у\s+всех|списать\s+у\s+всех)(?:\s+(?:сканы|сканов|рейты|рейтов))?\s+(\S+)$",
        body,
        flags=re.IGNORECASE,
    )
    if m_take_all:
        arg = m_take_all.group(1).lower()
        if arg in ("все", "всё", "all", "0"):
            with db_conn() as conn:
                c = conn.cursor()
                c.execute("UPDATE users SET free_limit = 0 WHERE free_limit > 0")
                affected = c.rowcount
            bot.reply_to(
                message,
                f"🗑 Все сканы (free_limit) обнулены у <b>{affected}</b> пользователей.",
                parse_mode="HTML",
            )
            return
        if not arg.isdigit() or int(arg) <= 0:
            bot.reply_to(
                message,
                "⚠️ Укажи число (> 0) или слово <code>все</code>. Пример: <code>. забрать у всех 1</code>",
                parse_mode="HTML",
            )
            return
        amount = int(arg)
        with db_conn() as conn:
            c = conn.cursor()
            c.execute(
                "UPDATE users SET free_limit = MAX(0, free_limit - ?) WHERE free_limit > 0",
                (amount,),
            )
            affected = c.rowcount
        bot.reply_to(
            message,
            f"✅ Списано до <b>-{amount} сканов</b> у всех пользователей с балансом (затронуто: <b>{affected}</b>).",
            parse_mode="HTML",
        )
        return

    if low in ("забрать стартовый", "снять стартовый"):
        with db_conn() as conn:
            c = conn.cursor()
            c.execute(
                """
                UPDATE users
                SET free_limit = MAX(0, free_limit - 1)
                WHERE free_limit > 0
                  AND COALESCE(scans_count, 0) = 0
                  AND COALESCE(pro_tier, 0) = 0
                  AND COALESCE(channel_bonus_claimed, 0) = 0
                  AND COALESCE(referrals_count, 0) = 0
                """
            )
            affected = c.rowcount
        bot.reply_to(
            message,
            f"✅ Неиспользованный стартовый скан списан у <b>{affected}</b> новичков "
            "(подписчики ТГК, реферальные и купленные сканы не затронуты).",
            parse_mode="HTML",
        )
        return

    if low in ("очистить кэш", "кэш", "clear_cache"):
        with db_conn() as conn:
            conn.cursor().execute("DELETE FROM photo_cache")
        bot.reply_to(message, "✅ Кэш фото очищен.")
        return

    if low in ("промокоды", "промо", "promos"):
        rows = list_promocodes_db(limit=25)
        if not rows:
            bot.reply_to(
                message,
                "🎁 Промокодов пока нет.\n"
                "Создать: <code>. создать промокод 10% ADONIS 50 24ч</code>",
                parse_mode="HTML",
            )
            return
        now = int(time.time())
        lines = []
        for code, ptype, val, max_u, used_c, exp_at, is_act in rows:
            expired = bool(exp_at > 0 and now >= exp_at)
            exhausted = bool(max_u > 0 and used_c >= max_u)
            icon = "✅" if (is_act and not expired and not exhausted) else "⛔"
            lim_str = f"{used_c}/{max_u}" if max_u > 0 else f"{used_c}/∞"
            time_str = format_time_left(exp_at)
            lines.append(
                f"{icon} <code>{html.escape(code)}</code> — {format_promo_reward(ptype, val)} "
                f"| {lim_str} | {time_str}"
            )
        bot.reply_to(
            message,
            "<b>🎁 Промокоды</b>\n\n<blockquote>" + "\n".join(lines) + "</blockquote>",
            parse_mode="HTML",
        )
        return

    m_del_promo = re.match(r"^(?:удалить|отключить)\s+промокод\s+(\S+)$", body, flags=re.IGNORECASE)
    if m_del_promo:
        code = m_del_promo.group(1).strip().upper()
        if deactivate_promocode_db(code):
            bot.reply_to(message, f"🗑 Промокод <code>{html.escape(code)}</code> отключён.", parse_mode="HTML")
        else:
            bot.reply_to(message, f"⚠️ Промокод <code>{html.escape(code)}</code> не найден.", parse_mode="HTML")
        return

    m_new_promo = re.match(r"^создать\s+промокод\s+(.+)$", body, flags=re.IGNORECASE)
    if m_new_promo:
        tokens = m_new_promo.group(1).strip().split()
        if len(tokens) < 2:
            bot.reply_to(
                message,
                "⚠️ Формат: <code>. создать промокод 10% ADONIS [лимит] [время]</code>\n"
                "Примеры:\n"
                "• <code>. создать промокод 10% ADONIS 50 24ч</code>\n"
                "• <code>. создать промокод 2скана START 100 7д</code>\n"
                "• <code>. создать промокод 3pro VIP 20</code>",
                parse_mode="HTML",
            )
            return

        ptype, pval = parse_promo_reward_token(tokens[0])
        if not ptype:
            bot.reply_to(
                message,
                "⚠️ Некорректная награда. Укажи: <code>10%</code> (1–90%), <code>2скана</code> или <code>3pro</code>.",
                parse_mode="HTML",
            )
            return

        code = tokens[1].strip().upper()
        if not re.fullmatch(r"[A-Z0-9_\-]{2,24}", code):
            bot.reply_to(
                message,
                "⚠️ Код должен быть длиной 2–24 символа (только латиница, цифры, _ или -).",
                parse_mode="HTML",
            )
            return

        max_uses = 0
        duration_sec = 0
        for extra in tokens[2:]:
            if extra.isdigit():
                max_uses = int(extra)
                continue
            parsed_dur = parse_promo_duration_token(extra)
            if parsed_dur is not None:
                duration_sec = parsed_dur
                continue
            bot.reply_to(
                message,
                f"⚠️ Не понял параметр <code>{html.escape(extra)}</code>.\n"
                "Лимит — число (например <code>50</code>), время — <code>30м</code>, <code>24ч</code> или <code>7д</code>.",
                parse_mode="HTML",
            )
            return

        expires_at = create_promocode_db(code, ptype, pval, max_uses=max_uses, duration_sec=duration_sec)
        uname = get_bot_username()
        link_line = (
            f"\nСсылка автоактивации:\n<code>https://t.me/{uname}?start=promo_{code}</code>"
            if uname
            else ""
        )
        lim_txt = f"{max_uses} активаций" if max_uses > 0 else "безлимит"
        exp_txt = f"до {format_datetime_from_ts(expires_at)} ({format_time_left(expires_at)})" if expires_at > 0 else "бессрочно"
        bot.reply_to(
            message,
            f"✅ <b>Промокод создан!</b>\n\n"
            f"<blockquote>Код: <code>{html.escape(code)}</code>\n"
            f"Награда: <b>{format_promo_reward(ptype, pval)}</b>\n"
            f"Лимит: <b>{lim_txt}</b>\n"
            f"Срок: <b>{exp_txt}</b></blockquote>"
            f"{link_line}",
            parse_mode="HTML",
        )
        return

    m_model = re.match(r"^(?:модель|модели|model|models)(?:\s+(.+))?$", body, flags=re.IGNORECASE)
    if m_model:
        clear_pending_modes(user_id)
        arg = (m_model.group(1) or "").strip()
        if not arg:
            text, markup = build_model_manager_view()
            bot.reply_to(message, text, parse_mode="HTML", reply_markup=markup)
            return
        if arg.lower() in ("сброс", "reset", "default"):
            saved = set_active_models(DEFAULT_MODELS)
            bot.reply_to(
                message,
                f"✅ Модель сброшена на стандартную: <code>{html.escape(', '.join(saved))}</code>",
                parse_mode="HTML",
            )
            return
        parsed = parse_models_input(arg)
        if not parsed:
            bot.reply_to(
                message,
                "⚠️ Некорректное название модели. Пример: <code>. модель gemini-3.5-flash-lite</code>",
                parse_mode="HTML",
            )
            return
        saved = set_active_models(parsed)
        bot.reply_to(
            message,
            f"✅ Активная модель обновлена и сохранена:\n<code>{html.escape(', '.join(saved))}</code>",
            parse_mode="HTML",
        )
        return

    if low == "рассылка":
        clear_pending_modes(user_id)
        with _broadcast_lock:
            _broadcast_state[user_id] = {"step": "await_content"}
        markup = InlineKeyboardMarkup()
        markup.add(InlineKeyboardButton("❌ Отмена", callback_data="bc_cancel"))
        bot.reply_to(
            message,
            "📢 <b>Режим рассылки</b>\n\n"
            "Отправь следующим сообщением <b>текст</b> или <b>фото с подписью</b>. "
            "Я покажу предпросмотр с кнопкой подтверждения перед отправкой.",
            parse_mode="HTML",
            reply_markup=markup,
        )
        return

    m_grant = re.match(r"^выдать\s+премиум\s+(\S+)(?:\s+(\S+))?$", body, flags=re.IGNORECASE)
    if m_grant:
        target_id = resolve_target_user(m_grant.group(1))
        if not target_id:
            bot.reply_to(message, "⚠️ Пользователь не найден в базе. Укажи ID или дождись, пока он напишет боту.")
            return
        dur_raw = (m_grant.group(2) or "навсегда").lower()
        ensure_user(target_id)

        if dur_raw in ("навсегда", "0", "life", "forever"):
            with db_conn() as conn:
                conn.cursor().execute(
                    "UPDATE users SET is_premium = 1, pro_tier = 2, pro_until = 0 WHERE user_id = ?",
                    (target_id,),
                )
            bot.reply_to(message, f"✅ Выдан <b>PRO Навсегда</b> для <code>{target_id}</code>.", parse_mode="HTML")
            try:
                bot.send_message(target_id, "💎 Тебе активирован <b>PRO Навсегда</b>!", parse_mode="HTML")
            except Exception:
                pass
            return

        if not dur_raw.isdigit() or int(dur_raw) <= 0:
            bot.reply_to(message, "⚠️ Укажи число дней (> 0) или слово <code>навсегда</code>.", parse_mode="HTML")
            return

        days = int(dur_raw)
        now = int(time.time())
        with db_conn() as conn:
            c = conn.cursor()
            c.execute(
                "SELECT COALESCE(pro_tier, 0), COALESCE(pro_until, 0) FROM users WHERE user_id = ?",
                (target_id,),
            )
            row = c.fetchone()
            cur_tier = row[0] if row else 0
            cur_until = row[1] if row else 0
            if cur_tier >= 2:
                bot.reply_to(
                    message,
                    f"ℹ️ У <code>{target_id}</code> уже активен <b>PRO Навсегда</b>. "
                    "Чтобы снять его, используй <code>. забрать премиум</code>.",
                    parse_mode="HTML",
                )
                return
            base = max(now, cur_until) if cur_tier == 1 else now
            until_ts = base + days * 86400
            c.execute(
                "UPDATE users SET is_premium = 1, pro_tier = 1, pro_until = ? WHERE user_id = ?",
                (until_ts, target_id),
            )
        bot.reply_to(
            message,
            f"✅ Выдан <b>PRO на {days} дн.</b> (до {format_date_from_ts(until_ts)}) для <code>{target_id}</code>.",
            parse_mode="HTML",
        )
        try:
            bot.send_message(
                target_id,
                f"👑 Тебе активирован <b>PRO на {days} дн.</b> (до {format_date_from_ts(until_ts)})!",
                parse_mode="HTML",
            )
        except Exception:
            pass
        return

    m_rev = re.match(r"^забрать\s+премиум\s+(\S+)$", body, flags=re.IGNORECASE)
    if m_rev:
        target_id = resolve_target_user(m_rev.group(1))
        if not target_id:
            bot.reply_to(message, "⚠️ Пользователь не найден в базе.")
            return
        ensure_user(target_id)
        with db_conn() as conn:
            conn.cursor().execute(
                "UPDATE users SET is_premium = 0, pro_tier = 0, pro_until = 0 WHERE user_id = ?",
                (target_id,),
            )
        bot.reply_to(message, f"❌ PRO снят у <code>{target_id}</code>.", parse_mode="HTML")
        return

    m_scans = re.match(r"^выдать\s+сканы\s+(\S+)\s+(\d+)$", body, flags=re.IGNORECASE)
    if m_scans:
        target_id = resolve_target_user(m_scans.group(1))
        amount = int(m_scans.group(2))
        if not target_id:
            bot.reply_to(message, "⚠️ Пользователь не найден в базе.")
            return
        if amount <= 0:
            bot.reply_to(message, "⚠️ Количество сканов должно быть больше 0.")
            return
        ensure_user(target_id)
        with db_conn() as conn:
            conn.cursor().execute(
                "UPDATE users SET free_limit = free_limit + ? WHERE user_id = ?",
                (amount, target_id),
            )
        bot.reply_to(message, f"✅ Начислено <b>+{amount} сканов</b> юзеру <code>{target_id}</code>.", parse_mode="HTML")
        try:
            bot.send_message(target_id, f"⚡ Тебе начислено <b>+{amount} сканов</b> на баланс!", parse_mode="HTML")
        except Exception:
            pass
        return

    m_take_user = re.match(
        r"^забрать\s+(?:сканы|рейты)\s+(\S+)\s+(\S+)$",
        body,
        flags=re.IGNORECASE,
    )
    if m_take_user:
        target_id = resolve_target_user(m_take_user.group(1))
        arg = m_take_user.group(2).lower()
        if not target_id:
            bot.reply_to(message, "⚠️ Пользователь не найден в базе.")
            return
        ensure_user(target_id)
        if arg in ("все", "всё", "all", "0"):
            with db_conn() as conn:
                conn.cursor().execute("UPDATE users SET free_limit = 0 WHERE user_id = ?", (target_id,))
            bot.reply_to(message, f"🗑 Все сканы обнулены у <code>{target_id}</code>.", parse_mode="HTML")
            return
        if not arg.isdigit() or int(arg) <= 0:
            bot.reply_to(message, "⚠️ Укажи число (> 0) или <code>все</code>.", parse_mode="HTML")
            return
        amount = int(arg)
        with db_conn() as conn:
            conn.cursor().execute(
                "UPDATE users SET free_limit = MAX(0, free_limit - ?) WHERE user_id = ?",
                (amount, target_id),
            )
        bot.reply_to(message, f"✅ Списано до <b>-{amount} сканов</b> у <code>{target_id}</code>.", parse_mode="HTML")
        return

    m_info = re.match(r"^инфо\s+(\S+)$", body, flags=re.IGNORECASE)
    if m_info:
        target_id = resolve_target_user(m_info.group(1))
        if not target_id:
            bot.reply_to(message, "⚠️ Пользователь не найден в базе.")
            return
        bot.reply_to(message, build_user_dossier_text(target_id), parse_mode="HTML")
        return

    m_ban = re.match(r"^(бан|разбан)\s+(\S+)$", body, flags=re.IGNORECASE)
    if m_ban:
        action = m_ban.group(1).lower()
        target_id = resolve_target_user(m_ban.group(2))
        if not target_id:
            bot.reply_to(message, "⚠️ Пользователь не найден в базе.")
            return
        if is_admin(target_id):
            bot.reply_to(message, "⚠️ Нельзя забанить администратора.")
            return
        ensure_user(target_id)
        ban_val = 1 if action == "бан" else 0
        with db_conn() as conn:
            conn.cursor().execute("UPDATE users SET is_banned = ? WHERE user_id = ?", (ban_val, target_id))
        msg = f"⛔ Пользователь <code>{target_id}</code> забанен." if ban_val else f"✅ Пользователь <code>{target_id}</code> разбанен."
        bot.reply_to(message, msg, parse_mode="HTML")
        return

    bot.reply_to(message, "⚠️ Неизвестная команда. Напиши <code>. админ</code> для списка.", parse_mode="HTML")


def _prepare_broadcast_preview(message):
    user_id = message.from_user.id
    with _broadcast_lock:
        state = _broadcast_state.get(user_id)
    if not state or state.get("step") != "await_content":
        return False

    if message.content_type == "photo":
        payload = {
            "step": "ready",
            "type": "photo",
            "file_id": message.photo[-1].file_id,
            "caption": message.caption or "",
        }
    elif message.content_type == "text":
        payload = {
            "step": "ready",
            "type": "text",
            "text": message.text,
        }
    else:
        bot.reply_to(message, "⚠️ Для рассылки отправь текст или фото с подписью.")
        return True

    with _broadcast_lock:
        _broadcast_state[user_id] = payload

    with db_conn() as conn:
        c = conn.cursor()
        c.execute("SELECT COUNT(*) FROM users WHERE COALESCE(is_banned, 0) = 0")
        total_targets = c.fetchone()[0]

    markup = InlineKeyboardMarkup(row_width=2)
    markup.add(
        InlineKeyboardButton(f"✅ Отправить ({total_targets})", callback_data="bc_send"),
        InlineKeyboardButton("❌ Отмена", callback_data="bc_cancel"),
    )

    bot.send_message(message.chat.id, "👁 <b>Предпросмотр рассылки:</b>", parse_mode="HTML")
    if payload["type"] == "photo":
        bot.send_photo(message.chat.id, payload["file_id"], caption=payload["caption"], reply_markup=markup)
    else:
        bot.send_message(message.chat.id, payload["text"], reply_markup=markup)
    return True


def _send_broadcast_item(uid, payload):
    if payload["type"] == "photo":
        bot.send_photo(uid, payload["file_id"], caption=payload["caption"])
    else:
        bot.send_message(uid, payload["text"])


def _run_broadcast_worker(admin_chat_id, payload):
    with db_conn() as conn:
        c = conn.cursor()
        c.execute("SELECT user_id FROM users WHERE COALESCE(is_banned, 0) = 0")
        user_ids = [row[0] for row in c.fetchall()]

    ok_cnt, fail_cnt = 0, 0
    for uid in user_ids:
        sent = False
        for attempt in range(2):
            try:
                _send_broadcast_item(uid, payload)
                sent = True
                break
            except telebot.apihelper.ApiTelegramException as api_err:
                if getattr(api_err, "error_code", None) == 429 and attempt == 0:
                    retry_after = 3
                    try:
                        retry_after = int((api_err.result_json or {}).get("parameters", {}).get("retry_after", 3))
                    except Exception:
                        retry_after = 3
                    time.sleep(min(max(1, retry_after), 60) + 0.5)
                    continue
                break
            except Exception:
                break
        if sent:
            ok_cnt += 1
        else:
            fail_cnt += 1
        time.sleep(0.05)

    try:
        bot.send_message(
            admin_chat_id,
            f"📢 <b>Рассылка завершена!</b>\n"
            f"Доставлено: <b>{ok_cnt}</b> | Ошибок/блок: <b>{fail_cnt}</b>",
            parse_mode="HTML",
        )
    except Exception:
        pass


@bot.message_handler(
    func=lambda m: is_admin(m.from_user.id) and is_awaiting_broadcast(m.from_user.id),
    content_types=["text", "photo"],
)
def handle_admin_broadcast_input(message):
    _prepare_broadcast_preview(message)


@bot.message_handler(
    func=lambda m: is_admin(m.from_user.id) and is_awaiting_model(m.from_user.id),
    content_types=["text"],
)
def handle_admin_model_input(message):
    user_id = message.from_user.id
    parsed = parse_models_input(message.text)
    if not parsed:
        markup = InlineKeyboardMarkup()
        markup.add(InlineKeyboardButton("❌ Отмена", callback_data="model_cancel"))
        bot.reply_to(
            message,
            "⚠️ Некорректное имя модели. Введи название латиницей, например:\n"
            "<code>gemini-3.5-flash-lite</code>\n"
            "<i>Или несколько моделей через запятую.</i>",
            parse_mode="HTML",
            reply_markup=markup,
        )
        return

    clear_awaiting_model(user_id)
    saved = set_active_models(parsed)
    text, markup = build_model_manager_view()
    bot.reply_to(
        message,
        f"✅ Модель обновлена и сохранена: <code>{html.escape(', '.join(saved))}</code>\n\n{text}",
        parse_mode="HTML",
        reply_markup=markup,
    )


def build_report_markup(photo_hash, include_profile_btn=True, is_profile=False):
    markup = InlineKeyboardMarkup(row_width=2)
    if photo_hash:
        btn_label = "📊 Подробный разбор профиля" if is_profile else "📊 Подробный разбор"
        if is_profile:
            markup.add(InlineKeyboardButton(btn_label, callback_data=f"full_{photo_hash}"))
        else:
            markup.add(
                InlineKeyboardButton(btn_label, callback_data=f"full_{photo_hash}"),
                InlineKeyboardButton("📤 Карточка для друга", callback_data=f"share_{photo_hash}"),
            )
            markup.add(InlineKeyboardButton("📈 План роста (PRO)", callback_data=f"growth_{photo_hash}"))
    row2 = []
    if include_profile_btn and not is_profile:
        row2.append(InlineKeyboardButton("📐 Профиль (PRO)", callback_data="profile_scan"))
    row2.append(InlineKeyboardButton("⚔️ Баттл", callback_data="battle_start_new"))
    row2.append(InlineKeyboardButton("🏠 Меню", callback_data="main_menu_new"))
    markup.add(*row2)
    return markup


def _run_growth_plan_worker(chat_id, user_id, photo_hash, scores_text, full_text, status_msg):
    try:
        gender = "f" if is_female_hash(photo_hash) else "m"
        report_context = f"{scores_text}\n\n{full_text}".strip()[:4500]
        prompt = get_growth_plan_prompt(gender).format(report_context=report_context)
        plan_text, _ = run_gemini_text_pipeline(prompt)
        delete_status_safe(chat_id, status_msg)

        if not plan_text:
            bot.send_message(
                chat_id,
                "⏳ Не удалось сгенерировать план роста прямо сейчас — попробуй нажать кнопку через минуту.",
            )
            return

        cache_set_growth_plan(photo_hash, plan_text)
        send_long_html(chat_id, "📈 Персональный план роста (PRO)", plan_text)
    except Exception as e:
        log_error(f"Ошибка в _run_growth_plan_worker: {e}")
        delete_status_safe(chat_id, status_msg)
        bot.send_message(chat_id, "⏳ Технический сбой при генерации плана роста. Попробуй ещё раз.")
    finally:
        with _growth_busy_lock:
            _growth_busy.discard((user_id, photo_hash))


def _run_share_card_worker(chat_id, user_id, photo_hash, scores_text, metrics_json, source_file_id, status_msg):
    try:
        gender = "f" if is_female_hash(photo_hash) else "m"
        metrics = deserialize_metrics(metrics_json) or extract_metrics_fallback(scores_text, gender=gender)
        if not metrics:
            delete_status_safe(chat_id, status_msg)
            bot.send_message(chat_id, "⚠️ Данные отчёта устарели. Отправь фото заново для создания карточки.")
            return

        if not source_file_id:
            delete_status_safe(chat_id, status_msg)
            bot.send_message(
                chat_id,
                "ℹ️ Этот отчёт был создан до обновления. Отправь фото ещё раз, чтобы сгенерировать карточку для друга.",
            )
            return

        src_bytes = download_and_process_file_id(source_file_id)
        geom = analyze_face_geometry(src_bytes, gender=gender)
        if geom and metrics.get("symmetry_pct") is None:
            metrics["symmetry_pct"] = geom["symmetry_pct"]
        if geom and not metrics.get("face_shape"):
            metrics["face_shape"] = geom["face_shape"]

        share_bytes = render_share_card(
            src_bytes,
            metrics,
            bot_username=get_bot_username(),
            geom=geom,
            get_font_fn=_get_font,
            crop_portrait_fn=_crop_portrait_with_mesh,
        )
        delete_status_safe(chat_id, status_msg)

        uname = get_bot_username()
        wm_caption = f"📤 <b>Карточка для друга готова!</b>\nСохрани или перешли другу • @{uname}" if uname else "📤 <b>Карточка для друга готова!</b>"
        with io.BytesIO(share_bytes) as bio:
            bio.name = "adonis_share_card.jpg"
            sent = bot.send_photo(chat_id, bio, caption=wm_caption, parse_mode="HTML")
        if sent and getattr(sent, "photo", None):
            cache_set_share_file_id(photo_hash, sent.photo[-1].file_id)
    except Exception as e:
        log_error(f"Ошибка в _run_share_card_worker: {e}")
        delete_status_safe(chat_id, status_msg)
        bot.send_message(chat_id, "⏳ Не удалось собрать карточку для друга. Попробуй ещё раз.")
    finally:
        with _share_busy_lock:
            _share_busy.discard((user_id, photo_hash))
        gc.collect()


def _build_front_caption(scores_text, verdict="", limit_info="", delta_line="", gender="m"):
    g = normalize_gender(gender)
    score = extract_final_score(scores_text)
    m_cat = re.search(r"(?im)^Категория[:\s]+(.+)$", scores_text)
    cat = m_cat.group(1).strip() if m_cat else (category_by_score(score, gender=g) if score else "")
    scale_tag = "👩 " if g == "f" else ""
    head = (
        f"<b>{scale_tag}Результат: {score:.1f}/8 • {html.escape(cat)}</b>"
        if score is not None
        else "<b>Карточка анализа лица готова</b>"
    )
    delta_block = f"\n{html.escape(delta_line)}" if delta_line else ""
    quote_block = f"\n<blockquote>{html.escape(verdict)}</blockquote>" if verdict else ""
    return f"{head}{delta_block}{quote_block}{limit_info}"


def _build_profile_caption(scores_text, verdict="", limit_info="", gender="m"):
    g = normalize_gender(gender)
    score = extract_final_score(scores_text)
    m_cat = re.search(r"(?im)^Категория[:\s]+(.+)$", scores_text)
    cat = m_cat.group(1).strip() if m_cat else (category_by_score(score, gender=g) if score else "")
    head = (
        f"<b>📐 Профиль: {score:.1f}/8 • {html.escape(cat)}</b>"
        if score is not None
        else "<b>📐 Анализ бокового профиля готов</b>"
    )
    quote_block = f"\n<blockquote>{html.escape(verdict)}</blockquote>" if verdict else ""
    return f"{head}{quote_block}{limit_info}"


def _send_report_card_or_text(
    chat_id,
    card_bytes,
    scores_text,
    full_text,
    photo_hash,
    verdict="",
    limit_info="",
    delta_line="",
    is_profile=False,
    card_file_id="",
    gender="m",
):
    markup = build_report_markup(
        photo_hash if full_text else None,
        include_profile_btn=not is_profile,
        is_profile=is_profile,
    )
    if not verdict:
        verdict = extract_verdict(scores_text)

    caption = (
        _build_profile_caption(scores_text, verdict=verdict, limit_info=limit_info, gender=gender)
        if is_profile
        else _build_front_caption(scores_text, verdict=verdict, limit_info=limit_info, delta_line=delta_line, gender=gender)
    )

    if card_file_id:
        try:
            bot.send_photo(chat_id, card_file_id, caption=caption, parse_mode="HTML", reply_markup=markup)
            return card_file_id
        except Exception as e:
            log_error(f"Не удалось отправить карточку по file_id, пробую резерв: {e}")

    if card_bytes:
        try:
            with io.BytesIO(card_bytes) as bio:
                bio.name = "adonis_psl_card.jpg"
                sent = bot.send_photo(chat_id, bio, caption=caption, parse_mode="HTML", reply_markup=markup)
            if sent and getattr(sent, "photo", None):
                return sent.photo[-1].file_id
            return ""
        except Exception as e:
            log_error(f"Не удалось отправить карточку, шлю текстом: {e}")

    title = "Анализ бокового профиля:" if is_profile else "Экспресс-оценка лица:"
    delta_block = f"\n{html.escape(delta_line)}" if delta_line else ""
    bot.send_message(
        chat_id,
        f"<b>{title}</b>{delta_block}\n\n<blockquote>{html.escape(scores_text)}</blockquote>{limit_info}",
        parse_mode="HTML",
        reply_markup=markup,
    )
    return ""


def _format_full_breakdown(full_text, geom=None):
    parts = []
    if geom and geom.get("metrics"):
        title = "📐 Пропорции (468 точек лица):" if geom.get("source") == "mediapipe" else "📐 Пропорции лица:"
        lines = [title]
        for m in geom["metrics"]:
            if m.get("display"):
                lines.append(f"• {m['name']}: {m['display']} — {m['status']} ({m['norm']})")
            else:
                lines.append(f"• {m['name']}: {m['status']} ({m['norm']})")
        lines.append(f"• Симметрия: {geom['symmetry_pct']:.1f}% — {geom['symmetry_status']}")
        if geom.get("face_shape"):
            lines.append(f"• Форма лица: {geom['face_shape']}")
        parts.append("\n".join(lines))
    if full_text:
        parts.append(full_text.strip())
    return "\n\n".join(parts)


def _send_no_scans_prompt(chat_id, user_id=None, needed=1):
    has_sub_bonus = (
        user_id is not None
        and is_channel_bonus_enabled()
        and not is_channel_bonus_claimed(user_id)
    )
    markup = InlineKeyboardMarkup(row_width=1)
    if has_sub_bonus:
        markup.add(
            InlineKeyboardButton(
                f"📢 +{CHANNEL_SUB_BONUS} скан за подписку на канал",
                callback_data="channel_bonus",
            )
        )
    markup.add(InlineKeyboardButton(f"🤝 Пригласить друга (+{REFERRAL_BONUS} скан)", callback_data="get_ref"))
    markup.add(InlineKeyboardButton("💎 Купить сканы / PRO", callback_data="buy_menu"))
    markup.add(InlineKeyboardButton("🏠 Главное меню", callback_data="main_menu"))

    need_note = f"Для баттла 1 на 1 нужно минимум <b>{needed} скана</b>." if needed > 1 else "На балансе нет доступных сканов."
    if has_sub_bonus:
        msg = (
            f"❌ <b>{need_note}</b>\n\n"
            f"Подпишись на наш канал (+{CHANNEL_SUB_BONUS} бесплатный скан), "
            f"пригласи друга (+{REFERRAL_BONUS} скан) или выбери тариф:"
        )
    else:
        msg = (
            f"❌ <b>{need_note}</b>\n\n"
            f"Пригласи друга по ссылке (+{REFERRAL_BONUS} скан) или выбери тариф:"
        )
    bot.send_message(chat_id, msg, parse_mode="HTML", reply_markup=markup)


def _send_pro_daily_limit_prompt(chat_id, daily_limit, needed=1):
    markup = InlineKeyboardMarkup(row_width=1)
    markup.add(InlineKeyboardButton("⚡ Докупить пакет сканов", callback_data="buy_menu"))
    markup.add(InlineKeyboardButton("🏠 Главное меню", callback_data="main_menu"))
    if needed > 1:
        msg = (
            f"⏳ <b>Недостаточно сканов для баттла (нужно {needed}).</b>\n"
            f"Дневной лимит PRO ({daily_limit}/день) почти исчерпан — обновится завтра в 00:00 или докупи пакет доп. сканов:"
        )
    else:
        msg = (
            f"⏳ <b>Дневной лимит PRO исчерпан ({daily_limit}/{daily_limit}).</b>\n"
            "Лимит обновится завтра в 00:00, либо можно докупить пакет дополнительных сканов:"
        )
    bot.send_message(chat_id, msg, parse_mode="HTML", reply_markup=markup)


def _has_enough_scans_for_battle(user_id):
    if is_admin(user_id):
        return True, 0, 0
    free_limit, pro_tier, _, _ = get_user_access(user_id)
    if pro_tier > 0:
        daily_limit = get_pro_daily_limit_for_tier(pro_tier)
        rem_today = get_pro_remaining_today(user_id, pro_tier)
        return (rem_today + free_limit) >= BATTLE_SCAN_COST, pro_tier, daily_limit
    return free_limit >= BATTLE_SCAN_COST, 0, 0


def _analyze_front_for_battle(processed_bytes, gender, source_file_id="", fighter_num=1):
    g = normalize_gender(gender)
    photo_hash = make_photo_hash(processed_bytes, gender=g, is_profile=False)
    cached = cache_get(photo_hash)
    if cached:
        scores_text, _, _, _, _, _, metrics_json, _ = cached
        metrics = deserialize_metrics(metrics_json) or extract_metrics_fallback(scores_text, gender=g)
        if metrics and metrics.get("params"):
            return metrics, photo_hash, True, None

    geom = analyze_face_geometry(processed_bytes, gender=g)
    prompt = build_adult_prompt(format_geometry_for_prompt(geom), gender=g)
    raw_response, api_errors = run_gemini_pipeline(processed_bytes, prompt)
    if not raw_response:
        return None, photo_hash, False, format_api_failure(api_errors)

    scores_part, full_text = split_model_response(raw_response)
    verdict = extract_verdict(scores_part)
    if geom is None:
        geom = extract_visual_geometry(scores_part, gender=g)
    scores_text, params_dict, final_score, category = normalize_adult_scores(scores_part, gender=g)
    if not scores_text or not params_dict:
        return (
            None,
            photo_hash,
            False,
            f"🤔 Не удалось распознать лицо на <b>фото Бойца {fighter_num}</b>. "
            "Пришли чёткие фото анфас при хорошем свете — сканы возвращены на баланс.",
        )

    full_combined = _format_full_breakdown(full_text, geom=geom)
    card_bytes = None
    try:
        card_bytes = render_front_report_card(
            processed_bytes,
            params_dict,
            final_score,
            category,
            verdict,
            geom,
            bot_username=get_bot_username(),
            gender=g,
        )
    except Exception as card_err:
        log_error(f"Ошибка рендера карточки в баттле: {card_err}")

    sym_pct = geom["symmetry_pct"] if geom else None
    face_shape = geom.get("face_shape", "") if geom else ""
    metrics_json = serialize_metrics(
        g,
        final_score,
        category,
        verdict,
        params_dict,
        symmetry_pct=sym_pct,
        face_shape=face_shape,
    )
    cache_put(
        photo_hash,
        scores_text,
        full_combined,
        card_image=card_bytes,
        card_file_id="",
        metrics_json=metrics_json,
        source_file_id=source_file_id,
    )
    metrics = deserialize_metrics(metrics_json)
    return metrics, photo_hash, False, None


def process_battle_photos(msg1, msg2, gender="m", status_msg=None):
    user_id = msg1.from_user.id
    chat_id = msg1.chat.id
    g = normalize_gender(gender)

    admin_user = is_admin(user_id)
    free_limit, pro_tier, _, _ = get_user_access(user_id)
    daily_limit = get_pro_daily_limit_for_tier(pro_tier)

    if not admin_user:
        if pro_tier > 0:
            if (get_pro_remaining_today(user_id, pro_tier) + free_limit) < BATTLE_SCAN_COST:
                delete_status_safe(chat_id, status_msg)
                _send_pro_daily_limit_prompt(chat_id, daily_limit, needed=BATTLE_SCAN_COST)
                return
        elif free_limit < BATTLE_SCAN_COST:
            delete_status_safe(chat_id, status_msg)
            _send_no_scans_prompt(chat_id, user_id=user_id, needed=BATTLE_SCAN_COST)
            return

    try:
        if not status_msg:
            status_msg = send_status_safe(msg2, "⚔️ Анализирую обоих бойцов и считаю раунды...")
        bytes1 = download_and_process_photo(msg1)
        bytes2 = download_and_process_photo(msg2)
        fid1 = get_message_media_file_id(msg1)
        fid2 = get_message_media_file_id(msg2)
    except ValueError as val_err:
        delete_status_safe(chat_id, status_msg)
        bot.send_message(chat_id, f"⚠️ {val_err}")
        return
    except Exception as e:
        delete_status_safe(chat_id, status_msg)
        log_error(f"Ошибка скачивания фото для баттла: {e}")
        bot.send_message(chat_id, "⏳ Не удалось скачать одно из фото. Попробуй запустить баттл ещё раз.")
        return

    consumed_pro, consumed_extra = 0, 0
    if not admin_user:
        ok, consumed_pro, consumed_extra = try_consume_battle_scans(
            user_id, pro_tier, daily_limit, cost=BATTLE_SCAN_COST
        )
        if not ok:
            delete_status_safe(chat_id, status_msg)
            if pro_tier > 0:
                _send_pro_daily_limit_prompt(chat_id, daily_limit, needed=BATTLE_SCAN_COST)
            else:
                _send_no_scans_prompt(chat_id, user_id=user_id, needed=BATTLE_SCAN_COST)
            return

    battle_completed = False
    try:
        metrics1, _, _, err1 = _analyze_front_for_battle(bytes1, g, source_file_id=fid1, fighter_num=1)
        if err1 or not metrics1:
            refund_battle_scans(user_id, consumed_pro, consumed_extra)
            delete_status_safe(chat_id, status_msg)
            bot.send_message(chat_id, err1 or "⚠️ Не удалось оценить Бойца 1.", parse_mode="HTML")
            return

        metrics2, _, _, err2 = _analyze_front_for_battle(bytes2, g, source_file_id=fid2, fighter_num=2)
        if err2 or not metrics2:
            refund_battle_scans(user_id, consumed_pro, consumed_extra)
            delete_status_safe(chat_id, status_msg)
            bot.send_message(chat_id, err2 or "⚠️ Не удалось оценить Бойца 2.", parse_mode="HTML")
            return

        battle_data = compute_battle_result(metrics1, metrics2, gender=g)
        battle_bytes = render_battle_card(
            bytes1,
            bytes2,
            battle_data,
            metrics1,
            metrics2,
            bot_username=get_bot_username(),
            get_font_fn=_get_font,
        )

        if battle_data["winner"] == 1:
            res_head = f"🏆 <b>Боец 1 побеждает</b> (+{battle_data['score_diff']:.1f})"
        elif battle_data["winner"] == 2:
            res_head = f"🏆 <b>Боец 2 побеждает</b> (+{battle_data['score_diff']:.1f})"
        else:
            res_head = "🤝 <b>Ничья по итоговому баллу</b>"

        limit_info = ""
        if not admin_user:
            if pro_tier > 0:
                pro_left = get_pro_remaining_today(user_id, pro_tier)
                limit_info = f"\n<i>PRO-сканов на сегодня: {pro_left}/{daily_limit}</i>"
            else:
                rem_limit, _, _, _ = get_user_access(user_id)
                limit_info = f"\n<i>Осталось сканов: {rem_limit}</i>"

        caption = (
            f"<b>⚔️ Баттл 1 на 1</b>\n"
            f"{res_head}\n"
            f"<blockquote>Боец 1: <b>{battle_data['score1']:.1f}/8</b> ({html.escape(battle_data['cat1'])})\n"
            f"Боец 2: <b>{battle_data['score2']:.1f}/8</b> ({html.escape(battle_data['cat2'])})\n"
            f"Раунды по чертам: <b>{battle_data['wins1']} : {battle_data['wins2']}</b></blockquote>"
            f"{limit_info}"
        )

        markup = InlineKeyboardMarkup(row_width=2)
        markup.add(
            InlineKeyboardButton("⚔️ Новый баттл", callback_data="battle_start_new"),
            InlineKeyboardButton("📸 Анализ анфас", callback_data="scan_front_tip_new"),
        )
        markup.add(InlineKeyboardButton("🏠 Главное меню", callback_data="main_menu_new"))

        delete_status_safe(chat_id, status_msg)
        with io.BytesIO(battle_bytes) as bio:
            bio.name = "adonis_battle_1v1.jpg"
            bot.send_photo(chat_id, bio, caption=caption, parse_mode="HTML", reply_markup=markup)
        battle_completed = True
        record_user_scan_stats(user_id, score=None, scan_increment=BATTLE_SCAN_COST)

    except Exception as e:
        log_error(f"Ошибка в process_battle_photos: {e}")
        if not battle_completed:
            refund_battle_scans(user_id, consumed_pro, consumed_extra)
            delete_status_safe(chat_id, status_msg)
            bot.send_message(chat_id, "⏳ Технический сбой при обработке баттла. Сканы возвращены на баланс.")
    finally:
        gc.collect()


def process_adult_photo(message, status_msg=None, gender="m"):
    user_id = message.from_user.id
    chat_id = message.chat.id
    g = normalize_gender(gender)

    free_limit, pro_tier, _, _ = get_user_access(user_id)
    admin_user = is_admin(user_id)
    daily_limit = get_pro_daily_limit_for_tier(pro_tier)

    if not admin_user:
        if pro_tier > 0:
            if get_pro_remaining_today(user_id, pro_tier) <= 0 and free_limit <= 0:
                delete_status_safe(chat_id, status_msg)
                _send_pro_daily_limit_prompt(chat_id, daily_limit)
                return
        elif free_limit <= 0:
            delete_status_safe(chat_id, status_msg)
            _send_no_scans_prompt(chat_id, user_id=user_id)
            return

    try:
        if not status_msg:
            status_msg = send_status_safe(message, "⚡ Сканю пропорции лица...")
        processed_bytes = download_and_process_photo(message)
        source_file_id = get_message_media_file_id(message)
    except ValueError as val_err:
        delete_status_safe(chat_id, status_msg)
        bot.send_message(chat_id, f"⚠️ {val_err}")
        return
    except Exception as e:
        delete_status_safe(chat_id, status_msg)
        log_error(f"Ошибка скачивания фото: {e}")
        bot.send_message(chat_id, "⏳ Не удалось скачать фото. Попробуй ещё раз.")
        return

    photo_hash = make_photo_hash(processed_bytes, gender=g, is_profile=False)
    cached = cache_get(photo_hash)
    if cached:
        scores_text, full_text, card_bytes, card_file_id, _, _, _, old_src_fid = cached
        delete_status_safe(chat_id, status_msg)
        sent_fid = _send_report_card_or_text(
            chat_id,
            card_bytes,
            scores_text,
            full_text,
            photo_hash,
            is_profile=False,
            card_file_id=card_file_id,
            gender=g,
        )
        if not card_file_id and sent_fid:
            cache_set_card_file_id(photo_hash, sent_fid)
        if not old_src_fid and source_file_id:
            with db_conn() as conn:
                conn.cursor().execute(
                    "UPDATE photo_cache SET source_file_id = ? WHERE photo_hash = ?",
                    (source_file_id, photo_hash),
                )
        return

    consumed_mode = None
    if not admin_user:
        if pro_tier > 0:
            if try_consume_pro_scan(user_id, daily_limit):
                consumed_mode = "pro"
            elif try_consume_extra_scan(user_id):
                consumed_mode = "extra"
            else:
                delete_status_safe(chat_id, status_msg)
                _send_pro_daily_limit_prompt(chat_id, daily_limit)
                return
        else:
            if not try_consume_scan(user_id):
                delete_status_safe(chat_id, status_msg)
                _send_no_scans_prompt(chat_id, user_id=user_id)
                return
            consumed_mode = "free"

    def refund_if_needed():
        if consumed_mode in ("free", "extra"):
            refund_scan(user_id)
        elif consumed_mode == "pro":
            refund_pro_scan(user_id)

    scan_completed = False
    try:
        geom = analyze_face_geometry(processed_bytes, gender=g)
        prompt = build_adult_prompt(format_geometry_for_prompt(geom), gender=g)
        raw_response, api_errors = run_gemini_pipeline(processed_bytes, prompt)

        if not raw_response:
            refund_if_needed()
            delete_status_safe(chat_id, status_msg)
            bot.send_message(chat_id, format_api_failure(api_errors), parse_mode="HTML")
            return

        scores_part, full_text = split_model_response(raw_response)
        verdict = extract_verdict(scores_part)
        if geom is None:
            geom = extract_visual_geometry(scores_part, gender=g)
        scores_text, params_dict, final_score, category = normalize_adult_scores(scores_part, gender=g)

        if not scores_text:
            refund_if_needed()
            delete_status_safe(chat_id, status_msg)
            bot.send_message(chat_id, "🤔 Не удалось распознать лицо. Пришли чёткое фото анфас при хорошем свете.")
            return

        full_combined = _format_full_breakdown(full_text, geom=geom)
        card_bytes = None
        try:
            card_bytes = render_front_report_card(
                processed_bytes,
                params_dict or {},
                final_score,
                category,
                verdict,
                geom,
                bot_username=get_bot_username(),
                gender=g,
            )
        except Exception as card_err:
            log_error(f"Ошибка рендера карточки: {card_err}")

        if consumed_mode == "free":
            rem_limit, _, _, _ = get_user_access(user_id)
            limit_info = (
                "\n<i>Сканы закончились — пригласи друга (/ref) или пополни баланс (/buy).</i>"
                if rem_limit == 0
                else f"\n<i>Осталось сканов: {rem_limit}</i>"
            )
        elif consumed_mode == "extra":
            rem_limit, _, _, _ = get_user_access(user_id)
            limit_info = f"\n<i>Списан доп. скан из пакета (осталось доп.: {rem_limit})</i>"
        elif consumed_mode == "pro":
            pro_left = get_pro_remaining_today(user_id, pro_tier)
            limit_info = f"\n<i>PRO-сканов на сегодня: {pro_left}/{daily_limit}</i>"
        else:
            limit_info = ""

        delta_val = preview_score_delta(user_id, final_score)
        delta_line = format_score_delta(delta_val)

        delete_status_safe(chat_id, status_msg)
        sent_file_id = _send_report_card_or_text(
            chat_id,
            card_bytes,
            scores_text,
            full_combined,
            photo_hash,
            verdict=verdict,
            limit_info=limit_info,
            delta_line=delta_line,
            is_profile=False,
            gender=g,
        )
        scan_completed = True
        metrics_json = serialize_metrics(
            g,
            final_score,
            category,
            verdict,
            params_dict or {},
            symmetry_pct=(geom["symmetry_pct"] if geom else None),
            face_shape=(geom.get("face_shape", "") if geom else ""),
        )
        cache_put(
            photo_hash,
            scores_text,
            full_combined,
            card_image=card_bytes,
            card_file_id=sent_file_id,
            metrics_json=metrics_json,
            source_file_id=source_file_id,
        )
        record_user_scan_stats(user_id, score=final_score)

    except Exception as e:
        log_error(f"Ошибка в process_adult_photo: {e}")
        if not scan_completed:
            refund_if_needed()
            delete_status_safe(chat_id, status_msg)
            bot.send_message(chat_id, "⏳ Произошёл технический сбой. Попробуй ещё раз.")
    finally:
        gc.collect()


def process_profile_photo(message, status_msg=None, gender="m"):
    user_id = message.from_user.id
    chat_id = message.chat.id
    g = normalize_gender(gender)

    def _keep_profile_markup():
        set_awaiting_profile(user_id, gender=g)
        m = InlineKeyboardMarkup()
        m.add(InlineKeyboardButton("❌ Отмена", callback_data="cancel_profile"))
        return m

    free_limit, pro_tier, _, _ = get_user_access(user_id)
    admin_user = is_admin(user_id)
    daily_limit = get_pro_daily_limit_for_tier(pro_tier)

    if not admin_user:
        if pro_tier <= 0:
            delete_status_safe(chat_id, status_msg)
            bot.send_message(chat_id, "👑 Анализ бокового профиля доступен только с активным PRO (/buy).")
            return
        if get_pro_remaining_today(user_id, pro_tier) <= 0 and free_limit <= 0:
            delete_status_safe(chat_id, status_msg)
            _send_pro_daily_limit_prompt(chat_id, daily_limit)
            return

    try:
        if not status_msg:
            status_msg = send_status_safe(message, "📐 Анализирую структуру бокового профиля...")
        processed_bytes = download_and_process_photo(message)
    except ValueError as val_err:
        delete_status_safe(chat_id, status_msg)
        bot.send_message(
            chat_id,
            f"⚠️ {val_err}\nРежим профиля активен — отправь другое фото сбоку или нажми «Отмена».",
            reply_markup=_keep_profile_markup(),
        )
        return
    except Exception as e:
        delete_status_safe(chat_id, status_msg)
        log_error(f"Ошибка скачивания фото профиля: {e}")
        bot.send_message(chat_id, "⏳ Не удалось скачать фото. Попробуй ещё раз.", reply_markup=_keep_profile_markup())
        return

    photo_hash = make_photo_hash(processed_bytes, gender=g, is_profile=True)
    cached = cache_get(photo_hash)
    if cached:
        scores_text, full_text, card_bytes, card_file_id, _, _, _, _ = cached
        delete_status_safe(chat_id, status_msg)
        _send_report_card_or_text(
            chat_id,
            card_bytes,
            scores_text,
            full_text,
            photo_hash,
            is_profile=True,
            card_file_id=card_file_id,
            gender=g,
        )
        return

    consumed_mode = None
    if not admin_user:
        if try_consume_pro_scan(user_id, daily_limit):
            consumed_mode = "pro"
        elif try_consume_extra_scan(user_id):
            consumed_mode = "extra"
        else:
            delete_status_safe(chat_id, status_msg)
            _send_pro_daily_limit_prompt(chat_id, daily_limit)
            return

    def refund_profile_if_needed():
        if consumed_mode == "pro":
            refund_pro_scan(user_id)
        elif consumed_mode == "extra":
            refund_scan(user_id)

    scan_completed = False
    try:
        raw_response, api_errors = run_gemini_pipeline(processed_bytes, get_profile_prompt(g))
        if not raw_response:
            refund_profile_if_needed()
            delete_status_safe(chat_id, status_msg)
            bot.send_message(chat_id, format_api_failure(api_errors), parse_mode="HTML", reply_markup=_keep_profile_markup())
            return

        profile_data, full_text = parse_profile_response(raw_response, gender=g)
        if not profile_data:
            refund_profile_if_needed()
            delete_status_safe(chat_id, status_msg)
            bot.send_message(
                chat_id,
                "🤔 Не удалось распознать боковой профиль. Пришли чёткое фото строго сбоку (90°), чтобы была видна линия челюсти.\n\n"
                "<i>Режим профиля остаётся активным — отправь следующее фото или нажми «Отмена».</i>",
                parse_mode="HTML",
                reply_markup=_keep_profile_markup(),
            )
            return

        card_bytes = None
        try:
            card_bytes = render_profile_report_card(
                processed_bytes,
                profile_data,
                bot_username=get_bot_username(),
                gender=g,
            )
        except Exception as card_err:
            log_error(f"Ошибка рендера карточки профиля: {card_err}")

        if consumed_mode == "pro":
            limit_info = f"\n<i>PRO-сканов на сегодня: {get_pro_remaining_today(user_id, pro_tier)}/{daily_limit}</i>"
        elif consumed_mode == "extra":
            rem_limit, _, _, _ = get_user_access(user_id)
            limit_info = f"\n<i>Списан доп. скан из пакета (осталось доп.: {rem_limit})</i>"
        else:
            limit_info = ""

        delete_status_safe(chat_id, status_msg)
        sent_file_id = _send_report_card_or_text(
            chat_id,
            card_bytes,
            profile_data["summary_text"],
            full_text,
            photo_hash,
            verdict=profile_data.get("verdict", ""),
            limit_info=limit_info,
            is_profile=True,
            gender=g,
        )
        scan_completed = True
        cache_put(photo_hash, profile_data["summary_text"], full_text, card_image=card_bytes, card_file_id=sent_file_id)
        record_user_scan_stats(user_id, score=None)

    except Exception as e:
        log_error(f"Ошибка в process_profile_photo: {e}")
        if not scan_completed:
            refund_profile_if_needed()
            delete_status_safe(chat_id, status_msg)
            bot.send_message(chat_id, "⏳ Произошёл технический сбой. Попробуй ещё раз.")
    finally:
        gc.collect()


def scan_worker_loop():
    while True:
        _, _, scan_type, payload, status_msg = _scan_queue.get()
        if scan_type == "battle":
            msg1, msg2, gender = payload
            user_id = msg1.from_user.id
        else:
            message, gender = payload
            user_id = message.from_user.id

        try:
            if scan_type == "profile":
                process_profile_photo(message, status_msg=status_msg, gender=gender)
            elif scan_type == "battle":
                process_battle_photos(msg1, msg2, gender=gender, status_msg=status_msg)
            else:
                process_adult_photo(message, status_msg=status_msg, gender=gender)
        except Exception as e:
            log_error(f"Ошибка в scan_worker_loop: {e}")
        finally:
            release_user(user_id)
            _scan_queue.task_done()


def start_scan_workers():
    for i in range(SCAN_WORKERS):
        threading.Thread(target=scan_worker_loop, name=f"scan-worker-{i + 1}", daemon=True).start()


def _enqueue_battle(user_id, msg1, msg2, gender):
    chat_id = msg2.chat.id
    if not acquire_user(user_id):
        set_awaiting_battle(user_id, gender=gender, msg1=msg1)
        bot.send_message(chat_id, "⏳ Предыдущий запрос ещё обрабатывается — подожди пару секунд.")
        return

    try:
        _, pro_tier, _, is_adult = get_user_access(user_id)
        if not is_adult and not is_admin(user_id):
            release_user(user_id)
            set_awaiting_battle(user_id, gender=gender, msg1=None)
            send_adult_confirm(chat_id)
            return

        if not is_admin(user_id) and pro_tier <= 0 and _scan_queue.qsize() >= MAX_SCAN_QUEUE_SIZE:
            release_user(user_id)
            set_awaiting_battle(user_id, gender=gender, msg1=None)
            bot.send_message(chat_id, "⏳ Очередь переполнена. Попробуй запустить баттл через минуту.")
            return

        if is_admin(user_id) or pro_tier >= 2:
            priority = 0
            status_text = "⚔️ Баттл 1 на 1: сравниваю обоих бойцов (топ-приоритет)..."
        elif pro_tier == 1:
            priority = 1
            status_text = "⚔️ Баттл 1 на 1: сравниваю обоих бойцов (PRO-приоритет)..."
        else:
            priority = 2
            status_text = (
                "⏳ Баттл добавлен в очередь..."
                if _scan_queue.qsize() >= SCAN_WORKERS
                else "⚔️ Баттл 1 на 1: сравниваю обоих бойцов..."
            )

        status_msg = send_status_safe(msg2, status_text)
        _scan_queue.put((priority, next(_scan_seq), "battle", (msg1, msg2, gender), status_msg))
    except Exception as e:
        release_user(user_id)
        log_error(f"Ошибка постановки баттла в очередь: {e}")
        bot.send_message(chat_id, "⏳ Произошла ошибка при запуске баттла. Попробуй ещё раз.")


def _flush_battle_album(album_key):
    with _battle_album_lock:
        entry = _battle_album_buf.pop(album_key, None)
    if not entry:
        return
    msgs = entry["messages"]
    user_id = entry["user_id"]
    gender = entry["gender"]
    if len(msgs) >= 2:
        clear_awaiting_battle(user_id)
        _enqueue_battle(user_id, msgs[0], msgs[1], gender)
    elif len(msgs) == 1:
        set_awaiting_battle(user_id, gender=gender, msg1=msgs[0])
        markup = InlineKeyboardMarkup()
        markup.add(InlineKeyboardButton("❌ Отмена", callback_data="cancel_battle"))
        bot.send_message(
            msgs[0].chat.id,
            "✅ <b>Фото Бойца 1 принято!</b>\nТеперь отправь <b>фото Бойца 2</b>.",
            parse_mode="HTML",
            reply_markup=markup,
        )


def _handle_battle_photo_input(message, battle_state):
    user_id = message.from_user.id
    chat_id = message.chat.id
    gender = battle_state["gender"]
    mgid = getattr(message, "media_group_id", None)

    if message.content_type == "document" and not is_image_document(message):
        bot.send_message(chat_id, "⚠️ Для баттла пришли фото или изображение (JPG/PNG/WEBP).")
        return

    if mgid and battle_state.get("msg1") is None:
        album_key = (user_id, str(mgid))
        flush_now = False
        with _battle_album_lock:
            entry = _battle_album_buf.get(album_key)
            if entry is None:
                timer = threading.Timer(1.6, _flush_battle_album, args=(album_key,))
                timer.daemon = True
                _battle_album_buf[album_key] = {
                    "user_id": user_id,
                    "gender": gender,
                    "messages": [message],
                    "timer": timer,
                }
                timer.start()
            else:
                if len(entry["messages"]) < 2:
                    entry["messages"].append(message)
                    if len(entry["messages"]) == 2:
                        entry["timer"].cancel()
                        flush_now = True
        if flush_now:
            _flush_battle_album(album_key)
        return

    if battle_state.get("msg1") is None:
        set_awaiting_battle(user_id, gender=gender, msg1=message)
        markup = InlineKeyboardMarkup()
        markup.add(InlineKeyboardButton("❌ Отмена", callback_data="cancel_battle"))
        bot.reply_to(
            message,
            "✅ <b>Фото Бойца 1 принято!</b>\nТеперь отправь <b>фото Бойца 2</b>.",
            parse_mode="HTML",
            reply_markup=markup,
        )
        return

    pop_awaiting_battle(user_id)
    _enqueue_battle(user_id, battle_state["msg1"], message, gender)


@bot.message_handler(content_types=["photo", "document"])
def handle_photo(message):
    user_id = message.from_user.id
    touch_user(message.from_user)
    if is_user_banned(user_id):
        bot.send_message(message.chat.id, "⛔ Доступ к боту ограничен.")
        return

    if is_admin(user_id) and _prepare_broadcast_preview(message):
        return

    battle_state, battle_expired = get_awaiting_battle(user_id)
    if battle_expired:
        markup = InlineKeyboardMarkup()
        markup.add(InlineKeyboardButton("⚔️ Запустить баттл заново", callback_data="battle_start"))
        bot.send_message(
            message.chat.id,
            "⏳ <b>Режим баттла 1 на 1 истёк (15 мин).</b>\n"
            "Нажми кнопку ниже и отправь 2 фото заново, чтобы кадр не ушёл в обычный скан.",
            parse_mode="HTML",
            reply_markup=markup,
        )
        return

    if battle_state is not None:
        mgid = getattr(message, "media_group_id", None)
        is_album_second = False
        if mgid and battle_state.get("msg1") is None:
            with _battle_album_lock:
                is_album_second = (user_id, str(mgid)) in _battle_album_buf
        if not is_album_second and not check_rate_limit(user_id, "media", min_interval=1.2, max_per_min=16):
            bot.reply_to(message, "⏳ Подожди секунду перед отправкой следующего фото.")
            return
        _handle_battle_photo_input(message, battle_state)
        return

    if _is_duplicate_media_group(user_id, getattr(message, "media_group_id", None)):
        return

    if not check_rate_limit(user_id, "media", min_interval=2.5, max_per_min=10):
        bot.reply_to(message, "⏳ Слишком частые запросы. Подожди пару секунд.")
        return

    is_profile_mode, profile_expired, profile_gender = pop_awaiting_profile(user_id)
    if profile_expired:
        markup = InlineKeyboardMarkup()
        markup.add(InlineKeyboardButton("📐 Включить режим профиля", callback_data="profile_scan"))
        bot.send_message(
            message.chat.id,
            "⏳ <b>Режим анализа бокового профиля истёк (30 мин).</b>\n"
            "Нажми кнопку ниже и отправь фото заново, чтобы оно не пошло как скан анфас.",
            parse_mode="HTML",
            reply_markup=markup,
        )
        return

    if message.content_type == "document" and not is_image_document(message):
        if is_profile_mode:
            set_awaiting_profile(user_id, gender=profile_gender)
        bot.send_message(message.chat.id, "Пришли фото или изображение (JPG/PNG/WEBP).")
        return

    if not acquire_user(user_id):
        if is_profile_mode:
            set_awaiting_profile(user_id, gender=profile_gender)
        bot.send_message(message.chat.id, "⏳ Предыдущее фото ещё обрабатывается — подожди пару секунд.")
        return

    try:
        _, pro_tier, _, is_adult = get_user_access(user_id)
        if not is_adult and not is_admin(user_id):
            release_user(user_id)
            if is_profile_mode:
                set_awaiting_profile(user_id, gender=profile_gender)
            send_adult_confirm(message.chat.id)
            return

        if not is_admin(user_id) and pro_tier <= 0 and _scan_queue.qsize() >= MAX_SCAN_QUEUE_SIZE:
            release_user(user_id)
            if is_profile_mode:
                set_awaiting_profile(user_id, gender=profile_gender)
            bot.send_message(message.chat.id, "⏳ Очередь переполнена. Попробуй отправить фото через минуту.")
            return

        scan_type = "profile" if is_profile_mode else "front"
        scan_gender = profile_gender if is_profile_mode else get_user_gender(user_id)
        front_label = "Сканю пропорции по 468 точкам" if is_mediapipe_available() else "Сканю пропорции лица"

        if is_admin(user_id) or pro_tier >= 2:
            priority = 0
            status_text = (
                "📐 Анализирую боковой профиль (топ-приоритет)..."
                if is_profile_mode
                else f"⚡ {front_label} (топ-приоритет)..."
            )
        elif pro_tier == 1:
            priority = 1
            status_text = (
                "📐 Анализирую боковой профиль (PRO-приоритет)..."
                if is_profile_mode
                else f"⚡ {front_label} (PRO-приоритет)..."
            )
        else:
            priority = 2
            status_text = "⏳ Фото добавлено в очередь..." if _scan_queue.qsize() >= SCAN_WORKERS else f"⚡ {front_label}..."

        status_msg = send_status_safe(message, status_text)
        _scan_queue.put((priority, next(_scan_seq), scan_type, (message, scan_gender), status_msg))
    except Exception as e:
        release_user(user_id)
        if is_profile_mode:
            set_awaiting_profile(user_id, gender=profile_gender)
        log_error(f"Ошибка постановки фото в очередь: {e}")
        bot.send_message(message.chat.id, "⏳ Произошла ошибка при обработке фото. Попробуй ещё раз.")


def check_plan_allowed(user_id, plan):
    if plan["type"] in ("pro30", "pro_life"):
        _, pro_tier, _, _ = get_user_access(user_id)
        if pro_tier >= 2:
            return False, "У тебя уже активен PRO Навсегда!"
    return True, None


@bot.pre_checkout_query_handler(func=lambda query: True)
def handle_pre_checkout(pre_checkout_query):
    user_id = pre_checkout_query.from_user.id
    if is_user_banned(user_id):
        bot.answer_pre_checkout_query(pre_checkout_query.id, ok=False, error_message="Доступ ограничен.")
        return

    payload = pre_checkout_query.invoice_payload or ""
    parts = payload.split(":")
    if len(parts) in (3, 4) and parts[0] == "plan" and parts[1] in PLANS and parts[2] == str(user_id):
        plan_id = parts[1]
        plan = PLANS[plan_id]
        promo_code = parts[3].strip().upper() if len(parts) == 4 else ""

        if promo_code:
            pct = validate_discount_promo_for_user(user_id, promo_code)
            if pct <= 0:
                bot.answer_pre_checkout_query(
                    pre_checkout_query.id,
                    ok=False,
                    error_message="Промокод истёк, исчерпан или привязан к активному крипто-счёту. Открой /buy заново.",
                )
                return
            expected_stars = calc_discounted_price(plan["stars"], pct)
        else:
            expected_stars = plan["stars"]

        if pre_checkout_query.currency != "XTR" or pre_checkout_query.total_amount != expected_stars:
            bot.answer_pre_checkout_query(pre_checkout_query.id, ok=False, error_message="Сумма платежа не совпадает.")
            return
        ok, err_msg = check_plan_allowed(user_id, plan)
        if not ok:
            bot.answer_pre_checkout_query(pre_checkout_query.id, ok=False, error_message=err_msg or "Тариф недоступен.")
            return
        bot.answer_pre_checkout_query(pre_checkout_query.id, ok=True)
    else:
        bot.answer_pre_checkout_query(pre_checkout_query.id, ok=False, error_message="Тариф не найден.")


@bot.message_handler(content_types=["successful_payment"])
def handle_successful_payment(message):
    sp = message.successful_payment
    user_id = message.from_user.id
    parts = (sp.invoice_payload or "").split(":")
    if len(parts) not in (3, 4) or parts[0] != "plan" or parts[1] not in PLANS or parts[2] != str(user_id):
        log_error(f"Некорректный successful_payment payload от {user_id}: {sp.invoice_payload}")
        return

    plan_id = parts[1]
    plan = PLANS[plan_id]
    promo_code = parts[3].strip().upper() if len(parts) == 4 else ""

    if promo_code:
        pct = get_promo_discount_value_raw(promo_code)
        expected_stars = calc_discounted_price(plan["stars"], pct) if pct > 0 else -1
    else:
        expected_stars = plan["stars"]

    if sp.currency != "XTR" or sp.total_amount != expected_stars:
        log_error(
            f"Несовпадение суммы Stars от {user_id}: {sp.total_amount} {sp.currency} != {expected_stars} XTR"
        )
        return

    if not record_stars_payment(sp.telegram_payment_charge_id, user_id, plan_id, sp.total_amount):
        return

    if promo_code:
        consume_discount_promo(user_id, promo_code)

    apply_plan_to_user(user_id, plan_id)
    bot.send_message(
        message.chat.id,
        f"✅ <b>Оплата прошла успешно!</b>\nАктивировано: <b>{html.escape(plan['title'])}</b>.",
        parse_mode="HTML",
    )

    username = f"@{message.from_user.username}" if message.from_user.username else "без юзернейма"
    promo_str = f" (промокод {html.escape(promo_code)})" if promo_code else ""
    for admin_id in ADMIN_IDS:
        try:
            bot.send_message(
                admin_id,
                f"⭐ <b>Оплата Telegram Stars</b>\n"
                f"Юзер: <code>{user_id}</code> ({html.escape(username)})\n"
                f"Тариф: {html.escape(plan['title'])} — <b>{sp.total_amount} ⭐</b>{promo_str}",
                parse_mode="HTML",
            )
        except Exception:
            pass


def _build_front_gender_prompt():
    text = (
        "<b>📸 Анализ лица анфас</b>\n\n"
        "<b>Кого оцениваем?</b>\n"
        "Выбери пол для точного расчёта пропорций и шкалы 1.0–8.0:"
    )
    markup = InlineKeyboardMarkup(row_width=2)
    markup.add(
        InlineKeyboardButton("👨 Мужчина", callback_data="front_gender_m"),
        InlineKeyboardButton("👩 Женщина", callback_data="front_gender_f"),
    )
    markup.add(InlineKeyboardButton("⬅️ Назад в меню", callback_data="main_menu"))
    return text, markup


def _build_profile_gender_prompt():
    text = (
        "<b>📐 Анализ бокового профиля (PRO)</b>\n\n"
        "<b>Кого оцениваем?</b>\n"
        "Выбери пол для подбора профильных критериев и шкалы:"
    )
    markup = InlineKeyboardMarkup(row_width=2)
    markup.add(
        InlineKeyboardButton("👨 Мужчина", callback_data="profile_gender_m"),
        InlineKeyboardButton("👩 Женщина", callback_data="profile_gender_f"),
    )
    markup.add(InlineKeyboardButton("⬅️ Назад в меню", callback_data="main_menu"))
    return text, markup


def _build_battle_gender_prompt():
    text = (
        "<b>⚔️ Баттл 1 на 1</b>\n\n"
        "<blockquote>Два фото анфас — подробный разбор раундов по каждой черте, "
        "двойной радар и определение победителя.\n"
        f"Стоимость баттла: <b>{BATTLE_SCAN_COST} скана</b>.</blockquote>\n\n"
        "<b>Кого сравниваем?</b>\n"
        "<i>Сравнение проводится строго в рамках одной шкалы (М vs М или Ж vs Ж).</i>"
    )
    markup = InlineKeyboardMarkup(row_width=2)
    markup.add(
        InlineKeyboardButton("👨 Мужчины", callback_data="battle_gender_m"),
        InlineKeyboardButton("👩 Женщины", callback_data="battle_gender_f"),
    )
    markup.add(InlineKeyboardButton("⬅️ Назад в меню", callback_data="main_menu"))
    return text, markup


@bot.callback_query_handler(func=lambda call: True)
def callback_handler(call):
    if not call.message:
        safe_answer(call.id)
        return

    user_id = call.from_user.id
    chat_id = call.message.chat.id
    msg_id = call.message.message_id
    is_text_msg = call.message.content_type == "text"
    edit_id = msg_id if is_text_msg else None

    touch_user(call.from_user)
    if is_user_banned(user_id):
        safe_answer(call.id, "Доступ ограничен.", show_alert=True)
        return

    if not check_rate_limit(user_id, "cb", min_interval=0.4, max_per_min=35):
        safe_answer(call.id, "Не так быстро 🙂")
        return

    data = call.data or ""

    if data == "confirm_18":
        set_user_adult(user_id)
        safe_answer(call.id, "Возраст подтверждён")
        try:
            bot.edit_message_text("✅ Доступ открыт. Выбери «Анализ анфас» в меню или отправь фото лица.", chat_id, msg_id)
        except Exception:
            bot.send_message(chat_id, "✅ Доступ открыт. Выбери «Анализ анфас» в меню или отправь фото лица.")

    elif data == "main_menu":
        clear_pending_modes(user_id)
        safe_answer(call.id)
        text, markup = build_main_menu_view(user_id)
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "main_menu_new":
        clear_pending_modes(user_id)
        safe_answer(call.id)
        text, markup = build_main_menu_view(user_id)
        bot.send_message(chat_id, text, parse_mode="HTML", reply_markup=markup)

    elif data == "psl_scale":
        clear_pending_modes(user_id)
        safe_answer(call.id)
        text, markup = build_psl_scale_view(get_user_gender(user_id))
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "psl_scale_new":
        clear_pending_modes(user_id)
        safe_answer(call.id)
        text, markup = build_psl_scale_view(get_user_gender(user_id))
        bot.send_message(chat_id, text, parse_mode="HTML", reply_markup=markup)

    elif data in ("scale_m", "scale_f"):
        safe_answer(call.id)
        text, markup = build_psl_scale_view("f" if data == "scale_f" else "m")
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "scan_front_tip":
        clear_pending_modes(user_id)
        safe_answer(call.id)
        text, markup = _build_front_gender_prompt()
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "scan_front_tip_new":
        clear_pending_modes(user_id)
        safe_answer(call.id)
        text, markup = _build_front_gender_prompt()
        bot.send_message(chat_id, text, parse_mode="HTML", reply_markup=markup)

    elif data in ("front_gender_m", "front_gender_f"):
        clear_pending_modes(user_id)
        g = "f" if data == "front_gender_f" else "m"
        set_user_gender(user_id, g)
        cfg = get_gender_config(g)
        safe_answer(call.id, f"Выбрана {cfg['label_short'].lower()} шкала")
        text = (
            f"<b>📸 Анализ анфас • {cfg['label_short']} шкала</b>\n\n"
            "<blockquote>• Смотри прямо в камеру без наклона головы\n"
            "• Ровный фронтальный свет, без жёстких теней\n"
            "• Нейтральное выражение лица, без фильтров и очков</blockquote>\n\n"
            "Отправь фото прямо сюда в чат."
        )
        markup = InlineKeyboardMarkup(row_width=2)
        markup.add(
            InlineKeyboardButton("🔄 Сменить пол", callback_data="scan_front_tip"),
            InlineKeyboardButton("📖 Шкала PSL", callback_data="scale_f" if g == "f" else "scale_m"),
        )
        markup.add(InlineKeyboardButton("⬅️ Назад в меню", callback_data="main_menu"))
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "my_profile":
        clear_pending_modes(user_id)
        safe_answer(call.id)
        text, markup = build_profile_cabinet_view(user_id)
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "buy_menu":
        clear_pending_modes(user_id)
        safe_answer(call.id)
        text, markup = build_buy_menu_view(user_id)
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "enter_promo":
        clear_pending_modes(user_id)
        set_awaiting_promo(user_id)
        safe_answer(call.id, "Введи промокод")
        markup = InlineKeyboardMarkup()
        markup.add(InlineKeyboardButton("❌ Отмена", callback_data="cancel_promo"))
        edit_or_send(
            chat_id,
            "🎁 <b>Активация промокода</b>\n\n"
            "Отправь промокод следующим сообщением в чат (например: <code>ADONIS</code>).",
            reply_markup=markup,
            message_id=edit_id,
        )

    elif data == "cancel_promo":
        clear_awaiting_promo(user_id)
        safe_answer(call.id, "Отменено")
        text, markup = build_main_menu_view(user_id)
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "channel_bonus":
        clear_pending_modes(user_id)
        if not is_channel_bonus_enabled():
            safe_answer(call.id, "Бонус пока недоступен.", show_alert=True)
            return
        if is_channel_bonus_claimed(user_id):
            safe_answer(call.id, "Ты уже получил бонус за подписку!", show_alert=True)
            return
        safe_answer(call.id)
        text, markup = build_channel_bonus_view()
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "check_sub":
        if not is_channel_bonus_enabled():
            safe_answer(call.id, "Канал не настроен.", show_alert=True)
            return
        if is_channel_bonus_claimed(user_id):
            safe_answer(call.id, "Бонус уже получен!", show_alert=True)
            return
        try:
            member = bot.get_chat_member(get_channel_chat_id(), user_id)
            is_sub = getattr(member, "status", "") in ("member", "administrator", "creator")
        except Exception as e:
            log_error(f"Ошибка проверки подписки на {CHANNEL_ID}: {e}")
            safe_answer(call.id, "Не удалось проверить подписку. Попробуй позже.", show_alert=True)
            return

        if not is_sub:
            safe_answer(call.id, "Подписка не найдена. Сначала подпишись на канал!", show_alert=True)
            return

        if claim_channel_bonus(user_id):
            safe_answer(call.id, f"+{CHANNEL_SUB_BONUS} скан начислен!", show_alert=True)
            text, markup = build_main_menu_view(user_id)
            edit_or_send(
                chat_id,
                f"🎉 <b>Спасибо за подписку!</b> Начислено <b>+{CHANNEL_SUB_BONUS} бесплатный скан</b>.\n\n{text}",
                reply_markup=markup,
                message_id=edit_id,
            )
        else:
            safe_answer(call.id, "Бонус уже был выдан ранее.", show_alert=True)

    elif data == "get_ref":
        clear_pending_modes(user_id)
        safe_answer(call.id)
        text, markup = build_ref_view(user_id)
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "support_menu":
        clear_pending_modes(user_id)
        safe_answer(call.id)
        text, markup = build_support_view()
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "profile_scan":
        clear_pending_modes(user_id)
        _, pro_tier, _, _ = get_user_access(user_id)
        if pro_tier <= 0 and not is_admin(user_id):
            safe_answer(call.id, "Доступно в PRO")
            markup = InlineKeyboardMarkup(row_width=1)
            markup.add(InlineKeyboardButton("👑 Подключить PRO", callback_data="buy_menu"))
            markup.add(InlineKeyboardButton("🤝 Получить PRO за друзей", callback_data="get_ref"))
            markup.add(InlineKeyboardButton("⬅️ Назад в меню", callback_data="main_menu"))
            text = (
                "<b>📐 Анализ бокового профиля (PRO)</b>\n\n"
                "<blockquote>Структурная карточка по 6 ключевым параметрам (мужская и женская шкалы):\n"
                "• Проекция подбородка и максиллы\n"
                "• Контур и чёткость нижней челюсти\n"
                "• Шейно-подбородочный переход\n"
                "• Профиль носа и общая гармония</blockquote>\n\n"
                "Открывается на тарифах <b>PRO 30 дней</b> и <b>PRO Навсегда</b>."
            )
            edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)
            return

        safe_answer(call.id)
        text, markup = _build_profile_gender_prompt()
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data in ("profile_gender_m", "profile_gender_f"):
        clear_pending_modes(user_id)
        _, pro_tier, _, _ = get_user_access(user_id)
        if pro_tier <= 0 and not is_admin(user_id):
            safe_answer(call.id, "Доступно только с PRO.", show_alert=True)
            return
        g = "f" if data == "profile_gender_f" else "m"
        set_user_gender(user_id, g)
        set_awaiting_profile(user_id, gender=g)
        cfg = get_gender_config(g)
        safe_answer(call.id, "Отправь фото в профиль")
        markup = InlineKeyboardMarkup(row_width=2)
        markup.add(
            InlineKeyboardButton("🔄 Сменить пол", callback_data="profile_scan"),
            InlineKeyboardButton("❌ Отмена", callback_data="cancel_profile"),
        )
        text = (
            f"<b>📐 Боковой профиль • {cfg['label_short']} шкала</b>\n\n"
            "<blockquote>Отправь чёткое фото строго <b>сбоку (90°)</b> при хорошем свете, "
            "чтобы была видна линия челюсти, подбородок и профиль носа.</blockquote>"
        )
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "cancel_profile":
        clear_awaiting_profile(user_id)
        safe_answer(call.id, "Режим профиля отменён")
        text, markup = build_main_menu_view(user_id)
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "battle_start":
        clear_pending_modes(user_id)
        safe_answer(call.id)
        text, markup = _build_battle_gender_prompt()
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "battle_start_new":
        clear_pending_modes(user_id)
        safe_answer(call.id)
        text, markup = _build_battle_gender_prompt()
        bot.send_message(chat_id, text, parse_mode="HTML", reply_markup=markup)

    elif data in ("battle_gender_m", "battle_gender_f"):
        clear_pending_modes(user_id)
        ok_bal, pro_tier, daily_limit = _has_enough_scans_for_battle(user_id)
        if not ok_bal:
            safe_answer(call.id, f"Нужно {BATTLE_SCAN_COST} скана", show_alert=True)
            if pro_tier > 0:
                _send_pro_daily_limit_prompt(chat_id, daily_limit, needed=BATTLE_SCAN_COST)
            else:
                _send_no_scans_prompt(chat_id, user_id=user_id, needed=BATTLE_SCAN_COST)
            return

        g = "f" if data == "battle_gender_f" else "m"
        set_user_gender(user_id, g)
        set_awaiting_battle(user_id, gender=g, msg1=None)
        pair_label = "Женщины (Ж vs Ж)" if g == "f" else "Мужчины (М vs М)"
        safe_answer(call.id, "Отправь 2 фото")
        markup = InlineKeyboardMarkup(row_width=2)
        markup.add(
            InlineKeyboardButton("🔄 Сменить пол", callback_data="battle_start"),
            InlineKeyboardButton("❌ Отмена", callback_data="cancel_battle"),
        )
        text = (
            f"<b>⚔️ Баттл 1 на 1 • {pair_label}</b>\n\n"
            "<blockquote>Отправь <b>2 фото анфас</b> — по очереди (сначала Боец 1, затем Боец 2) "
            "или сразу одним альбомом из 2 фото.\n"
            f"Спишется <b>{BATTLE_SCAN_COST} скана</b>.</blockquote>"
        )
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "cancel_battle":
        clear_awaiting_battle(user_id)
        safe_answer(call.id, "Баттл отменён")
        text, markup = build_main_menu_view(user_id)
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data.startswith("plan_"):
        clear_pending_modes(user_id)
        plan_id = data[5:]
        plan = PLANS.get(plan_id)
        if not plan:
            safe_answer(call.id, "Тариф не найден.", show_alert=True)
            return
        ok, err_msg = check_plan_allowed(user_id, plan)
        if not ok:
            safe_answer(call.id, err_msg, show_alert=True)
            return

        pr = get_plan_pricing(plan_id, user_id=user_id)
        safe_answer(call.id)
        markup = InlineKeyboardMarkup(row_width=1)
        markup.add(InlineKeyboardButton(f"⭐ Оплатить {pr['stars']} Stars (мгновенно)", callback_data=f"stars_{plan_id}"))
        if crypto_client.is_enabled():
            markup.add(InlineKeyboardButton(f"💎 Оплатить через @CryptoBot — {pr['rub']} ₽", callback_data=f"crypto_{plan_id}"))
        markup.add(InlineKeyboardButton("⬅️ К тарифам", callback_data="buy_menu"))

        if pr["promo_code"]:
            if crypto_client.is_enabled():
                promo_info = (
                    f"\n🎁 Промокод <code>{html.escape(pr['promo_code'])}</code>: скидка <b>-{pr['discount_pct']}%</b> "
                    f"(<s>{pr['orig_stars']} ⭐</s> → <b>{pr['stars']} ⭐</b> | <s>{pr['orig_rub']} ₽</s> → <b>{pr['rub']} ₽</b>)"
                )
            else:
                promo_info = (
                    f"\n🎁 Промокод <code>{html.escape(pr['promo_code'])}</code>: скидка <b>-{pr['discount_pct']}%</b> "
                    f"(<s>{pr['orig_stars']} ⭐</s> → <b>{pr['stars']} ⭐</b>)"
                )
        else:
            promo_info = ""

        text = (
            f"<b>{html.escape(plan['title'])}</b>\n\n"
            f"<blockquote>{html.escape(plan['desc'])}{promo_info}</blockquote>\n\n"
            "Выбери удобный способ оплаты:"
        )
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data.startswith("stars_"):
        clear_pending_modes(user_id)
        plan_id = data[6:]
        plan = PLANS.get(plan_id)
        if not plan:
            safe_answer(call.id, "Тариф не найден.", show_alert=True)
            return
        ok, err_msg = check_plan_allowed(user_id, plan)
        if not ok:
            safe_answer(call.id, err_msg, show_alert=True)
            return

        pr = get_plan_pricing(plan_id, user_id=user_id)
        inv_payload = (
            f"plan:{plan_id}:{user_id}:{pr['promo_code']}"
            if pr["promo_code"]
            else f"plan:{plan_id}:{user_id}"
        )
        desc = (
            f"{plan['desc']} (промокод {pr['promo_code']} -{pr['discount_pct']}%)"
            if pr["promo_code"]
            else plan["desc"]
        )
        safe_answer(call.id, "Открываю счёт...")
        try:
            bot.send_invoice(
                chat_id=chat_id,
                title=plan["title"],
                description=desc,
                invoice_payload=inv_payload,
                provider_token="",
                currency="XTR",
                prices=[LabeledPrice(label=plan["title"], amount=pr["stars"])],
            )
        except Exception as e:
            log_error(f"Ошибка выставления счёта Stars: {e}")
            bot.send_message(chat_id, "⚠️ Не удалось создать счёт Stars. Попробуй позже или выбери @CryptoBot.")

    elif data.startswith("crypto_"):
        clear_pending_modes(user_id)
        plan_id = data[7:]
        plan = PLANS.get(plan_id)
        if not plan or not crypto_client.is_enabled():
            safe_answer(call.id, "Оплата через @CryptoBot временно недоступна.", show_alert=True)
            return
        ok, err_msg = check_plan_allowed(user_id, plan)
        if not ok:
            safe_answer(call.id, err_msg, show_alert=True)
            return

        active_list = get_active_crypto_invoices_for_user(user_id)
        pr_check = get_plan_pricing(plan_id, user_id=user_id, ignore_active_crypto=True)
        for ex_id, ex_plan, ex_promo, ex_rub, ex_url, ex_exp in active_list:
            if ex_plan == plan_id and ex_rub == pr_check["rub"] and ex_url:
                safe_answer(call.id, "Открываю активный счёт")
                pct = get_promo_discount_value_raw(ex_promo) if ex_promo else 0
                text, markup = build_crypto_invoice_view(
                    plan_id, ex_id, ex_rub, ex_url, ex_exp, promo_code=ex_promo, discount_pct=pct
                )
                edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)
                return

        pr = get_plan_pricing(plan_id, user_id=user_id)
        safe_answer(call.id, "Создаю крипто-счёт...")
        uname = get_bot_username()
        paid_url = f"https://t.me/{uname}" if uname else None
        inv_payload = f"crypto:{plan_id}:{user_id}:{pr['promo_code']}" if pr["promo_code"] else f"crypto:{plan_id}:{user_id}"

        res, err = crypto_client.create_fiat_invoice(
            rub_amount=pr["rub"],
            description=f"Adonis PSL — {plan['title']}",
            payload=inv_payload,
            expires_in=CRYPTO_INVOICE_TTL,
            paid_btn_name="openBot" if paid_url else None,
            paid_btn_url=paid_url,
        )
        if err or not res or not res.get("pay_url"):
            log_error(f"Ошибка создания счёта CryptoBot: {err}")
            bot.send_message(chat_id, "⚠️ Не удалось создать счёт @CryptoBot. Попробуй позже или оплати через Telegram Stars.")
            return

        expires_at = int(time.time()) + CRYPTO_INVOICE_TTL
        save_crypto_invoice(
            res["invoice_id"],
            user_id,
            plan_id,
            pr["promo_code"],
            pr["rub"],
            res["pay_url"],
            expires_at,
        )
        text, markup = build_crypto_invoice_view(
            plan_id,
            res["invoice_id"],
            pr["rub"],
            res["pay_url"],
            expires_at,
            promo_code=pr["promo_code"],
            discount_pct=pr["discount_pct"],
        )
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data.startswith("cryptochk_"):
        try:
            inv_id = int(data[10:])
        except ValueError:
            safe_answer(call.id, "Некорректный счёт.", show_alert=True)
            return

        row = get_crypto_invoice_by_id(inv_id)
        if not row or row[1] != user_id:
            safe_answer(call.id, "Счёт не найден.", show_alert=True)
            return
        _, _, plan_id, _, _, status, _, _ = row
        if status == "paid":
            safe_answer(call.id, "Этот счёт уже оплачен!", show_alert=True)
            text, markup = build_main_menu_view(user_id)
            edit_or_send(chat_id, f"✅ <b>Оплата уже зачислена!</b>\n\n{text}", reply_markup=markup, message_id=edit_id)
            return
        if status != "active":
            safe_answer(call.id, "Счёт больше не активен.", show_alert=True)
            text, markup = build_buy_menu_view(user_id)
            edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)
            return

        items, err = crypto_client.get_invoices(inv_id)
        if err or items is None:
            safe_answer(call.id, "Не удалось связаться с @CryptoBot. Попробуй через пару секунд.", show_alert=True)
            return

        item = items[0] if items else None
        api_status = (item.get("status") or "").lower() if item else "expired"
        if api_status == "paid":
            ok_fulfill, plan_title = fulfill_crypto_payment(inv_id, item, notify_user=False)
            safe_answer(call.id, "Оплата подтверждена!", show_alert=True)
            title_txt = plan_title or PLANS.get(plan_id, {}).get("title", "Тариф")
            text, markup = build_main_menu_view(user_id)
            edit_or_send(
                chat_id,
                f"✅ <b>Оплата через @CryptoBot прошла успешно!</b>\nАктивировано: <b>{html.escape(title_txt)}</b>.\n\n{text}",
                reply_markup=markup,
                message_id=edit_id,
            )
            return

        if api_status == "expired":
            mark_crypto_invoice_status(inv_id, "expired")
            safe_answer(call.id, "Срок действия счёта истёк.", show_alert=True)
            text, markup = build_buy_menu_view(user_id)
            edit_or_send(
                chat_id,
                f"⏳ Счёт <code>#{inv_id}</code> истёк. Создай новый счёт в меню тарифов:\n\n{text}",
                reply_markup=markup,
                message_id=edit_id,
            )
            return

        safe_answer(call.id, "Оплата пока не поступила. Если ты только что оплатил — нажми ещё раз через 5 сек.", show_alert=True)

    elif data.startswith("cryptocancel_"):
        try:
            inv_id = int(data[13:])
        except ValueError:
            safe_answer(call.id, "Некорректный счёт.", show_alert=True)
            return

        row = get_crypto_invoice_by_id(inv_id)
        if not row or row[1] != user_id:
            safe_answer(call.id, "Счёт не найден.", show_alert=True)
            return
        if row[5] != "active":
            safe_answer(call.id, "Счёт уже закрыт.")
            text, markup = build_buy_menu_view(user_id)
            edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)
            return

        items, _ = crypto_client.get_invoices(inv_id)
        if items and (items[0].get("status") or "").lower() == "paid":
            _, plan_title = fulfill_crypto_payment(inv_id, items[0], notify_user=False)
            safe_answer(call.id, "Счёт уже оплачен — доступ выдан!", show_alert=True)
            text, markup = build_main_menu_view(user_id)
            edit_or_send(
                chat_id,
                f"✅ <b>Оплата уже поступила!</b> Активировано: <b>{html.escape(plan_title)}</b>.\n\n{text}",
                reply_markup=markup,
                message_id=edit_id,
            )
            return

        crypto_client.delete_invoice(inv_id)
        mark_crypto_invoice_status(inv_id, "cancelled")
        safe_answer(call.id, "Счёт отменён")
        text, markup = build_buy_menu_view(user_id)
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data.startswith("setmodel_"):
        if not is_admin(user_id):
            safe_answer(call.id, "Нет прав.", show_alert=True)
            return
        clear_awaiting_model(user_id)
        chosen = data[9:].strip()
        parsed = parse_models_input(chosen)
        if not parsed:
            safe_answer(call.id, "Некорректная модель.", show_alert=True)
            return
        set_active_models(parsed)
        safe_answer(call.id, f"Установлена {parsed[0]}")
        text, markup = build_model_manager_view()
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "model_custom":
        if not is_admin(user_id):
            safe_answer(call.id, "Нет прав.", show_alert=True)
            return
        clear_pending_modes(user_id)
        set_awaiting_model(user_id)
        safe_answer(call.id, "Отправь название модели")
        markup = InlineKeyboardMarkup()
        markup.add(InlineKeyboardButton("❌ Отмена", callback_data="model_cancel"))
        edit_or_send(
            chat_id,
            "✏️ <b>Ввод своей модели Gemini</b>\n\n"
            "Отправь следующим сообщением точное название модели (например: "
            "<code>gemini-3.5-flash-lite</code>) или несколько через запятую.",
            reply_markup=markup,
            message_id=edit_id,
        )

    elif data == "model_cancel":
        if not is_admin(user_id):
            safe_answer(call.id)
            return
        clear_awaiting_model(user_id)
        safe_answer(call.id, "Отменено")
        text, markup = build_model_manager_view()
        edit_or_send(chat_id, text, reply_markup=markup, message_id=edit_id)

    elif data == "model_reset_cd":
        if not is_admin(user_id):
            safe_answer(call.id, "Нет прав.", show_alert=True)
            return
        reset_model_cooldowns()
        safe_answer(call.id, "Паузы 404/429 сброшены!", show_alert=True)

    elif data == "bc_cancel":
        if not is_admin(user_id):
            safe_answer(call.id)
            return
        clear_broadcast_state(user_id)
        safe_answer(call.id, "Рассылка отменена")
        try:
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=None)
        except Exception:
            pass
        bot.send_message(chat_id, "❌ Рассылка отменена.")

    elif data == "bc_send":
        if not is_admin(user_id):
            safe_answer(call.id)
            return
        with _broadcast_lock:
            payload = _broadcast_state.pop(user_id, None)
        if not payload or payload.get("step") != "ready":
            safe_answer(call.id, "Нет активного черновика.", show_alert=True)
            return
        safe_answer(call.id, "Запускаю рассылку...")
        try:
            bot.edit_message_reply_markup(chat_id, msg_id, reply_markup=None)
        except Exception:
            pass
        bot.send_message(chat_id, "🚀 Рассылка запущена в фоне...")
        threading.Thread(target=_run_broadcast_worker, args=(chat_id, payload), daemon=True).start()

    elif data.startswith("full_"):
        photo_hash = data[5:]
        if not is_valid_photo_hash(photo_hash):
            safe_answer(call.id, "Некорректный идентификатор отчёта.", show_alert=True)
            return
        cached = cache_get(photo_hash)
        if cached and cached[1]:
            safe_answer(call.id, "Загружаю разбор...")
            title = "📐 Разбор бокового профиля" if is_profile_hash(photo_hash) else "💬 Подробный разбор"
            send_long_html(chat_id, title, cached[1])
        else:
            safe_answer(call.id, "Разбор устарел, отправь фото заново.", show_alert=True)

    elif data.startswith("share_"):
        photo_hash = data[6:]
        if not is_valid_photo_hash(photo_hash) or is_profile_hash(photo_hash):
            safe_answer(call.id, "Карточка для друга доступна только для скана анфас.", show_alert=True)
            return

        cached = cache_get(photo_hash)
        if not cached:
            safe_answer(call.id, "Отчёт устарел, отправь фото заново.", show_alert=True)
            return

        scores_text, _, _, _, _, share_file_id, metrics_json, source_file_id = cached
        if share_file_id:
            safe_answer(call.id, "Отправляю карточку...")
            uname = get_bot_username()
            wm_cap = f"📤 <b>Карточка для друга</b>\nСохрани или перешли другу • @{uname}" if uname else "📤 <b>Карточка для друга</b>"
            try:
                bot.send_photo(chat_id, share_file_id, caption=wm_cap, parse_mode="HTML")
                return
            except Exception as e:
                log_error(f"Не удалось отправить share_file_id, пересобираю: {e}")

        busy_key = (user_id, photo_hash)
        with _share_busy_lock:
            if busy_key in _share_busy:
                safe_answer(call.id, "Карточка уже собирается...")
                return
            _share_busy.add(busy_key)

        safe_answer(call.id, "Генерирую карточку для друга...")
        status_msg = bot.send_message(chat_id, "📤 Собираю стильную карточку для пересыла...")
        threading.Thread(
            target=_run_share_card_worker,
            args=(chat_id, user_id, photo_hash, scores_text, metrics_json, source_file_id, status_msg),
            daemon=True,
        ).start()

    elif data.startswith("growth_"):
        photo_hash = data[7:]
        if not is_valid_photo_hash(photo_hash) or is_profile_hash(photo_hash):
            safe_answer(call.id, "Некорректный идентификатор отчёта.", show_alert=True)
            return

        _, pro_tier, _, _ = get_user_access(user_id)
        if pro_tier <= 0 and not is_admin(user_id):
            safe_answer(call.id, "Доступно в PRO")
            markup = InlineKeyboardMarkup(row_width=1)
            markup.add(InlineKeyboardButton("👑 Подключить PRO", callback_data="buy_menu"))
            markup.add(InlineKeyboardButton("🤝 Получить PRO за друзей", callback_data="get_ref"))
            bot.send_message(
                chat_id,
                "<b>📈 Персональный план роста (PRO)</b>\n\n"
                "<blockquote>По результатам твоего скана бот составит пошаговый план:\n"
                "• Топ-3 зоны роста с максимальным эффектом\n"
                "• Подбор стрижки/причёски строго под твою форму лица\n"
                "• Чек-лист по коже, бровям, отёчности и уходу на 30 дней</blockquote>\n\n"
                "Открывается на тарифах <b>PRO</b> или бесплатно за 3 приглашённых друзей.",
                parse_mode="HTML",
                reply_markup=markup,
            )
            return

        cached = cache_get(photo_hash)
        if not cached:
            safe_answer(call.id, "Отчёт устарел, отправь фото заново.", show_alert=True)
            return

        scores_text, full_text, _, _, growth_plan, _, _, _ = cached
        if growth_plan:
            safe_answer(call.id, "Загружаю план роста...")
            send_long_html(chat_id, "📈 Персональный план роста (PRO)", growth_plan)
            return

        busy_key = (user_id, photo_hash)
        with _growth_busy_lock:
            if busy_key in _growth_busy:
                safe_answer(call.id, "План уже составляется, подожди пару секунд...")
                return
            _growth_busy.add(busy_key)

        safe_answer(call.id, "Составляю персональный план...")
        status_msg = bot.send_message(chat_id, "📈 Составляю персональный план роста по твоим метрикам...")
        threading.Thread(
            target=_run_growth_plan_worker,
            args=(chat_id, user_id, photo_hash, scores_text, full_text, status_msg),
            daemon=True,
        ).start()

    else:
        safe_answer(call.id)


@bot.message_handler(content_types=["text"])
def handle_fallback_text(message):
    user_id = message.from_user.id
    touch_user(message.from_user)
    if is_user_banned(user_id):
        return

    if is_awaiting_promo(user_id):
        clear_awaiting_promo(user_id)
        ok, ptype, msg_text = activate_promocode_for_user(user_id, message.text)
        markup = InlineKeyboardMarkup(row_width=1)
        if ok and ptype == "discount":
            markup.add(InlineKeyboardButton("💎 Перейти к тарифам со скидкой", callback_data="buy_menu"))
        elif not ok:
            markup.add(InlineKeyboardButton("🔁 Попробовать другой код", callback_data="enter_promo"))
        markup.add(InlineKeyboardButton("🏠 Главное меню", callback_data="main_menu"))
        bot.reply_to(message, msg_text, parse_mode="HTML", reply_markup=markup)
        return

    if is_awaiting_battle(user_id):
        state, _ = get_awaiting_battle(user_id)
        markup = InlineKeyboardMarkup()
        markup.add(InlineKeyboardButton("❌ Отмена", callback_data="cancel_battle"))
        if state and state.get("msg1") is not None:
            hint = "⚔️ Жду <b>фото Бойца 2</b> для баттла. Пришли фото анфас или нажми «Отмена»."
        else:
            hint = "⚔️ Сейчас активен режим <b>Баттл 1 на 1</b>. Пришли 2 фото анфас (по очереди или альбомом) или нажми «Отмена»."
        bot.reply_to(message, hint, parse_mode="HTML", reply_markup=markup)
    elif is_awaiting_profile(user_id):
        markup = InlineKeyboardMarkup()
        markup.add(InlineKeyboardButton("❌ Отмена", callback_data="cancel_profile"))
        bot.reply_to(
            message,
            "📐 Сейчас активен режим <b>бокового профиля</b>. Пришли фото сбоку (90°) или нажми «Отмена».",
            parse_mode="HTML",
            reply_markup=markup,
        )


if __name__ == "__main__":
    init_db()
    ensure_user_columns()
    load_active_models_from_db()
    setup_bot_commands()
    start_scan_workers()
    crypto_poller.start()
    is_mediapipe_available()
    uname = get_bot_username()
    cb_info = "CryptoBot ON" if crypto_client.is_enabled() else "CryptoBot OFF"
    print(f"🚀 Adonis PSL Bot (@{uname or 'unknown'}) запущен! [{cb_info}]")

    while True:
        try:
            bot.infinity_polling(
                timeout=30,
                long_polling_timeout=25,
                skip_pending=True,
            )
        except KeyboardInterrupt:
            crypto_poller.stop()
            print("🛑 Бот остановлен вручную.")
            break
        except Exception as e:
            log_error(f"Сбой polling, перезапуск через 5 сек: {e}")
            time.sleep(5)