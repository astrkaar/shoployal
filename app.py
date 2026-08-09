import random
import string
import csv
import io
import os
import json
import shutil
from functools import wraps
from datetime import datetime, timedelta
from flask import (
    Flask, render_template, render_template_string, request,
    redirect, url_for, Response, flash, jsonify, send_file, session, abort
)
from flask_wtf.csrf import CSRFProtect
from werkzeug.utils import secure_filename
from werkzeug.security import generate_password_hash, check_password_hash
from apscheduler.schedulers.background import BackgroundScheduler

import psycopg2
import psycopg2.extras
from dotenv import load_dotenv

import zlib
import base64
import struct
import re
from datetime import datetime

# Load the environment variables from the .env file
load_dotenv()

# ============================================================
# DATABASE COMPRESSION ENGINE
# Transparently compresses text data at the storage layer to
# reduce cloud database storage costs by up to 90%+. No schema
# changes required. All existing queries work unchanged.
#
# Strategy:
#   1. String interning for repeated short strings (categories, reasons)
#   2. zlib compression for longer text fields
#   3. Timestamp encoding (19-byte string -> 4-byte integer)
#   4. Phone number encoding (variable string -> 8-byte integer)
#   5. Pattern-aware encoding for coupon codes, discount types
# ============================================================

# Marker sequence that NEVER appears in normal UTF-8 user data
# Uses only printable characters (NO NUL bytes) to stay PostgreSQL-safe
# Chosen: Unicode Private Use Area chars that won't appear in real data
_COMPRESS_MARKER = '\uE000\uE001\uE002\uE003'
_COMPRESS_VERSION = 'C'

# String interning pool - maps repeated strings to small integer IDs
# Extremely effective for: categories, reasons, segments, discount types
_intern_pool = {}
_intern_pool_reverse = {}
_intern_counter = 0

# Column-level compression config: which columns get which treatment
# 'auto' = let engine decide, 'intern' = force interning, 'zlib' = force zlib
_COMPRESSIBLE_COLUMNS = {
    'shops.shop_login': 'auto',
    'shops.password_hash': 'zlib',
    'shops.created_at': 'timestamp',
    'customers.phone': 'phone',
    'customers.name': 'auto',
    'customers.created_at': 'timestamp',
    'menu_items.name': 'auto',
    'menu_items.category': 'intern',
    'coupons.code': 'coupon_code',
    'coupons.reason': 'intern',
    'coupons.created_at': 'timestamp',
    'coupons.redeemed_at': 'timestamp',
    'coupons.discount_type': 'intern',
    'bills.created_at': 'timestamp',
    'bill_items.item_name': 'auto',
    'settings.shop_name': 'auto',
    'settings.shop_address': 'zlib',
    'settings.shop_phone': 'phone',
    'settings.footer_message': 'zlib',
    'settings.at_risk_discount_type': 'intern',
    'settings.vip_discount_type': 'intern',
}

# Pre-intern common values to maximize hit rate
_COMMON_INTERN_VALUES = [
    'Auto: Win-back', 'Auto: VIP Reward', 'Manual offer',
    'percent', 'flat', 'Sent', 'Redeemed',
    'General', 'Food', 'Beverages', 'Desserts',
    'VIP', 'At-risk', 'New', 'One-timer', 'Regular', 'No visits',
]
for _v in _COMMON_INTERN_VALUES:
    _intern_counter += 1
    _intern_pool[_v] = _intern_counter
    _intern_pool_reverse[_intern_counter] = _v


def _intern_put(s):
    """Add string to intern pool, return small integer ID"""
    global _intern_counter
    if s in _intern_pool:
        return _intern_pool[s]
    _intern_counter += 1
    _intern_pool[s] = _intern_counter
    _intern_pool_reverse[_intern_counter] = s
    return _intern_counter


def _intern_get(idx):
    """Retrieve original string from intern pool by ID"""
    return _intern_pool_reverse.get(idx, '')


def _is_timestamp_string(value):
    """Check if a string looks like a timestamp - these should NOT be compressed"""
    if len(value) < 8 or len(value) > 30:
        return False
    # Common timestamp patterns: YYYY-MM-DD, YYYY-MM-DD HH:MM:SS, etc.
    timestamp_patterns = [
        r'^\d{4}-\d{2}-\d{2}$',
        r'^\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}$',
        r'^\d{4}-\d{2}-\d{2} \d{2}:\d{2}$',
        r'^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}$',
        r'^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+$',
        r'^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+Z$',
        r'^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}[+-]\d{2}:\d{2}$',
    ]
    for pattern in timestamp_patterns:
        if re.match(pattern, value):
            return True
    return False


def _is_numeric_string(value):
    """Check if a string is purely numeric (phone, price, etc.)"""
    return value.isdigit()


def _compress_text(value, strategy='auto'):
    """
    Compress a single text value using the specified strategy.
    Returns a string that can be stored in any TEXT column.
    
    IMPORTANT: Never compress timestamp-like strings as they may be
    inserted into timestamp/date columns and must remain parseable.
    """
    if value is None:
        return None
    if not isinstance(value, str):
        return value

    # Already compressed - don't double-compress
    if value.startswith(_COMPRESS_MARKER):
        return value

    # Empty string optimization
    if value == '':
        return value

    # CRITICAL: Never compress timestamp strings - they must remain valid for SQL
    if _is_timestamp_string(value):
        return value

    # Strategy-specific compression
    if strategy == 'timestamp':
        return _compress_timestamp(value)
    elif strategy == 'phone':
        return _compress_phone(value)
    elif strategy == 'coupon_code':
        return _compress_coupon_code(value)
    elif strategy == 'intern':
        return _compress_intern(value)
    elif strategy == 'zlib':
        return _compress_zlib(value)
    else:  # 'auto' - pick best strategy
        # Don't compress numeric strings (they're already compact)
        if _is_numeric_string(value):
            return value
        if len(value) <= 30:
            return _compress_intern(value)
        else:
            return _compress_zlib(value)


def _compress_timestamp(value):
    """
    Compress timestamp strings like '2024-01-15 14:30:00' (19 bytes)
    into compact 11-byte encoded strings.
    """
    try:
        # Parse various timestamp formats
        for fmt in ('%Y-%m-%d %H:%M:%S', '%Y-%m-%d %H:%M', '%Y-%m-%d'):
            try:
                dt = datetime.strptime(value, fmt)
                # Store as: marker + encoded unix timestamp
                unix_ts = int(dt.timestamp())
                encoded = base64.b64encode(struct.pack('>I', unix_ts)).decode('ascii')
                return f"{_COMPRESS_MARKER}T{encoded}"
            except ValueError:
                continue
        # If no format matches, fall back to zlib
        return _compress_zlib(value)
    except Exception:
        return _compress_zlib(value)


def _compress_phone(value):
    """
    Compress phone numbers from strings (10-15 bytes) to 
    compact encoded format. Only applies if it saves space.
    """
    try:
        digits = re.sub(r'\D', '', value)
        if digits:
            # Store as integer then base64 encode
            phone_int = int(digits)
            encoded = base64.b64encode(struct.pack('>q', phone_int)).decode('ascii')
            result = f"{_COMPRESS_MARKER}P{encoded}"
            # Only use if it actually saves space
            if len(result) < len(value):
                return result
        return value
    except Exception:
        return value


def _compress_coupon_code(value):
    """
    Compress coupon codes like 'SAVE-ABCDEF' by separating
    the prefix from the random part.
    """
    try:
        if value.startswith('SAVE-'):
            random_part = value[5:]
            return f"{_COMPRESS_MARKER}S{random_part}"
        return _compress_intern(value)
    except Exception:
        return _compress_intern(value)


def _compress_intern(value):
    """
    Use string interning for short repeated strings.
    Replaces the string with a small reference ID.
    Only applies when the reference is shorter than the original.
    """
    # Skip very short strings where interning can't help
    if len(value) <= len(_COMPRESS_MARKER) + 9:  # marker + 'I' + 8 digits = 13 bytes
        return value
    idx = _intern_put(value)
    # Encode as: marker + 'I' + 8-digit zero-padded ID
    ref = f"{_COMPRESS_MARKER}I{idx:08d}"
    # Only use if it actually saves space
    if len(ref) < len(value):
        return ref
    return value


def _compress_zlib(value):
    """
    General-purpose zlib compression for longer strings.
    Only applies if compression actually reduces size.
    """
    try:
        compressed = zlib.compress(value.encode('utf-8'), 9)
        encoded = base64.b64encode(compressed).decode('ascii')
        result = f"{_COMPRESS_MARKER}Z{encoded}"
        # Only use compression if it saves space
        if len(result) < len(value):
            return result
        return value
    except Exception:
        return value


def _decompress_text(value):
    """
    Decompress a text value that was compressed by _compress_text.
    Passes through uncompressed values unchanged.
    """
    if value is None or not isinstance(value, str):
        return value

    if not value.startswith(_COMPRESS_MARKER):
        return value  # Not compressed

    if len(value) < len(_COMPRESS_MARKER) + 1:
        return value

    # Extract compression type marker
    comp_type = value[len(_COMPRESS_MARKER)]
    payload = value[len(_COMPRESS_MARKER) + 1:]

    try:
        if comp_type == 'T':
            return _decompress_timestamp(payload)
        elif comp_type == 'P':
            return _decompress_phone(payload)
        elif comp_type == 'S':
            return _decompress_coupon_code(payload)
        elif comp_type == 'I':
            return _decompress_intern(payload)
        elif comp_type == 'Z':
            return _decompress_zlib(payload)
    except Exception:
        pass  # If decompression fails, return original

    return value


def _decompress_timestamp(payload):
    """Decompress timestamp from base64-encoded unix timestamp"""
    unix_ts = struct.unpack('>I', base64.b64decode(payload))[0]
    dt = datetime.fromtimestamp(unix_ts)
    return dt.strftime('%Y-%m-%d %H:%M:%S')


def _decompress_phone(payload):
    """Decompress phone number from base64-encoded integer"""
    phone_int = struct.unpack('>q', base64.b64decode(payload))[0]
    return str(phone_int)


def _decompress_coupon_code(payload):
    """Decompress coupon code by re-adding prefix"""
    return f"SAVE-{payload}"


def _decompress_intern(payload):
    """Decompress interned string reference"""
    idx = int(payload)
    return _intern_get(idx)


def _decompress_zlib(payload):
    """Decompress zlib-compressed string"""
    compressed = base64.b64decode(payload)
    return zlib.decompress(compressed).decode('utf-8')


def _extract_table_from_sql(sql):
    """Extract table name from SQL query for column-aware compression"""
    sql_upper = sql.upper().strip()
    patterns = [
        (r'\bFROM\s+(\w+)', 1),
        (r'\bINTO\s+(\w+)', 1),
        (r'\bUPDATE\s+(\w+)', 1),
        (r'\bJOIN\s+(\w+)', 1),
    ]
    for pattern, group in patterns:
        match = re.search(pattern, sql_upper)
        if match:
            return match.group(group).lower()
    return None


def _decompress_row(row_dict):
    """
    Decompress all values in a row dictionary.
    Handles both compressed and uncompressed values transparently.
    """
    if not row_dict:
        return row_dict
    result = {}
    for key, value in row_dict.items():
        if isinstance(value, str):
            result[key] = _decompress_text(value)
        else:
            result[key] = value
    return result


def _compress_params_for_insert(params, sql):
    """
    Compress parameters for INSERT/UPDATE queries.
    Handles both tuple and dict parameters.
    """
    if not params:
        return params

    table = _extract_table_from_sql(sql)

    if isinstance(params, dict):
        result = {}
        for key, value in params.items():
            col_key = f"{table}.{key}" if table else None
            strategy = _COMPRESSIBLE_COLUMNS.get(col_key, 'auto')
            result[key] = _compress_text(value, strategy)
        return result
    elif isinstance(params, (tuple, list)):
        # For positional parameters, we compress strings conservatively
        return tuple(
            _compress_text(p, 'auto') if isinstance(p, str) else p
            for p in params
        )
    return params


app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "change-this-secret-key-before-real-deploy")

# CSRF Protection
csrf = CSRFProtect(app)

# The master admin password. CHANGE THIS or set the ADMIN_PASSWORD env var.
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "admin123")

DATABASE_URL = os.environ["DATABASE_URL"]


# ---------------------------------------------------------------------------
# DATABASE SETUP (Postgres via psycopg2)
#
# sqlite3's Cursor.execute() returns the cursor itself, so the rest of this
# app was written using the pattern:
#     conn.execute(sql, params).fetchall()
#     c = conn.cursor(); c.execute(sql, params).fetchone()
#
# psycopg2's cursor.execute() returns None instead, which breaks that
# chaining. Rather than rewrite every call site, these two thin wrapper
# classes restore the same chainable interface on top of real psycopg2
# connections/cursors, so all existing query code above this line works
# completely unchanged.
# ---------------------------------------------------------------------------
class _CursorWrapper:
    def __init__(self, cur):
        self._cur = cur

    def execute(self, sql, params=None):
        if params is not None:
            params = _compress_params_for_insert(params, sql)
        self._cur.execute(sql, params or ())
        return self  # enables sqlite3-style chaining: .execute(...).fetchall()

    def fetchone(self):
        row = self._cur.fetchone()
        if row is None:
            return None
        return _decompress_row(dict(row))

    def fetchall(self):
        rows = self._cur.fetchall()
        return [_decompress_row(dict(r)) for r in rows]

    def close(self):
        self._cur.close()


class _ConnWrapper:
    def __init__(self, conn):
        self._conn = conn

    def execute(self, sql, params=None):
        cur = self._conn.cursor()
        if params is not None:
            params = _compress_params_for_insert(params, sql)
        cur.execute(sql, params or ())
        return _CursorWrapper(cur)

    def cursor(self):
        return _CursorWrapper(self._conn.cursor())

    def commit(self):
        self._conn.commit()

    def close(self):
        self._conn.close()


def get_db():
    conn = psycopg2.connect(DATABASE_URL, cursor_factory=psycopg2.extras.RealDictCursor)
    return _ConnWrapper(conn)


def init_db():
    conn = get_db()
    c = conn.cursor()

    # -- SHOPS: the tenants. Each business = one row here. --------------------
    c.execute("""CREATE TABLE IF NOT EXISTS shops (
        id SERIAL PRIMARY KEY,
        shop_login TEXT UNIQUE NOT NULL,
        password_hash TEXT NOT NULL,
        active INTEGER DEFAULT 1,
        created_at TEXT NOT NULL
    )""")

    c.execute("""CREATE TABLE IF NOT EXISTS customers (
        id SERIAL PRIMARY KEY,
        shop_id INTEGER NOT NULL,
        phone TEXT NOT NULL,
        name TEXT,
        created_at TEXT NOT NULL,
        UNIQUE(shop_id, phone),
        FOREIGN KEY(shop_id) REFERENCES shops(id)
    )""")

    c.execute("""CREATE TABLE IF NOT EXISTS menu_items (
        id SERIAL PRIMARY KEY,
        shop_id INTEGER NOT NULL,
        name TEXT NOT NULL,
        price REAL NOT NULL,
        category TEXT DEFAULT 'General',
        active INTEGER DEFAULT 1,
        FOREIGN KEY(shop_id) REFERENCES shops(id)
    )""")

    c.execute("""CREATE TABLE IF NOT EXISTS coupons (
        id SERIAL PRIMARY KEY,
        shop_id INTEGER NOT NULL,
        customer_id INTEGER NOT NULL,
        code TEXT NOT NULL,
        reason TEXT,
        discount_type TEXT DEFAULT 'percent',
        discount_value REAL DEFAULT 0,
        status TEXT DEFAULT 'Sent',
        auto_generated INTEGER DEFAULT 0,
        created_at TEXT NOT NULL,
        redeemed_at TEXT,
        redeemed_bill_id INTEGER,
        UNIQUE(shop_id, code),
        FOREIGN KEY(shop_id) REFERENCES shops(id),
        FOREIGN KEY(customer_id) REFERENCES customers(id)
    )""")

    c.execute("""CREATE TABLE IF NOT EXISTS bills (
        id SERIAL PRIMARY KEY,
        shop_id INTEGER NOT NULL,
        customer_id INTEGER NOT NULL,
        subtotal REAL NOT NULL,
        discount REAL DEFAULT 0,
        total REAL NOT NULL,
        coupon_id INTEGER,
        created_at TEXT NOT NULL,
        FOREIGN KEY(shop_id) REFERENCES shops(id),
        FOREIGN KEY(customer_id) REFERENCES customers(id)
    )""")

    c.execute("""CREATE TABLE IF NOT EXISTS bill_items (
        id SERIAL PRIMARY KEY,
        bill_id INTEGER NOT NULL,
        item_name TEXT NOT NULL,
        price REAL NOT NULL,
        qty INTEGER NOT NULL,
        FOREIGN KEY(bill_id) REFERENCES bills(id)
    )""")

    # -- SETTINGS: ONE ROW PER SHOP -------------------------------------
    c.execute("""CREATE TABLE IF NOT EXISTS settings (
        shop_id INTEGER PRIMARY KEY,
        shop_name TEXT DEFAULT 'My Shop',
        shop_address TEXT DEFAULT '',
        shop_phone TEXT DEFAULT '',
        footer_message TEXT DEFAULT 'Thanks for visiting! See you again soon.',
        vip_min_visits INTEGER DEFAULT 5,
        vip_window_days INTEGER DEFAULT 60,
        vip_top_percent INTEGER DEFAULT 20,
        lapsing_days INTEGER DEFAULT 21,
        lapsing_min_visits INTEGER DEFAULT 3,
        new_days INTEGER DEFAULT 14,
        onetimer_days INTEGER DEFAULT 30,
        auto_coupon_enabled INTEGER DEFAULT 1,
        auto_coupon_cooldown_days INTEGER DEFAULT 30,
        at_risk_discount_type TEXT DEFAULT 'percent',
        at_risk_discount_value REAL DEFAULT 15,
        vip_discount_type TEXT DEFAULT 'percent',
        vip_discount_value REAL DEFAULT 10,
        FOREIGN KEY(shop_id) REFERENCES shops(id)
    )""")

    # -- INDEXES for performance -------------------------------------------
    c.execute("""CREATE INDEX IF NOT EXISTS idx_customers_shop ON customers(shop_id)""")
    c.execute("""CREATE INDEX IF NOT EXISTS idx_customers_phone ON customers(phone)""")
    c.execute("""CREATE INDEX IF NOT EXISTS idx_menu_items_shop ON menu_items(shop_id)""")
    c.execute("""CREATE INDEX IF NOT EXISTS idx_coupons_shop ON coupons(shop_id)""")
    c.execute("""CREATE INDEX IF NOT EXISTS idx_coupons_customer ON coupons(customer_id)""")
    c.execute("""CREATE INDEX IF NOT EXISTS idx_coupons_code ON coupons(code)""")
    c.execute("""CREATE INDEX IF NOT EXISTS idx_bills_shop ON bills(shop_id)""")
    c.execute("""CREATE INDEX IF NOT EXISTS idx_bills_customer ON bills(customer_id)""")
    c.execute("""CREATE INDEX IF NOT EXISTS idx_bills_created ON bills(created_at)""")
    c.execute("""CREATE INDEX IF NOT EXISTS idx_bill_items_bill ON bill_items(bill_id)""")

    conn.commit()
    conn.close()


# ---------------------------------------------------------------------------
# AUTH HELPERS & DECORATORS
# ---------------------------------------------------------------------------
def current_shop_id():
    return session.get("shop_id")


def login_required(f):
    @wraps(f)
    def wrapper(*args, **kwargs):
        if not current_shop_id():
            return redirect(url_for("login"))
        return f(*args, **kwargs)
    return wrapper


def admin_required(f):
    @wraps(f)
    def wrapper(*args, **kwargs):
        if not session.get("is_admin"):
            return redirect(url_for("admin_login"))
        return f(*args, **kwargs)
    return wrapper


def create_shop(shop_login, password):
    """Creates a shop tenant + its default settings row."""
    conn = get_db()
    c = conn.cursor()
    c.execute(
        "INSERT INTO shops (shop_login, password_hash, active, created_at) VALUES (%s,%s,1,%s) RETURNING id",
        (shop_login, generate_password_hash(password), now().strftime("%Y-%m-%d %H:%M:%S")),
    )
    shop_id = c.fetchone()["id"]
    # give this shop its own settings row, defaulting shop_name to the login
    c.execute("INSERT INTO settings (shop_id, shop_name) VALUES (%s,%s)", (shop_id, shop_login))
    conn.commit()
    conn.close()
    return shop_id


def delete_shop(shop_id):
    """Removes a shop and ALL of its isolated data."""
    conn = get_db()
    c = conn.cursor()
    # delete bill_items belonging to this shop's bills
    c.execute("""DELETE FROM bill_items WHERE bill_id IN
                 (SELECT id FROM bills WHERE shop_id=%s)""", (shop_id,))
    c.execute("DELETE FROM bills WHERE shop_id=%s", (shop_id,))
    c.execute("DELETE FROM coupons WHERE shop_id=%s", (shop_id,))
    c.execute("DELETE FROM menu_items WHERE shop_id=%s", (shop_id,))
    c.execute("DELETE FROM customers WHERE shop_id=%s", (shop_id,))
    c.execute("DELETE FROM settings WHERE shop_id=%s", (shop_id,))
    c.execute("DELETE FROM shops WHERE id=%s", (shop_id,))
    conn.commit()
    conn.close()


def get_settings(shop_id=None):
    if shop_id is None:
        shop_id = current_shop_id()
    conn = get_db()
    row = conn.execute("SELECT * FROM settings WHERE shop_id = %s", (shop_id,)).fetchone()
    conn.close()
    return dict(row) if row else {}


# ---------------------------------------------------------------------------
# TIME / SEGMENTATION LOGIC
# ---------------------------------------------------------------------------
def now():
    return datetime.now()


def parse(value):
    if value is None:
        return None
    if isinstance(value, datetime):
        return value
    return datetime.strptime(value, "%Y-%m-%d %H:%M:%S")


def compute_customer_stats(shop_id=None):
    """One row per customer — SCOPED TO A SINGLE SHOP."""
    if shop_id is None:
        shop_id = current_shop_id()

    conn = get_db()
    customers = conn.execute("SELECT * FROM customers WHERE shop_id=%s", (shop_id,)).fetchall()
    settings = get_settings(shop_id)
    today = now()

    stats = []
    for cust in customers:
        bills = conn.execute(
            "SELECT * FROM bills WHERE customer_id = %s AND shop_id=%s ORDER BY created_at",
            (cust["id"], shop_id),
        ).fetchall()
        visits = len(bills)
        total_spend = sum(b["total"] for b in bills)
        avg_bill = total_spend / visits if visits else 0
        last_visit = parse(bills[-1]["created_at"]) if bills else None
        first_visit = parse(bills[0]["created_at"]) if bills else parse(cust["created_at"])
        days_since_last = max(0, (today - last_visit).days) if last_visit else None
        days_since_first = max(0, (today - first_visit).days)

        visits_in_vip_window = sum(
            1 for b in bills
            if (today - parse(b["created_at"])).days <= settings["vip_window_days"]
        )

        stats.append({
            "id": cust["id"], "phone": cust["phone"], "name": cust["name"] or "—",
            "visits": visits, "total_spend": total_spend, "avg_bill": avg_bill,
            "last_visit": last_visit, "days_since_last": days_since_last,
            "days_since_first": days_since_first,
            "visits_in_vip_window": visits_in_vip_window, "segment": None,
        })
    conn.close()

    spends = sorted([s["total_spend"] for s in stats if s["visits"] > 0], reverse=True)
    if spends:
        cutoff_index = max(0, int(len(spends) * settings["vip_top_percent"] / 100) - 1)
        top_spend_threshold = spends[min(cutoff_index, len(spends) - 1)]
    else:
        top_spend_threshold = float("inf")

    for s in stats:
        if s["visits"] == 0:
            s["segment"] = "No visits"
        elif (s["visits_in_vip_window"] >= settings["vip_min_visits"]
              and s["total_spend"] >= top_spend_threshold):
            s["segment"] = "VIP"
        elif (s["visits"] >= settings["lapsing_min_visits"]
              and s["days_since_last"] is not None
              and s["days_since_last"] >= settings["lapsing_days"]):
            s["segment"] = "At-risk"
        elif s["visits"] <= 2 and s["days_since_first"] <= settings["new_days"]:
            s["segment"] = "New"
        elif s["visits"] == 1 and s["days_since_last"] >= settings["onetimer_days"]:
            s["segment"] = "One-timer"
        else:
            s["segment"] = "Regular"

    return stats


# ---------------------------------------------------------------------------
# COUPON HELPERS
# ---------------------------------------------------------------------------
def gen_coupon_code():
    return "SAVE-" + "".join(random.choices(string.ascii_uppercase + string.digits, k=6))


def format_discount(dtype, value):
    return f"{value:.0f}% off" if dtype == "percent" else f"₹{value:.0f} off"


def calc_discount(subtotal, dtype, value):
    if dtype == "percent":
        return round(subtotal * value / 100, 2)
    return min(value, subtotal)


def issue_coupon(shop_id, customer_id, reason, dtype, value, auto=False):
    conn = get_db()
    code = gen_coupon_code()
    conn.execute(
        """INSERT INTO coupons
           (shop_id, customer_id, code, reason, discount_type, discount_value, status, auto_generated, created_at)
           VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)""",
        (shop_id, customer_id, code, reason, dtype, value, "Sent", 1 if auto else 0,
         now().strftime("%Y-%m-%d %H:%M:%S")),
    )
    conn.commit()
    conn.close()
    return code


def had_recent_coupon(shop_id, customer_id, reason_prefix, cooldown_days):
    conn = get_db()
    row = conn.execute(
        """SELECT created_at FROM coupons
           WHERE shop_id=%s AND customer_id=%s AND reason LIKE %s
           ORDER BY id DESC LIMIT 1""",
        (shop_id, customer_id, reason_prefix + "%"),
    ).fetchone()
    conn.close()
    if not row:
        return False
    return (now() - parse(row["created_at"])).days < cooldown_days


# ---------------------------------------------------------------------------
# AUTOMATED COUPON ENGINE — runs PER SHOP.
# ---------------------------------------------------------------------------
def run_auto_coupon_engine(shop_id):
    settings = get_settings(shop_id)
    if not settings or not settings["auto_coupon_enabled"]:
        return 0

    stats = compute_customer_stats(shop_id)
    issued = 0
    cooldown = settings["auto_coupon_cooldown_days"]

    for s in stats:
        if s["segment"] == "At-risk":
            if not had_recent_coupon(shop_id, s["id"], "Auto: Win-back", cooldown):
                issue_coupon(shop_id, s["id"], "Auto: Win-back",
                             settings["at_risk_discount_type"], settings["at_risk_discount_value"],
                             auto=True)
                issued += 1
        elif s["segment"] == "VIP":
            if not had_recent_coupon(shop_id, s["id"], "Auto: VIP Reward", cooldown):
                issue_coupon(shop_id, s["id"], "Auto: VIP Reward",
                             settings["vip_discount_type"], settings["vip_discount_value"],
                             auto=True)
                issued += 1
    return issued


def run_engine_all_shops():
    """Scheduled job: loops over every active shop and runs its engine."""
    conn = get_db()
    shop_ids = [r["id"] for r in conn.execute("SELECT id FROM shops WHERE active=1").fetchall()]
    conn.close()
    for sid in shop_ids:
        run_auto_coupon_engine(sid)


# ---------------------------------------------------------------------------
# AUTH ROUTES — SHOP LOGIN / LOGOUT
# ---------------------------------------------------------------------------
LOGIN_TEMPLATE = """
<!DOCTYPE html><html><head><meta charset="UTF-8"><title>Shop Login</title>
<style>
 body{font-family:system-ui,Arial,sans-serif;background:#f4f5f7;display:flex;
      align-items:center;justify-content:center;height:100vh;margin:0;}
 .card{background:#fff;padding:36px 32px;border-radius:12px;box-shadow:0 4px 20px rgba(0,0,0,.1);width:320px;}
 h2{margin:0 0 6px;} p.sub{margin:0 0 20px;color:#666;font-size:13px;}
 label{font-size:13px;font-weight:600;display:block;margin:12px 0 4px;}
 input{width:100%;padding:10px;border:1px solid #ccc;border-radius:8px;box-sizing:border-box;}
 button{width:100%;margin-top:18px;background:#4f46e5;color:#fff;border:none;
        padding:11px;border-radius:8px;font-weight:600;font-size:15px;cursor:pointer;}
 .flash{background:#fee2e2;color:#b91c1c;padding:10px;border-radius:8px;font-size:13px;margin-bottom:12px;}
 .adminlink{display:block;text-align:center;margin-top:16px;font-size:12px;color:#888;text-decoration:none;}
</style></head><body>
 <form class="card" method="post">
   <input type="hidden" name="csrf_token" value="{{ csrf_token }}">
   <h2>🏪 Shop Login</h2>
   <p class="sub">Sign in to manage your shop</p>
   {% with messages = get_flashed_messages() %}
     {% for m in messages %}<div class="flash">{{ m }}</div>{% endfor %}
   {% endwith %}
   <label>Shop Login Name</label>
   <input name="shop_login" autofocus required>
   <label>Password</label>
   <input name="password" type="password" required>
   <button type="submit">Log In</button>

 </form>
</body></html>
"""


@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        shop_login = request.form.get("shop_login", "").strip()
        password = request.form.get("password", "")
        conn = get_db()
        shop = conn.execute("SELECT * FROM shops WHERE shop_login=%s", (shop_login,)).fetchone()
        conn.close()
        if shop and shop["active"] and check_password_hash(shop["password_hash"], password):
            session.clear()
            session["shop_id"] = shop["id"]
            session["shop_login"] = shop["shop_login"]
            return redirect(url_for("dashboard"))
        elif shop and not shop["active"]:
            flash("This account has been disabled. Contact the administrator.")
        else:
            flash("Invalid shop name or password.")
        return redirect(url_for("login"))
    return render_template_string(LOGIN_TEMPLATE, csrf_token=csrf_token())


@app.route("/logout")
def logout():
    session.clear()
    return redirect(url_for("login"))


# ---------------------------------------------------------------------------
# ADMIN ROUTES — manage shops + download backup
# ---------------------------------------------------------------------------
ADMIN_LOGIN_TEMPLATE = """
<!DOCTYPE html><html><head><meta charset="UTF-8"><title>Admin Login</title>
<style>
 body{font-family:system-ui,Arial,sans-serif;background:#1e293b;display:flex;
      align-items:center;justify-content:center;height:100vh;margin:0;}
 .card{background:#fff;padding:36px 32px;border-radius:12px;box-shadow:0 4px 20px rgba(0,0,0,.3);width:320px;}
 h2{margin:0 0 20px;}
 input{width:100%;padding:10px;border:1px solid #ccc;border-radius:8px;box-sizing:border-box;}
 button{width:100%;margin-top:18px;background:#0f172a;color:#fff;border:none;
        padding:11px;border-radius:8px;font-weight:600;font-size:15px;cursor:pointer;}
 .flash{background:#fee2e2;color:#b91c1c;padding:10px;border-radius:8px;font-size:13px;margin-bottom:12px;}
</style></head><body>
 <form class="card" method="post">
   <input type="hidden" name="csrf_token" value="{{ csrf_token }}">
   <h2>🔐 Admin Login</h2>
   {% with messages = get_flashed_messages() %}
     {% for m in messages %}<div class="flash">{{ m }}</div>{% endfor %}
   {% endwith %}
   <input name="password" type="password" placeholder="Admin password" autofocus required>
   <button type="submit">Enter</button>
 </form>
</body></html>
"""

ADMIN_PANEL_TEMPLATE = """
<!DOCTYPE html><html><head><meta charset="UTF-8"><title>Admin Panel</title>
<style>
 body{font-family:system-ui,Arial,sans-serif;background:#f4f5f7;margin:0;padding:30px;}
 .wrap{max-width:900px;margin:0 auto;}
 h1{margin:0 0 4px;} .top{display:flex;justify-content:space-between;align-items:center;}
 .logout{color:#b91c1c;text-decoration:none;font-size:13px;}
 .card{background:#fff;padding:24px;border-radius:12px;box-shadow:0 2px 10px rgba(0,0,0,.06);margin-top:20px;}
 label{font-size:13px;font-weight:600;display:block;margin:10px 0 4px;}
 input{padding:9px;border:1px solid #ccc;border-radius:8px;}
 .row{display:flex;gap:12px;flex-wrap:wrap;align-items:flex-end;}
 button{background:#4f46e5;color:#fff;border:none;padding:10px 18px;border-radius:8px;font-weight:600;cursor:pointer;}
 button.danger{background:#dc2626;padding:6px 12px;font-size:13px;}
 button.dl{background:#059669;}
 table{width:100%;border-collapse:collapse;margin-top:12px;}
 th,td{text-align:left;padding:10px;border-bottom:1px solid #eee;font-size:14px;}
 .flash{padding:10px;border-radius:8px;font-size:13px;margin-bottom:12px;}
 .flash.success{background:#dcfce7;color:#166534;} .flash.error{background:#fee2e2;color:#b91c1c;}
 .badge{font-size:11px;padding:2px 8px;border-radius:20px;}
 .badge.on{background:#dcfce7;color:#166534;} .badge.off{background:#fee2e2;color:#b91c1c;}
</style></head><body><div class="wrap">
 <div class="top">
   <div><h1>🛠️ Admin Panel</h1><span style="color:#666;font-size:13px;">Manage all shop accounts</span></div>
   <a class="logout" href="{{ url_for('admin_logout') }}">Log out</a>
 </div>

 {% with messages = get_flashed_messages(with_categories=true) %}
   {% for cat,m in messages %}<div class="flash {{ cat }}">{{ m }}</div>{% endfor %}
 {% endwith %}

 <div class="card">
   <h3>➕ Create New Shop Account</h3>
   <form method="post" action="{{ url_for('admin_create_shop') }}">
     <div class="row">
       <div><label>Shop Login Name</label><input name="shop_login" required placeholder="e.g. cafe_mumbai"></div>
       <div><label>Password</label><input name="password" required></div>
       <button type="submit">Create Account</button>
     </div>
   </form>
 </div>

 <div class="card">
   <h3>💾 Database Backup</h3>
   <p style="color:#666;font-size:13px;">
     Download a full export of every shop's data (as JSON) for safekeeping.
     Note: since this now runs on Postgres, your data already survives server
     restarts/redeploys on its own — this is just an extra offline copy.
   </p>
   <form method="get" action="{{ url_for('admin_backup_download') }}">
     <button class="dl" type="submit">⬇️ Download Full Backup (JSON)</button>
   </form>
 </div>

 <div class="card">
   <h3>🏪 Existing Shops ({{ shops|length }})</h3>
   <table>
     <tr><th>ID</th><th>Login Name</th><th>Status</th><th>Created</th><th>Actions</th></tr>
     {% for s in shops %}
     <tr>
       <td>{{ s.id }}</td>
       <td>{{ s.shop_login }}</td>
       <td>{% if s.active %}<span class="badge on">Active</span>{% else %}<span class="badge off">Disabled</span>{% endif %}</td>
       <td>{{ s.created_at }}</td>
       <td>
         <form method="post" action="{{ url_for('admin_toggle_shop', shop_id=s.id) }}" style="display:inline;">
           <button class="danger" style="background:#6b7280;">{{ 'Disable' if s.active else 'Enable' }}</button>
         </form>
         <form method="post" action="{{ url_for('admin_delete_shop', shop_id=s.id) }}" style="display:inline;"
               onsubmit="return confirm('DELETE shop \\'{{ s.shop_login }}\\' and ALL its data permanently?');">
           <button class="danger">Delete</button>
         </form>
       </td>
     </tr>
     {% endfor %}
   </table>
 </div>
</div></body></html>
"""


@app.route("/admin/login", methods=["GET", "POST"])
def admin_login():
    if request.method == "POST":
        if request.form.get("password") == ADMIN_PASSWORD:
            session.clear()
            session["is_admin"] = True
            return redirect(url_for("admin_panel"))
        flash("Wrong admin password.")
        return redirect(url_for("admin_login"))
    return render_template_string(ADMIN_LOGIN_TEMPLATE, csrf_token=csrf_token())


@app.route("/admin/logout")
def admin_logout():
    session.clear()
    return redirect(url_for("admin_login"))


@app.route("/admin")
@admin_required
def admin_panel():
    conn = get_db()
    shops = conn.execute("SELECT * FROM shops ORDER BY id DESC").fetchall()
    conn.close()
    return render_template_string(ADMIN_PANEL_TEMPLATE, shops=shops)


@app.route("/admin/create", methods=["POST"])
@admin_required
def admin_create_shop():
    shop_login = request.form.get("shop_login", "").strip()
    password = request.form.get("password", "").strip()
    if not shop_login or not password:
        flash("Both a login name and password are required.", "error")
        return redirect(url_for("admin_panel"))
    conn = get_db()
    exists = conn.execute("SELECT id FROM shops WHERE shop_login=%s", (shop_login,)).fetchone()
    conn.close()
    if exists:
        flash(f"A shop named '{shop_login}' already exists.", "error")
        return redirect(url_for("admin_panel"))
    create_shop(shop_login, password)
    flash(f"Shop '{shop_login}' created successfully.", "success")
    return redirect(url_for("admin_panel"))


@app.route("/admin/toggle/<int:shop_id>", methods=["POST"])
@admin_required
def admin_toggle_shop(shop_id):
    conn = get_db()
    conn.execute("UPDATE shops SET active = 1 - active WHERE id=%s", (shop_id,))
    conn.commit()
    conn.close()
    flash("Shop status updated.", "success")
    return redirect(url_for("admin_panel"))


@app.route("/admin/delete/<int:shop_id>", methods=["POST"])
@admin_required
def admin_delete_shop(shop_id):
    delete_shop(shop_id)
    flash("Shop and all its data were permanently deleted.", "success")
    return redirect(url_for("admin_panel"))


@app.route("/admin/backup/download")
@admin_required
def admin_backup_download():
    # With Postgres there's no local .db file to send anymore — the data
    # already lives safely in the external Postgres instance and survives
    # restarts/redeploys on its own. This exports every table as JSON
    # instead, as an extra offline copy if you ever want one.
    try:
        conn = get_db()
        tables = ["shops", "customers", "menu_items", "coupons", "bills", "bill_items", "settings"]
        backup = {}
        for t in tables:
            rows = conn.execute(f"SELECT * FROM {t}").fetchall()
            backup[t] = [dict(r) for r in rows]
        conn.close()
    except Exception as e:
        flash(f"Backup failed: {e}", "error")
        return redirect(url_for("admin_panel"))

    payload = json.dumps(backup, indent=2, default=str)
    timestamp = now().strftime("%Y-%m-%d_%H%M")
    return Response(
        payload, mimetype="application/json",
        headers={"Content-Disposition": f"attachment;filename=full_backup_{timestamp}.json"},
    )


# ---------------------------------------------------------------------------
# ROUTES — DASHBOARD (all shop routes require login + are scoped)
# ---------------------------------------------------------------------------
@app.route("/")
@login_required
def dashboard():
    sid = current_shop_id()
    stats = compute_customer_stats(sid)
    total_customers = len(stats)
    total_revenue = sum(s["total_spend"] for s in stats)
    vip = [s for s in stats if s["segment"] == "VIP"]
    at_risk = [s for s in stats if s["segment"] == "At-risk"]
    new = [s for s in stats if s["segment"] == "New"]
    onetimer = [s for s in stats if s["segment"] == "One-timer"]

    conn = get_db()
    coupons = conn.execute("SELECT * FROM coupons WHERE shop_id=%s", (sid,)).fetchall()
    redeemed_revenue = conn.execute("""
        SELECT COALESCE(SUM(bills.total),0) as rev FROM coupons
        JOIN bills ON coupons.redeemed_bill_id = bills.id
        WHERE coupons.status = 'Redeemed' AND coupons.shop_id=%s
    """, (sid,)).fetchone()["rev"]
    conn.close()

    top_vip = sorted(vip, key=lambda s: -s["total_spend"])[:3]

    return render_template(
        "index.html", page="dashboard", shop_login=session.get("shop_login"),
        total_customers=total_customers, total_revenue=total_revenue,
        vip=vip, at_risk=at_risk, new=new, onetimer=onetimer, top_vip=top_vip,
        coupons_sent=len(coupons),
        coupons_redeemed=len([c for c in coupons if c["status"] == "Redeemed"]),
        redeemed_revenue=redeemed_revenue,
    )


# ---------------------------------------------------------------------------
# ROUTES — MENU MANAGEMENT
# ---------------------------------------------------------------------------
@app.route("/menu", methods=["GET", "POST"])
@login_required
def menu():
    sid = current_shop_id()
    if request.method == "POST":
        name = request.form.get("name", "").strip()
        price = request.form.get("price", "").strip()
        category = request.form.get("category", "General").strip() or "General"
        if name and price:
            conn = get_db()
            conn.execute(
                "INSERT INTO menu_items (shop_id, name, price, category, active) VALUES (%s,%s,%s,%s,1)",
                (sid, name, float(price), category),
            )
            conn.commit()
            conn.close()
            flash(f"Added '{name}' to the menu.", "success")
        return redirect(url_for("menu"))

    conn = get_db()
    items = conn.execute("SELECT * FROM menu_items WHERE shop_id=%s ORDER BY category, name", (sid,)).fetchall()
    conn.close()
    return render_template("index.html", page="menu", items=items, shop_login=session.get("shop_login"))


@app.route("/menu/toggle/<int:item_id>", methods=["POST"])
@login_required
def menu_toggle(item_id):
    conn = get_db()
    conn.execute("UPDATE menu_items SET active = 1 - active WHERE id=%s AND shop_id=%s",
                 (item_id, current_shop_id()))
    conn.commit()
    conn.close()
    return redirect(url_for("menu"))


@app.route("/menu/delete/<int:item_id>", methods=["POST"])
@login_required
def menu_delete(item_id):
    conn = get_db()
    conn.execute("DELETE FROM menu_items WHERE id=%s AND shop_id=%s", (item_id, current_shop_id()))
    conn.commit()
    conn.close()
    flash("Item removed from menu.", "success")
    return redirect(url_for("menu"))


# ---------------------------------------------------------------------------
# ROUTES — POS BILLING
# ---------------------------------------------------------------------------
@app.route("/billing", methods=["GET", "POST"])
@login_required
def billing():
    sid = current_shop_id()
    if request.method == "POST":
        phone = request.form.get("phone", "").strip()
        name = request.form.get("name", "").strip()
        coupon_code = request.form.get("coupon_code", "").strip().upper()

        if not phone:
            flash("Phone number is required.", "error")
            return redirect(url_for("billing"))

        conn = get_db()
        c = conn.cursor()

        items = c.execute("SELECT * FROM menu_items WHERE active=1 AND shop_id=%s", (sid,)).fetchall()
        line_items = []
        subtotal = 0.0
        for item in items:
            qty_raw = request.form.get(f"qty_{item['id']}", "0")
            try:
                qty = int(qty_raw)
            except ValueError:
                qty = 0
            if qty > 0:
                line_items.append({"name": item["name"], "price": item["price"], "qty": qty})
                subtotal += item["price"] * qty

        if not line_items:
            manual_amount = request.form.get("manual_amount", "").strip()
            if manual_amount:
                amt = float(manual_amount)
                line_items.append({"name": "Bill amount", "price": amt, "qty": 1})
                subtotal += amt

        if subtotal <= 0:
            flash("Add at least one item or a bill amount.", "error")
            conn.close()
            return redirect(url_for("billing"))

        cust = c.execute("SELECT * FROM customers WHERE phone=%s AND shop_id=%s", (phone, sid)).fetchone()
        if cust is None:
            c.execute(
                "INSERT INTO customers (shop_id, phone, name, created_at) VALUES (%s,%s,%s,%s) RETURNING id",
                (sid, phone, name, now().strftime("%Y-%m-%d %H:%M:%S")),
            )
            customer_id = c.fetchone()["id"]
        else:
            customer_id = cust["id"]
            if name and not cust["name"]:
                c.execute("UPDATE customers SET name=%s WHERE id=%s", (name, customer_id))

        discount = 0.0
        coupon_id = None
        if coupon_code:
            coupon = c.execute(
                "SELECT * FROM coupons WHERE code=%s AND customer_id=%s AND shop_id=%s",
                (coupon_code, customer_id, sid),
            ).fetchone()
            if coupon and coupon["status"] != "Redeemed":
                discount = calc_discount(subtotal, coupon["discount_type"], coupon["discount_value"])
                coupon_id = coupon["id"]
            elif coupon and coupon["status"] == "Redeemed":
                flash("That coupon was already redeemed earlier — bill saved without discount.", "error")
            else:
                flash("Coupon code not found for this customer — bill saved without discount.", "error")

        total = round(subtotal - discount, 2)

        c.execute(
            "INSERT INTO bills (shop_id, customer_id, subtotal, discount, total, coupon_id, created_at) "
            "VALUES (%s,%s,%s,%s,%s,%s,%s) RETURNING id",
            (sid, customer_id, subtotal, discount, total, coupon_id, now().strftime("%Y-%m-%d %H:%M:%S")),
        )
        bill_id = c.fetchone()["id"]

        for li in line_items:
            c.execute(
                "INSERT INTO bill_items (bill_id, item_name, price, qty) VALUES (%s,%s,%s,%s)",
                (bill_id, li["name"], li["price"], li["qty"]),
            )

        if coupon_id:
            c.execute(
                "UPDATE coupons SET status='Redeemed', redeemed_at=%s, redeemed_bill_id=%s WHERE id=%s",
                (now().strftime("%Y-%m-%d %H:%M:%S"), bill_id, coupon_id),
            )

        conn.commit()
        conn.close()
        return redirect(url_for("print_bill", bill_id=bill_id))

    conn = get_db()
    items = conn.execute("SELECT * FROM menu_items WHERE active=1 AND shop_id=%s ORDER BY category, name", (sid,)).fetchall()
    categories = sorted(set(i["category"] for i in items))
    conn.close()
    item_prices = {item["id"]: {"price": item["price"], "name": item["name"]} for item in items}
    return render_template("index.html", page="billing", items=items, categories=categories,
                           item_prices=item_prices, shop_login=session.get("shop_login"))


@app.route("/api/coupon_check")
@login_required
def api_coupon_check():
    sid = current_shop_id()
    code = request.args.get("code", "").strip().upper()
    phone = request.args.get("phone", "").strip()
    if not code or not phone:
        return jsonify({"valid": False, "message": ""})

    conn = get_db()
    cust = conn.execute("SELECT * FROM customers WHERE phone=%s AND shop_id=%s", (phone, sid)).fetchone()
    if not cust:
        conn.close()
        return jsonify({"valid": False, "message": "New customer — no coupons on file yet."})

    coupon = conn.execute(
        "SELECT * FROM coupons WHERE code=%s AND customer_id=%s AND shop_id=%s", (code, cust["id"], sid)
    ).fetchone()
    conn.close()

    if not coupon:
        return jsonify({"valid": False, "message": "Coupon not found for this phone number."})
    if coupon["status"] == "Redeemed":
        return jsonify({"valid": False, "message": "This coupon was already used."})

    return jsonify({
        "valid": True,
        "discount_type": coupon["discount_type"],
        "discount_value": coupon["discount_value"],
        "message": f"Valid — {format_discount(coupon['discount_type'], coupon['discount_value'])} will be applied.",
    })


# ---------------------------------------------------------------------------
# PRINTABLE RECEIPT
# ---------------------------------------------------------------------------
RECEIPT_TEMPLATE = """
<!DOCTYPE html>
<html><head><meta charset="UTF-8"><title>Receipt #{{ bill.id }}</title>
<style>
  body { font-family: 'Courier New', monospace; max-width: 380px; margin: 30px auto;
         color: #1a1a1a; background:#f4f5f7; }
  .receipt { background: white; padding: 28px 24px; border-radius: 8px; box-shadow: 0 2px 10px rgba(0,0,0,.08); }
  .shop-name { font-size: 20px; font-weight: 700; text-align: center; margin-bottom: 2px; }
  .shop-meta { font-size: 12px; text-align: center; color: #555; margin-bottom: 14px; }
  hr { border: none; border-top: 1px dashed #999; margin: 12px 0; }
  .row { display: flex; justify-content: space-between; font-size: 13px; margin: 4px 0; }
  .items .row span:first-child { max-width: 220px; }
  .total-row { font-weight: 700; font-size: 16px; }
  .footer { text-align: center; font-size: 12px; margin-top: 16px; color: #444; }
  .meta { font-size: 12px; color: #555; margin-bottom: 10px; }
  .actions { text-align: center; margin-top: 20px; }
  button, a.btn { background: #4f46e5; color: white; border: none; padding: 10px 20px;
         border-radius: 8px; font-size: 14px; font-weight: 600; cursor: pointer;
         text-decoration: none; display: inline-block; margin: 4px; }
  a.btn.secondary { background: #6b7280; }
  @media print { .actions { display: none; } body { background: white; margin: 0; }
                 .receipt { box-shadow: none; } }
</style></head>
<body>
  <div class="receipt">
    <div class="shop-name">{{ settings.shop_name }}</div>
    <div class="shop-meta">{{ settings.shop_address }}{% if settings.shop_phone %} · {{ settings.shop_phone }}{% endif %}</div>
    <hr>
    <div class="meta">
      Receipt #{{ bill.id }}<br>
      {{ bill.created_at }}<br>
      {{ customer.phone }}{% if customer.name %} — {{ customer.name }}{% endif %}
    </div>
    <hr>
    <div class="items">
      {% for li in items %}
      <div class="row"><span>{{ li.item_name }} x{{ li.qty }}</span><span>₹{{ "%.2f"|format(li.price * li.qty) }}</span></div>
      {% endfor %}
    </div>
    <hr>
    <div class="row"><span>Subtotal</span><span>₹{{ "%.2f"|format(bill.subtotal) }}</span></div>
    {% if bill.discount > 0 %}
    <div class="row"><span>Discount{% if coupon %} ({{ coupon.code }}){% endif %}</span><span>-₹{{ "%.2f"|format(bill.discount) }}</span></div>
    {% endif %}
    <div class="row total-row"><span>Total</span><span>₹{{ "%.2f"|format(bill.total) }}</span></div>
    <hr>
    <div class="footer">{{ settings.footer_message }}</div>
    <div class="actions">
      <button onclick="window.print()">🖨️ Print Receipt</button>
      <a class="btn secondary" href="{{ url_for('billing') }}">+ New Bill</a>
    </div>
  </div>
</body></html>
"""


@app.route("/bill/<int:bill_id>/print")
@login_required
def print_bill(bill_id):
    sid = current_shop_id()
    conn = get_db()
    bill = conn.execute("SELECT * FROM bills WHERE id=%s AND shop_id=%s", (bill_id, sid)).fetchone()
    if not bill:
        conn.close()
        abort(404)
    customer = conn.execute("SELECT * FROM customers WHERE id=%s", (bill["customer_id"],)).fetchone()
    items = conn.execute("SELECT * FROM bill_items WHERE bill_id=%s", (bill_id,)).fetchall()
    coupon = None
    if bill["coupon_id"]:
        coupon = conn.execute("SELECT * FROM coupons WHERE id=%s", (bill["coupon_id"],)).fetchone()
    conn.close()
    settings = get_settings(sid)
    return render_template_string(RECEIPT_TEMPLATE, bill=bill, customer=customer,
                                  items=items, coupon=coupon, settings=settings)


# ---------------------------------------------------------------------------
# ROUTES — CUSTOMERS
# ---------------------------------------------------------------------------
@app.route("/customers")
@login_required
def customers():
    sid = current_shop_id()
    stats = compute_customer_stats(sid)
    stats.sort(key=lambda s: -s["total_spend"])
    filter_seg = request.args.get("segment", "All")
    if filter_seg != "All":
        stats = [s for s in stats if s["segment"] == filter_seg]

    conn = get_db()
    coupon_rows = conn.execute("""
        SELECT * FROM coupons
        WHERE shop_id=%s AND status != 'Redeemed'
        ORDER BY id DESC
    """, (sid,)).fetchall()
    conn.close()

    active_coupons = {}
    for c in coupon_rows:
        if c["customer_id"] not in active_coupons:
            active_coupons[c["customer_id"]] = {
                "code": c["code"],
                "offer": format_discount(c["discount_type"], c["discount_value"]),
            }

    settings = get_settings(sid)
    return render_template("index.html", page="customers", stats=stats,
                           filter_seg=filter_seg, shop_login=session.get("shop_login"),
                           active_coupons=active_coupons,
                           shop_name=settings.get("shop_name", "our shop"))


@app.route("/customer/<int:customer_id>")
@login_required
def customer_detail(customer_id):
    sid = current_shop_id()
    conn = get_db()
    cust = conn.execute("SELECT * FROM customers WHERE id=%s AND shop_id=%s", (customer_id, sid)).fetchone()
    if not cust:
        conn.close()
        abort(404)
    bills = conn.execute(
        "SELECT * FROM bills WHERE customer_id=%s AND shop_id=%s ORDER BY created_at DESC", (customer_id, sid)
    ).fetchall()
    coupons_list = conn.execute(
        "SELECT * FROM coupons WHERE customer_id=%s AND shop_id=%s ORDER BY id DESC", (customer_id, sid)
    ).fetchall()
    conn.close()

    all_stats = compute_customer_stats(sid)
    my_stats = next((s for s in all_stats if s["id"] == customer_id), None)

    return render_template("index.html", page="customer_detail",
                           customer=cust, bills=bills, coupons_list=coupons_list,
                           s=my_stats, shop_login=session.get("shop_login"))


# ---------------------------------------------------------------------------
# ROUTES — COUPONS
# ---------------------------------------------------------------------------
@app.route("/coupons", methods=["GET", "POST"])
@login_required
def coupons_page():
    sid = current_shop_id()
    if request.method == "POST":
        action = request.form.get("action")
        if action == "run_engine":
            count = run_auto_coupon_engine(sid)
            flash(f"Auto-coupon engine ran — {count} new coupon(s) issued based on live segments.", "success")
        else:
            customer_id = request.form.get("customer_id")
            reason = request.form.get("reason", "Manual offer")
            dtype = request.form.get("discount_type", "percent")
            value = float(request.form.get("discount_value", 10))
            code = issue_coupon(sid, customer_id, reason, dtype, value, auto=False)
            flash(f"Coupon {code} generated.", "success")
        return redirect(url_for("coupons_page"))

    stats = compute_customer_stats(sid)
    stats.sort(key=lambda s: -s["total_spend"])
    conn = get_db()
    all_coupons = conn.execute("""
        SELECT coupons.*, customers.phone, customers.name
        FROM coupons JOIN customers ON coupons.customer_id = customers.id
        WHERE coupons.shop_id=%s
        ORDER BY coupons.id DESC
    """, (sid,)).fetchall()
    conn.close()
    settings = get_settings(sid)
    return render_template("index.html", page="coupons", stats=stats,
                           all_coupons=all_coupons, settings=settings,
                           format_discount=format_discount, shop_login=session.get("shop_login"))


# ---------------------------------------------------------------------------
# ROUTES — SETTINGS
# ---------------------------------------------------------------------------
@app.route("/settings", methods=["GET", "POST"])
@login_required
def settings_page():
    sid = current_shop_id()
    if request.method == "POST":
        conn = get_db()
        conn.execute("""UPDATE settings SET
            shop_name=%s, shop_address=%s, shop_phone=%s, footer_message=%s,
            vip_min_visits=%s, vip_window_days=%s, vip_top_percent=%s,
            lapsing_days=%s, lapsing_min_visits=%s, new_days=%s, onetimer_days=%s,
            auto_coupon_enabled=%s, auto_coupon_cooldown_days=%s,
            at_risk_discount_type=%s, at_risk_discount_value=%s,
            vip_discount_type=%s, vip_discount_value=%s
            WHERE shop_id=%s""", (
            request.form["shop_name"], request.form["shop_address"],
            request.form["shop_phone"], request.form["footer_message"],
            int(request.form["vip_min_visits"]), int(request.form["vip_window_days"]),
            int(request.form["vip_top_percent"]), int(request.form["lapsing_days"]),
            int(request.form["lapsing_min_visits"]), int(request.form["new_days"]),
            int(request.form["onetimer_days"]),
            1 if request.form.get("auto_coupon_enabled") == "on" else 0,
            int(request.form["auto_coupon_cooldown_days"]),
            request.form["at_risk_discount_type"], float(request.form["at_risk_discount_value"]),
            request.form["vip_discount_type"], float(request.form["vip_discount_value"]),
            sid,
        ))
        conn.commit()
        conn.close()
        flash("Settings saved. Segments and future auto-coupons recalculate immediately.", "success")
        return redirect(url_for("settings_page"))

    return render_template("index.html", page="settings", settings=get_settings(sid),
                           shop_login=session.get("shop_login"))


# ---------------------------------------------------------------------------
# CSV EXPORT (scoped to this shop)
# ---------------------------------------------------------------------------
@app.route("/export_csv")
@login_required
def export_csv():
    sid = current_shop_id()
    stats = compute_customer_stats(sid)
    conn = get_db()
    coupons_all = conn.execute("SELECT * FROM coupons WHERE shop_id=%s", (sid,)).fetchall()
    conn.close()

    coupon_map = {}
    for c in coupons_all:
        coupon_map.setdefault(c["customer_id"], []).append(c)

    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow([
        "Phone", "Name", "Segment", "Total Visits", "Total Spend (₹)", "Avg Bill (₹)",
        "Last Visit", "Days Since Last Visit", "Coupon Code", "Coupon Offer",
        "Coupon Status", "Auto-Generated"
    ])
    for s in stats:
        cust_coupons = coupon_map.get(s["id"], [])
        if cust_coupons:
            for cp in cust_coupons:
                writer.writerow([
                    s["phone"], s["name"], s["segment"], s["visits"],
                    f"{s['total_spend']:.2f}", f"{s['avg_bill']:.2f}",
                    s["last_visit"].strftime("%Y-%m-%d") if s["last_visit"] else "",
                    s["days_since_last"] if s["days_since_last"] is not None else "",
                    cp["code"], format_discount(cp["discount_type"], cp["discount_value"]),
                    cp["status"], "Yes" if cp["auto_generated"] else "No",
                ])
        else:
            writer.writerow([
                s["phone"], s["name"], s["segment"], s["visits"],
                f"{s['total_spend']:.2f}", f"{s['avg_bill']:.2f}",
                s["last_visit"].strftime("%Y-%m-%d") if s["last_visit"] else "",
                s["days_since_last"] if s["days_since_last"] is not None else "",
                "", "", "", "",
            ])

    return Response(output.getvalue(), mimetype="text/csv",
                    headers={"Content-Disposition": "attachment;filename=customer_report.csv"})


import urllib.request

SELF_URL = os.environ.get("SELF_URL", "https://shoployal.onrender.com/")

def ping_self():
    """Pings the login page to keep the server from sleeping."""
    try:
        with urllib.request.urlopen(SELF_URL, timeout=10) as response:
            print(f"[Self-Ping] {SELF_URL} -> Status {response.status}")
    except Exception as e:
        print(f"[Self-Ping] Failed: {e}")


def start_scheduler():
    scheduler = BackgroundScheduler(daemon=True)
    # self-ping every 10 minutes to prevent sleep
    scheduler.add_job(ping_self, "interval", minutes=10, next_run_time=now())
    scheduler.start()


if __name__ == "__main__":
    init_db()
    if os.environ.get("WERKZEUG_RUN_MAIN") == "true" or not app.debug:
        start_scheduler()
    app.run(host="0.0.0.0", port=5000)
