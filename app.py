
import os
import logging
import re
import json
import html
import hashlib
import uuid
import secrets
import string
import asyncio
from datetime import datetime, timezone, timedelta
from decimal import Decimal, ROUND_DOWN
from typing import Any, Optional
from functools import wraps
from threading import RLock
from types import SimpleNamespace
from zoneinfo import ZoneInfo

import httpx
import firebase_admin
from firebase_admin import credentials, db as firebase_db
from fastapi import FastAPI, Request, HTTPException
from fastapi.responses import HTMLResponse, Response
from pydantic import BaseModel
from telegram import (
    BotCommand, BotCommandScopeDefault, BotCommandScopeAllPrivateChats,
    BotCommandScopeAllGroupChats,
    CopyTextButton, Update, InlineKeyboardButton, InlineKeyboardMarkup,
    KeyboardButton, ReplyKeyboardMarkup,
)
from telegram.helpers import escape_markdown
from telegram.ext import (
    Application,
    CommandHandler,
    CallbackQueryHandler,
    ChatMemberHandler,
    MessageHandler,
    ContextTypes,
    filters,
)


logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("custom_call_bot")

BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
ADMIN_ID = int(os.getenv("ADMIN_ID", "7034779471"))
PUBLIC_BASE_URL = os.getenv("PUBLIC_BASE_URL", "").rstrip("/")
TELEGRAM_WEBHOOK_SECRET = os.getenv("TELEGRAM_WEBHOOK_SECRET", "").strip()
CALL_API_TOKEN = os.getenv("CALL_API_TOKEN", "").strip()
CALL_API_BASE = os.getenv("CALL_API_BASE", "https://sms.bd1b.com/api/v1").rstrip("/")
if CALL_API_BASE.lower().endswith("/call"):
    CALL_API_BASE = CALL_API_BASE[:-5].rstrip("/")
CALL_WEBHOOK_SECRET = os.getenv("CALL_WEBHOOK_SECRET", "").strip()
PAYMENT_REVIEW_CHAT_ID = os.getenv("PAYMENT_REVIEW_CHAT_ID", "@ffxemon").strip()
SUPPORT_CONTACT_URL = os.getenv("SUPPORT_CONTACT_URL", f"tg://user?id={os.getenv('ADMIN_ID', '7034779471').strip()}").strip()
REQUIRED_CHANNEL_USERNAME = os.getenv("REQUIRED_CHANNEL_USERNAME", "@CyberShunya_x").strip() or "@CyberShunya_x"
FIREBASE_DATABASE_URL = os.getenv("FIREBASE_DATABASE_URL", "").strip()
FIREBASE_CREDENTIALS_JSON = os.getenv("FIREBASE_CREDENTIALS_JSON", "").strip()
PORT = int(os.getenv("PORT", "8000"))

if not BOT_TOKEN:
    raise RuntimeError("BOT_TOKEN is missing")
if not CALL_API_TOKEN:
    raise RuntimeError("CALL_API_TOKEN is missing")
if not FIREBASE_CREDENTIALS_JSON:
    raise RuntimeError("FIREBASE_CREDENTIALS_JSON is missing")
if not FIREBASE_DATABASE_URL:
    raise RuntimeError("FIREBASE_DATABASE_URL is missing")

try:
    service_account_info = json.loads(FIREBASE_CREDENTIALS_JSON)
except json.JSONDecodeError as exc:
    raise RuntimeError("FIREBASE_CREDENTIALS_JSON is not valid JSON") from exc

if not firebase_admin._apps:
    cred = credentials.Certificate(service_account_info)
    firebase_options = {"databaseURL": FIREBASE_DATABASE_URL}
    firebase_admin.initialize_app(cred, firebase_options)


def _db_json(value):
    if isinstance(value, datetime):
        return value.astimezone(UTC).isoformat()
    if isinstance(value, dict):
        return {str(k): _db_json(v) for k, v in value.items() if v is not None}
    if isinstance(value, (list, tuple)):
        return [_db_json(v) for v in value]
    if isinstance(value, float) and (value != value or value in (float("inf"), float("-inf"))):
        return 0
    return value


class _Increment:
    def __init__(self, amount):
        self.amount = amount


class _Snapshot:
    def __init__(self, reference, value):
        self.reference = reference
        self.id = reference.id
        self.exists = value is not None
        self._value = value

    def to_dict(self):
        return dict(self._value) if isinstance(self._value, dict) else {}


_TRANSACTION_LOCK = RLock()


class _RtdbDocumentReference:
    def __init__(self, path):
        self.path = path.strip("/")
        self.id = self.path.rsplit("/", 1)[-1]
        self._ref = firebase_db.reference(self.path)

    def get(self, transaction=None):
        return _Snapshot(self, self._ref.get())

    def set(self, data, merge=False):
        if merge:
            self.update(data)
        else:
            self._ref.set(_db_json(data))

    def update(self, data):
        with _TRANSACTION_LOCK:
            current = self.get().to_dict()
            changes = {}
            for key, value in data.items():
                if isinstance(value, _Increment):
                    value = (current.get(key, 0) or 0) + value.amount
                changes[f"{self.path}/{key}"] = _db_json(value)
            if changes:
                firebase_db.reference("/").update(changes)

    def create(self, data):
        with _TRANSACTION_LOCK:
            if self.get().exists:
                raise ValueError("This operation was already recorded. Duplicate update blocked.")
            self._ref.set(_db_json(data))

    def delete(self):
        with _TRANSACTION_LOCK:
            self._ref.delete()


class _RtdbQuery:
    def __init__(self, path):
        self.path = path.strip("/")
        self.filters = []
        self.sort_field = None
        self.sort_direction = "ASCENDING"
        self.max_results = None

    def where(self, field, op, value):
        if op not in {"==", "!=", ">", ">=", "<", "<="}:
            raise ValueError(f"Unsupported query operator: {op}")
        self.filters.append((field, op, value))
        return self

    def order_by(self, field, direction="ASCENDING"):
        self.sort_field = field
        self.sort_direction = direction
        return self

    def limit(self, count):
        self.max_results = int(count)
        return self

    def stream(self):
        raw = firebase_db.reference(self.path).get() or {}
        if not isinstance(raw, dict):
            return iter(())
        docs = []
        for key, value in raw.items():
            if not isinstance(value, dict):
                continue
            ref = _RtdbDocumentReference(f"{self.path}/{key}")
            snapshot = _Snapshot(ref, value)
            item = snapshot.to_dict()
            valid = True
            for field, op, expected in self.filters:
                actual = item.get(field)
                if op == "==": valid = actual == expected
                elif op == "!=": valid = actual != expected
                elif op == ">": valid = actual is not None and actual > expected
                elif op == ">=": valid = actual is not None and actual >= expected
                elif op == "<": valid = actual is not None and actual < expected
                elif op == "<=": valid = actual is not None and actual <= expected
                if not valid:
                    break
            if valid:
                docs.append(snapshot)
        if self.sort_field:
            def sk(snap):
                value = (snap.to_dict() or {}).get(self.sort_field)
                if value is None:
                    return ""
                if isinstance(value, datetime):
                    return value.isoformat()
                return str(value)
            docs.sort(key=sk, reverse=self.sort_direction == "DESCENDING")
        if self.max_results is not None:
            docs = docs[:self.max_results]
        return iter(docs)


class _RtdbCollectionReference(_RtdbQuery):
    def document(self, document_id=None):
        if document_id is None:
            document_id = firebase_db.reference(self.path).push().key
        return _RtdbDocumentReference(f"{self.path}/{document_id}")

    def add(self, data):
        ref = self.document()
        ref.set(data)
        return now(), ref


class _RtdbTransaction:
    def __init__(self):
        self.operations = []

    def update(self, reference, data):
        self.operations.append(("update", reference, dict(data)))

    def create(self, reference, data):
        self.operations.append(("create", reference, dict(data)))

    def commit(self):
        updates = {}
        for operation, reference, data in self.operations:
            if operation == "create":
                if reference.get().exists:
                    raise ValueError("This operation was already recorded. Duplicate update blocked.")
                updates[reference.path] = _db_json(data)
                continue
            current = reference.get().to_dict()
            for key, value in data.items():
                if isinstance(value, _Increment):
                    value = (current.get(key, 0) or 0) + value.amount
                updates[f"{reference.path}/{key}"] = _db_json(value)
        if updates:
            firebase_db.reference("/").update(updates)


class _DatabaseCompat:
    def collection(self, path):
        return _RtdbCollectionReference(path)

    def transaction(self):
        return _RtdbTransaction()


def _transactional(function):
    @wraps(function)
    def run(transaction, *args, **kwargs):
        with _TRANSACTION_LOCK:
            result = function(transaction, *args, **kwargs)
            transaction.commit()
            return result
    return run


firestore = SimpleNamespace(
    transactional=_transactional,
    Increment=_Increment,
    Query=SimpleNamespace(DESCENDING="DESCENDING", ASCENDING="ASCENDING"),
)
db = _DatabaseCompat()
bucket = None

provider_http_client: Optional[httpx.AsyncClient] = None
provider_call_semaphore: Optional[asyncio.Semaphore] = None
audio_proxy_semaphore: Optional[asyncio.Semaphore] = None
USER_CALL_LOCKS: dict[int, asyncio.Lock] = {}

app = FastAPI(title="Custom Call Bot", version="1.0.0")

telegram_app: Optional[Application] = None
channel_recheck_task: Optional[asyncio.Task] = None

COL_USERS = "users"
COL_CALLS = "calls"
COL_LEDGER = "ledger"
COL_CODES = "redeem_codes"
COL_PAYMENTS = "payments"
COL_AUDIT = "audit_logs"
COL_SETTINGS = "settings"
COL_PROVIDER_AUDIO = "provider_audio_tokens"
COL_VOICE_TEMPLATES = "voice_templates"

UTC = timezone.utc

DEFAULT_SETTINGS = {
    "settings_schema": 4,
    "brand_name": "Custom Call",
    "maintenance": False,
    "call_credit_cost": 1.0,
    "daily_call_limit": 100,
    "call_cooldown_seconds": 15,
    "referral_bonus": 1.0,
    "daily_bonus": 1.0,
    "daily_bonus_enabled": False,
    "welcome_bonus": 1.0,
    "bkash_number": "01819202231",
    "nagad_number": "01819202231",
    "rocket_number": "",
    "bkash_enabled": True,
    "nagad_enabled": True,
    "rocket_enabled": False,
    "bkash_action": "send_money",
    "nagad_action": "send_money",
    "rocket_action": "send_money",
    "payment_number": "01819202231",
    "payment_review_chat_id": PAYMENT_REVIEW_CHAT_ID or "@ffxemon",
    "purchase_limit_count": 3,
    "purchase_limit_minutes": 10,
    "required_channel": REQUIRED_CHANNEL_USERNAME,
    "min_redeem_credits": 1.0,
    "support_text": "সহায়তার জন্য নিচের ‘Message Support Admin’ বাটনে চাপ দিন।",
    "support_contact_url": SUPPORT_CONTACT_URL,
    "buy_text": "প্যাকেজ নির্বাচন করুন, বিকাশ/নগদে পেমেন্ট করুন, তারপর Transaction ID পাঠান। অ্যাডমিন যাচাই করে ক্রেডিট যোগ করবেন।",
    "admin_notice": "Please call only people who have agreed to receive the call.",
    "packages": [
        {"id": "p50", "credits": 50, "price": 60, "label": "📞 50 Calls — 60 TK"},
        {"id": "p100", "credits": 100, "price": 100, "label": "📞 100 Calls — 100 TK"},
        {"id": "p200", "credits": 200, "price": 180, "label": "📞 200 Calls — 180 TK"},
        {"id": "p300", "credits": 300, "price": 240, "label": "📞 300 Calls — 240 TK"},
        {"id": "p500", "credits": 500, "price": 380, "label": "📞 500 Calls — 380 TK"},
    ],
    "payment_methods": [
        {"name": "bKash", "key": "bkash", "account": "01819202231"},
        {"name": "Nagad", "key": "nagad", "account": "01819202231"},
    ],
}


def now():
    return datetime.now(UTC)


def local_day_key():
    return datetime.now(ZoneInfo("Asia/Dhaka")).date().isoformat()


def parse_datetime(value):
    if isinstance(value, datetime):
        return value.replace(tzinfo=UTC) if value.tzinfo is None else value.astimezone(UTC)
    if isinstance(value, str) and value.strip():
        try:
            parsed = datetime.fromisoformat(value.strip().replace("Z", "+00:00"))
            return parsed.replace(tzinfo=UTC) if parsed.tzinfo is None else parsed.astimezone(UTC)
        except ValueError:
            return None
    return None


def iso(dt: Optional[datetime]) -> Optional[str]:
    parsed = parse_datetime(dt)
    if parsed is not None:
        return parsed.isoformat()
    return str(dt) if dt is not None else None


def clean_text(value: Any, limit: int = 4000) -> str:
    text = "" if value is None else str(value)
    text = text.replace("\x00", "").strip()
    return text[:limit]


def normalize_phone(raw: str) -> Optional[str]:
    digits = re.sub(r"\D+", "", raw or "")
    if digits.startswith("0088"):
        digits = digits[2:]
    if digits.startswith("01") and len(digits) == 11:
        digits = "88" + digits
    if digits.startswith("8801") and len(digits) == 13:
        pass
    elif digits.startswith("1") and len(digits) == 10:
        digits = "880" + digits
    if not (8 <= len(digits) <= 15):
        return None
    return digits


def credits_float(value: Any) -> float:
    try:
        d = Decimal(str(value)).quantize(Decimal("0.01"), rounding=ROUND_DOWN)
        return float(d)
    except Exception:
        return 0.0


def _safe_int(value):
    try:
        if value is None or str(value).strip() == "":
            return None
        return int(str(value).strip())
    except (TypeError, ValueError):
        return None


def telegram_id_for_record(snapshot):
    item = snapshot.to_dict() or {}
    for field in ("telegram_id", "user_id", "chat_id", "telegram_chat_id"):
        value = _safe_int(item.get(field))
        if value is not None and value != 0:
            return value
    return _safe_int(snapshot.id)


def ledger_ref_for(user_id: int, reason: str, reference: str = ""):
    reference = clean_text(reference, 250)
    if not reference:
        reference = uuid.uuid4().hex
    key = hashlib.sha256(f"{int(user_id)}|{reason}|{reference}".encode()).hexdigest()[:40]
    return db.collection(COL_LEDGER).document(key)

def user_ref(user_id: int):
    key = str(user_id).strip()
    direct = db.collection(COL_USERS).document(key)
    if direct.get().exists:
        return direct
    # Backward compatibility for imported records stored under a Firebase UID.
    target = _safe_int(key)
    if target is not None:
        for snap in db.collection(COL_USERS).stream():
            item = snap.to_dict() or {}
            for field in ("user_id", "telegram_id", "chat_id"):
                if _safe_int(item.get(field)) == target:
                    return snap.reference
    return direct

def get_settings() -> dict:
    ref = db.collection(COL_SETTINGS).document("app")
    snap = ref.get()
    data = snap.to_dict() if snap.exists else {}
    if not data:
        ref.set(DEFAULT_SETTINGS)
        data = dict(DEFAULT_SETTINGS)
    elif (_safe_int(data.get("settings_schema", 0)) or 0) < 3:
        old_number = re.sub(r"\D+", "", str(data.get("payment_number") or "01819202231"))
        data.update({
            "settings_schema": 3,
            "referral_bonus": data.get("referral_bonus", 1.0),
            "daily_bonus_enabled": data.get("daily_bonus_enabled", False),
            "bkash_number": data.get("bkash_number") or old_number,
            "nagad_number": data.get("nagad_number") or old_number,
            "payment_number": old_number,
            "payment_review_chat_id": data.get("payment_review_chat_id") or PAYMENT_REVIEW_CHAT_ID or "@ffxemon",
            "purchase_limit_count": 3,
            "purchase_limit_minutes": 10,
            "required_channel": REQUIRED_CHANNEL_USERNAME,
            "packages": list(DEFAULT_SETTINGS["packages"]),
        })
        ref.set(data, merge=True)
    if (_safe_int(data.get("settings_schema", 0)) or 0) < 4:
        if data.get("support_text") == "Support er jonno niche Message Support Admin button tap koro.":
            data["support_text"] = DEFAULT_SETTINGS["support_text"]
        if data.get("buy_text") == "Package select koro, bKash/Nagad-e payment koro, tarpor Transaction ID submit koro. Admin verify korle credits auto add hobe.":
            data["buy_text"] = DEFAULT_SETTINGS["buy_text"]
        data["settings_schema"] = 4
        ref.set(data, merge=True)
    merged = dict(DEFAULT_SETTINGS)
    merged.update(data)
    if not isinstance(merged.get("packages"), list):
        merged["packages"] = list(DEFAULT_SETTINGS["packages"])
    if not isinstance(merged.get("payment_methods"), list):
        merged["payment_methods"] = list(DEFAULT_SETTINGS["payment_methods"])
    # Keep each payment method independently configurable and safely disabled when empty.
    method_specs = (
        ("bkash", "bKash"),
        ("nagad", "Nagad"),
        ("rocket", "Rocket"),
    )
    merged["payment_methods"] = []
    for method_key, method_name in method_specs:
        number = str(merged.get(f"{method_key}_number", "") or "").strip()
        enabled = bool(merged.get(f"{method_key}_enabled", method_key != "rocket")) and bool(number)
        action = str(merged.get(f"{method_key}_action", "send_money") or "send_money").strip().lower()
        if action not in {"payment", "send_money", "cash_out"}:
            action = "send_money"
        merged["payment_methods"].append({
            "name": method_name, "key": method_key, "account": number,
            "enabled": enabled, "action": action,
        })
    return merged

def save_settings(data: dict):
    db.collection(COL_SETTINGS).document("app").set(data, merge=True)


def ensure_settings():
    ref = db.collection(COL_SETTINGS).document("app")
    snap = ref.get()
    if not snap.exists:
        ref.set(DEFAULT_SETTINGS)
    else:
        get_settings()


def safe_username(user) -> str:
    return clean_text(getattr(user, "username", "") or "", 100)


def default_user_payload(tg_user, referrer_id: Optional[int] = None, referral_eligible: bool = False):
    eligible_referrer = int(referrer_id) if referrer_id and referral_eligible and int(referrer_id) != tg_user.id else None
    return {
        "user_id": tg_user.id,
        "telegram_id": tg_user.id,
        "chat_id": tg_user.id,
        "username": safe_username(tg_user),
        "first_name": clean_text(tg_user.first_name, 100),
        "last_name": clean_text(tg_user.last_name, 100),
        "language": "en",
        "balance": 0.0,
        "total_calls": 0,
        "successful_calls": 0,
        "failed_calls": 0,
        "total_seconds": 0,
        "referrals": 0,
        "referred_by": eligible_referrer,
        "pending_referrer_id": eligible_referrer,
        "referral_eligible": bool(eligible_referrer),
        "referral_awarded": False,
        "is_blocked": False,
        "created_at": now(),
        "updated_at": now(),
        "last_call_at": None,
        "call_day": None,
        "calls_today": 0,
        "last_daily_bonus": None,
        "purchase_flow_times": [],
        "first_start_credit_claimed": False,
        "welcome_credit_pending": True,
    }

def ensure_user(tg_user, referrer_id: Optional[int] = None, referral_eligible: bool = False):
    with _TRANSACTION_LOCK:
        ref = user_ref(tg_user.id)
        snap = ref.get()
        if snap.exists:
            old_data = snap.to_dict() or {}
            ref.set({
                "user_id": tg_user.id,
                "telegram_id": tg_user.id,
                "chat_id": tg_user.id,
                "username": safe_username(tg_user),
                "first_name": clean_text(tg_user.first_name, 100),
                "last_name": clean_text(tg_user.last_name, 100),
                "updated_at": now(),
            }, merge=True)
            if old_data.get("welcome_credit_pending"):
                settings = get_settings()
                signup_bonus = credits_float(settings.get("welcome_bonus", 1))
                if signup_bonus > 0:
                    try:
                        add_credits(tg_user.id, signup_bonus, "welcome_bonus", f"signup:{tg_user.id}")
                    except ValueError as exc:
                        message = str(exc).lower()
                        if not any(token in message for token in ("already recorded", "record already exists", "already exists", "already applied", "duplicate", "duplicate credit operation")):
                            raise
                ref.update({"first_start_credit_claimed": True, "welcome_credit_pending": False})
            return ref.get().to_dict() or {}

        payload = default_user_payload(tg_user, referrer_id, referral_eligible)
        ref.set(payload)
        settings = get_settings()
        signup_bonus = credits_float(settings.get("welcome_bonus", 1))
        if signup_bonus > 0:
            try:
                add_credits(tg_user.id, signup_bonus, "welcome_bonus", f"signup:{tg_user.id}")
            except ValueError as exc:
                message = str(exc).lower()
                if not any(token in message for token in ("already recorded", "record already exists", "already exists", "already applied", "duplicate", "duplicate credit operation")):
                    raise
            ref.update({"first_start_credit_claimed": True, "welcome_credit_pending": False})
        else:
            ref.update({"welcome_credit_pending": False, "first_start_credit_claimed": True})
        return ref.get().to_dict() or payload

def audit(action: str, actor_id: int, data: Optional[dict] = None):
    db.collection(COL_AUDIT).add({
        "action": clean_text(action, 200),
        "actor_id": actor_id,
        "data": data or {},
        "created_at": now(),
    })


def add_credits(user_id: int, amount: float, reason: str, reference: str = "") -> float:
    user_id = int(user_id)
    amount = credits_float(amount)
    if amount <= 0:
        raise ValueError("Amount must be greater than zero.")
    ref = user_ref(user_id)
    ledger_ref = ledger_ref_for(user_id, reason, reference)
    with _TRANSACTION_LOCK:
        if ledger_ref.get().exists:
            raise ValueError("Duplicate credit operation blocked; this request was already applied.")
        transaction = db.transaction()
        @firestore.transactional
        def apply(transaction):
            snap = ref.get(transaction=transaction)
            if not snap.exists:
                raise ValueError("User account not found. The user must start the bot first.")
            data = snap.to_dict() or {}
            before = credits_float(data.get("balance", 0))
            after = credits_float(before + amount)
            transaction.update(ref, {"balance": after, "updated_at": now()})
            transaction.create(ledger_ref, {
                "user_id": user_id, "type": reason, "amount": amount,
                "before": before, "after": after,
                "reference": clean_text(reference, 250), "created_at": now(),
            })
            return after
        return apply(transaction)

def deduct_credits(user_id: int, amount: float, reason: str, reference: str = "") -> float:
    user_id = int(user_id)
    amount = credits_float(amount)
    if amount <= 0:
        raise ValueError("Amount must be greater than zero.")
    ref = user_ref(user_id)
    ledger_ref = ledger_ref_for(user_id, reason, reference)
    with _TRANSACTION_LOCK:
        if ledger_ref.get().exists:
            raise ValueError("Duplicate deduction operation blocked; this request was already applied.")
        transaction = db.transaction()
        @firestore.transactional
        def apply(transaction):
            snap = ref.get(transaction=transaction)
            if not snap.exists:
                raise ValueError("User account not found. The user must start the bot first.")
            data = snap.to_dict() or {}
            before = credits_float(data.get("balance", 0))
            if before < amount:
                raise ValueError("Insufficient credits.")
            after = credits_float(before - amount)
            updates = {"balance": after, "updated_at": now()}
            if after <= 0:
                updates.update({"subscription_tier": "INACTIVE", "subscription_exhausted": True, "subscription_ended_at": now()})
            transaction.update(ref, updates)
            transaction.create(ledger_ref, {
                "user_id": user_id, "type": reason, "amount": -amount,
                "before": before, "after": after,
                "reference": clean_text(reference, 250), "created_at": now(),
            })
            return after
        return apply(transaction)

def refund_credits(user_id: int, amount: float, reason: str, reference: str = "") -> float:
    after = add_credits(user_id, amount, reason, reference)
    user = get_user(user_id)
    paid_tier = clean_text(user.get("subscription_paid_tier", "INACTIVE"), 30).upper()
    if after > 0 and paid_tier not in {"", "INACTIVE"} and reason.startswith("call_refund"):
        user_ref(user_id).update({
            "subscription_tier": paid_tier,
            "subscription_exhausted": False,
            "updated_at": now(),
        })
    return after


def is_admin(user_id: int) -> bool:
    return _safe_int(user_id) == ADMIN_ID


COL_CHANNEL_MEMBERS = "channel_members"


def membership_history(user_id: int) -> dict:
    snap = db.collection(COL_CHANNEL_MEMBERS).document(str(user_id)).get()
    return snap.to_dict() if snap.exists else {}


def member_status_is_joined(member) -> bool:
    status = getattr(member, "status", "")
    if status in {"member", "administrator", "creator"}:
        return True
    if status == "restricted" and bool(getattr(member, "is_member", False)):
        return True
    return False


async def refresh_channel_membership(bot, user_id: int) -> Optional[bool]:
    """Force a Telegram membership lookup and persist the result for the Dhaka day."""
    uid = _safe_int(user_id)
    if uid is None or uid == 0:
        return None
    try:
        settings = await asyncio.to_thread(get_settings)
        channel = clean_text(settings.get("required_channel") or REQUIRED_CHANNEL_USERNAME, 100)
        member = await bot.get_chat_member(chat_id=channel, user_id=uid)
        joined = member_status_is_joined(member)
        ref = db.collection(COL_CHANNEL_MEMBERS).document(str(uid))
        old = await asyncio.to_thread(lambda: ref.get().to_dict() or {})
        await asyncio.to_thread(ref.set, {
            "user_id": uid,
            "ever_member": bool(old.get("ever_member", False) or joined),
            "is_member": joined,
            "checked_day": local_day_key(),
            "last_checked_at": now(),
            "last_status": clean_text(getattr(member, "status", "unknown"), 50),
            "last_error": None,
        }, merge=True)
        return joined
    except Exception as exc:
        try:
            ref = db.collection(COL_CHANNEL_MEMBERS).document(str(uid))
            await asyncio.to_thread(ref.set, {
                "user_id": uid,
                "last_check_attempt_at": now(),
                "last_error": clean_text(exc, 300),
            }, merge=True)
        except Exception:
            pass
        return None


async def channel_membership_status(bot, user_id: int, force: bool = False) -> Optional[bool]:
    """Use cached membership for the current local day; refresh on day change/manual check."""
    uid = _safe_int(user_id)
    if uid is None or uid == 0:
        return None
    history = await asyncio.to_thread(membership_history, uid)
    today = local_day_key()
    if not force and history.get("checked_day") == today and isinstance(history.get("is_member"), bool):
        return bool(history.get("is_member"))
    last_attempt = parse_datetime(history.get("last_check_attempt_at"))
    if not force and last_attempt is not None and now() - last_attempt < timedelta(minutes=5):
        return None
    return await refresh_channel_membership(bot, uid)


async def refresh_all_channel_memberships(bot):
    """Daily background sweep; runs off the user request path to keep the bot responsive."""
    try:
        users = await asyncio.to_thread(lambda: list(db.collection(COL_USERS).stream()))
    except Exception:
        return
    seen = set()
    for snapshot in users:
        uid = telegram_id_for_record(snapshot)
        if uid is None or uid == 0 or uid in seen:
            continue
        seen.add(uid)
        try:
            await refresh_channel_membership(bot, uid)
        except Exception:
            pass
        await asyncio.sleep(0.12)


async def channel_membership_midnight_worker(bot):
    """Refresh known channel memberships every 12 hours without blocking updates."""
    while True:
        await asyncio.sleep(12 * 60 * 60)
        try:
            await refresh_all_channel_memberships(bot)
        except asyncio.CancelledError:
            raise
        except Exception:
            logger.exception("Scheduled channel membership refresh failed")


def membership_keyboard():
    channel = clean_text(get_settings().get("required_channel") or REQUIRED_CHANNEL_USERNAME, 100)
    channel_url = "https://t.me/" + channel.lstrip("@").strip("/")
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📢 নির্ধারিত চ্যানেলে যোগ দিন", url=channel_url)],
        [InlineKeyboardButton("✅ যোগ দিয়েছি — যাচাই করুন", callback_data="membership:check")],
    ])


async def show_join_gate(target, context, verification_error: bool = False):
    text = (
        "🔒 *চ্যানেলে যোগ দেওয়া বাধ্যতামূলক*\n\n"
        f"প্রথমে {escape_markdown(clean_text(get_settings().get('required_channel') or REQUIRED_CHANNEL_USERNAME, 100), version=1)} চ্যানেলে যোগ দিন। যোগদান যাচাই না হওয়া পর্যন্ত বটের সুবিধাগুলো ব্যবহার করা যাবে না।\n\n"
        "যোগ দেওয়ার পর *যোগ দিয়েছি — যাচাই করুন* বাটনে চাপ দিন।"
    )
    if verification_error:
        text += "\n\n⚠️ যাচাই করা যায়নি। বটকে চ্যানেলে অ্যাডমিন করুন এবং আবার চেষ্টা করুন।"
    markup = membership_keyboard()
    if hasattr(target, "edit_message_text"):
        await edit_or_send(target, text, markup)
    elif hasattr(target, "reply_text"):
        await target.reply_text(text, parse_mode="Markdown", reply_markup=markup)


async def complete_pending_referral(user_id: int):
    referrer_id = None
    bonus = 0.0
    with _TRANSACTION_LOCK:
        user = get_user(user_id)
        if not user or not user.get("referral_eligible") or user.get("referral_awarded"):
            return False
        referrer_id = _safe_int(user.get("pending_referrer_id") or user.get("referred_by"))
        if not referrer_id or referrer_id == _safe_int(user_id):
            return False
        referrer_ref = user_ref(referrer_id)
        if not referrer_ref.get().exists:
            return False
        award_ref = db.collection("referral_awards").document(str(user_id))
        if award_ref.get().exists:
            user_ref(user_id).update({"referral_awarded": True, "referral_eligible": False})
            return False
        settings = get_settings()
        bonus = credits_float(settings.get("referral_bonus", 1))
        if bonus <= 0:
            return False
        try:
            add_credits(referrer_id, bonus, "referral_bonus", f"new_user:{_safe_int(user_id)}")
        except ValueError as exc:
            message = str(exc).lower()
            if not any(token in message for token in ("already recorded", "record already exists", "already exists", "already applied", "duplicate", "duplicate credit operation")):
                raise
        current = referrer_ref.get().to_dict() or {}
        new_referrals = (_safe_int(current.get("referrals", 0)) or 0) + 1
        new_user_ref = user_ref(user_id)
        # One RTDB root update makes the referral count + award marker + user flag consistent.
        firebase_db.reference("/").update(_db_json({
            f"{referrer_ref.path}/referrals": new_referrals,
            f"{referrer_ref.path}/updated_at": now(),
            f"{new_user_ref.path}/referral_awarded": True,
            f"{new_user_ref.path}/referral_eligible": False,
            f"{new_user_ref.path}/referral_completed_at": now(),
            f"{award_ref.path}": {"user_id": _safe_int(user_id), "referrer_id": referrer_id, "bonus": bonus, "created_at": now()},
        }))
    try:
        if telegram_app:
            await telegram_app.bot.send_message(
                chat_id=referrer_id,
                text=f"🎉 রেফারেল বোনাস: +{bonus:g} ক্রেডিট! আপনার আমন্ত্রণে নতুন ব্যবহারকারী চ্যানেলে যোগ দিয়েছেন। আরও বন্ধু আমন্ত্রণ করুন।",
            )
    except Exception:
        pass
    return True

async def track_channel_membership(update: Update, context: ContextTypes.DEFAULT_TYPE):
    member_update = update.chat_member
    if not member_update:
        return
    chat = member_update.chat
    configured = clean_text(get_settings().get("required_channel") or REQUIRED_CHANNEL_USERNAME, 100).lstrip("@").lower()
    chat_username = (getattr(chat, "username", "") or "").lower()
    if chat_username != configured:
        return
    member = member_update.new_chat_member
    tg_user = member.user
    joined = member_status_is_joined(member)
    ref = db.collection(COL_CHANNEL_MEMBERS).document(str(tg_user.id))
    old = ref.get().to_dict() or {}
    ref.set({
        "user_id": tg_user.id,
        "ever_member": bool(old.get("ever_member", False) or joined),
        "is_member": joined,
        "checked_day": local_day_key(),
        "last_checked_at": now(),
        "last_status": clean_text(getattr(member, "status", "unknown"), 50),
        "last_change_at": now(),
        "last_error": None,
    }, merge=True)


def user_blocked(user_id: int) -> bool:
    snap = user_ref(user_id).get()
    return bool((snap.to_dict() or {}).get("is_blocked", False))


def get_user(user_id: int) -> dict:
    snap = user_ref(user_id).get()
    return snap.to_dict() if snap.exists else {}


def format_balance(value: Any) -> str:
    return f"{credits_float(value):.2f}"


def subscription_tier_for_price(price: Any) -> str:
    """Return the plan unlocked by a confirmed, admin-approved package payment."""
    try:
        price_value = float(price)
    except (TypeError, ValueError):
        price_value = 0.0
    if price_value >= 380:
        return "LEGEND"
    if price_value >= 240:
        return "ELITE"
    if price_value >= 180:
        return "VIP"
    if price_value >= 100:
        return "MAX"
    if price_value >= 50:
        return "PRO"
    return "ACTIVE" if price_value > 0 else "INACTIVE"


def subscription_for_profile(user_data: dict) -> str:
    balance = credits_float(user_data.get("balance", 0))
    tier = clean_text(user_data.get("subscription_tier", "INACTIVE"), 30).upper() or "INACTIVE"
    if balance <= 0 or bool(user_data.get("subscription_exhausted", False)):
        return "INACTIVE"
    return tier if tier in {"ACTIVE", "PRO", "MAX", "VIP", "ELITE", "LEGEND"} else "INACTIVE"


def subscription_badge(tier: str) -> str:
    badges = {
        "INACTIVE": "⚪ INACTIVE",
        "ACTIVE": "🟢 ACTIVE",
        "PRO": "💎 PRO",
        "MAX": "🔷 MAX",
        "VIP": "🟣 VIP",
        "ELITE": "🟠 ELITE",
        "LEGEND": "🌟 LEGEND",
    }
    return badges.get(str(tier or "INACTIVE").upper(), "⚪ INACTIVE")


def profile_message(user_id: int, user_data: dict) -> str:
    name = html.escape(clean_text((str(user_data.get("first_name", "")) + " " + str(user_data.get("last_name", ""))).strip(), 100) or "ব্যবহারকারী")
    username = html.escape(clean_text(user_data.get("username") or "নেই", 100))
    balance = credits_float(user_data.get("balance", 0))
    tier = subscription_for_profile(user_data)
    joined_value = user_data.get("created_at") or user_data.get("joined_at") or user_data.get("first_seen_at")
    joined_dt = parse_datetime(joined_value)
    joined_text = joined_dt.astimezone(ZoneInfo("Asia/Dhaka")).strftime("%d %b %Y, %I:%M %p") if joined_dt else "Not available"
    tier_lines = {
                "INACTIVE": "Purchase a credit package to activate your membership.",
        "ACTIVE": "Your account is active.",
        "PRO": "PRO membership active — enjoy premium benefits.",
        "MAX": "MAX membership active — your premium benefits are enabled.",
        "VIP": "VIP membership active — thank you for using our service.",
        "ELITE": "ELITE membership active — special benefits have been unlocked.",
        "LEGEND": "LEGEND membership active — maximum package is active.",

    }
    return (
        "👤 <b>আমার প্রোফাইল</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"👑 <b>সদস্য:</b> {name}\n"
        f"🪪 <b>টেলিগ্রাম আইডি:</b> <code>{user_id}</code>\n"
        f"🔗 <b>ইউজারনেম:</b> @{username}\n"
        f"📅 <b>Joined:</b> {html.escape(joined_text)}\n"
        f"💳 <b>ক্রেডিট ব্যালেন্স: {balance:.2f}</b>\n\n"
        f"🏅 <b>Membership:</b> {html.escape(subscription_badge(tier))}\n"
        f"{html.escape(tier_lines.get(tier, tier_lines['INACTIVE']))}\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"📞 <b>মোট কল:</b> {_safe_int(user_data.get('total_calls', 0)) or 0}\n"
        f"✅ <b>সফল কল:</b> {_safe_int(user_data.get('successful_calls', 0)) or 0}\n"
        f"❌ <b>ব্যর্থ কল:</b> {_safe_int(user_data.get('failed_calls', 0)) or 0}\n"
        f"👥 <b>রেফারেল:</b> {_safe_int(user_data.get('referrals', 0)) or 0}\n"
        f"💠 <b>সর্বোচ্চ কেনাকাটার স্তর:</b> {html.escape(clean_text(user_data.get('subscription_paid_tier', 'NONE'), 30).upper())}\n"
        "━━━━━━━━━━━━━━━━━━"
    )


def referral_keyboard(referral_link: str):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📋 Copy Referral Link", copy_text=CopyTextButton(text=referral_link), style="success")],
    ])


def main_keyboard(user_id: int):
    """Single bottom dashboard keyboard; never attach a second inline dashboard."""
    rows = [
        [KeyboardButton("📞 Send Call"), KeyboardButton("👤 My Profile")],
        [KeyboardButton("👥 Refer"), KeyboardButton("📊 LP Statistics")],
        [KeyboardButton("💰 Buy Credits"), KeyboardButton("🎁 Redeem")],
        [KeyboardButton("🕘 Call History"), KeyboardButton("☎️ Support")],
    ]
    settings = get_settings()
    if settings.get("daily_bonus_enabled", False):
        rows.append([KeyboardButton("🎁 Daily Bonus")])
    if is_admin(user_id):
        rows.append([KeyboardButton("🛠 Admin Panel")])
    # No input_field_placeholder: do not force the unwanted “Choose an option” text.
    return ReplyKeyboardMarkup(rows, resize_keyboard=True, one_time_keyboard=False)

def back_button():
    # Keep navigation in the standard Telegram chat keyboard; do not add a fake exit/back button.
    return None


def interaction_message(update: Update):
    """Return a message usable from both callback-button and typed-text flows."""
    if update.callback_query and update.callback_query.message:
        return update.callback_query.message
    return update.effective_message


def create_audio_proxy_url(user_id: int, file_id: str, extension: str,
                           content_type: str, file_size: int = 0,
                           lifetime_minutes: int = 45) -> str:
    extension = (extension or "ogg").lower()
    if extension not in {"mp3", "wav", "ogg"}:
        raise ValueError("সমর্থিত অডিও ফরম্যাট: MP3, WAV, OGG")
    if not PUBLIC_BASE_URL or not re.match(r"^https://", PUBLIC_BASE_URL, re.I):
        raise ValueError("Render-এর HTTPS PUBLIC_BASE_URL সেট করা নেই")
    token = secrets.token_urlsafe(32)
    db.collection(COL_PROVIDER_AUDIO).document(token).set({
        "token": token,
        "file_id": clean_text(file_id, 500),
        "user_id": int(user_id),
        "extension": extension,
        "content_type": clean_text(content_type, 100),
        "file_size": _safe_int(file_size) or 0,
        "created_at": now(),
        "expires_at": now() + timedelta(minutes=max(5, min(60, int(lifetime_minutes)))),
        "fetches": 0,
    })
    return f"{PUBLIC_BASE_URL}/provider-audio/{token}/audio.{extension}"


def voice_templates_for_user(user_id: int) -> list:
    try:
        records = list(db.collection(COL_VOICE_TEMPLATES).stream())
    except Exception:
        return []
    result = []
    for record in records:
        item = record.to_dict() or {}
        scope = str(item.get("scope", "personal")).lower()
        owner_id = _safe_int(item.get("owner_id"))
        if not item.get("active", True):
            continue
        if scope == "global" or (scope == "personal" and owner_id == int(user_id)):
            item["_record_id"] = record.id
            result.append(item)
    result.sort(key=lambda item: (0 if item.get("scope") == "global" else 1, str(item.get("title", "")).lower()))
    return result


def voice_templates_keyboard(user_id: int, admin_view: bool = False):
    templates = voice_templates_for_user(user_id)
    rows = []
    for item in templates[:25]:
        title = clean_text(item.get("title", "ভয়েস টেমপ্লেট"), 42)
        scope_label = "🌐" if item.get("scope") == "global" else "👤"
        record_id = clean_text(item.get("_record_id", ""), 80)
        if admin_view:
            if item.get("scope") == "global":
                rows.append([InlineKeyboardButton(f"🗑 {title[:30]}", callback_data=f"admin:template_delete:{record_id}", style="danger")])
        else:
            rows.append([InlineKeyboardButton(f"{scope_label} {title}", callback_data=f"template:use:{record_id}", style="success" if item.get("scope") == "global" else "primary")])
    if admin_view:
        rows.insert(0, [InlineKeyboardButton("➕ বৈশ্বিক টেমপ্লেট তৈরি", callback_data="admin:template_create_global", style="success")])
        rows.append([InlineKeyboardButton("⬅️ Admin Panel", callback_data="admin:menu", style="primary")])
    else:
        rows.append([InlineKeyboardButton("➕ আমার ব্যক্তিগত টেমপ্লেট তৈরি", callback_data="template:create_personal", style="success")])
        rows.append([InlineKeyboardButton("❌ বাতিল", callback_data="call:cancel", style="danger")])
    return templates, InlineKeyboardMarkup(rows)


async def show_voice_templates(target, context: ContextTypes.DEFAULT_TYPE, admin_view: bool = False):
    user_id = target.from_user.id if hasattr(target, "from_user") else target.effective_user.id
    templates, markup = await asyncio.to_thread(voice_templates_keyboard, user_id, admin_view)
    if not templates:
        text = "🎙️ এখনো কোনো ভয়েস টেমপ্লেট নেই। নিচের বাটন দিয়ে নতুন টেমপ্লেট তৈরি করুন।"
    else:
        lines = ["🎙️ ভয়েস টেমপ্লেট", "━━━━━━━━━━━━━━━━━━"]
        for item in templates[:25]:
            label = "সবার জন্য" if item.get("scope") == "global" else "শুধু আপনার জন্য"
            lines.append(f"• {clean_text(item.get('title', 'ভয়েস টেমপ্লেট'), 60)} — {label}")
        text = "\n".join(lines)
    if hasattr(target, "edit_message_text"):
        await edit_or_send(target, text, markup, parse_mode=None)
    elif hasattr(target, "effective_message"):
        await target.effective_message.reply_text(text, reply_markup=markup)
    else:
        await target.reply_text(text, reply_markup=markup)


async def save_voice_template_title(update: Update, context: ContextTypes.DEFAULT_TYPE, title: str):
    state = context.user_data.get("state")
    pending = context.user_data.get("pending_voice_template") or {}
    if state not in {"voice_template_title_global", "voice_template_title_personal"} or not pending.get("file_id"):
        return False
    title = clean_text(title, 60)
    if len(title) < 2:
        await update.effective_message.reply_text("টেমপ্লেটের নাম কমপক্ষে ২ অক্ষরের দিন।")
        return True
    global_template = state == "voice_template_title_global"
    if global_template and not is_admin(update.effective_user.id):
        await update.effective_message.reply_text("এই টেমপ্লেট তৈরি করার অনুমতি নেই।")
        context.user_data.clear()
        return True
    reference = db.collection(COL_VOICE_TEMPLATES).document()
    reference.set({
        "title": title,
        "scope": "global" if global_template else "personal",
        "owner_id": 0 if global_template else update.effective_user.id,
        "created_by": update.effective_user.id,
        "file_id": clean_text(pending.get("file_id"), 500),
        "extension": clean_text(pending.get("extension", "ogg"), 10),
        "content_type": clean_text(pending.get("content_type", "audio/ogg"), 100),
        "file_size": _safe_int(pending.get("file_size")) or 0,
        "active": True,
        "created_at": now(),
        "updated_at": now(),
    })
    audit("voice_template_created", update.effective_user.id, {"template_id": reference.id, "title": title, "scope": "global" if global_template else "personal"})
    context.user_data.pop("pending_voice_template", None)
    context.user_data["state"] = "call_mode" if context.user_data.get("call_phone") else None
    await update.effective_message.reply_text(
        f"✅ ভয়েস টেমপ্লেট তৈরি হয়েছে: {title}\n" + ("এটি সব ব্যবহারকারী ব্যবহার করতে পারবেন।" if global_template else "এটি শুধু আপনার অ্যাকাউন্টে দেখা যাবে।")
    )
    if global_template:
        await update.effective_message.reply_text("🛠 Admin Voice Templates", reply_markup=admin_keyboard_markup())
    else:
        templates, markup = await asyncio.to_thread(voice_templates_keyboard, update.effective_user.id, False)
        await update.effective_message.reply_text("আপনার টেমপ্লেট থেকে একটি নির্বাচন করুন:", reply_markup=markup)
    return True


async def send_home(update: Update, context: ContextTypes.DEFAULT_TYPE):
    tg_user = update.effective_user
    message = update.effective_message
    if not tg_user or not message:
        return
    args = context.args if update.message and update.message.text else []
    referrer_id = None
    if args:
        match = re.fullmatch(r"ref_(\d+)", args[0].strip())
        if match:
            referrer_id = int(match.group(1))

    existing = get_user(tg_user.id)
    is_new_user = not bool(existing)
    prior_membership = membership_history(tg_user.id)
    status = await channel_membership_status(context.bot, tg_user.id)
    if status is None:
        await show_join_gate(message, context, verification_error=True)
        return

    if is_new_user and referrer_id and referrer_id != tg_user.id and status is False:
        # Keep the referral through the join gate. Telegram member events can arrive
        # before the user's verification button, so store the eligibility decision now.
        context.user_data["pending_referrer_id"] = referrer_id
        context.user_data["pending_referral_eligible"] = not bool(prior_membership.get("ever_member", False))

    if not status:
        # Do not create a new user record until the required channel join is verified.
        # This lets the successful verification path send the actual welcome message.
        await show_join_gate(message, context)
        return

    if not existing:
        history = membership_history(tg_user.id)
        # A direct /start from an already-joined member is not a new channel join.
        referral_eligible = bool(
            referrer_id and status is False and not prior_membership.get("ever_member", False)
            and referrer_id != tg_user.id
        )
        ensure_user(tg_user, referrer_id=referrer_id, referral_eligible=referral_eligible)
    else:
        ensure_user(tg_user)

    data = get_user(tg_user.id)
    if data.get("is_blocked") and not is_admin(tg_user.id):
        await message.reply_text("⛔ আপনার অ্যাকাউন্ট বন্ধ করা হয়েছে। সহায়তার জন্য Support-এ যোগাযোগ করুন।")
        return
    await complete_pending_referral(tg_user.id)
    settings = get_settings()
    notice = settings.get("admin_notice", "")
    text = (
        f"✨ *{escape_markdown(clean_text(settings.get('brand_name', 'Custom Call'), 60), version=1)}*\n\n"
        f"💳 Balance: *{format_balance(data.get('balance', 0))} credits*\n"
        f"📞 Total Calls: *{_safe_int(data.get('total_calls', 0)) or 0}*\n"
        f"👥 Referrals: *{_safe_int(data.get('referrals', 0)) or 0}*\n\n"
        "নিচের মেনু থেকে একটি সুবিধা নির্বাচন করুন।"
    )
    if settings.get("maintenance") and not is_admin(tg_user.id):
        text += "\n\n🛠 সেবা রক্ষণাবেক্ষণে আছে।"
    if notice:
        text += f"\n\nℹ️ {escape_markdown(clean_text(notice, 500), version=1)}"
    if is_new_user:
        welcome = (
            f"🎉 স্বাগতম, {clean_text(tg_user.first_name or 'বন্ধু', 80)}!\n\n"
            "Custom Call Bot-এ আপনাকে স্বাগতম। আপনার অ্যাকাউন্ট তৈরি হয়েছে এবং স্বাগতম বোনাসের নিয়ম অনুযায়ী ক্রেডিট যোগ করা হয়েছে।\n\n"
            "নিচের মেনু থেকে একটি অপশন বেছে নিন।"
        )
        text = welcome + "\n\n" + text
    await message.reply_text(text, parse_mode="Markdown", reply_markup=main_keyboard(tg_user.id))

def strip_markdown_for_fallback(text: str) -> str:
    value = str(text or "")
    value = re.sub(r"\\([_*`\[\]()>#+=|{}.!-])", r"\1", value)
    value = value.replace("`", "").replace("*", "").replace("_", "")
    return value


async def edit_or_send(query, text: str, markup=None, parse_mode="Markdown"):
    # Reply keyboards must be sent on a message, while inline buttons belong to a message.
    # Never auto-attach the dashboard to submenu messages: the dashboard exists only below.
    if isinstance(markup, ReplyKeyboardMarkup):
        try:
            if getattr(query, "message", None):
                await query.message.edit_reply_markup(reply_markup=None)
        except Exception:
            pass
        try:
            await query.message.reply_text(text, parse_mode=parse_mode, reply_markup=markup)
            return
        except Exception:
            await query.message.reply_text(strip_markdown_for_fallback(text), reply_markup=markup)
            return
    if markup is None:
        try:
            await query.edit_message_reply_markup(reply_markup=None)
        except Exception:
            pass
    try:
        await query.edit_message_text(text, parse_mode=parse_mode, reply_markup=markup)
        return
    except Exception:
        pass
    try:
        await query.message.reply_text(text, parse_mode=parse_mode, reply_markup=markup)
        return
    except Exception:
        await query.message.reply_text(strip_markdown_for_fallback(text), reply_markup=markup)


async def callback_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if not query:
        return
    data = query.data or ""
    if not data.startswith("pay:"):
        await query.answer()
    user_id = query.from_user.id

    if data == "membership:check":
        status = await channel_membership_status(context.bot, user_id, force=True)
        if status is True:
            is_new_user = not bool(get_user(user_id))
            if is_new_user:
                pending_referrer = _safe_int(context.user_data.get("pending_referrer_id"))
                pending_eligible = bool(context.user_data.get("pending_referral_eligible"))
                ensure_user(
                    query.from_user,
                    referrer_id=pending_referrer if pending_eligible else None,
                    referral_eligible=pending_eligible and bool(pending_referrer),
                )
            await complete_pending_referral(user_id)
            context.user_data.pop("pending_referrer_id", None)
            context.user_data.pop("pending_referral_eligible", None)
            if is_new_user:
                new_user_data = get_user(user_id)
                welcome = (
                    f"🎉 স্বাগতম, {clean_text(query.from_user.first_name or 'বন্ধু', 80)}!\n\n"
                    "Custom Call Bot-এ আপনাকে স্বাগতম। আপনার অ্যাকাউন্ট তৈরি হয়েছে। \n\n"
                    f"💳 আপনার ব্যালেন্স: {format_balance(new_user_data.get('balance', 0))} ক্রেডিট\n"
                    "নিচের মেনু থেকে একটি সুবিধা নির্বাচন করুন।"
                )
                await edit_or_send(query, welcome, main_keyboard(user_id), parse_mode=None)
            else:
                await edit_or_send(query, "✅ চ্যানেল যাচাই সম্পন্ন। বটের সুবিধাগুলো এখন ব্যবহার করতে পারবেন।", main_keyboard(user_id), parse_mode=None)
        elif status is False:
            await show_join_gate(query, context)
        else:
            await show_join_gate(query, context, verification_error=True)
        return

    status = await channel_membership_status(context.bot, user_id)
    if status is not True:
        if data.startswith("pay:"):
            try:
                await query.answer("Required channel join/verification is required.", show_alert=True)
            except Exception:
                pass
        await show_join_gate(query, context, verification_error=status is None)
        return

    ensure_user(query.from_user)
    if user_blocked(user_id) and not is_admin(user_id):
        await edit_or_send(query, "⛔ আপনার অ্যাকাউন্ট বন্ধ করা হয়েছে। সহায়তার জন্য Support-এ যোগাযোগ করুন।", None, parse_mode=None)
        return

    if data in {"menu:home", "menu:back"}:
        context.user_data.clear()
        u = get_user(user_id)
        await edit_or_send(query, f"🏠 *ড্যাশবোর্ড*\n\nব্যালেন্স: *{format_balance(u.get('balance', 0))} ক্রেডিট*\nনিচের মেনু থেকে একটি সুবিধা নির্বাচন করুন।", main_keyboard(user_id))
        return

    if data == "menu:profile":
        u = get_user(user_id)
        text = profile_message(user_id, u)
        await edit_or_send(query, text, back_button(), parse_mode="HTML")
        return

    if data == "menu:refer":
        me = await context.bot.get_me()
        referral_link = f"https://t.me/{me.username}?start=ref_{user_id}"
        bonus = credits_float(get_settings().get("referral_bonus", 1))
        text = ("👥 *বন্ধুদের আমন্ত্রণ করুন*\n\n" f"রেফারেল বোনাস: *{bonus:g} ক্রেডিট*\n" f"লিংক শেয়ার করুন এবং *{bonus:g} ক্রেডিট জিতে নিন!*\n\n" f"আপনার লিংক:\n`{escape_markdown(referral_link, version=1)}`\n\n" "বোনাস শুধু যোগ্য নতুন ব্যবহারকারীর জন্য।")
        await edit_or_send(query, text, referral_keyboard(referral_link))
        return

    if data == "menu:stats":
        settings = get_settings()
        totals = await local_stats()
        daily_limit = _safe_int(settings.get("daily_call_limit", 20))
        lines = [
            "📊 *LP Statistics*", "",
            f"Users: *{totals['users']}*",
            f"Total Calls: *{totals['calls']}*",
                "", "🏆 *Top Credit Holders*",
        ]
        top_users = [item for item in totals.get("top_users", []) if credits_float(item.get("balance", 0)) > 0][:10]
        if top_users:
            for rank, item in enumerate(top_users, 1):
                name = escape_markdown(item.get("name") or "User", version=1)
                lines.append(f"{rank}. {name} — *{format_balance(item.get('balance', 0))} credits*")
        else:
            lines.append("No credit holders yet.")
        await edit_or_send(query, "\n".join(lines), back_button())
        return

    if data == "menu:history":
        docs = list(db.collection(COL_CALLS).where("user_id", "==", user_id).limit(50).stream())
        items = sorted(docs, key=lambda snap: str((snap.to_dict() or {}).get("created_at") or ""), reverse=True)[:5]
        if not items:
            await edit_or_send(query, "📞 *কলের ইতিহাস*\n\nএখনো কোনো কলের ইতিহাস নেই।", back_button())
            return
        lines = ["📞 *Recent Calls*\n"]
        for snap in items:
            c = snap.to_dict() or {}
            status = str(c.get("status", "unknown")).upper()
            number = clean_text(c.get("number", ""), 30) or "অজানা"
            when = iso(c.get("created_at")) or "-"
            safe_status = escape_markdown(status, version=1)
            lines.append(f"• `{escape_markdown(number, version=1)}` — *{safe_status}* — {when[:16]}")
            if c.get("recording_url"):
                lines.append(f"  Recording: `{escape_markdown(clean_text(c.get('recording_url'), 300), version=1)}`")
        await edit_or_send(query, "\n".join(lines), back_button())
        return

    if data == "menu:support":
        support_url = clean_text(get_settings().get("support_contact_url") or SUPPORT_CONTACT_URL, 300)
        support_text = clean_text(get_settings().get("support_text", "সহায়তার জন্য নিচের বাটনে চাপ দিন।"), 1800)
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton("✉️ Message Support Admin", url=support_url, style="primary")],
        ])
        await edit_or_send(query, f"☎️ *Support*\n\n{support_text}\n\nAdmin ID: `{ADMIN_ID}`", markup)
        return
    if data == "menu:buy":
        await show_buy(query, context)
        return
    if data.startswith("buy:"):
        await select_package(query, context, data.split(":", 1)[1])
        return
    if data.startswith("paymethod:"):
        await select_payment_method(query, context, data.split(":", 1)[1])
        return
    if data == "menu:redeem":
        context.user_data.clear()
        context.user_data["state"] = "redeem_code"
        await edit_or_send(query, "🎁 *রিডিম কোড*\n\nআপনার রিডিম কোডটি পাঠান।", back_button())
        return
    if data == "menu:call":
        call_settings = get_settings()
        if call_settings.get("maintenance", False):
            await edit_or_send(query, "🛠 কল সার্ভিস রক্ষণাবেক্ষণে আছে। আপাতত শুধু কল বন্ধ; অন্য সুবিধাগুলো চালু আছে।", back_button(), parse_mode=None)
            return
        u = get_user(user_id)
        cost = credits_float(call_settings.get("call_credit_cost", 1))
        if credits_float(u.get("balance", 0)) <= 0 or credits_float(u.get("balance", 0)) < cost:
            await edit_or_send(query, f"❌ কল দিতে কমপক্ষে *{cost:g} ক্রেডিট* প্রয়োজন। Buy Credits অথবা Redeem ব্যবহার করুন।", back_button())
            return
        context.user_data.clear()
        context.user_data["state"] = "call_phone"
        await edit_or_send(query, "📞 *কল করুন*\n\nযে নম্বরে কল দিতে চান সেটি পাঠান। উদাহরণ: `01700000000`", back_button())
        return
    if data.startswith("callmode:"):
        mode = data.split(":", 1)[1]
        context.user_data.pop("call_text", None)
        context.user_data.pop("call_audio_url", None)
        context.user_data.pop("call_template_id", None)
        context.user_data.pop("call_template_title", None)
        context.user_data["call_mode"] = mode
        if mode == "templates":
            await show_voice_templates(query, context, admin_view=False)
        elif mode == "text":
            context.user_data["state"] = "call_content_text"
            await edit_or_send(query, "📝 কলে যে কথা বলা হবে, সেই টেক্সট পাঠান।", back_button(), parse_mode=None)
        elif mode == "audio_url":
            context.user_data["state"] = "call_content_audio_url"
            await edit_or_send(query, "🔗 সরাসরি MP3/WAV/OGG অডিও লিংক পাঠান।", back_button(), parse_mode=None)
        else:
            context.user_data["state"] = "call_content_audio_upload"
            await edit_or_send(query, "🎧 MP3/WAV/OGG ফাইল অথবা ভয়েস মেসেজ পাঠান।", back_button(), parse_mode=None)
        return
    if data == "template:create_personal":
        context.user_data["state"] = "voice_template_upload_personal"
        await edit_or_send(query, "🎙️ আপনার ব্যক্তিগত টেমপ্লেট তৈরি করতে MP3/WAV/OGG ফাইল বা ভয়েস মেসেজ পাঠান। এটি শুধু আপনার জন্য থাকবে।", None, parse_mode=None)
        return
    if data.startswith("template:use:"):
        template_id = data.split(":", 2)[2]
        template_ref = db.collection(COL_VOICE_TEMPLATES).document(template_id)
        template_snap = await asyncio.to_thread(template_ref.get)
        template = template_snap.to_dict() if template_snap.exists else {}
        if not template or not template.get("active", True):
            await edit_or_send(query, "এই ভয়েস টেমপ্লেটটি পাওয়া যায়নি বা নিষ্ক্রিয়।", None, parse_mode=None)
            return
        scope = str(template.get("scope", "personal")).lower()
        if scope != "global" and _safe_int(template.get("owner_id")) != user_id:
            await edit_or_send(query, "এই টেমপ্লেটটি আপনার জন্য নয়।", None, parse_mode=None)
            return
        if not context.user_data.get("call_phone"):
            await edit_or_send(query, "প্রথমে Send Call চাপুন এবং ফোন নম্বর দিন।", main_keyboard(user_id), parse_mode=None)
            return
        try:
            ext = clean_text(template.get("extension", "ogg"), 10).lower()
            audio_url = await asyncio.to_thread(
                create_audio_proxy_url,
                user_id,
                template.get("file_id"),
                ext,
                template.get("content_type", "audio/ogg"),
                _safe_int(template.get("file_size")) or 0,
            )
        except Exception as exc:
            await edit_or_send(query, f"❌ টেমপ্লেট প্রস্তুত করা যায়নি: {clean_text(exc, 300)}", None, parse_mode=None)
            return
        context.user_data["call_audio_url"] = audio_url
        context.user_data["call_text"] = None
        context.user_data["call_template_id"] = template_id
        context.user_data["call_template_title"] = clean_text(template.get("title", "Voice Template"), 100)
        context.user_data["call_mode"] = "template"
        await edit_or_send(query, f"✅ টেমপ্লেট নির্বাচিত: {clean_text(template.get('title', 'Voice Template'), 80)}\nএখন কলের সময় নির্বাচন করুন।", None, parse_mode=None)
        await ask_call_time(update)
        return
    if data.startswith("calltime:"):
        if data == "calltime:custom":
            context.user_data["state"] = "call_custom_duration"
            await edit_or_send(query, "⏱️ কাস্টম সময় লিখুন (১০–৩০০ সেকেন্ড)। শুধু সংখ্যা লিখবেন, যেমন: 45", None, parse_mode=None)
            return
        try:
            seconds = int(data.split(":", 1)[1])
        except (TypeError, ValueError):
            await edit_or_send(query, "কলের সময় সঠিক নয়। আবার নির্বাচন করুন।", back_button(), parse_mode=None)
            return
        if seconds < 10 or seconds > 300:
            await edit_or_send(query, "কলের সময় ১০ থেকে ৩০০ সেকেন্ডের মধ্যে হতে হবে।", back_button(), parse_mode=None)
            return
        context.user_data["call_time"] = seconds
        await execute_pending_call(update, context)
        return
    if data == "call:cancel":
        context.user_data.clear()
        await edit_or_send(query, "অনুরোধ বাতিল করা হয়েছে।", main_keyboard(user_id))
        return
    if data == "daily:claim":
        await claim_daily(query)
        return
    if data == "admin:menu" and is_admin(user_id):
        await admin_menu(query)
        return
    if data.startswith("admin:") and is_admin(user_id):
        await admin_callback(update, context)
        return
    if data.startswith("pay:"):
        if not is_admin(user_id):
            await query.answer("Only the configured admin can approve payments.", show_alert=True)
            return
        await admin_payment_callback(update, context)
        return

async def show_buy(query, context):
    settings = get_settings()
    packages = settings.get("packages", [])
    rows = [[InlineKeyboardButton(clean_text(p.get("label", f"{p.get('credits')} Calls"), 60), callback_data=f"buy:{p.get('id')}", style="success" if i % 2 == 0 else "primary")] for i, p in enumerate(packages)]
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data="menu:home", style="primary")])
    package_lines = "\n".join(f"• {clean_text(pkg.get('label'), 100)}" for pkg in packages)
    enabled_names = [m["name"] for m in settings.get("payment_methods", []) if m.get("enabled")]
    methods_text = ", ".join(enabled_names) if enabled_names else "এখন কোনো পেমেন্ট মাধ্যম চালু নেই"
    text = (
        "💰 *Credit Purchase*\n━━━━━━━━━━━━━━━━━\n\n"
        "📦 *Available Packages:*\n\n" + package_lines +
        "\n━━━━━━━━━━━━━━━━━\n"
        f"💳 পেমেন্ট মাধ্যম: *{methods_text}*\n"
        "‌\n"
        "⚡ অ্যাডমিন অনুমোদন দিলে ক্রেডিট স্বয়ংক্রিয়ভাবে যোগ হবে।\n\n"
        "👇 নিচের প্যাকেজ নির্বাচন করুন।"
    )
    await edit_or_send(query, text, InlineKeyboardMarkup(rows))


async def record_purchase_attempt(user_id: int) -> tuple[bool, int]:
    settings = get_settings()
    limit = max(1, _safe_int(settings.get("purchase_limit_count", 3)) or 3)
    minutes = max(1, _safe_int(settings.get("purchase_limit_minutes", 10)) or 10)
    ref = user_ref(user_id)
    with _TRANSACTION_LOCK:
        data = ref.get().to_dict() or {}
        current_time = now()
        times = [parse_datetime(x) for x in (data.get("purchase_flow_times") or [])]
        times = [x for x in times if x is not None and current_time - x < timedelta(minutes=minutes)]
        if len(times) >= limit:
            oldest = min(times)
            wait_seconds = max(1, int((timedelta(minutes=minutes) - (current_time - oldest)).total_seconds()))
            return False, wait_seconds
        times.append(current_time)
        ref.update({"purchase_flow_times": [x.isoformat() for x in times], "updated_at": current_time})
        return True, 0


async def select_package(query, context, pkg_id: str):
    settings = get_settings()
    package = next((p for p in settings.get("packages", []) if p.get("id") == pkg_id), None)
    if not package:
        await edit_or_send(query, "প্যাকেজটি পাওয়া যায়নি।", back_button())
        return

    # Keep the chosen package in the user's session, but do not reveal any
    # account number until the user explicitly selects bKash/Nagad/Rocket.
    context.user_data["payment_package"] = package
    context.user_data.pop("payment_method", None)
    context.user_data.pop("payment_number", None)
    context.user_data.pop("payment_action", None)
    context.user_data["state"] = "choose_payment_method"

    methods = []
    payment_labels = {"bkash": "💗 bKash", "nagad": "🧡 Nagad", "rocket": "🚀 Rocket"}
    action_labels = {"payment": "Payment", "send_money": "Send Money", "cash_out": "Cash Out"}
    for method in settings.get("payment_methods", []):
        if not method.get("enabled") or not clean_text(method.get("account"), 40):
            continue
        key = clean_text(method.get("key"), 20).lower()
        if key not in {"bkash", "nagad", "rocket"}:
            continue
        name = payment_labels.get(key, clean_text(method.get("name", key), 30))
        action_label = action_labels.get(method.get("action"), "Send Money")
        methods.append([InlineKeyboardButton(
            f"{name} · {action_label}",
            callback_data=f"paymethod:{key}",
            style="success" if key == "bkash" else "primary",
        )])
    methods.append([InlineKeyboardButton("⬅️ বাতিল", callback_data="menu:buy", style="primary")])
    if len(methods) == 1:
        await edit_or_send(query, "❌ অ্যাডমিন এখনো কোনো পেমেন্ট মাধ্যম চালু করেননি।", back_button())
        return

    await edit_or_send(
        query,
        f"📦 *{clean_text(package.get('label'), 100)}*\n"
        f"💳 ক্রেডিট: *{credits_float(package.get('credits', 0)):g}*\n"
        f"💰 মূল্য: *৳{int(package.get('price', 0))}*\n\n"
        "পেমেন্ট করার জন্য একটি মাধ্যম নির্বাচন করুন।\n"
        "‌",
        InlineKeyboardMarkup(methods),
    )


async def select_payment_method(query, context, method: str):
    package = context.user_data.get("payment_package")
    if not package:
        await edit_or_send(query, "প্যাকেজের সেশন শেষ হয়েছে। Buy Credits আবার খুলুন।", back_button())
        return
    method = clean_text(method, 20).lower()
    settings = get_settings()
    method_data = next((item for item in settings.get("payment_methods", []) if item.get("key") == method), None)
    if not method_data or not method_data.get("enabled"):
        await edit_or_send(query, "এই পেমেন্ট মাধ্যমটি বর্তমানে বন্ধ। অন্য মাধ্যম নির্বাচন করুন।", back_button())
        return
    number = clean_text(method_data.get("account"), 40)
    if not number:
        await edit_or_send(query, "এই পেমেন্ট মাধ্যমের নম্বর সেট করা নেই।", back_button())
        return
    action = str(method_data.get("action", "send_money"))
    action_label = {"payment": "Payment", "send_money": "Send Money", "cash_out": "Cash Out"}.get(action, "Send Money")
    context.user_data["payment_method"] = method
    context.user_data["payment_number"] = number
    context.user_data["payment_action"] = action
    context.user_data["state"] = "payment_txn"
    markup = InlineKeyboardMarkup([
        [InlineKeyboardButton("📋 নম্বর কপি করুন", copy_text=CopyTextButton(text=number), style="success")],
        [InlineKeyboardButton("⬅️ অন্য পেমেন্ট মাধ্যম", callback_data=f"buy:{package.get('id')}", style="primary")],
    ])
    await edit_or_send(
        query,
        f"💳 *{clean_text(method_data.get('name'), 30)} — {action_label}*\n\n"
        f"📦 প্যাকেজ: *{clean_text(package.get('label'), 100)}*\n"
        f"💰 পাঠাতে হবে: *৳{int(package.get('price', 0))}*\n"
        f"📱 পেমেন্ট নম্বর: *{number}*\n\n"
        f"১. উপরের নম্বরটি কপি করুন।\n"
        f"২. ঠিক *৳{int(package.get('price', 0))}* টাকা {action_label} করে পাঠান।\n"
        "৩. টাকা পাঠানোর পর Transaction ID এখানে পাঠান।\n\n"
        "⚠️ টাকা না পাঠালে বা Transaction ID যাচাই না হলে ক্রেডিট যোগ হবে না। অ্যাডমিন যাচাই করে অনুমোদন দিলে তবেই ক্রেডিট পাবেন।",
        markup,
    )

async def handle_dashboard_button(update: Update, context: ContextTypes.DEFAULT_TYPE, label: str):
    user = update.effective_user
    message = update.effective_message
    if not user or not message:
        return
    user_id = user.id
    settings = get_settings()
    keyboard = main_keyboard(user_id)

    if label == "📞 Send Call":
        if settings.get("maintenance", False):
            await message.reply_text("🛠 কল সার্ভিস রক্ষণাবেক্ষণে আছে। আপাতত কল বন্ধ, অন্য সুবিধাগুলো চালু আছে।", reply_markup=keyboard)
            return
        balance = credits_float(get_user(user_id).get("balance", 0))
        cost = credits_float(settings.get("call_credit_cost", 1))
        if balance <= 0 or balance < cost:
            await message.reply_text(f"❌ কল দিতে ক্রেডিট প্রয়োজন। প্রয়োজন: {cost:g}; বর্তমান ব্যালেন্স: {balance:g}। Buy Credits অথবা Redeem ব্যবহার করুন।", reply_markup=keyboard)
            return
        context.user_data["state"] = "call_phone"
        await message.reply_text("📞 কল করুন\nযে নম্বরে কল দিতে চান সেটি পাঠান। উদাহরণ: 01700000000", reply_markup=keyboard)
        return

    if label == "👤 My Profile":
        data = get_user(user_id)
        await message.reply_text(profile_message(user_id, data), reply_markup=keyboard, parse_mode="HTML")
        return

    if label == "👥 Refer":
        me = await context.bot.get_me()
        referral_link = f"https://t.me/{me.username}?start=ref_{user_id}"
        bonus = credits_float(settings.get("referral_bonus", 1))
        await message.reply_text(
            "👥 রেফারেল প্রোগ্রাম\n━━━━━━━━━━━━━━━━━\n"
            f"রেফারেল বোনাস: {bonus:g} ক্রেডিট\n"
            f"লিংক শেয়ার করুন এবং {bonus:g} ক্রেডিট জিতে নিন!\n\n"
            f"আপনার রেফারেল লিংক:\n{referral_link}\n\n"
            "বোনাস শুধু যোগ্য নতুন ব্যবহারকারীর জন্য। ",
            reply_markup=referral_keyboard(referral_link),
        )
        return

    if label == "📊 LP Statistics":
        totals = await local_stats()
        lines = [
            "📊 LP Statistics", "━━━━━━━━━━━━━━━━━",
            f"Users: {totals['users']}",
            f"Total Calls: {totals['calls']}",
            "", "🏆 Top Credit Holders",
        ]
        top_users = [item for item in totals.get("top_users", []) if credits_float(item.get("balance", 0)) > 0]
        if not top_users:
            lines.append("No credit holders yet.")
        else:
            for rank, item in enumerate(top_users, 1):
                lines.append(f"{rank}. {item.get('name') or 'User'} — {format_balance(item.get('balance', 0))} credits")
        await message.reply_text("\n".join(lines), reply_markup=keyboard)
        return

    if label == "💰 Buy Credits":
        packages = settings.get("packages", [])
        rows = [[InlineKeyboardButton(clean_text(pkg.get("label", f"{pkg.get('credits')} Calls"), 60), callback_data=f"buy:{pkg.get('id')}", style="success" if i % 2 == 0 else "primary")] for i, pkg in enumerate(packages)]
        rows.append([InlineKeyboardButton("⬅️ বাতিল", callback_data="menu:home", style="primary")])
        package_lines = "\n".join(f"• {html.escape(clean_text(pkg.get('label'), 100))}" for pkg in packages)
        enabled_names = [html.escape(str(item.get("name", ""))) for item in settings.get("payment_methods", []) if item.get("enabled")]
        methods_text = ", ".join(enabled_names) if enabled_names else "কোনো পেমেন্ট মাধ্যম চালু নেই"
        text = (
            "💰 <b>ক্রেডিট কিনুন</b>\n━━━━━━━━━━━━━━━━━\n\n"
            "📦 <b>উপলভ্য প্যাকেজ:</b>\n\n" + package_lines + "\n━━━━━━━━━━━━━━━━━\n"
            f"💳 <b>চালু পেমেন্ট মাধ্যম:</b> {methods_text}\n"
            "প্যাকেজ নির্বাচন করার পরেই পেমেন্ট নম্বর দেখানো হবে।\n"
            "⚡ অ্যাডমিন অনুমোদন দিলে ক্রেডিট স্বয়ংক্রিয়ভাবে যোগ হবে।\n\n👇 নিচের প্যাকেজ নির্বাচন করুন:"
        )
        await message.reply_text(text, parse_mode="HTML", reply_markup=InlineKeyboardMarkup(rows))
        return

    if label == "🎁 Redeem":
        context.user_data["state"] = "redeem_code"
        await message.reply_text("🎁 রিডিম কোড\nআপনার রিডিম কোডটি পাঠান।", reply_markup=keyboard)
        return

    if label == "🕘 Call History":
        docs = list(db.collection(COL_CALLS).where("user_id", "==", user_id).limit(50).stream())
        docs.sort(key=lambda snap: str((snap.to_dict() or {}).get("created_at") or ""), reverse=True)
        if not docs:
            await message.reply_text("📞 কলের ইতিহাস\nএখনো কোনো কলের ইতিহাস নেই।", reply_markup=keyboard)
            return
        lines = ["📞 Recent Calls"]
        for snap in docs[:5]:
            record = snap.to_dict() or {}
            number = clean_text(record.get("number", ""), 30) or "অজানা"
            lines.append(f"• {number} — {str(record.get('status', 'unknown')).upper()} — {iso(record.get('created_at')) or '-'}")
        await message.reply_text("\n".join(lines), reply_markup=keyboard)
        return

    if label == "☎️ Support":
        support_url = clean_text(settings.get("support_contact_url") or SUPPORT_CONTACT_URL, 300)
        support_text = clean_text(settings.get("support_text", "সহায়তার জন্য নিচের বাটনে চাপ দিন।"), 1800)
        markup = InlineKeyboardMarkup([[InlineKeyboardButton("✉️ Message Support Admin", url=support_url, style="primary")]])
        await message.reply_text(f"☎️ Support\n{support_text}\nAdmin id: {7034779471}", reply_markup=markup)
        return

    if label == "🎁 Daily Bonus":
        try:
            after = claim_daily_credit(user_id)
            await message.reply_text(f"🎁 দৈনিক বোনাস পেয়েছেন: +{credits_float(settings.get('daily_bonus', 0)):g} ক্রেডিট। নতুন ব্যালেন্স: {after:g}", reply_markup=main_keyboard(user_id))
        except Exception as exc:
            await message.reply_text(f"ℹ️ {clean_text(exc, 300)}", reply_markup=keyboard)
        return

    if label == "🛠 Admin Panel" and is_admin(user_id):
        await message.reply_text("🛠 Admin Panel — choose an operation:", reply_markup=admin_keyboard_markup())
        return

    return


async def handle_text_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not update.effective_message:
        return
    user_id = update.effective_user.id
    status = await channel_membership_status(context.bot, user_id)
    if status is not True:
        await show_join_gate(update.effective_message, context, verification_error=status is None)
        return
    ensure_user(update.effective_user)
    if user_blocked(user_id) and not is_admin(user_id):
        await update.effective_message.reply_text("⛔ আপনার অ্যাকাউন্ট বন্ধ করা হয়েছে। সহায়তার জন্য Support-এ যোগাযোগ করুন।")
        return

    text = clean_text(update.effective_message.text, 4000)
    dashboard_labels = {
        "📞 Send Call", "👤 My Profile", "👥 Refer", "📊 LP Statistics",
        "💰 Buy Credits", "🎁 Redeem", "🕘 Call History", "☎️ Support",
        "🎁 Daily Bonus", "🛠 Admin Panel",
    }
    if text in dashboard_labels:
        context.user_data.clear()
        await handle_dashboard_button(update, context, text)
        return
    state = context.user_data.get("state")
    if is_admin(user_id) and state and state.startswith("admin_"):
        await handle_admin_state(update, context, text)
        return
    if state == "redeem_code":
        await redeem_code(update, context, text)
        return
    if state == "payment_txn":
        await create_payment_request(update, context, text)
        return
    if state == "call_phone":
        u = get_user(user_id)
        cost = credits_float(get_settings().get("call_credit_cost", 1))
        if credits_float(u.get("balance", 0)) <= 0 or credits_float(u.get("balance", 0)) < cost:
            await update.effective_message.reply_text(f"❌ কল দিতে ক্রেডিট প্রয়োজন। প্রয়োজন: {cost:g} ক্রেডিট। Buy Credits অথবা Redeem ব্যবহার করুন।")
            context.user_data.clear()
            return
        phone = normalize_phone(text)
        if not phone:
            await update.effective_message.reply_text("❌ ফোন নম্বর সঠিক নয়। আবার চেষ্টা করুন।")
            return
        context.user_data["call_phone"] = phone
        context.user_data["state"] = "call_mode"
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton("📝 টেক্সট থেকে ভয়েস", callback_data="callmode:text", style="success")],
            [InlineKeyboardButton("🔗 অডিও লিংক", callback_data="callmode:audio_url", style="primary")],
            [InlineKeyboardButton("🎧 অডিও আপলোড", callback_data="callmode:audio_upload", style="primary")],
            [InlineKeyboardButton("🎙️ ভয়েস টেমপ্লেট ব্যবহার", callback_data="callmode:templates", style="success")],
            [InlineKeyboardButton("❌ বাতিল", callback_data="call:cancel", style="danger")],
        ])
        await update.effective_message.reply_text(f"📞 নম্বর: ****{phone[-4:]}\n\nকলের ভয়েস কীভাবে দিতে চান, নির্বাচন করুন।", parse_mode=None, reply_markup=markup)
        return
    if state in {"voice_template_title_global", "voice_template_title_personal"}:
        handled = await save_voice_template_title(update, context, text)
        if handled:
            return
    if state == "call_custom_duration":
        raw_seconds = re.sub(r"\s*(?:sec|secs|seconds|s|সেকেন্ড)\s*$", "", text, flags=re.I).strip()
        if not raw_seconds.isdigit():
            await update.effective_message.reply_text("শুধু সেকেন্ডের সংখ্যা লিখুন, যেমন 45।")
            return
        seconds = int(raw_seconds)
        if seconds < 10 or seconds > 300:
            await update.effective_message.reply_text("সময় ১০ থেকে ৩০০ সেকেন্ডের মধ্যে দিন।")
            return
        context.user_data["call_time"] = seconds
        await execute_pending_call(update, context)
        return
    if state == "call_content_text":
        if not text:
            await update.effective_message.reply_text("❌ কলের জন্য বলার টেক্সট প্রয়োজন।")
            return
        context.user_data["call_text"] = text
        await ask_call_time(update)
        return
    if state == "call_content_audio_url":
        if not re.match(r"^https?://", text, re.I):
            await update.effective_message.reply_text("❌ সঠিক http/https অডিও লিংক পাঠান।")
            return
        if not re.search(r"\.(mp3|wav|ogg)(\?.*)?$", text, re.I):
            await update.effective_message.reply_text("⚠️ লিংকটি সরাসরি MP3, WAV অথবা OGG ফাইলের হতে হবে।")
            return
        context.user_data["call_audio_url"] = text
        await ask_call_time(update)
        return
    if state == "call_content_audio_upload":
        await update.effective_message.reply_text("প্রথমে Send Call থেকে অডিও আপলোড নির্বাচন করে অডিও বা ভয়েস ফাইল পাঠান।")
        return
    if state == "admin_broadcast":
        await do_broadcast(update, context, text)
        return
    # কোনো অপশন নির্বাচন না করা থাকলে সাধারণ টেক্সটের উত্তর দেওয়া হবে না।
    return

async def ask_call_time(update: Update):
    markup = InlineKeyboardMarkup([
        [
            InlineKeyboardButton("10s", callback_data="calltime:10", style="success"),
            InlineKeyboardButton("30s", callback_data="calltime:30", style="primary"),
            InlineKeyboardButton("60s", callback_data="calltime:60", style="primary"),
        ],
        [
            InlineKeyboardButton("120s", callback_data="calltime:120", style="primary"),
            InlineKeyboardButton("180s", callback_data="calltime:180", style="primary"),
            InlineKeyboardButton("300s", callback_data="calltime:300", style="primary"),
        ],
        [InlineKeyboardButton("✍️ নিজের সময় লিখুন", callback_data="calltime:custom", style="success")],
        [InlineKeyboardButton("❌ বাতিল", callback_data="call:cancel", style="danger")],
    ])
    message = interaction_message(update)
    if message:
        await message.reply_text("⏱️ কলের সময় নির্বাচন করুন।", reply_markup=markup)


async def handle_audio_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not update.effective_message:
        return
    user_id = update.effective_user.id
    channel_status = await channel_membership_status(context.bot, user_id)
    if channel_status is not True:
        await show_join_gate(update.effective_message, context, verification_error=channel_status is None)
        return
    ensure_user(update.effective_user)
    if user_blocked(user_id) and not is_admin(user_id):
        await update.effective_message.reply_text("⛔ Your account is blocked.")
        return
    current_state = context.user_data.get("state")
    template_upload_state = current_state in {"voice_template_upload_global", "voice_template_upload_personal"}
    if current_state != "call_content_audio_upload" and not template_upload_state:
        await update.effective_message.reply_text("প্রথমে Send Call → অডিও আপলোড নির্বাচন করুন, তারপর MP3/WAV/OGG ফাইল বা ভয়েস মেসেজ পাঠান।")
        return

    message = update.effective_message
    media = None
    extension = "ogg"
    content_type = "audio/ogg"
    if message.audio:
        media = message.audio
        name = media.file_name or ""
        match = re.search(r"\.(mp3|wav|ogg)$", name, re.I)
        if match:
            extension = match.group(1).lower()
        else:
            mime = (getattr(media, "mime_type", "") or "").lower()
            extension = "wav" if "wav" in mime else "ogg" if "ogg" in mime else "mp3"
        content_type = {"mp3": "audio/mpeg", "wav": "audio/wav", "ogg": "audio/ogg"}[extension]
    elif message.voice:
        media = message.voice
        extension = "ogg"
        content_type = "audio/ogg"
    elif message.document:
        media = message.document
        name = media.file_name or ""
        match = re.search(r"\.(mp3|wav|ogg)$", name, re.I)
        if not match:
            await message.reply_text("❌ সমর্থিত অডিও ফরম্যাট: MP3, WAV, OGG।")
            return
        extension = match.group(1).lower()
        content_type = {"mp3": "audio/mpeg", "wav": "audio/wav", "ogg": "audio/ogg"}[extension]
    else:
        await message.reply_text("❌ MP3, WAV, OGG ফাইল অথবা Telegram voice message পাঠান।")
        return

    file_size = _safe_int(getattr(media, "file_size", None))
    max_size = 15 * 1024 * 1024
    if file_size is not None and file_size > max_size:
        await message.reply_text("❌ অডিও ফাইল ১৫ MB-এর বেশি। ছোট MP3/WAV/OGG ফাইল পাঠান।")
        return
    if template_upload_state:
        context.user_data["pending_voice_template"] = {
            "file_id": media.file_id,
            "extension": extension,
            "content_type": content_type,
            "file_size": file_size or 0,
        }
        context.user_data["state"] = "voice_template_title_global" if current_state == "voice_template_upload_global" else "voice_template_title_personal"
        await message.reply_text("✅ অডিও পাওয়া গেছে। এবার টেমপ্লেটের একটি নাম লিখুন (২–৬০ অক্ষর)।")
        return
    if not PUBLIC_BASE_URL or not re.match(r"^https://", PUBLIC_BASE_URL, re.I):
        await message.reply_text("❌ অডিও পাঠানোর জন্য Render-এর HTTPS PUBLIC_BASE_URL সেট করুন (উদাহরণ: https://your-service.onrender.com)। Firebase Storage bucket প্রয়োজন নেই।")
        return

    try:
        audio_url = await asyncio.to_thread(
            create_audio_proxy_url, user_id, media.file_id, extension,
            content_type, file_size or 0,
        )
        context.user_data["call_audio_url"] = audio_url
        context.user_data["call_mode"] = "audio_upload"
        context.user_data.pop("call_template_id", None)
        context.user_data.pop("call_template_title", None)
        await message.reply_text("✅ অডিও প্রস্তুত। এখন কলের সময় নির্বাচন করুন।")
        await ask_call_time(update)
    except Exception as exc:
        await message.reply_text(f"❌ অডিও প্রস্তুত করা যায়নি: {clean_text(exc, 400)}")


async def execute_pending_call(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    if user is None:
        return
    uid = user.id
    lock = USER_CALL_LOCKS.setdefault(uid, asyncio.Lock())
    if lock.locked():
        try:
            message = interaction_message(update)
            if message:
                await message.reply_text("⏳ আপনার একটি কলের অনুরোধ প্রক্রিয়াধীন আছে। একটু অপেক্ষা করুন।")
        except Exception:
            pass
        return
    try:
        async with lock:
            await _execute_pending_call_impl(update, context)
    finally:
        if USER_CALL_LOCKS.get(uid) is lock and not lock.locked():
            USER_CALL_LOCKS.pop(uid, None)


async def _execute_pending_call_impl(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    source_message = interaction_message(update)
    if source_message is None:
        return
    settings = get_settings()
    u = get_user(user_id)
    if u.get("is_blocked") and not is_admin(user_id):
        await source_message.reply_text("⛔ আপনার অ্যাকাউন্ট বন্ধ করা হয়েছে।")
        return
    if settings.get("maintenance", False):
        await source_message.reply_text("🛠 কল সার্ভিস রক্ষণাবেক্ষণে আছে। অন্য ফিচারগুলো চালু থাকবে।")
        context.user_data.clear()
        return
    phone = context.user_data.get("call_phone")
    txt = context.user_data.get("call_text")
    audio = context.user_data.get("call_audio_url")
    seconds = _safe_int(context.user_data.get("call_time", 30)) or 30
    if seconds < 10 or seconds > 300:
        await source_message.reply_text("কলের সময় ১০ থেকে ৩০০ সেকেন্ডের মধ্যে হতে হবে।")
        return
    if not phone or (not txt and not audio):
        await source_message.reply_text("❌ কলের তথ্য অসম্পূর্ণ। Send Call থেকে আবার শুরু করুন।")
        context.user_data.clear()
        return
    now_dt = now()
    last_call = parse_datetime(u.get("last_call_at"))
    cooldown = max(0, _safe_int(settings.get("call_cooldown_seconds", 15)) if _safe_int(settings.get("call_cooldown_seconds", 15)) is not None else 15)
    if last_call is not None and (now_dt-last_call).total_seconds() < cooldown and not is_admin(user_id):
        wait = max(1, int(cooldown-(now_dt-last_call).total_seconds()))
        await source_message.reply_text(f"⏳ পরের কল দেওয়ার আগে আরও {wait} সেকেন্ড অপেক্ষা করুন।")
        return
    day_key = local_day_key()
    calls_today = _safe_int(u.get("calls_today", 0)) or 0
    if u.get("call_day") != day_key:
        calls_today = 0
    limit = max(0, _safe_int(settings.get("daily_call_limit", 20)) if _safe_int(settings.get("daily_call_limit", 20)) is not None else 20)
    if calls_today >= limit and not is_admin(user_id):
        await source_message.reply_text("🚫 আজকের কলের সীমা শেষ হয়েছে।")
        context.user_data.clear()
        return
    cost = credits_float(settings.get("call_credit_cost", 1))
    balance = credits_float(u.get("balance", 0))
    if cost <= 0:
        await source_message.reply_text("⚠️ কলের চার্জের সেটিং সঠিক নয়। অ্যাডমিনের সঙ্গে যোগাযোগ করুন।")
        context.user_data.clear()
        return
    if balance <= 0 or balance < cost:
        await source_message.reply_text(f"❌ পর্যাপ্ত ক্রেডিট নেই। প্রয়োজন: {cost:g}; বর্তমান ব্যালেন্স: {balance:g}।")
        context.user_data.clear()
        return

    log_ref = db.collection(COL_CALLS).document()
    call_template_title = clean_text(context.user_data.get("call_template_title", ""), 100)
    selected_mode = str(context.user_data.get("call_mode", "")).lower()
    audio_source = "template" if call_template_title else ("audio_upload" if selected_mode == "audio_upload" else "audio_url" if audio else "text_to_speech")
    log_ref.set({
        "user_id": user_id, "number": phone, "mode": "text" if txt else "template" if call_template_title else "audio",
        "template_id": context.user_data.get("call_template_id"),
        "template_title": call_template_title or None,
        "audio_source": audio_source,
        "time": seconds, "status": "pending", "provider_call_id": None,
        "recording_url": None, "created_at": now_dt, "updated_at": now_dt,
        "cost": cost, "api_response": None,
    })
    try:
        deduct_credits(user_id, cost, "call_charge", log_ref.id)
        user_ref(user_id).set({
            "last_call_at": now_dt, "call_day": day_key,
            "calls_today": calls_today + 1, "updated_at": now_dt,
        }, merge=True)
    except Exception as exc:
        log_ref.update({"status": "rejected", "error": clean_text(exc, 500), "updated_at": now()})
        await source_message.reply_text(f"❌ {clean_text(exc, 500)}")
        context.user_data.clear()
        return

    progress_message = None
    try:
        progress_message = await source_message.reply_text(
            "📞 আপনার কলটি প্রক্রিয়াধীন…\nফলাফল নিশ্চিত হলেই এখানে জানানো হবে।",
            parse_mode=None,
        )
    except Exception:
        # Failure to display progress must not stop a valid provider request.
        progress_message = None

    async def report_call_result(text: str, reply_markup=None):
        if progress_message is not None:
            try:
                await progress_message.edit_text(text, parse_mode=None, reply_markup=reply_markup)
                return
            except Exception:
                pass
        try:
            await source_message.reply_text(text, parse_mode=None, reply_markup=reply_markup)
        except Exception:
            pass

    try:
        result = await provider_call(phone, txt=txt, audio=audio, seconds=seconds)
        status_value = str(result.get("status", "")).strip().lower()
        success = status_value in {"success", "succeeded", "completed"}
        uncertain = status_value in {"accepted_unconfirmed", "accepted", "ok", "pending", "processing", "queued", "unknown"}
        provider_data = result.get("data") if isinstance(result.get("data"), dict) else {}
        provider_id = provider_data.get("id") or provider_data.get("call_id") or result.get("call_id") or result.get("id")
        recording_url = provider_data.get("recording_url") or provider_data.get("recording") or provider_data.get("audio_url") or result.get("recording_url") or result.get("recording")
        stored_status = "success" if success else "submitted_unconfirmed" if uncertain else "failed"
        safe_result = {
            "status": stored_status,
            "message": clean_provider_message(result.get("message") or ("Provider accepted request" if success else "Provider confirmation unavailable" if uncertain else "Provider rejected request")),
            "http_code": result.get("http_code"),
            "response_type": result.get("response_type"),
            "provider_id": clean_text(provider_id, 300) if provider_id else None,
        }
        log_ref.update({
            "status": stored_status,
            "provider_call_id": clean_text(provider_id, 300) if provider_id else None,
            "recording_url": clean_text(recording_url, 2000) if recording_url else None,
            "api_response": safe_result, "updated_at": now(),
        })
        user_ref(user_id).set({
            "total_calls": firestore.Increment(1),
            "successful_calls": firestore.Increment(1 if success else 0),
            "failed_calls": firestore.Increment(0 if (success or uncertain) else 1),
            "total_seconds": firestore.Increment(seconds if success else 0),
            "updated_at": now(),
        }, merge=True)
        if success:
            msg = (
                "✅ কল সফল — কল API সফলতা নিশ্চিত করেছে।\n"
                "━━━━━━━━━━━━━━━━━━\n"
                f"📞 Number: ****{phone[-4:]}\n"
                f"⏱ Duration: {seconds}s\n"
                f"💳 Charged: {cost:g} credits\n"
                f"🆔 Call ID: {clean_text(provider_id or log_ref.id, 120)}\n"
                f"Provider: {clean_provider_message(result.get('message') or 'Success') or 'Success'}"
            )
            if recording_url and re.match(r"^https?://", str(recording_url), re.I):
                msg += "\n🎧 Recording available."
                markup = InlineKeyboardMarkup([[InlineKeyboardButton("▶️ Listen Recording", url=str(recording_url), style="success")]])
                await report_call_result(msg, reply_markup=markup)
            else:
                await report_call_result(msg)
        elif uncertain:
            msg = (
                "⏳ কলের ফলাফল এখনো নিশ্চিত নয়\n"
                "━━━━━━━━━━━━━━━━━━\n"
                f"Number: ****{phone[-4:]}\nCall ID: {clean_text(provider_id or log_ref.id, 120)}\n"
                "Provider থেকে চূড়ান্ত সফলতার উত্তর পাওয়া যায়নি, তাই কল সফল বলা হচ্ছে না। একই নম্বরে দ্বিতীয়বার কল এড়াতে অপেক্ষা করুন। ক্রেডিট আপাতত সংরক্ষিত আছে; নিশ্চিত ফলাফল এলে ইতিহাস আপডেট হবে।"
            )
            await report_call_result(msg)
        else:
            refund_credits(user_id, cost, "call_refund", log_ref.id)
            await report_call_result(
                "❌ কল ব্যর্থ হয়েছে\n"
                f"Reason: {clean_provider_message(result.get('message') or 'Provider rejected the request.') or 'Provider rejected the request.'}\n"
                f"{cost:g} ক্রেডিট ফেরত দেওয়া হয়েছে।"
            )
    except (httpx.ConnectError, httpx.ConnectTimeout, httpx.PoolTimeout) as exc:
        # These errors occur before an HTTP connection is established, so the provider
        # cannot have confirmed the request. Restore the reserved credits idempotently.
        log_ref.update({"status": "failed", "error": clean_text(exc, 500), "updated_at": now()})
        user_ref(user_id).set({
            "total_calls": firestore.Increment(1),
            "failed_calls": firestore.Increment(1),
            "updated_at": now(),
        }, merge=True)
        try:
            refund_credits(user_id, cost, "call_refund_connect_error", log_ref.id)
        except Exception:
            pass
        await report_call_result(
                f"❌ Provider-এর সঙ্গে সংযোগ হয়নি। {cost:g} ক্রেডিট ফেরত দেওয়া হয়েছে। কিছুক্ষণ পরে আবার চেষ্টা করুন।"
        )
    except Exception as exc:
        # Once a request may have left this server, a generic timeout/error is ambiguous.
        # Preserve a final status if it was already stored; never double-count the call.
        current_record = {}
        try:
            current_record = log_ref.get().to_dict() or {}
        except Exception:
            pass
        current_status = str(current_record.get("status", "")).lower()
        if current_status not in {"success", "failed", "submitted_unconfirmed"}:
            log_ref.update({"status": "submitted_unconfirmed", "error": clean_text(exc, 500), "updated_at": now()})
            user_ref(user_id).set({
                "total_calls": firestore.Increment(1),
                "updated_at": now(),
            }, merge=True)
        try:
            await report_call_result(
                f"⏳ কলের চূড়ান্ত অবস্থা নিশ্চিত নয়। Provider সফলতার নিশ্চিত উত্তর দেয়নি। Call ID: {log_ref.id}। Call History দেখুন; আবার কল দেওয়ার আগে অপেক্ষা করুন।"
            )
        except Exception:
            pass
    finally:
        context.user_data.clear()

def clean_provider_message(value: Any) -> str:
    text = clean_text(value, 1200)
    if not text:
        return ""
    lowered = text.lstrip().lower()
    if lowered.startswith(("<!doctype html", "<html", "&lt;!doctype html", "&lt;html")) or "<title>server error</title>" in lowered or "&lt;title&gt;server error" in lowered:
        return "Provider returned an invalid HTML response; raw page hidden."
    text = re.sub(r"<[^>]*>", " ", text)
    text = html.unescape(text)
    text = re.sub(r"\s+", " ", text).strip()
    return text[:800]


async def provider_call(number: str, txt: Optional[str] = None, audio: Optional[str] = None, seconds: int = 30) -> dict:
    if not txt and not audio:
        raise ValueError("Either text or audio is required")
    payload = {
        "api_token": CALL_API_TOKEN,
        "number": number,
        "time": int(max(1, min(300, seconds))),
    }
    if txt:
        payload["txt"] = txt
    else:
        payload["audio"] = audio

    # Provider docs allow POST/GET. Use POST form data to avoid placing the API token in URL logs.
    # Do not automatically retry an ambiguous call request: a retry can dial the same user twice.
    client = provider_http_client
    try:
        if client is None:
            async with httpx.AsyncClient(
                timeout=httpx.Timeout(connect=10.0, read=120.0, write=30.0, pool=15.0),
                follow_redirects=True,
                limits=httpx.Limits(max_connections=50, max_keepalive_connections=20, keepalive_expiry=20.0),
            ) as temporary_client:
                response = await temporary_client.post(f"{CALL_API_BASE}/call", data=payload)
        elif provider_call_semaphore is not None:
            async with provider_call_semaphore:
                response = await client.post(f"{CALL_API_BASE}/call", data=payload)
        else:
            response = await client.post(f"{CALL_API_BASE}/call", data=payload)
    except (httpx.ConnectError, httpx.ConnectTimeout, httpx.PoolTimeout):
        raise
    except httpx.TimeoutException:
        # A read timeout can happen after the provider has accepted the call.
        return {"status": "accepted_unconfirmed", "message": "Provider response timed out after sending the request; final result is unknown.", "response_type": "timeout"}

    body = response.text or ""
    content_type = (response.headers.get("content-type") or "").lower()
    try:
        data = response.json()
        if not isinstance(data, dict):
            data = None
    except Exception:
        data = None

    body_lower = body.lstrip().lower()
    looks_html = (
        "text/html" in content_type
        or body_lower.startswith(("<!doctype html", "<html", "&lt;!doctype html", "&lt;html"))
        or "<title>server error</title>" in body_lower
        or "&lt;title&gt;server error" in body_lower
    )

    # This provider has been observed to return a server HTML page after a call was actually placed.
    # Never expose the HTML, retry automatically, or refund on an ambiguous 5xx response.
    if response.status_code >= 500 or (data is None and looks_html):
        return {
            "status": "accepted_unconfirmed",
            "message": "Provider returned a server error/non-JSON reply. The call may have been accepted; status is unconfirmed.",
            "http_code": response.status_code,
            "response_type": "html" if looks_html else "server_error",
        }
    if data is None:
        if response.status_code >= 400:
            return {"status": "error", "message": f"Provider HTTP {response.status_code}; raw response hidden.", "http_code": response.status_code}
        return {"status": "accepted_unconfirmed", "message": "Provider returned an unreadable response; final status is unconfirmed.", "http_code": response.status_code, "response_type": "unknown"}

    nested = data.get("data") if isinstance(data.get("data"), dict) else {}
    raw_status = data.get("status", data.get("result", nested.get("status", "")))
    provider_status = str(raw_status).strip().lower()
    explicit_success = (
        data.get("success") is True
        or data.get("ok") is True
        or provider_status in {"success", "succeeded", "completed"}
        or (isinstance(raw_status, (int, float)) and raw_status == 1)
        or provider_status == "true"
    )
    explicit_failure = (
        data.get("success") is False
        or data.get("ok") is False
        or provider_status in {"error", "failed", "failure", "rejected", "denied", "cancelled", "canceled"}
    )
    if explicit_failure:
        return {
            "status": "error",
            "message": clean_provider_message(data.get("message") or nested.get("message") or "Provider rejected the request."),
            "http_code": response.status_code,
            "response_type": "json",
        }
    if response.status_code < 400 and explicit_success:
        data["status"] = "success"
        data["message"] = clean_provider_message(data.get("message") or nested.get("message") or "Provider confirmed success")
        data["http_code"] = response.status_code
        return data
    if response.status_code >= 400:
        return {"status": "error", "message": clean_provider_message(data.get("message") or f"Provider HTTP {response.status_code}"), "http_code": response.status_code}
    data["status"] = "accepted_unconfirmed"
    data["message"] = clean_provider_message(data.get("message") or nested.get("message") or "Provider did not return an explicit success status.")
    data["http_code"] = response.status_code
    return data


async def account_api(endpoint: str) -> dict:
    try:
        async with httpx.AsyncClient(timeout=30.0, follow_redirects=True) as client:
            response = await client.get(f"{CALL_API_BASE}/{endpoint}", params={"api_token": CALL_API_TOKEN})
            try:
                data = response.json()
            except Exception:
                return {"status": "error", "message": "Provider returned a non-JSON response.", "http_code": response.status_code}
            if not isinstance(data, dict):
                return {"status": "error", "message": "Provider returned an unexpected response format."}
            if "message" in data:
                data["message"] = clean_provider_message(data.get("message"))
            return data
    except Exception:
        return {"status": "error", "message": "Provider API is temporarily unavailable."}

def claim_daily_credit(user_id: int) -> float:
    settings = get_settings()
    if not settings.get("daily_bonus_enabled", False):
        raise ValueError("Daily Bonus is currently disabled by admin.")
    bonus = credits_float(settings.get("daily_bonus", 0))
    if bonus <= 0:
        raise ValueError("Daily bonus is disabled because its amount is zero.")
    today = local_day_key()
    ref = user_ref(user_id)
    transaction = db.transaction()

    @firestore.transactional
    def claim(transaction):
        snap = ref.get(transaction=transaction)
        if not snap.exists:
            raise ValueError("User account not found.")
        data = snap.to_dict() or {}
        if data.get("last_daily_bonus") == today:
            raise ValueError("Daily bonus already claimed today.")
        before = credits_float(data.get("balance", 0))
        after = credits_float(before + bonus)
        transaction.update(ref, {
            "balance": after,
            "last_daily_bonus": today,
            "updated_at": now(),
        })
        transaction.create(ledger_ref_for(user_id, "daily_bonus", today), {
            "user_id": user_id, "type": "daily_bonus", "amount": bonus,
            "before": before, "after": after, "reference": today, "created_at": now(),
        })
        return after

    return claim(transaction)


async def claim_daily(query):
    user_id = query.from_user.id
    try:
        after = claim_daily_credit(user_id)
        await edit_or_send(query, f"🎁 Daily bonus claimed: +{credits_float(get_settings().get('daily_bonus', 0)):g} credits.\n💳 New balance: {after:g}", back_button())
    except Exception as exc:
        await edit_or_send(query, f"ℹ️ {clean_text(exc, 300)}", back_button())


async def redeem_code(update: Update, context: ContextTypes.DEFAULT_TYPE, code_input: str):
    user_id = update.effective_user.id
    code = re.sub(r"\s+", "", code_input).upper()
    if not code:
        await update.effective_message.reply_text("❌ Code is required.")
        return
    q = db.collection(COL_CODES).where("code", "==", code).limit(1).stream()
    docs = list(q)
    if not docs:
        await update.effective_message.reply_text("❌ Invalid redeem code.")
        return
    snap = docs[0]
    ref = snap.reference
    transaction = db.transaction()

    @firestore.transactional
    def use_code(transaction):
        code_snap = ref.get(transaction=transaction)
        if not code_snap.exists:
            raise ValueError("Invalid code")
        data = code_snap.to_dict() or {}
        if not data.get("active", True):
            raise ValueError("Code is disabled")
        expires_at = parse_datetime(data.get("expires_at"))
        if expires_at is not None and expires_at < now():
            raise ValueError("Code has expired")
        used_by = list(data.get("used_by", []))
        if user_id in used_by:
            raise ValueError("You already used this code")
        uses = _safe_int(data.get("uses", 0)) or 0
        max_uses = _safe_int(data.get("max_uses", 1)) if _safe_int(data.get("max_uses", 1)) is not None else 1
        if max_uses > 0 and uses >= max_uses:
            raise ValueError("Code usage limit reached")
        amount = credits_float(data.get("credits", 0))
        if amount <= 0:
            raise ValueError("Invalid code amount")
        user_ref_local = user_ref(user_id)
        us = user_ref_local.get(transaction=transaction)
        if not us.exists:
            raise ValueError("User not found")
        ud = us.to_dict() or {}
        before = credits_float(ud.get("balance", 0))
        after = credits_float(before + amount)
        transaction.update(user_ref_local, {"balance": after, "updated_at": now()})
        if len(used_by) < 5000:
            used_by.append(user_id)
        transaction.update(
            ref,
            {
                "uses": uses + 1,
                "used_by": used_by,
                "updated_at": now(),
                "active": False if max_uses > 0 and uses + 1 >= max_uses else True,
            },
        )
        transaction.create(ledger_ref_for(user_id, "redeem", code), {
            "user_id": user_id, "type": "redeem", "amount": amount,
            "before": before, "after": after, "reference": code, "created_at": now(),
        })
        return amount

    try:
        amount = use_code(transaction)
        context.user_data.clear()
        await update.effective_message.reply_text(
            f"🎉 Redeemed successfully.\nAdded: +{amount:g} credits."
        )
    except Exception as exc:
        error_text = clean_text(exc, 800)
        lowered = error_text.lower()
        if any(token in lowered for token in ("already recorded", "record already exists", "already exists", "duplicate", "already used")):
            message = "ℹ️ Ei code age redeem hoyeche ba request already process hoyeche. Extra credit add kora hoyni."
        else:
            message = f"❌ Redeem failed: {error_text}"
        await update.effective_message.reply_text(message, reply_markup=main_keyboard(user_id))


async def create_payment_request(update: Update, context: ContextTypes.DEFAULT_TYPE, txn_id: str):
    user = update.effective_user
    user_id = user.id
    package = context.user_data.get("payment_package")
    method = context.user_data.get("payment_method")
    number = context.user_data.get("payment_number")
    payment_action = clean_text(context.user_data.get("payment_action", "send_money"), 30)
    if not package or method not in {"bkash", "nagad", "rocket"} or not number:
        await update.effective_message.reply_text("❌ কেনাকাটার সেশন শেষ হয়েছে। Buy Credits আবার খুলুন।")
        context.user_data.clear()
        return

    # Count every submitted transaction attempt, including malformed/duplicate IDs,
    # so a user cannot retry bad payment details indefinitely within one flow.
    allowed, wait_seconds = await record_purchase_attempt(user_id)
    if not allowed:
        await update.effective_message.reply_text(
            f"⏳ কেনাকাটার অনুরোধের সীমা পূর্ণ হয়েছে। ১০ মিনিটে সর্বোচ্চ ৩টি অনুরোধ করা যাবে। "
            f"{wait_seconds // 60} মিনিট {wait_seconds % 60} সেকেন্ড পরে আবার চেষ্টা করুন।"
        )
        return

    txn_id = clean_text(txn_id, 100)
    if not re.fullmatch(r"[A-Za-z0-9_-]{3,100}", txn_id):
        await update.effective_message.reply_text("❌ Transaction ID সঠিক নয়। ৩–১০০ অক্ষর/সংখ্যা অথবা _ / - ব্যবহার করুন। এই চেষ্টাটিও গণনা হয়েছে।")
        return
    duplicate_docs = list(db.collection(COL_PAYMENTS).stream())
    if any(str((snap.to_dict() or {}).get("transaction_id", "")).strip().casefold() == txn_id.casefold() for snap in duplicate_docs):
        await update.effective_message.reply_text("❌ এই Transaction ID আগেই পাঠানো হয়েছে। এই চেষ্টাটিও গণনা হয়েছে; আলাদা সঠিক ID দিন।")
        return

    settings = get_settings()
    ref = db.collection(COL_PAYMENTS).document()
    payload = {
        "user_id": user_id, "telegram_id": user_id, "username": safe_username(user),
        "first_name": clean_text(user.first_name, 100), "package_id": package.get("id"),
        "package_label": package.get("label"), "credits": credits_float(package.get("credits", 0)),
        "price": int(package.get("price", 0)), "transaction_id": txn_id,
        "payment_method": method, "payment_action": payment_action,
        "payment_number": clean_text(number, 40),
        "status": "pending", "created_at": now(), "updated_at": now(),
    }
    ref.set(payload)
    audit("payment_request_created", user_id, {"payment_id": ref.id, "package_id": package.get("id"), "method": method})
    context.user_data.clear()
    display_name = escape_markdown(clean_text(user.full_name, 120), version=1)
    uname = escape_markdown(safe_username(user) or "no_username", version=1)
    group_message = (
        "🧾 *NEW CREDIT PURCHASE REQUEST*\n━━━━━━━━━━━━━━━━━\n"
        f"🆔 Request: `{ref.id}`\n👤 User: {display_name} (@{uname})\n🪪 Telegram ID: `{user_id}`\n"
        f"📦 Package: {escape_markdown(clean_text(package.get('label'), 120), version=1)}\n"
        f"💳 Amount: *৳{int(package.get('price', 0))}*\n📱 Method: *{method.title()}*\n"
        f"📱 Action: *{payment_action}*\n"
        f"📱 Payment Number: `{clean_text(number,40)}`\n🧾 Transaction ID: `{txn_id}`\n"
        "━━━━━━━━━━━━━━━━━\nVerify payment manually before approval. Credits will be added only once."
    )
    review_markup = InlineKeyboardMarkup([[InlineKeyboardButton("✅ Approve & Add Credits", callback_data=f"pay:approve:{ref.id}", style="success"), InlineKeyboardButton("❌ Reject", callback_data=f"pay:reject:{ref.id}", style="danger")]])
    review_chat = clean_text(settings.get("payment_review_chat_id") or PAYMENT_REVIEW_CHAT_ID, 100)
    notified = False
    try:
        await context.bot.send_message(chat_id=review_chat, text=group_message, parse_mode="Markdown", reply_markup=review_markup)
        notified = True
    except Exception as exc:
        notify_error = clean_text(exc, 400)
        ref.update({"review_notify_error": notify_error, "updated_at": now()})
        try:
            await context.bot.send_message(ADMIN_ID, f"⚠️ Payment request {ref.id} গ্রুপে পাঠানো যায়নি। Review group এবং bot-এর permission পরীক্ষা করুন।")
        except Exception:
            pass
    confirmation = (
        "✅ পেমেন্ট অনুরোধ সংরক্ষণ করা হয়েছে।\n"
        f"🆔 Request ID: {ref.id}\n"
        "⏳ পেমেন্ট যাচাইয়ের অপেক্ষায় আছে। অ্যাডমিন অনুমোদন দিলে ক্রেডিট স্বয়ংক্রিয়ভাবে যোগ হবে।"
    )
    copy_markup = InlineKeyboardMarkup([[InlineKeyboardButton("📋 Request ID কপি করুন", copy_text=CopyTextButton(text=ref.id), style="success")]])
    await update.effective_message.reply_text(confirmation, reply_markup=copy_markup)
    await update.effective_message.reply_text("নিচের মেনু থেকে পরবর্তী সুবিধা বেছে নিন।", reply_markup=main_keyboard(user_id))

async def local_stats() -> dict:
    user_docs = list(db.collection(COL_USERS).stream())
    calls = list(db.collection(COL_CALLS).stream())
    valid_users = []
    for snap in user_docs:
        user = snap.to_dict() or {}
        uid = telegram_id_for_record(snap)
        if uid is None:
            continue
        name = clean_text((str(user.get("first_name", "")) + " " + str(user.get("last_name", ""))).strip(), 120) or "User"
        valid_users.append({"user_id": uid, "name": name, "balance": credits_float(user.get("balance", 0))})
    credits = sum(item["balance"] for item in valid_users)
    statuses = [str((snap.to_dict() or {}).get("status", "")).lower() for snap in calls]
    success = sum(1 for status in statuses if status in {"success", "succeeded", "completed"})
    failed = sum(1 for status in statuses if status == "failed")
    return {
        "users": len(valid_users), "calls": len(calls), "success": success, "failed": failed,
        "credits": credits,
        "top_users": sorted([item for item in valid_users if item["balance"] > 0], key=lambda item: item["balance"], reverse=True)[:10],
    }

def admin_keyboard_markup():
    settings = get_settings()
    daily_state = "ON ✅" if settings.get("daily_bonus_enabled", False) else "OFF ⛔"
    rows = [
        [InlineKeyboardButton("📈 Overview", callback_data="admin:overview", style="primary"), InlineKeyboardButton("👥 Users", callback_data="admin:users", style="primary")],
        [InlineKeyboardButton("💳 Add Credits", callback_data="admin:addcredits", style="success"), InlineKeyboardButton("➖ Deduct Credits", callback_data="admin:deductcredits", style="danger")],
        [InlineKeyboardButton("🚫 Block User", callback_data="admin:block", style="danger"), InlineKeyboardButton("✅ Unblock User", callback_data="admin:unblock", style="success")],
        [InlineKeyboardButton("🎁 Create Redeem", callback_data="admin:createcode", style="success"), InlineKeyboardButton("📜 Redeem Codes", callback_data="admin:codes", style="primary")],
        [InlineKeyboardButton("💰 Payments", callback_data="admin:payments", style="success"), InlineKeyboardButton("📞 Call Logs", callback_data="admin:calls", style="primary")],
        [InlineKeyboardButton("📣 Broadcast", callback_data="admin:broadcast", style="primary"), InlineKeyboardButton("⚙️ Settings", callback_data="admin:settings", style="primary")],
        [InlineKeyboardButton("💗 bKash Number", callback_data="admin:bkash_number", style="success"), InlineKeyboardButton("🧡 Nagad Number", callback_data="admin:nagad_number", style="danger")],
        [InlineKeyboardButton("🚀 Rocket Number", callback_data="admin:rocket_number", style="primary"), InlineKeyboardButton("⚙️ Payment Actions", callback_data="admin:paymentactions", style="primary")],
        [InlineKeyboardButton(f"bKash {'ON' if settings.get('bkash_enabled', True) else 'OFF'}", callback_data="admin:toggle_payment:bkash", style="success" if settings.get('bkash_enabled', True) else "danger"), InlineKeyboardButton(f"Nagad {'ON' if settings.get('nagad_enabled', True) else 'OFF'}", callback_data="admin:toggle_payment:nagad", style="success" if settings.get('nagad_enabled', True) else "danger"), InlineKeyboardButton(f"Rocket {'ON' if settings.get('rocket_enabled', False) else 'OFF'}", callback_data="admin:toggle_payment:rocket", style="success" if settings.get('rocket_enabled', False) else "danger")],
        [InlineKeyboardButton(f"🎁 Daily Bonus: {daily_state}", callback_data="admin:toggle_daily", style="success" if settings.get("daily_bonus_enabled", False) else "danger")],
        [InlineKeyboardButton(f"🛠 Call Maintenance: {'ON' if settings.get('maintenance', False) else 'OFF'}", callback_data="admin:toggle_maintenance", style="danger" if settings.get("maintenance", False) else "success")],
        [InlineKeyboardButton("📦 Edit Packages", callback_data="admin:packages", style="primary"), InlineKeyboardButton("🔎 User Info", callback_data="admin:userinfo", style="primary")],
        [InlineKeyboardButton("🎙️ Voice Templates", callback_data="admin:templates", style="success")],
        [InlineKeyboardButton("🔌 Provider", callback_data="admin:provider", style="primary"), InlineKeyboardButton("🛡 Safety", callback_data="admin:safety", style="danger")],
        [InlineKeyboardButton("⬅️ Home", callback_data="menu:home", style="primary")],
    ]
    return InlineKeyboardMarkup(rows)


async def admin_menu(query):
    await edit_or_send(query, "🛠 *Admin Panel*\n\nক্রেডিট, পেমেন্ট, ব্যবহারকারী, রেফারেল, বোনাস ও কলের সেটিংস পরিচালনা করুন।", admin_keyboard_markup())

async def admin_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    data = query.data or ""
    action = data.split(":", 1)[1]
    if action == "overview":
        stats = await local_stats()
        provider = await account_api("balance")
        balance = ((provider.get("data") or {}).get("main_balance", "N/A"))
        text = (
            "📈 *Admin Overview*\n\n"
            f"Users: *{stats['users']}*\n"
            f"Calls: *{stats['calls']}*\n"
            f"Success: *{stats['success']}*\n"
            f"Failed: *{stats['failed']}*\n"
            f"Credits circulation: *{format_balance(stats['credits'])}*\n"
            f"Provider main balance: *{balance}*"
        )
        await edit_or_send(query, text, back_button())
    elif action == "users":
        stats = await local_stats()
        users = list(db.collection(COL_USERS).limit(15).stream())
        lines = [f"👥 *Users ({stats['users']})*\n"]
        for snap in users:
            u = snap.to_dict() or {}
            lines.append(
                f"• `{u.get('user_id')}` — @{escape_markdown(clean_text(u.get('username') or 'none', 100), version=1)} — {format_balance(u.get('balance', 0))}"
            )
        await edit_or_send(query, "\n".join(lines), back_button())
    elif action == "addcredits":
        context.user_data["state"] = "admin_addcredits"
        await edit_or_send(query, "💳 Send: `USER_ID_OR_PRIVATE_CHAT_ID AMOUNT`\nExample: `123456789 25`\nTarget user must have started this bot.", back_button())
    elif action == "deductcredits":
        context.user_data["state"] = "admin_deductcredits"
        await edit_or_send(query, "➖ Send: `USER_ID_OR_PRIVATE_CHAT_ID AMOUNT`\nExample: `123456789 5`", back_button())
    elif action == "block":
        context.user_data["state"] = "admin_block"
        await edit_or_send(query, "🚫 Send the numeric Telegram User ID / private Chat ID to block.", back_button())
    elif action == "unblock":
        context.user_data["state"] = "admin_unblock"
        await edit_or_send(query, "✅ Send the numeric Telegram User ID / private Chat ID to unblock.", back_button())
    elif action == "createcode":
        context.user_data["state"] = "admin_createcode"
        await edit_or_send(
            query,
            "🎁 Custom Redeem Code\n\nSend: `CODE CREDITS MAX_USES DAYS`\nExample: `EMON50 50 100 30`\nCODE: letters, numbers, _ or - (3–32 chars).\nMAX_USES=0 means unlimited; DAYS=0 means never expires.",
            back_button(),
        )
    elif action == "codes":
        docs = list(db.collection(COL_CODES).order_by("created_at", direction=firestore.Query.DESCENDING).limit(10).stream())
        if not docs:
            await edit_or_send(query, "📜 No redeem codes yet.", back_button())
            return
        lines = ["📜 *Redeem Codes*\nTap a delete button to remove a code.\n"]
        rows = []
        for s in docs:
            c = s.to_dict() or {}
            code = clean_text(c.get("code", "unknown"), 40)
            uses = _safe_int(c.get("uses", 0)) or 0
            max_uses = _safe_int(c.get("max_uses", 0)) or 0
            lines.append(
                f"`{escape_markdown(code, version=1)}` — {credits_float(c.get('credits', 0)):g} credits — "
                f"{uses}/{max_uses if max_uses else '∞'} — {'ON' if c.get('active', True) else 'OFF'}"
            )
            rows.append([InlineKeyboardButton(f"🗑 Delete {code[:24]}", callback_data=f"admin:deletecode:{s.id}", style="danger")])
        rows.append([InlineKeyboardButton("⬅️ Back to Admin", callback_data="admin:menu", style="primary")])
        await edit_or_send(query, "\n".join(lines), InlineKeyboardMarkup(rows))
    elif action.startswith("deletecode:"):
        record_id = action.split(":", 1)[1]
        code_ref = db.collection(COL_CODES).document(record_id)
        code_snap = code_ref.get()
        if not code_snap.exists:
            await edit_or_send(query, "ℹ️ Ei redeem code already deleted or missing.", admin_keyboard_markup(), parse_mode=None)
            return
        code_data = code_snap.to_dict() or {}
        code_name = clean_text(code_data.get("code", record_id), 40)
        code_ref.delete()
        audit("redeem_code_deleted", query.from_user.id, {"code": code_name, "record_id": record_id})
        await edit_or_send(query, f"✅ Redeem code deleted: {code_name}", admin_keyboard_markup(), parse_mode=None)
    elif action == "payments":
        docs = list(
            db.collection(COL_PAYMENTS)
            .where("status", "==", "pending")
            .limit(25)
            .stream()
        )
        docs.sort(key=lambda s: str((s.to_dict() or {}).get("created_at") or ""))
        docs = docs[:10]
        if not docs:
            await edit_or_send(query, "💰 No pending payments.", back_button())
            return
        rows = []
        text = "💰 *Pending Payments*\n\n"
        for s in docs:
            p = s.to_dict() or {}
            text += (
                f"ID: `{s.id}`\n"
                f"User: `{p.get('user_id')}`\n"
                f"Txn: `{p.get('transaction_id')}`\n"
                f"Credits: *{credits_float(p.get('credits', 0)):g}*\n\n"
            )
            rows.append([
                InlineKeyboardButton(f"✅ {str(p.get('user_id'))}", callback_data=f"pay:approve:{s.id}", style="success"),
                InlineKeyboardButton("❌ Reject", callback_data=f"pay:reject:{s.id}", style="danger"),
            ])
        rows.append([InlineKeyboardButton("⬅️ Back", callback_data="admin:menu")])
        await edit_or_send(query, text, InlineKeyboardMarkup(rows))
    elif action == "calls":
        docs = list(db.collection(COL_CALLS).order_by("created_at", direction=firestore.Query.DESCENDING).limit(10).stream())
        lines = ["📞 *Recent Call Logs*\n"]
        for s in docs:
            c = s.to_dict() or {}
            lines.append(
                f"`{str(c.get('user_id'))}` — `{clean_text(c.get('number',''), 30)}` — "
                f"{str(c.get('status'))} — {str(c.get('mode'))} — {clean_text(c.get('template_title') or '', 50)}"
            )
            if c.get("audio_source"):
                lines.append(f"  🎙️ Voice source: {clean_text(c.get('audio_source'), 30)}")
            if c.get("recording_url"):
                lines.append("🎧 Recording URL stored.")
        await edit_or_send(query, "\n".join(lines), back_button())
    elif action == "templates":
        await show_voice_templates(query, context, admin_view=True)
    elif action == "template_create_global":
        context.user_data["state"] = "voice_template_upload_global"
        context.user_data.pop("pending_voice_template", None)
        await edit_or_send(query, "🎙️ সবার জন্য ভয়েস টেমপ্লেট তৈরি করতে MP3/WAV/OGG ফাইল অথবা ভয়েস মেসেজ পাঠান। এরপর টেমপ্লেটের নাম দিতে হবে।", None, parse_mode=None)
    elif action.startswith("template_delete:"):
        template_id = action.split(":", 1)[1]
        template_ref = db.collection(COL_VOICE_TEMPLATES).document(template_id)
        snapshot = template_ref.get()
        template = snapshot.to_dict() if snapshot.exists else {}
        if not template or str(template.get("scope", "personal")).lower() != "global":
            await edit_or_send(query, "এই বৈশ্বিক টেমপ্লেটটি পাওয়া যায়নি।", admin_keyboard_markup(), parse_mode=None)
            return
        template_ref.delete()
        audit("voice_template_deleted", query.from_user.id, {"template_id": template_id, "title": template.get("title")})
        await show_voice_templates(query, context, admin_view=True)
    elif action == "broadcast":
        context.user_data["state"] = "admin_broadcast"
        await edit_or_send(query, "📣 Send the message to broadcast to all users.", back_button())
    elif action == "toggle_maintenance":
        settings = get_settings()
        enabled = not bool(settings.get("maintenance", False))
        save_settings({"maintenance": enabled})
        audit("maintenance_toggled", query.from_user.id, {"enabled": enabled})
        status_label = "ON — calls disabled" if enabled else "OFF — calls enabled"
        await edit_or_send(query, f"🛠 Call maintenance: *{status_label}*. Other features will remain available.", InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Admin Panel", callback_data="admin:menu", style="primary")]]))
    elif action == "packages":
        packages = get_settings().get("packages", [])
        lines = ["📦 *Package Setup*", "", "Current packages:"]
        for pkg in packages:
            lines.append(f"{clean_text(pkg.get('id'), 20)} — {credits_float(pkg.get('credits', 0)):g} credits — {int(pkg.get('price', 0))} TK")
        lines += ["", "Send: `PACKAGE_ID PRICE CREDITS`", "Example: `p50 60 50`"]
        context.user_data["state"] = "admin_package"
        await edit_or_send(query, "\n".join(lines), back_button())
    elif action == "userinfo":
        context.user_data["state"] = "admin_userinfo"
        await edit_or_send(query, "🔎 Send numeric Telegram USER_ID or private CHAT_ID.", back_button())
    elif action == "settings":
        s = get_settings()
        text = (
            "⚙️ *Settings*\n\n"
            f"Maintenance: *{s.get('maintenance')}*\n"
            f"Call cost: *{credits_float(s.get('call_credit_cost', 1)):g}*\n"
            f"Daily limit: *{_safe_int(s.get('daily_call_limit', 20)) if _safe_int(s.get('daily_call_limit', 20)) is not None else 20}*\n"
            f"Cooldown: *{_safe_int(s.get('call_cooldown_seconds', 15)) if _safe_int(s.get('call_cooldown_seconds', 15)) is not None else 15}s*\n"
            f"Referral bonus: *{credits_float(s.get('referral_bonus', 0)):g}*\n"
            f"Daily bonus: *{credits_float(s.get('daily_bonus', 0)):g}*\n"
            f"Daily bonus enabled: *{bool(s.get('daily_bonus_enabled', False))}*\n"
            f"bKash number: `{clean_text(s.get('bkash_number', ''), 40) or 'Not set'}`\n"
            f"Nagad number: `{clean_text(s.get('nagad_number', ''), 40) or 'Not set'}`\n"
            f"Rocket number: `{clean_text(s.get('rocket_number', ''), 40) or 'Not set'}`\n"
            f"Payment methods: `bKash={bool(s.get('bkash_enabled'))}, Nagad={bool(s.get('nagad_enabled'))}, Rocket={bool(s.get('rocket_enabled'))}`\n"
            f"Review group: `{clean_text(s.get('payment_review_chat_id', PAYMENT_REVIEW_CHAT_ID), 100)}`\n"
            f"Required channel: `{clean_text(s.get('required_channel', REQUIRED_CHANNEL_USERNAME), 100)}`\n\n"
            "Use /help for all settings and commands."
        )
        rows = [
            [InlineKeyboardButton("💗 Set bKash Number", callback_data="admin:bkash_number")],
            [InlineKeyboardButton("🧡 Set Nagad Number", callback_data="admin:nagad_number")],
            [InlineKeyboardButton("🚀 Set Rocket Number", callback_data="admin:rocket_number")],
            [InlineKeyboardButton("⚙️ Payment Actions", callback_data="admin:paymentactions")],
            [InlineKeyboardButton("🎁 Toggle Daily Bonus", callback_data="admin:toggle_daily")],
            [InlineKeyboardButton("⬅️ Back to Admin", callback_data="admin:menu", style="primary")],
        ]
        await edit_or_send(query, text, InlineKeyboardMarkup(rows))
    elif action == "paymentactions":
        settings = get_settings()
        rows = []
        action_options = [("payment", "Payment"), ("send_money", "Send Money"), ("cash_out", "Cash Out")]
        for method_key, method_name in (("bkash", "bKash"), ("nagad", "Nagad"), ("rocket", "Rocket")):
            active = str(settings.get(f"{method_key}_action", "send_money"))
            rows.append([InlineKeyboardButton(f"{method_name}: {label} {'✅' if active == value else ''}", callback_data=f"admin:payment_action:{method_key}:{value}", style="success" if active == value else "primary") for value, label in action_options])
        rows.append([InlineKeyboardButton("⬅️ Admin Panel", callback_data="admin:menu", style="primary")])
        await edit_or_send(query, "প্রতিটি পেমেন্ট মাধ্যমে কোন ধরনের লেনদেন হবে তা বেছে নিন:", InlineKeyboardMarkup(rows), parse_mode=None)
    elif action.startswith("toggle_payment:"):
        method_key = action.split(":", 1)[1]
        if method_key not in {"bkash", "nagad", "rocket"}:
            await edit_or_send(query, "পেমেন্ট মাধ্যম সঠিক নয়।", admin_keyboard_markup(), parse_mode=None)
            return
        settings = get_settings()
        key = f"{method_key}_enabled"
        enabled = not bool(settings.get(key, method_key != "rocket"))
        if enabled and not clean_text(settings.get(f"{method_key}_number"), 40):
            await edit_or_send(query, f"আগে {method_key.title()}-এর পেমেন্ট নম্বর সেট করুন, তারপর চালু করুন।", admin_keyboard_markup(), parse_mode=None)
            return
        save_settings({key: enabled})
        audit("payment_method_toggled", query.from_user.id, {"method": method_key, "enabled": enabled})
        await edit_or_send(query, f"✅ {method_key.title()} payment {'চালু' if enabled else 'বন্ধ'} করা হয়েছে।", admin_keyboard_markup(), parse_mode=None)
    elif action.startswith("payment_action:"):
        parts = action.split(":")
        if len(parts) != 3 or parts[1] not in {"bkash", "nagad", "rocket"} or parts[2] not in {"payment", "send_money", "cash_out"}:
            await edit_or_send(query, "পেমেন্ট অ্যাকশন সঠিক নয়।", admin_keyboard_markup(), parse_mode=None)
            return
        method_key, action_value = parts[1], parts[2]
        save_settings({f"{method_key}_action": action_value})
        audit("payment_action_changed", query.from_user.id, {"method": method_key, "action": action_value})
        await edit_or_send(query, f"✅ {method_key.title()} action set to {action_value.replace('_', ' ')}.", admin_keyboard_markup(), parse_mode=None)
    elif action in {"paymentnumber", "bkash_number", "nagad_number", "rocket_number"}:
        method = "bkash" if action == "paymentnumber" else action.removesuffix("_number")
        key = f"{method}_number"
        context.user_data["state"] = f"admin_{method}_number"
        current_number = clean_text(get_settings().get(key, ""), 40) or "Not set"
        await edit_or_send(query, f"💳 *{method.title()} নম্বর সেট করুন*\n\nবর্তমান নম্বর: `{current_number}`\n\nনতুন নম্বর দিন (৮–১৫ অঙ্ক), অথবা মাধ্যম বন্ধ করতে `OFF` লিখুন।", back_button())
    elif action == "toggle_daily":
        settings = get_settings()
        enabled = not bool(settings.get("daily_bonus_enabled", False))
        save_settings({"daily_bonus_enabled": enabled})
        audit("daily_bonus_toggled", query.from_user.id, {"enabled": enabled})
        status = "enabled ✅" if enabled else "disabled ⛔"
        await edit_or_send(
            query,
            f"🎁 Daily Bonus is now *{status}*.\n\n{'The Daily Bonus button will appear for users.' if enabled else 'The Daily Bonus button has been hidden from users.'}",
            InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Admin Panel", callback_data="admin:menu")]]),
        )
    elif action == "provider":
        balance = await account_api("balance")
        profile = await account_api("profile")
        pricing = await account_api("pricing")
        bd = balance.get("data") or {}
        pd = profile.get("data") or {}
        pr = pricing.get("data") or {}
        text = (
            "🔌 *Provider*\n\n"
            f"Main Balance: `{bd.get('main_balance', 'N/A')}`\n"
            f"Call Balance: `{bd.get('call_balance', 'N/A')}`\n"
            f"Status: `{pd.get('status', 'N/A')}`\n"
            f"Voice Call Cost: `{pr.get('voice_call_cost', 'N/A')}`\n"
            f"Currency: `{pr.get('currency', bd.get('currency', 'N/A'))}`"
        )
        await edit_or_send(query, text, back_button())
    elif action == "safety":
        text = (
            "🛡 *Safety Controls*\n\n"
            "The bot includes daily limits, cooldowns, blocked accounts, and audit logs.\n"
            "Call recording is only supported when the upstream provider exposes a recording URL or webhook."
        )
        await edit_or_send(query, text, back_button())
    elif action == "menu":
        await admin_menu(query)


async def admin_payment_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if not query or not is_admin(query.from_user.id):
        if query:
            await query.answer("Admin only.", show_alert=True)
        return
    parts = (query.data or "").split(":")
    if len(parts) != 3 or parts[1] not in {"approve", "reject"}:
        await query.answer("Invalid payment action.", show_alert=True)
        return

    action, payment_id = parts[1], parts[2]
    payment_ref = db.collection(COL_PAYMENTS).document(payment_id)
    transaction = db.transaction()

    try:
        @firestore.transactional
        def process_payment(transaction):
            payment_snap = payment_ref.get(transaction=transaction)
            if not payment_snap.exists:
                raise ValueError("Payment request not found.")
            payment = payment_snap.to_dict() or {}
            if payment.get("status") != "pending":
                raise ValueError("This payment has already been processed.")
            user_id = _safe_int(payment.get("user_id"))
            if user_id is None or user_id == 0:
                raise ValueError("Payment record has no valid Telegram user ID.")
            user_document = user_ref(user_id)
            user_snap = user_document.get(transaction=transaction)
            if not user_snap.exists:
                raise ValueError("User account not found.")
            user_data = user_snap.to_dict() or {}
            current_balance = credits_float(user_data.get("balance", 0))
            amount = credits_float(payment.get("credits", 0))
            if action == "approve":
                if amount <= 0:
                    raise ValueError("Invalid credit amount.")
                new_balance = credits_float(current_balance + amount)
                paid_price = _safe_int(payment.get("price", 0)) or 0
                new_tier = subscription_tier_for_price(paid_price)
                transaction.update(user_document, {
                    "balance": new_balance,
                    "updated_at": now(),
                    "subscription_tier": new_tier if new_balance > 0 else "INACTIVE",
                    "subscription_paid_tier": new_tier,
                    "subscription_paid_price": paid_price,
                    "subscription_exhausted": new_balance <= 0,
                    "subscription_activated_at": now(),
                })
                transaction.create(ledger_ref_for(user_id, "purchase", payment_id), {
                    "user_id": user_id, "type": "purchase", "amount": amount,
                    "before": current_balance, "after": new_balance,
                    "reference": payment_id, "created_at": now(),
                })
                transaction.update(payment_ref, {
                    "status": "approved",
                    "approved_by": ADMIN_ID,
                    "approved_at": now(),
                    "updated_at": now(),
                })
            else:
                transaction.update(payment_ref, {
                    "status": "rejected",
                    "rejected_by": ADMIN_ID,
                    "rejected_at": now(),
                    "updated_at": now(),
                })
            return user_id, amount, (credits_float(current_balance + amount) if action == "approve" else current_balance)

        user_id, amount, balance_after = process_payment(transaction)
        audit("payment_approved" if action == "approve" else "payment_rejected", ADMIN_ID, {
            "payment_id": payment_id,
            "user_id": user_id,
            "credits": amount,
        })
        if action == "approve":
            try:
                await context.bot.send_message(
                    user_id,
                    f"✅ Payment approved!\n\n📦 Credits added: +{amount:g}\n💳 New balance: {balance_after:g}\n⭐ Subscription: {subscription_tier_for_price((db.collection(COL_PAYMENTS).document(payment_id).get().to_dict() or {}).get('price', 0))}",
                    reply_markup=main_keyboard(user_id),
                )
            except Exception:
                pass
            await query.answer("Approved; credits added once.", show_alert=True)
            final_text = (query.message.text or "Payment request") + f"\n\n✅ APPROVED by {ADMIN_ID} — +{amount:g} credits added."
        else:
            try:
                await context.bot.send_message(user_id, "❌ Your credit purchase request was rejected. Please check the transaction ID or contact support.")
            except Exception:
                pass
            await query.answer("Payment rejected.", show_alert=True)
            final_text = (query.message.text or "Payment request") + f"\n\n❌ REJECTED by {ADMIN_ID}."
        try:
            await query.edit_message_text(final_text, parse_mode=None, reply_markup=None)
        except Exception:
            try:
                await query.edit_message_reply_markup(reply_markup=None)
            except Exception:
                pass
    except Exception as exc:
        await query.answer(clean_text(exc, 180), show_alert=True)


async def handle_admin_state(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str):
    admin_id = update.effective_user.id
    state = context.user_data.get("state")

    if state in {"admin_bkash_number", "admin_nagad_number", "admin_rocket_number", "admin_payment_number"}:
        method = "rocket" if state == "admin_rocket_number" else "nagad" if state == "admin_nagad_number" else "bkash"
        if text.strip().lower() in {"off", "disable", "disabled", "none"}:
            digits = ""
        else:
            digits = re.sub(r"\D+", "", text)
            if not 8 <= len(digits) <= 15:
                await update.effective_message.reply_text("❌ সঠিক নম্বর দিন (৮–১৫ অঙ্ক), অথবা এই পেমেন্ট মাধ্যম বন্ধ করতে OFF লিখুন।")
                return
        save_settings({f"{method}_number": digits, f"{method}_enabled": bool(digits), **({"payment_number": digits} if digits else {})})
        audit("payment_number_changed", admin_id, {"method": method, "payment_number": digits})
        context.user_data.clear()
        await update.effective_message.reply_text(f"✅ {method.title()} পেমেন্ট নম্বর আপডেট হয়েছে: `{digits or 'বন্ধ'}`", parse_mode="Markdown", reply_markup=main_keyboard(admin_id))
        return

    if state in {"admin_addcredits", "admin_deductcredits"}:
        parts = text.split()
        if len(parts) != 2:
            await update.effective_message.reply_text("Format: USER_ID_OR_PRIVATE_CHAT_ID AMOUNT\nExample: `123456789 25`", parse_mode="Markdown")
            return
        target_id = _safe_int(re.sub(r"^(user_id|userid|chat_id|chatid|user|chat):", "", parts[0], flags=re.I))
        amount = credits_float(parts[1])
        if target_id is None or target_id == 0 or amount <= 0:
            await update.effective_message.reply_text("❌ সঠিক সংখ্যার Telegram User ID/Chat ID এবং শূন্যের চেয়ে বেশি পরিমাণ দিন।")
            return
        target_ref = user_ref(target_id)
        if not target_ref.get().exists:
            await update.effective_message.reply_text("❌ এই ID-এর অ্যাকাউন্ট পাওয়া যায়নি। আগে ব্যবহারকারীকে /start করতে বলুন, তারপর ক্রেডিট যোগ করুন।")
            return
        operation_ref = f"admin:{admin_id}:{update.effective_message.message_id}:{target_id}"
        try:
            if state == "admin_addcredits":
                after = add_credits(target_id, amount, "admin_add", operation_ref)
                action = "added"
            else:
                after = deduct_credits(target_id, amount, "admin_deduct", operation_ref)
                action = "deducted"
            audit(state, admin_id, {"target_id": target_id, "amount": amount})
            try:
                await context.bot.send_message(target_id, f"💳 Admin {amount:g} credits {action} koreche. New balance: {after:g}.")
            except Exception:
                pass
            await update.effective_message.reply_text(f"✅ Done. Target: `{target_id}`\nNew balance: `{after:g}`", parse_mode="Markdown", reply_markup=main_keyboard(admin_id))
            context.user_data.clear()
        except Exception as exc:
            await update.effective_message.reply_text(f"❌ {clean_text(exc, 400)}")
        return

    if state in {"admin_block", "admin_unblock"}:
        raw = text.strip()
        target_id = _safe_int(re.sub(r"^(user_id|userid|chat_id|chatid|user|chat):", "", raw, flags=re.I))
        if target_id is None or target_id == 0:
            await update.effective_message.reply_text("❌ সংখ্যায় Telegram User ID অথবা ব্যক্তিগত Chat ID পাঠান।")
            return
        target_ref = user_ref(target_id)
        if not target_ref.get().exists:
            await update.effective_message.reply_text("❌ User account not found. User-ke age bot start korte bolo.")
            return
        blocked = state == "admin_block"
        target_ref.update({"is_blocked": blocked, "updated_at": now()})
        audit("user_blocked" if blocked else "user_unblocked", admin_id, {"target_id": target_id})
        try:
            await context.bot.send_message(target_id, "⛔ অ্যাডমিন আপনার অ্যাকাউন্ট ব্লক করেছেন।" if blocked else "✅ অ্যাডমিন আপনার অ্যাকাউন্ট আনব্লক করেছেন।")
        except Exception:
            pass
        context.user_data.clear()
        await update.effective_message.reply_text(f"✅ User `{target_id}` {'blocked' if blocked else 'unblocked'}.", parse_mode="Markdown", reply_markup=main_keyboard(admin_id))
        return

    if state == "admin_createcode":
        parts = text.split()
        if len(parts) not in {3, 4}:
            await update.effective_message.reply_text(
                "Format: CODE CREDITS MAX_USES DAYS\nExample: EMON50 50 100 30\nFor random code, send: CREDITS MAX_USES DAYS.\nMAX_USES=0 unlimited; DAYS=0 never expires."
            )
            return
        try:
            if len(parts) == 4:
                code = parts[0].strip().upper()
                amount = credits_float(parts[1])
                max_uses = int(parts[2])
                days = int(parts[3])
                if not re.fullmatch(r"[A-Z0-9_-]{3,32}", code):
                    raise ValueError("Custom code must be 3–32 characters: A-Z, 0-9, _ or -.")
            else:
                amount = credits_float(parts[0])
                max_uses = int(parts[1])
                days = int(parts[2])
                alphabet = string.ascii_uppercase + string.digits
                code = "CALL-" + "".join(secrets.choice(alphabet) for _ in range(10))
            if amount <= 0 or max_uses < 0 or days < 0:
                raise ValueError("Credits must be positive; MAX_USES and DAYS must be zero or greater.")
            existing_code = any(
                str((item.to_dict() or {}).get("code", "")).strip().upper() == code
                for item in db.collection(COL_CODES).stream()
            )
            if existing_code:
                raise ValueError("This redeem code already exists. Choose another custom code.")
            expires = now() + timedelta(days=days) if days else None
            code_ref = db.collection(COL_CODES).document()
            code_ref.set({
                "code": code, "credits": amount, "max_uses": max_uses, "uses": 0,
                "used_by": [], "active": True, "expires_at": expires,
                "created_by": admin_id, "created_at": now(), "updated_at": now(),
            })
            try:
                audit("redeem_code_created", admin_id, {"code": code, "credits": amount, "max_uses": max_uses, "days": days, "document_id": code_ref.id})
            except Exception:
                pass
            await update.effective_message.reply_text(
                "✅ Redeem code created successfully!\n"
                f"Code: {code}\nCredits: {amount:g}\n"
                f"Max uses: {'Unlimited' if max_uses == 0 else max_uses}\n"
                f"Expires: {'Never' if not days else iso(expires)}\n"
                f"কোডের রেকর্ড: {code_ref.id}\n\nAdmin Panel → Redeem Codes থেকে এটি মুছে ফেলতে পারবেন।",
                reply_markup=main_keyboard(admin_id),
            )
            context.user_data.clear()
        except Exception as exc:
            # Don't hide the actual Firebase/database error behind a misleading "invalid values" response.
            await update.effective_message.reply_text(
                f"❌ Redeem code creation failed: {clean_text(exc, 600)}\nPlease retry or check Firebase RTDB permissions."
            )
        return

    if state == "admin_package":
        parts = text.split()
        if len(parts) != 3:
            await update.effective_message.reply_text("Format: PACKAGE_ID PRICE CREDITS\nExample: p50 60 50")
            return
        package_id = clean_text(parts[0], 20)
        price = _safe_int(parts[1])
        credits = credits_float(parts[2])
        if price is None or price < 1 or credits <= 0:
            await update.effective_message.reply_text("❌ Price must be positive and credits must be greater than zero.")
            return
        settings = get_settings()
        packages = list(settings.get("packages", []))
        found = False
        for package in packages:
            if str(package.get("id")) == package_id:
                package["price"] = price
                package["credits"] = credits
                package["label"] = f"📞 {credits:g} Calls — {price} TK"
                found = True
                break
        if not found:
            await update.effective_message.reply_text("❌ Package ID পাওয়া যায়নি। Admin Panel → Edit Packages থেকে ID দেখুন।")
            return
        save_settings({"packages": packages})
        audit("package_updated", admin_id, {"package_id": package_id, "price": price, "credits": credits})
        context.user_data.clear()
        await update.effective_message.reply_text(f"✅ Package updated: {package_id} — {credits:g} credits — {price} TK", reply_markup=main_keyboard(admin_id))
        return

    if state == "admin_userinfo":
        target_id = _safe_int(re.sub(r"^(user_id|userid|chat_id|chatid|user|chat):", "", text.strip(), flags=re.I))
        if target_id is None or target_id == 0:
            await update.effective_message.reply_text("❌ সংখ্যায় Telegram User ID অথবা Chat ID পাঠান।")
            return
        target_ref = user_ref(target_id)
        snap = target_ref.get()
        if not snap.exists:
            await update.effective_message.reply_text("❌ User record paoa jayni. User-ke bot /start korte bolo.")
            return
        user = snap.to_dict() or {}
        tier = subscription_for_profile(user)
        details = (
            "🔎 USER INFO\n\n"
            f"Name: {clean_text((str(user.get('first_name','')) + ' ' + str(user.get('last_name',''))).strip(), 100) or 'User'}\n"
            f"Telegram ID: {target_id}\n"
            f"Username: @{clean_text(user.get('username') or 'none', 100)}\n"
            f"Balance: {format_balance(user.get('balance', 0))} credits\n"
            f"Subscription: {tier}\n"
            f"Total Calls: {_safe_int(user.get('total_calls', 0)) or 0}\n"
            f"Successful Calls: {_safe_int(user.get('successful_calls', 0)) or 0}\n"
            f"Failed Calls: {_safe_int(user.get('failed_calls', 0)) or 0}\n"
            f"Referrals: {_safe_int(user.get('referrals', 0)) or 0}\n"
            f"Blocked: {bool(user.get('is_blocked', False))}\n"
            f"Joined: {iso(user.get('created_at')) or 'Unknown'}"
        )
        context.user_data.clear()
        await update.effective_message.reply_text(details, reply_markup=main_keyboard(admin_id))
        return

    if state == "admin_broadcast":
        await do_broadcast(update, context, text)
        return

async def do_broadcast(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str):
    if not text:
        await update.effective_message.reply_text("বার্তাটি খালি। কিছু লেখা পাঠান।")
        return
    users = list(db.collection(COL_USERS).stream())
    ok = 0
    fail = 0
    skipped = 0
    for snap in users:
        u = snap.to_dict() or {}
        uid = telegram_id_for_record(snap)
        if uid is None or uid == 0:
            skipped += 1
            continue
        if u.get("is_blocked"):
            skipped += 1
            continue
        try:
            await context.bot.send_message(chat_id=uid, text=text)
            ok += 1
        except Exception:
            fail += 1
        await asyncio.sleep(0.04)
    audit("broadcast", update.effective_user.id, {"success": ok, "failed": fail, "skipped": skipped})
    context.user_data.clear()
    await update.effective_message.reply_text(f"📣 Broadcast complete.\n✅ Sent: {ok}\n❌ Failed: {fail}\n⏭ Skipped invalid/non-Telegram records: {skipped}", reply_markup=main_keyboard(update.effective_user.id))

async def admin_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not is_admin(update.effective_user.id):
        await update.effective_message.reply_text("⛔ Admin only.")
        return
    status = await channel_membership_status(context.bot, update.effective_user.id)
    if status is not True:
        await show_join_gate(update.effective_message, context, verification_error=status is None)
        return
    ensure_user(update.effective_user)
    await update.effective_message.reply_text("🛠 Admin Panel", reply_markup=main_keyboard(update.effective_user.id))


async def set_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not is_admin(update.effective_user.id):
        await update.effective_message.reply_text("Admin only.")
        return
    status = await channel_membership_status(context.bot, update.effective_user.id)
    if status is not True:
        await show_join_gate(update.effective_message, context, verification_error=status is None)
        return
    if len(context.args) < 2:
        await update.effective_message.reply_text("Usage: /set key value. Full list: /help")
        return
    key = context.args[0].strip().lower()
    value = " ".join(context.args[1:]).strip()
    numeric_keys = {
        "call_credit_cost": float, "daily_call_limit": int,
        "call_cooldown_seconds": int, "referral_bonus": float,
        "daily_bonus": float, "welcome_bonus": float,
        "purchase_limit_count": int, "purchase_limit_minutes": int,
    }
    if key in numeric_keys:
        try:
            value = numeric_keys[key](value)
            if value < 0 or (key == "call_credit_cost" and value <= 0):
                raise ValueError
        except Exception:
            await update.effective_message.reply_text("Invalid number. call_credit_cost must be greater than 0.")
            return
    elif key in {"maintenance", "daily_bonus_enabled", "bkash_enabled", "nagad_enabled", "rocket_enabled"}:
        value = value.lower() in {"1", "true", "on", "yes", "enabled"}
    elif key in {"payment_number", "bkash_number", "nagad_number", "rocket_number"}:
        method_key = "bkash" if key == "payment_number" else key.removesuffix("_number")
        if value.lower() in {"off", "disable", "disabled", "none"} and key != "payment_number":
            value = ""
            save_settings({f"{method_key}_enabled": False})
        else:
            value = re.sub(r"\D+", "", value)
            if not 8 <= len(value) <= 15:
                await update.effective_message.reply_text("Payment number must contain 8–15 digits (or use OFF to disable a method).")
                return
            save_settings({f"{method_key}_enabled": True})
        if key == "payment_number":
            key = "bkash_number"
    elif key in {"bkash_action", "nagad_action", "rocket_action"}:
        aliases = {"payment": "payment", "send_money": "send_money", "send money": "send_money", "cash_out": "cash_out", "cash out": "cash_out"}
        value = aliases.get(value.lower())
        if value is None:
            await update.effective_message.reply_text("Action must be payment, send_money, or cash_out.")
            return
    elif key in {"payment_review_chat_id", "required_channel"}:
        value = clean_text(value, 100)
        if not value:
            await update.effective_message.reply_text("Value cannot be empty.")
            return
        if key == "required_channel" and not value.startswith("@"):
            value = "@" + value.lstrip("/")
    elif key in {"brand_name", "support_text", "buy_text", "admin_notice", "support_contact_url"}:
        value = clean_text(value, 2000 if key != "support_contact_url" else 300)
        if key == "support_contact_url" and not (value.startswith("https://") or value.startswith("tg://")):
            await update.effective_message.reply_text("support_contact_url must start with https:// or tg://")
            return
    elif re.fullmatch(r"package_(p50|p100|p200|p300|p500)_(price|credits)", key):
        try:
            numeric_value = float(value)
            if numeric_value <= 0:
                raise ValueError
        except Exception:
            await update.effective_message.reply_text("Package price/credits must be positive.")
            return
        package_id, field = key[len("package_"):].rsplit("_", 1)
        settings = get_settings()
        packages = list(settings.get("packages", []))
        target_package = next((pkg for pkg in packages if str(pkg.get("id")) == package_id), None)
        if not target_package:
            await update.effective_message.reply_text("প্যাকেজটি পাওয়া যায়নি।")
            return
        target_package[field] = int(numeric_value) if field == "price" else credits_float(numeric_value)
        target_package["label"] = f"📞 {credits_float(target_package.get('credits', 0)):g} Calls — {int(target_package.get('price', 0))} TK"
        save_settings({"packages": packages})
        audit("package_updated", update.effective_user.id, {"package_id": package_id, field: target_package[field]})
        await update.effective_message.reply_text(f"✅ Updated {package_id}: {target_package['label']}")
        return
    else:
        await update.effective_message.reply_text("এই সেটিংটি সমর্থিত নয়। বিস্তারিত জানতে /help দেখুন।")
        return
    save_settings({key: value})
    audit("setting_changed", update.effective_user.id, {"key": key, "value": value})
    await update.effective_message.reply_text(f"✅ Updated `{key}`.", parse_mode="Markdown")

async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id if update.effective_user else 0
    lines = [
        "📘 Custom Call Bot সহায়িকা", "",
        "📞 ব্যবহারকারীর সুবিধা", "/start — ড্যাশবোর্ড খুলুন", "/call — কল শুরু করুন", "/cancel — চলমান কাজ বাতিল করুন",
        "Send Call, My Profile, Refer, LP Statistics, Buy Credits, Redeem, Call History ও Support বাটন ব্যবহার করুন।",
        "রেফারেল বোনাস: ১ ক্রেডিট। লিংক শেয়ার করে যোগ্য নতুন ব্যবহারকারী আনুন। অ্যাডমিন Daily Bonus চালু করলে বাটন দেখা যাবে।",
        "নির্ধারিত চ্যানেলে যোগ দেওয়া বাধ্যতামূলক।", "",
    ]
    if is_admin(uid):
        lines += [
            "🛠 অ্যাডমিন কমান্ড", "/admin — Admin Panel", "/help — এই সহায়িকা",
            "/addcredits USER_ID_OR_CHAT_ID AMOUNT", "/block USER_ID", "/unblock USER_ID", "/userinfo USER_ID",
            "",
            "প্যাকেজ পরিবর্তন: Admin Panel → Edit Packages → PACKAGE_ID PRICE CREDITS পাঠান; যেমন p50 60 50।",
            "সদস্যতার স্তর: ৫০+ টাকা = PRO, ১০০+ = MAX, ১৮০+ = VIP, ২৪০+ = ELITE, ৩৮০+ = LEGEND। ব্যালেন্স শূন্য হলে স্তর INACTIVE হবে।",
            "",
            "⚙️ /set দিয়ে সেটিংস পরিবর্তন করুন",
            "/set call_credit_cost 1", "/set daily_call_limit 20", "/set call_cooldown_seconds 15",
            "/set referral_bonus 1", "/set welcome_bonus 1", "/set daily_bonus 1",
            "/set daily_bonus_enabled true", "/set maintenance false",
            "/set bkash_number 01819202231", "/set nagad_number 01819202231", "/set rocket_number 01700000000",
            "/set nagad_number off — নগদ বন্ধ করতে", "/set rocket_action cash_out", "/set bkash_action send_money",
            "/set bkash_enabled false — বাটন বন্ধ করতে; true দিয়ে চালু করতে", "/set rocket_enabled true — নম্বর সেট করার পর মাধ্যম চালু করতে",
            "/set payment_review_chat_id @ffxemon", "/set required_channel @CyberShunya_x",
            "/set purchase_limit_count 3", "/set purchase_limit_minutes 10",
            "/set package_p50_price 60", "/set package_p100_price 100", "/set support_contact_url tg://user?id=7034779471",
            "",
            "ক্রেডিট যোগ: সংখ্যার Telegram User ID অথবা ব্যক্তিগত Chat ID, তারপর পরিমাণ দিন। ব্যবহারকারীকে আগে বট /start করতে হবে।",
            "কেনাকাটার সুরক্ষা: ১০ মিনিটে সর্বোচ্চ ৩টি Transaction ID জমা দেওয়া যাবে; ভুল ও পুনরাবৃত্ত ID-ও গণনা হবে।",
            "রিডিম কোড: Admin Panel → Create Redeem → CODE CREDITS MAX_USES DAYS; যেমন EMON50 50 100 30। মুছতে Redeem Codes থেকে Delete চাপুন।",
            "চ্যানেলের সদস্যতা প্রতিদিন ক্যাশ করা হয় এবং স্বয়ংক্রিয়ভাবে ১২ ঘণ্টা পরপর পুনরায় যাচাই হয়। Join/Check বাটনে তাৎক্ষণিক যাচাই করা যায়।",
            "ব্যবহারকারীকে ব্লক বা আনব্লক করতে Admin Panel-এর সংশ্লিষ্ট বাটন ব্যবহার করুন।",
        ]
    await update.effective_message.reply_text("\n".join(lines), reply_markup=main_keyboard(uid) if uid else None)


async def resolve_admin_target(update, context, action: str, target_text: str, amount_text: Optional[str] = None):
    admin_id = update.effective_user.id
    target_id = _safe_int(re.sub(r"^(user_id|userid|chat_id|chatid|user|chat):", "", target_text.strip(), flags=re.I))
    if target_id is None or target_id == 0:
        await update.effective_message.reply_text("❌ Numeric Telegram User ID or private Chat ID required.")
        return
    target_ref = user_ref(target_id)
    if not target_ref.get().exists:
        await update.effective_message.reply_text("❌ Account not found. Target user must open this bot and press /start first.")
        return
    if action == "block" or action == "unblock":
        blocked = action == "block"
        target_ref.update({"is_blocked": blocked, "updated_at": now()})
        audit("user_blocked" if blocked else "user_unblocked", admin_id, {"target_id": target_id})
        await update.effective_message.reply_text(f"✅ User {target_id} {'blocked' if blocked else 'unblocked'}.")
        try:
            await context.bot.send_message(target_id, "⛔ অ্যাডমিন আপনার অ্যাকাউন্ট ব্লক করেছেন।" if blocked else "✅ অ্যাডমিন আপনার অ্যাকাউন্ট আনব্লক করেছেন।")
        except Exception:
            pass
        return
    amount = credits_float(amount_text)
    if amount <= 0:
        await update.effective_message.reply_text("❌ Amount must be greater than zero.")
        return
    operation_ref = f"command:{admin_id}:{update.effective_message.message_id}:{target_id}"
    try:
        if action == "addcredits":
            after = add_credits(target_id, amount, "admin_add", operation_ref)
        else:
            after = deduct_credits(target_id, amount, "admin_deduct", operation_ref)
        await update.effective_message.reply_text(f"✅ User {target_id} balance updated: {after:g} credits.")
        try:
            await context.bot.send_message(target_id, f"💳 Admin balance update koreche. New balance: {after:g} credits.")
        except Exception:
            pass
    except Exception as exc:
        await update.effective_message.reply_text(f"❌ {clean_text(exc, 400)}")


async def addcredits_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not is_admin(update.effective_user.id):
        await update.effective_message.reply_text("Admin only.")
        return
    status = await channel_membership_status(context.bot, update.effective_user.id)
    if status is not True:
        await show_join_gate(update.effective_message, context, verification_error=status is None)
        return
    if len(context.args) != 2:
        await update.effective_message.reply_text("Usage: /addcredits USER_ID_OR_PRIVATE_CHAT_ID AMOUNT")
        return
    await resolve_admin_target(update, context, "addcredits", context.args[0], context.args[1])


async def block_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not is_admin(update.effective_user.id):
        await update.effective_message.reply_text("Admin only.")
        return
    status = await channel_membership_status(context.bot, update.effective_user.id)
    if status is not True:
        await show_join_gate(update.effective_message, context, verification_error=status is None)
        return
    if len(context.args) != 1:
        await update.effective_message.reply_text("Usage: /block USER_ID")
        return
    await resolve_admin_target(update, context, "block", context.args[0])


async def userinfo_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not is_admin(update.effective_user.id):
        await update.effective_message.reply_text("Admin only.")
        return
    status = await channel_membership_status(context.bot, update.effective_user.id)
    if status is not True:
        await show_join_gate(update.effective_message, context, verification_error=status is None)
        return
    if len(context.args) != 1:
        await update.effective_message.reply_text("Usage: /userinfo USER_ID_OR_CHAT_ID")
        return
    target_id = _safe_int(re.sub(r"^(user_id|userid|chat_id|chatid|user|chat):", "", context.args[0], flags=re.I))
    if target_id is None:
        await update.effective_message.reply_text("Numeric Telegram User ID/Chat ID required.")
        return
    ref = user_ref(target_id)
    snap = ref.get()
    if not snap.exists:
        await update.effective_message.reply_text("User record not found. User must start the bot first.")
        return
    u = snap.to_dict() or {}
    await update.effective_message.reply_text(
        f"User Info\nName: {clean_text((str(u.get('first_name','')) + ' ' + str(u.get('last_name',''))).strip(), 100) or 'User'}\n"
        f"Telegram ID: {target_id}\nUsername: @{clean_text(u.get('username') or 'none', 100)}\n"
        f"Balance: {format_balance(u.get('balance', 0))} credits\nSubscription: {subscription_for_profile(u)}\n"
        f"Calls: {_safe_int(u.get('total_calls', 0)) or 0}\nReferrals: {_safe_int(u.get('referrals', 0)) or 0}\n"
        f"Blocked: {bool(u.get('is_blocked', False))}\nJoined: {iso(u.get('created_at')) or 'Unknown'}"
    )


async def unblock_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not is_admin(update.effective_user.id):
        await update.effective_message.reply_text("Admin only.")
        return
    status = await channel_membership_status(context.bot, update.effective_user.id)
    if status is not True:
        await show_join_gate(update.effective_message, context, verification_error=status is None)
        return
    if len(context.args) != 1:
        await update.effective_message.reply_text("Usage: /unblock USER_ID")
        return
    await resolve_admin_target(update, context, "unblock", context.args[0])


async def start_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        await send_home(update, context)
    except Exception as exc:
        await update.effective_message.reply_text(f"⚠️ Temporary error: {clean_text(exc, 500)}")


async def call_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    status = await channel_membership_status(context.bot, uid)
    if status is not True:
        await show_join_gate(update.effective_message, context, verification_error=status is None)
        return
    ensure_user(update.effective_user)
    if get_settings().get("maintenance", False):
        await update.effective_message.reply_text("🛠 কল সেবা রক্ষণাবেক্ষণে আছে। আপাতত কল বন্ধ; অন্য সুবিধাগুলো চালু আছে।", reply_markup=main_keyboard(uid))
        return
    if user_blocked(uid):
        await update.effective_message.reply_text("⛔ আপনার অ্যাকাউন্ট ব্লক করা হয়েছে। সহায়তার জন্য Support-এ যোগাযোগ করুন।")
        return
    u = get_user(uid)
    cost = credits_float(get_settings().get("call_credit_cost", 1))
    if credits_float(u.get("balance", 0)) <= 0 or credits_float(u.get("balance", 0)) < cost:
        await update.effective_message.reply_text(f"❌ কল দিতে ক্রেডিট প্রয়োজন। প্রয়োজন: {cost:g} ক্রেডিট।", reply_markup=main_keyboard(uid))
        return
    context.user_data.clear()
    context.user_data["state"] = "call_phone"
    await update.effective_message.reply_text("📞 যে ফোন নম্বরে কল দিতে চান, সেটি পাঠান।")

async def cancel_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data.clear()
    uid = update.effective_user.id
    await update.effective_message.reply_text("অনুরোধ বাতিল করা হয়েছে। নিচের মেনু থেকে আবার শুরু করুন।", reply_markup=main_keyboard(uid))

async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE):
    try:
        error_text = clean_text(context.error, 1800) or "Unknown error"
        if telegram_app:
            # Plain text is deliberate: exception strings often contain Markdown-reserved characters.
            await telegram_app.bot.send_message(ADMIN_ID, "⚠️ Bot error:\n" + error_text)
    except Exception:
        pass


class ProviderWebhookPayload(BaseModel):
    status: Optional[str] = None
    message: Optional[str] = None
    call_id: Optional[str] = None
    provider_call_id: Optional[str] = None
    recording_url: Optional[str] = None
    recording: Optional[str] = None
    audio_url: Optional[str] = None
    duration: Optional[int] = None
    id: Optional[str] = None
    data: Optional[dict] = None


@app.get("/", response_class=HTMLResponse)
async def root():
    return """
<!doctype html>
<html>
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Custom Call Bot</title>
<style>
body{margin:0;font-family:system-ui;background:#111;color:#eee;display:grid;place-items:center;min-height:100vh}
.card{width:min(720px,90vw);padding:28px;border:1px solid #333;border-radius:24px;background:#181818;box-shadow:0 20px 70px #0008}
h1{margin-top:0}.ok{color:#78e08f}.muted{color:#aaa}
</style>
</head>
<body>
<div class="card">
<h1>Custom Call Bot</h1>
<p class="ok">● Service is online</p>
<p class="muted">Telegram webhook and Firebase-backed persistence are active.</p>
</div>
</body>
</html>
"""


@app.get("/healthz")
async def healthz():
    return {"ok": True, "service": "custom-call-bot", "time": now().isoformat()}


@app.api_route("/provider-audio/{token}/audio.{extension}", methods=["GET", "HEAD"])
async def provider_audio_proxy(token: str, extension: str, request: Request):
    """Serve a short-lived Telegram audio file URL to the call provider, without Firebase Storage."""
    if not re.fullmatch(r"[A-Za-z0-9_-]{32,100}", token or ""):
        raise HTTPException(status_code=404, detail="Audio link not found")
    extension = (extension or "").lower()
    if extension not in {"mp3", "wav", "ogg"}:
        raise HTTPException(status_code=404, detail="Audio format not supported")
    if telegram_app is None:
        raise HTTPException(status_code=503, detail="Audio service is starting")

    try:
        token_ref = db.collection(COL_PROVIDER_AUDIO).document(token)
        snap = await asyncio.to_thread(token_ref.get)
        metadata = snap.to_dict() if snap.exists else {}
    except Exception:
        raise HTTPException(status_code=503, detail="Audio lookup temporarily unavailable")
    if not metadata or metadata.get("extension") != extension:
        raise HTTPException(status_code=404, detail="Audio link not found")
    expiry = parse_datetime(metadata.get("expires_at"))
    if expiry is None or expiry <= now():
        try:
            await asyncio.to_thread(token_ref.delete)
        except Exception:
            pass
        raise HTTPException(status_code=410, detail="Audio link expired")
    file_id = clean_text(metadata.get("file_id"), 500)
    if not file_id:
        raise HTTPException(status_code=404, detail="Audio file unavailable")

    content_types = {"mp3": "audio/mpeg", "wav": "audio/wav", "ogg": "audio/ogg"}
    head_headers = {
        "Content-Disposition": f'inline; filename="audio.{extension}"',
        "Cache-Control": "private, no-store, max-age=0",
        "X-Content-Type-Options": "nosniff",
    }
    stored_size = _safe_int(metadata.get("file_size"))
    if stored_size is not None and stored_size > 0:
        head_headers["Content-Length"] = str(stored_size)
    if request.method.upper() == "HEAD":
        return Response(status_code=200, media_type=content_types[extension], headers=head_headers)

    try:
        if audio_proxy_semaphore is not None:
            async with audio_proxy_semaphore:
                telegram_file = await telegram_app.bot.get_file(file_id)
                downloaded = await telegram_file.download_as_bytearray()
        else:
            telegram_file = await telegram_app.bot.get_file(file_id)
            downloaded = await telegram_file.download_as_bytearray()
        payload = bytes(downloaded)
    except Exception:
        raise HTTPException(status_code=502, detail="Could not retrieve audio from Telegram")

    # Prevent unexpectedly large audio transfers from consuming worker memory.
    if not payload or len(payload) > 15 * 1024 * 1024:
        raise HTTPException(status_code=413, detail="Audio file is empty or exceeds 15 MB")
    try:
        await asyncio.to_thread(token_ref.update, {"fetches": firestore.Increment(1), "last_fetched_at": now()})
    except Exception:
        pass
    return Response(
        content=payload,
        media_type=content_types[extension],
        headers={
            "Content-Disposition": f'inline; filename="audio.{extension}"',
            "Cache-Control": "private, no-store, max-age=0",
            "X-Content-Type-Options": "nosniff",
            "Content-Length": str(len(payload)),
        },
    )


@app.post("/telegram/webhook")
async def telegram_webhook(request: Request):
    if TELEGRAM_WEBHOOK_SECRET:
        received = request.headers.get("X-Telegram-Bot-Api-Secret-Token", "")
        if received != TELEGRAM_WEBHOOK_SECRET:
            raise HTTPException(status_code=403, detail="Forbidden")
    if telegram_app is None:
        raise HTTPException(status_code=503, detail="Bot not initialized")
    payload = await request.json()
    update = Update.de_json(payload, telegram_app.bot)
    await telegram_app.update_queue.put(update)
    return {"ok": True}


@app.post("/provider/call-webhook")
async def provider_call_webhook(request: Request):
    if CALL_WEBHOOK_SECRET:
        received = request.headers.get("X-Call-Webhook-Secret", "")
        if received != CALL_WEBHOOK_SECRET:
            raise HTTPException(status_code=403, detail="Forbidden")
    if telegram_app is None:
        raise HTTPException(status_code=503, detail="Bot not initialized")
    payload = await request.json()
    data = payload.get("data") if isinstance(payload.get("data"), dict) else payload
    provider_call_id = (
        data.get("provider_call_id")
        or data.get("call_id")
        or data.get("id")
    )
    recording_url = (
        data.get("recording_url")
        or data.get("recording")
        or data.get("audio_url")
    )
    status = data.get("status")
    duration = data.get("duration")

    if not provider_call_id:
        return {"ok": True, "updated": False, "reason": "No call id"}

    matches = list(
        db.collection(COL_CALLS)
        .where("provider_call_id", "==", str(provider_call_id))
        .limit(1)
        .stream()
    )
    if not matches:
        return {"ok": True, "updated": False, "reason": "Call not found"}

    call_ref = matches[0].reference
    call_data = matches[0].to_dict() or {}
    updates = {"updated_at": now()}
    raw_status = str(status or "").strip().lower()
    success_statuses = {"success", "succeeded", "completed"}
    failure_statuses = {"failed", "failure", "error", "rejected", "denied", "cancelled", "canceled"}
    new_status = None
    old_status = str(call_data.get("status", "")).strip().lower()
    if raw_status in success_statuses:
        new_status = "success"
        updates["status"] = new_status
    elif raw_status in failure_statuses:
        new_status = "failed"
        updates["status"] = new_status
    elif status:
        updates["provider_status"] = clean_text(status, 100)
    if recording_url:
        updates["recording_url"] = clean_text(recording_url, 2000)
    actual_duration = None
    if duration is not None:
        try:
            actual_duration = max(0, int(duration))
            updates["actual_duration"] = actual_duration
        except Exception:
            pass
    call_ref.update(updates)

    uid = _safe_int(call_data.get("user_id"))
    if uid is None or uid == 0:
        return {"ok": True, "updated": False, "reason": "Call record has no valid user ID"}

    # Apply provider final results to user stats once; only explicit provider success counts as success.
    user_document = user_ref(uid)
    if new_status == "success" and old_status not in success_statuses:
        increment_seconds = actual_duration if actual_duration is not None else (_safe_int(call_data.get("time", 0)) or 0)
        user_document.update({
            "successful_calls": firestore.Increment(1),
            "total_seconds": firestore.Increment(increment_seconds),
            "updated_at": now(),
        })
    elif new_status == "failed" and old_status not in failure_statuses:
        user_document.update({"failed_calls": firestore.Increment(1), "updated_at": now()})
        try:
            charge = credits_float(call_data.get("cost", 0))
            if charge > 0:
                refund_credits(uid, charge, "call_refund_webhook", matches[0].id)
        except Exception:
            pass
    if recording_url:
        try:
            recording_markup = None
            if re.match(r"^https?://", str(recording_url), re.I):
                recording_markup = InlineKeyboardMarkup(
                    [[InlineKeyboardButton("▶️ Listen Recording", url=str(recording_url), style="success")]]
                )
            await telegram_app.bot.send_message(
                uid,
                f"🎧 Call recording is ready.\nCall ID: {clean_text(provider_call_id, 120)}",
                parse_mode=None,
                reply_markup=recording_markup,
            )
        except Exception:
            pass

    return {"ok": True, "updated": True}


@app.on_event("startup")
async def startup():
    global telegram_app, channel_recheck_task, provider_http_client, provider_call_semaphore, audio_proxy_semaphore
    ensure_settings()
    provider_http_client = httpx.AsyncClient(
        timeout=httpx.Timeout(connect=10.0, read=120.0, write=30.0, pool=15.0),
        follow_redirects=True,
        limits=httpx.Limits(max_connections=50, max_keepalive_connections=20, keepalive_expiry=20.0),
    )
    provider_call_semaphore = asyncio.Semaphore(20)
    audio_proxy_semaphore = asyncio.Semaphore(8)
    telegram_app = Application.builder().token(BOT_TOKEN).concurrent_updates(32).build()
    telegram_app.add_handler(CommandHandler("start", start_command))
    telegram_app.add_handler(CommandHandler("admin", admin_command))
    telegram_app.add_handler(CommandHandler("call", call_command))
    telegram_app.add_handler(CommandHandler("cancel", cancel_command))
    telegram_app.add_handler(CommandHandler("set", set_command))
    telegram_app.add_handler(CommandHandler("help", help_command))
    telegram_app.add_handler(CommandHandler("addcredits", addcredits_command))
    telegram_app.add_handler(CommandHandler("block", block_command))
    telegram_app.add_handler(CommandHandler("unblock", unblock_command))
    telegram_app.add_handler(CommandHandler("userinfo", userinfo_command))
    telegram_app.add_handler(ChatMemberHandler(track_channel_membership, ChatMemberHandler.CHAT_MEMBER))
    telegram_app.add_handler(CallbackQueryHandler(callback_handler))
    telegram_app.add_handler(MessageHandler(filters.AUDIO | filters.VOICE | filters.Document.ALL, handle_audio_message))
    telegram_app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text_message))
    telegram_app.add_error_handler(error_handler)

    await telegram_app.initialize()
    await telegram_app.start()
    channel_recheck_task = asyncio.create_task(channel_membership_midnight_worker(telegram_app.bot))
    try:
        user_commands = [BotCommand("start", "Start")]
        # Clear previous command-menu entries and publish only /start in all common scopes.
        for command_scope in (BotCommandScopeDefault(), BotCommandScopeAllPrivateChats(), BotCommandScopeAllGroupChats()):
            try:
                await telegram_app.bot.delete_my_commands(scope=command_scope)
            except Exception:
                logger.warning("Could not clear a stale Telegram command scope: %s", type(command_scope).__name__)
            try:
                await telegram_app.bot.set_my_commands(user_commands, scope=command_scope)
            except Exception:
                logger.exception("Could not set the /start-only command list for %s", type(command_scope).__name__)
    except Exception:
        logger.exception("Could not set Telegram command menu")

    if PUBLIC_BASE_URL:
        webhook_url = f"{PUBLIC_BASE_URL}/telegram/webhook"
        await telegram_app.bot.set_webhook(
            url=webhook_url,
            secret_token=TELEGRAM_WEBHOOK_SECRET or None,
            allowed_updates=Update.ALL_TYPES,
        )


@app.on_event("shutdown")
async def shutdown():
    global telegram_app, channel_recheck_task, provider_http_client, provider_call_semaphore, audio_proxy_semaphore
    if channel_recheck_task:
        channel_recheck_task.cancel()
        try:
            await channel_recheck_task
        except asyncio.CancelledError:
            pass
        except Exception:
            pass
        channel_recheck_task = None
    if telegram_app:
        try:
            await telegram_app.stop()
            await telegram_app.shutdown()
        except Exception:
            pass
    if provider_http_client is not None:
        try:
            await provider_http_client.aclose()
        except Exception:
            pass
        provider_http_client = None
    provider_call_semaphore = None
    audio_proxy_semaphore = None


if __name__ == "__main__":
    import uvicorn
    uvicorn.run("app:app", host="0.0.0.0", port=PORT)
