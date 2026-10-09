
import os
import re
import json
import html
import hashlib
import uuid
import secrets
import string
import tempfile
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
from firebase_admin import credentials, db as firebase_db, storage
from fastapi import FastAPI, Request, HTTPException
from fastapi.responses import HTMLResponse
from pydantic import BaseModel
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
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


BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
ADMIN_ID = int(os.getenv("ADMIN_ID", "7034779471"))
PUBLIC_BASE_URL = os.getenv("PUBLIC_BASE_URL", "").rstrip("/")
TELEGRAM_WEBHOOK_SECRET = os.getenv("TELEGRAM_WEBHOOK_SECRET", "").strip()
CALL_API_TOKEN = os.getenv("CALL_API_TOKEN", "").strip()
CALL_API_BASE = os.getenv("CALL_API_BASE", "https://sms.bd1b.com/api/v1").rstrip("/")
CALL_WEBHOOK_SECRET = os.getenv("CALL_WEBHOOK_SECRET", "").strip()
PAYMENT_REVIEW_CHAT_ID = os.getenv("PAYMENT_REVIEW_CHAT_ID", "@ffxemon").strip()
REQUIRED_CHANNEL_USERNAME = os.getenv("REQUIRED_CHANNEL_USERNAME", "@CyberShunya_x").strip() or "@CyberShunya_x"
FIREBASE_DATABASE_URL = os.getenv("FIREBASE_DATABASE_URL", "").strip()
FIREBASE_CREDENTIALS_JSON = os.getenv("FIREBASE_CREDENTIALS_JSON", "").strip()
FIREBASE_STORAGE_BUCKET = os.getenv("FIREBASE_STORAGE_BUCKET", "").strip()
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
    if FIREBASE_STORAGE_BUCKET:
        firebase_options["storageBucket"] = FIREBASE_STORAGE_BUCKET
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
if FIREBASE_STORAGE_BUCKET:
    try:
        bucket = storage.bucket()
    except Exception:
        bucket = None

app = FastAPI(title="Custom Call Bot", version="1.0.0")

telegram_app: Optional[Application] = None

COL_USERS = "users"
COL_CALLS = "calls"
COL_LEDGER = "ledger"
COL_CODES = "redeem_codes"
COL_PAYMENTS = "payments"
COL_AUDIT = "audit_logs"
COL_SETTINGS = "settings"

UTC = timezone.utc

DEFAULT_SETTINGS = {
    "settings_schema": 3,
    "brand_name": "Custom Call",
    "maintenance": False,
    "call_credit_cost": 1.0,
    "daily_call_limit": 20,
    "call_cooldown_seconds": 15,
    "referral_bonus": 1.0,
    "daily_bonus": 1.0,
    "daily_bonus_enabled": False,
    "welcome_bonus": 1.0,
    "bkash_number": "01819202231",
    "nagad_number": "01819202231",
    "payment_number": "01819202231",
    "payment_review_chat_id": PAYMENT_REVIEW_CHAT_ID or "@ffxemon",
    "purchase_limit_count": 3,
    "purchase_limit_minutes": 10,
    "required_channel": REQUIRED_CHANNEL_USERNAME,
    "min_redeem_credits": 1.0,
    "support_text": "Support er jonno admin-ke message koro.",
    "buy_text": "Package select koro, bKash/Nagad-e payment koro, tarpor Transaction ID submit koro. Admin verify korle credits auto add hobe.",
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
    merged = dict(DEFAULT_SETTINGS)
    merged.update(data)
    if not isinstance(merged.get("packages"), list):
        merged["packages"] = list(DEFAULT_SETTINGS["packages"])
    if not isinstance(merged.get("payment_methods"), list):
        merged["payment_methods"] = list(DEFAULT_SETTINGS["payment_methods"])
    # Derive payment-method list from independently editable numbers.
    merged["payment_methods"] = [
        {"name": "bKash", "key": "bkash", "account": str(merged.get("bkash_number", "")).strip()},
        {"name": "Nagad", "key": "nagad", "account": str(merged.get("nagad_number", "")).strip()},
    ]
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
                        if "already recorded" not in str(exc).lower():
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
                if "already recorded" not in str(exc).lower():
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
            raise ValueError("This credit operation was already recorded. No duplicate credit was added.")
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
            raise ValueError("This credit operation was already recorded. No duplicate deduction was made.")
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
            transaction.update(ref, {"balance": after, "updated_at": now()})
            transaction.create(ledger_ref, {
                "user_id": user_id, "type": reason, "amount": -amount,
                "before": before, "after": after,
                "reference": clean_text(reference, 250), "created_at": now(),
            })
            return after
        return apply(transaction)

def refund_credits(user_id: int, amount: float, reason: str, reference: str = "") -> float:
    return add_credits(user_id, amount, reason, reference)


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


async def channel_membership_status(bot, user_id: int) -> Optional[bool]:
    settings = get_settings()
    channel = clean_text(settings.get("required_channel") or REQUIRED_CHANNEL_USERNAME, 100)
    try:
        member = await bot.get_chat_member(chat_id=channel, user_id=int(user_id))
        return member_status_is_joined(member)
    except Exception:
        return None


def membership_keyboard():
    channel = clean_text(get_settings().get("required_channel") or REQUIRED_CHANNEL_USERNAME, 100)
    channel_url = "https://t.me/" + channel.lstrip("@").strip("/")
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📢 Join Required Channel", url=channel_url)],
        [InlineKeyboardButton("✅ I Joined — Check Again", callback_data="membership:check")],
    ])


async def show_join_gate(target, context, verification_error: bool = False):
    text = (
        "🔒 *Channel Join Required*\n\n"
        f"Please join {escape_markdown(clean_text(get_settings().get('required_channel') or REQUIRED_CHANNEL_USERNAME, 100), version=1)} first. Bot-er kono feature join verify na howa porjonto kaj korbe na.\n\n"
        "Join korar por *I Joined — Check Again* button tap koro."
    )
    if verification_error:
        text += "\n\n⚠️ Verification failed. Admin-ke bot channel-e add kore admin permission dite bolo."
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
            if "already recorded" not in str(exc).lower():
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
                text=f"🎉 Referral Bonus: +{bonus:g} credit! Friend channel join complete koreche. More invite koro ar credit jito!",
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
        "last_status": clean_text(getattr(member, "status", "unknown"), 50),
        "last_change_at": now(),
    }, merge=True)


def user_blocked(user_id: int) -> bool:
    snap = user_ref(user_id).get()
    return bool((snap.to_dict() or {}).get("is_blocked", False))


def get_user(user_id: int) -> dict:
    snap = user_ref(user_id).get()
    return snap.to_dict() if snap.exists else {}


def format_balance(value: Any) -> str:
    return f"{credits_float(value):.2f}"


def main_keyboard(user_id: int):
    rows = [
        [InlineKeyboardButton("📞 Send Call", callback_data="menu:call"), InlineKeyboardButton("👤 My Profile", callback_data="menu:profile")],
        [InlineKeyboardButton("👥 Refer", callback_data="menu:refer"), InlineKeyboardButton("📊 LP Statistics", callback_data="menu:stats")],
        [InlineKeyboardButton("💰 Buy Credits", callback_data="menu:buy"), InlineKeyboardButton("🎁 Redeem", callback_data="menu:redeem")],
        [InlineKeyboardButton("🕘 Call History", callback_data="menu:history"), InlineKeyboardButton("☎️ Support", callback_data="menu:support")],
    ]
    settings = get_settings()
    if settings.get("daily_bonus_enabled", False):
        rows.append([InlineKeyboardButton("🎁 Daily Bonus", callback_data="daily:claim")])
    if is_admin(user_id):
        rows.append([InlineKeyboardButton("🛠 Admin Panel", callback_data="admin:menu")])
    return InlineKeyboardMarkup(rows)

def back_button():
    return InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="menu:home")]])


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
    status = await channel_membership_status(context.bot, tg_user.id)
    if status is None:
        await show_join_gate(message, context, verification_error=True)
        return

    if not existing:
        history = membership_history(tg_user.id)
        had_membership_before = bool(history.get("ever_member", False))
        referral_eligible = bool(referrer_id and status is False and not had_membership_before and referrer_id != tg_user.id)
        ensure_user(tg_user, referrer_id=referrer_id, referral_eligible=referral_eligible)
    else:
        ensure_user(tg_user)

    data = get_user(tg_user.id)
    if data.get("is_blocked") and not is_admin(tg_user.id):
        await message.reply_text("⛔ Your account is blocked. Support-er sathe contact koro.")
        return
    if not status:
        await show_join_gate(message, context)
        return

    await complete_pending_referral(tg_user.id)
    settings = get_settings()
    notice = settings.get("admin_notice", "")
    text = (
        f"✨ *{clean_text(settings.get('brand_name', 'Custom Call'), 60)}*\n\n"
        f"💳 Balance: *{format_balance(data.get('balance', 0))} credits*\n"
        f"📞 Total Calls: *{_safe_int(data.get('total_calls', 0)) or 0}*\n"
        f"👥 Referrals: *{_safe_int(data.get('referrals', 0)) or 0}*\n\n"
        "Nicher menu theke feature select koro."
    )
    if settings.get("maintenance") and not is_admin(tg_user.id):
        text += "\n\n🛠 Service maintenance-e ache."
    if notice:
        text += f"\n\nℹ️ {clean_text(notice, 500)}"
    await message.reply_text(text, parse_mode="Markdown", reply_markup=main_keyboard(tg_user.id))

async def edit_or_send(query, text: str, markup=None, parse_mode="Markdown"):
    try:
        await query.edit_message_text(text, parse_mode=parse_mode, reply_markup=markup)
    except Exception:
        await query.message.reply_text(text, parse_mode=parse_mode, reply_markup=markup)


async def callback_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if not query:
        return
    data = query.data or ""
    if not data.startswith("pay:"):
        await query.answer()
    user_id = query.from_user.id

    if data == "membership:check":
        status = await channel_membership_status(context.bot, user_id)
        if status is True:
            if not get_user(user_id):
                ensure_user(query.from_user)
            await complete_pending_referral(user_id)
            await edit_or_send(query, "✅ Channel verification successful. Feature unlock hoye geche.", main_keyboard(user_id))
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
        await edit_or_send(query, "⛔ Your account is blocked. Support-er sathe contact koro.", None)
        return

    if data == "menu:home":
        context.user_data.clear()
        u = get_user(user_id)
        await edit_or_send(query, f"🏠 *Dashboard*\n\nBalance: *{format_balance(u.get('balance', 0))} credits*\nMenu theke option select koro.", main_keyboard(user_id))
        return

    if data == "menu:profile":
        u = get_user(user_id)
        text = ("👤 *My Profile*\n\n" f"ID: `{user_id}`\n" f"Name: {escape_markdown(clean_text((u.get('first_name','') + ' ' + u.get('last_name','')).strip() or 'User',100), version=1)}\n" f"Username: @{escape_markdown(u.get('username') or 'none', version=1)}\n" f"Balance: *{format_balance(u.get('balance', 0))} credits*\n" f"Total Calls: *{_safe_int(u.get('total_calls', 0)) or 0}*\n" f"Successful: *{_safe_int(u.get('successful_calls', 0)) or 0}*\n" f"Failed: *{_safe_int(u.get('failed_calls', 0)) or 0}*\n" f"Total Seconds: *{_safe_int(u.get('total_seconds', 0)) or 0}*\n" f"Referrals: *{_safe_int(u.get('referrals', 0)) or 0}*")
        await edit_or_send(query, text, back_button())
        return

    if data == "menu:refer":
        me = await context.bot.get_me()
        referral_link = f"https://t.me/{me.username}?start=ref_{user_id}"
        bonus = credits_float(get_settings().get("referral_bonus", 1))
        text = ("👥 *Refer Friends*\n\n" f"Referral Bonus: *{bonus:g} Credit(s)*\n" f"Link share koro ar *{bonus:g} credit jite nao!*\n\n" f"Your Link:\n`{referral_link}`\n\n" "Bonus pabe shudhu notun user, jara age required channel member chilo na, bot start kore channel join complete korbe. Existing/previously tracked member referral count hobe na.")
        await edit_or_send(query, text, back_button())
        return

    if data == "menu:stats":
        settings = get_settings()
        totals = await local_stats()
        lines = ["📊 *LP Statistics*\n", f"Users: *{totals['users']}*", f"Total Calls: *{totals['calls']}*", f"Successful Calls: *{totals['success']}*", f"Failed Calls: *{totals['failed']}*", f"Credits in Circulation: *{format_balance(totals['credits'])}*", f"Daily Call Limit: *{int(settings.get('daily_call_limit', 20))}*"]
        if totals.get("top_users"):
            lines += ["", "🏆 *Top Credit Holders*"]
            for rank, item in enumerate(totals["top_users"], 1):
                # Deliberately show display name only; never show username here.
                name = escape_markdown(item.get("name") or "User", version=1)
                lines.append(f"{rank}. {name} — *{format_balance(item.get('balance', 0))} credits*")
        await edit_or_send(query, "\n".join(lines), back_button())
        return

    if data == "menu:history":
        docs = list(db.collection(COL_CALLS).where("user_id", "==", user_id).limit(50).stream())
        items = sorted(docs, key=lambda snap: str((snap.to_dict() or {}).get("created_at") or ""), reverse=True)[:10]
        if not items:
            await edit_or_send(query, "📞 *Call History*\n\nKono call history nei.", back_button())
            return
        lines = ["📞 *Recent Calls*\n"]
        for snap in items:
            c = snap.to_dict() or {}
            status = str(c.get("status", "unknown")).upper()
            number = str(c.get("number", ""))[-4:]
            when = iso(c.get("created_at")) or "-"
            lines.append(f"• `****{number}` — *{status}* — {when[:16]}")
            if c.get("recording_url"):
                lines.append(f"  Recording: {clean_text(c.get('recording_url'), 300)}")
        await edit_or_send(query, "\n".join(lines), back_button())
        return

    if data == "menu:support":
        await edit_or_send(query, f"☎️ *Support*\n\n{clean_text(get_settings().get('support_text', 'Support-er jonno admin-ke message koro.'), 1800)}", back_button())
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
        await edit_or_send(query, "🎁 *Redeem Code*\n\nYour redeem code pathao.", back_button())
        return
    if data == "menu:call":
        u = get_user(user_id)
        cost = credits_float(get_settings().get("call_credit_cost", 1))
        if credits_float(u.get("balance", 0)) <= 0 or credits_float(u.get("balance", 0)) < cost:
            await edit_or_send(query, f"❌ Call dite credit lagbe. Required: *{cost:g} credits*. Buy Credits ba Redeem use koro.", back_button())
            return
        context.user_data.clear()
        context.user_data["state"] = "call_phone"
        await edit_or_send(query, "📞 *Send Call*\n\nDestination phone number pathao. Example: `01700000000`", back_button())
        return
    if data.startswith("callmode:"):
        mode = data.split(":", 1)[1]
        context.user_data["call_mode"] = mode
        if mode == "text":
            context.user_data["state"] = "call_content_text"
            await edit_or_send(query, "📝 Call-e je text bola hobe seta pathao.", back_button())
        elif mode == "audio_url":
            context.user_data["state"] = "call_content_audio_url"
            await edit_or_send(query, "🔗 Direct MP3/WAV/OGG URL pathao.", back_button())
        else:
            context.user_data["state"] = "call_content_audio_upload"
            await edit_or_send(query, "🎧 MP3/WAV/OGG/Voice file upload koro.", back_button())
        return
    if data.startswith("calltime:"):
        try:
            seconds = int(data.split(":", 1)[1])
        except (TypeError, ValueError):
            await edit_or_send(query, "Invalid call duration. abar try koro.", back_button())
            return
        context.user_data["call_time"] = seconds
        await execute_pending_call(update, context)
        return
    if data == "call:cancel":
        context.user_data.clear()
        await edit_or_send(query, "Cancelled.", main_keyboard(user_id))
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
    rows = [[InlineKeyboardButton(clean_text(p.get("label", f"{p.get('credits')} Calls"), 60), callback_data=f"buy:{p.get('id')}")] for p in packages]
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data="menu:home")])
    bkash = clean_text(settings.get("bkash_number", ""), 40) or "Not set"
    nagad = clean_text(settings.get("nagad_number", ""), 40) or "Not set"
    package_lines = "\n".join(f"• {clean_text(pkg.get('label'), 100)}" for pkg in packages)
    text = (
        "💰 *Credit Purchase*\n━━━━━━━━━━━━━━━━━\n\n"
        "📦 *Available Packages:*\n\n" + package_lines +
        "\n━━━━━━━━━━━━━━━━━\n"
        f"💳 bKash: `{bkash}`\n💳 Nagad: `{nagad}`\n"
        "⚡ Admin approve korle credits auto add hobe.\n\n"
        "👇 Nicher package select koro:"
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
        await edit_or_send(query, "Package not found.", back_button())
        return
    context.user_data["payment_package"] = package
    methods = []
    if clean_text(settings.get("bkash_number"), 40):
        methods.append([InlineKeyboardButton("💗 Pay with bKash", callback_data="paymethod:bkash")])
    if clean_text(settings.get("nagad_number"), 40):
        methods.append([InlineKeyboardButton("🧡 Pay with Nagad", callback_data="paymethod:nagad")])
    methods.append([InlineKeyboardButton("⬅️ Cancel", callback_data="menu:buy")])
    if len(methods) == 1:
        await edit_or_send(query, "❌ Admin ekhono kono payment number set koreni.", back_button())
        return
    await edit_or_send(query, f"📦 *{clean_text(package.get('label'),100)}*\nCredits: *{credits_float(package.get('credits', 0)):g}*\nPrice: *{int(package.get('price',0))} TK*\n\nPayment method select koro:", InlineKeyboardMarkup(methods))


async def select_payment_method(query, context, method: str):
    package = context.user_data.get("payment_package")
    if not package:
        await edit_or_send(query, "Package session expired. Buy Credits abar open koro.", back_button())
        return
    key = "bkash_number" if method == "bkash" else "nagad_number" if method == "nagad" else None
    if not key:
        await edit_or_send(query, "Invalid payment method.", back_button())
        return
    settings = get_settings()
    number = clean_text(settings.get(key), 40)
    if not number:
        await edit_or_send(query, f"{method.title()} payment currently unavailable. onno method try koro.", back_button())
        return
    context.user_data["payment_method"] = method
    context.user_data["payment_number"] = number
    context.user_data["state"] = "payment_txn"
    await edit_or_send(query, f"💳 *{method.title()} Payment*\n\nSend money to: `{number}`\nPackage: *{clean_text(package.get('label'),100)}*\nAmount: *{int(package.get('price',0))} TK*\n\nPayment complete kore Transaction ID pathao. Same Transaction ID second time accept hobe na.", back_button())

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
        await update.effective_message.reply_text("⛔ Your account is blocked. Support-er sathe contact koro.")
        return

    state = context.user_data.get("state")
    text = clean_text(update.effective_message.text, 4000)
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
            await update.effective_message.reply_text(f"❌ Call dite credit lagbe. Required: {cost:g} credits. Buy Credits ba Redeem use koro.")
            context.user_data.clear()
            return
        phone = normalize_phone(text)
        if not phone:
            await update.effective_message.reply_text("❌ Invalid phone number. abar try koro.")
            return
        context.user_data["call_phone"] = phone
        context.user_data["state"] = "call_mode"
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton("📝 Text to Speech", callback_data="callmode:text")],
            [InlineKeyboardButton("🔗 Audio URL", callback_data="callmode:audio_url")],
            [InlineKeyboardButton("🎧 Upload Audio", callback_data="callmode:audio_upload")],
            [InlineKeyboardButton("❌ Cancel", callback_data="call:cancel")],
        ])
        await update.effective_message.reply_text(f"📞 Number: `****{phone[-4:]}`\n\nCall audio method select koro.", parse_mode="Markdown", reply_markup=markup)
        return
    if state == "call_content_text":
        if not text:
            await update.effective_message.reply_text("❌ Text required.")
            return
        context.user_data["call_text"] = text
        await ask_call_time(update)
        return
    if state == "call_content_audio_url":
        if not re.match(r"^https?://", text, re.I):
            await update.effective_message.reply_text("❌ Valid http/https direct audio URL pathao.")
            return
        if not re.search(r"\.(mp3|wav|ogg)(\?.*)?$", text, re.I):
            await update.effective_message.reply_text("⚠️ URL-ta direct MP3, WAV, or OGG file hote hobe.")
            return
        context.user_data["call_audio_url"] = text
        await ask_call_time(update)
        return
    if state == "call_content_audio_upload":
        await update.effective_message.reply_text("🎧 Send Call → Upload Audio select kore audio/voice file pathao.")
        return
    if state == "admin_broadcast":
        await do_broadcast(update, context, text)
        return
    await update.effective_message.reply_text("Dashboard menu use koro.", reply_markup=main_keyboard(user_id))

async def ask_call_time(update: Update):
    markup = InlineKeyboardMarkup([
        [
            InlineKeyboardButton("30s", callback_data="calltime:30"),
            InlineKeyboardButton("60s", callback_data="calltime:60"),
            InlineKeyboardButton("120s", callback_data="calltime:120"),
        ],
        [
            InlineKeyboardButton("180s", callback_data="calltime:180"),
            InlineKeyboardButton("300s", callback_data="calltime:300"),
        ],
        [InlineKeyboardButton("❌ Cancel", callback_data="call:cancel")],
    ])
    await update.effective_message.reply_text("⏱ Choose call duration.", reply_markup=markup)


async def handle_audio_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not update.effective_message:
        return
    user_id = update.effective_user.id
    status = await channel_membership_status(context.bot, user_id)
    if status is not True:
        await show_join_gate(update.effective_message, context, verification_error=status is None)
        return
    ensure_user(update.effective_user)
    if user_blocked(user_id) and not is_admin(user_id):
        await update.effective_message.reply_text("⛔ Your account is blocked.")
        return
    state = context.user_data.get("state")
    if state != "call_content_audio_upload":
        await update.effective_message.reply_text("Use Send Call → Upload Audio first.")
        return
    if bucket is None:
        await update.effective_message.reply_text(
            "❌ Firebase Storage is not configured. Set FIREBASE_STORAGE_BUCKET first."
        )
        return

    tg_file = None
    extension = "ogg"
    content_type = "audio/ogg"
    if update.effective_message.audio:
        tg_file = await update.effective_message.audio.get_file()
        name = update.effective_message.audio.file_name or "audio.mp3"
        m = re.search(r"\.(mp3|wav|ogg)$", name, re.I)
        extension = m.group(1).lower() if m else "mp3"
        content_type = {
            "mp3": "audio/mpeg",
            "wav": "audio/wav",
            "ogg": "audio/ogg",
        }.get(extension, "audio/mpeg")
    elif update.effective_message.voice:
        tg_file = await update.effective_message.voice.get_file()
        extension = "ogg"
        content_type = "audio/ogg"
    elif update.effective_message.document:
        name = update.effective_message.document.file_name or ""
        if not re.search(r"\.(mp3|wav|ogg)$", name, re.I):
            await update.effective_message.reply_text("❌ Supported upload types: MP3, WAV, OGG.")
            return
        tg_file = await update.effective_message.document.get_file()
        extension = re.search(r"\.(mp3|wav|ogg)$", name, re.I).group(1).lower()
        content_type = {
            "mp3": "audio/mpeg",
            "wav": "audio/wav",
            "ogg": "audio/ogg",
        }[extension]

    if tg_file is None:
        await update.effective_message.reply_text("❌ No supported audio file detected.")
        return

    status = await update.effective_message.reply_text("⏳ Uploading audio securely...")
    temp_path = None
    try:
        with tempfile.NamedTemporaryFile(delete=False, suffix=f".{extension}") as tmp:
            temp_path = tmp.name
        await tg_file.download_to_drive(temp_path)
        object_name = f"user_audio/{user_id}/{uuid.uuid4().hex}.{extension}"
        blob = bucket.blob(object_name)
        blob.upload_from_filename(temp_path, content_type=content_type)
        url = blob.generate_signed_url(
            version="v4",
            expiration=timedelta(minutes=30),
            method="GET",
        )
        context.user_data["call_audio_url"] = url
        await status.edit_text("✅ Audio uploaded. Choose the call duration.")
        await ask_call_time(update)
    except Exception as exc:
        await status.edit_text(f"❌ Audio upload failed: {clean_text(exc, 500)}")
    finally:
        if temp_path:
            try:
                os.remove(temp_path)
            except OSError:
                pass


async def execute_pending_call(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    settings = get_settings()
    u = get_user(user_id)
    if u.get("is_blocked") and not is_admin(user_id):
        await update.callback_query.message.reply_text("⛔ Your account is blocked.")
        return
    if settings.get("maintenance") and not is_admin(user_id):
        await update.callback_query.message.reply_text("🛠 Calls temporarily disabled. pore try koro.")
        return
    phone = context.user_data.get("call_phone")
    txt = context.user_data.get("call_text")
    audio = context.user_data.get("call_audio_url")
    seconds = int(context.user_data.get("call_time", 30))
    if not phone or (not txt and not audio):
        await update.callback_query.message.reply_text("❌ Call session incomplete. abar start koro.")
        context.user_data.clear()
        return
    now_dt = now()
    last_call = parse_datetime(u.get("last_call_at"))
    cooldown = max(0, _safe_int(settings.get("call_cooldown_seconds", 15)) if _safe_int(settings.get("call_cooldown_seconds", 15)) is not None else 15)
    if last_call is not None and (now_dt-last_call).total_seconds() < cooldown and not is_admin(user_id):
        wait = max(1, int(cooldown-(now_dt-last_call).total_seconds()))
        await update.callback_query.message.reply_text(f"⏳ {wait}s wait kore abar try koro.")
        return
    day_key = local_day_key()
    calls_today = _safe_int(u.get("calls_today", 0)) or 0
    if u.get("call_day") != day_key:
        calls_today = 0
    limit = max(0, _safe_int(settings.get("daily_call_limit", 20)) if _safe_int(settings.get("daily_call_limit", 20)) is not None else 20)
    if calls_today >= limit and not is_admin(user_id):
        await update.callback_query.message.reply_text("🚫 Daily call limit reached.")
        context.user_data.clear()
        return
    cost = credits_float(settings.get("call_credit_cost", 1))
    balance = credits_float(u.get("balance", 0))
    if cost <= 0:
        await update.callback_query.message.reply_text("⚠️ Admin call cost 0 set korte parbe na. Call charge valid korte admin-ke bolo.")
        context.user_data.clear()
        return
    if balance <= 0 or balance < cost:
        await update.callback_query.message.reply_text(f"❌ Credits chara call deya jabe na. Required: {cost:g}; current balance: {balance:g}.")
        context.user_data.clear()
        return

    log_ref = db.collection(COL_CALLS).document()
    log_ref.set({
        "user_id": user_id, "number": phone, "mode": "text" if txt else "audio",
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
        await update.callback_query.message.reply_text(f"❌ {clean_text(exc, 500)}")
        context.user_data.clear()
        return

    await update.callback_query.message.reply_text("📡 Call request pathano hocche...")
    try:
        result = await provider_call(phone, txt=txt, audio=audio, seconds=seconds)
        status_value = str(result.get("status", "")).strip().lower()
        success = status_value in {"success", "succeeded", "accepted", "ok", "completed"}
        uncertain = status_value == "accepted_unconfirmed"
        provider_data = result.get("data") if isinstance(result.get("data"), dict) else {}
        provider_id = provider_data.get("id") or provider_data.get("call_id") or result.get("call_id") or result.get("id")
        recording_url = provider_data.get("recording_url") or provider_data.get("recording") or provider_data.get("audio_url") or result.get("recording_url") or result.get("recording")
        stored_status = "submitted" if success else "submitted_unconfirmed" if uncertain else "failed"
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
        if success or uncertain:
            msg = (
                "✅ *Call Request Sent*\n\n"
                f"📞 Number: `****{phone[-4:]}`\n⏱ Duration: `{seconds}s`\n"
                f"💳 Cost: `{cost:g} credits`\n🆔 Call ID: `{clean_text(provider_id or log_ref.id, 120)}`\n\n"
            )
            if uncertain:
                msg += "Provider response valid JSON chilo na, tai exact status confirm kora jayni. Call request submit hoyeche bole record kora holo; raw server HTML hide kora hoyeche. Call na gele ei Call ID diye support-e contact koro."
            else:
                msg += f"Provider: {escape_markdown(clean_provider_message(result.get('message') or 'Accepted') or 'Accepted', version=1)}"
            if recording_url and re.match(r"^https?://", str(recording_url), re.I):
                msg += "\n🎧 Recording available."
                markup = InlineKeyboardMarkup([[InlineKeyboardButton("▶️ Listen Recording", url=str(recording_url))]])
                await update.callback_query.message.reply_text(msg, parse_mode="Markdown", reply_markup=markup)
            else:
                await update.callback_query.message.reply_text(msg, parse_mode="Markdown")
        else:
            refund_credits(user_id, cost, "call_refund", log_ref.id)
            await update.callback_query.message.reply_text(
                f"❌ Call request rejected by provider.\n{escape_markdown(clean_provider_message(result.get('message') or 'Please try later or contact support.') or 'Please try later.', version=1)}\nCredits refund kora hoyeche."
            )
    except Exception as exc:
        log_ref.update({"status": "submitted_unconfirmed", "error": clean_text(exc, 500), "updated_at": now()})
        user_ref(user_id).set({
            "total_calls": firestore.Increment(1),
            "updated_at": now(),
        }, merge=True)
        await update.callback_query.message.reply_text(
            f"✅ Call request pathano hoyeche, kintu provider confirmation paoa jayni. Raw error hide kora holo. Call ID: `{escape_markdown(log_ref.id, version=1)}`. Call na gele support-e contact koro.",
            parse_mode="Markdown",
        )
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
    payload = {"api_token": CALL_API_TOKEN, "number": number, "time": int(max(1, min(300, seconds)))}
    if txt:
        payload["txt"] = txt
    else:
        payload["audio"] = audio
    async with httpx.AsyncClient(timeout=45.0, follow_redirects=True) as client:
        response = await client.post(f"{CALL_API_BASE}/call", data=payload)
        body = response.text or ""
        content_type = (response.headers.get("content-type") or "").lower()
        try:
            data = response.json()
            if not isinstance(data, dict):
                data = {"status": "error", "message": "Provider returned an unexpected response format."}
        except Exception:
            data = None
        looks_html = "text/html" in content_type or body.lstrip().lower().startswith(("<!doctype html", "<html", "&lt;!doctype html", "&lt;html")) or "<title>server error</title>" in body.lower() or "&lt;title&gt;server error" in body.lower()
        if data is None and looks_html:
            # Some upstreams can dispatch the call and then fail while rendering their response.
            # Keep the request charged and mark it unconfirmed rather than showing raw HTML or false failure.
            return {"status": "accepted_unconfirmed", "message": "Provider did not return JSON; request status is unconfirmed.", "http_code": response.status_code, "response_type": "html"}
        if data is None:
            return {"status": "error", "message": "Provider returned an unreadable response. Raw output hidden.", "http_code": response.status_code, "response_type": "unknown"}
        provider_status = str(data.get("status", "")).strip().lower()
        if response.status_code >= 500 and provider_status not in {"success", "accepted", "ok", "completed"}:
            msg = clean_provider_message(data.get("message"))
            # HTTP 5xx can happen after the provider starts the call; don't falsely claim hard failure.
            return {"status": "accepted_unconfirmed", "message": msg or "Provider server error after request; status unconfirmed.", "http_code": response.status_code, "response_type": "json", "data": data.get("data")}
        if response.status_code >= 400 and provider_status not in {"success", "accepted", "ok", "completed"}:
            return {"status": "error", "message": clean_provider_message(data.get("message") or f"Provider HTTP {response.status_code}"), "http_code": response.status_code}
        if not provider_status and response.status_code < 400:
            # Don't treat an empty/malformed status as a confirmed success.
            data["status"] = "accepted_unconfirmed"
            data["message"] = clean_provider_message(data.get("message") or "Provider accepted HTTP request but did not return a status.")
        data["message"] = clean_provider_message(data.get("message") or "")
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

async def claim_daily(query):
    user_id = query.from_user.id
    settings = get_settings()
    if not settings.get("daily_bonus_enabled", False):
        await edit_or_send(query, "🎁 Daily Bonus is currently disabled by admin.", back_button())
        return
    bonus = credits_float(settings.get("daily_bonus", 0))
    if bonus <= 0:
        await edit_or_send(query, "Daily bonus is disabled because its amount is zero.", back_button())
        return
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

    try:
        after = claim(transaction)
        await edit_or_send(query, f"🎁 Daily bonus claimed: +{bonus:g} credits.\n💳 New balance: {after:g}", back_button())
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
        await update.effective_message.reply_text(f"❌ {clean_text(exc, 800)}")


async def create_payment_request(update: Update, context: ContextTypes.DEFAULT_TYPE, txn_id: str):
    user = update.effective_user
    user_id = user.id
    package = context.user_data.get("payment_package")
    method = context.user_data.get("payment_method")
    number = context.user_data.get("payment_number")
    if not package or method not in {"bkash", "nagad"} or not number:
        await update.effective_message.reply_text("❌ Purchase session incomplete. Buy Credits abar open koro.")
        context.user_data.clear()
        return

    # Count every submitted transaction attempt, including malformed/duplicate IDs,
    # so a user cannot retry bad payment details indefinitely within one flow.
    allowed, wait_seconds = await record_purchase_attempt(user_id)
    if not allowed:
        await update.effective_message.reply_text(
            f"⏳ Purchase attempt limit reached. 10 minute-e maximum 3 request. "
            f"{wait_seconds // 60}m {wait_seconds % 60}s pore try koro."
        )
        return

    txn_id = clean_text(txn_id, 100)
    if not re.fullmatch(r"[A-Za-z0-9_-]{3,100}", txn_id):
        await update.effective_message.reply_text("❌ Invalid Transaction ID. 3–100 letters/digits/_/- use koro. Ei attempt count hoyeche.")
        return
    duplicate_docs = list(db.collection(COL_PAYMENTS).stream())
    if any(str((snap.to_dict() or {}).get("transaction_id", "")).strip().casefold() == txn_id.casefold() for snap in duplicate_docs):
        await update.effective_message.reply_text("❌ Ei Transaction ID age submit kora hoyeche. Ei attempt count hoyeche; unique valid ID dao.")
        return

    settings = get_settings()
    ref = db.collection(COL_PAYMENTS).document()
    payload = {
        "user_id": user_id, "telegram_id": user_id, "username": safe_username(user),
        "first_name": clean_text(user.first_name, 100), "package_id": package.get("id"),
        "package_label": package.get("label"), "credits": credits_float(package.get("credits", 0)),
        "price": int(package.get("price", 0)), "transaction_id": txn_id,
        "payment_method": method, "payment_number": clean_text(number, 40),
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
        f"📱 Payment Number: `{clean_text(number,40)}`\n🧾 Transaction ID: `{txn_id}`\n"
        "━━━━━━━━━━━━━━━━━\nVerify payment manually before approval. Credits will be added only once."
    )
    review_markup = InlineKeyboardMarkup([[InlineKeyboardButton("✅ Approve & Add Credits", callback_data=f"pay:approve:{ref.id}"), InlineKeyboardButton("❌ Reject", callback_data=f"pay:reject:{ref.id}")]])
    review_chat = clean_text(settings.get("payment_review_chat_id") or PAYMENT_REVIEW_CHAT_ID, 100)
    notified = False
    try:
        await context.bot.send_message(chat_id=review_chat, text=group_message, parse_mode="Markdown", reply_markup=review_markup)
        notified = True
    except Exception as exc:
        notify_error = clean_text(exc, 400)
        ref.update({"review_notify_error": notify_error, "updated_at": now()})
        try:
            await context.bot.send_message(ADMIN_ID, f"⚠️ Payment request {ref.id} group-e post hoyni. Review group/bot permissions check koro.")
        except Exception:
            pass
    confirmation = f"✅ Payment request saved.\n🆔 Request ID: `{ref.id}`\n" + ("📨 @ffxemon review group-e pathano hoyeche. Admin approve korle credits auto add hobe." if notified else "⚠️ Database-e save hoyeche but review group-e pathano jayni. Admin-ke notify kora hoyeche.")
    await update.effective_message.reply_text(confirmation, parse_mode="Markdown", reply_markup=main_keyboard(user_id))

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
    success = sum(1 for status in statuses if status in {"submitted", "completed", "success"})
    failed = sum(1 for status in statuses if status == "failed")
    return {
        "users": len(valid_users), "calls": len(calls), "success": success, "failed": failed,
        "credits": credits, "top_users": sorted(valid_users, key=lambda item: item["balance"], reverse=True)[:5],
    }

async def admin_menu(query):
    settings = get_settings()
    daily_state = "ON ✅" if settings.get("daily_bonus_enabled", False) else "OFF ⛔"
    rows = [
        [InlineKeyboardButton("📈 Overview", callback_data="admin:overview"), InlineKeyboardButton("👥 Users", callback_data="admin:users")],
        [InlineKeyboardButton("💳 Add Credits", callback_data="admin:addcredits"), InlineKeyboardButton("➖ Deduct Credits", callback_data="admin:deductcredits")],
        [InlineKeyboardButton("🚫 Block User", callback_data="admin:block"), InlineKeyboardButton("✅ Unblock User", callback_data="admin:unblock")],
        [InlineKeyboardButton("🎁 Create Redeem", callback_data="admin:createcode"), InlineKeyboardButton("📜 Redeem Codes", callback_data="admin:codes")],
        [InlineKeyboardButton("💰 Payments", callback_data="admin:payments"), InlineKeyboardButton("📞 Call Logs", callback_data="admin:calls")],
        [InlineKeyboardButton("📣 Broadcast", callback_data="admin:broadcast"), InlineKeyboardButton("⚙️ Settings", callback_data="admin:settings")],
        [InlineKeyboardButton("💗 bKash Number", callback_data="admin:bkash_number"), InlineKeyboardButton("🧡 Nagad Number", callback_data="admin:nagad_number")],
        [InlineKeyboardButton(f"🎁 Daily Bonus: {daily_state}", callback_data="admin:toggle_daily")],
        [InlineKeyboardButton("🔌 Provider", callback_data="admin:provider"), InlineKeyboardButton("🛡 Safety", callback_data="admin:safety")],
        [InlineKeyboardButton("⬅️ Home", callback_data="menu:home")],
    ]
    await edit_or_send(query, "🛠 *Admin Panel*\n\nCredit, payment, user, referral, bonus, and call settings manage koro.", InlineKeyboardMarkup(rows))

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
                f"• `{u.get('user_id')}` — @{u.get('username') or 'none'} — {format_balance(u.get('balance', 0))}"
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
            "🎁 Send: `CREDITS MAX_USES DAYS`\nExample: `25 100 30`\nUse MAX_USES=0 for unlimited.",
            back_button(),
        )
    elif action == "codes":
        docs = list(db.collection(COL_CODES).order_by("created_at", direction=firestore.Query.DESCENDING).limit(15).stream())
        if not docs:
            await edit_or_send(query, "📜 No redeem codes yet.", back_button())
            return
        lines = ["📜 *Recent Redeem Codes*\n"]
        for s in docs:
            c = s.to_dict() or {}
            lines.append(
                f"`{c.get('code')}` — {credits_float(c.get('credits', 0)):g} — "
                f"{_safe_int(c.get('uses', 0)) or 0}/{(_safe_int(c.get('max_uses', 0)) or 0) if (_safe_int(c.get('max_uses', 0)) or 0) else '∞'} — "
                f"{'ON' if c.get('active', True) else 'OFF'}"
            )
        await edit_or_send(query, "\n".join(lines), back_button())
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
                InlineKeyboardButton(f"✅ {str(p.get('user_id'))}", callback_data=f"pay:approve:{s.id}"),
                InlineKeyboardButton("❌ Reject", callback_data=f"pay:reject:{s.id}"),
            ])
        rows.append([InlineKeyboardButton("⬅️ Back", callback_data="admin:menu")])
        await edit_or_send(query, text, InlineKeyboardMarkup(rows))
    elif action == "calls":
        docs = list(db.collection(COL_CALLS).order_by("created_at", direction=firestore.Query.DESCENDING).limit(10).stream())
        lines = ["📞 *Recent Call Logs*\n"]
        for s in docs:
            c = s.to_dict() or {}
            lines.append(
                f"`{str(c.get('user_id'))}` — ****{str(c.get('number',''))[-4:]} — "
                f"{str(c.get('status'))} — {str(c.get('mode'))}"
            )
            if c.get("recording_url"):
                lines.append("🎧 Recording URL stored.")
        await edit_or_send(query, "\n".join(lines), back_button())
    elif action == "broadcast":
        context.user_data["state"] = "admin_broadcast"
        await edit_or_send(query, "📣 Send the message to broadcast to all users.", back_button())
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
            f"Review group: `{clean_text(s.get('payment_review_chat_id', PAYMENT_REVIEW_CHAT_ID), 100)}`\n"
            f"Required channel: `{clean_text(s.get('required_channel', REQUIRED_CHANNEL_USERNAME), 100)}`\n\n"
            "Use /help for all settings and commands."
        )
        rows = [
            [InlineKeyboardButton("💗 Set bKash Number", callback_data="admin:bkash_number")],
            [InlineKeyboardButton("🧡 Set Nagad Number", callback_data="admin:nagad_number")],
            [InlineKeyboardButton("🎁 Toggle Daily Bonus", callback_data="admin:toggle_daily")],
            [InlineKeyboardButton("⬅️ Back to Admin", callback_data="admin:menu")],
        ]
        await edit_or_send(query, text, InlineKeyboardMarkup(rows))
    elif action in {"paymentnumber", "bkash_number", "nagad_number"}:
        method = "bkash" if action in {"paymentnumber", "bkash_number"} else "nagad"
        key = f"{method}_number"
        context.user_data["state"] = f"admin_{method}_number"
        current_number = clean_text(get_settings().get(key, ""), 40) or "Not set"
        await edit_or_send(query, f"💳 *Set {method.title()} Number*\n\nCurrent: `{current_number}`\n\nNew number pathao (8–15 digits), or `OFF` diye method disable koro.", back_button())
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
                transaction.update(user_document, {"balance": new_balance, "updated_at": now()})
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
                    f"✅ *Payment approved!*\n\n📦 Credits added: *+{amount:g}*\n💳 New balance: *{balance_after:g}*",
                    parse_mode="Markdown",
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
            await query.edit_message_text(final_text, parse_mode="Markdown", reply_markup=None)
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

    if state in {"admin_bkash_number", "admin_nagad_number", "admin_payment_number"}:
        method = "nagad" if state == "admin_nagad_number" else "bkash"
        if text.strip().lower() in {"off", "disable", "disabled", "none"}:
            digits = ""
        else:
            digits = re.sub(r"\D+", "", text)
            if not 8 <= len(digits) <= 15:
                await update.effective_message.reply_text("❌ Invalid number. 8–15 digits pathao, or send OFF to disable this payment method.")
                return
        save_settings({f"{method}_number": digits, **({"payment_number": digits} if digits else {})})
        audit("payment_number_changed", admin_id, {"method": method, "payment_number": digits})
        context.user_data.clear()
        await update.effective_message.reply_text(f"✅ {method.title()} number update hoyeche: `{digits}`", parse_mode="Markdown", reply_markup=main_keyboard(admin_id))
        return

    if state in {"admin_addcredits", "admin_deductcredits"}:
        parts = text.split()
        if len(parts) != 2:
            await update.effective_message.reply_text("Format: USER_ID_OR_PRIVATE_CHAT_ID AMOUNT\nExample: `123456789 25`", parse_mode="Markdown")
            return
        target_id = _safe_int(re.sub(r"^(user_id|userid|chat_id|chatid|user|chat):", "", parts[0], flags=re.I))
        amount = credits_float(parts[1])
        if target_id is None or target_id == 0 or amount <= 0:
            await update.effective_message.reply_text("❌ Invalid User ID/Chat ID or amount. Numeric Telegram ID and positive amount use koro.")
            return
        target_ref = user_ref(target_id)
        if not target_ref.get().exists:
            await update.effective_message.reply_text("❌ Ei ID-er bot account pai ni. User-ke age /start korte bolo, tarpor credit add koro.")
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
            await update.effective_message.reply_text("❌ Numeric Telegram User ID/private Chat ID pathao.")
            return
        target_ref = user_ref(target_id)
        if not target_ref.get().exists:
            await update.effective_message.reply_text("❌ User account not found. User-ke age bot start korte bolo.")
            return
        blocked = state == "admin_block"
        target_ref.update({"is_blocked": blocked, "updated_at": now()})
        audit("user_blocked" if blocked else "user_unblocked", admin_id, {"target_id": target_id})
        try:
            await context.bot.send_message(target_id, "⛔ Admin tomar account block koreche." if blocked else "✅ Admin tomar account unblock koreche.")
        except Exception:
            pass
        context.user_data.clear()
        await update.effective_message.reply_text(f"✅ User `{target_id}` {'blocked' if blocked else 'unblocked'}.", parse_mode="Markdown", reply_markup=main_keyboard(admin_id))
        return

    if state == "admin_createcode":
        parts = text.split()
        if len(parts) != 3:
            await update.effective_message.reply_text("Format: CREDITS MAX_USES DAYS\nExample: `25 100 30`\nMAX_USES=0 mane unlimited.", parse_mode="Markdown")
            return
        try:
            amount = credits_float(parts[0]); max_uses = int(parts[1]); days = int(parts[2])
            if amount <= 0 or max_uses < 0 or days < 0:
                raise ValueError
            alphabet = string.ascii_uppercase + string.digits
            code = "CALL-" + "".join(secrets.choice(alphabet) for _ in range(10))
            expires = now() + timedelta(days=days) if days else None
            db.collection(COL_CODES).document().set({
                "code": code, "credits": amount, "max_uses": max_uses, "uses": 0,
                "used_by": [], "active": True, "expires_at": expires,
                "created_by": admin_id, "created_at": now(), "updated_at": now(),
            })
            audit("redeem_code_created", admin_id, {"code": code, "credits": amount, "max_uses": max_uses, "days": days})
            await update.effective_message.reply_text(f"✅ Redeem code created:\n`{code}`\nCredits: {amount:g}\nMax uses: {'Unlimited' if max_uses == 0 else max_uses}\nExpires: {'Never' if not days else iso(expires)}", parse_mode="Markdown", reply_markup=main_keyboard(admin_id))
            context.user_data.clear()
        except Exception:
            await update.effective_message.reply_text("❌ Invalid values. CREDITS positive, MAX_USES and DAYS zero or greater hote hobe.")
        return

    if state == "admin_broadcast":
        await do_broadcast(update, context, text)
        return

async def do_broadcast(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str):
    if not text:
        await update.effective_message.reply_text("Message empty. Text pathao.")
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
    elif key in {"maintenance", "daily_bonus_enabled"}:
        value = value.lower() in {"1", "true", "on", "yes", "enabled"}
    elif key in {"payment_number", "bkash_number", "nagad_number"}:
        if value.lower() in {"off", "disable", "disabled", "none"} and key != "payment_number":
            value = ""
        else:
            value = re.sub(r"\D+", "", value)
            if not 8 <= len(value) <= 15:
                await update.effective_message.reply_text("Payment number must contain 8–15 digits (or use OFF for bKash_number/nagad_number).")
                return
        if key == "payment_number":
            key = "bkash_number"
    elif key in {"payment_review_chat_id", "required_channel"}:
        value = clean_text(value, 100)
        if not value:
            await update.effective_message.reply_text("Value cannot be empty.")
            return
        if key == "required_channel" and not value.startswith("@"):
            value = "@" + value.lstrip("/")
    elif key in {"brand_name", "support_text", "buy_text", "admin_notice"}:
        value = clean_text(value, 2000)
    else:
        await update.effective_message.reply_text("Unsupported setting. /help dekho.")
        return
    save_settings({key: value})
    audit("setting_changed", update.effective_user.id, {"key": key, "value": value})
    await update.effective_message.reply_text(f"✅ Updated `{key}`.", parse_mode="Markdown")

async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id if update.effective_user else 0
    lines = [
        "📘 Custom Call Bot Help", "",
        "📞 User Features", "/start — Dashboard open", "/call — Start a call", "/cancel — Cancel current action", 
        "Send Call, My Profile, Refer, LP Statistics, Buy Credits, Redeem, Call History, Support use koro.",
        "Referral Bonus: 1 Credit. Link share koro ar credit jite nao. Daily Bonus admin ON korle button dekhabe.",
        "Required channel join kora mandatory.", "",
    ]
    if is_admin(uid):
        lines += [
            "🛠 Admin Commands", "/admin — Admin Panel", "/help — This guide",
            "/addcredits USER_ID_OR_CHAT_ID AMOUNT", "/block USER_ID", "/unblock USER_ID",
            "",
            "⚙️ Settings using /set",
            "/set call_credit_cost 1", "/set daily_call_limit 20", "/set call_cooldown_seconds 15",
            "/set referral_bonus 1", "/set welcome_bonus 1", "/set daily_bonus 1",
            "/set daily_bonus_enabled true", "/set maintenance false",
            "/set bkash_number 01819202231", "/set nagad_number 01819202231", "/set nagad_number off to disable Nagad",
            "/set payment_review_chat_id @ffxemon", "/set required_channel @CyberShunya_x",
            "/set purchase_limit_count 3", "/set purchase_limit_minutes 10",
            "",
            "Credit add format: numeric Telegram user ID / private chat ID + amount. User must start bot first.",
            "Purchase protection: 3 transaction submission attempts per 10 minutes; invalid and duplicate Transaction IDs count toward the limit.",
            "Block/Unblock user Admin Panel-er buttons thekeo kora jay.",
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
            await context.bot.send_message(target_id, "⛔ Admin tomar account block koreche." if blocked else "✅ Admin tomar account unblock koreche.")
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
    if user_blocked(uid):
        await update.effective_message.reply_text("⛔ Your account is blocked. Support-er sathe contact koro.")
        return
    u = get_user(uid)
    cost = credits_float(get_settings().get("call_credit_cost", 1))
    if credits_float(u.get("balance", 0)) <= 0 or credits_float(u.get("balance", 0)) < cost:
        await update.effective_message.reply_text(f"❌ Call dite credit lagbe. Required: {cost:g} credits.", reply_markup=main_keyboard(uid))
        return
    context.user_data.clear()
    context.user_data["state"] = "call_phone"
    await update.effective_message.reply_text("📞 Destination phone number pathao.", reply_markup=back_button())

async def cancel_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data.clear()
    uid = update.effective_user.id
    await update.effective_message.reply_text("Cancelled. Dashboard-e fire gele features use korte parbe.", reply_markup=main_keyboard(uid))

async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE):
    try:
        if telegram_app:
            await telegram_app.bot.send_message(
                ADMIN_ID,
                f"⚠️ Bot error:\n`{clean_text(context.error, 1800)}`",
                parse_mode="Markdown",
            )
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
    await telegram_app.process_update(update)
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
    if status:
        updates["status"] = clean_text(status, 100)
    if recording_url:
        updates["recording_url"] = clean_text(recording_url, 2000)
    if duration is not None:
        try:
            updates["actual_duration"] = int(duration)
        except Exception:
            pass
    call_ref.update(updates)

    uid = _safe_int(call_data.get("user_id"))
    if uid is None or uid == 0:
        return {"ok": True, "updated": False, "reason": "Call record has no valid user ID"}
    if recording_url:
        try:
            await telegram_app.bot.send_message(
                uid,
                f"🎧 *Call recording is ready.*\nCall ID: `{provider_call_id}`",
                parse_mode="Markdown",
                reply_markup=InlineKeyboardMarkup(
                    [[InlineKeyboardButton("▶️ Listen Recording", url=str(recording_url))]]
                ),
            )
        except Exception:
            pass

    return {"ok": True, "updated": True}


@app.on_event("startup")
async def startup():
    global telegram_app
    ensure_settings()
    telegram_app = Application.builder().token(BOT_TOKEN).build()
    telegram_app.add_handler(CommandHandler("start", start_command))
    telegram_app.add_handler(CommandHandler("admin", admin_command))
    telegram_app.add_handler(CommandHandler("call", call_command))
    telegram_app.add_handler(CommandHandler("cancel", cancel_command))
    telegram_app.add_handler(CommandHandler("set", set_command))
    telegram_app.add_handler(CommandHandler("help", help_command))
    telegram_app.add_handler(CommandHandler("addcredits", addcredits_command))
    telegram_app.add_handler(CommandHandler("block", block_command))
    telegram_app.add_handler(CommandHandler("unblock", unblock_command))
    telegram_app.add_handler(ChatMemberHandler(track_channel_membership, ChatMemberHandler.CHAT_MEMBER))
    telegram_app.add_handler(CallbackQueryHandler(callback_handler))
    telegram_app.add_handler(MessageHandler(filters.AUDIO | filters.VOICE | filters.Document.ALL, handle_audio_message))
    telegram_app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text_message))
    telegram_app.add_error_handler(error_handler)

    await telegram_app.initialize()
    await telegram_app.start()

    if PUBLIC_BASE_URL:
        webhook_url = f"{PUBLIC_BASE_URL}/telegram/webhook"
        await telegram_app.bot.set_webhook(
            url=webhook_url,
            secret_token=TELEGRAM_WEBHOOK_SECRET or None,
            allowed_updates=Update.ALL_TYPES,
        )


@app.on_event("shutdown")
async def shutdown():
    global telegram_app
    if telegram_app:
        try:
            await telegram_app.stop()
            await telegram_app.shutdown()
        except Exception:
            pass


if __name__ == "__main__":
    import uvicorn
    uvicorn.run("app:app", host="0.0.0.0", port=PORT)
