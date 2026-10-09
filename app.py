
import os
import re
import json
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
                raise ValueError(f"Record already exists: {self.path}")
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
                    raise ValueError(f"Record already exists: {reference.path}")
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
    "settings_schema": 2,
    "brand_name": "Custom Call",
    "maintenance": False,
    "call_credit_cost": 1.0,
    "daily_call_limit": 20,
    "call_cooldown_seconds": 15,
    "referral_bonus": 1.0,
    "daily_bonus": 1.0,
    "daily_bonus_enabled": False,
    "payment_number": "01819202231",
    "payment_review_chat_id": PAYMENT_REVIEW_CHAT_ID or "@ffxemon",
    "min_redeem_credits": 1.0,
    "support_text": "Contact the administrator for support.",
    "buy_text": "Send the payment, then submit the transaction ID for admin approval.",
    "admin_notice": "Use this service only for lawful, authorized communications.",
    "packages": [
        {"id": "p50", "credits": 50, "price": 60, "label": "📞 ৫০ কল — ৬০ TK"},
        {"id": "p100", "credits": 100, "price": 100, "label": "📞 ১০০ কল — ১০০ TK"},
        {"id": "p200", "credits": 200, "price": 180, "label": "📞 ২০০ কল — ১৮০ TK"},
        {"id": "p300", "credits": 300, "price": 240, "label": "📞 ৩০০ কল — ২৪০ TK"},
        {"id": "p500", "credits": 500, "price": 380, "label": "📞 ৫০০ কল — ৩৮০ TK"},
    ],
    "payment_methods": [
        {"name": "bKash", "account": "01819202231"},
        {"name": "Nagad", "account": "01819202231"},
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


def user_ref(user_id: int):
    return db.collection(COL_USERS).document(str(user_id))


def get_settings() -> dict:
    ref = db.collection(COL_SETTINGS).document("app")
    snap = ref.get()
    data = snap.to_dict() if snap.exists else {}
    if not data:
        ref.set(DEFAULT_SETTINGS)
        data = dict(DEFAULT_SETTINGS)
    elif int(data.get("settings_schema", 0) or 0) < 2:
        data.update({
            "settings_schema": 2,
            "referral_bonus": 1.0,
            "daily_bonus_enabled": False,
            "payment_number": data.get("payment_number") or "01819202231",
            "payment_review_chat_id": data.get("payment_review_chat_id") or "@ffxemon",
            "packages": list(DEFAULT_SETTINGS["packages"]),
        })
        ref.set(data, merge=True)
    merged = dict(DEFAULT_SETTINGS)
    merged.update(data)
    if "packages" not in merged or not isinstance(merged["packages"], list):
        merged["packages"] = list(DEFAULT_SETTINGS["packages"])
    if "payment_methods" not in merged or not isinstance(merged["payment_methods"], list):
        merged["payment_methods"] = list(DEFAULT_SETTINGS["payment_methods"])
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


def default_user_payload(tg_user, referrer_id: Optional[int] = None):
    return {
        "user_id": tg_user.id,
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
        "referred_by": int(referrer_id) if referrer_id else None,
        "is_blocked": False,
        "created_at": now(),
        "updated_at": now(),
        "last_call_at": None,
        "call_day": None,
        "calls_today": 0,
        "last_daily_bonus": None,
    }


def ensure_user(tg_user, referrer_id: Optional[int] = None):
    with _TRANSACTION_LOCK:
        ref = user_ref(tg_user.id)
        snap = ref.get()
        if snap.exists:
            ref.set({
                "username": safe_username(tg_user),
                "first_name": clean_text(tg_user.first_name, 100),
                "last_name": clean_text(tg_user.last_name, 100),
                "updated_at": now(),
            }, merge=True)
            return snap.to_dict() or {}
        payload = default_user_payload(tg_user, referrer_id)
        ref.set(payload)
        if referrer_id and referrer_id != tg_user.id:
            referrer = user_ref(referrer_id)
            rsnap = referrer.get()
            if rsnap.exists:
                settings = get_settings()
                bonus = credits_float(settings.get("referral_bonus", 1))
                if bonus > 0:
                    add_credits(
                        referrer_id,
                        bonus,
                        "referral_bonus",
                        f"new_user:{tg_user.id}",
                    )
                    referrer.update({"referrals": firestore.Increment(1)})
                    try:
                        if telegram_app:
                            asyncio.create_task(
                                telegram_app.bot.send_message(
                                    chat_id=referrer_id,
                                    text=f"🎉 Referral bonus credited: +{bonus:g} credits.",
                                )
                            )
                    except Exception:
                        pass
        return payload


def audit(action: str, actor_id: int, data: Optional[dict] = None):
    db.collection(COL_AUDIT).add({
        "action": clean_text(action, 200),
        "actor_id": actor_id,
        "data": data or {},
        "created_at": now(),
    })


def add_credits(user_id: int, amount: float, reason: str, reference: str = "") -> float:
    amount = credits_float(amount)
    if amount <= 0:
        raise ValueError("Amount must be positive")
    ref = user_ref(user_id)
    transaction = db.transaction()

    @firestore.transactional
    def apply(transaction):
        snap = ref.get(transaction=transaction)
        if not snap.exists:
            raise ValueError("User not found")
        data = snap.to_dict() or {}
        before = credits_float(data.get("balance", 0))
        after = credits_float(before + amount)
        transaction.update(ref, {"balance": after, "updated_at": now()})
        transaction.create(db.collection(COL_LEDGER).document(), {
            "user_id": user_id,
            "type": reason,
            "amount": amount,
            "before": before,
            "after": after,
            "reference": clean_text(reference, 200),
            "created_at": now(),
        })
        return after

    return apply(transaction)


def deduct_credits(user_id: int, amount: float, reason: str, reference: str = "") -> float:
    amount = credits_float(amount)
    if amount <= 0:
        raise ValueError("Amount must be positive")
    ref = user_ref(user_id)
    transaction = db.transaction()

    @firestore.transactional
    def apply(transaction):
        snap = ref.get(transaction=transaction)
        if not snap.exists:
            raise ValueError("User not found")
        data = snap.to_dict() or {}
        before = credits_float(data.get("balance", 0))
        if before < amount:
            raise ValueError("Insufficient credits")
        after = credits_float(before - amount)
        transaction.update(ref, {"balance": after, "updated_at": now()})
        transaction.create(db.collection(COL_LEDGER).document(), {
            "user_id": user_id,
            "type": reason,
            "amount": -amount,
            "before": before,
            "after": after,
            "reference": clean_text(reference, 200),
            "created_at": now(),
        })
        return after

    return apply(transaction)


def refund_credits(user_id: int, amount: float, reason: str, reference: str = "") -> float:
    return add_credits(user_id, amount, reason, reference)


def is_admin(user_id: int) -> bool:
    return int(user_id) == ADMIN_ID


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
        [
            InlineKeyboardButton("📞 Send Call", callback_data="menu:call"),
            InlineKeyboardButton("👤 My Profile", callback_data="menu:profile"),
        ],
        [
            InlineKeyboardButton("👥 Refer", callback_data="menu:refer"),
            InlineKeyboardButton("📊 LP Statistics", callback_data="menu:stats"),
        ],
        [
            InlineKeyboardButton("💰 Buy Credits", callback_data="menu:buy"),
            InlineKeyboardButton("🎁 Redeem", callback_data="menu:redeem"),
        ],
        [
            InlineKeyboardButton("📞 Call History", callback_data="menu:history"),
            InlineKeyboardButton("☎️ Support", callback_data="menu:support"),
        ],
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
    if not tg_user:
        return
    args = context.args if update.message and update.message.text else []
    referrer_id = None
    if args:
        m = re.match(r"ref_(\d+)$", args[0])
        if m:
            referrer_id = int(m.group(1))
    ensure_user(tg_user, referrer_id)
    settings = get_settings()
    data = get_user(tg_user.id)
    if data.get("is_blocked"):
        await update.effective_message.reply_text("⛔ Your account is blocked.")
        return
    maintenance = bool(settings.get("maintenance", False))
    notice = settings.get("admin_notice", "")
    text = (
        f"✨ *{clean_text(settings.get('brand_name', 'Custom Call'), 60)}*\n\n"
        f"💳 Balance: *{format_balance(data.get('balance', 0))} credits*\n"
        f"📞 Calls: *{int(data.get('total_calls', 0))}*\n"
        f"👥 Referrals: *{int(data.get('referrals', 0))}*\n"
    )
    if maintenance and not is_admin(tg_user.id):
        text += "\n🛠 Service is currently in maintenance mode."
    if notice:
        text += f"\n\nℹ️ {clean_text(notice, 700)}"
    await update.effective_message.reply_text(
        text,
        parse_mode="Markdown",
        reply_markup=main_keyboard(tg_user.id),
    )


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
    ensure_user(query.from_user)
    if data == "menu:home":
        context.user_data.clear()
        await edit_or_send(
            query,
            "🏠 *Dashboard*\n\nChoose an option:",
            main_keyboard(user_id),
        )
        return

    if data == "menu:profile":
        u = get_user(user_id)
        text = (
            "👤 *My Profile*\n\n"
            f"ID: `{user_id}`\n"
            f"Username: @{u.get('username') or 'none'}\n"
            f"Balance: *{format_balance(u.get('balance', 0))} credits*\n"
            f"Total Calls: *{int(u.get('total_calls', 0))}*\n"
            f"Successful: *{int(u.get('successful_calls', 0))}*\n"
            f"Failed: *{int(u.get('failed_calls', 0))}*\n"
            f"Total Seconds: *{int(u.get('total_seconds', 0))}*\n"
            f"Referrals: *{int(u.get('referrals', 0))}*"
        )
        await edit_or_send(query, text, back_button())
        return

    if data == "menu:refer":
        referral_link = f"https://t.me/{(await context.bot.get_me()).username}?start=ref_{user_id}"
        settings = get_settings()
        bonus = credits_float(settings.get("referral_bonus", 0))
        text = (
            "👥 *Referral*\n\n"
            f"Invite link:\n`{referral_link}`\n\n"
            f"Referral bonus: *{bonus:g} credits*\n"
            "Share the link with people who have permission to receive calls."
        )
        await edit_or_send(query, text, back_button())
        return

    if data == "menu:stats":
        settings = get_settings()
        totals = await local_stats()
        text = (
            "📊 *LP Statistics*\n\n"
            f"Users: *{totals['users']}*\n"
            f"Total Calls: *{totals['calls']}*\n"
            f"Successful Calls: *{totals['success']}*\n"
            f"Failed Calls: *{totals['failed']}*\n"
            f"Credits in circulation: *{format_balance(totals['credits'])}*\n"
            f"Daily call limit: *{int(settings.get('daily_call_limit', 20))}*"
        )
        await edit_or_send(query, text, back_button())
        return

    if data == "menu:history":
        docs = db.collection(COL_CALLS).where("user_id", "==", user_id).limit(25).stream()
        items = sorted(
            list(docs),
            key=lambda s: str((s.to_dict() or {}).get("created_at") or ""),
            reverse=True,
        )[:10]
        if not items:
            text = "📞 *Call History*\n\nNo calls yet."
            await edit_or_send(query, text, back_button())
            return
        lines = ["📞 *Recent Calls*\n"]
        for snap in items:
            c = snap.to_dict() or {}
            status = str(c.get("status", "unknown")).upper()
            number = str(c.get("number", ""))[-4:]
            when = iso(c.get("created_at")) or "-"
            lines.append(f"• `****{number}` — *{status}* — {when[:16]}")
        await edit_or_send(query, "\n".join(lines), back_button())
        return

    if data == "menu:support":
        settings = get_settings()
        await edit_or_send(query, f"☎️ *Support*\n\n{clean_text(settings.get('support_text', 'Contact admin.'), 2000)}", back_button())
        return

    if data == "menu:buy":
        await show_buy(query, context)
        return

    if data.startswith("buy:"):
        pkg_id = data.split(":", 1)[1]
        await select_package(query, context, pkg_id)
        return

    if data == "menu:redeem":
        context.user_data.clear()
        context.user_data["state"] = "redeem_code"
        await edit_or_send(query, "🎁 *Redeem*\n\nSend your redeem code.", back_button())
        return

    if data == "menu:call":
        context.user_data.clear()
        context.user_data["state"] = "call_phone"
        await edit_or_send(
            query,
            "📞 *Send Call*\n\nSend the destination phone number.\nExample: `01700000000`",
            back_button(),
        )
        return

    if data.startswith("callmode:"):
        mode = data.split(":", 1)[1]
        context.user_data["call_mode"] = mode
        if mode == "text":
            context.user_data["state"] = "call_content_text"
            await edit_or_send(query, "📝 Send the text that will be spoken on the call.", back_button())
        elif mode == "audio_url":
            context.user_data["state"] = "call_content_audio_url"
            await edit_or_send(query, "🔗 Send a direct MP3/WAV/OGG URL.", back_button())
        else:
            context.user_data["state"] = "call_content_audio_upload"
            await edit_or_send(query, "🎧 Send an audio/voice file here.", back_button())
        return

    if data.startswith("calltime:"):
        seconds = int(data.split(":", 1)[1])
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

    if data == "buy:back":
        await show_buy(query, context)
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
    rows = [[InlineKeyboardButton(p.get("label", f"{p.get('credits')} calls"), callback_data=f"buy:{p.get('id')}")] for p in packages]
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data="menu:home")])
    payment_number = clean_text(settings.get("payment_number", "01819202231"), 40)
    text = (
        "💰 *Credit Purchase*\n"
        "━━━━━━━━━━━━━━━━━\n\n"
        "📦 *Available Packages:*\n\n"
        + "\n".join([f"• {clean_text(pkg.get('label'), 100)}" for pkg in packages])
        + "\n━━━━━━━━━━━━━━━━━\n"
        + f"💳 Payment: bKash / Nagad — `{payment_number}`\n"
        + "⚡ Admin approve করলে credit auto add হবে।\n\n"
        + "👇 নিচ থেকে package বেছে নিন:"
    )
    await edit_or_send(query, text, InlineKeyboardMarkup(rows))


async def select_package(query, context, pkg_id: str):
    settings = get_settings()
    package = next((p for p in settings.get("packages", []) if p.get("id") == pkg_id), None)
    if not package:
        await edit_or_send(query, "Package not found.", back_button())
        return
    context.user_data["state"] = "payment_txn"
    context.user_data["payment_package"] = package
    await edit_or_send(
        query,
        (
            f"💳 *{clean_text(package.get('label', 'Package'), 100)}*\n\n"
            f"Credits: *{credits_float(package.get('credits', 0)):g}*\n"
            f"Price: *৳{package.get('price', 0)}*\n\n"
            "Send your payment transaction ID. The admin will verify it."
        ),
        back_button(),
    )


async def handle_text_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not update.effective_message:
        return
    ensure_user(update.effective_user)
    user_id = update.effective_user.id

    if user_blocked(user_id):
        await update.effective_message.reply_text("⛔ Your account is blocked.")
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
        phone = normalize_phone(text)
        if not phone:
            await update.effective_message.reply_text("❌ Invalid phone number. Try again.")
            return
        context.user_data["call_phone"] = phone
        context.user_data["state"] = "call_mode"
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton("📝 Text to Speech", callback_data="callmode:text")],
            [InlineKeyboardButton("🔗 Audio URL", callback_data="callmode:audio_url")],
            [InlineKeyboardButton("🎧 Upload Audio", callback_data="callmode:audio_upload")],
            [InlineKeyboardButton("❌ Cancel", callback_data="call:cancel")],
        ])
        await update.effective_message.reply_text(
            f"📞 Number: `{phone}`\n\nChoose how the call audio should be supplied.",
            parse_mode="Markdown",
            reply_markup=markup,
        )
        return

    if state == "call_content_text":
        if not text:
            await update.effective_message.reply_text("❌ Text is required.")
            return
        context.user_data["call_text"] = text
        await ask_call_time(update)
        return

    if state == "call_content_audio_url":
        if not re.match(r"^https?://", text, re.I):
            await update.effective_message.reply_text("❌ Send a valid http/https direct audio URL.")
            return
        if not re.search(r"\.(mp3|wav|ogg)(\?.*)?$", text, re.I):
            await update.effective_message.reply_text("⚠️ The URL should point directly to MP3, WAV, or OGG.")
            return
        context.user_data["call_audio_url"] = text
        await ask_call_time(update)
        return

    if state == "call_content_audio_upload":
        await update.effective_message.reply_text("🎧 Please upload an audio or voice file.")
        return

    if state == "admin_broadcast":
        await do_broadcast(update, context, text)
        return

    await update.effective_message.reply_text(
        "Use the dashboard buttons below.",
        reply_markup=main_keyboard(user_id),
    )


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
    ensure_user(update.effective_user)
    user_id = update.effective_user.id
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
    if u.get("is_blocked"):
        await update.callback_query.message.reply_text("⛔ Your account is blocked.")
        return
    if settings.get("maintenance") and not is_admin(user_id):
        await update.callback_query.message.reply_text("🛠 Calls are temporarily disabled.")
        return

    phone = context.user_data.get("call_phone")
    txt = context.user_data.get("call_text")
    audio = context.user_data.get("call_audio_url")
    seconds = int(context.user_data.get("call_time", 30))
    if not phone or (not txt and not audio):
        await update.callback_query.message.reply_text("❌ Call session is incomplete. Start again.")
        context.user_data.clear()
        return

    now_dt = now()
    last_call = parse_datetime(u.get("last_call_at"))
    cooldown = int(settings.get("call_cooldown_seconds", 15))
    if last_call is not None:
        elapsed = (now_dt - last_call).total_seconds()
        if elapsed < cooldown and not is_admin(user_id):
            wait = max(1, int(cooldown - elapsed))
            await update.callback_query.message.reply_text(f"⏳ Please wait {wait}s before the next call.")
            return

    day_key = local_day_key()
    calls_today = int(u.get("calls_today", 0))
    if u.get("call_day") != day_key:
        calls_today = 0
    limit = int(settings.get("daily_call_limit", 20))
    if calls_today >= limit and not is_admin(user_id):
        await update.callback_query.message.reply_text("🚫 Daily call limit reached.")
        context.user_data.clear()
        return

    cost = credits_float(settings.get("call_credit_cost", 1))
    if not is_admin(user_id) and credits_float(u.get("balance", 0)) < cost:
        await update.callback_query.message.reply_text(
            f"❌ Insufficient credits.\nRequired: {cost:g}"
        )
        context.user_data.clear()
        return

    log_ref = db.collection(COL_CALLS).document()
    call_doc = {
        "user_id": user_id,
        "number": phone,
        "mode": "text" if txt else "audio",
        "time": seconds,
        "status": "pending",
        "provider_call_id": None,
        "recording_url": None,
        "created_at": now_dt,
        "updated_at": now_dt,
        "cost": cost,
        "api_response": None,
    }
    log_ref.set(call_doc)

    try:
        if not is_admin(user_id) and cost > 0:
            deduct_credits(user_id, cost, "call_charge", log_ref.id)
        user_ref(user_id).set(
            {
                "last_call_at": now_dt,
                "call_day": day_key,
                "calls_today": calls_today + 1,
                "updated_at": now_dt,
            },
            merge=True,
        )
    except Exception as exc:
        log_ref.update({"status": "rejected", "error": clean_text(exc, 1000), "updated_at": now()})
        await update.callback_query.message.reply_text(f"❌ {clean_text(exc, 500)}")
        context.user_data.clear()
        return

    await update.callback_query.message.reply_text("📡 Sending call request...")
    try:
        result = await provider_call(phone, txt=txt, audio=audio, seconds=seconds)
        success = result.get("status") == "success"
        provider_data = result.get("data") if isinstance(result.get("data"), dict) else {}
        provider_id = (
            provider_data.get("id")
            or provider_data.get("call_id")
            or result.get("call_id")
            or result.get("id")
        )
        recording_url = (
            provider_data.get("recording_url")
            or provider_data.get("recording")
            or provider_data.get("audio_url")
            or result.get("recording_url")
            or result.get("recording")
        )
        log_ref.update(
            {
                "status": "submitted" if success else "failed",
                "provider_call_id": clean_text(provider_id, 300) if provider_id else None,
                "recording_url": clean_text(recording_url, 2000) if recording_url else None,
                "api_response": result,
                "updated_at": now(),
            }
        )
        if success:
            user_ref(user_id).set(
                {
                    "total_calls": firestore.Increment(1),
                    "successful_calls": firestore.Increment(1),
                    "total_seconds": firestore.Increment(seconds),
                    "updated_at": now(),
                },
                merge=True,
            )
            msg = (
                "✅ *Call request submitted*\n\n"
                f"📞 Number: `****{phone[-4:]}`\n"
                f"⏱ Duration: `{seconds}s`\n"
                f"💳 Cost: `{cost:g}` credits\n"
                f"🆔 Call ID: `{clean_text(provider_id or log_ref.id, 200)}`\n\n"
                f"Provider: {clean_text(result.get('message', 'Accepted'), 900)}"
            )
            if recording_url:
                msg += "\n🎧 Recording is available."
                markup = InlineKeyboardMarkup(
                    [[InlineKeyboardButton("▶️ Listen Recording", url=str(recording_url))]]
                )
                await update.callback_query.message.reply_text(msg, parse_mode="Markdown", reply_markup=markup)
            else:
                await update.callback_query.message.reply_text(msg, parse_mode="Markdown")
        else:
            user_ref(user_id).set(
                {
                    "total_calls": firestore.Increment(1),
                    "failed_calls": firestore.Increment(1),
                    "updated_at": now(),
                },
                merge=True,
            )
            if not is_admin(user_id) and cost > 0:
                refund_credits(user_id, cost, "call_refund", log_ref.id)
            await update.callback_query.message.reply_text(
                f"❌ Call failed.\n\n{clean_text(result.get('message', 'Provider returned an error.'), 1200)}"
            )
    except Exception as exc:
        log_ref.update({"status": "failed", "error": clean_text(exc, 1000), "updated_at": now()})
        user_ref(user_id).set(
            {
                "total_calls": firestore.Increment(1),
                "failed_calls": firestore.Increment(1),
                "updated_at": now(),
            },
            merge=True,
        )
        if not is_admin(user_id) and cost > 0:
            try:
                refund_credits(user_id, cost, "call_refund_exception", log_ref.id)
            except Exception:
                pass
        await update.callback_query.message.reply_text(f"❌ Provider error: {clean_text(exc, 900)}")
    finally:
        context.user_data.clear()


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
    async with httpx.AsyncClient(timeout=45.0) as client:
        response = await client.post(f"{CALL_API_BASE}/call", data=payload)
        try:
            data = response.json()
        except Exception:
            data = {"status": "error", "message": response.text}
        if response.status_code >= 400 and data.get("status") != "success":
            return {
                "status": "error",
                "message": clean_text(data.get("message", f"HTTP {response.status_code}"), 1500),
                "http_code": response.status_code,
            }
        return data


async def account_api(endpoint: str) -> dict:
    async with httpx.AsyncClient(timeout=30.0) as client:
        response = await client.get(
            f"{CALL_API_BASE}/{endpoint}",
            params={"api_token": CALL_API_TOKEN},
        )
        try:
            data = response.json()
        except Exception:
            data = {"status": "error", "message": response.text}
        return data


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
        transaction.create(db.collection(COL_LEDGER).document(), {
            "user_id": user_id,
            "type": "daily_bonus",
            "amount": bonus,
            "before": before,
            "after": after,
            "reference": today,
            "created_at": now(),
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
        uses = int(data.get("uses", 0))
        max_uses = int(data.get("max_uses", 1))
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
        transaction.create(db.collection(COL_LEDGER).document(), {
            "user_id": user_id,
            "type": "redeem",
            "amount": amount,
            "before": before,
            "after": after,
            "reference": code,
            "created_at": now(),
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
    if not package:
        await update.effective_message.reply_text("❌ Package session expired. Open Buy Credits again.")
        context.user_data.clear()
        return
    txn_id = clean_text(txn_id, 100)
    if not re.fullmatch(r"[A-Za-z0-9_-]{3,100}", txn_id):
        await update.effective_message.reply_text("❌ Transaction ID must be 3–100 letters, digits, underscores, or hyphens.")
        return
    duplicates = list(db.collection(COL_PAYMENTS).where("transaction_id", "==", txn_id).limit(1).stream())
    if duplicates:
        await update.effective_message.reply_text("❌ This transaction ID has already been submitted.")
        return
    ref = db.collection(COL_PAYMENTS).document()
    settings = get_settings()
    payload = {
        "user_id": user_id,
        "username": safe_username(user),
        "first_name": clean_text(user.first_name, 100),
        "package_id": package.get("id"),
        "package_label": package.get("label"),
        "credits": credits_float(package.get("credits", 0)),
        "price": int(package.get("price", 0)),
        "transaction_id": txn_id,
        "payment_number": clean_text(settings.get("payment_number", "01819202231"), 40),
        "status": "pending",
        "created_at": now(),
        "updated_at": now(),
    }
    ref.set(payload)
    audit("payment_request_created", user_id, {"payment_id": ref.id, "package_id": package.get("id")})
    context.user_data.clear()
    group_message = (
        "🧾 *NEW CREDIT PURCHASE REQUEST*\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"🆔 Request: `{ref.id}`\n"
        f"👤 User: {escape_markdown(clean_text(user.full_name, 120), version=1)} (@{escape_markdown(safe_username(user) or 'no_username', version=1)})\n"
        f"🪪 Telegram ID: `{user_id}`\n"
        f"📦 Package: {escape_markdown(clean_text(package.get('label'), 120), version=1)}\n"
        f"💳 Amount: *৳{int(package.get('price', 0))}*\n"
        f"📱 Payment Number: `{payload['payment_number']}`\n"
        f"🧾 Transaction ID: `{txn_id}`\n"
        "━━━━━━━━━━━━━━━━━\n"
        "Review the transaction before approving. Credits will be added only once."
    )
    review_markup = InlineKeyboardMarkup([
        [
            InlineKeyboardButton("✅ Approve & Add Credits", callback_data=f"pay:approve:{ref.id}"),
            InlineKeyboardButton("❌ Reject", callback_data=f"pay:reject:{ref.id}"),
        ]
    ])
    review_chat = clean_text(settings.get("payment_review_chat_id") or PAYMENT_REVIEW_CHAT_ID, 100)
    notified = False
    notify_error = None
    try:
        await context.bot.send_message(
            chat_id=review_chat,
            text=group_message,
            parse_mode="Markdown",
            reply_markup=review_markup,
        )
        notified = True
    except Exception as exc:
        notify_error = clean_text(exc, 500)
        ref.update({"review_notify_error": notify_error, "updated_at": now()})
        try:
            await context.bot.send_message(ADMIN_ID, f"⚠️ Could not post payment request to {review_chat}.\nRequest: {ref.id}\nError: {notify_error}")
        except Exception:
            pass
    confirmation = (
        "✅ Payment request submitted!\n"
        f"🆔 Request ID: `{ref.id}`\n"
        + ("📨 Admin review group-এ পাঠানো হয়েছে। Approve হলে credit automatically যোগ হবে।" if notified else "⚠️ Request saved, but group notification failed. Admin has been notified.")
    )
    await update.effective_message.reply_text(
        confirmation,
        parse_mode="Markdown",
        reply_markup=main_keyboard(user_id),
    )


async def local_stats() -> dict:
    users = list(db.collection(COL_USERS).stream())
    calls = list(db.collection(COL_CALLS).stream())
    credits = sum(credits_float((x.to_dict() or {}).get("balance", 0)) for x in users)
    success = sum(1 for x in calls if (x.to_dict() or {}).get("status") == "submitted")
    failed = sum(1 for x in calls if (x.to_dict() or {}).get("status") == "failed")
    return {
        "users": len(users),
        "calls": len(calls),
        "success": success,
        "failed": failed,
        "credits": credits,
    }


async def admin_menu(query):
    settings = get_settings()
    daily_state = "ON ✅" if settings.get("daily_bonus_enabled", False) else "OFF ⛔"
    rows = [
        [
            InlineKeyboardButton("📈 Overview", callback_data="admin:overview"),
            InlineKeyboardButton("👥 Users", callback_data="admin:users"),
        ],
        [
            InlineKeyboardButton("💳 Add Credits", callback_data="admin:addcredits"),
            InlineKeyboardButton("➖ Deduct Credits", callback_data="admin:deductcredits"),
        ],
        [
            InlineKeyboardButton("🎁 Create Redeem", callback_data="admin:createcode"),
            InlineKeyboardButton("📜 Redeem Codes", callback_data="admin:codes"),
        ],
        [
            InlineKeyboardButton("💰 Payments", callback_data="admin:payments"),
            InlineKeyboardButton("📞 Call Logs", callback_data="admin:calls"),
        ],
        [
            InlineKeyboardButton("📣 Broadcast", callback_data="admin:broadcast"),
            InlineKeyboardButton("⚙️ Settings", callback_data="admin:settings"),
        ],
        [
            InlineKeyboardButton("💳 Change Payment Number", callback_data="admin:paymentnumber"),
            InlineKeyboardButton(f"🎁 Daily Bonus: {daily_state}", callback_data="admin:toggle_daily"),
        ],
        [
            InlineKeyboardButton("🔌 Provider", callback_data="admin:provider"),
            InlineKeyboardButton("🛡 Safety", callback_data="admin:safety"),
        ],
        [InlineKeyboardButton("⬅️ Home", callback_data="menu:home")],
    ]
    await edit_or_send(query, "🛠 *Admin Panel*\n\nManage payments, bonuses, users, and call settings.", InlineKeyboardMarkup(rows))

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
        await edit_or_send(query, "💳 Send: `USER_ID AMOUNT`", back_button())
    elif action == "deductcredits":
        context.user_data["state"] = "admin_deductcredits"
        await edit_or_send(query, "➖ Send: `USER_ID AMOUNT`", back_button())
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
                f"{int(c.get('uses', 0))}/{int(c.get('max_uses', 0)) if int(c.get('max_uses', 0)) else '∞'} — "
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
            f"Daily limit: *{int(s.get('daily_call_limit', 20))}*\n"
            f"Cooldown: *{int(s.get('call_cooldown_seconds', 15))}s*\n"
            f"Referral bonus: *{credits_float(s.get('referral_bonus', 0)):g}*\n"
            f"Daily bonus: *{credits_float(s.get('daily_bonus', 0)):g}*\n"
            f"Daily bonus enabled: *{bool(s.get('daily_bonus_enabled', False))}*\n"
            f"Payment number: `{clean_text(s.get('payment_number', '01819202231'), 40)}`\n"
            f"Review group: `{clean_text(s.get('payment_review_chat_id', PAYMENT_REVIEW_CHAT_ID), 100)}`\n\n"
            "Use `/set setting value` to update other settings."
        )
        rows = [
            [InlineKeyboardButton("💳 Change Payment Number", callback_data="admin:paymentnumber")],
            [InlineKeyboardButton("🎁 Toggle Daily Bonus", callback_data="admin:toggle_daily")],
            [InlineKeyboardButton("⬅️ Back to Admin", callback_data="admin:menu")],
        ]
        await edit_or_send(query, text, InlineKeyboardMarkup(rows))
    elif action == "paymentnumber":
        context.user_data["state"] = "admin_payment_number"
        current_number = clean_text(get_settings().get("payment_number", "01819202231"), 40)
        await edit_or_send(
            query,
            f"💳 *Change Payment Number*\n\nCurrent number: `{current_number}`\n\nSend the new bKash/Nagad number. Example: `01819202231`",
            back_button(),
        )
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
            user_id = int(payment.get("user_id"))
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
                transaction.create(db.collection(COL_LEDGER).document(), {
                    "user_id": user_id,
                    "type": "purchase",
                    "amount": amount,
                    "before": current_balance,
                    "after": new_balance,
                    "reference": payment_id,
                    "created_at": now(),
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
    user_id = update.effective_user.id
    state = context.user_data.get("state")

    if state == "admin_payment_number":
        digits = re.sub(r"\D+", "", text)
        if not 8 <= len(digits) <= 15:
            await update.effective_message.reply_text("❌ Invalid number. Send 8–15 digits, including country code if needed.")
            return
        save_settings({"payment_number": digits})
        audit("payment_number_changed", user_id, {"payment_number": digits})
        context.user_data.clear()
        await update.effective_message.reply_text(
            f"✅ Payment number updated to `{digits}`.\nIt will now appear in Buy Credits.",
            parse_mode="Markdown",
            reply_markup=main_keyboard(user_id),
        )
        return

    if state in {"admin_addcredits", "admin_deductcredits"}:
        parts = text.split()
        if len(parts) != 2:
            await update.effective_message.reply_text("Format: USER_ID AMOUNT")
            return
        try:
            target_id = int(parts[0])
            amount = credits_float(parts[1])
            if amount <= 0:
                raise ValueError
            if state == "admin_addcredits":
                after = add_credits(target_id, amount, "admin_add", str(user_id))
                action = "added"
            else:
                after = deduct_credits(target_id, amount, "admin_deduct", str(user_id))
                action = "deducted"
            audit(state, user_id, {"target_id": target_id, "amount": amount})
            try:
                await context.bot.send_message(target_id, f"💳 {amount:g} credits {action}. New balance: {after:g}")
            except Exception:
                pass
            await update.effective_message.reply_text(f"✅ Done. New balance: {after:g}", reply_markup=main_keyboard(user_id))
            context.user_data.clear()
        except Exception as exc:
            await update.effective_message.reply_text(f"❌ {clean_text(exc, 500)}")
        return

    if state == "admin_createcode":
        parts = text.split()
        if len(parts) != 3:
            await update.effective_message.reply_text("Format: CREDITS MAX_USES DAYS")
            return
        try:
            amount = credits_float(parts[0])
            max_uses = int(parts[1])
            days = int(parts[2])
            if amount <= 0 or max_uses < 0 or days < 0:
                raise ValueError
            alphabet = string.ascii_uppercase + string.digits
            code = "CALL-" + "".join(secrets.choice(alphabet) for _ in range(10))
            expires = now() + timedelta(days=days) if days else None
            db.collection(COL_CODES).document().set({
                "code": code,
                "credits": amount,
                "max_uses": max_uses,
                "uses": 0,
                "used_by": [],
                "active": True,
                "expires_at": expires,
                "created_by": user_id,
                "created_at": now(),
                "updated_at": now(),
            })
            audit("redeem_code_created", user_id, {"code": code, "credits": amount, "max_uses": max_uses, "days": days})
            await update.effective_message.reply_text(
                f"✅ Redeem code created:\n`{code}`\n\nCredits: {amount:g}\nMax uses: {'Unlimited' if max_uses == 0 else max_uses}\nExpires: {'Never' if days == 0 else (expires.astimezone(UTC).isoformat() if expires else '-')}",
                parse_mode="Markdown",
                reply_markup=main_keyboard(user_id),
            )
            context.user_data.clear()
        except Exception:
            await update.effective_message.reply_text("❌ Invalid values.")
        return

    if state == "admin_broadcast":
        await do_broadcast(update, context, text)
        return


async def do_broadcast(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str):
    if not text:
        await update.effective_message.reply_text("Message is empty.")
        return
    users = list(db.collection(COL_USERS).stream())
    ok = 0
    fail = 0
    for snap in users:
        uid = int(snap.id)
        u = snap.to_dict() or {}
        if u.get("is_blocked"):
            continue
        try:
            await context.bot.send_message(uid, text)
            ok += 1
        except Exception:
            fail += 1
        await asyncio.sleep(0.05)
    audit("broadcast", update.effective_user.id, {"success": ok, "failed": fail})
    context.user_data.clear()
    await update.effective_message.reply_text(
        f"📣 Broadcast finished.\nSent: {ok}\nFailed: {fail}",
        reply_markup=main_keyboard(update.effective_user.id),
    )


async def admin_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not is_admin(update.effective_user.id):
        await update.effective_message.reply_text("⛔ Admin only.")
        return
    ensure_user(update.effective_user)
    await update.effective_message.reply_text("🛠 Admin Panel", reply_markup=main_keyboard(update.effective_user.id))


async def set_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.effective_user or not is_admin(update.effective_user.id):
        return
    if len(context.args) < 2:
        await update.effective_message.reply_text("Usage: /set key value")
        return
    key = context.args[0]
    value = " ".join(context.args[1:])
    numeric_keys = {
        "call_credit_cost": float,
        "daily_call_limit": int,
        "call_cooldown_seconds": int,
        "referral_bonus": float,
        "daily_bonus": float,
    }
    if key in numeric_keys:
        try:
            value = numeric_keys[key](value)
            if value < 0:
                raise ValueError
        except Exception:
            await update.effective_message.reply_text("Invalid numeric value.")
            return
    elif key in {"maintenance", "daily_bonus_enabled"}:
        value = value.lower() in {"1", "true", "on", "yes", "enabled"}
    elif key == "payment_number":
        value = re.sub(r"\D+", "", value)
        if not 8 <= len(value) <= 15:
            await update.effective_message.reply_text("Payment number must contain 8–15 digits.")
            return
    elif key == "payment_review_chat_id":
        value = clean_text(value, 100)
    elif key in {"brand_name", "support_text", "buy_text", "admin_notice"}:
        value = clean_text(value, 2000)
    else:
        await update.effective_message.reply_text("Unsupported setting.")
        return
    save_settings({key: value})
    audit("setting_changed", update.effective_user.id, {"key": key, "value": value})
    await update.effective_message.reply_text(f"✅ Updated `{key}`.", parse_mode="Markdown")


async def start_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        await send_home(update, context)
    except Exception as exc:
        await update.effective_message.reply_text(f"⚠️ Temporary error: {clean_text(exc, 500)}")


async def call_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ensure_user(update.effective_user)
    context.user_data.clear()
    context.user_data["state"] = "call_phone"
    await update.effective_message.reply_text(
        "📞 Send destination phone number.",
        reply_markup=back_button(),
    )


async def cancel_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data.clear()
    await update.effective_message.reply_text("Cancelled.", reply_markup=main_keyboard(update.effective_user.id))


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

    uid = int(call_data.get("user_id"))
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
