#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
TG Account Manager Bot — v3.0
aiogram 3.x + Telethon MTProto
"""

import asyncio
import logging
import os
import random
import re
import time
from datetime import datetime, timezone
from typing import Optional, Dict, List
from collections import defaultdict, deque
from pathlib import Path
from io import BytesIO

import aiosqlite
from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.types import (
    Message, CallbackQuery,
    InlineKeyboardMarkup, InlineKeyboardButton,
    BufferedInputFile
)
from aiogram.filters import CommandStart
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.exceptions import TelegramBadRequest
from aiogram.dispatcher.middlewares.base import BaseMiddleware

from telethon import TelegramClient, events
from telethon.sessions import StringSession
from telethon.errors import (
    SessionPasswordNeededError, PhoneCodeInvalidError,
    FloodWaitError, PhoneNumberInvalidError,
    UserPrivacyRestrictedError, PeerFloodError,
    UserIsBlockedError, InputUserDeactivatedError
)
from telethon.tl.functions.contacts import BlockRequest, UnblockRequest, GetBlockedRequest
from telethon.tl.functions.account import (
    UpdateStatusRequest, SetPrivacyRequest, UpdateProfileRequest,
)
from telethon.tl.functions.photos import GetUserPhotosRequest, DeletePhotosRequest
from telethon.tl.functions.messages import ExportChatInviteRequest
from telethon.tl.functions.channels import (
    GetLeftChannelsRequest, GetAdminedPublicChannelsRequest,
)
from telethon.tl.types import (
    MessageMediaPhoto,
    MessageMediaDocument,
    User, Chat, Channel,
    UserStatusOnline, UserStatusOffline,
    InputPrivacyValueDisallowAll,
    InputPrivacyValueAllowAll,
    InputPrivacyValueAllowContacts,
    InputPrivacyKeyPhoneNumber,
    InputPrivacyKeyStatusTimestamp,
    InputPrivacyKeyProfilePhoto,
    InputPrivacyKeyAbout,
    InputMessagesFilterVoice,
    InputMessagesFilterRoundVideo,
    InputMessagesFilterPhotoVideo,
)

# ══════════════════════════════════════
# КОНФИГ (из переменных окружения)
# ══════════════════════════════════════
BOT_TOKEN = os.environ["BOT_TOKEN"]
API_ID    = int(os.environ["API_ID"])
API_HASH  = os.environ["API_HASH"]
DB_PATH   = os.getenv("DB_PATH", "manager_bot.db")
MEDIA_DIR = os.getenv("MEDIA_DIR", "saved_media")

# ALLOWED_USERS — whitelist Telegram user IDs (через запятую). Если пусто — доступ для всех.
_allowed_raw = os.getenv("ALLOWED_USERS", "")
ALLOWED_USERS: set = {int(x.strip()) for x in _allowed_raw.split(",") if x.strip().isdigit()}

Path(MEDIA_DIR).mkdir(exist_ok=True)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s"
)
log = logging.getLogger("TGManager")

# ══════════════════════════════════════
# УТИЛИТЫ
# ══════════════════════════════════════
def _serialize_entities(msg) -> list:
    """Сериализует entities aiogram-сообщения в JSON-совместимый список (для хранения в БД)."""
    result = []
    ents = msg.entities or msg.caption_entities or []
    for e in ents:
        d = {'type': e.type, 'offset': e.offset, 'length': e.length}
        if e.type == 'custom_emoji' and e.custom_emoji_id:
            d['custom_emoji_id'] = e.custom_emoji_id
        elif e.type == 'text_link' and e.url:
            d['url'] = e.url
        elif e.type == 'pre' and getattr(e, 'language', None):
            d['language'] = e.language
        result.append(d)
    return result



def _entities_to_html(text: str, entities_json: list) -> str:
    """Конвертирует text + entities (из БД) в HTML с форматированием для Telegram."""
    import html as _html_mod
    if not entities_json or not text:
        return _html_mod.escape(text)
    # Собираем события (позиция, тип(0=открыть/1=закрыть), тег)
    events = []
    for e in entities_json:
        o = e.get('offset', 0)
        l = e.get('length', 0)
        t = e.get('type', '')
        if t == 'bold':
            events += [(o, 0, '<b>'), (o+l, 1, '</b>')]
        elif t == 'italic':
            events += [(o, 0, '<i>'), (o+l, 1, '</i>')]
        elif t == 'underline':
            events += [(o, 0, '<u>'), (o+l, 1, '</u>')]
        elif t == 'strikethrough':
            events += [(o, 0, '<s>'), (o+l, 1, '</s>')]
        elif t == 'code':
            events += [(o, 0, '<code>'), (o+l, 1, '</code>')]
        elif t == 'pre':
            lang = e.get('language', '')
            open_t = f'<pre><code class="language-{lang}">' if lang else '<pre>'
            close_t = '</code></pre>' if lang else '</pre>'
            events += [(o, 0, open_t), (o+l, 1, close_t)]
        elif t == 'spoiler':
            events += [(o, 0, '<tg-spoiler>'), (o+l, 1, '</tg-spoiler>')]
        elif t == 'text_link':
            url = _html_mod.escape(e.get('url', ''))
            events += [(o, 0, f'<a href="{url}">'), (o+l, 1, '</a>')]
        elif t == 'custom_emoji':
            eid = e.get('custom_emoji_id', '')
            inner = _html_mod.escape(text[o:o+l])
            events += [(o, 0, f'<tg-emoji emoji-id="{eid}">'), (o+l, 1, '</tg-emoji>')]
    # Сортируем: сначала по позиции, закрывающие раньше открывающих на той же позиции
    events.sort(key=lambda x: (x[0], x[1]))
    parts = []
    prev  = 0
    for pos, kind, tag in events:
        if pos > prev:
            parts.append(_html_mod.escape(text[prev:pos]))
        parts.append(tag)
        prev = pos
    if prev < len(text):
        parts.append(_html_mod.escape(text[prev:]))
    return ''.join(parts)


def _content_item_html(item: dict) -> str:
    """Возвращает HTML-превью одного элемента черновика/автоответа."""
    t = item.get('type', '?')
    if t == 'text':
        if item.get('html'):
            return item['html']
        raw  = item.get('text', '')
        ents = item.get('entities', [])
        return _entities_to_html(raw, ents)
    _MEDIA_LABELS = {
        'photo':      '🖼 [фото]',
        'video':      '📹 [видео]',
        'voice':      '🎙 [голосовое]',
        'video_note': '🎥 [кружок]',
        'sticker':    '😊 [стикер]',
        'audio':      '🎵 [аудио]',
        'document':   '📎 [файл]',
        'animation':  '🎞 [гиф]',
        'album':      '🗂 [альбом]',
    }
    if t == 'album':
        n   = len(item.get('items', []))
        cap = item.get('caption', '')
        ents= item.get('entities', [])
        cap_html = _entities_to_html(cap, ents) if cap else ''
        base = f"🗂 [альбом · {n}]"
        return base + (f" {cap_html}" if cap_html else '')
    label = _MEDIA_LABELS.get(t, f'[{t}]')
    cap   = item.get('caption', '')
    ents  = item.get('entities', [])
    cap_html = _entities_to_html(cap, ents) if cap else ''
    return label + (f" {cap_html}" if cap_html else '')

def _build_telethon_entities(entities_json: list):
    """Восстанавливает Telethon MessageEntity из сохранённого JSON."""
    from telethon.tl.types import (
        MessageEntityBold, MessageEntityItalic, MessageEntityCode,
        MessageEntityPre, MessageEntityTextUrl, MessageEntityCustomEmoji,
        MessageEntityUnderline, MessageEntityStrike, MessageEntitySpoiler,
    )
    _map = {
        'bold': MessageEntityBold,
        'italic': MessageEntityItalic,
        'code': MessageEntityCode,
        'underline': MessageEntityUnderline,
        'strikethrough': MessageEntityStrike,
        'spoiler': MessageEntitySpoiler,
    }
    result = []
    for e in (entities_json or []):
        t = e.get('type', '')
        o, l = e.get('offset', 0), e.get('length', 0)
        if t in _map:
            result.append(_map[t](offset=o, length=l))
        elif t == 'custom_emoji':
            eid = e.get('custom_emoji_id')
            if eid:
                result.append(MessageEntityCustomEmoji(offset=o, length=l, document_id=int(eid)))
        elif t == 'text_link':
            result.append(MessageEntityTextUrl(offset=o, length=l, url=e.get('url', '')))
        elif t == 'pre':
            result.append(MessageEntityPre(offset=o, length=l, language=e.get('language', '')))
    return result


def make_progress_bar(current: int, total: int, width: int = 12) -> str:
    if total <= 0:
        return f"[{'░' * width}]"
    pct    = min(current / total, 1.0)
    filled = round(width * pct)
    bar    = "█" * filled + "░" * (width - filled)
    return f"[{bar}] {round(pct * 100)}%"

def tog(val): return "вкл ✅" if val else "выкл ❌"

async def animate_loading(bot: "Bot", chat_id: int, msg_id: int,
                           title: str, stop_event: asyncio.Event,
                           extra: str = "") -> None:
    """Анимирует точки в сообщении: .  →  ..  →  ...  →  .  (цикл)"""
    dots_seq = [".", "..", "..."]
    i = 0
    while not stop_event.is_set():
        dots = dots_seq[i % 3]
        i   += 1
        try:
            await bot.edit_message_text(
                f"{title}{dots}{chr(10) + extra if extra else ''}",
                chat_id=chat_id, message_id=msg_id, parse_mode='HTML'
            )
        except Exception:
            pass
        try:
            await asyncio.wait_for(asyncio.shield(stop_event.wait()), timeout=0.7)
        except asyncio.TimeoutError:
            pass

# ══════════════════════════════════════
# FSM СОСТОЯНИЯ
# ══════════════════════════════════════
class Auth(StatesGroup):
    phone    = State()
    code     = State()
    password = State()

class ARState(StatesGroup):
    trigger = State()   # шаг 1: триггеры (по одному на строку)
    content = State()   # шаг 2: накапливаем сообщения (как черновик)
    match   = State()   # шаг 3: тип совпадения

class SpamCfg(StatesGroup):
    value = State()

class DndText(StatesGroup):
    text = State()

class KWAdd(StatesGroup):
    keyword = State()

class OTAdd(StatesGroup):
    username = State()

class BroadcastState(StatesGroup):
    content   = State()   # накапливаем сообщения (как черновик)
    usernames = State()

class ARSchedule(StatesGroup):
    value = State()

class DraftAdd(StatesGroup):
    trigger = State()
    content = State()   # накапливаем сообщения
    confirm = State()   # финальное подтверждение


# ══════════════════════════════════════
# БАЗА ДАННЫХ
# ══════════════════════════════════════
async def init_db():
    async with aiosqlite.connect(DB_PATH) as db:
        await db.executescript("""
        CREATE TABLE IF NOT EXISTS accounts(
            id             INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id        INTEGER NOT NULL,
            phone          TEXT NOT NULL,
            session_string TEXT NOT NULL DEFAULT '',
            name           TEXT DEFAULT '',
            username       TEXT DEFAULT '',
            active         INTEGER DEFAULT 1,
            always_online  INTEGER DEFAULT 0,
            ghost_mode     INTEGER DEFAULT 0,
            auto_read      INTEGER DEFAULT 0,
            auto_read_filter TEXT DEFAULT 'all',
            security_mode  INTEGER DEFAULT 0,
            autoreply_on   INTEGER DEFAULT 0,
            spam_threshold INTEGER DEFAULT 5,
            spam_window    INTEGER DEFAULT 60,
            notify_deleted INTEGER DEFAULT 1,
            notify_media   INTEGER DEFAULT 1,
            dnd_mode       INTEGER DEFAULT 0,
            dnd_text       TEXT    DEFAULT 'сейчас недоступен, напишу позже'
        );
        CREATE TABLE IF NOT EXISTS blacklist_cache(
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id  INTEGER NOT NULL,
            peer_id     INTEGER,
            peer_name   TEXT DEFAULT '',
            peer_user   TEXT DEFAULT '',
            FOREIGN KEY(account_id) REFERENCES accounts(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS deleted_msgs(
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id  INTEGER NOT NULL,
            chat_id     INTEGER,
            chat_name   TEXT DEFAULT '',
            sender_name TEXT DEFAULT '',
            text        TEXT DEFAULT '',
            deleted_at  TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY(account_id) REFERENCES accounts(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS msg_cache(
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id   INTEGER NOT NULL,
            msg_id       INTEGER NOT NULL,
            chat_id      INTEGER,
            chat_name    TEXT DEFAULT '',
            sender_name  TEXT DEFAULT '',
            sender_id    INTEGER DEFAULT 0,
            sender_user  TEXT DEFAULT '',
            text         TEXT DEFAULT '',
            has_media    INTEGER DEFAULT 0,
            media_type   TEXT DEFAULT '',
            is_voice     INTEGER DEFAULT 0,
            is_videonote INTEGER DEFAULT 0,
            is_outgoing  INTEGER DEFAULT 0,
            UNIQUE(account_id, msg_id, chat_id)
        );
        CREATE TABLE IF NOT EXISTS autoreply_rules(
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id    INTEGER NOT NULL,
            trig          TEXT NOT NULL DEFAULT '',
            trigger_text  TEXT NOT NULL DEFAULT '',
            response      TEXT NOT NULL DEFAULT '',
            response_text TEXT NOT NULL DEFAULT '',
            match_type    TEXT DEFAULT 'contains',
            active        INTEGER DEFAULT 1,
            format_mode   TEXT DEFAULT 'html',
            FOREIGN KEY(account_id) REFERENCES accounts(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS autodel_rules(
            id              INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id      INTEGER NOT NULL,
            label           TEXT DEFAULT '',
            inactive_days   INTEGER DEFAULT 0,
            chat_type       TEXT DEFAULT 'all',
            skip_pinned     INTEGER DEFAULT 1,
            FOREIGN KEY(account_id) REFERENCES accounts(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS drafts(
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id   INTEGER NOT NULL,
            trigger_text TEXT NOT NULL DEFAULT '',
            content      TEXT NOT NULL DEFAULT '',
            active       INTEGER DEFAULT 1,
            created_at   TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY(account_id) REFERENCES accounts(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS shadow_whitelist(
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id   INTEGER NOT NULL,
            peer_id      INTEGER DEFAULT 0,
            peer_user    TEXT DEFAULT '',
            peer_name    TEXT DEFAULT '',
            FOREIGN KEY(account_id) REFERENCES accounts(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS onetime_media(
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id  INTEGER NOT NULL,
            from_name   TEXT DEFAULT '',
            media_type  TEXT DEFAULT '',
            file_path   TEXT DEFAULT '',
            saved_at    TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY(account_id) REFERENCES accounts(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS keyword_alerts(
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id  INTEGER NOT NULL,
            keyword     TEXT NOT NULL,
            active      INTEGER DEFAULT 1,
            FOREIGN KEY(account_id) REFERENCES accounts(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS online_tracker(
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id  INTEGER NOT NULL,
            peer_id     INTEGER NOT NULL,
            peer_name   TEXT DEFAULT '',
            peer_user   TEXT DEFAULT '',
            last_seen   TEXT DEFAULT '',
            UNIQUE(account_id, peer_id)
        );
        CREATE TABLE IF NOT EXISTS broadcast_log(
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id  INTEGER NOT NULL,
            message     TEXT NOT NULL,
            total       INTEGER DEFAULT 0,
            sent        INTEGER DEFAULT 0,
            failed      INTEGER DEFAULT 0,
            created_at  TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY(account_id) REFERENCES accounts(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS autoreactions(
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id    INTEGER NOT NULL,
            active        INTEGER DEFAULT 1,
            scope         TEXT DEFAULT 'private',
            reactions_json TEXT DEFAULT '[]',
            delay_sec     INTEGER DEFAULT 0,
            premium       INTEGER DEFAULT 0,
            FOREIGN KEY(account_id) REFERENCES accounts(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS stats_cache(
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id  INTEGER NOT NULL,
            chat_id     INTEGER NOT NULL,
            chat_name   TEXT DEFAULT '',
            username    TEXT DEFAULT '',
            total_msgs  INTEGER DEFAULT 0,
            out_msgs    INTEGER DEFAULT 0,
            voices      INTEGER DEFAULT 0,
            videonotes  INTEGER DEFAULT 0,
            media_count INTEGER DEFAULT 0,
            unread      INTEGER DEFAULT 0,
            last_date   TEXT DEFAULT '',
            updated_at  TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            UNIQUE(account_id, chat_id)
        );
        CREATE INDEX IF NOT EXISTS idx_stats_cache ON stats_cache(account_id, total_msgs DESC);
        CREATE TABLE IF NOT EXISTS tg_codes(
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            account_id  INTEGER NOT NULL,
            code        TEXT NOT NULL,
            full_text   TEXT DEFAULT '',
            received_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            FOREIGN KEY(account_id) REFERENCES accounts(id) ON DELETE CASCADE
        );
        CREATE INDEX IF NOT EXISTS idx_acc_user   ON accounts(user_id);
        CREATE INDEX IF NOT EXISTS idx_cache       ON msg_cache(account_id, msg_id);
        CREATE INDEX IF NOT EXISTS idx_cache_chat  ON msg_cache(account_id, chat_id);
        """)
        migrations = [
            "ALTER TABLE accounts ADD COLUMN security_mode    INTEGER DEFAULT 0",
            "ALTER TABLE accounts ADD COLUMN autoreply_on     INTEGER DEFAULT 0",
            "ALTER TABLE accounts ADD COLUMN spam_threshold   INTEGER DEFAULT 5",
            "ALTER TABLE accounts ADD COLUMN spam_window      INTEGER DEFAULT 60",
            "ALTER TABLE accounts ADD COLUMN always_online    INTEGER DEFAULT 0",
            "ALTER TABLE accounts ADD COLUMN ghost_mode       INTEGER DEFAULT 0",
            "ALTER TABLE accounts ADD COLUMN auto_read        INTEGER DEFAULT 0",
            "ALTER TABLE accounts ADD COLUMN auto_read_filter TEXT DEFAULT 'all'",
            "ALTER TABLE accounts ADD COLUMN notify_deleted   INTEGER DEFAULT 1",
            "ALTER TABLE accounts ADD COLUMN notify_media     INTEGER DEFAULT 1",
            "ALTER TABLE accounts ADD COLUMN dnd_mode         INTEGER DEFAULT 0",
            "ALTER TABLE accounts ADD COLUMN dnd_text         TEXT DEFAULT 'сейчас недоступен, напишу позже'",
            "ALTER TABLE msg_cache ADD COLUMN media_type      TEXT DEFAULT ''",
            "ALTER TABLE msg_cache ADD COLUMN is_voice        INTEGER DEFAULT 0",
            "ALTER TABLE msg_cache ADD COLUMN is_videonote    INTEGER DEFAULT 0",
            "ALTER TABLE msg_cache ADD COLUMN is_outgoing     INTEGER DEFAULT 0",
            "ALTER TABLE msg_cache ADD COLUMN sender_id       INTEGER DEFAULT 0",
            "ALTER TABLE msg_cache ADD COLUMN sender_user     TEXT DEFAULT ''",
            "ALTER TABLE accounts ADD COLUMN shadow_mode      INTEGER DEFAULT 0",
            "ALTER TABLE accounts ADD COLUMN shadow_stars     INTEGER DEFAULT 0",
            "ALTER TABLE accounts ADD COLUMN shadow_backup    TEXT    DEFAULT ''",
            "ALTER TABLE autoreply_rules ADD COLUMN content_json   TEXT    DEFAULT ''",
            "ALTER TABLE autoreply_rules ADD COLUMN buttons_json   TEXT    DEFAULT ''",
            "ALTER TABLE autoreply_rules ADD COLUMN schedule_start TEXT    DEFAULT ''",
            "ALTER TABLE autoreply_rules ADD COLUMN schedule_end   TEXT    DEFAULT ''",
            # Расширенный антиспам
            "ALTER TABLE accounts ADD COLUMN antispam_filter_links     INTEGER DEFAULT 0",
            "ALTER TABLE accounts ADD COLUMN antispam_filter_forwards  INTEGER DEFAULT 0",
            "ALTER TABLE accounts ADD COLUMN antispam_filter_stickers  INTEGER DEFAULT 0",
            "ALTER TABLE accounts ADD COLUMN antispam_action           TEXT    DEFAULT 'block'",
            "ALTER TABLE accounts ADD COLUMN antispam_warn_max         INTEGER DEFAULT 3",
        ]
        for sql in migrations:
            try: await db.execute(sql)
            except: pass

        # Таблица белого списка антиспама
        try:
            await db.execute("""
            CREATE TABLE IF NOT EXISTS antispam_whitelist(
                id         INTEGER PRIMARY KEY AUTOINCREMENT,
                account_id INTEGER NOT NULL,
                peer_id    INTEGER NOT NULL,
                peer_name  TEXT DEFAULT '',
                peer_user  TEXT DEFAULT '',
                UNIQUE(account_id, peer_id)
            )
            """)
        except: pass

        # Миграция: пересоздаём msg_cache с UNIQUE constraint чтобы убрать дубли
        # Проверяем — если UNIQUE уже есть, пропускаем
        try:
            idx = await db.execute(
                "SELECT name FROM sqlite_master WHERE type='index' AND name='idx_msg_cache_unique'"
            )
            row = await idx.fetchone()
            if not row:
                # Создаём новую таблицу с UNIQUE, переливаем уникальные строки, заменяем
                await db.executescript("""
                    CREATE TABLE IF NOT EXISTS msg_cache_new(
                        id           INTEGER PRIMARY KEY AUTOINCREMENT,
                        account_id   INTEGER NOT NULL,
                        msg_id       INTEGER NOT NULL,
                        chat_id      INTEGER,
                        chat_name    TEXT DEFAULT '',
                        sender_name  TEXT DEFAULT '',
                        sender_id    INTEGER DEFAULT 0,
                        sender_user  TEXT DEFAULT '',
                        text         TEXT DEFAULT '',
                        has_media    INTEGER DEFAULT 0,
                        media_type   TEXT DEFAULT '',
                        is_voice     INTEGER DEFAULT 0,
                        is_videonote INTEGER DEFAULT 0,
                        is_outgoing  INTEGER DEFAULT 0,
                        UNIQUE(account_id, msg_id, chat_id)
                    );
                    INSERT OR IGNORE INTO msg_cache_new
                        SELECT id,account_id,msg_id,chat_id,chat_name,sender_name,
                               sender_id,sender_user,text,has_media,media_type,
                               is_voice,is_videonote,is_outgoing
                        FROM msg_cache;
                    DROP TABLE msg_cache;
                    ALTER TABLE msg_cache_new RENAME TO msg_cache;
                    CREATE INDEX IF NOT EXISTS idx_cache       ON msg_cache(account_id, msg_id);
                    CREATE INDEX IF NOT EXISTS idx_cache_chat  ON msg_cache(account_id, chat_id);
                    CREATE UNIQUE INDEX idx_msg_cache_unique ON msg_cache(account_id, msg_id, chat_id);
                """)
                log.info("msg_cache migrated: UNIQUE constraint added, duplicates removed")
        except Exception as e:
            log.warning(f"msg_cache migration skipped: {e}")

        await db.commit()

async def db_get(q, p=()):
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        async with db.execute(q, p) as c:
            r = await c.fetchone()
            return dict(r) if r else None

async def db_all(q, p=()):
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        async with db.execute(q, p) as c:
            return [dict(r) for r in await c.fetchall()]

async def db_run(q, p=()):
    async with aiosqlite.connect(DB_PATH) as db:
        c = await db.execute(q, p)
        await db.commit()
        return c.lastrowid

# ══════════════════════════════════════
# КЛИЕНТ-МЕНЕДЖЕР
# ══════════════════════════════════════
class CM:
    def __init__(self):
        self.clients        : Dict[int, TelegramClient] = {}
        self.counters       : Dict[int, Dict[int, deque]] = defaultdict(lambda: defaultdict(deque))
        self.bot            : Optional[Bot] = None
        self._online_tasks  : Dict[int, asyncio.Task] = {}
        self._del_buf       : dict = {}
        self._online_status : dict = {}
        # активные рассылки {aid: {'running': bool, 'task': Task}}
        self._broadcasts    : dict = {}
        # буферы альбомов для черновиков {(aid, chat_id, group_id): {'items': [], 'task': Task}}
        self._album_buf     : dict = {}
        # счётчики предупреждений антиспама {(aid, sender_id): warn_count}
        self._warn_counts   : dict = defaultdict(int)
        # счётчики удалённых сообщений за нарушения (для отчётов) {(aid, sender_id): count}
        self._deleted_spam  : dict = defaultdict(int)

    def set_bot(self, b): self.bot = b

    async def load_all(self):
        for acc in await db_all("SELECT * FROM accounts WHERE active=1"):
            try: await self.start(acc)
            except Exception as e: log.error(f"load {acc['id']}: {e}")

    async def start(self, acc) -> Optional[TelegramClient]:
        aid = acc['id']
        if aid in self.clients:
            c = self.clients[aid]
            if c.is_connected(): return c
            try: await c.disconnect()
            except: pass
        c = TelegramClient(StringSession(acc['session_string']), API_ID, API_HASH,
            device_model="Galaxy S25 Ultra",
            system_version="Android 15",
            app_version="12.4.3",
            connection_retries=5,
            retry_delay=3,
            auto_reconnect=True,
            flood_sleep_threshold=60,
        )
        await c.connect()
        if not await c.is_user_authorized():
            await db_run("UPDATE accounts SET active=0 WHERE id=?", (aid,))
            log.warning(f"Account {aid} is no longer authorized — deactivated")
            return None
        # Проверяем, не заблокирован ли аккаунт
        try:
                if me is None:
                    await db_run("UPDATE accounts SET active=0 WHERE id=?", (aid,))
                log.warning(f"Account {aid} — get_me() returned None, deactivated")
                return None
        except Exception as e:
            log.warning(f"Account {aid} get_me() failed: {e}")
        self.clients[aid] = c
        self._attach(c, acc)
        if acc.get('always_online', 0):
            self._start_online_task(c, aid)
        log.info(f"Client started for account {aid} ({acc['phone']})")
        return c

    def get(self, aid) -> Optional[TelegramClient]:
        c = self.clients.get(aid)
        return c if c and c.is_connected() else None

    async def stop(self, aid):
        if aid in self._online_tasks:
            self._online_tasks.pop(aid).cancel()
        if aid in self.clients:
            try: await self.clients.pop(aid).disconnect()
            except: pass

    # ── Вечный онлайн ──
    def _start_online_task(self, c: TelegramClient, aid: int):
        if aid in self._online_tasks:
            self._online_tasks[aid].cancel()

        async def _loop():
            while True:
                try:
                    acc = await db_get("SELECT always_online FROM accounts WHERE id=?", (aid,))
                    if not acc or not acc.get('always_online'): break
                    if not c.is_connected():
                        try: await c.connect()
                        except: await asyncio.sleep(30); continue
                    await c(UpdateStatusRequest(offline=False))
                except asyncio.CancelledError: break
                except Exception as e: log.warning(f"always_online acc {aid}: {e}")
                await asyncio.sleep(55)

        self._online_tasks[aid] = asyncio.create_task(_loop())

    async def set_always_online(self, aid: int, enable: bool):
        await db_run("UPDATE accounts SET always_online=? WHERE id=?", (1 if enable else 0, aid))
        c = self.get(aid)
        if enable:
            if c: self._start_online_task(c, aid)
        else:
            if aid in self._online_tasks: self._online_tasks.pop(aid).cancel()
            if c:
                try: await c(UpdateStatusRequest(offline=True))
                except: pass

    def _attach(self, c: TelegramClient, acc: dict):
        aid = acc['id']

        @c.on(events.NewMessage(incoming=True))
        async def _new(ev):
            try: await self._on_new(c, ev, acc)
            except Exception as e: log.debug(f"on_new {e}")

        @c.on(events.NewMessage(outgoing=True))
        async def _outgoing(ev):
            try: await self._on_outgoing(c, ev)
            except Exception as e: log.debug(f"on_outgoing {e}")

        @c.on(events.MessageDeleted())
        async def _del(ev):
            try: await self._on_del(ev, acc)
            except Exception as e: log.debug(f"on_del {e}")

        @c.on(events.MessageEdited(incoming=True))
        async def _edit(ev):
            try: await self._on_edit(c, ev, acc)
            except Exception as e: log.debug(f"on_edit {e}")

    def _detect_media(self, msg):
        if not msg.media: return 0, '', 0, 0
        if msg.voice:       return 1, 'voice', 1, 0
        if msg.video_note:  return 1, 'video_note', 0, 1
        if isinstance(msg.media, MessageMediaPhoto): return 1, 'photo', 0, 0
        if msg.video:       return 1, 'video', 0, 0
        if msg.sticker:     return 1, 'sticker', 0, 0
        if msg.gif:         return 1, 'gif', 0, 0
        if msg.document:    return 1, 'document', 0, 0
        return 1, 'other', 0, 0

    async def _cache_message(self, aid, msg, chat_id, chat_name, sender_name,
                              sender_id=0, sender_user='', is_outgoing=0):
        has_med, mtype, is_voice, is_videonote = self._detect_media(msg)
        await db_run(
            "INSERT OR IGNORE INTO msg_cache"
            "(account_id,msg_id,chat_id,chat_name,sender_name,sender_id,sender_user,"
            "text,has_media,media_type,is_voice,is_videonote,is_outgoing) "
            "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (aid, msg.id, chat_id, chat_name, sender_name, sender_id, sender_user,
             msg.message or '', has_med, mtype, is_voice, is_videonote, is_outgoing)
        )

    async def _on_new(self, c, ev, acc):
        aid = acc['id']
        msg = ev.message
        try:
            sender  = await ev.get_sender()
            chat    = await ev.get_chat()
            chat_id = ev.chat_id or 0
            cname   = getattr(chat, 'title', None) or getattr(chat, 'first_name', '') or ''
            sname   = getattr(sender, 'first_name', '') if sender else ''
            sid     = getattr(sender, 'id', 0) if sender else 0
            susr    = getattr(sender, 'username', '') or '' if sender else ''
            await self._cache_message(aid, msg, chat_id, cname, sname, sid, susr, 0)
        except: pass

        # ── перехват кодов от telegram (777000) ──
        try:
            import re as _re
            sender_id_raw = getattr(ev.message.peer_id, 'user_id', None) or getattr(ev.message, 'from_id', None)
            # 777000 — официальный сервисный аккаунт Telegram
            if ev.is_private and getattr(sender, 'id', 0) == 777000:
                text_raw = msg.message or ''
                m = _re.search(r'\b(\d{5,6})\b', text_raw)
                if m:
                    code = m.group(1)
                    await db_run(
                        "INSERT INTO tg_codes(account_id, code, full_text) VALUES(?,?,?)",
                        (aid, code, text_raw[:500])
                    )
        except: pass

        # одноразовые медиа
        try:
            if msg.media and hasattr(msg.media, 'ttl_seconds') and msg.media.ttl_seconds:
                await self._grab_onetime(c, ev, acc)
        except: pass

        acc_row = await db_get("SELECT * FROM accounts WHERE id=?", (aid,))
        if not acc_row: return

        if acc_row.get('auto_read', 0):
            await self._do_autoread(c, ev, acc_row)
        if acc_row.get('security_mode', 0) and ev.is_private:
            await self._antispam(c, ev, acc_row)
        asyncio.create_task(self._check_keywords(ev, acc_row))
        if acc_row.get('dnd_mode', 0) and ev.is_private:
            await self._dnd_reply(c, ev, acc_row)
        if acc_row.get('autoreply_on', 0) and ev.is_private:
            await self._autoreply(c, ev, aid)

    async def _on_outgoing(self, c, ev):
        # ── Черновики: заменяем триггер на сохранённый контент ──
        try:
            aid = next((k for k, v in self.clients.items() if v is c), None)
            if aid is not None:
                raw = (ev.message.message or '').strip()
                if raw:
                    draft = await db_get(
                        "SELECT * FROM drafts WHERE account_id=? AND active=1 "
                        "AND LOWER(trigger_text)=LOWER(?)",
                        (aid, raw)
                    )
                    if draft:
                        import json as _json
                        try:
                            raw_content = _json.loads(draft['content'])
                            items = raw_content if isinstance(raw_content, list) else [raw_content]
                            reply_to_id = ev.message.reply_to_msg_id  # None если не реплай

                            async def _send_item(item, reply_to=None):
                                if item.get('type') == 'text':
                                    raw_text  = item.get('text', '')
                                    ents_json = item.get('entities', [])
                                    kw = {'link_preview': False}
                                    if reply_to: kw['reply_to'] = reply_to
                                    if ents_json:
                                        tl_ents = _build_telethon_entities(ents_json)
                                        await c.send_message(ev.chat_id, raw_text,
                                            formatting_entities=tl_ents, **kw)
                                    else:
                                        await c.send_message(ev.chat_id, raw_text,
                                            parse_mode='html', **kw)
                                else:
                                    await self._send_content(c, ev.chat_id, item,
                                                              reply_to=reply_to)

                            # ── во всех режимах: сначала удаляем триггер ──
                            try:
                                await ev.message.delete()
                            except Exception:
                                pass
                            await asyncio.sleep(0.05)

                            if reply_to_id:
                                # ── режим реплая: все элементы отправляем как реплай ──
                                for i, item in enumerate(items):
                                    await _send_item(item, reply_to=reply_to_id)
                                    if i < len(items) - 1:
                                        await asyncio.sleep(0.3)
                            else:
                                # ── обычный режим: шлём все элементы подряд ──
                                for i, item in enumerate(items):
                                    await _send_item(item)
                                    if i < len(items) - 1:
                                        await asyncio.sleep(0.3)
                        except Exception as de:
                            log.debug(f"draft send: {de}")
                        return
        except: pass

        # ── "закреп" — закрепить цитируемое сообщение ──
        try:
            text = (ev.message.message or '').strip().lower()
            if text == 'закреп' and ev.message.reply_to_msg_id:
                try:
                    await c.pin_message(ev.chat_id, ev.message.reply_to_msg_id, notify=False)
                    await ev.message.delete()
                except: pass
                return
        except: pass

        # ── "..." — редактировать своё сообщение через реплай ──
        # отвечаешь на своё сообщение текстом начинающимся с "..."
        # то сообщение на которое ответил изменится на новый текст
        try:
            raw_text = (ev.message.message or '')
            reply_id = ev.message.reply_to_msg_id
            if reply_id and raw_text.startswith('...'):
                new_text = raw_text[3:].lstrip('\n')  # убираем "..." и необязательный перенос
                try:
                    # Проверяем что цитируемое — наше сообщение
                    orig = await c.get_messages(ev.chat_id, ids=reply_id)
                    if orig and orig.out:
                        # Переносим entities с корректировкой смещения
                        shift = len(raw_text) - len(new_text)
                        raw_ents = ev.message.entities or []
                        adjusted_ents = []
                        for e in raw_ents:
                            no = e.offset - shift
                            if no >= 0 and no + e.length <= len(new_text):
                                try:
                                    import copy as _copy
                                    ne = _copy.copy(e)
                                    ne.offset = no
                                    adjusted_ents.append(ne)
                                except: pass
                        kw = {'link_preview': False}
                        if adjusted_ents:
                            kw['formatting_entities'] = adjusted_ents
                        await c.edit_message(ev.chat_id, reply_id, new_text, **kw)
                        await ev.message.delete()
                        return
                except Exception as e:
                    log.debug(f"... edit failed: {e}")
        except: pass

        # Кэшируем исходящие — ищем aid по клиенту
        try:
            aid = next((k for k, v in self.clients.items() if v is c), None)
            if aid is not None:
                msg     = ev.message
                chat_id = ev.chat_id or 0
                await self._cache_message(aid, msg, chat_id, '', 'me', 0, '', 1)
        except: pass

    async def _on_del(self, ev, acc):
        aid = acc['id']
        uid = acc['user_id']
        acc_row = await db_get("SELECT * FROM accounts WHERE id=?", (aid,))
        notify  = acc_row.get('notify_deleted', 1) if acc_row else 1
        c = self.get(aid)

        for mid in (ev.deleted_ids or []):
            row = await db_get("SELECT * FROM msg_cache WHERE account_id=? AND msg_id=?", (aid, mid))
            if not row: continue
            if row.get('is_outgoing', 0): continue
            if not (row['text'] or row['has_media']): continue
            # Только личные чаты: chat_id > 0 означает User-peer
            chat_id = row.get('chat_id', 0) or 0
            is_private = chat_id > 0
            # Пропускаем сообщения от ботов
            sid = row.get('sender_id', 0) or 0
            if sid and c:
                try:
                    sender_entity = await c.get_entity(sid)
                    if getattr(sender_entity, 'bot', False):
                        continue
                except Exception:
                    pass
            await db_run(
                "INSERT INTO deleted_msgs(account_id,chat_id,chat_name,sender_name,text) VALUES(?,?,?,?,?)",
                (aid, chat_id, row['chat_name'], row['sender_name'], row['text'])
            )
            # Уведомляем только если это личный чат (не группа/канал)
            if self.bot and notify and is_private:
                sname = row['sender_name'] or 'неизвестно'
                key   = (aid, uid, sid, sname)
                if key not in self._del_buf:
                    self._del_buf[key] = {'rows': []}
                self._del_buf[key]['rows'].append(row)
                if 'task' in self._del_buf[key] and not self._del_buf[key]['task'].done():
                    self._del_buf[key]['task'].cancel()
                self._del_buf[key]['task'] = asyncio.create_task(self._flush_del_buf(key))

    @staticmethod
    def _make_who(sname: str, sid: int, susr: str = '') -> str:
        name = sname or '?'
        if susr: return f'<a href="https://t.me/{susr}">{name}</a>'
        if sid:  return f'<a href="tg://user?id={sid}">{name}</a>'
        return f'<b>{name}</b>'

    async def _flush_del_buf(self, key):
        await asyncio.sleep(10)
        buf = self._del_buf.pop(key, None)
        if not buf: return
        aid, uid, sid, sname = key
        rows = buf['rows']
        if not rows: return
        susr = rows[0].get('sender_user', '') or ''
        who  = self._make_who(sname, sid, susr)
        if len(rows) == 1:
            content  = rows[0]['text'] or f"({rows[0].get('media_type','медиа')})"
            text_out = f"{who} удалил сообщение:\n<blockquote expandable>{content[:800]}</blockquote>"
        else:
            parts = []
            for i, r in enumerate(rows, 1):
                content = r['text'] or f"({r.get('media_type','медиа')})"
                parts.append(f"<b>{i}.</b> {content[:300]}")
            text_out = (
                f"{who} удалил <b>{len(rows)}</b> сообщений:\n\n"
                "<blockquote expandable>" + "\n\n".join(parts) + "</blockquote>"
            )
        try: await self.bot.send_message(uid, text_out, parse_mode='HTML', disable_web_page_preview=True)
        except: pass

    async def _on_edit(self, c, ev, acc):
        if not ev.is_private: return
        aid = acc['id']
        uid = acc['user_id']
        acc_row = await db_get("SELECT * FROM accounts WHERE id=?", (aid,))
        if not (acc_row and acc_row.get('notify_deleted', 1)): return
        try:
            chat   = await ev.get_chat()
            sender = await ev.get_sender()
            if not isinstance(chat, User): return
            if getattr(sender, 'bot', False): return
        except: return
        msg      = ev.message
        mid      = msg.id
        row      = await db_get("SELECT * FROM msg_cache WHERE account_id=? AND msg_id=?", (aid, mid))
        old_text = row['text'] if row else ''
        new_text = msg.message or ''
        if old_text == new_text: return
        sname = getattr(sender, 'first_name', '') if sender else ''
        sid   = getattr(sender, 'id', 0) if sender else 0
        susr  = getattr(sender, 'username', '') or '' if sender else ''
        who   = self._make_who(sname, sid, susr)
        text_out = (
            f"{who} изменил сообщение\n"
            f"было: <blockquote expandable>{old_text[:600] or '(пусто)'}</blockquote>"
            f"стало: <blockquote expandable>{new_text[:600]}</blockquote>"
        )
        if self.bot:
            try: await self.bot.send_message(uid, text_out, parse_mode='HTML', disable_web_page_preview=True)
            except: pass
        await db_run("UPDATE msg_cache SET text=? WHERE account_id=? AND msg_id=?", (new_text, aid, mid))

    async def _grab_onetime(self, c, ev, acc):
        aid = acc['id']; uid = acc['user_id']
        acc_row = await db_get("SELECT * FROM accounts WHERE id=?", (aid,))
        notify  = acc_row.get('notify_media', 1) if acc_row else 1
        try:
            sender = await ev.get_sender()
            sname  = getattr(sender, 'first_name', '?') if sender else '?'
            sid    = getattr(sender, 'id', 0) if sender else 0
            susr   = getattr(sender, 'username', '') or '' if sender else ''
            msg    = ev.message
            who    = self._make_who(sname, sid, susr)
            cap    = f"от {who}"
            is_voice     = bool(msg.voice)
            is_videonote = bool(msg.video_note)
            is_photo     = isinstance(msg.media, MessageMediaPhoto)
            mtype  = 'voice' if is_voice else ('video_note' if is_videonote else ('photo' if is_photo else 'video'))
            path   = os.path.join(MEDIA_DIR, f"acc{aid}_{msg.id}")
            dl     = await c.download_media(msg.media, file=path)
            if dl:
                await db_run(
                    "INSERT INTO onetime_media(account_id,from_name,media_type,file_path) VALUES(?,?,?,?)",
                    (aid, sname, mtype, str(dl))
                )
                if self.bot and notify:
                    with open(dl, 'rb') as f: data = f.read()
                    try:
                        if is_voice:
                            await self.bot.send_voice(uid, BufferedInputFile(data, 'voice.ogg'), caption=cap, parse_mode='HTML')
                        elif is_videonote:
                            await self.bot.send_video_note(uid, BufferedInputFile(data, 'vnote.mp4'))
                            await self.bot.send_message(uid, cap, parse_mode='HTML')
                        elif is_photo:
                            await self.bot.send_photo(uid, BufferedInputFile(data, 'm.jpg'), caption=cap, has_spoiler=True, parse_mode='HTML')
                        else:
                            await self.bot.send_video(uid, BufferedInputFile(data, 'm.mp4'), caption=cap, has_spoiler=True, parse_mode='HTML')
                    except: pass
        except Exception as e: log.debug(f"grab_onetime {e}")

    async def _check_keywords(self, ev, acc):
        try:
            aid  = acc['id']; uid = acc['user_id']
            text = (ev.message.message or '').lower()
            if not text: return
            kws = await db_all("SELECT keyword FROM keyword_alerts WHERE account_id=? AND active=1", (aid,))
            for kw_row in kws:
                kw = (kw_row['keyword'] or '').lower()
                if kw and kw in text:
                    sender = await ev.get_sender()
                    chat   = await ev.get_chat()
                    sname  = getattr(sender, 'first_name', '?') if sender else '?'
                    sid    = getattr(sender, 'id', 0) if sender else 0
                    susr   = getattr(sender, 'username', '') or '' if sender else ''
                    cname  = getattr(chat, 'title', None) or getattr(chat, 'first_name', '') or '?'
                    who    = self._make_who(sname, sid, susr)
                    snippet = ev.message.message[:400]
                    await self.bot.send_message(
                        uid,
                        f"🔔 ключевое слово: <b>{kw_row['keyword']}</b>\n"
                        f"{who} в <b>{cname}</b>:\n"
                        f"<blockquote>{snippet}</blockquote>",
                        parse_mode='HTML'
                    )
                    break
        except: pass

    async def _dnd_reply(self, c, ev, acc):
        try:
            sender = await ev.get_sender()
            if not sender or getattr(sender, 'bot', False): return
            txt = acc.get('dnd_text') or 'сейчас недоступен, напишу позже'
            if not hasattr(self, '_dnd_sent'): self._dnd_sent = {}
            key  = f"dnd_{acc['id']}_{ev.chat_id}"
            last = self._dnd_sent.get(key, 0)
            if time.time() - last < 1800: return
            self._dnd_sent[key] = time.time()
            await c.send_message(ev.chat_id, txt)
        except: pass

    async def _do_autoread(self, c, ev, acc):
        flt = acc.get('auto_read_filter', 'all')
        if flt == 'all':
            try: await c.send_read_acknowledge(ev.chat_id)
            except: pass
            return
        try:
            types = set(flt.split(','))
            chat  = await ev.get_chat()
            if isinstance(chat, User):    ctype = 'bot' if chat.bot else 'private'
            elif isinstance(chat, Channel): ctype = 'channel' if chat.broadcast else 'group'
            elif isinstance(chat, Chat):  ctype = 'group'
            else:                         ctype = 'private'
            if getattr(chat, 'forum', False): ctype = 'forum'
            if ctype in types:
                try: await c.send_read_acknowledge(ev.chat_id)
                except: pass
        except: pass

    async def _antispam(self, c, ev, acc):
        """
        Расширенный антиспам:
        - счётчик сообщений за окно времени
        - фильтр ссылок
        - фильтр форвардов
        - фильтр стикер-спама
        - режим действия: block / delete / warn+block
        - белый список
        """
        aid = acc['id']
        sid = ev.sender_id
        if not sid: return

        # ── Проверка белого списка ──
        wl = await db_get(
            "SELECT id FROM antispam_whitelist WHERE account_id=? AND peer_id=?", (aid, sid)
        )
        if wl: return

        msg     = ev.message
        text    = (msg.message or '').lower()
        thr     = acc.get('spam_threshold', 5)
        win     = acc.get('spam_window', 60)
        action  = acc.get('antispam_action', 'block') or 'block'
        warn_max= int(acc.get('antispam_warn_max', 3) or 3)

        f_links    = bool(acc.get('antispam_filter_links', 0))
        f_forwards = bool(acc.get('antispam_filter_forwards', 0))
        f_stickers = bool(acc.get('antispam_filter_stickers', 0))

        sender = ev.sender

        # ── Обнаружение нарушений (помимо частоты) ──
        violation = None

        if f_forwards and msg.fwd_from:
            violation = 'форвард'

        if f_links and not violation:
            import re as _re
            if _re.search(r'(https?://|t\.me/|@\w{4,}|www\.)', text):
                violation = 'ссылка'

        if f_stickers and not violation:
            if getattr(msg, 'sticker', None):
                violation = 'стикер-спам'

        # ── Счётчик частоты ──
        q   = self.counters[aid][sid]
        now = time.time()
        q.append(now)
        while q and now - q[0] > win: q.popleft()
        if len(q) >= thr and not violation:
            violation = f'{thr} сообщ за {win}с'

        if not violation:
            return

        # ── Применяем действие ──
        acc_row = await db_get("SELECT user_id FROM accounts WHERE id=?", (aid,))
        name    = getattr(sender, 'first_name', '') if sender else str(sid)
        uname   = getattr(sender, 'username', '') or '' if sender else ''

        if action == 'delete':
            # Просто удаляем сообщение, не блокируем
            try:
                await msg.delete()
                self._deleted_spam[(aid, sid)] += 1
                deleted_count = self._deleted_spam[(aid, sid)]
                if self.bot and acc_row and deleted_count % 5 == 1:
                    who = f'@{uname}' if uname else f'<a href="tg://user?id={sid}">{name}</a>'
                    await self.bot.send_message(
                        acc_row['user_id'],
                        f"🗑 <b>антиспам · удалено</b>\n\n{who}\n"
                        f"причина: {violation}\n"
                        f"всего удалено у этого пользователя: {deleted_count}",
                        parse_mode='HTML'
                    )
            except: pass
            return

        elif action == 'warn+block':
            # Предупреждаем N раз, затем блокируем
            key = (aid, sid)
            self._warn_counts[key] += 1
            warns = self._warn_counts[key]
            if warns < warn_max:
                try:
                    await msg.delete()
                    await c.send_message(ev.chat_id,
                        f"⚠️ предупреждение {warns}/{warn_max}: {violation}\n"
                        f"при следующих нарушениях вы будете заблокированы"
                    )
                    if self.bot and acc_row:
                        who = f'@{uname}' if uname else f'<a href="tg://user?id={sid}">{name}</a>'
                        await self.bot.send_message(
                            acc_row['user_id'],
                            f"⚠️ <b>антиспам · предупреждение</b> {warns}/{warn_max}\n\n"
                            f"{who}\nпричина: {violation}",
                            parse_mode='HTML'
                        )
                except: pass
                return
            else:
                # Исчерпаны предупреждения — блокируем
                self._warn_counts.pop(key, None)

        # action == 'block' или warn_max исчерпан — блокируем
        try:
            await c(BlockRequest(id=await ev.get_input_sender()))
            await db_run(
                "INSERT OR IGNORE INTO blacklist_cache(account_id,peer_id,peer_name,peer_user) "
                "VALUES(?,?,?,?)",
                (aid, sid, name, uname)
            )
            q.clear()
            self._warn_counts.pop((aid, sid), None)
            self._deleted_spam.pop((aid, sid), None)

            if self.bot and acc_row:
                who  = f'@{uname}' if uname else f'<a href="tg://user?id={sid}">{name}</a>'
                text_notify = (
                    f"🛡 <b>антиспам · заблокирован</b>\n\n"
                    f"{who}\nпричина: {violation}"
                )
                if action == 'warn+block':
                    text_notify += f"\n(исчерпаны предупреждения: {warn_max}/{warn_max})"
                try:
                    await self.bot.send_message(acc_row['user_id'], text_notify, parse_mode='HTML')
                except: pass
        except: pass

    async def _autoreply(self, c, ev, aid):
        import json as _json
        rules = await db_all("SELECT * FROM autoreply_rules WHERE account_id=? AND active=1", (aid,))
        text  = (ev.message.message or '').lower()
        now_h = datetime.now().hour * 60 + datetime.now().minute
        for r in rules:
            sch_start = (r.get('schedule_start') or '').strip()
            sch_end   = (r.get('schedule_end')   or '').strip()
            if sch_start and sch_end:
                try:
                    sh, sm = map(int, sch_start.split(':'))
                    eh, em = map(int, sch_end.split(':'))
                    s_min  = sh * 60 + sm; e_min = eh * 60 + em
                    if s_min <= e_min:
                        if not (s_min <= now_h <= e_min): continue
                    else:
                        if not (now_h >= s_min or now_h <= e_min): continue
                except: pass

            # Поддержка нескольких триггеров через "|"
            raw_trig = r.get('trig') or r.get('trigger_text') or ''
            triggers = [t.strip().lower() for t in raw_trig.split('|') if t.strip()]
            m   = r.get('match_type', 'contains')
            hit = False
            for t in triggers:
                if (m == 'exact' and text == t) or \
                   (m == 'contains' and t in text) or \
                   (m == 'startswith' and text.startswith(t)):
                    hit = True
                    break
            if not hit: continue
            try:
                content_raw = r.get('content_json') or ''
                if content_raw:
                    content_data = _json.loads(content_raw)
                    # Поддержка как списка (новый формат), так и одиночного объекта
                    items = content_data if isinstance(content_data, list) else [content_data]
                    for i, item in enumerate(items):
                        reply_to = ev.message.id if i == 0 else None
                        await self._send_content(c, ev.chat_id, item, reply_to=reply_to)
                        if i < len(items) - 1:
                            await asyncio.sleep(0.3)
                else:
                    resp = r.get('response') or r.get('response_text') or ''
                    await c.send_message(ev.chat_id, resp, reply_to=ev.message.id, parse_mode='html')
            except: pass
            break

    async def is_premium(self, aid: int) -> bool:
        """Проверяет, есть ли у аккаунта Telegram Premium."""
        c = self.get(aid)
        if not c:
            return False
        try:
            me = await c.get_me()
            return bool(getattr(me, 'premium', False))
        except Exception:
            return False

    async def _apply_default_privacy(self, aid: int):
        """Применяет безопасные настройки приватности для нового/восстановленного аккаунта."""
        c = self.get(aid)
        if not c:
            return
        try:
            await asyncio.sleep(3)  # даём клиенту прогреться
            # Номер телефона — только контакты
            # Статус — только контакты
            # Фото — все (не скрываем)
            allow_contacts = [InputPrivacyValueAllowContacts()]
            allow_all      = [InputPrivacyValueAllowAll()]
            for key, rules in [
                (InputPrivacyKeyPhoneNumber(),     allow_contacts),
                (InputPrivacyKeyStatusTimestamp(), allow_contacts),
                (InputPrivacyKeyProfilePhoto(),    allow_all),
                (InputPrivacyKeyAbout(),           allow_all),
            ]:
                try:
                    await c(SetPrivacyRequest(key=key, rules=rules))
                    await asyncio.sleep(0.5)
                except Exception as e:
                    log.debug(f"_apply_default_privacy {aid}: {e}")
            log.info(f"Default privacy applied for account {aid}")
        except Exception as e:
            log.warning(f"_apply_default_privacy {aid}: {e}")

    # ── Чёрный список ──
    async def get_blacklist(self, aid) -> List[dict]:
        """Загружает чёрный список напрямую из Telegram, обновляет кэш."""
        c   = self.get(aid)
        out = []
        if c:
            try:
                # Telegram отдаёт все заблокированные контакты
                result = await c(GetBlockedRequest(offset=0, limit=200))
                users  = getattr(result, 'users', []) or []
                for u in users:
                    out.append({
                        'id':       u.id,
                        'name':     (getattr(u, 'first_name', '') or '') + ' ' + (getattr(u, 'last_name', '') or ''),
                        'username': getattr(u, 'username', '') or '',
                    })
                    out[-1]['name'] = out[-1]['name'].strip()
                # Обновляем кэш
                await db_run("DELETE FROM blacklist_cache WHERE account_id=?", (aid,))
                for r in out:
                    await db_run(
                        "INSERT INTO blacklist_cache(account_id,peer_id,peer_name,peer_user) VALUES(?,?,?,?)",
                        (aid, r['id'], r['name'], r['username'])
                    )
            except Exception as e:
                log.warning(f"get_blacklist live failed: {e}, using cache")
                rows = await db_all("SELECT * FROM blacklist_cache WHERE account_id=?", (aid,))
                out  = [{'id': r['peer_id'], 'name': r['peer_name'] or '—', 'username': r['peer_user'] or ''} for r in rows]
        else:
            rows = await db_all("SELECT * FROM blacklist_cache WHERE account_id=?", (aid,))
            out  = [{'id': r['peer_id'], 'name': r['peer_name'] or '—', 'username': r['peer_user'] or ''} for r in rows]
        return out

    async def unblock_user(self, aid, user_id) -> bool:
        c = self.get(aid)
        if not c: return False
        try:
            await c(UnblockRequest(id=user_id))
            await db_run("DELETE FROM blacklist_cache WHERE account_id=? AND peer_id=?", (aid, user_id))
            return True
        except: return False

    async def clear_bl(self, aid) -> int:
        c = self.get(aid)
        if not c: return 0
        n = 0
        try:
            result = await c(GetBlockedRequest(offset=0, limit=200))
            users  = getattr(result, 'users', []) or []
            for u in users:
                try:
                    await c(UnblockRequest(id=u.id))
                    n += 1
                    await asyncio.sleep(0.4)
                except: pass
            await db_run("DELETE FROM blacklist_cache WHERE account_id=?", (aid,))
        except Exception as e:
            log.error(f"clear_bl {e}")
        return n

    # ── Диалоги (для слайдера удаления) ──
    async def get_dialogs_by_type(self, aid: int, ftype: str = 'all') -> List[dict]:
        """Возвращает отфильтрованный список диалогов."""
        c = self.get(aid)
        if not c: return []
        out = []
        try:
            dialogs = await c.get_dialogs(limit=500)
            for d in dialogs:
                e    = d.entity
                name = getattr(e, 'title', None) or getattr(e, 'first_name', '') or '?'
                if getattr(e, 'last_name', ''): name += ' ' + e.last_name
                name = name.strip()
                if isinstance(e, User):
                    dtype = 'bot' if e.bot else 'private'
                elif isinstance(e, Channel):
                    dtype = 'channel' if e.broadcast else 'group'
                elif isinstance(e, Chat):
                    dtype = 'group'
                else:
                    dtype = 'private'
                if getattr(e, 'forum', False): dtype = 'forum'
                if ftype != 'all' and dtype != ftype: continue
                out.append({'id': d.id, 'name': name, 'type': dtype})
        except Exception as e:
            log.error(f"get_dialogs_by_type {e}")
        return out

    # ── Массовое удаление сообщений с прогрессом ──
    async def mass_delete_my_msgs(self, aid: int, chat_id: int, progress_cb=None) -> int:
        c = self.get(aid)
        if not c: return -1
        try:
            entity = await c.get_entity(chat_id)
        except Exception as e:
            log.error(f"get_entity {e}"); return -1

        # Собираем все ID своих сообщений
        msg_ids = []
        try:
            async for msg in c.iter_messages(entity, from_user='me', limit=None):
                msg_ids.append(msg.id)
        except Exception as e:
            log.error(f"iter_messages {e}"); return -1

        total = len(msg_ids)
        if progress_cb: await progress_cb(0, total)

        deleted = 0
        # Удаляем батчами по 100
        for i in range(0, total, 100):
            batch = msg_ids[i:i + 100]
            try:
                await c.delete_messages(entity, batch)
                deleted += len(batch)
            except Exception as e:
                log.warning(f"delete_messages batch {e}")
                # Пробуем по одному при ошибке
                for mid in batch:
                    try:
                        await c.delete_messages(entity, [mid])
                        deleted += 1
                    except: pass
                    await asyncio.sleep(0.1)
            if progress_cb:
                await progress_cb(deleted, total)
            await asyncio.sleep(0.5)

        return deleted

    # ── Рассылка ──
    async def _send_content(self, c, entity, content: dict, reply_to=None, buttons=None) -> None:
        """Отправляет контент любого типа через Telethon-клиент."""
        ctype   = content.get('type', 'text')
        caption = content.get('caption', '') or ''
        extra   = {}
        if reply_to: extra['reply_to'] = reply_to
        if buttons:  extra['buttons']  = buttons
        if ctype == 'text':
            raw_text = content.get('text', '')
            ents_json = content.get('entities', [])
            if ents_json:
                tl_entities = _build_telethon_entities(ents_json)
                await c.send_message(entity, raw_text,
                                     formatting_entities=tl_entities,
                                     link_preview=False, **extra)
            else:
                await c.send_message(entity, raw_text, parse_mode='html',
                                     link_preview=False, **extra)
            return
        # ── альбом ──
        if ctype == 'album':
            items = content.get('items', [])
            if not items:
                return
            files = []
            cap   = content.get('caption', '') or ''
            for i, it in enumerate(items):
                bio = BytesIO()
                await self.bot.download(it['file_id'], destination=bio)
                bio.seek(0)
                bio.name = it.get('filename', 'file')
                files.append(bio)
            await c.send_file(entity, files,
                              caption=cap or None,
                              parse_mode='html', **extra)
            return
        # Медиа: скачиваем через Bot API → BytesIO → Telethon
        bio = BytesIO()
        await self.bot.download(content['file_id'], destination=bio)
        bio.seek(0)
        bio.name = content.get('filename', 'file')
        if ctype == 'sticker':
            await c.send_file(entity, bio, **extra)
        elif ctype == 'video_note':
            await c.send_file(entity, bio, video_note=True, **extra)
        elif ctype == 'voice':
            await c.send_file(entity, bio, voice_note=True,
                              caption=caption, parse_mode='html', **extra)
        elif ctype == 'audio':
            await c.send_file(entity, bio, caption=caption, parse_mode='html', **extra)
        else:
            await c.send_file(entity, bio, caption=caption, parse_mode='html', **extra)

    async def broadcast(self, aid: int, user_id: int, usernames: List[str],
                        items: list, progress_cb=None) -> dict:
        """
        Рассылка нескольких сообщений любого типа каждому получателю.
        items — список content-dict (как в черновиках).
        """
        c = self.get(aid)
        if not c:  return {'sent': 0, 'failed': 0, 'errors': ['клиент не активен']}
        if not self.bot: return {'sent': 0, 'failed': 0, 'errors': ['bot не задан']}

        total  = len(usernames)
        sent   = 0
        failed = 0
        errors = []
        self._broadcasts[aid] = {'running': True}

        # Поддержка старого формата (один dict вместо списка)
        if isinstance(items, dict):
            items = [items]

        preview = items[0].get('text') or items[0].get('caption') or f"[{items[0].get('type','?')}]" if items else "?"
        log_id = await db_run(
            "INSERT INTO broadcast_log(account_id,message,total) VALUES(?,?,?)",
            (aid, preview[:500], total)
        )

        for i, uname in enumerate(usernames):
            if not self._broadcasts.get(aid, {}).get('running', True):
                errors.append("рассылка остановлена")
                break
            uname = uname.strip().lstrip('@')
            if not uname: continue
            try:
                entity = await c.get_entity(uname)
                _ACTION_MAP = {
                    'text': 'typing',          'photo': 'upload-photo',
                    'video': 'upload-video',   'voice': 'record-audio',
                    'video_note': 'record-round', 'audio': 'upload-audio',
                    'document': 'upload-document', 'sticker': 'typing',
                    'animation': 'upload-video', 'album': 'upload-photo',
                }
                for item in items:
                    act = _ACTION_MAP.get(item.get('type', 'text'), 'typing')
                    async with c.action(entity, act):
                        await asyncio.sleep(random.uniform(1.0, 3.0))
                    await self._send_content(c, entity, item)
                    if len(items) > 1:
                        await asyncio.sleep(random.uniform(1.0, 5.0))
                sent += 1
                await db_run("UPDATE broadcast_log SET sent=? WHERE id=?", (sent, log_id))
                if progress_cb:
                    await progress_cb(i + 1, total, sent, failed)
                delay = random.uniform(5, 15)
                if sent % 10 == 0:
                    delay += random.uniform(15, 30)
                await asyncio.sleep(delay)
            except FloodWaitError as e:
                wait = e.seconds + 10
                log.warning(f"broadcast FloodWait {wait}s")
                if progress_cb:
                    await progress_cb(i + 1, total, sent, failed,
                                      status=f"⏳ FloodWait, жду {wait}s...")
                await asyncio.sleep(wait)
                try:
                    entity = await c.get_entity(uname)
                    for item in items:
                        act = _ACTION_MAP.get(item.get('type', 'text'), 'typing')
                        async with c.action(entity, act):
                            await asyncio.sleep(random.uniform(1.0, 2.0))
                        await self._send_content(c, entity, item)
                        if len(items) > 1:
                            await asyncio.sleep(random.uniform(1.0, 5.0))
                    sent += 1
                except Exception as e2:
                    failed += 1; errors.append(f"@{uname}: {e2}")
            except PeerFloodError:
                errors.append("слишком много запросов — Telegram заблокировал рассылку")
                break
            except (UserPrivacyRestrictedError, UserIsBlockedError):
                failed += 1
                errors.append(f"@{uname}: приватность/заблокирован")
            except InputUserDeactivatedError:
                failed += 1
                errors.append(f"@{uname}: аккаунт удалён")
            except Exception as e:
                failed += 1
                errors.append(f"@{uname}: {e}")

        await db_run(
            "UPDATE broadcast_log SET sent=?, failed=? WHERE id=?",
            (sent, failed, log_id)
        )
        self._broadcasts.pop(aid, None)
        return {'sent': sent, 'failed': failed, 'total': total, 'errors': errors}

    def stop_broadcast(self, aid: int):
        if aid in self._broadcasts:
            self._broadcasts[aid]['running'] = False
    # ── Статистика чатов (с подсчётом ВСЕХ сообщений через API) ──
    async def sync_chat_history(self, aid: int, chat_id: int, progress_cb=None) -> int:
        """Загружает всю историю чата в кэш (для полной статистики)."""
        c = self.get(aid)
        if not c: return 0
        n = 0
        try:
            entity = await c.get_entity(chat_id)
            cname  = getattr(entity, 'title', None) or getattr(entity, 'first_name', '') or ''
            async for msg in c.iter_messages(entity, limit=None):
                if not msg: continue
                sender = await msg.get_sender() if msg.sender_id else None
                sname  = getattr(sender, 'first_name', '') if sender else ''
                sid    = getattr(sender, 'id', 0) if sender else 0
                susr   = getattr(sender, 'username', '') or '' if sender else ''
                is_out = 1 if msg.out else 0
                # ВСЕГДА используем aid (account_id) — не 0
                await self._cache_message(aid, msg, chat_id, cname, sname, sid, susr, is_out)
                n += 1
                if progress_cb and n % 200 == 0:
                    await progress_cb(n)
                await asyncio.sleep(0)  # yield
        except Exception as e:
            log.error(f"sync_chat_history {e}")
        return n

    async def refresh_stats_cache(self, aid: int) -> None:
        """Фоновое обновление stats_cache через Telegram API.
        Запускается в фоне — не блокирует UI."""
        c = self.get(aid)
        if not c:
            return
        try:
            dialogs = await c.get_dialogs(limit=500)
            # msg_cache агрегат одним запросом
            agg_rows = await db_all(
                "SELECT chat_id, COUNT(*) as total, "
                "SUM(CASE WHEN is_outgoing=0 THEN 1 ELSE 0 END) as inc, "
                "SUM(CASE WHEN is_outgoing=1 THEN 1 ELSE 0 END) as out, "
                "SUM(is_voice) as voices, SUM(is_videonote) as vn, "
                "SUM(has_media) as media "
                "FROM msg_cache WHERE account_id=? GROUP BY chat_id",
                (aid,)
            )
            agg = {r['chat_id']: r for r in agg_rows}

            for d in dialogs:
                e = d.entity
                if not isinstance(e, User) or e.bot:
                    continue
                name = (getattr(e, 'first_name', '') or '').strip()
                if getattr(e, 'last_name', None):
                    name += ' ' + e.last_name.strip()
                name = name.strip() or '?'
                username = getattr(e, 'username', '') or ''
                # total через API без перебора сообщений
                total_msgs = 0
                try:
                    res = await c.get_messages(e, limit=0)
                    total_msgs = getattr(res, 'total', 0) or 0
                except Exception:
                    total_msgs = agg.get(d.id, {}).get('total', 0) or 0
                ag       = agg.get(d.id, {})
                last_str = d.date.strftime('%d.%m.%Y %H:%M') if d.date else ''

                # Подсчёт ГС, кружков и медиа через Telegram API (точные данные)
                voices_cnt = ag.get('voices', 0) or 0
                vn_cnt     = ag.get('vn', 0) or 0
                media_cnt  = ag.get('media', 0) or 0
                try:
                    rv = await c.get_messages(e, limit=0, filter=InputMessagesFilterVoice)
                    voices_cnt = getattr(rv, 'total', 0) or voices_cnt
                    await asyncio.sleep(0.1)
                    rr = await c.get_messages(e, limit=0, filter=InputMessagesFilterRoundVideo)
                    vn_cnt = getattr(rr, 'total', 0) or vn_cnt
                    await asyncio.sleep(0.1)
                    rm = await c.get_messages(e, limit=0, filter=InputMessagesFilterPhotoVideo)
                    media_cnt = getattr(rm, 'total', 0) or media_cnt
                    await asyncio.sleep(0.1)
                except Exception:
                    pass  # используем данные из msg_cache если API недоступен

                await db_run(
                    "INSERT INTO stats_cache"
                    "(account_id,chat_id,chat_name,username,total_msgs,out_msgs,"
                    "voices,videonotes,media_count,unread,last_date,updated_at)"
                    "VALUES(?,?,?,?,?,?,?,?,?,?,?,CURRENT_TIMESTAMP)"
                    "ON CONFLICT(account_id,chat_id) DO UPDATE SET "
                    "chat_name=excluded.chat_name, username=excluded.username,"
                    "total_msgs=excluded.total_msgs, out_msgs=excluded.out_msgs,"
                    "voices=excluded.voices, videonotes=excluded.videonotes,"
                    "media_count=excluded.media_count, unread=excluded.unread,"
                    "last_date=excluded.last_date, updated_at=CURRENT_TIMESTAMP",
                    (aid, d.id, name, username, total_msgs,
                     ag.get('out', 0) or 0,
                     voices_cnt, vn_cnt, media_cnt,
                     d.unread_count or 0, last_str)
                )
                await asyncio.sleep(0.15)   # не флудим API

            # Удаляем из кэша чаты которых больше нет в диалогах (удалены/забанены)
            live_ids = {d.id for d in dialogs if isinstance(d.entity, User) and not d.entity.bot}
            cached_ids_rows = await db_all(
                "SELECT chat_id FROM stats_cache WHERE account_id=?", (aid,)
            )
            for row in cached_ids_rows:
                if row['chat_id'] not in live_ids:
                    await db_run(
                        "DELETE FROM stats_cache WHERE account_id=? AND chat_id=?",
                        (aid, row['chat_id'])
                    )
        except Exception as e:
            log.error(f"refresh_stats_cache {aid}: {e}")

    async def get_stats_from_cache(self, aid: int) -> List[dict]:
        """Мгновенно возвращает статистику из локальной БД."""
        rows = await db_all(
            "SELECT * FROM stats_cache WHERE account_id=? ORDER BY total_msgs DESC",
            (aid,)
        )
        # Обогащаем данными из msg_cache (реального времени) если есть
        agg_rows = await db_all(
            "SELECT chat_id, COUNT(*) as total, "
            "SUM(CASE WHEN is_outgoing=0 THEN 1 ELSE 0 END) as inc, "
            "SUM(CASE WHEN is_outgoing=1 THEN 1 ELSE 0 END) as out, "
            "SUM(is_voice) as voices, SUM(is_videonote) as vn, SUM(has_media) as media "
            "FROM msg_cache WHERE account_id=? GROUP BY chat_id",
            (aid,)
        )
        agg = {r['chat_id']: r for r in agg_rows}
        result = []
        for r in rows:
            ag = agg.get(r['chat_id'], {})
            result.append({
                'id':          r['chat_id'],
                'name':        r['chat_name'] or '?',
                'username':    r['username'] or '',
                'unread':      r['unread'] or 0,
                'last':        r['last_date'] or '—',
                'total_msgs':  max(r['total_msgs'] or 0, ag.get('total', 0) or 0),
                'out_msgs':    max(r['out_msgs'] or 0, ag.get('out', 0) or 0),
                'voices':      max(r['voices'] or 0, ag.get('voices', 0) or 0),
                'videonotes':  max(r['videonotes'] or 0, ag.get('vn', 0) or 0),
                'media_count': max(r['media_count'] or 0, ag.get('media', 0) or 0),
                'updated_at':  r['updated_at'] or '',
            })
        # Если кэш пуст — возвращаем из msg_cache напрямую
        if not result:
            for cid, ag in agg.items():
                row = await db_get(
                    "SELECT chat_name, sender_name FROM msg_cache "
                    "WHERE account_id=? AND chat_id=? LIMIT 1", (aid, cid)
                )
                name = row['chat_name'] or row['sender_name'] or f'id:{cid}' if row else f'id:{cid}'
                result.append({
                    'id': cid, 'name': name, 'username': '', 'unread': 0,
                    'last': '—', 'total_msgs': ag.get('total', 0) or 0,
                    'out_msgs': ag.get('out', 0) or 0,
                    'voices': ag.get('voices', 0) or 0,
                    'videonotes': ag.get('vn', 0) or 0,
                    'media_count': ag.get('media', 0) or 0,
                    'updated_at': '',
                })
            result.sort(key=lambda x: x['total_msgs'], reverse=True)
        return result

    async def check_restrictions(self, aid):
        c = self.get(aid)
        if not c: return {'error': 'клиент не активен'}
        try:
            me = await c.get_me()
            reasons = []
            if me.restricted and hasattr(me, 'restriction_reason'):
                for x in (me.restriction_reason or []):
                    reasons.append(f"{x.platform}: {x.reason}")
            return {
                'restricted': bool(me.restricted),
                'reasons':    reasons,
                'phone':      me.phone,
                'name':       f"{me.first_name or ''} {me.last_name or ''}".strip(),
                'username':   me.username or '',
            }
        except Exception as e:
            return {'error': str(e)}


cm = CM()

# ══════════════════════════════════════
# UI HELPERS
# ══════════════════════════════════════
def kb(*rows) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=list(rows))

def b(text, data) -> InlineKeyboardButton:
    return InlineKeyboardButton(text=text, callback_data=data)

def bu(text, url) -> InlineKeyboardButton:
    return InlineKeyboardButton(text=text, url=url)

def paginate(items, page, per=6):
    total = len(items)
    pages = max(1, (total + per - 1) // per)
    page  = max(0, min(page, pages - 1))
    return items[page*per:(page+1)*per], page, pages

def nav(page, pages, pfx):
    row = []
    if page > 0:          row.append(b("◀️", f"{pfx}:{page-1}"))
    if page < pages - 1: row.append(b("▶️", f"{pfx}:{page+1}"))
    return row

async def edit(cb: CallbackQuery, text: str, markup: InlineKeyboardMarkup):
    try:
        await cb.message.edit_text(text, reply_markup=markup, parse_mode='HTML')
    except TelegramBadRequest:
        pass
    await cb.answer()

async def delete_user_msg(msg: Message):
    try: await msg.delete()
    except: pass

_CHAT_TYPE_ICONS = {'channel':'📢','group':'👥','private':'👤','bot':'🤖','forum':'💬'}

# ══════════════════════════════════════
# ГЛАВНОЕ МЕНЮ
# ══════════════════════════════════════
MAIN_TEXT = "🤖 <b>мои аккаунты</b>\n\nуправляй аккаунтами в одном месте"

def main_kb():
    return kb([b("👤 мои аккаунты", "accs:0"), b("➕ добавить", "add_acc")])

router = Router()
_auth_clients: dict = {}  # user_id -> TelegramClient (kept alive between send_code and sign_in)

# ── Access Guard Middleware — защита от несанкционированного доступа ──
from typing import Callable, Any
class AccessGuardMiddleware(BaseMiddleware):
    async def __call__(
        self,
        handler: Callable,
        event: Any,
        data: dict,
    ) -> Any:
        # Получаем user_id из event
        user = getattr(event, 'from_user', None)
        if not user:
            return  # неизвестный источник — игнорируем
        uid = user.id

        # Проверка whitelist
        if not _is_allowed(uid):
            log.warning(f"Unauthorized access from user_id={uid}")
            return  # молча игнорируем

        # Проверка rate limit
        if not _check_rate_limit(uid):
            # Отвечаем только на Message и CallbackQuery
            if isinstance(event, CallbackQuery):
                try: await event.answer("⚠️ слишком много запросов, подождите", show_alert=True)
                except: pass
            elif isinstance(event, Message):
                try: await event.answer("⚠️ слишком много запросов, подождите немного")
                except: pass
            return

        return await handler(event, data)
_rate_counters: dict = defaultdict(lambda: deque())
_RATE_LIMIT_MSGS = 20   # максимум сообщений
_RATE_LIMIT_WINDOW = 10  # за N секунд

def _check_rate_limit(user_id: int) -> bool:
    """True если пользователь не превысил лимит, False если заблокирован."""
    now = time.time()
    q = _rate_counters[user_id]
    q.append(now)
    while q and now - q[0] > _RATE_LIMIT_WINDOW:
        q.popleft()
    return len(q) <= _RATE_LIMIT_MSGS

def _is_allowed(user_id: int) -> bool:
    """Проверяет, разрешён ли доступ к боту для данного user_id."""
    if ALLOWED_USERS and user_id not in ALLOWED_USERS:
        return False
    return True

@router.message(CommandStart())
async def cmd_start(msg: Message, state: FSMContext):
    await state.clear()
    if msg.from_user.id in _auth_clients:
        try: await _auth_clients.pop(msg.from_user.id).disconnect()
        except: pass
    accs = await db_all("SELECT id FROM accounts WHERE user_id=? AND active=1", (msg.from_user.id,))
    txt  = MAIN_TEXT + f"\n\n<b>аккаунтов:</b> {len(accs)}"
    data = await state.get_data()
    if data.get('menu_id'):
        try: await msg.bot.delete_message(msg.chat.id, data['menu_id'])
        except: pass
    sent = await msg.answer(txt, reply_markup=main_kb(), parse_mode='HTML')
    await state.update_data(menu_id=sent.message_id)

@router.callback_query(F.data == "main")
async def cb_main(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    if cb.from_user.id in _auth_clients:
        try: await _auth_clients.pop(cb.from_user.id).disconnect()
        except: pass
    accs = await db_all("SELECT id FROM accounts WHERE user_id=? AND active=1", (cb.from_user.id,))
    txt  = MAIN_TEXT + f"\n\n<b>аккаунтов:</b> {len(accs)}"
    await edit(cb, txt, main_kb())

@router.callback_query(F.data == "noop")
async def cb_noop(cb: CallbackQuery): await cb.answer()

# ══════════════════════════════════════
# СПИСОК АККАУНТОВ
# ══════════════════════════════════════
@router.callback_query(F.data.startswith("accs:"))
async def cb_accs(cb: CallbackQuery):
    page = int(cb.data.split(":")[1])
    accs = await db_all("SELECT * FROM accounts WHERE user_id=? AND active=1", (cb.from_user.id,))
    if not accs:
        await edit(cb,
            "👥 <b>мои аккаунты</b>\n\nнет аккаунтов — добавьте первый",
            kb([b("➕ добавить", "add_acc")], [b("🏠 главная", "main")])
        ); return
    chunk, page, pages = paginate(accs, page, 5)
    rows = []
    for a in chunk:
        online = "🟢" if cm.get(a['id']) else "🔴"
        icons  = ""
        if a.get('always_online'): icons += "🌐"
        if a.get('auto_read'):     icons += "📖"
        label  = f"{online} {icons} {a['name'] or a['phone']}".strip()
        rows.append([b(label, f"acc:{a['id']}")])
    if pages > 1: rows.append(nav(page, pages, "accs"))
    rows.append([b("➕ добавить", "add_acc"), b("🏠 главная", "main")])
    await edit(cb, f"👥 <b>мои аккаунты</b>  ·  {len(accs)} шт", kb(*rows))

# ══════════════════════════════════════
# МЕНЮ АККАУНТА
# ══════════════════════════════════════
@router.callback_query(F.data.startswith("acc:"))
async def cb_acc(cb: CallbackQuery):
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    st    = "🟢 онлайн" if cm.get(aid) else "🔴 офлайн"
    icons = ""
    if acc.get('always_online'): icons += " 🌐"
    if acc.get('auto_read'):     icons += " 📖"
    await edit(cb,
        f"⚙️ <b>{acc['name'] or acc['phone']}</b>{icons}\n\n"
        f"📱 <code>{acc['phone']}</code>  ·  @{acc['username'] or '—'}\n"
        f"📶 {st}",
        kb(
            [b("📊 данные",     f"s_data:{aid}"), b("🤖 авто",      f"s_auto:{aid}")],
            [b("🛡 защита",     f"s_prot:{aid}"), b("👻 режимы",    f"s_mode:{aid}")],
            [b("⚙️ настройки", f"s_cfg:{aid}"),  b("🚪 выйти",     f"rm:{aid}")],
            [b("🔑 последний код", f"tgcode:{aid}"), b("‹ назад", "accs:0")]
        )
    )

# ── раздел: данные ──
@router.callback_query(F.data.startswith("s_data:"))
async def cb_s_data(cb: CallbackQuery):
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    await edit(cb, "📊 <b>данные</b>",
        kb(
            [b("📊 статистика",    f"stats:{aid}:0"),
             b("📋 чёрный список", f"bl:{aid}:0")],
            [b("🗑 удалённые",     f"dmsgs:{aid}:0"),
             b("🖼 медиа",         f"otime:{aid}:0")],
            [b("📬 непрочитанные", f"unread:{aid}:private")],
            [b("👥 группы и каналы", f"mychats:{aid}:0")],
            [b("‹ назад",          f"acc:{aid}")]
        )
    )

# ── раздел: авто ──
@router.callback_query(F.data.startswith("s_auto:"))
async def cb_s_auto(cb: CallbackQuery):
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    await edit(cb, "🤖 <b>автоматизация</b>",
        kb(
            [b("💬 ответы и сообщения",  f"s_auto_replies:{aid}")],
            [b("👁 мониторинг",          f"s_auto_monitor:{aid}")],
            [b("⚡ действия",            f"s_auto_actions:{aid}")],
            [b("‹ назад", f"acc:{aid}")]
        )
    )

@router.callback_query(F.data.startswith("s_auto_replies:"))
async def cb_s_auto_replies(cb: CallbackQuery):
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    ar  = "✅" if acc.get('autoreply_on') else "☐"
    dnd = "✅" if acc.get('dnd_mode')     else "☐"
    await edit(cb, "💬 <b>ответы и сообщения</b>",
        kb(
            [b(f"🤖 автоответчик {ar}",    f"ar:{aid}:menu")],
            [b(f"🔕 не беспокоить {dnd}",  f"dnd:{aid}:toggle")],
            [b("📝 черновики",             f"drafts:{aid}:list:0")],
            [b("‹ назад", f"s_auto:{aid}")]
        )
    )

@router.callback_query(F.data.startswith("s_auto_monitor:"))
async def cb_s_auto_monitor(cb: CallbackQuery):
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    await edit(cb, "👁 <b>мониторинг</b>",
        kb(
            [b("🔔 ключевые слова",   f"kw:{aid}:list")],
            [b("📡 трекер онлайна",   f"ot:{aid}:list")],
            [b("‹ назад", f"s_auto:{aid}")]
        )
    )

@router.callback_query(F.data.startswith("s_auto_actions:"))
async def cb_s_auto_actions(cb: CallbackQuery):
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    await edit(cb, "⚡ <b>действия</b>",
        kb(
            [b("📢 рассылка",            f"broadcast:{aid}:menu")],
            [b("🗑 удалить мои сообщ",   f"massdel:{aid}:menu")],
            [b("‹ назад", f"s_auto:{aid}")]
        )
    )


# ── раздел: защита ──
@router.callback_query(F.data.startswith("s_prot:"))
async def cb_s_prot(cb: CallbackQuery):
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    sec  = "✅" if acc.get('security_mode') else "☐"
    await edit(cb, "🛡 <b>защита аккаунта</b>",
        kb(
            [b(f"🔒 антиспам {sec}", f"sec_toggle:{aid}")],
            [b("⚙️ настройки антиспама", f"spam_cfg:{aid}:menu")],
            [b("🔍 проверить аккаунт", f"chk:{aid}")],
            [b("‹ назад",              f"acc:{aid}")]
        )
    )

# ── раздел: режимы ──
@router.callback_query(F.data.startswith("s_mode:"))
async def cb_s_mode(cb: CallbackQuery):
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    ao = "✅" if acc.get('always_online') else "☐"
    ar = "✅" if acc.get('auto_read')     else "☐"
    await edit(cb, f"👻 <b>режимы работы</b>",
        kb(
            [b(f"🌐 вечно онлайн {ao}", f"mode_tog:{aid}:online")],
            [b(f"📖 авточиталка {ar}",   f"mode_tog:{aid}:read")],
            [b("⚙️ настройки авточиталки", f"autoread_cfg:{aid}")],
            [b("‹ назад",                   f"acc:{aid}")]
        )
    )

@router.callback_query(F.data.startswith("mode_tog:"))
async def cb_mode_tog(cb: CallbackQuery):
    parts = cb.data.split(":")
    aid, mode = int(parts[1]), parts[2]
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    if mode == "online":
        new = 0 if acc.get('always_online') else 1
        await cm.set_always_online(aid, bool(new))
    elif mode == "read":
        new = 0 if acc.get('auto_read') else 1
        await db_run("UPDATE accounts SET auto_read=? WHERE id=?", (new, aid))
    await cb.answer()
    acc2 = await db_get("SELECT * FROM accounts WHERE id=?", (aid,))
    ao   = "✅" if acc2.get('always_online') else "☐"
    ar   = "✅" if acc2.get('auto_read')     else "☐"
    try:
        await cb.message.edit_text(
            f"👻 <b>режимы работы</b>",
            reply_markup=kb(
                [b(f"🌐 вечно онлайн {ao}", f"mode_tog:{aid}:online")],
                [b(f"📖 авточиталка {ar}",   f"mode_tog:{aid}:read")],
                [b("⚙️ настройки авточиталки", f"autoread_cfg:{aid}")],
                [b("‹ назад",                   f"acc:{aid}")]
            ), parse_mode='HTML'
        )
    except: pass

@router.callback_query(F.data.startswith("autoread_cfg:"))
async def cb_autoread_cfg(cb: CallbackQuery):
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    flt = acc.get('auto_read_filter', 'all')
    def _mark(typ): return "✅" if (flt == 'all' or (flt != 'none' and typ in flt.split(','))) else "☐"
    await edit(cb,
        f"📖 <b>авточиталка — фильтры</b>\n\nвыбери чаты для автопрочтения:",
        kb(
            [b(f"{_mark('all')} все чаты",    f"ar_flt:{aid}:all")],
            [b(f"{_mark('private')} личные",   f"ar_flt:{aid}:private"),
             b(f"{_mark('bot')} боты",          f"ar_flt:{aid}:bot")],
            [b(f"{_mark('group')} группы",      f"ar_flt:{aid}:group"),
             b(f"{_mark('channel')} каналы",    f"ar_flt:{aid}:channel")],
            [b(f"{_mark('forum')} форумы",      f"ar_flt:{aid}:forum")],
            [b("‹ назад", f"s_mode:{aid}")]
        )
    )

@router.callback_query(F.data.startswith("ar_flt:"))
async def cb_ar_flt(cb: CallbackQuery):
    parts = cb.data.split(":")
    aid, typ = int(parts[1]), parts[2]
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    flt = acc.get('auto_read_filter', 'all')
    if typ == 'all':
        new_flt = 'none' if flt == 'all' else 'all'
    else:
        types = set(flt.split(',')) if flt not in ('all', 'none', '') else set()
        if typ in types: types.discard(typ)
        else: types.add(typ)
        new_flt = ','.join(types) if types else 'none'
    await db_run("UPDATE accounts SET auto_read_filter=? WHERE id=?", (new_flt, aid))
    await cb.answer()
    acc2 = await db_get("SELECT * FROM accounts WHERE id=?", (aid,))
    flt2 = acc2.get('auto_read_filter', 'all')
    def _mark(t): return "✅" if (flt2 == 'all' or (flt2 not in ('none', '') and t in flt2.split(','))) else "☐"
    try:
        await cb.message.edit_text(
            f"📖 <b>авточиталка — фильтры</b>\n\nвыбери чаты для автопрочтения:",
            reply_markup=kb(
                [b(f"{_mark('all')} все чаты",    f"ar_flt:{aid}:all")],
                [b(f"{_mark('private')} личные",   f"ar_flt:{aid}:private"),
                 b(f"{_mark('bot')} боты",          f"ar_flt:{aid}:bot")],
                [b(f"{_mark('group')} группы",      f"ar_flt:{aid}:group"),
                 b(f"{_mark('channel')} каналы",    f"ar_flt:{aid}:channel")],
                [b(f"{_mark('forum')} форумы",      f"ar_flt:{aid}:forum")],
                [b("‹ назад", f"s_mode:{aid}")]
            ), parse_mode='HTML'
        )
    except: pass

# ── настройки уведомлений ──
@router.callback_query(F.data.startswith("s_cfg:"))
async def cb_s_cfg(cb: CallbackQuery):
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    nd = "✅" if acc.get('notify_deleted', 1) else "❌"
    nm = "✅" if acc.get('notify_media', 1)   else "❌"
    await edit(cb, "⚙️ <b>уведомления</b>",
        kb(
            [b(f"{nd} удалённые сообщения", f"cfg_tog:{aid}:notify_deleted")],
            [b(f"{nm} одноразовые медиа",   f"cfg_tog:{aid}:notify_media")],
            [b("‹ назад",                   f"acc:{aid}")]
        )
    )

@router.callback_query(F.data.startswith("cfg_tog:"))
async def cb_cfg_tog(cb: CallbackQuery):
    parts = cb.data.split(":")
    aid   = int(parts[1])
    field = parts[2]
    acc   = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    if field not in ('notify_deleted', 'notify_media'): await cb.answer(); return
    new = 0 if acc.get(field, 1) else 1
    await db_run(f"UPDATE accounts SET {field}=? WHERE id=?", (new, aid))
    await cb.answer()
    acc2 = await db_get("SELECT * FROM accounts WHERE id=?", (aid,))
    nd   = "✅" if acc2.get('notify_deleted', 1) else "❌"
    nm   = "✅" if acc2.get('notify_media', 1)   else "❌"
    try:
        await cb.message.edit_text(
            "⚙️ <b>уведомления</b>",
            reply_markup=kb(
                [b(f"{nd} удалённые сообщения", f"cfg_tog:{aid}:notify_deleted")],
                [b(f"{nm} одноразовые медиа",   f"cfg_tog:{aid}:notify_media")],
                [b("‹ назад",                   f"acc:{aid}")]
            ), parse_mode='HTML'
        )
    except: pass

# ══════════════════════════════════════
# ДОБАВЛЕНИЕ АККАУНТА (живые статусы)
# ══════════════════════════════════════
@router.callback_query(F.data == "add_acc")
async def cb_add(cb: CallbackQuery, state: FSMContext):
    await state.set_state(Auth.phone)
    await state.update_data(msg_id=cb.message.message_id, chat_id=cb.message.chat.id)
    await edit(cb,
        "➕ <b>добавление аккаунта</b>\n\n"
        "📱 введите номер телефона:\n<code>+79991234567</code>",
        kb([b("отмена", "main")])
    )

@router.message(Auth.phone)
async def auth_phone(msg: Message, state: FSMContext):
    await delete_user_msg(msg)
    data  = await state.get_data()
    mid   = data.get('msg_id')
    cid   = data.get('chat_id', msg.chat.id)
    raw   = msg.text.strip() if msg.text else ""
    phone = re.sub(r'[\s\-().]', '', raw)
    if not phone.startswith('+'): phone = '+' + phone
    # 8XXXXXXXXXX → +7XXXXXXXXXX
    if re.match(r'^\+8\d{10}$', phone):
        phone = '+7' + phone[2:]

    async def upd(text, markup=kb()):
        try: await msg.bot.edit_message_text(text, chat_id=cid, message_id=mid,
                                              reply_markup=markup, parse_mode='HTML')
        except: pass

    if not re.match(r'^\+\d{7,15}$', phone):
        await upd(
            "➕ <b>добавление аккаунта</b>\n\n"
            "❌ неверный формат\nпример: <code>+79991234567</code>",
            kb([b("отмена", "main")])
        ); return

    # ── Живые статусы регистрации ──
    await upd("📱 <b>добавление аккаунта</b>\n\n🔌 подключаюсь к Telegram...")
    await asyncio.sleep(0.5)

    client = TelegramClient(
        StringSession(), API_ID, API_HASH,
        device_model="Galaxy S25 Ultra",
        system_version="Android 15",
        app_version="12.4.3",
        lang_code="ru",
        system_lang_code="ru-RU",
        connection_retries=5,
        retry_delay=3,
        flood_sleep_threshold=60,
    )
    try:
        await client.connect()
        await upd(f"📱 <b>добавление аккаунта</b>\n\n📱 <code>{phone}</code>\n\n📤 отправляю код...")
        await asyncio.sleep(0.4)
        result = await client.send_code_request(phone)
        # Keep client alive! Disconnecting breaks phone_code_hash for DC-migrated numbers
        _auth_clients[msg.from_user.id] = client
        await state.update_data(phone=phone, hash=result.phone_code_hash, entered="")
        await state.set_state(Auth.code)
        text, markup = _code_view(phone, "")
        await upd(f"✅ <b>код отправлен!</b>\n\n" + text.split('\n\n', 1)[-1]
                  if '\n\n' in text else text, markup)
        # Редактируем на нормальный вид
        await upd(text, markup)
    except FloodWaitError as e:
        try: await client.disconnect()
        except: pass

        from datetime import datetime, timedelta, timezone
        MSK = timezone(timedelta(hours=3))

        def _fmt_flood(seconds_left: int) -> str:
            ready_at = datetime.now(MSK) + timedelta(seconds=seconds_left)
            ready_str = ready_at.strftime("%H:%M:%S")
            if seconds_left < 60:
                human = f"{seconds_left} сек"
            elif seconds_left < 3600:
                m, s = divmod(seconds_left, 60)
                human = f"{m} мин {s} сек" if s else f"{m} мин"
            else:
                h, rem = divmod(seconds_left, 3600)
                m = rem // 60
                human = f"{h} ч {m} мин" if m else f"{h} ч"
            return (
                f"⏳ <b>слишком много запросов</b>\n\n"
                f"осталось ждать: <b>{human}</b>\n"
                f"попробовать можно в: <b>{ready_str}</b>\n\n"
                f"⏱ код будет отправлен автоматически"
            )

        total = e.seconds
        flood_markup = kb([b("‹ назад", "main")])
        await upd(_fmt_flood(total), flood_markup)

        async def _flood_autoretry(seconds_total: int):
            import time as _time
            _start = _time.monotonic()
            while True:
                await asyncio.sleep(10)
                _elapsed = int(_time.monotonic() - _start)
                _left = seconds_total - _elapsed
                if _left <= 0:
                    break
                try: await upd(_fmt_flood(_left), flood_markup)
                except: pass
            await asyncio.sleep(2)
            try:
                await upd(
                    f"📱 <b>добавление аккаунта</b>\n\n"
                    f"📱 <code>{phone}</code>\n\n🔄 повторяю отправку кода..."
                )
                retry_client = TelegramClient(
                    StringSession(), API_ID, API_HASH,
                    device_model="Galaxy S25 Ultra",
                    system_version="Android 15",
                    app_version="12.4.3",
                    lang_code="ru",
                    system_lang_code="ru-RU",
                )
                await retry_client.connect()
                retry_result = await retry_client.send_code_request(phone)
                _auth_clients[cid] = retry_client
                await state.update_data(phone=phone, hash=retry_result.phone_code_hash, entered="")
                await state.set_state(Auth.code)
                text, markup = _code_view(phone, "")
                await upd(text, markup)
            except FloodWaitError as e2:
                await upd(_fmt_flood(e2.seconds), flood_markup)
                asyncio.create_task(_flood_autoretry(e2.seconds))
            except Exception as ex:
                await upd(f"❌ ошибка при повторной отправке: <code>{ex}</code>", kb([b("‹ назад", "main")]))

        asyncio.create_task(_flood_autoretry(total))
    except PhoneNumberInvalidError:
        try: await client.disconnect()
        except: pass
        await upd("❌ неверный номер телефона", kb([b("‹ назад", "main")]))
    except Exception as e:
        try: await client.disconnect()
        except: pass
        await upd(f"❌ ошибка подключения: <code>{e}</code>", kb([b("‹ назад", "main")]))

def _code_view(phone: str, code: str):
    slots  = [f"<b>{code[i]}</b>" if i < len(code) else "–" for i in range(5)]
    visual = "  ".join(slots)
    text   = (
        f"📲 <b>введите код из Telegram</b>\n\n"
        f"📱 <code>{phone}</code>\n\n"
        f"┌ {visual} ┐\n"
        f"код придёт в приложении Telegram"
    )
    markup = kb(
        [b("1","cd:1"), b("2","cd:2"), b("3","cd:3")],
        [b("4","cd:4"), b("5","cd:5"), b("6","cd:6")],
        [b("7","cd:7"), b("8","cd:8"), b("9","cd:9")],
        [b("⌫","cd:⌫"), b("0","cd:0"), b("✅","cd:✅")],
        [b("📞 позвоните мне", "cd:call")],
        [b("отмена","main")]
    )
    return text, markup

@router.callback_query(F.data.startswith("cd:"), Auth.code)
async def auth_code_btn(cb: CallbackQuery, state: FSMContext):
    digit = cb.data.split(":")[1]
    data  = await state.get_data()
    code  = data.get('entered', '')
    phone = data.get('phone', '')
    if digit == 'call':
        uid = cb.from_user.id
        client = _auth_clients.get(uid)
        if client and client.is_connected():
            try:
                from telethon.tl.functions.auth import ResendCodeRequest
                data2 = await state.get_data()
                await client(ResendCodeRequest(phone, data2['hash']))
                await cb.answer()
            except Exception as ex:
                err = str(ex)
                if "SEND_CODE_UNAVAILABLE" in err or "all available options" in err.lower():
                    await cb.answer()
                else:
                    await cb.answer()
        else:
            await cb.answer()
        return
    if digit == '⌫':
        code = code[:-1]
    elif digit == '✅':
        if len(code) < 4: return
        await _do_sign_in(cb, state, phone, code, data); return
    elif digit.isdigit() and len(code) < 5:
        code += digit
    await state.update_data(entered=code)
    text, markup = _code_view(phone, code)
    try: await cb.message.edit_text(text, reply_markup=markup, parse_mode='HTML')
    except TelegramBadRequest: pass
    await cb.answer()
    if len(code) == 5:
        await asyncio.sleep(0.3)
        await _do_sign_in(cb, state, phone, code, data)

async def _do_sign_in(cb, state, phone, code, data):
    mid = data.get('msg_id') or cb.message.message_id
    cid = cb.message.chat.id

    async def upd(text, markup=kb()):
        try: await cb.bot.edit_message_text(text, chat_id=cid, message_id=mid,
                                             reply_markup=markup, parse_mode='HTML')
        except: pass

    await upd("📲 <b>проверяю код</b>\n\n⏳ авторизация...")
    uid = cb.from_user.id
    client = _auth_clients.pop(uid, None)
    if client is None or not client.is_connected():
        # Fallback: reconnect with saved session
        client = TelegramClient(StringSession(data.get('session_str', '')), API_ID, API_HASH)
        await client.connect()
    elif not await client.is_user_authorized():
        if not client.is_connected(): await client.connect()
    try:
        await client.sign_in(phone=phone, code=code, phone_code_hash=data['hash'])
        await upd("📲 <b>авторизация</b>\n\n✅ код принят, загружаю данные...")
        me  = await client.get_me()
        ss  = client.session.save()
        await client.disconnect()
        aid = await db_run(
            "INSERT INTO accounts(user_id,phone,session_string,name,username) VALUES(?,?,?,?,?)",
            (cb.from_user.id, phone, ss,
             f"{me.first_name or ''} {me.last_name or ''}".strip(),
             me.username or '')
        )
        acc = await db_get("SELECT * FROM accounts WHERE id=?", (aid,))
        await cm.start(acc)
        asyncio.create_task(cm._apply_default_privacy(aid))
        await state.clear()
        await upd(
            f"✅ <b>аккаунт добавлен!</b>\n\n"
            f"👤 <b>{me.first_name or ''} {me.last_name or ''}</b>\n"
            f"📱 <code>+{me.phone}</code>\n🔗 @{me.username or '—'}",
            kb([b("⚙️ управление", f"acc:{aid}")], [b("🏠 главная", "main")])
        )
        await cb.answer()
    except SessionPasswordNeededError:
        ss = client.session.save()
        await client.disconnect()
        await state.update_data(tmp_session=ss)
        await state.set_state(Auth.password)
        await upd(
            f"🔐 <b>двухфакторная аутентификация</b>\n\n"
            f"📱 <code>{phone}</code>\n\n"
            f"введите пароль 2FA:",
            kb([b("отмена", "main")])
        )
        await cb.answer()
    except PhoneCodeInvalidError:
        await client.disconnect()
        await state.update_data(entered='')
        text, markup = _code_view(phone, '')
        try:
            await cb.bot.edit_message_text(
                f"❌ <b>неверный код!</b>\n\n" + text,
                chat_id=cid, message_id=mid, reply_markup=markup, parse_mode='HTML'
            )
        except: pass
        await cb.answer()
    except Exception as e:
        try: await client.disconnect()
        except: pass
        await upd(f"❌ ошибка: <code>{e}</code>", kb([b("‹ назад", "main")]))
        await cb.answer()

@router.message(Auth.password)
async def auth_password(msg: Message, state: FSMContext):
    await delete_user_msg(msg)
    data  = await state.get_data()
    mid   = data.get('msg_id')
    cid   = data.get('chat_id', msg.chat.id)
    phone = data.get('phone', '')
    ss    = data.get('tmp_session', '')
    pw    = msg.text.strip() if msg.text else ""

    async def upd(text, markup=kb()):
        try: await msg.bot.edit_message_text(text, chat_id=cid, message_id=mid,
                                              reply_markup=markup, parse_mode='HTML')
        except: pass

    await upd("🔐 <b>2FA</b>\n\n⏳ проверяю пароль...")
    client = TelegramClient(StringSession(ss), API_ID, API_HASH)
    await client.connect()
    try:
        await client.sign_in(password=pw)
        await upd("🔐 <b>2FA</b>\n\n✅ пароль принят, загружаю данные...")
        me  = await client.get_me()
        s   = client.session.save()
        await client.disconnect()
        aid = await db_run(
            "INSERT INTO accounts(user_id,phone,session_string,name,username) VALUES(?,?,?,?,?)",
            (msg.from_user.id, phone, s,
             f"{me.first_name or ''} {me.last_name or ''}".strip(),
             me.username or '')
        )
        acc = await db_get("SELECT * FROM accounts WHERE id=?", (aid,))
        await cm.start(acc)
        asyncio.create_task(cm._apply_default_privacy(aid))
        await state.clear()
        await upd(
            f"✅ <b>аккаунт добавлен!</b>\n\n"
            f"👤 <b>{me.first_name or ''}</b>\n📱 <code>+{me.phone}</code>",
            kb([b("⚙️ управление", f"acc:{aid}")], [b("🏠 главная", "main")])
        )
    except Exception as e:
        try: await client.disconnect()
        except: pass
        await upd(
            f"🔐 <b>2FA</b>\n\n❌ неверный пароль\n\nвведите снова:",
            kb([b("отмена", "main")])
        )

# ══════════════════════════════════════
# СТАТИСТИКА
# ══════════════════════════════════════
_sync_last_run: dict = {}   # {aid: timestamp}
_sync_running:  set  = set()  # aids currently syncing

async def _bg_sync_all(aid: int):
    """Фоновая синхронизация. Запускается не чаще 1 раза в 10 минут."""
    if aid in _sync_running:
        return  # уже идёт
    now = time.time()
    if now - _sync_last_run.get(aid, 0) < 600:  # 10 минут кулдаун
        return
    _sync_running.add(aid)
    _sync_last_run[aid] = now
    c = cm.get(aid)
    if not c:
        _sync_running.discard(aid)
        return
    try:
        # Берём диалоги из уже загруженного списка (не делаем лишний запрос)
        dialogs = await c.get_dialogs(limit=200)
        for d in dialogs:
            if not cm.get(aid): break  # клиент отключился
            try:
                await cm.sync_chat_history(aid, d.id)
                await asyncio.sleep(1.5)  # пауза между чатами
            except Exception:
                pass
    except Exception as e:
        log.debug(f"bg_sync_all {e}")
    finally:
        _sync_running.discard(aid)

# ══════════════════════════════════════
# СТАТИСТИКА
# ══════════════════════════════════════
def _fmt_num(n) -> str:
    """Форматирует число: 1 234 567 → '1.2M', 12 345 → '12.3k', иначе как есть."""
    if n is None: return '0'
    n = int(n)
    if n >= 1_000_000: return f"{n/1_000_000:.1f}M"
    if n >= 1_000:     return f"{n/1_000:.1f}k"
    return str(n)


def _bar(val: int, total: int, w: int = 8) -> str:
    if not total: return '░' * w
    filled = round(val / total * w)
    filled = max(0, min(w, filled))
    return '█' * filled + '░' * (w - filled)


_STATS_PAGE = 8


async def _live_analyze_stats(bot, cid: int, mid: int, aid: int) -> None:
    c = cm.get(aid)
    if not c: return

    async def _upd(text: str):
        try: await bot.edit_message_text(text, chat_id=cid, message_id=mid, parse_mode='HTML')
        except Exception: pass

    try:
        await _upd("📊 <b>анализ</b> — загружаю диалоги...")
        dialogs = await c.get_dialogs(limit=None)
        user_dialogs = [d for d in dialogs if isinstance(d.entity, User) and not d.entity.bot]
        total = len(user_dialogs)
        if not total:
            await _upd("📊 нет личных чатов"); return

        me = await c.get_me()
        done = 0
        for d in user_dialogs:
            e = d.entity
            name = ((getattr(e,"first_name","") or "") + " " + (getattr(e,"last_name","") or "")).strip() or f"id:{e.id}"
            username = getattr(e, "username", "") or ""
            done += 1
            pct = int(done / total * 100)
            bar = "█" * (pct // 10) + "░" * (10 - pct // 10)
            await _upd(f"📊 <b>анализирую</b> {done}/{total}\n<code>{bar}</code> {pct}%\n👤 {name}")

            total_msgs = voices_cnt = vn_cnt = media_cnt = 0
            try:
                res = await c.get_messages(e, limit=0)
                total_msgs = getattr(res, "total", 0) or 0
            except Exception: pass
            await asyncio.sleep(0.07)
            try:
                rv = await c.get_messages(e, limit=0, filter=InputMessagesFilterVoice)
                voices_cnt = getattr(rv, "total", 0) or 0
                await asyncio.sleep(0.07)
                rr = await c.get_messages(e, limit=0, filter=InputMessagesFilterRoundVideo)
                vn_cnt = getattr(rr, "total", 0) or 0
                await asyncio.sleep(0.07)
                rm = await c.get_messages(e, limit=0, filter=InputMessagesFilterPhotoVideo)
                media_cnt = getattr(rm, "total", 0) or 0
                await asyncio.sleep(0.07)
            except Exception: pass
            last_str = d.date.strftime("%d.%m.%Y  %H:%M") if d.date else ""
            await db_run(
                "INSERT INTO stats_cache"
                "(account_id,chat_id,chat_name,username,total_msgs,out_msgs,"
                "voices,videonotes,media_count,unread,last_date,updated_at)"
                "VALUES(?,?,?,?,?,?,?,?,?,?,?,CURRENT_TIMESTAMP)"
                "ON CONFLICT(account_id,chat_id) DO UPDATE SET "
                "chat_name=excluded.chat_name,username=excluded.username,"
                "total_msgs=excluded.total_msgs,out_msgs=excluded.out_msgs,"
                "voices=excluded.voices,videonotes=excluded.videonotes,"
                "media_count=excluded.media_count,unread=excluded.unread,"
                "last_date=excluded.last_date,updated_at=CURRENT_TIMESTAMP",
                (aid,d.id,name,username,total_msgs,0,voices_cnt,vn_cnt,media_cnt,d.unread_count or 0,last_str)
            )
            await asyncio.sleep(0.05)

        live_ids = {d.id for d in user_dialogs}
        for row in await db_all("SELECT chat_id FROM stats_cache WHERE account_id=?", (aid,)):
            if row["chat_id"] not in live_ids:
                await db_run("DELETE FROM stats_cache WHERE account_id=? AND chat_id=?", (aid, row["chat_id"]))

        await _render_stats(bot, cid, mid, aid, 0)
    except Exception as ex:
        log.error(f"_live_analyze_stats {aid}: {ex}")
        try: await _render_stats(bot, cid, mid, aid, 0)
        except Exception: pass


async def _render_stats(bot, cid: int, mid: int, aid: int, page: int) -> None:
    rows_db = await db_all("SELECT * FROM stats_cache WHERE account_id=? ORDER BY total_msgs DESC", (aid,))
    if not rows_db:
        try:
            await bot.edit_message_text(
                "📊 <b>статистика</b>\n\n<i>нет данных — открой снова для анализа</i>",
                chat_id=cid, message_id=mid,
                reply_markup=kb([b("‹ назад", f"s_data:{aid}")]), parse_mode='HTML')
        except Exception: pass
        return

    total_chats = len(rows_db)
    page = max(0, min(page, total_chats))

    # ── СВОДКА ────────────────────────────────────────────────────
    if page == 0:
        tm  = sum(r["total_msgs"] or 0 for r in rows_db)
        tu  = sum(r["unread"] or 0 for r in rows_db)
        tv  = sum(r["voices"] or 0 for r in rows_db)
        tvn = sum(r["videonotes"] or 0 for r in rows_db)
        tmd = sum(r["media_count"] or 0 for r in rows_db)
        unr = f"  🔴{_fmt_num(tu)} непрочит" if tu else ""
        text = (
            f"📊 <b>статистика</b> · {_fmt_num(total_chats)} чатов{unr}\n"
            f"<blockquote>"
            f"💬 {_fmt_num(tm)} сообщений\n"
            f"🎙 {_fmt_num(tv)}  🎥 {_fmt_num(tvn)}  📎 {_fmt_num(tmd)}"
            f"</blockquote>"
            f"\n<i>👉 листай чаты →</i>"
        )
        rows = [
            [b("чаты ▶", f"stats:{aid}:1")],
            [b("🏆 топ", f"stats_top:{aid}"), b("‹ назад", f"s_data:{aid}")],
        ]
        try:
            await bot.edit_message_text(text, chat_id=cid, message_id=mid,
                reply_markup=kb(*rows), parse_mode='HTML')
        except Exception as ex: log.debug(f"render_stats summary: {ex}")
        return

    # ── СЛАЙДЕР ЧАТА ──────────────────────────────────────────────
    r    = rows_db[page - 1]
    name = r["chat_name"] or "?"
    uname= r["username"] or ""
    unr  = r["unread"] or 0
    last = r["last_date"] or "—"
    tm   = r["total_msgs"] or 0
    to   = r["out_msgs"] or 0
    ti   = max(tm - to, 0)
    vo   = r["voices"] or 0
    vn   = r["videonotes"] or 0
    md   = r["media_count"] or 0
    ts      = max(tm, 1)
    med_pct = int((vo+vn+md)/ts*100)

    uname_part = f" · @{uname}" if uname else ""
    unr_part   = f" · 🔴{unr}" if unr else ""
    pos        = f"{page}/{total_chats}"

    media_parts = []
    if vo: media_parts.append(f"🎙{_fmt_num(vo)}")
    if vn: media_parts.append(f"🎥{_fmt_num(vn)}")
    if md: media_parts.append(f"📎{_fmt_num(md)}")
    media_line = ("  ".join(media_parts) + f"  ({med_pct}%)\n") if media_parts else ""

    text = (
        f"👤 <b>{name}</b>{uname_part}{unr_part}  <i>· {pos}</i>\n"
        f"<blockquote expandable>"
        f"💬 {_fmt_num(tm)} сообщений\n"
        f"{media_line}"
        f"🕐 {last}"
        f"</blockquote>"
    )

    nav = []
    if page > 1:           nav.append(b("◀", f"stats:{aid}:{page-1}"))
    if page < total_chats: nav.append(b("▶", f"stats:{aid}:{page+1}"))
    rows = []
    if nav: rows.append(nav)
    rows.append([b("📊 сводка", f"stats:{aid}:0"), b("🏆 топ", f"stats_top:{aid}")])
    rows.append([b("‹ назад", f"s_data:{aid}")])
    try:
        await bot.edit_message_text(text, chat_id=cid, message_id=mid,
            reply_markup=kb(*rows), parse_mode='HTML')
    except Exception as ex: log.debug(f"render_stats slide: {ex}")


@router.callback_query(F.data.startswith("stats:"))
async def cb_stats(cb: CallbackQuery):
    await cb.answer()
    parts = cb.data.split(":")
    aid   = int(parts[1])
    page  = int(parts[2]) if len(parts) > 2 else 0
    acc   = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: return
    if page > 0:
        await _render_stats(cb.bot, cb.message.chat.id, cb.message.message_id, aid, page)
        return
    asyncio.create_task(_live_analyze_stats(cb.bot, cb.message.chat.id, cb.message.message_id, aid))


@router.callback_query(F.data == "stats_noop")
async def cb_stats_noop(cb: CallbackQuery): await cb.answer()


@router.callback_query(F.data.startswith("chat_detail:"))
async def cb_chat_detail(cb: CallbackQuery):
    await cb.answer()
    parts = cb.data.split(":")
    aid   = int(parts[1])
    acc   = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: return
    await _render_stats(cb.bot, cb.message.chat.id, cb.message.message_id, aid, 1)


@router.callback_query(F.data.startswith("stats_top:"))
async def cb_stats_top(cb: CallbackQuery):
    await cb.answer()
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: return
    top = await db_all(
        "SELECT chat_name,chat_id,total_msgs,out_msgs,voices,videonotes,media_count,last_date "
        "FROM stats_cache WHERE account_id=? AND total_msgs>0 ORDER BY total_msgs DESC LIMIT 15", (aid,))
    if not top:
        await cb.message.edit_text(
            "🏆 <b>топ</b>\n\n<i>нет данных</i>",
            reply_markup=kb([b("‹ назад", f"stats:{aid}:0")]), parse_mode='HTML')
        return
    max_cnt = max((r.get("total_msgs") or 0) for r in top) or 1
    medals  = ["🥇","🥈","🥉","4️⃣","5️⃣","6️⃣","7️⃣","8️⃣","9️⃣","🔟","11","12","13","14","15"]
    lines   = ["🏆 <b>топ чатов</b>\n"]
    for i, r in enumerate(top):
        medal = medals[i] if i < len(medals) else f"{i+1}."
        name  = (r.get("chat_name") or f"id:{r['chat_id']}")[:22]
        cnt   = r.get("total_msgs", 0) or 0
        to    = r.get("out_msgs", 0) or 0
        ti    = max(cnt - to, 0)
        bar   = _bar(cnt, max_cnt, 6)
        extras= []
        if r.get("voices"):      extras.append(f"🎙{_fmt_num(r['voices'])}")
        if r.get("videonotes"):  extras.append(f"🎥{_fmt_num(r['videonotes'])}")
        if r.get("media_count"): extras.append(f"📎{_fmt_num(r['media_count'])}")
        ext   = "  " + "  ".join(extras) if extras else ""
        last  = f"  🕐{r['last_date']}" if r.get("last_date") else ""
        lines.append(
            f"{medal} <b>{name}</b>  <code>{bar}</code> {_fmt_num(cnt)}\n   📥{_fmt_num(ti)} · 📤{_fmt_num(to)}{ext}{last}"
        )
    try:
        await cb.message.edit_text("\n".join(lines),
            reply_markup=kb([b("‹ к списку", f"stats:{aid}:0")]), parse_mode='HTML')
    except Exception: pass


# ══════════════════════════════════════
# ЧЁРНЫЙ СПИСОК  (слайдер: 1 запись, кнопки ◀ / ▶)
# ══════════════════════════════════════
@router.callback_query(F.data.startswith("bl:"))
async def cb_bl(cb: CallbackQuery):
    await cb.answer()          # без текста — никакого всплывающего тоста
    parts = cb.data.split(":")

    # ── очистить весь ЧС ──
    if parts[1] == "clr":
        aid = int(parts[2])
        acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
        if not acc: return
        stop = asyncio.Event()
        asyncio.create_task(animate_loading(cb.bot, cb.message.chat.id, cb.message.message_id,
                                            "🗑 <b>очищаю чёрный список</b>", stop))
        n = await cm.clear_bl(aid)
        stop.set()
        await edit(cb, f"✅ разблокировано <b>{n}</b> пользователей",
                   kb([b("📋 ЧС", f"bl:{aid}:0"), b("‹ назад", f"s_data:{aid}")])); return

    # ── разблокировать одного ──
    if parts[1] == "unblock":
        aid = int(parts[2]); uid = int(parts[3])
        idx = int(parts[4]) if len(parts) > 4 else 0
        acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
        if not acc: return
        await cm.unblock_user(aid, uid)
        bl = await cm.get_blacklist(aid)
        # После удаления сдвигаем page если вышли за границу
        if not bl:
            await edit(cb, "📋 <b>чёрный список</b>\n\nпуст — никто не заблокирован",
                       kb([b("↻ обновить", f"bl:{aid}:0"), b("‹ назад", f"s_data:{aid}")])); return
        per   = 4
        pages = max(1, (len(bl) + per - 1) // per)
        page  = min(idx, pages - 1)
        await _show_bl_slide(cb, aid, bl, page); return

    # ── загрузить / переключить слайдер ──
    aid  = int(parts[1])
    idx  = int(parts[2]) if len(parts) > 2 else 0
    acc  = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: return
    stop = asyncio.Event()
    asyncio.create_task(animate_loading(cb.bot, cb.message.chat.id, cb.message.message_id,
                                        "📋 <b>загружаю чёрный список</b>", stop))
    bl = await cm.get_blacklist(aid)
    stop.set()
    if not bl:
        await edit(cb, "📋 <b>чёрный список</b>\n\nпуст — никто не заблокирован",
                   kb([b("↻ обновить", f"bl:{aid}:0"), b("‹ назад", f"s_data:{aid}")])); return
    await _show_bl_slide(cb, aid, bl, idx)


async def _show_bl_slide(cb: CallbackQuery, aid: int, bl: list, page: int):
    """Слайдер: показываем 4 пользователей на странице."""
    per   = 4
    total = len(bl)
    pages = max(1, (total + per - 1) // per)
    page  = max(0, min(page, pages - 1))
    chunk = bl[page * per : (page + 1) * per]

    page_txt = f"  ·  {page+1}/{pages}" if pages > 1 else ""
    lines    = [f"📋 <b>чёрный список</b>  ·  {total} чел{page_txt}\n"]
    for u in chunk:
        tag  = f"@{u['username']}" if u['username'] else f"id:{u['id']}"
        name = (u['name'] or '—').strip()
        lines.append(f"🚫 <b>{name}</b>  <code>{tag}</code>")

    rows = []
    # Кнопки разблокировки для каждого на странице
    for u in chunk:
        name_s = (u['name'] or '—').strip()[:18]
        rows.append([b(f"🔓 {name_s}", f"bl:unblock:{aid}:{u['id']}:{page}")])

    nav_row = []
    if page > 0:       nav_row.append(b("◀️", f"bl:{aid}:{page - 1}"))
    if page < pages-1: nav_row.append(b("▶️", f"bl:{aid}:{page + 1}"))
    if nav_row: rows.append(nav_row)

    rows.append([b("🗑 очистить всё", f"bl:clr:{aid}"), b("‹ назад", f"s_data:{aid}")])
    await edit(cb, "\n".join(lines), kb(*rows))

# ══════════════════════════════════════
# УДАЛЁННЫЕ СООБЩЕНИЯ
# ══════════════════════════════════════
@router.callback_query(F.data.startswith("dmsgs:"))
async def cb_dmsgs(cb: CallbackQuery):
    parts = cb.data.split(":")
    if parts[1] == "clr":
        aid = int(parts[2])
        await db_run("DELETE FROM deleted_msgs WHERE account_id=?", (aid,))
        await edit(cb, "✅ история очищена", kb([b("‹ назад", f"s_data:{aid}")])); return
    aid, page = int(parts[1]), int(parts[2]) if len(parts) > 2 else 0
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    msgs = await db_all("SELECT * FROM deleted_msgs WHERE account_id=? ORDER BY deleted_at DESC", (aid,))
    if not msgs:
        await edit(cb, "🗑 <b>удалённые</b>\n\nпока ничего нет",
                   kb([b("‹ назад", f"s_data:{aid}")])); return
    chunk, page, pages = paginate(msgs, page, 4)
    lines = [f"🗑 <b>удалённые сообщения</b>  ·  {len(msgs)} шт\n"]
    for m in chunk:
        dt      = (m['deleted_at'] or '')[:16]
        preview = (m['text'] or '(медиа)')[:80]
        lines.append(
            f"🔸 <b>{m['sender_name'] or '—'}</b>  ·  <i>{m['chat_name'] or '?'}</i>\n"
            f"    ⏰ {dt}\n    <code>{preview}</code>"
        )
    rows = []
    if pages > 1: rows.append(nav(page, pages, f"dmsgs:{aid}"))
    rows.append([b("🗑 очистить", f"dmsgs:clr:{aid}"), b("‹ назад", f"s_data:{aid}")])
    await edit(cb, "\n".join(lines), kb(*rows))

# ══════════════════════════════════════
# ОДНОРАЗОВЫЕ МЕДИА
# ══════════════════════════════════════
@router.callback_query(F.data.startswith("otime:"))
async def cb_otime(cb: CallbackQuery):
    parts = cb.data.split(":")
    if parts[1] == "clr":
        aid = int(parts[2])
        await db_run("DELETE FROM onetime_media WHERE account_id=?", (aid,))
        await edit(cb, "✅ история очищена", kb([b("‹ назад", f"s_data:{aid}")])); return
    aid, page = int(parts[1]), int(parts[2]) if len(parts) > 2 else 0
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    media = await db_all("SELECT * FROM onetime_media WHERE account_id=? ORDER BY saved_at DESC", (aid,))
    if not media:
        await edit(cb, "🔐 <b>одноразовые медиа</b>\n\nпока ничего нет",
                   kb([b("‹ назад", f"s_data:{aid}")])); return
    chunk, page, pages = paginate(media, page, 8)
    lines = [f"🔐 <b>перехваченные медиа</b>  ·  {len(media)} шт\n"]
    for m in chunk:
        ic = {"photo":"🖼","voice":"🎙","video_note":"🎥","video":"📹"}.get(m['media_type'], "📎")
        dt = (m['saved_at'] or '')[:16]
        lines.append(f"{ic} <b>{m['from_name']}</b>  ·  {dt}  ·  {m['media_type']}")
    rows = []
    if pages > 1: rows.append(nav(page, pages, f"otime:{aid}"))
    rows.append([b("🗑 очистить", f"otime:clr:{aid}"), b("‹ назад", f"s_data:{aid}")])
    await edit(cb, "\n".join(lines), kb(*rows))

# ══════════════════════════════════════
# РЕЖИМ «НЕ БЕСПОКОИТЬ»
# ══════════════════════════════════════
@router.callback_query(F.data.startswith("dnd:"))
async def cb_dnd(cb: CallbackQuery, state: FSMContext):
    parts  = cb.data.split(":")
    aid    = int(parts[1])
    action = parts[2] if len(parts) > 2 else "menu"
    acc    = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    if action == "toggle":
        new = 0 if acc.get('dnd_mode') else 1
        await db_run("UPDATE accounts SET dnd_mode=? WHERE id=?", (new, aid))
        await cb.answer()
        acc = await db_get("SELECT * FROM accounts WHERE id=?", (aid,))
    dnd = "✅" if acc.get('dnd_mode') else "☐"
    txt = acc.get('dnd_text') or 'сейчас недоступен, напишу позже'
    await edit(cb,
        f"🔕 <b>не беспокоить</b>\n\n"
        f"автоответ на первое сообщение в чате раз в 30 минут\n\n"
        f"текст ответа:\n<blockquote>{txt}</blockquote>",
        kb(
            [b(f"🔕 режим {dnd}", f"dnd:{aid}:toggle")],
            [b("✏️ изменить текст", f"dnd:{aid}:edit")],
            [b("‹ назад", f"s_auto_replies:{aid}")]
        )
    )

@router.callback_query(F.data.regexp(r"^dnd:\d+:edit$"))
async def cb_dnd_edit(cb: CallbackQuery, state: FSMContext):
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    await state.set_state(DndText.text)
    await state.update_data(aid=aid, msg_id=cb.message.message_id, chat_id=cb.message.chat.id)
    await edit(cb, "✏️ введите новый текст автоответа:", kb([b("отмена", f"dnd:{aid}:menu")]))

@router.message(DndText.text)
async def dnd_text_input(msg: Message, state: FSMContext):
    await delete_user_msg(msg)
    data = await state.get_data()
    aid  = data['aid']; mid = data['msg_id']; cid = data['chat_id']
    text = (msg.text or '').strip()[:500]
    if text: await db_run("UPDATE accounts SET dnd_text=? WHERE id=?", (text, aid))
    await state.clear()
    acc = await db_get("SELECT * FROM accounts WHERE id=?", (aid,))
    dnd = "✅" if acc.get('dnd_mode') else "☐"
    txt = acc.get('dnd_text') or 'сейчас недоступен, напишу позже'
    try:
        await msg.bot.edit_message_text(
            f"🔕 <b>не беспокоить</b>\n\nтекст ответа:\n<blockquote>{txt}</blockquote>",
            chat_id=cid, message_id=mid,
            reply_markup=kb(
                [b(f"🔕 режим {dnd}", f"dnd:{aid}:toggle")],
                [b("✏️ изменить текст", f"dnd:{aid}:edit")],
                [b("‹ назад", f"s_auto_replies:{aid}")]
            ), parse_mode='HTML'
        )
    except: pass

# ══════════════════════════════════════
# НЕПРОЧИТАННЫЕ
# ══════════════════════════════════════
@router.callback_query(F.data.startswith("unread:"))
async def cb_unread(cb: CallbackQuery):
    parts  = cb.data.split(":")
    aid    = int(parts[1])
    filter_type = parts[2] if len(parts) > 2 else "private"   # по умолчанию — личные
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    stop = asyncio.Event()
    anim = asyncio.create_task(animate_loading(cb.bot, cb.message.chat.id, cb.message.message_id,
                                               "📬 <b>загружаю непрочитанные</b>", stop))
    await cb.answer()
    c = cm.get(aid)
    if not c:
        stop.set(); await edit(cb, "❌ клиент не активен", kb([b("‹ назад", f"s_data:{aid}")])); return
    try:
        dialogs = await c.get_dialogs(limit=300)
        # Фильтруем: только реальные личные чаты (User, не боты)
        unread = []
        for d in dialogs:
            if d.unread_count <= 0: continue
            e = d.entity
            if filter_type == "private":
                if not isinstance(e, User) or e.bot: continue
            unread.append((d, d.unread_count))
        unread.sort(key=lambda x: x[1], reverse=True)
        total = sum(u for _, u in unread)
        stop.set()
        try: await anim
        except: pass
        if not unread:
            label = "в личных чатах" if filter_type == "private" else "во всех чатах"
            await edit(cb, f"📬 непрочитанных {label} нет 🎉",
                       kb([b("📋 все чаты", f"unread:{aid}:all")],
                          [b("‹ назад", f"s_data:{aid}")])); return
        lines = [f"📬 <b>непрочитанные</b>  ·  всего {total}\n"]
        for d, cnt in unread[:20]:
            e    = d.entity
            name = getattr(e, 'title', None) or getattr(e, 'first_name', '') or '?'
            lines.append(f"🔴 <b>{name[:25]}</b>  ·  {cnt}")
        if len(unread) > 20: lines.append(f"\n…и ещё {len(unread)-20} чатов")
        # Кнопки
        rows = []
        if filter_type == "private":
            rows.append([b("📋 показать все чаты", f"unread:{aid}:all")])
        else:
            rows.append([b("👤 только личные", f"unread:{aid}:private")])
        rows.append([b("✅ прочитать всё", f"unread_readall:{aid}:{filter_type}")])
        rows.append([b("‹ назад", f"s_data:{aid}")])
        await edit(cb, "\n".join(lines), kb(*rows))
    except Exception as e:
        stop.set()
        await edit(cb, f"❌ ошибка: <code>{e}</code>", kb([b("‹ назад", f"s_data:{aid}")]))


@router.callback_query(F.data.startswith("unread_readall:"))
async def cb_unread_readall(cb: CallbackQuery):
    """Прочитать все непрочитанные диалоги выбранного типа."""
    parts       = cb.data.split(":")
    aid         = int(parts[1])
    filter_type = parts[2] if len(parts) > 2 else "private"
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    c = cm.get(aid)
    if not c:
        await cb.answer(); return

    stop = asyncio.Event()
    anim = asyncio.create_task(animate_loading(cb.bot, cb.message.chat.id, cb.message.message_id,
                                               "✅ <b>читаю все диалоги</b>", stop))
    await cb.answer()
    n = 0
    try:
        dialogs = await c.get_dialogs(limit=300)
        for d in dialogs:
            if d.unread_count <= 0: continue
            e = d.entity
            if filter_type == "private":
                if not isinstance(e, User) or e.bot: continue
            try:
                await c.send_read_acknowledge(d.entity, max_id=0, clear_mentions=False)
                n += 1
                await asyncio.sleep(0.05)
            except Exception as ex:
                log.debug(f"read_acknowledge {d.id}: {ex}")
    except Exception as ex:
        log.error(f"unread_readall {ex}")
    finally:
        stop.set()
        try: await anim
        except: pass

    label = "личных" if filter_type == "private" else "всех"
    await edit(cb,
        f"✅ <b>готово!</b>\n\nПрочитано {label} чатов: <b>{n}</b>",
        kb([b("📬 непрочитанные", f"unread:{aid}:{filter_type}"), b("‹ назад", f"s_data:{aid}")])
    )

# ══════════════════════════════════════
# АНТИСПАМ
# ══════════════════════════════════════
# ══════════════════════════════════════
# ⚙️ НАСТРОЙКИ АНТИСПАМА (расширенные)
# ══════════════════════════════════════
def _spam_cfg_kb(aid, acc):
    """Строит клавиатуру меню антиспама."""
    fl  = "✅" if acc.get('antispam_filter_links', 0)    else "☐"
    ff  = "✅" if acc.get('antispam_filter_forwards', 0) else "☐"
    fs  = "✅" if acc.get('antispam_filter_stickers', 0) else "☐"
    act = acc.get('antispam_action', 'block') or 'block'
    act_labels = {'block': '🚫 блок', 'delete': '🗑 удал', 'warn+block': '⚠️ пред+блок'}
    act_lbl = act_labels.get(act, act)
    thr = acc.get('spam_threshold', 5)
    win = acc.get('spam_window', 60)
    wm  = acc.get('antispam_warn_max', 3)
    return kb(
        [b(f"{fl} ссылки",   f"spam_cfg:{aid}:tog:links"),
         b(f"{ff} форварды", f"spam_cfg:{aid}:tog:forwards")],
        [b(f"{fs} стикеры",  f"spam_cfg:{aid}:tog:stickers")],
        [b(f"⚡ действие: {act_lbl}", f"spam_cfg:{aid}:action")],
        [b(f"📊 порог: {thr} сообщ / {win}с", f"spam_cfg:{aid}:threshold")],
        [b(f"⚠️ предупреждений до блока: {wm}", f"spam_cfg:{aid}:warnmax")],
        [b("👥 белый список", f"spam_cfg:{aid}:wl:0")],
        [b("‹ назад", f"s_prot:{aid}")]
    )

@router.callback_query(F.data.startswith("spam_cfg:"))
async def cb_spam_cfg(cb: CallbackQuery, state: FSMContext):
    await cb.answer()
    parts  = cb.data.split(":")
    aid    = int(parts[1])
    action = parts[2] if len(parts) > 2 else "menu"
    acc    = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: return

    if action == "menu":
        await edit(cb, "⚙️ <b>настройки антиспама</b>\n\nфильтры срабатывают дополнительно к порогу частоты", _spam_cfg_kb(aid, acc))

    elif action == "tog":
        field_map = {
            'links':    'antispam_filter_links',
            'forwards': 'antispam_filter_forwards',
            'stickers': 'antispam_filter_stickers',
        }
        key = parts[3] if len(parts) > 3 else ''
        col = field_map.get(key)
        if col:
            new = 0 if acc.get(col, 0) else 1
            await db_run(f"UPDATE accounts SET {col}=? WHERE id=?", (new, aid))
            acc2 = await db_get("SELECT * FROM accounts WHERE id=?", (aid,))
            try: await cb.message.edit_reply_markup(reply_markup=_spam_cfg_kb(aid, acc2))
            except: pass

    elif action == "action":
        # Циклически: block → delete → warn+block → block
        cur   = acc.get('antispam_action', 'block') or 'block'
        order = ['block', 'delete', 'warn+block']
        nxt   = order[(order.index(cur) + 1) % len(order)] if cur in order else 'block'
        await db_run("UPDATE accounts SET antispam_action=? WHERE id=?", (nxt, aid))
        acc2 = await db_get("SELECT * FROM accounts WHERE id=?", (aid,))
        try: await cb.message.edit_reply_markup(reply_markup=_spam_cfg_kb(aid, acc2))
        except: pass

    elif action == "threshold":
        await state.set_state(SpamCfg.value)
        await state.update_data(aid=aid, msg_id=cb.message.message_id,
                                chat_id=cb.message.chat.id, spam_field='threshold')
        thr = acc.get('spam_threshold', 5)
        win = acc.get('spam_window', 60)
        await edit(cb,
            f"📊 <b>порог частоты</b>\n\n"
            f"текущий: <b>{thr} сообщ за {win} сек</b>\n\n"
            f"формат: <code>кол-во:секунды</code>\nпример: <code>5:60</code>",
            kb([b("отмена", f"spam_cfg:{aid}:menu")])
        )

    elif action == "warnmax":
        await state.set_state(SpamCfg.value)
        await state.update_data(aid=aid, msg_id=cb.message.message_id,
                                chat_id=cb.message.chat.id, spam_field='warnmax')
        wm = acc.get('antispam_warn_max', 3)
        await edit(cb,
            f"⚠️ <b>предупреждений до блока</b>\n\n"
            f"текущее: <b>{wm}</b>\n\n"
            f"введите число (1–10):",
            kb([b("отмена", f"spam_cfg:{aid}:menu")])
        )

    elif action == "wl":
        page = int(parts[3]) if len(parts) > 3 else 0
        wl   = await db_all("SELECT * FROM antispam_whitelist WHERE account_id=?", (aid,))
        if not wl:
            await edit(cb,
                "👥 <b>белый список антиспама</b>\n\nпуст — все проверяются.\n\n"
                "добавленные пользователи не будут подпадать под фильтры.",
                kb([b("➕ добавить", f"spam_cfg:{aid}:wl_add"),
                    b("‹ назад", f"spam_cfg:{aid}:menu")])
            ); return
        chunk, page, pages = paginate(wl, page, 5)
        lines = [f"👥 <b>белый список</b>  ·  {len(wl)} чел\n"]
        rows  = []
        for u in chunk:
            tag  = f"@{u['peer_user']}" if u['peer_user'] else f"id:{u['peer_id']}"
            name = (u['peer_name'] or '—')[:20]
            lines.append(f"✅ {name}  <code>{tag}</code>")
            rows.append([b(f"🗑 {name}", f"spam_cfg:{aid}:wl_del:{u['id']}")])
        if pages > 1: rows.append(nav(page, pages, f"spam_cfg:{aid}:wl"))
        rows += [[b("➕ добавить", f"spam_cfg:{aid}:wl_add"),
                  b("‹ назад", f"spam_cfg:{aid}:menu")]]
        await edit(cb, "\n".join(lines), kb(*rows))

    elif action == "wl_del":
        wid = int(parts[3])
        await db_run("DELETE FROM antispam_whitelist WHERE id=? AND account_id=?", (wid, aid))
        cb.data = f"spam_cfg:{aid}:wl:0"
        await cb_spam_cfg(cb, state)

    elif action == "wl_add":
        await state.set_state(SpamCfg.value)
        await state.update_data(aid=aid, msg_id=cb.message.message_id,
                                chat_id=cb.message.chat.id, spam_field='wl_add')
        await edit(cb,
            "👥 <b>добавить в белый список</b>\n\nвведите @username или числовой ID:",
            kb([b("отмена", f"spam_cfg:{aid}:wl:0")])
        )


@router.message(SpamCfg.value)
async def spam_cfg_msg(msg: Message, state: FSMContext):
    await delete_user_msg(msg)
    data  = await state.get_data()
    aid   = data['aid']; mid = data['msg_id']; cid = data['chat_id']
    field = data.get('spam_field', 'threshold')

    async def upd(text, markup):
        try: await msg.bot.edit_message_text(text, chat_id=cid, message_id=mid,
                                              reply_markup=markup, parse_mode='HTML')
        except: pass

    if field == 'threshold':
        try:
            parts = (msg.text or '').strip().split(':')
            thr   = int(parts[0])
            win   = int(parts[1]) if len(parts) > 1 else 60
            if thr < 1 or win < 1: raise ValueError
            await db_run("UPDATE accounts SET spam_threshold=?, spam_window=? WHERE id=?",
                         (thr, win, aid))
            await state.clear()
            await upd(f"✅ порог: <b>{thr} сообщ / {win} сек</b>",
                      kb([b("‹ назад", f"spam_cfg:{aid}:menu")]))
        except:
            await upd("❌ неверный формат, пример: <code>5:60</code>",
                      kb([b("отмена", f"spam_cfg:{aid}:menu")]))

    elif field == 'warnmax':
        try:
            val = int((msg.text or '').strip())
            if not (1 <= val <= 10): raise ValueError
            await db_run("UPDATE accounts SET antispam_warn_max=? WHERE id=?", (val, aid))
            await state.clear()
            await upd(f"✅ предупреждений до блока: <b>{val}</b>",
                      kb([b("‹ назад", f"spam_cfg:{aid}:menu")]))
        except:
            await upd("❌ введите число от 1 до 10",
                      kb([b("отмена", f"spam_cfg:{aid}:menu")]))

    elif field == 'wl_add':
        raw = (msg.text or '').strip().lstrip('@')
        c   = cm.get(aid)
        if c and raw:
            try:
                entity = await c.get_entity(raw)
                pid    = entity.id
                pname  = getattr(entity, 'first_name', '') or getattr(entity, 'title', '') or raw
                pusr   = getattr(entity, 'username', '') or ''
                await db_run(
                    "INSERT OR IGNORE INTO antispam_whitelist(account_id,peer_id,peer_name,peer_user) "
                    "VALUES(?,?,?,?)", (aid, pid, pname, pusr)
                )
                await state.clear()
                await upd(f"✅ добавлен в белый список: <b>{pname}</b>",
                          kb([b("‹ к белому списку", f"spam_cfg:{aid}:wl:0")]))
            except Exception as e:
                await upd(f"❌ не найден: {e}",
                          kb([b("отмена", f"spam_cfg:{aid}:wl:0")]))
        else:
            await upd("❌ введите @username или ID",
                      kb([b("отмена", f"spam_cfg:{aid}:wl:0")]))

@router.callback_query(F.data.startswith("sec_toggle:"))
async def cb_sec_toggle(cb: CallbackQuery):
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    new = 0 if acc.get('security_mode', 0) else 1
    await db_run("UPDATE accounts SET security_mode=? WHERE id=?", (new, aid))
    await cb.answer()
    acc2 = await db_get("SELECT * FROM accounts WHERE id=?", (aid,))
    sec  = "✅" if acc2.get('security_mode') else "☐"
    try:
        await cb.message.edit_text(
            "🛡 <b>защита аккаунта</b>",
            reply_markup=kb(
                [b(f"🔒 антиспам {sec}", f"sec_toggle:{aid}")],
                [b("⚙️ настройки антиспама", f"spam_cfg:{aid}:menu")],
                [b("🔍 проверить аккаунт", f"chk:{aid}")],
                [b("‹ назад",              f"acc:{aid}")]
            ), parse_mode='HTML'
        )
    except: pass

@router.callback_query(F.data.startswith("chk:"))
async def cb_chk(cb: CallbackQuery):
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    await cb.answer()
    stop = asyncio.Event()
    anim = asyncio.create_task(animate_loading(cb.bot, cb.message.chat.id, cb.message.message_id,
                                               "🔍 <b>проверяю аккаунт</b>", stop))
    info = await cm.check_restrictions(aid)
    stop.set()
    try: await anim
    except: pass
    if 'error' in info:
        await edit(cb, f"❌ ошибка: <code>{info['error']}</code>", kb([b("‹ назад", f"s_prot:{aid}")])); return
    st  = "🚫 есть ограничения" if info['restricted'] else "✅ ограничений нет"
    rsn = "\n".join(f"  • {r}" for r in info['reasons']) if info['reasons'] else "—"
    await edit(cb,
        f"🔍 <b>статус аккаунта</b>\n\n"
        f"👤 {info['name']}  ·  @{info['username'] or '—'}\n"
        f"📱 <code>+{info['phone']}</code>\n\n"
        f"📶 {st}\n📋 причины: {rsn}",
        kb([b("‹ назад", f"s_prot:{aid}")])
    )

# ══════════════════════════════════════
# АВТООТВЕТЧИК
# ══════════════════════════════════════
async def _ar_menu(cb, aid, acc):
    rules = await db_all("SELECT id FROM autoreply_rules WHERE account_id=?", (aid,))
    st    = "✅" if acc.get('autoreply_on') else "☐"
    await edit(cb,
        f"🤖 <b>автоответчик</b>\n\nправил: <b>{len(rules)}</b>",
        kb(
            [b(f"↕️ вкл / выкл {st}", f"ar:{aid}:toggle")],
            [b("📋 правила", f"ar:{aid}:list:0"), b("➕ добавить", f"ar:{aid}:add")],
            [b("‹ назад", f"s_auto_replies:{aid}")]
        )
    )

@router.callback_query(F.data.startswith("ar:"))
async def cb_ar(cb: CallbackQuery, state: FSMContext):
    parts  = cb.data.split(":")
    aid    = int(parts[1])
    action = parts[2] if len(parts) > 2 else "menu"
    extra  = parts[3] if len(parts) > 3 else "0"
    acc    = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    if action == "menu":
        await _ar_menu(cb, aid, acc)
    elif action == "toggle":
        new = 0 if acc.get('autoreply_on', 0) else 1
        await db_run("UPDATE accounts SET autoreply_on=? WHERE id=?", (new, aid))
        acc['autoreply_on'] = new
        await cb.answer()
        await _ar_menu(cb, aid, acc)
    elif action == "list":
        page  = int(extra)
        rules = await db_all("SELECT * FROM autoreply_rules WHERE account_id=?", (aid,))
        if not rules:
            await edit(cb, "📋 правил нет",
                       kb([b("➕ добавить", f"ar:{aid}:add")],
                          [b("‹ назад", f"ar:{aid}:menu")])); return
        chunk, page, pages = paginate(rules, page, 5)
        lines = [f"📋 <b>правила</b>  ·  {len(rules)} шт\n"]
        rows  = []
        for r in chunk:
            st2  = "✅" if r['active'] else "❌"
            raw_trig = (r.get('trig') or r.get('trigger_text') or '?')
            # Показываем все триггеры через " | "
            trigs = [t.strip() for t in raw_trig.split('|') if t.strip()]
            trig_display = ' | '.join(trigs)[:25]
            import json as _jl
            cj = r.get('content_json') or ''
            count_label = ''
            if cj:
                try:
                    items_l = _jl.loads(cj)
                    if isinstance(items_l, list) and len(items_l) > 1:
                        count_label = f" · {len(items_l)} сообщ"
                except: pass
            sch  = ""
            if r.get('schedule_start') and r.get('schedule_end'):
                sch = f" 🕐{r['schedule_start']}-{r['schedule_end']}"
            lines.append(f"{st2} <code>{trig_display}</code>{count_label}{sch}")
            rows.append([
                b(f"🗑 {trig_display[:15]}", f"ar:{aid}:del:{r['id']}"),
                b(f"🕐 расписание", f"ar:{aid}:sched:{r['id']}")
            ])
        if pages > 1: rows.append(nav(page, pages, f"ar:{aid}:list"))
        rows.append([b("➕ добавить", f"ar:{aid}:add"), b("‹ назад", f"ar:{aid}:menu")])
        await edit(cb, "\n".join(lines), kb(*rows))
    elif action == "del":
        rid = int(extra)
        await db_run("DELETE FROM autoreply_rules WHERE id=? AND account_id=?", (rid, aid))
        await cb.answer()
        cb.data = f"ar:{aid}:list:0"
        await cb_ar(cb, state)
    elif action == "sched":
        rid  = int(extra)
        rule = await db_get("SELECT * FROM autoreply_rules WHERE id=? AND account_id=?", (rid, aid))
        if not rule: await cb.answer(); return
        ss = rule.get('schedule_start') or ''
        se = rule.get('schedule_end')   or ''
        sch_txt = f"{ss}–{se}" if ss and se else "не задано"
        await state.set_state(ARSchedule.value)
        await state.update_data(aid=aid, rid=rid, msg_id=cb.message.message_id, chat_id=cb.message.chat.id)
        await edit(cb,
            f"🕐 <b>расписание автоответа</b>\n\n"
            f"текущее: <b>{sch_txt}</b>\n\n"
            f"формат: <code>09:00-23:00</code>\n"
            f"отправь <code>-</code> чтобы убрать расписание",
            kb([b("отмена", f"ar:{aid}:list:0")])
        )
    elif action == "add":
        await state.set_state(ARState.trigger)
        await state.update_data(aid=aid, msg_id=cb.message.message_id, chat_id=cb.message.chat.id)
        await edit(cb,
            "➕ <b>новое правило</b>  ·  шаг 1/3\n\n"
            "введите триггер или несколько триггеров — каждый с новой строки:",
            kb([b("отмена", f"ar:{aid}:menu")])
        )

@router.message(ARState.trigger)
async def ar_trigger(msg: Message, state: FSMContext):
    await delete_user_msg(msg)
    data = await state.get_data()
    raw = (msg.text or '').strip()
    if not raw:
        return
    # Парсим триггеры: каждый на новой строке
    triggers = [t.strip() for t in raw.splitlines() if t.strip()]
    if not triggers:
        return
    trig_str = ' | '.join(triggers)  # для отображения
    trig_db  = '|'.join(triggers)    # для хранения в БД
    await state.update_data(ar_trig=trig_db, ar_trig_display=trig_str, ar_items=[], ar_album_buf={})
    await state.set_state(ARState.content)
    try:
        await msg.bot.edit_message_text(
            f"➕ <b>новое правило</b>  ·  шаг 2/3\n\n"
            f"триггер(ы): <code>{trig_str[:200]}</code>\n\n"
            f"отправь одно или несколько сообщений — они все будут отправляться по триггеру\n"
            f"когда закончишь — нажми <b>готово</b>",
            chat_id=data['chat_id'], message_id=data['msg_id'],
            reply_markup=kb([
                b("✅ готово", f"ar_done:{data['aid']}"),
                b("отмена",   f"ar:{data['aid']}:menu"),
            ]),
            parse_mode='HTML'
        )
    except: pass


@router.message(ARState.content)
async def ar_content_input(msg: Message, state: FSMContext):
    await delete_user_msg(msg)
    data  = await state.get_data()
    aid   = data['aid']; mid = data['msg_id']; cid = data['chat_id']
    trig_str = data.get('ar_trig_display', '')
    items = data.get('ar_items', [])
    album_buf = data.get('ar_album_buf', {})

    # ── Альбом ──
    group_id = msg.media_group_id
    if group_id:
        grp_key = str(group_id)
        item = _msg_to_content(msg)
        if not item:
            return
        if grp_key not in album_buf:
            album_buf[grp_key] = []
        album_buf[grp_key].append(item)
        await state.update_data(ar_album_buf=album_buf)

        pending = data.get('ar_album_tasks', {})
        if grp_key in pending:
            try: pending[grp_key].cancel()
            except: pass

        async def _flush_ar_album(gk=grp_key):
            await asyncio.sleep(1.0)
            d2 = await state.get_data()
            buf2 = d2.get('ar_album_buf', {})
            group_items = buf2.pop(gk, [])
            if not group_items:
                return
            itms2 = d2.get('ar_items', [])
            cap = next((i.get('caption', '') for i in group_items if i.get('caption')), '')
            album_item = {'type': 'album', 'items': group_items, 'caption': cap}
            itms2.append(album_item)
            await state.update_data(ar_items=itms2, ar_album_buf=buf2)
            import json as _j2
            _, summ, _ = _draft_summary(_j2.dumps(itms2))
            try:
                await msg.bot.edit_message_text(
                    f"➕ <b>новое правило</b>  ·  шаг 2/3\n\n"
                    f"триггер(ы): <code>{trig_str[:200]}</code>\n"
                    f"добавлено: <b>{len(itms2)}</b>  ·  последнее: 🗂 альбом ({len(group_items)} шт)\n\n"
                    f"<blockquote expandable>{summ[:400]}</blockquote>\n\n"
                    f"можешь отправить ещё или нажать <b>готово</b>",
                    chat_id=cid, message_id=mid,
                    reply_markup=kb([
                        b(f"✅ готово ({len(itms2)})", f"ar_done:{aid}"),
                        b("отмена", f"ar:{aid}:menu"),
                    ]),
                    parse_mode='HTML'
                )
            except: pass

        task = asyncio.create_task(_flush_ar_album())
        pending[grp_key] = task
        await state.update_data(ar_album_tasks=pending)
        return

    # ── Одиночное сообщение ──
    item = _msg_to_content(msg)
    if not item:
        return

    items.append(item)
    await state.update_data(ar_items=items)

    import json as _j
    count = len(items)
    _, summary, _ = _draft_summary(_j.dumps(items))
    t  = item.get('type', '?')
    ic = _DRAFT_ICONS.get(t, '📄')
    lbl = _DRAFT_LABELS.get(t) or t
    try:
        await msg.bot.edit_message_text(
            f"➕ <b>новое правило</b>  ·  шаг 2/3\n\n"
            f"триггер(ы): <code>{trig_str[:200]}</code>\n"
            f"добавлено: <b>{count}</b>  ·  последнее: {ic} {lbl}\n\n"
            f"<blockquote expandable>{summary[:400]}</blockquote>\n\n"
            f"можешь отправить ещё или нажать <b>готово</b>",
            chat_id=cid, message_id=mid,
            reply_markup=kb([
                b(f"✅ готово ({count})", f"ar_done:{aid}"),
                b("отмена", f"ar:{aid}:menu"),
            ]),
            parse_mode='HTML'
        )
    except: pass


@router.callback_query(F.data.startswith("ar_done:"), ARState.content)
async def ar_done(cb: CallbackQuery, state: FSMContext):
    await cb.answer()
    aid  = int(cb.data.split(":")[1])
    data = await state.get_data()
    items = data.get('ar_items', [])
    if not items:
        await cb.answer()
        return
    await state.set_state(ARState.match)
    cid = data['chat_id']; mid = data['msg_id']
    trig_str = data.get('ar_trig_display', '')
    import json as _j
    _, summary, count = _draft_summary(_j.dumps(items))
    try:
        await cb.bot.edit_message_text(
            f"➕ <b>новое правило</b>  ·  шаг 3/3\n\n"
            f"триггер(ы): <code>{trig_str[:200]}</code>\n"
            f"сообщений: <b>{count}</b>\n\n"
            f"<blockquote expandable>{summary[:300]}</blockquote>\n\n"
            f"тип совпадения триггера:",
            chat_id=cid, message_id=mid,
            reply_markup=kb(
                [b("📝 содержит", "ar_m:contains"), b("🎯 точное", "ar_m:exact")],
                [b("⬆️ начинается с", "ar_m:startswith")],
                [b("отмена", f"ar:{aid}:menu")]
            ), parse_mode='HTML'
        )
    except: pass

@router.callback_query(F.data.startswith("ar_m:"), ARState.match)
async def ar_match(cb: CallbackQuery, state: FSMContext):
    import json as _j
    mt   = cb.data.split(":")[1]
    data = await state.get_data()
    aid  = data['aid']
    trig_db  = data.get('ar_trig', '')
    items    = data.get('ar_items', [])
    content_json = _j.dumps(items, ensure_ascii=False) if items else ''
    await db_run(
        "INSERT INTO autoreply_rules(account_id,trig,trigger_text,response,response_text,match_type,format_mode,content_json,buttons_json)"
        " VALUES(?,?,?,?,?,?,?,?,?)",
        (aid, trig_db, trig_db, '', '', mt, 'html', content_json, '')
    )
    await state.clear()
    await cb.answer()
    mt_labels = {'contains': 'содержит', 'exact': 'точное', 'startswith': 'начинается с'}
    trig_display = data.get('ar_trig_display', trig_db)
    _, summary, count = _draft_summary(content_json) if content_json else ('', '?', 0)
    try:
        await cb.message.edit_text(
            f"✅ <b>правило добавлено</b>\n\n"
            f"триггер(ы): <code>{trig_display[:200]}</code>  ·  <b>{mt_labels.get(mt, mt)}</b>\n"
            f"сообщений: <b>{count}</b>",
            reply_markup=kb([b("📋 правила", f"ar:{aid}:list:0")], [b("‹ назад", f"ar:{aid}:menu")]),
            parse_mode='HTML'
        )
    except: pass

# ══════════════════════════════════════
# АВТОУДАЛЕНИЕ
# ══════════════════════════════════════
# ══════════════════════════════════════
# 🗑 МАССОВОЕ УДАЛЕНИЕ СВОИХ СООБЩЕНИЙ
#    (выбор чата через слайдер)
# ══════════════════════════════════════
@router.callback_query(F.data.startswith("massdel:"))
async def cb_massdel(cb: CallbackQuery):
    parts  = cb.data.split(":")
    aid    = int(parts[1])
    action = parts[2] if len(parts) > 2 else "menu"
    acc    = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return

    if action == "menu":
        await edit(cb,
            "🗑 <b>удалить мои сообщения</b>\n\n"
            "выбери тип чата и нажми на нужный чат\n"
            "⚠️ действие необратимо!",
            kb(
                [b("💬 все чаты",  f"massdel:{aid}:browse:all:0")],
                [b("👤 личные",    f"massdel:{aid}:browse:private:0"),
                 b("🤖 боты",      f"massdel:{aid}:browse:bot:0")],
                [b("👥 группы",    f"massdel:{aid}:browse:group:0"),
                 b("📢 каналы",    f"massdel:{aid}:browse:channel:0")],
                [b("‹ назад",      f"s_auto_actions:{aid}")]
            )
        )

    elif action == "browse":
        ftype = parts[3] if len(parts) > 3 else "all"
        page  = int(parts[4]) if len(parts) > 4 else 0
        stop  = asyncio.Event()
        asyncio.create_task(animate_loading(cb.bot, cb.message.chat.id, cb.message.message_id,
                                            f"🗑 <b>загружаю список чатов</b>", stop))
        await cb.answer()
        dialogs = await cm.get_dialogs_by_type(aid, ftype)
        stop.set()
        if not dialogs:
            await edit(cb, f"🗑 нет чатов типа «{ftype}»",
                       kb([b("‹ назад", f"massdel:{aid}:menu")])); return
        chunk, page, pages = paginate(dialogs, page, 8)
        lines = [f"🗑 <b>выберите чат</b>  ·  тип: {ftype}  ·  {len(dialogs)} шт\n"]
        rows  = []
        for d in chunk:
            ic   = _CHAT_TYPE_ICONS.get(d['type'], '💬')
            name = d['name'][:25]
            rows.append([b(f"{ic} {name}", f"massdel:{aid}:confirm:{d['id']}")])
        if pages > 1: rows.append(nav(page, pages, f"massdel:{aid}:browse:{ftype}"))
        rows.append([b("‹ к фильтрам", f"massdel:{aid}:menu")])
        await edit(cb, "\n".join(lines), kb(*rows))

    elif action == "confirm":
        chat_id = int(parts[3])
        c = cm.get(aid)
        chat_name = str(chat_id)
        if c:
            try:
                entity = await c.get_entity(chat_id)
                chat_name = getattr(entity, 'title', None) or getattr(entity, 'first_name', '') or str(chat_id)
            except: pass
        await edit(cb,
            f"🗑 <b>удалить мои сообщения?</b>\n\n"
            f"чат: <b>{chat_name}</b>\n"
            f"id: <code>{chat_id}</code>\n\n"
            f"⚠️ удалятся ВСЕ твои сообщения в этом чате!\n"
            f"действие необратимо!",
            kb(
                [b("🗑 да, удалить всё", f"massdel:{aid}:go:{chat_id}")],
                [b("отмена", f"massdel:{aid}:menu")]
            )
        )

    elif action == "go":
        chat_id = int(parts[3])
        mid = cb.message.message_id
        cid = cb.message.chat.id

        await cb.bot.edit_message_text(
            "🗑 <b>считаю сообщения</b>...",
            chat_id=cid, message_id=mid, parse_mode='HTML'
        )
        await cb.answer()

        last_edit = [0]

        async def progress(deleted, total):
            now = time.time()
            if now - last_edit[0] < 2 and deleted < total: return  # не чаще раз в 2 сек
            last_edit[0] = now
            bar  = make_progress_bar(deleted, total)
            try:
                await cb.bot.edit_message_text(
                    f"🗑 <b>удаляю сообщения</b>\n\n"
                    f"{bar}\n"
                    f"удалено <b>{deleted}</b> из <b>{total}</b>",
                    chat_id=cid, message_id=mid, parse_mode='HTML'
                )
            except: pass

        n = await cm.mass_delete_my_msgs(aid, chat_id, progress)
        if n == -1:
            try:
                await cb.bot.edit_message_text(
                    "❌ чат не найден или аккаунт не активен",
                    chat_id=cid, message_id=mid,
                    reply_markup=kb([b("‹ назад", f"massdel:{aid}:menu")]),
                    parse_mode='HTML'
                )
            except: pass
        else:
            try:
                await cb.bot.edit_message_text(
                    f"✅ <b>готово!</b>\n\n"
                    f"удалено <b>{n}</b> сообщений",
                    chat_id=cid, message_id=mid,
                    reply_markup=kb(
                        [b("🗑 ещё чат", f"massdel:{aid}:menu")],
                        [b("‹ назад",    f"s_auto_actions:{aid}")]
                    ),
                    parse_mode='HTML'
                )
            except: pass

# ══════════════════════════════════════
# 📢 РАССЫЛКА
# ══════════════════════════════════════
@router.callback_query(F.data.startswith("broadcast:"))
async def cb_broadcast(cb: CallbackQuery, state: FSMContext):
    parts  = cb.data.split(":")
    aid    = int(parts[1])
    action = parts[2] if len(parts) > 2 else "menu"
    acc    = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return

    if action == "menu":
        # Последние рассылки
        logs = await db_all(
            "SELECT * FROM broadcast_log WHERE account_id=? ORDER BY created_at DESC LIMIT 3", (aid,)
        )
        lines = ["📢 <b>рассылка</b>\n\nотправь сообщение по списку получателей\n"
                 "⚡️ задержка 5–15 сек между сообщениями (защита от бана)\n"]
        if logs:
            lines.append("\n<b>последние рассылки:</b>")
            for l in logs:
                lines.append(f"  📤 {l['sent']}/{l['total']} · {(l['created_at'] or '')[:16]}")
        is_running = cm._broadcasts.get(aid, {}).get('running', False)
        rows = []
        if is_running:
            rows.append([b("⏹ остановить рассылку", f"broadcast:{aid}:stop")])
        else:
            rows.append([b("➕ новая рассылка", f"broadcast:{aid}:start")])
        rows.append([b("‹ назад", f"s_auto_actions:{aid}")])
        await edit(cb, "\n".join(lines), kb(*rows))

    elif action == "start":
        await state.set_state(BroadcastState.content)
        await state.update_data(aid=aid, msg_id=cb.message.message_id,
                                chat_id=cb.message.chat.id, bcast_items=[])
        await edit(cb,
            "📢 <b>новая рассылка</b>  ·  шаг 1/2\n\n"
            "✉️ отправь сообщения для рассылки\n\n"
            "когда добавишь всё — нажми <b>готово</b>",
            kb([b("✅ готово", f"broadcast:{aid}:done")],
               [b("отмена", f"broadcast:{aid}:menu")])
        )

    elif action == "done":
        data_d = await state.get_data()
        items  = data_d.get('bcast_items', [])
        if not items:
            await cb.answer(); return
        mid_d = data_d.get('msg_id'); cid_d = data_d.get('chat_id')
        await state.set_state(BroadcastState.usernames)
        cnt_label = f"{len(items)} сообщ" if len(items) > 1 else "1 сообщение"
        try:
            await cb.bot.edit_message_text(
                f"📢 <b>новая рассылка</b>  ·  шаг 2/2\n\n"
                f"контент: <b>{cnt_label}</b>\n\n"
                f"📋 введите список получателей:\n"
                f"• по одному @username в строку, или через запятую\n"
                f"• максимум 100 получателей\n\n"
                f"пример:\n<code>@user1\n@user2</code>",
                chat_id=cid_d, message_id=mid_d,
                reply_markup=kb([b("отмена", f"broadcast:{aid}:menu")]),
                parse_mode='HTML'
            )
        except Exception: pass

    elif action == "stop":
        cm.stop_broadcast(aid)
        await cb.answer()
        cb.data = f"broadcast:{aid}:menu"
        await cb_broadcast(cb, state)

@router.message(BroadcastState.content)
async def broadcast_content_input(msg: Message, state: FSMContext):
    """Накапливаем сообщения для рассылки (аналог DraftAdd.content)."""
    await delete_user_msg(msg)
    data  = await state.get_data()
    aid   = data['aid']; mid = data['msg_id']; cid = data['chat_id']
    items = data.get('bcast_items', [])

    item = _msg_to_content(msg)
    if not item:
        try:
            await msg.bot.edit_message_text(
                "❌ тип контента не поддерживается\n\nОтправь текст, фото, видео, ГС, кружок, стикер, GIF или файл",
                chat_id=cid, message_id=mid,
                reply_markup=kb([b("✅ готово", f"broadcast:{aid}:done")],
                                [b("отмена", f"broadcast:{aid}:menu")]),
                parse_mode='HTML'
            )
        except: pass
        return

    items.append(item)
    await state.update_data(bcast_items=items)
    import json as _jb
    count = len(items)
    t   = item.get('type', '?')
    ic  = _DRAFT_ICONS.get(t, '📄')
    lbl = _DRAFT_LABELS.get(t) or t
    _, summary, _ = _draft_summary(_jb.dumps(items, ensure_ascii=False))
    try:
        await msg.bot.edit_message_text(
            f"📢 <b>новая рассылка</b>  ·  шаг 1/2\n\n"
            f"добавлено: <b>{count}</b>  ·  последнее: {ic} {lbl}\n\n"
            f"<blockquote expandable>{summary[:400]}</blockquote>\n\n"
            f"можешь добавить ещё или нажми <b>готово</b>",
            chat_id=cid, message_id=mid,
            reply_markup=kb([b(f"✅ готово ({count})", f"broadcast:{aid}:done")],
                            [b("отмена", f"broadcast:{aid}:menu")]),
            parse_mode='HTML'
        )
    except: pass

@router.message(BroadcastState.usernames)
async def broadcast_usernames_input(msg: Message, state: FSMContext):
    await delete_user_msg(msg)
    data = await state.get_data()
    aid  = data['aid']; mid = data['msg_id']; cid = data['chat_id']
    text = (msg.text or '').strip()

    async def upd(t, markup=kb()):
        try: await msg.bot.edit_message_text(t, chat_id=cid, message_id=mid,
                                              reply_markup=markup, parse_mode='HTML')
        except: pass

    # Парсим список username (через запятую или перенос строки)
    raw = re.split(r'[,\n\s]+', text)
    usernames = [u.strip().lstrip('@') for u in raw if u.strip()]
    usernames = [u for u in usernames if u][:100]  # максимум 100

    if not usernames:
        await upd("❌ не найдено ни одного username", kb([b("отмена", f"broadcast:{aid}:menu")])); return

    items = data.get('bcast_items', [])
    await state.clear()

    cnt_lbl = f"{len(items)} сообщ" if len(items) > 1 else "1 сообщение"
    await upd(
        f"📢 <b>подтвердите рассылку</b>\n\n"
        f"получателей: <b>{len(usernames)}</b>\n"
        f"контент: <b>{cnt_lbl}</b>\n\n"
        f"⚡️ задержка 5–15 сек между отправками\n"
        f"примерное время: <b>{len(usernames) * 10 // 60}–{len(usernames) * 20 // 60} мин</b>",
        kb(
            [b("📤 запустить рассылку", f"broadcast_go:{aid}")],
            [b("отмена", f"broadcast:{aid}:menu")]
        )
    )
    # Временно храним в CM
    cm._broadcasts[f"pending_{aid}"] = {
        'usernames': usernames,
        'items':     items,
        'mid':       mid,
        'cid':       cid,
    }

@router.callback_query(F.data.startswith("broadcast_go:"))
async def cb_broadcast_go(cb: CallbackQuery):
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return

    pending = cm._broadcasts.pop(f"pending_{aid}", None)
    if not pending:
        await cb.answer(); return

    usernames = pending['usernames']
    items     = pending['items']
    mid       = pending['mid']
    cid       = pending['cid']

    await cb.bot.edit_message_text(
        f"📢 <b>рассылка запущена</b>\n\nполучателей: <b>{len(usernames)}</b>\n⏳ отправляю...",
        chat_id=cid, message_id=mid, parse_mode='HTML'
    )
    await cb.answer()

    last_edit = [0]

    async def progress(i, total, sent, failed, status=""):
        now = time.time()
        if now - last_edit[0] < 2 and i < total: return
        last_edit[0] = now
        bar = make_progress_bar(sent + failed, total)
        try:
            await cb.bot.edit_message_text(
                f"📢 <b>рассылка</b>\n\n"
                f"{bar}\n"
                f"отправлено: <b>{sent}</b>  |  ошибок: <b>{failed}</b>  |  всего: <b>{total}</b>"
                f"{chr(10) + status if status else ''}",
                chat_id=cid, message_id=mid,
                reply_markup=kb([b("⏹ остановить", f"broadcast:{aid}:stop")]),
                parse_mode='HTML'
            )
        except: pass

    result = await cm.broadcast(aid, cb.from_user.id, usernames, items, progress)

    err_text = ""
    if result['errors']:
        err_preview = "\n".join(result['errors'][:5])
        err_text = f"\n\n⚠️ ошибки:\n<blockquote>{err_preview}</blockquote>"
        if len(result['errors']) > 5:
            err_text += f"\n  …и ещё {len(result['errors'])-5}"

    try:
        await cb.bot.edit_message_text(
            f"✅ <b>рассылка завершена</b>\n\n"
            f"📤 отправлено: <b>{result['sent']}</b>\n"
            f"❌ не доставлено: <b>{result['failed']}</b>\n"
            f"📋 всего: <b>{result['total']}</b>"
            f"{err_text}",
            chat_id=cid, message_id=mid,
            reply_markup=kb([b("📢 новая рассылка", f"broadcast:{aid}:start"),
                             b("‹ назад", f"s_auto_actions:{aid}")]),
            parse_mode='HTML'
        )
    except: pass

# ══════════════════════════════════════
# КЛЮЧЕВЫЕ СЛОВА
# ══════════════════════════════════════
@router.callback_query(F.data.startswith("kw:"))
async def cb_kw(cb: CallbackQuery, state: FSMContext):
    parts  = cb.data.split(":")
    aid    = int(parts[1])
    action = parts[2] if len(parts) > 2 else "list"
    acc    = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return

    if action == "list":
        kws = await db_all("SELECT * FROM keyword_alerts WHERE account_id=? ORDER BY id", (aid,))
        if not kws:
            await edit(cb,
                "🔔 <b>ключевые слова</b>\n\nдобавь слова — получай уведомление когда их напишут",
                kb([b("➕ добавить", f"kw:{aid}:add")], [b("‹ назад", f"s_auto_monitor:{aid}")])
            ); return
        lines = [f"🔔 <b>ключевые слова</b>  ·  {len(kws)} шт\n"]
        rows  = []
        for kw in kws:
            st = "✅" if kw['active'] else "☐"
            lines.append(f"{st} <code>{kw['keyword']}</code>")
            rows.append([
                b(f"{'⏸' if kw['active'] else '▶️'} {kw['keyword']}", f"kw:{aid}:tog:{kw['id']}"),
                b("🗑", f"kw:{aid}:del:{kw['id']}")
            ])
        rows.append([b("➕ добавить", f"kw:{aid}:add"), b("‹ назад", f"s_auto_monitor:{aid}")])
        await edit(cb, "\n".join(lines), kb(*rows))
    elif action == "add":
        await state.set_state(KWAdd.keyword)
        await state.update_data(aid=aid, msg_id=cb.message.message_id, chat_id=cb.message.chat.id)
        await edit(cb, "🔔 <b>новое ключевое слово</b>\n\nnапиши слово или фразу:", kb([b("отмена", f"kw:{aid}:list")]))
    elif action == "tog":
        kid = int(parts[3])
        kw  = await db_get("SELECT * FROM keyword_alerts WHERE id=? AND account_id=?", (kid, aid))
        if kw: await db_run("UPDATE keyword_alerts SET active=? WHERE id=?", (0 if kw['active'] else 1, kid))
        await cb.answer()
        cb.data = f"kw:{aid}:list"
        await cb_kw(cb, state)
    elif action == "del":
        kid = int(parts[3])
        await db_run("DELETE FROM keyword_alerts WHERE id=? AND account_id=?", (kid, aid))
        await cb.answer()
        cb.data = f"kw:{aid}:list"
        await cb_kw(cb, state)

@router.message(KWAdd.keyword)
async def kw_add_msg(msg: Message, state: FSMContext):
    await delete_user_msg(msg)
    data = await state.get_data()
    aid, mid, cid = data['aid'], data['msg_id'], data['chat_id']
    kw = (msg.text or '').strip()
    async def upd(text, markup):
        try: await msg.bot.edit_message_text(text, chat_id=cid, message_id=mid,
                                              reply_markup=markup, parse_mode='HTML')
        except: pass
    if not kw or len(kw) > 50:
        await upd("❌ слово не должно быть пустым или длиннее 50 символов",
                  kb([b("отмена", f"kw:{aid}:list")])); return
    await db_run("INSERT INTO keyword_alerts(account_id,keyword,active) VALUES(?,?,1)", (aid, kw))
    await state.clear()
    await upd(f"✅ добавлено: <code>{kw}</code>",
              kb([b("➕ ещё", f"kw:{aid}:add"), b("📋 список", f"kw:{aid}:list")]))

# ══════════════════════════════════════
# ТРЕКЕР ОНЛАЙНА
# ══════════════════════════════════════
@router.callback_query(F.data.startswith("ot:"))
async def cb_ot(cb: CallbackQuery, state: FSMContext):
    parts  = cb.data.split(":")
    aid    = int(parts[1])
    action = parts[2] if len(parts) > 2 else "list"
    acc    = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return

    if action == "list":
        tracked = await db_all("SELECT * FROM online_tracker WHERE account_id=? ORDER BY peer_name", (aid,))
        if not tracked:
            await edit(cb,
                "👁 <b>трекер онлайна</b>\n\nдобавь пользователей — получай уведомления о статусе",
                kb([b("➕ добавить", f"ot:{aid}:add")], [b("‹ назад", f"s_auto_monitor:{aid}")])
            ); return
        lines = [f"👁 <b>трекер онлайна</b>  ·  {len(tracked)} чел\n"]
        rows  = []
        for t in tracked:
            tag = f"@{t['peer_user']}" if t['peer_user'] else f"id:{t['peer_id']}"
            ls  = f"  · {t['last_seen']}" if t['last_seen'] else ""
            lines.append(f"👤 <b>{t['peer_name'] or '?'}</b>  <code>{tag}</code>{ls}")
            rows.append([b(f"🗑 {(t['peer_name'] or tag)[:20]}", f"ot:{aid}:del:{t['id']}")])
        rows.append([b("➕ добавить", f"ot:{aid}:add"), b("‹ назад", f"s_auto_monitor:{aid}")])
        await edit(cb, "\n".join(lines), kb(*rows))
    elif action == "add":
        await state.set_state(OTAdd.username)
        await state.update_data(aid=aid, msg_id=cb.message.message_id, chat_id=cb.message.chat.id)
        await edit(cb, "👁 <b>добавить в трекер</b>\n\nнапиши @username:", kb([b("отмена", f"ot:{aid}:list")]))
    elif action == "del":
        tid = int(parts[3])
        await db_run("DELETE FROM online_tracker WHERE id=? AND account_id=?", (tid, aid))
        await cb.answer()
        cb.data = f"ot:{aid}:list"
        await cb_ot(cb, state)

@router.message(OTAdd.username)
async def ot_add_msg(msg: Message, state: FSMContext):
    await delete_user_msg(msg)
    data  = await state.get_data()
    aid, mid, cid = data['aid'], data['msg_id'], data['chat_id']
    uname = (msg.text or '').strip().lstrip('@')
    async def upd(text, markup):
        try: await msg.bot.edit_message_text(text, chat_id=cid, message_id=mid,
                                              reply_markup=markup, parse_mode='HTML')
        except: pass
    if not uname: await upd("❌ введи @username", kb([b("отмена", f"ot:{aid}:list")])); return
    c = cm.get(aid)
    if not c: await upd("❌ аккаунт не активен", kb([b("‹ назад", f"ot:{aid}:list")])); return
    try:
        entity = await c.get_entity(uname)
        pid    = entity.id
        pname  = getattr(entity, 'first_name', '') or uname
        pusr   = getattr(entity, 'username', '') or uname
        await db_run(
            "INSERT OR IGNORE INTO online_tracker(account_id,peer_id,peer_name,peer_user) VALUES(?,?,?,?)",
            (aid, pid, pname, pusr)
        )
        await state.clear()
        await upd(f"✅ <b>{pname}</b> добавлен в трекер",
                  kb([b("➕ ещё", f"ot:{aid}:add"), b("📋 список", f"ot:{aid}:list")]))
    except Exception as e:
        await upd(f"❌ не найден: <code>{e}</code>", kb([b("отмена", f"ot:{aid}:list")]))

# ══════════════════════════════════════
# ВЫХОД ИЗ АККАУНТА
# ══════════════════════════════════════
@router.callback_query(F.data.startswith("rm:"))
async def cb_rm(cb: CallbackQuery):
    parts = cb.data.split(":")
    if parts[1] == "ok":
        aid = int(parts[2])
        acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
        if not acc: return
        await cm.stop(aid)
        await db_run("UPDATE accounts SET active=0 WHERE id=?", (aid,))
        await edit(cb,
            f"✅ выход из <code>{acc['phone']}</code>",
            kb([b("‹ аккаунты", "accs:0"), b("🏠 главная", "main")])
        ); return
    aid = int(parts[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: await cb.answer(); return
    await edit(cb,
        f"🚪 <b>выйти из аккаунта?</b>\n\n📱 <code>{acc['phone']}</code>\n\nданные сохранятся",
        kb([b("✅ да, выйти", f"rm:ok:{aid}"), b("отмена", f"acc:{aid}")])
    )

# ══════════════════════════════════════
# ФОНОВЫЕ ЗАДАЧИ
# ══════════════════════════════════════
async def bg_online_watchdog():
    while True:
        await asyncio.sleep(120)
        for acc in await db_all("SELECT * FROM accounts WHERE active=1 AND always_online=1"):
            aid = acc['id']
            c   = cm.clients.get(aid)
            if c and not c.is_connected():
                try: await c.connect()
                except Exception as e: log.warning(f"watchdog reconnect {aid}: {e}")

async def bg_online_tracker():
    """Обновляет last_seen в БД — уведомления НЕ отправляются, статус виден в списке."""
    while True:
        await asyncio.sleep(180)
        try:
            rows = await db_all("SELECT * FROM online_tracker")
            for t in rows:
                aid = t['account_id']
                c   = cm.get(aid)
                if not c: continue
                try:
                    entity    = await c.get_entity(t['peer_id'])
                    status    = getattr(entity, 'status', None)
                    is_online = isinstance(status, UserStatusOnline)
                    key       = (aid, t['peer_id'])
                    was_online = cm._online_status.get(key)
                    cm._online_status[key] = is_online
                    now_str = datetime.now(timezone.utc).strftime('%H:%M')
                    if is_online and not was_online:
                        await db_run("UPDATE online_tracker SET last_seen=? WHERE id=?",
                                     (f"🟢 онлайн {now_str}", t['id']))
                    elif not is_online and was_online:
                        await db_run("UPDATE online_tracker SET last_seen=? WHERE id=?",
                                     (f"⚫️ офлайн {now_str}", t['id']))
                except: pass
        except: pass


# ══════════════════════════════════════
# 📝 ЧЕРНОВИКИ
# ══════════════════════════════════════
@router.message(ARSchedule.value)
async def ar_schedule_input(msg: Message, state: FSMContext):
    await delete_user_msg(msg)
    data = await state.get_data()
    aid  = data['aid']; mid = data['msg_id']; cid = data['chat_id']

    # Случай: установка расписания автоответа
    rid  = data.get('rid')
    text = (msg.text or '').strip()
    await state.clear()
    if text == '-':
        await db_run("UPDATE autoreply_rules SET schedule_start='', schedule_end='' WHERE id=? AND account_id=?",
                     (rid, aid))
        ss, se = '', ''
    else:
        try:
            parts = text.replace(' ', '').split('-')
            ss, se = parts[0].strip(), parts[1].strip()
            # validate HH:MM
            for t in (ss, se):
                h, m = map(int, t.split(':'))
                assert 0 <= h <= 23 and 0 <= m <= 59
            await db_run(
                "UPDATE autoreply_rules SET schedule_start=?, schedule_end=? WHERE id=? AND account_id=?",
                (ss, se, rid, aid)
            )
        except:
            try:
                await msg.bot.edit_message_text(
                    "❌ неверный формат. пример: <code>09:00-23:00</code>",
                    chat_id=cid, message_id=mid,
                    reply_markup=kb([b("отмена", f"ar:{aid}:list:0")]), parse_mode='HTML'
                )
            except: pass
            return
    sch_txt = f"{ss}–{se}" if ss else "убрано"
    try:
        await msg.bot.edit_message_text(
            f"✅ расписание: <b>{sch_txt}</b>",
            chat_id=cid, message_id=mid,
            reply_markup=kb([b("‹ к правилам", f"ar:{aid}:list:0")]), parse_mode='HTML'
        )
    except: pass


# ══════════════════════════════════════
# 📝 ЧЕРНОВИКИ
# ══════════════════════════════════════
_DRAFT_ICONS = {
    'text': '✏️', 'photo': '🖼', 'video': '📹', 'voice': '🎙',
    'video_note': '🎥', 'sticker': '😊', 'audio': '🎵',
    'document': '📎', 'animation': '🎞', 'album': '🗂',
}
_DRAFT_LABELS = {
    'text':       None,           # текст показываем напрямую
    'photo':      '[фото]',
    'video':      '[видео]',
    'voice':      '[голосовое]',
    'video_note': '[кружок]',
    'sticker':    '[стикер]',
    'audio':      '[аудио]',
    'document':   '[файл]',
    'animation':  '[гиф]',
    'album':      '[альбом]',
}
_DRAFT_PAGE = 4   # черновиков на страницу


def _draft_summary(content_json_str: str) -> tuple:
    """Возвращает (icon_str, html_preview_str, count) для черновика.
    Формат: • строка на каждый элемент, без пустых строк между ними."""
    import json as _j
    try:
        raw = _j.loads(content_json_str)
        items = raw if isinstance(raw, list) else [raw]
    except Exception:
        return '📄', '', 1
    count = len(items)
    parts = []
    for it in items:
        line = _content_item_html(it)
        parts.append(f"• {line[:300]}" if line else "• (пусто)")
    icon = _DRAFT_ICONS.get(items[0].get('type', ''), '📄') if items else '📄'
    return icon, '\n'.join(parts), count


def _msg_to_content(msg: Message) -> dict:
    """Конвертирует aiogram Message в content-dict для хранения в БД."""
    ents = _serialize_entities(msg)
    if msg.text:
        return {'type': 'text', 'text': msg.text, 'entities': ents,
                'html': msg.html_text or msg.text}
    if msg.photo:
        cap_html = msg.html_text if msg.caption else ''
        return {'type': 'photo', 'file_id': msg.photo[-1].file_id,
                'caption': msg.caption or '', 'entities': ents, 'filename': 'photo.jpg',
                'html': cap_html}
    if msg.video:
        cap_html = msg.html_text if msg.caption else ''
        return {'type': 'video', 'file_id': msg.video.file_id,
                'caption': msg.caption or '', 'entities': ents, 'filename': 'video.mp4',
                'html': cap_html}
    if msg.video_note:
        return {'type': 'video_note', 'file_id': msg.video_note.file_id, 'filename': 'vnote.mp4'}
    if msg.voice:
        return {'type': 'voice', 'file_id': msg.voice.file_id,
                'caption': msg.caption or '', 'filename': 'voice.ogg'}
    if msg.audio:
        return {'type': 'audio', 'file_id': msg.audio.file_id,
                'caption': msg.caption or '', 'entities': ents,
                'filename': msg.audio.file_name or 'audio.mp3'}
    if msg.sticker:
        return {'type': 'sticker', 'file_id': msg.sticker.file_id, 'filename': 'sticker.webp'}
    if msg.animation:
        return {'type': 'animation', 'file_id': msg.animation.file_id,
                'caption': msg.caption or '', 'entities': ents, 'filename': 'anim.gif'}
    if msg.document:
        return {'type': 'document', 'file_id': msg.document.file_id,
                'caption': msg.caption or '', 'entities': ents,
                'filename': msg.document.file_name or 'file'}
    return {}


async def _drafts_list(cb_or_bot, chat_id: int, msg_id: int,
                       aid: int, page: int, state: FSMContext):
    """Отрисовывает список черновиков со слайдером (4 на страницу)."""
    import json as _j
    items = await db_all(
        "SELECT * FROM drafts WHERE account_id=? ORDER BY id DESC", (aid,)
    )
    total = len(items)

    send = cb_or_bot.edit_message_text if hasattr(cb_or_bot, 'edit_message_text') else None
    bot  = cb_or_bot if send else None

    async def _edit(text, markup):
        try:
            if send:
                await send(text, chat_id=chat_id, message_id=msg_id,
                           reply_markup=markup, parse_mode='HTML')
            else:
                await bot.edit_message_text(text, chat_id=chat_id, message_id=msg_id,
                                            reply_markup=markup, parse_mode='HTML')
        except Exception:
            pass

    if not items:
        await _edit(
            "📝 <b>черновики</b>\n\nпусто\n\nзадайте триггер — при его отправке "
            "сообщение автоматически заменится на черновик",
            kb([b("➕ добавить", f"drafts:{aid}:add"), b("‹ назад", f"s_auto_replies:{aid}")])
        )
        return

    pages = max(1, (total + _DRAFT_PAGE - 1) // _DRAFT_PAGE)
    page  = max(0, min(page, pages - 1))
    chunk = items[page * _DRAFT_PAGE: (page + 1) * _DRAFT_PAGE]

    lines = [f"📝 <b>черновики</b>  ·  {total} шт  ·  стр {page+1}/{pages}\n"]
    btn_rows = []

    for d in chunk:
        icon, summary, count = _draft_summary(d['content'])
        trig = d['trigger_text'][:25]
        cnt_label = f"  ·  {count} сообщ" if count > 1 else ""
        is_on = d.get('active', 1)
        status = "✅" if is_on else "❌"
        lines.append(f"{status} {icon} <code>{trig}</code>{cnt_label}")
        btn_rows.append([b(f"{icon} {trig}{cnt_label}", f"drafts:{aid}:view:{d['id']}:{page}")])

    # слайдер
    if pages > 1:
        nav_btns = []
        if page > 0:
            nav_btns.append(b("◀", f"drafts:{aid}:list:{page-1}"))
        nav_btns.append(b(f"  {page+1} / {pages}  ", f"drafts:{aid}:noop"))
        if page < pages - 1:
            nav_btns.append(b("▶", f"drafts:{aid}:list:{page+1}"))
        btn_rows.append(nav_btns)

    btn_rows.append([b("➕ добавить", f"drafts:{aid}:add"), b("‹ назад", f"s_auto_replies:{aid}")])
    await _edit("\n".join(lines), kb(*btn_rows))


@router.callback_query(F.data.startswith("drafts:"))
async def cb_drafts(cb: CallbackQuery, state: FSMContext):
    await cb.answer()
    parts  = cb.data.split(":")
    aid    = int(parts[1])
    action = parts[2] if len(parts) > 2 else "list"

    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: return

    cid = cb.message.chat.id
    mid = cb.message.message_id

    # ── список ──────────────────────────────────────────────────────
    if action == "list":
        page = int(parts[3]) if len(parts) > 3 else 0
        await _drafts_list(cb.bot, cid, mid, aid, page, state)

    # ── noop (кнопка "страница N/M") ─────────────────────────────────
    elif action == "noop":
        pass

    # ── добавить ────────────────────────────────────────────────────
    elif action == "add":
        await state.set_state(DraftAdd.trigger)
        await state.update_data(aid=aid, msg_id=mid, chat_id=cid, draft_items=[])
        try:
            await cb.bot.edit_message_text(
                "📝 <b>новый черновик</b>  ·  шаг 1/2\n\nвведите триггер-слово:",
                chat_id=cid, message_id=mid,
                reply_markup=kb([b("отмена", f"drafts:{aid}:list:0")]),
                parse_mode='HTML'
            )
        except Exception: pass

    # ── просмотр черновика ───────────────────────────────────────────
    elif action == "view":
        did      = int(parts[3])
        back_pg  = int(parts[4]) if len(parts) > 4 else 0
        d = await db_get("SELECT * FROM drafts WHERE id=? AND account_id=?", (did, aid))
        if not d:
            await _drafts_list(cb.bot, cid, mid, aid, back_pg, state); return

        icon, summary, count = _draft_summary(d['content'])
        trig = d['trigger_text']
        is_on = d.get('active', 1)
        status = "вкл ✅" if is_on else "выкл ❌"
        cnt_label = f"\nсообщений: <b>{count}</b>" if count > 1 else ""
        text = (
            f"📝 <b>черновик</b>  <code>{trig}</code>\n\n"
            f"статус: {status}{cnt_label}\n\n"
            f"<blockquote expandable>{summary[:600] or '(нет превью)'}</blockquote>"
        )
        tog_lbl = "🔕 выключить" if is_on else "🔔 включить"
        try:
            await cb.bot.edit_message_text(
                text, chat_id=cid, message_id=mid,
                reply_markup=kb(
                    [b(tog_lbl, f"drafts:{aid}:tog:{did}:{back_pg}")],
                    [b("🗑 удалить", f"drafts:{aid}:del:{did}:{back_pg}")],
                    [b("‹ к списку", f"drafts:{aid}:list:{back_pg}")]
                ),
                parse_mode='HTML'
            )
        except Exception: pass

    # ── вкл/выкл ────────────────────────────────────────────────────
    elif action == "tog":
        did     = int(parts[3])
        back_pg = int(parts[4]) if len(parts) > 4 else 0
        d = await db_get("SELECT * FROM drafts WHERE id=? AND account_id=?", (did, aid))
        if not d:
            await _drafts_list(cb.bot, cid, mid, aid, back_pg, state)
            return
        new_val = 0 if d.get('active', 1) else 1
        await db_run("UPDATE drafts SET active=? WHERE id=? AND account_id=?", (new_val, did, aid))
        # сразу перерисовываем карточку с новым состоянием
        icon, summary, count = _draft_summary(d['content'])
        trig    = d['trigger_text']
        is_on   = bool(new_val)
        status  = "вкл ✅" if is_on else "выкл ❌"
        cnt_lbl = f"\nсообщений: <b>{count}</b>" if count > 1 else ""
        tog_lbl = "🔕 выключить" if is_on else "🔔 включить"
        text = (
            f"📝 <b>черновик</b>  <code>{trig}</code>\n\n"
            f"статус: {status}{cnt_lbl}\n\n"
            f"<blockquote expandable>{summary[:600] or '(нет превью)'}</blockquote>"
        )
        try:
            await cb.bot.edit_message_text(
                text, chat_id=cid, message_id=mid,
                reply_markup=kb(
                    [b(tog_lbl, f"drafts:{aid}:tog:{did}:{back_pg}")],
                    [b("🗑 удалить", f"drafts:{aid}:del:{did}:{back_pg}")],
                    [b("‹ к списку", f"drafts:{aid}:list:{back_pg}")]
                ),
                parse_mode='HTML'
            )
        except Exception: pass

    # ── удалить ─────────────────────────────────────────────────────
    elif action == "del":
        did     = int(parts[3])
        back_pg = int(parts[4]) if len(parts) > 4 else 0
        await db_run("DELETE FROM drafts WHERE id=? AND account_id=?", (did, aid))
        await _drafts_list(cb.bot, cid, mid, aid, back_pg, state)

    # ── подтвердить сохранение (кнопка «готово») ─────────────────────
    elif action == "done":
        data   = await state.get_data()
        items  = data.get('draft_items', [])
        trig   = data.get('draft_trigger', '')
        if not items or not trig:
            await state.clear()
            await _drafts_list(cb.bot, cid, mid, aid, 0, state)
            return
        import json as _j
        await db_run(
            "INSERT INTO drafts(account_id, trigger_text, content) VALUES(?,?,?)",
            (aid, trig, _j.dumps(items, ensure_ascii=False))
        )
        await state.clear()
        _, summary, count = _draft_summary(_j.dumps(items, ensure_ascii=False))
        cnt_label = f"  ·  {count} сообщ" if count > 1 else ""
        try:
            await cb.bot.edit_message_text(
                f"✅ черновик <code>{trig}</code> сохранён{cnt_label}\n"
                f"<blockquote expandable>{summary[:500]}</blockquote>",
                chat_id=cid, message_id=mid,
                reply_markup=kb([b("📝 к черновикам", f"drafts:{aid}:list:0")]),
                parse_mode='HTML'
            )
        except Exception: pass

    # ── отмена сбора сообщений ───────────────────────────────────────
    elif action == "cancel_add":
        await state.clear()
        await _drafts_list(cb.bot, cid, mid, aid, 0, state)


# ── шаг 1: триггер ──────────────────────────────────────────────────
@router.message(DraftAdd.trigger)
async def draft_trigger_input(msg: Message, state: FSMContext):
    await delete_user_msg(msg)
    data = await state.get_data()
    aid = data['aid']; mid = data['msg_id']; cid = data['chat_id']
    trig = (msg.text or '').strip()
    if not trig:
        return
    await state.update_data(draft_trigger=trig, draft_items=[])
    await state.set_state(DraftAdd.content)
    try:
        await msg.bot.edit_message_text(
            f"📝 <b>новый черновик</b>  ·  шаг 2/2\n\n"
            f"триггер: <code>{trig}</code>\n\n"
            f"отправь одно или несколько сообщений — они все будут отправляться по триггеру\n"
            f"когда закончишь — нажми <b>готово</b>",
            chat_id=cid, message_id=mid,
            reply_markup=kb([
                b("✅ готово", f"drafts:{aid}:done"),
                b("отмена",   f"drafts:{aid}:cancel_add"),
            ]),
            parse_mode='HTML'
        )
    except Exception: pass


# ── шаг 2: накапливаем сообщения (с поддержкой альбомов) ────────────
@router.message(DraftAdd.content)
async def draft_content_input(msg: Message, state: FSMContext):
    await delete_user_msg(msg)
    data  = await state.get_data()
    aid   = data['aid']; mid = data['msg_id']; cid = data['chat_id']
    trig  = data.get('draft_trigger', '')
    items = data.get('draft_items', [])
    album_buf = data.get('draft_album_buf', {})  # {group_id: [items]}

    # ── Альбом ──
    group_id = msg.media_group_id
    if group_id:
        grp_key = str(group_id)
        item = _msg_to_content(msg)
        if not item:
            return
        if grp_key not in album_buf:
            album_buf[grp_key] = []
        album_buf[grp_key].append(item)
        await state.update_data(draft_album_buf=album_buf)

        # Отменяем старый таймер и ставим новый
        pending = data.get('draft_album_tasks', {})
        if grp_key in pending:
            try: pending[grp_key].cancel()
            except: pass

        async def _flush_album(gk=grp_key):
            await asyncio.sleep(1.0)
            d2 = await state.get_data()
            buf2 = d2.get('draft_album_buf', {})
            group_items = buf2.pop(gk, [])
            if not group_items:
                return
            itms2 = d2.get('draft_items', [])
            # Определяем подпись альбома: берём caption первого элемента
            cap = next((i.get('caption', '') for i in group_items if i.get('caption')), '')
            album_item = {
                'type': 'album',
                'items': group_items,
                'caption': cap,
            }
            itms2.append(album_item)
            await state.update_data(draft_items=itms2, draft_album_buf=buf2)
            _, summary, _ = __import__('json').dumps, None, None  # noqa
            import json as _j2
            _, summ, _ = _draft_summary(_j2.dumps(itms2))
            try:
                await msg.bot.edit_message_text(
                    f"📝 <b>новый черновик</b>  ·  шаг 2/2\n\n"
                    f"триггер: <code>{trig}</code>\n"
                    f"добавлено: <b>{len(itms2)}</b>  ·  последнее: 🗂 альбом ({len(group_items)} шт)\n\n"
                    f"<blockquote expandable>{summ[:400]}</blockquote>\n\n"
                    f"можешь отправить ещё или нажать <b>готово</b>",
                    chat_id=cid, message_id=mid,
                    reply_markup=kb([
                        b(f"✅ готово ({len(itms2)})", f"drafts:{aid}:done"),
                        b("отмена", f"drafts:{aid}:cancel_add"),
                    ]),
                    parse_mode='HTML'
                )
            except Exception: pass

        task = asyncio.create_task(_flush_album())
        pending[grp_key] = task
        await state.update_data(draft_album_tasks=pending)
        return

    # ── Одиночное сообщение ──
    item = _msg_to_content(msg)
    if not item:
        return

    items.append(item)
    await state.update_data(draft_items=items)

    import json as _j
    count = len(items)
    _, summary, _ = _draft_summary(_j.dumps(items))
    t   = item.get('type', '?')
    ic  = _DRAFT_ICONS.get(t, '📄')
    lbl = _DRAFT_LABELS.get(t) or t
    try:
        await msg.bot.edit_message_text(
            f"📝 <b>новый черновик</b>  ·  шаг 2/2\n\n"
            f"триггер: <code>{trig}</code>\n"
            f"добавлено: <b>{count}</b>  ·  последнее: {ic} {lbl}\n\n"
            f"<blockquote expandable>{summary[:400]}</blockquote>\n\n"
            f"можешь отправить ещё или нажать <b>готово</b>",
            chat_id=cid, message_id=mid,
            reply_markup=kb([
                b(f"✅ готово ({count})", f"drafts:{aid}:done"),
                b("отмена", f"drafts:{aid}:cancel_add"),
            ]),
            parse_mode='HTML'
        )
    except Exception: pass



# ══════════════════════════════════════
# ПОСЛЕДНИЙ КОД ОТ TELEGRAM
# ══════════════════════════════════════

# ══════════════════════════════════════
# 👥 МОИ ГРУППЫ И КАНАЛЫ
# ══════════════════════════════════════
_MYCHATS_PER_PAGE = 10

@router.callback_query(F.data.startswith("mychats:"))
async def cb_mychats(cb: CallbackQuery):
    await cb.answer()
    parts = cb.data.split(":")
    aid   = int(parts[1])
    page  = int(parts[2]) if len(parts) > 2 else 0
    acc   = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: return

    c = cm.get(aid)
    if not c:
        await edit(cb, "❌ аккаунт не активен", kb([b("‹ назад", f"s_data:{aid}")])); return

    stop = asyncio.Event()
    asyncio.create_task(animate_loading(
        cb.bot, cb.message.chat.id, cb.message.message_id,
        "👥 <b>загружаю группы и каналы</b>", stop
    ))

    chats = []
    seen_ids = set()
    try:
        # Собираем ВСЕ диалоги: обычные + архивированные, без лимита
        async def _collect(archived_flag: bool):
            async for d in c.iter_dialogs(archived=archived_flag):
                e = d.entity
                if not isinstance(e, (Channel, Chat)):
                    continue
                if e.id in seen_ids:
                    continue
                seen_ids.add(e.id)

                is_channel   = isinstance(e, Channel) and getattr(e, 'broadcast', False)
                is_megagroup = isinstance(e, Channel) and getattr(e, 'megagroup', False)
                uname   = getattr(e, 'username', '') or ''
                title   = getattr(e, 'title', '') or f"id:{e.id}"
                members = getattr(e, 'participants_count', None)

                if is_channel:
                    dtype = 'channel'
                elif is_megagroup:
                    dtype = 'megagroup'
                else:
                    dtype = 'group'

                # Публичные — прямая ссылка, приватные — invite link (только если мы админ)
                if uname:
                    link = f"https://t.me/{uname}"
                else:
                    link = None
                    try:
                        inv  = await c(ExportChatInviteRequest(e))
                        link = getattr(inv, 'link', None)
                    except Exception:
                        pass

                chats.append({
                    'title':    title,
                    'uname':    uname,
                    'dtype':    dtype,
                    'members':  members,
                    'link':     link,
                    'id':       e.id,
                    'private':  not bool(uname),
                    'archived': archived_flag,
                    'left':     False,
                    'creator':  getattr(e, 'creator', False),
                })

        await _collect(False)   # обычные диалоги
        await _collect(True)    # архив

        # Покинутые каналы/группы (в т.ч. где ты создатель)
        async def _collect_left():
            offset = 0
            while True:
                try:
                    result = await c(GetLeftChannelsRequest(offset=offset))
                    left_chats = getattr(result, 'chats', [])
                    if not left_chats:
                        break
                    for e in left_chats:
                        if not isinstance(e, (Channel, Chat)):
                            continue
                        if e.id in seen_ids:
                            continue
                        seen_ids.add(e.id)
                        is_channel   = isinstance(e, Channel) and getattr(e, 'broadcast', False)
                        is_megagroup = isinstance(e, Channel) and getattr(e, 'megagroup', False)
                        uname   = getattr(e, 'username', '') or ''
                        title   = getattr(e, 'title', '') or f"id:{e.id}"
                        members = getattr(e, 'participants_count', None)
                        dtype = 'channel' if is_channel else ('megagroup' if is_megagroup else 'group')
                        if uname:
                            link = f"https://t.me/{uname}"
                        else:
                            link = None
                            # Для приватных — пробуем получить инвайт-ссылку
                            # (работает если ты создатель, даже после выхода)
                            try:
                                inv  = await c(ExportChatInviteRequest(e))
                                link = getattr(inv, 'link', None)
                            except Exception:
                                pass
                        chats.append({
                            'title':    title,
                            'uname':    uname,
                            'dtype':    dtype,
                            'members':  members,
                            'link':     link,
                            'id':       e.id,
                            'private':  not bool(uname),
                            'archived': False,
                            'left':     True,
                            'creator':  getattr(e, 'creator', False),
                        })
                    offset += len(left_chats)
                    if len(left_chats) < 100:
                        break
                except Exception:
                    break

        # Публичные каналы/группы где ты админ (в т.ч. если покинул)
        async def _collect_admined():
            try:
                result = await c(GetAdminedPublicChannelsRequest(by_location=False, check_limit=False))
                for e in getattr(result, 'chats', []):
                    if not isinstance(e, (Channel, Chat)):
                        continue
                    if e.id in seen_ids:
                        continue
                    seen_ids.add(e.id)
                    is_channel   = isinstance(e, Channel) and getattr(e, 'broadcast', False)
                    is_megagroup = isinstance(e, Channel) and getattr(e, 'megagroup', False)
                    uname   = getattr(e, 'username', '') or ''
                    title   = getattr(e, 'title', '') or f"id:{e.id}"
                    members = getattr(e, 'participants_count', None)
                    dtype = 'channel' if is_channel else ('megagroup' if is_megagroup else 'group')
                    link = f"https://t.me/{uname}" if uname else None
                    chats.append({
                        'title':    title,
                        'uname':    uname,
                        'dtype':    dtype,
                        'members':  members,
                        'link':     link,
                        'id':       e.id,
                        'private':  not bool(uname),
                        'archived': False,
                        'left':     False,
                        'creator':  getattr(e, 'creator', False),
                    })
            except Exception:
                pass

        await _collect_left()
        await _collect_admined()
    except Exception as ex:
        stop.set()
        await edit(cb, f"❌ ошибка загрузки: <code>{ex}</code>",
                   kb([b("‹ назад", f"s_data:{aid}")])); return
    stop.set()

    total = len(chats)
    if not total:
        await edit(cb, "👥 <b>группы и каналы</b>\n\nпусто — вы не состоите ни в одной группе или канале",
                   kb([b("‹ назад", f"s_data:{aid}")])); return

    per   = _MYCHATS_PER_PAGE
    pages = max(1, (total + per - 1) // per)
    page  = max(0, min(page, pages - 1))
    chunk = chats[page * per : (page + 1) * per]

    _icons = {'channel': '📢', 'group': '👥', 'megagroup': '💬'}
    page_txt       = f"  ·  {page+1}/{pages}" if pages > 1 else ""
    archived_count = sum(1 for ch in chats if ch.get('archived'))
    left_count     = sum(1 for ch in chats if ch.get('left'))
    arch_txt = f"  📦{archived_count}" if archived_count else ""
    left_txt = f"  🚪{left_count}" if left_count else ""
    lines = [f"👥 <b>группы и каналы</b>  ·  {total} чатов{arch_txt}{left_txt}{page_txt}\n"]

    rows = []
    for ch in chunk:
        ic         = _icons.get(ch['dtype'], '💬')
        name       = ch['title'][:28]
        tag        = f"  @{ch['uname']}" if ch['uname'] else '  🔒'
        mem_txt    = f"  · 👤{_fmt_num(ch['members'])}" if ch['members'] else ''
        badges     = ''
        if ch.get('creator'):  badges += '  👑'
        if ch.get('left'):     badges += '  🚪'
        if ch.get('archived'): badges += '  📦'
        lines.append(f"{ic} <b>{name}</b>{tag}{mem_txt}{badges}")
        if ch.get('link'):
            label = f"{ic} {name}" + (" 🔒" if ch.get('private') else "")
            rows.append([bu(label, ch['link'])])
        else:
            rows.append([b(f"{ic} {name} 🔒 (нет доступа)", f"mychats_info:{aid}:{ch['id']}")])

    nav_row = []
    if page > 0:       nav_row.append(b("◀️", f"mychats:{aid}:{page-1}"))
    if page < pages-1: nav_row.append(b("▶️", f"mychats:{aid}:{page+1}"))
    if nav_row: rows.append(nav_row)

    rows.append([b("🔄 обновить", f"mychats:{aid}:0"), b("‹ назад", f"s_data:{aid}")])
    await edit(cb, "\n".join(lines), kb(*rows))


@router.callback_query(F.data.startswith("mychats_info:"))
async def cb_mychats_info(cb: CallbackQuery):
    """Показывает инфо о приватной группе (без публичной ссылки)."""
    await cb.answer()
    parts   = cb.data.split(":")
    aid     = int(parts[1])
    chat_id = int(parts[2])
    acc     = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc: return
    c = cm.get(aid)
    if not c:
        await edit(cb, "❌ аккаунт не активен", kb([b("‹ назад", f"mychats:{aid}:0")])); return
    try:
        entity   = await c.get_entity(chat_id)
        title    = getattr(entity, 'title', '') or f"id:{chat_id}"
        members  = getattr(entity, 'participants_count', None)
        is_ch    = isinstance(entity, Channel) and entity.broadcast
        is_creator = getattr(entity, 'creator', False)
        dtype    = 'канал' if is_ch else 'группа/супергруппа'
        ic       = '📢' if is_ch else '👥'
        mem_txt  = f"\n👤 участников: <b>{_fmt_num(members)}</b>" if members else ''
        creator_txt = "\n👑 ты создатель" if is_creator else ''

        # Пробуем получить инвайт-ссылку (работает для создателя и админов)
        invite_link = None
        try:
            inv = await c(ExportChatInviteRequest(entity))
            invite_link = getattr(inv, 'link', None)
        except Exception:
            pass

        if invite_link:
            await edit(cb,
                f"{ic} <b>{title}</b>\n"
                f"🔒 приватный {dtype}{mem_txt}{creator_txt}\n\n"
                f"🔗 <code>{invite_link}</code>",
                kb([bu("🔗 открыть / пригласить", invite_link)], [b("‹ назад", f"mychats:{aid}:0")])
            )
        else:
            no_link_txt = "🔒 ты не администратор — ссылку получить нельзя" if not is_creator                           else "⚠️ не удалось получить ссылку (возможно, нужно сначала зайти в чат)"
            await edit(cb,
                f"{ic} <b>{title}</b>\n"
                f"🔒 приватный {dtype}{mem_txt}{creator_txt}\n\n"
                f"{no_link_txt}",
                kb([b("‹ назад", f"mychats:{aid}:0")])
            )
    except Exception as ex:
        await edit(cb, f"❌ ошибка: <code>{ex}</code>",
                   kb([b("‹ назад", f"mychats:{aid}:0")]))


@router.callback_query(F.data.startswith("tgcode:"))
async def cb_tgcode(cb: CallbackQuery):
    await cb.answer()
    aid = int(cb.data.split(":")[1])
    acc = await db_get("SELECT * FROM accounts WHERE id=? AND user_id=?", (aid, cb.from_user.id))
    if not acc:
        await cb.answer()
        return

    row = await db_get(
        "SELECT code, full_text, received_at FROM tg_codes "
        "WHERE account_id=? ORDER BY received_at DESC LIMIT 1",
        (aid,)
    )

    if not row:
        await cb.message.edit_text(
            "🔑 <b>последний код</b>\n\nкодов пока нет — бот перехватит следующий автоматически",
            reply_markup=kb([b("‹ назад", f"acc:{aid}")]),
            parse_mode='HTML'
        )
        return

    code     = row['code']
    received = row['received_at']
    # Форматируем время (убираем микросекунды если есть)
    try:
        from datetime import datetime as _dt
        dt = _dt.fromisoformat(str(received))
        time_str = dt.strftime("%d.%m.%Y  %H:%M:%S")
    except:
        time_str = str(received)

    await cb.message.edit_text(
        f"🔑 <b>последний код от telegram</b>\n\n"
        f"<code>{code}</code>\n\n"
        f"🕐 {time_str}",
        reply_markup=kb([b("‹ назад", f"acc:{aid}")]),
        parse_mode='HTML'
    )


# ══════════════════════════════════════
# ЗАПУСК
# ══════════════════════════════════════

async def _send_startup_notifications(bot: Bot) -> None:
    """При старте бота — уведомляет всех пользователей об обновлении."""
    await asyncio.sleep(2)   # дать боту полностью запуститься
    try:
        users = await db_all("SELECT DISTINCT user_id FROM accounts")
        if not users:
            # Если аккаунтов нет — пробуем из ALLOWED_USERS
            users = [{'user_id': uid} for uid in ALLOWED_USERS] if ALLOWED_USERS else []
        for row in users:
            uid = row['user_id']
            try:
                await bot.send_message(
                    uid,
                    "🔄 <b>бот был обновлён</b>\n\n"
                    "все привязанные аккаунты отключены — необходимо повторить привязку",
                    reply_markup=kb([b("➕ добавить аккаунт", "accs:0")]),
                    parse_mode='HTML'
                )
            except Exception as e:
                log.warning(f"startup notify {uid}: {e}")
            await asyncio.sleep(0.3)
    except Exception as e:
        log.error(f"_send_startup_notifications: {e}")


async def main():
    # Проверка обязательных переменных окружения
    for var in ("BOT_TOKEN", "API_ID", "API_HASH"):
        if not os.environ.get(var):
            raise RuntimeError(f"❌ Переменная окружения {var} не задана!")

    await init_db()
    bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode='HTML'))
    dp  = Dispatcher(storage=MemoryStorage())
    dp.include_router(router)

    # Подключаем middleware безопасности ко всем входящим событиям
    dp.message.middleware(AccessGuardMiddleware())
    dp.callback_query.middleware(AccessGuardMiddleware())

    cm.set_bot(bot)
    await cm.load_all()

    asyncio.create_task(bg_online_watchdog())
    asyncio.create_task(bg_online_tracker())

    log.info("🤖 Bot v3.0 started!")

    # ── уведомление об обновлении всем пользователям ──
    asyncio.create_task(_send_startup_notifications(bot))

    await dp.start_polling(bot, allowed_updates=["message", "callback_query"])

if __name__ == "__main__":
    asyncio.run(main())