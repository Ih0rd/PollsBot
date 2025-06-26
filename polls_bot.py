#!/usr/bin/env python3
"""
Telegram Polls Bot - Security Enhanced Version FIXED
Version: 1.1.2-enhanced-fixed
Исправленная версия с устранением критических ошибок запуска

Enhanced Features:
- Fixed bot token validation (removed Application creation in validation)
- Fixed database initialization errors
- Enhanced error handling and logging
- Improved directory creation
- Better configuration loading
- Fixed import error handling
"""

import json
import logging
import sqlite3
import re
import asyncio
import os
import sys
import time
import uuid
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple, Union
from collections import defaultdict
from functools import wraps
from contextlib import contextmanager

# Enhanced import handling with better error messages
try:
    from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, InlineQueryResultArticle, InputTextMessageContent
    from telegram.ext import Application, CommandHandler, CallbackQueryHandler, MessageHandler, InlineQueryHandler, PollAnswerHandler, filters, ContextTypes
    from telegram.constants import ParseMode
    from telegram.error import TelegramError, RetryAfter, TimedOut, NetworkError
    TELEGRAM_AVAILABLE = True
    print("✅ Telegram библиотека загружена успешно")
except ImportError as e:
    print(f"❌ Ошибка импорта telegram библиотеки: {e}")
    print("📦 Установите: pip3 install python-telegram-bot==20.7")
    TELEGRAM_AVAILABLE = False
    # Create dummy classes for testing
    class Update: pass
    class ContextTypes: 
        class DEFAULT_TYPE: pass
    class Application: pass
    class CommandHandler: pass
    class CallbackQueryHandler: pass
    class MessageHandler: pass
    class InlineQueryHandler: pass
    class PollAnswerHandler: pass
    class filters: pass
    class ParseMode: pass
    class TelegramError(Exception): pass
    class RetryAfter(Exception): pass
    class TimedOut(Exception): pass
    class NetworkError(Exception): pass

# Configuration
BOT_DIR = "/opt/root/PollsBot"
DB_PATH = f"{BOT_DIR}/polls.db"
CONFIG_PATH = f"{BOT_DIR}/config.json"
LOG_PATH = f"{BOT_DIR}/log.txt"
PID_FILE = f"{BOT_DIR}/bot.pid"

# Constants
MAX_POLL_QUESTION = 300
MAX_POLL_OPTION = 100
MAX_TEMPLATE_NAME = 50
RATE_LIMIT_WINDOW = 3600
SESSION_TIMEOUT = 7200  # 2 hours
MAX_RETRIES = 3
RETRY_DELAY = 5
MAX_USERS_IN_MEMORY = 1000  # Prevent memory exhaustion

# User states
class UserState:
    IDLE = "idle"
    WAITING_POLL_QUESTION = "waiting_poll_question"
    WAITING_POLL_OPTIONS = "waiting_poll_options"
    WAITING_TEMPLATE_NAME = "waiting_template_name"
    WAITING_TEMPLATE_QUESTION = "waiting_template_question"
    WAITING_TEMPLATE_OPTIONS = "waiting_template_options"
    WAITING_VARIABLE_VALUE = "waiting_variable_value"

# Enhanced directory creation
def ensure_directories():
    """Ensure all required directories exist"""
    try:
        os.makedirs(BOT_DIR, exist_ok=True)
        print(f"✅ Директория создана: {BOT_DIR}")
        return True
    except Exception as e:
        print(f"❌ Ошибка создания директории {BOT_DIR}: {e}")
        return False

# Setup logging with enhanced error handling
def setup_logging():
    """Setup logging with proper error handling"""
    try:
        ensure_directories()
        logging.basicConfig(
            filename=LOG_PATH, 
            level=logging.INFO,
            format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
            filemode='a'
        )
        logger = logging.getLogger(__name__)
        logger.info("Logging initialized successfully")
        return logger
    except Exception as e:
        print(f"❌ Ошибка настройки логирования: {e}")
        # Fallback to basic logging
        logging.basicConfig(level=logging.INFO)
        return logging.getLogger(__name__)

logger = setup_logging()

def error_handler(func):
    """Enhanced decorator for error handling"""
    @wraps(func)
    async def wrapper(*args, **kwargs):
        try:
            return await func(*args, **kwargs)
        except RetryAfter as e:
            logger.warning(f"Rate limited in {func.__name__}: retry after {e.retry_after}s")
            await asyncio.sleep(e.retry_after)
            return await func(*args, **kwargs)
        except (TimedOut, NetworkError) as e:
            logger.error(f"Network error in {func.__name__}: {e}")
            # Try to send error message
            if len(args) > 1:
                await safe_send_error_message(args[1], "❌ Проблемы с сетью. Попробуйте позже.")
        except TelegramError as e:
            logger.error(f"Telegram error in {func.__name__}: {e}")
            if len(args) > 1:
                await safe_send_error_message(args[1], "❌ Ошибка Telegram. Попробуйте позже.")
        except Exception as e:
            logger.error(f"Unexpected error in {func.__name__}: {e}", exc_info=True)
            if len(args) > 1:
                await safe_send_error_message(args[1], "❌ Внутренняя ошибка. Обратитесь к администратору.")
    return wrapper

async def safe_send_error_message(update_or_query, text: str):
    """Safely send error message to user"""
    try:
        if hasattr(update_or_query, 'edit_message_text'):
            # It's a CallbackQuery
            await update_or_query.edit_message_text(text)
        elif hasattr(update_or_query, 'message') and update_or_query.message:
            # It's an Update
            await update_or_query.message.reply_text(text)
        elif hasattr(update_or_query, 'effective_chat'):
            # Direct chat access
            await update_or_query.effective_chat.send_message(text)
    except Exception as e:
        logger.error(f"Failed to send error message: {e}")

def permission_required(permissions: List[str]):
    """Enhanced decorator for permission checking"""
    def decorator(func):
        @wraps(func)
        async def wrapper(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
            user_id = update.effective_user.id
            user_perm = self.get_permissions(user_id)
            
            if user_perm not in permissions and user_perm != "admin":
                await self.send_message(update, "❌ Недостаточно прав для выполнения команды.")
                return
            
            # Use rate limit from config
            rate_limit = self.config.get('rate_limit_hour', 10)
            if not self.rate_limiter.is_allowed(user_id, rate_limit):
                await self.send_message(update, "⚠️ Превышен лимит запросов. Попробуйте позже.")
                return
            
            return await func(self, update, context)
        return wrapper
    return decorator

class RateLimiter:
    """Enhanced rate limiter with memory leak protection"""
    def __init__(self):
        self.requests = defaultdict(list)
        self.last_cleanup = time.time()
    
    def is_allowed(self, user_id: int, limit: int = 10) -> bool:
        now = time.time()
        
        # More frequent cleanup every 60 seconds
        if now - self.last_cleanup > 60:
            self.cleanup()
            self.last_cleanup = now
        
        user_reqs = self.requests[user_id]
        # Clean old requests for this user
        user_reqs[:] = [t for t in user_reqs if now - t < RATE_LIMIT_WINDOW]
        
        if len(user_reqs) >= limit:
            return False
        
        user_reqs.append(now)
        return True
    
    def is_user_flooding(self, user_id: int) -> bool:
        """Check if user is sending too many messages (anti-flooding)"""
        now = time.time()
        user_messages = self.requests[user_id]
        
        # Check last minute (more strict)
        recent_messages = [t for t in user_messages if now - t < 60]
        if len(recent_messages) > 10:  # Max 10 messages per minute
            return True
        
        # Check last 10 seconds (very strict)
        very_recent = [t for t in user_messages if now - t < 10]
        if len(very_recent) > 3:  # Max 3 messages per 10 seconds
            return True
        
        return False
    
    def cleanup(self):
        """Remove old entries and limit memory usage"""
        now = time.time()
        users_to_remove = []
        
        # Clean old requests first
        for user_id in list(self.requests.keys()):
            self.requests[user_id][:] = [t for t in self.requests[user_id] if now - t < RATE_LIMIT_WINDOW]
            if not self.requests[user_id]:
                users_to_remove.append(user_id)
        
        # Remove users with no recent requests
        for user_id in users_to_remove:
            del self.requests[user_id]
        
        # Limit total users in memory (prevent memory exhaustion)
        if len(self.requests) > MAX_USERS_IN_MEMORY:
            logger.warning(f"RateLimiter memory limit reached: {len(self.requests)} users")
            # Keep most recent users, remove oldest
            oldest_users = sorted(self.requests.items(), 
                                key=lambda x: max(x[1]) if x[1] else 0)[:MAX_USERS_IN_MEMORY//2]
            for user_id, _ in oldest_users:
                del self.requests[user_id]
            logger.info(f"Removed {len(oldest_users)} oldest users from memory")
        
        # Log cleanup statistics
        if users_to_remove or len(self.requests) > MAX_USERS_IN_MEMORY:
            logger.info(f"RateLimiter cleanup: removed {len(users_to_remove)} inactive users, "
                       f"current users: {len(self.requests)}")

class Database:
    """Enhanced database manager with proper error handling"""
    def __init__(self, db_path: str):
        self.db_path = db_path
        # Don't initialize database in constructor - do it explicitly
        self._initialized = False
    
    def initialize(self):
        """Initialize database explicitly"""
        if self._initialized:
            return True
        
        try:
            ensure_directories()
            self.init_database()
            self._initialized = True
            logger.info("Database initialized successfully")
            return True
        except Exception as e:
            logger.error(f"Database initialization failed: {e}")
            return False
    
    @contextmanager
    def get_connection(self):
        conn = None
        try:
            conn = sqlite3.connect(self.db_path, timeout=30.0)
            conn.row_factory = sqlite3.Row
            conn.execute("PRAGMA foreign_keys = ON")
            conn.execute("PRAGMA journal_mode = WAL")
            conn.execute("PRAGMA synchronous = NORMAL")
            yield conn
        except sqlite3.Error as e:
            logger.error(f"Database error: {e}")
            return None
        except Exception as e:
            logger.error(f"Unexpected database error: {e}")
            return None
        finally:
            if conn:
                try:
                    conn.close()
                except Exception as e:
                    logger.warning(f"Error closing database connection: {e}")
    
    def query(self, sql: str, params: Tuple = ()) -> List[sqlite3.Row]:
        """Execute SELECT query with proper error handling"""
        try:
            with self.get_connection() as conn:
                cursor = conn.cursor()
                cursor.execute(sql, params)
                return cursor.fetchall()
        except Exception as e:
            logger.error(f"Query execution error: {sql}, params: {params}, error: {e}")
            return []
    
    def execute(self, sql: str, params: Tuple = ()) -> bool:
        """Execute INSERT/UPDATE/DELETE query with proper error handling"""
        try:
            with self.get_connection() as conn:
                cursor = conn.cursor()
                cursor.execute(sql, params)
                conn.commit()
                return True
        except Exception as e:
            logger.error(f"Execute error: {sql}, params: {params}, error: {e}")
            return False
    
    def execute_with_result(self, sql: str, params: Tuple = ()) -> Optional[int]:
        """Execute query and return lastrowid"""
        try:
            with self.get_connection() as conn:
                cursor = conn.cursor()
                cursor.execute(sql, params)
                conn.commit()
                return cursor.lastrowid
        except Exception as e:
            logger.error(f"Execute with result error: {sql}, params: {params}, error: {e}")
            return None
    
    def init_database(self):
        """Initialize database with all required tables"""
        try:
            with self.get_connection() as conn:
                conn.executescript("""
                    CREATE TABLE IF NOT EXISTS users (
                        user_id INTEGER PRIMARY KEY,
                        username TEXT,
                        permissions TEXT DEFAULT 'use',
                        last_activity TEXT DEFAULT CURRENT_TIMESTAMP
                    );

                    CREATE TABLE IF NOT EXISTS templates (
                        name TEXT PRIMARY KEY,
                        question TEXT NOT NULL,
                        options TEXT NOT NULL,
                        description TEXT,
                        variables TEXT DEFAULT '[]',
                        created_by INTEGER,
                        usage_count INTEGER DEFAULT 0,
                        threshold INTEGER DEFAULT 50,
                        non_anonymous INTEGER DEFAULT 0,
                        created_date TEXT DEFAULT CURRENT_TIMESTAMP
                    );

                    CREATE TABLE IF NOT EXISTS polls (
                        poll_id TEXT PRIMARY KEY,
                        telegram_poll_id TEXT UNIQUE,
                        question TEXT NOT NULL,
                        options TEXT NOT NULL,
                        chat_id INTEGER NOT NULL,
                        message_id INTEGER,
                        creator_id INTEGER NOT NULL,
                        status TEXT DEFAULT 'active',
                        created_date TEXT DEFAULT CURRENT_TIMESTAMP,
                        template_used TEXT,
                        threshold INTEGER DEFAULT 50,
                        non_anonymous INTEGER DEFAULT 0,
                        total_voters INTEGER DEFAULT 0
                    );

                    CREATE TABLE IF NOT EXISTS poll_votes (
                        poll_id TEXT,
                        user_id INTEGER,
                        username TEXT,
                        option_id INTEGER,
                        vote_date TEXT DEFAULT CURRENT_TIMESTAMP,
                        UNIQUE(poll_id, user_id)
                    );

                    CREATE TABLE IF NOT EXISTS template_sessions (
                        session_id TEXT PRIMARY KEY,
                        user_id INTEGER NOT NULL,
                        template_name TEXT NOT NULL,
                        variables_needed TEXT NOT NULL,
                        variables_values TEXT DEFAULT '{}',
                        current_variable INTEGER DEFAULT 0,
                        chat_id INTEGER NOT NULL,
                        created_date TEXT DEFAULT CURRENT_TIMESTAMP
                    );

                    CREATE TABLE IF NOT EXISTS user_states (
                        user_id INTEGER PRIMARY KEY,
                        state TEXT DEFAULT 'idle',
                        data TEXT DEFAULT '{}',
                        updated_date TEXT DEFAULT CURRENT_TIMESTAMP
                    );

                    CREATE INDEX IF NOT EXISTS idx_polls_creator ON polls(creator_id);
                    CREATE INDEX IF NOT EXISTS idx_sessions_user ON template_sessions(user_id);
                    CREATE INDEX IF NOT EXISTS idx_user_states ON user_states(user_id);
                    CREATE INDEX IF NOT EXISTS idx_sessions_created ON template_sessions(created_date);
                """)
                conn.commit()
                logger.info("Database tables created successfully")
        except Exception as e:
            logger.error(f"Database initialization error: {e}")
            raise

class PollsBot:
    """Enhanced Telegram Polls Bot with security fixes"""
    
    def __init__(self):
        print("🔧 Инициализация PollsBot...")
        
        # Check telegram library availability
        if not TELEGRAM_AVAILABLE:
            print("❌ Telegram библиотека не установлена!")
            print("📦 Установите: pip3 install python-telegram-bot==20.7")
            sys.exit(1)
        
        # Load configuration first
        self.config = self._load_config()
        print(f"✅ Конфигурация загружена")
        
        # Initialize database
        self.db = Database(DB_PATH)
        if not self.db.initialize():
            print("❌ Ошибка инициализации базы данных!")
            sys.exit(1)
        print("✅ База данных инициализирована")
        
        # Initialize other components
        self.rate_limiter = RateLimiter()
        self.application = None
        self._cleanup_task = None
        
        # Create default templates
        self._create_default_templates()
        print("✅ Шаблоны по умолчанию созданы")
        
        # Write PID file
        self._write_pid()
        print("✅ PID файл создан")
        
        print("✅ PollsBot инициализирован успешно")

    def _load_config(self) -> Dict:
        """Load configuration with comprehensive defaults"""
        defaults = {
            "bot_token": "",
            "admin_chat_id": "",
            "polling_interval": 2,
            "max_poll_options": 10,
            "rate_limit_hour": 10,
            "web_port": 8080,
            "default_decision_threshold": 50,
            "auto_close_hours": 24
        }
        
        if os.path.exists(CONFIG_PATH):
            try:
                with open(CONFIG_PATH, 'r', encoding='utf-8') as f:
                    config = json.load(f)
                    merged_config = {**defaults, **config}
                    print(f"✅ Конфигурация загружена из {CONFIG_PATH}")
                    return merged_config
            except Exception as e:
                logger.error(f"Config load error: {e}")
                print(f"⚠️ Ошибка загрузки конфигурации: {e}")
                print("📝 Используются настройки по умолчанию")
        else:
            print(f"⚠️ Файл конфигурации не найден: {CONFIG_PATH}")
            print("📝 Используются настройки по умолчанию")
        
        return defaults

    def _write_pid(self):
        """Write PID file"""
        try:
            with open(PID_FILE, 'w') as f:
                f.write(str(os.getpid()))
            logger.info(f"PID file written: {os.getpid()}")
        except Exception as e:
            logger.warning(f"Could not write PID: {e}")
            print(f"⚠️ Не удалось создать PID файл: {e}")

    def _create_default_templates(self):
        """Create default templates if they don't exist"""
        templates = [
            ("yes_no", "{X}?", "Да|Нет", "Простой шаблон да/нет", ["X"]),
            ("budget", "Выделить {X} рублей на {Y}?", "За|Против|Воздержаться", "Голосование по бюджету", ["X", "Y"]),
            ("meeting", "Встреча {X} в {Y}?", "Подходит|Не подходит|Предложить другое", "Согласование встречи", ["X", "Y"]),
            ("priority", "Приоритет: {X}", "Высокий|Средний|Низкий", "Определение приоритета", ["X"])
        ]
        
        try:
            for name, question, options, desc, variables in templates:
                existing = self.db.query("SELECT name FROM templates WHERE name = ?", (name,))
                if not existing:
                    self.db.execute("""
                        INSERT INTO templates (name, question, options, description, variables, created_by)
                        VALUES (?, ?, ?, ?, ?, ?)
                    """, (name, question, options, desc, json.dumps(variables), 0))
            logger.info("Default templates created")
        except Exception as e:
            logger.error(f"Error creating default templates: {e}")
            print(f"⚠️ Ошибка создания шаблонов по умолчанию: {e}")

    async def validate_bot_token(self, token: str) -> bool:
        """Validate bot token format and accessibility"""
        if not token or not re.match(r'^\d+:[A-Za-z0-9_-]{35}$', token):
            logger.error("Invalid bot token format")
            return False
        
        # Don't create Application here - just validate format
        # The actual API validation will be done during bot startup
        logger.info("Bot token format validated")
        return True

    def validate_callback_data(self, data: str) -> bool:
        """Validate callback data against whitelist"""
        if not data or len(data) > 100:
            return False
        
        # Whitelist of allowed patterns
        allowed_patterns = [
            r'^use:[a-zA-Z0-9_-]+$',
            r'^cancel:[a-f0-9-]{36}$',  # UUID format
            r'^(create_simple|create_template|new_template)$'
        ]
        
        return any(re.match(pattern, data) for pattern in allowed_patterns)

    # Utility methods
    def sanitize(self, text: str, max_len: int = 200) -> str:
        """Enhanced text sanitization"""
        if not text or not isinstance(text, str):
            return ""
        
        # Remove control characters and excessive whitespace
        text = re.sub(r'[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]', '', text)
        text = re.sub(r'\s+', ' ', text.strip())
        
        return text[:max_len] if len(text) > max_len else text

    def extract_variables(self, text: str) -> List[str]:
        """Extract {X}, {Y}, {Z} variables"""
        variables = re.findall(r'\{([A-Z])\}', text)
        return sorted(list(set(variables)))

    def substitute_variables(self, text: str, values: Dict[str, str]) -> str:
        """Replace variables with values and validate"""
        result = text
        for var, value in values.items():
            placeholder = f"{{{var}}}"
            if placeholder in result:
                result = result.replace(placeholder, str(value))
        
        # Check for unresolved variables
        remaining_vars = re.findall(r'\{([A-Z])\}', result)
        if remaining_vars:
            logger.warning(f"Unresolved variables in template: {remaining_vars}")
            # Replace remaining variables with placeholder
            for var in remaining_vars:
                result = result.replace(f"{{{var}}}", f"[{var}]")
        
        return result

    def validate_poll_data(self, question: str, options: List[str]) -> Tuple[bool, str]:
        """Validate poll data"""
        if not question or len(question.strip()) == 0:
            return False, "Вопрос не может быть пустым"
        
        if len(question) > MAX_POLL_QUESTION:
            return False, f"Вопрос слишком длинный (макс. {MAX_POLL_QUESTION} символов)"
        
        if len(options) < 2:
            return False, "Нужно минимум 2 варианта ответа"
        
        if len(options) > self.config.get('max_poll_options', 10):
            return False, f"Максимум {self.config.get('max_poll_options', 10)} вариантов"
        
        for option in options:
            if not option or len(option.strip()) == 0:
                return False, "Варианты ответов не могут быть пустыми"
            if len(option) > MAX_POLL_OPTION:
                return False, f"Вариант слишком длинный (макс. {MAX_POLL_OPTION} символов)"
        
        return True, ""

    async def send_message(self, update_or_query, text: str, reply_markup=None):
        """Universal message sender with retry logic"""
        for attempt in range(MAX_RETRIES):
            try:
                if hasattr(update_or_query, 'edit_message_text'):
                    await update_or_query.edit_message_text(text, parse_mode=ParseMode.MARKDOWN, reply_markup=reply_markup)
                else:
                    await update_or_query.message.reply_text(text, parse_mode=ParseMode.MARKDOWN, reply_markup=reply_markup)
                return True
            except RetryAfter as e:
                if attempt < MAX_RETRIES - 1:
                    await asyncio.sleep(e.retry_after)
                    continue
                else:
                    logger.error(f"Max retries exceeded for send_message")
                    return False
            except Exception as e:
                if attempt < MAX_RETRIES - 1:
                    await asyncio.sleep(RETRY_DELAY)
                    continue
                else:
                    logger.error(f"Failed to send message after {MAX_RETRIES} attempts: {e}")
                    return False

    # Enhanced user state management (database-backed)
    def get_user_state(self, user_id: int) -> Dict:
        """Get user state from database"""
        try:
            result = self.db.query("SELECT state, data FROM user_states WHERE user_id = ?", (user_id,))
            if result:
                state_data = json.loads(result[0][1]) if result[0][1] else {}
                return {"state": result[0][0], "data": state_data}
            return {"state": UserState.IDLE, "data": {}}
        except Exception as e:
            logger.error(f"Get user state error: {e}")
            return {"state": UserState.IDLE, "data": {}}

    def set_user_state(self, user_id: int, state: str, data: Dict = None):
        """Set user state in database"""
        try:
            if data is None:
                data = {}
            
            self.db.execute("""
                INSERT OR REPLACE INTO user_states (user_id, state, data, updated_date)
                VALUES (?, ?, ?, ?)
            """, (user_id, state, json.dumps(data), datetime.now().isoformat()))
        except Exception as e:
            logger.error(f"Set user state error: {e}")

    def clear_user_state(self, user_id: int):
        """Clear user state"""
        try:
            self.db.execute("DELETE FROM user_states WHERE user_id = ?", (user_id,))
        except Exception as e:
            logger.error(f"Clear user state error: {e}")

    def get_permissions(self, user_id: int) -> str:
        """Get user permissions"""
        try:
            result = self.db.query("SELECT permissions FROM users WHERE user_id = ?", (user_id,))
            if result:
                return result[0][0]
            
            # Auto-add user with default permissions
            self.add_user(user_id, f"user_{user_id}", "use")
            return "use"
        except Exception as e:
            logger.error(f"Get permissions error: {e}")
            return "use"

    def add_user(self, user_id: int, username: str, permissions: str = "use"):
        """Add user to database"""
        try:
            self.db.execute("""
                INSERT OR REPLACE INTO users (user_id, username, permissions, last_activity)
                VALUES (?, ?, ?, ?)
            """, (user_id, username, permissions, datetime.now().isoformat()))
        except Exception as e:
            logger.error(f"Add user error: {e}")

    def get_templates(self) -> List[Dict]:
        """Get all templates"""
        try:
            results = self.db.query("""
                SELECT name, question, options, description, variables, usage_count
                FROM templates ORDER BY usage_count DESC
            """)
            
            templates = []
            for row in results:
                templates.append({
                    "name": row[0],
                    "question": row[1],
                    "options": row[2],
                    "description": row[3],
                    "variables": json.loads(row[4]) if row[4] else [],
                    "usage_count": row[5]
                })
            return templates
        except Exception as e:
            logger.error(f"Get templates error: {e}")
            return []

    async def run(self):
        """Enhanced main bot runner with token validation"""
        if not self.config.get("bot_token"):
            logger.error("Bot token not configured!")
            print("❌ Токен бота не настроен!")
            return
        
        # Only validate token format, not API call
        if not await self.validate_bot_token(self.config["bot_token"]):
            logger.error("Bot token validation failed!")
            print("❌ Валидация токена бота не прошла!")
            return
        
        try:
            print("🚀 Запускаю бота...")
            self.application = Application.builder().token(self.config["bot_token"]).build()
            
            # Add handlers
            handlers = [
                CommandHandler("start", self.start_command),
                CommandHandler("create", self.create_command),
                CommandHandler("templates", self.templates_command),
                CommandHandler("status", self.status_command),
                CommandHandler("help", self.help_command),
                CallbackQueryHandler(self.callback_handler),
                InlineQueryHandler(self.inline_query_handler),
                PollAnswerHandler(self.poll_answer_handler),
                MessageHandler(filters.TEXT & ~filters.COMMAND, self.text_handler)
            ]
            
            for handler in handlers:
                self.application.add_handler(handler)
            
            # Start cleanup task
            self._cleanup_task = asyncio.create_task(self.periodic_cleanup())
            
            logger.info("Starting PollsBot v1.1.2-enhanced-fixed...")
            print("✅ Бот запущен успешно!")
            await self.application.run_polling(poll_interval=self.config.get("polling_interval", 2))
            
        except Exception as e:
            logger.error(f"Bot error: {e}")
            print(f"❌ Ошибка запуска бота: {e}")
            raise
        finally:
            await self._shutdown()

    # Command handlers
    @error_handler
    async def start_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle /start command"""
        user = update.effective_user
        self.add_user(user.id, user.username or f"user_{user.id}")
        
        welcome_text = f"""
🎉 Добро пожаловать в PollsBot!

Я помогу вам создавать и проводить опросы в Telegram.

📋 Доступные команды:
/start - это сообщение
/create - создать новый опрос
/templates - список шаблонов
/status - статус активных опросов
/help - справка

👤 Ваш ID: {user.id}
🔑 Права: {self.get_permissions(user.id)}
        """
        
        await self.send_message(update, welcome_text.strip())

    @error_handler
    @permission_required(["use", "create", "manage", "admin"])
    async def create_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle /create command"""
        keyboard = [
            [InlineKeyboardButton("📝 Простой опрос", callback_data="create_simple")],
            [InlineKeyboardButton("📋 Из шаблона", callback_data="create_template")],
            [InlineKeyboardButton("➕ Новый шаблон", callback_data="new_template")]
        ]
        reply_markup = InlineKeyboardMarkup(keyboard)
        
        await self.send_message(
            update, 
            "🗳️ Выберите тип опроса:",
            reply_markup=reply_markup
        )

    @error_handler
    async def templates_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle /templates command"""
        templates = self.get_templates()
        
        if not templates:
            await self.send_message(update, "📋 Шаблоны не найдены")
            return
        
        text = "📋 Доступные шаблоны:\n\n"
        for template in templates[:10]:  # Show first 10
            text += f"• **{template['name']}**\n"
            text += f"  {template['question']}\n"
            text += f"  Варианты: {template['options']}\n"
            if template['variables']:
                text += f"  Переменные: {', '.join(template['variables'])}\n"
            text += f"  Использований: {template['usage_count']}\n\n"
        
        if len(templates) > 10:
            text += f"... и еще {len(templates) - 10} шаблонов"
        
        await self.send_message(update, text)

    @error_handler
    async def status_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle /status command"""
        try:
            active_polls = self.db.query("""
                SELECT COUNT(*) as count FROM polls WHERE status = 'active'
            """)
            total_polls = self.db.query("SELECT COUNT(*) as count FROM polls")
            
            active_count = active_polls[0][0] if active_polls else 0
            total_count = total_polls[0][0] if total_polls else 0
            
            text = f"""
📊 Статистика опросов:

🟢 Активных: {active_count}
📈 Всего: {total_count}
👥 Пользователей: {len(self.db.query("SELECT user_id FROM users"))}
            """
            
            await self.send_message(update, text.strip())
            
        except Exception as e:
            logger.error(f"Status command error: {e}")
            await self.send_message(update, "❌ Ошибка получения статистики")

    @error_handler
    async def help_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle /help command"""
        help_text = """
📖 Справка по PollsBot

🗳️ Создание опросов:
• /create - создать опрос
• Простой опрос - введите вопрос и варианты
• Шаблон - выберите готовый шаблон
• Новый шаблон - создайте свой шаблон

📋 Управление:
• /templates - список шаблонов
• /status - статистика
• /help - эта справка

🔧 Шаблоны поддерживают переменные:
• {X}, {Y}, {Z} - заменяются на ваши значения
• Пример: "Встреча {X} в {Y}?"

💡 Советы:
• Используйте короткие вопросы
• Не более 10 вариантов ответа
• Шаблоны экономят время
        """
        
        await self.send_message(update, help_text.strip())

    @error_handler
    async def callback_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle callback queries"""
        query = update.callback_query
        await query.answer()
        
        if not self.validate_callback_data(query.data):
            await query.edit_message_text("❌ Неверные данные")
            return
        
        user_id = query.from_user.id
        self.add_user(user_id, query.from_user.username or f"user_{user_id}")
        
        if query.data == "create_simple":
            self.set_user_state(user_id, UserState.WAITING_POLL_QUESTION)
            await query.edit_message_text("📝 Введите вопрос для опроса:")
            
        elif query.data == "create_template":
            templates = self.get_templates()
            if not templates:
                await query.edit_message_text("📋 Шаблоны не найдены")
                return
            
            keyboard = []
            for template in templates[:10]:
                keyboard.append([InlineKeyboardButton(
                    template['name'], 
                    callback_data=f"use:{template['name']}"
                )])
            
            reply_markup = InlineKeyboardMarkup(keyboard)
            await query.edit_message_text(
                "📋 Выберите шаблон:",
                reply_markup=reply_markup
            )
            
        elif query.data == "new_template":
            self.set_user_state(user_id, UserState.WAITING_TEMPLATE_NAME)
            await query.edit_message_text("📝 Введите название шаблона:")
            
        elif query.data.startswith("use:"):
            template_name = query.data[4:]
            await self.handle_template_use(query, template_name)
            
        elif query.data.startswith("cancel:"):
            session_id = query.data[7:]
            self.clear_template_session(session_id)
            await query.edit_message_text("❌ Создание отменено")

    @error_handler
    async def inline_query_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle inline queries"""
        query = update.inline_query
        if not query.query:
            return
        
        # Simple inline poll creation
        results = []
        try:
            # Parse query like "question? option1|option2|option3"
            if "?" in query.query and "|" in query.query:
                question_part, options_part = query.query.split("?", 1)
                question = question_part.strip()
                options = [opt.strip() for opt in options_part.split("|") if opt.strip()]
                
                if len(options) >= 2 and len(options) <= 10:
                    poll_id = str(uuid.uuid4())
                    
                    # Create poll in database
                    self.db.execute("""
                        INSERT INTO polls (poll_id, question, options, chat_id, creator_id, status)
                        VALUES (?, ?, ?, ?, ?, ?)
                    """, (poll_id, question, "|".join(options), query.from_user.id, query.from_user.id, "active"))
                    
                    # Create inline result
                    result = InlineQueryResultArticle(
                        id=poll_id,
                        title=f"📊 {question}",
                        description=f"Варианты: {', '.join(options[:3])}{'...' if len(options) > 3 else ''}",
                        input_message_content=InputTextMessageContent(
                            f"🗳️ **{question}**\n\n" + "\n".join([f"{i+1}. {opt}" for i, opt in enumerate(options)])
                        )
                    )
                    results.append(result)
        except Exception as e:
            logger.error(f"Inline query error: {e}")
        
        await query.answer(results)

    @error_handler
    async def poll_answer_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle poll answers"""
        poll_answer = update.poll_answer
        user_id = poll_answer.user.id
        username = poll_answer.user.username or f"user_{user_id}"
        
        try:
            # Record vote
            self.db.execute("""
                INSERT OR REPLACE INTO poll_votes (poll_id, user_id, username, option_id)
                VALUES (?, ?, ?, ?)
            """, (poll_answer.poll_id, user_id, username, poll_answer.option_ids[0]))
            
            logger.info(f"Vote recorded: user {user_id} voted {poll_answer.option_ids[0]} in poll {poll_answer.poll_id}")
            
        except Exception as e:
            logger.error(f"Poll answer error: {e}")

    @error_handler
    async def text_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle text messages"""
        user_id = update.effective_user.id
        text = update.message.text.strip()
        
        if not text:
            return
        
        # Check for flooding
        if self.rate_limiter.is_user_flooding(user_id):
            await self.send_message(update, "⚠️ Слишком много сообщений. Подождите немного.")
            return
        
        user_state = self.get_user_state(user_id)
        state = user_state["state"]
        data = user_state["data"]
        
        if state == UserState.WAITING_POLL_QUESTION:
            data["question"] = self.sanitize(text, MAX_POLL_QUESTION)
            self.set_user_state(user_id, UserState.WAITING_POLL_OPTIONS, data)
            await self.send_message(update, "📝 Введите варианты ответов через запятую:")
            
        elif state == UserState.WAITING_POLL_OPTIONS:
            options = [opt.strip() for opt in text.split(",") if opt.strip()]
            valid, error = self.validate_poll_data(data.get("question", ""), options)
            
            if not valid:
                await self.send_message(update, f"❌ {error}")
                return
            
            # Create poll
            await self.create_poll(update, data["question"], options)
            self.clear_user_state(user_id)
            
        elif state == UserState.WAITING_TEMPLATE_NAME:
            if not re.match(r'^[a-zA-Z0-9_-]{3,50}$', text):
                await self.send_message(update, "❌ Название должно содержать 3-50 символов (буквы, цифры, _ -)")
                return
            
            data["template_name"] = text
            self.set_user_state(user_id, UserState.WAITING_TEMPLATE_QUESTION, data)
            await self.send_message(update, "📝 Введите вопрос шаблона (используйте {X}, {Y} для переменных):")
            
        elif state == UserState.WAITING_TEMPLATE_QUESTION:
            data["template_question"] = text
            self.set_user_state(user_id, UserState.WAITING_TEMPLATE_OPTIONS, data)
            await self.send_message(update, "📝 Введите варианты ответов через запятую:")
            
        elif state == UserState.WAITING_TEMPLATE_OPTIONS:
            options = [opt.strip() for opt in text.split(",") if opt.strip()]
            if len(options) < 2:
                await self.send_message(update, "❌ Нужно минимум 2 варианта ответа")
                return
            
            # Create template
            template_name = data["template_name"]
            template_question = data["template_question"]
            variables = self.extract_variables(template_question)
            
            try:
                self.db.execute("""
                    INSERT OR REPLACE INTO templates (name, question, options, description, variables, created_by)
                    VALUES (?, ?, ?, ?, ?, ?)
                """, (template_name, template_question, "|".join(options), 
                     f"Шаблон от {update.effective_user.username or update.effective_user.id}",
                     json.dumps(variables), user_id))
                
                await self.send_message(update, f"✅ Шаблон '{template_name}' создан!")
                self.clear_user_state(user_id)
                
            except Exception as e:
                logger.error(f"Template creation error: {e}")
                await self.send_message(update, "❌ Ошибка создания шаблона")
                self.clear_user_state(user_id)

    async def handle_template_use(self, query, template_name: str):
        """Handle template usage"""
        try:
            template_data = self.db.query("""
                SELECT question, options, variables FROM templates WHERE name = ?
            """, (template_name,))
            
            if not template_data:
                await query.edit_message_text("❌ Шаблон не найден")
                return
            
            template = template_data[0]
            question = template[0]
            options = template[1].split("|")
            variables = json.loads(template[2]) if template[2] else []
            
            if not variables:
                # No variables, create poll directly
                await self.create_poll_from_query(query, question, options, template_name)
            else:
                # Has variables, start variable collection
                session_id = str(uuid.uuid4())
                self.db.execute("""
                    INSERT INTO template_sessions (session_id, user_id, template_name, variables_needed, chat_id)
                    VALUES (?, ?, ?, ?, ?)
                """, (session_id, query.from_user.id, template_name, json.dumps(variables), query.message.chat_id))
                
                keyboard = [[InlineKeyboardButton("❌ Отмена", callback_data=f"cancel:{session_id}")]]
                reply_markup = InlineKeyboardMarkup(keyboard)
                
                await query.edit_message_text(
                    f"📝 Введите значение для переменной {variables[0]}:",
                    reply_markup=reply_markup
                )
                
        except Exception as e:
            logger.error(f"Template use error: {e}")
            await query.edit_message_text("❌ Ошибка использования шаблона")

    async def create_poll(self, update: Update, question: str, options: List[str]):
        """Create and send a poll"""
        try:
            poll_id = str(uuid.uuid4())
            
            # Save to database
            self.db.execute("""
                INSERT INTO polls (poll_id, question, options, chat_id, creator_id, status)
                VALUES (?, ?, ?, ?, ?, ?)
            """, (poll_id, question, "|".join(options), update.effective_chat.id, update.effective_user.id, "active"))
            
            # Send poll
            poll_message = await update.message.reply_poll(
                question=question,
                options=options,
                is_anonymous=False,
                allows_multiple_answers=False
            )
            
            # Update database with Telegram poll ID
            self.db.execute("""
                UPDATE polls SET telegram_poll_id = ?, message_id = ? WHERE poll_id = ?
            """, (poll_message.poll.id, poll_message.message_id, poll_id))
            
            await self.send_message(update, "✅ Опрос создан!")
            
        except Exception as e:
            logger.error(f"Poll creation error: {e}")
            await self.send_message(update, "❌ Ошибка создания опроса")

    async def create_poll_from_query(self, query, question: str, options: List[str], template_name: str = None):
        """Create poll from callback query"""
        try:
            poll_id = str(uuid.uuid4())
            
            # Save to database
            self.db.execute("""
                INSERT INTO polls (poll_id, question, options, chat_id, creator_id, status, template_used)
                VALUES (?, ?, ?, ?, ?, ?, ?)
            """, (poll_id, question, "|".join(options), query.message.chat_id, query.from_user.id, "active", template_name))
            
            # Update template usage count
            if template_name:
                self.db.execute("""
                    UPDATE templates SET usage_count = usage_count + 1 WHERE name = ?
                """, (template_name,))
            
            # Send poll
            poll_message = await query.message.reply_poll(
                question=question,
                options=options,
                is_anonymous=False,
                allows_multiple_answers=False
            )
            
            # Update database with Telegram poll ID
            self.db.execute("""
                UPDATE polls SET telegram_poll_id = ?, message_id = ? WHERE poll_id = ?
            """, (poll_message.poll.id, poll_message.message_id, poll_id))
            
            await query.edit_message_text("✅ Опрос создан!")
            
        except Exception as e:
            logger.error(f"Poll creation from query error: {e}")
            await query.edit_message_text("❌ Ошибка создания опроса")

    def clear_template_session(self, session_id: str):
        """Clear template session"""
        try:
            self.db.execute("DELETE FROM template_sessions WHERE session_id = ?", (session_id,))
        except Exception as e:
            logger.error(f"Clear session error: {e}")

    async def periodic_cleanup(self):
        """Periodic cleanup task"""
        while True:
            try:
                # Clean old sessions
                cutoff_time = datetime.now() - timedelta(hours=1)
                self.db.execute("""
                    DELETE FROM template_sessions WHERE created_date < ?
                """, (cutoff_time.isoformat(),))
                
                # Clean old user states
                self.db.execute("""
                    DELETE FROM user_states WHERE updated_date < ?
                """, (cutoff_time.isoformat(),))
                
                # Auto-close old polls
                auto_close_hours = self.config.get('auto_close_hours', 24)
                if auto_close_hours > 0:
                    cutoff_time = datetime.now() - timedelta(hours=auto_close_hours)
                    self.db.execute("""
                        UPDATE polls SET status = 'closed' 
                        WHERE status = 'active' AND created_date < ?
                    """, (cutoff_time.isoformat(),))
                
                logger.info("Periodic cleanup completed")
                
            except Exception as e:
                logger.error(f"Cleanup error: {e}")
            
            await asyncio.sleep(300)  # Run every 5 minutes

    async def _shutdown(self):
        """Cleanup on shutdown"""
        try:
            if self._cleanup_task:
                self._cleanup_task.cancel()
                try:
                    await self._cleanup_task
                except asyncio.CancelledError:
                    pass
            
            if self.application:
                await self.application.shutdown()
            
            # Remove PID file
            if os.path.exists(PID_FILE):
                os.remove(PID_FILE)
            
            logger.info("Bot shutdown completed")
            
        except Exception as e:
            logger.error(f"Shutdown error: {e}")

def main():
    """Entry point with enhanced error handling"""
    try:
        print("🚀 Запуск PollsBot v1.1.2-enhanced-fixed...")
        print("=" * 50)
        
        # Check if we're in the right directory
        if not os.path.exists(BOT_DIR):
            print(f"📂 Создаю директорию: {BOT_DIR}")
            ensure_directories()
        
        # Create bot instance
        bot = PollsBot()
        
        # Run the bot
        print("🔄 Запускаю основной цикл бота...")
        asyncio.run(bot.run())
        
    except KeyboardInterrupt:
        print("\n⏹️ Бот остановлен пользователем")
        logger.info("Bot stopped by user")
    except Exception as e:
        print(f"\n❌ Критическая ошибка: {e}")
        logger.error(f"Fatal error: {e}", exc_info=True)
        
        # Additional diagnostics
        print("\n🔍 Диагностика:")
        print(f"• Python версия: {sys.version}")
        print(f"• Текущая директория: {os.getcwd()}")
        print(f"• Директория бота: {BOT_DIR}")
        print(f"• Telegram доступна: {TELEGRAM_AVAILABLE}")
        
        if os.path.exists(CONFIG_PATH):
            print(f"• Конфигурация найдена: {CONFIG_PATH}")
        else:
            print(f"• Конфигурация не найдена: {CONFIG_PATH}")
        
        sys.exit(1)

if __name__ == "__main__":
    main()
