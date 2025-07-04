#!/usr/bin/env python3
"""
Telegram Polls Bot 2.0

"""

import asyncio
from collections import defaultdict
from contextlib import contextmanager
from datetime import datetime, timedelta
from functools import wraps
import base64
import json
import logging
import os
import re
import sqlite3
import sys
import time
from typing import Dict, List, Optional, Tuple, Union
import uuid
import math

try:
    from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, InlineQueryResultArticle, InputTextMessageContent
    from telegram.ext import Application, CommandHandler, CallbackQueryHandler, MessageHandler, InlineQueryHandler, filters, ContextTypes
    from telegram.constants import ParseMode
    from telegram.error import TelegramError, RetryAfter, TimedOut, NetworkError
except ImportError:
    print("telegram library not found. Install: pip3 install python-telegram-bot==20.7")
    sys.exit(1)

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
SESSION_TIMEOUT = 7200
MAX_RETRIES = 3
RETRY_DELAY = 5
MAX_USERS_IN_MEMORY = 1000

# User states
class UserState:
    IDLE = "idle"
    WAITING_POLL_QUESTION = "waiting_poll_question"
    WAITING_POLL_OPTIONS = "waiting_poll_options"
    WAITING_POLL_OPTION = "waiting_poll_option"  # Новое состояние для ввода вариантов по одному
    WAITING_TEMPLATE_NAME = "waiting_template_name"
    WAITING_TEMPLATE_QUESTION = "waiting_template_question"
    WAITING_TEMPLATE_OPTIONS = "waiting_template_options"
    WAITING_TEMPLATE_OPTION = "waiting_template_option"
    WAITING_VARIABLE_VALUE = "waiting_variable_value"
    WAITING_DECISION_NUMBER = "waiting_decision_number"
    WAITING_DECISION_NUMBER_INPUT = "waiting_decision_number_input"
    WAITING_TEMPLATE_THRESHOLD = "waiting_template_threshold"
    WAITING_EDIT_TEMPLATE_THRESHOLD = "waiting_edit_template_threshold"
    WAITING_MAX_PARTICIPANTS = "waiting_max_participants"
    WAITING_TEMPLATE_CREATION_THRESHOLD = "waiting_template_creation_threshold"
    WAITING_POLL_THRESHOLD = "waiting_poll_threshold"
    WAITING_TEMPLATE_POLL_THRESHOLD = "waiting_template_poll_threshold"

# Setup logging
os.makedirs(BOT_DIR, exist_ok=True)

# Создаем отдельные файлы для разных уровней логирования
LOG_DIR = f"{BOT_DIR}/logs"
os.makedirs(LOG_DIR, exist_ok=True)

# Пути к файлам логов
LOG_FILES = {
    'debug': f"{LOG_DIR}/debug.log",
    'info': f"{LOG_DIR}/info.log",
    'warning': f"{LOG_DIR}/warning.log",
    'error': f"{LOG_DIR}/error.log",
    'critical': f"{LOG_DIR}/critical.log"
}

# Настройка основного логгера
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(LOG_FILES['debug'], encoding='utf-8'),
        logging.StreamHandler()  # Вывод в консоль
    ]
)

# Предварительная настройка логгеров сторонних библиотек
# Это поможет избежать проблем с httpcore и другими библиотеками
for logger_name in ['httpcore', 'httpx', 'telegram', 'urllib3', 'asyncio', 'aiohttp', 'websockets']:
    try:
        third_party_logger = logging.getLogger(logger_name)
        third_party_logger.setLevel(logging.WARNING)  # Устанавливаем WARNING по умолчанию
        third_party_logger.propagate = False
    except Exception:
        pass  # Игнорируем ошибки, если логгер не существует

# Создаем отдельные логгеры для каждого уровня
loggers = {}
for level, log_file in LOG_FILES.items():
    logger_obj = logging.getLogger(f"polls_bot.{level}")
    logger_obj.setLevel(logging.NOTSET)  # Логгер принимает все сообщения

    # Создаем handler для файла
    file_handler = logging.FileHandler(log_file, encoding='utf-8')
    file_handler.setLevel(getattr(logging, level.upper()))  # Handler фильтрует по уровню

    # Создаем форматтер
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    file_handler.setFormatter(formatter)

    # Добавляем handler к логгеру
    logger_obj.addHandler(file_handler)
    logger_obj.propagate = False  # Предотвращаем дублирование

    loggers[level] = logger_obj

class CustomLogger:
    """Кастомный логгер, который использует LogManager для проверки включения уровней и пишет только в нужный файл"""

    def __init__(self, name: str):
        self.name = name
        # Не используем self._logger, а всегда обращаемся к нужному логгеру по уровню

    def _should_log(self, level: str) -> bool:
        return LogManager.should_log(level)

    def debug(self, message: str):
        if self._should_log('debug'):
            logging.getLogger('polls_bot.debug').debug(message)

    def info(self, message: str):
        if self._should_log('info'):
            logging.getLogger('polls_bot.info').info(message)

    def warning(self, message: str):
        if self._should_log('warning'):
            logging.getLogger('polls_bot.warning').warning(message)

    def error(self, message: str, exc_info=False):
        if self._should_log('error'):
            logging.getLogger('polls_bot.error').error(message, exc_info=exc_info)

    def critical(self, message: str, exc_info=False):
        if self._should_log('critical'):
            logging.getLogger('polls_bot.critical').critical(message, exc_info=exc_info)

# Создаем кастомный логгер для использования в коде
logger = CustomLogger(__name__)

class LogManager:
    """Менеджер для управления логами"""

    # Список известных сторонних библиотек для управления их логгерами
    THIRD_PARTY_LOGGERS = {
        'telegram': 'telegram',
        'httpx': 'httpx',
        'httpcore': 'httpcore',  # Добавляем httpcore для управления его логированием
        'urllib3': 'urllib3',
        'asyncio': 'asyncio',
        'sqlite3': 'sqlite3',
        'aiohttp': 'aiohttp',
        'websockets': 'websockets',
        'requests': 'requests',
        'urllib': 'urllib',
        'ssl': 'ssl',
        'socket': 'socket'
    }

    @staticmethod
    def setup_third_party_loggers():
        """Настройка логгеров сторонних библиотек для подчинения нашей системе управления уровнями"""
        try:
            # Получаем текущую конфигурацию уровней
            config_file = f"{LOG_DIR}/logging_config.json"
            if os.path.exists(config_file):
                with open(config_file, 'r', encoding='utf-8') as f:
                    config = json.load(f)
            else:
                config = {level: True for level in LOG_FILES.keys()}

            # Определяем максимальный уровень логирования на основе включенных уровней
            enabled_levels = [level for level, enabled in config.items() if enabled]
            if not enabled_levels:
                # Если все уровни отключены, устанавливаем CRITICAL
                max_level = logging.CRITICAL
            else:
                # Находим самый низкий (наиболее подробный) включенный уровень
                level_mapping = {
                    'debug': logging.DEBUG,
                    'info': logging.INFO,
                    'warning': logging.WARNING,
                    'error': logging.ERROR,
                    'critical': logging.CRITICAL
                }
                max_level = min(level_mapping[level] for level in enabled_levels)

            # Настраиваем логгеры сторонних библиотек
            for logger_name in LogManager.THIRD_PARTY_LOGGERS.values():
                third_party_logger = logging.getLogger(logger_name)

                # Устанавливаем уровень логгера
                third_party_logger.setLevel(max_level)

                # Удаляем существующие handlers, чтобы избежать дублирования
                for handler in third_party_logger.handlers[:]:
                    third_party_logger.removeHandler(handler)

                # Добавляем наш кастомный handler только если есть включенные уровни
                if enabled_levels:
                    custom_handler = LogManager.ThirdPartyLogHandler()
                    custom_handler.setLevel(logging.DEBUG)  # Handler принимает все сообщения
                    third_party_logger.addHandler(custom_handler)

                # Отключаем propagate для предотвращения дублирования
                third_party_logger.propagate = False

            logger.info(f"Third-party loggers configured with max level: {logging.getLevelName(max_level)}")
            return True
        except Exception as e:
            logger.error(f"Error setting up third-party loggers: {e}")
            return False

    @staticmethod
    def update_third_party_loggers():
        """Обновить настройки логгеров сторонних библиотек при изменении конфигурации"""
        try:
            # Получаем текущую конфигурацию уровней
            config_file = f"{LOG_DIR}/logging_config.json"
            if os.path.exists(config_file):
                with open(config_file, 'r', encoding='utf-8') as f:
                    config = json.load(f)
            else:
                config = {level: True for level in LOG_FILES.keys()}

            # Определяем максимальный уровень логирования на основе включенных уровней
            enabled_levels = [level for level, enabled in config.items() if enabled]
            if not enabled_levels:
                # Если все уровни отключены, устанавливаем CRITICAL
                max_level = logging.CRITICAL
            else:
                # Находим самый низкий (наиболее подробный) включенный уровень
                level_mapping = {
                    'debug': logging.DEBUG,
                    'info': logging.INFO,
                    'warning': logging.WARNING,
                    'error': logging.ERROR,
                    'critical': logging.CRITICAL
                }
                max_level = min(level_mapping[level] for level in enabled_levels)

            # Обновляем настройки логгеров сторонних библиотек
            for logger_name in LogManager.THIRD_PARTY_LOGGERS.values():
                third_party_logger = logging.getLogger(logger_name)

                # Устанавливаем новый уровень логгера
                third_party_logger.setLevel(max_level)

                # Удаляем существующие handlers
                for handler in third_party_logger.handlers[:]:
                    third_party_logger.removeHandler(handler)

                # Добавляем наш кастомный handler только если есть включенные уровни
                if enabled_levels:
                    custom_handler = LogManager.ThirdPartyLogHandler()
                    custom_handler.setLevel(logging.DEBUG)
                    third_party_logger.addHandler(custom_handler)

                # Отключаем propagate
                third_party_logger.propagate = False

            logger.info(f"Third-party loggers updated with max level: {logging.getLevelName(max_level)}")
            return True
        except Exception as e:
            logger.error(f"Error updating third-party loggers: {e}")
            return False

    @staticmethod
    def get_third_party_loggers_status() -> dict:
        """Получить статус логгеров сторонних библиотек"""
        status = {}
        try:
            for display_name, logger_name in LogManager.THIRD_PARTY_LOGGERS.items():
                third_party_logger = logging.getLogger(logger_name)
                status[display_name] = {
                    'level': logging.getLevelName(third_party_logger.level),
                    'handlers_count': len(third_party_logger.handlers),
                    'propagate': third_party_logger.propagate
                }
        except Exception as e:
            logger.error(f"Error getting third-party loggers status: {e}")
        return status

    class ThirdPartyLogHandler(logging.Handler):
        """Кастомный handler для логгеров сторонних библиотек"""

        def emit(self, record):
            """Обработка лог-записи от сторонних библиотек"""
            try:
                # Определяем уровень записи
                level_name = logging.getLevelName(record.levelno).lower()

                # Маппинг уровней Python logging в наши уровни
                level_mapping = {
                    'debug': 'debug',
                    'info': 'info',
                    'warning': 'warning',
                    'error': 'error',
                    'critical': 'critical'
                }

                # Получаем соответствующий уровень
                mapped_level = level_mapping.get(level_name, 'info')

                # Проверяем, включен ли этот уровень в нашей системе
                if LogManager.should_log(mapped_level):
                    # Форматируем сообщение
                    message = self.format(record)

                    # Добавляем префикс для идентификации источника
                    prefixed_message = f"[{record.name}] {message}"

                    # Логируем в соответствующий файл
                    if mapped_level in LOG_FILES:
                        timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
                        log_entry = f"[{timestamp}] {level_name.upper()}: {prefixed_message}\n"

                        try:
                            with open(LOG_FILES[mapped_level], 'a', encoding='utf-8') as f:
                                f.write(log_entry)
                        except (IOError, OSError) as e:
                            # Если не удается записать в файл, логируем ошибку в консоль
                            print(f"Error writing to log file {mapped_level}: {e}")
            except Exception as e:
                # Fallback: логируем ошибку в консоль
                print(f"Error in ThirdPartyLogHandler: {e}")

    @staticmethod
    def get_log_size(level: Optional[str] = None) -> int:
        """Получить размер лог файла в байтах"""
        if level:
            if level in LOG_FILES and os.path.exists(LOG_FILES[level]):
                return os.path.getsize(LOG_FILES[level])
            return 0
        else:
            total_size = 0
            for log_file in LOG_FILES.values():
                if os.path.exists(log_file):
                    total_size += os.path.getsize(log_file)
            return total_size

    @staticmethod
    def get_log_stats() -> dict:
        """Получить статистику по логам"""
        stats = {}
        for level, log_file in LOG_FILES.items():
            if os.path.exists(log_file):
                size = os.path.getsize(log_file)
                stats[level] = {
                    'size_bytes': size,
                    'size_mb': round(size / (1024 * 1024), 2),
                    'lines': sum(1 for _ in open(log_file, 'r', encoding='utf-8'))
                }
            else:
                stats[level] = {'size_bytes': 0, 'size_mb': 0, 'lines': 0}
        return stats

    @staticmethod
    def clear_logs(level: Optional[str] = None) -> bool:
        """Очистить логи указанного уровня или все логи"""
        try:
            if level:
                if level in LOG_FILES:
                    with open(LOG_FILES[level], 'w', encoding='utf-8') as f:
                        f.write("")
                    return True
                return False
            else:
                # Очищаем все файлы логов
                for log_file in LOG_FILES.values():
                    with open(log_file, 'w', encoding='utf-8') as f:
                        f.write("")
                return True
        except Exception as e:
            logger.error(f"Error clearing logs: {e}")
            return False

    @staticmethod
    def rotate_logs(max_size_mb: int = 5) -> bool:
        """Ротация логов при превышении размера"""
        try:
            rotated = False
            for level, log_file in LOG_FILES.items():
                if os.path.exists(log_file):
                    size_mb = os.path.getsize(log_file) / (1024 * 1024)
                    if size_mb > max_size_mb:
                        # Создаем резервную копию
                        backup_file = f"{log_file}.{int(time.time())}"
                        os.rename(log_file, backup_file)

                        # Создаем новый пустой файл
                        with open(log_file, 'w', encoding='utf-8') as f:
                            f.write("")

                        # Удаляем старые резервные копии (оставляем только 5 последних)
                        backup_files = [f for f in os.listdir(LOG_DIR) if f.startswith(f"{os.path.basename(log_file)}.")]
                        backup_files.sort(reverse=True)
                        for old_backup in backup_files[5:]:
                            os.remove(os.path.join(LOG_DIR, old_backup))

                        rotated = True
                        logger.info(f"Rotated {level} log file (size: {size_mb:.2f}MB)")

            return rotated
        except Exception as e:
            logger.error(f"Error rotating logs: {e}")
            return False

    @staticmethod
    def get_recent_logs(level: str = 'info', lines: int = 50) -> list:
        """Получить последние строки лога"""
        try:
            if level in LOG_FILES and os.path.exists(LOG_FILES[level]):
                with open(LOG_FILES[level], 'r', encoding='utf-8') as f:
                    all_lines = f.readlines()
                    return all_lines[-lines:] if len(all_lines) > lines else all_lines
            return []
        except Exception as e:
            logger.error(f"Error reading recent logs: {e}")
            return []

    @staticmethod
    def toggle_logs(level: str) -> bool:
        """Включить/выключить логирование для определенного уровня"""
        try:
            config_file = f"{LOG_DIR}/logging_config.json"

            # Загружаем текущую конфигурацию
            if os.path.exists(config_file):
                with open(config_file, 'r', encoding='utf-8') as f:
                    config = json.load(f)
            else:
                config = {level: True for level in LOG_FILES.keys()}

            # Переключаем состояние
            config[level] = not config.get(level, True)

            # Сохраняем конфигурацию
            with open(config_file, 'w', encoding='utf-8') as f:
                json.dump(config, f, indent=2, ensure_ascii=False)

            # Обновляем настройки логгеров сторонних библиотек
            LogManager.update_third_party_loggers()

            logger.info(f"Logging for {level} {'enabled' if config[level] else 'disabled'}")
            return True
        except Exception as e:
            logger.error(f"Error toggling logs for {level}: {e}")
            return False

    @staticmethod
    def is_enabled(level: str) -> bool:
        """Проверить, включено ли логирование для определенного уровня"""
        try:
            config_file = f"{LOG_DIR}/logging_config.json"

            if os.path.exists(config_file):
                with open(config_file, 'r', encoding='utf-8') as f:
                    config = json.load(f)
                    return config.get(level, True)
            return True  # По умолчанию включено
        except Exception as e:
            logger.error(f"Error checking log status for {level}: {e}")
            return True

    @staticmethod
    def should_log(level: str) -> bool:
        """Проверить, нужно ли логировать сообщение определенного уровня"""
        return LogManager.is_enabled(level)

    @staticmethod
    def log_message(level: str, message: str):
        """Логировать сообщение с проверкой включения уровня"""
        if LogManager.should_log(level):
            try:
                if level in LOG_FILES:
                    timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
                    log_entry = f"[{timestamp}] {level.upper()}: {message}\n"

                    with open(LOG_FILES[level], 'a', encoding='utf-8') as f:
                        f.write(log_entry)
            except Exception as e:
                # Fallback to console if file logging fails
                logger.error(f"Log error: {e}")
                logger.error(f"[{level.upper()}] {message}")

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
            await update_or_query.edit_message_text(text)
        elif hasattr(update_or_query, 'message') and update_or_query.message:
            await update_or_query.message.reply_text(text)
        elif hasattr(update_or_query, 'effective_chat'):
            await update_or_query.effective_chat.send_message(text)
    except Exception as e:
        logger.error(f"Failed to send error message: {e}")

class RateLimiter:
    """Enhanced rate limiter with memory leak protection"""
    def __init__(self):
        self.requests = defaultdict(list)
        self.last_cleanup = time.time()

    def is_allowed(self, user_id: int, limit: int = 10) -> bool:
        now = time.time()

        if now - self.last_cleanup > 60:
            self.cleanup()
            self.last_cleanup = now

        user_reqs = self.requests[user_id]
        user_reqs[:] = [t for t in user_reqs if now - t < RATE_LIMIT_WINDOW]

        if len(user_reqs) >= limit:
            return False

        user_reqs.append(now)
        return True

    def is_user_flooding(self, user_id: int) -> bool:
        """Check if user is sending too many messages (anti-flooding)"""
        now = time.time()
        user_messages = self.requests[user_id]

        recent_messages = [t for t in user_messages if now - t < 60]
        if len(recent_messages) > 10:
            return True

        very_recent = [t for t in user_messages if now - t < 10]
        if len(very_recent) > 3:
            return True

        return False

    def cleanup(self):
        """Remove old entries and limit memory usage"""
        now = time.time()
        users_to_remove = []

        if len(self.requests) > MAX_USERS_IN_MEMORY:
            logger.warning(f"RateLimiter memory limit reached: {len(self.requests)} users")
            oldest_users = sorted(self.requests.items(),
                                key=lambda x: max(x[1]) if x[1] else 0)[:MAX_USERS_IN_MEMORY//2]
            for user_id, _ in oldest_users:
                del self.requests[user_id]
            logger.info(f"Removed {len(oldest_users)} oldest users from memory")

        for user_id in list(self.requests.keys()):
            self.requests[user_id][:] = [t for t in self.requests[user_id] if now - t < RATE_LIMIT_WINDOW]
            if not self.requests[user_id]:
                users_to_remove.append(user_id)

        for user_id in users_to_remove:
            del self.requests[user_id]

        if users_to_remove:
            logger.info(f"RateLimiter cleanup: removed {len(users_to_remove)} empty records")

class Database:
    """Enhanced database manager with proper error handling"""
    def __init__(self, db_path: str):
        self.db_path = db_path
        self.init_database()

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
            if conn:
                try:
                    conn.rollback()
                except sqlite3.Error:
                    pass
            raise
        except Exception as e:
            logger.error(f"Database connection error: {e}")
            if conn:
                try:
                    conn.rollback()
                except sqlite3.Error:
                    pass
            raise
        finally:
            if conn:
                try:
                    conn.close()
                except sqlite3.Error:
                    pass

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
        os.makedirs(BOT_DIR, exist_ok=True)

        with self.get_connection() as conn:
            conn.executescript("""
                CREATE TABLE IF NOT EXISTS users (
                    user_id INTEGER PRIMARY KEY,
                    username TEXT,
                    permissions TEXT DEFAULT 'use',
                    last_activity TEXT DEFAULT CURRENT_TIMESTAMP
                );

                CREATE TABLE IF NOT EXISTS templates (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    name TEXT NOT NULL,
                    question TEXT NOT NULL,
                    options TEXT NOT NULL,
                    description TEXT,
                    variables TEXT DEFAULT '[]',
                    created_by INTEGER,
                    usage_count INTEGER DEFAULT 0,
                    threshold INTEGER DEFAULT 50,
                    non_anonymous INTEGER DEFAULT 0,
                    max_participants INTEGER DEFAULT 0,
                    created_date TEXT DEFAULT CURRENT_TIMESTAMP
                );

                CREATE TABLE IF NOT EXISTS polls (
                    poll_id TEXT PRIMARY KEY,
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
                    total_voters INTEGER DEFAULT 0,
                    max_participants INTEGER DEFAULT 0,
                    decision_number INTEGER,
                    decision_status TEXT DEFAULT 'pending',
                    voting_type TEXT
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

                CREATE TABLE IF NOT EXISTS user_settings (
                    user_id INTEGER PRIMARY KEY,
                    settings TEXT
                );

                CREATE INDEX IF NOT EXISTS idx_polls_creator ON polls(creator_id);
                CREATE INDEX IF NOT EXISTS idx_sessions_user ON template_sessions(user_id);
                CREATE INDEX IF NOT EXISTS idx_user_states ON user_states(user_id);
                CREATE INDEX IF NOT EXISTS idx_sessions_created ON template_sessions(created_date);
                CREATE INDEX IF NOT EXISTS idx_polls_decision_number ON polls(decision_number);
            """)
            conn.commit()
            logger.info("Database initialized successfully")

def permission_required(permissions):
    """Enhanced decorator for permission checking (универсальный для update и callback_query)"""
    def decorator(func):
        @wraps(func)
        async def wrapper(self, update_or_query, context):
            user_id = self.get_user_id(update_or_query)
            user_perm = self.get_permissions(user_id)
            if user_perm not in permissions and user_perm != "admin":
                await self.send_message(update_or_query, "❌ Недостаточно прав для выполнения команды.")
                return
            rate_limit = self.config.get('rate_limit_hour', 10)
            if not self.rate_limiter.is_allowed(user_id, rate_limit):
                await self.send_message(update_or_query, "⚠️ Превышен лимит запросов. Попробуйте позже.")
                return
            return await func(self, update_or_query, context)
        return wrapper
    return decorator

class PollsBot:
    """Enhanced Telegram Polls Bot with Vote-style system"""
    BOT_VERSION = "2.0"

    def __init__(self):
        self.config = self._load_config()
        self.db = Database(DB_PATH)
        self.rate_limiter = RateLimiter()
        self.application = None
        self._cleanup_task = None
        self._write_pid()
        self.menus = self.Menus(self)

    class Menus:
        def __init__(self, bot):
            self.bot = bot

        def main_menu(self, user_id=None):
            # user_id нужен для показа админки
            buttons = [
                [InlineKeyboardButton("📊 Создать голосование", callback_data="create_poll")],
                [InlineKeyboardButton("📋 Шаблоны", callback_data="templates")],
                [InlineKeyboardButton("🗳️ Активные голосования", callback_data="active_polls")],
                [InlineKeyboardButton("🔒 Закрытые голосования", callback_data="closed_polls")],
            ]

            if user_id and self.bot.get_permissions(user_id) == "admin":
                buttons.append([InlineKeyboardButton("🛠 Админка", callback_data="admin")])
            buttons.append([InlineKeyboardButton("⚙️ Настройки отображения", callback_data="display_settings")])
            buttons.append([InlineKeyboardButton("ℹ️ Справка", callback_data="help")])
            return InlineKeyboardMarkup(buttons)

        def admin_menu(self):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("👥 Управление пользователями", callback_data="admin_users")],
                [InlineKeyboardButton("📊 Статистика системы", callback_data="admin_stats")],
                [InlineKeyboardButton("📋 Управление логами", callback_data="admin_logs")],
                [InlineKeyboardButton("🔙 Назад", callback_data="back_to_main")]
            ])

        def template_menu(self, templates, user_id):
            keyboard = []
            for template in templates[:10]:
                # Безопасно получаем ID шаблона
                template_id = template.get('id') or template.get('template_id') or str(template.get('name', ''))
                row = [InlineKeyboardButton(f"📊 {template['name']}", callback_data=f"use_tpl:{template_id}")]
                if user_id is not None and (
                    (template.get('created_by') == user_id) or (self.bot.get_permissions(user_id) == "admin")
                ):
                    row.append(InlineKeyboardButton("✏️ Изменить порог", callback_data=f"edit_tpl_threshold:{template_id}"))
                    row.append(InlineKeyboardButton("🗑️", callback_data=f"delete_tpl:{template_id}"))
                keyboard.append(row)
            if self.bot.get_permissions(user_id) in ["create", "admin"]:
                keyboard.append([InlineKeyboardButton("➕ Создать", callback_data="new_template")])
            keyboard.append([InlineKeyboardButton("⬅️ Назад", callback_data="back_to_main")])
            return InlineKeyboardMarkup(keyboard)

        def poll_options_menu(self, options):
            keyboard = [[InlineKeyboardButton(f"{i+1}. {opt}", callback_data=f"vote_option:{i}")]
                        for i, opt in enumerate(options)]
            return InlineKeyboardMarkup(keyboard)

        def finish_poll_menu(self):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("✅ Завершить создание", callback_data="finish_poll_creation")],
                [InlineKeyboardButton("⬅️ Назад", callback_data="back_to_main")]
            ])

        def finish_template_menu(self):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("✅ Завершить создание", callback_data="finish_template_creation")],
                [InlineKeyboardButton("⬅️ Назад", callback_data="back_to_main")]
            ])

        def back_to_templates_menu(self):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("⬅️ Назад", callback_data="back_to_templates")]
            ])

        def confirm_delete_template_menu(self, template_name):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("✅ Да, удалить", callback_data=f"confirm_delete_template:{template_name}")],
                [InlineKeyboardButton("❌ Отмена", callback_data="back_to_templates")]
            ])

        def continue_template_menu(self, template_name):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("⬅️ Назад", callback_data="back_to_templates"),
                 InlineKeyboardButton("➡️ Продолжить", callback_data=f"continue_tpl:{template_name}")]
            ])

        def close_poll_menu(self, poll_id):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("🔒 Закрыть голосование", callback_data=f"close_poll:{poll_id}")]
            ])

        def admin_users_menu(self):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("🔄 Обновить", callback_data="admin_users")],
                [InlineKeyboardButton("🔙 Назад", callback_data="admin_back")]
            ])

        def admin_stats_menu(self):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("🔄 Обновить", callback_data="admin_stats")],
                [InlineKeyboardButton("🔙 Назад", callback_data="admin_back")]
            ])

        def admin_back_menu(self):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("🔙 Назад", callback_data="admin_back")]
            ])

        def admin_setperm_menu(self, target_user_id):
            perms = [
                ("use", "👤 use"),
                ("create", "📝 create"),
                ("admin", "🛠 admin")
            ]
            perm_buttons = [InlineKeyboardButton(label, callback_data=f"admin_perm_select:{target_user_id}:{p}") for p, label in perms]
            keyboard = [perm_buttons[i:i+2] for i in range(0, len(perm_buttons), 2)]
            keyboard.append([InlineKeyboardButton("🔙 Назад", callback_data="admin_users")])
            return InlineKeyboardMarkup(keyboard)

        def admin_delete_menu(self, target_user_id):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("✅ Да, удалить", callback_data=f"admin_confirm_delete:{target_user_id}")],
                [InlineKeyboardButton("❌ Отмена", callback_data="admin_users")]
            ])

        def cancel_delete_menu(self):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("❌ Отмена", callback_data="cancel_delete")]
            ])

        def ask_variable_menu(self, session_id):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("❌ Отмена", callback_data=f"cancel:{session_id}")]
            ])

        def back_menu(self, to="main"):
            if to == "main":
                return InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Назад", callback_data="back_to_main")]])
            elif to == "templates":
                return InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Назад", callback_data="back_to_templates")]])
            else:
                return InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Назад", callback_data=f"back_to_{to}")]])

        def poll_type_menu(self):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("📊 Простое голосование", callback_data="create_simple")],
                [InlineKeyboardButton("📋 Голосование из шаблона", callback_data="create_from_template")],
                [InlineKeyboardButton("⬅️ Назад", callback_data="back_to_main")]
            ])

        def display_settings_menu(self, user_id, user_settings, config):
            opts = [
                ("show_author", "👤 Автор"),
                ("show_creation_date", "📅 Дата создания"),
                ("show_vote_count", "👥 Кол-во проголосовавших"),
                ("show_template", "🏷️ Шаблон"),
                ("show_decision_status", "🎯 Статус решения"),
                ("show_voter_names", "👥 Имена проголосовавших"),
                ("show_decision_numbers", "🔢 Номер решения"),
            ]
            keyboard = []
            for opt, label in opts:
                val = user_settings.get(opt, config.get(opt, True))
                btn = InlineKeyboardButton(f"{label}: {'✅' if val else '❌'}", callback_data=f"toggle_setting:{opt}")
                keyboard.append([btn])
            keyboard.append([InlineKeyboardButton("♻️ Сбросить к стандартным", callback_data="reset_settings")])
            keyboard.append([InlineKeyboardButton("⬅️ Назад", callback_data="back_to_main")])
            return InlineKeyboardMarkup(keyboard)

        def decision_number_menu(self, user_id):
            user_settings = self.bot.get_user_settings(user_id)
            last_num = user_settings.get('last_decision_number', 0)
            next_num = last_num + 1 if last_num else 1
            return InlineKeyboardMarkup([
                [InlineKeyboardButton('Ввести номер вручную', callback_data='enter_decision_number')],
                [InlineKeyboardButton(f'Следующий номер ({next_num})', callback_data='next_decision_number')],
                [InlineKeyboardButton('⬅️ Назад', callback_data='back_to_main')]
            ])



        def admin_logs_menu(self):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("📊 Статистика логов", callback_data="admin_logs_stats")],
                [InlineKeyboardButton("🧹 Очистить все логи", callback_data="admin_clear_all_logs")],
                [InlineKeyboardButton("🔧 Очистить по уровням", callback_data="admin_clear_logs_by_level")],
                [InlineKeyboardButton("📄 Последние логи", callback_data="admin_view_recent_logs")],
                [InlineKeyboardButton("🔄 Ротация логов", callback_data="admin_rotate_logs")],
                [InlineKeyboardButton("⚙️ Управление уровнями", callback_data="admin_logs_levels")],
                [InlineKeyboardButton("🔌 Статус сторонних логгеров", callback_data="admin_third_party_loggers")],
                [InlineKeyboardButton("🔙 Назад", callback_data="admin_back")]
            ])

        def admin_logs_levels_menu(self):
            """Меню управления уровнями логирования"""
            from polls_bot import LogManager

            keyboard = []
            for level in ['debug', 'info', 'warning', 'error', 'critical']:
                enabled = LogManager.is_enabled(level)
                status = "✅" if enabled else "❌"
                keyboard.append([
                    InlineKeyboardButton(
                        f"{status} {level.title()}",
                        callback_data=f"admin_toggle_logs:{level}"
                    )
                ])
            keyboard.append([InlineKeyboardButton("🔙 Назад", callback_data="admin_logs")])
            return InlineKeyboardMarkup(keyboard)

        def admin_clear_logs_by_level_menu(self):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("🐛 Debug", callback_data="admin_clear_logs:debug")],
                [InlineKeyboardButton("ℹ️ Info", callback_data="admin_clear_logs:info")],
                [InlineKeyboardButton("⚠️ Warning", callback_data="admin_clear_logs:warning")],
                [InlineKeyboardButton("❌ Error", callback_data="admin_clear_logs:error")],
                [InlineKeyboardButton("🚨 Critical", callback_data="admin_clear_logs:critical")],
                [InlineKeyboardButton("🔙 Назад", callback_data="admin_logs")]
            ])

        def admin_view_logs_menu(self):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("🐛 Debug", callback_data="admin_view_logs:debug")],
                [InlineKeyboardButton("ℹ️ Info", callback_data="admin_view_logs:info")],
                [InlineKeyboardButton("⚠️ Warning", callback_data="admin_view_logs:warning")],
                [InlineKeyboardButton("❌ Error", callback_data="admin_view_logs:error")],
                [InlineKeyboardButton("🚨 Critical", callback_data="admin_view_logs:critical")],
                [InlineKeyboardButton("🔙 Назад", callback_data="admin_logs")]
            ])

        def admin_rotate_logs_menu(self):
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("🔙 Назад", callback_data="admin_logs")]
            ])

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
            "auto_close_hours": 24,
            "show_poll_stats": True,
            "show_author": True,
            "show_template": True,
            "show_creation_date": True,
            "show_vote_count": True,
            "show_decision_status": True,
            "non_anonymous_voting": False,
            "show_voter_names": True,
            "show_decision_numbers": True,
            "max_voters_display": 5
        }

        if os.path.exists(CONFIG_PATH):
            try:
                with open(CONFIG_PATH, 'r', encoding='utf-8') as f:
                    config = json.load(f)
                    return {**defaults, **config}
            except Exception as e:
                logger.error(f"Config load error: {e}")

        return defaults

    def _write_pid(self):
        """Write PID file"""
        try:
            with open(PID_FILE, 'w') as f:
                f.write(str(os.getpid()))
            logger.info(f"PID file written: {os.getpid()}")
        except (OSError, IOError) as e:
            logger.warning(f"Could not write PID: {e}")

    async def validate_bot_token(self, token: str) -> bool:
        """Validate bot token format and accessibility"""
        if not token or not re.match(r'^\d+:[A-Za-z0-9_-]{35}$', token):
            logger.error("Invalid bot token format")
            return False

        try:
            app = Application.builder().token(token).build()
            async with app:
                bot_info = await app.bot.get_me()
                logger.info(f"Bot validated: {bot_info.username} ({bot_info.id})")
                return True
        except Exception as e:
            logger.error(f"Bot token validation failed: {e}")
            return False

    def validate_callback_data(self, data: str) -> bool:
        """Validate callback data against whitelist"""
        if not data or len(data) > 100:
            return False

        allowed_patterns = [
            # Основные меню
            r'^(create_poll|templates|active_polls|closed_polls|status|admin|help|display_settings|reset_settings)$',
            r'^(back_to_main|back_to_templates|back_to_\w+)$',
            
            # Создание опросов
            r'^(create_simple|create_from_template|new_template|finish_poll_creation|finish_template_creation)$',

            r'^(enter_decision_number|next_decision_number)$',
            
            # Шаблоны
            r'^use_tpl:\d+$',
            r'^continue_tpl:\d+$',
            r'^delete_tpl:\d+$',
            r'^confirm_delete_template:\d+$',
            r'^edit_tpl_threshold:\d+$',
            
            # Голосования
            r'^vote:[a-f0-9-]{36}:\d+$',
            r'^vote_option:\d+$',
            r'^close_poll:[a-f0-9-]{36}$',
            r'^edit_poll:[a-f0-9-]{36}$',
            r'^delete_poll:[a-f0-9-]{36}$',
            r'^confirm_delete_poll:[a-f0-9-]{36}$',
            r'^edit_poll_question:[a-f0-9-]{36}$',
            r'^edit_poll_options:[a-f0-9-]{36}$',
            r'^show_poll:[a-f0-9-]{36}$',
            r'^show_closed_poll:[a-f0-9-]{36}$',
            
            # Админка - пользователи
            r'^admin_(users|stats|back)$',
            r'^admin_setperm:\d+$',
            r'^admin_perm_select:\d+:(use|create|admin)$',
            r'^admin_revoke:\d+$',
            r'^admin_delete:\d+$',
            r'^admin_confirm_delete:\d+$',
            
            # Админка - логи
            r'^admin_(logs|logs_stats|clear_all_logs|clear_logs_by_level|view_recent_logs|rotate_logs|logs_levels|third_party_loggers)$',
            r'^admin_clear_logs:(debug|info|warning|error|critical)$',
            r'^admin_view_logs:(debug|info|warning|error|critical)$',
            r'^admin_toggle_logs:(debug|info|warning|error|critical)$',
            
            # Настройки
            r'^toggle_setting:[\w_]+$',
            
            # Отмена и подтверждения
            r'^cancel:[a-f0-9-]{36}$',
            r'^cancel_delete$',
            r'^confirm_delete:\d+$',
        ]

        return any(re.match(pattern, data) for pattern in allowed_patterns)

    # Utility methods
    def sanitize(self, text: str, max_len: int = 200) -> str:
        """Enhanced text sanitization"""
        if not text or not isinstance(text, str):
            return ""

        text = re.sub(r'[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]', '', text)
        text = re.sub(r'\s+', ' ', text.strip())

        return text[:max_len] if len(text) > max_len else text

    def clean_poll_option(self, option: str) -> str:
        """Clean poll option from markdown symbols and extra formatting"""
        if not option or not isinstance(option, str):
            return ""
        
        # Remove markdown symbols that can cause display issues
        cleaned = option.replace('**', '').replace('*', '').replace('`', '').replace('_', '')
        
        # Remove extra whitespace
        cleaned = re.sub(r'\s+', ' ', cleaned.strip())
        
        return cleaned

    def format_username_for_display(self, username: str) -> str:
        """Format username for display in Markdown, properly escaping special characters"""
        if not username:
            return ""
        
        # Remove @ if present for processing
        if username.startswith('@'):
            username = username[1:]
        
        # Escape Markdown special characters
        username = username.replace('_', '\\_').replace('*', '\\*').replace('`', '\\`')
        
        # Add @ back
        return f"@{username}"

    def extract_variables(self, text: str) -> List[str]:
        """Extract variables like {ФИО}, {Дата}, {email} (1-30 символов, любые буквы/цифры/_)"""
        variables = re.findall(r'\{([\w\sА-Яа-яЁёA-Za-z0-9@#\-\.,:;/!\?&%+=\'\"\(\)\[\]]{1,30})\}', text, re.UNICODE)
        return sorted(list(set(variables)))

    def substitute_variables(self, text: str, values: Dict[str, str]) -> str:
        """Replace variables with values and validate"""
        result = text
        for var, value in values.items():
            placeholder = f"{{{var}}}"
            if placeholder in result:
                result = result.replace(placeholder, str(value))
        # Найти все неразрешённые переменные
        remaining_vars = re.findall(r'\{([\w\sА-Яа-яЁёA-Za-z0-9@#\-\.,:;/!\?&%+=\'\"\(\)\[\]]{1,30})\}', result, re.UNICODE)
        if remaining_vars:
            logger.warning(f"Unresolved variables in template: {remaining_vars}")
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
        """Universal message sender with Markdown fallback"""
        logger.debug(f"send_message called: text='{text}', reply_markup={reply_markup}")
        for attempt in range(MAX_RETRIES):
            try:
                # Сначала пробуем отправить с Markdown
                if hasattr(update_or_query, 'edit_message_text'):
                    logger.debug(f"Calling edit_message_text with text='{text}' and reply_markup={reply_markup}")
                    await update_or_query.edit_message_text(
                        text,
                        parse_mode=ParseMode.MARKDOWN,
                        reply_markup=reply_markup
                    )
                elif hasattr(update_or_query, 'message') and update_or_query.message:
                    logger.debug(f"Calling reply_text with text='{text}' and reply_markup={reply_markup}")
                    await update_or_query.message.reply_text(
                        text,
                        parse_mode=ParseMode.MARKDOWN,
                        reply_markup=reply_markup
                    )
                elif hasattr(update_or_query, 'effective_chat'):
                    logger.debug(f"Calling send_message with text='{text}' and reply_markup={reply_markup}")
                    await update_or_query.effective_chat.send_message(
                        text,
                        parse_mode=ParseMode.MARKDOWN,
                        reply_markup=reply_markup
                    )
                else:
                    logger.error(f"Unknown update_or_query type: {type(update_or_query)}")
                    return False
                logger.debug("send_message success")
                return True

            except TelegramError as e:
                logger.error(f"TelegramError in send_message: {e}")
                if "can't parse entities" in str(e).lower() or "can't find end of the entity" in str(e).lower():
                    # Если ошибка парсинга Markdown - отправляем без форматирования
                    logger.warning(f"Markdown parse error, sending as plain text: {e}")
                    try:
                        # Очищаем текст от markdown символов
                        clean_text = text.replace('**', '').replace('`', '').replace('*', '').replace('_', '')
                        logger.debug(f"Fallback to plain text: '{clean_text}'")
                        if hasattr(update_or_query, 'edit_message_text'):
                            await update_or_query.edit_message_text(clean_text, reply_markup=reply_markup)
                        elif hasattr(update_or_query, 'message') and update_or_query.message:
                            await update_or_query.message.reply_text(clean_text, reply_markup=reply_markup)
                        elif hasattr(update_or_query, 'effective_chat'):
                            await update_or_query.effective_chat.send_message(clean_text, reply_markup=reply_markup)
                        else:
                            logger.error(f"Unknown update_or_query type in fallback: {type(update_or_query)}")
                            return False
                        logger.debug("send_message fallback success")
                        return True
                    except Exception as fallback_error:
                        logger.error(f"Fallback send failed: {fallback_error}")
                        if attempt < MAX_RETRIES - 1:
                            await asyncio.sleep(RETRY_DELAY)
                            continue
                        else:
                            return False
                else:
                    # Другие ошибки - повторяем попытку
                    if attempt < MAX_RETRIES - 1:
                        await asyncio.sleep(RETRY_DELAY)
                        continue
                    else:
                        logger.error(f"Failed to send message after {MAX_RETRIES} attempts: {e}")
                        return False

            except RetryAfter as e:
                logger.error(f"RetryAfter in send_message: {e}")
                if attempt < MAX_RETRIES - 1:
                    await asyncio.sleep(e.retry_after)
                    continue
                else:
                    logger.error(f"Max retries exceeded for send_message")
                    return False
            except Exception as e:
                logger.error(f"Exception in send_message: {e}")
                if attempt < MAX_RETRIES - 1:
                    await asyncio.sleep(RETRY_DELAY)
                    continue
                else:
                    logger.error(f"Failed to send message after {MAX_RETRIES} attempts: {e}")
                    return False

    # Decision logic
    def get_next_decision_number(self) -> int:
        """Get next decision number"""
        result = self.db.query("SELECT MAX(decision_number) FROM polls WHERE decision_number IS NOT NULL")
        if result and result[0][0]:
            return result[0][0] + 1
        return 1

    def assign_decision_number(self, poll_id: str) -> int:
        """Assign decision number to poll"""
        decision_number = self.get_next_decision_number()
        self.db.execute("UPDATE polls SET decision_number = ? WHERE poll_id = ?",
                       (decision_number, poll_id))
        return decision_number

    def determine_voting_type(self, options: List[str]) -> str:
        """Determine voting type based on options with improved detection"""
        try:
            # Расширенные ключевые слова для лучшего определения
            positive_keywords = [
                'за', 'да', 'одобрить', 'согласен', 'поддерживаю', 'принять', 'утвердить',
                'согласие', 'поддержка', 'одобрение', 'утверждение', 'принятие',
                'за', 'да', 'согласен', 'поддерживаю', 'принимаю', 'утверждаю',
                'положительно', 'в пользу', 'за принятие', 'за утверждение',
                'соглашаюсь', 'одобряю', 'поддерживаю', 'принимаю', 'утверждаю',
                'да', 'конечно', 'разумеется', 'безусловно', 'несомненно',
                'за', 'за!', 'за.', 'за,', 'за?', 'за...',
                'да', 'да!', 'да.', 'да,', 'да?', 'да...',
                'согласен', 'согласен!', 'согласен.', 'согласен,', 'согласен?',
                'одобряю', 'одобряю!', 'одобряю.', 'одобряю,', 'одобряю?',
                'поддерживаю', 'поддерживаю!', 'поддерживаю.', 'поддерживаю,',
                'принимаю', 'принимаю!', 'принимаю.', 'принимаю,', 'принимаю?',
                'утверждаю', 'утверждаю!', 'утверждаю.', 'утверждаю,', 'утверждаю?'
            ]
            
            negative_keywords = [
                'против', 'нет', 'отклонить', 'не согласен', 'отказать',
                'отклонение', 'отказ', 'несогласие', 'против принятия',
                'против', 'нет', 'не согласен', 'отклоняю', 'отказываю',
                'отрицательно', 'против принятия', 'против утверждения',
                'не согласен', 'не соглашаюсь', 'не одобряю', 'не поддерживаю',
                'не принимаю', 'не утверждаю', 'отклоняю', 'отказываю',
                'нет', 'не', 'ни', 'никогда', 'ни за что',
                'против', 'против!', 'против.', 'против,', 'против?', 'против...',
                'нет', 'нет!', 'нет.', 'нет,', 'нет?', 'нет...',
                'не согласен', 'не согласен!', 'не согласен.', 'не согласен,',
                'не одобряю', 'не одобряю!', 'не одобряю.', 'не одобряю,',
                'не поддерживаю', 'не поддерживаю!', 'не поддерживаю.', 'не поддерживаю,',
                'не принимаю', 'не принимаю!', 'не принимаю.', 'не принимаю,',
                'отклоняю', 'отклоняю!', 'отклоняю.', 'отклоняю,', 'отклоняю?',
                'отказываю', 'отказываю!', 'отказываю.', 'отказываю,', 'отказываю?'
            ]
            
            abstain_keywords = [
                'воздержался', 'воздержаться', 'нейтрально', 'не определился',
                'воздержание', 'нейтральная позиция', 'не определился',
                'воздержался', 'нейтрально', 'не определился', 'не знаю',
                'затрудняюсь ответить', 'не могу определиться',
                'воздержался', 'воздержался!', 'воздержался.', 'воздержался,', 'воздержался?',
                'воздержаться', 'воздержаться!', 'воздержаться.', 'воздержаться,',
                'нейтрально', 'нейтрально!', 'нейтрально.', 'нейтрально,', 'нейтрально?',
                'не определился', 'не определился!', 'не определился.', 'не определился,',
                'не знаю', 'не знаю!', 'не знаю.', 'не знаю,', 'не знаю?',
                'затрудняюсь', 'затрудняюсь ответить', 'затрудняюсь!', 'затрудняюсь.',
                'не могу определиться', 'не могу определиться!', 'не могу определиться.',
                'не определился', 'не определился!', 'не определился.', 'не определился,',
                'не определился?', 'не определился...',
                'не знаю', 'не знаю!', 'не знаю.', 'не знаю,', 'не знаю?', 'не знаю...',
                'затрудняюсь ответить', 'затрудняюсь ответить!', 'затрудняюсь ответить.',
                'не могу определиться', 'не могу определиться!', 'не могу определиться.',
                'нейтральная позиция', 'нейтральная позиция!', 'нейтральная позиция.',
                'воздержание', 'воздержание!', 'воздержание.', 'воздержание,'
            ]

            # Нормализуем варианты ответов и убираем дубликаты
            options_lower = []
            seen_options = set()
            
            for opt in options:
                if opt.strip():  # Пропускаем пустые варианты
                    normalized = opt.lower().strip()
                    # Убираем знаки препинания в конце для нормализации
                    normalized = normalized.rstrip('.,!?;:')
                    if normalized and normalized not in seen_options:
                        options_lower.append(normalized)
                        seen_options.add(normalized)
            
            if not options_lower:
                logger.warning("No valid options provided for voting type detection")
                return "choice"

            # Проверяем наличие ключевых слов в каждом варианте
            positive_matches = []
            negative_matches = []
            abstain_matches = []
            
            for i, option in enumerate(options_lower):
                # Проверяем точные совпадения и частичные совпадения
                option_words = option.split()  # Разбиваем на слова
                
                # Проверяем каждое слово в варианте
                for word in option_words:
                    # Нормализуем слово (убираем знаки препинания)
                    word_clean = word.strip('.,!?;:()[]{}"\'').lower()
                    
                    # Проверяем положительные ключевые слова
                    for keyword in positive_keywords:
                        if (keyword == word_clean or 
                            keyword in word_clean or 
                            word_clean in keyword or
                            keyword in option or 
                            option in keyword):
                            positive_matches.append(i)
                            break
                    if i in positive_matches:
                        break
                
                # Проверяем отрицательные ключевые слова
                if i not in positive_matches:
                    for word in option_words:
                        word_clean = word.strip('.,!?;:()[]{}"\'').lower()
                        for keyword in negative_keywords:
                            if (keyword == word_clean or 
                                keyword in word_clean or 
                                word_clean in keyword or
                                keyword in option or 
                                option in keyword):
                                negative_matches.append(i)
                                break
                        if i in negative_matches:
                            break
                
                # Проверяем нейтральные ключевые слова
                if i not in positive_matches and i not in negative_matches:
                    for word in option_words:
                        word_clean = word.strip('.,!?;:()[]{}"\'').lower()
                        for keyword in abstain_keywords:
                            if (keyword == word_clean or 
                                keyword in word_clean or 
                                word_clean in keyword or
                                keyword in option or 
                                option in keyword):
                                abstain_matches.append(i)
                                break
                        if i in abstain_matches:
                            break

            # Убираем дубликаты
            positive_matches = list(set(positive_matches))
            negative_matches = list(set(negative_matches))
            abstain_matches = list(set(abstain_matches))

            has_positive = len(positive_matches) > 0
            has_negative = len(negative_matches) > 0
            has_abstain = len(abstain_matches) > 0

            # Логируем для отладки
            logger.debug(f"Voting type detection: options={options}")
            logger.debug(f"Positive matches: {positive_matches}, Negative matches: {negative_matches}, Abstain matches: {abstain_matches}")
            logger.debug(f"Has positive: {has_positive}, Has negative: {has_negative}, Has abstain: {has_abstain}")

            # Определяем тип голосования с учетом количества вариантов
            num_options = len(options_lower)
            
            # Правило 1: Если вариантов ровно 2 и есть "за" и "против" - бинарное голосование
            if num_options == 2 and has_positive and has_negative:
                logger.info(f"Detected binary voting type (2 options with за/против) for options: {options}")
                return "binary"
            
            # Правило 2: Если вариантов 3 и есть "за", "против", "воздержался" - approval
            elif num_options == 3 and has_positive and has_negative and has_abstain:
                logger.info(f"Detected approval voting type (3 options with за/против/воздержался) for options: {options}")
                return "approval"
            
            # Правило 3: Если вариантов больше 3 - всегда обычный выбор
            elif num_options > 3:
                logger.info(f"Detected choice voting type (more than 3 options) for options: {options}")
                return "choice"
            
            # Дополнительные правила для случаев, когда количество не соответствует стандартным схемам
            elif has_positive and has_negative and has_abstain:
                logger.info(f"Detected approval voting type (keywords match) for options: {options}")
                return "approval"  # За/против/воздержался
            elif has_positive and has_negative:
                logger.info(f"Detected binary voting type (keywords match) for options: {options}")
                return "binary"    # За/против
            else:
                logger.info(f"Detected choice voting type (default) for options: {options}")
                return "choice"    # Обычный выбор
                
        except Exception as e:
            logger.error(f"Error in determine_voting_type: {e}")
            return "choice"  # По умолчанию обычный выбор

    def check_decision_status(self, poll_id: str) -> Dict:
        """Check decision status based on threshold and voting type"""
        try:
            poll_data = self.db.query("""
                SELECT threshold, total_voters, options, voting_type, status, max_participants FROM polls WHERE poll_id = ?
            """, (poll_id,))

            if not poll_data:
                return {"status": "unknown", "percentage": 0, "threshold": 50}

            threshold, total_voters, options_str, saved_voting_type, poll_status, max_participants = poll_data[0]
            options = options_str.split('|')

            if total_voters == 0:
                return {"status": "pending", "percentage": 0, "threshold": threshold}

            # Get vote counts for each option
            votes_data = self.db.query("""
                SELECT option_id, COUNT(*) as vote_count
                FROM poll_votes WHERE poll_id = ?
                GROUP BY option_id ORDER BY vote_count DESC
            """, (poll_id,))

            if not votes_data:
                return {"status": "pending", "percentage": 0, "threshold": threshold}

            # Use saved voting type or determine automatically
            voting_type = saved_voting_type if saved_voting_type else self.determine_voting_type(options)

            # Find the option with the most votes
            max_votes = votes_data[0][1]
            max_option_id = votes_data[0][0]
            max_option_text = options[max_option_id]

            # Calculate percentage based on voting type
            if voting_type == "approval":
                # For approval voting (за/против/воздержался), only "за" votes count for approval
                positive_keywords = ['за', 'да', 'одобрить', 'согласен', 'поддерживаю', 'принять', 'утвердить']
                is_positive_option = any(keyword in max_option_text.lower() for keyword in positive_keywords)

                if is_positive_option:
                    base_count = max_participants if max_participants and max_participants > 0 else total_voters
                    percentage = (max_votes / base_count) * 100
                    # Decision is accepted only if positive option gets enough votes
                    if percentage >= threshold - 0.5: # Допуск 0.5%
                        status = "accepted"
                    else:
                        # Для закрытых голосований всегда "rejected" при недоборе
                        if poll_status == 'closed':
                            status = "rejected"
                        else:
                            status = "rejected" if total_voters >= 3 else "pending"
                else:
                    # If negative option has most votes, decision is rejected
                    percentage = (max_votes / total_voters) * 100
                    if poll_status == 'closed':
                        status = "rejected"
                    else:
                        status = "rejected" if total_voters >= 3 else "pending"

            elif voting_type == "binary":
                # For binary voting (за/против), check if positive option wins
                positive_keywords = ['за', 'да', 'одобрить', 'согласен', 'поддерживаю', 'принять', 'утвердить']
                is_positive_option = any(keyword in max_option_text.lower() for keyword in positive_keywords)

                base_count = max_participants if max_participants and max_participants > 0 else total_voters
                percentage = (max_votes / base_count) * 100
                if is_positive_option and percentage >= threshold:
                    status = "accepted"
                else:
                    # Для закрытых голосований всегда "rejected" при недоборе
                    if poll_status == 'closed':
                        status = "rejected"
                    else:
                        status = "rejected" if total_voters >= 3 else "pending"

            else:
                # For choice voting, use original logic
                base_count = max_participants if max_participants and max_participants > 0 else total_voters
                percentage = (max_votes / base_count) * 100
                if percentage >= threshold - 0.5:  # Допуск 0.5%
                    status = "accepted"
                else:
                    # Для закрытых голосований всегда "rejected" при недоборе
                    if poll_status == 'closed':
                        status = "rejected"
                    else:
                        status = "rejected" if total_voters >= 3 else "pending"

            return {
                "status": status,
                "percentage": percentage,
                "threshold": threshold,
                "max_option_id": max_option_id,
                "max_votes": max_votes,
                "total_voters": total_voters,
                "voting_type": voting_type,
                "max_option_text": max_option_text,
                "max_participants": max_participants
            }

        except Exception as e:
            logger.error(f"Error checking decision status: {e}")
            return {"status": "error", "percentage": 0, "threshold": 50}

    def format_poll_message(self, poll_id: str, show_results: bool = True, for_user_id: int = 0) -> Tuple[str, InlineKeyboardMarkup]:
        """Format poll message with results (Vote-style)"""
        try:
            logger.info(f"format_poll_message called for poll_id: {poll_id}, for_user_id: {for_user_id}")

            # Получаем индивидуальные настройки пользователя (если for_user_id > 0)
            if for_user_id:
                user_settings = self.get_user_settings(for_user_id)
                logger.debug(f"Formatting poll {poll_id} for user {for_user_id} with settings: {user_settings}")
            else:
                user_settings = {}
                logger.debug(f"Formatting poll {poll_id} with default settings")
            def get_opt(opt):
                return user_settings.get(opt, self.config.get(opt, True))

            # Get poll data
            logger.info("Querying poll data from database...")
            poll_data = self.db.query("""
                SELECT question, options, threshold, non_anonymous, decision_number,
                       created_date, template_used, creator_id, decision_status, status, max_participants
                FROM polls WHERE poll_id = ?
            """, (poll_id,))

            # Проверяем, что данные опроса найдены
            if not poll_data:
                logger.error(f"Poll {poll_id} not found in database")
                return "❌ Голосование не найдено", InlineKeyboardMarkup([[]])

            logger.info(f"Poll data found: {len(poll_data)} rows")
            poll_data = poll_data[0]  # Берем первую (и единственную) запись

            question, options_str, threshold, non_anonymous, decision_number, \
            created_date, template_used, creator_id, decision_status, status, max_participants = poll_data

            logger.info(f"Question: {question[:50]}..., Options: {options_str[:50]}..., Status: {status}")

            options = options_str.split('|')
            logger.info(f"Split options: {options}")

            # Get votes data
            logger.info("Querying votes data...")
            votes_data = self.db.query("""
                SELECT option_id, username FROM poll_votes
                WHERE poll_id = ? ORDER BY vote_date
            """, (poll_id,))

            logger.info(f"Votes data: {len(votes_data)} votes")

            # Group votes by option
            votes_by_option = defaultdict(list)
            for option_id, username in votes_data:
                votes_by_option[option_id].append(username)

            total_votes = len(votes_data)
            logger.info(f"Total votes: {total_votes}")

            # Build message - убираем "📊 Вопрос: " из начала
            text = f"**{question}**\n\n"

            max_votes = 0
            for option_votes in votes_by_option.values():
                if len(option_votes) > max_votes:
                    max_votes = len(option_votes)

            # Объединенная статистика и порог в одну строку
            if status != 'closed':
                # Определяем тип голосования и находим голоса "за"
                voting_type = self.determine_voting_type(options)
                
                if voting_type in ["approval", "binary"]:
                    # Для approval/binary подсчитываем только голоса "за"
                    positive_keywords = ['за', 'да', 'одобрить', 'согласен', 'поддерживаю', 'принять', 'утвердить']
                    positive_votes = 0
                    
                    for i, option in enumerate(options):
                        if any(keyword in option.lower() for keyword in positive_keywords):
                            option_voters = votes_by_option.get(i, [])
                            positive_votes = len(option_voters)
                            break
                    
                    current_votes = positive_votes
                else:
                    # Для обычного выбора используем максимальные голоса
                    current_votes = max_votes

                if max_participants and max_participants > 0:
                    needed_votes = max(1, int((threshold * max_participants) / 100))
                    percent = int((total_votes / max_participants) * 100)
                    text += f" {threshold}% порог ({needed_votes}/{max_participants}) | 👥 {total_votes} голосов ({percent}%) | ✅ {current_votes}/{needed_votes}\n\n"
                else:
                    # Исправляем формулу для случая без max_participants - убираем +1
                    needed_votes = max(1, int((threshold * total_votes) / 100))
                    text += f" {threshold}% порог | 👥 {total_votes} голосов | ✅ {current_votes}/{needed_votes}\n\n"

            # Build keyboard and results
            keyboard = []
            logger.info("Building keyboard and results...")

            # Проверяем, является ли голосование закрытым
            is_closed = status == 'closed'

            if show_results and votes_data:
                text += "🗳️ **Результаты голосования:**\n\n"

                for i, option in enumerate(options):
                    voters = votes_by_option.get(i, [])
                    count = len(voters)
                    percentage = (count / total_votes * 100) if total_votes > 0 else 0

                    # Emoji for option
                    if "да" in option.lower() or "за" in option.lower():
                        emoji = "✅"
                    elif "нет" in option.lower() or "против" in option.lower():
                        emoji = "❌"
                    elif "воздерж" in option.lower():
                        emoji = "🟡"
                    else:
                        emoji = f"{i+1}️⃣"

                    text += f"**{emoji} {option.replace('**', '')}** - {count} голос"
                    if count != 1:
                        text += "ов"
                    text += f" ({percentage:.0f}%)\n"

                    # Show voter names if enabled
                    if get_opt('show_voter_names') and voters:
                        max_display = user_settings.get('max_voters_display', self.config.get('max_voters_display', 5))
                        displayed_voters = voters[:max_display]
                        # Используем вспомогательную функцию для правильного форматирования никнеймов
                        formatted_voters = [self.format_username_for_display(v) for v in displayed_voters]
                        voters_text = ", ".join(formatted_voters)

                        if len(voters) > max_display:
                            voters_text += f" и еще {len(voters) - max_display}"

                        text += f"    👥 {voters_text}\n"
                    elif voters:
                        text += f"    👥 {count} человек\n"
                    else:
                        text += f"    👥 —\n"

                    text += "\n"

                    # Add vote button only if poll is not closed
                    if not is_closed:
                        button_text = f"{emoji} {option.replace('**', '')}"
                        if count > 0:
                            button_text += f" ({count})"

                        keyboard.append([InlineKeyboardButton(
                            button_text,
                            callback_data=f"vote:{poll_id}:{i}"
                        )])
            else:
                # No results yet, just show voting buttons (only if poll is not closed)
                if not is_closed:
                    for i, option in enumerate(options):
                        emoji = f"{i+1}️⃣"
                        if "да" in option.lower() or "за" in option.lower():
                            emoji = "✅"
                        elif "нет" in option.lower() or "против" in option.lower():
                            emoji = "❌"
                        elif "воздерж" in option.lower():
                            emoji = "🟡"

                        keyboard.append([InlineKeyboardButton(
                            f"{emoji} {option.replace('**', '')}",
                            callback_data=f"vote:{poll_id}:{i}"
                        )])

            logger.info(f"Keyboard built with {len(keyboard)} rows")

            # Check and show decision status
            if show_results and total_votes > 0:
                logger.info("Checking decision status...")
                decision_info = self.check_decision_status(poll_id)
                logger.info(f"Decision info: {decision_info}")

                if get_opt('show_decision_status'):
                    if decision_info['status'] == 'accepted':
                        status_text = "✅ **Решение"
                        if get_opt('show_decision_numbers') and decision_number:
                            status_text += f" №{decision_number}"

                        # Добавляем информацию о типе голосования
                        if decision_info.get('voting_type') == 'approval':
                            status_text += f" принято**"
                        elif decision_info.get('voting_type') == 'binary':
                            status_text += f" принято**"
                        else:
                            status_text += f" принято**"

                        text += f"\n{status_text}\n\n"

                        # Assign decision number if not assigned
                        if not decision_number:
                            self.assign_decision_number(poll_id)
                            self.db.execute("UPDATE polls SET decision_status = ? WHERE poll_id = ?",
                                          ('accepted', poll_id))

                    elif decision_info['status'] == 'rejected' and (total_votes >= 3 or status == 'closed'):
                        status_text = "❌ **Решение"
                        if get_opt('show_decision_numbers') and decision_number:
                            status_text += f" №{decision_number}"

                        # Добавляем информацию о типе голосования
                        if decision_info.get('voting_type') == 'approval':
                            status_text += f" не принято**"
                        elif decision_info.get('voting_type') == 'binary':
                            status_text += f" не принято**"
                        else:
                            status_text += f" не принято**"

                        text += f"\n{status_text}\n\n"

                        # Assign decision number if not assigned
                        if not decision_number:
                            self.assign_decision_number(poll_id)
                            self.db.execute("UPDATE polls SET decision_status = ? WHERE poll_id = ?",
                                          ('rejected', poll_id))


                    else:
                        text += f"\n⏳ **Голосование продолжается**\n"

                    # Add closed status indicator after decision status
                    if status == 'closed':
                        text += "🔒 **Голосование закрыто**\n"

            # Show additional info if enabled
            info_parts = []
            if get_opt('show_vote_count') and total_votes > 0:
                info_parts.append(f"👥 **{total_votes} человек** проголосовали")

            if get_opt('show_creation_date'):
                try:
                    created_dt = datetime.fromisoformat(created_date.replace('Z', '+00:00'))
                    info_parts.append(f"📅 Создан: {created_dt.strftime('%d.%m.%Y %H:%M')}")
                except:
                    info_parts.append(f"📅 Создан: {created_date}")

            if get_opt('show_template') and template_used:
                info_parts.append(f"🏷️ Шаблон: `{template_used}`")

            if get_opt('show_author'):
                info_parts.append(f"👤 Автор: {creator_id}")

            if info_parts:
                text += f"\n{' • '.join(info_parts)}\n"

            # Add share button - только для создателя и админов
            if for_user_id == creator_id or self.get_permissions(for_user_id) == "admin":
                keyboard.append([InlineKeyboardButton(
                    "🌎 Поделиться голосованием",
                    switch_inline_query=f"share_{poll_id}"
                )])

                # Add admin controls - только для создателя и админов, и только если голосование не закрыто
                if not is_closed:
                    keyboard.append([InlineKeyboardButton(
                        "🔒 Закрыть голосование",
                        callback_data=f"close_poll:{poll_id}"
                    )])
                    # Add edit and delete buttons
                    keyboard.append([
                        InlineKeyboardButton("✏️ Редактировать", callback_data=f"edit_poll:{poll_id}"),
                        InlineKeyboardButton("🗑️ Удалить", callback_data=f"delete_poll:{poll_id}")
                    ])

            logger.info(f"format_poll_message completed successfully. Text length: {len(text)}, Keyboard rows: {len(keyboard)}")
            return text, InlineKeyboardMarkup(keyboard)

        except Exception as e:
            logger.error(f"Error formatting poll message: {e}", exc_info=True)
            logger.debug(f"Error in format_poll_message for poll {poll_id}: {e}")
            return "❌ Ошибка отображения опроса", InlineKeyboardMarkup([[]])

    def format_poll_message_public(self, poll_id: str, show_results: bool = True, for_user_id: int = 0) -> Tuple[str, InlineKeyboardMarkup]:
        """Format poll message for public sharing (without admin controls)"""
        try:
            logger.info(f"format_poll_message_public called for poll_id: {poll_id}, for_user_id: {for_user_id}")

            # Получаем индивидуальные настройки пользователя (если for_user_id > 0)
            if for_user_id:
                user_settings = self.get_user_settings(for_user_id)
                logger.debug(f"Formatting public poll {poll_id} for user {for_user_id} with settings: {user_settings}")
            else:
                user_settings = {}
                logger.debug(f"Formatting public poll {poll_id} with default settings")

            def get_opt(opt):
                return user_settings.get(opt, self.config.get(opt, True))

            # Get poll data
            logger.info("Querying poll data from database...")
            poll_data = self.db.query("""
                SELECT question, options, threshold, non_anonymous, decision_number,
                       created_date, template_used, creator_id, decision_status, voting_type, status, max_participants
                FROM polls WHERE poll_id = ?
            """, (poll_id,))

            if not poll_data:
                logger.error(f"Poll {poll_id} not found")
                return "❌ Голосование не найдено", InlineKeyboardMarkup([[]])

            question, options_str, threshold, non_anonymous, decision_number, \
            created_date, template_used, creator_id, decision_status, voting_type, status, max_participants = poll_data[0]

            logger.info(f"Question: {question[:50]}..., Options: {options_str[:50]}..., Status: {status}")

            options = options_str.split('|')
            logger.info(f"Split options: {options}")

            # Get votes data
            logger.info("Querying votes data...")
            votes_data = self.db.query("""
                SELECT option_id, username FROM poll_votes
                WHERE poll_id = ? ORDER BY vote_date
            """, (poll_id,))

            logger.info(f"Votes data: {len(votes_data)} votes")

            # Group votes by option
            votes_by_option = defaultdict(list)
            for option_id, username in votes_data:
                votes_by_option[option_id].append(username)

            total_votes = len(votes_data)
            logger.info(f"Total votes: {total_votes}")

            # Build message - убираем "📊 Вопрос: " из начала
            text = f"**{question}**\n\n"

            max_votes = 0
            for option_votes in votes_by_option.values():
                if len(option_votes) > max_votes:
                    max_votes = len(option_votes)

            # Объединенная статистика и порог в одну строку
            if status != 'closed':
                # Определяем тип голосования и находим голоса "за"
                voting_type = self.determine_voting_type(options)
                
                if voting_type in ["approval", "binary"]:
                    # Для approval/binary подсчитываем только голоса "за"
                    positive_keywords = ['за', 'да', 'одобрить', 'согласен', 'поддерживаю', 'принять', 'утвердить']
                    positive_votes = 0
                    
                    for i, option in enumerate(options):
                        if any(keyword in option.lower() for keyword in positive_keywords):
                            option_voters = votes_by_option.get(i, [])
                            positive_votes = len(option_voters)
                            break
                    
                    current_votes = positive_votes
                else:
                    # Для обычного выбора используем максимальные голоса
                    current_votes = max_votes

                if max_participants and max_participants > 0:
                    needed_votes = max(1, int((threshold * max_participants) / 100))
                    percent = int((total_votes / max_participants) * 100)
                    text += f" {threshold}% порог ({needed_votes}/{max_participants}) | 👥 {total_votes} голосов ({percent}%) | ✅ {current_votes}/{needed_votes}\n\n"
                else:
                    # Исправляем формулу для случая без max_participants - убираем +1
                    needed_votes = max(1, int((threshold * total_votes) / 100))
                    text += f" {threshold}% порог | 👥 {total_votes} голосов | ✅ {current_votes}/{needed_votes}\n\n"

            # Build keyboard and results
            keyboard = []
            logger.info("Building keyboard and results...")

            # Проверяем, является ли голосование закрытым
            is_closed = status == 'closed'

            if show_results and votes_data:
                text += "🗳️ **Результаты голосования:**\n\n"

                for i, option in enumerate(options):
                    voters = votes_by_option.get(i, [])
                    count = len(voters)
                    percentage = (count / total_votes * 100) if total_votes > 0 else 0

                    # Emoji for option
                    if "да" in option.lower() or "за" in option.lower():
                        emoji = "✅"
                    elif "нет" in option.lower() or "против" in option.lower():
                        emoji = "❌"
                    elif "воздерж" in option.lower():
                        emoji = "🟡"
                    else:
                        emoji = f"{i+1}️⃣"

                    text += f"**{emoji} {option.replace('**', '')}** - {count} голос"
                    if count != 1:
                        text += "ов"
                    text += f" ({percentage:.0f}%)\n"

                    # Show voter names if enabled
                    if get_opt('show_voter_names') and voters:
                        max_display = user_settings.get('max_voters_display', self.config.get('max_voters_display', 5))
                        displayed_voters = voters[:max_display]
                        # Используем вспомогательную функцию для правильного форматирования никнеймов
                        formatted_voters = [self.format_username_for_display(v) for v in displayed_voters]
                        voters_text = ", ".join(formatted_voters)

                        if len(voters) > max_display:
                            voters_text += f" и еще {len(voters) - max_display}"

                        text += f"    👥 {voters_text}\n"
                    elif voters:
                        text += f"    👥 {count} человек\n"
                    else:
                        text += f"    👥 —\n"

                    text += "\n"

                    # Add vote button only if poll is not closed
                    if not is_closed:
                        button_text = f"{emoji} {option.replace('**', '')}"
                        if count > 0:
                            button_text += f" ({count})"

                        keyboard.append([InlineKeyboardButton(
                            button_text,
                            callback_data=f"vote:{poll_id}:{i}"
                        )])
            else:
                # No results yet, just show voting buttons (only if poll is not closed)
                if not is_closed:
                    for i, option in enumerate(options):
                        emoji = f"{i+1}️⃣"
                        if "да" in option.lower() or "за" in option.lower():
                            emoji = "✅"
                        elif "нет" in option.lower() or "против" in option.lower():
                            emoji = "❌"
                        elif "воздерж" in option.lower():
                            emoji = "🟡"

                        keyboard.append([InlineKeyboardButton(
                            f"{emoji} {option.replace('**', '')}",
                            callback_data=f"vote:{poll_id}:{i}"
                        )])

            logger.info(f"Keyboard built with {len(keyboard)} rows")

            # Check and show decision status
            if show_results and total_votes > 0:
                logger.info("Checking decision status...")
                decision_info = self.check_decision_status(poll_id)
                logger.info(f"Decision info: {decision_info}")

                if get_opt('show_decision_status'):
                    if decision_info['status'] == 'accepted':
                        status_text = "✅ **Решение"
                        if get_opt('show_decision_numbers') and decision_number:
                            status_text += f" №{decision_number}"

                        # Добавляем информацию о типе голосования
                        if decision_info.get('voting_type') == 'approval':
                            status_text += f" принято**"
                        elif decision_info.get('voting_type') == 'binary':
                            status_text += f" принято**"
                        else:
                            status_text += f" принято**"

                        text += f"\n{status_text}\n\n"

                    elif decision_info['status'] == 'rejected' and (total_votes >= 3 or status == 'closed'):
                        status_text = "❌ **Решение"
                        if get_opt('show_decision_numbers') and decision_number:
                            status_text += f" №{decision_number}"

                        # Добавляем информацию о типе голосования
                        if decision_info.get('voting_type') == 'approval':
                            status_text += f" не принято**"
                        elif decision_info.get('voting_type') == 'binary':
                            status_text += f" не принято**"
                        else:
                            status_text += f" не принято**"

                        text += f"\n{status_text}\n\n"
                    else:
                        text += f"\n⏳ **Голосование продолжается**\n"

                    # Add closed status indicator after decision status
                    if status == 'closed':
                        text += "🔒 **Голосование закрыто**\n"

            # Show additional info if enabled
            info_parts = []
            if get_opt('show_vote_count') and total_votes > 0:
                info_parts.append(f"👥 **{total_votes} человек** проголосовали")

            if get_opt('show_creation_date'):
                try:
                    created_dt = datetime.fromisoformat(created_date.replace('Z', '+00:00'))
                    info_parts.append(f"📅 Создан: {created_dt.strftime('%d.%m.%Y %H:%M')}")
                except:
                    info_parts.append(f"📅 Создан: {created_date}")

            if get_opt('show_template') and template_used:
                info_parts.append(f"🏷️ Шаблон: `{template_used}`")

            if get_opt('show_author'):
                info_parts.append(f"👤 Автор: {creator_id}")

            if info_parts:
                text += f"\n{' • '.join(info_parts)}\n"

            # НЕ добавляем админские кнопки в публичную версию
            logger.info(f"format_poll_message_public completed successfully. Text length: {len(text)}, Keyboard rows: {len(keyboard)}")
            return text, InlineKeyboardMarkup(keyboard)

        except Exception as e:
            logger.error(f"Error formatting public poll message: {e}", exc_info=True)
            logger.debug(f"Error in format_poll_message_public for poll {poll_id}: {e}")
            return "❌ Ошибка отображения опроса", InlineKeyboardMarkup([[]])

    # Enhanced user state management (database-backed)
    def get_user_state(self, user_id: int) -> Dict:
        """Get user state from database"""
        try:
            result = self.db.query("SELECT state, data FROM user_states WHERE user_id = ?", (user_id,))
            if result:
                state_data = json.loads(result[0][1]) if result[0][1] else {}
                return {"state": result[0][0], "data": state_data}
            return {"state": UserState.IDLE, "data": {}}
        except (Exception, json.JSONDecodeError) as e:
            logger.error(f"Get user state error: {e}")
            return {"state": UserState.IDLE, "data": {}}

    def set_user_state(self, user_id: int, state: str, data: Optional[Dict] = None):
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
        self.set_user_state(user_id, UserState.IDLE, {})

    # User management
    def get_permissions(self, user_id: int) -> str:
        """Get user permissions with safe result handling"""
        try:
            result = self.db.query("SELECT permissions FROM users WHERE user_id = ?", (user_id,))
            if result and len(result) > 0 and len(result[0]) > 0:
                return result[0][0]
            return "none"
        except Exception as e:
            logger.error(f"Error getting permissions for user {user_id}: {e}")
            return "none"

    async def is_user_in_chat(self, user_id: int, chat_id: int, context) -> bool:
        """Check if user is a member of the chat"""
        try:
            chat_member = await context.bot.get_chat_member(chat_id, user_id)
            return chat_member.status not in ['left', 'kicked']
        except Exception as e:
            logger.warning(f"Failed to check chat membership for user {user_id} in chat {chat_id}: {e}")
            # If we can't check membership, allow access for safety
            return True

    def add_user(self, user_id: int, username: str, permissions: str = "use"):
        """Add or update user with validation. Не понижать права, если уже выше."""
        try:
            username = self.sanitize(username, 50)
            # Получаем текущие права
            current = self.db.query("SELECT permissions FROM users WHERE user_id = ?", (user_id,))
            if current:
                current_perm = current[0][0]
                # Если текущие права выше, не понижаем
                perm_order = ["none", "use", "create", "admin"]
                if perm_order.index(permissions) < perm_order.index(current_perm):
                    permissions = current_perm
            self.db.execute(
                """
                INSERT OR REPLACE INTO users (user_id, username, permissions, last_activity)
                VALUES (?, ?, ?, ?)
                """,
                (user_id, username, permissions, datetime.now().isoformat())
            )
        except Exception as e:
            logger.error(f"Add user error: {e}")

    # Template management (same as before, keeping existing methods)
    def get_templates(self) -> List[Dict]:
        """Get all templates with safe result handling"""
        try:
            results = self.db.query("SELECT * FROM templates ORDER BY usage_count DESC")
            templates = []
            for row in results:
                template = dict(row)
                try:
                    template['variables'] = json.loads(template.get('variables', '[]'))
                except json.JSONDecodeError:
                    template['variables'] = []
                templates.append(template)
            return templates
        except Exception as e:
            logger.error(f"Get templates error: {e}")
            return []

    def get_active_polls(self, user_id: Optional[int] = None, limit: int = 5) -> List[Dict]:
        """Получить список активных опросов с учетом прав пользователя"""
        try:
            logger.debug(f"Getting active polls for user {user_id} with limit {limit}")

            if user_id is None:
                # Если user_id не передан, возвращаем все активные голосования (для админов)
                results = self.db.query(
                    "SELECT poll_id, question, options, created_date FROM polls WHERE status = 'active' ORDER BY created_date DESC LIMIT ?",
                    (limit,)
                )
            else:
                user_perm = self.get_permissions(user_id)

                if user_perm == "admin":
                    # Администратор видит все активные голосования
                    results = self.db.query(
                        "SELECT poll_id, question, options, created_date FROM polls WHERE status = 'active' ORDER BY created_date DESC LIMIT ?",
                        (limit,)
                    )
                elif user_perm == "create":
                    # Пользователи с правом create видят свои голосования + те, в которых участвовали
                    results = self.db.query(
                        """SELECT DISTINCT p.poll_id, p.question, p.options, p.created_date
                           FROM polls p
                           LEFT JOIN poll_votes pv ON p.poll_id = pv.poll_id AND pv.user_id = ?
                           WHERE p.status = 'active'
                           AND (p.creator_id = ? OR pv.user_id IS NOT NULL)
                           ORDER BY p.created_date DESC LIMIT ?""",
                        (user_id, user_id, limit)
                    )
                else:
                    # Обычные пользователи видят только те голосования, в которых участвовали
                    results = self.db.query(
                        """SELECT p.poll_id, p.question, p.options, p.created_date
                           FROM polls p
                           INNER JOIN poll_votes pv ON p.poll_id = pv.poll_id
                           WHERE p.status = 'active' AND pv.user_id = ?
                           ORDER BY p.created_date DESC LIMIT ?""",
                        (user_id, limit)
                    )

            logger.debug(f"Database returned {len(results)} results")
            polls = []
            for row in results:
                polls.append({
                    "poll_id": row[0],
                    "question": row[1],
                    "options": row[2],
                    "created_date": row[3]
                })
            logger.debug(f"Returning {len(polls)} polls")
            return polls
        except Exception as e:
            logger.error(f"Get active polls error: {e}")
            logger.debug(f"Error in get_active_polls: {e}")
            return []

    def get_closed_polls(self, user_id: int, limit: int = 10) -> List[Dict]:
        """Получить список закрытых голосований с учетом прав доступа и участия пользователя"""
        try:
            user_perm = self.get_permissions(user_id)

            if user_perm == "admin":
                # Администратор видит все закрытые голосования
                results = self.db.query(
                    """SELECT poll_id, question, options, created_date, creator_id, total_voters, decision_number
                       FROM polls WHERE status = 'closed' ORDER BY created_date DESC LIMIT ?""",
                    (limit,)
                )
            elif user_perm == "create":
                # Пользователи с правом create видят свои закрытые голосования + те, в которых участвовали
                results = self.db.query(
                    """SELECT DISTINCT p.poll_id, p.question, p.options, p.created_date, p.creator_id, p.total_voters, p.decision_number
                       FROM polls p
                       LEFT JOIN poll_votes pv ON p.poll_id = pv.poll_id AND pv.user_id = ?
                       WHERE p.status = 'closed'
                       AND (p.creator_id = ? OR pv.user_id IS NOT NULL)
                       ORDER BY p.created_date DESC LIMIT ?""",
                    (user_id, user_id, limit)
                )
            else:
                # Обычные пользователи видят только те закрытые голосования, в которых участвовали
                results = self.db.query(
                    """SELECT p.poll_id, p.question, p.options, p.created_date, p.creator_id, p.total_voters, p.decision_number
                       FROM polls p
                       INNER JOIN poll_votes pv ON p.poll_id = pv.poll_id
                       WHERE p.status = 'closed' AND pv.user_id = ?
                       ORDER BY p.created_date DESC LIMIT ?""",
                    (user_id, limit)
                )

            polls = []
            for row in results:
                polls.append({
                    "poll_id": row[0],
                    "question": row[1],
                    "options": row[2],
                    "created_date": row[3],
                    "creator_id": row[4],
                    "total_voters": row[5] or 0,
                    "decision_number": row[6]
                })

            return polls
        except Exception as e:
            logger.error(f"Get closed polls error: {e}")
            return []

    def create_template_session(self, user_id: int, template_name: str, variables: List[str], chat_id: int) -> str:
        """Create template session with cleanup of old sessions and global limits"""
        try:
            # 🔍 ДОБАВЬТЕ ЭТО:
            print(f"🔍 DEBUG creating template session for user {user_id}, template {template_name}")
            import traceback
            traceback.print_stack()  # Покажет, откуда вызывается
            total_sessions = len(self.db.query("SELECT session_id FROM template_sessions"))
            if total_sessions > 100:
                logger.warning(f"Global session limit reached: {total_sessions}")
                self.db.execute("""
                    DELETE FROM template_sessions
                    WHERE session_id IN (
                        SELECT session_id FROM template_sessions
                        ORDER BY created_date ASC LIMIT 50
                    )
                """)

            session_id = str(uuid.uuid4())

            self.db.execute("DELETE FROM template_sessions WHERE user_id = ?", (user_id,))

            success = self.db.execute("""
                INSERT INTO template_sessions (session_id, user_id, template_name, variables_needed, chat_id)
                VALUES (?, ?, ?, ?, ?)
            """, (session_id, user_id, template_name, json.dumps(variables), chat_id))

            return session_id if success else ""
        except Exception as e:
            logger.error(f"Create session error: {e}")
            return ""

    def get_template_session(self, user_id: int) -> Optional[Dict]:
        """Get active template session with safe result handling"""
        try:
            result = self.db.query("""
                SELECT session_id, template_name, variables_needed, variables_values, current_variable, chat_id
                FROM template_sessions WHERE user_id = ? ORDER BY created_date DESC LIMIT 1
            """, (user_id,))

            if result and len(result) > 0:
                row = result[0]
                try:
                    variables_needed = json.loads(row[2]) if row[2] else []
                    variables_values = json.loads(row[3]) if row[3] else {}
                except json.JSONDecodeError:
                    variables_needed = []
                    variables_values = {}

                return {
                    "session_id": row[0],
                    "template_name": row[1],
                    "variables_needed": variables_needed,
                    "variables_values": variables_values,
                    "current_variable": row[4] if row[4] is not None else 0,
                    "chat_id": row[5]
                }
            return None
        except Exception as e:
            logger.error(f"Get session error: {e}")
            return None

    def update_template_session(self, session_id: str, value: str) -> bool:
        """Update session with variable value and bounds checking"""
        try:
            value = self.sanitize(value, 100)
            result = self.db.query("""
                SELECT variables_needed, variables_values, current_variable
                FROM template_sessions WHERE session_id = ?
            """, (session_id,))

            if not result or len(result) == 0:
                return False

            try:
                variables_needed = json.loads(result[0][0]) if result[0][0] else []
                variables_values = json.loads(result[0][1]) if result[0][1] else {}
            except json.JSONDecodeError:
                variables_needed = []
                variables_values = {}

            current = result[0][2] if result[0][2] is not None else 0

            if current >= len(variables_needed):
                logger.warning(f"Template session {session_id}: current variable index out of bounds")
                return False

            var_name = variables_needed[current]
            variables_values[var_name] = value

            return self.db.execute("""
                UPDATE template_sessions SET variables_values = ?, current_variable = ? WHERE session_id = ?
            """, (json.dumps(variables_values), current + 1, session_id))

        except Exception as e:
            logger.error(f"Update session error: {e}")
            return False

    def complete_session(self, session_id: str):
        """Remove completed session"""
        try:
            self.db.execute("DELETE FROM template_sessions WHERE session_id = ?", (session_id,))
        except (sqlite3.Error, Exception) as e:
            logger.error(f"Complete session error: {e}")

    def increment_template_usage(self, template_name: str):
        """Increment template usage counter"""
        try:
            self.db.execute("UPDATE templates SET usage_count = usage_count + 1 WHERE name = ?", (template_name,))
        except (sqlite3.Error, Exception) as e:
            logger.error(f"Increment usage error: {e}")

    # Enhanced poll management (Vote-style)
    async def create_poll(self, question: str, options: List[str], chat_id: int, creator_id: int,
                         template_name: Optional[str] = None, threshold: int = 50, non_anonymous: bool = False,
                         voting_type: Optional[str] = None, max_participants: int = 0) -> bool:
        """Create a new Vote-style poll with inline buttons"""
        try:
            # Clean options from markdown symbols before validation
            cleaned_options = [self.clean_poll_option(option) for option in options]
            
            # Validate
            valid, error_msg = self.validate_poll_data(question, cleaned_options)
            if not valid:
                logger.warning(f"Poll validation failed: {error_msg}")
                return False

            # Check for recent duplicates (last hour)
            hour_ago = (datetime.now() - timedelta(hours=1)).isoformat()
            existing = self.db.query("""
                SELECT poll_id FROM polls
                WHERE creator_id = ? AND question = ? AND created_date > ?
            """, (creator_id, question, hour_ago))

            if existing:
                logger.warning(f"Duplicate poll attempt by user {creator_id}: {question}")
                return False

            # Автоматически определяем тип голосования, если не передан
            if voting_type is None:
                voting_type = self.determine_voting_type(cleaned_options)
                logger.info(f"Auto-detected voting type '{voting_type}' for poll: {question}")

            # Create poll in database
            poll_id = str(uuid.uuid4())

            success = self.db.execute("""
                INSERT INTO polls (poll_id, question, options, chat_id,
                                 creator_id, template_used, threshold, non_anonymous, voting_type, max_participants)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (poll_id, question, "|".join(cleaned_options), chat_id,
                  creator_id, template_name, threshold, 1 if non_anonymous else 0, voting_type, max_participants))

            if not success:
                logger.error("Failed to save poll to database")
                return False

            # Send poll message with Vote-style inline buttons
            text, keyboard = self.format_poll_message(poll_id, show_results=False, for_user_id=creator_id)

            try:
                if not self.application:
                    logger.error("Application not initialized")
                    return False

                message = await self.application.bot.send_message(
                    chat_id=chat_id,
                    text=text,
                    parse_mode=ParseMode.MARKDOWN,
                    reply_markup=keyboard
                )

                # Update message_id in database
                self.db.execute("UPDATE polls SET message_id = ? WHERE poll_id = ?",
                               (message.message_id, poll_id))

                if template_name:
                    self.increment_template_usage(template_name)

                logger.info(f"Vote-style poll created successfully: {poll_id} by user {creator_id}")
                return True

            except Exception as e:
                logger.error(f"Failed to send poll message: {e}")
                # Clean up database entry
                self.db.execute("DELETE FROM polls WHERE poll_id = ?", (poll_id,))
                return False

        except Exception as e:
            logger.error(f"Create poll error: {e}")
            return False

    # Command handlers (mostly unchanged, keeping existing)
    @error_handler
    async def start_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle /start command with enhanced user management"""
        if update.effective_chat.type != "private":
            bot_username = getattr(context.bot, 'username', 'BotName')
            await self.send_message(update, f"❌ В группах команды не поддерживаются. Для публикации и голосования используйте inline-режим: @{bot_username} ...")
            return
        user = update.effective_user
        self.add_user(user.id, user.username or user.first_name or str(user.id))
        self.clear_user_state(user.id)
        permissions = self.get_permissions(user.id)
        if permissions == "none":
            await self.send_message(update, f"❌ У вас нет доступа к боту.\nВаш ID: `{user.id}`\nОбратитесь к администратору.")
            return
        await self.send_message(update, "🗳️ Главное меню:", self.menus.main_menu(user.id))

    @error_handler
    @permission_required(["create"])
    async def create_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle /create command"""
        if update.effective_chat.type != "private":
            bot_username = getattr(context.bot, 'username', 'BotName')
            await self.send_message(update, f"❌ В группах команды не поддерживаются. Для публикации и голосования используйте inline-режим: @{bot_username} ...")
            return
        self.clear_user_state(update.effective_user.id)

        await self.send_message(update, "🗳️ **Создание голосования**\n\nВыберите тип:",
                               self.menus.main_menu())

    # Vote handler (NEW - main feature)
    @error_handler
    async def vote_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle vote button clicks (NEW - core Vote-style feature)"""
        query = update.callback_query
        await query.answer()

        data = query.data
        user_id = query.from_user.id
        username = query.from_user.username or query.from_user.first_name or str(user_id)

        if not data.startswith("vote:"):
            return

        try:
            _, poll_id, option_id_str = data.split(":")
            option_id = int(option_id_str)

            # Check if poll exists
            poll_data = self.db.query("SELECT chat_id, status FROM polls WHERE poll_id = ?", (poll_id,))
            if not poll_data:
                await query.edit_message_text("❌ Голосование не найдено")
                return

            chat_id, status = poll_data[0]
            if status != 'active':
                # Показываем результаты закрытого голосования вместо ошибки
                text, keyboard = self.format_poll_message(poll_id, show_results=True, for_user_id=user_id)
                
                try:
                    await query.edit_message_text(
                        text=text,
                        parse_mode=ParseMode.MARKDOWN,
                        reply_markup=keyboard
                    )
                    await query.answer("❌ Голосование уже закрыто", show_alert=True)
                except Exception as e:
                    logger.error(f"Failed to show closed poll results: {e}")
                    await query.edit_message_text("❌ Голосование закрыто")
                    await query.answer("❌ Голосование уже закрыто", show_alert=True)
                return

            # Check user permissions
            user_perms = self.get_permissions(user_id)

            # Allow voting if user has "use" permissions or higher
            if user_perms in ["use", "create", "admin"]:
                can_vote = True
            else:
                # Check if user is in the chat where poll is posted
                can_vote = await self.is_user_in_chat(user_id, chat_id, context)

            if not can_vote:
                await query.answer("❌ У вас нет прав для голосования в этом опросе", show_alert=True)
                return

            # Record vote (replace if user already voted)
            success = self.db.execute("""
                INSERT OR REPLACE INTO poll_votes (poll_id, user_id, username, option_id)
                VALUES (?, ?, ?, ?)
            """, (poll_id, user_id, username, option_id))

            if not success:
                await query.answer("❌ Ошибка записи голоса", show_alert=True)
                return

            # Update total voters count
            self.db.execute("""
                UPDATE polls SET total_voters = (
                    SELECT COUNT(DISTINCT user_id) FROM poll_votes WHERE poll_id = ?
                ) WHERE poll_id = ?
            """, (poll_id, poll_id))

            # АВТОМАТИЧЕСКОЕ ЗАКРЫТИЕ ОПРОСА
            poll_info = self.db.query("SELECT max_participants, total_voters, creator_id FROM polls WHERE poll_id = ?", (poll_id,))
            auto_closed = False

            if poll_info:
                max_participants, total_voters, creator_id = poll_info[0]
                if max_participants and max_participants > 0 and total_voters >= max_participants:
                    self.db.execute("UPDATE polls SET status = 'closed' WHERE poll_id = ?", (poll_id,))
                    auto_closed = True
                    
                    # Уведомление создателю (только если это не тот же пользователь)
                    if creator_id != user_id:
                        try:
                            poll_details = self.db.query("SELECT question FROM polls WHERE poll_id = ?", (poll_id,))
                            if poll_details:
                                question = poll_details[0][0]
                                notification_text = (
                                    f"🛑 **Голосование автоматически закрыто**\n\n"
                                    f"❓ Вопрос: {question}\n"
                                    f"👥 Проголосовали все {max_participants} участников"
                                )
                                await self.send_message(creator_id, notification_text)
                                logger.info(f"Auto-close notification sent to creator {creator_id}")
                        except Exception as e:
                            logger.error(f"Failed to send auto-close notification: {e}")

            # Update message with new results
            text, keyboard = self.format_poll_message(poll_id, show_results=True, for_user_id=user_id)

            try:
                await query.edit_message_text(
                    text=text,
                    parse_mode=ParseMode.MARKDOWN,
                    reply_markup=keyboard
                )
                
                # Показываем соответствующее уведомление
                if auto_closed:
                    await query.answer("✅ Ваш голос учтен! Голосование автоматически закрыто.", show_alert=False)
                else:
                    await query.answer("✅ Ваш голос учтен!", show_alert=False)
                    
                logger.info(f"Vote recorded: poll {poll_id}, user {user_id}, option {option_id}")

            except Exception as e:
                logger.error(f"Failed to update poll message: {e}")
                if auto_closed:
                    await query.answer("✅ Голос учтен! Голосование закрыто.", show_alert=False)
                else:
                    await query.answer("✅ Голос учтен, но не удалось обновить отображение")

        except Exception as e:
            logger.error(f"Vote handler error: {e}")
            await query.answer("❌ Ошибка обработки голоса", show_alert=True)

    @error_handler
    async def close_poll_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle poll closing (NEW)"""
        query = update.callback_query
        await query.answer()

        data = query.data
        user_id = query.from_user.id

        if not data.startswith("close_poll:"):
            return

        try:
            poll_id = data.split(":", 1)[1]

            # Check permissions
            poll_data = self.db.query("SELECT creator_id, status FROM polls WHERE poll_id = ?", (poll_id,))
            if not poll_data:
                await query.answer("❌ Голосование не найдено", show_alert=True)
                return

            creator_id, status = poll_data[0]
            user_perms = self.get_permissions(user_id)

            # Allow closing only if user is creator or admin
            if user_id != creator_id and user_perms != "admin":
                await query.answer("❌ Недостаточно прав для закрытия опроса", show_alert=True)
                return

            if status != 'active':
                await query.answer("❌ Опрос уже закрыт", show_alert=True)
                return

            # Close poll
            self.db.execute("UPDATE polls SET status = 'closed' WHERE poll_id = ?", (poll_id,))

            # Update message
            text, _ = self.format_poll_message(poll_id, show_results=True, for_user_id=user_id)

            await query.edit_message_text(
                text=text,
                parse_mode=ParseMode.MARKDOWN
            )

            await query.answer("✅ Опрос закрыт", show_alert=False)
            logger.info(f"Poll closed: {poll_id} by user {user_id}")

        except Exception as e:
            logger.error(f"Close poll handler error: {e}")
            await query.answer("❌ Ошибка закрытия опроса", show_alert=True)

    @error_handler
    async def edit_poll_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle poll editing"""
        query = update.callback_query
        await query.answer()

        data = query.data
        user_id = query.from_user.id

        if not data.startswith("edit_poll:"):
            return

        try:
            poll_id = data.split(":", 1)[1]

            # Check permissions
            poll_data = self.db.query("SELECT creator_id, status, question FROM polls WHERE poll_id = ?", (poll_id,))
            if not poll_data:
                await query.answer("❌ Голосование не найдено", show_alert=True)
                return

            creator_id, status, question = poll_data[0]
            user_perms = self.get_permissions(user_id)

            # Allow editing only if user is creator or admin
            if user_id != creator_id and user_perms != "admin":
                await query.answer("❌ Недостаточно прав для редактирования опроса", show_alert=True)
                return

            if status != 'active':
                await query.answer("❌ Можно редактировать только активные опросы", show_alert=True)
                return

            # Set user state for editing
            self.set_user_state(user_id, UserState.WAITING_POLL_QUESTION, {
                "type": "edit",
                "poll_id": poll_id,
                "original_question": question
            })

            # Show edit menu
            keyboard = [
                [InlineKeyboardButton("📝 Изменить вопрос", callback_data=f"edit_poll_question:{poll_id}")],
                [InlineKeyboardButton("📋 Изменить варианты", callback_data=f"edit_poll_options:{poll_id}")],
                [InlineKeyboardButton("⬅️ Назад", callback_data=f"show_poll:{poll_id}")]
            ]

            await query.edit_message_text(
                text=f"✏️ **Редактирование опроса**\n\n❓ Вопрос: {question}\n\nВыберите, что хотите изменить:",
                reply_markup=InlineKeyboardMarkup(keyboard),
                parse_mode=ParseMode.MARKDOWN
            )

        except Exception as e:
            logger.error(f"Edit poll handler error: {e}")
            await query.answer("❌ Ошибка редактирования опроса", show_alert=True)

    @error_handler
    async def delete_poll_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle poll deletion with confirmation"""
        query = update.callback_query
        await query.answer()

        data = query.data
        user_id = query.from_user.id

        if not data.startswith("delete_poll:"):
            return

        try:
            poll_id = data.split(":", 1)[1]

            # Check permissions
            poll_data = self.db.query("SELECT creator_id, question FROM polls WHERE poll_id = ?", (poll_id,))
            if not poll_data:
                await query.answer("❌ Голосование не найдено", show_alert=True)
                return

            creator_id, question = poll_data[0]
            user_perms = self.get_permissions(user_id)

            # Allow deletion only if user is creator or admin
            if user_id != creator_id and user_perms != "admin":
                await query.answer("❌ Недостаточно прав для удаления опроса", show_alert=True)
                return

            # Show confirmation menu
            keyboard = [
                [InlineKeyboardButton("✅ Да, удалить", callback_data=f"confirm_delete_poll:{poll_id}")],
                [InlineKeyboardButton("❌ Отмена", callback_data=f"show_poll:{poll_id}")]
            ]

            await query.edit_message_text(
                text=f"🗑️ **Удаление опроса**\n\n❓ Вопрос: {question}\n\n⚠️ **Внимание!** Это действие нельзя отменить.\n\nВы уверены, что хотите удалить этот опрос?",
                reply_markup=InlineKeyboardMarkup(keyboard),
                parse_mode=ParseMode.MARKDOWN
            )

        except Exception as e:
            logger.error(f"Delete poll handler error: {e}")
            await query.answer("❌ Ошибка удаления опроса", show_alert=True)

    # Keep existing callback handler but add vote handling
    @error_handler
    async def callback_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Enhanced callback handler with comprehensive error handling"""
        try:
            query = update.callback_query
            user_id = query.from_user.id
            data = query.data
            logger.info(f"callback_handler: user_id={user_id}, data={data}")

            # Rate limiting check
            if self.rate_limiter.is_user_flooding(user_id):
                await query.answer("⚠️ Слишком много запросов. Подождите немного.", show_alert=True)
                return

            # Validate callback data
            if not self.validate_callback_data(data):
                logger.warning(f"Invalid callback data from user {user_id}: {data}")
                await query.answer("❌ Неверная команда", show_alert=True)
                return

            # Add user to database if not exists
            self.add_user(user_id, query.from_user.username or str(user_id))

            # Handle different callback types
            if data == "create_poll":
                if self.get_permissions(user_id) in ["create", "admin"]:
                    await self.send_message(query, "Выберите тип опроса:", self.menus.poll_type_menu())
                else:
                    await self.send_message(query, "❌ Недостаточно прав для создания голосований")
                return

            elif data == "templates":
                await self.show_templates_for_use(query)
                return

            elif data == "active_polls":
                await self.show_active_polls(query)
                return

            elif data == "closed_polls":
                await self.show_closed_polls(query)
                return

            elif data.startswith("use_tpl:"):
                template_id = data.split(":", 1)[1]
                await self.handle_use_template(query, template_id)
                return

            elif data == "status":
                await self.status_command(query, context)
                return

            elif data == "admin":
                try:
                    await self.admin_command(query, context)
                except Exception as e:
                    logger.error(f"Admin command error: {e}")
                    await query.edit_message_text("❌ Внутренняя ошибка. Обратитесь к администратору.")
                return

            elif data == "help":
                await self.help_command(query, context)
                return

            elif data.startswith("admin_"):
                try:
                    await self.handle_admin_callback(query, data)
                except Exception as e:
                    logger.error(f"Admin callback error: {e}")
                    await query.edit_message_text("❌ Внутренняя ошибка. Обратитесь к администратору.")
                return

            elif data.startswith("delete_tpl:"):
                template_id = data.split(":", 1)[1]
                result = self.db.query("SELECT created_by FROM templates WHERE id = ?", (template_id,))
                if not result:
                    await query.answer("❌ Шаблон не найден", show_alert=True)
                    return
                created_by = result[0][0]
                if (created_by == user_id) or (self.get_permissions(user_id) == "admin"):
                    keyboard = [
                        [InlineKeyboardButton("✅ Да, удалить", callback_data=f"confirm_delete_template:{template_id}")],
                        [InlineKeyboardButton("❌ Отмена", callback_data="back_to_templates")]
                    ]
                    template_name_row = self.db.query("SELECT name FROM templates WHERE id = ?", (template_id,))
                    template_name = template_name_row[0][0] if template_name_row else str(template_id)
                    await self.send_message(query, f"🗑️ Вы уверены, что хотите удалить шаблон **{template_name}**?",
                                          reply_markup=InlineKeyboardMarkup(keyboard))
                else:
                    await query.answer("❌ Нет прав на удаление", show_alert=True)
                return

            elif data.startswith("confirm_delete_template:"):
                template_id = data.split(":", 1)[1]
                template_name_row = self.db.query("SELECT name FROM templates WHERE id = ?", (template_id,))
                template_name = template_name_row[0][0] if template_name_row else str(template_id)
                self.db.execute("DELETE FROM templates WHERE id = ?", (template_id,))
                await self.send_message(query, f"✅ Шаблон **{template_name}** удалён.")
                # После удаления возвращаем пользователя к списку шаблонов
                await self.show_templates_for_use(query)
                return

            elif data == "back_to_templates":
                await self.show_templates_for_use(query)
                return

            elif data.startswith("continue_tpl:"):
                template_id = data.split(":", 1)[1]
                # Получаем переменные из шаблона
                variables_json = self.db.query("SELECT variables FROM templates WHERE id = ?", (template_id,))
                variables = json.loads(variables_json[0][0]) if variables_json and variables_json[0][0] else []
                session_id = self.create_template_session(
                    query.from_user.id, template_id, variables, query.message.chat_id
                )
                if session_id:
                    await self.ask_next_variable(query, session_id)
                else:
                    await self.send_message(query, "❌ Ошибка создания сессии")
                return

            # Handle vote callbacks
            elif data.startswith("vote:"):
                await self.vote_handler(update, context)
                return

            elif data.startswith("close_poll:"):
                await self.close_poll_handler(update, context)
                return

            elif data.startswith("edit_poll:"):
                await self.edit_poll_handler(update, context)
                return

            elif data.startswith("delete_poll:"):
                await self.delete_poll_handler(update, context)
                return

            elif data.startswith("confirm_delete_poll:"):
                await self.confirm_delete_poll_handler(update, context)
                return

            elif data.startswith("edit_poll_question:"):
                await self.start_edit_poll_question(update, context)
                return

            elif data.startswith("edit_poll_options:"):
                await self.start_edit_poll_options(update, context)
                return

            elif data.startswith("show_poll:"):
                poll_id = data.split(":", 1)[1]
                await self.show_single_poll(query, poll_id)
                return

            elif data.startswith("show_closed_poll:"):
                poll_id = data.split(":", 1)[1]
                await self.show_single_poll(query, poll_id)
                return

            # Handle user deletion confirmation
            elif data.startswith("confirm_delete:"):
                await self.handle_user_deletion(query, data)
                return

            elif data == "cancel_delete":
                await query.edit_message_text("❌ Удаление отменено")
                return

            elif data.startswith("cancel:"):
                session_id = data.split(":", 1)[1]
                self.complete_session(session_id)
                self.clear_user_state(user_id)
                await query.edit_message_text("❌ Отменено")

            elif data == "create_simple":
                if self.get_permissions(user_id) in ["create", "admin"]:
                    self.set_user_state(user_id, UserState.WAITING_POLL_QUESTION, {"type": "simple"})
                    await self.send_message(query, "📝 Введите вопрос для простого опроса:")
                else:
                    await self.send_message(query, "❌ Недостаточно прав для создания голосований")



            elif data == "create_from_template":
                if self.get_permissions(user_id) in ["create", "admin"]:
                    await self.show_templates_for_use(query)
                else:
                    await query.edit_message_text("❌ Недостаточно прав для создания голосований")

            elif data == "new_template":
                if self.get_permissions(user_id) in ["create", "admin"]:
                    # Очищаем старые template_sessions для этого пользователя
                    self.db.execute("DELETE FROM template_sessions WHERE user_id = ?", (user_id,))
                    
                    self.set_user_state(user_id, UserState.WAITING_TEMPLATE_NAME)
                    await query.edit_message_text("📋 Введите название шаблона:")
                else:
                    await query.edit_message_text("❌ Недостаточно прав")
                return

            elif data == "finish_poll_creation":
                user_state = self.get_user_state(user_id)
                state_data = user_state.get("data", {})
                question = state_data.get("question", "")
                options = state_data.get("options", [])
                poll_type = state_data.get("type", "simple")
                await self.finalize_poll_creation(update, question, options, poll_type)
                return

            elif data == "finish_template_creation":
                user_state = self.get_user_state(user_id)
                state_data = user_state.get("data", {})
                name = state_data.get("name", "")
                question = state_data.get("question", "")
                variables = state_data.get("variables", [])
                options = state_data.get("options", [])
                await self.finalize_template_creation(query, name, question, variables, options)
                return

            elif data == "display_settings":
                user_settings = self.get_user_settings(user_id)
                await self.send_message(query, "⚙️ Настройки отображения опросов:", self.menus.display_settings_menu(user_id, user_settings, self.config))
                return

            elif data.startswith("toggle_setting:"):
                opt = data.split(":", 1)[1]
                user_settings = self.get_user_settings(user_id)
                current = user_settings.get(opt, self.config.get(opt, True))
                user_settings[opt] = not current
                self.set_user_settings(user_id, user_settings)
                logger.info(f"User {user_id} toggled setting '{opt}' from {current} to {user_settings[opt]}")
                await self.send_message(query, "⚙️ Настройки обновлены:", self.menus.display_settings_menu(user_id, user_settings, self.config))
                return

            elif data == "reset_settings":
                self.db.execute("DELETE FROM user_settings WHERE user_id = ?", (user_id,))
                await self.send_message(query, "⚙️ Настройки сброшены к стандартным", self.menus.display_settings_menu(user_id, {}, self.config))
                return

            elif data == "enter_decision_number":
                user_state = self.get_user_state(user_id)
                state_data = user_state.get("data", {})
                self.set_user_state(user_id, UserState.WAITING_DECISION_NUMBER_INPUT, state_data)
                await self.send_message(query, "Введите номер решения (целое число):",
                                      self.menus.back_menu("main"))
                return

            elif data == "next_decision_number":
                user_state = self.get_user_state(user_id)
                state_data = user_state.get("data", {})
                user_settings = self.get_user_settings(user_id)
                last_num = user_settings.get('last_decision_number', 0)
                next_num = last_num + 1 if last_num else 1
                user_settings['last_decision_number'] = next_num
                self.set_user_settings(user_id, user_settings)
                max_participants = state_data.get("max_participants", 0)
                await self.create_poll_from_template_with_max_participants(
                    query, 
                    state_data["template_id"],
                    state_data["question"], 
                    state_data["options"],
                    state_data["values"], 
                    state_data["threshold"],
                    non_anonymous=state_data["non_anonymous"], 
                    chat_id=state_data["chat_id"],
                    user_id=user_id, 
                    max_participants=max_participants,
                    decision_number=next_num
                )
                return

            elif data == "back_to_main":
                await self.send_message(query, "🗳️ Главное меню:", self.menus.main_menu(user_id))
                return

            elif data.startswith("edit_tpl_threshold:"):
                template_id = data.split(":", 1)[1]
                result = self.db.query("SELECT threshold, name, created_by FROM templates WHERE id = ?", (template_id,))
                if not result:
                    await query.answer("❌ Шаблон не найден", show_alert=True)
                    return
                threshold, name, created_by = result[0]
                if (created_by == user_id) or (self.get_permissions(user_id) == "admin"):
                    self.set_user_state(user_id, UserState.WAITING_EDIT_TEMPLATE_THRESHOLD,
                                      {"template_id": template_id, "name": name})
                    await self.send_message(query, f"Текущий порог шаблона **{name}**: {threshold}%\nВведите новый порог (целое число):")
                else:
                    await query.answer("❌ Нет прав на редактирование", show_alert=True)
                return

            elif data == "admin_clear_all_logs":
                await self.clear_all_logs(query)
                return
            elif data == "admin_logs_stats":
                await self.show_admin_logs_stats(query)
                return
            elif data == "admin_clear_logs_by_level":
                await query.edit_message_text(
                    "🔧 **Очистка логов по уровням**\n\nВыберите уровень для очистки:",
                    reply_markup=self.menus.admin_clear_logs_by_level_menu()
                )
            elif data.startswith("admin_clear_logs:"):
                level = data.split(":")[1]
                success = await self.clear_logs_by_level(query, level)
                if success:
                    await query.edit_message_text(
                        f"✅ Логи уровня '{level}' очищены!",
                        reply_markup=self.menus.admin_clear_logs_by_level_menu()
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Ошибка очистки логов уровня '{level}'",
                        reply_markup=self.menus.admin_clear_logs_by_level_menu()
                    )
            elif data == "admin_view_recent_logs":
                await query.edit_message_text(
                    "📄 **Просмотр логов**\n\nВыберите уровень для просмотра:",
                    reply_markup=self.menus.admin_view_logs_menu()
                )
            elif data.startswith("admin_view_logs:"):
                level = data.split(":")[1]
                text = await self.view_logs_by_level(query, level)
                await query.edit_message_text(
                    text,
                    reply_markup=self.menus.admin_view_logs_menu()
                )
            elif data == "admin_rotate_logs":
                success = await self.rotate_logs(query)
                if success:
                    await query.edit_message_text(
                        "🔄 **Ротация логов выполнена**",
                        reply_markup=self.menus.admin_logs_menu()
                    )
                else:
                    await query.edit_message_text(
                        "❌ Ошибка ротации логов",
                        reply_markup=self.menus.admin_logs_menu()
                    )
            elif data == "admin_logs_levels":
                await query.edit_message_text(
                    "⚙️ **Управление уровнями логирования**\n\nНажмите на уровень для включения/выключения:",
                    reply_markup=self.menus.admin_logs_levels_menu()
                )
            elif data.startswith("admin_toggle_logs:"):
                level = data.split(":")[1]
                message = await self.toggle_logs_by_level(query, level)
                await query.edit_message_text(
                    message,
                    reply_markup=self.menus.admin_logs_levels_menu()
                )
            elif data == "admin_third_party_loggers":
                await self.show_third_party_loggers_status(query)
            elif data.startswith("admin_setperm:"):
                target_user_id = int(data.split(":")[1])
                perms = [
                    ("use", "👤 use"),
                    ("create", "📝 create"),
                    ("admin", "🛠 admin")
                ]
                perm_buttons = [InlineKeyboardButton(label, callback_data=f"admin_perm_select:{target_user_id}:{p}") for p, label in perms]
                keyboard = [perm_buttons[i:i+2] for i in range(0, len(perm_buttons), 2)]
                keyboard.append([InlineKeyboardButton("🔙 Назад", callback_data="admin_users")])
                await query.edit_message_text(f"Выберите права для пользователя `{target_user_id}`:", reply_markup=InlineKeyboardMarkup(keyboard))
            elif data.startswith("admin_perm_select:"):
                _, target_user_id, new_perm = data.split(":")
                target_user_id = int(target_user_id)
                # Обновляем права
                self.db.execute("UPDATE users SET permissions = ? WHERE user_id = ?", (new_perm, target_user_id))
                await query.edit_message_text(f"✅ Права пользователя `{target_user_id}` обновлены на `{new_perm}`.")
                await self.show_admin_users_list(query)
            elif data.startswith("admin_revoke:"):
                target_user_id = int(data.split(":")[1])
                self.db.execute("UPDATE users SET permissions = 'use' WHERE user_id = ?", (target_user_id,))
                await query.edit_message_text(f"✅ Права пользователя `{target_user_id}` отозваны (установлено 'use').")
                await self.show_admin_users_list(query)
            elif data.startswith("admin_delete:"):
                target_user_id = int(data.split(":")[1])
                keyboard = [
                    [InlineKeyboardButton("✅ Да, удалить", callback_data=f"admin_confirm_delete:{target_user_id}")],
                    [InlineKeyboardButton("❌ Отмена", callback_data="admin_users")]
                ]
                await query.edit_message_text(f"⚠️ Подтвердите удаление пользователя `{target_user_id}`:", reply_markup=InlineKeyboardMarkup(keyboard))
            elif data.startswith("admin_confirm_delete:"):
                target_user_id = int(data.split(":")[1])
                self.db.execute("DELETE FROM users WHERE user_id = ?", (target_user_id,))
                self.db.execute("DELETE FROM poll_votes WHERE user_id = ?", (target_user_id,))
                self.db.execute("DELETE FROM user_states WHERE user_id = ?", (target_user_id,))
                self.db.execute("DELETE FROM template_sessions WHERE user_id = ?", (target_user_id,))
                await query.edit_message_text(f"✅ Пользователь `{target_user_id}` и все его данные удалены.")
                await self.show_admin_users_list(query)
            elif data == "admin_clear_logs":
                await self.clear_all_logs(query)
            elif data.startswith("admin_logs_"):
                await self.handle_admin_logs_command(query, data)
                return
            elif data == "admin_back":
                await query.edit_message_text(
                    "🛠 **Панель администратора**\n\nВыберите действие:",
                    reply_markup=self.menus.admin_menu()
                )
                return
            elif data == "admin_users":
                await self.show_admin_users_list(query)
                return
            elif data == "admin_stats":
                await self.show_admin_stats(query)
                return
            elif data == "admin_logs":
                await query.edit_message_text(
                    "📋 **Управление логами**\n\nВыберите действие:",
                    reply_markup=self.menus.admin_logs_menu()
                )
                return
            else:
                logger.warning(f"Unknown callback data from user {user_id}: {data}")
                await query.answer("❌ Неизвестная команда", show_alert=True)
                return

        except Exception as e:
            logger.error(f"Callback handler error for user {user_id}: {e}", exc_info=True)
            try:
                await query.answer("❌ Произошла ошибка", show_alert=True)
            except:
                pass

    async def handle_use_template(self, query, template_id: str):
        """Handle template usage with enhanced validation"""
        try:
            result = self.db.query("""
                SELECT question, options, variables, threshold, non_anonymous
                FROM templates WHERE id = ?
            """, (template_id,))

            if not result or len(result) == 0:
                if hasattr(query, 'edit_message_text'):
                    await query.edit_message_text("❌ Шаблон не найден")
                else:
                    await self.send_message(query, "❌ Шаблон не найден")
                return
            question, options, variables_json, threshold, non_anonymous = result[0]
            try:
                variables = json.loads(variables_json) if variables_json else []
            except:
                variables = []
            chat_id = query.message.chat_id
            template_name_row = self.db.query("SELECT name FROM templates WHERE id = ?", (template_id,))
            template_name = template_name_row[0][0] if template_name_row else str(template_id)
            text = f"📋 **Шаблон:** {template_name}\n"
            text += f"❓ {question}\n"
            text += f"📋 Варианты: {options.replace('|', ', ')}\n"
            if variables:
                text += f"🔧 Переменные: {', '.join(variables)}\n"
            text += f"🎯 Порог: {threshold or 50}%"
            if hasattr(query, 'edit_message_text'):
                await query.edit_message_text(text, parse_mode=ParseMode.MARKDOWN)
            else:
                await self.send_message(query, text)
            if variables:
                keyboard = [
                    [
                        InlineKeyboardButton("⬅️ Назад", callback_data="back_to_templates"),
                        InlineKeyboardButton("➡️ Продолжить", callback_data=f"continue_tpl:{template_id}")
                    ]
                ]
                if hasattr(query, 'edit_message_text'):
                    await query.edit_message_text(
                        "Нажмите «Продолжить» для заполнения переменных шаблона или «Назад» для возврата к списку.",
                        reply_markup=InlineKeyboardMarkup(keyboard)
                    )
                else:
                    await self.send_message(query, "Нажмите «Продолжить» для заполнения переменных шаблона или «Назад» для возврата к списку.", reply_markup=InlineKeyboardMarkup(keyboard))
                return
            else:
                await self.create_poll_from_template(query, template_id, question, options, {}, threshold or 50, bool(non_anonymous))
                return
        except Exception as e:
            logger.error(f"Handle use template error: {e}")
            if hasattr(query, 'edit_message_text'):
                await query.edit_message_text("❌ Ошибка использования шаблона")
            else:
                await self.send_message(query, "❌ Ошибка использования шаблона")

    async def ask_next_variable(self, query_or_update, session_id: str):
        """Ask for next template variable with enhanced validation"""
        try:
            result = self.db.query("""
                SELECT template_name, variables_needed, variables_values, current_variable
                FROM template_sessions WHERE session_id = ?
            """, (session_id,))

            if not result or len(result) == 0:
                await self.send_message(query_or_update, "❌ Сессия не найдена")
                return

            template_name, variables_json, values_json, current = result[0]

            try:
                variables = json.loads(variables_json) if variables_json else []
                values = json.loads(values_json) if values_json else {}
            except json.JSONDecodeError:
                variables = []
                values = {}

            current = current if current is not None else 0

            if current >= len(variables):
                await self.finalize_template_poll(query_or_update, session_id)
                return

            var_name = variables[current]
            text = f"🔧 **{template_name}** ({current + 1}/{len(variables)})\n\n"
            text += f"📝 Введите значение для **{{{var_name}}}**:"

            if values:
                text += f"\n\n✅ Заполнено: " + ", ".join([f"{{{k}}}={v}" for k, v in values.items()])

            keyboard = self.menus.ask_variable_menu(session_id)
            await self.send_message(query_or_update, text, keyboard)

        except Exception as e:
            logger.error(f"Ask variable error: {e}")
            await self.send_message(query_or_update, "❌ Ошибка запроса переменной")

    async def finalize_template_poll(self, query_or_update, session_id: str):
        """Create poll from completed template with validation"""
        try:
            result = self.db.query("""
                SELECT template_name, variables_values, chat_id, user_id FROM template_sessions WHERE session_id = ?
            """, (session_id,))

            if not result or len(result) == 0:
                await self.send_message(query_or_update, "❌ Сессия не найдена")
                return

            template_id, values_json, chat_id, user_id = result[0]

            try:
                values = json.loads(values_json) if values_json else {}
            except json.JSONDecodeError:
                values = {}

            template_result = self.db.query(
                "SELECT question, options, threshold, non_anonymous FROM templates WHERE id = ?",
                (template_id,)
            )

            if template_result and len(template_result) > 0:
                question, options, threshold, non_anonymous = template_result[0]
                # шаг выбора номера решения
                user_settings = self.get_user_settings(user_id)
                show_decision_numbers = user_settings.get('show_decision_numbers', self.config.get('show_decision_numbers', True))
                if show_decision_numbers:
                    template_data = self.db.query("SELECT max_participants FROM templates WHERE id = ?", (template_id,))
                    template_max_participants = template_data[0][0] if template_data else 0
                    self.set_user_state(user_id, UserState.WAITING_DECISION_NUMBER, {
                        "template_id": template_id,
                        "question": question,
                        "options": options,
                        "values": values,
                        "threshold": threshold,
                        "non_anonymous": non_anonymous,
                        "chat_id": chat_id,
                        "max_participants": template_max_participants
                    })
                    await self.send_message(query_or_update, "Выберите способ нумерации решения:", self.menus.decision_number_menu(user_id))
                    return
                # Запрашиваем максимальное количество участников
                self.set_user_state(user_id, UserState.WAITING_MAX_PARTICIPANTS, {
                    "template_id": template_id,
                    "question": question,
                    "options": options,
                    "values": values,
                    "threshold": threshold or 50,
                    "non_anonymous": bool(non_anonymous),
                    "chat_id": chat_id,
                    "is_template": True
                })
                await self.send_message(
                    query_or_update,
                    "👥 **Максимальное количество участников**\n\n"
                    "Введите число участников или 0 для неограниченного количества:"
                )
            else:
                await self.send_message(query_or_update, "❌ Шаблон не найден")

            self.complete_session(session_id)

        except Exception as e:
            logger.error(f"Finalize poll error: {e}")
            await self.send_message(query_or_update, "❌ Ошибка создания голосования")

    async def create_poll_from_template(self, query_or_update, template_id: str, question: str, options: str,
                                       values: Dict[str, str], threshold: int = 50, non_anonymous: bool = False,
                                       chat_id: Optional[int] = None, user_id: Optional[int] = None, decision_number: Optional[int] = None):
        """Create poll from template with enhanced error handling"""
        try:
            if hasattr(query_or_update, 'message'):
                chat_id = chat_id or query_or_update.message.chat_id
                user_id = user_id or query_or_update.from_user.id
            else:
                chat_id = chat_id or query_or_update.effective_chat.id
                user_id = user_id or query_or_update.effective_user.id

            # Проверяем права на создание опросов
            if self.get_permissions(user_id) not in ["create", "admin"]:
                await self.send_message(query_or_update, "❌ Недостаточно прав для создания голосований")
                return

            final_question = self.substitute_variables(question, values)
            final_options = [self.clean_poll_option(self.sanitize(self.substitute_variables(opt.strip(), values), MAX_POLL_OPTION)) for opt in options.split('|') if opt.strip()]

            valid, error_msg = self.validate_poll_data(final_question, final_options)
            if not valid:
                await self.send_message(query_or_update, f"❌ {error_msg}")
                return

            # Автоматически определяем тип голосования
            voting_type = self.determine_voting_type(final_options)
            logger.info(f"Auto-detected voting type '{voting_type}' for template poll: {final_question}")

            # Если decision_number задан, сохраняем его в polls
            poll_id = str(uuid.uuid4())
            success = self.db.execute(
                "INSERT INTO polls (poll_id, question, options, chat_id, creator_id, template_used, threshold, non_anonymous, voting_type, decision_number, max_participants) "
                "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)" if decision_number is not None else
                "INSERT INTO polls (poll_id, question, options, chat_id, creator_id, template_used, threshold, non_anonymous, voting_type, max_participants) "
                "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
                (poll_id, final_question, "|".join(final_options), chat_id, user_id, template_id, threshold, 1 if non_anonymous else 0, voting_type, decision_number, 0) if decision_number is not None else
                (poll_id, final_question, "|".join(final_options), chat_id, user_id, template_id, threshold, 1 if non_anonymous else 0, voting_type, 0)
            )
            if not success:
                await self.send_message(query_or_update, "❌ Ошибка создания голосования")
                return
            # Отправляем сообщение с опросом
            text, keyboard = self.format_poll_message(poll_id, show_results=False, for_user_id=user_id)
            if not self.application:
                logger.error("Application not initialized")
                return
            message = await self.application.bot.send_message(
                chat_id=chat_id,
                text=text,
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=keyboard
            )
            self.db.execute("UPDATE polls SET message_id = ? WHERE poll_id = ?", (message.message_id, poll_id))
            # Увеличиваем usage_count шаблона
            template_name_row = self.db.query("SELECT name FROM templates WHERE id = ?", (template_id,))
            template_name = template_name_row[0][0] if template_name_row else str(template_id)
            self.increment_template_usage(template_name)
            
            # Автоматически определяем тип голосования
            voting_type = self.determine_voting_type(final_options)
            
            msg = f"✅ Голосование создано из шаблона **{template_name}**!"
            if values:
                msg += f"\n🔧 " + ", ".join([f"{{{k}}}={v}" for k, v in values.items()])
            msg += f"\n🎯 Порог: {threshold}%"
            
            # Добавляем информацию о типе голосования
            msg += self.get_voting_type_text(voting_type)
            
            if non_anonymous:
                msg += f"\n👥 Режим: Неанонимный"
            await self.send_message(query_or_update, msg)
            return

        except Exception as e:
            logger.error(f"Create poll from template error: {e}")
            await self.send_message(query_or_update, "❌ Ошибка создания голосования")

    async def create_poll_from_template_with_max_participants(self, query_or_update, template_id: str, question: str, options: str,
                                   values: Dict[str, str], threshold: int = 50, non_anonymous: bool = False,
                                   chat_id: Optional[int] = None, user_id: Optional[int] = None, 
                                   max_participants: int = 0, decision_number: Optional[int] = None):
        """Create poll from template with max_participants parameter"""
        try:
            if hasattr(query_or_update, 'message'):
                chat_id = chat_id or query_or_update.message.chat_id
                user_id = user_id or query_or_update.from_user.id
            else:
                chat_id = chat_id or query_or_update.effective_chat.id
                user_id = user_id or query_or_update.effective_user.id

            # Проверяем права на создание опросов
            if self.get_permissions(user_id) not in ["create", "admin"]:
                await self.send_message(query_or_update, "❌ Недостаточно прав для создания голосований")
                return

            final_question = self.substitute_variables(question, values)
            final_options = [self.clean_poll_option(self.sanitize(self.substitute_variables(opt.strip(), values), MAX_POLL_OPTION)) for opt in options.split('|') if opt.strip()]

            valid, error_msg = self.validate_poll_data(final_question, final_options)
            if not valid:
                await self.send_message(query_or_update, f"❌ {error_msg}")
                return

            # Автоматически определяем тип голосования
            voting_type = self.determine_voting_type(final_options)
            logger.info(f"Auto-detected voting type '{voting_type}' for template poll: {final_question}")

            # Создаем опрос с max_participants
            poll_id = str(uuid.uuid4())

            if decision_number is not None:
                success = self.db.execute(
                    "INSERT INTO polls (poll_id, question, options, chat_id, creator_id, template_used, threshold, non_anonymous, voting_type, max_participants, decision_number) "
                    "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
                    (poll_id, final_question, "|".join(final_options), chat_id, user_id, template_id, threshold, 1 if non_anonymous else 0, voting_type, max_participants, decision_number)
                )
            else:
                success = self.db.execute(
                    "INSERT INTO polls (poll_id, question, options, chat_id, creator_id, template_used, threshold, non_anonymous, voting_type, max_participants) "
                    "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
                    (poll_id, final_question, "|".join(final_options), chat_id, user_id, template_id, threshold, 1 if non_anonymous else 0, voting_type, max_participants)
                )
            if not success:
                await self.send_message(query_or_update, "❌ Ошибка создания голосования")
                return
                
            # Отправляем сообщение с опросом
            text, keyboard = self.format_poll_message(poll_id, show_results=False, for_user_id=user_id)
            if not self.application:
                logger.error("Application not initialized")
                return
            message = await self.application.bot.send_message(
                chat_id=chat_id,
                text=text,
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=keyboard
            )
            self.db.execute("UPDATE polls SET message_id = ? WHERE poll_id = ?", (message.message_id, poll_id))
            
            # Увеличиваем usage_count шаблона
            template_name_row = self.db.query("SELECT name FROM templates WHERE id = ?", (template_id,))
            template_name = template_name_row[0][0] if template_name_row else str(template_id)
            self.increment_template_usage(template_name)
            
            msg = f"✅ Голосование создано из шаблона **{template_name}**!"
            if values:
                msg += f"\n🔧 " + ", ".join([f"{{{k}}}={v}" for k, v in values.items()])
            msg += f"\n🎯 Порог: {threshold}%"
            msg += f"\n👥 Максимум участников: {max_participants if max_participants else 'не ограничено'}"
            
            # Добавляем информацию о типе голосования
            msg += self.get_voting_type_text(voting_type)
            
            if non_anonymous:
                msg += f"\n👥 Режим: Неанонимный"
            await self.send_message(query_or_update, msg)
            return

        except Exception as e:
            logger.error(f"Create poll from template error: {e}")
            await self.send_message(query_or_update, "❌ Ошибка создания голосования")

    @error_handler
    async def text_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Enhanced text handler with flood protection"""
        user_id = update.effective_user.id
        text = self.sanitize(update.message.text, 500)

        # 🔍 ДОБАВЬТЕ ЭТО ДЛЯ ДИАГНОСТИКИ:
        user_state = self.get_user_state(user_id)
        state = user_state.get("state", UserState.IDLE)
        session = self.get_template_session(user_id)
        
        print(f"🔍 DEBUG user {user_id}: state={state}, text='{text[:20]}...'")
        if session:
            print(f"🔍 DEBUG session found: {session}")
        else:
            print(f"🔍 DEBUG no session")

        if not text:
            return

        if self.rate_limiter.is_user_flooding(user_id):
            await self.send_message(update, "⚠️ Слишком много сообщений. Подождите немного.")
            return

        # Get user state
        user_state = self.get_user_state(user_id)
        state = user_state.get("state", UserState.IDLE)
        state_data = user_state.get("data", {})

        # Check template session only if user is not in poll creation state
        if state not in [UserState.WAITING_POLL_QUESTION, UserState.WAITING_POLL_OPTION, UserState.WAITING_POLL_OPTIONS, UserState.WAITING_DECISION_NUMBER_INPUT, UserState.WAITING_TEMPLATE_NAME, UserState.WAITING_TEMPLATE_QUESTION, UserState.WAITING_TEMPLATE_OPTION, UserState.WAITING_TEMPLATE_OPTIONS, UserState.WAITING_TEMPLATE_THRESHOLD, UserState.WAITING_EDIT_TEMPLATE_THRESHOLD, UserState.WAITING_MAX_PARTICIPANTS, UserState.WAITING_TEMPLATE_CREATION_THRESHOLD, UserState.WAITING_TEMPLATE_POLL_THRESHOLD, UserState.WAITING_POLL_THRESHOLD]:
            session = self.get_template_session(user_id)
            if session:
                try:
                    if self.update_template_session(session["session_id"], text):
                        await self.ask_next_variable(update, session["session_id"])
                    else:
                        logger.error(f"Failed to update template session {session['session_id']} for user {user_id}")
                        await self.send_message(update, "❌ Ошибка обновления сессии. Попробуйте еще раз или начните заново.")
                        self.complete_session(session["session_id"])
                        self.clear_user_state(user_id)
                except Exception as e:
                    logger.error(f"Template session error for user {user_id}: {e}")
                    await self.send_message(update, "❌ Ошибка обработки шаблона. Попробуйте еще раз.")
                    self.complete_session(session["session_id"])
                    self.clear_user_state(user_id)
                return

        try:
            if state == UserState.WAITING_POLL_QUESTION:
                await self.handle_poll_question_input(update, text, state_data)

            elif state == UserState.WAITING_POLL_OPTION:
                await self.handle_poll_option_input(update, text, state_data)

            elif state == UserState.WAITING_POLL_OPTIONS:
                await self.handle_poll_options_input(update, text, state_data)

            elif state == UserState.WAITING_TEMPLATE_OPTION:
                await self.handle_template_option_input(update, text, state_data)

            elif state == UserState.WAITING_TEMPLATE_NAME:
                await self.handle_template_name_input(update, text)

            elif state == UserState.WAITING_TEMPLATE_QUESTION:
                await self.handle_template_question_input(update, text, state_data)

            elif state == UserState.WAITING_TEMPLATE_OPTIONS:
                await self.handle_template_options_input(update, text, state_data)

            elif state == UserState.WAITING_DECISION_NUMBER_INPUT:
                try:
                    num = int(text)
                    user_settings = self.get_user_settings(user_id)
                    user_settings['last_decision_number'] = num
                    self.set_user_settings(user_id, user_settings)
                    # Получаем state_data
                    state_data = user_state.get("data", {})
                    max_participants = state_data.get("max_participants", 0)
                    await self.create_poll_from_template_with_max_participants(
                        update, 
                        state_data["template_id"], 
                        state_data["question"], 
                        state_data["options"], 
                        state_data["values"], 
                        state_data["threshold"], 
                        non_anonymous=state_data["non_anonymous"], 
                        chat_id=state_data["chat_id"], 
                        user_id=user_id, 
                        max_participants=max_participants,
                        decision_number=num
                    )
                    self.clear_user_state(user_id)
                except ValueError:
                    await self.send_message(update, "❌ Введите целое число!", self.menus.back_menu("main"))
                return
            elif state == UserState.WAITING_TEMPLATE_THRESHOLD:
                try:
                    threshold = int(text)
                    user_settings = self.get_user_settings(user_id)
                    user_settings['threshold'] = threshold
                    self.set_user_settings(user_id, user_settings)
                    await self.finalize_template_creation(update, state_data["name"], state_data["question"], state_data["variables"], state_data["options"])
                    return
                except ValueError:
                    await self.send_message(update, "❌ Введите целое число!", self.menus.back_menu("main"))
                return
            elif state == UserState.WAITING_EDIT_TEMPLATE_THRESHOLD:
                state_data = user_state.get("data", {})
                is_template_creation = state_data.get("is_template_creation", False)
                try:
                    threshold = int(text)
                    template_id = state_data.get("template_id")
                    name = state_data.get("name", "")
                    if not template_id:
                        await self.send_message(update, "❌ Не удалось определить шаблон.", self.menus.back_menu("templates"))
                        self.clear_user_state(user_id)
                        return
                    # Обновляем threshold в таблице templates
                    success = self.db.execute("UPDATE templates SET threshold = ? WHERE id = ?", (threshold, template_id))
                    if success:
                        self.clear_user_state(user_id)
                        await self.send_message(update, f"✅ Порог шаблона **{name}** обновлён: {threshold}%", self.menus.back_menu("templates"))
                    else:
                        await self.send_message(update, "❌ Ошибка обновления порога шаблона", self.menus.back_menu("templates"))
                    return
                except ValueError:
                    if is_template_creation:
                        state_data["is_template_creation"] = True
                    await self.send_message(update, "❌ Введите целое число!", self.menus.back_menu("main"))
                return
            elif state == UserState.WAITING_TEMPLATE_CREATION_THRESHOLD:
                state_data = user_state.get("data", {})
                is_template_creation = state_data.get("is_template_creation", False)
                try:
                    threshold = int(text)
                    if threshold < 1 or threshold > 100:
                        if is_template_creation:
                            state_data["is_template_creation"] = True
                        await self.send_message(update, "❌ Порог должен быть от 1 до 100%!", self.menus.back_menu("main"))
                        return
                    # Получаем данные для создания шаблона
                    name = state_data.get("name", "")
                    question = state_data.get("question", "")
                    variables = state_data.get("variables", [])
                    options = state_data.get("options", [])
                    max_participants = state_data.get("max_participants", 0)
                    user_id = update.effective_user.id
                    
                    # Создаем шаблон с порогом
                    cleaned_options = [self.clean_poll_option(opt) for opt in options]
                    success = self.db.execute(
                        "INSERT INTO templates (name, question, options, variables, created_by, max_participants, threshold) VALUES (?, ?, ?, ?, ?, ?, ?)",
                        (name, question, "|".join(cleaned_options), json.dumps(variables), user_id, max_participants, threshold)
                    )
                    
                    if success:
                        self.clear_user_state(user_id)
                        await self.send_message(
                            update,
                            f"✅ Шаблон **{name}** сохранён!\n\n"
                            f"❓ Вопрос: {question}\n"
                            f"📋 Варианты: {', '.join(options)}\n"
                            f"🎯 Порог: {threshold}%\n"
                            f"👥 Максимум участников: {max_participants if max_participants else 'не ограничено'}"
                        )
                        return
                    else:
                        await self.send_message(update, "❌ Ошибка сохранения шаблона")
                        return
                except ValueError:
                    await self.send_message(update, "❌ Введите целое число!", self.menus.back_menu("main"))
                return
            elif state == UserState.WAITING_MAX_PARTICIPANTS:
                try:
                    max_participants = int(text)
                    state_data = user_state.get("data", {})
                    is_template_creation = state_data.get("is_template_creation", False)

                    if "is_template" in state_data and state_data["is_template"]:
                        # Создание опроса из шаблона - запрашиваем порог
                        template_id = state_data.get("template_id")
                        question = state_data.get("question", "")
                        options = state_data.get("options", "")
                        values = state_data.get("values", {})
                        threshold = state_data.get("threshold", 50)
                        non_anonymous = state_data.get("non_anonymous", False)
                        chat_id = state_data.get("chat_id")
                        user_id = update.effective_user.id
                        
                        # Сохраняем max_participants и переходим к запросу порога
                        state_data["max_participants"] = max_participants
                        #state_data["is_template_creation"] = True
                        self.set_user_state(user_id, UserState.WAITING_TEMPLATE_POLL_THRESHOLD, state_data)
                        
                        await self.send_message(
                            update,
                            f"🎯 **Порог принятия решения**\n\n"
                            f"Введите процент голосов для принятия решения (по умолчанию {threshold}%):"
                        )
                        return
                    elif is_template_creation:
                        # Это создание шаблона - запрашиваем порог
                        name = state_data.get("name", "")
                        question = state_data.get("question", "")
                        variables = state_data.get("variables", [])
                        options = state_data.get("options", [])
                        user_id = update.effective_user.id
                        
                        # Сохраняем max_participants и переходим к запросу порога
                        state_data["max_participants"] = max_participants
                        self.set_user_state(user_id, UserState.WAITING_TEMPLATE_CREATION_THRESHOLD, state_data)
                        
                        await self.send_message(
                            update,
                            f"🎯 **Порог принятия решения**\n\n"
                            f"Введите процент голосов для принятия решения (по умолчанию 50%):"
                        )
                        return
                    else:
                        # Обычный опрос - запрашиваем порог
                        question = state_data.get("question", "")
                        options = state_data.get("options", [])
                        poll_type = state_data.get("poll_type", "simple")
                        
                        # Сохраняем max_participants и переходим к запросу порога
                        state_data["max_participants"] = max_participants
                        self.set_user_state(user_id, UserState.WAITING_POLL_THRESHOLD, state_data)
                        
                        await self.send_message(
                            update,
                            f"🎯 **Порог принятия решения**\n\n"
                            f"Введите процент голосов для принятия решения (по умолчанию 50%):"
                        )
                        return
                except ValueError:
                    state_data = user_state.get("data", {})
                    if state_data.get("is_template_creation", False):
                        state_data["is_template_creation"] = True
                    await self.send_message(update, "❌ Введите целое число!", self.menus.back_menu("main"))
                return
            elif state == UserState.WAITING_TEMPLATE_POLL_THRESHOLD:
                try:
                    threshold = int(text)
                    if threshold < 1 or threshold > 100:
                        await self.send_message(update, "❌ Порог должен быть от 1 до 100%!")
                        return
                    
                    # Получаем данные для создания опроса из шаблона
                    template_id = state_data.get("template_id")
                    question = state_data.get("question", "")
                    options = state_data.get("options", "")
                    values = state_data.get("values", {})
                    non_anonymous = state_data.get("non_anonymous", False)
                    chat_id = state_data.get("chat_id")
                    max_participants = state_data.get("max_participants", 0)
                    user_id = update.effective_user.id
                    
                    # Создаем опрос из шаблона с порогом
                    await self.create_poll_from_template_with_max_participants(
                        update, template_id, question, options, values, threshold, 
                        non_anonymous=non_anonymous, chat_id=chat_id, user_id=user_id, max_participants=max_participants
                    )
                    self.clear_user_state(user_id)
                except ValueError:
                    await self.send_message(update, "❌ Введите целое число!", self.menus.back_menu("main"))
                return
            elif state == UserState.WAITING_POLL_THRESHOLD:
                try:
                    threshold = int(text)
                    if threshold < 1 or threshold > 100:
                        await self.send_message(update, "❌ Порог должен быть от 1 до 100%!")
                        return
                    
                    # Получаем данные для создания опроса
                    question = state_data.get("question", "")
                    options = state_data.get("options", [])
                    poll_type = state_data.get("poll_type", "simple")
                    max_participants = state_data.get("max_participants", 0)
                    chat_id = update.message.chat_id
                    non_anonymous = self.config.get('non_anonymous_voting', False)
                    voting_type = self.determine_voting_type(options)
                    
                    # Создаем опрос с порогом
                    success = await self.create_poll(
                        question, options, chat_id, user_id, None, threshold, non_anonymous, voting_type, max_participants
                    )
                    
                    if success:
                        self.clear_user_state(user_id)
                        options_text = "\n".join([f"• {opt}" for opt in options])
                        voting_type_text = self.get_voting_type_text(voting_type)
                        await self.send_message(
                            update,
                            f"✅ Голосование создано!\n\n"
                            f"❓ **{question}**\n\n"
                            f"📋 Варианты:\n{options_text}\n\n"
                            f"🎯 Порог: {threshold}%{voting_type_text}\n"
                            f"👥 Максимум участников: {max_participants if max_participants else 'не ограничено'}"
                        )
                    else:
                        await self.send_message(update, "❌ Ошибка создания голосования")
                except ValueError:
                    await self.send_message(update, "❌ Введите целое число!", self.menus.back_menu("main"))
                return
#            else:
#                # Quick poll creation
#                await self.handle_quick_poll_creation(update, text)

        except Exception as e:
            logger.error(f"Text handler error for user {user_id}: {e}")
            self.clear_user_state(user_id)
            await self.send_message(update, "❌ Произошла ошибка. Попробуйте снова.")

    async def handle_poll_question_input(self, update: Update, text: str, state_data: Dict):
        """Handle poll question input with validation"""
        user_id = update.effective_user.id

        # Проверяем, это создание нового опроса или редактирование
        edit_type = state_data.get("type")

        if edit_type == "edit_question":
            # Редактирование вопроса существующего опроса
            poll_id = state_data.get("poll_id")

            # Проверяем права на редактирование
            poll_data = self.db.query("SELECT creator_id FROM polls WHERE poll_id = ?", (poll_id,))
            if not poll_data:
                await self.send_message(update, "❌ Голосование не найдено")
                self.clear_user_state(user_id)
                return

            creator_id = poll_data[0][0]
            user_perms = self.get_permissions(user_id)

            # Allow editing only if user is creator or admin
            if user_id != creator_id and user_perms != "admin":
                await self.send_message(update, "❌ Недостаточно прав для редактирования опроса")
                self.clear_user_state(user_id)
                return

            if len(text) > MAX_POLL_QUESTION:
                await self.send_message(update, f"❌ Вопрос слишком длинный (макс. {MAX_POLL_QUESTION} символов)")
                return

            # Обновляем вопрос в базе данных
            success = self.db.execute("UPDATE polls SET question = ? WHERE poll_id = ?", (text, poll_id))

            if success:
                self.clear_user_state(user_id)
                await self.send_message(update, f"✅ Вопрос обновлен: **{text}**")
                logger.info(f"Poll question updated: {poll_id} by user {user_id}")
            else:
                await self.send_message(update, "❌ Ошибка обновления вопроса")

            return

        # Создание нового опроса (существующая логика)
        # Проверяем права на создание опросов
        if self.get_permissions(user_id) not in ["create", "admin"]:
            await self.send_message(update, "❌ Недостаточно прав для создания голосований")
            self.clear_user_state(user_id)
            return

        if len(text) > MAX_POLL_QUESTION:
            await self.send_message(update, f"❌ Вопрос слишком длинный (макс. {MAX_POLL_QUESTION} символов)")
            return

        poll_type = state_data.get("type", "simple")
        new_state_data = {**state_data, "question": text, "options": []}
        self.set_user_state(user_id, UserState.WAITING_POLL_OPTION, new_state_data)

        await self.send_message(update, f"❓ Вопрос: **{text}**\n\n📝 Введите первый вариант ответа:",
                               reply_markup=InlineKeyboardMarkup([[
                                   InlineKeyboardButton("⬅️ Назад", callback_data="create_poll")
                               ]]))

    async def handle_poll_options_input(self, update: Update, text: str, state_data: Dict):
        """Handle poll options input with validation"""
        user_id = update.effective_user.id

        # Проверяем, это создание нового опроса или редактирование
        edit_type = state_data.get("type")

        if edit_type == "edit_options":
            # Редактирование вариантов существующего опроса
            poll_id = state_data.get("poll_id")

            # Проверяем права на редактирование
            poll_data = self.db.query("SELECT creator_id FROM polls WHERE poll_id = ?", (poll_id,))
            if not poll_data:
                await self.send_message(update, "❌ Голосование не найдено")
                self.clear_user_state(user_id)
                return

            creator_id = poll_data[0][0]
            user_perms = self.get_permissions(user_id)

            # Allow editing only if user is creator or admin
            if user_id != creator_id and user_perms != "admin":
                await self.send_message(update, "❌ Недостаточно прав для редактирования опроса")
                self.clear_user_state(user_id)
                return

            options = [self.clean_poll_option(opt.strip()) for opt in text.split(",") if opt.strip()]

            # Валидация вариантов
            if len(options) < 2:
                await self.send_message(update, "❌ Должно быть минимум 2 варианта ответа")
                return

            if len(options) > 10:
                await self.send_message(update, "❌ Максимум 10 вариантов ответа")
                return

            for option in options:
                if len(option) > 100:
                    await self.send_message(update, "❌ Вариант ответа слишком длинный (макс. 100 символов)")
                    return

            # Обновляем варианты в базе данных
            cleaned_options = [self.clean_poll_option(opt) for opt in options]
            options_str = "|".join(cleaned_options)
            success = self.db.execute("UPDATE polls SET options = ? WHERE poll_id = ?", (options_str, poll_id))

            if success:
                self.clear_user_state(user_id)
                options_text = "\n".join([f"{i+1}. {opt}" for i, opt in enumerate(options)])
                await self.send_message(update, f"✅ Варианты обновлены:\n\n{options_text}")
                logger.info(f"Poll options updated: {poll_id} by user {user_id}")
            else:
                await self.send_message(update, "❌ Ошибка обновления вариантов")

            return

        # Создание нового опроса (существующая логика)
        # Проверяем права на создание опросов
        if self.get_permissions(user_id) not in ["create", "admin"]:
            await self.send_message(update, "❌ Недостаточно прав для создания голосований")
            self.clear_user_state(user_id)
            return

        question = state_data.get("question", "")
        poll_type = state_data.get("type", "simple")

        options = [self.clean_poll_option(opt.strip()) for opt in text.split(",") if opt.strip()]

        valid, error_msg = self.validate_poll_data(question, options)
        if not valid:
            await self.send_message(update, f"❌ {error_msg}\n\nПопробуйте еще раз:")
            return

        # Get default threshold
        threshold = self.config.get('default_decision_threshold', 50)
        non_anonymous = self.config.get('non_anonymous_voting', False)

        # Автоматически определяем тип голосования
        voting_type = self.determine_voting_type(options)
        
        success = await self.create_poll(question, options, update.message.chat_id, user_id,
                                       None, threshold, non_anonymous, voting_type)

        if success:
            self.clear_user_state(user_id)
            
            # Добавляем информацию о типе голосования в сообщение
            voting_type_text = self.get_voting_type_text(voting_type)
            
            await self.send_message(update, f"✅ Голосование создано!\n\n❓ {question}\n🎯 Порог: {threshold}%{voting_type_text}")
        else:
            await self.send_message(update, "❌ Ошибка создания голосования")

    async def handle_quick_poll_creation(self, update: Update, text: str):
        """Handle quick poll creation from direct message"""
        user_id = update.effective_user.id

        if self.get_permissions(user_id) not in ["create", "admin"]:
            await self.send_message(update, "❌ Недостаточно прав для создания голосований")
            return

        if len(text) > MAX_POLL_QUESTION:
            await self.send_message(update, f"❌ Вопрос слишком длинный (макс. {MAX_POLL_QUESTION} символов)")
            return

        self.set_user_state(user_id, UserState.WAITING_POLL_OPTION, {"question": text, "type": "quick", "options": []})
        await self.send_message(update, f"❓ Вопрос: **{text}**\n\n📝 Введите первый вариант ответа:",
                               reply_markup=InlineKeyboardMarkup([[
                                   InlineKeyboardButton("⬅️ Назад", callback_data="back_to_main")
                               ]]))

    @error_handler
    async def inline_query_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Enhanced inline query handler"""
        logger.debug("InlineQueryHandler вызван!")
        query = update.inline_query.query
        user_id = update.inline_query.from_user.id

        logger.debug(f"Inline query from user {user_id}: '{query}'")

        if self.get_permissions(user_id) not in ["create", "admin"]:
            logger.debug(f"User {user_id} has insufficient permissions")
            await update.inline_query.answer([])
            return

        results = []
        bot_username = context.bot.username

        # Обрабатываем запросы для шаринга опросов
        if query.startswith("share_"):
            logger.debug("Обрабатываем share_ запрос!")
            logger.debug(f"Processing share request: {query}")
            poll_id = query.split("_", 1)[1]
            logger.debug(f"Extracted poll_id: {poll_id}")
            poll_data = self.db.query("""
                SELECT question, options, threshold, non_anonymous, decision_number,
                       created_date, template_used, creator_id, decision_status
                FROM polls WHERE poll_id = ?
            """, (poll_id,))
            if not poll_data:
                logger.debug(f"Poll {poll_id} not found for sharing")
                await update.inline_query.answer([])
                return
            question, options_str, threshold, non_anonymous, decision_number, \
            created_date, template_used, creator_id, decision_status = poll_data[0]
            options = options_str.split('|')

            # Используем публичную версию без админских кнопок для пересылки
            text, keyboard = self.format_poll_message_public(poll_id, show_results=True, for_user_id=user_id)
            logger.debug(f"Formatted public poll message for sharing, text length: {len(text)}")
            results = [InlineQueryResultArticle(
                id=f"share_{poll_id}",
                title=f"📤 {question[:50]}{'...' if len(question) > 50 else ''}",
                description=f"Переслать опрос с {len(options)} вариантами",
                input_message_content=InputTextMessageContent(
                    text,
                    parse_mode=ParseMode.MARKDOWN
                ),
                reply_markup=keyboard
            )]
            logger.debug("Created InlineQueryResultArticle for sharing")
            await update.inline_query.answer(results, cache_time=0, is_personal=True)
            logger.debug(f"Отправлен share результат для poll {poll_id}")
            return

        # Если запрос пустой, показываем активные опросы по умолчанию
        if query == "":
            # Пустой запрос - показываем последние активные и закрытые
            logger.debug("Empty query, showing recent polls")
            
            # Активные опросы (последние 6)
            active_polls = self.get_active_polls(limit=6)
            logger.debug(f"Found {len(active_polls)} active polls")
            
            for poll in active_polls:
                poll_id = poll["poll_id"]
                question = poll["question"]
                options = poll["options"].split("|")
                options_preview = ", ".join(options[:3])
                if len(options) > 3:
                    options_preview += "..."

                text, keyboard = self.format_poll_message_public(poll_id, show_results=True, for_user_id=user_id)
                deeplink = f"https://t.me/{bot_username}?start=showpoll_{poll_id}"

                results.append(InlineQueryResultArticle(
                    id=f"active_{poll_id}",
                    title=f"🗳️ {question[:50]}{'...' if len(question) > 50 else ''}",
                    description=f"Активный • {options_preview}",
                    input_message_content=InputTextMessageContent(
                        f"👉 [Открыть опрос]({deeplink})\n\n{text}",
                        parse_mode=ParseMode.MARKDOWN
                    ),
                    reply_markup=keyboard
                ))

            # Закрытые опросы (последние 4)
            closed_polls = self.get_closed_polls(user_id, limit=4)
            logger.debug(f"Found {len(closed_polls)} closed polls")
            
            for poll in closed_polls:
                poll_id = poll["poll_id"]
                question = poll["question"]
                options = poll["options"].split("|")
                options_preview = ", ".join(options[:3])
                if len(options) > 3:
                    options_preview += "..."

                text, keyboard = self.format_poll_message_public(poll_id, show_results=True, for_user_id=user_id)
                deeplink = f"https://t.me/{bot_username}?start=showpoll_{poll_id}"

                results.append(InlineQueryResultArticle(
                    id=f"closed_{poll_id}",
                    title=f"🔒 [Закрыт] {question[:50]}{'...' if len(question) > 50 else ''}",
                    description=f"Закрытый • {options_preview}",
                    input_message_content=InputTextMessageContent(
                        f"👉 [Открыть опрос]({deeplink})\n\n{text}",
                        parse_mode=ParseMode.MARKDOWN
                    ),
                    reply_markup=keyboard
                ))

        else:
            # ПОИСК ПО КЛЮЧЕВЫМ СЛОВАМ
            logger.debug(f"Searching polls with query: '{query}'")
            
            # Получаем все опросы пользователя для поиска
            all_active_polls = self.get_active_polls(limit=50)  # Больше для поиска
            all_closed_polls = self.get_closed_polls(user_id, limit=50)  # Больше для поиска
            
            query_lower = query.lower()
            
            # Поиск среди активных опросов
            matching_active = []
            for poll in all_active_polls:
                if (query_lower in poll["question"].lower() or 
                    query_lower in poll["options"].lower()):
                    matching_active.append(poll)
            
            # Поиск среди закрытых опросов
            matching_closed = []
            for poll in all_closed_polls:
                if (query_lower in poll["question"].lower() or 
                    query_lower in poll["options"].lower()):
                    matching_closed.append(poll)
            
            logger.debug(f"Found {len(matching_active)} matching active, {len(matching_closed)} matching closed")
            
            # Добавляем результаты активных опросов (до 8)
            for poll in matching_active[:8]:
                poll_id = poll["poll_id"]
                question = poll["question"]
                options = poll["options"].split("|")
                options_preview = ", ".join(options[:3])
                if len(options) > 3:
                    options_preview += "..."

                text, keyboard = self.format_poll_message_public(poll_id, show_results=True, for_user_id=user_id)
                deeplink = f"https://t.me/{bot_username}?start=showpoll_{poll_id}"

                results.append(InlineQueryResultArticle(
                    id=f"search_active_{poll_id}",
                    title=f"🗳️ {question[:50]}{'...' if len(question) > 50 else ''}",
                    description=f"Активный • {options_preview}",
                    input_message_content=InputTextMessageContent(
                        f"👉 [Открыть опрос]({deeplink})\n\n{text}",
                        parse_mode=ParseMode.MARKDOWN
                    ),
                    reply_markup=keyboard
                ))
            
            # Добавляем результаты закрытых опросов (до 12, чтобы всего было 20)
            remaining_slots = max(0, 12 - len(matching_active))
            for poll in matching_closed[:remaining_slots]:
                poll_id = poll["poll_id"]
                question = poll["question"]
                options = poll["options"].split("|")
                options_preview = ", ".join(options[:3])
                if len(options) > 3:
                    options_preview += "..."

                text, keyboard = self.format_poll_message_public(poll_id, show_results=True, for_user_id=user_id)
                deeplink = f"https://t.me/{bot_username}?start=showpoll_{poll_id}"

                results.append(InlineQueryResultArticle(
                    id=f"search_closed_{poll_id}",
                    title=f"🔒 [Закрыт] {question[:50]}{'...' if len(question) > 50 else ''}",
                    description=f"Закрытый • {options_preview}",
                    input_message_content=InputTextMessageContent(
                        f"👉 [Открыть опрос]({deeplink})\n\n{text}",
                        parse_mode=ParseMode.MARKDOWN
                    ),
                    reply_markup=keyboard
                ))
            
            # Если ничего не найдено
            if not results:
                results.append(InlineQueryResultArticle(
                    id="no_results",
                    title=f"Не найдено опросов по запросу: {query}",
                    description="Попробуйте другие ключевые слова",
                    input_message_content=InputTextMessageContent(
                        f"🔍 Не найдено опросов по запросу: **{query}**\n\nПопробуйте:\n• Другие ключевые слова\n• Часть названия опроса\n• Оставить пустой запрос для просмотра последних",
                        parse_mode=ParseMode.MARKDOWN
                    )
                ))

        # Добавляем подсказки, если результатов мало
        if len(results) < 3 and query == "":
            results.append(InlineQueryResultArticle(
                id="search_hint",
                title="💡 Как найти опрос?",
                description="Введите ключевые слова для поиска среди всех опросов",
                input_message_content=InputTextMessageContent(
                    "🔍 **Как найти нужный опрос:**\n\n• Оставьте пустой запрос - покажутся последние опросы\n• Введите ключевые слова из названия опроса\n• Введите часть текста из вариантов ответа\n\nПример: \"решение\", \"кандидат\", \"бюджет\"",
                    parse_mode=ParseMode.MARKDOWN
                )
            ))

        await update.inline_query.answer(results, cache_time=30)
        logger.debug(f"Отправлено {len(results)} результатов для запроса '{query}'")

    async def cleanup_old_data(self):
        """Enhanced cleanup with proper error handling"""
        try:
            cutoff_time = datetime.now() - timedelta(seconds=SESSION_TIMEOUT)
            cutoff_str = cutoff_time.isoformat()

            old_sessions = self.db.query("SELECT COUNT(*) FROM template_sessions WHERE created_date < ?", (cutoff_str,))
            sessions_count = old_sessions[0][0] if old_sessions else 0

            self.db.execute("DELETE FROM template_sessions WHERE created_date < ?", (cutoff_str,))

            hour_ago = (datetime.now() - timedelta(hours=1)).isoformat()
            self.db.execute("DELETE FROM user_states WHERE state = ? AND updated_date < ?", (UserState.IDLE, hour_ago))

            self.rate_limiter.cleanup()

            if sessions_count > 0:
                logger.info(f"Cleaned up {sessions_count} old template sessions")

        except Exception as e:
            logger.error(f"Cleanup error: {e}")

    async def periodic_cleanup(self):
        """Periodic cleanup task with proper error handling and log rotation"""
        while True:
            try:
                await asyncio.sleep(1800)  # 30 minutes

                # Очистка старых данных
                await self.cleanup_old_data()

                # Автоматическая ротация логов (каждые 30 минут проверяем размер)
                try:
                    LogManager.rotate_logs(max_size_mb=5)  # Ротация при превышении 5MB
                except Exception as e:
                    logger.error(f"Log rotation error: {e}")

            except asyncio.CancelledError:
                logger.info("Cleanup task cancelled")
                break
            except Exception as e:
                logger.error(f"Cleanup task error: {e}")
                await asyncio.sleep(300)  # 5 minutes on error

    async def run(self):
        """Enhanced main bot runner with token validation"""
        if not self.config.get("bot_token"):
            logger.error("Bot token not configured!")
            return

        try:
            self.application = Application.builder().token(self.config["bot_token"]).build()

            # Add handlers
            handlers = [
                CommandHandler("start", self.start_command),
                CommandHandler("create", self.create_command),
                CommandHandler("templates", self.templates_command),
                CommandHandler("status", self.status_command),
                CommandHandler("help", self.help_command),
                CommandHandler("admin", self.admin_command),
                CommandHandler("users", self.users_command),
                CommandHandler("grant", self.grant_command),
                CommandHandler("revoke", self.revoke_command),
                CommandHandler("delete_user", self.delete_user_command),
                CallbackQueryHandler(self.callback_handler),
                InlineQueryHandler(self.inline_query_handler),
                MessageHandler(filters.TEXT & ~filters.COMMAND, self.text_handler)
            ]

            for handler in handlers:
                self.application.add_handler(handler)

            # Start cleanup task
            self._cleanup_task = asyncio.create_task(self.periodic_cleanup())

            logger.info("Starting PollsBot v2.0...")
            logger.info("🚀 PollsBot запущен и готов к работе!")

            # Прямой запуск без asyncio.run()
            self.application.run_polling(poll_interval=self.config.get("polling_interval", 2))

        except Exception as e:
            logger.error(f"Bot error: {e}")
            raise

    @error_handler
    async def handle_template_name_input(self, update: Update, text: str):
        """Handle template name input with validation"""
        user_id = update.effective_user.id

        # Очищаем старые template_sessions для этого пользователя
        self.db.execute("DELETE FROM template_sessions WHERE user_id = ?", (user_id,))

        # Проверяем права на создание шаблонов
        if self.get_permissions(user_id) not in ["create", "admin"]:
            await self.send_message(update, "❌ Недостаточно прав для создания шаблонов")
            self.clear_user_state(user_id)
            return

        name = self.sanitize(text, MAX_TEMPLATE_NAME)
        if not re.match(r'^[\w\s\-]{3,50}$', name, re.UNICODE):
            await self.send_message(update, "❌ Название должно быть буквами, цифрами, пробелами, _, - (3-50 символов)")
            return
        # Check if template exists
        exists = self.db.query("SELECT name FROM templates WHERE name = ?", (name,))
        if exists:
            await self.send_message(update, "❌ Шаблон с таким названием уже существует")
            return
        self.set_user_state(user_id, UserState.WAITING_TEMPLATE_QUESTION, {"name": name})
        explanation = (
            "ℹ️ Шаблоны позволяют быстро создавать голосования с переменными. "
            "В тексте вопроса и вариантах ответа вы можете использовать переменные в фигурных скобках, например: {Имя}, {Дата}, {Сумма}. "
            "Перед публикацией бот попросит ввести значения для этих переменных.\n\n"
            "⚠️ **Важно:** Внутри самих переменных нельзя использовать фигурные скобки {} — это нарушит работу шаблона.\n\n"
            "Пример: Вопрос — 'Согласны ли вы с решением для {Имя} от {Дата}?'\n"
            "Варианты — 'Да', 'Нет', 'Воздержался'."
        )
        await self.send_message(update, f"📋 Название: **{name}**\n\n{explanation}\n📝 Введите текст вопроса (можно использовать {{X}}, {{Y}}, ...):",
                               reply_markup=InlineKeyboardMarkup([[
                                   InlineKeyboardButton("⬅️ Назад", callback_data="back_to_main")
                               ]]))

    @error_handler
    async def handle_template_question_input(self, update: Update, text: str, state_data: Dict):
        """Handle template question input with variable extraction"""
        user_id = update.effective_user.id

        # Проверяем права на создание шаблонов
        if self.get_permissions(user_id) not in ["create", "admin"]:
            await self.send_message(update, "❌ Недостаточно прав для создания шаблонов")
            self.clear_user_state(user_id)
            return

        name = state_data.get("name", "")
        question = self.sanitize(text, MAX_POLL_QUESTION)
        if not question:
            await self.send_message(update, "❌ Вопрос не может быть пустым")
            return
        variables = self.extract_variables(question)
        self.set_user_state(user_id, UserState.WAITING_TEMPLATE_OPTION, {"name": name, "question": question, "variables": variables, "options": []})
        await self.send_message(update, f"❓ Вопрос: **{question}**\n\n📝 Введите первый вариант ответа для шаблона:",
                               reply_markup=InlineKeyboardMarkup([[
                                   InlineKeyboardButton("⬅️ Назад", callback_data="new_template")
                               ]]))

    @error_handler
    async def handle_template_option_input(self, update: Update, text: str, state_data: Dict):
        user_id = update.effective_user.id

        # ИСПРАВЛЕНИЕ: Проверяем, что мы действительно создаем шаблон
        poll_type = state_data.get("type", "")
        is_template_creation = state_data.get("is_template_creation", False)
        
        logger.info(f"handle_template_option_input: user_id={user_id}, poll_type='{poll_type}', is_template_creation={is_template_creation}")
        
        if poll_type == "simple" and not is_template_creation:
            # Это простое голосование, а не шаблон! Перенаправляем на правильную функцию
            logger.warning(f"Redirecting simple poll creation from template handler to poll handler for user {user_id}")
            await self.handle_poll_option_input(update, text, state_data)
            return

        if self.get_permissions(user_id) not in ["create", "admin"]:
            await self.send_message(update, "❌ Недостаточно прав для создания шаблонов")
            self.clear_user_state(user_id)
            return

        name = state_data.get("name", "")
        question = state_data.get("question", "")
        variables = state_data.get("variables", [])
        options = state_data.get("options", [])

        if not text or len(text.strip()) == 0:
            await self.send_message(update, "❌ Вариант ответа не может быть пустым. Попробуйте еще раз:")
            return

        if len(text) > MAX_POLL_OPTION:
            await self.send_message(update, f"❌ Вариант слишком длинный (макс. {MAX_POLL_OPTION} символов). Попробуйте еще раз:")
            return

        option = self.clean_poll_option(text.strip())
        options.append(option)

        if len(options) < 2:
            await self.send_message(update, f"✅ Вариант {len(options)}: **{option}**\n\n📝 Введите следующий вариант ответа:",
                                   reply_markup=InlineKeyboardMarkup([[\
                                       InlineKeyboardButton("⬅️ Назад", callback_data="create_poll")
                                   ]]))
            new_state_data = {**state_data, "options": options}
            self.set_user_state(user_id, UserState.WAITING_POLL_OPTION, new_state_data)
            return

        max_options = self.config.get('max_poll_options', 10)
        if len(options) >= max_options:
            await self.finalize_template_creation(update, name, question, variables, options)
            return

        options_text = "\n".join([f"{i+1}. **{opt}**" for i, opt in enumerate(options)])
        await self.send_message(
            update,
            f"✅ Вариант {len(options)}: **{option}**\n\n"
            f"📋 Текущие варианты:\n{options_text}\n\n"
            f"📝 Введите следующий вариант ответа или нажмите 'Завершить создание':",
            self.menus.finish_template_menu()
        )
        new_state_data = {**state_data, "options": options}
        self.set_user_state(user_id, UserState.WAITING_TEMPLATE_OPTION, new_state_data)

    @error_handler
    async def finalize_template_creation(self, update_or_query, name, question, variables, options):
        user_id = (
            update_or_query.effective_user.id
            if hasattr(update_or_query, "effective_user")
            else update_or_query.from_user.id
        )

        # Очищаем старые template_sessions для этого пользователя
        self.db.execute("DELETE FROM template_sessions WHERE user_id = ?", (user_id,))

        if len(options) < 2:
            await self.send_message(update_or_query, "❌ Нужно минимум 2 варианта ответа для шаблона")
            return

        valid, error_msg = self.validate_poll_data(question, options)
        if not valid:
            await self.send_message(update_or_query, f"❌ {error_msg}")
            return

        # Запрашиваем максимальное количество участников
        self.set_user_state(user_id, UserState.WAITING_MAX_PARTICIPANTS, {
            "name": name,
            "question": question,
            "variables": variables,
            "options": options,
            "is_template_creation": True  # Добавляем флаг для идентификации создания шаблона
        })
        await self.send_message(
            update_or_query,
            "👥 **Максимальное количество участников**\n\n"
            "Введите число участников или 0 для неограниченного количества:"
        )

    @error_handler
    async def handle_template_options_input(self, update: Update, text: str, state_data: Dict):
        """Handle template options input and save template"""
        user_id = update.effective_user.id

        # Проверяем права на создание шаблонов
        if self.get_permissions(user_id) not in ["create", "admin"]:
            await self.send_message(update, "❌ Недостаточно прав для создания шаблонов")
            self.clear_user_state(user_id)
            return

        name = state_data.get("name", "")
        question = state_data.get("question", "")
        variables = state_data.get("variables", [])
        options = [self.clean_poll_option(opt.strip()) for opt in text.split("|") if opt.strip()]
        valid, error_msg = self.validate_poll_data(question, options)
        if not valid:
            await self.send_message(update, f"❌ {error_msg}\n\nПопробуйте еще раз:")
            return
        
        # Запрашиваем максимальное количество участников
        self.set_user_state(user_id, UserState.WAITING_MAX_PARTICIPANTS, {
            "name": name,
            "question": question,
            "variables": variables,
            "options": options,
            "is_template_creation": True  # Добавляем флаг для идентификации создания шаблона
        })
        await self.send_message(
            update,
            "👥 **Максимальное количество участников**\n\n"
            "Введите число участников или 0 для неограниченного количества:"
        )

    # Административные команды
    @error_handler
    @permission_required(["admin"])
    async def admin_command(self, update_or_query, context: ContextTypes.DEFAULT_TYPE):
        user_id, chat_id = self.get_user_and_chat_id(update_or_query)
        logger.info(f"admin_command called: user_id={user_id}, chat_id={chat_id}")
        if chat_id is None:
            logger.error("admin_command: chat_id is None")
            await self.send_message(update_or_query, "❌ Не удалось определить чат.")
            return
        if user_id is None:
            logger.error("admin_command: user_id is None")
            await self.send_message(update_or_query, "❌ Не удалось определить пользователя.")
            return
        try:
            permissions = self.get_permissions(user_id)
            logger.info(f"admin_command: permissions={permissions}")
            menu = self.menus.admin_menu()
            try:
                menu_dict = menu.to_dict() if hasattr(menu, 'to_dict') else str(menu)
            except Exception as e:
                menu_dict = f"[menu to_dict error: {e}]"
            logger.info(f"admin_command: menu={menu_dict}")
            logger.info(f"admin_command: about to send message with text='🛠 **Панель администратора**\\n\\nВыберите действие:'")
            await self.send_message(update_or_query, "🛠 **Панель администратора**\n\nВыберите действие:", menu)
        except Exception as e:
            import traceback
            logger.error(f"admin_command send_message error: {e}\n{traceback.format_exc()}")
            if hasattr(update_or_query, 'edit_message_text'):
                await update_or_query.edit_message_text("❌ Внутренняя ошибка. Обратитесь к администратору.")
            else:
                await self.send_message(update_or_query, "❌ Внутренняя ошибка. Обратитесь к администратору.")

    @error_handler
    async def users_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle /users command - список пользователей"""
        if update.effective_chat.type != "private":
            bot_username = getattr(context.bot, 'username', 'BotName')
            await self.send_message(update, f"❌ В группах команды не поддерживаются. Для публикации и голосования используйте inline-режим: @{bot_username} ...")
            return
        try:
            users = self.db.query("""
                SELECT user_id, username, permissions, last_activity
                FROM users
                ORDER BY last_activity DESC
                LIMIT 20
            """)

            if not users:
                await self.send_message(update, "📋 Пользователи не найдены")
                return

            text = "👥 **Последние 20 пользователей:**\n\n"

            for user in users:
                user_id, username, permissions, last_activity = user
                username = username or f"User{user_id}"

                # Определяем эмодзи для прав
                if permissions == "admin":
                    perm_emoji = "🛠"
                elif permissions == "create":
                    perm_emoji = "📝"
                else:
                    perm_emoji = "👤"

                # Форматируем дату
                try:
                    last_dt = datetime.fromisoformat(last_activity.replace('Z', '+00:00'))
                    last_str = last_dt.strftime('%d.%m %H:%M')
                except:
                    last_str = "неизвестно"

                text += f"{perm_emoji} **{username}** (`{user_id}`)\n"
                text += f"   Права: `{permissions}` | Активность: {last_str}\n\n"

            await self.send_message(update, text, self.menus.admin_users_menu())

        except Exception as e:
            logger.error(f"Users command error: {e}")
            await self.send_message(update, "❌ Ошибка получения списка пользователей")

    @error_handler
    async def grant_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle /grant command - выдать права пользователю"""
        if update.effective_chat.type != "private":
            bot_username = getattr(context.bot, 'username', 'BotName')
            await self.send_message(update, f"❌ В группах команды не поддерживаются. Для публикации и голосования используйте inline-режим: @{bot_username} ...")
            return
        if not context.args or len(context.args) < 2:
            await self.send_message(update,
                                   "❌ Неверный формат команды.\n\n"
                                   "Использование: `/grant <user_id> <rights>`\n\n"
                                   "Примеры:\n"
                                   "• `/grant 123456789 create` - выдать права на создание\n"
                                   "• `/grant 123456789 admin` - выдать админские права\n\n"
                                   "Доступные права: `use`, `create`, `admin`")
            return

        try:
            target_user_id = int(context.args[0])
            new_permissions = context.args[1].lower()

            # Проверяем валидность прав
            valid_permissions = ["use", "create", "admin"]
            if new_permissions not in valid_permissions:
                await self.send_message(update,
                                       f"❌ Неверные права: `{new_permissions}`\n\n"
                                       f"Доступные права: {', '.join(valid_permissions)}")
                return

            # Проверяем существование пользователя
            existing_user = self.db.query("SELECT username, permissions FROM users WHERE user_id = ?", (target_user_id,))

            if existing_user:
                old_permissions = existing_user[0][1]
                username = existing_user[0][0] or f"User{target_user_id}"

                # Обновляем права
                success = self.db.execute("UPDATE users SET permissions = ? WHERE user_id = ?",
                                        (new_permissions, target_user_id))

                if success:
                    await self.send_message(update,
                                           f"✅ Права пользователя обновлены!\n\n"
                                           f"👤 **{username}** (`{target_user_id}`)\n"
                                           f"🔄 `{old_permissions}` → `{new_permissions}`")
                else:
                    await self.send_message(update, "❌ Ошибка обновления прав")
            else:
                # Создаем нового пользователя
                success = self.db.execute("""
                    INSERT INTO users (user_id, username, permissions, last_activity)
                    VALUES (?, ?, ?, ?)
                """, (target_user_id, f"User{target_user_id}", new_permissions, datetime.now().isoformat()))

                if success:
                    await self.send_message(update,
                                           f"✅ Новый пользователь создан!\n\n"
                                           f"👤 **User{target_user_id}** (`{target_user_id}`)\n"
                                           f"🎯 Права: `{new_permissions}`")
                else:
                    await self.send_message(update, "❌ Ошибка создания пользователя")

        except ValueError:
            await self.send_message(update, "❌ Неверный ID пользователя. ID должен быть числом.")
        except Exception as e:
            logger.error(f"Grant command error: {e}")
            await self.send_message(update, "❌ Ошибка выполнения команды")

    @error_handler
    async def revoke_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle /revoke command - отозвать права пользователя"""
        if update.effective_chat.type != "private":
            bot_username = getattr(context.bot, 'username', 'BotName')
            await self.send_message(update, f"❌ В группах команды не поддерживаются. Для публикации и голосования используйте inline-режим: @{bot_username} ...")
            return
        if not context.args or len(context.args) < 1:
            await self.send_message(update,
                                   "❌ Неверный формат команды.\n\n"
                                   "Использование: `/revoke <user_id>`\n\n"
                                   "Примеры:\n"
                                   "• `/revoke 123456789` - отозвать права (установить 'use')\n\n"
                                   "⚠️ Команда устанавливает права 'use' (базовые)")
            return

        try:
            target_user_id = int(context.args[0])

            # Проверяем существование пользователя
            existing_user = self.db.query("SELECT username, permissions FROM users WHERE user_id = ?", (target_user_id,))

            if not existing_user:
                await self.send_message(update, "❌ Пользователь не найден")
                return

            old_permissions = existing_user[0][1]
            username = existing_user[0][0] or f"User{target_user_id}"

            # Отзываем права (устанавливаем 'use')
            success = self.db.execute("UPDATE users SET permissions = 'use' WHERE user_id = ?", (target_user_id,))

            if success:
                await self.send_message(update,
                                       f"✅ Права пользователя отозваны!\n\n"
                                       f"👤 **{username}** (`{target_user_id}`)\n"
                                       f"🔄 `{old_permissions}` → `use`")
            else:
                await self.send_message(update, "❌ Ошибка отзыва прав")

        except ValueError:
            await self.send_message(update, "❌ Неверный ID пользователя. ID должен быть числом.")
        except Exception as e:
            logger.error(f"Revoke command error: {e}")
            await self.send_message(update, "❌ Ошибка выполнения команды")

    @error_handler
    async def delete_user_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle /delete_user command - удалить пользователя"""
        if update.effective_chat.type != "private":
            bot_username = getattr(context.bot, 'username', 'BotName')
            await self.send_message(update, f"❌ В группах команды не поддерживаются. Для публикации и голосования используйте inline-режим: @{bot_username} ...")
            return
        if not context.args or len(context.args) < 1:
            await self.send_message(update,
                                   "❌ Неверный формат команды.\n\n"
                                   "Использование: `/delete_user <user_id>`\n\n"
                                   "Примеры:\n"
                                   "• `/delete_user 123456789` - удалить пользователя\n\n"
                                   "⚠️ **ВНИМАНИЕ:** Пользователь будет полностью удален из системы!")
            return

        try:
            target_user_id = int(context.args[0])

            # Проверяем существование пользователя
            existing_user = self.db.query("SELECT username, permissions FROM users WHERE user_id = ?", (target_user_id,))

            if not existing_user:
                await self.send_message(update, "❌ Пользователь не найден")
                return

            username = existing_user[0][0] or f"User{target_user_id}"
            permissions = existing_user[0][1]

            # Создаем клавиатуру подтверждения
            keyboard = [
                [InlineKeyboardButton("✅ Да, удалить", callback_data=f"confirm_delete:{target_user_id}")],
                [InlineKeyboardButton("❌ Отмена", callback_data="cancel_delete")]
            ]

            await self.send_message(update,
                                   f"⚠️ **Подтверждение удаления**\n\n"
                                   f"Вы действительно хотите удалить пользователя?\n\n"
                                   f"👤 **{username}** (`{target_user_id}`)\n"
                                   f"🎯 Права: `{permissions}`\n\n"
                                   f"🗑️ Это действие нельзя отменить!",
                                   InlineKeyboardMarkup(keyboard))

        except ValueError:
            await self.send_message(update, "❌ Неверный ID пользователя. ID должен быть числом.")
        except Exception as e:
            logger.error(f"Delete user command error: {e}")
            await self.send_message(update, "❌ Ошибка выполнения команды")

    async def handle_admin_callback(self, query, data: str):
        """Handle admin panel callbacks (buttons for all admin actions)"""
        user_id = query.from_user.id
        if self.get_permissions(user_id) != "admin":
            await query.answer("❌ Недостаточно прав", show_alert=True)
            return
        await query.answer()
        try:
            if data == "admin_users":
                await self.show_admin_users_list(query)
            elif data == "admin_stats":
                await self.show_admin_stats(query)
            elif data == "admin_logs":
                await query.edit_message_text(
                    "📋 **Управление логами**\n\nВыберите действие:",
                    reply_markup=self.menus.admin_logs_menu()
                )
            elif data == "admin_clear_logs_by_level":
                await query.edit_message_text(
                    "🔧 **Очистка логов по уровням**\n\nВыберите уровень для очистки:",
                    reply_markup=self.menus.admin_clear_logs_by_level_menu()
                )
            elif data == "admin_view_recent_logs":
                await query.edit_message_text(
                    "📄 **Просмотр логов**\n\nВыберите уровень для просмотра:",
                    reply_markup=self.menus.admin_view_logs_menu()
                )
            elif data == "admin_rotate_logs":
                await self.rotate_logs(query)
                await query.edit_message_text(
                    "🔄 **Ротация логов выполнена**",
                    reply_markup=self.menus.admin_logs_menu()
                )
            elif data == "admin_logs_levels":
                await query.edit_message_text(
                    "⚙️ **Управление уровнями логирования**\n\nНажмите на уровень для включения/выключения:",
                    reply_markup=self.menus.admin_logs_levels_menu()
                )
            # Добавляем обработку callback'ов для очистки логов по уровням
            elif data.startswith("admin_clear_logs:"):
                level = data.split(":")[1]
                success = await self.clear_logs_by_level(query, level)
                if success:
                    await query.edit_message_text(
                        f"✅ Логи уровня '{level}' очищены!",
                        reply_markup=self.menus.admin_clear_logs_by_level_menu()
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Ошибка очистки логов уровня '{level}'",
                        reply_markup=self.menus.admin_clear_logs_by_level_menu()
                    )
            # Добавляем обработку callback'ов для просмотра логов по уровням
            elif data.startswith("admin_view_logs:"):
                level = data.split(":")[1]
                text = await self.view_logs_by_level(query, level)
                await query.edit_message_text(
                    text,
                    reply_markup=self.menus.admin_view_logs_menu()
                )
            # Добавляем обработку callback'ов для переключения уровней логирования
            elif data.startswith("admin_toggle_logs:"):
                level = data.split(":")[1]
                message = await self.toggle_logs_by_level(query, level)
                await query.edit_message_text(
                    message,
                    reply_markup=self.menus.admin_logs_levels_menu()
                )
            elif data == "admin_third_party_loggers":
                await self.show_third_party_loggers_status(query)
            elif data.startswith("admin_setperm:"):
                target_user_id = int(data.split(":")[1])
                perms = [
                    ("use", "👤 use"),
                    ("create", "📝 create"),
                    ("admin", "🛠 admin")
                ]
                perm_buttons = [InlineKeyboardButton(label, callback_data=f"admin_perm_select:{target_user_id}:{p}") for p, label in perms]
                keyboard = [perm_buttons[i:i+2] for i in range(0, len(perm_buttons), 2)]
                keyboard.append([InlineKeyboardButton("🔙 Назад", callback_data="admin_users")])
                await query.edit_message_text(f"Выберите права для пользователя `{target_user_id}`:", reply_markup=InlineKeyboardMarkup(keyboard))
            elif data.startswith("admin_perm_select:"):
                _, target_user_id, new_perm = data.split(":")
                target_user_id = int(target_user_id)
                # Обновляем права
                self.db.execute("UPDATE users SET permissions = ? WHERE user_id = ?", (new_perm, target_user_id))
                await query.edit_message_text(f"✅ Права пользователя `{target_user_id}` обновлены на `{new_perm}`.")
                await self.show_admin_users_list(query)
            elif data.startswith("admin_revoke:"):
                target_user_id = int(data.split(":")[1])
                self.db.execute("UPDATE users SET permissions = 'use' WHERE user_id = ?", (target_user_id,))
                await query.edit_message_text(f"✅ Права пользователя `{target_user_id}` отозваны (установлено 'use').")
                await self.show_admin_users_list(query)
            elif data.startswith("admin_delete:"):
                target_user_id = int(data.split(":")[1])
                keyboard = [
                    [InlineKeyboardButton("✅ Да, удалить", callback_data=f"admin_confirm_delete:{target_user_id}")],
                    [InlineKeyboardButton("❌ Отмена", callback_data="admin_users")]
                ]
                await query.edit_message_text(f"⚠️ Подтвердите удаление пользователя `{target_user_id}`:", reply_markup=InlineKeyboardMarkup(keyboard))
            elif data.startswith("admin_confirm_delete:"):
                target_user_id = int(data.split(":")[1])
                self.db.execute("DELETE FROM users WHERE user_id = ?", (target_user_id,))
                self.db.execute("DELETE FROM poll_votes WHERE user_id = ?", (target_user_id,))
                self.db.execute("DELETE FROM user_states WHERE user_id = ?", (target_user_id,))
                self.db.execute("DELETE FROM template_sessions WHERE user_id = ?", (target_user_id,))
                await query.edit_message_text(f"✅ Пользователь `{target_user_id}` и все его данные удалены.")
                await self.show_admin_users_list(query)
            elif data == "admin_clear_logs":
                await self.clear_all_logs(query)
            elif data.startswith("admin_logs_"):
                await self.handle_admin_logs_command(query, data)
            elif data == "admin_back":
                await self.safe_edit_message(
                    query,
                    "🛠 **Панель администратора**\n\nВыберите действие:",
                    reply_markup=self.menus.admin_menu()
                )
            else:
                logger.warning(f"Unknown callback data: {data}")
                await query.answer("❌ Неизвестная команда", show_alert=True)
        except Exception as e:
            logger.error(f"Admin callback error: {e}")
            await query.edit_message_text("❌ Ошибка обработки команды")

    async def handle_user_deletion(self, query, data: str):
        """Handle user deletion confirmation"""
        user_id = query.from_user.id

        # Проверяем права администратора
        if self.get_permissions(user_id) != "admin":
            await query.answer("❌ Недостаточно прав", show_alert=True)
            return

        await query.answer()

        try:
            target_user_id = int(data.split(":", 1)[1])

            # Получаем информацию о пользователе
            user_info = self.db.query("SELECT username, permissions FROM users WHERE user_id = ?", (target_user_id,))

            if not user_info:
                await query.edit_message_text("❌ Пользователь не найден")
                return

            username = user_info[0][0] or f"User{target_user_id}"

            # Удаляем пользователя и все связанные данные
            success = self.db.execute("DELETE FROM users WHERE user_id = ?", (target_user_id,))

            if success:
                # Также удаляем связанные данные
                self.db.execute("DELETE FROM poll_votes WHERE user_id = ?", (target_user_id,))
                self.db.execute("DELETE FROM user_states WHERE user_id = ?", (target_user_id,))
                self.db.execute("DELETE FROM template_sessions WHERE user_id = ?", (target_user_id,))

                await query.edit_message_text(
                    f"✅ Пользователь удален!\n\n"
                    f"👤 **{username}** (`{target_user_id}`)\n"
                    f"🗑️ Все данные пользователя удалены из системы"
                )
            else:
                await query.edit_message_text("❌ Ошибка удаления пользователя")

        except Exception as e:
            logger.error(f"User deletion error: {e}")
            await query.edit_message_text("❌ Ошибка удаления пользователя")

    async def show_admin_users_list(self, query):
        """Show admin users list with management options (buttons)"""
        try:
            users = self.db.query("""
                SELECT user_id, username, permissions, last_activity
                FROM users
                ORDER BY last_activity DESC
                LIMIT 15
            """)

            if not users:
                await query.edit_message_text("📋 Пользователи не найдены")
                return

            text = "👥 **Управление пользователями**\n\n"
            keyboard = []
            for user in users:
                user_id, username, permissions, last_activity = user
                username = username or f"User{user_id}"
                if permissions == "admin":
                    perm_emoji = "🛠"
                elif permissions == "create":
                    perm_emoji = "📝"
                else:
                    perm_emoji = "👤"
                try:
                    last_dt = datetime.fromisoformat(last_activity.replace('Z', '+00:00'))
                    last_str = last_dt.strftime('%d.%m %H:%M')
                except:
                    last_str = "неизвестно"
                text += f"{perm_emoji} **{username}** (`{user_id}`)\n   Права: `{permissions}` | Активность: {last_str}\n"
                row = [
                    InlineKeyboardButton("Права", callback_data=f"admin_setperm:{user_id}"),
                    InlineKeyboardButton("Отозвать", callback_data=f"admin_revoke:{user_id}"),
                    InlineKeyboardButton("Удалить", callback_data=f"admin_delete:{user_id}")
                ]
                keyboard.append(row)
            keyboard.append([InlineKeyboardButton("🔄 Обновить", callback_data="admin_users")])
            keyboard.append([InlineKeyboardButton("🔙 Назад", callback_data="admin_back")])
            await self.send_message(query, text, InlineKeyboardMarkup(keyboard))
        except Exception as e:
            logger.error(f"Show admin users error: {e}")
            await query.edit_message_text("❌ Ошибка получения списка пользователей")

    async def show_admin_stats(self, query):
        """Show detailed system statistics for admin"""
        try:
            # Получаем статистику
            stats = {
                'total_users': len(self.db.query("SELECT user_id FROM users")),
                'admin_users': len(self.db.query("SELECT user_id FROM users WHERE permissions = 'admin'")),
                'create_users': len(self.db.query("SELECT user_id FROM users WHERE permissions = 'create'")),
                'use_users': len(self.db.query("SELECT user_id FROM users WHERE permissions = 'use'")),
                'total_polls': len(self.db.query("SELECT poll_id FROM polls")),
                'active_polls': len(self.db.query("SELECT poll_id FROM polls WHERE status = 'active'")),
                'total_votes': len(self.db.query("SELECT poll_id FROM poll_votes")),
                'templates': len(self.db.query("SELECT name FROM templates")),
                'decisions': len(self.db.query("SELECT poll_id FROM polls WHERE decision_number IS NOT NULL"))
            }

            # Активность за последние 24 часа
            day_ago = (datetime.now() - timedelta(days=1)).isoformat()
            recent_users = self.db.query("SELECT COUNT(*) FROM users WHERE last_activity > ?", (day_ago,))
            recent_polls = self.db.query("SELECT COUNT(*) FROM polls WHERE created_date > ?", (day_ago,))

            text = "📊 **Статистика системы**\n\n"

            text += "👥 **Пользователи:**\n"
            text += f"• Всего: {stats['total_users']}\n"
            text += f"• Админы: {stats['admin_users']}\n"
            text += f"• Создатели: {stats['create_users']}\n"
            text += f"• Пользователи: {stats['use_users']}\n"
            text += f"• Активны за 24ч: {recent_users[0][0] if recent_users else 0}\n\n"

            text += "🗳️ **Опросы:**\n"
            text += f"• Всего: {stats['total_polls']}\n"
            text += f"• Активных: {stats['active_polls']}\n"
            text += f"• Создано за 24ч: {recent_polls[0][0] if recent_polls else 0}\n"
            text += f"• Всего голосов: {stats['total_votes']}\n"
            text += f"• Принято решений: {stats['decisions']}\n\n"

            text += "📋 **Шаблоны:**\n"
            text += f"• Всего: {stats['templates']}\n\n"

            text += "💾 **Система:**\n"
            text += f"• БД: {'✅' if os.path.exists(DB_PATH) else '❌'}\n"
            text += f"• Лимит запросов: {self.config.get('rate_limit_hour', 10)}/час\n"

            await self.send_message(query, text, self.menus.admin_stats_menu())

        except Exception as e:
            logger.error(f"Show admin stats error: {e}")
            await self.send_message(query, "❌ Ошибка получения статистики")

    async def show_admin_permissions_help(self, query):
        """Show help for permissions management"""
        text = """🔧 **Управление правами пользователей**

**Команды:**
• `/grant <user_id> <rights>` - выдать права
• `/revoke <user_id>` - отозвать права

**Доступные права:**
• `use` - базовые права (голосование)
• `create` - создание опросов и шаблонов
• `admin` - полные права администратора

**Примеры:**
• `/grant 123456789 create` - выдать права на создание
• `/grant 123456789 admin` - выдать админские права
• `/revoke 123456789` - отозвать права (установить 'use')

**Примечание:** Команда `/grant` создает пользователя, если он не существует."""

        keyboard = [
            [InlineKeyboardButton("🔙 Назад", callback_data="admin_back")]
        ]

        await self.send_message(query, text, self.menus.admin_back_menu())

    async def show_admin_delete_help(self, query):
        """Show help for user deletion"""
        text = """🗑️ **Удаление пользователей**

**Команда:**
• `/delete_user <user_id>` - удалить пользователя

**Пример:**
• `/delete_user 123456789` - удалить пользователя

**⚠️ ВНИМАНИЕ:**
• Пользователь будет полностью удален из системы
• Удаляются все данные пользователя:
  - Профиль пользователя
  - Голоса в опросах
  - Состояния сессий
• Это действие нельзя отменить!
• Используйте с осторожностью

**Рекомендация:** Сначала отзовите права командой `/revoke`, а затем удаляйте."""

        keyboard = [
            [InlineKeyboardButton("🔙 Назад", callback_data="admin_back")]
        ]

        await self.send_message(query, text, self.menus.admin_back_menu())

    async def handle_poll_option_input(self, update: Update, text: str, state_data: Dict):
        """Handle poll option input one by one"""
        user_id = update.effective_user.id

        # Проверяем права на создание опросов
        if self.get_permissions(user_id) not in ["create", "admin"]:
            await self.send_message(update, "❌ Недостаточно прав для создания голосований")
            self.clear_user_state(user_id)
            return

        question = state_data.get("question", "")
        options = state_data.get("options", [])
        poll_type = state_data.get("type", "simple")

        # Валидация варианта ответа
        if not text or len(text.strip()) == 0:
            await self.send_message(update, "❌ Вариант ответа не может быть пустым. Попробуйте еще раз:")
            return

        if len(text) > MAX_POLL_OPTION:
            await self.send_message(update, f"❌ Вариант слишком длинный (макс. {MAX_POLL_OPTION} символов). Попробуйте еще раз:")
            return

        option = self.clean_poll_option(text.strip())
        options.append(option)

        # Проверяем минимальное количество вариантов
        if len(options) < 2:
            await self.send_message(update, f"✅ Вариант {len(options)}: **{option}**\n\n📝 Введите следующий вариант ответа:",
                                   reply_markup=InlineKeyboardMarkup([[\
                                       InlineKeyboardButton("⬅️ Назад", callback_data="create_poll")
                                   ]]))
            new_state_data = {**state_data, "options": options}
            self.set_user_state(user_id, UserState.WAITING_POLL_OPTION, new_state_data)
            return

        # Проверяем максимальное количество вариантов
        max_options = self.config.get('max_poll_options', 10)
        if len(options) >= max_options:
            await self.finalize_poll_creation(update, question, options, poll_type)
            return

        # Показываем текущие варианты и запрашиваем следующий
        options_text = "\n".join([f"{i+1}. **{opt}**" for i, opt in enumerate(options)])

        await self.send_message(
            update,
            f"✅ Вариант {len(options)}: **{option}**\n\n"
            f"📋 Текущие варианты:\n{options_text}\n\n"
            f"📝 Введите следующий вариант ответа или нажмите 'Завершить создание':",
            self.menus.finish_poll_menu()
        )

        new_state_data = {**state_data, "options": options}
        self.set_user_state(user_id, UserState.WAITING_TEMPLATE_OPTION, new_state_data)

    async def finalize_poll_creation(self, update: Update, question: str, options: List[str], poll_type: str):
        """Finalize poll creation with collected options"""
        # Определяем user_id
        if hasattr(update, "effective_user") and update.effective_user:
            user_id = update.effective_user.id
        elif hasattr(update, "from_user") and update.from_user:
            user_id = update.from_user.id
        else:
            user_id = None

        # Определяем chat_id
        if hasattr(update, "message") and update.message:
            chat_id = update.message.chat_id
        elif hasattr(update, "callback_query") and update.callback_query and hasattr(update.callback_query.message, "chat_id"):
            chat_id = update.callback_query.message.chat_id
        elif hasattr(update, "chat_id"):
            chat_id = update.chat_id
        else:
            chat_id = None

        if user_id is None or chat_id is None:
            await self.send_message(update, "❌ Не удалось определить пользователя или чат для создания опроса")
            if user_id:
                self.clear_user_state(user_id)
            return

        # Автоматически определяем тип голосования на основе вариантов ответов
        voting_type = self.determine_voting_type(options)

        # Финальная валидация
        valid, error_msg = self.validate_poll_data(question, options)
        if not valid:
            await self.send_message(update, f"❌ {error_msg}")
            self.clear_user_state(user_id)
            return

        # Запрашиваем максимальное количество участников
        self.set_user_state(user_id, UserState.WAITING_MAX_PARTICIPANTS, {
            "question": question,
            "options": options,
            "poll_type": poll_type
        })
        await self.send_message(
            update,
            "👥 **Максимальное количество участников**\n\n"
            "Введите число участников или 0 для неограниченного количества:"
        )

    def get_voting_type_text(self, voting_type: str) -> str:
        """Get formatted text description for voting type"""
        if voting_type == "approval":
            return "\n🎯 **Тип голосования:** За/Против/Воздержался (решение принимается только при большинстве голосов 'за')"
        elif voting_type == "binary":
            return "\n🎯 **Тип голосования:** За/Против (решение принимается только при большинстве голосов 'за')"
        elif voting_type == "choice":
            return "\n🎯 **Тип голосования:** Обычный выбор (решение принимается при большинстве голосов за любой вариант)"
        else:
            return ""

    def get_version_info(self):
        return f"🗳️ PollsBot v{self.BOT_VERSION}\n\n"

    def get_user_id(self, update_or_query):
        if hasattr(update_or_query, 'effective_user') and update_or_query.effective_user:
            return update_or_query.effective_user.id
        elif hasattr(update_or_query, 'from_user') and update_or_query.from_user:
            return update_or_query.from_user.id
        return None

    def get_chat_id(self, update_or_query):
        if hasattr(update_or_query, 'effective_chat') and update_or_query.effective_chat:
            return update_or_query.effective_chat.id
        elif hasattr(update_or_query, 'message') and hasattr(update_or_query.message, 'chat_id'):
            return update_or_query.message.chat_id
        elif hasattr(update_or_query, 'chat_id'):
            return update_or_query.chat_id
        elif hasattr(update_or_query, 'message') and hasattr(update_or_query.message, 'chat') and hasattr(update_or_query.message.chat, 'id'):
            return update_or_query.message.chat.id
        return None

    def get_user_and_chat_id(self, update_or_query):
        return self.get_user_id(update_or_query), self.get_chat_id(update_or_query)

    @staticmethod
    def permission_required(permissions):
        """Enhanced decorator for permission checking (универсальный для update и callback_query)"""
        def decorator(func):
            @wraps(func)
            async def wrapper(self, update_or_query, context):
                user_id = self.get_user_id(update_or_query)
                user_perm = self.get_permissions(user_id)
                if user_perm not in permissions and user_perm != "admin":
                    await self.send_message(update_or_query, "❌ Недостаточно прав для выполнения команды.")
                    return
                rate_limit = self.config.get('rate_limit_hour', 10)
                if not self.rate_limiter.is_allowed(user_id, rate_limit):
                    await self.send_message(update_or_query, "⚠️ Превышен лимит запросов. Попробуйте позже.")
                    return
                return await func(self, update_or_query, context)
            return wrapper
        return decorator

    def get_user_settings(self, user_id: int) -> dict:
        row = self.db.query("SELECT settings FROM user_settings WHERE user_id = ?", (user_id,))
        if row and row[0][0]:
            try:
                return json.loads(row[0][0])
            except Exception:
                return {}
        return {}

    def set_user_settings(self, user_id: int, settings: dict):
        self.db.execute(
            "INSERT OR REPLACE INTO user_settings (user_id, settings) VALUES (?, ?)",
            (user_id, json.dumps(settings, ensure_ascii=False))
        )

    async def show_templates_for_use(self, query):
        """Show templates for use with proper error handling"""
        try:
            templates = self.get_templates()
            logger.debug(f"Found {len(templates)} templates")
            if templates:
                logger.debug(f"Template names: {[t.get('name', 'NO_NAME') for t in templates]}")
                logger.debug(f"Template IDs: {[t.get('id', t.get('template_id', 'NO_ID')) for t in templates]}")
                text = "📋 **Доступные шаблоны:**\n\n"
                for t in templates:
                    text += (
                        f"• **{t.get('name', 'NO_NAME')}**\n"
                        f"  ❓ {t.get('question', '')[:60]}{'...' if len(t.get('question', '')) > 60 else ''}\n"
                        f"  📝 Вариантов: {len(t.get('options', '').split('|'))}\n"
                        f"  🔧 Переменных: {', '.join(t.get('variables', [])) if t.get('variables') else 'нет'}\n\n"
                    )
                await self.send_message(query, text, self.menus.template_menu(templates, query.from_user.id))
            else:
                # Создаем клавиатуру с кнопкой создания шаблона
                keyboard = []
                if self.get_permissions(query.from_user.id) in ["create", "admin"]:
                    keyboard.append([InlineKeyboardButton("➕ Создать шаблон", callback_data="new_template")])
                keyboard.append([InlineKeyboardButton("⬅️ Назад", callback_data="back_to_main")])
                await self.send_message(query, "📋 Шаблоны не найдены. Создайте первый шаблон!", InlineKeyboardMarkup(keyboard))
        except Exception as e:
            logger.error(f"Show templates error: {e}")
            logger.debug(f"Error in show_templates_for_use: {e}")
            await query.edit_message_text("❌ Ошибка загрузки шаблонов")

    async def show_active_polls(self, query):
        """Show active polls with voting buttons"""
        try:
            user_id = query.from_user.id
            active_polls = self.get_active_polls(user_id=user_id, limit=10)
            
            if not active_polls:
                # Отправляем сообщение с клавиатурой, даже если опросов нет
                keyboard = [[InlineKeyboardButton("⬅️ Назад", callback_data="back_to_main")]]
                await self.send_message(query, "🗳️ В данный момент нет активных голосований, в которых вы участвовали.", InlineKeyboardMarkup(keyboard))
                return

            text = "🗳️ **Активные опросы:**\n\n"
            keyboard = []

            for i, poll in enumerate(active_polls[:5]):  # Показываем максимум 5 опросов
                poll_id = poll["poll_id"]
                question = poll["question"]
                options = poll["options"].split("|")

                # Обрезаем длинный вопрос
                display_question = question[:60] + "..." if len(question) > 60 else question
                text += f"**{i+1}. {display_question}**\n"

                # Добавляем кнопку для просмотра опроса
                keyboard.append([InlineKeyboardButton(
                    f"🗳️ {display_question[:30]}...",
                    callback_data=f"show_poll:{poll_id}"
                )])

            if len(active_polls) > 5:
                text += f"\n... и еще {len(active_polls) - 5} опросов"

            keyboard.append([InlineKeyboardButton("⬅️ Назад", callback_data="back_to_main")])

            await self.send_message(query, text, InlineKeyboardMarkup(keyboard))

        except Exception as e:
            logger.error(f"Show active polls error: {e}")
            await self.send_message(query, "❌ Ошибка загрузки активных опросов")

    async def show_single_poll(self, query, poll_id: str):
        """Show single poll with full details"""
        try:
            logger.info(f"show_single_poll called for poll_id: {poll_id}")

            result = self.db.query("""
                SELECT poll_id, question, options, created_date, creator_id, status,
                       total_voters, decision_number, template_used, threshold, non_anonymous
                FROM polls WHERE poll_id = ?
            """, (poll_id,))

            logger.info(f"Database query result: {len(result) if result else 0} rows")

            if not result:
                logger.warning(f"Poll {poll_id} not found in database")
                await self.send_message(query, "❌ Голосование не найдено")
                return

            poll = result[0]
            logger.info(f"Poll data retrieved: {poll[1][:50]}...")  # Первые 50 символов вопроса

            logger.info("Calling format_poll_message...")
            text, keyboard = self.format_poll_message(poll_id, show_results=True, for_user_id=query.from_user.id)
            logger.info(f"format_poll_message returned: text length={len(text)}, keyboard type={type(keyboard)}")

            # Проверяем, что форматирование прошло успешно
            if text == "❌ Ошибка отображения опроса" or text == "❌ Голосование не найдено":
                logger.error(f"format_poll_message returned error: {text}")
                await self.send_message(query, text)
                return

            # Добавляем дополнительную информацию
            logger.info("Adding additional poll information...")
            creator_info = self.db.query("SELECT username FROM users WHERE user_id = ?", (poll[4],))
            creator_name = f"@{creator_info[0][0]}" if creator_info else f"ID: {poll[4]}"

            # Получаем настройки пользователя
            user_settings = self.get_user_settings(query.from_user.id)
            config = self.config
            show_voter_names = user_settings.get('show_voter_names', config.get('show_voter_names', True))

            additional_info = f"\n\n📊 **Информация об опросе:**\n"
            additional_info += f"👤 Создатель: {creator_name}\n"
            additional_info += f"📅 Дата создания: {poll[3][:19]}\n"
            additional_info += f"👥 Всего проголосовало: {poll[6] or 0}\n"
            additional_info += f"🔢 Номер решения: {poll[7] or 'Не назначен'}\n"
            additional_info += f" Порог: {poll[9]}%\n"
            additional_info += f"🔍 Анонимность: {'Нет' if show_voter_names else 'Да'}"

            if poll[8]:  # template_used
                additional_info += f"\n📋 Шаблон: {poll[8]}"

            text += additional_info
            logger.info(f"Text length after adding info: {len(text)}")

            # Добавляем кнопку "Назад" в зависимости от контекста
            logger.info(f"Processing keyboard: type={type(keyboard)}, hasattr inline_keyboard={hasattr(keyboard, 'inline_keyboard')}")

            if keyboard and hasattr(keyboard, 'inline_keyboard') and keyboard.inline_keyboard:
                logger.info("Creating new keyboard with back button...")
                logger.info(f"inline_keyboard type: {type(keyboard.inline_keyboard)}")
                logger.info(f"inline_keyboard length: {len(keyboard.inline_keyboard)}")

                # Создаем новую клавиатуру с кнопкой "Назад"
                new_keyboard = list(keyboard.inline_keyboard)

                # Определяем, откуда пришел пользователь
                if poll[5] == 'closed':  # status = 'closed'
                    new_keyboard.append([InlineKeyboardButton("⬅️ Назад к списку", callback_data="closed_polls")])
                    logger.info("Added back button for closed polls")
                else:
                    new_keyboard.append([InlineKeyboardButton("⬅️ Назад к списку", callback_data="active_polls")])
                    logger.info("Added back button for active polls")

                keyboard = InlineKeyboardMarkup(new_keyboard)
                logger.info(f"New keyboard created with {len(new_keyboard)} rows")
            elif not keyboard:
                logger.info("Creating new keyboard from scratch...")
                # Если клавиатура пустая, создаем новую с кнопкой "Назад"
                if poll[5] == 'closed':  # status = 'closed'
                    keyboard = InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Назад к списку", callback_data="closed_polls")]])
                else:
                    keyboard = InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Назад к списку", callback_data="active_polls")]])
                logger.info("New keyboard created from scratch")
            else:
                logger.info("Keyboard exists but no inline_keyboard attribute or empty")

            logger.info("Sending message...")
            await self.send_message(query, text, reply_markup=keyboard)
            logger.info("Message sent successfully")

        except Exception as e:
            logger.error(f"Show single poll error: {e}", exc_info=True)
            await self.send_message(query, "❌ Ошибка при отображении опроса")

    async def show_closed_polls(self, query):
        """Показать список закрытых голосований"""
        try:
            user_id = query.from_user.id
            closed_polls = self.get_closed_polls(user_id, limit=10)

            if not closed_polls:
                # Отправляем сообщение с клавиатурой, даже если опросов нет
                keyboard = [[InlineKeyboardButton("⬅️ Назад", callback_data="back_to_main")]]
                await self.send_message(query, "📭 Закрытых голосований, в которых вы участвовали, не найдено", InlineKeyboardMarkup(keyboard))
                return

            text = "🔒 **Закрытые голосования:**\n\n"
            keyboard = []

            for i, poll in enumerate(closed_polls[:10]):
                # Обрезаем вопрос если он слишком длинный
                question = poll['question'][:50] + "..." if len(poll['question']) > 50 else poll['question']

                # Получаем имя создателя
                creator_info = self.db.query("SELECT username FROM users WHERE user_id = ?", (poll['creator_id'],))
                creator_name = f"@{creator_info[0][0]}" if creator_info else f"ID: {poll['creator_id']}"

                # Форматируем дату
                created_date = poll['created_date'][:19] if poll['created_date'] else "Неизвестно"

                text += f"{i+1}. **{question}**\n"
                text += f"   👤 {creator_name} | 📅 {created_date}\n"
                text += f"   👥 {poll['total_voters']} голосов"

                if poll['decision_number']:
                    text += f" | 🔢 Решение №{poll['decision_number']}"
                text += "\n\n"

                # Добавляем кнопку для просмотра деталей
                keyboard.append([InlineKeyboardButton(f"👁️ {i+1}. {question[:30]}...",
                                                    callback_data=f"show_closed_poll:{poll['poll_id']}")])

            # Добавляем кнопку "Назад"
            keyboard.append([InlineKeyboardButton("⬅️ Назад", callback_data="back_to_main")])

            await self.send_message(query, text, InlineKeyboardMarkup(keyboard))

        except Exception as e:
            logger.error(f"Show closed polls error: {e}")
            await self.send_message(query, "❌ Ошибка при загрузке закрытых голосований")

    async def status_command(self, update_or_query, context):
        await self.send_message(update_or_query, "Статистика пока не реализована.")

    async def help_command(self, update_or_query, context):
        help_text = """ℹ️ **Справка по системе голосований**

👥 **Права пользователей:**

• **👤 use** - Базовые права
  - Просмотр активных опросов (только тех, в которых участвовали)
  - Просмотр закрытых опросов (только тех, в которых участвовали)
  - Голосование в опросах
  - Просмотр результатов

• **📝 create** - Права создателя
  - Все права уровня "use"
  - Создание новых опросов
  - Создание и использование шаблонов
  - Просмотр своих созданных опросов + опросов, в которых участвовали
  - Редактирование своих опросов

• **🛠 admin** - Административные права
  - Все права уровня "create"
  - Просмотр всех опросов (активных и закрытых)
  - Управление пользователями
  - Просмотр статистики системы
  - Редактирование любых опросов
  - Удаление опросов и пользователей

🗳️ **Как работает система:**

1. **Создание опроса** - Выберите тип (простой или из шаблона)
2. **Голосование** - Нажмите на вариант ответа в опросе
3. **Результаты** - Отображаются в реальном времени
4. **Закрытие** - Автоматическое или ручное закрытие опросов
5. **Шаблоны** - Используйте {Переменная} для быстрого создания

🔒 **Приватность голосований:**

• **Пользователи "use"** видят только те голосования, в которых участвовали
• **Пользователи "create"** видят свои созданные голосования + те, в которых участвовали
• **Администраторы** видят все голосования в системе

🔧 **Переменные в шаблонах:**

Переменные позволяют создавать универсальные шаблоны опросов:

• **Формат:** `{НазваниеПеременной}` - в фигурных скобках
• **Примеры:** `{Дата}`, `{Место}`, `{Время}`, `{Тема}`
• **Использование:** В вопросе и вариантах ответа
• **Заполнение:** При создании опроса система запросит значения

**Пример шаблона:**
```
Вопрос: Голосование по {Тема} на {Дата}
Варианты:
- За
- Против
- Воздержаться
```

При использовании система спросит:
- Значение для {Тема}: "Встреча команды"
- Значение для {Дата}: "15 декабря"

📞 **Поддержка:** @ih0rd"""

        await self.send_message(update_or_query, help_text,
                               reply_markup=InlineKeyboardMarkup([[
                                   InlineKeyboardButton("⬅️ Назад", callback_data="back_to_main")
                               ]]))
    async def templates_command(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Обработчик команды /templates"""
        await self.show_templates_for_use(update)

    @error_handler
    async def confirm_delete_poll_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Handle poll deletion confirmation"""
        query = update.callback_query
        await query.answer()

        data = query.data
        user_id = query.from_user.id

        if not data.startswith("confirm_delete_poll:"):
            return

        try:
            poll_id = data.split(":", 1)[1]

            # Check permissions again
            poll_data = self.db.query("SELECT creator_id, question FROM polls WHERE poll_id = ?", (poll_id,))
            if not poll_data:
                await query.answer("❌ Голосование не найдено", show_alert=True)
                return

            creator_id, question = poll_data[0]
            user_perms = self.get_permissions(user_id)

            # Allow deletion only if user is creator or admin
            if user_id != creator_id and user_perms != "admin":
                await query.answer("❌ Недостаточно прав для удаления опроса", show_alert=True)
                return

            # Delete poll
            self.db.execute("DELETE FROM polls WHERE poll_id = ?", (poll_id,))

            await query.edit_message_text(
                text=f"🗑️ **Опрос удален**\n\n❓ Вопрос: {question}\n\n✅ Опрос успешно удален из системы.",
                parse_mode=ParseMode.MARKDOWN
            )

            await query.answer("✅ Опрос удален", show_alert=False)
            logger.info(f"Poll deleted: {poll_id} by user {user_id}")

        except Exception as e:
            logger.error(f"Confirm delete poll handler error: {e}")
            await query.answer("❌ Ошибка удаления опроса", show_alert=True)

    @error_handler
    async def start_edit_poll_question(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Start editing poll question"""
        query = update.callback_query
        await query.answer()

        data = query.data
        user_id = query.from_user.id

        if not data.startswith("edit_poll_question:"):
            return

        try:
            poll_id = data.split(":", 1)[1]

            # Check permissions
            poll_data = self.db.query("SELECT creator_id, status, question FROM polls WHERE poll_id = ?", (poll_id,))
            if not poll_data:
                await query.answer("❌ Голосование не найдено", show_alert=True)
                return

            creator_id, status, question = poll_data[0]
            user_perms = self.get_permissions(user_id)

            # Allow editing only if user is creator or admin
            if user_id != creator_id and user_perms != "admin":
                await query.answer("❌ Недостаточно прав для редактирования опроса", show_alert=True)
                return

            if status != 'active':
                await query.answer("❌ Можно редактировать только активные опросы", show_alert=True)
                return

            # Set user state for editing question
            self.set_user_state(user_id, UserState.WAITING_POLL_QUESTION, {
                "type": "edit_question",
                "poll_id": poll_id,
                "original_question": question
            })

            await query.edit_message_text(
                text=f"📝 **Редактирование вопроса**\n\n❓ Текущий вопрос: {question}\n\n📝 Введите новый вопрос:",
                reply_markup=InlineKeyboardMarkup([[
                    InlineKeyboardButton("⬅️ Назад", callback_data=f"edit_poll:{poll_id}")
                ]]),
                parse_mode=ParseMode.MARKDOWN
            )

        except Exception as e:
            logger.error(f"Start edit poll question error: {e}")
            await query.answer("❌ Ошибка редактирования вопроса", show_alert=True)

    @error_handler
    async def start_edit_poll_options(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        """Start editing poll options"""
        query = update.callback_query
        await query.answer()

        data = query.data
        user_id = query.from_user.id

        if not data.startswith("edit_poll_options:"):
            return

        try:
            poll_id = data.split(":", 1)[1]

            # Check permissions
            poll_data = self.db.query("SELECT creator_id, status, options FROM polls WHERE poll_id = ?", (poll_id,))
            if not poll_data:
                await query.answer("❌ Голосование не найдено", show_alert=True)
                return

            creator_id, status, options_str = poll_data[0]
            user_perms = self.get_permissions(user_id)

            # Allow editing only if user is creator or admin
            if user_id != creator_id and user_perms != "admin":
                await query.answer("❌ Недостаточно прав для редактирования опроса", show_alert=True)
                return

            if status != 'active':
                await query.answer("❌ Можно редактировать только активные опросы", show_alert=True)
                return

            options = options_str.split('|')

            # Set user state for editing options
            self.set_user_state(user_id, UserState.WAITING_POLL_OPTIONS, {
                "type": "edit_options",
                "poll_id": poll_id,
                "original_options": options
            })

            options_text = "\n".join([f"{i+1}. {opt}" for i, opt in enumerate(options)])

            await query.edit_message_text(
                text=f"📋 **Редактирование вариантов ответа**\n\n📝 Текущие варианты:\n{options_text}\n\n📝 Введите новые варианты через запятую или перенос строки:",
                reply_markup=InlineKeyboardMarkup([[
                    InlineKeyboardButton("⬅️ Назад", callback_data=f"edit_poll:{poll_id}")
                ]]),
                parse_mode=ParseMode.MARKDOWN
            )

        except Exception as e:
            logger.error(f"Start edit poll options error: {e}")
            await query.answer("❌ Ошибка редактирования вариантов", show_alert=True)

    async def handle_admin_logs_command(self, query, data: str):
        """Handle admin logs commands"""
        user_id = query.from_user.id
        if self.get_permissions(user_id) != "admin":
            await query.answer("❌ Недостаточно прав", show_alert=True)
            return
        await query.answer()
        try:
            if data == "admin_logs_stats":
                await self.show_admin_logs_stats(query)
            elif data == "admin_clear_all_logs":
                await self.clear_all_logs(query)
            elif data.startswith("admin_clear_logs:"):
                level = data.split(":")[1]
                success = await self.clear_logs_by_level(query, level)
                if success:
                    await self.safe_edit_message(
                        query,
                        f"✅ Логи уровня '{level}' очищены!",
                        reply_markup=self.menus.admin_clear_logs_by_level_menu()
                    )
                else:
                    await self.safe_edit_message(
                        query,
                        f"❌ Ошибка очистки логов уровня '{level}'",
                        reply_markup=self.menus.admin_clear_logs_by_level_menu()
                    )
            elif data == "admin_view_recent_logs":
                await self.safe_edit_message(
                    query,
                    "📄 **Просмотр логов**\n\nВыберите уровень для просмотра:",
                    reply_markup=self.menus.admin_view_logs_menu()
                )
            elif data.startswith("admin_view_logs:"):
                level = data.split(":")[1]
                text = await self.view_logs_by_level(query, level)
                await self.safe_edit_message(
                    query,
                    text,
                    reply_markup=self.menus.admin_view_logs_menu()
                )
            elif data == "admin_rotate_logs":
                success = await self.rotate_logs(query)
                if success:
                    await self.safe_edit_message(
                        query,
                        "🔄 **Ротация логов выполнена**",
                        reply_markup=self.menus.admin_logs_menu()
                    )
                else:
                    await self.safe_edit_message(
                        query,
                        "❌ Ошибка ротации логов",
                        reply_markup=self.menus.admin_logs_menu()
                    )
            elif data == "admin_logs_levels":
                await self.safe_edit_message(
                    query,
                    "⚙️ **Управление уровнями логирования**\n\nНажмите на уровень для включения/выключения:",
                    reply_markup=self.menus.admin_logs_levels_menu()
                )
            elif data.startswith("admin_toggle_logs:"):
                level = data.split(":")[1]
                message = await self.toggle_logs_by_level(query, level)
                await self.safe_edit_message(
                    query,
                    message,
                    reply_markup=self.menus.admin_logs_levels_menu()
                )
            elif data == "admin_third_party_loggers":
                await self.show_third_party_loggers_status(query)
            elif data.startswith("admin_setperm:"):
                target_user_id = int(data.split(":")[1])
                perms = [
                    ("use", "👤 use"),
                    ("create", "📝 create"),
                    ("admin", "🛠 admin")
                ]
                perm_buttons = [InlineKeyboardButton(label, callback_data=f"admin_perm_select:{target_user_id}:{p}") for p, label in perms]
                keyboard = [perm_buttons[i:i+2] for i in range(0, len(perm_buttons), 2)]
                keyboard.append([InlineKeyboardButton("🔙 Назад", callback_data="admin_users")])
                await self.safe_edit_message(query, f"Выберите права для пользователя `{target_user_id}`:", reply_markup=InlineKeyboardMarkup(keyboard))
            elif data.startswith("admin_perm_select:"):
                _, target_user_id, new_perm = data.split(":")
                target_user_id = int(target_user_id)
                # Обновляем права
                self.db.execute("UPDATE users SET permissions = ? WHERE user_id = ?", (new_perm, target_user_id))
                await self.safe_edit_message(query, f"✅ Права пользователя `{target_user_id}` обновлены на `{new_perm}`.")
                await self.show_admin_users_list(query)
            elif data.startswith("admin_revoke:"):
                target_user_id = int(data.split(":")[1])
                self.db.execute("UPDATE users SET permissions = 'use' WHERE user_id = ?", (target_user_id,))
                await self.safe_edit_message(query, f"✅ Права пользователя `{target_user_id}` отозваны (установлено 'use').")
                await self.show_admin_users_list(query)
            elif data.startswith("admin_delete:"):
                target_user_id = int(data.split(":")[1])
                keyboard = [
                    [InlineKeyboardButton("✅ Да, удалить", callback_data=f"admin_confirm_delete:{target_user_id}")],
                    [InlineKeyboardButton("❌ Отмена", callback_data="admin_users")]
                ]
                await self.safe_edit_message(query, f"⚠️ Подтвердите удаление пользователя `{target_user_id}`:", reply_markup=InlineKeyboardMarkup(keyboard))
            elif data.startswith("admin_confirm_delete:"):
                target_user_id = int(data.split(":")[1])
                self.db.execute("DELETE FROM users WHERE user_id = ?", (target_user_id,))
                self.db.execute("DELETE FROM poll_votes WHERE user_id = ?", (target_user_id,))
                self.db.execute("DELETE FROM user_states WHERE user_id = ?", (target_user_id,))
                self.db.execute("DELETE FROM template_sessions WHERE user_id = ?", (target_user_id,))
                await self.safe_edit_message(query, f"✅ Пользователь `{target_user_id}` и все его данные удалены.")
                await self.show_admin_users_list(query)
            elif data == "admin_clear_logs":
                await self.clear_all_logs(query)
            elif data.startswith("admin_logs_"):
                await self.handle_admin_logs_command(query, data)
            elif data == "admin_back":
                await self.safe_edit_message(
                    query,
                    "🛠 **Панель администратора**\n\nВыберите действие:",
                    reply_markup=self.menus.admin_menu()
                )
            else:
                logger.warning(f"Unknown callback data: {data}")
                await query.answer("❌ Неизвестная команда", show_alert=True)
        except Exception as e:
            logger.error(f"Admin logs command error: {e}")
            await self.safe_edit_message(query, "❌ Ошибка выполнения команды")

    async def show_admin_logs_stats(self, query):
        """Show admin logs statistics"""
        try:
            stats = LogManager.get_log_stats()
            text = "📊 **Статистика логов:**\n\n"
            for level, stat in stats.items():
                text += f"🔧 **{level}**: {stat['size_mb']:.2f}MB, {stat['lines']} строк\n"
            await self.safe_edit_message(query, text, reply_markup=self.menus.admin_logs_menu())
        except Exception as e:
            logger.error(f"Show admin logs stats error: {e}")
            await self.safe_edit_message(query, "❌ Ошибка получения статистики логов", reply_markup=self.menus.admin_logs_menu())

    async def clear_all_logs(self, query):
        """Clear all logs"""
        try:
            LogManager.clear_logs()
            await self.safe_edit_message(query, "✅ Все логи очищены!", reply_markup=self.menus.admin_logs_menu())
        except Exception as e:
            logger.error(f"Clear all logs error: {e}")
            await self.safe_edit_message(query, "❌ Ошибка очистки логов", reply_markup=self.menus.admin_logs_menu())

    async def clear_logs_by_level(self, query, level: str):
        """Clear logs by level"""
        try:
            LogManager.clear_logs(level)
            return True
        except Exception as e:
            logger.error(f"Clear logs by level error: {e}")
            return False

    async def view_recent_logs(self, query):
        """View recent logs"""
        try:
            logs = LogManager.get_recent_logs()
            text = "📄 **Последние логи:**\n\n"
            for log in logs:
                text += f"{log}\n\n"
            return text
        except Exception as e:
            logger.error(f"View recent logs error: {e}")
            return "❌ Ошибка загрузки последних логов"

    async def rotate_logs(self, query):
        """Rotate logs"""
        try:
            LogManager.rotate_logs()
            return True
        except Exception as e:
            logger.error(f"Rotate logs error: {e}")
            return False

    async def view_logs_by_level(self, query, level: str):
        """View logs by level"""
        try:
            logs = LogManager.get_recent_logs(level, lines=20)  # Ограничиваем до 20 строк
            if not logs:
                text = f"📄 **Логи уровня '{level}':**\n\n📭 Файл пуст или не существует"
            else:
                text = f"📄 **Логи уровня '{level}':**\n\n"
                for log in logs:
                    text += f"{log}\n"

                # Ограничиваем длину текста для Telegram (максимум 4096 символов)
                if len(text) > 4000:
                    text = text[:4000] + "\n\n... (логи обрезаны)"

            return text
        except Exception as e:
            logger.error(f"View logs by level error: {e}")
            return f"❌ Ошибка загрузки логов уровня '{level}': {str(e)}"

    async def toggle_logs_by_level(self, query, level: str):
        """Toggle logs by level"""
        try:
            # Переключаем состояние
            success = LogManager.toggle_logs(level)
            if not success:
                return "❌ Ошибка изменения состояния логов"

            # Проверяем новое состояние
            enabled = LogManager.is_enabled(level)
            status = "включены" if enabled else "выключены"
            emoji = "✅" if enabled else "❌"

            # Добавляем информацию о файле конфигурации
            config_file = f"{LOG_DIR}/logging_config.json"
            config_info = ""
            if os.path.exists(config_file):
                try:
                    with open(config_file, 'r', encoding='utf-8') as f:
                        config = json.load(f)
                    config_info = f"\n\n📁 Конфигурация сохранена в: {config_file}"
                except Exception as e:
                    config_info = f"\n\n⚠️ Ошибка чтения конфигурации: {e}"

            return f"{emoji} Логи уровня '{level}' теперь {status}!{config_info}"
        except Exception as e:
            logger.error(f"Toggle logs by level error: {e}")
            return f"❌ Ошибка изменения состояния логов: {str(e)}"

    async def show_third_party_loggers_status(self, query):
        """Show third-party loggers status"""
        try:
            status = LogManager.get_third_party_loggers_status()
            text = "📊 **Статус сторонних логгеров:**\n\n"
            for logger_name, info in status.items():
                text += f"🔧 **{logger_name}**: {info['level']}, {info['handlers_count']} handlers, {'включены' if info['propagate'] else 'выключены'}\n"
            await self.safe_edit_message(query, text, reply_markup=self.menus.admin_logs_menu())
        except Exception as e:
            logger.error(f"Show third-party loggers status error: {e}")
            await self.safe_edit_message(query, "❌ Ошибка получения статуса сторонних логгеров")

    async def safe_edit_message(self, query, text: str, reply_markup=None):
        """Safely edit message with handling of 'Message is not modified' error"""
        try:
            await query.edit_message_text(text, reply_markup=reply_markup)
        except Exception as e:
            if "Message is not modified" in str(e):
                # Если сообщение не изменилось, просто отвечаем на callback
                await query.answer("ℹ️ Информация актуальна")
            else:
                # Для других ошибок логируем и показываем пользователю
                logger.error(f"Error editing message: {e}")
                await query.answer("❌ Ошибка обновления сообщения", show_alert=True)

def main():
    """Entry point with enhanced error handling"""
    try:
        logger.debug("🚀 Запуск PollsBot...")

        # Инициализируем логгеры сторонних библиотек
        LogManager.setup_third_party_loggers()
        logger.debug("✅ Логгеры сторонних библиотек настроены")

        bot = PollsBot()
        logger.debug(f"✅ Бот инициализирован, токен: {bot.config.get('bot_token', 'НЕ НАЙДЕН')[:10]}...")

        # Убираем asyncio.run() и используем run_polling() напрямую
        bot.application = Application.builder().token(bot.config["bot_token"]).build()
        logger.debug("✅ Application создан")

        # Add handlers
        handlers = [
            CommandHandler("start", bot.start_command),
            CommandHandler("create", bot.create_command),
            CommandHandler("templates", bot.templates_command),
            CommandHandler("status", bot.status_command),
            CommandHandler("help", bot.help_command),
            CommandHandler("admin", bot.admin_command),
            CommandHandler("users", bot.users_command),
            CommandHandler("grant", bot.grant_command),
            CommandHandler("revoke", bot.revoke_command),
            CommandHandler("delete_user", bot.delete_user_command),
            CallbackQueryHandler(bot.callback_handler),
            InlineQueryHandler(bot.inline_query_handler),
            MessageHandler(filters.TEXT & ~filters.COMMAND, bot.text_handler)
        ]

        for handler in handlers:
            bot.application.add_handler(handler)

        logger.debug(f"✅ Добавлено {len(handlers)} обработчиков")
        logger.debug("✅ InlineQueryHandler добавлен")

        logger.info("Starting PollsBot v2.0...")
        logger.debug("🚀 PollsBot запущен и готов к работе!")

        # Прямой запуск без asyncio.run()
        bot.application.run_polling(poll_interval=bot.config.get("polling_interval", 2))

    except KeyboardInterrupt:
        logger.info("Bot stopped by user")
        logger.debug("\n🛑 Бот остановлен пользователем")
    except Exception as e:
        logger.error(f"Fatal error: {e}", exc_info=True)
        logger.debug(f"❌ Критическая ошибка: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()

