# Telegram Polls Bot 2.0 - Бот для голосования

## 📋 Описание проекта

**Telegram Polls Bot 2.0** - это продвинутый бот для создания и управления голосованиями в Telegram. Бот поддерживает различные типы голосований, систему шаблонов, административные функции и детальное логирование.

### 🎯 Основные возможности

- **Создание голосований**: Поддержка различных типов голосований (бинарное, за/против/воздержался, множественный выбор, рейтинг)
- **Система шаблонов**: Создание и использование шаблонов голосований с переменными
- **Административная панель**: Управление пользователями, правами доступа, логами
- **Продвинутое логирование**: Многоуровневая система логов с возможностью управления
- **Inline режим**: Создание голосований через inline запросы
- **Система прав доступа**: Гранулярное управление правами пользователей
- **Автоматическая очистка**: Удаление устаревших данных и логов

## 🚀 Быстрый старт

### Требования

- Python 3.8+
- Telegram Bot Token (получить у [@BotFather](https://t.me/BotFather))

### Установка

1. **Клонирование репозитория**
```bash
git clone <repository-url>
cd polls-bot
```

2. **Установка зависимостей**
```bash
pip install python-telegram-bot==20.7
```

3. **Настройка конфигурации**
```bash
# Создайте файл config.json в директории /opt/root/PollsBot/
mkdir -p /opt/root/PollsBot
```

Содержимое `config.json`:
```json
{
    "bot_token": "YOUR_BOT_TOKEN_HERE",
    "admin_user_ids": [123456789],
    "polling_interval": 2,
    "max_poll_question": 300,
    "max_poll_option": 100,
    "rate_limit_window": 3600,
    "session_timeout": 7200
}
```

4. **Запуск бота**
```bash
python polls_bot.py
```

## 📖 Подробная документация

### 🏗️ Архитектура проекта

#### Основные компоненты

1. **PollsBot** - главный класс бота
2. **Database** - работа с SQLite базой данных
3. **LogManager** - управление системой логирования
4. **RateLimiter** - ограничение частоты запросов
5. **Menus** - система меню и интерфейса

#### Структура базы данных

```sql
-- Пользователи
CREATE TABLE users (
    user_id INTEGER PRIMARY KEY,
    username TEXT,
    permissions TEXT DEFAULT 'use',
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Голосования
CREATE TABLE polls (
    poll_id TEXT PRIMARY KEY,
    question TEXT NOT NULL,
    options TEXT NOT NULL,
    chat_id INTEGER NOT NULL,
    creator_id INTEGER NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    closed_at TIMESTAMP,
    threshold INTEGER DEFAULT 50,
    non_anonymous BOOLEAN DEFAULT FALSE,
    voting_type TEXT DEFAULT 'multiple_choice',
    max_participants INTEGER DEFAULT 0,
    decision_number INTEGER
);

-- Голоса
CREATE TABLE votes (
    vote_id INTEGER PRIMARY KEY AUTOINCREMENT,
    poll_id TEXT NOT NULL,
    user_id INTEGER NOT NULL,
    option_index INTEGER NOT NULL,
    voted_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (poll_id) REFERENCES polls(poll_id)
);

-- Шаблоны
CREATE TABLE templates (
    template_id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL,
    question TEXT NOT NULL,
    options TEXT NOT NULL,
    variables TEXT,
    creator_id INTEGER NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    usage_count INTEGER DEFAULT 0
);

-- Сессии шаблонов
CREATE TABLE template_sessions (
    session_id TEXT PRIMARY KEY,
    user_id INTEGER NOT NULL,
    template_name TEXT NOT NULL,
    variables TEXT NOT NULL,
    values TEXT,
    chat_id INTEGER NOT NULL,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Состояния пользователей
CREATE TABLE user_states (
    user_id INTEGER PRIMARY KEY,
    state TEXT NOT NULL,
    data TEXT,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
```

### 🎮 Команды бота

#### Основные команды

| Команда | Описание | Права |
|---------|----------|-------|
| `/start` | Запуск бота, главное меню | Все |
| `/create` | Создание нового голосования | create |
| `/templates` | Управление шаблонами | create |
| `/status` | Статус бота | Все |
| `/help` | Справка по командам | Все |

#### Административные команды

| Команда | Описание | Права |
|---------|----------|-------|
| `/admin` | Панель администратора | admin |
| `/users` | Список пользователей | admin |
| `/grant` | Выдача прав пользователю | admin |
| `/revoke` | Отзыв прав пользователя | admin |
| `/delete_user` | Удаление пользователя | admin |

### 🗳️ Типы голосований

#### 1. Бинарное голосование (Binary)
- Простое голосование с двумя вариантами: "За" и "Против"
- Автоматически определяется при наличии вариантов "Да", "Нет", "Yes", "No", "За", "Против"

#### 2. Голосование за/против/воздержался (Approval)
- Голосование с тремя вариантами: "За", "Против", "Воздержался"
- Поддерживает нейтральную позицию
- Автоматически определяется при наличии соответствующих ключевых слов

#### 3. Множественный выбор (Choice)
- Стандартное голосование с несколькими вариантами
- Пользователь может выбрать один вариант
- Используется для голосований с более чем 3 вариантами

#### 4. Рейтинг (Rating)
- Голосование с числовыми оценками
- Автоматически определяется при наличии числовых вариантов (1-5, 1-10)

### 📝 Система шаблонов

#### Создание шаблона

1. Используйте команду `/templates`
2. Выберите "Создать шаблон"
3. Введите название шаблона
4. Создайте вопрос с переменными в формате `{variable_name}`
5. Добавьте варианты ответов

#### Пример шаблона

**Название**: Выбор места встречи
**Вопрос**: Где проведем встречу {event_name}?
**Варианты**:
- Кафе {cafe_name}
- Парк {park_name}
- Офис

#### Использование шаблона

1. Выберите шаблон из списка
2. Введите значения для переменных
3. Настройте параметры голосования
4. Создайте голосование

### 🔐 Система прав доступа

#### Уровни прав

| Право | Описание |
|-------|----------|
| `use` | Базовые права пользователя |
| `create` | Создание голосований и шаблонов |
| `admin` | Полные административные права |

#### Управление правами

```bash
# Выдача прав
/grant @username create

# Отзыв прав
/revoke @username create

# Удаление пользователя
/delete_user @username
```

### 📊 Административная панель

#### Доступные функции

1. **Управление пользователями**
   - Просмотр списка пользователей
   - Изменение прав доступа
   - Удаление пользователей

2. **Статистика**
   - Количество пользователей
   - Активные голосования
   - Использование шаблонов

3. **Управление логами**
   - Просмотр логов по уровням
   - Очистка логов
   - Ротация логов
   - Настройка уровней логирования

### 📋 Система логирования

#### Уровни логов

- **DEBUG** - Отладочная информация
- **INFO** - Общая информация
- **WARNING** - Предупреждения
- **ERROR** - Ошибки
- **CRITICAL** - Критические ошибки

#### Управление логами

```bash
# Просмотр статистики логов
/admin -> Логи -> Статистика

# Очистка всех логов
/admin -> Логи -> Очистить все

# Просмотр логов определенного уровня
/admin -> Логи -> Просмотр -> Выбрать уровень
```

### 🔧 Конфигурация

#### Основные параметры

```json
{
    "bot_token": "YOUR_BOT_TOKEN",
    "admin_user_ids": [123456789],
    "polling_interval": 2,
    "max_poll_question": 300,
    "max_poll_option": 100,
    "rate_limit_window": 3600,
    "session_timeout": 7200,
    "max_retries": 3,
    "retry_delay": 5
}
```

#### Описание параметров

| Параметр | Описание | По умолчанию |
|----------|----------|--------------|
| `bot_token` | Токен бота от BotFather | - |
| `admin_user_ids` | ID администраторов | [] |
| `polling_interval` | Интервал опроса Telegram API | 2 |
| `max_poll_question` | Максимальная длина вопроса | 300 |
| `max_poll_option` | Максимальная длина варианта | 100 |
| `rate_limit_window` | Окно ограничения запросов (сек) | 3600 |
| `session_timeout` | Таймаут сессии (сек) | 7200 |

### 🚀 Развертывание

#### Docker (рекомендуется)

```dockerfile
FROM python:3.9-slim

WORKDIR /app

COPY requirements.txt .
RUN pip install -r requirements.txt

COPY polls_bot.py .
COPY config.json /opt/root/PollsBot/

CMD ["python", "polls_bot.py"]
```

#### Systemd сервис

```ini
[Unit]
Description=Telegram Polls Bot
After=network.target

[Service]
Type=simple
User=botuser
WorkingDirectory=/opt/root/PollsBot
ExecStart=/usr/bin/python3 /opt/root/PollsBot/polls_bot.py
Restart=always
RestartSec=10

[Install]
WantedBy=multi-user.target
```

### 🐛 Отладка и устранение неполадок

#### Частые проблемы

1. **Бот не отвечает**
   - Проверьте токен в config.json
   - Убедитесь, что бот не заблокирован
   - Проверьте логи на наличие ошибок

2. **Ошибки базы данных**
   - Проверьте права доступа к файлу polls.db
   - Убедитесь в корректности SQL запросов

3. **Проблемы с логированием**
   - Проверьте права на запись в директорию логов
   - Убедитесь в достаточном месте на диске

#### Полезные команды

```bash
# Просмотр логов в реальном времени
tail -f /opt/root/PollsBot/logs/info.log

# Проверка статуса бота
python polls_bot.py --status

# Очистка старых данных
python polls_bot.py --cleanup
```

### 📈 Мониторинг

#### Метрики для отслеживания

- Количество активных пользователей
- Количество созданных голосований
- Время отклика бота
- Размер файлов логов
- Использование памяти

#### Рекомендуемые инструменты

- **Prometheus + Grafana** - для метрик
- **ELK Stack** - для анализа логов
- **Uptime Robot** - для мониторинга доступности

### 🔄 Обновления

#### Процесс обновления

1. Остановите бота
2. Создайте резервную копию базы данных
3. Обновите код
4. Проверьте конфигурацию
5. Запустите бота

```bash
# Резервное копирование
cp polls.db polls.db.backup

# Обновление
git pull origin main

# Перезапуск
systemctl restart polls-bot
```