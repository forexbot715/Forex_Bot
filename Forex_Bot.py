import asyncio
import pandas as pd
import ta
import time
from datetime import datetime, timedelta
import colorama
from colorama import Fore, Style
import firebase_admin
from firebase_admin import credentials, db
import os
import numpy as np
import json
import websockets
import aiohttp

# --- Configuration ---
# Yeh CONFIG me bot ke saare settings / parameters rakhe gaye hain
CONFIG = {
    # --- Telegram Settings ---
    "telegram_token": os.environ.get("TELEGRAM_TOKEN"),
    "telegram_chat_id": os.environ.get("TELEGRAM_CHAT_ID"),

    # --- Tiingo API Settings ---
    # NOTE: Yahan apna real Tiingo FX API token dalna hai
    # Behtar yeh hai ke aap env var use karein (security ke liye)
    "tiingo_api_token": os.getenv("TIINGO_FX_API_TOKEN"),
    "tiingo_websocket_url": "wss://api.tiingo.com/fx",

    # --- Strategy Timeframes ---
    "signal_timeframe": "15m",  # Internal aggregation minute candles se hoti hai

    # --- Strong Trend Strategy Settings ---
    "trend_timeframes": ["4h", "1h"],
    "trend_ema_period": 50,

    # --- RSI Volume Pullback Strategy Settings ---
    "pullback_trend_ema_len": 200,
    "pullback_rsi_len": 14,
    "pullback_rsi_oversold": 40,
    "pullback_rsi_overbought": 60,
    "pullback_volume_sma_len": 20,
    "pullback_volume_mult": 1.5,

    # --- Multi-Timeframe "Simple & Strong" Strategy Settings ---
    "mtf_strategy": {
        "trend_timeframe": "4h",
        "filter_timeframe": "1h",
        "trend_ema_period": 200,
        "filter_ema_period": 50,
        "supertrend_period": 10,
        "supertrend_multiplier": 3,
        "entry_volume_sma_len": 20,
        "entry_volume_multiplier": 1.5,
    },

    # --- Bollinger Bands Breakout Strategy Settings ---
    "bb_strategy": {
        "bb_period": 20,
        "bb_std_dev": 2,
        "squeeze_threshold_period": 20,
        "squeeze_threshold_mult": 0.8,
        "breakout_volume_sma_len": 20,
        "breakout_volume_mult": 1.2,
    },

    # --- Common Signal Confirmation (15m chart) ---
    "strategy": {
        "fast_ema": 9,
        "slow_ema": 21,
        "rsi_period": 14,
        "rsi_overbought": 70,
        "rsi_oversold": 30,
        # Supertrend settings SL calculation ke liye
        "supertrend_period": 10,
        "supertrend_multiplier": 3,
    },

    "active_strategy": "advanced",  # Options: "simple", "mtf", "pullback", "bollinger", "advanced"

    # --- Advanced Strategy (MACD + RSI + ATR) ---
    "advanced_strategy": {
        "trend_timeframe": "4h",
        "trend_ema_period": 200,
        "macd_fast": 12,
        "macd_slow": 26,
        "macd_signal": 9,
        "rsi_period": 14,
        "rsi_buy_threshold": 50,
        "rsi_sell_threshold": 50,
        "atr_period": 14,
        "atr_sl_multiplier": 1.5,
        "atr_tp_multiplier": 3.0
    },

    # --- Risk Management ---
    "risk_management": {
        "tp_percentage": 0.02,  # 2% TP (SL dynamic Supertrend se nikalta hai)
    },

    # --- Firebase Settings ---
    # NOTE: Yahan bhi aap env vars use kar sakte ho production me
    "firebase_db_url": os.getenv("FIREBASE_DB_URL"),
    "firebase_credentials_json": os.environ.get("FIREBASE_CREDENTIALS_JSON"),
    "firebase_credentials_path": os.getenv("FIREBASE_CREDENTIALS_PATH"),

    # --- Proxy Settings (Optional) ---
    "proxy_url": os.getenv("PROXY_URL"), # Example: "http://user:pass@host:port"
}

# --- Colorama init (terminal colors ke liye) ---
colorama.init(autoreset=True)


class ForexTradingBotTiingo:
    """
    Yeh main Forex bot class hai jo:
    - Tiingo WebSocket se live FX ticks leta hai
    - 1-min candles banata hai
    - Un se 15m, 1h, 4h candles aggregate karta hai
    - Multiple strategies se signals generate karta hai
    - Firebase par live prices, signals aur history sync karta hai
    """

    def __init__(self, config):
        # Basic state
        self.config = config
        self.websocket = None

        # Firebase init
        self.db = self._initialize_firebase()

        # Active signals mapping: symbol_name -> signal_data
        self.active_signals = {}

        # Forex pairs list (Tiingo tickers)
        self.top_pairs = []

        # Helper states
        self.last_price_print_time = 0

        # OHLC data per symbol/timeframe: key = "eurusd_15", "eurusd_60", "eurusd_240"
        self.ohlc_data = {}

        # 1-min candles state
        self.minute_candles = {}          # current running 1-min candle
        self.minute_candle_history = {}   # 1-min candle history list

        # Last closed candle timestamps for har timeframe
        self.last_candle_timestamps = {}

        # Latest price per symbol (display + Firebase live_prices)
        self.latest_prices = {}

        # History cleanup tracking
        self.last_history_cleanup = datetime.now()

        # Last 15m candle ko double process na karne ke liye
        self.last_15m_candle_time = {}

    # ------------------ Helper Functions ------------------

    async def _send_telegram_alert(self, message):
        """Sends an alert message to Telegram."""
        token = self.config.get('telegram_token')
        chat_id = self.config.get('telegram_chat_id')
        if not token or not chat_id:
            return

        url = f"https://api.telegram.org/bot{token}/sendMessage"
        payload = {
            "chat_id": chat_id,
            "text": message,
            "parse_mode": "HTML"
        }
        try:
            async with aiohttp.ClientSession() as session:
                async with session.post(url, json=payload) as response:
                    if response.status != 200:
                        print(f"{Fore.RED}Telegram alert failed: {await response.text()}")
        except Exception as e:
            print(f"{Fore.RED}Error sending Telegram alert: {e}")

    def _format_symbol_for_display(self, symbol):
        """
        Symbol ko display format me convert karta hai.
        Example: 'eurusd' -> 'EUR/USD'
        """
        return symbol[:3].upper() + '/' + symbol[3:].upper()

    def _get_firebase_key(self, symbol_name):
        """
        Forex symbol ko Firebase key me convert karta hai.
        Abhi simple lower-case hi use kar rahe hain.
        Example: 'eurusd' -> 'eurusd'
        """
        return symbol_name.lower()

    def calculate_supertrend(self, df, period=10, multiplier=3):
        """
        Supertrend indicator calculate karta hai.
        Iska use:
        - MTF strategy me trend filter
        - SL ke liye dynamic support/resistance
        """
        try:
            # Data length check
            if len(df) < period + 1:
                return None

            hl2 = (df['high'] + df['low']) / 2
            atr = ta.volatility.average_true_range(
                df['high'], df['low'], df['close'], window=period
            )

            # ATR agar NaN ho raha ho to bhi exit
            if atr.isna().all():
                return None

            upper_band = hl2 + (multiplier * atr)
            lower_band = hl2 - (multiplier * atr)
            final_upper_band = upper_band.copy()
            final_lower_band = lower_band.copy()

            for i in range(1, len(df)):
                if final_upper_band[i - 1] > df['close'][i - 1] or upper_band[i] > final_upper_band[i - 1]:
                    final_upper_band[i] = min(upper_band[i], final_upper_band[i - 1])
                else:
                    final_upper_band[i] = upper_band[i]

                if final_lower_band[i - 1] < df['close'][i - 1] or lower_band[i] < final_lower_band[i - 1]:
                    final_lower_band[i] = max(lower_band[i], final_lower_band[i - 1])
                else:
                    final_lower_band[i] = lower_band[i]

            supertrend = [True] * len(df)
            supertrend_direction = [1] * len(df)

            for i in range(len(df)):
                if i == 0:
                    continue
                if df['close'][i] > final_upper_band[i - 1]:
                    supertrend[i] = True
                    supertrend_direction[i] = 1
                elif df['close'][i] < final_lower_band[i - 1]:
                    supertrend[i] = False
                    supertrend_direction[i] = -1
                else:
                    supertrend[i] = supertrend[i - 1]
                    supertrend_direction[i] = supertrend_direction[i - 1]

            df['supertrend'] = np.where(supertrend, final_lower_band, final_upper_band)
            df['supertrend_direction'] = supertrend_direction
            return df

        except Exception as e:
            print(f"{Fore.RED}Error calculating Supertrend: {e}")
            return None

    def _initialize_firebase(self):
        """
        Firebase Realtime Database se connection banata hai.
        Pehle Env Var (FIREBASE_CREDENTIALS_JSON) check karta hai, phir local file.
        """
        try:
            if not firebase_admin._apps:
                # 1. Try Environment Variable (Railway/Render)
                cred_json = self.config.get('firebase_credentials_json')
                if cred_json:
                    try:
                        print(f"{Fore.CYAN}Using Firebase credentials from environment variable...")
                        if isinstance(cred_json, str):
                            cred_info = json.loads(cred_json)
                        else:
                            cred_info = cred_json
                        cred = credentials.Certificate(cred_info)
                        firebase_admin.initialize_app(cred, {'databaseURL': self.config['firebase_db_url']})
                        print(f"{Fore.GREEN}Successfully connected to Firebase Realtime Database (via Env Var).")
                        return db.reference('/')
                    except Exception as env_e:
                        print(f"{Fore.YELLOW}Failed to load credentials from Env Var: {env_e}. Falling back to file...")

                # 2. Try Local File Path
                cred_path = self.config['firebase_credentials_path']
                if os.path.exists(cred_path):
                    cred = credentials.Certificate(cred_path)
                    firebase_admin.initialize_app(
                        cred,
                        {'databaseURL': self.config['firebase_db_url']},
                    )
                    print(f"{Fore.GREEN}Successfully connected to Firebase Realtime Database (via File).")
                    return db.reference('/')
                else:
                    print(f"{Fore.RED}Firebase credentials not found in environment variable OR file at: {cred_path}")
                    return None

            return db.reference('/')

        except Exception as e:
            print(f"{Fore.RED}Failed to initialize Firebase: {e}")
            return None

    def _send_top_pairs_to_firebase(self, pairs_list):
        """
        Forex pairs ki list ko Firebase ke 'config/topPairs' me store karta hai.
        UI ko yeh list dikhane ke liye easy ho jata hai.
        """
        if not self.db:
            print(f"{Fore.YELLOW}Firebase not initialized, cannot send pairs.")
            return

        try:
            self.db.child('config').child('topPairs').set(pairs_list)
            print("Successfully updated top pairs in Firebase config.")
        except Exception as e:
            print(f"{Fore.RED}Error sending pairs to Firebase: {e}")

    def _get_forex_pairs(self):
        """
        Yahan major/minor forex pairs define kiye gaye hain (Tiingo ke format me).
        Tiingo FX symbols: sab lowercase, beghair slash, e.g. 'eurusd'
        """
        forex_pairs = [
            'eurusd', 'gbpusd', 'usdjpy', 'usdchf', 'audusd',
            'nzdusd', 'usdcad', 'eurgbp', 'eurjpy', 'gbpjpy', 'eurchf',
        ]
        self.top_pairs = forex_pairs
        print(
            "Top FOREX pairs selected: "
            + ", ".join([self._format_symbol_for_display(p) for p in self.top_pairs])
        )
        self._send_top_pairs_to_firebase(
            [self._format_symbol_for_display(p) for p in self.top_pairs]
        )

    def _load_existing_signals_from_firebase(self):
        if not self.db:
            return

        try:
            signals_ref = self.db.child('signals')
            data = signals_ref.get()
            if not data or not isinstance(data, dict):
                return

            restored_count = 0
            now_iso = datetime.now().isoformat()

            for key, raw in data.items():
                if not isinstance(raw, dict):
                    continue

                status = str(raw.get('status') or '').upper()
                if status not in ("HOLD", "OPEN"):
                    continue

                symbol_name = str(key).lower()

                try:
                    entry_price = float(raw.get('entry_price'))
                    tp = float(raw.get('tp'))
                    sl = float(raw.get('sl'))
                except (TypeError, ValueError):
                    continue

                signal = {
                    'type': str(raw.get('type') or ''),
                    'condition': str(raw.get('condition') or ''),
                    'entry_price': entry_price,
                    'tp': tp,
                    'sl': sl,
                    'timestamp': raw.get('timestamp', now_iso),
                    'firebase_key': key,
                }

                self.active_signals[symbol_name] = signal

                current_price_raw = raw.get('current_price')
                try:
                    current_price_val = float(current_price_raw)
                    if current_price_val > 0:
                        self.latest_prices[symbol_name] = current_price_val
                except (TypeError, ValueError):
                    pass

                restored_count += 1

            if restored_count > 0:
                print(
                    f"{Fore.CYAN}Restored {restored_count} active HOLD signals from Firebase for monitoring."
                )
        except Exception as e:
            print(f"{Fore.RED}Error loading existing signals from Firebase: {e}")

    # ------------------ WebSocket Connection ------------------

    async def _connect_and_subscribe(self):
        """
        Tiingo WebSocket se connect hota hai aur forex pairs subscribe karta hai.
        Agar connection toot jaye to auto-reconnect try karega.
        """
        # Yahan runtime me actual token use hoga (CONFIG se)
        base_token = self.config['tiingo_api_token']
        uri = f"{self.config['tiingo_websocket_url']}?token={base_token}"

        try:
            async with websockets.connect(uri) as websocket:
                self.websocket = websocket
                print("Successfully connected to Tiingo WebSocket.")
                print("Starting FOREX ticker watch loop...")
                print("Starting FOREX signal generation loop...")

                await self._subscribe_to_pairs()
                await self._handle_websocket_messages()

        except Exception as e:
            print(f"{Fore.RED}WebSocket connection failed: {e}")
            print(f"{Fore.YELLOW}Reconnecting in 5 seconds...")
            await asyncio.sleep(5)
            await self._connect_and_subscribe()

    async def _subscribe_to_pairs(self):
        """
        Tiingo ko subscription message bhejta hai, takay hum live ticks receive kar saken.
        """
        subscription_message = {
            "eventName": "subscribe",
            "authorization": self.config['tiingo_api_token'],
            "eventData": {
                "tickers": self.top_pairs,
            },
        }
        await self.websocket.send(json.dumps(subscription_message))
        # Agar yahan error nahi aaya to subscription ok hai

    # ------------------ Candle Building (1-min -> 15m/1h/4h) ------------------

    def _update_minute_candle(self, symbol, tick_data):
        """
        Har aane wale tick se current 1-min candle update karta hai.
        Naya minute start hone par purani minute candle ko history me push karta hai.
        """
        from datetime import datetime, timezone

        now = datetime.now(timezone.utc)
        current_minute_dt = now.replace(second=0, microsecond=0)

        # Minute candle history init
        if symbol not in self.minute_candle_history:
            self.minute_candle_history[symbol] = []

        # Agar new minute start ho gaya
        if symbol not in self.minute_candles or self.minute_candles[symbol]['timestamp'] < current_minute_dt:
            # Pehli se chal rahi candle ko history me daal do
            if symbol in self.minute_candles:
                self.minute_candle_history[symbol].append(self.minute_candles[symbol])
                # Memory bachaane ke liye sirf last 1000 minute candles rakhte hain
                if len(self.minute_candle_history[symbol]) > 1000:
                    self.minute_candle_history[symbol] = self.minute_candle_history[symbol][-1000:]

            # Nayi 1-min candle create karo
            self.minute_candles[symbol] = {
                'timestamp': current_minute_dt,
                'open': tick_data['price'],
                'high': tick_data['price'],
                'low': tick_data['price'],
                'close': tick_data['price'],
                # Tiingo FX ticks me volume mostly nahi hota, isliye 0 ya constant rakh sakte hain
                'volume': 0,
            }
        else:
            # Current minute ke andar hi hai, to candle ko update karo
            candle = self.minute_candles[symbol]
            candle['high'] = max(candle['high'], tick_data['price'])
            candle['low'] = min(candle['low'], tick_data['price'])
            candle['close'] = tick_data['price']
            # Agar real volume aaye to yahan add kar sakte hain

    async def _build_higher_timeframe_candles(self, symbol):
        """
        1-min candles se 15m, 1h, 4h candles aggregate karta hai.
        Isi se indicators aur strategies ka data banta hai.
        """
        if symbol not in self.minute_candles:
            return

        last_minute_candle = self.minute_candles[symbol]

        # ---------- 15m Candle ----------
        key_15m = f"{symbol}_15"
        if key_15m not in self.ohlc_data:
            self.ohlc_data[key_15m] = pd.DataFrame()

        # 15m close check: minute % 15 == 0 aur last timestamp se bada
        if (
            last_minute_candle['timestamp'].minute % 15 == 0
            and (
                key_15m not in self.last_candle_timestamps
                or self.last_candle_timestamps[key_15m] < last_minute_candle['timestamp']
            )
        ):
            # last_15m_candle_time double-processing avoid ke liye
            if symbol not in self.last_15m_candle_time:
                self.last_15m_candle_time[symbol] = None

            if self.last_15m_candle_time[symbol] != last_minute_candle['timestamp']:
                self.last_15m_candle_time[symbol] = last_minute_candle['timestamp']

                # last 15 minute candles se ek 15m candle aggregate karo
                if symbol in self.minute_candle_history and len(self.minute_candle_history[symbol]) >= 15:
                    minute_candles = self.minute_candle_history[symbol][-15:]

                    fifteen_min_candle = {
                        'timestamp': minute_candles[0]['timestamp'],
                        'open': minute_candles[0]['open'],
                        'high': max(c['high'] for c in minute_candles),
                        'low': min(c['low'] for c in minute_candles),
                        'close': minute_candles[-1]['close'],
                        'volume': sum(c['volume'] for c in minute_candles),
                    }

                    new_candle_df = pd.DataFrame([fifteen_min_candle])
                    self.ohlc_data[key_15m] = pd.concat(
                        [self.ohlc_data[key_15m], new_candle_df],
                        ignore_index=True,
                    )

                    # Sirf last 500 15m candles rakhte hain
                    if len(self.ohlc_data[key_15m]) > 500:
                        self.ohlc_data[key_15m] = self.ohlc_data[key_15m].iloc[-500:]

                    self.last_candle_timestamps[key_15m] = last_minute_candle['timestamp']

                    # 15m Supertrend SL ke liye calculate karo (agar data kaafi ho)
                    if len(self.ohlc_data[key_15m]) >= self.config['strategy']['supertrend_period'] + 1:
                        self.ohlc_data[key_15m] = self.calculate_supertrend(
                            self.ohlc_data[key_15m],
                            self.config['strategy']['supertrend_period'],
                            self.config['strategy']['supertrend_multiplier'],
                        )

                    # Log message for 15m candle close
                    clean_symbol = self._format_symbol_for_display(symbol)
                    print(
                        f"[{datetime.now().strftime('%H:%M:%S')}] "
                        f"New 15m candle closed for {clean_symbol}. Checking for signals..."
                    )

                    # Agar already koi active signal nahin, to naya signal check karo
                    if symbol not in self.active_signals:
                        await self._check_symbol_for_signals(symbol, fifteen_min_candle['close'])

        # ---------- 1h Candle ----------
        key_1h = f"{symbol}_60"
        if key_1h not in self.ohlc_data:
            self.ohlc_data[key_1h] = pd.DataFrame()

        if (
            last_minute_candle['timestamp'].minute == 0
            and (
                key_1h not in self.last_candle_timestamps
                or self.last_candle_timestamps[key_1h] < last_minute_candle['timestamp']
            )
        ):
            if symbol in self.minute_candle_history and len(self.minute_candle_history[symbol]) >= 60:
                minute_candles = self.minute_candle_history[symbol][-60:]

                one_hour_candle = {
                    'timestamp': minute_candles[0]['timestamp'],
                    'open': minute_candles[0]['open'],
                    'high': max(c['high'] for c in minute_candles),
                    'low': min(c['low'] for c in minute_candles),
                    'close': minute_candles[-1]['close'],
                    'volume': sum(c['volume'] for c in minute_candles),
                }

                new_candle_df = pd.DataFrame([one_hour_candle])
                self.ohlc_data[key_1h] = pd.concat(
                    [self.ohlc_data[key_1h], new_candle_df],
                    ignore_index=True,
                )

                if len(self.ohlc_data[key_1h]) > 500:
                    self.ohlc_data[key_1h] = self.ohlc_data[key_1h].iloc[-500:]

                self.last_candle_timestamps[key_1h] = last_minute_candle['timestamp']

        # ---------- 4h Candle ----------
        key_4h = f"{symbol}_240"
        if key_4h not in self.ohlc_data:
            self.ohlc_data[key_4h] = pd.DataFrame()

        if (
            last_minute_candle['timestamp'].hour % 4 == 0
            and last_minute_candle['timestamp'].minute == 0
            and (
                key_4h not in self.last_candle_timestamps
                or self.last_candle_timestamps[key_4h] < last_minute_candle['timestamp']
            )
        ):
            if symbol in self.minute_candle_history and len(self.minute_candle_history[symbol]) >= 240:
                minute_candles = self.minute_candle_history[symbol][-240:]

                four_hour_candle = {
                    'timestamp': minute_candles[0]['timestamp'],
                    'open': minute_candles[0]['open'],
                    'high': max(c['high'] for c in minute_candles),
                    'low': min(c['low'] for c in minute_candles),
                    'close': minute_candles[-1]['close'],
                    'volume': sum(c['volume'] for c in minute_candles),
                }

                new_candle_df = pd.DataFrame([four_hour_candle])
                self.ohlc_data[key_4h] = pd.concat(
                    [self.ohlc_data[key_4h], new_candle_df],
                    ignore_index=True,
                )

                if len(self.ohlc_data[key_4h]) > 500:
                    self.ohlc_data[key_4h] = self.ohlc_data[key_4h].iloc[-500:]

                self.last_candle_timestamps[key_4h] = last_minute_candle['timestamp']

    # ------------------ WebSocket Message Handling ------------------

    async def _handle_websocket_messages(self):
        """
        WebSocket se har tick message read karta hai, JSON parse karta hai,
        price update karta hai, candles build karta hai, aur TP/SL check karta hai.
        """
        try:
            async for message in self.websocket:
                try:
                    data = json.loads(message)

                    if data.get("service") == "fx" and "data" in data and data.get("messageType") == "A":
                        tick_data = data['data']
                        # Tiingo FX format: ["Q", "symbol", "timestamp", "volume", "bid", "ask", "volume", "mid"]
                        if len(tick_data) >= 6:
                            symbol = tick_data[1]  # FX symbol e.g. 'eurusd'
                            bid = tick_data[4]
                            ask = tick_data[5]
                            price = (bid + ask) / 2

                            # Latest price store karo
                            self.latest_prices[symbol] = price

                            from datetime import datetime, timezone
                            self._update_minute_candle(
                                symbol,
                                {'price': price, 'timestamp': datetime.now(timezone.utc)},
                            )

                            # Agar signal active hai to TP/SL check + signal price update
                            if symbol in self.active_signals:
                                await self._check_tp_sl(symbol, price)
                                self._update_signal_price_in_firebase(symbol, price)
                            else:
                                # Agar koi active signal nahi hai to sirf live price Firebase me bhejo
                                self._update_live_price_in_firebase(symbol, price)

                            await self._build_higher_timeframe_candles(symbol)

                except json.JSONDecodeError:
                    print(f"{Fore.RED}[ERROR] Failed to decode JSON from message: {message}")
                except Exception as e:
                    print(f"{Fore.RED}[ERROR] Error processing message: {e}")
                    import traceback
                    print(traceback.format_exc())

        except websockets.exceptions.ConnectionClosed as e:
            print(
                f"{Fore.RED}[ERROR] WebSocket connection closed unexpectedly. "
                f"Code: {e.code}, Reason: {e.reason}"
            )
            print(f"{Fore.YELLOW}Attempting to reconnect in 5 seconds...")
            await asyncio.sleep(5)
            await self._connect_and_subscribe()
        except Exception as e:
            print(f"{Fore.RED}[ERROR] A critical error occurred in message handler: {e}")
            import traceback
            print(traceback.format_exc())

    # ------------------ Firebase Helpers (live price + signals + history) ------------------

    def _update_signal_price_in_firebase(self, symbol_name, current_price):
        """
        Active signal ki current price ko Firebase 'signals/{key}' me update karta hai.
        """
        if symbol_name not in self.active_signals or not self.db:
            return

        signal_data = self.active_signals[symbol_name]
        firebase_key = signal_data.get('firebase_key') or self._get_firebase_key(symbol_name)

        try:
            update_data = {
                "current_price": current_price,
                "last_updated": datetime.now().isoformat(),
            }
            signal_ref = self.db.child('signals').child(firebase_key)
            signal_ref.update(update_data)
        except Exception as e:
            print(f"{Fore.RED}Error updating signal price in Firebase: {e}")

    def _update_live_price_in_firebase(self, symbol_name, current_price):
        """
        Jab koi active signal nahi ho, tab 'live_prices/{symbol}' me sirf last price update hota hai.
        Dashboard 'WAIT FOR SIGNAL' ke waqt yahan se price dikha sakta hai.
        """
        if not self.db:
            return

        try:
            update_data = {
                "price": current_price,
                "timestamp": datetime.now().isoformat(),
            }
            price_ref = self.db.child('live_prices').child(symbol_name)
            price_ref.update(update_data)
        except Exception:
            # Yahan error silent rakha gaya hai takay bot crash na kare
            pass

    async def _check_tp_sl(self, symbol_name, current_price):
        """
        Active signal ke liye TP/SL hit check karta hai.
        Agar TP/SL hit ho jaye to:
        - Firebase me signal status update
        - History me entry add
        - active_signals se remove
        - Telegram alert send karta hai
        """
        if symbol_name not in self.active_signals:
            return

        signal_data = self.active_signals[symbol_name]
        tp_hit, sl_hit = False, False

        # Support both old and advanced signal types
        is_buy = "Buy" in signal_data['type']
        is_sell = "Sell" in signal_data['type']

        if is_buy:
            if current_price >= signal_data['tp']:
                tp_hit = True
            elif current_price <= signal_data['sl']:
                sl_hit = True
        elif is_sell:
            if current_price <= signal_data['tp']:
                tp_hit = True
            elif current_price >= signal_data['sl']:
                sl_hit = True

        if tp_hit or sl_hit:
            status = "TP_HIT" if tp_hit else "SL_HIT"
            result_text = "✅ TP HIT" if tp_hit else "❌ SL HIT"
            clean_symbol = self._format_symbol_for_display(symbol_name)

            print(f"\n{Fore.MAGENTA}{'=' * 40}")
            print(f"{Fore.CYAN}{clean_symbol} | {signal_data['type']} Signal Closed")
            print(f"{result_text} at {current_price:.5f}")
            print(f"{Fore.MAGENTA}{'=' * 40}\n")

            # Firebase par signal status update karo
            update_data = {
                "status": status,
                "closed_at": datetime.now().isoformat(),
                "close_price": current_price,
                "close_reason": status,
            }
            self._update_signal_in_firebase(symbol_name, signal_data.get('firebase_key'), update_data)

            # History me save karo
            self._save_to_history(symbol_name, signal_data, current_price, tp_hit)

            # --- Telegram Alert for Closed Trade ---
            pnl_val = ((current_price - signal_data['entry_price']) / signal_data['entry_price']) * 100
            if is_sell: pnl_val = -pnl_val
            
            close_message = (
                f"<b>{result_text} - FOREX SIGNAL CLOSED</b>\n\n"
                f"<b>Symbol:</b> {clean_symbol}\n"
                f"<b>Type:</b> {signal_data['type']}\n"
                f"<b>Entry:</b> {signal_data['entry_price']:.5f}\n"
                f"<b>Close:</b> {current_price:.5f}\n"
                f"<b>PnL:</b> {pnl_val:.2f}%"
            )
            await self._send_telegram_alert(close_message)

            # In‑memory se hata do
            del self.active_signals[symbol_name]

            # Abse sirf live price Firebase me jayega
            self._update_live_price_in_firebase(symbol_name, current_price)

    def _save_to_history(self, symbol_name, signal_data, close_price, tp_hit):
        """
        Closed signal ko Firebase 'history' node me push karta hai.
        Dashboard ka history table issi data ko use karega.
        """
        if not self.db:
            return

        try:
            history_ref = self.db.child('history')

            # PnL percentage calculate
            pnl_pct = ((close_price - signal_data['entry_price']) / signal_data['entry_price']) * 100

            history_entry = {
                "symbol": self._format_symbol_for_display(symbol_name),
                "type": signal_data['type'],
                "condition": signal_data['condition'],
                "entry_price": signal_data['entry_price'],
                "tp": signal_data['tp'],
                "sl": signal_data['sl'],
                "close_price": close_price,
                "status": "TP_HIT" if tp_hit else "SL_HIT",
                "open_timestamp": signal_data.get('timestamp', datetime.now().isoformat()),
                "close_timestamp": datetime.now().isoformat(),
                "profit_loss_pct": pnl_pct,
            }
            history_ref.push(history_entry)
            print(
                f"{Fore.CYAN}Signal saved to history: {signal_data['type']} "
                f"for {self._format_symbol_for_display(symbol_name)}"
            )

        except Exception as e:
            print(f"{Fore.RED}Error saving signal to history: {e}")

    def _cleanup_history(self):
        """
        History me se 3 din se purani entries delete karta hai.
        Isse Firebase ka size manageable rehta hai.
        """
        if not self.db:
            return

        try:
            history_ref = self.db.child('history')
            three_days_ago = (datetime.now() - timedelta(days=3)).isoformat()

            all_history = history_ref.get()
            if not all_history:
                return

            for key, entry in all_history.items():
                if entry.get('close_timestamp', '') < three_days_ago:
                    history_ref.child(key).delete()
                    print(f"{Fore.YELLOW}Removed old history entry for {entry.get('symbol', 'Unknown')}")

            self.last_history_cleanup = datetime.now()
            print(f"{Fore.GREEN}History cleanup completed")

        except Exception as e:
            print(f"{Fore.RED}Error during history cleanup: {e}")

    # ------------------ Trend + Strategy Helpers ------------------

    def _get_trend(self, symbol_name, timeframe_minutes, ema_period):
        """
        Given timeframe (15/60/240 min) par EMA se BULLISH/BEARISH/NEUTRAL trend detect karta hai.
        """
        key = f"{symbol_name}_{timeframe_minutes}"
        if key not in self.ohlc_data or len(self.ohlc_data[key]) < ema_period:
            return "NEUTRAL"

        df = self.ohlc_data[key]
        df['ema'] = ta.trend.ema_indicator(df['close'], window=ema_period)
        last_candle_close = df['close'].iloc[-1]
        last_ema_value = df['ema'].iloc[-1]

        if last_candle_close > last_ema_value:
            return "BULLISH"
        elif last_candle_close < last_ema_value:
            return "BEARISH"
        else:
            return "NEUTRAL"

    def _generate_strong_trend_signal(self, symbol_name):
        """
        Strong Trend Strategy:
        - 4H aur 1H trend match hona chahiye
        - 15m par EMA + MACD + RSI confirmation
        """
        trend_4h = self._get_trend(symbol_name, 240, self.config['trend_ema_period'])
        trend_1h = self._get_trend(symbol_name, 60, self.config['trend_ema_period'])

        if trend_4h != trend_1h or trend_1h == "NEUTRAL":
            return None

        key = f"{symbol_name}_15"
        if key not in self.ohlc_data or len(self.ohlc_data[key]) < 50:
            return None

        df = self.ohlc_data[key].copy()
        df = self._calculate_indicators(df)

        if len(df) < 3:
            return None

        # Repainting avoid karne ke liye second last candle use karte hain
        last_candle = df.iloc[-2]
        prev_candle = df.iloc[-3]

        if trend_1h == "BULLISH":
            ema_cross_buy = (
                prev_candle['ema_fast'] < prev_candle['ema_slow']
                and last_candle['ema_fast'] > last_candle['ema_slow']
            )
            macd_cross_buy = (
                prev_candle['macd'] < prev_candle['macd_signal']
                and last_candle['macd'] > last_candle['macd_signal']
            )
            rsi_ok_buy = last_candle['rsi'] < self.config['strategy']['rsi_overbought']

            if ema_cross_buy and macd_cross_buy and rsi_ok_buy:
                return {
                    "type": "Strong Buy",
                    "condition": "Bullish (HTF Confirmed)",
                    "entry_price": last_candle['close'],
                }

        elif trend_1h == "BEARISH":
            ema_cross_sell = (
                prev_candle['ema_fast'] > prev_candle['ema_slow']
                and last_candle['ema_fast'] < last_candle['ema_slow']
            )
            macd_cross_sell = (
                prev_candle['macd'] > prev_candle['macd_signal']
                and last_candle['macd'] < last_candle['macd_signal']
            )
            rsi_ok_sell = last_candle['rsi'] > self.config['strategy']['rsi_oversold']

            if ema_cross_sell and macd_cross_sell and rsi_ok_sell:
                return {
                    "type": "Strong Sell",
                    "condition": "Bearish (HTF Confirmed)",
                    "entry_price": last_candle['close'],
                }

        return None

    def _generate_rsi_volume_pullback_signal(self, symbol_name):
        """
        RSI + Volume Pullback Strategy:
        - Strong trend me RSI oversold/overbought se reversal candle + high volume dhoondhta hai.
        """
        key = f"{symbol_name}_15"
        if (
            key not in self.ohlc_data
            or self.ohlc_data[key] is None
            or len(self.ohlc_data[key]) < self.config['pullback_trend_ema_len']
        ):
            return None

        df = self.ohlc_data[key].copy()
        df['ema_trend'] = ta.trend.ema_indicator(
            df['close'], window=self.config['pullback_trend_ema_len']
        )
        df['rsi'] = ta.momentum.rsi(
            df['close'], window=self.config['pullback_rsi_len']
        )
        df['vol_sma'] = ta.trend.sma_indicator(
            df['volume'], window=self.config['pullback_volume_sma_len']
        )

        if len(df) < 2:
            return None

        last_candle = df.iloc[-1]
        prev_candle = df.iloc[-2]

        is_uptrend = last_candle['close'] > last_candle['ema_trend']
        is_downtrend = last_candle['close'] < last_candle['ema_trend']
        strong_volume = last_candle['volume'] > (
            last_candle['vol_sma'] * self.config['pullback_volume_mult']
        )
        rsi_was_oversold = prev_candle['rsi'] < self.config['pullback_rsi_oversold']
        price_reverses_up = (
            last_candle['close'] > prev_candle['close']
            and last_candle['close'] > last_candle['open']
        )

        if is_uptrend and rsi_was_oversold and price_reverses_up and strong_volume:
            return {
                "type": "Buy",
                "condition": "Bullish Pullback (Volume Confirmed)",
                "entry_price": last_candle['close'],
            }

        rsi_was_overbought = prev_candle['rsi'] > self.config['pullback_rsi_overbought']
        price_reverses_down = (
            last_candle['close'] < prev_candle['close']
            and last_candle['close'] < last_candle['open']
        )

        if is_downtrend and rsi_was_overbought and price_reverses_down and strong_volume:
            return {
                "type": "Sell",
                "condition": "Bearish Pullback (Volume Confirmed)",
                "entry_price": last_candle['close'],
            }

        return None

    def _generate_multi_timeframe_pullback_signal(self, symbol_name):
        """
        MTF Pullback Strategy:
        - 4H Supertrend + EMA se main trend
        - 1H EMA filter
        - 15m Supertrend cross + volume se entry
        """
        mtf_config = self.config['mtf_strategy']

        # 4H trend
        key_4h = f"{symbol_name}_240"
        if (
            key_4h not in self.ohlc_data
            or self.ohlc_data[key_4h] is None
            or len(self.ohlc_data[key_4h]) < mtf_config['trend_ema_period']
        ):
            return None

        df_4h = self.ohlc_data[key_4h].copy()
        df_4h['ema'] = ta.trend.ema_indicator(
            df_4h['close'], window=mtf_config['trend_ema_period']
        )
        df_4h = self.calculate_supertrend(
            df_4h, mtf_config['supertrend_period'], mtf_config['supertrend_multiplier']
        )

        if df_4h is None:
            return None

        last_4h = df_4h.iloc[-1]
        is_4h_bullish = last_4h['close'] > last_4h['ema'] and last_4h['supertrend_direction'] == 1
        is_4h_bearish = last_4h['close'] < last_4h['ema'] and last_4h['supertrend_direction'] == -1

        if not is_4h_bullish and not is_4h_bearish:
            return None

        # 1H filter
        key_1h = f"{symbol_name}_60"
        if (
            key_1h not in self.ohlc_data
            or self.ohlc_data[key_1h] is None
            or len(self.ohlc_data[key_1h]) < mtf_config['filter_ema_period']
        ):
            return None

        df_1h = self.ohlc_data[key_1h].copy()
        df_1h['ema'] = ta.trend.ema_indicator(
            df_1h['close'], window=mtf_config['filter_ema_period']
        )
        last_1h = df_1h.iloc[-1]

        if is_4h_bullish and not (last_1h['close'] > last_1h['ema']):
            return None

        if is_4h_bearish and not (last_1h['close'] < last_1h['ema']):
            return None

        # 15m entry
        key_15m = f"{symbol_name}_15"
        if key_15m not in self.ohlc_data or self.ohlc_data[key_15m] is None:
            return None

        df_15m = self.ohlc_data[key_15m].copy()
        df_15m = self.calculate_supertrend(
            df_15m, mtf_config['supertrend_period'], mtf_config['supertrend_multiplier']
        )
        df_15m['vol_sma'] = ta.trend.sma_indicator(
            df_15m['volume'], window=mtf_config['entry_volume_sma_len']
        )

        if df_15m is None or len(df_15m) < 2:
            return None

        last_candle = df_15m.iloc[-1]
        prev_candle = df_15m.iloc[-2]
        strong_volume = last_candle['volume'] > (
            last_candle['vol_sma'] * mtf_config['entry_volume_multiplier']
        )

        if is_4h_bullish:
            pullback_condition = prev_candle['close'] < prev_candle['supertrend']
            entry_condition = (
                last_candle['close'] > last_candle['supertrend']
                and last_candle['close'] > last_candle['open']
            )

            if pullback_condition and entry_condition and strong_volume:
                return {
                    "type": "Buy",
                    "condition": "MTF Bullish Pullback",
                    "entry_price": last_candle['close'],
                }

        if is_4h_bearish:
            pullback_condition = prev_candle['close'] > prev_candle['supertrend']
            entry_condition = (
                last_candle['close'] < last_candle['supertrend']
                and last_candle['close'] < last_candle['open']
            )

            if pullback_condition and entry_condition and strong_volume:
                return {
                    "type": "Sell",
                    "condition": "MTF Bearish Pullback",
                    "entry_price": last_candle['close'],
                }

        return None

    def _generate_bollinger_breakout_signal(self, symbol_name):
        """
        Bollinger Bands Breakout Strategy:
        - Pehle squeeze (narrow bands) detect karta hai
        - Phir volume ke sath upper/lower band breakout dhoondhta hai
        """
        bb_config = self.config['bb_strategy']

        key = f"{symbol_name}_15"
        if key not in self.ohlc_data or self.ohlc_data[key] is None:
            return None

        df = self.ohlc_data[key].copy()
        df['bb_upperband'] = ta.volatility.bollinger_hband(
            df['close'],
            window=bb_config['bb_period'],
            window_dev=bb_config['bb_std_dev'],
        )
        df['bb_lowerband'] = ta.volatility.bollinger_lband(
            df['close'],
            window=bb_config['bb_period'],
            window_dev=bb_config['bb_std_dev'],
        )
        df['bb_width'] = df['bb_upperband'] - df['bb_lowerband']
        df['bb_width_sma'] = ta.trend.sma_indicator(
            df['bb_width'], window=bb_config['squeeze_threshold_period']
        )
        df['vol_sma'] = ta.trend.sma_indicator(
            df['volume'], window=bb_config['breakout_volume_sma_len']
        )

        if len(df) < 2:
            return None

        last_candle = df.iloc[-1]
        prev_candle = df.iloc[-2]

        # Squeeze condition (bands narrow)
        was_squeezed = prev_candle['bb_width'] < (
            prev_candle['bb_width_sma'] * bb_config['squeeze_threshold_mult']
        )

        strong_volume = last_candle['volume'] > (
            last_candle['vol_sma'] * bb_config['breakout_volume_mult']
        )

        # Long breakout
        bullish_breakout = last_candle['close'] > last_candle['bb_upperband']
        if was_squeezed and bullish_breakout and strong_volume:
            return {
                "type": "Buy",
                "condition": "Bollinger Bullish Breakout",
                "entry_price": last_candle['close'],
            }

        # Short breakout
        bearish_breakout = last_candle['close'] < last_candle['bb_lowerband']
        if was_squeezed and bearish_breakout and strong_volume:
            return {
                "type": "Sell",
                "condition": "Bollinger Bearish Breakout",
                "entry_price": last_candle['close'],
            }

        return None

    def _calculate_indicators(self, df):
        """
        EMA + RSI + MACD indicators calc karta hai (Strong Trend ke liye).
        """
        df['ema_fast'] = ta.trend.ema_indicator(
            df['close'], window=self.config['strategy']['fast_ema']
        )
        df['ema_slow'] = ta.trend.ema_indicator(
            df['close'], window=self.config['strategy']['slow_ema']
        )
        df['rsi'] = ta.momentum.rsi(
            df['close'], window=self.config['strategy']['rsi_period']
        )
        df['macd'] = ta.trend.macd_diff(df['close'])
        df['macd_signal'] = ta.trend.macd_signal(df['close'])
        return df

    def _add_advanced_indicators(self, df):
        """Adds all required indicators for the Advanced Strategy to the DataFrame."""
        adv_cfg = self.config['advanced_strategy']
        # MACD
        macd = ta.trend.MACD(
            df['close'],
            window_fast=adv_cfg['macd_fast'],
            window_slow=adv_cfg['macd_slow'],
            window_sign=adv_cfg['macd_signal']
        )
        df['macd_val'] = macd.macd()
        df['macd_sig'] = macd.macd_signal()
        df['macd_diff'] = macd.macd_diff()
        # RSI
        df['rsi_val'] = ta.momentum.rsi(df['close'], window=adv_cfg['rsi_period'])
        # ATR
        df['atr_val'] = ta.volatility.average_true_range(
            df['high'], df['low'], df['close'], window=adv_cfg['atr_period']
        )
        return df

    def _generate_advanced_signal(self, symbol_name):
        """Generates a signal using the Advanced Strategy (Trend EMA, MACD, RSI, ATR)."""
        adv_cfg = self.config['advanced_strategy']

        # 1. Trend Confirmation (HTF - 4H)
        trend_4h = self._get_trend(symbol_name, 240, adv_cfg['trend_ema_period'])
        if trend_4h == "NEUTRAL":
            return None
        
        is_uptrend = (trend_4h == "BULLISH")
        is_downtrend = (trend_4h == "BEARISH")

        # 2. Entry Signal (LTF - 15m)
        key_15m = f"{symbol_name}_15"
        if key_15m not in self.ohlc_data or self.ohlc_data[key_15m] is None:
            return None

        df_15m = self.ohlc_data[key_15m].copy()
        df_15m = self._add_advanced_indicators(df_15m)
        
        if len(df_15m) < 3:
            return None

        last = df_15m.iloc[-1]
        prev = df_15m.iloc[-2]

        # --- Buy Signal Conditions ---
        if is_uptrend:
            macd_crossed_up = prev['macd_val'] < prev['macd_sig'] and last['macd_val'] > last['macd_sig']
            rsi_is_ok = last['rsi_val'] > adv_cfg['rsi_buy_threshold']
            if macd_crossed_up and rsi_is_ok:
                return {
                    "type": "Advanced Buy",
                    "condition": f"Uptrend (4H EMA) + MACD Crossover",
                    "entry_price": last['close'],
                    "atr": last['atr_val']
                }

        # --- Sell Signal Conditions ---
        if is_downtrend:
            macd_crossed_down = prev['macd_val'] > prev['macd_sig'] and last['macd_val'] < last['macd_sig']
            rsi_is_ok = last['rsi_val'] < adv_cfg['rsi_sell_threshold']
            if macd_crossed_down and rsi_is_ok:
                return {
                    "type": "Advanced Sell",
                    "condition": f"Downtrend (4H EMA) + MACD Crossover",
                    "entry_price": last['close'],
                    "atr": last['atr_val']
                }

        return None

    def _calculate_atr_sl_tp(self, signal_type, entry_price, atr):
        """Calculates ATR-based SL/TP for Forex."""
        adv_cfg = self.config['advanced_strategy']
        sl_mult = adv_cfg['atr_sl_multiplier']
        tp_mult = adv_cfg['atr_tp_multiplier']

        if "Buy" in signal_type:
            sl = entry_price - (atr * sl_mult)
            tp = entry_price + (atr * tp_mult)
        else:
            sl = entry_price + (atr * sl_mult)
            tp = entry_price - (atr * tp_mult)
        return sl, tp

    def _calculate_fixed_sl_tp(self, signal_type, entry_price, df_15m):
        """Fallback fixed/Supertrend SL/TP calculation."""
        tp_offset = entry_price * self.config['risk_management']['tp_percentage']
        last_candle = df_15m.iloc[-1]
        
        if 'supertrend' in last_candle and not pd.isna(last_candle['supertrend']):
            sl = last_candle['supertrend']
        else:
            sl_offset = entry_price * 0.01
            sl = entry_price - sl_offset if "Buy" in signal_type else entry_price + sl_offset
            
        tp = entry_price + tp_offset if "Buy" in signal_type else entry_price - tp_offset
        return sl, tp

    # ------------------ Firebase: Signal Send/Update + Console Display ------------------

    async def _send_signal_to_firebase(self, symbol_name, signal_data):
        """
        Naya signal Firebase me 'signals/{symbolKey}' par save karta hai.
        Har pair ke liye ek hi active signal rakha jata hai (push IDs nahi).
        """
        if not self.db:
            return None

        try:
            firebase_key = self._get_firebase_key(symbol_name)
            clean_symbol = self._format_symbol_for_display(symbol_name)
            now_iso = datetime.now().isoformat()

            dashboard_signal = {
                "symbol": clean_symbol,
                "type": signal_data['type'],
                "condition": signal_data['condition'],
                "entry_price": signal_data['entry_price'],
                "tp": signal_data['tp'],
                "sl": signal_data['sl'],
                "status": "HOLD",
                "timestamp": signal_data.get('timestamp', now_iso),
                "current_price": signal_data['entry_price'],
                "last_updated": now_iso,
            }

            # Yahan direct object set ho raha hai, push nahi
            self.db.child('signals').child(firebase_key).set(dashboard_signal)

            # --- Telegram Alert ---
            emoji = "🚀" if "Buy" in signal_data['type'] else "📉"
            message = (
                f"<b>{emoji} NEW FOREX SIGNAL</b>\n\n"
                f"<b>Symbol:</b> {clean_symbol}\n"
                f"<b>Type:</b> {signal_data['type']}\n"
                f"<b>Condition:</b> {signal_data.get('condition', 'N/A')}\n"
                f"<b>Entry:</b> {signal_data['entry_price']:.5f}\n"
                f"<b>TP:</b> {signal_data['tp']:.5f}\n"
                f"<b>SL:</b> {signal_data['sl']:.5f}"
            )
            await self._send_telegram_alert(message)

            print(
                f"{Fore.CYAN}Signal sent to Firebase & Telegram: {signal_data['type']} "
                f"for {clean_symbol}"
            )
            return firebase_key

        except Exception as e:
            print(f"{Fore.RED}Error sending signal to Firebase/Telegram: {e}")
            return None

    def _update_signal_in_firebase(self, symbol_name, firebase_key, update_data):
        """
        Existing signal ko Firebase me update karta hai (status/close info waghera).
        Agar firebase_key missing ho to symbol se derive karta hai.
        """
        if not self.db:
            return

        key = firebase_key or self._get_firebase_key(symbol_name)

        try:
            signal_ref = self.db.child('signals').child(key)
            signal_ref.update(update_data)
            print(f"{Fore.CYAN}Signal {key} updated in Firebase.")
        except Exception as e:
            print(f"{Fore.RED}Error updating signal in Firebase: {e}")

    def _display_signal(self, symbol_name, signal_data, current_price):
        """
        Naye signal ko terminal me pretty format me print karta hai.
        """
        signal_type = signal_data['type']
        color = Fore.GREEN if "Buy" in signal_type else Fore.RED
        clean_symbol = self._format_symbol_for_display(symbol_name)

        print(f"\n{Fore.MAGENTA}{'=' * 40}")
        print(f"{color}NEW FOREX SIGNAL: {signal_type} | {clean_symbol}")
        print(f"{Fore.CYAN}Market Condition: {signal_data['condition']}")
        print(f"{Fore.YELLOW}Entry Price: {signal_data['entry_price']:.5f}")
        print(f"{Fore.GREEN}Take-Profit (TP): {signal_data['tp']:.5f} (2%)")
        print(f"{Fore.RED}Stop-Loss (SL): {signal_data['sl']:.5f} (Supertrend/Fallback)")
        print(f"{Fore.BLUE}Live Price: {current_price:.5f}")
        print(f"{Fore.MAGENTA}{'=' * 40}\n")

    async def _check_symbol_for_signals(self, symbol_name, current_price):
        """
        Jab naya 15m candle close hota hai:
        - Strategy selection ke mutabiq signals generate karta hai.
        - Dynamic SL/TP calculate karta hai.
        """
        if symbol_name in self.active_signals:
            return

        strategy_name = self.config.get('active_strategy', 'simple')
        signal = None

        if strategy_name == 'advanced':
            signal = self._generate_advanced_signal(symbol_name)
        elif strategy_name == 'simple':
            signal = self._generate_strong_trend_signal(symbol_name)
        elif strategy_name == 'pullback':
            signal = self._generate_rsi_volume_pullback_signal(symbol_name)
        elif strategy_name == 'mtf':
            signal = self._generate_multi_timeframe_pullback_signal(symbol_name)
        elif strategy_name == 'bollinger':
            signal = self._generate_bollinger_breakout_signal(symbol_name)
        else:
            signal = self._generate_strong_trend_signal(symbol_name)

        if signal:
            key_15m = f"{symbol_name}_15"
            if key_15m not in self.ohlc_data or self.ohlc_data[key_15m] is None:
                return
            df_15m = self.ohlc_data[key_15m]

            # SL/TP Calculation
            if strategy_name == 'advanced' and 'atr' in signal:
                sl, tp = self._calculate_atr_sl_tp(signal['type'], signal['entry_price'], signal['atr'])
            else:
                sl, tp = self._calculate_fixed_sl_tp(signal['type'], signal['entry_price'], df_15m)

            signal['sl'] = sl
            signal['tp'] = tp
            signal['timestamp'] = datetime.now().isoformat()

            # Firebase me bhejo + in‑memory store
            firebase_key = await self._send_signal_to_firebase(symbol_name, signal)
            signal['firebase_key'] = firebase_key

            self.active_signals[symbol_name] = signal
            self._display_signal(symbol_name, signal, current_price)

    async def _print_price_updates(self):
        """
        Har 60 sec baad sab pairs ki live situation print karta hai:
        - Agar signal active ho to HOLD + TP/SL + Live price
        - Warna WAIT FOR SIGNAL + live price
        """
        while True:
            await asyncio.sleep(60)
            print(f"\n--- Live FOREX Price Update ({datetime.now().strftime('%H:%M:%S')}) ---")
            for symbol_name in self.top_pairs:
                clean_symbol = self._format_symbol_for_display(symbol_name)
                current_price = self.latest_prices.get(symbol_name, 0)

                if symbol_name in self.active_signals:
                    signal = self.active_signals[symbol_name]
                    color = Fore.GREEN if "Buy" in signal['type'] else Fore.RED
                    print(
                        f"{color}{clean_symbol:<12} | HOLD | "
                        f"Entry: {signal['entry_price']:.5f} | "
                        f"TP: {signal['tp']:.5f} | SL: {signal['sl']:.5f} | "
                        f"Live Price: {current_price:.5f}"
                    )
                else:
                    if current_price > 0:
                        print(
                            f"{clean_symbol:<12} | WAIT FOR SIGNAL | "
                            f"Live Price: {current_price:.5f}"
                        )
                    else:
                        print(f"{clean_symbol:<12} | WAIT FOR SIGNAL")

            print("-" * 40)

            # Daily history cleanup
            if (datetime.now() - self.last_history_cleanup).days >= 1:
                self._cleanup_history()

    # ------------------ Main Run Loop ------------------

    async def run(self):
        """
        Main bot run method:
        - Forex pairs set karta hai
        - Startup par history cleanup karta hai
        - Periodic price print task start karta hai
        - WebSocket se connect ho kar infinite loop chalata hai
        """
        # Forex pairs set karo
        self._get_forex_pairs()

        # Startup par existing HOLD/Open signals ko Firebase se restore karo
        self._load_existing_signals_from_firebase()

        # Startup par history cleanup
        self._cleanup_history()

        # Background task: live price prints
        asyncio.create_task(self._print_price_updates())

        # WebSocket connect + message handling (reconnect logic andar hai)
        await self._connect_and_subscribe()


# ------------------ Auto-Restart Main Loop ------------------

if __name__ == "__main__":
    # Yeh main loop bot ko crash hone par auto-restart karta hai
    while True:
        try:
            bot = ForexTradingBotTiingo(CONFIG)
            asyncio.run(bot.run())

        except KeyboardInterrupt:
            # User ne manually Ctrl+C se stop kiya
            print(f"\n{Fore.YELLOW}Bot stopped by user. Exiting...")
            break

        except Exception as e:
            # Agar unexpected error aaye to 30 sec wait karke dobara start karega
            print(
                f"{Fore.RED}[CRITICAL ERROR] Bot crashed with error: {e}. "
                f"Restarting in 30 seconds..."
            )
            time.sleep(30)
