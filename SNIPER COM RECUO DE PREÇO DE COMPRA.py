import customtkinter as ctk
import ccxt
import pandas as pd
import numpy as np
import time
import threading
import math
import json
import os
from datetime import datetime
from PIL import Image
import random
from io import BytesIO
import requests

try:
    import winsound
except ImportError:
    winsound = None

# --- CONFIGURAÇÃO DO GIF ---
GIF_URL = "https://media0.giphy.com/media/v1.Y2lkPTc5MGI3NjExMG5ud25jYngzOHNtc21kdjg5eXVnNjhjeWIxNDRzZzJibWI3ZTVhNyZlcD12MV9pbnRlcm5hbF9naWZfYnlfaWQmY3Q9Zw/t7jzGb5JT0B2D7w771/giphy.gif"

CMD_PHRASES = [
    "Conectando ao Socket Stream da Binance...",
    "Descriptografando pacotes JSON...",
    "Calculando Entropia de Shannon...",
    "Otimizando threads do processador...",
    "Ping API: 14ms [OK]",
    "Verificando integridade da Wallet...",
    "Carregando módulos de IA (TensorFlow)...",
    "Buscando liquidez oculta no Order Book...",
    "Analisando divergência de RSI...",
    "Sincronizando relógio atômico...",
    "Limpando cache de memória RAM...",
    "Detectando baleias no fluxo de ordens...",
    "Recalculando Bandas de Bollinger...",
    "Monitorando Hashrate da rede...",
    "Executando script de proteção de capital...",
    "Aguardando tick...",
    "Scanning ports 80, 443...",
    "Traceback complete.",
    "Bypass firewall... Success."
]

# ==========================================
# --- CONFIGURAÇÕES E PARÂMETROS ---
# ==========================================
MAX_ATIVOS = 5
DEFAULT_ATIVOS = ["ZEC/USDT"]
DEFAULT_VALOR_USDT = 20.0
TIMEFRAME = "5m"
TIMEFRAME_MACRO = "1h"
SALDO_INICIAL = 100.0
RESERVA_CAPITAL_REAL = 0.95  # Mantém ~5% de folga e divide o restante entre os slots livres.
VALOR_MINIMO_ORDEM_USDT = 10.0

# Gestão de Risco e Lucro
TARGET_NORMAL = 0.0050
TARGET_REPIQUE = 0.0060
STOP_LOSS_FIXO = 0.03
GATILHO_BREAKEVEN = 0.0055

# Entrada com recuo após sinal confirmado
# Ex.: sinal em 1.0000 compra somente entre 0.9982 e 0.9950.
RECUO_ENTRADA_MIN = 0.0018  # 0.18%
RECUO_ENTRADA_MAX = 0.0050  # 0.50%
RECUO_ENTRADA_EXPIRA_SEG = 30 * 60  # cancela sinal pendente após 30 minutos

# Configuração da SAÍDA DE EMERGÊNCIA
PERDA_MAX_EMERGENCIA = -0.018
RSI_EMERGENCIA = 25

# Filtros (Anti-Topo e Book)
DISTANCIA_PADRAO = 0.025
DISTANCIA_EUFORIA = 0.050
BOOK_DEPTH_PCT = 0.005
BOOK_IMBALANCE_LIMIT = 2.5

# Indicadores
ADX_PADRAO = 23
ADX_FORTE = 21
RSI_TETO_MAXIMO = 75

# Arquivos
ARQUIVO_ATIVOS = "ativos_robo.json"
ARQUIVO_ESTADO = "trades_abertos_multi.json"
ARQUIVO_LOG_REAL = "relatorio_trades_REAL.xlsx"
ARQUIVO_LOG_SIM = "relatorio_trades_SIMULACAO.xlsx"

# CHAVES API: defina no Windows antes de executar:
# setx BINANCE_API_KEY "sua_api_key"
# setx BINANCE_SECRET_KEY "sua_secret_key"
API_KEY = os.getenv("BINANCE_API_KEY", "HxPLfQck6PqbUMw47TBgzMeU2d8fvLAHrmtWXYzj9ywtn3DhjjHtVtHuL75lewQC")
SECRET_KEY = os.getenv("BINANCE_SECRET_KEY", "xf9259yVwGSHytF7YvTxBPvO1x8CR8WWF2qjCK7reN5O2hm3IsrCxBos5XDThKPt")


def normalizar_symbol(valor: str) -> str:
    """Normaliza o ativo digitado na interface.

    Exemplos:
    - zec/usdt -> ZEC/USDT
    - zecusdt  -> ZEC/USDT
    - zec      -> ZEC/USDT
    """
    valor = (valor or "").strip().upper().replace(" ", "")
    if not valor:
        return ""
    if "/" in valor:
        base, quote = valor.split("/", 1)
        return f"{base}/{quote or 'USDT'}"
    if valor.endswith("USDT") and len(valor) > 4:
        return f"{valor[:-4]}/USDT"
    return f"{valor}/USDT"


class CryptoBot(ctk.CTk):
    def __init__(self):
        super().__init__()

        self.title("Sniper Pro V8 Multiativos")
        self.geometry("1600x980")
        ctk.set_appearance_mode("Dark")
        ctk.set_default_color_theme("dark-blue")

        self.executando = False
        self.worker_thread = None
        self.selected_symbol = None
        self.symbol_entries = []
        self.amount_entries = []
        self.asset_widgets = {}
        self.telemetry_widgets = {}
        self.telemetry_cache = {}
        self.asset_states = {}
        self.ui_lock = threading.Lock()
        self.config_lock = threading.RLock()

        self.ativos, valores_config = self.carregar_ativos_config()
        if not self.ativos:
            self.ativos = DEFAULT_ATIVOS.copy()
            valores_config = {self.ativos[0]: DEFAULT_VALOR_USDT}
        self.selected_symbol = self.ativos[0]
        for symbol in self.ativos:
            self.asset_states[symbol] = self.create_asset_state(symbol, valores_config.get(symbol, DEFAULT_VALOR_USDT))

        # Conexão Binance
        self.exchange = ccxt.binance({
            "apiKey": API_KEY,
            "secret": SECRET_KEY,
            "enableRateLimit": True,
            "options": {"defaultType": "spot", "adjustForTimeDifference": True}
        })

        self.setup_ui()
        self.verificar_trades_pendentes()

    # ==========================================
    # --- ESTADO E CONFIGURAÇÃO DE ATIVOS ---
    # ==========================================
    def create_asset_state(self, symbol, valor_usdt=None):
        valor = self.parse_valor_usdt(valor_usdt, DEFAULT_VALOR_USDT)
        return {
            "symbol": symbol,
            "valor_usdt": valor,
            "posicionado": False,
            "aguardando_confirmacao": False,
            "entrada_recuo_pendente": False,
            "preco_sinal_entrada": 0.0,
            "preco_recuo_min": 0.0,
            "preco_recuo_max": 0.0,
            "entrada_recuo_inicio": 0.0,
            "entrada_recuo_motivo": "",
            "entrada_recuo_status": "",
            "last_candle_time": None,
            "breakeven_ativado": False,
            "modo_tendencia_ativo": False,
            "preco_compra": 0.0,
            "stop_loss": 0.0,
            "take_profit": 0.0,
            "saldo_usdt": valor,
            "saldo_crypto": 0.0,
            "alvo_atual": TARGET_NORMAL,
            "status": "STATUS: 💤 Aguardando",
            "ativo_ativo": True,
            "remover_apos_venda": False
        }

    def parse_valor_usdt(self, valor, padrao=DEFAULT_VALOR_USDT):
        try:
            if valor is None:
                return float(padrao)
            if isinstance(valor, str):
                valor = valor.strip().replace("$", "").replace("USDT", "").replace(",", ".")
            valor = float(valor)
            return max(valor, 0.0)
        except Exception:
            return float(padrao)

    def carregar_ativos_config(self):
        try:
            if not os.path.exists(ARQUIVO_ATIVOS):
                return DEFAULT_ATIVOS.copy(), {DEFAULT_ATIVOS[0]: DEFAULT_VALOR_USDT}
            with open(ARQUIVO_ATIVOS, "r", encoding="utf-8") as f:
                dados = json.load(f)

            ativos_raw = dados.get("ativos", DEFAULT_ATIVOS)
            valores_salvos = dados.get("valores_usdt", {})
            ativos = []
            valores = {}

            for item in ativos_raw:
                if isinstance(item, dict):
                    symbol = normalizar_symbol(item.get("symbol") or item.get("ativo") or item.get("par") or "")
                    valor = self.parse_valor_usdt(item.get("valor_usdt"), DEFAULT_VALOR_USDT)
                else:
                    symbol = normalizar_symbol(item)
                    valor = self.parse_valor_usdt(valores_salvos.get(symbol), DEFAULT_VALOR_USDT)

                if symbol and symbol not in ativos:
                    ativos.append(symbol)
                    valores[symbol] = valor
                if len(ativos) >= MAX_ATIVOS:
                    break

            if not ativos:
                return DEFAULT_ATIVOS.copy(), {DEFAULT_ATIVOS[0]: DEFAULT_VALOR_USDT}
            return ativos, valores
        except Exception:
            return DEFAULT_ATIVOS.copy(), {DEFAULT_ATIVOS[0]: DEFAULT_VALOR_USDT}

    def salvar_ativos_config(self):
        """Salva apenas os ativos que continuam configurados para novas análises.

        Ativos que foram removidos enquanto estavam posicionados continuam sendo
        monitorados até vender, mas não ficam gravados como ativos fixos para
        novas compras depois do fechamento.
        """
        dados = []
        for symbol in self.ativos:
            state = self.asset_states.get(symbol, {})
            if state.get("remover_apos_venda"):
                continue
            if not state.get("ativo_ativo", True):
                continue
            dados.append({
                "symbol": symbol,
                "valor_usdt": round(float(state.get("valor_usdt", DEFAULT_VALOR_USDT)), 2)
            })
        with open(ARQUIVO_ATIVOS, "w", encoding="utf-8") as f:
            json.dump({"ativos": dados}, f, indent=2)

    def possui_posicao_aberta(self):
        return any(st.get("posicionado") for st in self.asset_states.values())

    def aplicar_ativos_da_interface(self):
        """Aplica alterações sem precisar parar o robô.

        Regras de segurança:
        - Ativo sem posição pode ser adicionado, removido ou ter valor alterado a qualquer momento.
        - Ativo com posição aberta não é interrompido. Se o usuário remover esse ativo,
          ele fica marcado como "remover após venda": o robô continua monitorando a saída
          e não inicia novo ciclo de compra para ele depois que vender.
        - O limite total de monitoramento continua sendo MAX_ATIVOS.
        """
        novos = []
        novos_valores = {}
        for i, entry in enumerate(self.symbol_entries):
            symbol = normalizar_symbol(entry.get())
            valor = DEFAULT_VALOR_USDT
            if i < len(self.amount_entries):
                valor = self.parse_valor_usdt(self.amount_entries[i].get(), DEFAULT_VALOR_USDT)
            if symbol and symbol not in novos:
                novos.append(symbol)
                novos_valores[symbol] = valor

        novos = novos[:MAX_ATIVOS]
        if not novos:
            self.log("Informe pelo menos 1 ativo.")
            return False

        mensagens = []
        with self.config_lock:
            estados_antigos = self.asset_states
            posicionados = [s for s, st in estados_antigos.items() if st.get("posicionado")]

            # Garante que posições abertas continuem sendo monitoradas mesmo se o usuário remover da lista.
            ativos_finais = []
            for symbol in novos:
                if len(ativos_finais) < MAX_ATIVOS and symbol not in ativos_finais:
                    ativos_finais.append(symbol)

            for symbol in posicionados:
                if symbol in ativos_finais:
                    continue
                # Se a lista nova já ocupou 5 vagas, remove o último ativo sem posição para preservar o monitoramento seguro.
                if len(ativos_finais) >= MAX_ATIVOS:
                    removido_para_preservar_posicao = None
                    for idx in range(len(ativos_finais) - 1, -1, -1):
                        candidato = ativos_finais[idx]
                        if not estados_antigos.get(candidato, {}).get("posicionado"):
                            removido_para_preservar_posicao = ativos_finais.pop(idx)
                            break
                    if removido_para_preservar_posicao:
                        mensagens.append(
                            f"{removido_para_preservar_posicao} não entrou porque {symbol} ainda está posicionado e precisa ser monitorado."
                        )
                    else:
                        mensagens.append(
                            f"{symbol} está posicionado e não pôde ser removido do monitoramento agora."
                        )
                        continue
                ativos_finais.append(symbol)
                mensagens.append(f"{symbol} será removido automaticamente após a venda.")

            # Marca os antigos que saíram da lista e não têm posição como inativos.
            for symbol, state in list(estados_antigos.items()):
                if symbol not in ativos_finais and not state.get("posicionado"):
                    state["ativo_ativo"] = False
                    state["remover_apos_venda"] = False

            self.ativos = ativos_finais
            for symbol in self.ativos:
                valor = novos_valores.get(symbol)
                if symbol in estados_antigos:
                    state = estados_antigos[symbol]
                    state["ativo_ativo"] = True
                    state["remover_apos_venda"] = symbol not in novos and state.get("posicionado", False)
                    if valor is not None:
                        state["valor_usdt"] = valor
                        if not state.get("posicionado"):
                            state["saldo_usdt"] = valor
                    self.asset_states[symbol] = state
                else:
                    self.asset_states[symbol] = self.create_asset_state(symbol, novos_valores.get(symbol, DEFAULT_VALOR_USDT))

            if self.selected_symbol not in self.ativos:
                self.selected_symbol = self.ativos[0]
            self.salvar_ativos_config()

        self.rebuild_asset_cards()
        self.preencher_entries_ativos()
        resumo = ", ".join([
            f"{s}=${self.asset_states[s]['valor_usdt']:.2f}"
            + (" (sai após venda)" if self.asset_states[s].get("remover_apos_venda") else "")
            for s in self.ativos
        ])
        if self.executando:
            self.log(f"Ativos/valores atualizados com o robô rodando: {resumo}")
        else:
            self.log(f"Ativos/valores atualizados: {resumo}")
        for msg in mensagens:
            self.log(msg)
        return True

    def remover_ativo_slot(self, idx):
        if idx < len(self.symbol_entries):
            self.symbol_entries[idx].delete(0, "end")
        if idx < len(self.amount_entries):
            self.amount_entries[idx].delete(0, "end")

    def preencher_entries_ativos(self):
        # Mostra nos campos apenas os ativos configurados para novas análises.
        # Ativo removido com posição aberta pode continuar no dashboard até vender,
        # mas não volta para os campos de configuração.
        ativos_para_entries = [
            s for s in self.ativos
            if not self.asset_states.get(s, {}).get("remover_apos_venda")
            and self.asset_states.get(s, {}).get("ativo_ativo", True)
        ]

        for i, entry in enumerate(self.symbol_entries):
            entry.delete(0, "end")
            if i < len(ativos_para_entries):
                symbol = ativos_para_entries[i]
                entry.insert(0, symbol)
        for i, entry in enumerate(self.amount_entries):
            entry.delete(0, "end")
            if i < len(ativos_para_entries):
                symbol = ativos_para_entries[i]
                valor = self.asset_states.get(symbol, {}).get("valor_usdt", DEFAULT_VALOR_USDT)
                entry.insert(0, f"{valor:.2f}")

    # ==========================================
    # --- INTERFACE ---
    # ==========================================
    def setup_ui(self):
        self.grid_columnconfigure(0, weight=3)
        self.grid_columnconfigure(1, weight=2)
        self.grid_rowconfigure(0, weight=1)

        # --- LADO ESQUERDO: CONTROLES + CARDS DOS ATIVOS ---
        self.left_container = ctk.CTkFrame(self, fg_color="transparent")
        self.left_container.grid(row=0, column=0, sticky="nsew", padx=10, pady=10)
        self.left_container.grid_rowconfigure(2, weight=1)
        self.left_container.grid_columnconfigure(0, weight=1)

        self.frame_top = ctk.CTkFrame(self.left_container)
        self.frame_top.grid(row=0, column=0, sticky="ew", pady=(0, 10))
        self.frame_top.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(self.frame_top, text="ROBÔ SNIPER MULTIATIVOS", font=("Roboto", 20, "bold")).grid(row=0, column=0, pady=(5, 2), sticky="ew")
        self.lbl_status_geral = ctk.CTkLabel(self.frame_top, text="STATUS: 💤 Aguardando", font=("Roboto", 16, "bold"), text_color="gray")
        self.lbl_status_geral.grid(row=1, column=0, pady=(2, 5), sticky="ew")

        self.modo_teste_var = ctk.BooleanVar(value=True)
        self.switch_mode = ctk.CTkSwitch(
            self.frame_top,
            text="MODO SIMULAÇÃO",
            variable=self.modo_teste_var,
            onvalue=True,
            offvalue=False,
            command=self.toggle_mode
        )
        self.switch_mode.grid(row=2, column=0, pady=5)

        self.frame_ativos_cfg = ctk.CTkFrame(self.left_container)
        self.frame_ativos_cfg.grid(row=1, column=0, sticky="ew", pady=(0, 10))
        self.frame_ativos_cfg.grid_columnconfigure(1, weight=2)
        self.frame_ativos_cfg.grid_columnconfigure(2, weight=1)
        ctk.CTkLabel(self.frame_ativos_cfg, text=f"ATIVOS PARA ANÁLISE/OPERAÇÃO (máx. {MAX_ATIVOS})", font=("Roboto", 13, "bold"), text_color="#3498DB").grid(row=0, column=0, columnspan=4, pady=(6, 4), sticky="ew")
        ctk.CTkLabel(self.frame_ativos_cfg, text="Ativo", text_color="gray", font=("Roboto", 11, "bold")).grid(row=1, column=1, padx=4, sticky="w")
        ctk.CTkLabel(self.frame_ativos_cfg, text="Valor USDT", text_color="gray", font=("Roboto", 11, "bold")).grid(row=1, column=2, padx=4, sticky="w")

        for i in range(MAX_ATIVOS):
            row = i + 2
            ctk.CTkLabel(self.frame_ativos_cfg, text=f"#{i + 1}", text_color="gray", width=35).grid(row=row, column=0, padx=(8, 4), pady=3)
            entry = ctk.CTkEntry(self.frame_ativos_cfg, placeholder_text="Ex: ZEC/USDT")
            entry.grid(row=row, column=1, padx=4, pady=3, sticky="ew")
            self.symbol_entries.append(entry)

            amount_entry = ctk.CTkEntry(self.frame_ativos_cfg, placeholder_text="Ex: 20.00", width=110)
            amount_entry.grid(row=row, column=2, padx=4, pady=3, sticky="ew")
            self.amount_entries.append(amount_entry)

            ctk.CTkButton(self.frame_ativos_cfg, text="Remover", width=75, fg_color="#7F1D1D", command=lambda idx=i: self.remover_ativo_slot(idx)).grid(row=row, column=3, padx=(4, 8), pady=3)

        self.preencher_entries_ativos()
        ctk.CTkButton(self.frame_ativos_cfg, text="APLICAR ATIVOS / VALORES", command=self.aplicar_ativos_da_interface, fg_color="#1F6AA5", height=32).grid(row=MAX_ATIVOS + 2, column=0, columnspan=4, padx=8, pady=(6, 8), sticky="ew")

        self.frame_assets_scroll = ctk.CTkScrollableFrame(self.left_container, label_text="DASHBOARD DOS ATIVOS")
        self.frame_assets_scroll.grid(row=2, column=0, sticky="nsew", pady=(0, 10))
        self.frame_assets_scroll.grid_columnconfigure(0, weight=1)
        self.rebuild_asset_cards()

        self.textbox = ctk.CTkTextbox(self.left_container, height=120)
        self.textbox.grid(row=3, column=0, sticky="ew", pady=(0, 10))

        self.btn_start = ctk.CTkButton(self.left_container, text="MR ROBOT", command=self.start_thread, fg_color="#27AE60", height=40)
        self.btn_start.grid(row=4, column=0, sticky="ew", pady=(0, 6))
        self.btn_stop = ctk.CTkButton(self.left_container, text="PARAR", command=self.stop_bot, fg_color="#C0392B")
        self.btn_stop.grid(row=5, column=0, sticky="ew")

        # --- LADO DIREITO: TELEMETRIA AVANÇADA DE TODOS OS ATIVOS ---
        self.right_container = ctk.CTkFrame(self, fg_color="#212121")
        self.right_container.grid(row=0, column=1, sticky="nsew", padx=(0, 10), pady=10)
        self.create_detailed_dashboard()

    def rebuild_asset_cards(self):
        if not hasattr(self, "frame_assets_scroll"):
            return
        for widget in self.frame_assets_scroll.winfo_children():
            widget.destroy()
        self.asset_widgets = {}

        for row, symbol in enumerate(self.ativos):
            card = ctk.CTkFrame(self.frame_assets_scroll, fg_color="#2B2B2B", border_width=1, border_color="#3A3A3A")
            card.grid(row=row, column=0, sticky="ew", padx=4, pady=6)
            for col in range(6):
                card.grid_columnconfigure(col, weight=1)

            titulo_symbol = symbol + ("  • sai após venda" if self.asset_states.get(symbol, {}).get("remover_apos_venda") else "")
            title = ctk.CTkLabel(card, text=titulo_symbol, font=("Roboto", 16, "bold"), text_color="#F1C40F")
            title.grid(row=0, column=0, padx=6, pady=(6, 3), sticky="w")
            status_texto = self.asset_states.get(symbol, {}).get("status", "STATUS: 💤 Aguardando")
            if self.asset_states.get(symbol, {}).get("remover_apos_venda"):
                status_texto = "STATUS: 👀 Aguardando venda para remover"
            status = ctk.CTkLabel(card, text=status_texto, font=("Roboto", 13, "bold"), text_color="gray")
            status.grid(row=0, column=1, columnspan=4, padx=6, pady=(6, 3), sticky="ew")
            ctk.CTkButton(card, text="Telemetria", width=90, command=lambda s=symbol: self.selecionar_ativo(s)).grid(row=0, column=5, padx=6, pady=(6, 3), sticky="e")

            labels = {
                "status": status,
                "price": self.create_metric(card, "Preço", "---", 1, 0, "#FFFFFF"),
                "rsi": self.create_metric(card, "RSI", "---", 1, 1, "#9B59B6"),
                "adx": self.create_metric(card, "ADX", "---", 1, 2, "#8E44AD"),
                "sma_20": self.create_metric(card, "SMA 20", "---", 1, 3, "#3498DB"),
                "ema_9": self.create_metric(card, "EMA 9", "---", 1, 4, "#E67E22"),
                "ema_50": self.create_metric(card, "EMA 50", "---", 1, 5, "#C0392B"),
                "upper_bb": self.create_metric(card, "B. Superior", "---", 2, 0, "#1ABC9C"),
                "lower_bb": self.create_metric(card, "B. Inferior", "---", 2, 1, "#1ABC9C"),
                "distancia": self.create_metric(card, "Esticamento", "---", 2, 2, "white"),
                "macro": self.create_metric(card, "Macro 1H", "---", 2, 3, "gray"),
                "book": self.create_metric(card, "Book", "---", 2, 4, "gray"),
                "mode": self.create_metric(card, "Modo", "---", 2, 5, "white"),
                "balance": self.create_metric(card, "Saldo/Posição", "---", 3, 0, "#F1C40F"),
                "alvos": self.create_metric(card, "Alvos", "---", 3, 1, "white"),
                "valor_usdt": self.create_metric(
                    card,
                    "Valor USDT",
                    f"${self.asset_states.get(symbol, {}).get('valor_usdt', DEFAULT_VALOR_USDT):.2f}",
                    3,
                    2,
                    "#F1C40F"
                ),
            }
            self.asset_widgets[symbol] = labels

            # A linha 3 tem menos elementos para preservar a largura do cartão.
            ctk.CTkLabel(card, text="", fg_color="transparent").grid(row=3, column=3, columnspan=3, sticky="ew")

        if hasattr(self, "telemetry_scroll"):
            self.rebuild_telemetry_cards()

    def create_metric(self, parent, title, val, r, c, color="white"):
        f = ctk.CTkFrame(parent, fg_color="#1F1F1F")
        f.grid(row=r, column=c, padx=4, pady=4, sticky="ew")
        ctk.CTkLabel(f, text=title, text_color="gray", font=("Roboto", 10)).pack(pady=(4, 0))
        lbl = ctk.CTkLabel(f, text=val, text_color=color, font=("Roboto", 13, "bold"))
        lbl.pack(pady=(0, 4))
        return lbl

    def create_telemetry_value(self, parent, title, val, r, c, color="white"):
        f = ctk.CTkFrame(parent, fg_color="#1F1F1F")
        f.grid(row=r, column=c, padx=3, pady=3, sticky="ew")
        ctk.CTkLabel(f, text=title, text_color="gray", font=("Roboto", 9)).pack(pady=(3, 0))
        lbl = ctk.CTkLabel(f, text=val, text_color=color, font=("Roboto", 11, "bold"))
        lbl.pack(pady=(0, 3))
        return lbl

    def create_detailed_dashboard(self):
        self.right_container.grid_columnconfigure(0, weight=1)
        self.lbl_detail_title = ctk.CTkLabel(
            self.right_container,
            text="TELEMETRIA AVANÇADA - TODOS OS ATIVOS EM ANÁLISE",
            font=("Roboto", 18, "bold"),
            text_color="#3498DB"
        )
        self.lbl_detail_title.pack(pady=(10, 2))
        self.lbl_telemetry_count = ctk.CTkLabel(
            self.right_container,
            text="Exibindo todos os ativos configurados no painel da esquerda",
            font=("Roboto", 11, "bold"),
            text_color="gray"
        )
        self.lbl_telemetry_count.pack(pady=(0, 6))

        self.telemetry_scroll = ctk.CTkScrollableFrame(
            self.right_container,
            label_text="DADOS DETALHADOS POR ATIVO",
            fg_color="#212121",
            height=520
        )
        self.telemetry_scroll.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        self.telemetry_scroll.grid_columnconfigure(0, weight=1)
        self.rebuild_telemetry_cards()

        self.frame_gif = ctk.CTkFrame(self.right_container, fg_color="black", border_width=1, border_color="#333333", height=250)
        self.frame_gif.pack(fill="x", expand=False, padx=10, pady=(0, 10))
        self.frame_gif.pack_propagate(False)
        self.lbl_gif = ctk.CTkLabel(self.frame_gif, text="Inicializando HUD...", text_color="#00FF00", font=("Consolas", 12))
        self.lbl_gif.pack(expand=True, fill="both")
        self.gif_frames = []
        self.gif_idx = 0
        threading.Thread(target=self.carregar_gif, daemon=True).start()

    def create_advanced_asset_card(self, parent, symbol, row):
        state = self.asset_states.get(symbol, {})
        card = ctk.CTkFrame(parent, fg_color="#2B2B2B", border_width=1, border_color="#3A3A3A")
        card.grid(row=row, column=0, sticky="ew", padx=4, pady=5)
        for col in range(3):
            card.grid_columnconfigure(col, weight=1)

        titulo = symbol
        if state.get("posicionado"):
            titulo += "  • POSICIONADO"
        elif state.get("remover_apos_venda"):
            titulo += "  • sai após venda"

        ctk.CTkLabel(card, text=titulo, font=("Roboto", 15, "bold"), text_color="#F1C40F").grid(row=0, column=0, padx=6, pady=(6, 2), sticky="w")
        status = ctk.CTkLabel(card, text=state.get("status", "STATUS: ---"), font=("Roboto", 11, "bold"), text_color="gray")
        status.grid(row=0, column=1, columnspan=2, padx=6, pady=(6, 2), sticky="e")

        widgets = {
            "card": card,
            "status": status,
            "preco": self.create_telemetry_value(card, "Preço", "---", 1, 0, "#FFFFFF"),
            "valor_usdt": self.create_telemetry_value(card, "Valor USDT", f"${float(state.get('valor_usdt', DEFAULT_VALOR_USDT)):.2f}", 1, 1, "#F1C40F"),
            "alvos": self.create_telemetry_value(card, "Alvos", "---", 1, 2, "#FFFFFF"),
            "adx": self.create_telemetry_value(card, "ADX", "---", 2, 0, "#95A5A6"),
            "di_plus": self.create_telemetry_value(card, "DI+", "---", 2, 1, "#2ECC71"),
            "di_minus": self.create_telemetry_value(card, "DI-", "---", 2, 2, "#E74C3C"),
            "dist_ema9": self.create_telemetry_value(card, "Dist. EMA 9", "---", 3, 0, "#FFFFFF"),
            "dist_ema50": self.create_telemetry_value(card, "Dist. EMA 50", "---", 3, 1, "#FFFFFF"),
            "dist_sma20": self.create_telemetry_value(card, "Dist. SMA 20", "---", 3, 2, "#3498DB"),
            "bb_width": self.create_telemetry_value(card, "Largura BB", "---", 4, 0, "#FFFFFF"),
            "bb_pos": self.create_telemetry_value(card, "Posição BB", "---", 4, 1, "#FFFFFF"),
            "candle_type": self.create_telemetry_value(card, "Candle", "---", 4, 2, "#FFFFFF"),
            "wicks": self.create_telemetry_value(card, "Pavios", "---", 5, 0, "#FFFFFF"),
            "book": self.create_telemetry_value(card, "Book", "---", 5, 1, "#FFFFFF"),
            "btc_rsi": self.create_telemetry_value(card, "BTC RSI", "---", 5, 2, "#FFFFFF"),
        }
        self.telemetry_widgets[symbol] = widgets

    def rebuild_telemetry_cards(self):
        if not hasattr(self, "telemetry_scroll"):
            return
        for widget in self.telemetry_scroll.winfo_children():
            widget.destroy()
        self.telemetry_widgets = {}

        for row, symbol in enumerate(self.ativos):
            self.create_advanced_asset_card(self.telemetry_scroll, symbol, row)

        def _update_count():
            if hasattr(self, "lbl_telemetry_count"):
                lista = ", ".join(self.ativos) if self.ativos else "nenhum ativo"
                self.lbl_telemetry_count.configure(text=f"Exibindo {len(self.ativos)} ativo(s): {lista}")
        self.safe_ui(_update_count)

        # Reaplica os últimos dados já calculados, para a tela não voltar para "---" após alterar ativos.
        for symbol, cache in list(self.telemetry_cache.items()):
            if symbol in self.telemetry_widgets:
                self.update_telemetry(symbol, **cache)

    def selecionar_ativo(self, symbol):
        # O botão do cartão esquerdo agora apenas destaca o cartão correspondente
        # na telemetria. A telemetria continua exibindo TODOS os ativos.
        self.selected_symbol = symbol

        def _focus():
            self.lbl_detail_title.configure(text="TELEMETRIA AVANÇADA - TODOS OS ATIVOS EM ANÁLISE")
            for s, widgets in self.telemetry_widgets.items():
                if "card" in widgets:
                    widgets["card"].configure(border_color="#3498DB" if s == symbol else "#3A3A3A")

        self.safe_ui(_focus)
        cache = self.telemetry_cache.get(symbol)
        if cache:
            self.update_telemetry(symbol, **cache)
        self.log(f"Ativo destacado na telemetria: {symbol}")

    def safe_ui(self, func):
        try:
            self.after(0, func)
        except RuntimeError:
            pass

    def log(self, msg, symbol=None):
        prefix = f"[{symbol}] " if symbol else ""
        linha = f"[{datetime.now().strftime('%H:%M:%S')}] {prefix}{msg}\n"
        def _write():
            self.textbox.insert("0.0", linha)
        self.safe_ui(_write)

    def set_status(self, symbol, text, color="gray"):
        state = self.asset_states.get(symbol)
        if state is not None:
            state["status"] = text

        def _update():
            widgets = self.asset_widgets.get(symbol)
            if widgets:
                widgets["status"].configure(text=text, text_color=color)
            ativos_posicionados = sum(1 for st in self.asset_states.values() if st.get("posicionado"))
            self.lbl_status_geral.configure(
                text=f"STATUS: {'🟢 Rodando' if self.executando else '💤 Aguardando'} | Ativos: {len(self.ativos)} | Posições: {ativos_posicionados}",
                text_color="#2ECC71" if self.executando else "gray"
            )
        self.safe_ui(_update)

    def update_card_metric(self, symbol, key, text, color=None):
        def _update():
            widgets = self.asset_widgets.get(symbol)
            if widgets and key in widgets:
                if color:
                    widgets[key].configure(text=text, text_color=color)
                else:
                    widgets[key].configure(text=text)
        self.safe_ui(_update)

    # ==========================================
    # --- TELEMETRIA DETALHADA ---
    # ==========================================
    def update_telemetry(self, symbol, current_price, df_last, book_ratio, rsi_btc):
        self.telemetry_cache[symbol] = {
            "current_price": current_price,
            "df_last": df_last,
            "book_ratio": book_ratio,
            "rsi_btc": rsi_btc,
        }

        def _update():
            widgets = self.telemetry_widgets.get(symbol)
            if not widgets:
                return

            # Mantém o título geral. O ativo selecionado só fica destacado pela borda do cartão.
            self.lbl_detail_title.configure(text="TELEMETRIA AVANÇADA - TODOS OS ATIVOS EM ANÁLISE")

            state = self.asset_states.get(symbol, {})
            widgets["status"].configure(text=state.get("status", "STATUS: ---"))
            widgets["preco"].configure(text=f"${current_price:.6f}")
            widgets["valor_usdt"].configure(text=f"${float(state.get('valor_usdt', DEFAULT_VALOR_USDT)):.2f}")

            if state.get("posicionado"):
                widgets["alvos"].configure(text=f"TP: {state.get('take_profit', 0):.4f} | SL: {state.get('stop_loss', 0):.4f}", text_color="#F1C40F")
            else:
                widgets["alvos"].configure(text="---", text_color="#FFFFFF")

            adx = float(df_last["adx"])
            plus = float(df_last["plus_di"])
            minus = float(df_last["minus_di"])
            cor_adx = "#2ECC71" if adx > 25 else "#95A5A6"

            widgets["adx"].configure(text=f"{adx:.1f}", text_color=cor_adx)
            widgets["di_plus"].configure(text=f"{plus:.1f}", text_color="#2ECC71", font=("Roboto", 11, "bold" if plus > minus else "normal"))
            widgets["di_minus"].configure(text=f"{minus:.1f}", text_color="#E74C3C", font=("Roboto", 11, "bold" if minus > plus else "normal"))

            d_ema9 = ((current_price - float(df_last["ema_9"])) / float(df_last["ema_9"])) * 100
            d_ema50 = ((current_price - float(df_last["ema_50"])) / float(df_last["ema_50"])) * 100
            d_sma20 = ((current_price - float(df_last["sma_20"])) / float(df_last["sma_20"])) * 100

            widgets["dist_ema9"].configure(text=f"{d_ema9:+.2f}%", text_color="#2ECC71" if d_ema9 > 0 else "#E74C3C")
            widgets["dist_ema50"].configure(text=f"{d_ema50:+.2f}%", text_color="#2ECC71" if d_ema50 > 0 else "#E74C3C")
            widgets["dist_sma20"].configure(text=f"{d_sma20:+.2f}%", text_color="#3498DB")

            bb_width = ((float(df_last["upper_bb"]) - float(df_last["lower_bb"])) / float(df_last["sma_20"])) * 100
            widgets["bb_width"].configure(text=f"{bb_width:.2f}%", text_color="#F1C40F" if bb_width > 1.5 else "white")

            pos_bb = "Dentro"
            cor_bb = "white"
            if current_price > float(df_last["upper_bb"]):
                pos_bb = "Rompeu TOPO"
                cor_bb = "#E74C3C"
            elif current_price < float(df_last["lower_bb"]):
                pos_bb = "Rompeu FUNDO"
                cor_bb = "#E74C3C"
            widgets["bb_pos"].configure(text=pos_bb, text_color=cor_bb)

            open_p = float(df_last["open"])
            close_p = float(df_last["close"])
            high_p = float(df_last["high"])
            low_p = float(df_last["low"])
            corpo = abs(close_p - open_p)
            pavio_sup = high_p - max(open_p, close_p)
            pavio_inf = min(open_p, close_p) - low_p

            tipo = "Neutro"
            cor_tipo = "gray"
            if close_p > open_p:
                tipo = "ALTA"
                cor_tipo = "#2ECC71"
            elif close_p < open_p:
                tipo = "BAIXA"
                cor_tipo = "#E74C3C"
            if pavio_inf > (corpo * 2):
                tipo += " / Martelo?"
            widgets["candle_type"].configure(text=tipo, text_color=cor_tipo)
            widgets["wicks"].configure(text=f"Sup {pavio_sup:.4f} | Inf {pavio_inf:.4f}")
            widgets["book"].configure(text=f"{book_ratio:.2f}x", text_color="#E74C3C" if book_ratio > BOOK_IMBALANCE_LIMIT else "#2ECC71")
            widgets["btc_rsi"].configure(text=f"{rsi_btc:.1f}", text_color="#E74C3C" if rsi_btc < 30 else "#2ECC71")

        self.safe_ui(_update)

    # ==========================================
    # --- GUARDIÕES E INDICADORES ---
    # ==========================================
    def checar_tendencia_macro(self, symbol):
        try:
            candles_1h = self.exchange.fetch_ohlcv(symbol, timeframe=TIMEFRAME_MACRO, limit=210)
            if not candles_1h:
                return True
            df_1h = pd.DataFrame(candles_1h, columns=["time", "open", "high", "low", "close", "vol"])
            ema_200_1h = df_1h["close"].ewm(span=200, adjust=False).mean().iloc[-1]
            preco_atual = float(df_1h["close"].iloc[-1])
            is_safe = preco_atual > ema_200_1h
            cor = "#2ECC71" if is_safe else "#E74C3C"
            txt = "ALTA (Safe)" if is_safe else "BAIXA (Repique)"
            self.update_card_metric(symbol, "macro", txt, cor)
            return is_safe
        except Exception as e:
            self.log(f"Erro macro: {e}", symbol)
            return True

    def checar_confirmacao_15m(self, symbol):
        try:
            candles_15m = self.exchange.fetch_ohlcv(symbol, timeframe="15m", limit=5)
            if not candles_15m:
                return False

            tempo_agora_ms = self.exchange.milliseconds()
            intervalo_ms = 900000
            inicio_vela_atual_ms = (tempo_agora_ms // intervalo_ms) * intervalo_ms
            inicio_vela_fechada_alvo = inicio_vela_atual_ms - intervalo_ms

            vela_alvo = None
            for candle in reversed(candles_15m):
                if int(candle[0]) == int(inicio_vela_fechada_alvo):
                    vela_alvo = candle
                    break

            if vela_alvo is None:
                return False

            open_p = float(vela_alvo[1])
            close_p = float(vela_alvo[4])
            is_green = close_p > open_p

            high_p = float(vela_alvo[2])
            low_p = float(vela_alvo[3])
            tamanho_total = high_p - low_p
            if tamanho_total > 0:
                tamanho_corpo = abs(close_p - open_p)
                if (tamanho_corpo / tamanho_total) < 0.2:
                    return False

            return is_green
        except Exception as e:
            self.log(f"⚠️ Erro 15m: {e}", symbol)
            return False

    def checar_livro_ordens(self, symbol, current_price):
        try:
            book = self.exchange.fetch_order_book(symbol, limit=100)
            bids = book["bids"]
            asks = book["asks"]
            min_p = current_price * (1 - BOOK_DEPTH_PCT)
            max_p = current_price * (1 + BOOK_DEPTH_PCT)
            vol_compra = sum([a for p, a in bids if p >= min_p])
            vol_venda = sum([a for p, a in asks if p <= max_p])
            if vol_compra == 0:
                return False
            ratio = vol_venda / vol_compra
            is_safe = ratio < BOOK_IMBALANCE_LIMIT
            cor = "#2ECC71" if is_safe else "#E74C3C"
            self.update_card_metric(symbol, "book", f"Ratio: {ratio:.2f}x", cor)
            return is_safe
        except Exception:
            return True

    def checar_tendencia_bitcoin(self):
        try:
            btc_candles = self.exchange.fetch_ohlcv("BTC/USDT", timeframe=TIMEFRAME, limit=30)
            if not btc_candles:
                return False, False, 50
            df_btc = pd.DataFrame(btc_candles, columns=["time", "open", "high", "low", "close", "vol"])
            ema_20_btc = df_btc["close"].ewm(span=20, adjust=False).mean().iloc[-1]
            preco_btc = float(df_btc["close"].iloc[-1])
            delta = df_btc["close"].diff()
            gain = (delta.where(delta > 0, 0)).rolling(window=14).mean()
            loss = (-delta.where(delta < 0, 0)).rolling(window=14).mean()
            rs = gain / loss
            rsi_btc = float((100 - (100 / (1 + rs))).iloc[-1])
            is_healthy = preco_btc > ema_20_btc
            distancia_btc = (preco_btc - ema_20_btc) / ema_20_btc
            is_euphoria = is_healthy and (rsi_btc > 65 or distancia_btc > 0.01)
            return is_healthy, is_euphoria, rsi_btc
        except Exception:
            return False, False, 50

    def calcular_indicadores(self, df):
        delta = df["close"].diff()
        gain = (delta.where(delta > 0, 0)).rolling(window=14).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(window=14).mean()
        rs = gain / loss
        df["rsi"] = 100 - (100 / (1 + rs))
        df["sma_20"] = df["close"].rolling(window=20).mean()
        df["std_20"] = df["close"].rolling(window=20).std()
        df["lower_bb"] = df["sma_20"] - (df["std_20"] * 2)
        df["upper_bb"] = df["sma_20"] + (df["std_20"] * 2)
        df["ema_9"] = df["close"].ewm(span=9, adjust=False).mean()
        df["ema_50"] = df["close"].ewm(span=50, adjust=False).mean()
        df["tr0"] = abs(df["high"] - df["low"])
        df["tr1"] = abs(df["high"] - df["close"].shift())
        df["tr2"] = abs(df["low"] - df["close"].shift())
        df["tr"] = df[["tr0", "tr1", "tr2"]].max(axis=1)
        df["up_move"] = df["high"] - df["high"].shift()
        df["down_move"] = df["low"].shift() - df["low"]
        df["plus_dm"] = np.where((df["up_move"] > df["down_move"]) & (df["up_move"] > 0), df["up_move"], 0)
        df["minus_dm"] = np.where((df["down_move"] > df["up_move"]) & (df["down_move"] > 0), df["down_move"], 0)
        df["tr_s"] = df["tr"].ewm(alpha=1 / 14, adjust=False).mean()
        df["plus_dm_s"] = df["plus_dm"].ewm(alpha=1 / 14, adjust=False).mean()
        df["minus_dm_s"] = df["minus_dm"].ewm(alpha=1 / 14, adjust=False).mean()
        df["plus_di"] = 100 * (df["plus_dm_s"] / df["tr_s"])
        df["minus_di"] = 100 * (df["minus_dm_s"] / df["tr_s"])
        df["dx"] = 100 * abs(df["plus_di"] - df["minus_di"]) / (df["plus_di"] + df["minus_di"])
        df["adx"] = df["dx"].ewm(alpha=1 / 14, adjust=False).mean()
        return df

    # ==========================================
    # --- LOOP PRINCIPAL MULTIATIVOS ---
    # ==========================================
    def run_strategy(self):
        self.log(f"Iniciando Full Monitor Multiativos: {', '.join(self.ativos)}")

        while self.executando:
            try:
                with self.config_lock:
                    symbols_snapshot = list(self.ativos)
                for symbol in symbols_snapshot:
                    if not self.executando:
                        break
                    with self.config_lock:
                        if symbol not in self.ativos or symbol not in self.asset_states:
                            continue
                    self.processar_ativo(symbol)
                    time.sleep(0.6)  # Pequena pausa para respeitar rate limit entre ativos.
                time.sleep(4)
            except Exception as e:
                self.log(f"Erro Loop Geral: {e}")
                time.sleep(5)

    def processar_ativo(self, symbol):
        with self.config_lock:
            state = self.asset_states.get(symbol)
            if state is None or symbol not in self.ativos:
                return
            if state.get("remover_apos_venda") and not state.get("posicionado"):
                return

        # 1. Checagem Macro por ativo.
        macro_alta = self.checar_tendencia_macro(symbol)

        # 1.1 Se já existe um sinal armado, aguarda o recuo antes de comprar.
        # Isso evita que novas leituras sobrescrevam o preço do sinal.
        if state.get("entrada_recuo_pendente") and not state.get("posicionado"):
            try:
                ticker = self.exchange.fetch_ticker(symbol)
                current_price = float(ticker["last"])
                self.update_card_metric(symbol, "price", f"${current_price:.6f}")
                self.monitorar_entrada_com_recuo(symbol, current_price)
            except Exception as e:
                self.log(f"⚠️ Erro ao monitorar recuo de entrada: {e}", symbol)
            return

        # 2. Se este ativo já estiver posicionado, ele apenas monitora saída.
        if state["posicionado"]:
            self.update_card_metric(symbol, "alvos", f"TP: {state['take_profit']:.4f} | SL: {state['stop_loss']:.4f}")
            ticker = self.exchange.fetch_ticker(symbol)
            current_price = float(ticker["last"])
            rsi_now = self.calcular_rsi_rapido(symbol)

            # Mesmo posicionado, atualiza a telemetria avançada completa do ativo.
            # Assim todos os ativos continuam aparecendo no painel direito enquanto aguardam venda.
            try:
                candles_check = self.exchange.fetch_ohlcv(symbol, timeframe=TIMEFRAME, limit=100)
                if candles_check:
                    df_check = pd.DataFrame(candles_check, columns=["time", "open", "high", "low", "close", "vol"])
                    df_check = self.calcular_indicadores(df_check).dropna().reset_index(drop=True)
                    if len(df_check) > 0:
                        candle_current = df_check.iloc[-1]
                        rsi_now = float(candle_current["rsi"])
                        sma_20_curr = float(candle_current["sma_20"])
                        upper_bb_curr = float(candle_current["upper_bb"])
                        lower_bb_curr = float(candle_current["lower_bb"])
                        adx_curr = float(candle_current["adx"])
                        ema_9_curr = float(candle_current["ema_9"])
                        ema_50_curr = float(candle_current["ema_50"])
                        plus_di = float(candle_current["plus_di"])
                        minus_di = float(candle_current["minus_di"])

                        self.atualizar_card_basico(
                            symbol=symbol,
                            current_price=current_price,
                            rsi_curr=rsi_now,
                            adx_curr=adx_curr,
                            plus_di=plus_di,
                            minus_di=minus_di,
                            sma_20=sma_20_curr,
                            ema_9=ema_9_curr,
                            ema_50=ema_50_curr,
                            upper_bb=upper_bb_curr,
                            lower_bb=lower_bb_curr,
                        )
                        distancia_pct = (current_price - sma_20_curr) / sma_20_curr
                        cor_dist = "#E74C3C" if abs(distancia_pct) > DISTANCIA_PADRAO else "#2ECC71"
                        self.update_card_metric(symbol, "distancia", f"{distancia_pct * 100:.2f}%", cor_dist)
                        book_ratio_val, _ = self.calcular_book_resumido(symbol)
                        _, _, rsi_btc_val = self.checar_tendencia_bitcoin()
                        self.update_telemetry(symbol, current_price, candle_current, book_ratio_val, rsi_btc_val)
                    else:
                        self.update_card_metric(symbol, "price", f"${current_price:.6f}")
                        self.update_card_metric(symbol, "rsi", f"{rsi_now:.1f}")
                else:
                    self.update_card_metric(symbol, "price", f"${current_price:.6f}")
                    self.update_card_metric(symbol, "rsi", f"{rsi_now:.1f}")
            except Exception as e:
                self.log(f"Erro telemetria posicionado: {e}", symbol)
                self.update_card_metric(symbol, "price", f"${current_price:.6f}")
                self.update_card_metric(symbol, "rsi", f"{rsi_now:.1f}")

            self.monitorar_saida(symbol, current_price, rsi_now)
            return

        # 3. Se este ativo não estiver posicionado, busca entrada normalmente.
        candles = self.exchange.fetch_ohlcv(symbol, timeframe=TIMEFRAME, limit=100)
        if not candles:
            time.sleep(2)
            return

        df = pd.DataFrame(candles, columns=["time", "open", "high", "low", "close", "vol"])
        df = self.calcular_indicadores(df)
        df = df.dropna().reset_index(drop=True)
        if len(df) < 3:
            self.set_status(symbol, "STATUS: Dados insuficientes", "gray")
            return

        candle_closed = df.iloc[-2]
        candle_current = df.iloc[-1]

        current_price = float(candle_current["close"])
        sma_20_curr = float(candle_current["sma_20"])
        upper_bb_curr = float(candle_current["upper_bb"])
        lower_bb_curr = float(candle_current["lower_bb"])
        rsi_curr = float(candle_current["rsi"])
        adx_curr = float(candle_current["adx"])
        ema_9_curr = float(candle_current["ema_9"])
        ema_50_curr = float(candle_current["ema_50"])
        plus_di = float(candle_current["plus_di"])
        minus_di = float(candle_current["minus_di"])

        self.atualizar_card_basico(
            symbol=symbol,
            current_price=current_price,
            rsi_curr=rsi_curr,
            adx_curr=adx_curr,
            plus_di=plus_di,
            minus_di=minus_di,
            sma_20=sma_20_curr,
            ema_9=ema_9_curr,
            ema_50=ema_50_curr,
            upper_bb=upper_bb_curr,
            lower_bb=lower_bb_curr,
        )

        distancia_pct = (current_price - sma_20_curr) / sma_20_curr
        cor_dist = "#E74C3C" if abs(distancia_pct) > DISTANCIA_PADRAO else "#2ECC71"
        self.update_card_metric(symbol, "distancia", f"{distancia_pct * 100:.2f}%", cor_dist)

        book_ratio_val, book_ok = self.calcular_book_resumido(symbol)
        btc_ok, btc_euforia, rsi_btc_val = self.checar_tendencia_bitcoin()
        self.update_telemetry(symbol, current_price, candle_current, book_ratio_val, rsi_btc_val)

        if rsi_btc_val < 20:
            state["aguardando_confirmacao"] = False
            self.set_status(symbol, "STATUS: ⛔ BTC CRASH", "#E74C3C")
            return

        if plus_di > minus_di:
            state["modo_tendencia_ativo"] = True
            self.update_card_metric(symbol, "mode", "Tendência", "#2ECC71")
            self.logica_tendencia(
                symbol,
                current_price,
                ema_9_curr,
                rsi_curr,
                candle_closed,
                sma_20_curr,
                distancia_pct,
                macro_alta,
                book_ok,
                btc_ok,
                btc_euforia,
                adx_curr,
                ema_50_curr,
            )
        else:
            state["modo_tendencia_ativo"] = False
            self.update_card_metric(symbol, "mode", "Lateral", "#3498DB")
            self.logica_lateral(symbol, current_price, lower_bb_curr, rsi_curr, candle_closed, book_ok, btc_ok, rsi_btc_val)

        if not state["posicionado"]:
            self.update_card_metric(symbol, "alvos", "---")

    def atualizar_card_basico(self, symbol, current_price, rsi_curr, adx_curr, plus_di, minus_di, sma_20, ema_9, ema_50, upper_bb, lower_bb):
        self.update_card_metric(symbol, "price", f"${current_price:.6f}")
        cor_rsi = "#E74C3C" if rsi_curr > 70 else ("#2ECC71" if rsi_curr < 30 else "#FFFFFF")
        self.update_card_metric(symbol, "rsi", f"{rsi_curr:.1f}", cor_rsi)
        trend_icon = "🐂" if plus_di > minus_di else "🐻"
        self.update_card_metric(symbol, "adx", f"{adx_curr:.1f} {trend_icon}")
        self.update_card_metric(symbol, "sma_20", f"${sma_20:.6f}")
        self.update_card_metric(symbol, "ema_9", f"${ema_9:.6f}")
        self.update_card_metric(symbol, "ema_50", f"${ema_50:.6f}")
        self.update_card_metric(symbol, "upper_bb", f"${upper_bb:.6f}")
        self.update_card_metric(symbol, "lower_bb", f"${lower_bb:.6f}")

    def calcular_book_resumido(self, symbol):
        book_ratio_val = 0.0
        book_ok = True
        try:
            book = self.exchange.fetch_order_book(symbol, limit=20)
            bids = sum([x[1] for x in book["bids"]])
            asks = sum([x[1] for x in book["asks"]])
            if bids > 0:
                book_ratio_val = asks / bids
                cor_book = "#2ECC71" if book_ratio_val < 0.6 else ("#E74C3C" if book_ratio_val > 1.5 else "gray")
                self.update_card_metric(symbol, "book", f"Ratio: {book_ratio_val:.2f}x", cor_book)
                book_ok = book_ratio_val < BOOK_IMBALANCE_LIMIT
            else:
                self.update_card_metric(symbol, "book", "S/ Liquidez")
                book_ok = False
        except Exception:
            pass
        return book_ratio_val, book_ok

    def calcular_rsi_rapido(self, symbol):
        try:
            candles_check = self.exchange.fetch_ohlcv(symbol, timeframe=TIMEFRAME, limit=30)
            df_check = pd.DataFrame(candles_check, columns=["time", "open", "high", "low", "close", "vol"])
            delta = df_check["close"].diff()
            gain = (delta.where(delta > 0, 0)).rolling(window=14).mean()
            loss = (-delta.where(delta < 0, 0)).rolling(window=14).mean()
            rs = gain / loss
            return float((100 - (100 / (1 + rs))).iloc[-1])
        except Exception:
            return 50.0

    # ==========================================
    # --- LÓGICAS DE ENTRADA ---
    # ==========================================
    def logica_lateral(self, symbol, current_price, lower_bb, rsi, candle_closed, book_ok, btc_ok, rsi_btc):
        state = self.asset_states[symbol]

        if float(candle_closed["adx"]) > 35:
            state["aguardando_confirmacao"] = False
            self.set_status(symbol, "STATUS: ⚠️ Tendência de Baixa Forte", "#E74C3C")
            return

        distancia_media = (float(candle_closed["sma_20"]) - current_price) / current_price
        if distancia_media < (TARGET_NORMAL * 1.1):
            state["aguardando_confirmacao"] = False
            self.set_status(symbol, "STATUS: 🤏 Bandas Estreitas", "gray")
            return

        closed_time = int(candle_closed["time"])

        if not state["aguardando_confirmacao"]:
            if (current_price <= lower_bb) and rsi < 30:
                state["aguardando_confirmacao"] = True
                self.log("👀 [REBOUND] Fora da banda. Monitorando...", symbol)
                self.set_status(symbol, "STATUS: 🔫 MIRANDO REPIQUE...", "#F39C12")
            return

        if closed_time != state["last_candle_time"]:
            state["last_candle_time"] = closed_time
            is_green_5m = float(candle_closed["close"]) > float(candle_closed["open"])
            is_green_15m = self.checar_confirmacao_15m(symbol)

            body_bottom = min(float(candle_closed["open"]), float(candle_closed["close"]))
            pavio_inf = body_bottom - float(candle_closed["low"])
            corpo = abs(float(candle_closed["close"]) - float(candle_closed["open"]))
            is_hammer_5m = pavio_inf > (corpo * 1.5)

            pode_comprar = False
            motivo = ""

            if is_green_5m and is_green_15m and float(candle_closed["rsi"]) < 35:
                pode_comprar = True
                motivo = "Reversão 5m+15m"
            elif is_hammer_5m and is_green_15m and float(candle_closed["rsi"]) < 30:
                pode_comprar = True
                motivo = "Martelo 5m + 15m Verde"
            elif float(candle_closed["rsi"]) < 20:
                pode_comprar = True
                motivo = "RSI Extremo (<20)"

            if pode_comprar:
                if not is_green_15m and float(candle_closed["rsi"]) > 25:
                    self.log("⏳ [LATERAL] Abortado: 15m ainda é Vermelho.", symbol)
                    return
                if not btc_ok and float(candle_closed["rsi"]) > 25:
                    self.log("⚠️ [REBOUND] Abortado: BTC caindo.", symbol)
                    state["aguardando_confirmacao"] = False
                    return
                if not book_ok:
                    self.log("🧱 [REBOUND] Abortado: Book desbalanceado.", symbol)
                    state["aguardando_confirmacao"] = False
                    return

                self.log(f"🟢 [REBOUND] Entrada confirmada ({motivo}). Armando compra com recuo...", symbol)
                state["alvo_atual"] = TARGET_REPIQUE
                self.armar_entrada_com_recuo(symbol, current_price, motivo=f"REBOUND - {motivo}")
                state["aguardando_confirmacao"] = False
            else:
                if is_green_5m and not is_green_15m:
                    self.log("⏳ [REBOUND] 5m reverteu, mas 15m ainda não. Aguardando...", symbol)
                else:
                    self.log("⏳ [REBOUND] Cancelado (Sem confirmação).", symbol)
                    state["aguardando_confirmacao"] = False

    def logica_tendencia(self, symbol, current_price, ema_9, rsi, candle_closed, sma_20, distancia_pct, macro_alta, book_ok, btc_ok, btc_euforia, adx_curr, ema_50):
        state = self.asset_states[symbol]

        if current_price < ema_50:
            state["aguardando_confirmacao"] = False
            self.set_status(symbol, "STATUS: 🛑 Abaixo EMA 50", "#E74C3C")
            return

        adx_exigido = ADX_PADRAO if macro_alta else ADX_FORTE
        if adx_curr < adx_exigido:
            state["aguardando_confirmacao"] = False
            self.set_status(symbol, f"STATUS: ⚠️ ADX Fraco (<{adx_exigido})", "#E74C3C")
            return

        is_green_15m = self.checar_confirmacao_15m(symbol)
        if not is_green_15m:
            state["aguardando_confirmacao"] = False
            self.set_status(symbol, "STATUS: ⏳ Aguardando 15m Verde...", "#E67E22")
            return

        distancia_do_alvo = (current_price - ema_9) / ema_9
        esta_no_ponto = 0.0 <= distancia_do_alvo <= 0.0003

        if esta_no_ponto:
            if not book_ok:
                self.set_status(symbol, "STATUS: 🧱 Book Ruim", "gray")
                return

            self.log("🚀 [SNIPER] 15m Confirmado + Preço na Média! Armando compra com recuo...", symbol)
            state["alvo_atual"] = TARGET_NORMAL if macro_alta else TARGET_REPIQUE
            self.armar_entrada_com_recuo(symbol, current_price, motivo="SNIPER - 15m + EMA 9")
            state["aguardando_confirmacao"] = False
            return

        if current_price > (ema_9 * 1.0025):
            state["aguardando_confirmacao"] = True
            self.set_status(symbol, f"STATUS: 🔭 Esperando EMA 9 ({distancia_do_alvo * 100:.2f}%)", "#F1C40F")
        elif current_price < ema_9:
            self.set_status(symbol, "STATUS: 📉 Abaixo EMA 9. Aguardando rompimento...", "#E67E22")

    # ==========================================
    # --- EXECUÇÃO E ORDENS ---
    # ==========================================
    def limpar_entrada_com_recuo(self, symbol):
        state = self.asset_states.get(symbol)
        if not state:
            return
        state["entrada_recuo_pendente"] = False
        state["preco_sinal_entrada"] = 0.0
        state["preco_recuo_min"] = 0.0
        state["preco_recuo_max"] = 0.0
        state["entrada_recuo_inicio"] = 0.0
        state["entrada_recuo_motivo"] = ""
        state["entrada_recuo_status"] = ""

    def cancelar_entrada_com_recuo(self, symbol, motivo):
        self.limpar_entrada_com_recuo(symbol)
        self.set_status(symbol, f"STATUS: 🚫 Recuo cancelado ({motivo})", "#E74C3C")
        self.log(f"🚫 Entrada com recuo cancelada: {motivo}", symbol)

    def armar_entrada_com_recuo(self, symbol, preco_sinal, motivo=""):
        """Arma a compra para acontecer somente após recuo de 0.18% a 0.50%.

        Exemplo:
        - Sinal em 1.0000
        - Compra liberada entre 0.9982 e 0.9950
        """
        if not self.ativo_liberado_para_nova_compra(symbol):
            self.log("Entrada com recuo bloqueada: ativo removido/desativado.", symbol)
            return

        state = self.asset_states[symbol]
        if state.get("posicionado"):
            return

        preco_sinal = float(preco_sinal)
        preco_recuo_max = preco_sinal * (1 - RECUO_ENTRADA_MIN)  # recuo mínimo: preço mais alto da faixa
        preco_recuo_min = preco_sinal * (1 - RECUO_ENTRADA_MAX)  # recuo máximo: preço mais baixo da faixa

        state["entrada_recuo_pendente"] = True
        state["preco_sinal_entrada"] = preco_sinal
        state["preco_recuo_min"] = preco_recuo_min
        state["preco_recuo_max"] = preco_recuo_max
        state["entrada_recuo_inicio"] = time.time()
        state["entrada_recuo_motivo"] = motivo
        state["entrada_recuo_status"] = "armado"

        self.log(
            f"🎯 Sinal confirmado ({motivo}). Aguardando recuo de "
            f"{RECUO_ENTRADA_MIN * 100:.2f}% a {RECUO_ENTRADA_MAX * 100:.2f}%: "
            f"comprar entre {preco_recuo_max:.6f} e {preco_recuo_min:.6f}.",
            symbol
        )
        self.set_status(symbol, "STATUS: 🎯 Aguardando recuo para compra", "#F1C40F")
        self.update_card_metric(symbol, "alvos", f"Entrada: {preco_recuo_max:.4f}~{preco_recuo_min:.4f}")

    def monitorar_entrada_com_recuo(self, symbol, current_price):
        """Monitora um sinal armado e compra apenas quando o preço entra na faixa."""
        state = self.asset_states.get(symbol)
        if not state or not state.get("entrada_recuo_pendente"):
            return False

        if not self.ativo_liberado_para_nova_compra(symbol):
            self.cancelar_entrada_com_recuo(symbol, "ativo indisponível para nova compra")
            return True

        preco_sinal = float(state.get("preco_sinal_entrada", 0.0))
        preco_recuo_min = float(state.get("preco_recuo_min", 0.0))
        preco_recuo_max = float(state.get("preco_recuo_max", 0.0))

        if preco_sinal <= 0 or preco_recuo_min <= 0 or preco_recuo_max <= 0:
            self.cancelar_entrada_com_recuo(symbol, "preço de sinal inválido")
            return True

        if RECUO_ENTRADA_EXPIRA_SEG > 0:
            inicio = float(state.get("entrada_recuo_inicio", 0.0))
            if inicio > 0 and (time.time() - inicio) > RECUO_ENTRADA_EXPIRA_SEG:
                self.cancelar_entrada_com_recuo(symbol, "tempo expirado")
                return True

        current_price = float(current_price)
        recuo_pct = (preco_sinal - current_price) / preco_sinal

        # Faixa correta: caiu pelo menos 0.18%, mas não mais que 0.50%.
        if preco_recuo_min <= current_price <= preco_recuo_max:
            self.log(
                f"✅ Recuo atingido ({recuo_pct * 100:.3f}%). Comprando @ {current_price:.6f}",
                symbol
            )
            self.limpar_entrada_com_recuo(symbol)
            self.executar_entrada(symbol, current_price)
            return True

        # Evita spam no log: só registra quando muda de zona.
        if current_price > preco_recuo_max:
            status = "aguardando_recuo"
            self.set_status(symbol, f"STATUS: ⏳ Recuo atual {recuo_pct * 100:.3f}%", "#F1C40F")
        else:
            status = "recuo_profundo"
            self.set_status(symbol, f"STATUS: ⚠️ Recuo passou de {RECUO_ENTRADA_MAX * 100:.2f}%", "#E67E22")

        if state.get("entrada_recuo_status") != status:
            state["entrada_recuo_status"] = status
            if status == "aguardando_recuo":
                self.log(
                    f"⏳ Aguardando preço entrar na faixa: atual {current_price:.6f} | "
                    f"faixa {preco_recuo_max:.6f} até {preco_recuo_min:.6f}",
                    symbol
                )
            else:
                self.log(
                    f"⚠️ Preço caiu além da faixa de entrada: atual {current_price:.6f}. "
                    f"Não compra; aguarda voltar para a faixa.",
                    symbol
                )

        return True

    def ativo_liberado_para_nova_compra(self, symbol):
        with self.config_lock:
            state = self.asset_states.get(symbol)
            if state is None:
                return False
            if symbol not in self.ativos:
                return False
            if state.get("remover_apos_venda"):
                return False
            if not state.get("ativo_ativo", True):
                return False
            return True

    def executar_entrada(self, symbol, price):
        if not self.ativo_liberado_para_nova_compra(symbol):
            self.log("Entrada bloqueada: ativo removido/desativado para novas compras.", symbol)
            return
        state = self.asset_states[symbol]
        state["preco_compra"] = price
        state["take_profit"] = price * (1 + state["alvo_atual"])
        state["stop_loss"] = price * (1 - STOP_LOSS_FIXO)
        state["breakeven_ativado"] = False

        if self.modo_teste_var.get():
            valor_configurado = math.floor(float(state.get("valor_usdt", DEFAULT_VALOR_USDT)) * 100) / 100.0
            saldo_disponivel = math.floor(float(state.get("saldo_usdt", 0.0)) * 100) / 100.0
            investimento = min(valor_configurado, saldo_disponivel)
            if investimento <= 0:
                self.log("❌ Saldo simulado insuficiente.", symbol)
                return
            state["posicionado"] = True
            state["saldo_crypto"] = investimento / price
            state["saldo_usdt"] = round(saldo_disponivel - investimento, 8)
            self.log(f"🔵 COMPRA SIM: ${investimento:.2f} @ {price:.5f}", symbol)
            self.update_card_metric(symbol, "balance", f"Qtd: {state['saldo_crypto']:.6f}")
            self.update_card_metric(symbol, "valor_usdt", f"${state['valor_usdt']:.2f}")
            self.update_card_metric(symbol, "alvos", f"TP: {state['take_profit']:.4f} | SL: {state['stop_loss']:.4f}")
            self.set_status(symbol, "STATUS: 🟢 POSICIONADO", "#2ECC71")
            self.salvar_estado_trades()
            return

        try:
            if not API_KEY or not SECRET_KEY:
                self.log("❌ Configure BINANCE_API_KEY e BINANCE_SECRET_KEY para operar em modo real.", symbol)
                return

            self.exchange.load_time_difference()
            bal = self.exchange.fetch_balance()
            usdt_free = float(bal.get("USDT", {}).get("free", 0.0))
            investimento_usdt = math.floor(float(state.get("valor_usdt", DEFAULT_VALOR_USDT)) * 100) / 100.0
            saldo_operavel = math.floor((usdt_free * RESERVA_CAPITAL_REAL) * 100) / 100.0

            if investimento_usdt < VALOR_MINIMO_ORDEM_USDT:
                self.log(f"❌ Valor configurado abaixo do mínimo (< ${VALOR_MINIMO_ORDEM_USDT:.0f}): ${investimento_usdt:.2f}", symbol)
                return
            if investimento_usdt > saldo_operavel:
                self.log(f"❌ Saldo USDT insuficiente. Configurado: ${investimento_usdt:.2f} | Livre c/ reserva: ${saldo_operavel:.2f}", symbol)
                return

            self.log(f"Enviando Ordem a Mercado: ${investimento_usdt:.2f}...", symbol)
            params_buy = {"quoteOrderQty": investimento_usdt}
            order_buy = self.exchange.create_market_buy_order(symbol, None, params=params_buy)

            real_buy_price = float(order_buy.get("average", price) or price)
            if real_buy_price == 0:
                real_buy_price = float(order_buy["cost"]) / float(order_buy["filled"])

            amount_filled = float(order_buy["filled"])
            state["preco_compra"] = real_buy_price
            state["take_profit"] = real_buy_price * (1 + state["alvo_atual"])
            state["stop_loss"] = real_buy_price * (1 - STOP_LOSS_FIXO)
            state["saldo_crypto"] = amount_filled

            self.log(f"🔵 COMPRA REAL: {amount_filled} @ {real_buy_price:.5f}", symbol)
            self.tocar_som("COMPRA")
            self.enviar_ordem_oco(symbol, state["take_profit"], state["stop_loss"])

            state["posicionado"] = True
            self.update_card_metric(symbol, "balance", "POSICIONADO (OCO)")
            self.update_card_metric(symbol, "alvos", f"TP: {state['take_profit']:.4f} | SL: {state['stop_loss']:.4f}")
            self.set_status(symbol, "STATUS: 🟢 POSICIONADO", "#2ECC71")
            self.salvar_estado_trades()
        except Exception as e:
            self.log(f"❌ Erro Entrada/OCO: {e}", symbol)
            state["posicionado"] = False

    def enviar_ordem_oco(self, symbol, tp_price, sl_price):
        try:
            self.log("🛡️ Enviando Ordem OCO...", symbol)
            symbol_clean = symbol.replace("/", "")
            currency = symbol.split("/")[0]
            bal = self.exchange.fetch_balance()
            amount_real = float(bal.get(currency, {}).get("free", 0.0))
            amount_str = self.exchange.amount_to_precision(symbol, amount_real)

            if float(amount_str) == 0:
                self.log("❌ Erro OCO: Saldo zerado ou poeira.", symbol)
                return

            price_str = self.exchange.price_to_precision(symbol, tp_price)
            stop_price_str = self.exchange.price_to_precision(symbol, sl_price)
            stop_limit_price = sl_price * 0.998
            stop_limit_str = self.exchange.price_to_precision(symbol, stop_limit_price)

            params_oco = {
                "symbol": symbol_clean,
                "side": "SELL",
                "quantity": amount_str,
                "price": price_str,
                "stopPrice": stop_price_str,
                "stopLimitPrice": stop_limit_str,
                "stopLimitTimeInForce": "GTC"
            }

            oco_res = self.exchange.private_post_order_oco(params_oco)
            self.log(f"✅ OCO REGISTRADA! ID: {oco_res.get('orderListId')}", symbol)
            self.update_card_metric(symbol, "alvos", f"TP: {tp_price:.4f} | SL: {sl_price:.4f}")
        except Exception as e:
            self.log(f"❌ Erro ao enviar OCO: {e}", symbol)

    # ==========================================
    # --- MONITORAMENTO DE SAÍDA ---
    # ==========================================
    def monitorar_saida(self, symbol, current_price, rsi_curr):
        state = self.asset_states[symbol]
        if state["preco_compra"] <= 0:
            return

        lucro_atual_pct = (current_price - state["preco_compra"]) / state["preco_compra"]
        if lucro_atual_pct < PERDA_MAX_EMERGENCIA and rsi_curr < RSI_EMERGENCIA:
            self.log(f"🆘 ALERTA DE PÂNICO: Queda {lucro_atual_pct * 100:.2f}% s/ repique (RSI {rsi_curr:.1f})", symbol)
            self.fechar_posicao_segura(symbol, current_price, "EMERGÊNCIA 🆘")
            return

        if not state["breakeven_ativado"]:
            gatilho_be = state["preco_compra"] * (1 + GATILHO_BREAKEVEN)
            if current_price >= gatilho_be:
                state["breakeven_ativado"] = True
                if not self.modo_teste_var.get():
                    self.mover_stop_binance_breakeven(symbol)
                else:
                    state["stop_loss"] = state["preco_compra"] * 1.002
                    self.log("🛡️ (Simulado) Stop movido para 0x0.", symbol)
                    self.set_status(symbol, "STATUS: 🛡️ STOP NO ZERO", "#F1C40F")
                    self.update_card_metric(symbol, "alvos", f"TP: {state['take_profit']:.4f} | SL: {state['stop_loss']:.4f}")
                    self.salvar_estado_trades()

        if current_price >= state["take_profit"]:
            self.fechar_posicao_segura(symbol, current_price, "LUCRO 🎯")
        elif current_price <= state["stop_loss"]:
            self.fechar_posicao_segura(symbol, current_price, "STOP LOSS 🛑")
        else:
            self.set_status(symbol, "STATUS: 👀 Aguardando venda", "#F1C40F")

    def mover_stop_binance_breakeven(self, symbol):
        state = self.asset_states[symbol]
        try:
            self.log("🛡️ Movendo Stop Loss para 0x0 na Binance...", symbol)
            try:
                self.exchange.cancel_all_orders(symbol)
            except Exception as e:
                if "-2011" in str(e) or "Unknown order" in str(e):
                    self.log("⚠️ Ordem antiga já executada ou inexistente. Verificando saldo...", symbol)
                else:
                    self.log(f"⚠️ Erro ao cancelar (Ignorável): {e}", symbol)

            time.sleep(1.5)
            currency = symbol.split("/")[0]
            bal = self.exchange.fetch_balance()
            amount_free = float(bal.get(currency, {}).get("free", 0.0))

            if amount_free < (state["saldo_crypto"] * 0.1):
                self.log("ℹ️ Trade já encerrado (TP atingido?). Cancelando Breakeven.", symbol)
                state["breakeven_ativado"] = True
                return

            novo_stop = state["preco_compra"] * 1.002
            state["stop_loss"] = novo_stop
            self.enviar_ordem_oco(symbol, state["take_profit"], novo_stop)
            state["breakeven_ativado"] = True
            self.log("🛡️ Stop Loss movido com sucesso!", symbol)
            self.salvar_estado_trades()
        except Exception as e:
            self.log(f"❌ Falha no processo de Breakeven: {e}", symbol)

    def fechar_posicao_segura(self, symbol, price, motivo):
        state = self.asset_states[symbol]

        if self.modo_teste_var.get():
            novo_saldo = state["saldo_crypto"] * price
            lucro_pct = ((price - state["preco_compra"]) / state["preco_compra"]) * 100
            self.log(f"🔴 VENDA SIM ({motivo}): {price:.5f} | Res: {lucro_pct:.2f}%", symbol)
            state["saldo_usdt"] = float(state.get("saldo_usdt", 0.0)) + novo_saldo
            state["saldo_crypto"] = 0.0
            self.registrar_trade_excel(symbol, price, motivo)
            self.reset_posicao(symbol)
            self.update_card_metric(symbol, "balance", f"${state['saldo_usdt']:.2f} (Sim)")
            self.update_card_metric(symbol, "alvos", "---")
            self.set_status(symbol, "STATUS: 🔎 Buscando...", "#3498DB")
            self.salvar_estado_trades()
            self.finalizar_remocao_apos_venda(symbol)
            return

        try:
            self.exchange.load_time_difference()
            self.log(f"🔄 Iniciando protocolo de fechamento ({motivo})...", symbol)

            try:
                self.exchange.cancel_all_orders(symbol)
            except Exception as e:
                if "-2011" not in str(e):
                    self.log(f"⚠️ Aviso Cancelamento: {e}", symbol)

            time.sleep(1)
            currency = symbol.split("/")[0]
            bal = self.exchange.fetch_balance()
            crypto_free = float(bal.get(currency, {}).get("free", 0.0))
            limite_poeira = max((state["saldo_crypto"] * 0.1), 0.0001)

            if crypto_free > limite_poeira:
                self.log(f"💰 Executando VENDA A MERCADO para garantir {motivo}...", symbol)
                ordem_venda = self.exchange.create_market_sell_order(symbol, crypto_free)
                preco_real_venda = float(ordem_venda.get("average", price) or price)
                self.log(f"🔴 VENDA CONFIRMADA: {crypto_free} @ {preco_real_venda}", symbol)
                self.registrar_trade_excel(symbol, preco_real_venda, motivo)
            else:
                self.log(f"ℹ️ A Binance já executou a ordem OCO ({motivo}).", symbol)
                self.tocar_som("VENDA")
                self.registrar_trade_excel(symbol, price, motivo)

            self.reset_posicao(symbol)
            self.update_card_metric(symbol, "alvos", "---")
            bal_novo = self.exchange.fetch_balance()
            self.update_card_metric(symbol, "balance", f"${float(bal_novo.get('USDT', {}).get('free', 0.0)):.2f}")
            self.set_status(symbol, "STATUS: 🔎 Buscando...", "#3498DB")
            self.salvar_estado_trades()
            self.finalizar_remocao_apos_venda(symbol)
        except Exception as e:
            self.log(f"❌ Erro Crítico Fechamento: {e}", symbol)

    def reset_posicao(self, symbol):
        state = self.asset_states[symbol]
        state["posicionado"] = False
        state["aguardando_confirmacao"] = False
        self.limpar_entrada_com_recuo(symbol)
        state["breakeven_ativado"] = False
        state["preco_compra"] = 0.0
        state["stop_loss"] = 0.0
        state["take_profit"] = 0.0
        state["saldo_crypto"] = 0.0
        state["alvo_atual"] = TARGET_NORMAL

    def finalizar_remocao_apos_venda(self, symbol):
        """Remove do dashboard/configuração um ativo que o usuário retirou enquanto estava posicionado."""
        with self.config_lock:
            state = self.asset_states.get(symbol)
            if not state or not state.get("remover_apos_venda") or state.get("posicionado"):
                return False
            if symbol in self.ativos:
                self.ativos.remove(symbol)
            state["ativo_ativo"] = False
            state["remover_apos_venda"] = False
            self.telemetry_cache.pop(symbol, None)
            if self.selected_symbol == symbol:
                self.selected_symbol = self.ativos[0] if self.ativos else None
            self.salvar_ativos_config()

        def _refresh():
            self.rebuild_asset_cards()
            self.preencher_entries_ativos()
            self.rebuild_telemetry_cards()
            self.lbl_detail_title.configure(text="TELEMETRIA AVANÇADA - TODOS OS ATIVOS EM ANÁLISE")
            self.lbl_status_geral.configure(
                text=f"STATUS: {'🟢 Rodando' if self.executando else '💤 Aguardando'} | Ativos: {len(self.ativos)}",
                text_color="#2ECC71" if self.executando else "gray"
            )
        self.safe_ui(_refresh)
        self.log("Ativo removido após fechamento da posição.", symbol)
        return True

    # ==========================================
    # --- PERSISTÊNCIA E LOG ---
    # ==========================================
    def registrar_trade_excel(self, symbol, preco_venda, motivo):
        try:
            state = self.asset_states[symbol]
            nome_arquivo = ARQUIVO_LOG_SIM if self.modo_teste_var.get() else ARQUIVO_LOG_REAL
            data_hora = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            lucro_pct = ((preco_venda - state["preco_compra"]) / state["preco_compra"]) * 100
            novo_registro = {
                "Data/Hora": [data_hora],
                "Ativo": [symbol],
                "Compra ($)": [state["preco_compra"]],
                "Venda ($)": [preco_venda],
                "Resultado (%)": [round(lucro_pct, 4)],
                "Motivo Saída": [motivo],
                "Modo": ["SIM" if self.modo_teste_var.get() else "REAL"]
            }
            df_novo = pd.DataFrame(novo_registro)
            if os.path.exists(nome_arquivo):
                df_existente = pd.read_excel(nome_arquivo)
                df_final = pd.concat([df_existente, df_novo], ignore_index=True)
            else:
                df_final = df_novo
            df_final.to_excel(nome_arquivo, index=False)
            self.log(f"📊 Trade registrado: {nome_arquivo}", symbol)
        except Exception as e:
            self.log(f"⚠️ Erro Excel: {e}", symbol)

    def salvar_estado_trades(self):
        dados = {"trades": {}, "modo_simulacao": self.modo_teste_var.get()}
        for symbol, state in self.asset_states.items():
            if state.get("posicionado"):
                dados["trades"][symbol] = {
                    "preco_compra": state["preco_compra"],
                    "take_profit": state["take_profit"],
                    "stop_loss": state["stop_loss"],
                    "breakeven_ativado": state["breakeven_ativado"],
                    "saldo_simulado_crypto": state["saldo_crypto"],
                    "saldo_simulado_usdt": state["saldo_usdt"],
                    "valor_usdt": state.get("valor_usdt", DEFAULT_VALOR_USDT),
                    "alvo_atual": state["alvo_atual"]
                }
        try:
            if dados["trades"]:
                with open(ARQUIVO_ESTADO, "w", encoding="utf-8") as f:
                    json.dump(dados, f, indent=2)
                self.log("💾 Estado multiativos salvo.")
            elif os.path.exists(ARQUIVO_ESTADO):
                os.remove(ARQUIVO_ESTADO)
                self.log("🗑️ Arquivo de estado limpo.")
        except Exception as e:
            self.log(f"⚠️ Erro ao salvar estado: {e}")

    def verificar_trades_pendentes(self):
        if not os.path.exists(ARQUIVO_ESTADO):
            return
        try:
            with open(ARQUIVO_ESTADO, "r", encoding="utf-8") as f:
                dados = json.load(f)
            self.modo_teste_var.set(dados.get("modo_simulacao", True))
            trades = dados.get("trades", {})
            novos_ativos = list(dict.fromkeys(self.ativos + list(trades.keys())))[:MAX_ATIVOS]
            self.ativos = novos_ativos
            for symbol in self.ativos:
                if symbol not in self.asset_states:
                    self.asset_states[symbol] = self.create_asset_state(symbol)
            self.rebuild_asset_cards()
            self.preencher_entries_ativos()

            for symbol, trade in trades.items():
                if symbol not in self.asset_states:
                    continue
                state = self.asset_states[symbol]
                state["ativo_ativo"] = True
                state["remover_apos_venda"] = False
                state["posicionado"] = True
                state["preco_compra"] = float(trade["preco_compra"])
                state["take_profit"] = float(trade["take_profit"])
                state["stop_loss"] = float(trade["stop_loss"])
                state["breakeven_ativado"] = bool(trade.get("breakeven_ativado", False))
                state["saldo_crypto"] = float(trade.get("saldo_simulado_crypto", 0.0))
                state["saldo_usdt"] = float(trade.get("saldo_simulado_usdt", state["saldo_usdt"]))
                state["valor_usdt"] = float(trade.get("valor_usdt", state.get("valor_usdt", DEFAULT_VALOR_USDT)))
                state["alvo_atual"] = float(trade.get("alvo_atual", TARGET_NORMAL))
                self.update_card_metric(symbol, "valor_usdt", f"${state['valor_usdt']:.2f}")
                self.update_card_metric(symbol, "alvos", f"TP: {state['take_profit']:.4f} | SL: {state['stop_loss']:.4f}")
                self.update_card_metric(symbol, "balance", "POSICIONADO (Rec)" if not self.modo_teste_var.get() else f"Qtd: {state['saldo_crypto']:.6f}")
                self.set_status(symbol, "STATUS: ♻️ TRADE RECUPERADO", "#F1C40F")
                self.log("♻️ TRADE RECUPERADO!", symbol)
        except Exception as e:
            self.log(f"⚠️ Erro ao recuperar estado: {e}")

    # ==========================================
    # --- CONTROLES, SOM E GIF ---
    # ==========================================
    def tocar_som(self, tipo):
        if winsound is None:
            return

        def _play():
            try:
                if tipo == "COMPRA":
                    winsound.Beep(1000, 200)
                    time.sleep(0.05)
                    winsound.Beep(1500, 400)
                elif tipo == "VENDA":
                    winsound.Beep(2000, 100)
                    time.sleep(0.05)
                    winsound.Beep(2000, 100)
                    time.sleep(0.05)
                    winsound.Beep(2500, 300)
            except Exception:
                pass

        threading.Thread(target=_play, daemon=True).start()

    def toggle_mode(self):
        if self.possui_posicao_aberta():
            self.log("Não altere o modo com posição aberta.")
            self.modo_teste_var.set(not self.modo_teste_var.get())
            return

        if not self.modo_teste_var.get():
            self.log("Tentando conectar na Binance...")
            try:
                if not API_KEY or not SECRET_KEY:
                    raise RuntimeError("BINANCE_API_KEY/BINANCE_SECRET_KEY não configuradas")
                self.exchange.load_time_difference()
                bal = self.exchange.fetch_balance()
                usdt_free = float(bal.get("USDT", {}).get("free", 0.0))
                for symbol in self.ativos:
                    self.update_card_metric(symbol, "balance", f"${usdt_free:.2f}")
                self.log(f"✅ Conectado! Saldo USDT livre: ${usdt_free:.2f}")
            except Exception as e:
                self.log(f"❌ Erro Conexão: {e}")
                self.modo_teste_var.set(True)
        else:
            for symbol, state in self.asset_states.items():
                self.update_card_metric(symbol, "balance", f"${state['saldo_usdt']:.2f} (Sim)")

    def start_thread(self):
        if self.executando:
            return
        if not self.aplicar_ativos_da_interface():
            return
        self.executando = True
        self.lbl_status_geral.configure(text=f"STATUS: 🟢 Rodando | Ativos: {len(self.ativos)}", text_color="#2ECC71")
        self.worker_thread = threading.Thread(target=self.run_strategy, daemon=True)
        self.worker_thread.start()

    def stop_bot(self):
        self.executando = False
        self.log("Parando...")
        self.lbl_status_geral.configure(text="STATUS: 🛑 Parado", text_color="#E74C3C")
        for symbol in self.ativos:
            if not self.asset_states[symbol].get("posicionado"):
                self.set_status(symbol, "STATUS: 🛑 Parado", "#E74C3C")

    def carregar_gif(self):
        try:
            headers = {"User-Agent": "Mozilla/5.0"}
            response = requests.get(GIF_URL, headers=headers, timeout=10)
            if response.status_code != 200:
                self.safe_ui(lambda: self.lbl_gif.configure(text=f"Erro HTTP {response.status_code}", text_color="red"))
                return

            img_data = BytesIO(response.content)
            gif_source = Image.open(img_data)
            self.gif_frames = []
            try:
                while True:
                    frame = gif_source.copy().convert("RGBA").resize((350, 220), Image.Resampling.LANCZOS)
                    ctk_img = ctk.CTkImage(light_image=frame, dark_image=frame, size=(350, 220))
                    self.gif_frames.append(ctk_img)
                    gif_source.seek(len(self.gif_frames))
            except EOFError:
                pass

            if self.gif_frames:
                self.safe_ui(lambda: self.lbl_gif.configure(text=""))
                self.animar_gif()
            else:
                self.safe_ui(lambda: self.lbl_gif.configure(text="Erro: GIF Vazio", text_color="red"))
        except Exception as e:
            print(f"Erro Crítico GIF: {e}")
            self.safe_ui(lambda: self.lbl_gif.configure(text="Erro Conexão", text_color="red"))

    def animar_gif(self):
        if self.gif_frames:
            frame_atual = self.gif_frames[self.gif_idx]
            self.lbl_gif.configure(image=frame_atual)
            self.gif_idx = (self.gif_idx + 1) % len(self.gif_frames)
            self.after(40, self.animar_gif)


if __name__ == "__main__":
    app = CryptoBot()
    app.mainloop()
