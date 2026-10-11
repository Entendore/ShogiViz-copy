#!/usr/bin/env python3
"""
Shogi Puzzle Learning Application — Professional Edition
Features:
- Integer board encoding, pre-computed move/ray tables, make/unmake, Zobrist hashing
- YaneuraOu Engine Integration (USI Protocol) for analysis and professional mate solving
- MP4 Video Maker with YouTube / YouTube Shorts resolution presets
"""

import sys, json, sqlite3, os, math, random, time, re, subprocess, threading
from collections import OrderedDict
from datetime import datetime
from typing import Optional, List, Dict, Tuple, Set, Any

from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QLabel, QPushButton, QComboBox, QSpinBox, QFileDialog, QMessageBox,
    QDialog, QFormLayout, QLineEdit, QTextEdit, QSplitter, QGroupBox,
    QTableWidget, QTableWidgetItem, QHeaderView, QListWidget,
    QListWidgetItem, QCheckBox, QProgressDialog, QInputDialog,
    QToolBar, QDockWidget, QTabWidget, QFrame, QSizePolicy, QGridLayout,
    QAbstractItemView, QStatusBar, QMenu, QMenuBar, QDialogButtonBox,
    QSlider, QRadioButton, QButtonGroup,
)
from PySide6.QtCore import Qt, QRect, QRectF, QPointF, Signal, Slot, QSize, QTimer, QThread, QObject
from PySide6.QtGui import (
    QPainter, QPen, QBrush, QColor, QFont, QPainterPath, QAction,
    QPolygonF, QLinearGradient, QRadialGradient, QFontMetrics,
    QTransform, QPixmap, QFontInfo, QKeySequence, QIcon, QImage,
)

# --- Video Export Dependencies ---
try:
    import imageio.v2 as imageio
    import numpy as np
    VIDEO_EXPORT_AVAILABLE = True
except ImportError:
    VIDEO_EXPORT_AVAILABLE = False

# ══════════════════════════════════════════════════════════════════════════════
#  INTEGER PIECE ENCODING
# ══════════════════════════════════════════════════════════════════════════════
EMPTY = 0
K_ID, R_ID, B_ID, G_ID, S_ID, N_ID, L_ID, P_ID = 1, 2, 3, 4, 5, 6, 7, 8
PR_ID, PB_ID, PS_ID, PN_ID, PL_ID, PP_ID = 9, 10, 11, 12, 13, 14
SENTE, GOTE = 0, 1

def make_piece(owner: int, tid: int) -> int: return (owner << 4) | tid
def owner_of(p: int) -> int: return p >> 4
def type_of(p: int) -> int: return p & 0xF
def is_promoted_type(tid: int) -> bool: return tid >= 9

SK, SR, SB, SG, SS, SN, SL, SP = [make_piece(SENTE, t) for t in range(1, 9)]
SPR, SPB, SPS, SPN, SPL, SPP = [make_piece(SENTE, t) for t in range(9, 15)]
GK, GR, GB, GG, GS, GN, GL, GP = [make_piece(GOTE, t) for t in range(1, 9)]
GPR, GPB, GPS, GPN, GPL, GPP = [make_piece(GOTE, t) for t in range(9, 15)]

PROMOTE_MAP = {R_ID: PR_ID, B_ID: PB_ID, S_ID: PS_ID, N_ID: PN_ID, L_ID: PL_ID, P_ID: PP_ID}
DEMOTE_MAP = {v: k for k, v in PROMOTE_MAP.items()}
PROMOTABLE_IDS = set(PROMOTE_MAP.keys())
GOLD_LIKE_IDS = {G_ID, PS_ID, PN_ID, PL_ID, PP_ID}

STR_TO_TID = {"K": K_ID, "R": R_ID, "B": B_ID, "G": G_ID, "S": S_ID, "N": N_ID, "L": L_ID, "P": P_ID, "+R": PR_ID, "+B": PB_ID, "+S": PS_ID, "+N": PN_ID, "+L": PL_ID, "+P": PP_ID}
TID_TO_STR = {v: k for k, v in STR_TO_TID.items()}
PIECE_TO_SFEN = {SK:'K',SR:'R',SB:'B',SG:'G',SS:'S',SN:'N',SL:'L',SP:'P',SPR:'+R',SPB:'+B',SPS:'+S',SPN:'+N',SPL:'+L',SPP:'+P',GK:'k',GR:'r',GB:'b',GG:'g',GS:'s',GN:'n',GL:'l',GP:'p',GPR:'+r',GPB:'+b',GPS:'+s',GPN:'+n',GPL:'+l',GPP:'+p'}
SFEN_TO_PIECE = {v: k for k, v in PIECE_TO_SFEN.items()}
KANJI_MAP = {(SENTE,K_ID):"玉",(GOTE,K_ID):"王",(SENTE,R_ID):"飛",(GOTE,R_ID):"飛",(SENTE,B_ID):"角",(GOTE,B_ID):"角",(SENTE,G_ID):"金",(GOTE,G_ID):"金",(SENTE,S_ID):"銀",(GOTE,S_ID):"銀",(SENTE,N_ID):"桂",(GOTE,N_ID):"桂",(SENTE,L_ID):"香",(GOTE,L_ID):"香",(SENTE,P_ID):"歩",(GOTE,P_ID):"歩",(SENTE,PR_ID):"龍",(GOTE,PR_ID):"龍",(SENTE,PB_ID):"馬",(GOTE,PB_ID):"馬",(SENTE,PS_ID):"全",(GOTE,PS_ID):"全",(SENTE,PN_ID):"圭",(GOTE,PN_ID):"圭",(SENTE,PL_ID):"杏",(GOTE,PL_ID):"杏",(SENTE,PP_ID):"と",(GOTE,PP_ID):"と"}
EN_NAME_MAP = {K_ID:"King",R_ID:"Rook",B_ID:"Bishop",G_ID:"Gold",S_ID:"Silver",N_ID:"Knight",L_ID:"Lance",P_ID:"Pawn",PR_ID:"Dragon",PB_ID:"Horse",PS_ID:"+Silver",PN_ID:"+Knight",PL_ID:"+Lance",PP_ID:"Tokin"}
HAND_ORDER_IDS = [R_ID, B_ID, G_ID, S_ID, N_ID, L_ID, P_ID]
ROW_KANJI = ["一","二","三","四","五","六","七","八","九"]

N_DIR, S_DIR, E_DIR, W_DIR = 0, 1, 2, 3
NE_DIR, NW_DIR, SE_DIR, SW_DIR = 4, 5, 6, 7
_DIR_DR = (-1, 1, 0, 0, -1, -1, 1, 1)
_DIR_DC = (0, 0, 1, -1, 1, -1, 1, -1)
_RAYS: List[List[Tuple[int, ...]]] = [[] for _ in range(8)]
for _d in range(8):
    _dr, _dc = _DIR_DR[_d], _DIR_DC[_d]; _tbl = []
    for _sq in range(81):
        _r, _c = divmod(_sq, 9); _ray = []; _nr, _nc = _r + _dr, _c + _dc
        while 0 <= _nr < 9 and 0 <= _nc < 9: _ray.append(_nr * 9 + _nc); _nr += _dr; _nc += _dc
        _tbl.append(tuple(_ray))
    _RAYS[_d] = _tbl

_GOLD_DELTAS = {SENTE: [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,0)], GOTE: [(1,-1),(1,0),(1,1),(0,-1),(0,1),(-1,0)]}
_SILVER_DELTAS = {SENTE: [(-1,-1),(-1,0),(-1,1),(1,-1),(1,1)], GOTE: [(1,-1),(1,0),(1,1),(-1,-1),(-1,1)]}
_KNIGHT_DELTAS = {SENTE: [(-2,-1),(-2,1)], GOTE: [(2,-1),(2,1)]}
_PAWN_DELTAS = {SENTE: [(-1,0)], GOTE: [(1,0)]}

FIXED_MOVES: List[List[Optional[List[Tuple[int, ...]]]]] = [[None]*15 for _ in range(2)]
def _build_fixed(deltas_map, tids):
    for _owner, _deltas in deltas_map.items():
        for _tid in tids:
            _tbl = [None]*81
            for _sq in range(81):
                _r, _c = divmod(_sq, 9); _dests = []
                for _dr, _dc in _deltas:
                    _nr, _nc = _r + _dr, _c + _dc
                    if 0 <= _nr < 9 and 0 <= _nc < 9: _dests.append(_nr * 9 + _nc)
                _tbl[_sq] = tuple(_dests)
            FIXED_MOVES[_owner][_tid] = _tbl

for _owner in (SENTE, GOTE):
    _tbl = [None]*81
    for _sq in range(81):
        _r, _c = divmod(_sq, 9); _dests = []
        for _dr in (-1,0,1):
            for _dc in (-1,0,1):
                if _dr or _dc:
                    _nr, _nc = _r+_dr, _c+_dc
                    if 0 <= _nr < 9 and 0 <= _nc < 9: _dests.append(_nr*9+_nc)
        _tbl[_sq] = tuple(_dests)
    FIXED_MOVES[_owner][K_ID] = _tbl

_build_fixed(_GOLD_DELTAS, GOLD_LIKE_IDS); _build_fixed(_SILVER_DELTAS, {S_ID}); _build_fixed(_KNIGHT_DELTAS, {N_ID}); _build_fixed(_PAWN_DELTAS, {P_ID})
for _owner in (SENTE, GOTE):
    _tbl = [None]*81
    for _sq in range(81):
        _dests = []
        for _d in (NE_DIR, NW_DIR, SE_DIR, SW_DIR):
            if _RAYS[_d][_sq]: _dests.append(_RAYS[_d][_sq][0])
        _tbl[_sq] = tuple(_dests)
    FIXED_MOVES[_owner][PR_ID] = _tbl
    _tbl = [None]*81
    for _sq in range(81):
        _dests = []
        for _d in (N_DIR, S_DIR, E_DIR, W_DIR):
            if _RAYS[_d][_sq]: _dests.append(_RAYS[_d][_sq][0])
        _tbl[_sq] = tuple(_dests)
    FIXED_MOVES[_owner][PB_ID] = _tbl
LANCE_SLIDE_DIR = {SENTE: N_DIR, GOTE: S_DIR}

# --- Zobrist Hashing Tables ---
random.seed(42)
ZOBRIST_BOARD = [[random.getrandbits(64) for _ in range(31)] for _ in range(81)]
ZOBRIST_TURN = random.getrandbits(64)
random.seed()

CLR_BOARD_CELL = QColor(216, 179, 120); CLR_BOARD_LINE = QColor(60, 40, 15, 200)
CLR_SEL = QColor(60, 210, 60, 100); CLR_LAST = QColor(230, 210, 60, 80); CLR_CHECK = QColor(240, 60, 60, 100); CLR_PROM_TEXT = QColor(185, 15, 15)
WOOD_LIGHT = QColor(250, 235, 200); WOOD_MID = QColor(230, 200, 155); WOOD_DARK = QColor(195, 160, 110)
PROM_WOOD_LIGHT = QColor(255, 225, 205); PROM_WOOD_MID = QColor(240, 195, 155); PROM_WOOD_DARK = QColor(210, 155, 100)
KANJI_FONT_FAMILIES = ["Yu Mincho","Hiragino Mincho ProN","MS Mincho","Noto Serif CJK JP","Meiryo","Yu Gothic","Arial Unicode MS"]
CELL = 66; MARGIN = 32; PAGE_SIZE = 50

# Video Preserves
VIDEO_PRESETS = OrderedDict([
    ("YouTube 1080p  (1920×1080)",  {"w": 1920, "h": 1080, "orient": "landscape", "fps_default": 30}),
    ("YouTube 720p   (1280×720)",   {"w": 1280, "h": 720,  "orient": "landscape", "fps_default": 30}),
    ("YouTube 480p   (854×480)",    {"w": 854,  "h": 480,  "orient": "landscape", "fps_default": 30}),
    ("YouTube 360p   (640×360)",    {"w": 640,  "h": 360,  "orient": "landscape", "fps_default": 30}),
    ("Shorts 1080p   (1080×1920)",  {"w": 1080, "h": 1920, "orient": "portrait",  "fps_default": 30}),
    ("Shorts 720p    (720×1280)",   {"w": 720,  "h": 1280, "orient": "portrait",  "fps_default": 30}),
    ("Shorts 480p    (480×854)",    {"w": 480,  "h": 854,  "orient": "portrait",  "fps_default": 30}),
])

# USI Piece Mapping for Drops
USI_HAND_MAP = {'R': R_ID, 'B': B_ID, 'G': G_ID, 'S': S_ID, 'N': N_ID, 'L': L_ID, 'P': P_ID}

# ══════════════════════════════════════════════════════════════════════════════
#  YANEURAOU USI ENGINE BRIDGE
# ══════════════════════════════════════════════════════════════════════════════
class USIEngine(QObject):
    ready = Signal()
    bestmove = Signal(str, str)
    checkmate = Signal(str)
    info = Signal(dict)
    error = Signal(str)
    
    def __init__(self, parent=None):
        super().__init__(parent)
        self.proc: Optional[subprocess.Popen] = None
        self.running = False
        self.thread: Optional[threading.Thread] = None

    def start_engine(self, path: str) -> bool:
        try:
            self.proc = subprocess.Popen(
                [path], stdin=subprocess.PIPE, stdout=subprocess.PIPE, 
                stderr=subprocess.PIPE, text=True, bufsize=1, encoding='utf-8'
            )
            self.running = True
            self.thread = threading.Thread(target=self._read_loop, daemon=True)
            self.thread.start()
            self.send_command("usi")
            return True
        except Exception as e:
            self.error.emit(f"Failed to start engine: {e}")
            return False

    def _read_loop(self):
        while self.running and self.proc and self.proc.poll() is None:
            try:
                line = self.proc.stdout.readline().strip()
                if not line: continue
                self._parse_line(line)
            except Exception:
                break

    def _parse_line(self, line: str):
        if line == "usiok":
            self.ready.emit()
        elif line == "readyok":
            self.ready.emit()
        elif line.startswith("bestmove"):
            parts = line.split()
            move = parts[1] if len(parts) > 1 else "resign"
            ponder = parts[3] if len(parts) > 3 and parts[2] == "ponder" else ""
            self.bestmove.emit(move, ponder)
        elif line.startswith("checkmate"):
            result = line.split()[1] if len(line.split()) > 1 else "nomate"
            moves_str = " ".join(line.split()[1:])
            self.checkmate.emit(moves_str)
        elif line.startswith("info"):
            self.info.emit({"raw": line})

    def send_command(self, cmd: str):
        if self.proc and self.running and self.proc.poll() is None:
            try:
                self.proc.stdin.write(cmd + "\n")
                self.proc.stdin.flush()
            except Exception:
                self.error.emit("Engine process terminated unexpectedly.")

    def quit(self):
        self.send_command("quit")
        self.running = False
        if self.proc:
            try: self.proc.terminate()
            except: pass

# ══════════════════════════════════════════════════════════════════════════════
#  KomaRenderer
# ══════════════════════════════════════════════════════════════════════════════
class LRUCache:
    def __init__(self, capacity: int): self._cache = OrderedDict(); self._capacity = capacity
    def get(self, key):
        if key in self._cache: self._cache.move_to_end(key); return self._cache[key]
        return None
    def put(self, key, value):
        if key in self._cache: self._cache.move_to_end(key)
        self._cache[key] = value
        while len(self._cache) > self._capacity: self._cache.popitem(last=False)

class KomaRenderer:
    _cached_font_name: Optional[str] = None
    _pixmap_cache = LRUCache(600); _mini_cache = LRUCache(300)

    @classmethod
    def _resolve_font(cls, size: int, weight=QFont.Bold) -> QFont:
        if cls._cached_font_name is None:
            for fam in KANJI_FONT_FAMILIES:
                f = QFont(fam, size, weight); f.setStyleStrategy(QFont.PreferMatch | QFont.PreferQuality)
                actual = QFontInfo(f).family().lower().replace(" ", "")
                if actual in [x.lower().replace(" ","") for x in KANJI_FONT_FAMILIES]: cls._cached_font_name = fam; break
            if cls._cached_font_name is None: cls._cached_font_name = "Sans"
        font = QFont(cls._cached_font_name, size, weight); font.setStyleHint(QFont.Serif); return font

    @staticmethod
    def _pentagon_sente(cx, cy, w, h):
        path = QPainterPath(); ty=cy-h*0.50; my=cy-h*0.10; by=cy+h*0.50; thw=w*0.08; mhw=w*0.38; bhw=w*0.46
        path.moveTo(cx, ty); path.lineTo(cx+thw, ty+h*0.08); path.lineTo(cx+mhw, my); path.lineTo(cx+bhw, by-h*0.04); path.lineTo(cx+bhw-w*0.02, by); path.lineTo(cx-bhw+w*0.02, by); path.lineTo(cx-bhw, by-h*0.04); path.lineTo(cx-mhw, my); path.lineTo(cx-thw, ty+h*0.08); path.closeSubpath(); return path

    @staticmethod
    def _pentagon_gote(cx, cy, w, h):
        path = QPainterPath(); by=cy+h*0.50; my=cy+h*0.10; ty=cy-h*0.50; bhw=w*0.08; mhw=w*0.38; thw=w*0.46
        path.moveTo(cx, by); path.lineTo(cx-bhw, by-h*0.08); path.lineTo(cx-mhw, my); path.lineTo(cx-thw, ty+h*0.04); path.lineTo(cx-thw+w*0.02, ty); path.lineTo(cx+thw-w*0.02, ty); path.lineTo(cx+thw, ty+h*0.04); path.lineTo(cx+mhw, my); path.lineTo(cx+bhw, by-h*0.08); path.closeSubpath(); return path

    @classmethod
    def cached_koma_pixmap(cls, piece_owner, tid, w, h, selected=False):
        key = (piece_owner, tid, int(w), int(h), selected); pm = cls._pixmap_cache.get(key)
        if pm is None:
            iw=max(int(w),1); ih=max(int(h),1); pm=QPixmap(iw,ih); pm.fill(Qt.transparent)
            qp=QPainter(pm); qp.setRenderHint(QPainter.Antialiasing); cls._draw_koma_impl(qp,w/2,h/2,w,h,piece_owner,tid,selected); qp.end(); cls._pixmap_cache.put(key,pm)
        return pm

    @classmethod
    def _draw_koma_impl(cls, qp, cx, cy, w, h, piece_owner, tid, selected):
        promoted = is_promoted_type(tid); is_king = tid == K_ID
        path = cls._pentagon_sente(cx, cy, w, h) if piece_owner == SENTE else cls._pentagon_gote(cx, cy, w, h)
        sp = QPainterPath(path); sp.translate(3, 4); qp.setPen(Qt.NoPen); qp.setBrush(QColor(40,25,5,60)); qp.drawPath(sp)
        eg = QLinearGradient(cx-w/2,cy-h/2,cx+w/2,cy+h/2); eg.setColorAt(0,QColor(180,140,80)); eg.setColorAt(1,QColor(130,90,40))
        qp.setPen(QPen(QColor(110,75,30),1.8)); qp.setBrush(QBrush(eg)); qp.drawPath(path)
        t=QTransform(); t.translate(cx,cy); t.scale(0.92,0.93); t.translate(-cx,-cy); inner=t.map(path)
        wg = QLinearGradient(cx,cy-h/2,cx,cy+h/2) if piece_owner==SENTE else QLinearGradient(cx,cy+h/2,cx,cy-h/2)
        if promoted: wg.setColorAt(0,PROM_WOOD_LIGHT); wg.setColorAt(0.3,PROM_WOOD_MID); wg.setColorAt(0.7,PROM_WOOD_MID); wg.setColorAt(1,PROM_WOOD_DARK)
        elif is_king: wg.setColorAt(0,QColor(255,240,210)); wg.setColorAt(0.3,QColor(240,215,170)); wg.setColorAt(0.7,QColor(235,210,165)); wg.setColorAt(1,QColor(210,175,120))
        else: wg.setColorAt(0,WOOD_LIGHT); wg.setColorAt(0.3,WOOD_MID); wg.setColorAt(0.7,WOOD_MID); wg.setColorAt(1,WOOD_DARK)
        qp.setPen(Qt.NoPen); qp.setBrush(QBrush(wg)); qp.drawPath(inner)
        qp.save(); qp.setClipPath(inner); qp.setPen(QPen(QColor(170,135,80,30),0.6))
        for i in range(-8,9): gy=cy+i*(h/14)+(2 if i%2==0 else -1); qp.drawLine(QPointF(cx-w*0.45,gy),QPointF(cx+w*0.45,gy))
        qp.restore()
        ht=QTransform(); ht.translate(cx,cy); ht.scale(0.88,0.89); ht.translate(-cx,-cy); hp=ht.map(path)
        hg = QLinearGradient(cx,cy-h*0.45,cx,cy-h*0.05) if piece_owner==SENTE else QLinearGradient(cx,cy+h*0.45,cx,cy+h*0.05)
        hg.setColorAt(0,QColor(255,255,240,90)); hg.setColorAt(0.5,QColor(255,255,240,30)); hg.setColorAt(1,QColor(255,255,240,0))
        qp.setPen(Qt.NoPen); qp.setBrush(QBrush(hg)); qp.drawPath(hp)
        kanji = KANJI_MAP.get((piece_owner, tid), "?"); text_cy = cy + h*0.04 if piece_owner == SENTE else cy - h*0.04
        base_sz = min(w, h) * (0.52 if not is_king else 0.494); fsz = base_sz if len(kanji)==1 else base_sz*0.7
        font = cls._resolve_font(int(fsz)); font.setWeight(QFont.Bold); qp.setFont(font)
        tc = CLR_PROM_TEXT if promoted else QColor(30,20,10); tr = QRectF(cx-w*0.38,text_cy-h*0.28,w*0.76,h*0.56)
        if piece_owner == GOTE: qp.save(); qp.translate(tr.center()); qp.rotate(180); qp.translate(-tr.center())
        sr = tr.adjusted(1.2,1.2,1.2,1.2); qp.setPen(QColor(80,50,20,50)); qp.drawText(sr, Qt.AlignCenter, kanji)
        qp.setPen(QPen(tc)); qp.drawText(tr, Qt.AlignCenter, kanji)
        if piece_owner == GOTE: qp.restore()
        if selected: qp.setPen(QPen(QColor(50,220,50,200),2.5)); qp.setBrush(QColor(50,220,50,40)); qp.drawPath(path)

    @staticmethod
    def draw_koma(qp, cx, cy, w, h, piece_owner, tid, selected=False):
        pm = KomaRenderer.cached_koma_pixmap(piece_owner, tid, w, h, selected); qp.drawPixmap(QPointF(cx - w/2, cy - h/2), pm)

    @classmethod
    def cached_mini_pixmap(cls, piece_owner, tid, mw, mh):
        key = (piece_owner, tid, int(mw), int(mh)); pm = cls._mini_cache.get(key)
        if pm is None:
            iw=max(int(mw),1); ih=max(int(mh),1); pm=QPixmap(iw,ih); pm.fill(Qt.transparent)
            qp=QPainter(pm); qp.setRenderHint(QPainter.Antialiasing); cls._draw_mini_impl(qp,mw,mh,piece_owner,tid); qp.end(); cls._mini_cache.put(key,pm)
        return pm

    @classmethod
    def _draw_mini_impl(cls, qp, mw, mh, piece_owner, tid):
        cx,cy=mw/2,mh/2; promoted=is_promoted_type(tid)
        path = cls._pentagon_sente(cx,cy,mw*0.75,mh*0.85) if piece_owner==SENTE else cls._pentagon_gote(cx,cy,mw*0.75,mh*0.85)
        sp=QPainterPath(path); sp.translate(1.5,2); qp.setPen(Qt.NoPen); qp.setBrush(QColor(40,25,5,50)); qp.drawPath(sp)
        g=QLinearGradient(cx,cy-mh/2,cx,cy+mh/2)
        if promoted: g.setColorAt(0,PROM_WOOD_LIGHT); g.setColorAt(1,PROM_WOOD_DARK)
        else: g.setColorAt(0,WOOD_LIGHT); g.setColorAt(1,WOOD_DARK)
        qp.setPen(QPen(QColor(120,85,35),1.2)); qp.setBrush(QBrush(g)); qp.drawPath(path)
        kanji=KANJI_MAP.get((piece_owner,tid),"?"); font=cls._resolve_font(max(int(mw*0.28),7)); font.setWeight(QFont.Bold); qp.setFont(font)
        qp.setPen(QPen(CLR_PROM_TEXT if promoted else QColor(30,20,10))); tr=QRectF(cx-mw*0.32,cy-mh*0.25,mw*0.64,mh*0.5)
        if piece_owner==GOTE: qp.save(); qp.translate(tr.center()); qp.rotate(180); qp.translate(-tr.center()); qp.drawText(tr,Qt.AlignCenter,kanji); qp.restore()
        else: qp.drawText(tr,Qt.AlignCenter,kanji)

    @staticmethod
    def draw_mini_koma(qp, x, y, mw, mh, piece_owner, tid, count=1):
        pm = KomaRenderer.cached_mini_pixmap(piece_owner, tid, mw, mh); qp.drawPixmap(QPointF(x, y), pm)

# ══════════════════════════════════════════════════════════════════════════════
#  ShogiBoard
# ══════════════════════════════════════════════════════════════════════════════
class _Undo:
    __slots__ = ('frm','to','moved_piece','captured_piece','new_piece','is_drop','drop_owner','drop_tid','hand_key','hand_old_val','king_owner_moved','king_old_sq','cap_king_owner','cap_king_old_sq','prev_hash','prev_turn','drop_pawn_col_owner','drop_pawn_col_col','moved_pawn_col_from_owner','moved_pawn_col_from_col','moved_pawn_col_to_owner','moved_pawn_col_to_col')

class ShogiBoard:
    def __init__(self):
        self.board: List[int] = [EMPTY]*81; self.king_pos: List[int] = [-1,-1]; self.pawn_col_count: List[List[int]] = [[0]*9,[0]*9]
        self.hand: List[Dict[int,int]] = [{}, {}]; self.turn: int = SENTE; self.zhash: int = 0; self.history: List[dict] = []

    def at(self, r, c): return self.board[r*9+c] if 0<=r<9 and 0<=c<9 else EMPTY
    def _compute_hash(self):
        h=0
        for sq in range(81):
            p=self.board[sq]
            if p: h^=ZOBRIST_BOARD[sq][p]
        if self.turn: h^=ZOBRIST_TURN
        return h
    def copy(self):
        b=ShogiBoard(); b.board=self.board[:]; b.king_pos=self.king_pos[:]; b.pawn_col_count=[r[:] for r in self.pawn_col_count]; b.hand=[dict(h) for h in self.hand]; b.turn=self.turn; b.zhash=self.zhash; b.history=list(self.history); return b

    @staticmethod
    def in_zone(ow, row): return row<=2 if ow==SENTE else row>=6
    @staticmethod
    def must_promote(ow, tid, to_row):
        if tid==P_ID or tid==L_ID: return (ow==SENTE and to_row==0) or (ow==GOTE and to_row==8)
        if tid==N_ID: return (ow==SENTE and to_row<=1) or (ow==GOTE and to_row>=7)
        return False
    @staticmethod
    def can_promote(ow, tid, fr, tr): return tid in PROMOTABLE_IDS and (ShogiBoard.in_zone(ow, fr) or ShogiBoard.in_zone(ow, tr))

    def valid_moves(self, r, c):
        sq=r*9+c; p=self.board[sq]
        if not p: return []
        ow=owner_of(p); tid=type_of(p); mvs=[]
        ftbl=FIXED_MOVES[ow][tid]
        if ftbl is not None:
            for dsq in ftbl[sq]:
                dp=self.board[dsq]
                if not dp or owner_of(dp)!=ow: mvs.append(dsq)
        if tid==R_ID or tid==PR_ID:
            for d in (N_DIR,S_DIR,E_DIR,W_DIR):
                for rsq in _RAYS[d][sq]:
                    rp=self.board[rsq]
                    if not rp: mvs.append(rsq)
                    elif owner_of(rp)!=ow: mvs.append(rsq); break
                    else: break
        if tid==B_ID or tid==PB_ID:
            for d in (NE_DIR,NW_DIR,SE_DIR,SW_DIR):
                for rsq in _RAYS[d][sq]:
                    rp=self.board[rsq]
                    if not rp: mvs.append(rsq)
                    elif owner_of(rp)!=ow: mvs.append(rsq); break
                    else: break
        if tid==L_ID:
            for rsq in _RAYS[LANCE_SLIDE_DIR[ow]][sq]:
                rp=self.board[rsq]
                if not rp: mvs.append(rsq)
                elif owner_of(rp)!=ow: mvs.append(rsq); break
                else: break
        return mvs

    def legal_moves(self, r, c):
        sq=r*9+c; p=self.board[sq]
        if not p: return []
        ow=owner_of(p); tid=type_of(p); legal=[]
        for dsq in self.valid_moves(r, c):
            dr,_=divmod(dsq,9); must=self.must_promote(ow,tid,dr)
            if must:
                undo=self._make(sq,dsq,promote=True); ok=not self.in_check(ow); self._unmake(undo)
                if ok: legal.append(dsq)
            else:
                undo=self._make(sq,dsq,promote=False); ok_no=not self.in_check(ow); self._unmake(undo)
                if ok_no: legal.append(dsq)
                elif self.can_promote(ow,tid,r,dr):
                    undo=self._make(sq,dsq,promote=True); ok_p=not self.in_check(ow); self._unmake(undo)
                    if ok_p: legal.append(dsq)
        return legal

    def drop_positions(self, ow, tid):
        pos=[]
        for sq in range(81):
            if self.board[sq]: continue
            r,c=divmod(sq,9)
            if tid==P_ID and self.pawn_col_count[ow][c]>0: continue
            if tid in (P_ID,L_ID) and ((ow==SENTE and r==0) or (ow==GOTE and r==8)): continue
            if tid==N_ID and ((ow==SENTE and r<=1) or (ow==GOTE and r>=7)): continue
            if tid==P_ID:
                undo=self._make_drop(sq,ow,P_ID); opp=1-ow
                if self.in_check(opp) and self._is_checkmate(opp): self._unmake(undo); continue
                self._unmake(undo)
            pos.append(sq)
        return pos

    def _make(self, frm_sq, to_sq, promote=False):
        u=_Undo(); u.frm=frm_sq; u.to=to_sq; u.is_drop=False; u.drop_owner=-1; u.drop_tid=-1; u.prev_hash=self.zhash; u.prev_turn=self.turn; u.drop_pawn_col_owner=-1; u.drop_pawn_col_col=-1; u.moved_pawn_col_from_owner=-1; u.moved_pawn_col_from_col=-1; u.moved_pawn_col_to_owner=-1; u.moved_pawn_col_to_col=-1
        moved=self.board[frm_sq]; captured=self.board[to_sq]; u.moved_piece=moved; u.captured_piece=captured
        ow=owner_of(moved); tid=type_of(moved); new_tid=PROMOTE_MAP[tid] if (promote and tid in PROMOTE_MAP) else tid; new_piece=make_piece(ow,new_tid); u.new_piece=new_piece
        self.zhash^=ZOBRIST_BOARD[frm_sq][moved]
        if captured: self.zhash^=ZOBRIST_BOARD[to_sq][captured]
        self.zhash^=ZOBRIST_BOARD[to_sq][new_piece]; self.board[frm_sq]=EMPTY; self.board[to_sq]=new_piece
        if tid==P_ID: _,fc=divmod(frm_sq,9); self.pawn_col_count[ow][fc]-=1; u.moved_pawn_col_from_owner=ow; u.moved_pawn_col_from_col=fc
        if new_tid==P_ID: _,tc=divmod(to_sq,9); self.pawn_col_count[ow][tc]+=1; u.moved_pawn_col_to_owner=ow; u.moved_pawn_col_to_col=tc
        u.king_owner_moved=-1; u.king_old_sq=-1
        if tid==K_ID: u.king_owner_moved=ow; u.king_old_sq=self.king_pos[ow]; self.king_pos[ow]=to_sq
        u.cap_king_owner=-1; u.cap_king_old_sq=-1
        if captured and type_of(captured)==K_ID: cap_ow=owner_of(captured); u.cap_king_owner=cap_ow; u.cap_king_old_sq=self.king_pos[cap_ow]; self.king_pos[cap_ow]=-1
        u.hand_key=None; u.hand_old_val=0
        if captured: cap_tid=type_of(captured); base_tid=DEMOTE_MAP.get(cap_tid,cap_tid); u.hand_key=(ow,base_tid); u.hand_old_val=self.hand[ow].get(base_tid,0); self.hand[ow][base_tid]=u.hand_old_val+1
        self.turn=1-self.turn; self.zhash^=ZOBRIST_TURN; return u

    def _make_drop(self, to_sq, ow, tid):
        u=_Undo(); u.frm=-1; u.to=to_sq; u.is_drop=True; u.drop_owner=ow; u.drop_tid=tid; u.moved_piece=EMPTY; u.captured_piece=EMPTY; u.new_piece=EMPTY; u.prev_hash=self.zhash; u.prev_turn=self.turn; u.king_owner_moved=-1; u.king_old_sq=-1; u.cap_king_owner=-1; u.cap_king_old_sq=-1; u.moved_pawn_col_from_owner=-1; u.moved_pawn_col_from_col=-1; u.moved_pawn_col_to_owner=-1; u.moved_pawn_col_to_col=-1
        piece=make_piece(ow,tid); self.zhash^=ZOBRIST_BOARD[to_sq][piece]; self.board[to_sq]=piece; u.new_piece=piece
        u.hand_key=(ow,tid); u.hand_old_val=self.hand[ow].get(tid,0); cnt=u.hand_old_val-1
        if cnt<=0: self.hand[ow].pop(tid,None)
        else: self.hand[ow][tid]=cnt
        if tid==P_ID: _,tc=divmod(to_sq,9); self.pawn_col_count[ow][tc]+=1; u.drop_pawn_col_owner=ow; u.drop_pawn_col_col=tc
        else: u.drop_pawn_col_owner=-1; u.drop_pawn_col_col=-1
        self.turn=1-self.turn; self.zhash^=ZOBRIST_TURN; return u

    def _unmake(self, u):
        self.zhash=u.prev_hash; self.turn=u.prev_turn
        if u.is_drop:
            self.board[u.to]=EMPTY
            if u.drop_pawn_col_owner>=0: self.pawn_col_count[u.drop_pawn_col_owner][u.drop_pawn_col_col]-=1
            ow,tid=u.hand_key; self.hand[ow][tid]=u.hand_old_val; return
        self.board[u.frm]=u.moved_piece; self.board[u.to]=u.captured_piece
        if u.moved_pawn_col_from_owner>=0: self.pawn_col_count[u.moved_pawn_col_from_owner][u.moved_pawn_col_from_col]+=1
        if u.moved_pawn_col_to_owner>=0: self.pawn_col_count[u.moved_pawn_col_to_owner][u.moved_pawn_col_to_col]-=1
        if u.king_owner_moved>=0: self.king_pos[u.king_owner_moved]=u.king_old_sq
        if u.cap_king_owner>=0: self.king_pos[u.cap_king_owner]=u.cap_king_old_sq
        if u.hand_key is not None:
            ow,base_tid=u.hand_key
            if u.hand_old_val==0: self.hand[ow].pop(base_tid,None)
            else: self.hand[ow][base_tid]=u.hand_old_val

    def in_check(self, ow):
        ksq=self.king_pos[ow]
        if ksq<0: return True
        opp=1-ow
        for check_tid, check_set in [(G_ID,GOLD_LIKE_IDS),(S_ID,{S_ID}),(N_ID,{N_ID}),(P_ID,{P_ID}),(K_ID,{K_ID}),(PR_ID,{PR_ID}),(PB_ID,{PB_ID})]:
            ftbl=FIXED_MOVES[opp][check_tid]
            if ftbl is None: continue
            for dsq in ftbl[ksq]:
                p=self.board[dsq]
                if p and owner_of(p)==opp and type_of(p) in check_set: return True
        for d in (N_DIR,S_DIR,E_DIR,W_DIR):
            for rsq in _RAYS[d][ksq]:
                p=self.board[rsq]
                if p:
                    if owner_of(p)==opp and type_of(p) in (R_ID,PR_ID): return True
                    break
        for d in (NE_DIR,NW_DIR,SE_DIR,SW_DIR):
            for rsq in _RAYS[d][ksq]:
                p=self.board[rsq]
                if p:
                    if owner_of(p)==opp and type_of(p) in (B_ID,PB_ID): return True
                    break
        lance_dir=S_DIR if opp==SENTE else N_DIR
        for rsq in _RAYS[lance_dir][ksq]:
            p=self.board[rsq]
            if p:
                if owner_of(p)==opp and type_of(p)==L_ID: return True
                break
        return False

    def find_king(self, ow): sq=self.king_pos[ow]; return divmod(sq,9) if sq>=0 else None

    def _is_checkmate(self, ow):
        if not self.in_check(ow): return False
        for sq in range(81):
            p=self.board[sq]
            if p and owner_of(p)==ow:
                r,c=divmod(sq,9); tid=type_of(p)
                for dsq in self.valid_moves(r,c):
                    dr,_=divmod(dsq,9); must=self.must_promote(ow,tid,dr)
                    undo=self._make(sq,dsq,promote=must); ok=not self.in_check(ow); self._unmake(undo)
                    if ok: return False
                    if not must and self.can_promote(ow,tid,r,dr):
                        undo=self._make(sq,dsq,promote=True); ok=not self.in_check(ow); self._unmake(undo)
                        if ok: return False
        for tid,cnt in list(self.hand[ow].items()):
            if cnt<=0: continue
            for sq in range(81):
                if self.board[sq]: continue
                r,c=divmod(sq,9)
                if tid in (P_ID,L_ID) and ((ow==SENTE and r==0) or (ow==GOTE and r==8)): continue
                if tid==N_ID and ((ow==SENTE and r<=1) or (ow==GOTE and r>=7)): continue
                if tid==P_ID and self.pawn_col_count[ow][c]>0: continue
                undo=self._make_drop(sq,ow,tid); ok=not self.in_check(ow); self._unmake(undo)
                if ok: return False
        return True

    def is_checkmate(self, ow): return self.in_check(ow) and self._is_checkmate(ow)

    def make_move(self, frm, to, promote=False, drop=None):
        b=self.copy()
        if drop:
            ow,tid=drop; tsq=to[0]*9+to[1]; b.board[tsq]=make_piece(ow,tid); cnt=b.hand[ow].get(tid,0)-1
            if cnt<=0: b.hand[ow].pop(tid,None)
            else: b.hand[ow][tid]=cnt
            if tid==P_ID: b.pawn_col_count[ow][to[1]]+=1
            if tid==K_ID: b.king_pos[ow]=tsq
        else:
            fsq=frm[0]*9+frm[1]; tsq=to[0]*9+to[1]; piece=b.board[fsq]; ow=owner_of(piece); tid=type_of(piece); cap=b.board[tsq]
            if cap: cap_tid=type_of(cap); base=DEMOTE_MAP.get(cap_tid,cap_tid); b.hand[ow][base]=b.hand[ow].get(base,0)+1
            if cap and type_of(cap)==K_ID: b.king_pos[owner_of(cap)]=-1
            new_tid=PROMOTE_MAP[tid] if (promote and tid in PROMOTE_MAP) else tid; b.board[fsq]=EMPTY; b.board[tsq]=make_piece(ow,new_tid)
            if tid==K_ID: b.king_pos[ow]=tsq
            if tid==P_ID: b.pawn_col_count[ow][frm[1]]-=1
            if new_tid==P_ID: b.pawn_col_count[ow][to[1]]+=1
        b.history.append({"from":frm,"to":to,"promote":promote,"drop":drop is not None}); b.turn=1-b.turn; b.zhash=b._compute_hash(); return b

    def to_dict(self):
        bd=[]
        for r in range(9):
            row=[]
            for c in range(9):
                p=self.board[r*9+c]
                if p: row.append(f"{'s' if owner_of(p)==SENTE else 'g'}{TID_TO_STR[type_of(p)]}")
                else: row.append("")
            bd.append(row)
        return {"board":bd,"hand_sente":{TID_TO_STR[k]:v for k,v in self.hand[SENTE].items()},"hand_gote":{TID_TO_STR[k]:v for k,v in self.hand[GOTE].items()},"turn":self.turn}

    @classmethod
    def from_dict(cls, d):
        b=cls()
        for r in range(9):
            for c in range(9):
                cell=d["board"][r][c]
                if cell:
                    ow=SENTE if cell[0]=='s' else GOTE; tid=STR_TO_TID[cell[1:]]; sq=r*9+c; b.board[sq]=make_piece(ow,tid)
                    if tid==K_ID: b.king_pos[ow]=sq
                    if tid==P_ID: b.pawn_col_count[ow][c]+=1
        b.hand[SENTE]={STR_TO_TID[k]:int(v) for k,v in d.get("hand_sente",{}).items()}; b.hand[GOTE]={STR_TO_TID[k]:int(v) for k,v in d.get("hand_gote",{}).items()}; b.turn=d.get("turn",SENTE); b.zhash=b._compute_hash(); return b

    @classmethod
    def from_sfen(cls, sfen):
        b=cls(); parts=sfen.split(); rows=parts[0].split("/")
        for r, row_str in enumerate(rows):
            c=0; i=0
            while i<len(row_str):
                ch=row_str[i]
                if ch=="+": key="+"+row_str[i+1]; i+=2
                elif ch.isdigit(): c+=int(ch); i+=1; continue
                else: key=ch; i+=1
                piece=SFEN_TO_PIECE.get(key)
                if piece: sq=r*9+c; b.board[sq]=piece; type_p=type_of(piece)
                if type_p==K_ID: b.king_pos[owner_of(piece)]=sq
                if type_p==P_ID: b.pawn_col_count[owner_of(piece)][c]+=1
                c+=1
        if len(parts)>1: b.turn=SENTE if parts[1]=="b" else GOTE
        if len(parts)>2 and parts[2]!="-":
            hs=parts[2]; i=0; hand_map={'R':R_ID,'B':B_ID,'G':G_ID,'S':S_ID,'N':N_ID,'L':L_ID,'P':P_ID}
            while i<len(hs):
                cnt=0
                while i<len(hs) and hs[i].isdigit(): cnt=cnt*10+int(hs[i]); i+=1
                if i>=len(hs): break
                ch=hs[i]; i+=1; cnt=cnt or 1; tid=hand_map.get(ch.upper())
                if tid: ow=SENTE if ch.isupper() else GOTE; b.hand[ow][tid]=b.hand[ow].get(tid,0)+cnt
        b.zhash=b._compute_hash(); return b

    def to_sfen(self):
        rows=[]
        for r in range(9):
            s=""; empty=0
            for c in range(9):
                p=self.board[r*9+c]
                if not p: empty+=1
                else:
                    if empty: s+=str(empty); empty=0
                    s+=PIECE_TO_SFEN[p]
            if empty: s+=str(empty)
            rows.append(s)
        sfen="/".join(rows); sfen+=" b" if self.turn==SENTE else " w"; hand_str=""; sfen_hand={R_ID:'r',B_ID:'b',G_ID:'g',S_ID:'s',N_ID:'n',L_ID:'l',P_ID:'p'}
        for ow in (SENTE,GOTE):
            for tid in HAND_ORDER_IDS:
                cnt=self.hand[ow].get(tid,0)
                if cnt<=0: continue
                ch=sfen_hand[tid]
                if ow==SENTE: ch=ch.upper()
                hand_str+=(str(cnt) if cnt>1 else "")+ch
        sfen+=" "+(hand_str or "-"); return sfen

    def setup_initial(self):
        self.board=[EMPTY]*81; self.king_pos=[-1,-1]; self.pawn_col_count=[[0]*9,[0]*9]; self.hand=[{},{}]; back=[L_ID,N_ID,S_ID,G_ID,K_ID,G_ID,S_ID,N_ID,L_ID]
        for c, tid in enumerate(back):
            self.board[0*9+c]=make_piece(GOTE,tid); self.board[8*9+c]=make_piece(SENTE,tid)
            if tid==K_ID: self.king_pos[GOTE]=0*9+c; self.king_pos[SENTE]=8*9+c
        self.board[1*9+1]=GB; self.board[1*9+7]=GR; self.board[7*9+1]=SB; self.board[7*9+7]=SR
        for c in range(9): self.board[2*9+c]=GP; self.pawn_col_count[GOTE][c]=1; self.board[6*9+c]=SP; self.pawn_col_count[SENTE][c]=1
        self.turn=SENTE; self.zhash=self._compute_hash()

    # ------------------------------------------------------------------
    #  USI Move Conversion Utilities
    # ------------------------------------------------------------------
    def move_to_usi(self, frm, to, promote=False, drop=None) -> str:
        if drop:
            ow, tid = drop
            piece_char = TID_TO_STR[tid] if not is_promoted_type(tid) else TID_TO_STR[tid]
            if ow == SENTE: piece_char = piece_char.upper()
            else: piece_char = piece_char.lower()
            # Remove + for drops (e.g. +R -> R)
            piece_char = piece_char.replace("+", "") 
            # USI Drops: Piece*Dest  -> Dest is (9-col) + row_char
            dest_col_usi = 9 - to[1]
            dest_row_usi = chr(ord('a') + 8 - to[0])
            return f"{piece_char}*{dest_col_usi}{dest_row_usi}"
        else:
            frm_col_usi = 9 - frm[1]
            frm_row_usi = chr(ord('a') + 8 - frm[0])
            to_col_usi = 9 - to[1]
            to_row_usi = chr(ord('a') + 8 - to[0])
            prom_str = "+" if promote else ""
            return f"{frm_col_usi}{frm_row_usi}{to_col_usi}{to_row_usi}{prom_str}"

    @staticmethod
    def usi_to_move(usi_str: str):
        """Returns (frm_tuple, to_tuple, promote_bool, drop_tuple_or_None)"""
        if '*' in usi_str:
            # Drop move
            parts = usi_str.split('*')
            piece_char = parts[0].upper().replace("+", "")
            tid = USI_HAND_MAP.get(piece_char)
            ow = SENTE if parts[0].isupper() else GOTE
            
            dest_col_usi = int(parts[1][0])
            dest_row_usi = ord(parts[1][1]) - ord('a')
            
            to_c = 9 - dest_col_usi
            to_r = 8 - dest_row_usi
            return None, (to_r, to_c), False, (ow, tid)
        else:
            # Board move
            promote = usi_str.endswith('+')
            move_str = usi_str.strip('+')
            
            frm_c = 9 - int(move_str[0])
            frm_r = 8 - (ord(move_str[1]) - ord('a'))
            to_c = 9 - int(move_str[2])
            to_r = 8 - (ord(move_str[3]) - ord('a'))
            
            return (frm_r, frm_c), (to_r, to_c), promote, None


# ══════════════════════════════════════════════════════════════════════════════
#  NATIVE TSUME GENERATOR (Fallback if no engine is loaded)
# ══════════════════════════════════════════════════════════════════════════════
class TsumeGenerator:
    @staticmethod
    def find_mate(board: "ShogiBoard", depth: int = 3) -> Optional[List[dict]]:
        if board.turn == SENTE: return TsumeGenerator._search_sente(board, depth)
        return TsumeGenerator._search_gote(board, depth)

    @staticmethod
    def _search_sente(board: "ShogiBoard", depth: int) -> Optional[List[dict]]:
        if depth <= 0: return None
        for sq in range(81):
            p = board.board[sq]
            if p and owner_of(p) == SENTE:
                r, c = divmod(sq, 9)
                for dsq in board.valid_moves(r, c):
                    dr, dc = divmod(dsq, 9)
                    must_prom = board.must_promote(SENTE, type_of(p), dr)
                    for prom in ([True, False] if board.can_promote(SENTE, type_of(p), r, dr) and not must_prom else [must_prom]):
                        undo = board._make(sq, dsq, promote=prom)
                        if board.in_check(GOTE):
                            gote_resp = TsumeGenerator._search_gote(board, depth - 1)
                            if gote_resp is not None:
                                frm_rc, to_rc = divmod(sq, 9), divmod(dsq, 9)
                                move_dict = {"from": frm_rc, "to": to_rc, "promote": prom, "drop": None}
                                board._unmake(undo)
                                return [move_dict] + gote_resp
                        board._unmake(undo)
        for tid, cnt in list(board.hand[SENTE].items()):
            if cnt <= 0: continue
            for sq in board.drop_positions(SENTE, tid):
                undo = board._make_drop(sq, SENTE, tid)
                if board.in_check(GOTE):
                    gote_resp = TsumeGenerator._search_gote(board, depth - 1)
                    if gote_resp is not None:
                        to_rc = divmod(sq, 9)
                        move_dict = {"from": None, "to": to_rc, "promote": False, "drop": (SENTE, tid)}
                        board._unmake(undo)
                        return [move_dict] + gote_resp
                board._unmake(undo)
        return None

    @staticmethod
    def _search_gote(board: "ShogiBoard", depth: int) -> Optional[List[dict]]:
        if not board.in_check(GOTE): return None
        has_escape = False; longest_mate_line = None
        for sq in range(81):
            p = board.board[sq]
            if p and owner_of(p) == GOTE:
                r, c = divmod(sq, 9)
                for dsq in board.legal_moves(r, c):
                    has_escape = True
                    dr, dc = divmod(dsq, 9); must_prom = board.must_promote(GOTE, type_of(p), dr)
                    for prom in ([True, False] if board.can_promote(GOTE, type_of(p), r, dr) and not must_prom else [must_prom]):
                        undo = board._make(sq, dsq, promote=prom)
                        if not board.in_check(GOTE):
                            sente_resp = TsumeGenerator._search_sente(board, depth - 1)
                            board._unmake(undo)
                            if sente_resp is None: return None
                            if longest_mate_line is None or len(sente_resp) > len(longest_mate_line):
                                frm_rc, to_rc = divmod(sq, 9), divmod(dsq, 9)
                                longest_mate_line = [{"from": frm_rc, "to": to_rc, "promote": prom, "drop": None}] + sente_resp
                        else: board._unmake(undo)
        for tid, cnt in list(board.hand[GOTE].items()):
            if cnt <= 0: continue
            for sq in board.drop_positions(GOTE, tid):
                has_escape = True; undo = board._make_drop(sq, GOTE, tid)
                if not board.in_check(GOTE):
                    sente_resp = TsumeGenerator._search_sente(board, depth - 1)
                    board._unmake(undo)
                    if sente_resp is None: return None
                    if longest_mate_line is None or len(sente_resp) > len(longest_mate_line):
                        to_rc = divmod(sq, 9)
                        longest_mate_line = [{"from": None, "to": to_rc, "promote": False, "drop": (GOTE, tid)}] + sente_resp
                else: board._unmake(undo)
        if not has_escape: return []
        return longest_mate_line

    @staticmethod
    def generate_random_tsume(max_depth: int = 5) -> Tuple["ShogiBoard", List[dict]]:
        while True:
            b = ShogiBoard()
            kr, kc = random.choice([(0,0),(0,1),(1,0),(1,1),(7,7),(7,8),(8,7),(8,8)])
            b.board[kr*9+kc] = GK; b.king_pos[GOTE] = kr*9+kc
            sr, sc = random.choice([(6,6),(6,7),(7,6)])
            b.board[sr*9+sc] = SK; b.king_pos[SENTE] = sr*9+sc
            pieces_to_add = random.choice([[SR, SG],[SR, SP],[SB, SG, SP],[SR, SB],[SG, SG, SP]])
            for tid in pieces_to_add:
                for _ in range(50):
                    r2, c2 = random.randint(max(0,kr-3), min(8,kr+3)), random.randint(max(0,kc-3), min(8,kc+3))
                    if b.board[r2*9+c2] == EMPTY: b.board[r2*9+c2] = make_piece(SENTE, tid); break
            b.turn = SENTE; b.zhash = b._compute_hash()
            solution = TsumeGenerator.find_mate(b, max_depth)
            if solution and not b.is_checkmate(GOTE) and len(solution) >= 1: return b, solution

# ══════════════════════════════════════════════════════════════════════════════
#  VIDEO EXPORTER (YouTube / Shorts)
# ══════════════════════════════════════════════════════════════════════════════
class PuzzleVideoExporter:
    @staticmethod
    def render_frame(board, size, highlights=None, moving_piece=None, orientation="landscape"):
        pm = QPixmap(size); pm.fill(QColor(40, 30, 20))
        qp = QPainter(pm); qp.setRenderHint(QPainter.Antialiasing)
        if orientation == "portrait": PuzzleVideoExporter._render_portrait(qp, board, size, highlights, moving_piece)
        else: PuzzleVideoExporter._render_landscape(qp, board, size, highlights, moving_piece)
        qp.end(); return pm

    @staticmethod
    def _render_landscape(qp, board, size, highlights, moving_piece):
        W, H = size.width(), size.height()
        hand_w = int(W * 0.20); board_area_w = W - hand_w
        s = min(board_area_w / (MARGIN*2 + CELL*9), H / (MARGIN*2 + CELL*9))
        cs = int(CELL * s); m = int(MARGIN * s); board_total = m*2 + cs*9
        ox = (board_area_w - board_total) // 2; oy = (H - board_total) // 2
        bg = QLinearGradient(m+ox, m+oy, m+ox+cs*9, m+oy+cs*9); bg.setColorAt(0.0, QColor(195,158,105)); bg.setColorAt(1.0, QColor(190,152,100))
        qp.setPen(QPen(QColor(80,50,15), max(3*s,2))); qp.setBrush(QBrush(bg)); qp.drawRoundedRect(QRectF(m+ox-4*s, m+oy-4*s, cs*9+8*s, cs*9+8*s), 4*s, 4*s)
        for sq in range(81):
            r, c = divmod(sq, 9); qp.fillRect(QRectF(m+ox+c*cs+0.5, m+oy+r*cs+0.5, cs-1, cs-1), QBrush(CLR_BOARD_CELL))
        qp.setPen(QPen(CLR_BOARD_LINE, max(1.5*s,1)))
        for i in range(10): qp.drawLine(QPointF(m+ox+i*cs, m+oy), QPointF(m+ox+i*cs, m+oy+9*cs)); qp.drawLine(QPointF(m+ox, m+oy+i*cs), QPointF(m+ox+9*cs, m+oy+i*cs))
        if highlights:
            for r, c in highlights: qp.fillRect(QRectF(m+ox+c*cs, m+oy+r*cs, cs, cs), CLR_LAST)
        for sq in range(81):
            p = board.board[sq]
            if p:
                if moving_piece and moving_piece.get("sq") == sq: continue
                r, c = divmod(sq, 9); cx = m+ox + c*cs + cs/2; cy = m+oy + r*cs + cs/2
                KomaRenderer.draw_koma(qp, cx, cy, cs*0.82, cs*0.88, owner_of(p), type_of(p))
        if moving_piece:
            p = moving_piece["piece"]; cx = m+ox + moving_piece["x"]*cs + cs/2; cy = m+oy + moving_piece["y"]*cs + cs/2
            KomaRenderer.draw_koma(qp, cx, cy, cs*0.82, cs*0.88, owner_of(p), type_of(p))
        hx = board_area_w
        for ow, start_y, label in [(GOTE, 0, "▲ Gote Hand"), (SENTE, H//2, "△ Sente Hand")]:
            gr = QRectF(hx, start_y, hand_w, H//2); hbg = QLinearGradient(gr.topLeft(), gr.bottomRight()); hbg.setColorAt(0, QColor(230,210,170,80)); hbg.setColorAt(1, QColor(200,175,135,80))
            qp.setPen(QPen(QColor(140,110,60,120), 1)); qp.setBrush(QBrush(hbg)); qp.drawRoundedRect(gr, 6, 6)
            qp.setFont(QFont("Arial", max(int(11*s),8), QFont.Bold)); qp.setPen(QColor(60,40,15)); qp.drawText(QRectF(hx+4, start_y+6, hand_w-8, 24*s), Qt.AlignCenter, label)
            yy = start_y + int(34*s); mw_k, mh_k = int(32*s), int(32*s)
            for tid in HAND_ORDER_IDS:
                cnt = board.hand[ow].get(tid, 0)
                if cnt <= 0: continue
                KomaRenderer.draw_mini_koma(qp, hx+6, yy+2, mw_k, mh_k, ow, tid, cnt)
                name = EN_NAME_MAP.get(tid, "?"); promoted = is_promoted_type(tid)
                qp.setFont(QFont("Arial", max(int(10*s),7))); qp.setPen(QPen(CLR_PROM_TEXT if promoted else QColor(40,30,15)))
                qp.drawText(QRectF(hx+mw_k+10, yy, hand_w-mw_k-18, int(32*s)), Qt.AlignVCenter|Qt.AlignLeft, f"×{cnt}  {name}"); yy += int(38*s)
        tt = "△ Sente" if board.turn == SENTE else "▲ Gote"
        qp.setFont(QFont("Arial", max(int(12*s),9), QFont.Bold)); qp.setPen(QColor(220,200,160)); qp.drawText(QRectF(hx, H-30*s, hand_w, 24*s), Qt.AlignCenter, f"Turn: {tt}")

    @staticmethod
    def _render_portrait(qp, board, size, highlights, moving_piece):
        W, H = size.width(), size.height()
        m = int(W * 0.04); cs = (W - 2*m) // 9
        board_h = cs * 9; hand_zone_h = (H - board_h - 2*m) // 2
        gote_hand_y = m; board_y = m + hand_zone_h; sente_hand_y = board_y + board_h + m
        bg = QLinearGradient(m, board_y, m+cs*9, board_y+cs*9); bg.setColorAt(0.0, QColor(195,158,105)); bg.setColorAt(1.0, QColor(190,152,100))
        qp.setPen(QPen(QColor(80,50,15), 3)); qp.setBrush(QBrush(bg)); qp.drawRoundedRect(QRectF(m-4, board_y-4, cs*9+8, cs*9+8), 4, 4)
        for sq in range(81):
            r, c = divmod(sq, 9); qp.fillRect(QRectF(m+c*cs+0.5, board_y+r*cs+0.5, cs-1, cs-1), QBrush(CLR_BOARD_CELL))
        qp.setPen(QPen(CLR_BOARD_LINE, 1.5))
        for i in range(10): qp.drawLine(QPointF(m+i*cs, board_y), QPointF(m+i*cs, board_y+9*cs)); qp.drawLine(QPointF(m, board_y+i*cs), QPointF(m+9*cs, board_y+i*cs))
        if highlights:
            for r, c in highlights: qp.fillRect(QRectF(m+c*cs, board_y+r*cs, cs, cs), CLR_LAST)
        for sq in range(81):
            p = board.board[sq]
            if p:
                if moving_piece and moving_piece.get("sq") == sq: continue
                r, c = divmod(sq, 9); cx = m + c*cs + cs/2; cy = board_y + r*cs + cs/2
                KomaRenderer.draw_koma(qp, cx, cy, cs*0.82, cs*0.88, owner_of(p), type_of(p))
        if moving_piece:
            p = moving_piece["piece"]; cx = m + moving_piece["x"]*cs + cs/2; cy = board_y + moving_piece["y"]*cs + cs/2
            KomaRenderer.draw_koma(qp, cx, cy, cs*0.82, cs*0.88, owner_of(p), type_of(p))
        PuzzleVideoExporter._draw_hand_horizontal(qp, board, GOTE, "▲ Gote Hand", QRectF(m, gote_hand_y, cs*9, hand_zone_h), cs)
        PuzzleVideoExporter._draw_hand_horizontal(qp, board, SENTE, "△ Sente Hand", QRectF(m, sente_hand_y, cs*9, hand_zone_h), cs)
        tt = "△ Sente" if board.turn == SENTE else "▲ Gote"
        qp.setFont(QFont("Arial", max(int(cs*0.22),10), QFont.Bold)); qp.setPen(QColor(220,200,160)); qp.drawText(QRectF(m, H - m - int(cs*0.35), cs*9, int(cs*0.35)), Qt.AlignCenter, f"Turn: {tt}")

    @staticmethod
    def _draw_hand_horizontal(qp, board, ow, label, rect, cs):
        hbg = QLinearGradient(rect.topLeft(), rect.bottomRight()); hbg.setColorAt(0, QColor(230,210,170,90)); hbg.setColorAt(1, QColor(200,175,135,90))
        qp.setPen(QPen(QColor(140,110,60,120), 1)); qp.setBrush(QBrush(hbg)); qp.drawRoundedRect(rect, 6, 6)
        qp.setFont(QFont("Arial", max(int(cs*0.18),9), QFont.Bold)); qp.setPen(QColor(60,40,15)); qp.drawText(QRectF(rect.x()+4, rect.y()+2, rect.width()-8, cs*0.35), Qt.AlignCenter, label)
        mw_k = int(cs*0.55); mh_k = int(cs*0.58); piece_types = [tid for tid in HAND_ORDER_IDS if board.hand[ow].get(tid, 0) > 0]
        if not piece_types: return
        slot_w = min((rect.width() - 8) / len(piece_types), mw_k + 36); start_x = rect.x() + max((rect.width() - slot_w * len(piece_types)) / 2, 4); yy = rect.y() + cs*0.38
        for idx, tid in enumerate(piece_types):
            cnt = board.hand[ow][tid]; px = start_x + idx * slot_w
            KomaRenderer.draw_mini_koma(qp, px+2, yy+2, mw_k, mh_k, ow, tid, cnt)
            name = EN_NAME_MAP.get(tid, "?"); promoted = is_promoted_type(tid)
            qp.setFont(QFont("Arial", max(int(cs*0.14),7))); qp.setPen(QPen(CLR_PROM_TEXT if promoted else QColor(40,30,15)))
            qp.drawText(QRectF(px+mw_k+4, yy, slot_w-mw_k-8, mh_k), Qt.AlignVCenter|Qt.AlignLeft, f"×{cnt}")

    @staticmethod
    def pixmap_to_array(pm: QPixmap) -> 'np.ndarray':
        qimg = pm.toImage().convertToFormat(QImage.Format_RGB888); width, height = qimg.width(), qimg.height()
        ptr = qimg.bits(); ptr.setsize(height * width * 3); arr = np.array(ptr).reshape((height, width, 3)); return arr

    @staticmethod
    def export_to_mp4(initial_board, solution_moves, filepath, preset_key="YouTube 720p   (1280×720)", fps=30, duration_pause=1.0, duration_slide=0.4):
        if not VIDEO_EXPORT_AVAILABLE: raise ImportError("Install imageio[ffmpeg] and numpy")
        preset = VIDEO_PRESETS[preset_key]; W, H = preset["w"], preset["h"]; orientation = preset["orient"]; size = QSize(W, H)
        writer = imageio.get_writer(filepath, fps=fps); board = initial_board.copy()
        init_pm = PuzzleVideoExporter.render_frame(board, size, highlights=[], orientation=orientation); init_arr = PuzzleVideoExporter.pixmap_to_array(init_pm)
        for _ in range(int(fps * duration_pause)): writer.append_data(init_arr)
        for move in solution_moves:
            frm = move.get("from"); to = move["to"]; promote = move.get("promote", False); drop = move.get("drop")
            hl = []
            if frm: hl.append(frm)
            hl.append(to)
            hl_pm = PuzzleVideoExporter.render_frame(board, size, highlights=hl, orientation=orientation); hl_arr = PuzzleVideoExporter.pixmap_to_array(hl_pm)
            for _ in range(int(fps * 0.5)): writer.append_data(hl_arr)
            frames_slide = max(int(fps * duration_slide), 1)
            for f_idx in range(frames_slide):
                t = (f_idx + 1) / frames_slide
                if drop:
                    ow, tid = drop; piece = make_piece(ow, tid); start_x, start_y = to[1], -1; end_x, end_y = to[1], to[0]
                    cur_x = start_x + (end_x - start_x) * t; cur_y = start_y + (end_y - start_y) * t
                    anim_dict = {"piece": piece, "sq": -1, "x": cur_x, "y": cur_y}
                else:
                    fsq = frm[0]*9 + frm[1]; piece = board.board[fsq]; start_x, start_y = frm[1], frm[0]; end_x, end_y = to[1], to[0]
                    cur_x = start_x + (end_x - start_x) * t; cur_y = start_y + (end_y - start_y) * t
                    anim_dict = {"piece": piece, "sq": fsq, "x": cur_x, "y": cur_y}
                anim_pm = PuzzleVideoExporter.render_frame(board, size, highlights=hl, moving_piece=anim_dict, orientation=orientation)
                writer.append_data(PuzzleVideoExporter.pixmap_to_array(anim_pm))
            board = board.make_move(frm, to, promote=promote, drop=drop)
            post_pm = PuzzleVideoExporter.render_frame(board, size, highlights=[to], orientation=orientation); post_arr = PuzzleVideoExporter.pixmap_to_array(post_pm)
            for _ in range(int(fps * duration_pause)): writer.append_data(post_arr)
        writer.close()


# ══════════════════════════════════════════════════════════════════════════════
#  VIDEO EXPORT DIALOG
# ══════════════════════════════════════════════════════════════════════════════
class VideoExportDialog(QDialog):
    def __init__(self, parent=None, puzzle_name: str = "puzzle"):
        super().__init__(parent); self.setWindowTitle("Export Puzzle Video"); self.setMinimumWidth(520); self._puzzle_name = puzzle_name; self._build_ui()

    def _build_ui(self):
        layout = QVBoxLayout(self)
        fmt_group = QGroupBox("Video Format"); fmt_lay = QVBoxLayout(fmt_group)
        self.rb_youtube = QRadioButton("YouTube  (Landscape 16:9)"); self.rb_shorts  = QRadioButton("YouTube Shorts  (Portrait 9:16)"); self.rb_youtube.setChecked(True)
        fmt_lay.addWidget(self.rb_youtube); fmt_lay.addWidget(self.rb_shorts); layout.addWidget(fmt_group)
        res_group = QGroupBox("Resolution"); res_lay = QFormLayout(res_group); self.combo_res = QComboBox(); self._populate_resolutions("landscape")
        res_lay.addRow("Preset:", self.combo_res); self.lbl_size = QLabel(); self._update_size_label(); res_lay.addRow("Frame size:", self.lbl_size); layout.addWidget(res_group)
        time_group = QGroupBox("Timing"); time_lay = QFormLayout(time_group)
        self.spin_fps = QSpinBox(); self.spin_fps.setRange(10, 60); self.spin_fps.setValue(30); time_lay.addRow("Frames per second:", self.spin_fps)
        self.spin_pause = QDoubleSpinBox(); self.spin_pause.setRange(0.2, 5.0); self.spin_pause.setValue(1.0); self.spin_pause.setSingleStep(0.1); self.spin_pause.setSuffix(" s"); time_lay.addRow("Pause between moves:", self.spin_pause)
        self.spin_slide = QDoubleSpinBox(); self.spin_slide.setRange(0.1, 2.0); self.spin_slide.setValue(0.4); self.spin_slide.setSingleStep(0.05); self.spin_slide.setSuffix(" s"); time_lay.addRow("Slide animation:", self.spin_slide); layout.addWidget(time_group)
        file_group = QGroupBox("Output File"); file_lay = QHBoxLayout(file_group); self.edit_path = QLineEdit(self._default_path()); btn_browse = QPushButton("Browse…"); btn_browse.clicked.connect(self._browse)
        file_lay.addWidget(self.edit_path, 1); file_lay.addWidget(btn_browse); layout.addWidget(file_group)
        btn_box = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel); btn_box.accepted.connect(self.accept); btn_box.rejected.connect(self.reject); layout.addWidget(btn_box)
        self.rb_youtube.toggled.connect(self._on_format_changed); self.combo_res.currentIndexChanged.connect(self._update_size_label)

    def _populate_resolutions(self, orient: str):
        self.combo_res.blockSignals(True); self.combo_res.clear()
        for key, preset in VIDEO_PRESETS.items():
            if preset["orient"] == orient: self.combo_res.addItem(key, key)
        self.combo_res.blockSignals(False)
        if self.combo_res.count() > 0: self.combo_res.setCurrentIndex(0)
        self._update_size_label()

    def _on_format_changed(self): self._populate_resolutions("landscape" if self.rb_youtube.isChecked() else "portrait")

    def _update_size_label(self):
        key = self.combo_res.currentData()
        if key and key in VIDEO_PRESETS: p = VIDEO_PRESETS[key]; self.lbl_size.setText(f"{p['w']} × {p['h']}  ({p['orient']})")
        else: self.lbl_size.setText("—")

    def _default_path(self) -> str: return os.path.join(os.path.expanduser("~"), f"{re.sub(r'[^\w\-.]', '_', self._puzzle_name)[:40]}.mp4")
    def _browse(self):
        path, _ = QFileDialog.getSaveFileName(self, "Save Video", self.edit_path.text(), "MP4 Video (*.mp4)")
        if path: self.edit_path.setText(path)

    def get_preset_key(self) -> str: return self.combo_res.currentData() or list(VIDEO_PRESETS.keys())[0]
    def get_filepath(self) -> str: p = self.edit_path.text().strip(); return p if p.lower().endswith(".mp4") else p + ".mp4"
    def get_fps(self) -> int: return self.spin_fps.value()
    def get_pause(self) -> float: return self.spin_pause.value()
    def get_slide(self) -> float: return self.spin_slide.value()


# ══════════════════════════════════════════════════════════════════════════════
#  UI WIDGETS
# ══════════════════════════════════════════════════════════════════════════════
class BoardWidget(QWidget):
    cell_clicked = Signal(int, int); hand_clicked = Signal(int, int)

    def __init__(self, parent=None):
        super().__init__(parent); self.board = ShogiBoard(); self.sel = None; self.sel_hand = None; self.valid = set(); self.last_move = None; self.check_cells = []; self.edit_mode = False; self._hand_rects = {SENTE: {}, GOTE: {}}; self._scale = 1.0
        w = MARGIN*2 + CELL*9 + 160; h = MARGIN*2 + CELL*9; self.setMinimumSize(w, h); self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)

    def set_board(self, board: ShogiBoard):
        self.board = board; self.sel = None; self.sel_hand = None; self.valid = set(); self._update_check(); self.update()

    def _update_check(self):
        self.check_cells = []
        for ow in (SENTE, GOTE):
            if self.board.in_check(ow):
                kp = self.board.find_king(ow)
                if kp: self.check_cells.append(kp)

    def _cell_at(self, pos):
        s = self._scale; m = int(MARGIN * s); cs = int(CELL * s); c = (pos.x() - m) // cs; r = (pos.y() - m) // cs
        return (r, c) if 0 <= r < 9 and 0 <= c < 9 else None

    def mousePressEvent(self, e):
        p = e.position().toPoint(); cell = self._cell_at(p)
        if cell: self.cell_clicked.emit(cell[0], cell[1]); return
        for ow in (SENTE, GOTE):
            for tid, rect in self._hand_rects[ow].items():
                if rect.contains(p): self.hand_clicked.emit(ow, tid); return

    def paintEvent(self, e):
        qp = QPainter(self)
        try: self._paint(qp)
        finally: qp.end()

    def _paint(self, qp):
        qp.setRenderHint(QPainter.Antialiasing); available_w = self.width() - 160; available_h = self.height(); sx = available_w / (MARGIN * 2 + CELL * 9); sy = available_h / (MARGIN * 2 + CELL * 9); self._scale = min(sx, sy, 1.5); s = self._scale; cs = int(CELL * s); m = int(MARGIN * s); b = self.board
        board_rect = QRectF(m-4, m-4, cs*9+8, cs*9+8); bg = QLinearGradient(m, m, m+cs*9, m+cs*9); bg.setColorAt(0.0, QColor(195,158,105)); bg.setColorAt(1.0, QColor(190,152,100)); qp.setPen(QPen(QColor(80,50,15), 3)); qp.setBrush(QBrush(bg)); qp.drawRoundedRect(board_rect, 4, 4)
        for sq in range(81):
            r, c = divmod(sq, 9); cg = QLinearGradient(m+c*cs, m+r*cs, m+c*cs+cs, m+r*cs+cs); cg.setColorAt(0.0, CLR_BOARD_CELL.lighter(102)); cg.setColorAt(1.0, CLR_BOARD_CELL.darker(102)); qp.fillRect(QRectF(m+c*cs+0.5, m+r*cs+0.5, cs-1, cs-1), QBrush(cg))
        qp.save(); qp.setClipRect(QRectF(m, m, cs*9, cs*9)); qp.setPen(QPen(QColor(180,145,90,25), 0.8))
        for i in range(0, cs*9, max(int(7*s), 3)): qp.drawLine(QPointF(m, m+i), QPointF(m+cs*9, m+i+3))
        qp.restore(); qp.setPen(QPen(CLR_BOARD_LINE, 1.5))
        for i in range(10): qp.drawLine(QPointF(m+i*cs, m), QPointF(m+i*cs, m+9*cs)); qp.drawLine(QPointF(m, m+i*cs), QPointF(m+9*cs, m+i*cs))
        qp.setBrush(QBrush(QColor(60,40,15,180))); qp.setPen(Qt.NoPen)
        for sr, sc in [(3,3),(3,6),(6,3),(6,6)]: qp.drawEllipse(QPointF(m+sc*cs, m+sr*cs), 3.5, 3.5)
        lf = QFont("Arial", max(int(10*s),7), QFont.Bold); qp.setFont(lf); qp.setPen(QColor(60,40,15))
        for i in range(9):
            qp.drawText(QRectF(m+i*cs, 2, cs, m-4), Qt.AlignCenter, str(9-i)); qp.setFont(QFont("Yu Mincho", max(int(9*s),6))); qp.drawText(QRectF(m+9*cs+4, m+i*cs, m-6, cs), Qt.AlignVCenter|Qt.AlignLeft, ROW_KANJI[i]); qp.setFont(lf)
        if self.last_move:
            for pos in self.last_move:
                if pos: qp.fillRect(QRectF(m+pos[1]*cs, m+pos[0]*cs, cs, cs), CLR_LAST)
        for r, c in self.check_cells: qp.fillRect(QRectF(m+c*cs, m+r*cs, cs, cs), CLR_CHECK)
        if self.sel: qp.fillRect(QRectF(m+self.sel[1]*cs, m+self.sel[0]*cs, cs, cs), CLR_SEL)
        for sq in self.valid:
            r, c = divmod(sq, 9); target = b.board[sq]
            if target: qp.setPen(QPen(QColor(220,60,60,160),3)); qp.setBrush(Qt.NoBrush); qp.drawRoundedRect(QRectF(m+c*cs+3, m+r*cs+3, cs-6, cs-6), 4, 4)
            else: qp.setPen(Qt.NoPen); qp.setBrush(QBrush(QColor(60,130,240,100))); qp.drawEllipse(QPointF(m+c*cs+cs/2, m+r*cs+cs/2), cs/7, cs/7)
        for sq in range(81):
            p = b.board[sq]
            if p: r, c = divmod(sq, 9); cx = m + c*cs + cs/2; cy = m + r*cs + cs/2; pw = cs*0.82; ph = cs*0.88; is_sel = (self.sel == (r, c)); KomaRenderer.draw_koma(qp, cx, cy, pw, ph, owner_of(p), type_of(p), is_sel)
        self._draw_hands(qp, m, cs, s)
        if self.edit_mode: qp.setPen(QPen(QColor(255,50,50,180), 3, Qt.DashLine)); qp.setBrush(Qt.NoBrush); qp.drawRoundedRect(board_rect, 4, 4)
        tt = "△ Sente" if b.turn == SENTE else "▲ Gote"; qp.setFont(QFont("Arial", max(int(11*s),8), QFont.Bold)); qp.setPen(QColor(50,40,20)); qp.drawText(QRectF(m, m+9*cs+6, cs*9, 20*s), Qt.AlignCenter, f"Turn: {tt}")

    def _draw_hands(self, qp, m, cs, s):
        bx = m + 9*cs + int(38*s); b = self.board; self._hand_rects = {SENTE: {}, GOTE: {}}; hw = int(140*s)
        for ow, start_y, label in [(GOTE, m, "▲ Gote Hand"), (SENTE, m+cs*9//2, "△ Sente Hand")]:
            gr = QRectF(bx-6, start_y-2, hw+8, cs*9//2+4); hbg = QLinearGradient(gr.topLeft(), gr.bottomRight()); hbg.setColorAt(0, QColor(230,210,170,80)); hbg.setColorAt(1, QColor(200,175,135,80)); qp.setPen(QPen(QColor(140,110,60,120), 1)); qp.setBrush(QBrush(hbg)); qp.drawRoundedRect(gr, 6, 6)
            qp.setFont(QFont("Arial", max(int(9*s),7), QFont.Bold)); qp.setPen(QColor(60,40,15)); qp.drawText(QRectF(bx, start_y+2, hw, int(18*s)), Qt.AlignCenter, label)
            yy = start_y + int(24*s)
            for tid in HAND_ORDER_IDS:
                cnt = b.hand[ow].get(tid, 0)
                if cnt <= 0: continue
                rect = QRectF(bx, yy, hw-4, int(32*s)); self._hand_rects[ow][tid] = rect.toRect()
                if self.sel_hand == (ow, tid): qp.fillRect(rect, QColor(60,210,60,50)); qp.setPen(QPen(QColor(50,200,50,150), 1.5)); qp.setBrush(Qt.NoBrush); qp.drawRoundedRect(rect, 4, 4)
                mw, mh = int(28*s), int(28*s); KomaRenderer.draw_mini_koma(qp, bx+2, yy+2, mw, mh, ow, tid, cnt)
                promoted = is_promoted_type(tid); name = EN_NAME_MAP.get(tid, "?"); qp.setFont(QFont("Arial", max(int(10*s),7))); qp.setPen(QPen(CLR_PROM_TEXT if promoted else QColor(40,30,15))); qp.drawText(QRectF(bx+int(34*s), yy, hw-int(40*s), int(32*s)), Qt.AlignVCenter|Qt.AlignLeft, f"×{cnt}  {name}"); yy += int(34*s)


# ══════════════════════════════════════════════════════════════════════════════
#  PUZZLE DATABASE
# ══════════════════════════════════════════════════════════════════════════════
class PuzzleDatabase:
    def __init__(self, path="shogi_puzzles.db"): self.conn = sqlite3.connect(path); self.conn.row_factory = sqlite3.Row; self.conn.execute("PRAGMA journal_mode=WAL"); self.conn.execute("PRAGMA foreign_keys=ON"); self._init_db()
    def _init_db(self): self.conn.executescript("CREATE TABLE IF NOT EXISTS puzzles(id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT NOT NULL, category TEXT DEFAULT 'general', difficulty INTEGER DEFAULT 1, description TEXT, board_json TEXT NOT NULL, solution_json TEXT, sfen TEXT, source TEXT, created_at TEXT); CREATE TABLE IF NOT EXISTS progress(puzzle_id INTEGER PRIMARY KEY, solved INTEGER DEFAULT 0, attempts INTEGER DEFAULT 0, last_attempt TEXT, FOREIGN KEY(puzzle_id) REFERENCES puzzles(id));")
    def add_puzzle(self, name, board_json, solution_json=None, sfen=None, category="general", difficulty=1, description="", source=""): self.conn.execute("INSERT INTO puzzles(name,category,difficulty,description,board_json,solution_json,sfen,source,created_at) VALUES(?,?,?,?,?,?,?,?,?)", (name, category, difficulty, description, board_json, solution_json, sfen, source, datetime.now().isoformat())); self.conn.commit()
    def get_puzzle(self, puzzle_id): row = self.conn.execute("SELECT * FROM puzzles WHERE id=?", (puzzle_id,)).fetchone(); return dict(row) if row else None
    def list_puzzles(self, category=None, difficulty=None): q = "SELECT id,name,category,difficulty FROM puzzles WHERE 1=1"; params = []; 
    if category: q += " AND category=?"; params.append(category)
    if difficulty: q += " AND difficulty=?"; params.append(difficulty)
    q += " ORDER BY difficulty, id"; return [dict(r) for r in self.conn.execute(q, params).fetchall()]
    def delete_puzzle(self, puzzle_id): self.conn.execute("DELETE FROM puzzles WHERE id=?", (puzzle_id,)); self.conn.execute("DELETE FROM progress WHERE puzzle_id=?", (puzzle_id,)); self.conn.commit()

# ══════════════════════════════════════════════════════════════════════════════
#  MAIN WINDOW
# ══════════════════════════════════════════════════════════════════════════════
class ShogiMainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Shogi Puzzle Learning — YaneuraOu Engine Edition")
        self.resize(1100, 780)

        self.db = PuzzleDatabase()
        self.current_board: Optional[ShogiBoard] = None
        self.current_solution: Optional[List[dict]] = None
        self.solution_step = 0
        self.playing_solution = False
        self.initial_board = None

        # YaneuraOu Engine
        self.engine = USIEngine()
        self.engine.ready.connect(self._on_engine_ready)
        self.engine.bestmove.connect(self._on_engine_bestmove)
        self.engine.checkmate.connect(self._on_engine_checkmate)
        self.engine.error.connect(self._on_engine_error)
        self.engine_loaded = False

        self._build_ui()
        self._build_menus()
        self._load_random_tsume()

    # ------------------------------------------------------------------
    def _build_ui(self):
        central = QWidget(); self.setCentralWidget(central)
        main_lay = QHBoxLayout(central)
        self.board_widget = BoardWidget()
        self.board_widget.cell_clicked.connect(self._on_cell_clicked)
        self.board_widget.hand_clicked.connect(self._on_hand_clicked)

        right_panel = QWidget(); right_lay = QVBoxLayout(right_panel); right_panel.setFixedWidth(300)

        info_group = QGroupBox("Puzzle Info"); info_lay = QFormLayout(info_group)
        self.lbl_puzzle_name = QLabel("—"); self.lbl_difficulty = QLabel("—"); self.lbl_category = QLabel("—")
        info_lay.addRow("Name:", self.lbl_puzzle_name); info_lay.addRow("Difficulty:", self.lbl_difficulty); info_lay.addRow("Category:", self.lbl_category)
        right_lay.addWidget(info_group)

        sol_group = QGroupBox("Solution"); sol_lay = QVBoxLayout(sol_group)
        btn_row = QHBoxLayout()
        self.btn_play = QPushButton("▶ Play"); self.btn_play.clicked.connect(self._play_solution)
        self.btn_step = QPushButton("→ Step"); self.btn_step.clicked.connect(self._step_solution)
        self.btn_reset = QPushButton("⟲ Reset"); self.btn_reset.clicked.connect(self._reset_solution)
        btn_row.addWidget(self.btn_play); btn_row.addWidget(self.btn_step); btn_row.addWidget(self.btn_reset)
        sol_lay.addLayout(btn_row); self.lbl_step = QLabel("Step: 0 / 0"); sol_lay.addWidget(self.lbl_step)
        right_lay.addWidget(sol_group)

        act_group = QGroupBox("Actions"); act_lay = QVBoxLayout(act_group)
        btn_new = QPushButton("🎲 New Random Tsume"); btn_new.clicked.connect(self._load_random_tsume)
        btn_engine_mate = QPushButton("🤖 Engine Solve Mate"); btn_engine_mate.clicked.connect(self._engine_solve_mate)
        btn_export = QPushButton("🎬 Export Video…"); btn_export.clicked.connect(self._export_video)
        if not VIDEO_EXPORT_AVAILABLE: btn_export.setEnabled(False); btn_export.setToolTip("Install imageio[ffmpeg] and numpy")
        act_lay.addWidget(btn_new); act_lay.addWidget(btn_engine_mate); act_lay.addWidget(btn_export)
        right_lay.addWidget(act_group)

        self.lbl_engine_status = QLabel("Engine: Not Loaded"); self.lbl_engine_status.setStyleSheet("color: #cc5555; font-weight: bold;")
        right_lay.addWidget(self.lbl_engine_status)

        list_group = QGroupBox("Saved Puzzles"); list_lay = QVBoxLayout(list_group)
        self.puzzle_list = QListWidget(); self.puzzle_list.currentRowChanged.connect(self._on_puzzle_selected)
        list_lay.addWidget(self.puzzle_list)
        btn_del = QPushButton("Delete Selected"); btn_del.clicked.connect(self._delete_puzzle); list_lay.addWidget(btn_del)
        right_lay.addWidget(list_group)

        right_lay.addStretch()
        main_lay.addWidget(self.board_widget, 1); main_lay.addWidget(right_panel)
        self.statusBar().showMessage("Ready — Load YaneuraOu engine from the Engine menu for advanced solving.")

    # ------------------------------------------------------------------
    def _build_menus(self):
        menu_bar = self.menuBar()

        file_menu = menu_bar.addMenu("&File")
        act_load_sfen = QAction("Load &SFEN…", self); act_load_sfen.triggered.connect(self._load_sfen)
        act_save = QAction("&Save Puzzle…", self); act_save.triggered.connect(self._save_puzzle)
        act_quit = QAction("&Quit", self); act_quit.setShortcut(QKeySequence.Quit); act_quit.triggered.connect(self.close)
        file_menu.addAction(act_load_sfen); file_menu.addSeparator(); file_menu.addAction(act_save); file_menu.addSeparator(); file_menu.addAction(act_quit)

        engine_menu = menu_bar.addMenu("&Engine")
        act_load_engine = QAction("Load YaneuraOu…", self); act_load_engine.triggered.connect(self._load_engine)
        act_mate = QAction("Solve &Mate", self); act_mate.triggered.connect(self._engine_solve_mate)
        engine_menu.addAction(act_load_engine); engine_menu.addAction(act_mate)

    # ------------------------------------------------------------------
    #  YANEURAOU ENGINE INTEGRATION
    # ------------------------------------------------------------------
    def _load_engine(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select YaneuraOu Executable", "", "Executable Files (*.exe *);;All Files (*)")
        if path:
            self.statusBar().showMessage("Starting YaneuraOu...")
            if self.engine.start_engine(path):
                self.lbl_engine_status.setText("Engine: Initializing...")
                self.lbl_engine_status.setStyleSheet("color: #aaaa55; font-weight: bold;")
            else:
                self.lbl_engine_status.setText("Engine: Failed to Load")
                self.lbl_engine_status.setStyleSheet("color: #cc5555; font-weight: bold;")

    def _on_engine_ready(self):
        if not self.engine_loaded:
            self.engine_loaded = True
            self.engine.send_command("setoption name Threads value 2")
            self.engine.send_command("setoption name Hash value 256")
            self.lbl_engine_status.setText("Engine: Ready (YaneuraOu)")
            self.lbl_engine_status.setStyleSheet("color: #55aa55; font-weight: bold;")
            self.statusBar().showMessage("YaneuraOu engine loaded successfully.")
        else:
            self.statusBar().showMessage("Engine is ready.")

    def _on_engine_error(self, err_msg):
        self.statusBar().showMessage(f"Engine Error: {err_msg}")
        self.lbl_engine_status.setText("Engine: Error")
        self.lbl_engine_status.setStyleSheet("color: #cc5555; font-weight: bold;")

    def _engine_solve_mate(self):
        if not self.engine_loaded:
            QMessageBox.warning(self, "Engine Not Loaded", "Please load the YaneuraOu engine first (Engine -> Load YaneuraOu...).")
            return
        if not self.current_board: return

        sfen = self.current_board.to_sfen()
        self.statusBar().showMessage("Engine searching for mate...")
        self.engine.send_command("usinewgame")
        self.engine.send_command(f"position sfen {sfen}")
        # Search for mate up to depth 30 (or infinite depending on build)
        self.engine.send_command("go mate 30") 

    def _on_engine_checkmate(self, result_str: str):
        self.engine.send_command("gameover win")
        if result_str == "nomate" or result_str == "timeout":
            self.statusBar().showMessage(f"Engine result: {result_str}")
            QMessageBox.information(self, "Mate Search", f"Engine result: {result_str}")
            return

        # Parse USI moves e.g. "7g7f 8c8d ..."
        usi_moves = result_str.split()
        solution = []
        temp_board = self.current_board.copy()

        for usi_move in usi_moves:
            frm, to, promote, drop = ShogiBoard.usi_to_move(usi_move)
            move_dict = {"from": frm, "to": to, "promote": promote, "drop": drop}
            solution.append(move_dict)
            temp_board = temp_board.make_move(frm, to, promote=promote, drop=drop)

        self.current_solution = solution
        self.solution_step = 0
        self.initial_board = self.current_board.copy()
        self._update_step_label()
        self.statusBar().showMessage(f"Engine found mate in {len(solution)} moves!")
        self.lbl_difficulty.setText(str(len(solution)))

    def _on_engine_bestmove(self, move_str, ponder_str):
        self.engine.send_command("gameover win")
        self.statusBar().showMessage(f"Engine suggests: {move_str}")

    # ------------------------------------------------------------------
    #  Puzzle loading
    # ------------------------------------------------------------------
    def _load_random_tsume(self):
        self.statusBar().showMessage("Generating tsume-shogi… (Using built-in generator)")
        QApplication.processEvents()
        try:
            board, solution = TsumeGenerator.generate_random_tsume(max_depth=5)
            self._set_puzzle(board, solution, name="Random Tsume", category="tsume", difficulty=len(solution))
            self.statusBar().showMessage(f"Generated {len(solution)}-move tsume. Use Engine Solve for deeper/harder puzzles.")
        except Exception as e:
            QMessageBox.warning(self, "Error", f"Generation failed:\n{e}")

    def _set_puzzle(self, board, solution, name="", category="", difficulty=1):
        self.current_board = board; self.current_solution = solution; self.solution_step = 0; self.playing_solution = False
        self.initial_board = board.copy(); self.board_widget.set_board(board); self.board_widget.last_move = None
        self.lbl_puzzle_name.setText(name); self.lbl_difficulty.setText(str(difficulty)); self.lbl_category.setText(category)
        self._update_step_label()

    def _update_step_label(self):
        total = len(self.current_solution) if self.current_solution else 0
        self.lbl_step.setText(f"Step: {self.solution_step} / {total}")

    # ------------------------------------------------------------------
    #  Solution playback
    # ------------------------------------------------------------------
    def _play_solution(self):
        if not self.current_solution: return
        self.playing_solution = True; self.btn_play.setText("⏸ Pause")
        self.btn_play.clicked.disconnect(); self.btn_play.clicked.connect(self._pause_solution); self._auto_step()

    def _pause_solution(self):
        self.playing_solution = False; self.btn_play.setText("▶ Play")
        self.btn_play.clicked.disconnect(); self.btn_play.clicked.connect(self._play_solution)

    def _auto_step(self):
        if not self.playing_solution: return
        if self.solution_step >= len(self.current_solution): self._pause_solution(); return
        self._step_solution(); QTimer.singleShot(800, self._auto_step)

    def _step_solution(self):
        if not self.current_solution or self.solution_step >= len(self.current_solution): return
        move = self.current_solution[self.solution_step]
        frm = move.get("from"); to = move["to"]; promote = move.get("promote", False); drop = move.get("drop")
        self.current_board = self.current_board.make_move(frm, to, promote=promote, drop=drop)
        self.board_widget.set_board(self.current_board); self.board_widget.last_move = [frm, to]
        self.solution_step += 1; self._update_step_label()

    def _reset_solution(self):
        if self.initial_board:
            self.current_board = self.initial_board.copy(); self.solution_step = 0; self.playing_solution = False
            self.board_widget.set_board(self.current_board); self.board_widget.last_move = None
            self.btn_play.setText("▶ Play")
            try: self.btn_play.clicked.disconnect()
            except: pass
            self.btn_play.clicked.connect(self._play_solution); self._update_step_label()

    def _on_cell_clicked(self, r, c): self.board_widget.sel = (r, c); self.board_widget.update()
    def _on_hand_clicked(self, ow, tid): self.board_widget.sel_hand = (ow, tid); self.board_widget.update()

    # ------------------------------------------------------------------
    #  File I/O
    # ------------------------------------------------------------------
    def _load_sfen(self):
        text, ok = QInputDialog.getMultiLineText(self, "Load SFEN", "Enter SFEN string:", "lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b -")
        if ok and text.strip():
            try:
                board = ShogiBoard.from_sfen(text.strip()); self._set_puzzle(board, [], name="SFEN Import", category="import")
                self.statusBar().showMessage("SFEN loaded successfully")
            except Exception as e: QMessageBox.warning(self, "Error", f"Invalid SFEN:\n{e}")

    def _save_puzzle(self):
        if not self.current_board: return
        name, ok = QInputDialog.getText(self, "Save Puzzle", "Puzzle name:", text=self.lbl_puzzle_name.text())
        if ok and name:
            board_json = json.dumps(self.current_board.to_dict()); solution_json = json.dumps(self.current_solution) if self.current_solution else None
            sfen = self.current_board.to_sfen()
            self.db.add_puzzle(name, board_json, solution_json, sfen, category=self.lbl_category.text(), difficulty=int(self.lbl_difficulty.text() or "1"))
            self._refresh_puzzle_list(); self.statusBar().showMessage(f"Puzzle '{name}' saved")

    # ------------------------------------------------------------------
    #  VIDEO EXPORT
    # ------------------------------------------------------------------
    def _export_video(self):
        if not VIDEO_EXPORT_AVAILABLE: QMessageBox.warning(self, "Missing Dependency", "Install imageio[ffmpeg] and numpy"); return
        if not self.current_board or not self.current_solution: QMessageBox.information(self, "No Puzzle", "Load a puzzle with a solution first."); return

        dlg = VideoExportDialog(self, puzzle_name=self.lbl_puzzle_name.text() or "puzzle")
        if dlg.exec() != QDialog.Accepted: return

        preset_key = dlg.get_preset_key(); filepath = dlg.get_filepath(); fps = dlg.get_fps(); pause = dlg.get_pause(); slide = dlg.get_slide()
        preset = VIDEO_PRESETS[preset_key]; orient_label = "YouTube Shorts (Portrait)" if preset["orient"] == "portrait" else "YouTube (Landscape)"
        progress = QProgressDialog(f"Rendering {orient_label} {preset['w']}×{preset['h']}…", "Cancel", 0, 100, self)
        progress.setWindowTitle("Exporting Video"); progress.setWindowModality(Qt.WindowModal); progress.setMinimumDuration(0)

        try:
            PuzzleVideoExporter.export_to_mp4(initial_board=self.initial_board, solution_moves=self.current_solution, filepath=filepath, preset_key=preset_key, fps=fps, duration_pause=pause, duration_slide=slide)
            progress.setValue(100); self.statusBar().showMessage(f"Video exported: {filepath}")
            QMessageBox.information(self, "Export Complete", f"Video saved to:\n{filepath}\n\nFormat: {orient_label}\nResolution: {preset['w']}×{preset['h']}\nFPS: {fps}")
        except Exception as e:
            progress.close(); QMessageBox.critical(self, "Export Error", f"Failed to export video:\n{e}")

    # ------------------------------------------------------------------
    #  Puzzle List
    # ------------------------------------------------------------------
    def _refresh_puzzle_list(self):
        self.puzzle_list.clear(); puzzles = self.db.list_puzzles()
        for p in puzzles:
            item = QListWidgetItem(f"#{p['id']}  {p['name']}  (★{p['difficulty']})"); item.setData(Qt.UserRole, p['id']); self.puzzle_list.addItem(item)

    def _on_puzzle_selected(self, row):
        if row < 0: return
        item = self.puzzle_list.item(row)
        if not item: return
        pid = item.data(Qt.UserRole); data = self.db.get_puzzle(pid)
        if data:
            board = ShogiBoard.from_dict(json.loads(data["board_json"])); solution = json.loads(data["solution_json"]) if data["solution_json"] else []
            self._set_puzzle(board, solution, name=data["name"], category=data["category"], difficulty=data["difficulty"])

    def _delete_puzzle(self):
        row = self.puzzle_list.currentRow()
        if row < 0: return
        item = self.puzzle_list.item(row)
        if not item: return
        pid = item.data(Qt.UserRole)
        if QMessageBox.question(self, "Delete Puzzle", "Are you sure?", QMessageBox.Yes | QMessageBox.No, QMessageBox.No) == QMessageBox.Yes:
            self.db.delete_puzzle(pid); self._refresh_puzzle_list(); self.statusBar().showMessage("Puzzle deleted")

    def closeEvent(self, event):
        if self.engine_loaded: self.engine.quit()
        self.db.conn.close(); super().closeEvent(event)


# ══════════════════════════════════════════════════════════════════════════════
#  APPLICATION ENTRY POINT
# ══════════════════════════════════════════════════════════════════════════════
if __name__ == "__main__":
    app = QApplication(sys.argv)
    app.setStyle("Fusion"); app.setFont(QFont("Segoe UI", 10))
    window = ShogiMainWindow()
    window.show()
    sys.exit(app.exec())