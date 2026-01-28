
import os
import sys
import math
import json
import copy
import platform
import time
import threading
import traceback
import queue
import itertools
from typing import List, Dict, Optional, Tuple, Any
from dataclasses import dataclass, field, asdict
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, colorchooser, Canvas

from PIL import Image, ImageTk, ImageOps, ImageDraw, ImageFont
import customtkinter as ctk

# --- Constants & Defaults ---
CONFIG_FILE = "config.json"
DEFAULT_CONFIG = {
    "auto_save_enabled": False,
    "auto_save_interval": 5, # minutes
    "startup_cover_mode": False,
    "startup_export_fmt": "PDF",
    "snap_enabled": True,
    "zoom_sensitivity": 1.1,
    "export_dpi": 300,
    "export_bleed_mm": 0.0,
    "export_quality": 95,
    "export_crop_marks": False,
    "preview_quality": "medium",
    "default_image_folder": "",
    "default_margin_top": 15.0,
    "default_margin_bottom": 15.0,
    "default_margin_inner": 15.0,
    "default_margin_outer": 15.0
}

MM_TO_INCH = 1 / 25.4

PAPER_SIZES = {
    "A0": (841, 1189), "A1": (594, 841), "A2": (420, 594), "A3": (297, 420),
    "A4": (210, 297), "A5": (148, 210), "A6": (105, 148), "B4": (257, 364),
    "B5": (182, 257), "Hagaki": (100, 148), "L-Size": (89, 127), "2L-Size": (127, 178)
}
PAPER_KEYS = sorted(PAPER_SIZES.keys())
IMG_EXTS = (".jpg", ".jpeg", ".png", ".bmp", ".webp")

# Colors
COLOR_BG_MAIN = "#121212"
COLOR_BG_SEC = "#1e1e1e"
COLOR_BG_TER = "#252525"
COLOR_FG_TEXT = "#eeeeee"
COLOR_FG_DIM = "#aaaaaa"
COLOR_BTN_NORM = "#333333"
COLOR_BTN_HOVER = "#444444"
COLOR_ORANGE_MAIN = "#E68A2E"
COLOR_ORANGE_HOVER = "#F09C45"
COLOR_RED_LIGHT = "#E56B6F"
COLOR_RED_HOVER = "#FF7D82"
COLOR_HIGHLIGHT = "#E68A2E"
COLOR_MENU_BG = "#000000"

# --- Font Helpers ---
def get_system_fonts():
    if platform.system() == "Windows":
        return ["Meiryo UI", "Yu Gothic UI", "Segoe UI", "Arial"]
    elif platform.system() == "Darwin":
        return ["Helvetica Neue", "Hiragino Sans", "Arial"]
    else:
        return ["Noto Sans", "DejaVu Sans", "FreeSans"]

def load_font(family, size):
    try: return ImageFont.truetype(family, size)
    except: return ImageFont.load_default()

# --- Data Models ---
@dataclass
class CropInfo:
    left: float = 0.0; top: float = 0.0; right: float = 1.0; bottom: float = 1.0

@dataclass
class PhotoItem:
    path: str; slot_index: int = 0; rotation: int = 0; crop: CropInfo = field(default_factory=CropInfo)

@dataclass
class TextItem:
    text: str; x_rel: float = 0.5; y_rel: float = 0.5; font_size: int = 40
    color: str = "#000000"; font_family: str = "Arial"; rotation: int = 0; uuid: str = ""
    def __post_init__(self):
        if not self.uuid: import uuid; self.uuid = str(uuid.uuid4())

@dataclass
class Page:
    layout_name: str = "1枚 (全面)"; spacing_mm: float = 0.0; background_color: str = "#FFFFFF"
    photos: List[PhotoItem] = field(default_factory=list); texts: List[TextItem] = field(default_factory=list)
    custom_margins: Optional[Dict[str, float]] = None 

@dataclass
class Project:
    paper_size: str = "A4"; orientation: str = "Portrait"
    margin_top: float = 15.0; margin_bottom: float = 15.0; margin_inner: float = 15.0; margin_outer: float = 15.0
    pages: List[Page] = field(default_factory=list); current_spread_index: int = 0

class LayoutManager:
    LAYOUTS = {
        "1枚 (全面)": [(0.0, 0.0, 1.0, 1.0)], "1枚 (中央)": [(0.1, 0.1, 0.8, 0.8)],
        "2枚 (縦並び)": [(0.0, 0.0, 1.0, 0.5), (0.0, 0.5, 1.0, 0.5)], "2枚 (横並び)": [(0.0, 0.0, 0.5, 1.0), (0.5, 0.0, 0.5, 1.0)],
        "3枚 (分割)": [(0.0, 0.0, 1.0, 0.5), (0.0, 0.5, 0.5, 0.5), (0.5, 0.5, 0.5, 0.5)],
        "4枚 (グリッド)": [(0.0, 0.0, 0.5, 0.5), (0.5, 0.0, 0.5, 0.5), (0.0, 0.5, 0.5, 0.5), (0.5, 0.5, 0.5, 0.5)],
        "6枚 (グリッド)": [(0.0, 0.0, 0.5, 0.333), (0.5, 0.0, 0.5, 0.333), (0.0, 0.333, 0.5, 0.333), (0.5, 0.333, 0.5, 0.333), (0.0, 0.666, 0.5, 0.333), (0.5, 0.666, 0.5, 0.333)],
    }
    @staticmethod
    def get_layout_rects(name): return LayoutManager.LAYOUTS.get(name, [(0,0,1,1)])

# --- HBS Viewer Class (Integrated) ---
class HBSViewer(ctk.CTkToplevel):
    def __init__(self, parent=None, project_data=None):
        super().__init__(parent)
        self.title("HomeBook Viewer v5.0")
        self.geometry("1400x950")
        
        # 親ウィンドウがある場合の処理
        if parent:
            try:
                self.transient(parent)
                self.lift()
            except: pass

        # Theme Setup
        ctk.set_appearance_mode("Dark")
        ctk.set_default_color_theme("dark-blue")
        
        # UI Font Setup
        sys_font = get_system_fonts()[0]
        self.ui_font = (sys_font, 12)
        self.ui_font_sm = (sys_font, 11)
        self.ui_font_bold = (sys_font, 12, "bold")
        self.ui_font_header = (sys_font, 18, "bold")

        # State
        self.project = project_data # 初期データ
        self.current_page_idx = 0  
        self.is_single_view = False 
        self.is_cover_mode = False 
        
        self.is_fullscreen = False
        self.is_maximized = False
        self.zoom_scale = 1.0
        self.pan_start_x = 0
        self.pan_start_y = 0
        
        self.is_slideshow_running = False
        self.slideshow_timer = None
        self.is_grid_mode = False
        self.is_running = True

        # Cache & Async Loader
        # cache stores ImageTk.PhotoImage directly
        self.image_cache = {}
        self.load_queue = queue.PriorityQueue()
        self.task_counter = itertools.count() 

        self.mini_thumb_frames = {} 

        self.loader_thread = threading.Thread(target=self._image_loader_worker, daemon=True)
        self.loader_thread.start()

        self._build_ui()
        self._bind_events()

        # 初期データがある場合の描画
        if self.project:
            self.lbl_filename.configure(text="プレビュー中", text_color=COLOR_FG_TEXT)
            self.btn_grid.configure(state="normal")
            self.btn_view_mode.configure(state="normal")
            self.btn_slideshow.configure(state="normal")
            self._init_mini_viewer()
            self._update_nav_state()
            self._draw_main_view()

    def destroy(self):
        self.is_running = False
        super().destroy()

    def update_project_data(self, project_obj):
        """HBS.py からプロジェクトデータを受け取り、画面を更新する"""
        if not self.winfo_exists(): return

        # プロジェクトデータを更新
        self.project = project_obj
        
        # ページ数が減って現在のページが存在しなくなった場合の補正
        if self.project and self.project.pages:
            total_pages = len(self.project.pages)
            if self.current_page_idx >= total_pages:
                self.current_page_idx = max(0, total_pages - 1)
        else:
            self.current_page_idx = 0

        # UI有効化
        self.lbl_filename.configure(text="同期中...", text_color=COLOR_ORANGE_MAIN)
        self.btn_grid.configure(state="normal")
        self.btn_view_mode.configure(state="normal")
        self.btn_slideshow.configure(state="normal")

        # 再描画
        # キャッシュをクリアせず、新しい内容で更新
        self._init_mini_viewer()
        if self.is_grid_mode:
            self._fill_grid()
        else:
            self._draw_main_view()
        
        self._update_nav_state()
        self.lbl_filename.configure(text="プレビュー (同期済み)", text_color=COLOR_FG_TEXT)

    def _bind_events(self):
        self.bind("<Left>", lambda e: self._prev_page())
        self.bind("<Right>", lambda e: self._next_page())
        self.bind("<space>", lambda e: self._next_page())
        self.bind("<Home>", lambda e: self._go_first())
        self.bind("<End>", lambda e: self._go_last())
        self.bind("<F11>", lambda e: self._toggle_fullscreen())
        self.bind("<Escape>", lambda e: self._on_escape())
        
        # Mouse Wheel Zoom
        self.canvas.bind("<MouseWheel>", self._on_mouse_wheel)
        self.canvas.bind("<Button-4>", lambda e: self._on_mouse_wheel(e, 120))
        self.canvas.bind("<Button-5>", lambda e: self._on_mouse_wheel(e, -120))
        
        # Pan
        self.canvas.bind("<ButtonPress-1>", self._on_pan_start)
        self.canvas.bind("<B1-Motion>", self._on_pan_move)

    def _image_loader_worker(self):
        """
        画像を別スレッドでロードし、PILオブジェクトを作成する。
        ImageTkへの変換はメインスレッドで行うことで、表示バグを防ぐ。
        """
        while self.is_running:
            try:
                priority, _, req = self.load_queue.get(timeout=0.1)
                
                canvas, tag_id, path, w, h, rotation = req
                cache_key = (path, w, h, rotation)
                
                # キャッシュにあれば即座に適用（通常ここには来ないが念のため）
                if cache_key in self.image_cache:
                    tk_img = self.image_cache[cache_key]
                    self.after(0, lambda c=canvas, t=tag_id, img=tk_img: self._set_image_on_canvas(c, t, img))
                    self.load_queue.task_done()
                    continue

                pil_img = None
                if os.path.exists(path):
                    try:
                        pil = Image.open(path)
                        if rotation: pil = pil.rotate(-rotation, expand=True)
                        # Mini Viewerなどでサイズが極端に小さい場合のエラー回避
                        w = max(1, int(w))
                        h = max(1, int(h))
                        pil.thumbnail((w, h), Image.LANCZOS)
                        pil_img = pil
                    except: pass
                
                # メインスレッドで ImageTk に変換して描画
                if pil_img:
                    self.after(0, lambda c=canvas, t=tag_id, p=pil_img, k=cache_key: self._update_canvas_image(c, t, p, k))
                
                self.load_queue.task_done()
            except queue.Empty:
                continue
            except Exception as e:
                # print(f"Loader error: {e}")
                pass

    def _update_canvas_image(self, canvas, tag_id, pil_img, cache_key):
        """メインスレッドで実行: PIL画像をImageTkに変換してキャッシュし、Canvasにセット"""
        try:
            tk_img = ImageTk.PhotoImage(pil_img)
            self.image_cache[cache_key] = tk_img
            self._set_image_on_canvas(canvas, tag_id, tk_img)
        except Exception as e:
            # ウィンドウが閉じられた場合などに発生するエラーを無視
            pass

    def _set_image_on_canvas(self, canvas, tag_id, tk_img):
        """実際にCanvasアイテムを更新する"""
        try:
            if canvas.winfo_exists():
                canvas.itemconfig(tag_id, image=tk_img)
                # 参照を保持しないとガベージコレクションで消える
                if not hasattr(canvas, "keep_refs"): canvas.keep_refs = []
                canvas.keep_refs.append(tk_img)
                # 強制再描画（MiniViewerの更新ラグ対策）
                canvas.update_idletasks()
        except: pass

    def _build_ui(self):
        # Configure Grid Layout (Row 1 is main content)
        self.grid_rowconfigure(1, weight=1)
        self.grid_columnconfigure(0, weight=1)

        # --- HEADER (Black Strip) ---
        header = ctk.CTkFrame(self, height=40, fg_color=COLOR_BG_MAIN, corner_radius=0)
        header.grid(row=0, column=0, sticky="ew")
        header.pack_propagate(False)

        # Left: App Logo/Title & Open Button
        left_box = ctk.CTkFrame(header, fg_color="transparent")
        left_box.pack(side="left", padx=10, fill="y")
        
        ctk.CTkLabel(left_box, text="HBS Viewer", font=self.ui_font_header, text_color=COLOR_FG_TEXT).pack(side="left", padx=(0, 15))
        
        btn_style = {
            "font": self.ui_font, "fg_color": COLOR_BTN_NORM, "hover_color": COLOR_BTN_HOVER, 
            "text_color": COLOR_FG_TEXT, "height": 28, "corner_radius": 4
        }
        ctk.CTkButton(left_box, text="📂 ファイルを開く", command=self._load_file, width=120, **btn_style).pack(side="left")

        # Center: Filename
        self.lbl_filename = ctk.CTkLabel(header, text="プロジェクト未読み込み", font=self.ui_font, text_color=COLOR_FG_DIM)
        self.lbl_filename.pack(side="left", fill="x", expand=True)

        # Right: Controls
        right_box = ctk.CTkFrame(header, fg_color="transparent")
        right_box.pack(side="right", padx=10)

        # Control Buttons Style
        ctrl_btn_style = {
            "width": 80, "height": 28, "font": self.ui_font, "fg_color": "transparent", 
            "hover_color": COLOR_BTN_HOVER, "text_color": COLOR_FG_TEXT, "border_width": 1, "border_color": COLOR_BTN_NORM
        }

        self.btn_grid = ctk.CTkButton(right_box, text="田 一覧", command=self._toggle_grid_mode, state="disabled", **ctrl_btn_style)
        self.btn_grid.pack(side="left", padx=2)

        self.btn_view_mode = ctk.CTkButton(right_box, text="単ページ", command=self._toggle_view_mode, state="disabled", **ctrl_btn_style)
        self.btn_view_mode.pack(side="left", padx=2)

        # Zoom Reset
        ctk.CTkButton(right_box, text="100%", command=self._reset_zoom, **{**ctrl_btn_style, "width": 50}).pack(side="left", padx=2)

        # Maximize Button (Added Feature)
        self.btn_maximize = ctk.CTkButton(right_box, text="□", command=self._toggle_maximize, **{**ctrl_btn_style, "width": 40})
        self.btn_maximize.pack(side="left", padx=2)

        # Slideshow
        ss_frame = ctk.CTkFrame(right_box, fg_color="transparent")
        ss_frame.pack(side="left", padx=10)
        
        self.btn_slideshow = ctk.CTkButton(ss_frame, text="▶ 再生", width=70, height=28, command=self._toggle_slideshow, state="disabled", 
                                           fg_color=COLOR_ORANGE_MAIN, hover_color=COLOR_ORANGE_HOVER, text_color="white", font=self.ui_font_bold)
        self.btn_slideshow.pack(side="left", padx=2)
        
        self.entry_interval = ctk.CTkEntry(ss_frame, width=40, height=28, fg_color=COLOR_BTN_NORM, border_width=0, text_color="white", justify="center")
        self.entry_interval.insert(0, "3")
        self.entry_interval.pack(side="left", padx=2)
        ctk.CTkLabel(ss_frame, text="秒", font=self.ui_font_sm, text_color=COLOR_FG_DIM).pack(side="left")

        self.cb_cover_mode = ctk.CTkCheckBox(right_box, text="表紙", command=self._toggle_cover_mode, 
                                             font=self.ui_font_sm, text_color=COLOR_FG_TEXT, hover_color=COLOR_ORANGE_MAIN, fg_color=COLOR_BG_MAIN)
        self.cb_cover_mode.pack(side="right", padx=10)

        # --- CENTER (Main Canvas) ---
        self.center_container = ctk.CTkFrame(self, fg_color=COLOR_BG_SEC, corner_radius=0)
        self.center_container.grid(row=1, column=0, sticky="nsew")

        self.single_view_frame = ctk.CTkFrame(self.center_container, fg_color="transparent")
        self.single_view_frame.pack(fill="both", expand=True)
        
        self.canvas = Canvas(self.single_view_frame, bg="#202020", highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Configure>", lambda e: self._delayed_redraw())

        self.grid_view_frame = ctk.CTkScrollableFrame(self.center_container, orientation="vertical", fg_color=COLOR_BG_SEC)

        # --- FOOTER ---
        self.footer_area = ctk.CTkFrame(self, fg_color=COLOR_BG_MAIN, corner_radius=0)
        self.footer_area.grid(row=2, column=0, sticky="ew")

        # Navigation Bar
        nav_bar = ctk.CTkFrame(self.footer_area, height=40, fg_color=COLOR_BG_MAIN)
        nav_bar.pack(fill="x", padx=10, pady=5)
        
        nav_btn_style = {"width": 40, "height": 30, "fg_color": "transparent", "hover_color": COLOR_BTN_HOVER, "text_color": COLOR_FG_TEXT, "font": self.ui_font_bold}
        
        # Center Navigation Group
        nav_center = ctk.CTkFrame(nav_bar, fg_color="transparent")
        nav_center.pack(anchor="center")
        
        self.btn_prev = ctk.CTkButton(nav_center, text="<", command=self._prev_page, state="disabled", **nav_btn_style)
        self.btn_prev.pack(side="left", padx=5)

        self.entry_page_nav = ctk.CTkEntry(nav_center, width=50, justify="center", font=self.ui_font, 
                                           fg_color=COLOR_BTN_NORM, border_width=0, text_color="white")
        self.entry_page_nav.pack(side="left", padx=5)
        self.entry_page_nav.bind("<Return>", self._on_page_entry_submit)

        self.lbl_page_total = ctk.CTkLabel(nav_center, text="/ --", font=self.ui_font_bold, text_color=COLOR_FG_DIM)
        self.lbl_page_total.pack(side="left", padx=5)

        self.btn_next = ctk.CTkButton(nav_center, text=">", command=self._next_page, state="disabled", **nav_btn_style)
        self.btn_next.pack(side="left", padx=5)

        # Mini Viewer Area
        self.mini_viewer_frame = ctk.CTkScrollableFrame(self.footer_area, orientation="horizontal", height=110, fg_color=COLOR_BG_TER)
        self.mini_viewer_frame.pack(fill="x", padx=0, pady=0)
        
        self.redraw_timer = None

    # --- Event Handlers (Modified for Fullscreen/Maximize) ---
    def _on_escape(self):
        if self.is_fullscreen: self._toggle_fullscreen()
        elif self.is_grid_mode: self._toggle_grid_mode()

    def _toggle_fullscreen(self):
        self.is_fullscreen = not self.is_fullscreen
        self.attributes("-fullscreen", self.is_fullscreen)
        # フルスクリーン解除時に元のサイズに戻す
        if not self.is_fullscreen:
            # 最大化状態だった場合は最大化に戻す（OS依存の挙動を考慮）
            if self.is_maximized and platform.system() == "Windows":
                self.state("zoomed")

    def _toggle_maximize(self):
        """ウィンドウ最大化の切り替え"""
        if platform.system() == "Windows":
            if self.state() == "zoomed":
                self.state("normal")
                self.is_maximized = False
            else:
                self.state("zoomed")
                self.is_maximized = True
        else:
            # macOS/Linux (簡易実装)
            self.is_maximized = not self.is_maximized
            self.attributes("-zoomed", self.is_maximized)

    def _on_mouse_wheel(self, event, linux_delta=None):
        if not self.project or self.is_grid_mode: return
        if linux_delta: delta = linux_delta
        else: delta = event.delta
        scale_amount = 1.1 if delta > 0 else 0.9
        self.zoom_scale *= scale_amount
        if self.zoom_scale < 0.5: self.zoom_scale = 0.5
        if self.zoom_scale > 5.0: self.zoom_scale = 5.0
        self._draw_main_view()

    def _reset_zoom(self):
        self.zoom_scale = 1.0
        self._draw_main_view()

    def _on_pan_start(self, event):
        self.pan_start_x = event.x
        self.pan_start_y = event.y

    def _on_pan_move(self, event):
        if self.zoom_scale <= 1.0: return 
        dx = event.x - self.pan_start_x
        dy = event.y - self.pan_start_y
        self.canvas.move("all", dx, dy)
        self.pan_start_x = event.x
        self.pan_start_y = event.y

    def _delayed_redraw(self):
        if self.redraw_timer: self.after_cancel(self.redraw_timer)
        self.redraw_timer = self.after(150, self._draw_main_view)

    # --- Loading Logic ---
    def _load_file(self):
        path = filedialog.askopenfilename(filetypes=[("HBS Project", "*.hbs")])
        if not path: return
        
        try:
            self.image_cache.clear()
            try:
                while not self.load_queue.empty():
                    self.load_queue.get_nowait()
                    self.load_queue.task_done() 
            except: pass

            with open(path, "r", encoding="utf-8") as f: data = json.load(f)
            
            # Use safe get with defaults corresponding to HBS.py structure
            self.project = Project(
                paper_size=data.get("paper_size", "A4"), orientation=data.get("orientation", "Portrait"),
                margin_top=data.get("margin_top", 15.0), margin_bottom=data.get("margin_bottom", 15.0),
                margin_inner=data.get("margin_inner", 20.0), margin_outer=data.get("margin_outer", 15.0),
                pages=[]
            )
            for p in data.get("pages", []):
                pg = Page(layout_name=p.get("layout_name", "1枚 (全面)"), spacing_mm=p.get("spacing_mm", 0.0), 
                          background_color=p.get("background_color", "#FFFFFF"), custom_margins=p.get("custom_margins"))
                for ph in p.get("photos", []):
                    pg.photos.append(PhotoItem(path=ph["path"], slot_index=ph.get("slot_index", 0), rotation=ph.get("rotation", 0)))
                for txt in p.get("texts", []):
                    pg.texts.append(TextItem(text=txt["text"], x_rel=txt["x_rel"], y_rel=txt["y_rel"], font_size=txt.get("font_size", 40), 
                                           color=txt.get("color", "black"), rotation=txt.get("rotation", 0)))
                self.project.pages.append(pg)

            self.lbl_filename.configure(text=os.path.basename(path), text_color=COLOR_FG_TEXT)
            self.btn_grid.configure(state="normal")
            self.btn_view_mode.configure(state="normal")
            self.btn_slideshow.configure(state="normal")
            
            self.current_page_idx = 0
            self.zoom_scale = 1.0
            
            self._init_mini_viewer()
            self._init_grid_view() 
            
            self._update_nav_state()
            self._draw_main_view()
            
        except Exception as e:
            messagebox.showerror("エラー", f"読込失敗: {e}")
            import traceback
            traceback.print_exc()

    # --- Drawing ---
    def _draw_main_view(self):
        if not self.project: return
        w = self.canvas.winfo_width()
        h = self.canvas.winfo_height()
        if w < 10: return
        self._draw_pages_on_canvas(self.canvas, self.current_page_idx, w, h, is_thumbnail=False, priority=0)

    def _draw_pages_on_canvas(self, target_canvas: Canvas, start_idx: int, w: int, h: int, is_thumbnail: bool, priority: int):
        target_canvas.delete("all")
        target_canvas.keep_refs = [] 
        
        size_key = self.project.paper_size if self.project.paper_size in PAPER_SIZES else "A4"
        pw_mm, ph_mm = PAPER_SIZES[size_key]
        if self.project.orientation == "Landscape": pw_mm, ph_mm = ph_mm, pw_mm
        
        # Cover Mode Logic
        pages_to_draw = []
        is_cover_page = False

        if self.is_single_view:
            pages_to_draw = [start_idx]
            spread_ratio = pw_mm / ph_mm
        else:
            if self.is_cover_mode:
                if start_idx == 0:
                    pages_to_draw = [0]
                    is_cover_page = True
                    spread_ratio = (pw_mm * 2) / ph_mm
                else:
                    if start_idx % 2 == 0: start_idx -= 1
                    pages_to_draw = [start_idx, start_idx + 1]
                    spread_ratio = (pw_mm * 2) / ph_mm
            else:
                idx_left = (start_idx // 2) * 2
                pages_to_draw = [idx_left, idx_left + 1]
                spread_ratio = (pw_mm * 2) / ph_mm

        pages_to_draw = [p for p in pages_to_draw if p < len(self.project.pages)]

        eff_w = w * (self.zoom_scale if not is_thumbnail else 1.0)
        eff_h = h * (self.zoom_scale if not is_thumbnail else 1.0)

        canvas_ratio = eff_w / eff_h
        
        if canvas_ratio > spread_ratio:
            draw_h = eff_h * 0.95
            draw_w = draw_h * spread_ratio
        else:
            draw_w = eff_w * 0.95
            draw_h = draw_w / spread_ratio
            
        cx = w / 2
        cy = h / 2
        x0 = cx - draw_w / 2
        y0 = cy - draw_h / 2
        
        if self.is_single_view:
            p_w = draw_w
        else:
            p_w = draw_w / 2
            
        scale = p_w / pw_mm

        # Spine Shadow
        if not is_thumbnail and not self.is_single_view and len(pages_to_draw) == 2:
            spine_x = cx
            shadow_colors = ["#333", "#383838", "#444"]
            for i, col in enumerate(shadow_colors):
                target_canvas.create_line(spine_x - i, y0, spine_x - i, y0+draw_h, fill=col, width=1)
            target_canvas.create_line(spine_x, y0, spine_x, y0+draw_h, fill="#222", width=1)

        for i, p_idx in enumerate(pages_to_draw):
            page = self.project.pages[p_idx]
            
            if self.is_single_view:
                px = x0
            else:
                if self.is_cover_mode:
                    if p_idx == 0: # Cover is on Right
                        px = x0 + p_w 
                    else:
                        px = x0 + (i * p_w)
                else:
                    px = x0 + (i * p_w)

            target_canvas.create_rectangle(px, y0, px+p_w, y0+draw_h, fill=page.background_color, outline="#333")
            
            mt, mb, mi, mo = (page.custom_margins["top"], page.custom_margins["bottom"], page.custom_margins["inner"], page.custom_margins["outer"]) if page.custom_margins else (self.project.margin_top, self.project.margin_bottom, self.project.margin_inner, self.project.margin_outer)
            
            is_left = False
            if self.is_single_view:
                is_left = (p_idx % 2 == 0)
            else:
                if self.is_cover_mode:
                    if p_idx == 0: is_left = False
                    else: is_left = (p_idx % 2 != 0)
                else:
                    is_left = (p_idx % 2 == 0)

            if is_left:
                safe = (px + mo*scale, y0 + mt*scale, px + p_w - mi*scale, y0 + draw_h - mb*scale)
            else:
                safe = (px + mi*scale, y0 + mt*scale, px + p_w - mo*scale, y0 + draw_h - mb*scale)

            sw, sh = safe[2]-safe[0], safe[3]-safe[1]
            if not is_thumbnail: target_canvas.create_rectangle(*safe, outline="#ddd", dash=(2,4))
            
            rects = LayoutManager.get_layout_rects(page.layout_name)
            sp_px = page.spacing_mm * scale
            
            for r_idx, (rx, ry, rw, rh) in enumerate(rects):
                sx = safe[0] + rx * sw + sp_px/2
                sy = safe[1] + ry * sh + sp_px/2
                slot_w = rw * sw - sp_px
                slot_h = rh * sh - sp_px
                
                # スロットサイズが正の値であることを保証
                if slot_w > 0 and slot_h > 0:
                    placeholder_id = target_canvas.create_image(sx + slot_w/2, sy + slot_h/2, image="")
                    target_canvas.create_rectangle(sx, sy, sx+slot_w, sy+slot_h, outline="#eee", width=1)
                    
                    photo = next((p for p in page.photos if p.slot_index == r_idx), None)
                    if photo:
                        cache_key = (photo.path, slot_w, slot_h, photo.rotation)
                        if cache_key in self.image_cache:
                            img = self.image_cache[cache_key]
                            target_canvas.itemconfig(placeholder_id, image=img)
                            target_canvas.keep_refs.append(img)
                        elif os.path.exists(photo.path):
                            self.load_queue.put((priority, next(self.task_counter), (target_canvas, placeholder_id, photo.path, slot_w, slot_h, photo.rotation)))
                        else:
                            target_canvas.create_text(sx+slot_w/2, sy+slot_h/2, text="!", fill="red")

            if not is_thumbnail or w > 200:
                for txt in page.texts:
                    f_size = int(txt.font_size * 0.7 * self.zoom_scale) if is_thumbnail else int(txt.font_size * self.zoom_scale)
                    pos_x = px + txt.x_rel * p_w
                    pos_y = y0 + txt.y_rel * draw_h
                    target_canvas.create_text(pos_x, pos_y, text=txt.text, fill=txt.color, font=(txt.font_family, max(8, f_size)))

    # --- Feature: Cover Mode Toggle ---
    def _toggle_cover_mode(self):
        self.is_cover_mode = bool(self.cb_cover_mode.get())
        self.current_page_idx = 0
        self._init_mini_viewer() 
        self._update_nav_state()
        self._draw_main_view()

    # --- Feature: Single/Spread Toggle ---
    def _toggle_view_mode(self):
        self.is_single_view = not self.is_single_view
        if self.is_single_view:
            self.btn_view_mode.configure(text="見開き")
            self.cb_cover_mode.pack_forget()
        else:
            self.btn_view_mode.configure(text="単ページ")
            self.cb_cover_mode.pack(side="right", padx=10)
            if self.current_page_idx > 0 and self.current_page_idx % 2 != 0:
                self.current_page_idx -= 1
        
        self.zoom_scale = 1.0 
        self._update_nav_state()
        self._draw_main_view()

    # --- Feature: Grid ---
    def _toggle_grid_mode(self):
        if not self.project: return
        self.is_grid_mode = not self.is_grid_mode
        if self.is_grid_mode:
            self.btn_grid.configure(text="戻る", fg_color=COLOR_ORANGE_MAIN, text_color="white")
            self.single_view_frame.pack_forget()
            self.grid_view_frame.pack(fill="both", expand=True)
            self._fill_grid()
        else:
            self.btn_grid.configure(text="田 一覧", fg_color="transparent", text_color=COLOR_FG_TEXT)
            self.grid_view_frame.pack_forget()
            self.single_view_frame.pack(fill="both", expand=True)
            self._draw_main_view()

    def _fill_grid(self):
        for w in self.grid_view_frame.winfo_children(): w.destroy()
        
        total_pages = len(self.project.pages)
        spreads = []
        
        if self.is_cover_mode:
            spreads.append([0])
            for i in range(1, total_pages, 2):
                if i+1 < total_pages: spreads.append([i, i+1])
                else: spreads.append([i])
        else:
            for i in range(0, total_pages, 2):
                if i+1 < total_pages: spreads.append([i, i+1])
                else: spreads.append([i])

        cols = 3
        
        for s_idx, pages in enumerate(spreads):
            row, col = s_idx // cols, s_idx % cols
            frame = ctk.CTkFrame(self.grid_view_frame, fg_color=COLOR_BG_TER, border_width=1, border_color="#444")
            frame.grid(row=row, column=col, padx=15, pady=15, sticky="nsew")
            
            cv = Canvas(frame, width=320, height=200, bg="#333", highlightthickness=0)
            cv.pack(padx=5, pady=5)
            
            p_start = pages[0]
            self._draw_pages_on_canvas(cv, p_start, 320, 200, is_thumbnail=True, priority=1)
            
            cv.bind("<Button-1>", lambda e, idx=p_start: self._jump_to_page(idx))
            
            lbl_txt = f"Page {pages[0]+1}"
            if len(pages) > 1: lbl_txt += f" - {pages[1]+1}"
            
            ctk.CTkLabel(frame, text=lbl_txt, font=self.ui_font_bold, text_color=COLOR_FG_TEXT).pack(pady=5)

    def _init_grid_view(self):
        pass

    # --- Mini Viewer & Sync Logic ---
    def _init_mini_viewer(self):
        for w in self.mini_viewer_frame.winfo_children(): w.destroy()
        self.mini_thumb_frames = {} 
        if not self.project: return
        
        total_pages = len(self.project.pages)
        spreads = []
        if self.is_cover_mode:
            spreads.append([0])
            for i in range(1, total_pages, 2):
                spreads.append([i] if i+1 >= total_pages else [i, i+1])
        else:
            for i in range(0, total_pages, 2):
                spreads.append([i] if i+1 >= total_pages else [i, i+1])
        
        for s_idx, pages in enumerate(spreads):
            frame = ctk.CTkFrame(self.mini_viewer_frame, fg_color="transparent", border_width=2, border_color=COLOR_BG_TER)
            frame.pack(side="left", padx=2, pady=5)
            
            self.mini_thumb_frames[tuple(pages)] = frame 
            
            cv = Canvas(frame, width=120, height=80, bg="#222", highlightthickness=0)
            cv.pack(padx=2, pady=2)
            
            p_start = pages[0]
            self._draw_pages_on_canvas(cv, p_start, 120, 80, is_thumbnail=True, priority=1)
            
            cv.bind("<Button-1>", lambda e, idx=p_start: self._jump_to_page(idx))
            frame.bind("<Button-1>", lambda e, idx=p_start: self._jump_to_page(idx))
            
            lbl_txt = f"{pages[0]+1}"
            if len(pages) > 1: lbl_txt += f"-{pages[1]+1}"
            ctk.CTkLabel(frame, text=lbl_txt, font=("Arial", 10), text_color=COLOR_FG_DIM).pack()

    # --- Feature: Page Jump (Inline) ---
    def _on_page_entry_submit(self, event=None):
        if not self.project: return
        try:
            val = int(self.entry_page_nav.get())
            total = len(self.project.pages)
            if 1 <= val <= total:
                self._jump_to_page(val - 1)
                self.canvas.focus_set()
            else:
                self._update_nav_state()
        except ValueError:
            self._update_nav_state()

    # --- Navigation ---
    def _jump_to_page(self, p_idx):
        self.current_page_idx = p_idx
        if self.is_grid_mode: self._toggle_grid_mode()
        self._update_nav_state()
        self._draw_main_view()

    def _prev_page(self):
        step = 1 if self.is_single_view else 2
        if self.is_cover_mode and not self.is_single_view:
            if self.current_page_idx == 0: return
            if self.current_page_idx == 1: 
                self.current_page_idx = 0
            else:
                self.current_page_idx -= 2
        else:
            if self.current_page_idx > 0:
                self.current_page_idx = max(0, self.current_page_idx - step)
                if not self.is_single_view and self.current_page_idx % 2 != 0:
                    self.current_page_idx -= 1
                    
        self._update_nav_state()
        self._draw_main_view()

    def _next_page(self):
        if not self.project: return
        total = len(self.project.pages)
        step = 1 if self.is_single_view else 2
        
        if self.is_cover_mode and not self.is_single_view:
            if self.current_page_idx == 0:
                if total > 1: self.current_page_idx = 1
            else:
                if self.current_page_idx + 2 < total:
                    self.current_page_idx += 2
        else:
            if self.current_page_idx < total:
                target = self.current_page_idx + step
                if target < total:
                    self.current_page_idx = target
                elif not self.is_single_view and target == total:
                    pass
                    
        self._update_nav_state()
        self._draw_main_view()

    def _go_first(self):
        self.current_page_idx = 0
        self._update_nav_state()
        self._draw_main_view()
        
    def _go_last(self):
        if not self.project: return
        total = len(self.project.pages)
        self.current_page_idx = total - 1
        
        if not self.is_single_view:
            if self.is_cover_mode:
                if self.current_page_idx % 2 == 0 and self.current_page_idx != 0:
                    self.current_page_idx -= 1
            else:
                if self.current_page_idx % 2 != 0:
                    self.current_page_idx -= 1
                    
        self._update_nav_state()
        self._draw_main_view()

    def _update_nav_state(self):
        if not self.project: return
        idx = self.current_page_idx
        total = len(self.project.pages)
        
        self.btn_prev.configure(state="normal" if idx > 0 else "disabled")
        
        if idx >= total - 1:
             self.btn_next.configure(state="disabled")
        else:
             self.btn_next.configure(state="normal")

        # Update inline navigation
        current_display_num = idx + 1
        self.entry_page_nav.delete(0, "end")
        self.entry_page_nav.insert(0, str(current_display_num))
        self.lbl_page_total.configure(text=f"/ {total}")

        # Mini Viewer Sync
        total_items = len(self.mini_thumb_frames)
        current_item_index = 0
        
        for i, (pages, frame) in enumerate(self.mini_thumb_frames.items()):
            if idx in pages:
                frame.configure(border_color=COLOR_ORANGE_MAIN)
                current_item_index = i
            else:
                frame.configure(border_color=COLOR_BG_TER)
        
        if total_items > 1:
            try:
                canvas = self.mini_viewer_frame._parent_canvas
                visible_width = canvas.winfo_width()
                scroll_region = canvas.bbox("all")
                if scroll_region:
                    content_width = scroll_region[2]
                    item_center_ratio = (current_item_index + 0.5) / total_items
                    target_center_px = item_center_ratio * content_width
                    desired_left_px = target_center_px - (visible_width / 2)
                    fraction = desired_left_px / content_width
                    fraction = max(0.0, min(1.0, fraction))
                    canvas.xview_moveto(fraction)
            except: pass

    # --- Slideshow ---
    def _toggle_slideshow(self):
        if self.is_slideshow_running:
            self.is_slideshow_running = False
            self.btn_slideshow.configure(text="▶ 再生", fg_color=COLOR_ORANGE_MAIN)
            if self.slideshow_timer: self.after_cancel(self.slideshow_timer)
        else:
            self.is_slideshow_running = True
            self.btn_slideshow.configure(text="■ 停止", fg_color=COLOR_RED_LIGHT)
            self._slideshow_loop()

    def _slideshow_loop(self):
        if not self.is_slideshow_running or not self.project: return
        try: interval = max(1000, int(float(self.entry_interval.get()) * 1000))
        except: interval = 3000
        
        total = len(self.project.pages)
        can_move = False
        if self.is_single_view:
            if self.current_page_idx + 1 < total: can_move = True
        else:
            if self.is_cover_mode:
                if self.current_page_idx == 0: 
                    if total > 1: can_move = True
                elif self.current_page_idx + 2 < total: can_move = True
            else:
                if self.current_page_idx + 2 < total: can_move = True
        
        if can_move:
            self._next_page()
            self.slideshow_timer = self.after(interval, self._slideshow_loop)
        else:
            self.is_slideshow_running = False
            self.btn_slideshow.configure(text="▶ 再生", fg_color=COLOR_ORANGE_MAIN)

# --- Main Application ---
class HomeBookStudio(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("HomeBook Studio 1.0")
        self.geometry("1600x1000")
        
        # Load Config
        self.config_data = DEFAULT_CONFIG.copy()
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, "r") as f: self.config_data.update(json.load(f))
            except: pass
            
        ctk.set_appearance_mode("Dark")
        ctk.set_default_color_theme("dark-blue")
        
        # UI Font
        sys_font = get_system_fonts()[0]
        self.ui_font = (sys_font, 12)
        self.ui_font_sm = (sys_font, 11)
        self.ui_font_bold = (sys_font, 12, "bold")
        self.ui_font_header = (sys_font, 18, "bold") 

        # State Initialization
        self.project = Project(
            margin_top=self.config_data.get("default_margin_top", 15.0),
            margin_bottom=self.config_data.get("default_margin_bottom", 15.0),
            margin_inner=self.config_data.get("default_margin_inner", 15.0),
            margin_outer=self.config_data.get("default_margin_outer", 15.0)
        )
        self.project.pages = [Page(), Page()] 

        self.history_stack = []; self.redo_stack = []
        self.image_library = []; self.thumbnails_cache = {}; self.thumb_btns = {}
        self.preview_image_cache = {}; self.mini_img_cache = {}; self.mini_canvas_refs = {}
        self.last_highlighted_mini_index = -1 
        self.drag_data = {"path": None, "item": None, "start_x": 0, "start_y": 0}
        self.selected_item = None; self.selected_item_page_idx = -1
        self.is_text_mode = False; self.ignore_ui_callbacks = False
        self.viewer_window = None 

        self.is_export_cancelled = False

        self.is_cover_mode = self.config_data.get("startup_cover_mode", False)
        
        self.mini_thumb_frames = {} 
        self.current_project_path = None
        self.auto_save_timer = None
        
        self.margin_entries = {}
        self.margin_sliders = {}

        # Variables
        self.var_paper_size = ctk.StringVar(value=self.project.paper_size)
        self.var_orientation = ctk.StringVar(value=self.project.orientation)
        self.var_output_fmt = ctk.StringVar(value=self.config_data.get("startup_export_fmt", "PDF"))
        
        self.var_rev_back = ctk.BooleanVar(value=False) 
        self.var_rot_back = ctk.BooleanVar(value=False)
        self.var_keep_orig = ctk.BooleanVar(value=False)
        
        self.var_m_top = ctk.DoubleVar(value=self.project.margin_top)
        self.var_m_bot = ctk.DoubleVar(value=self.project.margin_bottom)
        self.var_m_in = ctk.DoubleVar(value=self.project.margin_inner)
        self.var_m_out = ctk.DoubleVar(value=self.project.margin_outer)
        
        self.var_custom_margin_mode = ctk.BooleanVar(value=False)
        self.var_margin_scope = ctk.StringVar(value="All")

        self.var_layout_target = ctk.StringVar(value="Spread") 
        self.var_spacing = ctk.DoubleVar(value=0.0)
        self.var_item_rotation = ctk.DoubleVar(value=0)
        self.var_cover_mode = ctk.BooleanVar(value=self.is_cover_mode)

        self._build_menu_bar()
        self._build_ui()
        self._refresh_ui_from_project(rebuild_mode="full")
        self._start_auto_save()
        
        self.bind("<Control-z>", lambda e: self._undo())
        self.bind("<Control-y>", lambda e: self._redo())
        self.bind("<Left>", lambda e: self._prev_spread())
        self.bind("<Right>", lambda e: self._next_spread())

    def _save_config(self):
        try:
            with open(CONFIG_FILE, "w") as f: json.dump(self.config_data, f, indent=2)
        except: pass

    def _start_auto_save(self):
        if self.config_data["auto_save_enabled"] and self.current_project_path:
            self._auto_save_loop()
            
    def _auto_save_loop(self):
        if not self.config_data["auto_save_enabled"]: return
        if self.current_project_path:
            try:
                data = asdict(self.project)
                with open(self.current_project_path, "w") as f: json.dump(data, f, indent=2)
            except: pass
        
        interval_ms = self.config_data["auto_save_interval"] * 60000
        if interval_ms > 0:
            self.auto_save_timer = self.after(interval_ms, self._auto_save_loop)

    def _save_history(self):
        self.history_stack.append(copy.deepcopy(self.project))
        self.redo_stack.clear()
        if len(self.history_stack) > 30: self.history_stack.pop(0)

    def _undo(self):
        if not self.history_stack: return
        self.redo_stack.append(copy.deepcopy(self.project))
        self.project = self.history_stack.pop()
        self.selected_item = None
        self.preview_image_cache.clear()
        self._refresh_ui_from_project(rebuild_mode="full")
        self._refresh_thumbnails() # Undo時にも枚数カウント更新

    def _redo(self):
        if not self.redo_stack: return
        self.history_stack.append(copy.deepcopy(self.project))
        self.project = self.redo_stack.pop()
        self.selected_item = None
        self.preview_image_cache.clear()
        self._refresh_ui_from_project(rebuild_mode="full")
        self._refresh_thumbnails() # Redo時にも枚数カウント更新

    # --- UI Construction ---
    def _build_menu_bar(self):
        menu_bar = ctk.CTkFrame(self, height=28, fg_color="#000000", corner_radius=0)
        menu_bar.grid(row=0, column=0, sticky="ew")
        menu_bar.pack_propagate(False)

        def menu_btn(parent, text, cmd):
            btn = ctk.CTkButton(parent, text=text, font=(self.ui_font[0], 13), fg_color="transparent", 
                                hover_color="#444444", width=70, height=30, corner_radius=4, 
                                anchor="center", command=cmd)
            btn.pack(side="left", padx=2, pady=1)
            return btn
        
        def show_menu(event, menu):
            try:
                x = event.widget.winfo_rootx()
                y = event.widget.winfo_rooty() + event.widget.winfo_height()
                menu.tk_popup(x, y)
            finally:
                menu.grab_release()
        
        menu_kwargs = {"tearoff": 0, "bg": "#222", "fg": "white", "activebackground": COLOR_ORANGE_MAIN, "activeforeground": "white", "font": (self.ui_font[0], 11)}

        self.file_menu = tk.Menu(self, **menu_kwargs)
        self.file_menu.add_command(label="新規プロジェクト...", command=self._new_project)
        self.file_menu.add_command(label="開く...", command=self._load_project)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="上書き保存", command=self._save_project)
        self.file_menu.add_command(label="名前を付けて保存...", command=self._save_project_as)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="書き出し...", command=self._start_export)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="終了", command=self.destroy)
        
        self.edit_menu = tk.Menu(self, **menu_kwargs)
        self.edit_menu.add_command(label="元に戻す", command=self._undo)
        self.edit_menu.add_command(label="やり直し", command=self._redo)
        self.edit_menu.add_separator()
        self.edit_menu.add_command(label="ページ追加", command=self._add_page)
        self.edit_menu.add_command(label="ページ削除", command=self._remove_page)
        self.edit_menu.add_separator()
        self.edit_menu.add_command(label="環境設定...", command=self._open_preferences)

        self.view_menu = tk.Menu(self, **menu_kwargs)
        self.view_menu.add_checkbutton(label="表紙モード", onvalue=True, offvalue=False, variable=self.var_cover_mode, command=self._toggle_cover_mode)

        self.help_menu = tk.Menu(self, **menu_kwargs)
        self.help_menu.add_command(label="バージョン情報", command=self._show_about)

        b_file = menu_btn(menu_bar, "ファイル(F)", lambda: None)
        b_file.bind("<Button-1>", lambda e: show_menu(e, self.file_menu))
        b_edit = menu_btn(menu_bar, "編集(E)", lambda: None)
        b_edit.bind("<Button-1>", lambda e: show_menu(e, self.edit_menu))
        b_view = menu_btn(menu_bar, "表示(V)", lambda: None)
        b_view.bind("<Button-1>", lambda e: show_menu(e, self.view_menu))
        b_help = menu_btn(menu_bar, "ヘルプ(H)", lambda: None)
        b_help.bind("<Button-1>", lambda e: show_menu(e, self.help_menu))

    def _build_ui(self):
        self.grid_rowconfigure(2, weight=1)
        self.grid_columnconfigure(0, weight=1)

        # Header
        header = ctk.CTkFrame(self, height=35, fg_color=COLOR_BG_MAIN, corner_radius=0)
        header.grid(row=1, column=0, sticky="ew")
        header.pack_propagate(False) 
        
        left_box = ctk.CTkFrame(header, fg_color="transparent")
        left_box.pack(side="left", padx=15, fill="y")
        self.logo_image = None
        try:
            if os.path.exists("logo.png"):
                img = Image.open("logo.png")
                self.logo_image = ctk.CTkImage(light_image=img, dark_image=img, size=(24, 24))
        except: pass

        if self.logo_image: ctk.CTkLabel(left_box, text=" HomeBook Studio 1.0", image=self.logo_image, compound="left", font=self.ui_font_header, text_color=COLOR_FG_TEXT).pack(side="left")
        else: ctk.CTkLabel(left_box, text="HBS 1.0", font=self.ui_font_header, text_color=COLOR_FG_TEXT).pack(side="left")

        # Header Status
        self.header_status_frame = ctk.CTkFrame(header, fg_color="transparent")
        self.header_status_frame.pack(side="left", fill="x", expand=True, padx=20)
        self.header_status_label = ctk.CTkLabel(self.header_status_frame, text="書き出し中...", font=self.ui_font_bold, text_color=COLOR_ORANGE_MAIN)
        self.header_progress = ctk.CTkProgressBar(self.header_status_frame, width=200, height=6, progress_color=COLOR_ORANGE_MAIN, fg_color=COLOR_BTN_NORM)
        self.header_cancel_btn = ctk.CTkButton(self.header_status_frame, text="×", width=24, height=24, 
                                              fg_color=COLOR_RED_LIGHT, hover_color=COLOR_RED_HOVER, 
                                              font=("Arial", 12, "bold"), command=self._cancel_export)

        # Right Header Buttons
        right_box = ctk.CTkFrame(header, fg_color="transparent")
        right_box.pack(side="right", padx=10, fill="y")
        btn_style = {"width": 60, "height": 24, "font": self.ui_font_sm, "fg_color": "transparent", "hover_color": COLOR_BTN_HOVER, "text_color": COLOR_FG_TEXT, "corner_radius": 4, "border_width": 1, "border_color": COLOR_BTN_NORM}
        
        ctk.CTkButton(right_box, text="ビューワー", command=self._open_viewer, **btn_style).pack(side="left", padx=2, pady=5)
        ctk.CTkButton(right_box, text="元に戻す", command=self._undo, **btn_style).pack(side="left", padx=2, pady=5)
        ctk.CTkButton(right_box, text="やり直し", command=self._redo, **btn_style).pack(side="left", padx=2, pady=5)
        ctk.CTkButton(right_box, text="保存", command=self._save_project, **btn_style).pack(side="left", padx=2, pady=5)

        # Main Container
        container = ctk.CTkFrame(self, fg_color=COLOR_BG_SEC, corner_radius=0)
        container.grid(row=2, column=0, sticky="nsew")

        # Left Sidebar
        self.sidebar_tabs = ctk.CTkTabview(container, width=280, fg_color=COLOR_BG_SEC, segmented_button_fg_color=COLOR_BG_TER, segmented_button_selected_color=COLOR_ORANGE_MAIN, segmented_button_selected_hover_color=COLOR_ORANGE_HOVER, text_color=COLOR_FG_TEXT)
        self.sidebar_tabs.pack(side="left", fill="y")
        
        self.tab_imgs = self.sidebar_tabs.add("画像")
        self.tab_layout = self.sidebar_tabs.add("レイアウト")
        self.tab_settings = self.sidebar_tabs.add("設定")

        ctk.CTkButton(self.tab_imgs, text="フォルダ選択", font=self.ui_font, command=self._select_folder, height=28, fg_color=COLOR_ORANGE_MAIN, hover_color=COLOR_ORANGE_HOVER, text_color=COLOR_FG_TEXT).pack(fill="x", padx=5, pady=5)
        self.scroll_thumbs = ctk.CTkScrollableFrame(self.tab_imgs, fg_color="transparent")
        self.scroll_thumbs.pack(fill="both", expand=True, padx=0, pady=2)
        self.scroll_thumbs.grid_columnconfigure(0, weight=1); self.scroll_thumbs.grid_columnconfigure(1, weight=1); self.scroll_thumbs.grid_columnconfigure(2, weight=1)

        self._build_layout_tab()
        self._build_settings_tab()

        # Right Sidebar
        nav_frame = ctk.CTkFrame(container, width=180, fg_color=COLOR_BG_SEC)
        nav_frame.pack(side="right", fill="y")
        p_ops = ctk.CTkFrame(nav_frame, fg_color="transparent")
        p_ops.pack(fill="x", pady=5, padx=5)
        ctk.CTkLabel(p_ops, text="ページ操作", font=self.ui_font_bold, text_color=COLOR_FG_DIM).pack(side="left")
        ctk.CTkButton(p_ops, text="-", command=self._remove_page, width=30, height=24, font=self.ui_font, fg_color=COLOR_RED_LIGHT, hover_color=COLOR_RED_HOVER, text_color=COLOR_FG_TEXT).pack(side="right", padx=2)
        ctk.CTkButton(p_ops, text="+", command=self._add_page, width=30, height=24, font=self.ui_font, fg_color=COLOR_ORANGE_MAIN, hover_color=COLOR_ORANGE_HOVER, text_color=COLOR_FG_TEXT).pack(side="right", padx=2)
        
        self.nav_scroll = ctk.CTkScrollableFrame(nav_frame, height=200, fg_color="transparent")
        self.nav_scroll.pack(fill="x", padx=2, pady=2)
        ctk.CTkFrame(nav_frame, height=1, fg_color=COLOR_BTN_NORM).pack(fill="x", pady=10, padx=10)
        
        self.frame_props = ctk.CTkFrame(nav_frame, fg_color="transparent")
        self.frame_props.pack(fill="both", expand=True, padx=5, pady=5)
        ctk.CTkLabel(self.frame_props, text="アイテム編集", font=self.ui_font_bold, text_color=COLOR_FG_DIM).pack(pady=5, anchor="w")
        ctk.CTkLabel(self.frame_props, text="回転", font=self.ui_font_sm, text_color=COLOR_FG_DIM).pack(anchor="w")
        self.slider_item_rot = ctk.CTkSlider(self.frame_props, from_=0, to=360, variable=self.var_item_rotation, command=self._on_item_rotate, progress_color=COLOR_ORANGE_MAIN, button_color=COLOR_FG_TEXT, button_hover_color=COLOR_FG_TEXT)
        self.slider_item_rot.pack(fill="x", pady=5)
        self.btn_text_color = ctk.CTkButton(self.frame_props, text="文字色", font=self.ui_font, height=28, fg_color=COLOR_BTN_NORM, hover_color=COLOR_BTN_HOVER, text_color=COLOR_FG_TEXT, command=self._change_text_color)
        self.btn_del_item = ctk.CTkButton(self.frame_props, text="削除", font=self.ui_font, height=28, fg_color=COLOR_RED_LIGHT, hover_color=COLOR_RED_HOVER, text_color=COLOR_FG_TEXT, command=self._delete_selected_item)
        self.btn_del_item.pack(fill="x", pady=10, side="bottom")
        self._toggle_edit_panel(False)

        # Center Preview
        center_frame = ctk.CTkFrame(container, fg_color=COLOR_BG_MAIN, corner_radius=0)
        center_frame.pack(side="left", fill="both", expand=True)
        tools_bar = ctk.CTkFrame(center_frame, height=36, fg_color=COLOR_BG_MAIN)
        tools_bar.pack(fill="x", padx=10, pady=5)
        self.btn_text_mode = ctk.CTkButton(tools_bar, text="T テキスト", width=80, height=26, font=self.ui_font_bold,
                                           command=self._toggle_text_mode, fg_color="transparent", border_width=1, border_color=COLOR_BTN_NORM, text_color=COLOR_FG_TEXT, hover_color=COLOR_BTN_HOVER)
        self.btn_text_mode.pack(side="left")
        nav_cnt = ctk.CTkFrame(tools_bar, fg_color="transparent")
        nav_cnt.pack(side="left", expand=True)
        ctk.CTkButton(nav_cnt, text="<", width=30, height=26, fg_color="transparent", hover_color=COLOR_BTN_HOVER, text_color=COLOR_FG_TEXT, command=self._prev_spread).pack(side="left", padx=5)
        self.lbl_page_info = ctk.CTkLabel(nav_cnt, text="P1-P2", font=self.ui_font_bold, text_color=COLOR_FG_TEXT)
        self.lbl_page_info.pack(side="left", padx=10)
        ctk.CTkButton(nav_cnt, text=">", width=30, height=26, fg_color="transparent", hover_color=COLOR_BTN_HOVER, text_color=COLOR_FG_TEXT, command=self._next_spread).pack(side="left", padx=5)

        self.canvas_frame = ctk.CTkFrame(center_frame, fg_color=COLOR_BG_MAIN)
        self.canvas_frame.pack(fill="both", expand=True, padx=10)
        self.canvas = tk.Canvas(self.canvas_frame, bg="#202020", highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Configure>", lambda e: self.draw_preview())
        self.canvas.bind("<Button-1>", self._on_canvas_click)
        self.canvas.bind("<B1-Motion>", self._on_canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_canvas_release)

        # Mini Viewer
        self.mini_viewer_container = ctk.CTkFrame(self, height=140, fg_color=COLOR_BG_TER, corner_radius=0)
        self.mini_viewer_container.grid(row=3, column=0, sticky="ew")
        self.mini_viewer_scroll = ctk.CTkScrollableFrame(self.mini_viewer_container, orientation="horizontal", height=120, fg_color="transparent")
        self.mini_viewer_scroll.pack(fill="both", expand=True, padx=5, pady=5)

        # Footer
        footer = ctk.CTkFrame(self, height=40, fg_color=COLOR_BG_MAIN, corner_radius=0)
        footer.grid(row=4, column=0, sticky="ew")
        footer.pack_propagate(False)
        opt_frame = ctk.CTkFrame(footer, fg_color="transparent")
        opt_frame.pack(side="left", padx=10)
        opt_style = {"width": 80, "height": 24, "font": self.ui_font_sm, "fg_color": COLOR_BTN_NORM, "button_color": COLOR_BTN_HOVER, "button_hover_color": COLOR_ORANGE_MAIN, "text_color": COLOR_FG_TEXT}
        ctk.CTkOptionMenu(opt_frame, values=["PDF", "JPG"], variable=self.var_output_fmt, **opt_style).pack(side="left", padx=2)
        chk_style = {"font": self.ui_font_sm, "text_color": COLOR_FG_DIM, "hover_color": COLOR_ORANGE_MAIN, "fg_color": COLOR_FG_TEXT, "checkmark_color": COLOR_BG_MAIN}
        ctk.CTkCheckBox(opt_frame, text="逆順", variable=self.var_rev_back, **chk_style, width=50).pack(side="left", padx=10)
        ctk.CTkCheckBox(opt_frame, text="180°", variable=self.var_rot_back, **chk_style, width=50).pack(side="left", padx=5)
        ctk.CTkButton(footer, text="書き出し (EXPORT)", command=self._start_export, width=140, height=28, fg_color=COLOR_ORANGE_MAIN, hover_color=COLOR_ORANGE_HOVER, text_color="#ffffff", font=("Arial", 12, "bold")).pack(side="right", padx=20, pady=6)

    def _build_layout_tab(self):
        f = self.tab_layout
        lbl_style = {"font": self.ui_font_sm, "text_color": COLOR_FG_DIM}
        
        ctk.CTkLabel(f, text="適用先", **lbl_style).pack(anchor="w", padx=5, pady=(5,2))
        row_target = ctk.CTkFrame(f, fg_color="transparent")
        row_target.pack(fill="x", padx=2)
        rb_style = {"font": self.ui_font_sm, "text_color": COLOR_FG_TEXT, "fg_color": COLOR_ORANGE_MAIN, "hover_color": COLOR_ORANGE_HOVER, "width": 40}
        ctk.CTkRadioButton(row_target, text="左", variable=self.var_layout_target, value="Left", **rb_style).pack(side="left", padx=2)
        ctk.CTkRadioButton(row_target, text="右", variable=self.var_layout_target, value="Right", **rb_style).pack(side="left", padx=2)
        ctk.CTkRadioButton(row_target, text="両方", variable=self.var_layout_target, value="Spread", **rb_style).pack(side="left", padx=2)
        ctk.CTkRadioButton(row_target, text="全", variable=self.var_layout_target, value="All", **rb_style).pack(side="left", padx=2)

        ctk.CTkLabel(f, text="間隔 (mm)", **lbl_style).pack(anchor="w", padx=5, pady=(10,2))
        sl = ctk.CTkSlider(f, from_=0, to=20, variable=self.var_spacing, command=lambda v: [self.var_spacing.set(round(v,1)), self._apply_layout_spacing()],
                           progress_color=COLOR_ORANGE_MAIN, button_color=COLOR_FG_TEXT, button_hover_color=COLOR_FG_TEXT)
        sl.pack(fill="x", padx=5)

        row_style = ctk.CTkFrame(f, fg_color="transparent")
        row_style.pack(fill="x", padx=2, pady=10)
        ctk.CTkButton(row_style, text="背景色", width=70, command=self._change_bg_color, font=self.ui_font_sm, fg_color=COLOR_ORANGE_MAIN, hover_color=COLOR_ORANGE_HOVER, text_color=COLOR_FG_TEXT).pack(side="left", padx=2)
        ctk.CTkButton(row_style, text="クリア", width=70, command=self._clear_page_content, font=self.ui_font_sm, fg_color=COLOR_RED_LIGHT, hover_color=COLOR_RED_HOVER, text_color=COLOR_FG_TEXT).pack(side="left", padx=2)

        ctk.CTkLabel(f, text="テンプレート", **lbl_style).pack(anchor="w", padx=5, pady=(5,2))
        self.scroll_layouts = ctk.CTkScrollableFrame(f, fg_color="transparent")
        self.scroll_layouts.pack(fill="both", expand=True, padx=2, pady=2)
        self._populate_layout_list()

    def _build_settings_tab(self):
        f = self.tab_settings
        lbl_style = {"font": self.ui_font_sm, "text_color": COLOR_FG_DIM}
        
        ctk.CTkLabel(f, text="用紙サイズ", **lbl_style).pack(anchor="w", padx=5, pady=(5,2))
        opt_s = {"height": 24, "font": self.ui_font, "fg_color": COLOR_BTN_NORM, "button_color": COLOR_BTN_HOVER, "button_hover_color": COLOR_ORANGE_MAIN, "text_color": COLOR_FG_TEXT}
        self.om_paper = ctk.CTkOptionMenu(f, values=PAPER_KEYS, variable=self.var_paper_size, command=self._on_settings_change, **opt_s)
        self.om_paper.pack(fill="x", padx=5, pady=2)
        
        row_or = ctk.CTkFrame(f, fg_color="transparent")
        row_or.pack(fill="x", padx=5, pady=5)
        rb_style = {"font": self.ui_font_sm, "text_color": COLOR_FG_TEXT, "fg_color": COLOR_ORANGE_MAIN, "hover_color": COLOR_ORANGE_HOVER}
        self.rb_port = ctk.CTkRadioButton(row_or, text="縦", variable=self.var_orientation, value="Portrait", command=self._on_settings_change, **rb_style).pack(side="left", padx=10)
        self.rb_land = ctk.CTkRadioButton(row_or, text="横", variable=self.var_orientation, value="Landscape", command=self._on_settings_change, **rb_style).pack(side="left", padx=10)

        self.sw_cover_mode = ctk.CTkSwitch(f, text="表紙モード", variable=self.var_cover_mode, command=self._toggle_cover_mode, font=self.ui_font, progress_color=COLOR_ORANGE_MAIN, button_color=COLOR_FG_TEXT, button_hover_color=COLOR_FG_TEXT, fg_color=COLOR_BTN_NORM)
        self.sw_cover_mode.pack(anchor="w", padx=5, pady=10)
        
        ctk.CTkLabel(f, text="余白設定 (mm)", **lbl_style).pack(anchor="w", padx=5, pady=(10,2))
        
        # 適用範囲の選択
        self.frame_margin_target = ctk.CTkFrame(f, fg_color="transparent")
        self.frame_margin_target.pack(fill="x", padx=2, pady=2)
        
        rb_scope_style = {"font": self.ui_font_sm, "text_color": COLOR_FG_TEXT, "fg_color": COLOR_ORANGE_MAIN, "hover_color": COLOR_ORANGE_HOVER, "width": 40}
        ctk.CTkRadioButton(self.frame_margin_target, text="全体", variable=self.var_margin_scope, value="All", command=lambda: self._refresh_ui_from_project("highlight"), **rb_scope_style).pack(side="left", padx=2)
        ctk.CTkRadioButton(self.frame_margin_target, text="右", variable=self.var_margin_scope, value="Right", command=lambda: self._refresh_ui_from_project("highlight"), **rb_scope_style).pack(side="left", padx=2)
        ctk.CTkRadioButton(self.frame_margin_target, text="左", variable=self.var_margin_scope, value="Left", command=lambda: self._refresh_ui_from_project("highlight"), **rb_scope_style).pack(side="left", padx=2)
        ctk.CTkRadioButton(self.frame_margin_target, text="見開き", variable=self.var_margin_scope, value="Spread", command=lambda: self._refresh_ui_from_project("highlight"), **rb_scope_style).pack(side="left", padx=2)

        # 個別設定ロックスイッチ
        self.sw_custom = ctk.CTkSwitch(f, text="個別設定 (ロック)", variable=self.var_custom_margin_mode, command=self._toggle_margin_mode, font=self.ui_font, progress_color=COLOR_ORANGE_MAIN, button_color=COLOR_FG_TEXT, button_hover_color=COLOR_FG_TEXT, fg_color=COLOR_BTN_NORM)
        self.sw_custom.pack(anchor="w", padx=5, pady=(5, 5))

        self.margin_entries = {}
        self.margin_sliders = {}
        
        def add_control(lbl, var, key):
            row = ctk.CTkFrame(f, fg_color="transparent")
            row.pack(fill="x", padx=2, pady=2)
            ctk.CTkLabel(row, text=lbl, width=20, font=self.ui_font_sm, text_color=COLOR_FG_DIM).pack(side="left")
            entry = ctk.CTkEntry(row, width=50, height=24, font=self.ui_font_sm)
            entry.pack(side="left", padx=(5, 5))
            entry.insert(0, str(var.get()))
            entry.bind("<Return>", lambda e: self._on_margin_entry_change(key, var, entry))
            entry.bind("<FocusOut>", lambda e: self._on_margin_entry_change(key, var, entry))
            self.margin_entries[key] = entry
            
            slider = ctk.CTkSlider(row, from_=0, to=50, variable=var, 
                                   command=lambda v: self._on_margin_slider_change(key, v, entry),
                                   progress_color=COLOR_ORANGE_MAIN, button_color=COLOR_FG_TEXT, button_hover_color=COLOR_FG_TEXT)
            slider.pack(side="left", fill="x", expand=True)
            self.margin_sliders[key] = slider

        add_control("上", self.var_m_top, "top")
        add_control("下", self.var_m_bot, "bottom")
        add_control("内", self.var_m_in, "inner")
        add_control("外", self.var_m_out, "outer")

        ctk.CTkButton(f, text="全ページ統一", height=24, font=self.ui_font_sm, fg_color=COLOR_RED_LIGHT, hover_color=COLOR_RED_HOVER, text_color=COLOR_FG_TEXT,
                      command=self._reset_all_margins).pack(pady=20, fill="x", padx=10)

    def _new_project(self):
        if messagebox.askyesno("新規作成", "現在の内容は破棄されます。よろしいですか？"):
            self.current_project_path = None
            self.project = Project(
                margin_top=self.config_data.get("default_margin_top", 15.0),
                margin_bottom=self.config_data.get("default_margin_bottom", 15.0),
                margin_inner=self.config_data.get("default_margin_inner", 15.0),
                margin_outer=self.config_data.get("default_margin_outer", 15.0)
            )
            self.project.pages = [Page(layout_name="1枚 (全面)"), Page(layout_name="1枚 (全面)")]
            self.history_stack.clear(); self.redo_stack.clear()
            self.image_library = []; self.thumbnails_cache = {}; self.preview_image_cache.clear()
            for w in self.scroll_thumbs.winfo_children(): w.destroy()
            self._refresh_ui_from_project("full")

    def _open_preferences(self):
        top = ctk.CTkToplevel(self)
        top.title("環境設定")
        top.geometry("500x500") 
        
        self.update_idletasks()
        x = self.winfo_x() + (self.winfo_width() // 2) - 250
        y = self.winfo_y() + (self.winfo_height() // 2) - 250
        top.geometry(f"+{x}+{y}")
        top.attributes("-topmost", True)
        top.focus_force()
        
        tabs = ctk.CTkTabview(top)
        tabs.pack(fill="both", expand=True, padx=10, pady=10)
        t_gen = tabs.add("全般"); t_edit = tabs.add("編集"); t_exp = tabs.add("書き出し"); t_perf = tabs.add("パフォーマンス")

        # General
        ctk.CTkLabel(t_gen, text="起動時の設定", font=self.ui_font_bold).pack(anchor="w", padx=10, pady=5)
        
        cv_val = ctk.BooleanVar(value=self.config_data.get("startup_cover_mode", False))
        def update_startup_cover(val): self.config_data["startup_cover_mode"] = bool(val); self._save_config()
        ctk.CTkSwitch(t_gen, text="起動時に表紙モードをオン", variable=cv_val, command=lambda: update_startup_cover(cv_val.get())).pack(anchor="w", padx=20, pady=5)

        ctk.CTkLabel(t_gen, text="初期書き出し形式").pack(anchor="w", padx=20, pady=(10,2))
        fmt_var = ctk.StringVar(value=self.config_data.get("startup_export_fmt", "PDF"))
        def update_startup_fmt(val): self.config_data["startup_export_fmt"] = val; self._save_config()
        ctk.CTkOptionMenu(t_gen, values=["PDF", "JPG"], variable=fmt_var, command=update_startup_fmt).pack(anchor="w", padx=20)
        
        ctk.CTkLabel(t_gen, text="自動保存 (分)").pack(anchor="w", padx=10, pady=(20,5))
        as_var = ctk.StringVar(value=str(self.config_data["auto_save_interval"]))
        def save_as_int(v): self.config_data["auto_save_interval"] = int(v); self.config_data["auto_save_enabled"] = int(v)>0; self._save_config(); self._start_auto_save()
        ctk.CTkEntry(t_gen, textvariable=as_var).pack(padx=20, anchor="w")
        ctk.CTkButton(t_gen, text="適用", width=60, command=lambda: save_as_int(as_var.get())).pack(pady=5, anchor="w", padx=20)

        ctk.CTkLabel(t_gen, text="新規プロジェクトの初期余白 (mm)", font=self.ui_font_bold).pack(anchor="w", padx=10, pady=(20,5))
        f_m = ctk.CTkFrame(t_gen, fg_color="transparent")
        f_m.pack(padx=20, anchor="w")
        
        def make_entry(parent, label, key):
            f = ctk.CTkFrame(parent, fg_color="transparent")
            f.pack(side="left", padx=5)
            ctk.CTkLabel(f, text=label).pack(anchor="w")
            v = ctk.StringVar(value=str(self.config_data.get(key, 15.0)))
            e = ctk.CTkEntry(f, textvariable=v, width=50)
            e.pack()
            return v

        v_top = make_entry(f_m, "上", "default_margin_top")
        v_bot = make_entry(f_m, "下", "default_margin_bottom")
        v_in  = make_entry(f_m, "内", "default_margin_inner")
        v_out = make_entry(f_m, "外", "default_margin_outer")

        def save_defaults():
            try:
                self.config_data["default_margin_top"] = float(v_top.get())
                self.config_data["default_margin_bottom"] = float(v_bot.get())
                self.config_data["default_margin_inner"] = float(v_in.get())
                self.config_data["default_margin_outer"] = float(v_out.get())
                self._save_config()
                messagebox.showinfo("保存", "設定を保存しました。\n次回の新規作成から適用されます。")
            except ValueError:
                messagebox.showerror("エラー", "数値で入力してください")

        ctk.CTkButton(t_gen, text="デフォルト値を保存", command=save_defaults).pack(pady=10, anchor="w", padx=20)

        # Edit
        ctk.CTkCheckBox(t_edit, text="スナップ機能 (準備中)", variable=ctk.BooleanVar(value=self.config_data["snap_enabled"])).pack(anchor="w", padx=10, pady=10)
        
        # Export
        ctk.CTkLabel(t_exp, text="書き出し解像度 (DPI)").pack(anchor="w", padx=10, pady=5)
        dpi_var = ctk.StringVar(value=str(self.config_data["export_dpi"]))
        ctk.CTkOptionMenu(t_exp, values=["72","150","300","350","600"], variable=dpi_var, command=lambda v: [self.config_data.update({"export_dpi": int(v)}), self._save_config()]).pack(padx=10)
        
        ctk.CTkLabel(t_exp, text="塗り足し (mm)").pack(anchor="w", padx=10, pady=5)
        bleed_var = ctk.StringVar(value=str(self.config_data["export_bleed_mm"]))
        ctk.CTkOptionMenu(t_exp, values=["0.0", "3.0", "5.0"], variable=bleed_var, command=lambda v: [self.config_data.update({"export_bleed_mm": float(v)}), self._save_config()]).pack(padx=10)
        
        ctk.CTkLabel(t_exp, text="JPEG品質").pack(anchor="w", padx=10, pady=5)
        q_sl = ctk.CTkSlider(t_exp, from_=50, to=100)
        q_sl.set(self.config_data["export_quality"])
        q_sl.pack(padx=10); q_sl.bind("<ButtonRelease-1>", lambda e: [self.config_data.update({"export_quality": int(q_sl.get())}), self._save_config()])

        # Performance
        ctk.CTkLabel(t_perf, text="プレビュー画質").pack(anchor="w", padx=10, pady=5)
        qual_var = ctk.StringVar(value=self.config_data["preview_quality"])
        ctk.CTkOptionMenu(t_perf, values=["low", "medium", "high"], variable=qual_var, command=lambda v: [self.config_data.update({"preview_quality": v}), self._save_config()]).pack(padx=10)
        
        ctk.CTkButton(t_perf, text="キャッシュをクリア", fg_color=COLOR_RED_LIGHT, hover_color=COLOR_RED_HOVER,
                      command=lambda: [self.preview_image_cache.clear(), self.mini_img_cache.clear(), messagebox.showinfo("完了", "キャッシュを削除しました")]).pack(pady=20)

    def _show_about(self): messagebox.showinfo("バージョン情報", "HomeBook Studio 1.0 ver1.8\n\nHomeBookStudio © 2025-2026 HomeBookStudio1.0")
    
    def _populate_layout_list(self):
        for name in LayoutManager.LAYOUTS.keys():
            btn = ctk.CTkButton(self.scroll_layouts, text=name, 
                                fg_color="transparent", border_width=1, border_color=COLOR_BTN_NORM, height=28,
                                hover_color=COLOR_BTN_HOVER, text_color=COLOR_FG_TEXT,
                                command=lambda n=name: self._set_current_page_layout(n))
            btn.pack(fill="x", padx=2, pady=2)

    def _toggle_text_mode(self):
        self.is_text_mode = not self.is_text_mode
        if self.is_text_mode:
            self.btn_text_mode.configure(fg_color=COLOR_ORANGE_MAIN, text_color=COLOR_FG_TEXT)
        else:
            self.btn_text_mode.configure(fg_color="transparent", text_color=COLOR_FG_TEXT)

    def _toggle_cover_mode(self):
        self.is_cover_mode = self.var_cover_mode.get()
        self.project.current_spread_index = 0
        self._refresh_ui_from_project(rebuild_mode="full")

    def _get_image_usage_counts(self):
        counts = {}
        for page in self.project.pages:
            for photo in page.photos: counts[photo.path] = counts.get(photo.path, 0) + 1
        return counts

    def _get_target_pages_indices(self):
        target = self.var_layout_target.get()
        pages = self._get_current_spread_pages()
        pages_to_update = []
        total = len(self.project.pages)
        if target == "All": return list(range(total))
        if self.is_cover_mode and self.project.current_spread_index == 0:
            if target == "Right" or target == "Spread":
                if pages: pages_to_update.append(pages[0])
        else:
            if len(pages) > 0 and (target == "Left" or target == "Spread"): pages_to_update.append(pages[0])
            if len(pages) > 1 and (target == "Right" or target == "Spread"): pages_to_update.append(pages[1])
        return pages_to_update

    def _get_current_spread_pages(self) -> List[int]:
        idx = self.project.current_spread_index
        if self.is_cover_mode:
            if idx == 0: return [0]
            start = 1 + (idx - 1) * 2
            return [start, start + 1]
        else:
            start = idx * 2
            return [start, start + 1]

    def _select_folder(self):
        folder = filedialog.askdirectory()
        if not folder: return
        self.image_library = [os.path.join(folder, f) for f in sorted(os.listdir(folder)) if f.lower().endswith(IMG_EXTS)]
        self._refresh_thumbnails()

    def _refresh_thumbnails(self):
        for w in self.scroll_thumbs.winfo_children(): w.destroy()
        self.thumb_btns.clear()
        counts = self._get_image_usage_counts()
        for idx, path in enumerate(self.image_library):
            try:
                if path not in self.thumbnails_cache:
                    img = Image.open(path)
                    img.thumbnail((80, 80))
                    self.thumbnails_cache[path] = img
                thumb_img = self.thumbnails_cache[path].copy()
                count = counts.get(path, 0)
                if count > 0:
                    draw = ImageDraw.Draw(thumb_img)
                    r = 10; x, y = 12, 12
                    draw.ellipse((x-r, y-r, x+r, y+r), fill=COLOR_ORANGE_MAIN, outline="white", width=1)
                    draw.text((x, y), str(count), fill="white", anchor="mm", font_size=12)
                ctk_img = ctk.CTkImage(light_image=thumb_img, dark_image=thumb_img, size=thumb_img.size)
                btn = ctk.CTkButton(self.scroll_thumbs, image=ctk_img, text="", width=84, height=84,
                                    fg_color="transparent", border_width=0, corner_radius=0,
                                    command=lambda p=path: self._on_thumb_click(p))
                btn.grid(row=idx//3, column=idx%3, padx=2, pady=2)
                self.thumb_btns[path] = btn
            except: pass

    def _on_thumb_click(self, path):
        self.drag_data["path"] = path 
        for p, btn in self.thumb_btns.items():
            if p == path: btn.configure(border_width=2, border_color=COLOR_FG_TEXT) 
            else: btn.configure(border_width=0)

    def _set_current_page_layout(self, layout_name):
        self._save_history()
        for idx in self._get_target_pages_indices():
            if idx < len(self.project.pages): self.project.pages[idx].layout_name = layout_name
        self.preview_image_cache.clear() 
        self._refresh_ui_from_project(rebuild_mode="full")

    def _apply_layout_spacing(self):
        if self.ignore_ui_callbacks: return
        self._save_history()
        spacing = self.var_spacing.get()
        for i in self._get_target_pages_indices():
            if i < len(self.project.pages): self.project.pages[i].spacing_mm = spacing
        self.draw_preview()

    def _change_bg_color(self):
        color_code = colorchooser.askcolor(title="背景色")[1]
        if color_code:
            self._save_history()
            for i in self._get_target_pages_indices():
                if i < len(self.project.pages): self.project.pages[i].background_color = color_code
            self._refresh_ui_from_project(rebuild_mode="full")

    def _clear_page_content(self):
        if not messagebox.askyesno("確認", "画像を削除しますか？"): return
        self._save_history()
        for i in self._get_target_pages_indices():
            if i < len(self.project.pages):
                self.project.pages[i].photos.clear()
                self.project.pages[i].texts.clear()
                self.project.pages[i].background_color = "#FFFFFF" 
        self._refresh_ui_from_project(rebuild_mode="full")
        self._refresh_thumbnails()

    def _add_page(self):
        self._save_history()
        self.project.pages.append(Page(layout_name="1枚 (全面)"))
        self.project.pages.append(Page(layout_name="1枚 (全面)"))
        self._refresh_ui_from_project(rebuild_mode="full")

    def _remove_page(self):
        total_pages = len(self.project.pages)
        if total_pages <= 2:
            messagebox.showwarning("警告", "これ以上ページを削除できません")
            return
        
        if not messagebox.askyesno("確認", "現在表示しているページを削除しますか？\n（この操作は元に戻せます）"):
            return

        self._save_history()
        
        idx = self.project.current_spread_index
        start_idx = 0
        
        if self.is_cover_mode:
            if idx == 0:
                messagebox.showerror("エラー", "表紙ページは削除できません。\n内容をクリアしたい場合は「クリア」ボタンを使用してください。")
                return 
            else:
                start_idx = 1 + (idx - 1) * 2
        else:
            start_idx = idx * 2
            
        if start_idx >= total_pages:
            self.project.pages.pop()
            self.project.pages.pop()
        else:
            del self.project.pages[start_idx : start_idx + 2]
            
        max_spread = (len(self.project.pages) // 2) + (1 if self.is_cover_mode else 0)
        if self.project.current_spread_index >= max_spread:
             self.project.current_spread_index = max(0, max_spread - 1)

        self.preview_image_cache.clear()
        self._refresh_ui_from_project(rebuild_mode="full")
        self._refresh_thumbnails()
    
    # --- 余白設定バグ修正版 ---

    def _get_target_pages_for_margin(self) -> List[int]:
        scope = self.var_margin_scope.get()
        current_pages = self._get_current_spread_pages()
        
        if scope == "All":
            return list(range(len(self.project.pages)))

        targets = []
        if self.is_cover_mode and self.project.current_spread_index == 0:
            if scope == "Right" or scope == "Spread":
                if current_pages: targets.append(current_pages[0])
        else:
            if scope == "Left" or scope == "Spread":
                if len(current_pages) > 0: targets.append(current_pages[0])
            if scope == "Right" or scope == "Spread":
                if len(current_pages) > 1: targets.append(current_pages[1])
                
        return targets

    def _toggle_margin_mode(self):
        """個別設定ロックスイッチの切り替え"""
        if self.ignore_ui_callbacks: return
        
        is_custom = self.var_custom_margin_mode.get()
        scope = self.var_margin_scope.get()
        
        if scope == "All":
            self.var_custom_margin_mode.set(False)
            return

        target_indices = self._get_target_pages_for_margin()
        if not target_indices: return

        self._save_history()

        if is_custom:
            vals = {
                "top": self.var_m_top.get(),
                "bottom": self.var_m_bot.get(),
                "inner": self.var_m_in.get(),
                "outer": self.var_m_out.get()
            }
            for idx in target_indices:
                if idx < len(self.project.pages):
                    if self.project.pages[idx].custom_margins is None:
                        self.project.pages[idx].custom_margins = vals.copy()
            
            for s in self.margin_sliders.values(): s.configure(state="normal")
            for e in self.margin_entries.values(): e.configure(state="normal")

        else:
            for idx in target_indices:
                 if idx < len(self.project.pages):
                     self.project.pages[idx].custom_margins = None
            
            self.var_m_top.set(self.project.margin_top)
            self.var_m_bot.set(self.project.margin_bottom)
            self.var_m_in.set(self.project.margin_inner)
            self.var_m_out.set(self.project.margin_outer)
            self._update_margin_entries_from_vars()
            
            for s in self.margin_sliders.values(): s.configure(state="disabled")
            for e in self.margin_entries.values(): e.configure(state="disabled")

        self.draw_preview()

    def _on_margin_slider_change(self, key, value, entry_widget):
        val = round(value, 1)
        current_text = entry_widget.get()
        if current_text != str(val):
            entry_widget.delete(0, "end")
            entry_widget.insert(0, str(val))
        self._apply_margin_change()

    def _on_margin_entry_change(self, key, var, entry_widget):
        try:
            val = float(entry_widget.get())
            if val < 0: val = 0
            if val > 50: val = 50
            if var.get() != val:
                var.set(val)
                self._apply_margin_change()
            entry_widget.delete(0, "end")
            entry_widget.insert(0, str(val))
            self.canvas.focus_set()
        except ValueError:
            entry_widget.delete(0, "end")
            entry_widget.insert(0, str(var.get()))

    def _apply_margin_change(self):
        if self.ignore_ui_callbacks: return
        
        vals = {
            "top": self.var_m_top.get(),
            "bottom": self.var_m_bot.get(),
            "inner": self.var_m_in.get(),
            "outer": self.var_m_out.get()
        }

        scope = self.var_margin_scope.get()
        is_locked = self.var_custom_margin_mode.get()

        if scope == "All":
            self.project.margin_top = vals["top"]
            self.project.margin_bottom = vals["bottom"]
            self.project.margin_inner = vals["inner"]
            self.project.margin_outer = vals["outer"]
        else:
            if is_locked:
                target_indices = self._get_target_pages_for_margin()
                for idx in target_indices:
                    if idx < len(self.project.pages):
                        if self.project.pages[idx].custom_margins is None:
                            self.project.pages[idx].custom_margins = vals.copy()
                        else:
                            self.project.pages[idx].custom_margins.update(vals)

        self.draw_preview()

    def _on_settings_change(self, _=None):
        if self.ignore_ui_callbacks: return
        self._save_history()
        self.project.paper_size = self.var_paper_size.get()
        self.project.orientation = self.var_orientation.get()
        self.draw_preview()
        self._init_mini_viewer(force_rebuild=True)

    def _update_margin_entries_from_vars(self):
        mapping = {"top": self.var_m_top, "bottom": self.var_m_bot, "inner": self.var_m_in, "outer": self.var_m_out}
        for key, var in mapping.items():
            if key in self.margin_entries:
                curr_state = self.margin_entries[key].cget("state")
                if curr_state == "disabled":
                    self.margin_entries[key].configure(state="normal")
                
                self.margin_entries[key].delete(0, "end")
                self.margin_entries[key].insert(0, str(round(var.get(), 1)))
                
                if curr_state == "disabled":
                    self.margin_entries[key].configure(state="disabled")

    def _reset_all_margins(self):
        self._save_history()
        self.project.margin_top = self.var_m_top.get()
        self.project.margin_bottom = self.var_m_bot.get()
        self.project.margin_inner = self.var_m_in.get()
        self.project.margin_outer = self.var_m_out.get()
        for p in self.project.pages: p.custom_margins = None
        
        self.var_margin_scope.set("All")
        self.var_custom_margin_mode.set(False)
        self.sw_custom.configure(state="disabled")
        
        for s in self.margin_sliders.values(): s.configure(state="normal")
        for e in self.margin_entries.values(): e.configure(state="normal")
        
        self._update_margin_entries_from_vars()
        self.draw_preview()

    def _open_viewer(self):
        if self.viewer_window is None or not self.viewer_window.winfo_exists():
            self.viewer_window = HBSViewer(parent=self, project_data=self.project)
        else:
            self.viewer_window.lift()
            self.viewer_window.focus_force()
            self.viewer_window.update_project_data(self.project)

    def _sync_viewer(self):
        if self.viewer_window and self.viewer_window.winfo_exists():
            self.viewer_window.update_project_data(self.project)

    def _refresh_ui_from_project(self, rebuild_mode="full"):
        self.ignore_ui_callbacks = True 
        
        self.om_paper.set(self.project.paper_size)
        self.var_orientation.set(self.project.orientation)
        
        scope = self.var_margin_scope.get()
        
        if scope == "All":
            self.var_custom_margin_mode.set(False)
            self.sw_custom.configure(state="disabled")
            
            for s in self.margin_sliders.values(): s.configure(state="normal")
            for e in self.margin_entries.values(): e.configure(state="normal")
            
            self.var_m_top.set(self.project.margin_top)
            self.var_m_bot.set(self.project.margin_bottom)
            self.var_m_in.set(self.project.margin_inner)
            self.var_m_out.set(self.project.margin_outer)
        else:
            self.sw_custom.configure(state="normal")
            
            target_indices = self._get_target_pages_for_margin()
            
            is_locked = False
            ref_page = None
            if target_indices and target_indices[0] < len(self.project.pages):
                ref_page = self.project.pages[target_indices[0]]
                if ref_page.custom_margins:
                    is_locked = True
            
            self.var_custom_margin_mode.set(is_locked)
            
            if is_locked and ref_page and ref_page.custom_margins:
                for s in self.margin_sliders.values(): s.configure(state="normal")
                for e in self.margin_entries.values(): e.configure(state="normal")
                
                self.var_m_top.set(ref_page.custom_margins["top"])
                self.var_m_bot.set(ref_page.custom_margins["bottom"])
                self.var_m_in.set(ref_page.custom_margins["inner"])
                self.var_m_out.set(ref_page.custom_margins["outer"])
            else:
                for s in self.margin_sliders.values(): s.configure(state="disabled")
                for e in self.margin_entries.values(): e.configure(state="disabled")
                
                self.var_m_top.set(self.project.margin_top)
                self.var_m_bot.set(self.project.margin_bottom)
                self.var_m_in.set(self.project.margin_inner)
                self.var_m_out.set(self.project.margin_outer)

        self._update_margin_entries_from_vars()

        p_info = ""
        pages = self._get_current_spread_pages()
        if self.is_cover_mode:
            if self.project.current_spread_index == 0: p_info = "Cover (P1)"
            else:
                if pages:
                    st = pages[0] + 1
                    p_info = f"P{st} - P{st+1}"
        else:
            if pages:
                st = pages[0] + 1
                p_info = f"P{st} - P{st+1}"
        self.lbl_page_info.configure(text=p_info)

        self._refresh_nav_list()
        
        if rebuild_mode == "full":
            self._init_mini_viewer(force_rebuild=True)
        else:
            self._sync_mini_viewer_scroll()
        
        self.selected_item = None
        self._toggle_edit_panel(False)
        self.draw_preview()
        self.ignore_ui_callbacks = False 

        self._sync_viewer()

    def _refresh_nav_list(self):
        for w in self.nav_scroll.winfo_children(): w.destroy()
        total = len(self.project.pages)
        count = 1 + (total-1+1)//2 if self.is_cover_mode else (total+1)//2
        for s in range(count):
            is_cur = (s == self.project.current_spread_index)
            txt = ""
            if self.is_cover_mode:
                if s == 0: txt = "P1"
                else:
                    st = 1 + (s-1)*2 + 1
                    txt = f"P{st}-{st+1}"
            else:
                st = s*2 + 1
                txt = f"P{st}-{st+1}"
            
            fg = COLOR_ORANGE_MAIN if is_cur else "transparent"
            hover = COLOR_ORANGE_HOVER if is_cur else COLOR_BTN_HOVER
            text_c = "#ffffff" if is_cur else COLOR_FG_TEXT

            btn = ctk.CTkButton(self.nav_scroll, text=txt,
                                fg_color=fg, hover_color=hover, text_color=text_c,
                                font=self.ui_font_sm, height=24, anchor="w",
                                command=lambda x=s: self._jump_spread(x))
            btn.pack(fill="x", pady=1, padx=2)

    # --- High Performance Mini Viewer ---
    def _init_mini_viewer(self, force_rebuild=False):
        total_pages = len(self.project.pages)
        spreads = []
        if self.is_cover_mode:
            spreads.append([0])
            for i in range(1, total_pages, 2): spreads.append([i] if i+1 >= total_pages else [i, i+1])
        else:
            for i in range(0, total_pages, 2): spreads.append([i] if i+1 >= total_pages else [i, i+1])
        
        if force_rebuild or len(self.mini_thumb_frames) != len(spreads):
            for w in self.mini_viewer_scroll.winfo_children(): w.destroy()
            self.mini_thumb_frames = {}
            self.mini_canvas_refs = {}
            self.last_highlighted_mini_index = -1
            
            for s_idx, pages in enumerate(spreads):
                frame = ctk.CTkFrame(self.mini_viewer_scroll, fg_color="transparent", border_width=2, border_color="#1a1a1a")
                frame.pack(side="left", padx=2, pady=2)
                self.mini_thumb_frames[s_idx] = frame
                
                cv = tk.Canvas(frame, width=120, height=80, bg="#222", highlightthickness=0)
                cv.pack(padx=2, pady=2)
                
                cv.bind("<Button-1>", lambda e, idx=s_idx: self._jump_spread(idx))
                frame.bind("<Button-1>", lambda e, idx=s_idx: self._jump_spread(idx))
                
                self._draw_mini_thumb(cv, pages, s_idx == 0 and self.is_cover_mode, s_idx)
                
                lbl = f"P{pages[0]+1}"
                if len(pages)>1: lbl+=f"-{pages[1]+1}"
                ctk.CTkLabel(frame, text=lbl, font=("Arial", 10), text_color=COLOR_FG_DIM).pack()
        
        self._sync_mini_viewer_scroll()

    def _draw_mini_thumb(self, canvas, pages, is_cover, s_idx):
        w, h = 120, 80
        canvas.delete("all")
        
        size_key = self.project.paper_size if self.project.paper_size in PAPER_SIZES else "A4"
        pw_mm, ph_mm = PAPER_SIZES[size_key]
        if self.project.orientation == "Landscape": pw_mm, ph_mm = ph_mm, pw_mm
        
        spread_ratio = (pw_mm * 2) / ph_mm
        canvas_ratio = w / h
        if canvas_ratio > spread_ratio:
            draw_h = h * 0.9; draw_w = draw_h * spread_ratio
        else:
            draw_w = w * 0.9; draw_h = draw_w / spread_ratio
            
        cx, cy = w/2, h/2
        x0 = cx - draw_w/2; y0 = cy - draw_h/2
        p_w = draw_w / 2
        
        pages_to_draw = []
        if is_cover: pages_to_draw.append((1, pages[0]))
        else:
            for i, p_idx in enumerate(pages): pages_to_draw.append((i, p_idx))

        self.mini_canvas_refs[s_idx] = []

        for offset, p_idx in pages_to_draw:
            if p_idx >= len(self.project.pages): continue
            page = self.project.pages[p_idx]
            px = x0 + offset * p_w
            
            canvas.create_rectangle(px, y0, px+p_w, y0+draw_h, fill=page.background_color, outline="#444")
            
            scale = p_w / pw_mm
            rects = LayoutManager.get_layout_rects(page.layout_name)
            mt, mb, mi, mo = self.project.margin_top, self.project.margin_bottom, self.project.margin_inner, self.project.margin_outer
            sx = px + (mo if offset==0 else mi)*scale
            sy = y0 + mt*scale
            
            sw = p_w - (mi+mo)*scale
            sh = draw_h - (mt+mb)*scale
            
            for r_idx, (rx, ry, rw, rh) in enumerate(rects):
                bx = sx + rx*sw; by = sy + ry*sh; bw = rw*sw; bh = rh*sh
                photo = next((p for p in page.photos if p.slot_index == r_idx), None)
                
                if photo:
                    img_key = f"{photo.path}_mini_{int(bw)}x{int(bh)}"
                    tk_thumb = None
                    
                    if img_key in self.mini_img_cache:
                        tk_thumb = self.mini_img_cache[img_key]
                    else:
                        try:
                            if os.path.exists(photo.path):
                                pil = Image.open(photo.path)
                                fitted = ImageOps.fit(pil, (int(bw), int(bh)), method=Image.NEAREST)
                                tk_thumb = ImageTk.PhotoImage(fitted)
                                self.mini_img_cache[img_key] = tk_thumb
                        except: pass
                    
                    if tk_thumb:
                        canvas.create_image(bx + bw/2, by + bh/2, image=tk_thumb)
                        self.mini_canvas_refs[s_idx].append(tk_thumb)
                    else:
                        canvas.create_rectangle(bx, by, bx+bw, by+bh, fill=COLOR_ORANGE_MAIN, outline="#666")
                    
                    canvas.create_rectangle(bx, by, bx+bw, by+bh, outline="#666", width=1)
                else:
                    canvas.create_rectangle(bx, by, bx+bw, by+bh, outline="#444")

    def _sync_mini_viewer_scroll(self):
        idx = self.project.current_spread_index
        total = len(self.mini_thumb_frames)
        
        if self.last_highlighted_mini_index != -1 and self.last_highlighted_mini_index in self.mini_thumb_frames:
             self.mini_thumb_frames[self.last_highlighted_mini_index].configure(border_color="#1a1a1a", border_width=2)
        
        if idx in self.mini_thumb_frames:
             self.mini_thumb_frames[idx].configure(border_color=COLOR_HIGHLIGHT, border_width=3)
             self.last_highlighted_mini_index = idx

        if total > 1:
            try:
                cv = self.mini_viewer_scroll._parent_canvas
                vw = cv.winfo_width(); sr = cv.bbox("all")
                if sr:
                    cw = sr[2]
                    ctr = (idx + 0.5) / total * cw
                    left = ctr - (vw / 2)
                    frac = max(0.0, min(1.0, left / cw))
                    cv.xview_moveto(frac)
            except: pass

    # --- Navigation ---
    def _jump_spread(self, idx):
        if self.project.current_spread_index == idx: return
        self.project.current_spread_index = idx
        self._refresh_ui_from_project(rebuild_mode="highlight")

    def _prev_spread(self):
        if self.project.current_spread_index > 0:
            self.project.current_spread_index -= 1
            self._refresh_ui_from_project(rebuild_mode="highlight")
    
    def _next_spread(self):
        self.project.current_spread_index += 1
        current_indices = self._get_current_spread_pages()
        max_idx = max(current_indices) if current_indices else 0
        
        if len(self.project.pages) <= max_idx:
            self.project.pages.append(Page(layout_name="1枚 (全面)"))
            self.project.pages.append(Page(layout_name="1枚 (全面)"))
            self._refresh_ui_from_project(rebuild_mode="full")
        else:
            self._refresh_ui_from_project(rebuild_mode="highlight")

    # --- Item Selection & Editing ---
    def _toggle_edit_panel(self, enabled: bool):
        state = "normal" if enabled else "disabled"
        self.slider_item_rot.configure(state=state)
        self.btn_del_item.configure(state=state)
        if not enabled:
            self.slider_item_rot.set(0)
            self.btn_text_color.pack_forget() 
        else:
            if isinstance(self.selected_item, TextItem): self.btn_text_color.pack(fill="x", pady=2, after=self.slider_item_rot)
            else: self.btn_text_color.pack_forget()

    def _select_item(self, page_idx, item):
        self.selected_item = item
        self.selected_item_page_idx = page_idx
        if item:
            self.ignore_ui_callbacks = True
            self.slider_item_rot.set(item.rotation)
            self.ignore_ui_callbacks = False
            self._toggle_edit_panel(True)
        else:
            self._toggle_edit_panel(False)
        self.draw_preview()

    def _on_item_rotate(self, val):
        if self.selected_item and not self.ignore_ui_callbacks:
            self._save_history() 
            self.selected_item.rotation = int(val)
            self.draw_preview()

    def _delete_selected_item(self):
        if self.selected_item and self.selected_item_page_idx != -1:
            self._save_history()
            page = self.project.pages[self.selected_item_page_idx]
            if isinstance(self.selected_item, PhotoItem):
                if self.selected_item in page.photos: page.photos.remove(self.selected_item)
            elif isinstance(self.selected_item, TextItem):
                if self.selected_item in page.texts: page.texts.remove(self.selected_item)
            self.selected_item = None
            self._toggle_edit_panel(False)
            self.draw_preview()
            self._refresh_thumbnails() # 削除時にカウント更新
            self._refresh_ui_from_project(rebuild_mode="full")

    def _change_text_color(self):
        if isinstance(self.selected_item, TextItem):
            color = colorchooser.askcolor(color=self.selected_item.color)[1]
            if color:
                self._save_history()
                self.selected_item.color = color
                self.draw_preview()

    # --- Canvas Logic ---
    def _get_draw_metrics(self):
        w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
        if w < 10: return None
        size_key = self.project.paper_size if self.project.paper_size in PAPER_SIZES else "A4"
        pw_mm, ph_mm = PAPER_SIZES[size_key]
        if self.project.orientation == "Landscape": pw_mm, ph_mm = ph_mm, pw_mm
        
        spread_ratio = (pw_mm * 2) / ph_mm
        canvas_ratio = w / h
        if canvas_ratio > spread_ratio:
            draw_h = h * 0.95; draw_w = draw_h * spread_ratio 
        else:
            draw_w = w * 0.95; draw_h = draw_w / spread_ratio
        x0 = (w - draw_w) / 2; y0 = (h - draw_h) / 2
        return x0, y0, draw_w, draw_h, pw_mm

    def _get_page_margins(self, page: Page):
        if page.custom_margins:
            return page.custom_margins["top"], page.custom_margins["bottom"], page.custom_margins["inner"], page.custom_margins["outer"]
        return self.project.margin_top, self.project.margin_bottom, self.project.margin_inner, self.project.margin_outer

    def _hit_test(self, cx, cy) -> Tuple[int, int]:
        metrics = self._get_draw_metrics()
        if not metrics: return -1, -1
        x0, y0, dw, dh, pw_mm = metrics
        p_w = dw / 2; scale = p_w / pw_mm
        if not (y0 <= cy <= y0 + dh): return -1, -1
        
        page_offset = -1
        if x0 <= cx <= x0+p_w: page_offset = 0
        elif x0+p_w <= cx <= x0+dw: page_offset = 1
        else: return -1, -1
        
        p_idx = -1
        pages = self._get_current_spread_pages()
        if self.is_cover_mode and self.project.current_spread_index == 0:
            if page_offset == 1: p_idx = pages[0]
        else:
            if page_offset == 0 and len(pages) > 0: p_idx = pages[0]
            if page_offset == 1 and len(pages) > 1: p_idx = pages[1]
            
        if p_idx == -1 or p_idx >= len(self.project.pages): return -1, -1
        
        page = self.project.pages[p_idx]
        mt, mb, mi, mo = self._get_page_margins(page)
        px_start = x0 + (page_offset * p_w)
        
        if page_offset == 0: safe = (px_start + mo*scale, y0 + mt*scale, px_start + p_w - mi*scale, y0 + dh - mb*scale)
        else: safe = (px_start + mi*scale, y0 + mt*scale, px_start + p_w - mo*scale, y0 + dh - mb*scale)
            
        sw, sh = safe[2]-safe[0], safe[3]-safe[1]
        if sw < 1: sw = 1
        if sh < 1: sh = 1
        rects = LayoutManager.get_layout_rects(page.layout_name)
        sp_px = page.spacing_mm * scale
        for i, (rx, ry, rw, rh) in enumerate(rects):
            slot_x = safe[0] + rx * sw + sp_px/2
            slot_y = safe[1] + ry * sh + sp_px/2
            slot_w = rw * sw - sp_px
            slot_h = rh * sh - sp_px
            if slot_x <= cx <= slot_x+slot_w and slot_y <= cy <= slot_y+slot_h:
                return p_idx, i
        return p_idx, -1

    def _hit_test_text(self, cx, cy) -> Tuple[int, Optional[TextItem]]:
        metrics = self._get_draw_metrics()
        if not metrics: return -1, None
        x0, y0, dw, dh, _ = metrics
        p_w = dw / 2
        
        current_pages = self._get_current_spread_pages()
        pages_to_check = []
        if self.is_cover_mode and self.project.current_spread_index == 0:
            pages_to_check.append((1, current_pages[0]))
        else:
            for i, pid in enumerate(current_pages): pages_to_check.append((i, pid))
                
        for offset, p_idx in pages_to_check:
            if p_idx >= len(self.project.pages): continue
            px_start = x0 + (offset * p_w)
            page = self.project.pages[p_idx]
            for txt in page.texts:
                tx = px_start + txt.x_rel * p_w
                ty = y0 + txt.y_rel * dh
                if abs(cx - tx) < txt.font_size and abs(cy - ty) < txt.font_size: return p_idx, txt
        return -1, None

    def draw_preview(self):
        self.canvas.delete("all")
        metrics = self._get_draw_metrics()
        if not metrics: return
        x0, y0, dw, dh, pw_mm = metrics
        p_w = dw / 2; scale = p_w / pw_mm 
        
        pages_to_draw = []
        current_pages = self._get_current_spread_pages()
        if self.is_cover_mode and self.project.current_spread_index == 0:
            if current_pages: pages_to_draw.append((1, current_pages[0]))
        else:
            for i, pid in enumerate(current_pages): pages_to_draw.append((i, pid))

        # Spine
        spine_x = x0 + p_w
        self.canvas.create_line(spine_x, y0, spine_x, y0+dh, fill="#444", width=1)
        
        self._draw_refs = [] 

        for offset, p_idx in pages_to_draw:
            if p_idx >= len(self.project.pages): continue
            page = self.project.pages[p_idx]
            px = x0 + (offset * p_w)
            
            self.canvas.create_rectangle(px, y0, px+p_w, y0+dh, fill=page.background_color, outline="#333")
            mt, mb, mi, mo = self._get_page_margins(page)
            
            if offset == 0: safe = (px + mo*scale, y0 + mt*scale, px + p_w - mi*scale, y0 + dh - mb*scale)
            else: safe = (px + mi*scale, y0 + mt*scale, px + p_w - mo*scale, y0 + dh - mb*scale)
            
            self.canvas.create_rectangle(*safe, outline="#ddd", dash=(2,4))
            
            rects = LayoutManager.get_layout_rects(page.layout_name)
            sp_px = page.spacing_mm * scale
            for r_idx, (rx, ry, rw, rh) in enumerate(rects):
                sx = safe[0] + rx * (safe[2]-safe[0]) + sp_px/2
                sy = safe[1] + ry * (safe[3]-safe[1]) + sp_px/2
                w = rw * (safe[2]-safe[0]) - sp_px
                h = rh * (safe[3]-safe[1]) - sp_px
                if w > 0 and h > 0:
                    outline_col = "#eee"
                    if isinstance(self.selected_item, PhotoItem) and self.selected_item in page.photos and self.selected_item.slot_index == r_idx:
                        outline_col = COLOR_HIGHLIGHT
                    self.canvas.create_rectangle(sx, sy, sx+w, sy+h, outline=outline_col, width=2 if outline_col==COLOR_HIGHLIGHT else 1)
                    
                    photo = next((p for p in page.photos if p.slot_index == r_idx), None)
                    if photo:
                        cache_key = (photo.path, int(w), int(h), photo.rotation)
                        if cache_key in self.preview_image_cache:
                            tk_img = self.preview_image_cache[cache_key]
                            self.canvas.create_image(sx + w/2, sy + h/2, image=tk_img)
                        else:
                            if os.path.exists(photo.path):
                                try:
                                    pil = Image.open(photo.path)
                                    if photo.rotation: pil = pil.rotate(-photo.rotation, expand=True)
                                    pil.thumbnail((int(w), int(h)))
                                    tk_img = ImageTk.PhotoImage(pil)
                                    self.preview_image_cache[cache_key] = tk_img
                                    self.canvas.create_image(sx + w/2, sy + h/2, image=tk_img)
                                except: pass
                                
            for txt in page.texts:
                fnt = load_font(txt.font_family, int(txt.font_size))
                dummy = ImageDraw.Draw(Image.new("RGBA", (1,1)))
                bbox = dummy.textbbox((0,0), txt.text, font=fnt)
                txt_img = Image.new("RGBA", (bbox[2]-bbox[0]+20, bbox[3]-bbox[1]+20), (0,0,0,0))
                d = ImageDraw.Draw(txt_img)
                d.text((10,10), txt.text, font=fnt, fill=txt.color)
                if txt.rotation != 0: txt_img = txt_img.rotate(txt.rotation, expand=True, resample=Image.BICUBIC)
                tk_txt = ImageTk.PhotoImage(txt_img)
                self._draw_refs.append(tk_txt) 
                
                pos_x = px + txt.x_rel * p_w
                pos_y = y0 + txt.y_rel * dh
                self.canvas.create_image(pos_x, pos_y, image=tk_txt, tags="text")
                if self.selected_item == txt:
                    self.canvas.create_rectangle(pos_x-10, pos_y-10, pos_x+10, pos_y+10, outline=COLOR_HIGHLIGHT, width=2)
            self.canvas.create_text(px + p_w/2, y0 + dh + 15, text=f"P{p_idx+1}", fill="white")

    # --- Interaction ---
    def _on_canvas_drop(self, event):
        if not self.drag_data.get("path"): return
        p_idx, s_idx = self._hit_test(event.x, event.y)
        if p_idx != -1 and s_idx != -1:
            self._save_history()
            page = self.project.pages[p_idx]
            page.photos = [p for p in page.photos if p.slot_index != s_idx]
            new_photo = PhotoItem(path=self.drag_data["path"], slot_index=s_idx)
            page.photos.append(new_photo)
            self.draw_preview()
            self._select_item(p_idx, new_photo)
            self._refresh_ui_from_project(rebuild_mode="full")
            self._refresh_thumbnails() # ドロップ時に枚数カウント更新
        self.drag_data["path"] = None

    def _on_canvas_click(self, event):
        p_idx, txt_item = self._hit_test_text(event.x, event.y)
        if txt_item:
            self._select_item(p_idx, txt_item)
            self.drag_data["item"] = txt_item
            self.drag_data["p_idx"] = p_idx
            return

        if self.is_text_mode:
            p_idx, _ = self._hit_test(event.x, event.y) 
            if p_idx != -1:
                text = simpledialog.askstring("入力", "テキスト:")
                if text:
                    self._save_history()
                    metrics = self._get_draw_metrics()
                    x0, y0, dw, dh, _ = metrics
                    page_w = dw/2
                    
                    offset = -1
                    if self.is_cover_mode and self.project.current_spread_index == 0:
                        if p_idx == self._get_current_spread_pages()[0]: offset = 1
                    else:
                        current_pages = self._get_current_spread_pages()
                        if p_idx == current_pages[0]: offset = 0
                        elif len(current_pages)>1 and p_idx == current_pages[1]: offset = 1

                    page_x = x0 + (offset * page_w)
                    rel_x = (event.x - page_x) / page_w
                    rel_y = (event.y - y0) / dh
                    new_txt = TextItem(text=text, x_rel=rel_x, y_rel=rel_y)
                    self.project.pages[p_idx].texts.append(new_txt)
                    self._select_item(p_idx, new_txt)
                    self._refresh_ui_from_project(rebuild_mode="full")
            self._toggle_text_mode()
            return

        if self.drag_data.get("path") and not self.drag_data.get("item"):
             p_idx, s_idx = self._hit_test(event.x, event.y)
             if p_idx != -1 and s_idx != -1:
                 self._save_history()
                 page = self.project.pages[p_idx]
                 page.photos = [p for p in page.photos if p.slot_index != s_idx]
                 new_photo = PhotoItem(path=self.drag_data["path"], slot_index=s_idx)
                 page.photos.append(new_photo)
                 self._select_item(p_idx, new_photo)
                 self.draw_preview()
                 self._refresh_ui_from_project(rebuild_mode="full")
                 self._refresh_thumbnails() # クリック配置時にカウント更新
                 return 
                 
        p_idx, s_idx = self._hit_test(event.x, event.y)
        if p_idx != -1 and s_idx != -1:
             page = self.project.pages[p_idx]
             existing = next((p for p in page.photos if p.slot_index == s_idx), None)
             if existing: self._select_item(p_idx, existing)
             else: self._select_item(-1, None)
        else:
             self._select_item(-1, None)
        
        self.draw_preview()

    def _on_canvas_drag(self, event):
        item = self.drag_data.get("item")
        if item and isinstance(item, TextItem):
            metrics = self._get_draw_metrics()
            x0, y0, dw, dh, _ = metrics
            page_w = dw/2
            p_idx = self.drag_data["p_idx"]
            
            offset = 0
            if self.is_cover_mode and self.project.current_spread_index == 0: offset = 1
            else:
                 current_pages = self._get_current_spread_pages()
                 if len(current_pages) > 1 and p_idx == current_pages[1]: offset = 1
            
            page_x = x0 + (offset * page_w)
            item.x_rel = (event.x - page_x) / page_w
            item.y_rel = (event.y - y0) / dh
            self.draw_preview()

    def _on_canvas_release(self, event):
        if self.drag_data.get("item"): self._save_history()
        self.drag_data["item"] = None

    def _on_canvas_right_click(self, event):
        self._on_canvas_click(event)

    def _save_project(self):
        if self.current_project_path:
            self._save_file_to_path(self.current_project_path)
        else:
            self._save_project_as()

    def _save_project_as(self):
        path = filedialog.asksaveasfilename(defaultextension=".hbs", filetypes=[("HBS Project", "*.hbs")])
        if not path: return
        self.current_project_path = path
        self._save_file_to_path(path)

    def _save_file_to_path(self, path):
        try:
            data = asdict(self.project)
            with open(path, "w") as f: json.dump(data, f, indent=2)
            messagebox.showinfo("保存", "保存完了")
        except Exception as e:
            messagebox.showerror("エラー", f"保存失敗: {e}")

    def _load_project(self):
        path = filedialog.askopenfilename(filetypes=[("HBS Project", "*.hbs")])
        if not path: return
        try:
            with open(path, "r") as f: data = json.load(f)
            self.project = Project(**data)
            self.current_project_path = path 
            raw_pages = data.get("pages", [])
            self.project.pages = []
            for p in raw_pages:
                pg = Page(layout_name=p.get("layout_name", "1枚 (全面)"), spacing_mm=p.get("spacing_mm", 0.0), custom_margins=p.get("custom_margins"), background_color=p.get("background_color", "#FFFFFF"))
                for ph in p.get("photos", []):
                    pg.photos.append(PhotoItem(path=ph["path"], slot_index=ph.get("slot_index",0), rotation=ph.get("rotation",0)))
                for txt in p.get("texts", []):
                    pg.texts.append(TextItem(text=txt["text"], x_rel=txt["x_rel"], y_rel=txt["y_rel"], font_size=txt.get("font_size",40), color=txt.get("color","black"), rotation=txt.get("rotation",0)))
                self.project.pages.append(pg)
            self.preview_image_cache.clear()
            self._refresh_ui_from_project(rebuild_mode="full")
            self._refresh_thumbnails()
        except Exception as e:
            messagebox.showerror("エラー", f"読込失敗: {e}")

    def _start_export(self):
        out_dir = filedialog.askdirectory(title="出力先フォルダ")
        if not out_dir: return
        self.is_export_cancelled = False 
        self.header_status_label.configure(text="書き出し中...")
        self.header_status_label.pack(side="left", padx=5)
        self.header_progress.pack(side="left", padx=5, fill="x", expand=True)
        self.header_cancel_btn.pack(side="left", padx=2) 
        self.header_progress.set(0)
        threading.Thread(target=self._export_worker, args=(out_dir,), daemon=True).start()

    def _cancel_export(self):
        self.is_export_cancelled = True
        self.header_status_label.configure(text="キャンセル中...")

    def _export_worker(self, out_dir):
        try:
            total = len(self.project.pages)
            if total % 2 == 1: total += 1
            def update_prog(val): self.header_progress.set(val)
            if self.var_keep_orig.get(): self._export_original(out_dir, total, update_prog)
            else: self._export_canvas(out_dir, total, update_prog)
            
            if not self.is_export_cancelled:
                self.after(0, lambda: [messagebox.showinfo("完了", "出力完了"), self._hide_export_status()])
            else:
                 self.after(0, lambda: [messagebox.showinfo("キャンセル", "書き出しをキャンセルしました"), self._hide_export_status()])
        except Exception as e:
            traceback.print_exc()
            self.after(0, lambda: [messagebox.showerror("エラー", str(e)), self._hide_export_status()])

    def _hide_export_status(self):
        self.header_status_label.pack_forget()
        self.header_progress.pack_forget()
        self.header_cancel_btn.pack_forget()

    def _export_original(self, out_dir, total, progress_cb):
        imgs = []
        for i in range(total):
            if self.is_export_cancelled: return
            progress_cb(i / total)
            if i < len(self.project.pages) and self.project.pages[i].photos:
                p_item = self.project.pages[i].photos[0]
                try:
                    im = Image.open(p_item.path)
                    if p_item.rotation: im = im.rotate(-p_item.rotation, expand=True)
                    imgs.append(im)
                except: imgs.append(Image.new("RGB", (100,100), "white"))
            else: imgs.append(Image.new("RGB", (100,100), "white"))
        
        if not self.is_export_cancelled:
            self._save_images(out_dir, imgs)

    def _export_canvas(self, out_dir, total, progress_cb):
        dpi = self.config_data["export_dpi"]
        size_key = self.project.paper_size if self.project.paper_size in PAPER_SIZES else "A4"
        pw_mm, ph_mm = PAPER_SIZES[size_key]
        if self.project.orientation == "Landscape": pw_mm, ph_mm = ph_mm, pw_mm
        px_w = int(math.ceil(pw_mm * MM_TO_INCH * dpi))
        px_h = int(math.ceil(ph_mm * MM_TO_INCH * dpi))
        scale = dpi / 25.4
        imgs = []
        for i in range(total):
            if self.is_export_cancelled: return
            progress_cb(i / total)
            if i < len(self.project.pages): page = self.project.pages[i]
            else: page = Page()
            canvas = Image.new("RGB", (px_w, px_h), page.background_color)
            draw = ImageDraw.Draw(canvas)
            mt, mb, mi, mo = self._get_page_margins(page)
            
            is_left_page = (i % 2 == 0)

            if self.is_cover_mode:
                is_left_page = (i % 2 != 0)

            if is_left_page:
                ml, mr = mo, mi
            else:
                ml, mr = mi, mo
            
            safe_x_px = ml * scale; safe_y_px = mt * scale
            safe_w_px = px_w - (ml+mr) * scale; safe_h_px = px_h - (mt+mb) * scale
            
            rects = LayoutManager.get_layout_rects(page.layout_name)
            sp_px = page.spacing_mm * scale
            for r_idx, (rx, ry, rw, rh) in enumerate(rects):
                slot_x = safe_x_px + rx * safe_w_px + sp_px/2
                slot_y = safe_y_px + ry * safe_h_px + sp_px/2
                slot_w = rw * safe_w_px - sp_px
                slot_h = rh * safe_h_px - sp_px 
                photo = next((p for p in page.photos if p.slot_index == r_idx), None)
                if photo and slot_w > 0 and slot_h > 0:
                    try:
                        im = Image.open(photo.path).convert("RGB")
                        if photo.rotation: im = im.rotate(-photo.rotation, expand=True)
                        
                        im.thumbnail((int(slot_w), int(slot_h)), Image.LANCZOS)
                        
                        iw, ih = im.size
                        paste_x = int(slot_x + (slot_w - iw) / 2)
                        paste_y = int(slot_y + (slot_h - ih) / 2)
                        
                        canvas.paste(im, (paste_x, paste_y))
                    except: pass
            
            for txt in page.texts:
                fnt_size_px = int(txt.font_size * (dpi / 72)) 
                fnt = load_font(txt.font_family, fnt_size_px)
                dummy = ImageDraw.Draw(Image.new("RGBA", (1,1)))
                bbox = dummy.textbbox((0,0), txt.text, font=fnt)
                txt_img = Image.new("RGBA", (bbox[2]-bbox[0]+100, bbox[3]-bbox[1]+100), (0,0,0,0))
                d = ImageDraw.Draw(txt_img)
                d.text((50,50), txt.text, font=fnt, fill=txt.color)
                if txt.rotation: txt_img = txt_img.rotate(txt.rotation, expand=True, resample=Image.BICUBIC)
                paste_x = int(txt.x_rel * px_w) - txt_img.width // 2
                paste_y = int(txt.y_rel * px_h) - txt_img.height // 2
                canvas.paste(txt_img, (paste_x, paste_y), txt_img)
            imgs.append(canvas)
        
        if not self.is_export_cancelled:
            self._save_images(out_dir, imgs)

    def _save_images(self, out_dir, all_images):
        front = all_images[0::2]; back = all_images[1::2]
        if self.var_rev_back.get(): back.reverse()
        if self.var_rot_back.get(): back = [im.rotate(180, expand=True) for im in back]
        
        if self.var_output_fmt.get() == "PDF":
            if front: front[0].save(os.path.join(out_dir, "export_front.pdf"), save_all=True, append_images=front[1:])
            if back: back[0].save(os.path.join(out_dir, "export_back.pdf"), save_all=True, append_images=back[1:])
        else:
            for i, im in enumerate(front): im.save(os.path.join(out_dir, f"front_{i+1:02d}.jpg"), quality=95)
            for i, im in enumerate(back): im.save(os.path.join(out_dir, f"back_{i+1:02d}.jpg"), quality=95)

if __name__ == "__main__":
    app = HomeBookStudio()
    app.mainloop()