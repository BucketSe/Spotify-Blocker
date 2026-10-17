"""
Ad Guard for Spotify - Windows desktop app.

Watches the Spotify desktop client. When an ad starts playing it either
  * mutes the ad until it is over (Spotify keeps running, nothing restarts), or
  * closes Spotify, relaunches it and resumes playback (skips the ad).
It also shows what is playing, with album art and Previous / Play / Next buttons,
and keeps a history of blocked ads.

Install:   py -m pip install psutil pycaw comtypes customtkinter pillow
Optional (album art, exact pause detection, controls aimed only at Spotify):
           py -m pip install winrt-runtime winrt-Windows.Media.Control winrt-Windows.Storage.Streams winrt-Windows.Foundation winrt-Windows.Foundation.Collections
Run:       py spotify_ad_guard.py
Build EXE: py -m pip install pyinstaller
           py -m PyInstaller --noconfirm --onedir --windowed --icon adguard.ico --collect-all customtkinter --collect-submodules winrt --name AdGuard spotify_ad_guard.py
           (then zip the dist/AdGuard folder to share it)
"""

import ctypes
import json
import math
import os
import queue
import subprocess
import sys
import tempfile
import threading
import time
import tkinter as tk
import tkinter.font as tkfont
from ctypes import wintypes
from datetime import date, datetime
from io import BytesIO

import comtypes
import customtkinter as ctk
import psutil
from PIL import Image, ImageChops, ImageDraw, ImageFilter, ImageOps, ImageTk
from pycaw.pycaw import AudioUtilities, IAudioMeterInformation, ISimpleAudioVolume

try:  # optional: Windows' media controls (album art, exact play/pause, targeted buttons)
    import asyncio
    from winrt.windows.media.control import (
        GlobalSystemMediaTransportControlsSessionManager as _SmtcManager)
    from winrt.windows.storage.streams import DataReader as _DataReader
    HAVE_SMTC = True
except Exception:  # not installed: everything still works from window titles and sound
    HAVE_SMTC = False

user32 = ctypes.windll.user32
user32.IsIconic.argtypes = [wintypes.HWND]
user32.ShowWindowAsync.argtypes = [wintypes.HWND, ctypes.c_int]

APP_VERSION = "3.0.0"
APP_ID = "AdGuard.SpotifyAdGuard.1"
RESAMPLE = Image.Resampling

# ---------- Detection settings ----------

AD_TITLES = {"Advertisement", "Spotify", "Spotify Free", "Spotify Premium"}
IGNORE_TITLES = {"Chrome Legacy Window", "Default IME", "MSCTFIME UI", "GDI+ Window"}

POLL_SECONDS = 0.1      # how often to check for an ad (lower = faster reaction)
AD_CONFIRM_SURE = 0.25  # seconds an 'Advertisement' title (with sound) must last before restarting
AD_CONFIRM_MAYBE = 1.5  # same for generic titles ('Spotify Free'...) that also mean 'paused'
MUTE_CONFIRM_SURE = 0.1  # muting is harmless if wrong, so it reacts faster than a restart
MUTE_CONFIRM_MAYBE = 0.7
MUTE_END_CONFIRM = 0.15  # a song title must last this long before the sound comes back
MUTE_MAX_HOLD = 180.0   # never keep Spotify muted longer than this (safety net)
AD_ESTIMATE = 30        # seconds an ad is assumed to last when a restart skips it
MEDIA_POLL = 0.4        # how often the Windows media session is read
LOOP_LIMIT = 6          # this many restarts within LOOP_WINDOW seconds means something is wrong
LOOP_WINDOW = 60.0
LOOP_BACKOFF = 30.0     # then leave Spotify alone for this long
PAUSE_GRACE = 2.0       # after a click / Space / Play-Pause, a generic title is not an ad
SOUND_THRESHOLD = 0.001 # quieter than this counts as silence
RELAUNCH_WAIT = 0.2     # extra pause after the Spotify window appears
AUTOPLAY_CHECK = 2.0    # seconds to wait for Spotify to resume by itself
COOLDOWN = 2.0          # pause after a restart before watching again
PID_REFRESH = 2.0       # how often to re-scan for Spotify processes
METER_REFRESH = 3.0     # how often to re-scan Spotify's audio sessions
VOLUME_BOOT = 10.0      # seconds after Spotify's audio starts when it may still reset its volume
VOLUME_BOOT_MAX = 45.0  # stop waiting for Spotify's audio to start after this long
VOLUME_FIXES = 6        # most start-up resets undone per restart (never fight forever)
QUIET_HOLD = 8.0        # seconds to keep Spotify minimized after a quiet restart
SW_SHOWMINNOACTIVE = 7  # Windows: minimize a window without activating it

CLASSIC_PATH = os.path.expandvars(r"%APPDATA%\Spotify\Spotify.exe")
STORE_LAUNCH = r"shell:AppsFolder\SpotifyAB.SpotifyMusic_zpdnekdrzrea0!Spotify"

# ---------- User settings (saved between launches) ----------

SETTINGS_DIR = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), "AdGuard")
SETTINGS_FILE = os.path.join(SETTINGS_DIR, "settings.json")
HISTORY_MAX = 3000          # blocked ads remembered for the charts
DEFAULT_SETTINGS = {
    "theme": "dark",
    "animations": True,
    "ambience": "nebula",     # glow colors and accent, see AMBIENCES
    "on_top": False,
    "verbose": False,
    "mode": "restart",        # "restart" = reopen Spotify, "mute" = silence the ad
    "after_ad": "next",
    "quiet_restart": True,
    "auto_start": True,       # start protecting as soon as the app opens
    "windows_startup": False,
    "lifetime_ads": 0,
    "lifetime_saved": 0,
    "history": [],            # [unix time, seconds saved, "m" (muted) or "r" (restarted)]
    "muted_by_us": False,     # Spotify was muted by Ad Guard (cleared when it is restored)
}


def load_settings():
    cfg = dict(DEFAULT_SETTINGS)
    try:
        with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        for k in cfg:
            if k in data and isinstance(data[k], type(cfg[k])):
                cfg[k] = data[k]
    except Exception:
        pass
    if cfg["theme"] not in ("dark", "light"):
        cfg["theme"] = "dark"
    if cfg["after_ad"] not in ("next", "resume"):
        cfg["after_ad"] = "next"
    if cfg["mode"] not in ("restart", "mute"):
        cfg["mode"] = "restart"
    if cfg["ambience"] not in AMBIENCES:
        cfg["ambience"] = "nebula"
    history = []
    for e in cfg["history"]:
        try:
            history.append([int(e[0]), int(e[1]), "m" if e[2] == "m" else "r"])
        except Exception:
            pass
    cfg["history"] = history[-HISTORY_MAX:]
    return cfg


_SAVE_LOCK = threading.Lock()


def save_settings(cfg):
    """Written from the window and from the worker thread, so one at a time."""
    try:
        with _SAVE_LOCK:
            os.makedirs(SETTINGS_DIR, exist_ok=True)
            tmp = SETTINGS_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(cfg, f, indent=2)
            os.replace(tmp, SETTINGS_FILE)  # never leaves a half-written file behind
    except Exception:
        pass


# ---------- Colors ----------

# Canvas colors are hex strings; glass layers are RGBA tuples blended over the background.
PALETTES = {
    "dark": dict(
        BG=(8, 7, 17), BG2=(13, 10, 28), SURFACE="#16132b",
        TEXT="#f5f3ff", MUTED="#a5a0bf", FAINT="#6f6a8c", ON_ACCENT="#ffffff",
        GREEN="#3ddc97", AMBER="#ffb547", RED="#ff6170", BLUE="#66abff",
        GLASS=(255, 255, 255, 13), SHEEN=(255, 255, 255, 18), EDGE=(255, 255, 255, 40),
        EDGE_LOW=(255, 255, 255, 12), SHADOW=(0, 0, 0, 120), CHIP=(255, 255, 255, 16),
        CHIP_HOVER=(255, 255, 255, 30), TRACK=(255, 255, 255, 26), LINE=(255, 255, 255, 20),
        TIP=(26, 22, 48, 246), BLOB=0.62,
    ),
    "light": dict(
        BG=(237, 238, 250), BG2=(229, 227, 247), SURFACE="#f6f5fd",
        TEXT="#16132c", MUTED="#5c5878", FAINT="#938fae", ON_ACCENT="#ffffff",
        GREEN="#129a62", AMBER="#c27806", RED="#d93447", BLUE="#2a72de",
        GLASS=(255, 255, 255, 135), SHEEN=(255, 255, 255, 90), EDGE=(255, 255, 255, 235),
        EDGE_LOW=(255, 255, 255, 110), SHADOW=(60, 48, 140, 34), CHIP=(30, 24, 80, 13),
        CHIP_HOVER=(30, 24, 80, 26), TRACK=(30, 24, 80, 22), LINE=(30, 24, 80, 20),
        TIP=(255, 255, 255, 250), BLOB=0.34,
    ),
}

# Ambience = the colored light behind the glass plus the accent gradient used everywhere.
AMBIENCES = {
    "nebula": dict(name="Nebula", a1=(124, 92, 255), a2=(214, 96, 255),
                   blobs=[(112, 68, 255), (38, 92, 255), (196, 64, 236), (72, 40, 210)]),
    "aurora": dict(name="Aurora", a1=(29, 205, 110), a2=(30, 196, 222),
                   blobs=[(18, 170, 112), (22, 120, 210), (36, 200, 160), (40, 70, 190)]),
    "ember": dict(name="Ember", a1=(255, 112, 64), a2=(255, 64, 150),
                  blobs=[(232, 82, 44), (206, 40, 120), (250, 128, 60), (120, 40, 170)]),
    "ocean": dict(name="Ocean", a1=(56, 132, 255), a2=(48, 210, 255),
                  blobs=[(30, 86, 232), (20, 168, 222), (70, 56, 210), (18, 122, 204)]),
}
AMBIENCE_ORDER = ["nebula", "aurora", "ember", "ocean"]


def hex_to_rgb(h):
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


def rgb_to_hex(c):
    return "#%02x%02x%02x" % tuple(max(0, min(255, int(round(v)))) for v in c[:3])


def _rgb(c):
    return hex_to_rgb(c) if isinstance(c, str) else tuple(c[:3])


def mix(c1, c2, a):
    c1, c2 = _rgb(c1), _rgb(c2)
    return tuple(c1[i] + (c2[i] - c1[i]) * a for i in range(3))


def _i(c):
    return tuple(max(0, min(255, int(round(v)))) for v in c)


def rgba(c, a):
    return _i(_rgb(c)) + (max(0, min(255, int(a))),)


def lerp_hex(h1, h2, a):
    return rgb_to_hex(mix(h1, h2, a))


def ease_out(p):
    return 1.0 - (1.0 - p) ** 3


def ease_in_out(p):
    return 4 * p ** 3 if p < 0.5 else 1 - (-2 * p + 2) ** 3 / 2


def _scale_alpha(im, f):
    im.putalpha(im.getchannel("A").point(lambda v: int(v * f)))
    return im


# ---------- Shapes ----------

_GRAD = {}


def _grad(size, horizontal):
    """Grayscale ramp (0 -> 255) across `size`, left->right or top->bottom."""
    key = (size, horizontal)
    if key not in _GRAD:
        if len(_GRAD) > 64:
            _GRAD.clear()
        g = Image.linear_gradient("L")
        if horizontal:
            g = g.transpose(Image.Transpose.TRANSPOSE)
        _GRAD[key] = g.resize(size, RESAMPLE.BILINEAR)
    return _GRAD[key]


def _vgrad(w, h, top, bottom):
    return ImageOps.colorize(_grad((max(1, w), max(1, h)), False), black=_i(top), white=_i(bottom))


def _rr_mask(size, box, r):
    m = Image.new("L", size, 0)
    ImageDraw.Draw(m).rounded_rectangle(box, radius=max(0, r), fill=255)
    return m


_SHAPES = {}


def shape_image(w, h, r, scale, fill=None, grad=None, edge=None, glow=None, sheen=0,
                pad=0, ss=3):
    """Anti-aliased rounded rectangle at `scale`, with optional parts:
    fill (RGBA) or grad ((rgb1, rgb2) left -> right), a 1px edge (RGBA), a top sheen
    (0-255) and a soft glow (RGBA) that spills `pad` px around it."""
    key = (w, h, r, scale, fill, grad, edge, glow, sheen, pad)
    if key in _SHAPES:
        return _SHAPES[key]
    W, H = max(2, round((w + 2 * pad) * scale)), max(2, round((h + 2 * pad) * scale))
    out = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    if glow:
        g = Image.new("RGBA", (W, H), glow[:3] + (0,))
        g.putalpha(_rr_mask((W, H), (pad * scale, (pad + 3) * scale, (pad + w) * scale,
                                     (pad + h) * scale), r * scale).point(
            lambda v: v * glow[3] // 255))
        out = g.filter(ImageFilter.GaussianBlur(max(1, pad * scale * 0.42)))
    S = (W * ss, H * ss)
    k = scale * ss
    box = (pad * k, pad * k, (pad + w) * k - 1, (pad + h) * k - 1)
    mask = _rr_mask(S, box, r * k)
    if grad:
        body = ImageOps.colorize(_grad(S, True), black=_i(grad[0]), white=_i(grad[1])).convert("RGBA")
        body.putalpha(mask)
    elif fill:
        body = Image.new("RGBA", S, fill[:3] + (0,))
        body.putalpha(mask.point(lambda v: v * fill[3] // 255))
    else:
        body = Image.new("RGBA", S, (0, 0, 0, 0))
    if sheen:
        ramp = _grad(S, False).point(lambda v: max(0, int(sheen * (1 - v / 110.0))))
        layer = Image.new("RGBA", S, (255, 255, 255, 0))
        layer.putalpha(ImageChops.multiply(ramp, mask))
        body = Image.alpha_composite(body, layer)
    if edge:
        bw = max(1, round(k))
        inner = _rr_mask(S, (box[0] + bw, box[1] + bw, box[2] - bw, box[3] - bw), r * k - bw)
        ring = ImageChops.subtract(mask, inner).point(lambda v: v * edge[3] // 255)
        layer = Image.new("RGBA", S, edge[:3] + (0,))
        layer.putalpha(ring)
        body = Image.alpha_composite(body, layer)
    out.alpha_composite(body.resize((W, H), RESAMPLE.LANCZOS))
    if len(_SHAPES) > 400:
        _SHAPES.clear()
    _SHAPES[key] = out
    return out


GLASS_PAD = 24  # room around a glass card for its shadow


def glass_image(w, h, r, scale, P, lines=(), ss=2):
    """A frosted glass card: soft shadow, translucent body, top sheen, a 1px edge that is
    brighter at the top, and optional hairline dividers (card coordinates)."""
    key = ("glass", w, h, r, scale, P["GLASS"], P["EDGE"], tuple(lines))
    if key in _SHAPES:
        return _SHAPES[key]
    m = GLASS_PAD
    W, H = round((w + 2 * m) * scale), round((h + 2 * m) * scale)
    shadow = Image.new("RGBA", (W, H), P["SHADOW"][:3] + (0,))
    shadow.putalpha(_rr_mask((W, H), (m * scale, (m + 10) * scale, (m + w) * scale,
                                      (m + h + 4) * scale), r * scale).point(
        lambda v: v * P["SHADOW"][3] // 255))
    out = shadow.filter(ImageFilter.GaussianBlur(14 * scale))

    S = (W * ss, H * ss)
    k = scale * ss
    box = (m * k, m * k, (m + w) * k - 1, (m + h) * k - 1)
    mask = _rr_mask(S, box, r * k)
    body = Image.new("RGBA", S, P["GLASS"][:3] + (0,))
    body.putalpha(mask.point(lambda v: v * P["GLASS"][3] // 255))
    top = m / (h + 2 * m)
    sheen_a = P["SHEEN"][3]
    ramp = _grad(S, False).point(
        lambda v: max(0, int(sheen_a * (1 - max(0.0, v / 255.0 - top) / 0.35))))
    layer = Image.new("RGBA", S, (255, 255, 255, 0))
    layer.putalpha(ImageChops.multiply(ramp, mask))
    body = Image.alpha_composite(body, layer)

    bw = max(1, round(k))
    inner = _rr_mask(S, (box[0] + bw, box[1] + bw, box[2] - bw, box[3] - bw), r * k - bw)
    ring = ImageChops.subtract(mask, inner)
    hi, lo = P["EDGE"][3], P["EDGE_LOW"][3]
    fade = _grad(S, False).point(lambda v: int(hi + (lo - hi) * min(1.0, v / 255.0 * 1.6)))
    edge = Image.new("RGBA", S, P["EDGE"][:3] + (0,))
    edge.putalpha(ImageChops.multiply(ring, fade))
    body = Image.alpha_composite(body, edge)
    if lines:  # drawn on their own layer so they blend over the glass instead of replacing it
        layer = Image.new("RGBA", S, P["LINE"][:3] + (0,))
        d = ImageDraw.Draw(layer)
        for x0, y0, x1, y1 in lines:
            d.line(((m + x0) * k, (m + y0) * k, (m + x1) * k, (m + y1) * k),
                   fill=P["LINE"], width=bw)
        body = Image.alpha_composite(body, layer)
    out.alpha_composite(body.resize((W, H), RESAMPLE.LANCZOS))
    _SHAPES[key] = out
    return out


def rounded(im, radius):
    im = im.convert("RGBA")
    im.putalpha(_rr_mask(im.size, (0, 0, im.size[0] - 1, im.size[1] - 1), radius))
    return im


# ---------- Logo ----------

def _bezier(p0, p1, p2, n=16):
    pts = []
    for i in range(n + 1):
        t = i / n
        pts.append(((1 - t) ** 2 * p0[0] + 2 * (1 - t) * t * p1[0] + t * t * p2[0],
                    (1 - t) ** 2 * p0[1] + 2 * (1 - t) * t * p1[1] + t * t * p2[1]))
    return pts


SHIELD = ([(0.50, 0.12), (0.83, 0.24), (0.83, 0.50)]
          + _bezier((0.83, 0.50), (0.83, 0.75), (0.50, 0.90))[1:]
          + _bezier((0.50, 0.90), (0.17, 0.75), (0.17, 0.50))[1:]
          + [(0.17, 0.24)])

_LOGO_BASE = {}


def _diag(S, c1, c2):
    """Square with a diagonal gradient, c1 at the top-left to c2 at the bottom-right."""
    tiny = Image.new("L", (2, 2))
    tiny.putdata([0, 128, 128, 255])
    g = tiny.resize((S, S), RESAMPLE.BILINEAR)
    g = ImageOps.autocontrast(g)
    return ImageOps.colorize(g, black=_i(c1), white=_i(c2))


def _logo_base(S, amb):
    key = (S, amb)
    if key not in _LOGO_BASE:
        if len(_LOGO_BASE) > 24:
            _LOGO_BASE.clear()
        a = AMBIENCES[amb]
        base = _diag(S, mix(a["a1"], (255, 255, 255), 0.12), mix(a["a2"], (0, 0, 0), 0.10))
        base = base.convert("RGBA")
        base.putalpha(_rr_mask((S, S), (0, 0, S - 1, S - 1), int(S * 0.27)))
        _LOGO_BASE[key] = base
    return _LOGO_BASE[key]


def make_logo(size=256, bars=(0.45, 1.0, 0.7), ss=4, amb="nebula"):
    """Shield with three equalizer bars on a rounded square in the accent gradient."""
    S = int(size * ss)
    img = _logo_base(S, amb).copy()
    d = ImageDraw.Draw(img)
    d.polygon([(x * S, y * S) for x, y in SHIELD], fill=(255, 255, 255, 255))
    bar = _i(mix(AMBIENCES[amb]["a1"], (20, 10, 60), 0.35)) + (255,)
    max_h, bw, gap = 0.36, 0.075, 0.052
    x0 = 0.5 - (3 * bw + 2 * gap) / 2
    for i, b in enumerate(bars):
        hh = max_h * max(0.12, min(1.0, b))
        x = x0 + i * (bw + gap)
        d.rounded_rectangle((x * S, (0.5 - hh / 2) * S, (x + bw) * S, (0.5 + hh / 2) * S),
                            radius=bw * S / 2, fill=bar)
    return img.resize((int(size), int(size)), RESAMPLE.LANCZOS)


def ensure_icon(amb="nebula"):
    path = os.path.join(tempfile.gettempdir(), f"adguard_icon_{amb}_v3.ico")
    try:
        if not os.path.exists(path):
            make_logo(256, amb=amb).save(path, format="ICO",
                                         sizes=[(16, 16), (24, 24), (32, 32), (48, 48),
                                                (64, 64), (128, 128), (256, 256)])
        return path
    except Exception:
        return None


# ---------- Icons ----------

def make_dot(color, t, period, size=20, ss=4):
    """Status dot with expanding rings. period=None means no rings."""
    S = size * ss
    c = S / 2
    base = Image.new("RGBA", (S, S), (0, 0, 0, 0))
    color = _i(_rgb(color))
    if period:
        for k in range(2):
            p = ((t / period) + k * 0.5) % 1.0
            r = (S * 0.17) + (S * 0.31) * ease_out(p)
            a = int(150 * (1 - p) ** 1.5)
            layer = Image.new("RGBA", (S, S), (0, 0, 0, 0))
            ImageDraw.Draw(layer).ellipse((c - r, c - r, c + r, c + r),
                                          outline=color + (a,), width=max(1, int(S * 0.06)))
            base = Image.alpha_composite(base, layer)
    d = ImageDraw.Draw(base)
    r0 = S * 0.17
    d.ellipse((c - r0, c - r0, c + r0, c + r0), fill=color + (255,))
    return base.resize((size, size), RESAMPLE.LANCZOS)


def make_icon(kind, size, color, ss=4):
    """Filled transport icons (prev / play / pause / next / skip) at any size."""
    S = int(size * ss)
    im = Image.new("RGBA", (S, S), (0, 0, 0, 0))
    d = ImageDraw.Draw(im)
    c = _i(_rgb(color)) + (255,)

    def tri(x0, x1):  # triangle between x0 (flat side) and x1 (point)
        d.polygon([(x0 * S, 0.22 * S), (x0 * S, 0.78 * S), (x1 * S, 0.5 * S)], fill=c)

    if kind == "play":
        tri(0.33, 0.80)
    elif kind == "pause":
        for x in (0.28, 0.56):
            d.rounded_rectangle((x * S, 0.22 * S, (x + 0.16) * S, 0.78 * S), radius=0.05 * S, fill=c)
    elif kind == "next":
        tri(0.22, 0.66)
        d.rounded_rectangle((0.69 * S, 0.22 * S, 0.79 * S, 0.78 * S), radius=0.04 * S, fill=c)
    elif kind == "prev":
        tri(0.78, 0.34)
        d.rounded_rectangle((0.21 * S, 0.22 * S, 0.31 * S, 0.78 * S), radius=0.04 * S, fill=c)
    elif kind == "skip":  # double chevron: "skip this ad"
        for x in (0.16, 0.46):
            d.polygon([(x * S, 0.24 * S), ((x + 0.14) * S, 0.24 * S), ((x + 0.34) * S, 0.5 * S),
                       ((x + 0.14) * S, 0.76 * S), (x * S, 0.76 * S), ((x + 0.2) * S, 0.5 * S)],
                      fill=c)
    return im.resize((int(size), int(size)), RESAMPLE.LANCZOS)


FILLED_ICONS = {"play", "pause", "next", "prev", "skip"}
_ICONS = {}


def line_icon(name, size, color, stroke=2.0, ss=4):
    """Outline icons on a 24-unit grid (Lucide-like), drawn at `size` px."""
    color = _i(_rgb(color))
    key = (name, size, color, stroke)
    if key in _ICONS:
        return _ICONS[key]
    if name in FILLED_ICONS:
        _ICONS[key] = make_icon(name, size, color)
        return _ICONS[key]
    S = max(4, int(round(size * ss)))
    im = Image.new("RGBA", (S, S), (0, 0, 0, 0))
    d = ImageDraw.Draw(im)
    k = S / 24.0
    c = color + (255,)
    w = max(1, int(round(stroke * k)))

    def dot(x, y, r=None):
        r = (r if r is not None else stroke / 2) * k
        d.ellipse((x * k - r, y * k - r, x * k + r, y * k + r), fill=c)

    def line(*pts, closed=False):
        pts = list(pts)
        if closed:
            pts.append(pts[0])
        d.line([(x * k, y * k) for x, y in pts], fill=c, width=w, joint="curve")
        for x, y in pts:
            dot(x, y)

    def circle(x, y, r):
        d.ellipse(((x - r - stroke / 2) * k, (y - r - stroke / 2) * k,
                   (x + r + stroke / 2) * k, (y + r + stroke / 2) * k), outline=c, width=w)

    def rrect(x0, y0, x1, y1, r):
        h = stroke / 2
        d.rounded_rectangle(((x0 - h) * k, (y0 - h) * k, (x1 + h) * k, (y1 + h) * k),
                            radius=(r + h) * k, outline=c, width=w)

    def arc(x0, y0, x1, y1, a0, a1):
        h = stroke / 2
        d.arc(((x0 - h) * k, (y0 - h) * k, (x1 + h) * k, (y1 + h) * k), a0, a1, fill=c, width=w)

    if name == "dashboard":
        for x, y in ((3.5, 3.5), (13.5, 3.5), (3.5, 13.5), (13.5, 13.5)):
            rrect(x, y, x + 7, y + 7, 2)
    elif name == "activity":
        line((2.5, 12), (6.5, 12), (9.5, 4.5), (14.5, 19.5), (17.5, 12), (21.5, 12))
    elif name == "sliders":
        for y, kx in ((6, 15), (12, 8.5), (18, 13)):
            line((3.5, y), (kx - 2.6, y))
            line((kx + 2.6, y), (20.5, y))
            circle(kx, y, 2.2)
    elif name == "sun":
        circle(12, 12, 3.8)
        for i in range(8):
            a = math.pi / 4 * i
            line((12 + 7.2 * math.cos(a), 12 + 7.2 * math.sin(a)),
                 (12 + 9.4 * math.cos(a), 12 + 9.4 * math.sin(a)))
    elif name == "moon":
        m = Image.new("L", (S, S), 0)
        md = ImageDraw.Draw(m)
        md.ellipse((3.5 * k, 3.5 * k, 20.5 * k, 20.5 * k), fill=255)
        md.ellipse((9 * k, -1 * k, 25 * k, 15 * k), fill=0)
        im.paste(Image.new("RGBA", (S, S), c), (0, 0), m)
    elif name == "power":
        arc(4.5, 4.5, 19.5, 19.5, -55, 235)
        line((12, 2.8), (12, 10.5))
    elif name == "shield":
        pts = ([(12, 2.8), (19.5, 5.6), (19.5, 11.2)] + _bezier((19.5, 11.2), (19.5, 17.6), (12, 21.2))[1:]
               + _bezier((12, 21.2), (4.5, 17.6), (4.5, 11.2))[1:] + [(4.5, 5.6)])
        line(*pts, closed=True)
        line((8.8, 12), (11.1, 14.3), (15.4, 9.8))
    elif name == "clock":
        circle(12, 12, 9)
        line((12, 7), (12, 12), (15.5, 14))
    elif name == "zap":
        line((13, 2.5), (4.5, 13.5), (11.5, 13.5), (10.5, 21.5), (19.5, 10.5), (12.5, 10.5),
             closed=True)
    elif name == "volume_x":
        line((3.5, 9.5), (7.5, 9.5), (12.5, 5), (12.5, 19), (7.5, 14.5), (3.5, 14.5), closed=True)
        line((16.5, 9.5), (21, 14.5))
        line((21, 9.5), (16.5, 14.5))
    elif name == "refresh":
        arc(4, 4, 20, 20, 40, 320)
        line((19.8, 3.2), (18.6, 7.6), (14.2, 6.6))
    elif name == "music":
        line((9, 17.5), (9, 5.5), (20, 3.5), (20, 15.5))
        dot(6.4, 17.5, 2.9)
        dot(17.4, 15.5, 2.9)
    elif name == "folder":
        line((3, 6), (9.5, 6), (11.5, 8.5), (21, 8.5), (21, 19), (3, 19), closed=True)
    elif name == "arrow_right":
        line((5, 12), (19, 12))
        line((13, 6), (19, 12), (13, 18))
    elif name == "copy":
        rrect(8.5, 8.5, 20.5, 20.5, 2.5)
        line((15.5, 5.5), (15.5, 3.5), (3.5, 3.5), (3.5, 15.5), (5.5, 15.5))
    elif name == "trash":
        line((3.5, 6.5), (20.5, 6.5))
        line((9, 6.5), (9, 3.5), (15, 3.5), (15, 6.5))
        line((5.5, 6.5), (6.8, 20.5), (17.2, 20.5), (18.5, 6.5))
    elif name == "check":
        circle(12, 12, 9)
        line((8, 12.3), (10.8, 15), (16, 9.5))
    elif name == "alert":
        line((12, 3.5), (21.5, 20), (2.5, 20), closed=True)
        line((12, 9.5), (12, 13.8))
        dot(12, 16.8, 1.3)
    elif name == "info":
        circle(12, 12, 9)
        line((12, 11), (12, 16.5))
        dot(12, 7.8, 1.3)
    elif name == "pin":
        line((12, 15.5), (12, 21.5))
        line((7, 15.5), (17, 15.5), (15.5, 11), (15.5, 4), (8.5, 4), (8.5, 11), closed=True)
    out = im.resize((int(size), int(size)), RESAMPLE.LANCZOS)
    if len(_ICONS) > 600:
        _ICONS.clear()
    _ICONS[key] = out
    return out


# ---------- Art ----------

def art_from_bytes(data, size, radius):
    """Album art bytes -> square, rounded RGBA image (None if the data is not an image)."""
    try:
        im = Image.open(BytesIO(data)).convert("RGBA")
        if all(hi - lo < 8 for lo, hi in im.convert("RGB").getextrema()):
            return None  # a blank (one-color) thumbnail: show the placeholder instead
        if im.getextrema()[3][0] < 255:  # transparent parts: put them on a dark tile
            im = Image.alpha_composite(Image.new("RGBA", im.size, (24, 20, 40, 255)), im)
        im = im.convert("RGB")
        w, h = im.size
        side = min(w, h)
        im = im.crop(((w - side) // 2, (h - side) // 2, (w - side) // 2 + side,
                      (h - side) // 2 + side)).resize((size, size), RESAMPLE.LANCZOS)
        return rounded(im, radius)
    except Exception:
        return None


def placeholder_art(size, radius, c1, c2, icon, surface):
    """Stand-in cover: a soft gradient tile with a line icon."""
    tile = _diag(size, mix(surface, c1, 0.55), mix(surface, c2, 0.30)).convert("RGBA")
    ic = line_icon(icon, int(size * 0.34), (255, 255, 255), stroke=1.8)
    ic = _scale_alpha(ic.copy(), 0.9)
    tile.alpha_composite(ic, ((size - ic.size[0]) // 2, (size - ic.size[1]) // 2))
    return rounded(tile, radius)


def art_glow(img, pad, strength):
    """Colored halo from the cover itself: a blurred, padded copy placed under it."""
    w, h = img.size
    out = Image.new("RGBA", (w + 2 * pad, h + 2 * pad), (0, 0, 0, 0))
    small = img.resize((max(4, w // 4), max(4, h // 4)), RESAMPLE.BILINEAR)
    small = small.resize((w, h), RESAMPLE.BILINEAR)
    out.alpha_composite(small, (pad, pad + pad // 4))
    out = out.filter(ImageFilter.GaussianBlur(pad * 0.55))
    return _scale_alpha(out, strength)


# ---------- Background ----------

GLOW_PATH = [  # center x, y, swing x, y, speed, phase, radius (fractions of the width)
    (0.14, 0.08, 0.08, 0.10, 0.11, 0.0, 0.34),
    (0.92, 0.18, 0.07, 0.12, 0.09, 1.7, 0.30),
    (0.66, 1.00, 0.14, 0.07, 0.10, 3.1, 0.36),
    (0.05, 0.98, 0.07, 0.08, 0.12, 4.6, 0.24),
]


def render_glow(w, h, t, P, amb):
    """Deep base gradient lit by slowly drifting blobs of the ambience colors."""
    sw, sh = max(24, w // 10), max(16, h // 10)
    img = _vgrad(sw, sh, P["BG"], P["BG2"])
    for (cx0, cy0, ax, ay, sp, ph, rad), col in zip(GLOW_PATH, AMBIENCES[amb]["blobs"]):
        cx = (cx0 + ax * math.sin(t * sp + ph)) * sw
        cy = (cy0 + ay * math.cos(t * sp * 0.83 + ph * 1.7)) * sh
        r = rad * sw * (1 + 0.06 * math.sin(t * sp * 1.3 + ph))
        m = Image.new("L", (sw, sh), 0)
        ImageDraw.Draw(m).ellipse((cx - r, cy - r, cx + r, cy + r), fill=255)
        m = m.filter(ImageFilter.GaussianBlur(r * 0.6))
        img = Image.composite(Image.new("RGB", (sw, sh), _i(mix(P["BG"], col, P["BLOB"]))), img, m)
    return img.resize((w, h), RESAMPLE.BICUBIC)


# ---------- Ring gauge and charts ----------

def ring_image(D, thick, scale, colors, sweep=360, ramp=False, alpha=255, glow=0.0, pad=18,
               ss=3):
    """A ring, or an arc that starts at 12 o'clock and runs clockwise for `sweep` degrees.

    colors  one RGB color, or (c1, c2) for a conic gradient c1 -> c2 -> c1
    ramp    fade in along the arc like a comet tail (0 at the tail, `alpha` at the head)
    glow    0-1, strength of a soft blurred copy under it"""
    size = max(4, int(round((D + 2 * pad) * scale)))
    S = size * ss
    k = scale * ss
    col = Image.new("RGB", (S, S), 0)
    mask = Image.new("L", (S, S), 0)
    dc, dm = ImageDraw.Draw(col), ImageDraw.Draw(mask)
    box = (pad * k, pad * k, S - pad * k - 1, S - pad * k - 1)
    t = max(1, int(thick * k))
    two = isinstance(colors[0], (tuple, list))
    n = max(6, int(sweep / 2.5))
    for i in range(n):
        f = (i + 0.5) / n
        a0 = -90 + sweep * i / n
        a1 = -90 + sweep * (i + 1) / n + (0.7 if i < n - 1 or sweep < 360 else 0.0)
        if two:
            c = _i(mix(colors[0], colors[1], 0.5 - 0.5 * math.cos(2 * math.pi * f)))
        else:
            c = _i(colors)
        al = int(alpha * (f ** 1.6 if ramp else 1.0))
        dc.arc(box, a0, a1, fill=c, width=t)
        dm.arc(box, a0, a1, fill=al, width=t)
    if sweep < 360:  # round head
        R = (D / 2) * k - t / 2
        a = math.radians(-90 + sweep)
        cx, cy = S / 2 + R * math.cos(a), S / 2 + R * math.sin(a)
        c = _i(colors[0] if two else colors)
        dc.ellipse((cx - t / 2, cy - t / 2, cx + t / 2, cy + t / 2), fill=c)
        dm.ellipse((cx - t / 2, cy - t / 2, cx + t / 2, cy + t / 2), fill=alpha)
    img = col.convert("RGBA")
    img.putalpha(mask)
    img = img.resize((size, size), RESAMPLE.LANCZOS)
    if glow:
        g = _scale_alpha(img.copy(), glow).filter(ImageFilter.GaussianBlur(thick * scale * 0.9))
        img = Image.alpha_composite(g, img)
    return img


def bar_image(w, h, frac, scale, track, c1, c2, ss=3):
    """Rounded progress bar: track plus an accent-gradient fill."""
    out = shape_image(w, h, h / 2, scale, fill=track, ss=ss).copy()
    frac = max(0.0, min(1.0, frac))
    if frac > 0:
        fw = max(h, w * frac)
        fill = shape_image(round(fw, 1), h, h / 2, scale, grad=(c1, mix(c1, c2, frac)), ss=ss)
        out.alpha_composite(fill, (0, 0))
    return out


def chart_image(w, h, counts, top, hover, scale, P, amb, ss=2):
    """Daily bars in the accent gradient; today's bar glows, the hovered one is lit."""
    a = AMBIENCES[amb]
    W, H = round(w * scale) * ss, round(h * scale) * ss
    k = scale * ss
    out = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    d = ImageDraw.Draw(out)
    for j in range(4):
        y = int(2 * k + (H - 3 * k) * j / 3)
        for x in range(0, W, int(6 * k)):
            d.line((x, y, x + 2 * k, y), fill=P["LINE"], width=max(1, int(k)))
    n = len(counts)
    slot = W / n
    bw = min(22 * k, slot * 0.56)
    plot = H - 3 * k
    if hover is not None:
        cx = slot * (hover + 0.5)
        d.rounded_rectangle((cx - slot * 0.44, 0, cx + slot * 0.44, H - 1), radius=8 * k,
                            fill=P["CHIP"])
    mask = Image.new("L", (W, H), 0)
    md = ImageDraw.Draw(mask)
    stubs = []
    for i, v in enumerate(counts):
        cx = slot * (i + 0.5)
        if v <= 0:
            stubs.append(cx)
            continue
        bh = max(6 * k, plot * min(1.0, v / top))
        md.rounded_rectangle((cx - bw / 2, H - 1 - bh, cx + bw / 2, H - 1), radius=bw * 0.32,
                             fill=255)
    grad = _vgrad(W, H, mix(a["a2"], (255, 255, 255), 0.08), a["a1"]).convert("RGBA")
    if counts and counts[-1] > 0:  # today glows
        gm = Image.new("L", (W, H), 0)
        cx = slot * (n - 0.5)
        bh = max(6 * k, plot * min(1.0, counts[-1] / top))
        ImageDraw.Draw(gm).rounded_rectangle((cx - bw / 2, H - 1 - bh, cx + bw / 2, H - 1),
                                             radius=bw * 0.32, fill=150)
        glow = Image.new("RGBA", (W, H), _i(a["a2"]) + (0,))
        glow.putalpha(gm.filter(ImageFilter.GaussianBlur(9 * k)))
        out = Image.alpha_composite(out, glow)
    if hover is None or counts[hover] <= 0:
        dim = mask
    else:
        dim = mask.point(lambda v: int(v * 0.82))
        hm = Image.new("L", (W, H), 0)
        cx = slot * (hover + 0.5)
        bh = max(6 * k, plot * min(1.0, counts[hover] / top))
        ImageDraw.Draw(hm).rounded_rectangle((cx - bw / 2, H - 1 - bh, cx + bw / 2, H - 1),
                                             radius=bw * 0.32, fill=255)
        dim = ImageChops.lighter(dim, hm)
    grad.putalpha(dim)
    out = Image.alpha_composite(out, grad)
    d = ImageDraw.Draw(out)
    for cx in stubs:
        d.rounded_rectangle((cx - bw / 2, H - 1 - 4 * k, cx + bw / 2, H - 1), radius=2 * k,
                            fill=P["TRACK"])
    return out.resize((round(w * scale), round(h * scale)), RESAMPLE.LANCZOS)


# ---------- Spotify helpers ----------

class SpotifyProbe:
    """Cached lookups so checking several times a second stays cheap.

    Must be created and used from the same thread (pycaw uses COM).
    """

    def __init__(self):
        self.pids = set()
        self.pids_at = 0.0
        self.sessions = []  # (meter, volume) pairs for Spotify's audio sessions
        self.sessions_at = 0.0
        self.fast_until = 0.0  # re-scan the audio sessions often until this time

    def reset(self):
        """Forget everything (call after killing or launching Spotify)."""
        self.pids = set()
        self.pids_at = 0.0
        self.sessions = []
        self.sessions_at = 0.0

    def get_pids(self, max_age=None):
        now = time.time()
        limit = max_age if max_age is not None else (PID_REFRESH if self.pids else 0.5)
        if now - self.pids_at > limit:
            self.pids = {p.pid for p in psutil.process_iter(["name"])
                         if p.info["name"] == "Spotify.exe"}
            self.pids_at = now
        return self.pids

    def titles(self):
        pids = self.get_pids()
        found = []
        if not pids:
            return found

        @ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)
        def enum(hwnd, _):
            pid = wintypes.DWORD()
            user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
            if pid.value in pids and user32.IsWindowVisible(hwnd):
                n = user32.GetWindowTextLengthW(hwnd)
                if n:
                    buf = ctypes.create_unicode_buffer(n + 1)
                    user32.GetWindowTextW(hwnd, buf, n + 1)
                    found.append(buf.value)
            return True

        user32.EnumWindows(enum, 0)
        return found

    def windows(self, max_age=None):
        """Every top-level window owned by Spotify: (hwnd, visible, minimized, title)."""
        pids = self.get_pids(max_age)
        found = []
        if not pids:
            return found

        @ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)
        def enum(hwnd, _):
            pid = wintypes.DWORD()
            user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
            if pid.value in pids:
                n = user32.GetWindowTextLengthW(hwnd)
                title = ""
                if n:
                    buf = ctypes.create_unicode_buffer(n + 1)
                    user32.GetWindowTextW(hwnd, buf, n + 1)
                    title = buf.value
                found.append((hwnd, bool(user32.IsWindowVisible(hwnd)),
                              bool(user32.IsIconic(hwnd)), title))
            return True

        user32.EnumWindows(enum, 0)
        return found

    def window_state(self):
        """How Spotify's window looks right now: 'visible', 'minimized' or 'hidden'."""
        wins = [w for w in self.windows() if w[3] and w[3] not in IGNORE_TITLES]
        if any(vis and not mini for _, vis, mini, _ in wins):
            return "visible"
        if any(vis and mini for _, vis, mini, _ in wins):
            return "minimized"
        return "hidden"

    def minimize_visible(self, max_age=None):
        """Minimize (without activating) any Spotify window that is open on screen.

        Minimize, never hide: ad detection needs the window to stay 'visible' to Windows.
        Returns how many windows were told to minimize."""
        count = 0
        for hwnd, vis, mini, title in self.windows(max_age):
            if vis and not mini and title and title not in IGNORE_TITLES:
                user32.ShowWindowAsync(hwnd, SW_SHOWMINNOACTIVE)
                count += 1
        return count

    def _find_sessions(self):
        found = []
        for s in AudioUtilities.GetAllSessions():
            if s.Process and s.Process.name() == "Spotify.exe":
                found.append((s._ctl.QueryInterface(IAudioMeterInformation),
                              s._ctl.QueryInterface(ISimpleAudioVolume)))
        return found

    def _refresh(self):
        now = time.time()
        limit = METER_REFRESH if (self.sessions and now >= self.fast_until) else 0.5
        if now - self.sessions_at > limit:
            self.sessions_at = now
            self.sessions = self._find_sessions()

    def making_sound(self, log=None):
        """True if Spotify currently has audio output (i.e. not paused)."""
        try:
            self._refresh()
            return any(m.GetPeakValue() > SOUND_THRESHOLD for m, _ in self.sessions)
        except Exception as e:
            self.sessions = []
            if log:
                log(f"Audio check error: {e}")
            return False

    def get_volume(self):
        """Spotify's current (volume 0-1, muted), or None if it has no audio session.

        If Spotify has several audio sessions, the one that is making sound is the real one."""
        try:
            self._refresh()
            best = None
            for meter, vol in self.sessions:
                reading = (float(vol.GetMasterVolume()), bool(vol.GetMute()))
                if meter.GetPeakValue() > SOUND_THRESHOLD:
                    return reading
                if best is None:
                    best = reading
            return best
        except Exception:
            self.sessions = []
        return None

    def set_volume(self, level, muted):
        """Put Spotify's volume back to the given value. True if anything changed."""
        changed = False
        try:
            self._refresh()
            for _, v in self.sessions:
                if abs(float(v.GetMasterVolume()) - level) > 0.005:
                    v.SetMasterVolume(level, None)
                    changed = True
                if bool(v.GetMute()) != muted:
                    v.SetMute(1 if muted else 0, None)
                    changed = True
        except Exception:
            self.sessions = []
        return changed


    def set_mute(self, muted):
        """Mute or unmute every Spotify audio session. Returns how many it reached."""
        self.sessions_at = 0.0  # look at the sessions as they are right now
        reached = 0
        try:
            self._refresh()
            for _, v in self.sessions:
                if bool(v.GetMute()) != muted:
                    v.SetMute(1 if muted else 0, None)
                reached += 1
        except Exception:
            self.sessions = []
        return reached

    def mute_states(self, fresh=False):
        """The mute flag of each Spotify audio session."""
        try:
            if fresh:
                self.sessions_at = 0.0
            self._refresh()
            return [bool(v.GetMute()) for _, v in self.sessions]
        except Exception:
            self.sessions = []
        return []


VK_LBUTTON, VK_CONTROL, VK_UP, VK_DOWN = 0x01, 0x11, 0x26, 0x28
VK_VOLUME_MUTE, VK_VOLUME_DOWN, VK_VOLUME_UP = 0xAD, 0xAE, 0xAF
VK_SPACE, VK_MEDIA_PLAY_PAUSE = 0x20, 0xB3


class UserInput:
    """Remembers when the user last used a way of changing the volume (mouse button,
    volume keys, Ctrl+Up/Down) and a way of pausing (mouse button, Space, Play/Pause).

    Windows only lets the "pressed since last check" bit of a key be read once, so
    everything shares this one sampler instead of reading the keys separately."""

    def __init__(self):
        self.last_volume = 0.0
        self.last_pause = 0.0

    def poll(self):
        now = time.time()

        def hit(vk):
            return bool(user32.GetAsyncKeyState(vk) & 0x8001)

        try:
            mouse = hit(VK_LBUTTON)
            ctrl = hit(VK_CONTROL)
            if (mouse or hit(VK_VOLUME_UP) or hit(VK_VOLUME_DOWN) or hit(VK_VOLUME_MUTE)
                    or (ctrl and (hit(VK_UP) or hit(VK_DOWN)))):
                self.last_volume = now
            if mouse or hit(VK_SPACE) or hit(VK_MEDIA_PLAY_PAUSE):
                self.last_pause = now
        except Exception:
            pass


def volume_differs(a, b):
    return abs(a[0] - b[0]) > 0.005 or a[1] != b[1]


class VolumeKeeper:
    """Keeps Spotify's volume where the user left it, across restarts.

    `good` is the volume the user wants.
      * Normally (Spotify has been up for a while) whatever the volume is IS the user's
        choice, so every change is adopted. This includes changes made during ads.
      * Right after a restart Spotify sometimes resets its own volume. In that start-up
        window the keeper puts the volume back, but never while you are using the mouse
        or volume keys: a change you make then is adopted and wins.
    """

    def __init__(self, probe, log=None, dbg=None, inputs=None):
        self.probe = probe
        self.log = log
        self.dbg = dbg
        self.inputs = inputs or UserInput()
        self.good = None          # (level, muted) the user wants
        self.last_seen = None     # volume at the previous check
        self.booting = False      # inside the start-up window after a restart
        self.boot_started = 0.0
        self.boot_ends = None     # set once Spotify's audio session shows up
        self.fixes = 0
        self.logged = False

    def resync(self):
        """Forget the last reading (after the volume was touched on purpose)."""
        self.last_seen = None

    def start_boot(self):
        """Call right after relaunching Spotify."""
        now = time.time()
        self.booting = True
        self.boot_started = now
        self.boot_ends = None
        self.fixes = 0
        self.logged = False
        self.last_seen = None  # the new session's first reading is not a "change"
        self.probe.fast_until = now + VOLUME_BOOT_MAX

    def tick(self):
        """Call often. Learns the user's volume and undoes start-up resets."""
        now = time.time()
        cur = self.probe.get_volume()
        if cur is None:  # no audio session right now (Spotify closed or still starting)
            if self.booting and now - self.boot_started > VOLUME_BOOT_MAX:
                self.booting = False
            return

        self.inputs.poll()
        touched = now - self.inputs.last_volume < 1.0
        moved = self.last_seen is not None and volume_differs(cur, self.last_seen)
        self.last_seen = cur

        if self.booting:
            if self.boot_ends is None:  # the clock starts when the audio session exists
                self.boot_ends = now + VOLUME_BOOT
                self.probe.fast_until = self.boot_ends
            elif now > self.boot_ends:
                self.booting = False

        if self.good is None or not self.booting:
            self.good = cur
        elif touched and moved:
            self.good = cur  # you changed it during start-up: your change wins
            if self.dbg:
                self.dbg(f"Kept your new volume ({round(cur[0] * 100)}%)")
        elif (not touched and volume_differs(cur, self.good)
              and self.fixes < VOLUME_FIXES):
            if self.probe.set_volume(*self.good):
                self.fixes += 1
                self.last_seen = self.good
                if self.log and not self.logged:
                    self.logged = True
                    self.log(f"Volume put back to {round(self.good[0] * 100)}%")


def looks_like_ad(title):
    """Tracks show as 'Artist - Song'. Anything else is not a track."""
    if title in IGNORE_TITLES:
        return False
    return title in AD_TITLES or " - " not in title


def is_track_title(title):
    return title not in IGNORE_TITLES and not looks_like_ad(title)


def is_sure_ad(title):
    """Spotify's own label for an ad. Titles that merely aren't a track ('Spotify Free',
    'Spotify'...) are what a paused Spotify shows too, so they are not proof."""
    return title.strip().lower().startswith("advertisement")


def is_ad_title(title):
    """For titles from the media session, which hold only the song name (no 'Artist - ')."""
    t = title.strip()
    return t in AD_TITLES or t.lower().startswith("advertisement")


def parse_track(title):
    """'Artist - Song' -> (song, artist)."""
    if " - " in title:
        artist, song = title.split(" - ", 1)
        return song.strip(), artist.strip()
    return title.strip(), ""


def stamp():
    """Current time in 12-hour format, e.g. 4:33:07 PM."""
    return datetime.now().strftime("%I:%M:%S %p").lstrip("0")


def clock():
    return datetime.now().strftime("%I:%M %p").lstrip("0")


def fmt_duration(sec):
    sec = int(max(0, sec))
    if sec < 60:
        return f"{sec}s"
    if sec < 3600:
        return f"{sec // 60}m {sec % 60:02d}s"
    return f"{sec // 3600}h {(sec % 3600) // 60:02d}m"


def fmt_clock(sec):
    sec = int(max(0, sec))
    return f"{sec // 60}:{sec % 60:02d}"


def kill_spotify():
    procs = []
    for p in psutil.process_iter(["name"]):
        if p.info["name"] == "Spotify.exe":
            try:
                p.kill()
                procs.append(p)
            except Exception:
                pass
    psutil.wait_procs(procs, timeout=2)  # returns as soon as they're gone


def launch_spotify(minimized=False):
    if os.path.exists(CLASSIC_PATH):
        info = None
        if minimized:
            # Ask Windows to open the window minimized and without taking focus.
            info = subprocess.STARTUPINFO()
            info.dwFlags |= subprocess.STARTF_USESHOWWINDOW
            info.wShowWindow = SW_SHOWMINNOACTIVE
        subprocess.Popen([CLASSIC_PATH], startupinfo=info)
    else:  # Microsoft Store version: no options possible, the watcher minimizes it instead
        subprocess.Popen(["explorer.exe", STORE_LAUNCH])


def press_key(vk):
    user32.keybd_event(vk, 0, 0, 0)
    user32.keybd_event(vk, 0, 2, 0)


def press_next():
    press_key(0xB0)


def press_prev():
    press_key(0xB1)


def press_play():
    press_key(0xB3)


# ---------- Windows integration ----------

_MUTEX = []


def single_instance():
    """False if Ad Guard is already running (two copies would fight over Spotify)."""
    try:
        handle = ctypes.windll.kernel32.CreateMutexW(None, False, "Local\\AdGuardForSpotify")
        if ctypes.windll.kernel32.GetLastError() == 183:  # ERROR_ALREADY_EXISTS
            return False
        _MUTEX.append(handle)
    except Exception:
        pass
    return True


def startup_command():
    if getattr(sys, "frozen", False):
        return f'"{sys.executable}" --startup'
    exe = sys.executable
    pyw = os.path.join(os.path.dirname(exe), "pythonw.exe")
    if os.path.exists(pyw):
        exe = pyw
    return f'"{exe}" "{os.path.abspath(__file__)}" --startup'


RUN_KEY = r"Software\Microsoft\Windows\CurrentVersion\Run"


def set_windows_startup(enable):
    """Add or remove Ad Guard from the apps that start with Windows. True on success."""
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0, winreg.KEY_SET_VALUE) as key:
            if enable:
                winreg.SetValueEx(key, "AdGuard", 0, winreg.REG_SZ, startup_command())
            else:
                try:
                    winreg.DeleteValue(key, "AdGuard")
                except FileNotFoundError:
                    pass
        return True
    except Exception:
        return False


# ---------- Now playing ----------

EMPTY_MEDIA = {"ok": False, "title": "", "artist": "", "album": "", "status": None,
               "pos": 0.0, "dur": 0.0, "at": 0.0, "art": None, "track_id": 0}


class MediaSession(threading.Thread):
    """Reads Spotify through Windows' media controls (the same thing the volume-key overlay
    uses): song, artist, album art, position and a reliable play/pause state. Also sends
    Play / Next / Previous to Spotify only, instead of to whichever app owns the media keys.

    Needs the optional winrt packages. Without them `ready` stays False and the app falls
    back to window titles and the media keys."""

    STATUS = {4: "playing", 5: "paused", 3: "stopped", 0: "stopped"}

    def __init__(self):
        super().__init__(daemon=True)
        self.info = dict(EMPTY_MEDIA)
        self.stop_event = threading.Event()
        self.loop = None
        self.session = None
        self.error = None
        self._key = None
        self._track_id = 0
        self._art = None

    @property
    def ready(self):
        return HAVE_SMTC and self.session is not None and self.loop is not None

    def run(self):
        if not HAVE_SMTC:
            return
        try:
            self.loop = asyncio.new_event_loop()
            asyncio.set_event_loop(self.loop)
            self.loop.run_until_complete(self._main())
        except Exception as e:
            self.error = repr(e)

    async def _main(self):
        manager = await _SmtcManager.request_async()
        while not self.stop_event.is_set():
            try:
                await self._poll(manager)
            except Exception as e:
                self.error = repr(e)
                self.session = None
                self.info = dict(EMPTY_MEDIA)
            await asyncio.sleep(MEDIA_POLL)

    async def _poll(self, manager):
        spotify = None
        for sess in manager.get_sessions():
            try:
                if "spotify" in str(sess.source_app_user_model_id).lower():
                    spotify = sess
                    break
            except Exception:
                pass
        self.session = spotify
        if spotify is None:
            self._key = None
            self.info = dict(EMPTY_MEDIA)
            return
        props = await spotify.try_get_media_properties_async()
        status = self.STATUS.get(int(spotify.get_playback_info().playback_status), "other")
        pos = dur = 0.0
        try:
            tl = spotify.get_timeline_properties()
            dur = max(0.0, (tl.end_time - tl.start_time).total_seconds())
            pos = max(0.0, tl.position.total_seconds())
            if status == "playing":  # position is as of last_updated_time: add the age
                last = tl.last_updated_time
                now = datetime.now(last.tzinfo) if last.tzinfo else datetime.utcnow()
                age = (now - last).total_seconds()
                if 0 <= age < 3600:
                    pos += age
        except Exception:
            pass
        key = (props.title, props.artist, props.album_title)
        if key != self._key:
            self._key = key
            self._track_id += 1
            self._art = None
        info = {"ok": True, "title": props.title or "", "artist": props.artist or "",
                "album": props.album_title or "", "status": status, "pos": pos, "dur": dur,
                "at": time.monotonic(), "art": self._art, "track_id": self._track_id}
        self.info = info
        if self._art is None and props.thumbnail is not None and info["title"]:
            art = await self._read_art(props.thumbnail)
            if art and key == self._key:
                self._art = art
                self.info = dict(self.info, art=art)

    async def _read_art(self, ref):
        try:
            stream = await ref.open_read_async()
            size = int(stream.size)
            if not 0 < size < 8_000_000:
                return None
            try:
                reader = _DataReader(stream)
            except Exception:
                reader = _DataReader(stream.get_input_stream_at(0))
            await reader.load_async(size)
            data = bytearray(size)
            reader.read_bytes(data)
            reader.close()
            return bytes(data)
        except Exception as e:
            self.error = f"album art: {e!r}"
            return None

    def command(self, name, timeout=1.5):
        """'next' / 'prev' / 'play' / 'pause' / 'toggle'. True if Spotify accepted it."""
        if not self.ready:
            return False

        async def go():
            sess = self.session
            if sess is None:
                return False
            fn = {"next": sess.try_skip_next_async, "prev": sess.try_skip_previous_async,
                  "play": sess.try_play_async, "pause": sess.try_pause_async,
                  "toggle": sess.try_toggle_play_pause_async}[name]
            return bool(await fn())

        try:
            return bool(asyncio.run_coroutine_threadsafe(go(), self.loop).result(timeout))
        except Exception:
            return False


def build_now(titles, mi, ad_flag=False, last=None):
    """What to show as 'now playing'.

    titles   Spotify's window titles ('Artist - Song', 'Advertisement', 'Spotify Free'...)
    mi       the media-session dict (may be stale or empty)
    ad_flag  the watcher has confirmed an ad is playing
    last     the last track that was shown (a paused Spotify no longer names its song)

    kind is one of 'none' (Spotify not running), 'idle' (open, nothing known), 'track',
    'paused', 'ad'."""
    now = time.monotonic()
    fresh = bool(mi) and bool(mi.get("ok")) and now - mi.get("at", 0.0) < 3.0
    status = mi.get("status") if fresh else None
    titles = [t for t in titles if t and t not in IGNORE_TITLES]
    out = {"kind": "none", "title": "", "artist": "", "album": "", "art": None,
           "track_id": 0, "pos": None, "dur": None, "playing": None}

    def use_media():
        out.update(title=mi["title"], artist=mi["artist"], album=mi["album"], art=mi["art"],
                   track_id=mi["track_id"])
        dur = mi.get("dur") or 0.0
        if dur > 0:
            pos = mi.get("pos", 0.0) + ((now - mi["at"]) if status == "playing" else 0.0)
            out["pos"], out["dur"] = max(0.0, min(pos, dur)), dur

    def use_last():
        if last:
            out.update(title=last["title"], artist=last["artist"], album=last.get("album", ""),
                       art=last.get("art"), track_id=last.get("track_id", 0))

    def paused():
        if fresh and mi.get("title") and not is_ad_title(mi["title"]):
            use_media()  # Windows keeps the paused song's details
        else:
            use_last()
        out.update(kind="paused" if out["title"] else "idle", playing=False)

    def advert():
        out.update(kind="ad", title="Advertisement", artist="Spotify", playing=True)

    track_t = next((t for t in titles if is_track_title(t)), None)
    ad_t = next((t for t in titles if looks_like_ad(t)), None)

    if track_t:
        song, artist = parse_track(track_t)
        out.update(kind="track", title=song, artist=artist, playing=True)
        if fresh and mi.get("title") and mi["title"].strip() and mi["title"].strip() in track_t:
            use_media()
            out["artist"] = mi["artist"] or artist
        if status == "paused":
            out.update(kind="paused", playing=False)
    elif ad_t is not None:
        if status == "paused" or not (is_sure_ad(ad_t) or ad_flag):
            paused()  # a generic title with no sign of an ad: Spotify is simply paused
        else:
            advert()
    elif fresh and mi.get("title"):  # window hidden (e.g. closed to the tray): use the session
        if is_ad_title(mi["title"]):
            if status == "paused" or not (is_sure_ad(mi["title"]) or ad_flag):
                paused()
            else:
                advert()
        else:
            use_media()
            out.update(kind="paused" if status == "paused" else "track",
                       playing=status != "paused")
    return out


class NowPlaying(threading.Thread):
    """Feeds the 'now playing' card. Always on, whether or not protection is running."""

    def __init__(self):
        super().__init__(daemon=True)
        self.media = MediaSession()
        self.stop_event = threading.Event()
        self.titles = []

    def run(self):
        probe = SpotifyProbe()
        self.media.start()
        while not self.stop_event.wait(0.5):
            try:
                self.titles = probe.titles()
            except Exception:
                self.titles = []
        self.media.stop_event.set()

    def view(self, ad_flag=False, last=None):
        return build_now(self.titles, self.media.info, ad_flag, last)

    def command(self, name):
        """Run a player command in Spotify. Returns True if it was sent to Spotify itself;
        otherwise falls back to the media keys (which go to whichever app has them)."""
        if self.media.command(name):
            return True
        {"next": press_next, "prev": press_prev}.get(name, press_play)()
        return False


# ---------- Worker thread ----------

class Watcher(threading.Thread):
    """Watches Spotify and deals with ads, in whichever way the settings say."""

    def __init__(self, q, cfg, media=None):
        super().__init__(daemon=True)
        self.q = q
        self.cfg = cfg          # the live settings: changes apply immediately
        self.media = media      # MediaSession-like, or None
        self.stop_event = threading.Event()
        self.skip_now = threading.Event()   # set by the "Skip this ad" button
        self._status = None
        self._state = None
        self.probe = self.keeper = self.inputs = None
        self.hold = None              # set while an ad is muted
        self.ad_since = None          # when the current ad-looking stretch began
        self.cooldown_until = 0.0
        self.backoff_until = 0.0
        self.quiet_until = 0.0        # keep Spotify minimized until then (quiet restarts)
        self.recover_at = 0.0
        self.assert_at = 0.0
        self.last_key = None
        self.restarts = []
        self.err_text = None
        self.err_count = 0

    # --- settings, read live ---

    @property
    def debug(self):
        return bool(self.cfg.get("verbose"))

    @property
    def mode(self):
        return self.cfg.get("mode", "restart")

    @property
    def quiet(self):
        return bool(self.cfg.get("quiet_restart"))

    @property
    def after_ad(self):
        return self.cfg.get("after_ad", "next")

    # --- messages to the window ---

    def log(self, msg, level="info", debug=False):
        if debug and not self.debug:
            return
        self.q.put(("log", level, stamp(), msg))

    def dbg(self, msg):
        self.log(msg, "warn", debug=True)

    def status(self, s):
        if s != self._status:
            self._status = s
            self.q.put(("status", s))

    def publish(self, ad, action=None):
        st = (bool(ad), action)
        if st != self._state:
            self._state = st
            self.q.put(("state", {"ad": st[0], "action": st[1]}))

    # --- helpers ---

    def fresh_media(self):
        mi = getattr(self.media, "info", None) if self.media is not None else None
        if mi and mi.get("ok") and time.monotonic() - mi.get("at", 0.0) < 3.0:
            return mi
        return None

    def send(self, name):
        """Play / next, aimed at Spotify itself when possible, else the media keys."""
        if self.media is not None:
            try:
                if self.media.ready and self.media.command(name, 1.0):
                    return True
            except Exception:
                pass
        {"next": press_next}.get(name, press_play)()
        return False

    # --- restart mode ---

    def resume_playback(self, probe, keeper, quiet=False):
        def settle():
            """Things to keep doing while Spotify boots."""
            keeper.tick()
            if quiet:
                probe.minimize_visible(0.25)

        deadline = time.time() + 30
        while time.time() < deadline and not self.stop_event.is_set():
            keeper.tick()
            if quiet:
                probe.minimize_visible(0.1)  # catch the window the moment it appears
            if probe.titles():
                break
            time.sleep(0.03 if quiet else 0.1)
        time.sleep(RELAUNCH_WAIT)

        # Play/Pause is a toggle, so only press it if Spotify is silent.
        playing = False
        end = time.time() + AUTOPLAY_CHECK
        while time.time() < end:
            settle()
            if probe.making_sound(self.dbg):
                playing = True
                self.log("Playback resumed on its own")
                break
            time.sleep(0.05)
        if not playing:
            self.log("Resuming playback")
            self.send("play")

        if self.after_ad == "next":
            # Wait until audio is really flowing so the Next key lands on a ready player.
            end = time.time() + 5
            while time.time() < end and not self.stop_event.is_set():
                settle()
                if probe.making_sound(self.dbg):
                    break
                time.sleep(0.05)
            settle()
            time.sleep(0.15)
            self.send("next")
            self.log("Skipped to the next song")
        settle()

    def restart(self, title, forced=False):
        probe, keeper = self.probe, self.keeper
        self.release_mute()  # un-mute first: Windows remembers a muted Spotify
        t0 = time.time()
        if forced:
            self.log("Skipping the ad you picked, restarting Spotify", "warn")
        else:
            self.log(f'Ad detected ("{title}"), restarting Spotify', "warn")
        self.status("restarting")
        self.publish(True, "restarting")
        keeper.tick()  # grab the volume as it is right now
        quiet = False
        if self.quiet:
            try:
                quiet = probe.window_state() != "visible"
            except Exception:
                quiet = False
            if quiet:
                self.log("Spotify is minimized, so it will reopen minimized")
        kill_spotify()
        probe.reset()
        keeper.start_boot()
        launch_spotify(minimized=quiet)
        self.resume_playback(probe, keeper, quiet)
        if quiet:
            self.quiet_until = time.time() + QUIET_HOLD
        self.q.put(("ad", clock(), "restart"))
        self.log(f"Ad skipped ({time.time() - t0:.1f}s)", "ok")
        self.status("watching")
        self.publish(False)
        now = time.time()
        self.cooldown_until = now + COOLDOWN
        self.last_key = None
        self.ad_since = None
        # Many restarts in a row means something is misreading Spotify: stop and say so.
        self.restarts = [t for t in self.restarts if now - t < LOOP_WINDOW] + [now]
        if len(self.restarts) >= LOOP_LIMIT:
            self.backoff_until = now + LOOP_BACKOFF
            self.restarts = []
            self.log(f"Too many restarts in a row. Pausing for {int(LOOP_BACKOFF)}s", "warn")

    # --- mute mode ---

    def start_mute(self, title):
        probe = self.probe
        cur = probe.get_volume()
        prev = cur[1] if cur else False
        try:
            reached = probe.set_mute(True)
        except Exception:
            reached = 0
        if not reached:
            self.log("Couldn't reach Spotify's volume, restarting instead", "warn")
            self.restart(title)
            return
        self.hold = {"start": time.time(), "prev": prev, "override": False, "end": None,
                     "title": title}
        if not prev:
            self.cfg["muted_by_us"] = True
            save_settings(self.cfg)
        self.log(f'Ad detected ("{title}"), muted until it ends', "warn")
        self.q.put(("ad", clock(), "mute"))
        self.status("muted")
        self.publish(True, "muted")

    def hold_step(self, titles, mi, now):
        h, probe, inputs = self.hold, self.probe, self.inputs
        self.status("muted")
        inputs.poll()
        if not probe.get_pids():
            self.release_mute("Spotify closed", finished=False)
            return
        if self.skip_now.is_set():
            self.skip_now.clear()
            self.restart(h["title"], forced=True)
            return
        if self.mode != "mute":
            self.release_mute("Mode changed, sound restored")
            return
        if titles:
            song = any(is_track_title(t) for t in titles)
        else:  # window hidden: ask the media session
            song = bool(mi and mi.get("title") and not is_ad_title(mi["title"])
                        and mi.get("status") == "playing")
        if song:
            if h["end"] is None:
                h["end"] = now
            elif now - h["end"] >= MUTE_END_CONFIRM:
                self.release_mute("Ad finished, sound back", finished=True)
        else:
            h["end"] = None
            if now - h["start"] > MUTE_MAX_HOLD:
                self.release_mute("Ad lasted too long, sound restored", warn=True)
            elif now - self.assert_at > 0.5:
                # keep every Spotify audio session muted (a new one can appear mid-ad),
                # unless you un-muted on purpose
                self.assert_at = now
                states = probe.mute_states(fresh=True)
                if states and not all(states) and not h["override"]:
                    if now - inputs.last_volume < 1.0:
                        h["override"] = True
                        self.dbg("You un-muted the ad yourself, leaving it")
                    else:
                        probe.set_mute(True)

    def release_mute(self, why=None, finished=False, warn=False):
        h = self.hold
        if h is None:
            return
        self.hold = None
        reached = 0
        try:
            reached = self.probe.set_mute(h["prev"])
        except Exception:
            pass
        if reached or h["prev"]:
            self.cfg["muted_by_us"] = False
            save_settings(self.cfg)
        dur = time.time() - h["start"]
        if finished:
            self.q.put(("saved", dur))
        if why:
            self.log(f"{why} ({dur:.0f}s)", "warn" if warn else "ok")
        self.keeper.resync()
        self.status("watching")
        self.publish(False)

    def recover_mute(self):
        """Spotify was left muted by an earlier run that closed in the middle of an ad."""
        now = time.time()
        if now < self.recover_at:
            return
        self.recover_at = now + 2.0
        if self.probe.set_mute(False):
            self.cfg["muted_by_us"] = False
            save_settings(self.cfg)
            self.log("Spotify's sound restored (it was left muted)", "ok")

    # --- the loop ---

    def run(self):
        comtypes.CoInitialize()  # required for pycaw inside a background thread
        try:
            self.loop_forever()
        except Exception as e:
            self.log(f"Protection stopped unexpectedly: {e!r}", "warn")
            self.q.put(("crashed", repr(e)))
        finally:
            try:
                self.release_mute()  # never leave Spotify muted
            except Exception:
                pass
            self.publish(False)

    def loop_forever(self):
        self.probe = SpotifyProbe()
        self.inputs = UserInput()
        self.keeper = VolumeKeeper(self.probe, self.log, self.dbg, self.inputs)
        self.log("Protection started", "ok")
        while not self.stop_event.is_set():
            try:
                self.step()
                self.err_count = 0
            except Exception as e:
                self.err_count += 1
                text = repr(e)
                if text != self.err_text:  # say each new problem once
                    self.err_text = text
                    self.log(f"Check failed: {text}", "warn")
                if self.err_count > 100:
                    raise
            self.stop_event.wait(POLL_SECONDS)
        self.log("Protection stopped")

    def step(self):
        probe, keeper, inputs = self.probe, self.keeper, self.inputs
        now = time.time()
        titles = probe.titles()
        mi = self.fresh_media()

        if self.cfg.get("muted_by_us") and self.hold is None:
            self.recover_mute()
        if self.hold is not None:
            self.hold_step(titles, mi, now)
            return

        sound = probe.making_sound(self.dbg)
        keeper.tick()  # learns your volume, fixes start-up resets
        self.status("watching" if probe.pids else "waiting")

        key = (tuple(titles), sound, mi.get("status") if mi else None)
        if key != self.last_key:
            self.log(f"titles={titles} sound={sound} media={mi.get('status') if mi else None}",
                     debug=True)
            self.last_key = key

        inputs.poll()
        # Windows' media session knows for certain when Spotify is paused. A fading sound
        # and a generic window title otherwise look just like an ad starting.
        paused = bool(mi and mi.get("status") in ("paused", "stopped"))
        playing = sound and not paused
        if titles:
            sure_src = any(is_sure_ad(t) for t in titles)
        else:  # window hidden (closed to the tray): the media session still names the ad
            sure_src = bool(mi and is_sure_ad(mi.get("title", "")))
        sure = playing and sure_src
        maybe = sure or (playing and any(looks_like_ad(t) for t in titles))
        # A generic title only counts once it has lasted a while, and never right after you
        # clicked, pressed Space or hit Play/Pause.
        if maybe and not sure and now - inputs.last_pause < PAUSE_GRACE:
            maybe = False
        if maybe:
            if self.ad_since is None:
                self.ad_since = now
        else:
            self.ad_since = None

        mute_mode = self.mode == "mute"
        need = ((MUTE_CONFIRM_SURE, MUTE_CONFIRM_MAYBE) if mute_mode
                else (AD_CONFIRM_SURE, AD_CONFIRM_MAYBE))[0 if sure else 1]
        confirmed = self.ad_since is not None and now - self.ad_since >= need
        ad_title = next((t for t in titles if looks_like_ad(t)),
                        (mi or {}).get("title", "") if not titles else "")

        forced = self.skip_now.is_set()
        if forced:
            self.skip_now.clear()
            if self.ad_since is None and not any(looks_like_ad(t) for t in titles):
                forced = False  # no ad is playing, nothing to skip
        self.publish(confirmed or forced)

        # After a quiet restart, keep Spotify minimized for a few seconds in case it
        # tries to pop its window back open while it finishes starting up.
        if self.quiet and now < self.quiet_until:
            probe.minimize_visible(0.5)

        if forced:
            self.ad_since = None
            self.restart(ad_title or "Advertisement", forced=True)
        elif confirmed:
            if mute_mode:
                self.ad_since = None
                self.start_mute(ad_title or "Advertisement")
            elif now > self.cooldown_until and now > self.backoff_until:
                self.ad_since = None
                self.restart(ad_title or "Advertisement")


# ---------- GUI ----------

AFTER_LABELS = {"next": "Next song", "resume": "Same song"}
MODE_LABELS = {"restart": "Restart Spotify", "mute": "Mute the ad"}
MODE_HINTS = {"restart": "Skips the ad by quickly reopening Spotify. Takes a few seconds.",
              "mute": "Silences the ad the moment it starts. Spotify keeps running."}
MODE_LINES = {"restart": "Ads are skipped by restarting Spotify",
              "mute": "Ads are muted until they end"}

# mode -> (color key, title, subtitle, chip label)
LOOK = {
    "off": ("FAINT", "Protection off", "Press start to begin", "OFF"),
    "waiting": ("AMBER", "Waiting for Spotify", "Open Spotify to begin", "STANDBY"),
    "watching": ("GREEN", "Protection active", "Watching for ads", "ACTIVE"),
    "restarting": ("AMBER", "Skipping an ad", "Restarting Spotify", "SKIPPING"),
    "muted": ("BLUE", "Ad muted", "Silent until it ends", "MUTED"),
}
PULSE = {"waiting": 2.6, "watching": 2.0, "restarting": 0.9, "muted": 1.2}
RING_SPEED = {"waiting": 0.16, "watching": 0.2, "restarting": 0.85, "muted": 0.28}

PAGES = [("dashboard", "Dashboard", "Spotify ad protection at a glance", "dashboard"),
         ("activity", "Activity", "Everything Ad Guard has done this session", "activity"),
         ("settings", "Settings", "Tune how Ad Guard looks and behaves", "sliders")]
LOG_ROWS = 15
LOG_MAX = 500


def caps(text):
    """Small uppercase labels read better with a little letter spacing."""
    return " ".join(text.upper())


def ago(ts):
    s = int(time.time() - ts)
    if s < 45:
        return "just now"
    if s < 3600:
        return f"{max(1, round(s / 60))}m ago"
    if s < 86400:
        return f"{s // 3600}h ago"
    return f"{s // 86400}d ago"


class Btn:
    """A button drawn on the canvas: one background image per state, plus icon and label.

    kind: 'accent' (gradient with glow), 'glass', 'ghost' or 'danger'."""

    def __init__(self, app, x, y, w, h, tags, kind="accent", text="", icon=None, font="btn",
                 command=None, radius=None, icon_size=18):
        self.app, self.x, self.y, self.w, self.h = app, x, y, w, h
        self.text, self.icon, self.font, self.command = text, icon, font, command
        self.r = h / 2 if radius is None else radius
        self.icon_size = icon_size
        self.enabled, self.visible, self.hover, self.down = True, True, False, False
        self.tag = app.new_tag()
        tags = tuple(tags) + (self.tag,)
        c = app.canvas
        self.bg = c.create_image(0, 0, anchor="nw", tags=tags)
        self.icon_item = c.create_image(0, 0, anchor="center", tags=tags, state="disabled")
        self.text_item = c.create_text(0, 0, anchor="w", text="", font=app.fonts[font],
                                       tags=tags, state="disabled")
        self.items = (self.bg, self.icon_item, self.text_item)
        c.tag_bind(self.tag, "<Enter>", self.on_enter)
        c.tag_bind(self.tag, "<Leave>", self.on_leave)
        c.tag_bind(self.tag, "<ButtonPress-1>", self.on_down)
        c.tag_bind(self.tag, "<ButtonRelease-1>", self.on_up)
        self.kind = None
        self.set_kind(kind)

    @property
    def pad(self):
        return 14 if self.kind == "accent" else 0

    def set_kind(self, kind):
        if kind == self.kind:
            return
        a = self.app
        origin = self.origin() if self.kind else (a.S(self.x), a.S(self.y))
        self.kind = kind
        self.imgs = a.button_images(kind, self.w, self.h, self.r)
        self.layout(origin)
        self.refresh()

    def origin(self):
        """Top-left of the button itself (not its glow), in canvas pixels."""
        x, y = self.app.canvas.coords(self.bg)
        return x + self.app.S(self.pad), y + self.app.S(self.pad)

    def layout(self, origin=None):
        a, c = self.app, self.app.canvas
        ox, oy = origin or self.origin()
        c.coords(self.bg, ox - a.S(self.pad), oy - a.S(self.pad))
        tw = a.fonts[self.font].measure(self.text) if self.text else 0
        iw = a.S(self.icon_size) if self.icon else 0
        gap = a.S(8) if (self.text and self.icon) else 0
        x0 = ox + (a.S(self.w) - (tw + iw + gap)) / 2
        cy = oy + a.S(self.h) / 2
        c.coords(self.icon_item, x0 + iw / 2, cy)
        c.coords(self.text_item, x0 + iw + gap, cy)
        c.itemconfigure(self.text_item, text=self.text)

    def fg(self):
        P = self.app.P
        if not self.enabled:
            return P["FAINT"]
        return {"accent": P["ON_ACCENT"], "danger": P["RED"]}.get(self.kind, P["TEXT"])

    def refresh(self):
        state = ("disabled" if not self.enabled else "down" if self.down
                 else "hover" if self.hover else "normal")
        c, a = self.app.canvas, self.app
        c.itemconfigure(self.bg, image=self.imgs[state])
        fg = self.fg()
        c.itemconfigure(self.text_item, fill=fg)
        if self.icon:
            c.itemconfigure(self.icon_item, image=a.icon_photo(self.icon, self.icon_size, fg))
        else:
            c.itemconfigure(self.icon_item, image="")

    def configure(self, text=None, icon=None, kind=None, enabled=None):
        relayout = False
        if kind is not None and kind != self.kind:
            self.set_kind(kind)
        if text is not None and text != self.text:
            self.text, relayout = text, True
        if icon is not None and icon != self.icon:
            self.icon, relayout = icon, True
        if enabled is not None and enabled != self.enabled:
            self.enabled = enabled
            if not enabled:
                self.hover = self.down = False
        if relayout:
            self.layout()
        self.refresh()

    def set_visible(self, on):
        if on == self.visible:
            return
        self.visible = on
        c = self.app.canvas
        c.itemconfigure(self.bg, state="normal" if on else "hidden")
        for it in (self.icon_item, self.text_item):
            c.itemconfigure(it, state="disabled" if on else "hidden")
        if not on:
            self.hover = self.down = False
            self.refresh()

    def inside(self, e):
        x, y = self.origin()
        return x <= e.x <= x + self.app.S(self.w) and y <= e.y <= y + self.app.S(self.h)

    def on_enter(self, e):
        if self.enabled:
            self.hover = True
            self.app.canvas.configure(cursor="hand2")
            self.refresh()

    def on_leave(self, e):
        self.hover = False
        self.down = False
        self.app.canvas.configure(cursor="")
        self.refresh()

    def on_down(self, e):
        if self.enabled:
            self.down = True
            self.refresh()

    def on_up(self, e):
        fire = self.down and self.enabled and self.inside(e)
        self.down = False
        self.hover = self.inside(e)
        self.refresh()
        if fire and self.command:
            self.command()


class Switch:
    """Toggle switch with a label and an optional description, drawn on the canvas."""

    TW, TH = 42, 24

    def __init__(self, app, x, y, tags, label, desc, value, command):
        self.app, self.value, self.command = app, bool(value), command
        self.enabled = True
        self.pos = 1.0 if self.value else 0.0
        self.tag = app.new_tag()
        tags = tuple(tags) + (self.tag,)
        ty = y + (5 if desc else 0)
        self.track = app.put_image(x, ty, Image.new("RGBA", (2, 2)), tags)
        tx = x + self.TW + 14
        self.label = app.put_text(tx, y + (0 if desc else self.TH / 2), label, "bodysb", "TEXT",
                                  tags, anchor="nw" if desc else "w", state="normal")
        self.desc = None
        if desc:
            self.desc = app.put_text(tx, y + 21, desc, "small", "MUTED", tags, state="normal")
        c = app.canvas
        c.tag_bind(self.tag, "<Button-1>", lambda e: self.toggle())
        c.tag_bind(self.tag, "<Enter>", lambda e: c.configure(cursor="hand2" if self.enabled else ""))
        c.tag_bind(self.tag, "<Leave>", lambda e: c.configure(cursor=""))
        self.draw()

    def draw(self):
        a = self.app
        a.set_image(self.track, a.switch_image(self.pos, self.enabled))

    def set(self, value, animate=False):
        value = bool(value)
        if value == self.value and not animate:
            self.pos = 1.0 if value else 0.0
            self.draw()
            return
        self.value = value
        start, end = self.pos, 1.0 if value else 0.0

        def step(p):
            self.pos = start + (end - start) * ease_out(p)
            self.draw()

        if animate:
            self.app.tween(200, step, key=self.tag)
        else:
            step(1.0)

    def toggle(self):
        if not self.enabled:
            return
        self.set(not self.value, animate=True)
        if self.command:
            self.command(self.value)

    def set_enabled(self, on):
        self.enabled = on
        P = self.app.P
        self.app.canvas.itemconfigure(self.label, fill=P["TEXT"] if on else P["FAINT"])
        if self.desc:
            self.app.canvas.itemconfigure(self.desc, fill=P["MUTED"] if on else P["FAINT"])
        self.draw()


class Segment:
    """Segmented control: a glass track with a sliding accent pill."""

    def __init__(self, app, x, y, w, h, tags, options, value, command):
        self.app, self.w, self.h, self.command = app, w, h, command
        self.options = options  # [(value, label)]
        self.enabled = True
        self.tag = app.new_tag()
        tags = tuple(tags) + (self.tag,)
        n = len(options)
        self.iw = (w - 8) / n
        P = app.P
        self.track = app.put_image(x, y, shape_image(w, h, h / 2, app.scale, fill=P["CHIP"],
                                                     edge=P["EDGE_LOW"]), tags)
        self.pill_on = shape_image(round(self.iw, 2), h - 8, (h - 8) / 2, app.scale,
                                   grad=(app.A["a1"], app.A["a2"]), sheen=40)
        self.pill_off = shape_image(round(self.iw, 2), h - 8, (h - 8) / 2, app.scale,
                                    fill=P["CHIP_HOVER"])
        self.idx = max(0, [v for v, _ in options].index(value) if value in
                       [v for v, _ in options] else 0)
        self.pill = app.put_image(x + 4 + self.iw * self.idx, y + 4, self.pill_on, tags)
        self.labels = []
        for i, (_, label) in enumerate(options):
            self.labels.append(app.put_text(x + 4 + self.iw * (i + 0.5), y + h / 2, label,
                                            "bodysb", "MUTED", tags, anchor="center",
                                            state="normal"))
        c = app.canvas
        c.tag_bind(self.tag, "<Button-1>", self.on_click)
        c.tag_bind(self.tag, "<Enter>", lambda e: c.configure(cursor="hand2" if self.enabled else ""))
        c.tag_bind(self.tag, "<Leave>", lambda e: c.configure(cursor=""))
        self.paint()

    def paint(self):
        P, c = self.app.P, self.app.canvas
        for i, it in enumerate(self.labels):
            if not self.enabled:
                col = P["FAINT"]
            else:
                col = P["ON_ACCENT"] if i == self.idx else P["MUTED"]
            c.itemconfigure(it, fill=col)
        self.app.set_image(self.pill, self.pill_on if self.enabled else self.pill_off)

    def on_click(self, e):
        if not self.enabled:
            return
        x0 = self.app.canvas.coords(self.track)[0]
        i = int((e.x - x0 - self.app.S(4)) / self.app.S(self.iw))
        i = max(0, min(len(self.options) - 1, i))
        if i != self.idx:
            self.select(i, animate=True)
            if self.command:
                self.command(self.options[i][0])

    def select(self, i, animate=False):
        a, c = self.app, self.app.canvas
        tx, ty = c.coords(self.track)
        start = c.coords(self.pill)[0]
        end = tx + a.S(4 + self.iw * i)
        self.idx = i
        self.paint()

        def step(p):
            c.coords(self.pill, start + (end - start) * ease_out(p), ty + a.S(4))

        if animate:
            a.tween(240, step, key=self.tag)
        else:
            step(1.0)

    def set(self, value):
        vals = [v for v, _ in self.options]
        if value in vals:
            self.select(vals.index(value))

    def set_enabled(self, on):
        self.enabled = on
        self.paint()


class App(ctk.CTk):
    W, H = 1000, 660
    ART = 120

    def __init__(self, start_minimized=False):
        super().__init__()
        self.cfg = load_settings()
        self.dark = self.cfg["theme"] != "light"
        ctk.set_appearance_mode("dark" if self.dark else "light")

        self.closing = False
        self.t0 = time.time()
        self.q = queue.Queue()
        self.watcher = None
        self.started_at = None
        self.total_skipped = 0
        self.saved_seconds = 0.0
        self.ad_flag = False          # the watcher says an ad is playing
        self.action = None            # "muted" / "restarting" while it deals with one
        self.action_since = 0.0
        self.last_track = None        # last song shown, kept for the paused view
        self.last_ad = "—"
        self._media_seen = False
        self._media_err = None
        self.opt_until = 0.0
        self.playing_icon = False
        self.feed = NowPlaying()
        self.feed.start()
        self.mode = "off"
        self.page = "dashboard"
        self.sliding = False
        self.rebuilding = False
        self.logs = []                # (level, time text, message)
        self.log_scroll = 0           # rows scrolled up from the newest
        self.chart_hover = None
        self.spotify_state = None
        self._tok = {}
        self._tags = 0
        self.bar_cur = [0.05, 0.05, 0.05]
        self.pulse_at = -10.0
        self.bg_at = 0.0
        self.bg_size = None
        self.bg_photo = None

        self.title("Ad Guard for Spotify")
        self.fit_to_screen()
        self.geometry(f"{self.W}x{self.H}")
        self.resizable(False, False)
        if self.cfg["animations"]:
            self.attributes("-alpha", 0.0)
        if self.cfg["on_top"]:
            self.attributes("-topmost", True)

        self.scale = self._get_scale()
        self.canvas = tk.Canvas(self, highlightthickness=0, bd=0)
        self.canvas.place(x=0, y=0, relwidth=1, relheight=1)
        self.make_fonts()
        self.build_ui()

        self.add_log("info", stamp(), f"Ad Guard {APP_VERSION} ready.")
        if not HAVE_SMTC:
            self.add_log("warn", stamp(), "Optional: install the winrt packages (see the top of "
                         "the file) for album art and better pause detection.")
        if start_minimized:
            self.after(300, self.iconify)
        if self.cfg["auto_start"]:
            self.after(900, self.auto_start)

        self.canvas.bind("<MouseWheel>", self.on_wheel)
        for i, (key, *_rest) in enumerate(PAGES):
            self.bind(f"<Control-Key-{i + 1}>", lambda e, k=key: self.show_page(k))
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.after(120, self.pump)
        self.after(1000, self.tick)
        self.after(30, self.intro)
        self.after(60, self.anim_tick)
        self.after(400, self.refresh_icon)
        self.after(300, self.refresh_now)

    # ----- setup helpers -----

    def _get_scale(self):
        try:
            return float(self._get_window_scaling())
        except Exception:
            return 1.0

    def fit_to_screen(self):
        """Shrink the whole window a little if it would not fit above the taskbar
        (e.g. a 1080p laptop at 150% display scaling)."""
        try:
            rect = wintypes.RECT()
            user32.SystemParametersInfoW(0x30, 0, ctypes.byref(rect), 0)  # SPI_GETWORKAREA
            need = (self.H + 48) * self._get_scale()  # window plus its title bar
            avail = rect.bottom - rect.top
            if avail > 200 and need > avail:
                ctk.set_window_scaling(max(0.6, avail / need))
        except Exception:
            pass

    def make_fonts(self):
        fams = set(tkfont.families(self))

        def pick(*names):
            return next((n for n in names if n in fams), "Segoe UI")

        disp = pick("Segoe UI Variable Display Semib", "Segoe UI Semibold")
        text = pick("Segoe UI Variable Text", "Segoe UI")
        semi = pick("Segoe UI Variable Text Semibold", "Segoe UI Semibold")
        small = pick("Segoe UI Variable Small Semibol", "Segoe UI Semibold")
        mono = pick("Cascadia Mono", "Consolas")
        s = self.scale

        def F(fam, px, weight="normal"):
            return tkfont.Font(self, family=fam, size=-int(round(px * s)), weight=weight)

        self.fonts = {
            "h1": F(disp, 28), "hero": F(disp, 23), "big": F(disp, 44), "kpi": F(disp, 20),
            "title": F(semi, 15), "track": F(semi, 17), "body": F(text, 13),
            "bodysb": F(semi, 13), "small": F(text, 12), "cap": F(small, 10),
            "mono": F(mono, 12), "btn": F(semi, 14),
        }

    def S(self, v):
        return v * self.scale

    def new_tag(self):
        self._tags += 1
        return f"w{self._tags}"

    def col(self, c):
        return self.P.get(c, c) if isinstance(c, str) else rgb_to_hex(c)

    def put_image(self, x, y, pil, tags=(), anchor="nw", state="normal"):
        ph = ImageTk.PhotoImage(pil)
        item = self.canvas.create_image(self.S(x), self.S(y), image=ph, anchor=anchor,
                                        tags=tags, state=state)
        self.ph[item] = ph
        return item

    def set_image(self, item, pil):
        ph = ImageTk.PhotoImage(pil)
        self.canvas.itemconfigure(item, image=ph)
        self.ph[item] = ph

    def put_text(self, x, y, text, font, color, tags=(), anchor="nw", width=None,
                 state="disabled"):
        kw = {"width": self.S(width)} if width else {}
        return self.canvas.create_text(self.S(x), self.S(y), text=text, font=self.fonts[font],
                                       fill=self.col(color), anchor=anchor, tags=tags,
                                       state=state, **kw)

    def set_text(self, item, text, color=None):
        c = self.canvas
        if c.itemcget(item, "text") != text:
            c.itemconfigure(item, text=text)
        if color is not None:
            c.itemconfigure(item, fill=self.col(color))

    def card(self, x, y, w, h, tags, r=22, lines=()):
        return self.put_image(x - GLASS_PAD, y - GLASS_PAD,
                              glass_image(w, h, r, self.scale, self.P, lines), tags)

    def icon_photo(self, name, size, color):
        key = ("icon", name, size, color)
        if key not in self.photos:
            self.photos[key] = ImageTk.PhotoImage(line_icon(name, round(self.S(size)), color))
        return self.photos[key]

    def button_images(self, kind, w, h, r):
        key = ("btn", kind, w, h, r)
        if key in self.photos:
            return self.photos[key]
        P, A, s = self.P, self.A, self.scale
        a1, a2 = A["a1"], A["a2"]
        lift = lambda c, f: _i(mix(c, (255, 255, 255), f))
        sink = lambda c, f: _i(mix(c, (0, 0, 0), f))
        if kind == "accent":
            spec = {
                "normal": dict(grad=(a1, a2), sheen=46, glow=rgba(a1, 110), pad=14),
                "hover": dict(grad=(lift(a1, 0.1), lift(a2, 0.1)), sheen=56, glow=rgba(a2, 170), pad=14),
                "down": dict(grad=(sink(a1, 0.12), sink(a2, 0.12)), sheen=30, glow=rgba(a1, 70), pad=14),
                "disabled": dict(fill=P["CHIP"], edge=P["EDGE_LOW"], pad=14),
            }
        elif kind == "danger":
            red = _rgb(P["RED"])
            spec = {
                "normal": dict(fill=rgba(red, 30), edge=rgba(red, 90)),
                "hover": dict(fill=rgba(red, 48), edge=rgba(red, 150)),
                "down": dict(fill=rgba(red, 22), edge=rgba(red, 90)),
                "disabled": dict(fill=P["CHIP"], edge=P["EDGE_LOW"]),
            }
        elif kind == "ghost":
            spec = {
                "normal": dict(fill=(0, 0, 0, 0)),
                "hover": dict(fill=P["CHIP"]),
                "down": dict(fill=P["CHIP_HOVER"]),
                "disabled": dict(fill=(0, 0, 0, 0)),
            }
        else:  # glass
            spec = {
                "normal": dict(fill=P["CHIP"], edge=P["EDGE_LOW"]),
                "hover": dict(fill=P["CHIP_HOVER"], edge=P["EDGE"]),
                "down": dict(fill=P["CHIP"], edge=P["EDGE"]),
                "disabled": dict(fill=P["CHIP"], edge=P["EDGE_LOW"]),
            }
        imgs = {st: ImageTk.PhotoImage(shape_image(w, h, r, s, **kw)) for st, kw in spec.items()}
        self.photos[key] = imgs
        return imgs

    def switch_image(self, pos, enabled):
        P, A, s = self.P, self.A, self.scale
        w, h = Switch.TW, Switch.TH
        off = shape_image(w, h, h / 2, s, fill=P["TRACK"], edge=P["EDGE_LOW"]).copy()
        if pos > 0:
            on = shape_image(w, h, h / 2, s, grad=(A["a1"], A["a2"]), sheen=40).copy()
            off.alpha_composite(_scale_alpha(on, pos))
        knob = 18
        kx = 3 + pos * (w - knob - 6)
        kimg = shape_image(knob, knob, knob / 2, s, fill=(255, 255, 255, 255),
                           glow=(0, 0, 0, 90), pad=3)
        off.alpha_composite(kimg, (round((kx - 3) * s), round(0 * s)))
        if not enabled:
            off = _scale_alpha(off, 0.45)
        return off

    def refresh_icon(self):
        icon = ensure_icon(self.cfg["ambience"])
        if icon:
            try:
                self.iconbitmap(icon)
            except Exception:
                pass

    # ----- build -----

    def set_palette(self):
        self.P = PALETTES["dark" if self.dark else "light"]
        self.A = AMBIENCES[self.cfg["ambience"]]
        a1 = self.A["a1"]
        self.ACC = (rgb_to_hex(mix(a1, (255, 255, 255), 0.35)) if self.dark
                    else rgb_to_hex(mix(a1, (0, 0, 0), 0.18)))

    def build_ui(self):
        c = self.canvas
        c.delete("all")
        self.ph, self.photos, self.ring_cache = {}, {}, {}
        self._ui = {}
        self.tip_items = []
        self.set_palette()
        bg = rgb_to_hex(self.P["BG"])
        c.configure(bg=bg)
        self.configure(fg_color=bg)
        self.bg_item = c.create_image(0, 0, anchor="nw", tags=("bg",))
        self.bg_size = None
        self.page_off = {}
        self.build_sidebar()
        self.build_dashboard(("pg-dashboard",))
        self.build_activity(("pg-activity",))
        self.build_settings(("pg-settings",))
        self.build_topbar()  # last, so sliding pages pass under it
        for key, *_ in PAGES:
            self.page_off[key] = 0.0
            if key != self.page:
                self.set_off(key, self.H * 2)
        self.sync_all()
        self.draw_bg(time.time() - self.t0)
        self.dirty = True

    def sync_all(self):
        """Push the current state into freshly built widgets."""
        self.title_shown = None
        self.art_key = None
        self._ring_sig = None
        self.set_status(self.mode)
        self.style_button(animated=False)
        self.update_stats()
        self.render_history()
        self.render_log()
        self.update_spotify_pill(force=True)
        try:
            self.render_now(self.feed.view(self.ad_flag, self.last_track))
        except Exception:
            pass

    def build_sidebar(self):
        T = ("chrome",)
        P = self.P
        self.card(20, 20, 72, 620, T, r=26)
        self.logo_item = self.put_image(56, 62, make_logo(round(self.S(42)), amb=self.cfg["ambience"]),
                                        T, anchor="center")
        ind = shape_image(46, 46, 15, self.scale, grad=(self.A["a1"], self.A["a2"]), sheen=50,
                          glow=rgba(self.A["a1"], 120), pad=14)
        cy = self.nav_y(self.page)
        self.nav_ind = self.put_image(56, cy, ind, T, anchor="center")
        blank = Image.new("RGBA", (round(self.S(46)), round(self.S(46))), (0, 0, 0, 0))
        self.hover_img = ImageTk.PhotoImage(shape_image(46, 46, 15, self.scale, fill=P["CHIP_HOVER"]))
        self.blank_img = ImageTk.PhotoImage(blank)
        self.nav = {}
        for key, title, _, icon in PAGES:
            self.nav[key] = self.nav_button(self.nav_y(key), icon, title,
                                            lambda k=key: self.show_page(k))
        self.theme_nav = self.nav_button(590, "sun" if self.dark else "moon",
                                         "Light mode" if self.dark else "Dark mode",
                                         lambda: self.set_theme("light" if self.dark else "dark"))
        self.pin_nav = self.nav_button(536, "pin", "Keep on top", self.toggle_on_top)
        self.paint_nav()

    def nav_y(self, key):
        return 152 + [p[0] for p in PAGES].index(key) * 58

    def nav_button(self, y, icon, tip, command):
        tag = self.new_tag()
        T = ("chrome", tag)
        hit = self.canvas.create_image(self.S(56), self.S(y), image=self.blank_img, anchor="center",
                                       tags=T)
        ic = self.canvas.create_image(self.S(56), self.S(y), anchor="center", tags=T,
                                      state="disabled")
        nb = {"hit": hit, "icon": ic, "name": icon, "y": y, "tip": tip}

        def enter(e):
            self.canvas.configure(cursor="hand2")
            if not nb.get("active"):
                self.canvas.itemconfigure(hit, image=self.hover_img)
            self.show_tip(104, y, nb["tip"], side="right")

        def leave(e):
            self.canvas.configure(cursor="")
            self.canvas.itemconfigure(hit, image=self.blank_img)
            self.hide_tip()

        self.canvas.tag_bind(tag, "<Enter>", enter)
        self.canvas.tag_bind(tag, "<Leave>", leave)
        self.canvas.tag_bind(tag, "<Button-1>", lambda e: command())
        return nb

    def paint_nav(self):
        P = self.P
        for key, nb in self.nav.items():
            nb["active"] = key == self.page
            color = P["ON_ACCENT"] if nb["active"] else P["MUTED"]
            self.canvas.itemconfigure(nb["icon"], image=self.icon_photo(nb["name"], 21, color))
        self.canvas.itemconfigure(self.theme_nav["icon"],
                                  image=self.icon_photo(self.theme_nav["name"], 20, P["MUTED"]))
        pin_col = self.ACC if self.cfg["on_top"] else P["MUTED"]
        self.canvas.itemconfigure(self.pin_nav["icon"], image=self.icon_photo("pin", 20, pin_col))
        self.pin_nav["tip"] = "Keep on top: on" if self.cfg["on_top"] else "Keep on top: off"

    def build_topbar(self):
        T = ("chrome",)
        P = self.P
        self.put_image(786, 30, shape_image(194, 38, 19, self.scale, fill=P["CHIP"],
                                            edge=P["EDGE_LOW"]), T)
        self.sp_dot = self.put_image(806, 49, make_dot(_rgb(P["FAINT"]), 0, None,
                                                       size=round(self.S(18))), T, anchor="center")
        self.sp_text = self.put_text(820, 49, "Spotify not running", "bodysb", "MUTED", T,
                                     anchor="w")

    def header(self, T, key):
        _, title, sub, _ = next(p for p in PAGES if p[0] == key)
        self.put_text(112, 20, title, "h1", "TEXT", T)
        self.put_text(113, 61, sub, "body", "MUTED", T)

    def build_dashboard(self, T):
        P = self.P
        self.header(T, "dashboard")

        # protection hero
        self.card(112, 104, 480, 272, T, lines=[(24, 204, 456, 204)])
        self.ring_item = self.put_image(220, 206, Image.new("RGBA", (2, 2)), T, anchor="center")
        self.ring_num = self.put_text(220, 198, "0", "big", "TEXT", T, anchor="center")
        self.ring_cap = self.put_text(220, 234, caps("blocked today"), "cap", "MUTED", T,
                                      anchor="center")
        self.chip_bg = self.put_image(328, 128, Image.new("RGBA", (2, 2)), T)
        self.chip_dot = self.put_image(343, 140, Image.new("RGBA", (2, 2)), T, anchor="center")
        self.chip_txt = self.put_text(356, 140, "", "cap", "MUTED", T, anchor="w")
        self.status_title = self.put_text(327, 158, "", "hero", "TEXT", T)
        self.status_sub = self.put_text(328, 193, "", "body", "MUTED", T)
        self.mode_txt = self.put_text(328, 214, "", "small", "FAINT", T)
        self.main_btn = Btn(self, 328, 244, 240, 46, T, kind="accent", text="Start protection",
                            icon="power", command=self.toggle)
        self.stat_vals = []
        for i, (icon, label) in enumerate((("clock", "time saved"), ("shield", "all-time blocked"),
                                           ("zap", "last ad"))):
            x = 136 + i * 150
            self.put_image(x, 323, line_icon(icon, round(self.S(14)), P["MUTED"]), T)
            self.put_text(x + 21, 330, caps(label), "cap", "MUTED", T, anchor="w")
            self.stat_vals.append(self.put_text(x, 342, "0", "kpi", "TEXT", T))

        # now playing
        self.card(608, 104, 372, 272, T)
        self.art_glow = self.put_image(692, 188, Image.new("RGBA", (2, 2)), T, anchor="center")
        self.art_item = self.put_image(632, 128, Image.new("RGBA", (2, 2)), T)
        self.np_dot = self.put_image(773, 138, Image.new("RGBA", (2, 2)), T, anchor="center")
        self.np_chip = self.put_text(784, 138, "", "cap", "MUTED", T, anchor="w")
        self.np_title = self.put_text(768, 152, "", "track", "TEXT", T)
        self.np_artist = self.put_text(768, 179, "", "body", "MUTED", T)
        self.np_album = self.put_text(768, 200, "", "small", "FAINT", T)
        self.pbar = self.put_image(632, 268, Image.new("RGBA", (2, 2)), T)
        self.t_left = self.put_text(632, 280, "", "small", "FAINT", T)
        self.t_right = self.put_text(956, 280, "", "small", "FAINT", T, anchor="ne")
        self.prev_btn = Btn(self, 706, 310, 46, 46, T, kind="glass", icon="prev", icon_size=18,
                            command=lambda: self.player_cmd("prev"))
        self.play_btn = Btn(self, 766, 304, 58, 58, T, kind="accent", icon="play", icon_size=22,
                            command=lambda: self.player_cmd("toggle"))
        self.next_btn = Btn(self, 838, 310, 46, 46, T, kind="glass", icon="next", icon_size=18,
                            command=lambda: self.player_cmd("next"))
        self.skip_btn = Btn(self, 632, 310, 324, 46, T, kind="accent", text="Skip this ad",
                            icon="skip", command=self.on_skip_ad)
        self.skip_btn.set_visible(False)

        # chart
        self.card(112, 392, 560, 248, T)
        self.put_text(136, 414, "Ads blocked", "title", "TEXT", T)
        self.put_text(136, 437, "Last 14 days", "small", "MUTED", T)
        self.put_text(648, 414, caps("this week"), "cap", "MUTED", T, anchor="ne")
        self.week_val = self.put_text(648, 428, "0", "kpi", "TEXT", T, anchor="ne")
        self.put_text(548, 414, caps("daily avg"), "cap", "MUTED", T, anchor="ne")
        self.avg_val = self.put_text(548, 428, "0", "kpi", "TEXT", T, anchor="ne")
        ctag = self.new_tag()
        self.chart_item = self.put_image(136, 476, Image.new("RGBA", (2, 2)), T + (ctag,))
        self.canvas.tag_bind(ctag, "<Motion>", self.on_chart_motion)
        self.canvas.tag_bind(ctag, "<Leave>", self.on_chart_leave)
        self.chart_labels = [self.put_text(136 + 512 / 14 * (i + 0.5), 604, "", "small", "FAINT",
                                           T, anchor="n") for i in range(14)]

        # recent ads
        self.card(688, 392, 292, 248, T)
        self.put_text(712, 414, "Recent ads", "title", "TEXT", T)
        ltag = self.new_tag()
        self.view_all = self.put_text(956, 416, "View all  →", "bodysb", self.ACC, T + (ltag,),
                                      anchor="ne", state="normal")
        self.canvas.tag_bind(ltag, "<Button-1>", lambda e: self.show_page("activity"))
        self.canvas.tag_bind(ltag, "<Enter>", lambda e: (
            self.canvas.configure(cursor="hand2"),
            self.canvas.itemconfigure(self.view_all, fill=self.P["TEXT"])))
        self.canvas.tag_bind(ltag, "<Leave>", lambda e: (
            self.canvas.configure(cursor=""),
            self.canvas.itemconfigure(self.view_all, fill=self.ACC)))
        self.recent = []
        for i in range(4):
            y = 452 + i * 44
            self.recent.append(dict(
                badge=self.put_image(712, y, Image.new("RGBA", (2, 2)), T),
                title=self.put_text(754, y - 1, "", "bodysb", "TEXT", T),
                sub=self.put_text(754, y + 18, "", "small", "MUTED", T),
                when=self.put_text(956, y + 1, "", "small", "FAINT", T, anchor="ne")))
        self.recent_empty = [
            self.put_image(834, 494, line_icon("shield", round(self.S(30)), P["FAINT"], stroke=1.6),
                           T, anchor="center"),
            self.put_text(834, 528, "No ads blocked yet", "bodysb", "MUTED", T, anchor="center"),
            self.put_text(834, 550, "They will show up here", "small", "FAINT", T, anchor="center"),
        ]

    def build_activity(self, T):
        self.header(T, "activity")
        self.card(112, 104, 868, 536, T, lines=[(24, 76, 844, 76)])
        self.put_text(136, 124, "Event log", "title", "TEXT", T)
        self.log_count = self.put_text(136, 147, "", "small", "MUTED", T)
        self.copy_btn = Btn(self, 760, 124, 92, 36, T, kind="glass", text="Copy", icon="copy",
                            font="bodysb", icon_size=15, command=self.copy_log, radius=12)
        Btn(self, 862, 124, 94, 36, T, kind="glass", text="Clear", icon="trash", font="bodysb",
            icon_size=15, command=self.clear_log, radius=12)
        self.log_rows = []
        for i in range(LOG_ROWS):
            y = 196 + i * 28
            self.log_rows.append(dict(
                dot=self.put_image(144, y + 9, Image.new("RGBA", (2, 2)), T, anchor="center"),
                time=self.put_text(160, y, "", "mono", "FAINT", T),
                msg=self.put_text(266, y, "", "body", "TEXT", T)))
        self.log_thumb = self.put_image(958, 196, Image.new("RGBA", (2, 2)), T)
        self.log_empty = self.put_text(546, 380, "Nothing logged yet", "body", "FAINT", T,
                                       anchor="center")

    def build_settings(self, T):
        self.header(T, "settings")

        # appearance
        self.card(112, 104, 426, 296, T)
        self.put_text(136, 126, "Appearance", "title", "TEXT", T)
        self.put_text(136, 149, "Theme, colors and motion", "small", "MUTED", T)
        self.put_text(136, 199, "Theme", "bodysb", "TEXT", T, anchor="w")
        self.theme_seg = Segment(self, 318, 181, 196, 36, T, [("dark", "Dark"), ("light", "Light")],
                                 "dark" if self.dark else "light",
                                 lambda v: self.set_theme(v))
        self.put_text(136, 238, "Ambience", "bodysb", "TEXT", T, anchor="w")
        self.amb_tiles = {}
        for i, key in enumerate(AMBIENCE_ORDER):
            x = 136 + i * 96
            tag = self.new_tag()
            sel = key == self.cfg["ambience"]
            thumb = render_glow(round(self.S(86)), round(self.S(54)), 4.0, self.P, key).convert("RGBA")
            dot = AMBIENCES[key]
            sw = shape_image(22, 22, 11, self.scale, grad=(dot["a1"], dot["a2"]), sheen=60)
            thumb.alpha_composite(sw, (round(self.S(32)), round(self.S(16))))
            thumb = rounded(thumb, round(self.S(12)))
            if sel:
                ring = shape_image(90, 58, 14, self.scale, edge=rgba(self.A["a1"], 255))
                ring2 = shape_image(88, 56, 13, self.scale, edge=rgba(self.A["a2"], 200))
                self.put_image(x - 2, 256, ring, T)
                self.put_image(x - 1, 257, ring2, T)
            self.put_image(x, 258, thumb, T + (tag,))
            self.put_text(x + 43, 322, dot["name"], "small", "TEXT" if sel else "MUTED", T,
                          anchor="n")
            self.canvas.tag_bind(tag, "<Button-1>", lambda e, k=key: self.set_ambience(k))
            self.canvas.tag_bind(tag, "<Enter>", lambda e: self.canvas.configure(cursor="hand2"))
            self.canvas.tag_bind(tag, "<Leave>", lambda e: self.canvas.configure(cursor=""))
        self.anim_sw = Switch(self, 136, 352, T, "Animations", "Live background and smooth motion",
                              self.cfg["animations"], self.on_anim_switch)

        # ad handling
        self.card(554, 104, 426, 296, T)
        self.put_text(578, 126, "Ad handling", "title", "TEXT", T)
        self.put_text(578, 149, "What happens when an ad starts", "small", "MUTED", T)
        self.put_text(578, 184, caps("when an ad plays"), "cap", "MUTED", T)
        self.mode_seg = Segment(self, 578, 202, 378, 38, T, list(MODE_LABELS.items()),
                                self.cfg["mode"], self.on_mode_seg)
        self.mode_hint = self.put_text(580, 248, MODE_HINTS[self.cfg["mode"]], "small", "MUTED",
                                       T, width=374)
        self.put_text(578, 282, caps("after a restart, play"), "cap", "MUTED", T)
        self.after_seg = Segment(self, 578, 300, 378, 34, T, list(AFTER_LABELS.items()),
                                 self.cfg["after_ad"], self.on_after_seg)
        self.quiet_sw = Switch(self, 578, 350, T, "Reopen minimized",
                               "If Spotify was minimized before the ad",
                               self.cfg["quiet_restart"], self.on_quiet_changed)

        # general
        self.card(112, 416, 868, 224, T, lines=[(24, 174, 844, 174)])
        self.put_text(136, 438, "General", "title", "TEXT", T)
        self.put_text(136, 461, "Startup and behavior", "small", "MUTED", T)
        self.auto_sw = Switch(self, 136, 496, T, "Auto-start protection",
                              "Start protecting as soon as Ad Guard opens",
                              self.cfg["auto_start"], self.on_auto_changed)
        self.startup_sw = Switch(self, 568, 496, T, "Start with Windows",
                                 "Launch quietly when you sign in",
                                 self.cfg["windows_startup"], self.on_startup_changed)
        self.top_sw = Switch(self, 136, 544, T, "Keep window on top",
                             "Stay above other windows", self.cfg["on_top"], self.on_top_changed)
        self.debug_sw = Switch(self, 568, 544, T, "Verbose log",
                               "Show detailed detection messages", self.cfg["verbose"],
                               self.on_debug_changed)
        self.put_image(136, 603, make_logo(round(self.S(20)), amb=self.cfg["ambience"]), T)
        self.put_text(164, 613, f"Ad Guard for Spotify  ·  v{APP_VERSION}", "small", "MUTED", T,
                      anchor="w")
        ftag = self.new_tag()
        self.folder_link = self.put_text(956, 613, "Open data folder", "bodysb", self.ACC,
                                         T + (ftag,), anchor="e", state="normal")
        self.canvas.tag_bind(ftag, "<Button-1>", lambda e: self.open_data_folder())
        self.canvas.tag_bind(ftag, "<Enter>", lambda e: (
            self.canvas.configure(cursor="hand2"),
            self.canvas.itemconfigure(self.folder_link, fill=self.P["TEXT"])))
        self.canvas.tag_bind(ftag, "<Leave>", lambda e: (
            self.canvas.configure(cursor=""),
            self.canvas.itemconfigure(self.folder_link, fill=self.ACC)))
        self.apply_mode_ui()

    # ----- tooltip -----

    def show_tip(self, x, y, text, side="top"):
        self.hide_tip()
        f = self.fonts["small"]
        w = f.measure(text) / self.scale + 22
        h = 28
        if side == "right":
            x0, y0 = x, y - h / 2
        else:
            x0, y0 = x - w / 2, y - h - 8
        x0 = max(8, min(self.W - w - 8, x0))
        img = shape_image(round(w), h, 9, self.scale, fill=self.P["TIP"], edge=self.P["EDGE"],
                          glow=(0, 0, 0, 70), pad=8)
        self.tip_items = [
            self.put_image(x0 - 8, y0 - 8, img, ("tip",)),
            self.put_text(x0 + 11, y0 + h / 2, text, "small", "TEXT", ("tip",), anchor="w")]
        self.canvas.tag_raise("tip")

    def hide_tip(self):
        for it in self.tip_items:
            self.canvas.delete(it)
            self.ph.pop(it, None)
        self.tip_items = []

    # ----- theme / ambience -----

    def fade_rebuild(self, change):
        if self.rebuilding:
            return

        def swap():
            change()
            self.build_ui()
            save_settings(self.cfg)
            self.refresh_icon()

        if self.cfg["animations"]:
            self.rebuilding = True

            def back():
                self.rebuilding = False
                self.tween(260, lambda p: self.attributes("-alpha", 0.25 + 0.75 * ease_out(p)))

            self.tween(150, lambda p: self.attributes("-alpha", 1 - 0.75 * ease_out(p)),
                       lambda: (swap(), self.after(10, back)))
        else:
            swap()

    def set_theme(self, name):
        dark = name == "dark"
        if dark == self.dark:
            return

        def change():
            self.dark = dark
            self.cfg["theme"] = "dark" if dark else "light"
            ctk.set_appearance_mode(self.cfg["theme"])

        self.fade_rebuild(change)

    def set_ambience(self, key):
        if key == self.cfg["ambience"]:
            return
        self.fade_rebuild(lambda: self.cfg.__setitem__("ambience", key))

    # ----- animation engine -----

    def tween(self, ms, step, done=None, key=None):
        if self.closing:
            return
        if not self.cfg["animations"]:
            step(1.0)
            if done:
                done()
            return
        tok = None
        if key is not None:
            self._tok[key] = self._tok.get(key, 0) + 1
            tok = self._tok[key]
        t0 = time.time()

        def frame():
            if self.closing:
                return
            if key is not None and self._tok.get(key) != tok:
                return
            p = min(1.0, (time.time() - t0) * 1000.0 / ms)
            step(p)
            if p < 1.0:
                self.after(15, frame)
            elif done:
                done()

        frame()

    def intro(self):
        if self.cfg["animations"]:
            self.tween(420, lambda p: self.attributes("-alpha", ease_out(p)))
        else:
            self.attributes("-alpha", 1.0)
        self.pulse_at = time.time()

    def anim_tick(self):
        if self.closing:
            return
        start = time.time()
        try:
            if self.state() == "iconic":
                delay = 300
            elif self.cfg["animations"]:
                t = start - self.t0
                if start - self.bg_at > 0.07:
                    self.bg_at = start
                    self.draw_bg(t)
                self.draw_live(t, False)
                delay = max(10, 33 - int((time.time() - start) * 1000))
            else:
                if self.dirty:
                    self.draw_bg(0.0)
                    self.draw_live(0.0, True)
                    self.dirty = False
                delay = 150
        except Exception as e:  # never let a drawing error kill the loop
            print("animation error:", e)
            delay = 250
        self.after(delay, self.anim_tick)

    def draw_bg(self, t):
        cw, ch = round(self.S(self.W)), round(self.S(self.H))
        if (cw, ch) != self.bg_size:
            self.bg_size = (cw, ch)
            self.bg_photo = ImageTk.PhotoImage(Image.new("RGB", (cw, ch)))
            self.canvas.itemconfigure(self.bg_item, image=self.bg_photo)
        try:
            self.bg_photo.paste(render_glow(cw, ch, t, self.P, self.cfg["ambience"]))
        except Exception as e:
            print("background error:", e)

    def draw_live(self, t, static):
        self.draw_logo(t, static)
        self.draw_ring(t, static)
        self.draw_dots(t, static)

    def bar_targets(self, t, static):
        rest = (0.45, 1.0, 0.7)
        if static or self.mode == "off":
            return rest
        speeds = {"watching": (5.1, 6.3, 4.4), "restarting": (11.0, 13.0, 9.5),
                  "muted": (3.4, 4.1, 3.0)}.get(self.mode, (2.2, 2.8, 2.0))
        phases = (0.0, 1.9, 3.7)
        return tuple(0.30 + 0.70 * (0.5 + 0.5 * math.sin(t * speeds[i] + phases[i]))
                     for i in range(3))

    def draw_logo(self, t, static):
        target = self.bar_targets(t, static)
        if static:
            self.bar_cur = list(target)
        else:
            self.bar_cur = [c + (g - c) * 0.3 for c, g in zip(self.bar_cur, target)]
        bump = 0.0
        if not static:
            age = time.time() - self.pulse_at
            if 0 <= age < 0.7:
                bump = math.sin(math.pi * age / 0.7)
        size_px = max(20, int(round(self.S(42) * (1 + 0.12 * bump))))
        self.set_image(self.logo_item, make_logo(size_px, self.bar_cur, ss=3,
                                                 amb=self.cfg["ambience"]))

    def ring_layers(self, mode):
        if mode in self.ring_cache:
            return self.ring_cache[mode]
        P, A, s = self.P, self.A, self.scale
        D, th = 168, 12
        track = ring_image(D, th, s, _rgb(P["TRACK"]), alpha=P["TRACK"][3])
        base, comet = track, None
        white = (255, 255, 255)
        if mode == "watching":
            base = Image.alpha_composite(track, ring_image(D, th, s, (A["a1"], A["a2"]), glow=0.85))
            comet = ring_image(D, th, s, white, sweep=80, ramp=True, alpha=170 if self.dark else 120)
        elif mode == "muted":
            blue = _rgb(P["BLUE"])
            base = Image.alpha_composite(track, ring_image(D, th, s, (blue, mix(blue, A["a2"], 0.5)),
                                                           glow=0.8))
            comet = ring_image(D, th, s, white, sweep=80, ramp=True, alpha=150)
        elif mode in ("waiting", "restarting"):
            amber = _rgb(P["AMBER"])
            sweep = 110 if mode == "waiting" else 230
            comet = ring_image(D, th, s, amber, sweep=sweep, ramp=True, glow=0.7)
        self.ring_cache[mode] = (base, comet)
        return base, comet

    def draw_ring(self, t, static):
        base, comet = self.ring_layers(self.mode)
        if comet is None:
            sig = (self.mode, "still")
            if sig != self._ring_sig:
                self._ring_sig = sig
                self.set_image(self.ring_item, base)
            return
        ang = 0.0 if static else (t * RING_SPEED.get(self.mode, 0.2) * 360.0) % 360.0
        sig = (self.mode, round(ang, 1))
        if sig == self._ring_sig:
            return
        self._ring_sig = sig
        frame = base.copy()
        frame.alpha_composite(comet.rotate(-ang, resample=RESAMPLE.BICUBIC) if ang else comet)
        self.set_image(self.ring_item, frame)

    def draw_dots(self, t, static):
        key, *_ = LOOK[self.mode]
        period = None if static else PULSE.get(self.mode)
        self.set_image(self.chip_dot, make_dot(hex_to_rgb(self.P[key]), t, period,
                                               size=round(self.S(22))))

    # ----- status / button -----

    def running(self):
        return bool(self.watcher and self.watcher.is_alive())

    def update_sub(self):
        sub = LOOK[self.mode][2]
        if self.started_at:
            elapsed = int(time.time() - self.started_at)
            h, rem = divmod(elapsed, 3600)
            m, sec = divmod(rem, 60)
            sub += f"  ·  {h}:{m:02d}:{sec:02d}" if h else f"  ·  {m:02d}:{sec:02d}"
        self.set_text(self.status_sub, sub)

    def set_status(self, mode):
        self.mode = mode
        key, title, _, chip = LOOK[mode]
        P = self.P
        self.set_text(self.status_title, title)
        self.update_sub()
        self.set_text(self.mode_txt, MODE_LINES[self.cfg["mode"]])
        color = P[key]
        w = self.fonts["cap"].measure(caps(chip)) / self.scale + 40
        self.set_image(self.chip_bg, shape_image(round(w), 24, 12, self.scale,
                                                 fill=rgba(color, 34), edge=rgba(color, 90)))
        self.set_text(self.chip_txt, caps(chip), color)
        self.set_text(self.ring_cap, caps("blocked today"))
        self._ring_sig = None
        self.dirty = True

    def style_button(self, animated=True):
        if self.running():
            self.main_btn.configure(kind="danger", text="Stop protection")
        else:
            self.main_btn.configure(kind="accent", text="Start protection")

    def flash(self, item, color=None):
        start = color or self.ACC

        def step(p):
            self.canvas.itemconfigure(item, fill=lerp_hex(start, self.P["TEXT"], ease_out(p)))

        self.tween(1100, step, key=f"flash{item}")

    # ----- pages -----

    def set_off(self, name, off):
        delta = off - self.page_off[name]
        if delta:
            self.canvas.move(f"pg-{name}", 0, self.S(delta))
            self.page_off[name] = off

    def show_page(self, name):
        if self.sliding or name == self.page or self.rebuilding:
            return
        order = [p[0] for p in PAGES]
        sign = 1 if order.index(name) > order.index(self.page) else -1
        out, inc = self.page, name
        self.hide_tip()
        self.on_chart_leave(None)
        self.sliding = True
        self.set_off(inc, sign * self.H)
        self.page = inc
        self.paint_nav()
        y0, y1 = self.nav_y(out), self.nav_y(inc)
        cx = self.S(56)
        if inc == "activity":
            self.log_scroll = 0
            self.render_log()

        def step(p):
            e = ease_out(p)
            self.set_off(out, -sign * self.H * e)
            self.set_off(inc, sign * self.H * (1 - e))
            self.canvas.coords(self.nav_ind, cx, self.S(y0 + (y1 - y0) * ease_in_out(p)))

        def done():
            self.set_off(out, self.H * 2)
            self.set_off(inc, 0)
            self.sliding = False

        self.tween(420, step, done)

    # ----- settings handlers -----

    def on_anim_switch(self, value):
        self.cfg["animations"] = value
        save_settings(self.cfg)
        self.dirty = True
        if value:
            self.pulse_at = time.time()

    def toggle_on_top(self):
        self.top_sw.set(not self.cfg["on_top"], animate=True)
        self.on_top_changed(not self.cfg["on_top"])

    def on_top_changed(self, value):
        self.cfg["on_top"] = value
        self.attributes("-topmost", value)
        save_settings(self.cfg)
        self.paint_nav()

    def on_mode_seg(self, value):
        self.cfg["mode"] = value
        save_settings(self.cfg)
        self.apply_mode_ui()
        self.set_text(self.mode_txt, MODE_LINES[value])

    def apply_mode_ui(self):
        mode = self.cfg["mode"]
        self.set_text(self.mode_hint, MODE_HINTS[mode])
        on = mode == "restart"
        self.after_seg.set_enabled(on)
        self.quiet_sw.set_enabled(on)

    def on_after_seg(self, value):
        self.cfg["after_ad"] = value
        save_settings(self.cfg)

    def on_quiet_changed(self, value):
        self.cfg["quiet_restart"] = value
        save_settings(self.cfg)

    def on_debug_changed(self, value):
        self.cfg["verbose"] = value
        save_settings(self.cfg)

    def on_auto_changed(self, value):
        self.cfg["auto_start"] = value
        save_settings(self.cfg)

    def on_startup_changed(self, value):
        if set_windows_startup(value):
            self.cfg["windows_startup"] = value
            save_settings(self.cfg)
        else:
            self.startup_sw.set(not value, animate=True)
            self.add_log("warn", stamp(), "Couldn't change the Windows startup setting.")

    def open_data_folder(self):
        try:
            os.makedirs(SETTINGS_DIR, exist_ok=True)
            os.startfile(SETTINGS_DIR)
        except Exception:
            self.add_log("warn", stamp(), "Couldn't open the data folder.")

    # ----- actions -----

    def auto_start(self):
        if not self.running() and not self.closing:
            self.toggle()

    def toggle(self):
        if self.running():
            self.watcher.stop_event.set()
            self.watcher = None
            self.started_at = None
            self.ad_flag, self.action = False, None
            self.set_status("off")
        else:
            self.watcher = Watcher(self.q, self.cfg, self.feed.media)
            self.watcher.start()
            self.started_at = time.time()
            self.set_status("watching")
        self.pulse_at = time.time()
        self.style_button(animated=True)

    def on_skip_ad(self):
        if self.running():
            self.watcher.skip_now.set()
        else:
            self.toggle()  # protection is off: turn it on

    def player_cmd(self, name):
        if name == "toggle":  # flip the icon at once, the card confirms it a moment later
            self.playing_icon = not self.playing_icon
            self.opt_until = time.time() + 1.2
            self._ui["playicon"] = self.playing_icon
            self.play_btn.configure(icon="pause" if self.playing_icon else "play")
        threading.Thread(target=self.feed.command, args=(name,), daemon=True).start()

    # ----- activity log -----

    def clear_log(self):
        self.logs = []
        self.log_scroll = 0
        self.render_log()

    def copy_log(self):
        text = "\n".join(f"{ts}  {msg}" for _, ts, msg in self.logs)
        try:
            self.clipboard_clear()
            self.clipboard_append(text)
            self.copy_btn.configure(text="Copied", icon="check")
            self.after(1400, lambda: self.copy_btn.configure(text="Copy", icon="copy"))
        except Exception:
            pass

    def add_log(self, level, ts, msg):
        self.logs.append((level, ts, msg))
        if len(self.logs) > LOG_MAX:
            del self.logs[:50]
        if self.log_scroll:
            self.log_scroll += 1  # keep the rows you are reading in place
        self.render_log()

    def on_wheel(self, e):
        if self.page != "activity" or self.sliding:
            return
        top = max(0, len(self.logs) - LOG_ROWS)
        step = 3 if e.delta > 0 else -3
        new = max(0, min(top, self.log_scroll + step))
        if new != self.log_scroll:
            self.log_scroll = new
            self.render_log()

    def render_log(self):
        P = self.P
        n = len(self.logs)
        self.log_scroll = max(0, min(self.log_scroll, max(0, n - LOG_ROWS)))
        end = n - self.log_scroll
        rows = self.logs[max(0, end - LOG_ROWS):end]
        colors = {"ok": P["GREEN"], "warn": P["AMBER"]}
        c = self.canvas
        for i, row in enumerate(self.log_rows):
            if i < len(rows):
                level, ts, msg = rows[i]
                self.set_image(row["dot"], self.level_dot(colors.get(level, P["FAINT"])))
                c.itemconfigure(row["dot"], state="normal")
                self.set_text(row["time"], ts)
                self.set_text(row["msg"], self.fit(msg, self.fonts["body"], 680),
                              P["TEXT"] if level != "info" else P["MUTED"])
            else:
                c.itemconfigure(row["dot"], state="hidden")
                self.set_text(row["time"], "")
                self.set_text(row["msg"], "")
        c.itemconfigure(self.log_empty, state="hidden" if n else "disabled")
        word = "event" if n == 1 else "events"
        extra = f"  ·  scrolled back {self.log_scroll}" if self.log_scroll else ""
        self.set_text(self.log_count, f"{n} {word} this session{extra}")
        if n > LOG_ROWS:
            span = 28 * LOG_ROWS - 8
            th = max(30, span * LOG_ROWS / n)
            frac = 1 - self.log_scroll / max(1, n - LOG_ROWS)
            y = 196 + (span - th) * frac
            x0 = self.canvas.coords(self.log_thumb)
            img = shape_image(4, round(th), 2, self.scale, fill=P["CHIP_HOVER"])
            self.set_image(self.log_thumb, img)
            self.canvas.coords(self.log_thumb, x0[0], self.S(y + self.page_off.get("activity", 0)))
            c.itemconfigure(self.log_thumb, state="normal")
        else:
            c.itemconfigure(self.log_thumb, state="hidden")

    def level_dot(self, color):
        key = ("dot", color)
        if key not in self.photos:
            self.photos[key] = make_dot(hex_to_rgb(color), 0, None, size=round(self.S(18)))
        return self.photos[key]

    # ----- history (chart and recent ads) -----

    def day_counts(self, days=14):
        today = date.today()
        counts = [0] * days
        for ts, _, _ in self.cfg["history"]:
            d = (today - date.fromtimestamp(ts)).days
            if 0 <= d < days:
                counts[days - 1 - d] += 1
        return counts

    def render_history(self):
        P = self.P
        counts = self.day_counts()
        self.counts = counts
        self.chart_top = max(4, math.ceil(max(counts) * 1.15)) if counts else 4
        self.set_image(self.chart_item, chart_image(512, 120, counts, self.chart_top,
                                                    self.chart_hover, self.scale, P,
                                                    self.cfg["ambience"]))
        today = date.today()
        for i, item in enumerate(self.chart_labels):
            d = date.fromordinal(today.toordinal() - (13 - i))
            label = "Today" if i == 13 else d.strftime("%a")[:2]
            self.set_text(item, label, P["TEXT"] if i == 13 else P["FAINT"])
        week = sum(counts[-7:])
        self.set_text(self.week_val, f"{week:,}")
        avg = sum(counts) / len(counts)
        self.set_text(self.avg_val, f"{avg:.1f}" if avg < 10 else f"{avg:.0f}")
        self.set_text(self.ring_num, f"{counts[-1]:,}")
        self.render_recent()

    def render_recent(self):
        P = self.P
        items = list(reversed(self.cfg["history"][-4:]))
        for i, row in enumerate(self.recent):
            c = self.canvas
            if i < len(items):
                ts, secs, how = items[i]
                muted = how == "m"
                color = P["BLUE"] if muted else self.ACC
                key = ("badge", how)
                if key not in self.photos:
                    img = shape_image(32, 32, 10, self.scale, fill=rgba(color, 40),
                                      edge=rgba(color, 70)).copy()
                    ic = line_icon("volume_x" if muted else "refresh", round(self.S(16)), color)
                    img.alpha_composite(ic, ((img.size[0] - ic.size[0]) // 2,
                                             (img.size[1] - ic.size[1]) // 2))
                    self.photos[key] = img
                self.set_image(row["badge"], self.photos[key])
                c.itemconfigure(row["badge"], state="normal")
                self.set_text(row["title"], "Ad muted" if muted else "Ad skipped")
                if muted:
                    sub = f"Silenced for {fmt_duration(secs)}" if secs else "Silenced until it ended"
                else:
                    sub = "Spotify restarted"
                self.set_text(row["sub"], sub)
                self.set_text(row["when"], ago(ts))
            else:
                c.itemconfigure(row["badge"], state="hidden")
                for k in ("title", "sub", "when"):
                    self.set_text(row[k], "")
        for it in self.recent_empty:
            self.canvas.itemconfigure(it, state="hidden" if items else "disabled")

    def on_chart_motion(self, e):
        x0, y0 = self.canvas.coords(self.chart_item)
        i = int((e.x - x0) / self.S(512 / 14))
        i = max(0, min(13, i))
        if i == self.chart_hover:
            return
        self.chart_hover = i
        self.set_image(self.chart_item, chart_image(512, 120, self.counts, self.chart_top, i,
                                                    self.scale, self.P, self.cfg["ambience"]))
        d = date.fromordinal(date.today().toordinal() - (13 - i))
        v = self.counts[i]
        bh = 0 if v <= 0 else max(6, 117 * min(1.0, v / self.chart_top))
        word = "ad" if v == 1 else "ads"
        label = "Today" if i == 13 else d.strftime("%a %d %b").replace(" 0", " ")
        self.show_tip(136 + 512 / 14 * (i + 0.5), 476 + 120 - bh - 4, f"{label}  ·  {v} {word}")

    def on_chart_leave(self, e):
        if self.chart_hover is None:
            return
        self.chart_hover = None
        self.hide_tip()
        self.set_image(self.chart_item, chart_image(512, 120, self.counts, self.chart_top, None,
                                                    self.scale, self.P, self.cfg["ambience"]))

    # ----- now playing card -----

    def fit(self, text, font, width):
        """Shorten text with an ellipsis so it fits in `width` (logical) pixels."""
        limit = width * self.scale
        try:
            if font.measure(text) <= limit:
                return text
            while text and font.measure(text + "…") > limit:
                text = text[:-1]
            return text.rstrip() + "…"
        except Exception:
            return text

    def now_look(self, view):
        """(chip text, chip color key, title, artist) for the card."""
        kind = view["kind"]
        if self.action == "restarting":
            return "Skipping ad", "AMBER", "Restarting Spotify…", "Back in a moment"
        if kind == "ad":
            if self.action == "muted":
                held = fmt_clock(time.time() - self.action_since)
                return f"Ad muted  {held}", "BLUE", "Advertisement", "Silent until the ad ends"
            return "Ad playing", "AMBER", "Advertisement", "Spotify"
        if kind == "track":
            return "Now playing", "GREEN", view["title"], view["artist"]
        if kind == "paused":
            return "Paused", "MUTED", view["title"], view["artist"]
        if kind == "idle":
            return "Spotify open", "MUTED", "Nothing playing", "Press play in Spotify"
        return "Not running", "FAINT", "Spotify isn't running", "Open it and your music shows here"

    def refresh_now(self):
        if self.closing:
            return
        try:
            if not self.rebuilding:
                view = self.feed.view(self.ad_flag, self.last_track)
                if view["kind"] == "track" and view["title"]:
                    self.last_track = dict(view)
                self.render_now(view)
        except Exception as e:  # the card must never take the window down
            print("now playing error:", e)
        self.after(300, self.refresh_now)

    def changed(self, key, value):
        """True (and remembers it) if `value` differs from the last one shown for `key`."""
        if self._ui.get(key) == value:
            return False
        self._ui[key] = value
        return True

    def render_now(self, view):
        P, f = self.P, self.fonts
        kind = view["kind"]
        chip, ckey, title, artist = self.now_look(view)
        if self.changed("chip", (chip, ckey)):
            self.set_text(self.np_chip, caps(chip), P[ckey])
            self.set_image(self.np_dot, self.level_dot(P[ckey]))

        sig = (title, artist)
        if sig != self.title_shown:
            fresh = self.title_shown is not None and kind in ("track", "paused")
            self.title_shown = sig
            self.set_text(self.np_title, self.fit(title, f["track"], 188))
            self.set_text(self.np_artist, self.fit(artist, f["body"], 188))
            if fresh:
                c0, c1 = P["SURFACE"], P["TEXT"]
                self.tween(360, lambda p: self.canvas.itemconfigure(
                    self.np_title, fill=lerp_hex(c0, c1, ease_out(p))), key="title")
        album = (view.get("album") or "") if kind in ("track", "paused") else ""
        if self.changed("album", album):
            self.set_text(self.np_album, self.fit(album, f["small"], 188))

        art = view["art"]
        akey = (kind, self.action, view["track_id"], len(art) if art else 0, title)
        if akey != self.art_key:
            self.art_key = akey
            px, rad = round(self.S(self.ART)), round(self.S(16))
            img = art_from_bytes(art, px, rad) if art and kind in ("track", "paused") else None
            if img is None:
                if kind == "ad" or self.action == "restarting":
                    c1 = _rgb(P["BLUE"]) if self.action == "muted" else _rgb(P["AMBER"])
                    img = placeholder_art(px, rad, c1, self.A["a2"],
                                          "volume_x" if self.action == "muted" else "zap",
                                          P["SURFACE"])
                else:
                    img = placeholder_art(px, rad, self.A["a1"], self.A["a2"], "music", P["SURFACE"])
            self.set_image(self.art_item, img)
            self.set_image(self.art_glow, art_glow(img, round(self.S(26)),
                                                   0.75 if self.dark else 0.45))

        if view["dur"] and kind in ("track", "paused"):
            frac = view["pos"] / view["dur"]
            if self.changed("pbar", round(frac * 324)):
                self.set_image(self.pbar, bar_image(324, 5, frac, self.scale, P["TRACK"],
                                                    self.A["a1"], self.A["a2"]))
            self.set_text(self.t_left, fmt_clock(view["pos"]))
            self.set_text(self.t_right, fmt_clock(view["dur"]))
        elif self.changed("pbar", -1):
            self.set_image(self.pbar, bar_image(324, 5, 0, self.scale, P["TRACK"],
                                                self.A["a1"], self.A["a2"]))
            self.set_text(self.t_left, "--:--")
            self.set_text(self.t_right, "--:--")

        is_ad = kind == "ad" or self.action == "restarting"
        if self.changed("controls", not is_ad):
            for b in (self.prev_btn, self.play_btn, self.next_btn):
                b.set_visible(not is_ad)
            self.skip_btn.set_visible(is_ad)
        if is_ad:
            label = "Skip this ad" if self.running() else "Start protection"
            if self.action == "restarting":
                label = "Skipping…"
            enabled = self.action != "restarting"
            if self.changed("adbtn", (label, enabled)):
                self.skip_btn.configure(text=label, enabled=enabled)
        else:
            enabled = kind in ("track", "paused", "idle")
            if self.changed("btnstate", enabled):
                for b in (self.prev_btn, self.play_btn, self.next_btn):
                    b.configure(enabled=enabled)
            if time.time() > self.opt_until:  # not right after you pressed play/pause
                self.playing_icon = bool(view["playing"])
            if self.changed("playicon", self.playing_icon):
                self.play_btn.configure(icon="pause" if self.playing_icon else "play")

    def update_spotify_pill(self, force=False):
        try:
            kind = self.feed.view(self.ad_flag, self.last_track)["kind"]
        except Exception:
            kind = "none"
        state = kind != "none"
        if state == self.spotify_state and not force:
            return
        self.spotify_state = state
        P = self.P
        color = P["GREEN"] if state else P["FAINT"]
        self.set_image(self.sp_dot, make_dot(hex_to_rgb(color), 0, None, size=round(self.S(18))))
        self.set_text(self.sp_text, "Spotify connected" if state else "Spotify not running",
                      P["TEXT"] if state else P["MUTED"])

    # ----- stats -----

    def update_stats(self):
        self.set_text(self.stat_vals[0], fmt_duration(self.cfg["lifetime_saved"]))
        self.set_text(self.stat_vals[1], f"{self.cfg['lifetime_ads']:,}")
        self.set_text(self.stat_vals[2], self.last_ad)

    def count_ad(self, clock_text, how):
        self.total_skipped += 1
        self.cfg["lifetime_ads"] += 1
        self.last_ad = clock_text
        restart = how == "restart"
        self.cfg["history"].append([int(time.time()), AD_ESTIMATE if restart else 0,
                                    "r" if restart else "m"])
        del self.cfg["history"][:-HISTORY_MAX]
        self.pulse_at = time.time()
        if restart:  # an ad skipped by restarting: assume a typical length
            self.add_saved(AD_ESTIMATE, record=False)
        else:
            save_settings(self.cfg)
        self.update_stats()
        self.render_history()
        for item in (self.stat_vals[1], self.stat_vals[2], self.ring_num):
            self.flash(item)

    def add_saved(self, seconds, record=True):
        self.saved_seconds += seconds
        self.cfg["lifetime_saved"] = int(self.cfg["lifetime_saved"] + seconds)
        h = self.cfg["history"]
        if record and h and h[-1][2] == "m" and not h[-1][1] and time.time() - h[-1][0] < 600:
            h[-1][1] = int(seconds)  # a muted ad just ended: remember how long it was
            self.render_recent()
        self.update_stats()
        self.flash(self.stat_vals[0])
        save_settings(self.cfg)

    # ----- loops -----

    def on_crashed(self, why=""):
        if self.watcher is not None:
            self.watcher = None
            self.started_at = None
            self.ad_flag, self.action = False, None
            self.set_status("off")
            self.style_button(animated=True)
            self.add_log("warn", stamp(), "Protection stopped unexpectedly. Press start to resume.")

    def pump(self):
        if self.closing:
            return
        try:
            while not self.rebuilding:
                msg = self.q.get_nowait()
                kind = msg[0]
                if kind == "log":
                    self.add_log(msg[1], msg[2], msg[3])
                elif kind == "status" and self.watcher:
                    self.set_status(msg[1])
                elif kind == "state":
                    self.ad_flag = msg[1]["ad"]
                    if msg[1]["action"] != self.action:
                        self.action_since = time.time()
                    self.action = msg[1]["action"]
                elif kind == "ad":
                    self.count_ad(msg[1], msg[2] if len(msg) > 2 else "restart")
                elif kind == "saved":
                    self.add_saved(msg[1])
                elif kind == "crashed":
                    self.on_crashed(msg[1])
        except queue.Empty:
            pass
        self.after(100, self.pump)

    def tick(self):
        if self.closing:
            return
        if not self.rebuilding:
            if self.watcher is not None and not self.watcher.is_alive():
                self.on_crashed()
            self.update_sub()
            self.update_spotify_pill()
            if int(time.time()) % 15 == 0:
                self.render_recent()
            if self.changed("day", date.today().toordinal()):
                self.render_history()  # a new day: the chart moves along
            media = self.feed.media
            if media.ready and not self._media_seen:
                self._media_seen = True
                self.add_log("ok", stamp(), "Connected to Spotify's media controls "
                             "(album art, exact pause detection)")
            if media.error and media.error != self._media_err:
                self._media_err = media.error  # each new problem once, so it can be reported
                self.add_log("warn", stamp(), f"Media controls: {media.error}")
        self.after(1000, self.tick)

    def on_close(self):
        self.closing = True
        save_settings(self.cfg)
        w = self.watcher
        if w:
            w.stop_event.set()
            w.join(1.5)  # lets it hand Spotify's sound back if an ad was muted
        self.feed.stop_event.set()
        self.destroy()


if __name__ == "__main__":
    try:  # gives the app its own taskbar icon instead of python's
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(APP_ID)
    except Exception:
        pass
    if not single_instance():
        try:
            ctypes.windll.user32.MessageBoxW(0, "Ad Guard is already running.\n"
                                             "Look for it in the taskbar.",
                                             "Ad Guard for Spotify", 0x40)
        except Exception:
            pass
        sys.exit(0)
    App(start_minimized="--startup" in sys.argv).mainloop()
