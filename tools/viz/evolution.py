# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""The module import graph as a poster and as a growing-network video.

Layout: Graphviz `sfdp` lays out, once, the import graph of every library module that ever
existed (undirected; edges into `CslibFrontier.Init`, which every module imports, are left out
because they would pull everything into one star). Modules keep their place for the whole video
and the camera follows the visible part. Frames are drawn with Pillow and piped to ffmpeg.
"""

from __future__ import annotations

import colorsys
import datetime as dt
import hashlib
import json
import math
import shutil
import subprocess
import tempfile
from collections import Counter
from pathlib import Path

import numpy as np
from matplotlib import font_manager
from PIL import Image, ImageDraw, ImageFont

import history as h
import style as s

INIT = "CslibFrontier.Init"
SWEEP = 150  # commits touching more library files than this do not make modules glow
LAYOUT_VERSION = 4
T = s.DARK
BG = (13, 13, 13)


def _rgb(hexcolor: str) -> tuple[int, int, int]:
    hexcolor = hexcolor.lstrip("#")
    return tuple(int(hexcolor[i:i + 2], 16) for i in (0, 2, 4))  # type: ignore[return-value]


def _lift(rgb, amount=0.18):
    """A slightly lighter step of a colour, for glow on the near-black page."""
    r, g, b = (c / 255 for c in rgb)
    hh, ll, ss = colorsys.rgb_to_hls(r, g, b)
    r, g, b = colorsys.hls_to_rgb(hh, min(1, ll + amount), ss)
    return int(r * 255), int(g * 255), int(b * 255)


AREA_RGB = {a: _rgb(c) for a, c in s.area_colors(T).items()}


def _font(size: int, bold: bool = False) -> ImageFont.FreeTypeFont:
    path = font_manager.findfont(font_manager.FontProperties(
        family="DejaVu Sans", weight="bold" if bold else "normal"))
    return ImageFont.truetype(path, size)


# --------------------------------------------------------------------------------------------
# Layout


def _sfdp(nodes: list[str], edges: list[tuple[str, str]], init: dict[str, tuple[float, float]]):
    ids = {m: i for i, m in enumerate(nodes)}
    lines = ["graph G {", "graph [overlap=true, splines=false, outputorder=edgesfirst];",
             "node [shape=point];"]
    for m in nodes:
        if m in init:
            x, y = init[m]
            lines.append(f'{ids[m]} [pos="{x:.4f},{y:.4f}"];')
        else:
            lines.append(f"{ids[m]};")
    for a, b in edges:
        lines.append(f"{ids[a]}--{ids[b]};")
    lines.append("}")
    out = subprocess.run(["sfdp", "-Tplain"], input="\n".join(lines), capture_output=True,
                         text=True, check=True).stdout
    pos = {}
    for line in out.splitlines():
        if line.startswith("node "):
            _, i, x, y, *_ = line.split()
            pos[nodes[int(i)]] = (float(x), float(y))
    return pos


def _layout_edges(graph: dict[str, set[str]]):
    return [(m, d) for m, ds in graph.items() for d in ds if d != INIT and m != INIT]


def layout(H: h.History) -> dict[str, tuple[float, float]]:
    """One fixed position for every library module that ever existed, cached on disk.

    The graph laid out is the union over history: each module with the imports of its latest
    version. A fixed layout keeps every module in place for the whole video, so growth reads as
    the graph filling in while the camera pulls back."""
    key = f"{LAYOUT_VERSION}:{H.blobs.fingerprint}:{H.commits[-1].sha}"
    fp = hashlib.sha256(key.encode()).hexdigest()[:16]
    cache = h.HERE / ".cache" / f"layout-{fp}.json"
    if cache.exists():
        return {m: tuple(p) for m, p in json.loads(cache.read_text()).items()}
    latest: dict[str, str] = {}
    for c in H.commits:
        for p, b in c.changes:
            if b and h.is_library(p):
                latest[p] = b
    graph = h.import_graph(H.blobs, latest)
    # Hidden directory nodes tie each module to its folder and each folder to its parent, so
    # the layout groups modules by place in the tree as well as by imports.
    edges = _layout_edges(graph)
    dirs: set[str] = set()
    for m in graph:
        parts = m.split(".")
        child = m
        for k in range(len(parts) - 1, 0, -1):
            d = "dir:" + ".".join(parts[:k])
            edges.append((child, d))
            if d in dirs:
                break
            dirs.add(d)
            child = d
    pos = _sfdp(sorted(graph) + sorted(dirs), edges, {})
    pos = {m: p for m, p in pos.items() if not m.startswith("dir:")}
    cache.parent.mkdir(parents=True, exist_ok=True)
    for old in cache.parent.glob("layout-*.json"):
        old.unlink()
    cache.write_text(json.dumps(pos))
    return pos


# --------------------------------------------------------------------------------------------
# Rendering


class Renderer:
    def __init__(self, H: h.History, width: int, height: int,
                 pos: dict[str, tuple[float, float]] | None = None):
        self.H = H
        self.W, self.Hh = width, height
        pos = layout(H) if pos is None else pos
        self.mods = sorted(pos)
        self.mid = {m: i for i, m in enumerate(self.mods)}
        self.P = np.array([pos[m] for m in self.mods])
        self.area = np.array([s.ALL_AREAS.index(h.area_of(m.replace(".", "/") + ".lean"))
                              for m in self.mods])
        self.cam = None
        unit = height / 1080
        self.u = unit
        self.f_title = _font(int(30 * unit), bold=True)
        self.f_big = _font(int(26 * unit), bold=True)
        self.f_med = _font(int(17 * unit))
        self.f_small = _font(int(14 * unit))
        self.f_area = _font(int(17 * unit), bold=True)

    def positions(self, t: float) -> np.ndarray:
        return self.P

    def camera(self, pts: np.ndarray, smooth: float):
        if len(pts) == 0:
            return self.cam or (0.0, 0.0, 1.0)
        lo = np.percentile(pts, 0.5, axis=0)
        hi = np.percentile(pts, 99.5, axis=0)
        cx, cy = (lo + hi) / 2
        margin_x, margin_y = self.W * 0.66, self.Hh * 0.78
        span = max((hi[0] - lo[0]) / margin_x, (hi[1] - lo[1]) / margin_y, 1e-3)
        target = (cx, cy, span)
        if self.cam is None or smooth >= 1:
            self.cam = target
        else:
            self.cam = tuple(c + (t - c) * smooth for c, t in zip(self.cam, target))
        return self.cam

    def draw(self, t: float, state: "State", smooth: float = 0.08, recent: dict | None = None,
             caption: bool = True) -> Image.Image:
        P = self.positions(t)
        vis = np.array([self.mid[m] for m in state.graph if m in self.mid], dtype=int)
        vis = vis[~np.isnan(P[vis, 0])] if len(vis) else vis
        cx, cy, span = self.camera(P[vis], smooth)
        ox = self.W * 0.56
        oy = self.Hh * 0.53

        def screen(idx):
            q = P[idx]
            return np.stack([(q[:, 0] - cx) / span + ox, oy - (q[:, 1] - cy) / span], axis=1)

        img = Image.new("RGB", (self.W, self.Hh), BG)
        layer = Image.new("RGBA", (self.W, self.Hh), (0, 0, 0, 0))
        d = ImageDraw.Draw(layer, "RGBA")
        n_vis = max(1, len(vis))
        # Edges.
        if state.edges:
            ea = np.array([self.mid[a] for a, _ in state.edges])
            eb = np.array([self.mid[b] for _, b in state.edges])
            ok = ~(np.isnan(P[ea, 0]) | np.isnan(P[eb, 0]))
            ea, eb = ea[ok], eb[ok]
            sa, sb = screen(ea), screen(eb)
            alpha = int(max(28, min(90, 4000 / math.sqrt(len(ea) + 1))))
            ew = max(1, int(round(self.u)))
            for (x0, y0), (x1, y1), ar in zip(sa, sb, self.area[ea]):
                r, g, b = AREA_RGB[s.ALL_AREAS[ar]]
                d.line((x0, y0, x1, y1), fill=(r, g, b, alpha), width=ew)
        img.paste(layer, (0, 0), layer)
        d = ImageDraw.Draw(img, "RGBA")
        # Nodes.
        if len(vis):
            sp = screen(vis)
            base = max(1.2, min(4.5, 90 / math.sqrt(n_vis))) * self.u
            for (x, y), i in zip(sp, vis):
                m = self.mods[i]
                size = state.code.get(m, 0)
                r = base * (0.55 + 0.45 * math.sqrt(min(size, 2500) / 200))
                col = AREA_RGB[s.ALL_AREAS[self.area[i]]]
                age = recent.get(m) if recent else None
                if age is not None:
                    glow = 1 - age
                    rr = r + (2 + 6 * glow) * self.u
                    lc = _lift(col, 0.3)
                    d.ellipse((x - rr, y - rr, x + rr, y + rr),
                              fill=(*lc, int(25 + 70 * glow)))
                    col = _lift(col, 0.25 * glow + 0.05)
                d.ellipse((x - r, y - r, x + r, y + r), fill=col)
            # Area labels on the densest part of each area's modules, nudged apart.
            labels = []
            cell = 40 * self.u
            for ai, a in enumerate(s.ALL_AREAS):
                sel = sp[self.area[vis] == ai]
                if len(sel) < 25 or a == h.OTHER:
                    continue
                gx = np.floor(sel[:, 0] / cell).astype(int)
                gy = np.floor(sel[:, 1] / cell).astype(int)
                keys, counts = np.unique(np.stack([gx, gy], 1), axis=0, return_counts=True)
                kx, ky = keys[np.argmax(counts)]
                labels.append([(kx + 0.5) * cell, (ky + 0.5) * cell, a])
            gap = 30 * self.u
            for _ in range(30):
                for i in range(len(labels)):
                    for j in range(i + 1, len(labels)):
                        dx = labels[j][0] - labels[i][0]
                        dy = labels[j][1] - labels[i][1]
                        wx = (len(labels[i][2]) + len(labels[j][2])) * 5.5 * self.u
                        if abs(dx) < wx and abs(dy) < gap:
                            push = (gap - abs(dy)) / 2 + 1
                            sgn = 1 if dy >= 0 else -1
                            labels[i][1] -= sgn * push
                            labels[j][1] += sgn * push
            for x, y, a in labels:
                d.text((x, y), a, font=self.f_area, fill=(240, 239, 236), anchor="mm",
                       stroke_width=int(3 * self.u), stroke_fill=BG)
        if caption:
            self.overlay(d, t, state)
        return img

    def overlay(self, d: ImageDraw.ImageDraw, t: float, state: "State"):
        u = self.u
        ink, ink2, muted = _rgb(T.ink), _rgb(T.ink2), _rgb(T.muted)
        x0, y = int(40 * u), int(36 * u)
        d.text((x0, y), "cslib-frontier", font=self.f_title, fill=ink)
        y += int(42 * u)
        d.text((x0, y), "module import graph", font=self.f_med, fill=ink2)
        y += int(46 * u)
        when = dt.datetime.fromtimestamp(t, dt.timezone.utc)
        d.text((x0, y), f"{when:%a %b %-d, %Y}", font=self.f_big, fill=ink)
        y += int(34 * u)
        d.text((x0, y), f"{when:%H:%M} UTC", font=self.f_med, fill=ink2)
        y += int(52 * u)
        for label, val in (("modules", len(state.graph)), ("lines of code", state.total_code),
                           ("theorems", state.theorems), ("imports", state.n_imports)):
            d.text((x0, y), s.human(val) if val >= 10000 else f"{val:,}", font=self.f_big,
                   fill=ink)
            d.text((x0, y + int(31 * u)), label, font=self.f_small, fill=ink2)
            y += int(66 * u)
        # Legend.
        y = self.Hh - int(40 * u) - len(s.ALL_AREAS) * int(24 * u)
        for a in s.ALL_AREAS:
            col = AREA_RGB[a]
            r = int(6 * u)
            d.ellipse((x0, y + int(9 * u) - r, x0 + 2 * r, y + int(9 * u) + r), fill=col)
            d.text((x0 + int(22 * u), y), a, font=self.f_small, fill=ink2)
            y += int(24 * u)
        # Recently landed work.
        yy = self.Hh - int(36 * u)
        for k, subj in enumerate(reversed(state.subjects[-3:])):
            fade = [ink, ink2, muted][k]
            if len(subj) > 110:
                subj = subj[:109] + "…"
            d.text((self.W - int(40 * u), yy), subj, font=self.f_small, fill=fade, anchor="rs",
                   stroke_width=int(3 * u), stroke_fill=BG)
            yy -= int(22 * u)


class State:
    """Running totals of the replayed tree."""

    def __init__(self, H: h.History):
        self.H = H
        self.tree: dict[str, str] = {}
        self.graph: dict[str, set[str]] = {}
        self.edges: list[tuple[str, str]] = []
        self.code: dict[str, int] = {}
        self.total_code = 0
        self.theorems = 0
        self.n_imports = 0
        self.subjects: list[str] = []
        self.dirty = False

    def apply(self, c: h.Commit):
        for p, b in c.changes:
            if not h.is_library(p):
                continue
            m = h.module_of(p)
            old = self.tree.get(p)
            if old:
                info = self.H.blobs[old]
                self.total_code -= info.code
                self.theorems -= info.decls.get("theorem", 0) + info.decls.get("lemma", 0)
            if b is None:
                self.tree.pop(p, None)
                self.code.pop(m, None)
            else:
                self.tree[p] = b
                info = self.H.blobs[b]
                self.code[m] = info.code
                self.total_code += info.code
                self.theorems += info.decls.get("theorem", 0) + info.decls.get("lemma", 0)
        self.subjects.append(c.subject)
        self.dirty = True

    def refresh(self):
        if self.dirty:
            self.graph = h.import_graph(self.H.blobs, self.tree)
            self.edges = _layout_edges(self.graph)
            self.n_imports = sum(len(v) for v in self.graph.values())
            self.dirty = False


def video(H: h.History, out: Path, seconds: float = 48, fps: int = 30, width: int = 1920,
          height: int = 1080, hold: float = 4):
    """How did the import graph grow, day by day?"""
    if not shutil.which("ffmpeg") or not shutil.which("sfdp"):
        raise SystemExit("evolution video needs ffmpeg and Graphviz sfdp on PATH")
    out.mkdir(parents=True, exist_ok=True)
    R = Renderer(H, width, height)
    st = State(H)
    t0, t1 = H.commits[0].time, H.commits[-1].time
    n = int(seconds * fps)
    per_frame = (t1 - t0) / max(1, n - 1)
    glow_span = per_frame * fps * 0.5  # a change glows for half a second of video
    path = out / "evolution.mp4"
    ff = subprocess.Popen(
        ["ffmpeg", "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgb24",
         "-s", f"{width}x{height}", "-r", str(fps), "-i", "-", "-c:v", "libx264",
         "-preset", "slow", "-crf", "26", "-pix_fmt", "yuv420p", "-movflags", "+faststart",
         str(path)], stdin=subprocess.PIPE)
    assert ff.stdin
    ci = 0
    touched: dict[str, float] = {}
    img = None
    for f in range(n):
        t = t0 + f * per_frame
        while ci < len(H.commits) and H.commits[ci].time <= t:
            c = H.commits[ci]
            st.apply(c)
            lib = [p for p, _ in c.changes if h.is_library(p)]
            if len(lib) <= SWEEP:  # sweeping renames and refactors would light up everything
                for p in lib:
                    touched[h.module_of(p)] = c.time
            ci += 1
        st.refresh()
        recent = {m: (t - tt) / glow_span for m, tt in touched.items() if t - tt < glow_span}
        img = R.draw(t, st, smooth=1 if f == 0 else 0.06, recent=recent)
        ff.stdin.write(img.tobytes())
    while ci < len(H.commits):
        st.apply(H.commits[ci])
        ci += 1
    st.refresh()
    for f in range(int(hold * fps)):
        img = R.draw(t1, st, smooth=0.06, recent={})
        ff.stdin.write(img.tobytes())
    ff.stdin.close()
    if ff.wait():
        raise SystemExit("ffmpeg failed")
    poster = out / "evolution.png"
    img.save(poster)
    return [path, poster]


def poster(H: h.History, out: Path, width: int = 3840, height: int = 2160):
    """The whole import graph today."""
    if not shutil.which("sfdp"):
        raise SystemExit("import-graph poster needs Graphviz sfdp on PATH")
    out.mkdir(parents=True, exist_ok=True)
    R = Renderer(H, width, height)
    st = State(H)
    for c in H.commits:
        st.apply(c)
    st.refresh()
    img = R.draw(H.commits[-1].time, st, smooth=1, recent={})
    path = out / "import-graph.png"
    img.save(path, optimize=True)
    return [path]
