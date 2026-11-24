# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""An atlas of the library: the import graph drawn as a map of sub-area territories.

Each library module keeps its place in a nested sub-area layout (`nested_layout`). Every point of
the picture belongs to the sub-area (`<Area>/<Sub>`) of its nearest module, up to a coastline
distance, so sub-areas become territories: a Voronoi diagram of the modules, coloured by sub-area.
Territories take their area's palette colour in a few lightness steps, with borders between
neighbours; areas are labelled like countries and sub-areas like regions. In the video, imports
that a commit adds between two sub-areas fly as comets from the importing territory to the
imported one.
"""

from __future__ import annotations

import colorsys
import hashlib
import json
import math
import subprocess
from collections import Counter
from pathlib import Path

import numpy as np
from PIL import Image, ImageDraw
from scipy.spatial import cKDTree

import evolution as ev
import history as h
import style as s

GRID = 2  # territory raster step in pixels at 1080p
ATLAS_LAYOUT_VERSION = 1


def nested_layout(H: h.History, seed: int = 7) -> dict[str, tuple[float, float]]:
    """Positions for every library module that ever existed, nested by area and sub-area, cached.

    Within each area, sub-areas are laid out as discs weighted by inter-sub-area imports and pushed
    apart; the areas are then packed as discs weighted by cross-area imports, and each sub-area's
    modules are laid out by their own imports and folders inside its disc. Territories come out
    contiguous."""
    if not H.commits:
        return {}
    cache = None
    if hasattr(H.blobs, "fingerprint"):
        key = f"{ATLAS_LAYOUT_VERSION}:{seed}:{H.blobs.fingerprint}:{H.commits[-1].sha}"
        fp = hashlib.sha256(key.encode()).hexdigest()[:16]
        cache = h.HERE / ".cache" / f"atlas-layout-{fp}.json"
        if cache.exists():
            return {m: tuple(p) for m, p in json.loads(cache.read_text()).items()}
    import networkx as nx

    latest: dict[str, str] = {}
    for c in H.commits:
        for p, b in c.changes:
            if b and h.is_library(p):
                latest[p] = b
    graph = h.import_graph(H.blobs, latest)
    if not graph:
        return {}
    sub = {m: _sub_of(m) for m in graph}
    members: dict[str, list[str]] = {}
    for m, sb in sub.items():
        members.setdefault(sb, []).append(m)
    w = Counter()
    for m, deps in graph.items():
        for d in deps:
            if d != ev.INIT and m != ev.INIT and sub[m] != sub[d]:
                w[tuple(sorted((sub[m], sub[d])))] += 1
    area = {sb: h.area_of("CslibFrontier/" + sb + "/x.lean") for sb in members}

    def pack(names, weight, radius, seed):
        """Discs for `names`, arranged by a weighted spring layout and then pushed apart and
        drawn together until they touch without overlapping. Returns centres about the origin
        and the radius of the whole pack."""
        if len(names) == 1:
            return {names[0]: np.zeros(2)}, radius[names[0]]
        G = nx.Graph()
        G.add_nodes_from(names)
        for (a, b), x in weight.items():
            if a in G and b in G:
                G.add_edge(a, b, weight=math.log1p(x))
        pos = nx.spring_layout(G, weight="weight", seed=seed, iterations=200)
        total = sum(radius[n] for n in names)
        c = {n: np.array(pos[n], dtype=float) * total for n in names}
        for it in range(600):
            mean = np.mean([c[n] for n in names], axis=0)
            for n in names:  # compaction
                c[n] += (mean - c[n]) * 0.03
            for i, a in enumerate(names):
                for b in names[i + 1:]:
                    d = c[b] - c[a]
                    dist = float(np.hypot(*d)) or 1e-6
                    need = radius[a] + radius[b] + 0.35
                    if dist < need:
                        push = (need - dist) / 2 * d / dist
                        c[a] -= push
                        c[b] += push
        mean = np.mean([c[n] for n in names], axis=0)
        c = {n: v - mean for n, v in c.items()}
        return c, max(float(np.hypot(*c[n])) + radius[n] for n in names)

    # Provinces inside each country, then countries on the map.
    sub_r = {sb: math.sqrt(len(ms)) for sb, ms in members.items()}
    areas = sorted(set(area.values()))
    local: dict[str, np.ndarray] = {}
    area_r: dict[str, float] = {}
    for k, a in enumerate(areas):
        subs = sorted(sb for sb in members if area[sb] == a)
        cs, r = pack(subs, w, sub_r, seed + k)
        local.update(cs)
        area_r[a] = r + 0.8
    aw = Counter()
    for (x, y), n in w.items():
        if area[x] != area[y]:
            aw[tuple(sorted((area[x], area[y])))] += n
    ac, _ = pack(areas, aw, area_r, seed)
    centers = {sb: ac[area[sb]] + local[sb] for sb in members}
    radius = sub_r
    out: dict[str, tuple[float, float]] = {}
    for sb, ms in members.items():
        ms = sorted(ms)
        if len(ms) <= 3:
            local = {m: (math.cos(2 * math.pi * k / len(ms)) * 0.4,
                         math.sin(2 * math.pi * k / len(ms)) * 0.4) for k, m in enumerate(ms)}
        else:
            inner = {m: {d for d in graph[m] if d in sub and sub[d] == sb} for m in ms}
            edges = ev._layout_edges(inner)
            dirs: set[str] = set()
            for m in ms:  # tie modules to their folders inside the sub-area
                parts = m.split(".")
                child = m
                for k in range(len(parts) - 1, 2, -1):
                    dn = "dir:" + ".".join(parts[:k])
                    edges.append((child, dn))
                    if dn in dirs:
                        break
                    dirs.add(dn)
                    child = dn
            raw = ev._sfdp(ms + sorted(dirs), edges, {})
            pts = np.array([raw[m] for m in ms])
            pts -= pts.mean(axis=0)
            scale = np.percentile(np.hypot(pts[:, 0], pts[:, 1]), 96) or 1.0
            pts = pts / scale * 0.92
            # Fold stragglers back inside the disc.
            rr = np.hypot(pts[:, 0], pts[:, 1])
            far = rr > 1
            pts[far] = pts[far] / rr[far, None] * (0.9 + 0.1 * np.tanh(rr[far, None] - 1))
            local = {m: tuple(p) for m, p in zip(ms, pts)}
        c, r = centers[sb], radius[sb]
        for m, (x, y) in local.items():
            out[m] = (float(c[0] + x * r), float(c[1] + y * r))
    if cache is not None:
        cache.parent.mkdir(parents=True, exist_ok=True)
        for old in cache.parent.glob("atlas-layout-*.json"):
            old.unlink()
        cache.write_text(json.dumps(out))
    return out


def _mix(rgb, other, t):
    return tuple(int(a * (1 - t) + b * t) for a, b in zip(rgb, other))


def _shade(rgb, dl):
    r, g, b = (c / 255 for c in rgb)
    hh, ll, ss = colorsys.rgb_to_hls(r, g, b)
    r, g, b = colorsys.hls_to_rgb(hh, max(0.0, min(1.0, ll + dl)), ss)
    return int(r * 255), int(g * 255), int(b * 255)


def _sub_of(module: str) -> str:
    return h.subarea_of(module.replace(".", "/") + ".lean")


class Atlas(ev.Renderer):
    def __init__(self, H: h.History, width: int, height: int):
        super().__init__(H, width, height, pos=nested_layout(H))
        self.sub_names = sorted({_sub_of(m) for m in self.mods})
        self.sub_idx = {n: i for i, n in enumerate(self.sub_names)}
        self.sub = np.array([self.sub_idx[_sub_of(m)] for m in self.mods])
        self.sub_area = [s.ALL_AREAS.index(h.area_of("CslibFrontier/" + n + "/x.lean"))
                         for n in self.sub_names]
        # Within each area, sub-areas (largest first) take alternating lightness steps.
        size = Counter(_sub_of(m) for m in self.mods)
        steps = [0.0, 0.10, -0.08, 0.18, -0.14, 0.05, -0.03, 0.14, -0.11, 0.22]
        self.fill = np.zeros((len(self.sub_names) + 1, 3), dtype=np.uint8)
        self.border = np.zeros((len(self.sub_names) + 1, 3), dtype=np.uint8)
        by_area: dict[str, list[str]] = {}
        for n in sorted(self.sub_names, key=lambda n: -size[n]):
            by_area.setdefault(h.area_of("CslibFrontier/" + n + "/x.lean"), []).append(n)
        for a, names in by_area.items():
            base = ev.AREA_RGB[a]
            for k, n in enumerate(names):
                col = _shade(base, steps[k % len(steps)])
                self.fill[self.sub_idx[n]] = _mix(col, ev.BG, 0.72)
                self.border[self.sub_idx[n]] = _mix(col, (255, 255, 255), 0.15)
        self.fill[-1] = ev.BG
        self.border[-1] = ev.BG
        u = self.u
        self.f_country = ev._font(int(34 * u), bold=True)
        self.f_region = [ev._font(int(px * u), bold=True) for px in (11, 13, 15, 18)]

    def draw(self, t, state, smooth=0.08, recent=None, caption=True, comets=None):
        P = self.positions(t)
        vis = np.array([self.mid[m] for m in state.graph if m in self.mid], dtype=int)
        cx, cy, span = self.camera(P[vis], smooth)
        ox, oy = self.W * 0.56, self.Hh * 0.53

        def screen(idx):
            q = P[idx]
            return np.stack([(q[:, 0] - cx) / span + ox, oy - (q[:, 1] - cy) / span], axis=1)

        W, Hh, u = self.W, self.Hh, self.u
        if not len(vis):
            img = Image.new("RGB", (W, Hh), ev.BG)
            if caption:
                self.overlay(ImageDraw.Draw(img, "RGBA"), t, state)
            return img
        sp = screen(vis)
        n_vis = len(vis)
        # Territories: nearest visible module within a coastline radius, on a coarse raster.
        g = max(2, int(round(GRID * u)))
        gw, gh = W // g + 1, Hh // g + 1
        gx, gy = np.meshgrid(np.arange(gw) * g + g / 2, np.arange(gh) * g + g / 2)
        tree = cKDTree(sp)
        reach = max(14.0, min(48.0, 1400 / math.sqrt(n_vis))) * u
        dist, near = tree.query(np.stack([gx.ravel(), gy.ravel()], 1), distance_upper_bound=reach)
        lab = np.full(gw * gh, len(self.sub_names), dtype=np.int32)
        hit = near < n_vis
        lab[hit] = self.sub[vis[near[hit]]]
        lab = lab.reshape(gh, gw)
        rgb = self.fill[lab]
        # Borders where a neighbouring raster cell belongs to another territory (or the sea).
        edge = np.zeros_like(lab, dtype=bool)
        edge[:, 1:] |= lab[:, 1:] != lab[:, :-1]
        edge[1:, :] |= lab[1:, :] != lab[:-1, :]
        owner = np.where(lab == len(self.sub_names), np.roll(lab, 1, axis=1), lab)
        owner = np.where(owner == len(self.sub_names), np.roll(lab, 1, axis=0), owner)
        rgb[edge] = self.border[owner[edge]]
        img = Image.fromarray(rgb, "RGB").resize((gw * g, gh * g), Image.NEAREST).crop((0, 0, W, Hh))
        d = ImageDraw.Draw(img, "RGBA")
        # Imports: faint within a province; between provinces, one route per pair of provinces,
        # wider for more imports.
        if state.edges:
            ea = np.array([self.mid[a] for a, _ in state.edges])
            eb = np.array([self.mid[b] for _, b in state.edges])
            same = self.sub[ea] == self.sub[eb]
            sa, sb_ = screen(ea[same]), screen(eb[same])
            for (x0, y0), (x1, y1) in zip(sa, sb_):
                d.line((x0, y0, x1, y1), fill=(235, 235, 230, 16), width=1)
            pair = Counter(zip(np.minimum(self.sub[ea[~same]], self.sub[eb[~same]]),
                               np.maximum(self.sub[ea[~same]], self.sub[eb[~same]])))
            centre = {}
            for si in set(self.sub[vis]):
                centre[si] = sp[self.sub[vis] == si].mean(axis=0)
            top = pair.most_common(90)
            if top:
                hi = math.log1p(top[0][1])
                for (a, b), n in top:
                    if a not in centre or b not in centre:
                        continue
                    curve = self._curve(centre[a], centre[b])
                    f = math.log1p(n) / hi
                    d.line([tuple(q) for q in curve], fill=(240, 238, 230, int(8 + 26 * f)),
                           width=max(1, int((0.6 + 2.4 * f) * u)), joint="curve")
        self._centre = {si: sp[self.sub[vis] == si].mean(axis=0) for si in set(self.sub[vis])}
        self.countries(img, sp, vis)
        d = ImageDraw.Draw(img, "RGBA")
        base = max(1.0, min(3.6, 75 / math.sqrt(n_vis))) * u
        for (x, y), i in zip(sp, vis):
            m = self.mods[i]
            size = state.code.get(m, 0)
            r = base * (0.55 + 0.45 * math.sqrt(min(size, 2500) / 200))
            col = ev.AREA_RGB[s.ALL_AREAS[self.area[i]]]
            age = recent.get(m) if recent else None
            if age is not None:
                glow = 1 - age
                rr = r + (2 + 6 * glow) * u
                d.ellipse((x - rr, y - rr, x + rr, y + rr), fill=(*ev._lift(col, 0.3), int(30 + 80 * glow)))
                col = ev._lift(col, 0.25 * glow + 0.05)
            d.ellipse((x - r, y - r, x + r, y + r), fill=col)
        self.draw_comets(img, comets or [])
        d = ImageDraw.Draw(img, "RGBA")
        self.labels(d, sp, vis)
        if caption:
            self.overlay(d, t, state)
        return img

    @staticmethod
    def _curve(p0, p1, n=28):
        """The route from p0 to p1: a quadratic arc that bends the same way in either direction."""
        a, b = (p0, p1) if (p0[0], p0[1]) <= (p1[0], p1[1]) else (p1, p0)
        ctrl = (a + b) / 2 + np.array([-(b - a)[1], (b - a)[0]]) * 0.18
        ts = np.linspace(0, 1, n)[:, None]
        c = (1 - ts) ** 2 * p0 + 2 * (1 - ts) * ts * ctrl + ts ** 2 * p1
        return c

    def draw_comets(self, img, comets):
        """New imports between provinces in flight: (importer sub, imported sub, progress 0..1,
        strength 0..1). A bright head runs along the route toward the imported province with a
        fading tail, on an additive-looking glow layer."""
        if not comets:
            return
        layer = Image.new("RGBA", img.size, (0, 0, 0, 0))
        d = ImageDraw.Draw(layer)
        u = self.u
        for a, b, prog, strength in comets:
            if a not in self._centre or b not in self._centre:
                continue
            curve = self._curve(self._centre[a], self._centre[b], 64)
            col = ev._lift(ev.AREA_RGB[s.ALL_AREAS[self.sub_area[a]]], 0.35)
            head = prog * (len(curve) - 1)
            tail = 14
            for k in range(tail):
                j = head - k * 0.9
                if j < 0:
                    break
                i0 = int(j)
                frac = j - i0
                q = curve[i0] * (1 - frac) + curve[min(i0 + 1, len(curve) - 1)] * frac
                fade = (1 - k / tail) ** 1.6
                rad = (1.2 + 3.2 * strength) * u * (0.35 + 0.65 * fade)
                alpha = int(255 * fade * (0.45 + 0.55 * strength))
                c = col if k else (255, 255, 250)
                d.ellipse((q[0] - rad, q[1] - rad, q[0] + rad, q[1] + rad), fill=(*c, alpha))
            if prog > 0.97:  # arrival flash at the imported province
                q = curve[-1]
                rr = (6 + 10 * strength) * u
                d.ellipse((q[0] - rr, q[1] - rr, q[0] + rr, q[1] + rr), fill=(*col, 60))
        img.paste(layer, (0, 0), layer)

    def _core(self, pts):
        # The densest cell, so the label sits on the territory rather than between parts.
        cell = 36 * self.u
        k, c = np.unique(np.floor(pts / cell).astype(int), axis=0, return_counts=True)
        return (k[np.argmax(c)] + 0.5) * cell

    def countries(self, img, sp, vis):
        """Area names, letter-spaced and faint, just above each country. Drawn on their own
        layer: Pillow ignores a text colour's alpha when drawing on an RGB image."""
        layer = Image.new("RGBA", img.size, (0, 0, 0, 0))
        d = ImageDraw.Draw(layer)
        placed = []
        sized = sorted(((int((self.area[vis] == ai).sum()), ai, a) for ai, a in enumerate(s.ALL_AREAS)),
                       reverse=True)
        for n, ai, a in sized:
            sel = sp[self.area[vis] == ai]
            if n < 40 or a == h.OTHER:
                continue
            text = " ".join(a.upper())
            x = float(np.median(sel[:, 0]))
            for y in (float(np.percentile(sel[:, 1], 2)) - 26 * self.u,
                      float(np.percentile(sel[:, 1], 98)) + 26 * self.u):
                b = d.textbbox((x, y), text, font=self.f_country, anchor="mm")
                if all(b[2] < q[0] or b[0] > q[2] or b[3] < q[1] or b[1] > q[3] for q in placed):
                    placed.append(b)
                    d.text((x, y), text, font=self.f_country, anchor="mm", fill=(250, 249, 245, 92))
                    break
        img.paste(layer, (0, 0), layer)

    def labels(self, d, sp, vis):
        """Regions (sub-areas) sized by module count. A label is dropped when it would overlap
        one already placed, largest first."""
        u = self.u
        placed: list[tuple[float, float, float, float]] = []

        def fits(box):
            x0, y0, x1, y1 = box
            if x0 < 300 * u or x1 > self.W - 10 or y0 < 10 or y1 > self.Hh - 90 * u:
                return False
            return all(x1 < a0 or x0 > a1 or y1 < b0 or y0 > b1 for a0, b0, a1, b1 in placed)

        regions = Counter(self.sub[vis])
        for si, n in regions.most_common():
            if n < 12:
                break
            name = self.sub_names[si]
            text = name.split("/", 1)[-1]
            sel = sp[self.sub[vis] == si]
            x, y = self._core(sel)
            f = self.f_region[min(3, int(math.log2(max(n, 12) / 12) / 1.3))]
            box = d.textbbox((x, y), text, font=f, anchor="mm")
            box = (box[0] - 4, box[1] - 2, box[2] + 4, box[3] + 2)
            if not fits(box):
                continue
            placed.append(box)
            d.text((x, y), text, font=f, anchor="mm", fill=(245, 244, 240),
                   stroke_width=max(2, int(2.5 * u)), stroke_fill=ev.BG)


def video(H: h.History, out: Path, seconds: float = 60, fps: int = 30, width: int = 1920,
          height: int = 1080, hold: float = 5, name: str = "atlas"):
    """The atlas growing over the library's lifetime."""
    out.mkdir(parents=True, exist_ok=True)
    R = Atlas(H, width, height)
    st = ev.State(H)
    t0, t1 = H.commits[0].time, H.commits[-1].time
    n = int(seconds * fps)
    per_frame = (t1 - t0) / max(1, n - 1)
    glow_span = per_frame * fps * 0.5
    path = out / f"{name}.mp4"
    ff = subprocess.Popen(
        ["ffmpeg", "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgb24",
         "-s", f"{width}x{height}", "-r", str(fps), "-i", "-", "-c:v", "libx264",
         "-preset", "slow", "-crf", "23", "-pix_fmt", "yuv420p", "-movflags", "+faststart",
         str(path)], stdin=subprocess.PIPE)
    ci = 0
    touched: dict[str, float] = {}
    img = None
    prev_edges: set = set()
    flying: list[list] = []  # [importer sub, imported sub, start frame, strength]
    travel = int(fps * 1.3)
    for f in range(n):
        t = t0 + f * per_frame
        sweep = False
        while ci < len(H.commits) and H.commits[ci].time <= t:
            c = H.commits[ci]
            st.apply(c)
            lib = [p for p, _ in c.changes if h.is_library(p)]
            if len(lib) <= ev.SWEEP:
                for p in lib:
                    touched[h.module_of(p)] = c.time
            else:
                sweep = True
            ci += 1
        st.refresh()
        edges = set(st.edges)
        if prev_edges and not sweep:
            fresh = Counter()
            for a, b in edges - prev_edges:
                if a in R.mid and b in R.mid:
                    sa, sb = int(R.sub[R.mid[a]]), int(R.sub[R.mid[b]])
                    if sa != sb:
                        fresh[(sa, sb)] += 1
            for (sa, sb), k in fresh.most_common(24):
                strength = min(1.0, math.log1p(k) / math.log(20))
                for j in range(min(3, 1 + k // 4)):  # a few staggered comets for big batches
                    flying.append([sa, sb, f + 3 * j, strength])
        prev_edges = edges
        live = [c for c in flying if 0 <= f - c[2] <= travel]
        flying = [c for c in flying if f - c[2] <= travel]
        comets = [(a, b, (f - start) / travel, sg) for a, b, start, sg in live]
        recent = {m: (t - tt) / glow_span for m, tt in touched.items() if t - tt < glow_span}
        img = R.draw(t, st, smooth=1 if f == 0 else 0.06, recent=recent, comets=comets)
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
    img.save(out / f"{name}.png")
    return [path, out / f"{name}.png"]


def poster(H: h.History, out: Path, width: int = 3840, height: int = 2160):
    R = Atlas(H, width, height)
    st = ev.State(H)
    for c in H.commits:
        st.apply(c)
    st.refresh()
    img = R.draw(H.commits[-1].time, st, smooth=1, recent={})
    p = out / "atlas-poster.png"
    img.save(p, optimize=True)
    return [p]
