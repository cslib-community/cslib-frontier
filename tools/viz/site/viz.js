// Codebase views: shared helpers. No dependencies; every page embeds its data as JSON.
"use strict";

const V = (() => {
  const data = JSON.parse(document.getElementById("data").textContent);
  const meta = data.meta;

  // ---- formatting ----------------------------------------------------------------------
  function human(v) {
    const a = Math.abs(v);
    const trim = (s) => (s.includes(".") ? s.replace(/0+$/, "").replace(/\.$/, "") : s);
    if (a >= 1e6) return trim((v / 1e6).toFixed(2)) + "M";
    if (a >= 1e4) return (v / 1e3).toFixed(0) + "K";
    if (a >= 1e3) return trim((v / 1e3).toFixed(1)) + "K";
    return String(Math.round(v));
  }
  const int = (v) => Math.round(v).toLocaleString("en-US");
  // Round tick steps (1, 2, 2.5, 5 × 10^k) and a max that is a multiple of the step.
  function niceTicks(max, count = 4) {
    const raw = Math.max(max, 1) / count, p = Math.pow(10, Math.floor(Math.log10(raw)));
    const step = [1, 2, 2.5, 5, 10].map((m) => m * p).find((s) => s >= raw);
    return { step, max: Math.ceil(max / step) * step };
  }
  const signed = (v, f = int) => (v > 0 ? "+" : v < 0 ? "−" : "±") + f(Math.abs(v));
  const date = (iso) => new Date(iso + "T00:00:00Z").toLocaleDateString("en-US",
    { month: "short", day: "numeric", timeZone: "UTC" });
  const when = (t) => new Date(t * 1000).toLocaleString("en-US",
    { month: "short", day: "numeric", hour: "2-digit", minute: "2-digit", timeZone: "UTC" }) + " UTC";
  const esc = (s) => String(s).replace(/[&<>"']/g, (c) =>
    ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));

  // ---- colours: CSS tokens, so they follow the theme -----------------------------------
  const areaVar = {};
  meta.areas.forEach((a, i) => { areaVar[a] = i < 7 ? `var(--s${i + 1})` : "var(--other)"; });
  const areaColor = (a) => areaVar[a] || "var(--other)";
  const key = (a) => `<span class="key" style="background:${areaColor(a)}"></span>`;

  // ---- links ---------------------------------------------------------------------------
  const modPath = (m) => "CslibFrontier/" + m.replace(/\./g, "/");
  const apiModule = (m) => `${meta.apiRoot}${modPath(m)}.html`;
  const apiDecl = (module, name) =>
    `${meta.apiRoot}${module.replace(/\./g, "/")}.html#${encodeURIComponent(name)}`;
  const source = (path, line) => `${meta.repoUrl}/blob/${meta.sha}/${path}${line ? "#L" + line : ""}`;
  const pr = (n) => `${meta.repoUrl}/pull/${n}`;

  // ---- tooltip ---------------------------------------------------------------------------
  const tip = document.createElement("div");
  tip.className = "tip";
  tip.setAttribute("role", "status");
  document.body.appendChild(tip);
  function showTip(html, x, y) {
    tip.innerHTML = html;
    tip.style.display = "block";
    const w = tip.offsetWidth, h = tip.offsetHeight;
    let left = x + 14, top = y + 14;
    if (left + w > window.innerWidth - 8) left = x - w - 14;
    if (top + h > window.innerHeight - 8) top = y - h - 14;
    tip.style.left = Math.max(8, left) + "px";
    tip.style.top = Math.max(8, top) + "px";
  }
  const hideTip = () => { tip.style.display = "none"; };

  // ---- sparkline -------------------------------------------------------------------------
  // A single-series trend with a hover readout; the value stays readable without hovering.
  function sparkline(el, dates, values, fmt = int) {
    const W = 200, H = 34, n = values.length;
    if (n < 2) { el.innerHTML = ""; return; }
    const lo = Math.min(...values), hi = Math.max(...values);
    const x = (i) => (i / (n - 1)) * W;
    const y = (v) => H - 2 - ((v - lo) / (hi - lo || 1)) * (H - 4);
    const pts = values.map((v, i) => `${x(i).toFixed(1)},${y(v).toFixed(1)}`).join(" ");
    el.setAttribute("viewBox", `0 0 ${W} ${H}`);
    el.setAttribute("preserveAspectRatio", "none");
    el.innerHTML =
      `<polyline points="${pts}" fill="none" stroke="var(--s1)" stroke-width="2" vector-effect="non-scaling-stroke" stroke-linejoin="round"/>` +
      `<line class="hair" y1="0" y2="${H}" stroke="var(--axis)" vector-effect="non-scaling-stroke" visibility="hidden"/>`;
    const hair = el.querySelector(".hair");
    el.addEventListener("mousemove", (ev) => {
      const r = el.getBoundingClientRect();
      const i = Math.max(0, Math.min(n - 1, Math.round(((ev.clientX - r.left) / r.width) * (n - 1))));
      hair.setAttribute("x1", x(i)); hair.setAttribute("x2", x(i));
      hair.setAttribute("visibility", "visible");
      showTip(`<div class="t">${date(dates[i])}</div>${fmt(values[i])}`, ev.clientX, ev.clientY);
    });
    el.addEventListener("mouseleave", () => { hair.setAttribute("visibility", "hidden"); hideTip(); });
  }

  // ---- stacked area chart ----------------------------------------------------------------
  // Areas stacked over time with a crosshair tooltip listing every visible series, legend
  // toggles that keep each area's colour, and an optional table view.
  function stackedArea(root, dates, names, rows, opts = {}) {
    const on = names.map(() => true);
    const wrap = document.createElement("div");
    wrap.className = "chart-wrap";
    const legend = document.createElement("div");
    legend.className = "legend";
    root.append(wrap, legend);
    names.forEach((nm, k) => {
      const b = document.createElement("button");
      b.setAttribute("aria-pressed", "true");
      b.innerHTML = key(nm) + esc(nm);
      b.onclick = () => { on[k] = !on[k]; b.setAttribute("aria-pressed", on[k]); draw(); };
      legend.appendChild(b);
    });
    function draw() {
      const W = Math.max(320, wrap.clientWidth), H = opts.height || 320;
      const m = { l: 52, r: 12, t: 10, b: 26 };
      const iw = W - m.l - m.r, ih = H - m.t - m.b, n = dates.length;
      const tot = rows.map((r) => r.reduce((s, v, k) => s + (on[k] ? v : 0), 0));
      const nt = niceTicks(Math.max(1, ...tot) * 1.02), max = nt.max;
      const x = (i) => m.l + (n === 1 ? iw / 2 : (i / (n - 1)) * iw);
      const y = (v) => m.t + ih - (v / max) * ih;
      let svg = `<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="${esc(opts.label || "")}">`;
      for (let v = 0; v <= max + 1e-9; v += nt.step) {
        svg += `<line x1="${m.l}" x2="${W - m.r}" y1="${y(v)}" y2="${y(v)}" stroke="var(--line)"/>` +
          `<text x="${m.l - 8}" y="${y(v) + 4}" text-anchor="end" font-size="11" fill="var(--ink2)">${human(v)}</text>`;
      }
      const step = Math.max(1, Math.ceil(n / Math.max(2, Math.floor(iw / 80))));
      for (let i = 0; i < n; i += step) {
        svg += `<text x="${x(i)}" y="${H - 6}" text-anchor="middle" font-size="11" fill="var(--ink2)">${date(dates[i])}</text>`;
      }
      const base = new Array(n).fill(0);
      names.forEach((nm, k) => {
        if (!on[k]) return;
        const top = base.map((b, i) => b + rows[i][k]);
        const d = top.map((v, i) => `${i ? "L" : "M"}${x(i).toFixed(1)},${y(v).toFixed(1)}`).join("") +
          base.map((v, i) => [i, v]).reverse().map(([i, v]) => `L${x(i).toFixed(1)},${y(v).toFixed(1)}`).join("") + "Z";
        svg += `<path d="${d}" fill="${areaColor(nm)}" stroke="var(--surface)" stroke-width="1"/>`;
        top.forEach((v, i) => { base[i] = v; });
      });
      svg += `<line class="hair" y1="${m.t}" y2="${m.t + ih}" stroke="var(--ink2)" visibility="hidden"/>`;
      svg += `<rect class="hit" x="${m.l}" y="${m.t}" width="${iw}" height="${ih}" fill="transparent"/></svg>`;
      wrap.innerHTML = svg;
      const s = wrap.querySelector("svg"), hair = s.querySelector(".hair");
      s.addEventListener("mousemove", (ev) => {
        const r = s.getBoundingClientRect();
        const px = ((ev.clientX - r.left) / r.width) * W;
        const i = Math.max(0, Math.min(n - 1, Math.round(((px - m.l) / iw) * (n - 1))));
        hair.setAttribute("x1", x(i)); hair.setAttribute("x2", x(i)); hair.setAttribute("visibility", "visible");
        let html = `<div class="t">${date(dates[i])}</div>`;
        names.map((nm, k) => [nm, k]).filter(([, k]) => on[k]).reverse().forEach(([nm, k]) => {
          html += `<div class="row"><span>${key(nm)}${esc(nm)}</span><span>${int(rows[i][k])}</span></div>`;
        });
        html += `<div class="row"><span><b>Total</b></span><span><b>${int(tot[i])}</b></span></div>`;
        showTip(html, ev.clientX, ev.clientY);
      });
      s.addEventListener("mouseleave", () => { hair.setAttribute("visibility", "hidden"); hideTip(); });
    }
    draw();
    let t;
    window.addEventListener("resize", () => { clearTimeout(t); t = setTimeout(draw, 100); });
    return draw;
  }

  // ---- stacked horizontal meter ------------------------------------------------------------
  function meter(parts, total) {
    // parts: [[label, value, colour]]; segments separated by a 2px surface gap.
    const sum = total || parts.reduce((s, p) => s + p[1], 0) || 1;
    return `<div class="meter">` + parts.filter((p) => p[1] > 0).map((p) =>
      `<span style="width:${(100 * p[1] / sum).toFixed(2)}%;background:${p[2]}" data-tip="${esc(p[0])}: ${int(p[1])}"></span>`).join("") + `</div>`;
  }
  document.addEventListener("mousemove", (ev) => {
    const t = ev.target.closest && ev.target.closest("[data-tip]");
    if (t) showTip(esc(t.dataset.tip), ev.clientX, ev.clientY);
    else if (!ev.target.closest || !ev.target.closest("svg")) hideTip();
  });

  // ---- header: navigation and theme toggle ---------------------------------------------------
  function header(active) {
    const pages = [["index.html", "Briefing"], ["modules.html", "Modules"], ["results.html", "Results"],
      ["textbooks.html", "Textbooks"], ["areas.html", "Areas"], ["prs.html", "Pull requests"],
      ["agents.html", "Agent activity"], ["index.html#charts", "Charts"]];
    const h = document.createElement("header");
    h.className = "top";
    h.innerHTML = `<div class="bar"><a class="brand" href="index.html">cslib-frontier · views</a><nav>` +
      pages.filter(([href]) => (href !== "prs.html" || meta.prs) && (href !== "agents.html" || meta.agents)).map(([href, label]) => `<a href="${href}"${label === active ? ' aria-current="page"' : ""}>${label}</a>`).join("") +
      `</nav><button class="theme-toggle" type="button" aria-label="Switch light or dark theme">◐ Theme</button></div>`;
    document.body.prepend(h);
    const btn = h.querySelector(".theme-toggle");
    let saved = null;
    try { saved = localStorage.getItem("viz-theme"); } catch (e) { /* storage may be blocked */ }
    if (saved) document.documentElement.dataset.theme = saved;
    btn.onclick = () => {
      const dark = getComputedStyle(document.documentElement).colorScheme.includes("dark");
      const next = dark ? "light" : "dark";
      document.documentElement.dataset.theme = next;
      try { localStorage.setItem("viz-theme", next); } catch (e) { /* ignore */ }
      document.dispatchEvent(new Event("themechange"));
    };
    const f = document.createElement("footer");
    f.className = "page";
    f.innerHTML = `Built from <a href="${meta.repoUrl}/commit/${meta.sha}"><code>${meta.sha.slice(0, 12)}</code></a> ` +
      `(${when(meta.time)}) by <code>tools/viz/build.py</code>. ${meta.lean ? "Declaration counts come from the Lean census of the built library." : "No library build was available, so declaration counts come from source text."}`;
    document.body.appendChild(f);
  }

  // ---- hash state -----------------------------------------------------------------------------
  function getHash() {
    const out = {};
    location.hash.slice(1).split("&").filter(Boolean).forEach((kv) => {
      const i = kv.indexOf("=");
      const k = i < 0 ? kv : kv.slice(0, i), v = i < 0 ? "" : kv.slice(i + 1);
      try {
        out[decodeURIComponent(k)] = decodeURIComponent(v);
      } catch (e) { /* ignore malformed percent-encoding */ }
    });
    return out;
  }
  function setHash(obj) {
    const s = Object.entries(obj).filter(([, v]) => v !== "" && v != null)
      .map(([k, v]) => `${encodeURIComponent(k)}=${encodeURIComponent(v)}`).join("&");
    history.replaceState(null, "", s ? "#" + s : location.pathname + location.search);
  }

  function percentile(sorted, v) {
    // Share of values strictly below v.
    let lo = 0, hi = sorted.length;
    while (lo < hi) { const mid = (lo + hi) >> 1; if (sorted[mid] < v) lo = mid + 1; else hi = mid; }
    return sorted.length ? lo / sorted.length : 0;
  }

  return { data, meta, human, int, niceTicks, signed, date, when, esc, areaColor, key, apiModule, apiDecl,
    source, pr, modPath, showTip, hideTip, sparkline, stackedArea, meter, header, getHash,
    setHash, percentile };
})();
