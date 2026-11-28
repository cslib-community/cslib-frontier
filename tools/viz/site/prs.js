// Pull requests: headline numbers, the galaxy of every pull request, and the PR charts.
"use strict";
(() => {
  const { data, meta, int, esc } = V;
  V.header("Pull requests");
  const F = {};
  data.prs.fields.forEach((f, i) => { F[f] = i; });
  const R = data.prs.rows.map((r) => Object.fromEntries(data.prs.fields.map((f, i) => [f, r[i]])));
  const KINDS = data.kinds;
  const now = R.reduce((m, r) => Math.max(m, r.merged || 0, r.created || 0), meta.time);
  const hours = (s) => s / 3600;
  const dur = (s) => {
    const v = Math.max(0, s);
    return v >= 86400 ? (v / 86400).toFixed(1) + " days" : v >= 3600 ? (v / 3600).toFixed(1) + " h" : Math.round(v / 60) + " min";
  };

  // ---- headline numbers ---------------------------------------------------------------------
  const merged = R.filter((r) => r.merged && r.merged <= now);
  const lat = merged.map((r) => r.merged - r.created).sort((a, b) => a - b);
  const q = (p) => (lat.length ? lat[Math.min(lat.length - 1, Math.floor(p * lat.length))] : 0);
  const open = R.filter((r) => r.state === "OPEN" || (r.merged && r.merged > now));
  const week = merged.filter((r) => r.merged > now - 7 * 86400);
  const oldest = open.slice().sort((a, b) => a.created - b.created)[0];
  const earliest = R.length ? R.reduce((m, r) => Math.min(m, r.created), R[0].created) : now;
  const tiles = [
    [int(merged.length), "merged pull requests", R.length ? `${int(R.length)} opened since ${new Date(earliest * 1000).toLocaleDateString("en-US", { month: "short", day: "numeric", timeZone: "UTC" })}` : "0 pull requests"],
    [int(week.length), "merged in the last 7 days", `${(week.length / 7).toFixed(0)} a day`],
    [lat.length ? `${hours(q(0.5)).toFixed(1)} h` : "—", "median time to merge", lat.length ? `90% within ${hours(q(0.9)).toFixed(0)} h` : ""],
    [int(open.length), "open now", oldest ? `oldest opened ${dur(now - oldest.created)} ago` : ""],
    [int(R.filter((r) => r.state === "CLOSED" && !r.merged).length), "closed without merging", ""],
  ];
  document.getElementById("tiles").innerHTML = tiles.map(([v, l, n]) =>
    `<div class="card tile"><div class="label">${esc(l)}</div><div class="value">${v}</div>${n ? `<div class="note">${esc(n)}</div>` : ""}</div>`).join("");

  // ---- galaxy ---------------------------------------------------------------------------------
  const lanes = [...meta.areas, "Tooling and docs", "Still open", "Closed unmerged"];
  const laneOf = (r) => (r.state === "OPEN" ? lanes.length - 2 : !r.merged ? lanes.length - 1 :
    r.area ? meta.areas.indexOf(r.area) : meta.areas.length);
  const on = [true, true, true];
  const css = (v) => getComputedStyle(document.documentElement).getPropertyValue(v).trim();
  const kinds = document.getElementById("kinds");
  KINDS.forEach((k, i) => {
    const b = document.createElement("button");
    b.className = "chip"; b.setAttribute("aria-pressed", "true");
    b.innerHTML = `<span class="key" style="background:var(--s${i + 1});border-radius:50%"></span>${esc(k)}`;
    b.onclick = () => { on[i] = !on[i]; b.setAttribute("aria-pressed", on[i]); draw(); };
    kinds.appendChild(b);
  });
  const authors = Object.entries(R.reduce((m, r) => ((m[r.author] = (m[r.author] || 0) + 1), m), {})).sort((a, b) => b[1] - a[1]);
  const asel = document.getElementById("author");
  asel.innerHTML = `<option value="">All authors (${authors.length})</option>` +
    authors.map(([a, n]) => `<option value="${esc(a)}">${esc(a)} (${n})</option>`).join("");
  const qEl = document.getElementById("q");
  qEl.oninput = draw; asel.onchange = draw;
  const c = document.getElementById("galaxy"), ctx = c.getContext("2d");
  const jit = (n) => { const x = Math.sin(n * 12.9898) * 43758.5453; return x - Math.floor(x); };
  const tOf = (r) => r.merged || r.created;
  const t0 = R.length ? R.reduce((m, r) => Math.min(m, r.created), R[0].created) : now - 86400;
  const t1 = Math.max(t0 + 1, R.length ? R.reduce((m, r) => Math.max(m, tOf(r)), t0) : now);
  const bySize = R.slice().sort((a, b) => (b.add + b.del) - (a.add + a.del));
  let pts = [];
  function draw() {
    const dpr = window.devicePixelRatio || 1, W = c.clientWidth;
    const H = Math.max(520, Math.min(860, window.innerHeight - 160));
    c.width = W * dpr; c.height = H * dpr; c.style.height = H + "px";
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    const dark = getComputedStyle(document.documentElement).colorScheme.includes("dark");
    const L = Math.min(150, W * 0.28), Rm = 10, T = 6, B = 26, lh = (H - T - B) / lanes.length;
    ctx.clearRect(0, 0, W, H);
    ctx.font = "12px system-ui, sans-serif"; ctx.textBaseline = "middle";
    lanes.forEach((name, i) => {
      const y = T + i * lh;
      if (i % 2) { ctx.fillStyle = css("--hover"); ctx.fillRect(L, y, W - L - Rm, lh); }
      ctx.fillStyle = css("--ink2"); ctx.textAlign = "right"; ctx.fillText(name, L - 8, y + lh / 2);
    });
    const x = (t) => L + ((t - t0) / (t1 - t0)) * (W - L - Rm);
    ctx.textAlign = "center"; ctx.fillStyle = css("--muted");
    const stepDays = W < 700 ? 6 : 2;
    for (let d = Math.ceil(t0 / 86400) * 86400; d <= t1; d += 86400 * stepDays) {
      ctx.fillText(new Date(d * 1000).toLocaleDateString("en-US", { month: "short", day: "numeric", timeZone: "UTC" }), x(d), H - 11);
      ctx.strokeStyle = css("--line"); ctx.beginPath(); ctx.moveTo(x(d), T); ctx.lineTo(x(d), H - B); ctx.stroke();
    }
    const kc = [css("--s1"), css("--s2"), css("--s3")], openC = css("--ink"), closedC = css("--neutral");
    const qs = qEl.value.trim().toLowerCase().split(/\s+/).filter(Boolean), au = asel.value;
    pts = []; let shown = 0, lines = 0;
    // Additive light reads as glow on the dark surface; on the light one, plain transparency.
    ctx.globalCompositeOperation = dark ? "lighter" : "source-over";
    for (const r of bySize) {
      const match = on[r.kind] && (!au || r.author === au) && qs.every((t) => r.title.toLowerCase().includes(t));
      const size = r.add + r.del, li = laneOf(r);
      const px = x(tOf(r)), py = T + li * lh + lh * (0.12 + 0.76 * jit(r.n));
      const rad = Math.max(1.4, Math.min(15, Math.sqrt(size) / 9));
      ctx.globalAlpha = match ? (r.merged ? (dark ? 0.55 : 0.45) : 0.85) : 0.04;
      ctx.fillStyle = r.merged ? kc[r.kind] : r.state === "OPEN" ? openC : closedC;
      ctx.beginPath(); ctx.arc(px, py, rad, 0, 7); ctx.fill();
      if (match) { pts.push([px, py, rad, r]); shown++; lines += size; }
    }
    ctx.globalAlpha = 1; ctx.globalCompositeOperation = "source-over";
    document.getElementById("stats").textContent = `${int(shown)} pull requests · ${int(lines)} lines changed`;
  }
  function nearest(ev) {
    const b = c.getBoundingClientRect(), mx = ev.clientX - b.left, my = ev.clientY - b.top;
    let best = null, bd = 1e9;
    for (const p of pts) { const d = Math.hypot(p[0] - mx, p[1] - my) - p[2]; if (d < bd) { bd = d; best = p; } }
    return bd < 8 ? best[3] : null;
  }
  c.addEventListener("mousemove", (ev) => {
    const r = nearest(ev);
    if (!r) { V.hideTip(); c.style.cursor = "default"; return; }
    c.style.cursor = "pointer";
    V.showTip(`<div class="t">#${r.n} ${esc(r.title)}</div>` +
      `<div>${esc(r.author)} · ${esc(KINDS[r.kind])}${r.sub ? " · " + esc(r.sub) : ""}</div>` +
      `<div>+${int(r.add)} −${int(r.del)} in ${int(r.files)} files · ${r.commits} commits · ${r.reviews} reviews</div>` +
      `<div>${r.merged ? "merged after " + dur(r.merged - r.created) : r.state === "OPEN" ? "open for " + dur(now - r.created) : "closed without merging"}</div>`,
    ev.clientX, ev.clientY);
  });
  c.addEventListener("mouseleave", V.hideTip);
  c.addEventListener("click", (ev) => { const r = nearest(ev); if (r) window.open(V.pr(r.n), "_blank", "noopener"); });
  document.addEventListener("themechange", draw);
  window.matchMedia("(prefers-color-scheme: dark)").addEventListener("change", draw);
  let rt; window.addEventListener("resize", () => { clearTimeout(rt); rt = setTimeout(draw, 120); });
  draw();

  // ---- charts -----------------------------------------------------------------------------------
  document.getElementById("charts").innerHTML = data.charts.map((ch) => {
    const f = ch.files;
    const files = Object.entries(f).filter(([k]) => k !== "dark").map(([k, v]) => `<a href="${esc(v)}">${k.toUpperCase()}</a>`).join("");
    return `<h2>${esc(ch.title)}</h2><p class="sub">${esc(ch.question)} ${esc(ch.reading)}</p>` +
      `<a href="${esc(f.png)}"><picture>${f.dark ? `<source srcset="${esc(f.dark)}" media="(prefers-color-scheme: dark)">` : ""}` +
      `<img src="${esc(f.png)}" alt="${esc(ch.title)}" style="width:100%;height:auto;border:1px solid var(--line);border-radius:8px" data-light="${esc(f.png)}" data-dark="${esc(f.dark || f.png)}"></picture></a>` +
      `<div class="files" style="display:flex;gap:10px;font-size:12.5px;margin-top:4px">${files}</div>`;
  }).join("");
  function syncImages() {
    const t = document.documentElement.dataset.theme;
    document.querySelectorAll("#charts img[data-dark]").forEach((img) => {
      const src = t === "dark" ? img.dataset.dark : t === "light" ? img.dataset.light : null;
      const source = img.parentElement.querySelector("source");
      if (src) { if (source) source.media = "not all"; img.src = src; }
      else if (source) source.media = "(prefers-color-scheme: dark)";
    });
  }
  document.addEventListener("themechange", syncImages);
  syncImages();
  document.getElementById("data-note").textContent =
    "Pull request data comes from the GitHub API (title, author, size, review counts, times), read with the workflow's read-only token; prs.json beside this page holds it.";
})();
