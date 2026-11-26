// Briefing: headline numbers with trends, what changed, growth, and the chart gallery.
"use strict";
(() => {
  const { data, meta, int, human, signed, date, esc, key, sparkline } = V;
  V.header("Briefing");
  const D = data.daily, rows = D.rows, dates = D.dates, last = rows.length - 1;

  // ---- headline tiles -------------------------------------------------------------------------
  // Values are now; changes are over the same rolling 24 hours and 7 days as the digest below;
  // the trend line shows the end of each UTC day.
  const R = data.rolling;
  const tiles = [
    ["Lines of Lean", (r) => r.lean_lines, "repository, tests included", human],
    ["Library code", (r) => r.lib_code, "lines, not comments or blank", human],
    ["Library modules", (r) => r.modules, "", int],
    ["Theorems", (r) => r.theorems, data.lean ? "value from the Lean census; changes and trend from source text" : "source text", human, data.headline.theorems],
    ["Definitions", (r) => r.definitions, data.lean ? "value from the Lean census; changes and trend from source text" : "source text", human, data.headline.definitions],
    ["Longest import chain", (r) => r.chain, "modules; bounds build time", int],
  ];
  const tileRoot = document.getElementById("tiles");
  function tile(label, series, note, fmt, value, d1, d7, deltaText) {
    const el = document.createElement("div");
    el.className = "card tile";
    el.innerHTML = `<div class="label">${esc(label)}</div><div class="value">${fmt(value)}</div>` +
      `<div class="delta">${deltaText || `<b>${signed(d1, fmt)}</b> 24 h · <b>${signed(d7, fmt)}</b> 7 days`}</div>` +
      `<svg aria-hidden="true"></svg>` + (note ? `<div class="note">${esc(note)}</div>` : "");
    tileRoot.appendChild(el);
    sparkline(el.querySelector("svg"), dates, series, fmt);
  }
  tiles.forEach(([label, f, note, fmt, value]) => {
    const now = f(R["0"]);
    tile(label, rows.map(f), note, fmt, value != null ? value : now, now - f(R["1"]), now - f(R["7"]));
  });
  tile("Commits, last 24 hours", rows.map((r) => r.commits), "touching Lean files; trend per UTC day",
    int, R.commits["1"], 0, 0, `<b>${int(R.commits["7"])}</b> in 7 days`);
  Object.entries(data.audit_daily).forEach(([book, series]) => {
    const now = series[last];
    tile(`${book === "arora-barak" ? "Arora–Barak" : "Goldreich"} results covered`, series,
      `of ${data.audit_totals[book]} audited`, int, now,
      now - data.audit_at[`${book}@1`], now - data.audit_at[`${book}@7`]);
  });
  if (data.headline.unused_imports != null) {
    const el = document.createElement("div");
    el.className = "card tile";
    el.innerHTML = `<div class="label">Unused imports</div><div class="value">${int(data.headline.unused_imports)}</div>` +
      `<div class="delta">of ${int(data.headline.imports)} imports</div>` +
      `<div class="note">by what declarations mention (Lean census)</div>`;
    tileRoot.appendChild(el);
  }

  // ---- what changed -------------------------------------------------------------------------
  const digest = document.getElementById("digest");
  const lede = document.getElementById("lede");
  const modLink = (m) => `<a href="modules.html#m=${encodeURIComponent(m.replace(/^CslibFrontier\./, ""))}">${esc(m.replace(/^CslibFrontier\./, ""))}</a>`;
  function list(items, render, empty = "Nothing in this window.") {
    return items.length ? `<ol>${items.map(render).join("")}</ol>` : `<p class="empty">${empty}</p>`;
  }
  function prLine(p) {
    const label = p.pr ? `<a href="${V.pr(p.pr)}">#${p.pr}</a> ` : "";
    const subj = esc(p.subject.replace(/\s*\(#\d+\)\s*$/, ""));
    return `<li><span class="grow" title="${subj}">${label}${subj}</span><span class="right">${signed(p.code, human)}</span></li>`;
  }
  function renderChanges(days) {
    const c = data.changes[days];
    const span = days === "1" ? "the last 24 hours" : "the last 7 days";
    const areas = Object.entries(c.area_code).sort((a, b) => b[1] - a[1]);
    const lead = areas.length ? areas[0][0] : null;
    lede.innerHTML = `In ${span}, <b>${int(c.commits)}</b> commits reached <code>main</code>: ` +
      `<b>${signed(c.code, human)}</b> lines of library code, <b>${signed(c.theorems, int)}</b> theorems ` +
      `(source text), <b>${int(c.added_count)}</b> new modules and <b>${int(c.removed_count)}</b> removed` +
      (lead ? `. Most growth was in <b>${esc(lead)}</b>.` : ".");
    const maxArea = Math.max(1, ...areas.map(([, v]) => Math.abs(v)));
    let html = "";
    html += `<div class="card"><h3>Largest changes <span class="small">lines of code</span></h3>${list(c.largest, prLine)}</div>`;
    html += `<div class="card"><h3>New modules <span class="small">${int(c.added_count)}</span></h3>` +
      list(c.added.slice(0, 12), ([m, n]) => `<li><span class="grow">${modLink(m)}</span><span class="right">${human(n)}</span></li>`) + `</div>`;
    html += `<div class="card"><h3>Growth by area</h3><ol>` + areas.map(([a, v]) =>
      `<li><span class="grow">${key(a)}${esc(a)}</span><span style="flex:1.2;display:flex;align-items:center"><span style="display:block;height:8px;border-radius:2px;width:${(100 * Math.abs(v) / maxArea).toFixed(1)}%;background:${V.areaColor(a)};opacity:${v < 0 ? 0.45 : 1}"></span></span><span class="right">${signed(v, human)}</span></li>`).join("") + `</ol></div>`;
    html += `<div class="card"><h3>Grew the most</h3>` +
      list(c.grown, ([m, n]) => `<li><span class="grow">${modLink(m)}</span><span class="right">${signed(n, human)}</span></li>`) + `</div>`;
    const cc = data.census_changes;
    if (cc) {
      let inner = `<p class="small">Since the census of ${esc(cc.since)}: <b>${signed(cc.theorems)}</b> theorems, <b>${signed(cc.definitions)}</b> definitions.</p>`;
      if (cc.results_added) inner += `<div class="section-title">New registered results</div>` +
        list(cc.results_added, ([id, t]) => `<li><span class="grow"><a href="results.html#r=${encodeURIComponent(id)}">${esc(t)}</a></span></li>`, "None.");
      if (cc.audit) inner += `<div class="section-title">Audit rows that changed</div>` +
        list(cc.audit, ([book, id, from, to]) => `<li><span class="grow">${esc(book)} ${esc(id)}</span><span class="right">${esc(from || "new")} → ${esc(to)}</span></li>`, "None.");
      html += `<div class="card"><h3>Lean census, night over night</h3>${inner}</div>`;
    } else {
      html += `<div class="card"><h3>Lean census, night over night</h3><p class="empty">The census compares two nightly runs; this appears once the series has a second night.</p></div>`;
    }
    html += `<div class="card"><h3>Most recent</h3>${list(c.recent.slice(0, 10), prLine)}</div>`;
    digest.innerHTML = html;
  }
  const seg = document.getElementById("window");
  seg.querySelectorAll("button").forEach((b) => {
    b.onclick = () => {
      seg.querySelectorAll("button").forEach((x) => x.setAttribute("aria-pressed", x === b));
      renderChanges(b.dataset.days);
    };
  });
  renderChanges("1");

  // ---- growth -------------------------------------------------------------------------------
  V.stackedArea(document.getElementById("growth"), dates, meta.areas, rows.map((r) => r.area_code),
    { label: "Library code by area over time", height: 340 });
  const tbl = document.getElementById("growth-table");
  document.getElementById("growth-toggle").onclick = (ev) => {
    const open = tbl.hidden;
    tbl.hidden = !open;
    ev.target.textContent = open ? "Hide table" : "Show as table";
    if (open && !tbl.innerHTML) {
      tbl.innerHTML = `<table><thead><tr><th>Date</th>${meta.areas.map((a) => `<th class="r">${esc(a)}</th>`).join("")}<th class="r">Total</th></tr></thead><tbody>` +
        rows.map((r, i) => `<tr><td>${date(dates[i])}</td>${r.area_code.map((v) => `<td class="r">${int(v)}</td>`).join("")}<td class="r">${int(r.area_code.reduce((s, v) => s + v, 0))}</td></tr>`).join("") +
        `</tbody></table>`;
    }
  };

  // ---- chart gallery ------------------------------------------------------------------------
  const gal = document.getElementById("gallery");
  let html = "";
  data.sections.forEach((sec) => {
    const charts = data.charts.filter((c) => c.section === sec);
    if (!charts.length) return;
    html += `<h3 style="margin:22px 0 10px">${esc(sec)}</h3><div class="gallery">`;
    charts.forEach((c) => {
      const f = c.files;
      let media;
      if (f.mp4) {
        media = `<video controls loop muted playsinline preload="metadata"${f.png ? ` poster="${esc(f.png)}"` : ""}><source src="${esc(f.mp4)}" type="video/mp4"></video>`;
      } else {
        media = `<a href="${esc(f.png)}"><picture>${f.dark ? `<source srcset="${esc(f.dark)}" media="(prefers-color-scheme: dark)">` : ""}<img src="${esc(f.png)}" alt="${esc(c.title)}: ${esc(c.question)}" loading="lazy" data-light="${esc(f.png)}" data-dark="${esc(f.dark || f.png)}"></picture></a>`;
      }
      const files = Object.entries(f).filter(([k]) => k !== "dark").map(([k, v]) => `<a href="${esc(v)}">${k.toUpperCase()}</a>`).join("");
      html += `<figure id="${esc(c.name)}" class="${c.wide ? "wide" : ""}">${media}<figcaption><b>${esc(c.title)}</b>` +
        `<div class="q">${esc(c.question)}</div><div class="how">${esc(c.reading)}</div><div class="files">${files}</div></figcaption></figure>`;
    });
    html += `</div>`;
  });
  gal.innerHTML = html;
  // Respect an explicit theme choice, which <picture> media queries cannot see.
  function syncImages() {
    const t = document.documentElement.dataset.theme;
    gal.querySelectorAll("img[data-dark]").forEach((img) => {
      const src = t === "dark" ? img.dataset.dark : t === "light" ? img.dataset.light : null;
      const source = img.parentElement.querySelector("source");
      if (src) { if (source) source.media = "not all"; img.src = src; }
      else if (source) source.media = "(prefers-color-scheme: dark)";
    });
  }
  document.addEventListener("themechange", syncImages);
  syncImages();
  if (location.hash === "#charts") document.getElementById("charts").scrollIntoView();
})();
