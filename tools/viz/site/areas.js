// Areas: one card per top-level area, each on its own scale; values are printed beside the trend.
"use strict";
(() => {
  const { data, meta, int, human, esc, key, signed } = V;
  V.header("Areas");
  const M = data.modules, F = {};
  M.fields.forEach((f, i) => { F[f] = i; });
  const dates = data.daily.dates, rows = data.daily.rows, last = rows.length - 1;
  const results = data.results.results;
  const week = data.changes["7"];
  const root = document.getElementById("areas");
  const total = rows[last].area_code.reduce((s, v) => s + v, 0);

  meta.areas.forEach((a, k) => {
    const mods = M.rows.filter((r) => r[F.area] === a);
    if (!mods.length) return;
    const series = rows.map((r) => r.area_code[k]);
    const sum = (f) => mods.reduce((s, r) => s + r[F[f]], 0);
    const unused = mods.reduce((s, r) => s + r[F.unused].length, 0);
    const names = new Set(mods.map((r) => r[F.name]));
    const resultsHere = results.filter((r) => names.has(r.module));
    const top = (f, n = 5) => mods.slice().sort((x, y) => y[F[f]] - x[F[f]]).slice(0, n);
    const link = (r) => `<a href="modules.html#m=${encodeURIComponent(r[F.name])}">${esc(r[F.name].replace(/^[^.]+\./, ""))}</a>`;
    const el = document.createElement("section");
    el.className = "card";
    el.innerHTML =
      `<h2 style="margin:0 0 2px;display:flex;align-items:center">${key(a)}${esc(a)}</h2>` +
      `<div class="small">${(100 * series[last] / total).toFixed(1)}% of library code · ${signed(week.area_code[a] || 0, human)} lines in 7 days</div>` +
      `<div class="tiles" style="grid-template-columns:minmax(0,1fr)"><div class="tile" style="padding:6px 0 0"><div class="value">${human(series[last])}</div><div class="label">lines of code</div><svg aria-hidden="true"></svg></div></div>` +
      `<div class="stats" style="grid-template-columns:repeat(3,minmax(0,1fr))">` +
      `<div class="stat"><div class="v">${int(mods.length)}</div><div class="l">modules</div></div>` +
      `<div class="stat"><div class="v">${human(sum("theorems"))}</div><div class="l">theorems</div></div>` +
      `<div class="stat"><div class="v">${human(sum("definitions"))}</div><div class="l">definitions</div></div>` +
      `<div class="stat"><div class="v">${int(resultsHere.length)}</div><div class="l">registered results stated here</div></div>` +
      (M.lean ? `<div class="stat"><div class="v">${int(unused)}</div><div class="l">unused definitions</div></div>` : "") +
      `<div class="stat"><div class="v">${int(Math.max(...mods.map((r) => r[F.depth])))}</div><div class="l">deepest import chain</div></div></div>` +
      `<div class="section-title">Most rebuilt by a change</div><div class="namelist" style="flex-direction:column">${top("reach").map((r) => `<span>${link(r)} <span class="muted">${int(r[F.reach])}</span></span>`).join("")}</div>` +
      `<div class="section-title">Most changed</div><div class="namelist" style="flex-direction:column">${top("commits").map((r) => `<span>${link(r)} <span class="muted">${int(r[F.commits])} commits</span></span>`).join("")}</div>` +
      `<p class="small" style="margin:12px 0 0"><a href="modules.html#area=${encodeURIComponent(a)}">Explore all ${int(mods.length)} modules →</a></p>`;
    root.appendChild(el);
    V.sparkline(el.querySelector("svg"), dates, series, int);
  });
})();
