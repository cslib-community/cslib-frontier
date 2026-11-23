// Module explorer: find any library module and see everything known about it.
"use strict";
(() => {
  const { data, meta, int, human, esc, key, when } = V;
  V.header("Modules");
  const M = data.modules, F = {};
  M.fields.forEach((f, i) => { F[f] = i; });
  const rows = M.rows, N = rows.length;
  const byName = new Map(rows.map((r, i) => [r[F.name], i]));
  const importers = rows.map(() => []);
  M.imports.forEach((deps, i) => deps.forEach((d) => importers[d].push(i)));
  const sorted = {};
  ["code", "reach", "commits", "theorems", "depth", "importers"].forEach((f) => {
    sorted[f] = rows.map((r) => r[F[f]]).sort((a, b) => a - b);
  });
  const resultsTitle = new Map((data.results || []).map((r) => [r[0], r[1]]));

  const cols = [
    ["name", "Module", false], ["code", "Code", true], ["theorems", "Theorems", true],
    ["reach", "Rebuilds", true], ["commits", "Commits", true],
  ];
  const state = { q: "", areas: new Set(), sort: "reach", desc: true, sel: null };

  // ---- controls --------------------------------------------------------------------------
  const q = document.getElementById("q"), sortSel = document.getElementById("sort");
  const chips = document.getElementById("areas");
  meta.areas.forEach((a) => {
    const b = document.createElement("button");
    b.className = "chip"; b.setAttribute("aria-pressed", "false");
    b.innerHTML = key(a) + esc(a);
    b.onclick = () => {
      state.areas.has(a) ? state.areas.delete(a) : state.areas.add(a);
      b.setAttribute("aria-pressed", state.areas.has(a));
      render();
    };
    b.dataset.area = a;
    chips.appendChild(b);
  });
  const sortOptions = [["reach", "Most rebuilt by a change"], ["code", "Largest"], ["commits", "Most changed"],
    ["theorems", "Most theorems"], ["depth", "Deepest in the import graph"], ["importers", "Most direct importers"],
    ["last", "Most recently changed"], ["first", "Newest"], ["unused", "Most unused definitions"], ["name", "Name"]];
  sortSel.innerHTML = sortOptions.map(([v, l]) => `<option value="${v}">${l}</option>`).join("");
  q.oninput = () => { state.q = q.value.trim().toLowerCase(); render(); };
  sortSel.onchange = () => { state.sort = sortSel.value; state.desc = state.sort !== "name"; render(); };

  // ---- list -------------------------------------------------------------------------------
  const listEl = document.getElementById("list"), countEl = document.getElementById("count");
  function value(r, f) {
    if (f === "unused") return r[F.unused].length;
    return r[F[f]];
  }
  function matches(r) {
    if (state.areas.size && !state.areas.has(r[F.area])) return false;
    if (!state.q) return true;
    const name = r[F.name].toLowerCase();
    return state.q.split(/\s+/).every((t) => name.includes(t));
  }
  function render() {
    let idx = [];
    for (let i = 0; i < N; i++) if (matches(rows[i])) idx.push(i);
    const f = state.sort, dir = state.desc ? -1 : 1;
    idx.sort((a, b) => {
      const va = value(rows[a], f), vb = value(rows[b], f);
      return (va < vb ? -1 : va > vb ? 1 : 0) * dir || (rows[a][F.name] < rows[b][F.name] ? -1 : 1);
    });
    countEl.textContent = `${int(idx.length)} of ${int(N)} modules${idx.length > 300 ? " · showing the first 300" : ""}`;
    const head = `<thead><tr>${cols.map(([c, l, r]) => `<th class="sortable${r ? " r" : ""}" data-col="${c}" aria-sort="${state.sort === c ? (state.desc ? "descending" : "ascending") : "none"}">${l}${state.sort === c ? (state.desc ? " ↓" : " ↑") : ""}</th>`).join("")}</tr></thead>`;
    const body = idx.slice(0, 300).map((i) => {
      const r = rows[i];
      return `<tr data-i="${i}" aria-selected="${state.sel === i}"><td class="modname">${key(r[F.area])}${esc(r[F.name]).replace(/\./g, ".<wbr>")}</td>` +
        `<td class="r">${human(r[F.code])}</td><td class="r">${int(r[F.theorems])}</td>` +
        `<td class="r">${int(r[F.reach])}</td><td class="r">${int(r[F.commits])}</td></tr>`;
    }).join("");
    listEl.innerHTML = `<table>${head}<tbody>${body}</tbody></table>`;
    listEl.querySelectorAll("th.sortable").forEach((th) => {
      th.onclick = () => {
        const c = th.dataset.col;
        if (state.sort === c) state.desc = !state.desc; else { state.sort = c; state.desc = c !== "name"; }
        sortSel.value = sortOptions.some(([v]) => v === c) ? c : sortSel.value;
        render();
      };
    });
    listEl.querySelectorAll("tbody tr").forEach((tr) => { tr.onclick = () => select(+tr.dataset.i); });
    V.setHash({ m: state.sel != null ? rows[state.sel][F.name] : "", q: state.q,
      area: [...state.areas].join(","), sort: state.sort === "reach" ? "" : state.sort });
  }

  // ---- detail ------------------------------------------------------------------------------
  const detail = document.getElementById("detail");
  const pct = (f, v) => Math.round(100 * V.percentile(sorted[f], v));
  function names(list, limit = 60) {
    if (!list.length) return `<p class="empty">None.</p>`;
    const items = list.slice(0, limit).map((i) =>
      `<a href="#m=${encodeURIComponent(rows[i][F.name])}" data-i="${i}">${esc(rows[i][F.name])}</a>`).join("");
    return `<div class="namelist">${items}${list.length > limit ? `<span class="muted">and ${int(list.length - limit)} more</span>` : ""}</div>`;
  }
  function select(i) {
    state.sel = i;
    const r = rows[i], m = r[F.name];
    const imps = M.imports[i].slice().sort((a, b) => rows[b][F.reach] - rows[a][F.reach]);
    const imrs = importers[i].slice().sort((a, b) => rows[b][F.reach] - rows[a][F.reach]);
    const stat = (v, l, p) => `<div class="stat"><div class="v">${v}</div><div class="l">${l}</div>${p ? `<div class="p">${p}</div>` : ""}</div>`;
    const declared = r[F.results_declared];
    detail.innerHTML =
      `<div class="tag">${key(r[F.area])}${esc(r[F.subarea])}</div><h2 style="margin:4px 0 2px" class="name">${esc(m)}</h2>` +
      `<div class="links"><a href="${V.apiModule(m)}">API documentation</a><a href="${V.source(V.modPath(m) + ".lean")}">Source</a>` +
      (r[F.last_pr] ? `<a href="${V.pr(r[F.last_pr])}">Last change: #${r[F.last_pr]}</a>` : "") + `</div>` +
      `<div class="stats">` +
      stat(human(r[F.code]), "lines of code", `${int(r[F.lines])} lines in all · larger than ${pct("code", r[F.code])}%`) +
      stat(int(r[F.theorems]), "theorems", `more than ${pct("theorems", r[F.theorems])}% of modules`) +
      stat(int(r[F.definitions]), "definitions", r[F.types] ? `${int(r[F.types])} types · ${int(r[F.instances])} instances` : "") +
      stat(int(r[F.reach]), "modules rebuild when it changes", `${(100 * r[F.reach] / N).toFixed(1)}% of the library`) +
      stat(int(r[F.depth]), "modules on its longest import chain", `deeper than ${pct("depth", r[F.depth])}%`) +
      stat(int(r[F.commits]), "commits have changed it", r[F.first] ? `first ${when(r[F.first])}` : "") +
      (M.lean ? stat(int(r[F.results_resting]), "registered results rest on it", "") : "") +
      `</div>` +
      (r[F.last] ? `<p class="small">Last changed ${when(r[F.last])}.</p>` : "") +
      (declared.length ? `<div class="section-title">Results it states</div><div class="namelist">${declared.map((id) => `<a href="results.html#r=${encodeURIComponent(id)}">${esc(resultsTitle.get(id) || id)}</a>`).join("")}</div>` : "") +
      (M.lean ? `<div class="section-title">Definitions nothing in the library uses (${r[F.unused].length})</div>` +
        (r[F.unused].length ? `<div class="namelist">${r[F.unused].map((n) => `<a href="${V.apiDecl(meta.libRoot + "." + m, n)}"><code>${esc(n)}</code></a>`).join("")}</div>` : `<p class="empty">None.</p>`) : "") +
      `<div class="section-title">Imports (${imps.length})</div>${names(imps)}` +
      `<div class="section-title">Imported by (${imrs.length})</div>${names(imrs)}`;
    detail.querySelectorAll("a[data-i]").forEach((a) => {
      a.onclick = (ev) => { ev.preventDefault(); select(+a.dataset.i); detail.scrollTop = 0; };
    });
    listEl.querySelectorAll("tbody tr").forEach((tr) => tr.setAttribute("aria-selected", +tr.dataset.i === i));
    V.setHash({ m, q: state.q, area: [...state.areas].join(","), sort: state.sort === "reach" ? "" : state.sort });
    if (window.innerWidth <= 900) detail.scrollIntoView({ behavior: "smooth", block: "start" });
  }

  // ---- initial state from the URL ------------------------------------------------------------
  const h = V.getHash();
  if (h.q) { q.value = h.q; state.q = h.q.toLowerCase(); }
  if (h.area) h.area.split(",").forEach((a) => {
    state.areas.add(a);
    const b = chips.querySelector(`[data-area="${CSS.escape(a)}"]`);
    if (b) b.setAttribute("aria-pressed", "true");
  });
  if (h.sort) { state.sort = h.sort; sortSel.value = h.sort; state.desc = h.sort !== "name"; }
  render();
  const start = h.m && byName.has(h.m) ? byName.get(h.m) : null;
  if (start != null) select(start);
  else detail.innerHTML = `<p class="empty">Choose a module from the list, or search for one. Links on other pages open here.</p>`;
  window.addEventListener("hashchange", () => {
    const hh = V.getHash();
    if (hh.m && byName.has(hh.m) && byName.get(hh.m) !== state.sel) select(byName.get(hh.m));
  });
})();
