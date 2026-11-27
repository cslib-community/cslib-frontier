// Result explorer: every registered result, what it states and what it rests on.
"use strict";
(() => {
  const { data, meta, int, esc, key } = V;
  V.header("Results");
  const R = data.results.results;
  const byId = new Map(R.map((r, i) => [r.id, i]));
  const topics = [...new Set(R.map((r) => r.topic).filter(Boolean))].sort();
  const books = Object.fromEntries(data.books.map((b) => [b.key, b]));
  const state = { q: "", topic: "", sort: "cone", sel: null };

  const q = document.getElementById("q"), topicSel = document.getElementById("topic"),
    sortSel = document.getElementById("sort"), listEl = document.getElementById("list"),
    countEl = document.getElementById("count"), detail = document.getElementById("detail");
  topicSel.innerHTML = `<option value="">All topics (${topics.length})</option>` +
    topics.map((t) => `<option>${esc(t)}</option>`).join("");
  sortSel.innerHTML = [["cone", "Largest dependency cone"], ["title", "Title"], ["topic", "Topic"],
    ["audit", "Cited by a textbook audit"]].map(([v, l]) => `<option value="${v}">${l}</option>`).join("");
  q.oninput = () => { state.q = q.value.trim().toLowerCase(); render(); };
  topicSel.onchange = () => { state.topic = topicSel.value; render(); };
  sortSel.onchange = () => { state.sort = sortSel.value; render(); };

  const coneSize = (r) => (r.cone ? r.cone.declarations : -1);
  const maxCone = Math.max(1, ...R.map(coneSize));
  function matches(r) {
    if (state.topic && r.topic !== state.topic) return false;
    if (!state.q) return true;
    const hay = (r.title + " " + r.id + " " + r.topic + " " + r.theorems.map((t) => t[0]).join(" ") +
      " " + r.sources.map((s) => s.join(" ")).join(" ")).toLowerCase();
    return state.q.split(/\s+/).every((t) => hay.includes(t));
  }
  function render() {
    const idx = R.map((_, i) => i).filter((i) => matches(R[i]));
    const cmp = {
      cone: (a, b) => coneSize(R[b]) - coneSize(R[a]),
      title: (a, b) => R[a].title.localeCompare(R[b].title),
      topic: (a, b) => R[a].topic.localeCompare(R[b].topic) || R[a].title.localeCompare(R[b].title),
      audit: (a, b) => R[b].audit.length - R[a].audit.length || coneSize(R[b]) - coneSize(R[a]),
    }[state.sort];
    idx.sort(cmp);
    countEl.textContent = `${int(idx.length)} of ${int(R.length)} results`;
    listEl.innerHTML = `<table><thead><tr><th>Result</th><th class="r">Cone</th></tr></thead><tbody>` +
      idx.map((i) => {
        const r = R[i];
        const bar = r.cone ? `<div style="width:110px;margin-left:auto">${V.meter(meta.areas.map((a, k) => [a, r.cone.areas[k], V.areaColor(a)]), maxCone)}</div>` : "";
        return `<tr data-i="${i}" aria-selected="${state.sel === i}"><td><div>${esc(r.title)}</div><div class="small">${esc(r.topic)}</div></td>` +
          `<td class="r">${r.cone ? int(r.cone.declarations) : "–"}${bar}</td></tr>`;
      }).join("") + `</tbody></table>`;
    listEl.querySelectorAll("tbody tr").forEach((tr) => { tr.onclick = () => select(+tr.dataset.i); });
  }

  function select(i) {
    state.sel = i;
    const r = R[i];
    let html = `<div class="tag">${esc(r.topic)}</div><h2 style="margin:4px 0 6px">${esc(r.title)}</h2>`;
    html += `<div class="links"><a href="${meta.repoUrl}/blob/${meta.sha}/CslibFrontierResults/">Registry entry: <code>${esc(r.id)}</code></a>` +
      (r.module ? `<a href="modules.html#m=${encodeURIComponent(r.module)}">Module: ${esc(r.module)}</a>` : "") + `</div>`;
    if (r.scope) html += `<p class="small" style="max-width:75ch">${esc(r.scope)}</p>`;
    if (r.sources.length) {
      html += `<div class="section-title">Sources</div><ul style="margin:0;padding-left:18px">` +
        r.sources.map(([bib, thm, loc]) => `<li class="small"><b>${esc(thm || bib)}</b>${thm ? ` · ${esc(bib)}` : ""}${loc ? ` · ${esc(loc)}` : ""}</li>`).join("") + `</ul>`;
    }
    html += `<div class="section-title">Theorems</div><div class="namelist">` +
      r.theorems.map(([n, mod]) => mod ? `<a href="${V.apiDecl(mod, n)}"><code>${esc(n)}</code></a>` : `<code>${esc(n)}</code>`).join("") + `</div>`;
    if (r.cone) {
      const c = r.cone;
      html += `<div class="section-title">What it rests on</div>` +
        `<div class="stats"><div class="stat"><div class="v">${int(c.declarations)}</div><div class="l">library declarations, directly or transitively</div></div>` +
        `<div class="stat"><div class="v">${int(c.modules)}</div><div class="l">modules</div></div>` +
        `<div class="stat"><div class="v">${c.sorry ? "⚠ sorry" : "✓ none"}</div><div class="l">${c.sorry ? "its cone contains sorryAx" : "sorryAx anywhere in its cone"}</div></div></div>` +
        V.meter(meta.areas.map((a, k) => [a, c.areas[k], V.areaColor(a)])) +
        `<div class="legend" style="margin-top:6px">${meta.areas.map((a, k) => c.areas[k] ? `<span class="tag">${key(a)}${esc(a)} ${int(c.areas[k])}</span>` : "").join("")}</div>` +
        (c.found < c.requested ? `<p class="small">⚠ ${c.requested - c.found} of its ${c.requested} theorems are not in the build.</p>` : "") +
        `<div class="section-title">Modules carrying the most of it</div><table><tbody>` +
        c.top.map(([m, n]) => `<tr><td class="name"><a href="modules.html#m=${encodeURIComponent(m)}">${esc(m)}</a></td><td class="r">${int(n)}</td></tr>`).join("") +
        `</tbody></table>`;
    } else {
      html += `<p class="empty">The dependency cone needs the Lean census of a build.</p>`;
    }
    if (r.audit.length) {
      html += `<div class="section-title">Textbook audit rows citing it</div><ul style="margin:0;padding-left:18px">` +
        r.audit.map(([book, id, cls, line]) => `<li class="small"><a href="${V.source(books[book].path, line)}">${esc(books[book].title)} ${esc(id)}</a> · ${esc(cls)}</li>`).join("") + `</ul>`;
    }
    detail.innerHTML = html;
    listEl.querySelectorAll("tbody tr").forEach((tr) => tr.setAttribute("aria-selected", +tr.dataset.i === i));
    V.setHash({ r: r.id, q: state.q, topic: state.topic });
    if (window.innerWidth <= 900) detail.scrollIntoView({ behavior: "smooth", block: "start" });
  }

  const h = V.getHash();
  if (h.q) { q.value = h.q; state.q = h.q.toLowerCase(); }
  if (h.topic) { state.topic = h.topic; topicSel.value = h.topic; }
  render();
  if (h.r && byId.has(h.r)) select(byId.get(h.r));
  else if (!data.results.registry) detail.innerHTML = `<p class="empty">The results registry was not available to this build: exporting it needs a built <code>CslibFrontierResults</code>. The nightly build has one.</p>`;
  else detail.innerHTML = `<p class="empty">Choose a result. ${data.results.lean ? "" : "Dependency cones need the Lean census of a build."}</p>`;
})();
