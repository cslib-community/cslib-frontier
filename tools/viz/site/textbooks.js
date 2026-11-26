// Textbook map: the audits' dispositions by chapter, clickable down to each audited result.
"use strict";
(() => {
  const { data, int, esc } = V;
  V.header("Textbooks");
  const classes = data.textbooks.classes;
  const color = (c) => ({ "Not located": "var(--neutral)", Other: "var(--other)" }[c] ||
    `var(--s${classes.indexOf(c) + 1})`);
  const resultTitle = new Map(data.results.results.map((r) => [r.id, r.title]));
  const root = document.getElementById("books");
  const filter = {};

  data.textbooks.books.forEach((book) => {
    const rows = book.rows; // [id, chapter, title, cls, status, line, theorems, results]
    const chapters = [...new Set(rows.map((r) => r[1]))].sort((a, b) => a - b);
    const covered = rows.filter((r) => r[3].startsWith("Covered")).length;
    const sec = document.createElement("section");
    sec.className = "card";
    sec.style.marginBottom = "18px";
    sec.innerHTML = `<div style="display:flex;justify-content:space-between;gap:16px;flex-wrap:wrap;align-items:baseline">` +
      `<h2 style="margin:0">${esc(book.title)}</h2><div class="small"><b>${covered}</b> of ${rows.length} audited results covered · ` +
      `<a href="${V.source(book.path)}">the audit</a></div></div>` +
      `<div class="tiles" style="grid-template-columns:minmax(0,1fr);margin:6px 0"><div class="tile" style="padding:0"><div class="label">Covered over time</div><svg aria-hidden="true"></svg></div></div>` +
      `<div class="chart-wrap bars"></div><div class="legend"></div>` +
      `<div class="controls" style="margin-top:12px"><span class="small filt"></span></div><div class="rows"></div>`;
    root.appendChild(sec);
    V.sparkline(sec.querySelector("svg"), data.daily.dates, book.covered);
    sec.querySelector(".legend").innerHTML = classes.filter((c) => rows.some((r) => r[3] === c))
      .map((c) => `<span class="tag"><span class="key" style="background:${color(c)}"></span>${esc(c)} ${rows.filter((r) => r[3] === c).length}</span>`).join("");
    filter[book.key] = { ch: null, cls: null };

    // Columns per chapter, one segment per disposition; clicking filters the rows below.
    const W = 960, H = 220, m = { l: 34, r: 8, t: 8, b: 26 };
    const iw = W - m.l - m.r, ih = H - m.t - m.b;
    const counts = chapters.map((ch) => classes.map((c) => rows.filter((r) => r[1] === ch && r[3] === c).length));
    const nt = V.niceTicks(Math.max(...counts.map((cs) => cs.reduce((s, v) => s + v, 0))), 4);
    const max = nt.max;
    const bw = iw / chapters.length;
    let svg = `<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="Audited results by chapter and disposition">`;
    for (let v = 0; v <= max; v += nt.step) {
      const y = m.t + ih - (v / max) * ih;
      svg += `<line x1="${m.l}" x2="${W - m.r}" y1="${y}" y2="${y}" stroke="var(--line)"/><text x="${m.l - 6}" y="${y + 4}" font-size="11" text-anchor="end" fill="var(--ink2)">${v}</text>`;
    }
    chapters.forEach((ch, j) => {
      let y = m.t + ih;
      const x = m.l + j * bw + bw * 0.14, w = bw * 0.72;
      classes.forEach((c, k) => {
        const n = counts[j][k];
        if (!n) return;
        const hgt = (n / max) * ih;
        y -= hgt;
        svg += `<rect x="${x}" y="${y + 1}" width="${w}" height="${Math.max(1, hgt - 2)}" rx="2" fill="${color(c)}" data-ch="${ch}" data-cls="${esc(c)}" data-tip="Chapter ${ch} · ${esc(c)}: ${n}" style="cursor:pointer"/>`;
      });
      svg += `<text x="${x + w / 2}" y="${H - 8}" text-anchor="middle" font-size="11" fill="var(--ink2)" data-ch="${ch}" style="cursor:pointer">${ch}</text>`;
    });
    svg += `</svg>`;
    const bars = sec.querySelector(".bars");
    bars.innerHTML = svg;
    bars.querySelectorAll("[data-ch]").forEach((el) => {
      el.addEventListener("click", () => {
        const f = filter[book.key];
        const ch = +el.dataset.ch, cls = el.dataset.cls || null;
        if (f.ch === ch && f.cls === cls) { f.ch = null; f.cls = null; } else { f.ch = ch; f.cls = cls; }
        renderRows();
      });
    });

    function renderRows() {
      const f = filter[book.key];
      const shown = rows.filter((r) => (f.ch == null || r[1] === f.ch) && (f.cls == null || r[3] === f.cls));
      sec.querySelector(".filt").innerHTML = f.ch == null ? `All ${rows.length} audited results · click a bar or chapter to filter` :
        `Chapter ${f.ch}${f.cls ? ` · ${esc(f.cls)}` : ""} · ${shown.length} results · <a href="#" class="clear">show all</a>`;
      const clr = sec.querySelector(".clear");
      if (clr) clr.onclick = (ev) => { ev.preventDefault(); f.ch = null; f.cls = null; renderRows(); };
      sec.querySelector(".rows").innerHTML = `<div style="max-height:520px;overflow:auto"><table><thead><tr><th>Result</th><th>Disposition</th><th>Formalized as</th></tr></thead><tbody>` +
        shown.map(([id, ch, title, cls, status, line, thms, results]) => `<tr style="cursor:default"><td><a href="${V.source(book.path, line)}"><b>${esc(id)}</b></a> ${esc(title)}</td>` +
          `<td><span class="pill"><span class="dot" style="background:${color(cls)}"></span>${esc(status)}</span></td>` +
          `<td class="small">${results.map((rid) => `<a href="results.html#r=${encodeURIComponent(rid)}">${esc(resultTitle.get(rid) || rid)}</a>`).join("<br>")}` +
          `${results.length && thms.length ? "<br>" : ""}${thms.slice(0, 4).map((t) => `<code>${esc(t)}</code>`).join(" ")}${thms.length > 4 ? ` <span class="muted">+${thms.length - 4}</span>` : ""}</td></tr>`).join("") +
        `</tbody></table></div>`;
    }
    renderRows();
  });
})();
