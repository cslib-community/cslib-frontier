// Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Authors: Christian Reitwiessner
"use strict";

(() => {
  const { activity } = V.data;
  const { esc, int, sparkline, when } = V;
  V.header("Agent activity");
  const tiles = document.getElementById("tiles");
  const table = document.getElementById("accounts");
  const coverage = document.getElementById("coverage");
  const buttons = [...document.querySelectorAll("#window button")];

  document.getElementById("as-of").textContent = "As of " + when(activity.as_of);

  const tilesToShow = [
    ["sessions", "Active sessions", "var(--s1)"],
    ["worker", "Worker sessions", "var(--s2)"],
    ["coordinator", "Coordinator sessions", "var(--s3)"],
    ["without_session", "Records without a session", "var(--other)"],
  ];

  function render(days) {
    const summary = activity.windows[days];
    const daily = activity.daily.slice(-Number(days));
    const dates = daily.map((row) => row.date);
    const maxRole = Math.max(1, ...summary.accounts.map((row) => Math.max(row.worker, row.coordinator)));

    tiles.innerHTML = tilesToShow.map(([key, label]) =>
      `<div class="card tile"><div class="label">${label}</div>
        <div class="value">${int(summary[key])}</div><svg aria-hidden="true"></svg>
        <div class="note">Daily counts in UTC</div></div>`).join("");
    tiles.querySelectorAll("svg").forEach((svg, i) => {
      const [key, , color] = tilesToShow[i];
      sparkline(svg, dates, daily.map((row) => row[key]));
      svg.querySelector("polyline").setAttribute("stroke", color);
    });
    coverage.textContent = `${int(summary.events)} disclosed records · ${int(summary.without_role)} ` +
      `without a role · ${int(summary.both)} sessions observed in both roles`;

    function roleCell(value, color) {
      return `<td class="r"><span class="agent-role" style="--role-color:${color};--role-width:${100 * value / maxRole}%">
        ${int(value)}</span></td>`;
    }

    table.innerHTML = summary.accounts.map((row) => {
      const account = row.login
        ? `<a href="https://github.com/${encodeURIComponent(row.login)}">@${esc(row.login)}</a>`
        : "Unknown account";
      const evidence = row.evidence.filter((url) => url.startsWith("https://github.com/")).map((url, i) => {
        const number = new URL(url).pathname.split("/").pop();
        return `<a href="${esc(url)}" aria-label="Record ${i + 1} for ${esc(row.login || "unknown account")}, #${esc(number)}">#${esc(number)}</a>`;
      }).join(" · ");
      return `<tr><th scope="row" class="name">${account}${row.sessions > 1 ?
        '<span class="small agent-shared">Multiple sessions</span>' : ""}
        </th><td class="r">${int(row.sessions)}</td>
        ${roleCell(row.worker, "var(--s2)")}${roleCell(row.coordinator, "var(--s3)")}
        <td class="r">${int(row.events)}</td><td>${evidence}</td></tr>`;
    }).join("");
    document.getElementById("empty").hidden = summary.accounts.length > 0;
    buttons.forEach((button) => button.setAttribute("aria-pressed", button.dataset.days === days));
  }

  function selected() {
    const day = V.getHash().days;
    return Object.hasOwn(activity.windows, day) ? day : "7";
  }

  buttons.forEach((button) => button.onclick = () => { location.hash = "days=" + button.dataset.days; });
  window.addEventListener("hashchange", () => render(selected()));
  render(selected());
})();
