// Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Authors: Christian Reitwiessner
"use strict";

(() => {
  const { activity } = V.data;
  const { esc, int, sparkline, when } = V;
  V.header("Worker activity");
  const tiles = document.getElementById("tiles");
  const table = document.getElementById("accounts");
  const buttons = [...document.querySelectorAll("#window button")];

  document.getElementById("as-of").textContent = "As of " + when(activity.as_of);

  const tilesToShow = [
    ["workers", "Active worker IDs", "var(--s1)"],
    ["events", "Records with a worker ID", "var(--s2)"],
  ];

  function render(days) {
    const summary = activity.windows[days];
    const daily = summary.daily;
    const dates = daily.map((row) => row.date);

    tiles.innerHTML = tilesToShow.map(([key, label]) =>
      `<div class="card tile"><div class="label">${label}</div>
        <div class="value">${int(summary[key])}</div><svg aria-hidden="true"></svg>
        <div class="note">Daily counts in UTC</div></div>`).join("");
    tiles.querySelectorAll("svg").forEach((svg, i) => {
      const [key, , color] = tilesToShow[i];
      sparkline(svg, dates, daily.map((row) => row[key]));
      svg.querySelector("polyline").setAttribute("stroke", color);
    });
    table.innerHTML = summary.accounts.map((row) => {
      const account = row.login
        ? `<a href="https://github.com/${encodeURIComponent(row.login)}">@${esc(row.login)}</a>`
        : "Unknown account";
      const workers = row.workers_by_id.filter(({url}) => url.startsWith("https://github.com/"))
        .map(({id, url}) => `<a class="mono" href="${esc(url)}">${esc(id)}</a>`).join(" · ");
      return `<tr><th scope="row" class="name">${account}</th>
        <td class="r">${int(row.workers)}</td><td class="r">${int(row.events)}</td>
        <td class="name">${workers}</td></tr>`;
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
