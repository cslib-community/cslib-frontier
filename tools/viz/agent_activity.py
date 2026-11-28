# Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Christian Reitwiessner
"""Collect and summarize public GitHub work records that disclose agent activity."""

from __future__ import annotations

from collections import defaultdict
import datetime as dt
import itertools
import json
import re
import urllib.parse
import urllib.request

import github_prs

WINDOWS = (7, 30)
ROLES = ("worker", "coordinator")
SESSION = r"[a-z0-9][a-z0-9_-]{3,79}"
# Recognize explicit fields and the first-person claim formats used in the repository.
FIELDS = re.compile(rf"^Agent session:[ \t]*`?({SESSION})`?[ \t]*$", re.I | re.M)
ROLE = re.compile(r"^Agent role:[ \t]*(worker|coordinator)[ \t]*$", re.I | re.M)
WORKER = re.compile(
    r"^(?:Codex session `?([0-9a-f]{8,64})`? (?:claims|extends|submitted|is extending)\b|"
    r"Claimed by a Claude Code worker session \([^\n]*, session ([0-9a-f]{8,64})\))",
    re.I,
)
# These are self-signatures, distinct from references to a coordinator elsewhere in a post.
SIGNATURES = {
    "worker": re.compile(rf"^— Codex worker(?:, session)? `?({SESSION})`?(?:,|[ \t]*$)",
                         re.I | re.M),
    "coordinator": re.compile(
        rf"^— `?(coordinator-{SESSION})`? \(agent(?: coordination)?\)[ \t]*$|"
        rf"^— `?({SESSION})`?, queue coordinator\b",
        re.I | re.M),
}
SELF_IDENTIFICATION = {
    "worker": re.compile(
        rf"^Worker `?(codex-{SESSION})`? is taking\b|"
        r"^awaiting review[^\n]*\(worker session `?([0-9a-f]{8,64})`?\)",
        re.I,
    ),
    "coordinator": re.compile(
        rf"^I[’']m taking [^\n]+? as coordinator `(codex-{SESSION})`", re.I,
    ),
}
DISCLOSED_ROLE = re.compile(
    r"^\*?AI (?:assistance|disclosure): (?:written|authored) by an? (?:AI )?"
    r"(?:coding )?agent acting as (?:a )?(worker|coordinator)\b",
    re.I | re.M,
)
DISCLOSURE = re.compile(
    r"^\*?Authored by an AI agent\b|^\*?\(?Independent non-author(?:ing)? (?:agent|AI)\b",
    re.I | re.M,
)


def disclosure(body: str) -> tuple[str | None, str | None] | None:
    """Return an explicitly disclosed session and role, or no recognizable AI disclosure."""
    # Ignore quoted messages and fenced examples. A review label may name a task rather than
    # a session, and a review can come from either operational role.
    body = re.sub(r"(?s)<!--.*?(?:-->|\Z)", "", body.replace("\r\n", "\n"))
    body = re.sub(r"(?ms)^[ \t]*(`{3,}|~{3,})[^\n]*\n.*?(?:^[ \t]*\1[ \t]*$|\Z)", "", body)
    sessions = {s.lower() for s in FIELDS.findall(body)}
    roles = {r.lower() for pattern in (ROLE, DISCLOSED_ROLE) for r in pattern.findall(body)}
    for role, signature in SIGNATURES.items():
        for match in signature.finditer(body):
            sessions.add(next(s for s in match.groups() if s).lower())
            roles.add(role)
    for role, pattern in (("worker", WORKER), *SELF_IDENTIFICATION.items()):
        claim = pattern.match(body.lstrip("\n"))
        if claim:
            sessions.add(next(s for s in claim.groups() if s).lower())
            roles.add(role)
    if sessions or roles or DISCLOSURE.search(body):
        return (next(iter(sessions)) if len(sessions) == 1 else None,
                next(iter(roles)) if len(roles) == 1 else None)
    return None


def _records(url, token):
    """Paginate GitHub REST collections, including cursor-based issue listings."""
    while url:
        if urllib.parse.urlsplit(url).netloc != "api.github.com" or not url.startswith("https://"):
            raise ValueError("Unexpected GitHub API pagination URL")
        request = urllib.request.Request(url, headers={
            "Authorization": f"Bearer {token}", "Accept": "application/vnd.github+json",
            "User-Agent": "cslib-frontier-viz",
        })

        def read():
            with urllib.request.urlopen(request, timeout=60) as response:
                return json.load(response), response.headers.get("Link", "")

        rows, links = github_prs.retry(read)
        yield from rows
        match = re.search(r'<([^>]+)>; rel="next"', links)
        url = match[1] if match else None


def _comments(url, since, token):
    """Advance the updated-time cursor before hitting GitHub's 30,000-record offset limit."""
    batch_size = 24_000
    while True:
        query = urllib.parse.urlencode({"since": since.isoformat(), "per_page": 100,
                                       "sort": "updated", "direction": "asc"})
        rows = itertools.islice(_records(f"{url}/comments?{query}", token), batch_size)
        count = 0
        for count, row in enumerate(rows, 1):
            yield row
        if count < batch_size:
            return
        # Keep one second of overlap to retain every record sharing the boundary timestamp.
        # The collector layers deduplication by public URL on top of this pagination.
        cursor = github_prs.parse_iso(row["updated_at"]) - dt.timedelta(seconds=1)
        if cursor <= since:
            raise RuntimeError("GitHub comment pagination could not advance its updated-time cursor")
        since = cursor


def _reviews(repo, numbers, token):
    """Fetch submitted reviews in batches, paging back through the collection when necessary."""
    owner, name = repo.split("/")
    pending = [(number, None) for number in numbers]
    while pending:
        batch, pending = pending[:50], pending[50:]
        fields = []
        for i, (number, before) in enumerate(batch):
            cursor = f", before: {json.dumps(before)}" if before else ""
            fields.append(f"""
              p{i}: pullRequest(number: {number}) {{
                reviews(last: 20{cursor}) {{
                  pageInfo {{ hasPreviousPage startCursor }}
                  nodes {{ author {{ login }} body submittedAt url }}
                }}
              }}
            """)
        query = ("query($owner: String!, $name: String!) { repository(owner: $owner, name: $name) {"
                 + "".join(fields) + "}}")
        page = github_prs.graphql(query, {"owner": owner, "name": name}, token)["repository"]
        for i, (number, _) in enumerate(batch):
            reviews = page[f"p{i}"]["reviews"]
            yield from (row for row in reviews["nodes"] if row and row["submittedAt"])
            info = reviews["pageInfo"]
            if info["hasPreviousPage"]:
                pending.append((number, info["startCursor"]))


def fetch(repo: str, token: str, prs: list[dict], now: dt.datetime) -> list[dict]:
    """Read only the range used by the dashboard. Keep no raw message text in the report."""
    if not re.fullmatch(r"[\w.-]+/[\w.-]+", repo):
        raise ValueError("Expected a GitHub repository as owner/name")
    since = now - dt.timedelta(days=max(WINDOWS))
    url = f"https://api.github.com/repos/{repo}/issues"
    query = urllib.parse.urlencode({"since": since.isoformat(), "per_page": 100})
    prs_with_reviews = [int(p["number"]) for p in prs
                        if github_prs.parse_iso(p.get("updatedAt") or p["createdAt"]) >= since
                        and p.get("reviews", {}).get("totalCount", 0)]
    records = itertools.chain(
        ((row, "created_at", "html_url", "user")
         for row in _records(f"{url}?state=all&{query}", token)),
        ((row, "created_at", "html_url", "user")
         for row in _comments(url, since, token)),
        ((row, "submittedAt", "url", "author")
         for row in _reviews(repo, prs_with_reviews, token)),
    )
    public_urls = re.compile(rf"https://github\.com/{re.escape(repo)}/(?:issues|pull)/[0-9]+"
                             r"(?:#(?:issuecomment|pullrequestreview)-[0-9]+)?", re.I)
    events = {}
    for row, date_key, url_key, user_key in records:
        when = github_prs.parse_iso(row[date_key])
        if not since <= when <= now:
            continue
        attribution = disclosure(row.get("body") or "")
        if attribution is None:
            continue
        link = row[url_key]
        if not public_urls.fullmatch(link):
            raise ValueError("Unexpected public work record URL")
        session, role = attribution
        login = (row.get(user_key) or {}).get("login")
        events[link] = {"time": int(when.timestamp()), "account": login.lower() if login else None,
                        "session": session, "role": role, "url": link}
    return list(events.values())


def _counts(events):
    sessions = {event["session"] for event in events if event["session"]}
    roles = {role: {event["session"] for event in events
                    if event["session"] and event["role"] == role} for role in ROLES}
    return {"sessions": len(sessions), **{role: len(ids) for role, ids in roles.items()},
            "both": len(roles["worker"] & roles["coordinator"]),
            "without_session": sum(event["session"] is None for event in events),
            "without_role": sum(event["role"] is None for event in events),
            "events": len(events)}


def summarize(events: list[dict], now: dt.datetime) -> dict:
    """Produce window counts and account evidence without exporting session identifiers."""
    end = int(now.timestamp())
    day = 86400
    ordered = sorted(events, key=lambda event: (event["time"], event["url"]), reverse=True)
    windows = {}
    midnight = now.replace(hour=0, minute=0, second=0, microsecond=0)
    for days in WINDOWS:
        recent = [event for event in ordered if end - day * days < event["time"] <= end]
        by_account = defaultdict(list)
        for event in recent:
            by_account[event["account"]].append(event)
        accounts = []
        for login, activity in by_account.items():
            # Prefer records supporting attribution. Keep evidence for both roles when present.
            evidence = [next((e for e in activity if e["session"] and e["role"] == role), None)
                        for role in ROLES]
            evidence = list(dict.fromkeys(e["url"] for e in evidence + activity if e))[:3]
            accounts.append({"login": login, **_counts(activity), "evidence": evidence})
        accounts.sort(key=lambda row: (-row["sessions"], -row["events"], row["login"] or ""))
        daily = []
        for offset in reversed(range(days + 1)):
            date = midnight - dt.timedelta(days=offset)
            start = int(date.timestamp())
            if start + day <= end - day * days:
                continue
            daily.append({"date": date.date().isoformat(), **_counts([
                event for event in recent if start <= event["time"] < start + day
            ])})
        windows[str(days)] = {**_counts(recent), "accounts": accounts, "daily": daily}
    return {"as_of": end, "windows": windows}
