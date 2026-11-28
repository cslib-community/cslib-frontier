# Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Christian Reitwiessner
"""Collect and summarize public GitHub work records that identify workers."""

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
ID = r"[a-z0-9][a-z0-9_-]{3,79}"
WORKER_FIELD = re.compile(rf"^Worker ID:[ \t]*`?({ID})`?[ \t]*$", re.I | re.M)
WORKER_CLAIMS = (
    re.compile(rf"^Worker `?({ID})`? (?:is taking|is preparing|claims|has claimed)\b", re.I),
    re.compile(rf"^(?:I[’']m|I am) (?:taking|implementing|preparing) [^\n]+? as worker `({ID})`", re.I),
)
WORKER_SIGNATURE = re.compile(
    rf"^— Codex worker `?({ID})`?(?:,|[ \t]*$)", re.I | re.M,
)


# Preserve the entire worker ID: several distinct workers share the same fleet suffix.
AUTHORING_WORKER = re.compile(
    rf"^[*_-]*[ \t]*(?:\*\*)?(?:Authoring worker|Worker):(?:\*\*)?[ \t]*`({ID})`"
    rf"|^[*_]*(?:Implemented by (?:agent|AI) worker) `({ID})`"
    rf"|^[*_]*(?:Authored with AI assistance|"
    rf"(?:Implemented(?: and locally validated)? (?:by|with)|Drafted, proved, and locally validated by)"
    rf" an? [^\n()]*coding agent) \(`(worker-{ID})`(?=[ \t)]|$)"
    rf"|^Addressed [^\n]*?\((?:posted )?by `(worker-{ID})`\):",
    re.I | re.M,
)


def worker_id(body: str) -> str | None:
    """Read a public worker ID from a field, self-claim, signature, or author credit."""
    body = re.sub(r"(?s)<!--.*?(?:-->|\Z)", "", body.replace("\r\n", "\n"))
    body = re.sub(
        r"(?ms)^[ \t]*(?P<fence>(?P<mark>[`~])(?P=mark){2,})[^\n]*\n"
        r".*?(?:^[ \t]*(?P=fence)(?P=mark)*[ \t]*$|\Z)", "", body,
    )
    fields = WORKER_FIELD.findall(body)
    if fields:
        ids = {value.lower() for value in fields}
        return next(iter(ids)) if len(ids) == 1 else None
    ids = {value.lower() for value in WORKER_SIGNATURE.findall(body)}
    ids.update(value.lower() for match in AUTHORING_WORKER.findall(body) for value in match if value)
    for pattern in WORKER_CLAIMS:
        claim = pattern.match(body.lstrip("\n"))
        if claim:
            ids.add(claim[1].lower())
    return next(iter(ids)) if len(ids) == 1 else None


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
        identifier = worker_id(row.get("body") or "")
        if identifier is None:
            continue
        link = row[url_key]
        if not public_urls.fullmatch(link):
            raise ValueError("Unexpected public work record URL")
        login = (row.get(user_key) or {}).get("login")
        events[link] = {"time": int(when.timestamp()), "account": login.lower() if login else None,
                        "worker_id": identifier, "url": link}
    return list(events.values())


def _counts(events):
    return {"workers": len({event["worker_id"] for event in events}), "events": len(events)}


def summarize(events: list[dict], now: dt.datetime) -> dict:
    """Count distinct public worker IDs and link them to their public records."""
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
            latest = {}
            for event in activity:
                latest.setdefault(event["worker_id"], event["url"])
            accounts.append({"login": login, **_counts(activity),
                             "workers_by_id": [{"id": key, "url": latest[key]}
                                               for key in sorted(latest)]})
        accounts.sort(key=lambda row: (-row["workers"], -row["events"], row["login"] or ""))
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
    return {"metric": "worker_ids", "as_of": end, "windows": windows}
