# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""Pull request metadata from the GitHub GraphQL API, read-only.

`fetch` pages through every pull request of the repository (oldest first) with the token in
`GITHUB_TOKEN` or `GH_TOKEN`; the workflow's own token with `pull-requests: read` suffices.
`update` starts from a previous list (the `prs.json` the last nightly run published) and fetches
only the pull requests updated since, newest first, which takes a page or two instead of the
whole history. A transient failure is retried; a persistent one raises, so a build never
publishes PR views made from a partial list.
"""

from __future__ import annotations

import datetime as dt
import http.client
import json
import os
import sys
import time
import urllib.error
import urllib.request

_FIELDS = """number title state createdAt updatedAt mergedAt closedAt author { login }"""
QUERY = """query($owner: String!, $name: String!, $after: String) {
  repository(owner: $owner, name: $name) {
    pullRequests(first: 50, after: $after, orderBy: {field: CREATED_AT, direction: ASC}) {
      pageInfo { hasNextPage endCursor }
      nodes { FIELDS
        additions deletions changedFiles
        reviews { totalCount } commits { totalCount } } } } }"""
RECENT = QUERY.replace("CREATED_AT, direction: ASC", "UPDATED_AT, direction: DESC")
QUERY = QUERY.replace("FIELDS", _FIELDS)
RECENT = RECENT.replace("FIELDS", _FIELDS)
OVERLAP_MINUTES = 30


def _parse_iso(stamp: str) -> dt.datetime:
    parsed = dt.datetime.fromisoformat(stamp.replace("Z", "+00:00"))
    return parsed if parsed.tzinfo else parsed.replace(tzinfo=dt.timezone.utc)


def token() -> str | None:
    return os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")


def _post(body: dict, tok: str) -> dict:
    req = urllib.request.Request(
        "https://api.github.com/graphql", data=json.dumps(body).encode(),
        headers={"Authorization": f"bearer {tok}", "Content-Type": "application/json",
                 "User-Agent": "cslib-frontier-viz"})
    with urllib.request.urlopen(req, timeout=60) as r:
        return json.load(r)


def _pages(query: str, repo: str, tok: str):
    owner, name = repo.split("/")
    after = None
    while True:
        variables = {"owner": owner, "name": name, "after": after}
        prs = None
        for attempt in range(6):
            try:
                page = _post({"query": query, "variables": variables}, tok)
                if "errors" in page:
                    raise RuntimeError(str(page["errors"])[:300])
                prs = ((page.get("data") or {}).get("repository") or {}).get("pullRequests")
                if not isinstance(prs, dict):
                    raise RuntimeError("GitHub GraphQL returned no pullRequests payload")
                break
            except (urllib.error.URLError, http.client.HTTPException, OSError,
                    ValueError, RuntimeError, TimeoutError) as e:
                if attempt == 5:
                    raise
                print(f"github: retrying after {e}", file=sys.stderr, flush=True)
                time.sleep(5 * (attempt + 1))
        assert isinstance(prs, dict)
        yield prs["nodes"]
        if not prs["pageInfo"]["hasNextPage"]:
            return
        after = prs["pageInfo"]["endCursor"]


def fetch(repo: str = "cslib-community/cslib-frontier", tok: str | None = None) -> list[dict]:
    """Every pull request, oldest first."""
    tok = tok or token()
    if not tok:
        raise RuntimeError("no GITHUB_TOKEN or GH_TOKEN")
    return [pr for nodes in _pages(QUERY, repo, tok) for pr in nodes]


def update(previous: list[dict], repo: str = "cslib-community/cslib-frontier",
           tok: str | None = None) -> list[dict]:
    """`previous` brought up to date: pull requests updated since slightly before its newest
    `updatedAt` (an overlap window avoids missing updates made mid-fetch) are fetched newest first,
    stopping at the first older one, and replace or join the old list. A previous list without
    `updatedAt` stamps is replaced by a full fetch."""
    tok = tok or token()
    if not tok:
        raise RuntimeError("no GITHUB_TOKEN or GH_TOKEN")
    stamps = [p.get("updatedAt") for p in previous]
    if not previous or not all(stamps):
        return fetch(repo, tok)
    since = max(_parse_iso(s) for s in stamps) - dt.timedelta(minutes=OVERLAP_MINUTES)
    by_number = {p["number"]: p for p in previous}
    for nodes in _pages(RECENT, repo, tok):
        fresh = [p for p in nodes if _parse_iso(p["updatedAt"]) >= since]
        for p in fresh:
            by_number[p["number"]] = p
        if len(fresh) < len(nodes):
            break
    return sorted(by_number.values(), key=lambda p: (p["createdAt"], p["number"]))


def load_previous(source: str) -> list[dict]:
    """The previously published list, or `[]` when there is none yet (HTTP 404 or no file).
    Any other failure raises rather than silently refetching everything."""
    if source.startswith(("http://", "https://")):
        try:
            req = urllib.request.Request(source, headers={"User-Agent": "cslib-frontier-viz"})
            with urllib.request.urlopen(req, timeout=60) as r:
                return json.load(r)
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return []
            raise
    from pathlib import Path
    p = Path(source)
    return json.loads(p.read_text()) if p.exists() else []
