# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""Pull request metadata from the GitHub GraphQL API, read-only.

`fetch` pages through every pull request of the repository (oldest first) with the token in
`GITHUB_TOKEN` or `GH_TOKEN`; the workflow's own token with `pull-requests: read` suffices. A
transient failure is retried; a persistent one raises, so a build never publishes PR views made
from a partial list.
"""

from __future__ import annotations

import json
import os
import sys
import time
import urllib.error
import urllib.request

QUERY = """query($owner: String!, $name: String!, $after: String) {
  repository(owner: $owner, name: $name) {
    pullRequests(first: 50, after: $after, orderBy: {field: CREATED_AT, direction: ASC}) {
      pageInfo { hasNextPage endCursor }
      nodes { number title state createdAt mergedAt closedAt author { login }
        additions deletions changedFiles
        reviews { totalCount } comments { totalCount } commits { totalCount } } } } }"""


def token() -> str | None:
    return os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")


def _post(body: dict, tok: str) -> dict:
    req = urllib.request.Request(
        "https://api.github.com/graphql", data=json.dumps(body).encode(),
        headers={"Authorization": f"bearer {tok}", "Content-Type": "application/json",
                 "User-Agent": "cslib-frontier-viz"})
    with urllib.request.urlopen(req, timeout=60) as r:
        return json.load(r)


def fetch(repo: str = "cslib-community/cslib-frontier", tok: str | None = None) -> list[dict]:
    """Every pull request, oldest first."""
    tok = tok or token()
    if not tok:
        raise RuntimeError("no GITHUB_TOKEN or GH_TOKEN")
    owner, name = repo.split("/")
    out: list[dict] = []
    after = None
    while True:
        variables = {"owner": owner, "name": name, "after": after}
        for attempt in range(6):
            try:
                page = _post({"query": QUERY, "variables": variables}, tok)
                if "errors" in page:
                    raise RuntimeError(str(page["errors"])[:300])
                break
            except (urllib.error.URLError, RuntimeError, TimeoutError) as e:
                if attempt == 5:
                    raise
                print(f"github: retrying after {e}", file=sys.stderr, flush=True)
                time.sleep(5 * (attempt + 1))
        prs = page["data"]["repository"]["pullRequests"]
        out += prs["nodes"]
        if not prs["pageInfo"]["hasNextPage"]:
            return out
        after = prs["pageInfo"]["endCursor"]
