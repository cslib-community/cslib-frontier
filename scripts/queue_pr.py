#!/usr/bin/env python3
"""Add a pull request to the merge queue at exactly the approved head.

Usage: python3 scripts/queue_pr.py PR SHA [--wait MINUTES] [--hold-hubs | --allow-hub]
                                   [--reviewer ID] [--repo OWNER/NAME]

This is the queueing half of approve-and-queue (AGENTS.md, "Approve and queue"). It refuses
unless the pull request is open, not a draft, based on `main`, has head SHA, and merges cleanly
into its base, and the required check (`REQUIRED_CHECKS`) has succeeded at SHA. All pages of check
contexts are read from the same commit before selecting each required check's latest attempt.
While that check is still running it waits up to `--wait` minutes (default 0: report and stop);
it always waits briefly for GitHub to compute mergeability. Just before enqueueing, if other pull
requests are already ahead in the merge queue, it replays that queue prefix in a full local Git
repository (supporting `GIT_DIR`, including bare repositories) and refuses on a textual conflict or
when automatic replay is unavailable. When active queue entries are ahead and the PR modifies
high-fan-in `CslibFrontier/` hub modules (`>= 500` transitive importers), it compares the modules
the PR rebuilds with the union of those the entries ahead already rebuild. It refuses when more
than `HUB_PACING_DEPTH` entries are ahead and the PR adds at least 500 modules to that union, unless
`--allow-hub` is passed; `--hold-hubs` refuses whenever entries are ahead. Otherwise it prints an
advisory rebuild notice after enqueueing. It then enqueues with `expectedHeadOid` = SHA, so a push
after the approval can never be queued in its place. Every run prints the queue depth ahead of the
PR and a rough time to land.
Whenever it sleeps or replays a non-empty queue prefix, it snapshots the PR discussion beforehand
and rereads it on the mutation side just before enqueueing. A changed body, comment, submitted
review or inline thread stops the enqueue so the reviewer can reread and rerun. Check events and
reactions are not discussion changes.

On every run, just before enqueueing, it reads the PR's comments and submitted reviews for review
records, each a whole line outside fenced code blocks:
- `HOLD owner=ID until=YYYY-MM-DDTHH:MMZ reason=TEXT`, in force until `until` passes or its owner
  posts a later `HOLD-RELEASED by=ID reason=TEXT` (for `owner=maintainer`, `by=maintainer` or
  `by=SamuelSchlesinger`);
- `CLAIM review head=SHA by=ID until=YYYY-MM-DDTHH:MMZ`, a review lease of at most 45 minutes after
  it is posted, which the same reviewer's verdict at SHA ends;
- verdicts: posts whose first non-empty line begins `**APPROVE** at SHA` or
  `**REQUEST_CHANGES** at SHA`, naming the reviewer as ` by ID`.
It refuses while a hold is in force, while another reviewer's claim on the head is unexpired, or
when a `**REQUEST_CHANGES**` at the head is not followed by a later `**APPROVE**` there.
`--reviewer ID` exempts your own claim. Free-text holds cannot be parsed: comments since the
approval that say "hold" or "holding" outside a record are listed as an advisory.

It does not judge the approval itself or a free-text hold; the reviewer checks those before
running it. The discussion read is not atomic with enqueue and does not inspect linked issues. Its
retarget check (a base change
newer than the head's commit date when current `main` is not already an ancestor of the head) only
catches the common mistake of queueing a stacked PR before it merges `main`;
`scripts/check_restack.py` is what verifies a restacked head.

Exit status: 0 when the PR is queued (or already was), 1 when it is refused or the check is still
running, 2 on a `gh` error. Requires an authenticated `gh` with write access to the repository.
"""

from __future__ import annotations

import argparse
from collections.abc import Callable
import contextlib
import datetime
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from typing import NamedTuple

if __name__ == "__main__":
    sys.modules.setdefault("queue_pr", sys.modules[__name__])

ROOT = Path(__file__).resolve().parents[1]
REPO = "cslib-community/cslib-frontier"
# The checks the `main` ruleset requires (Settings → Rules → main), each with the GitHub App that
# must report it (15368 is GitHub Actions), as the ruleset pins them; keep in sync with it.
REQUIRED_CHECKS = {"ci-checks": 15368}
POLL_SECONDS = 30
# GitHub computes mergeability lazily, so the first query can return UNKNOWN; re-ask this often.
MERGEABLE_RETRIES, MERGEABLE_SECONDS = 10, 3
# Rough merge-queue timing for the printed estimate: a successful group build takes about this many
# minutes, and the ruleset builds this many groups at once (keep in sync with it).
GROUP_BUILD_MINUTES, CONCURRENT_GROUP_BUILDS = 14, 8
# A PR that adds a high-fan-in hub's rebuild cone to the queue waits while more entries than this
# are ahead (every later group build pays for that cone until the PR lands), unless `--allow-hub`.
HUB_PACING_DEPTH = 6

QUERY = """
query($owner: String!, $name: String!, $number: Int!) {
  repository(owner: $owner, name: $name) {
    mergeQueue { entries { totalCount } }
    pullRequest(number: $number) {
      id state isDraft baseRefName baseRefOid headRefOid mergeable
      mergeQueueEntry { position state }
      timelineItems(last: 1, itemTypes: [BASE_REF_CHANGED_EVENT,
                                         AUTOMATIC_BASE_CHANGE_SUCCEEDED_EVENT]) {
        nodes {
          ... on BaseRefChangedEvent { createdAt }
          ... on AutomaticBaseChangeSucceededEvent { createdAt }
        }
      }
      commits(last: 1) { nodes { commit { id oid committedDate
        statusCheckRollup { contexts(first: 100) {
          nodes {
            ... on CheckRun { name status conclusion startedAt checkSuite { app { databaseId } } }
          }
          pageInfo { endCursor hasNextPage }
        } } } } }
    }
  }
}"""

CONTEXTS_QUERY = """
query($id: ID!, $after: String!) {
  node(id: $id) {
    ... on Commit { oid
      statusCheckRollup { contexts(first: 100, after: $after) {
        nodes {
          ... on CheckRun { name status conclusion startedAt checkSuite { app { databaseId } } }
        }
        pageInfo { endCursor hasNextPage }
      } }
    }
  }
}"""

PAGE_INFO = "pageInfo { endCursor hasNextPage }"
COMMENT_FIELDS = "id body updatedAt"
INLINE_FIELDS = f"{COMMENT_FIELDS} state"
REVIEW_FIELDS = f"{COMMENT_FIELDS} state submittedAt"
THREAD_FIELDS = (f"id isResolved comments(first: 100) {{ nodes {{ {INLINE_FIELDS} }} "
                 f"{PAGE_INFO} }}")
DISCUSSION_QUERY = f"""
query($id: ID!) {{
  node(id: $id) {{
    ... on PullRequest {{ id body
      comments(first: 100) {{ nodes {{ {COMMENT_FIELDS} }} {PAGE_INFO} }}
      reviews(first: 100) {{ nodes {{ {REVIEW_FIELDS} }} {PAGE_INFO} }}
      reviewThreads(first: 100) {{ nodes {{ {THREAD_FIELDS} }} {PAGE_INFO} }}
    }}
  }}
}}"""

ENQUEUE = """
mutation($id: ID!, $sha: GitObjectID!) {
  enqueuePullRequest(input: {pullRequestId: $id, expectedHeadOid: $sha}) {
    mergeQueueEntry { position state }
  }
}"""


class GhError(Exception):
    pass


def gh_graphql(query: str, **variables: str | int) -> dict:
    command = ["gh", "api", "graphql", "-f", f"query={query}"]
    for key, value in variables.items():
        command += ["-F" if isinstance(value, int) else "-f", f"{key}={value}"]
    result = subprocess.run(command, capture_output=True, text=True)
    if result.returncode != 0:
        raise GhError(result.stderr.strip() or result.stdout.strip())
    try:
        data = json.loads(result.stdout)
    except ValueError as error:
        raise GhError("GitHub returned invalid JSON") from error
    if not isinstance(data, dict):
        raise GhError("GitHub returned no GraphQL response object")
    if data.get("errors"):
        raise GhError("; ".join(error.get("message", str(error)) for error in data["errors"]))
    if not isinstance(data.get("data"), dict):
        raise GhError("GitHub returned no GraphQL data")
    return data["data"]


def is_ancestor(owner: str, name: str, base: str, head: str) -> bool:
    """Return True when GitHub reports `base` is an ancestor of `head` (fail-closed on error)."""
    if base == head:
        return True
    result = subprocess.run(
        ["gh", "api", f"repos/{owner}/{name}/compare/{base}...{head}"],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        return False
    try:
        data = json.loads(result.stdout)
    except ValueError:
        return False
    return (
        isinstance(data, dict)
        and data.get("status") in {"ahead", "identical"}
        and data.get("behind_by") == 0
        and isinstance(data.get("merge_base_commit"), dict)
        and data["merge_base_commit"].get("sha") == base
    )


def fetch_pr(owner: str, name: str, number: int) -> dict:
    """Read the PR and every check page, pinned to its initial commit's node ID and OID.

    Querying `commits(last: 1)` again during pagination could mix two heads after a push. The
    immutable commit node keeps these pages together; enqueue's `expectedHeadOid` still rejects
    a push after this read. Null or incomplete later pages must never make an old success usable.
    """
    repository = gh_graphql(QUERY, owner=owner, name=name, number=number).get("repository")
    pr = (repository or {}).get("pullRequest")
    if not isinstance(pr, dict):
        raise GhError(f"no pull request #{number} in {owner}/{name}")
    depth = (((repository.get("mergeQueue") or {}).get("entries")) or {}).get("totalCount")
    if isinstance(depth, int) and not isinstance(depth, bool) and depth >= 0:
        pr["queueDepth"] = depth  # only for the printed estimate; the prefix check rereads the queue
    commits = (pr.get("commits") or {}).get("nodes")
    if not isinstance(commits, list):
        raise GhError("GitHub returned no commit list for the pull request")
    if not commits:
        return pr  # `assess` refuses a PR without a latest commit.
    commit = (commits[0] or {}).get("commit")
    if not isinstance(commit, dict) or not commit.get("id") or not commit.get("oid"):
        raise GhError("GitHub returned no latest commit identity")
    retargets = [
        e["createdAt"] for e in ((pr.get("timelineItems") or {}).get("nodes") or [])
        if isinstance(e, dict) and isinstance(e.get("createdAt"), str) and e["createdAt"]
    ]
    committed = commit.get("committedDate")
    base_oid = pr.get("baseRefOid")
    if (pr.get("state") == "OPEN"
            and not pr.get("mergeQueueEntry")
            and pr.get("baseRefName") == "main"
            and isinstance(committed, str) and committed
            and retargets and retargets[-1] > committed
            and isinstance(base_oid, str) and re.fullmatch(r"[0-9a-f]{40}", base_oid)
            and isinstance(commit["oid"], str) and re.fullmatch(r"[0-9a-f]{40}", commit["oid"])):
        pr["baseIsAncestor"] = is_ancestor(owner, name, base_oid, commit["oid"])
    if commit.get("statusCheckRollup") is None:
        return pr  # No checks have been reported yet.
    page, contexts, seen = commit, [], set()
    while True:
        connection = (page.get("statusCheckRollup") or {}).get("contexts")
        nodes = (connection or {}).get("nodes")
        info = (connection or {}).get("pageInfo")
        if (not isinstance(nodes, list) or any(not isinstance(node, dict) for node in nodes)
                or not isinstance(info, dict) or not isinstance(info.get("hasNextPage"), bool)):
            raise GhError("GitHub returned an incomplete check-context page")
        contexts.extend(nodes)
        if not info["hasNextPage"]:
            break
        cursor = info.get("endCursor")
        if not isinstance(cursor, str) or not cursor or cursor in seen:
            raise GhError("GitHub returned a missing or repeated check-context cursor")
        seen.add(cursor)
        page = gh_graphql(CONTEXTS_QUERY, id=commit["id"], after=cursor).get("node")
        if not isinstance(page, dict) or page.get("oid") != commit["oid"]:
            raise GhError("GitHub returned no matching commit for the next check-context page")
    commit["statusCheckRollup"]["contexts"] = {"nodes": contexts, "pageInfo": info}
    return pr


def discussion_nodes(owner: dict, kind: str, field: str, fields: str) -> list[dict]:
    """Read every page of one discussion connection, pinned to its owning node ID."""
    page, nodes, cursors, identities = owner, [], set(), set()
    while True:
        connection = page.get(field)
        batch = connection.get("nodes") if isinstance(connection, dict) else None
        info = connection.get("pageInfo") if isinstance(connection, dict) else None
        if (not isinstance(batch, list) or any(not isinstance(n, dict) for n in batch)
                or not isinstance(info, dict) or not isinstance(info.get("hasNextPage"), bool)):
            raise GhError(f"GitHub returned an incomplete discussion {field} page")
        for node in batch:
            identity = node.get("id")
            if not isinstance(identity, str) or not identity or identity in identities:
                raise GhError(f"GitHub returned a missing or repeated discussion {field} ID")
            identities.add(identity)
        nodes.extend(batch)
        if not info["hasNextPage"]:
            return nodes
        cursor = info.get("endCursor")
        if not isinstance(cursor, str) or not cursor or cursor in cursors:
            raise GhError(f"GitHub returned a missing or repeated discussion {field} cursor")
        cursors.add(cursor)
        query = f"""
query($id: ID!, $after: String!) {{
  node(id: $id) {{
    ... on {kind} {{ id
      {field}(first: 100, after: $after) {{ nodes {{ {fields} }} {PAGE_INFO} }}
    }}
  }}
}}"""
        page = gh_graphql(query, id=owner["id"], after=cursor).get("node")
        if not isinstance(page, dict) or page.get("id") != owner["id"]:
            raise GhError(f"GitHub returned no matching node for discussion {field} pagination")


def discussion_text(node: dict) -> tuple[str, str, str]:
    """Keep exact text as well as its edit time, including edits within the same second."""
    if (not isinstance(node.get("body"), str) or not isinstance(node.get("updatedAt"), str)
            or not node["updatedAt"]):
        raise GhError("GitHub returned incomplete discussion text")
    return node["id"], node["body"], node["updatedAt"]


def fetch_discussion(pr_id: str) -> tuple:
    """Snapshot visible discussion, without interpreting approvals or hold prose.

    Use explicit reviewThreads: timelineItems does not reliably return inline threads. Read
    all comments, not just the newest, so edits/deletions of older holds are observable. Draft
    reviews and unpublished inline comments do not change the submitted discussion. GitHub has
    no expected-discussion lease; this read and the enqueue mutation still have a bounded race.
    """
    pr = gh_graphql(DISCUSSION_QUERY, id=pr_id).get("node")
    if not isinstance(pr, dict) or pr.get("id") != pr_id or not isinstance(pr.get("body"), str):
        raise GhError("GitHub returned no matching pull request discussion")
    comments = [discussion_text(c) for c in discussion_nodes(
        pr, "PullRequest", "comments", COMMENT_FIELDS)]
    reviews = []
    for review in discussion_nodes(pr, "PullRequest", "reviews", REVIEW_FIELDS):
        text = discussion_text(review)
        state, submitted = review.get("state"), review.get("submittedAt")
        if (not isinstance(state, str)
                or state not in {"PENDING", "APPROVED", "CHANGES_REQUESTED", "COMMENTED",
                                 "DISMISSED"}):
            raise GhError("GitHub returned an incomplete discussion review state")
        if state != "PENDING":
            if not isinstance(submitted, str) or not submitted:
                raise GhError("GitHub returned no submitted discussion review time")
            reviews.append((*text, state, submitted))
    threads = []
    for thread in discussion_nodes(pr, "PullRequest", "reviewThreads", THREAD_FIELDS):
        if not isinstance(thread.get("isResolved"), bool):
            raise GhError("GitHub returned an incomplete discussion thread state")
        inline = []
        for comment in discussion_nodes(
                thread, "PullRequestReviewThread", "comments", INLINE_FIELDS):
            text = discussion_text(comment)
            if comment.get("state") not in ("PENDING", "SUBMITTED"):
                raise GhError("GitHub returned an incomplete inline discussion comment state")
            if comment["state"] == "SUBMITTED":
                inline.append(text)
        if inline:
            threads.append((thread["id"], thread["isResolved"], tuple(sorted(inline))))
    return pr["body"], tuple(sorted(comments)), tuple(sorted(reviews)), tuple(sorted(threads))


def check_state(pr: dict) -> tuple[str, list[str]]:
    """Combined state of the required checks on the PR's latest commit, with failing names.

    Only check runs from the app the ruleset names count, and, like branch protection, only the
    most recent run of each check (an earlier run of the same commit may have been cancelled or
    failed). `success` when every required check's latest run succeeded, `pending` while one is
    missing or running, `failure` otherwise.
    """
    commits = pr["commits"]["nodes"]
    rollup = commits[0]["commit"].get("statusCheckRollup") if commits else None
    contexts = rollup["contexts"]["nodes"] if rollup else []
    pending, failed = False, []
    for name, app in REQUIRED_CHECKS.items():
        runs = [c for c in contexts if c.get("name") == name
                and ((c.get("checkSuite") or {}).get("app") or {}).get("databaseId") == app]
        if not runs:
            pending = True
            continue
        latest = max(runs, key=lambda c: c.get("startedAt") or "~")
        if latest.get("status") != "COMPLETED":
            pending = True
        elif latest.get("conclusion") != "SUCCESS":
            failed.append(name)
    if failed:
        return "failure", failed
    return ("pending" if pending else "success"), []


def assess(pr: dict, sha: str) -> tuple[str, list[str]]:
    """`queued`, `ready`, `pending` or `refused`, with reasons for a refusal or wait."""
    if pr["state"] != "OPEN":
        return "refused", [f"the pull request is {pr['state'].lower()}"]
    if pr["headRefOid"] != sha:
        return "refused", [f"its head is {pr['headRefOid']}, not the approved {sha}; "
                           "review the new head (or run scripts/check_restack.py) first"]
    if pr.get("mergeQueueEntry"):
        return "queued", []
    commits = pr["commits"]["nodes"]
    if not commits or commits[0]["commit"]["oid"] != sha:
        return "refused", ["GitHub's latest commit for it is not the approved head; retry shortly"]
    reasons = []
    retargets = [e["createdAt"] for e in pr["timelineItems"]["nodes"] if e.get("createdAt")]
    if (retargets and retargets[-1] > commits[0]["commit"]["committedDate"]
            and not pr.get("baseIsAncestor")):
        reasons.append("its base changed after the approved head was committed (a stacked PR "
                       "retargeted when its lower PR landed); merge `main` into it, run "
                       "scripts/check_restack.py, and queue the new head")
    if pr["isDraft"]:
        reasons.append("it is a draft")
    if pr["baseRefName"] != "main":
        reasons.append(f"it is based on `{pr['baseRefName']}`, not `main`; queue it once the "
                       "lower PR lands and GitHub retargets it")
    if pr["mergeable"] == "CONFLICTING":
        reasons.append("it conflicts with `main`; merge `main` into it first")
    state, failed = check_state(pr)
    if state == "failure":
        reasons.append(f"required checks failed at the approved head: {', '.join(failed)}")
    if reasons:
        return "refused", reasons
    waiting = []
    if pr["mergeable"] != "MERGEABLE":
        waiting.append("GitHub has not yet determined whether it merges cleanly")
    if state == "pending":
        waiting.append("required checks are still running at the approved head")
    return ("pending", waiting) if waiting else ("ready", [])


def queue_estimate(pr: dict, number: int) -> str | None:
    """The queue depth ahead of the PR and a rough time to land, if no group build fails."""
    entry = pr.get("mergeQueueEntry")
    if isinstance(entry, dict) and isinstance(entry.get("position"), int):
        ahead = entry["position"] - 1
    elif isinstance(pr.get("queueDepth"), int):
        ahead = pr["queueDepth"]  # a new entry joins the end of the queue
    else:
        return None
    minutes = round(ahead * GROUP_BUILD_MINUTES / CONCURRENT_GROUP_BUILDS) + GROUP_BUILD_MINUTES
    return (f"Merge queue: {ahead} {'entry' if ahead == 1 else 'entries'} ahead of #{number}; "
            f"roughly {minutes} min to land ({ahead} x {GROUP_BUILD_MINUTES} min / "
            f"{CONCURRENT_GROUP_BUILDS} concurrent group builds, then its own build) if no group "
            "build fails.")


# Review records (see the module docstring): whole lines of a PR comment or review body, outside
# fenced code blocks. Matching is case-sensitive; leading whitespace and a leading `**` are
# tolerated.
RECORD_TIME = r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}Z"
HOLD_LINE = re.compile(rf"HOLD owner=(\S+) until=({RECORD_TIME}) reason=(.*)")
RELEASE_LINE = re.compile(r"HOLD-RELEASED by=(\S+) reason=(.*)")
CLAIM_LINE = re.compile(rf"CLAIM review head=([0-9a-f]{{40}}) by=(\S+) until=({RECORD_TIME})"
                        r"(?:\*\*)?")
VERDICT_LINE = re.compile(r"\*\*(APPROVE|REQUEST_CHANGES)\*\* at `?([0-9a-f]{7,40})`?"
                          r"(?: by `?([^\s`]+)`?)?")
CLAIM_LEASE = datetime.timedelta(minutes=45)  # the longest lease a claim line can hold
# `owner=maintainer` names Samuel, whose GitHub login may release it as well; so may `maintainer`.
MAINTAINER_IDS = frozenset({"maintainer", "SamuelSchlesinger"})
LEGACY_HOLD = re.compile(r"\bhold(?:ing)?\b", re.IGNORECASE)


class ReviewPost(NamedTuple):
    """A PR comment or submitted review: where it is, when it was posted and its text."""
    url: str
    posted: str  # GitHub's `YYYY-MM-DDTHH:MM:SSZ`; equal-width strings sort chronologically
    body: str


def gh_rest_items(endpoint: str) -> list:
    """Every item of a paginated REST list endpoint.

    `gh api --paginate` prints each page's JSON array in turn (`[...][...]`). Its `--slurp`, which
    would join them, needs gh 2.48, newer than some machines that run this script have.
    """
    result = subprocess.run(["gh", "api", "--paginate", endpoint], capture_output=True, text=True)
    if result.returncode != 0:
        raise GhError(result.stderr.strip() or result.stdout.strip())
    decoder, text, index, pages = json.JSONDecoder(), result.stdout, 0, []
    while True:
        while index < len(text) and text[index].isspace():
            index += 1
        if index == len(text):
            break
        try:
            page, index = decoder.raw_decode(text, index)
        except ValueError as error:
            raise GhError("GitHub returned invalid JSON") from error
        pages.append(page)
    if not pages or any(not isinstance(page, list) for page in pages):
        raise GhError(f"GitHub returned no list for {endpoint}")
    return [item for page in pages for item in page]


def fetch_review_posts(owner: str, name: str, number: int) -> list[ReviewPost]:
    """The PR's comments and submitted reviews, oldest first, read over REST."""
    posts = []
    for kind, endpoint, time_key in (
            ("comment", f"repos/{owner}/{name}/issues/{number}/comments?per_page=100",
             "created_at"),
            ("review", f"repos/{owner}/{name}/pulls/{number}/reviews?per_page=100",
             "submitted_at")):
        for item in gh_rest_items(endpoint):
            if not isinstance(item, dict):
                raise GhError(f"GitHub returned a malformed {kind}")
            if kind == "review" and item.get("state") == "PENDING":
                continue  # an unsubmitted draft review is not visible discussion
            posted, body = item.get(time_key), item.get("body") or ""
            if not isinstance(posted, str) or not re.fullmatch(
                    r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", posted) or not isinstance(body, str):
                raise GhError(f"GitHub returned a {kind} without its time or text")
            posts.append(ReviewPost(str(item.get("html_url") or f"{kind} {item.get('id')}"),
                                    posted, body))
    return sorted(posts, key=lambda post: post.posted)


def utc_now() -> datetime.datetime:
    return datetime.datetime.now(datetime.timezone.utc)


def _record_time(value: str) -> datetime.datetime:
    return datetime.datetime.strptime(value, "%Y-%m-%dT%H:%MZ").replace(
        tzinfo=datetime.timezone.utc)


def _posted_time(post: ReviewPost) -> datetime.datetime:
    return datetime.datetime.strptime(post.posted, "%Y-%m-%dT%H:%M:%SZ").replace(
        tzinfo=datetime.timezone.utc)


def _record_line(line: str) -> str:
    line = line.strip()
    return line[2:] if line.startswith("**") else line


def _unfenced_lines(body: str) -> list[str]:
    """The lines of `body` outside fenced code blocks, where examples of records are quoted."""
    lines, fence = [], None
    for raw in body.splitlines():
        stripped = raw.strip()
        if fence is not None:
            if stripped.startswith(fence):
                fence = None
        elif stripped.startswith(("```", "~~~")):
            fence = stripped[:3]
        else:
            lines.append(raw)
    return lines


def _releases(owner: str, by: str) -> bool:
    return by == owner or (owner in MAINTAINER_IDS and by in MAINTAINER_IDS)


def _verdict(post: ReviewPost) -> tuple[str, str, str | None] | None:
    """`(verdict, sha prefix, reviewer or None)` when the post's first non-empty line is one."""
    first = next((line.strip() for line in post.body.splitlines() if line.strip()), "")
    match = VERDICT_LINE.match(first)
    if not match:
        return None
    return match[1], match[2], match[3].rstrip(".,;:)") if match[3] else None


def review_record_check(posts: list[ReviewPost], sha: str, *, now: datetime.datetime,
                        since: str, reviewer: str | None = None) -> tuple[list[str], list[str]]:
    """`(refusals, advisories)` from the review records in `posts`, for queueing head `sha`.

    Refuses while a hold is in force (no later `HOLD-RELEASED` by its owner, `until` not passed);
    while another reviewer's claim on `sha` is unexpired (at most `CLAIM_LEASE` after it was
    posted) and that reviewer has posted no verdict at `sha` since; and when a `**REQUEST_CHANGES**`
    at `sha` is no older than the newest `**APPROVE**` at `sha`. A verdict names its reviewer by
    ` by <id>` on its line or, failing that, anywhere in its post. Free-text holds cannot be parsed:
    posts since the newest approval at `sha` (else since `since`) whose other lines mention a hold
    are listed as advisories.
    """
    def at_head(prefix: str) -> bool:
        return sha.startswith(prefix)

    verdicts = [(index, post, verdict) for index, post in enumerate(posts)
                if (verdict := _verdict(post)) is not None and at_head(verdict[1])]
    approvals = [index for index, _, verdict in verdicts if verdict[0] == "APPROVE"]
    newest_approval = approvals[-1] if approvals else None
    refusals: list[str] = []
    for index, post, verdict in verdicts:
        if verdict[0] == "REQUEST_CHANGES" and (
                newest_approval is None or post.posted >= posts[newest_approval].posted):
            refusals.append(f"a **REQUEST_CHANGES** at {sha[:12]} ({post.url}) is not followed by "
                            "a later **APPROVE** at that head")

    holds: list[tuple[tuple[int, int], str, str, str, ReviewPost]] = []
    releases: list[tuple[tuple[int, int], str]] = []
    claims: list[tuple[int, str, str, ReviewPost]] = []
    advisories: list[str] = []
    for index, post in enumerate(posts):
        free_text = []
        for number, raw in enumerate(_unfenced_lines(post.body)):
            line = _record_line(raw)
            if hold := HOLD_LINE.fullmatch(line):
                holds.append(((index, number), hold[1], hold[2], hold[3].strip(), post))
            elif release := RELEASE_LINE.fullmatch(line):
                releases.append(((index, number), release[1]))
            elif claim := CLAIM_LINE.fullmatch(line):
                if claim[1] == sha:
                    claims.append((index, claim[2], claim[3], post))
            elif LEGACY_HOLD.search(raw):
                free_text.append(raw.strip())
        start = posts[newest_approval].posted if newest_approval is not None else since
        if free_text and post.posted >= start:
            excerpt = free_text[0] if len(free_text[0]) <= 100 else free_text[0][:97] + "..."
            advisories.append(f"{post.url}: {excerpt}")

    for position, owner, until, reason, post in holds:
        released = any(_releases(owner, by) and later > position for later, by in releases)
        if not released and _record_time(until) > now:
            refusals.append(f"HOLD owner={owner} until={until} is in force ({post.url}): {reason}; "
                            f"its owner releases it with `HOLD-RELEASED by={owner} reason=...`")

    for index, by, until, post in claims:
        if by == reviewer:
            continue
        expires = min(_record_time(until), _posted_time(post) + CLAIM_LEASE)
        if expires <= now:
            continue
        mention = re.compile(rf"(?<![\w-]){re.escape(by)}(?![\w-])")
        if any(later >= index and (verdict[2] == by if verdict[2] else
                                   bool(mention.search(verdict_post.body)))
               for later, verdict_post, verdict in verdicts):
            continue
        hint = "" if reviewer else " (pass --reviewer ID if the claim is yours)"
        refusals.append(f"`{by}` claims review of {sha[:12]} until "
                        f"{expires.strftime('%Y-%m-%dT%H:%MZ')} with no verdict yet ({post.url}); "
                        f"wait for its verdict or for the claim to expire{hint}")
    return refusals, advisories


QUEUE_PREFIX_QUERY = """
query($owner: String!, $name: String!, $number: Int!, $cursor: String) {
  repository(owner: $owner, name: $name) {
    ref(qualifiedName: "refs/heads/main") { target { oid } }
    pullRequest(number: $number) { headRefOid baseRefName state }
    mergeQueue { entries(first: 100, after: $cursor) {
      totalCount nodes { position pullRequest { number headRefOid } }
      pageInfo { endCursor hasNextPage }
    } }
  }
}"""


def _oid(value: str) -> str:
    if not re.fullmatch(r"[0-9a-f]{40}", value):
        raise ValueError("expected a full lowercase commit SHA")
    return value


def snapshot_queue_prefix(
    owner: str,
    name: str,
    number: int,
    approved: str,
    *,
    graphql: Callable[..., dict] | None = None,
) -> tuple[str, list[tuple[int, str]]]:
    """Snapshot the merge-queue entries ahead of `number`, or the whole queue for a new entry."""
    call = gh_graphql if graphql is None else graphql
    entries: list[tuple[int, str]] = []
    numbers: set[int] = set()
    cursors: set[str] = set()
    variables: dict[str, object] = dict(owner=owner, name=name, number=number)
    while True:
        repo = call(QUEUE_PREFIX_QUERY, **variables)["repository"]
        pr = repo["pullRequest"]
        if not pr or (pr["state"], pr["baseRefName"], pr["headRefOid"]) != ("OPEN", "main", approved):
            raise ValueError(f"#{number} is not an open PR targeting main at {approved}")
        page = repo["mergeQueue"]["entries"]
        snapshot = (_oid(repo["ref"]["target"]["oid"]), page["totalCount"])
        if not entries:
            main_oid, count = snapshot
        elif (main_oid, count) != snapshot:
            raise ValueError("the queue changed during pagination; retry")
        for entry in page["nodes"]:
            queued = entry["pullRequest"]
            n = queued["number"]
            if entry["position"] != len(entries) + 1 or n in numbers:
                raise ValueError("queue positions changed during pagination; retry")
            if n == number:
                return main_oid, entries
            numbers.add(n)
            entries.append((n, _oid(queued["headRefOid"])))
        if not page["pageInfo"]["hasNextPage"]:
            if len(entries) != count:
                raise ValueError("incomplete queue listing; retry")
            return main_oid, entries
        cursor = page["pageInfo"]["endCursor"]
        if not cursor or cursor in cursors:
            raise ValueError("incomplete queue listing; retry")
        variables["cursor"] = cursor
        cursors.add(cursor)


def replay_repository(root: Path | None = None) -> Path | None:
    """Locate a non-shallow Git repository for prefix replay, honoring `GIT_DIR` (including bare
    repositories), `ROOT`, and the current working directory."""
    env = {k: v for k, v in os.environ.items()
           if k not in ("GIT_ATTR_SOURCE", "GIT_CONFIG", "GIT_SHALLOW_FILE")
           and not k.startswith("GIT_TEST_")}
    if env.get("GIT_DIR"):
        git_dir = Path(env["GIT_DIR"])
        if not git_dir.is_absolute():
            env["GIT_DIR"] = str((Path.cwd() / git_dir).resolve())
        candidates = [root] if root is not None else [Path.cwd()]
    elif root is not None:
        candidates = [root]
    else:
        candidates = [ROOT, Path.cwd()]
    seen: set[str] = set()
    for candidate in candidates:
        key = str(candidate)
        if key in seen or not candidate.exists():
            continue
        seen.add(key)
        probe = subprocess.run(
            ["git", "-c", "core.commitGraph=false", "-C", key,
             "rev-parse", "--is-shallow-repository"],
            capture_output=True, text=True, env=env,
        )
        if probe.returncode == 0 and probe.stdout.strip() == "false":
            return candidate
    return None


def _format_hub_hits(hits: list[tuple[str, int]], limit: int = 3) -> str:
    shown = [f"`{rel}` ({trans:,} transitive importers)" for rel, trans in hits[:limit]]
    if len(hits) > limit:
        shown.append(f"and {len(hits) - limit} more")
    return ", ".join(shown)


def _modified_library_paths(cr_mod, repo_dir: Path, base: str, sha: str) -> list[str]:
    """`CslibFrontier/*.lean` paths that `sha` modifies or deletes since its merge base with `base`."""
    diff = cr_mod.git(
        repo_dir, "diff", "--no-ext-diff", "--no-renames", "--diff-filter=MD",
        "--name-only", "-z", cr_mod.merge_base(repo_dir, base, sha), sha, "--", "CslibFrontier/",
    )
    return sorted(
        p for p in diff.stdout.decode("utf-8", "surrogateescape").split("\0") if p.endswith(".lean")
    )


def _module_name(rel: str) -> str:
    return ".".join(Path(rel).with_suffix("").parts)


def _evaluate_hub_impact(
    repo_dir: Path,
    base: str,
    sha: str,
    entries: list[tuple[int, str]],
    number: int,
    *,
    cr_mod,
    root: Path | None = None,
    hold_hubs: bool = False,
    allow_hub: bool = False,
) -> tuple[str | None, str | None]:
    """Check whether `sha` modifies high-fan-in `CslibFrontier/` modules behind queue `entries`.

    Returns `(refusal, notice)`. `--hold-hubs` refuses a hub PR behind any entry, and fails closed
    whenever `sha` modifies existing `CslibFrontier/*.lean` modules and fan-in cannot be verified.
    Otherwise, while more than `HUB_PACING_DEPTH` entries are ahead and `allow_hub` is unset, a hub
    PR is refused when it adds at least the hub threshold of modules to the union of the modules
    the entries ahead rebuild, and gets a note when that cannot be verified. A hub PR that is not
    refused gets an advisory notice.
    """
    ahead = ", ".join(f"#{n}" for n, _ in entries)
    pace = not hold_hubs and not allow_hub and len(entries) > HUB_PACING_DEPTH

    def unverified(reason: str) -> tuple[str | None, str | None]:
        if hold_hubs:
            return f"--hold-hubs {reason}; run from a full checkout of current `main` or omit it.", None
        if pace:
            return None, (f"Note: hub pacing {reason}, so #{number} was queued behind "
                          f"{len(entries)} entries without checking its rebuild cone.")
        return None, None

    for oid in (base, sha):
        if cr_mod.git(repo_dir, "cat-file", "-e", f"{oid}^{{commit}}", ok=(0, 1, 128)).returncode:
            return unverified(f"could not inspect commit {oid[:12]} in {repo_dir}")
    try:
        modified = _modified_library_paths(cr_mod, repo_dir, base, sha)
    except cr_mod.GitError as error:
        return unverified(f"could not diff {sha[:12]} against {base[:12]}: {error}")
    if not modified:
        return None, None
    scan_root = (
        repo_dir if (repo_dir / "CslibFrontier").is_dir()
        else (ROOT if root is None and (ROOT / "CslibFrontier").is_dir() else None)
    )
    try:
        import check_hub_impact
    except ImportError:
        check_hub_impact = None
    if scan_root is None or check_hub_impact is None:
        return unverified("needs a local `CslibFrontier/` checkout and `scripts/check_hub_impact.py`")
    try:
        graph, _total = check_hub_impact.build_reverse_graph(scan_root)
    except OSError as error:
        return unverified(f"could not scan `CslibFrontier/` imports: {error}")
    threshold = check_hub_impact.DEFAULT_THRESHOLD
    high_threshold = getattr(check_hub_impact, "HIGH_THRESHOLD", 2000)
    cones: dict[str, set[str]] = {}

    def rebuilds(mod: str) -> set[str]:
        if mod not in cones:
            cones[mod] = check_hub_impact.rebuilt_importers(graph, mod) | {mod}
        return cones[mod]

    hits: list[tuple[str, int]] = []
    own: set[str] = set()
    for rel in modified:
        target = scan_root / rel
        if not target.is_file() or target.is_symlink():
            if (hold_hubs or pace) and not cr_mod.git(
                repo_dir, "cat-file", "-e", f"{base}:{rel}", ok=(0, 1, 128)
            ).returncode:
                return unverified(f"needs `{scan_root}` updated to current `main` "
                                  f"(`{rel}` is missing or symlinked locally)")
            continue
        cone = rebuilds(_module_name(rel))
        own |= cone
        if len(cone) - 1 >= threshold:
            hits.append((rel, len(cone) - 1))
    if not hits:
        return None, None
    hits.sort(key=lambda item: (-item[1], item[0]))
    summary = _format_hub_hits(hits)
    if hold_hubs:
        return (
            f"modifies high-fan-in hub module(s) ({summary}) while merge queue has entries ahead "
            f"({ahead}); wait for the queue to clear or omit --hold-hubs.",
            None,
        )
    # Every group build behind an entry rebuilds that entry's modules too, so what this PR costs
    # the queue is the part of its rebuild set that the entries ahead do not already rebuild.
    queued: set[str] = set()
    for _, entry_sha in entries:
        for rel in _modified_library_paths(cr_mod, repo_dir, base, entry_sha):
            queued |= rebuilds(_module_name(rel))
    added = len(own - queued)
    cost = (f"it adds {added:,} module{'' if added == 1 else 's'} to the {len(queued):,} that the "
            f"{len(entries)} entries ahead already rebuild")
    if pace and added >= threshold:
        return (
            f"modifies high-fan-in hub module(s) ({summary}) and {cost}; a hub PR waits while more "
            f"than {HUB_PACING_DEPTH} entries are ahead, because every later group build rebuilds "
            "its modules until it lands. Rerun when the queue is shorter, or pass --allow-hub to "
            "queue it now.",
            None,
        )
    severity = "Warning" if hits[0][1] >= high_threshold else "Note"
    notice = (
        f"{severity}: #{number} modifies high-fan-in hub module(s) ({summary}) with active queue "
        f"entries ahead ({ahead}); {cost}. Sequence broad hub refactors so trailing PRs do not "
        "stall behind cold rebuilds."
    )
    return None, notice


def check_queue_prefix(
    owner: str,
    name: str,
    number: int,
    sha: str,
    root: Path | None = None,
    before_replay: Callable[[], None] | None = None,
    hold_hubs: bool = False,
    on_hub_notice: Callable[[str], None] | None = None,
    allow_hub: bool = False,
) -> str | None:
    """Replay any merge-queue entries ahead of `number`.

    Returns `None` when the queue ahead of `number` is empty or merges cleanly, and returns a
    refusal description when the replay conflicts, when hub pacing or `--hold-hubs` blocks a
    high-fan-in hub PR behind active queue entries (`_evaluate_hub_impact`), or when non-empty queue
    entries cannot be replayed automatically (missing helper scripts or no full local Git
    repository).
    """
    scripts_dir = str(Path(__file__).resolve().parent)
    if scripts_dir not in sys.path:
        sys.path.insert(0, scripts_dir)
    try:
        import queue_status
    except ImportError:
        queue_status = None
    imported_gh_error = (
        getattr(getattr(queue_status, "queue_pr", None), "GhError", GhError)
        if queue_status is not None else GhError
    )
    git_error = queue_status.cr.GitError if queue_status is not None else ()
    try:
        if queue_status is not None:
            base, entries = queue_status.prefix(owner, name, number, sha, graphql=gh_graphql)
        else:
            base, entries = snapshot_queue_prefix(owner, name, number, sha, graphql=gh_graphql)
        if not entries:
            return None
        if before_replay is not None:
            before_replay()
        ahead = ", ".join(f"#{n}" for n, _ in entries)
        repo_dir = replay_repository(root)
        if queue_status is None or repo_dir is None:
            return (f"merge queue has entries ahead ({ahead}) and automatic prefix replay needs "
                    "`scripts/queue_status.py` and a full Git repository (or `GIT_DIR`); run "
                    f"`python3 scripts/queue_status.py prefix {number} {sha}` from a full clone "
                    "or wait for the queue to clear.")
        env_patch = {}
        if os.environ.get("GIT_DIR") and not Path(os.environ["GIT_DIR"]).is_absolute():
            env_patch["GIT_DIR"] = str((Path.cwd() / os.environ["GIT_DIR"]).resolve())
        old_git_dir = os.environ.get("GIT_DIR")
        hub_refusal, hub_notice = None, None
        try:
            if env_patch:
                os.environ["GIT_DIR"] = env_patch["GIT_DIR"]
            queue_status.fetch_objects(
                repo_dir, f"{owner}/{name}", [base, sha, *(queued_sha for _, queued_sha in entries)]
            )
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                rc = queue_status.check_prefix(repo_dir, base, entries, sha)
            if rc == 0:
                hub_refusal, hub_notice = _evaluate_hub_impact(
                    repo_dir, base, sha, entries, number,
                    cr_mod=queue_status.cr, root=root, hold_hubs=hold_hubs, allow_hub=allow_hub,
                )
        finally:
            if env_patch:
                if old_git_dir is None:
                    os.environ.pop("GIT_DIR", None)
                else:
                    os.environ["GIT_DIR"] = old_git_dir
        if rc == 0 and hub_refusal is not None:
            return hub_refusal
        if rc == 0 and queue_status.prefix(owner, name, number, sha,
                                           graphql=gh_graphql) != (base, entries):
            return "the merge queue changed during prefix replay; rerun the helper."
    except GhError:
        raise
    except imported_gh_error as error:
        raise GhError(str(error)) from error
    except (KeyError, TypeError, OSError, ValueError, subprocess.SubprocessError,
            git_error) as error:
        raise GhError(f"merge-queue prefix check failed: {error}") from error
    if rc == 0:
        if hub_notice is not None and on_hub_notice is not None:
            on_hub_notice(hub_notice)
        return None
    details = " ".join(line.strip() for line in output.getvalue().splitlines() if line.strip())
    return (f"{details}; wait for the conflicting queue entry to land or leave the queue, "
            "then rerun.")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("pr", type=int, help="pull request number")
    parser.add_argument("sha", help="the full approved head commit")
    parser.add_argument("--reviewer", metavar="ID",
                        help="your reviewer ID, so that your own review claim does not block")
    parser.add_argument("--wait", type=float, default=0, metavar="MINUTES",
                        help="wait this long for running required checks (default 0)")
    hubs = parser.add_mutually_exclusive_group()
    hubs.add_argument("--hold-hubs", action="store_true",
                      help="refuse to enqueue when active queue entries are ahead and the PR "
                           "modifies a high-fan-in CslibFrontier hub (>= 500 importers)")
    hubs.add_argument("--allow-hub", action="store_true",
                      help=f"enqueue a hub PR even when more than {HUB_PACING_DEPTH} entries are "
                           "ahead (default: refuse when it adds >= 500 modules to their rebuilds)")
    parser.add_argument("--repo", default=REPO, help=f"OWNER/NAME (default {REPO})")
    args = parser.parse_args(argv)
    if not re.fullmatch(r"[0-9a-f]{40}", args.sha):
        parser.error("SHA must be the full 40-character commit hash")
    if not re.fullmatch(r"[^/\s]+/[^/\s]+", args.repo):
        parser.error("--repo must be OWNER/NAME")
    if args.reviewer is not None and not re.fullmatch(r"[A-Za-z0-9_.-]+", args.reviewer):
        parser.error("--reviewer must be an ID of letters, digits, '.', '_' or '-'")
    owner, name = args.repo.split("/", 1)
    deadline = time.monotonic() + 60 * args.wait
    retries = MERGEABLE_RETRIES
    discussion = None
    try:
        while True:
            pr = fetch_pr(owner, name, args.pr)
            status, reasons = assess(pr, args.sha)
            if status != "pending":
                break
            if pr["mergeable"] == "UNKNOWN" and retries > 0:
                retries -= 1
                delay = MERGEABLE_SECONDS
            elif time.monotonic() < deadline:
                delay = POLL_SECONDS
            else:
                break
            if discussion is None:
                discussion = fetch_discussion(pr["id"])
            time.sleep(delay)
        if (estimate := queue_estimate(pr, args.pr)) is not None:
            print(estimate)
        if status == "queued":
            entry = pr["mergeQueueEntry"]
            print(f"#{args.pr} is already queued at {args.sha[:12]} "
                  f"(position {entry['position']}, {entry['state'].lower()}).")
            return 0
        if status != "ready":
            verb = "not queued yet" if status == "pending" else "not queued"
            print(f"#{args.pr} {verb}: " + "; ".join(reasons) + ".")
            return 1

        def snapshot_before_replay() -> None:
            nonlocal discussion
            if discussion is None:
                discussion = fetch_discussion(pr["id"])

        notices: list[str] = []
        conflict = check_queue_prefix(owner, name, args.pr, args.sha,
                                      before_replay=snapshot_before_replay,
                                      hold_hubs=args.hold_hubs,
                                      on_hub_notice=notices.append,
                                      allow_hub=args.allow_hub)
        if conflict is not None:
            print(f"#{args.pr} not queued: {conflict}")
            return 1
        if discussion is not None and fetch_discussion(pr["id"]) != discussion:
            print(f"#{args.pr} not queued: its review discussion changed while waiting; "
                  "reread the PR and any review holds, then rerun the helper.")
            return 1
        refusals, advisories = review_record_check(
            fetch_review_posts(owner, name, args.pr), args.sha,
            now=utc_now(), reviewer=args.reviewer,
            since=pr["commits"]["nodes"][0]["commit"]["committedDate"])
        if advisories:
            print(f"Advisory: comments since the approval of {args.sha[:12]} mention a hold "
                  "that is not a HOLD line; check that none is still in force:")
            for advisory in advisories:
                print(f"  {advisory}")
        if refusals:
            print(f"#{args.pr} not queued: " + "; ".join(refusals) + ".")
            return 1
        entry = (gh_graphql(ENQUEUE, id=pr["id"], sha=args.sha).get("enqueuePullRequest")
                 or {}).get("mergeQueueEntry")
    except GhError as error:
        print(f"queue_pr: {error}", file=sys.stderr)
        return 2
    if entry is None:
        print(f"queue_pr: GitHub returned no queue entry for #{args.pr}; check its state",
              file=sys.stderr)
        return 2
    print(f"#{args.pr} queued at {args.sha[:12]} (position {entry['position']}).")
    for notice in notices:
        print(notice)
    return 0


if __name__ == "__main__":
    sys.exit(main())
