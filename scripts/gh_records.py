#!/usr/bin/env python3
"""GitHub access and record parsing shared by the maintenance reports.

`tender_report.py`, `stale_notices.py` and `branch_cleanup.py` read pull requests, issues and
branches through `gh api`. They use the REST API, which has a larger budget on the shared account
than GraphQL; GraphQL is used only where REST has no endpoint (converting a pull request to a
draft). Every call goes through `GitHub`, which counts calls, follows pagination, backs off and
retries on a rate-limit response, and refuses to start a scan when the account's remaining REST
budget is below a floor, so that one report cannot spend what other fleets need.

A pull request's or issue's timeline (`issues/N/timeline`) supplies, in one paginated listing, its
comments, submitted reviews with their bodies and commits, pushes, base changes and merge-queue
events. `posts` turns it into `Post` records, and the parsers below read the machine-readable lines
that reviewers and coordinators write. Each line stands alone outside fenced code blocks in a PR
body, comment or review body; matching is case-sensitive and tolerates leading whitespace and a
leading `**`:

    HOLD owner=<id> until=<YYYY-MM-DDTHH:MMZ> reason=<free text to end of line>
    HOLD-RELEASED by=<id> reason=<text>
    CLAIM review head=<40-hex sha> by=<reviewer-id> until=<YYYY-MM-DDTHH:MMZ>

A hold is released by a later `HOLD-RELEASED` line from its owner (`maintainer` and the
maintainer's login name each other), by a later one whose reason starts with `expired` once the
hold's `until` has passed, or, for blocking purposes, when `until` passes. A verdict is a review or
comment whose first non-empty line begins with `**APPROVE**` or `**REQUEST_CHANGES**` followed by
` at <sha>`; a submitted review without such a line counts by its GitHub state (approved or changes
requested) at the commit it was submitted on. Inline review comments are not read.

Free-text holds written before the line format still bind until a coordinator converts them.
`free_text_holds` finds likely ones by wording, for a person to read; it cannot tell whether one is
still in force.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
import json
import re
import subprocess
import threading
import time
from urllib.parse import quote

REPO = "cslib-community/cslib-frontier"
MAINTAINER = "SamuelSchlesinger"
ACCEPT = "Accept: application/vnd.github+json"
# Refuse to start a scan with fewer REST calls left than this on the shared account.
MIN_REMAINING = 500
# `gh` reports both the primary and the secondary (abuse) limits with these words.
RATE_LIMITED = re.compile(r"rate limit|HTTP 429|abuse detection", re.IGNORECASE)
HTTP_STATUS = re.compile(r"\(HTTP (\d{3})\)")


class GitHubError(RuntimeError):
    """A `gh api` call failed; `status` is the HTTP status when `gh` reported one."""

    def __init__(self, message: str, status: int | None = None):
        super().__init__(message)
        self.status = status


class GitHub:
    """REST calls through `gh api`, one per page, with call counting and rate-limit backoff."""

    def __init__(self, repo: str = REPO, *, run: Callable = subprocess.run,
                 sleep: Callable[[float], None] = time.sleep, retries: int = 4,
                 backoff: float = 45.0):
        self.repo = repo
        self.calls = 0
        self.remaining_seen: int | None = None
        self._run, self._sleep = run, sleep
        self._retries, self._backoff = retries, backoff
        self._lock = threading.Lock()

    def _gh(self, args: list[str], stdin: str | None = None) -> str:
        for attempt in range(self._retries + 1):
            with self._lock:
                self.calls += 1
            try:
                return self._run(["gh", "api", *args], check=True, capture_output=True,
                                 text=True, timeout=120, input=stdin).stdout
            except subprocess.CalledProcessError as error:
                stderr = (error.stderr or "").strip()
                if attempt < self._retries and RATE_LIMITED.search(stderr):
                    self._sleep(self._backoff)
                    continue
                status = HTTP_STATUS.search(stderr)
                raise GitHubError(f"gh api {' '.join(args)}: {stderr}",
                                  int(status.group(1)) if status else None) from error
        raise AssertionError("unreachable")

    def _page(self, url: str) -> tuple[object, str | None]:
        """One GET with its headers: the decoded body and the next page's URL."""
        lines = self._gh(["-H", ACCEPT, "--include", url]).split("\n")
        end = next((i for i, line in enumerate(lines) if i and not line.strip("\r")), len(lines))
        headers = "\n".join(line.rstrip("\r") for line in lines[1:end])
        body = "\n".join(lines[end + 1:])
        if left := re.search(r"^x-ratelimit-remaining:\s*(\d+)", headers, re.I | re.M):
            self.remaining_seen = int(left.group(1))
        link = re.search(r"^link:(.*)$", headers, re.I | re.M)
        after = re.search(r'<([^>]+)>;\s*rel="next"', link.group(1)) if link else None
        return (json.loads(body) if body.strip() else None), (after.group(1) if after else None)

    def get(self, endpoint: str):
        """One GET; the decoded JSON body."""
        return self._page(endpoint)[0]

    def get_all(self, endpoint: str, key: str | None = None) -> list:
        """Every page of a listing; `key` names the list in an object-valued page."""
        records: list = []
        url: str | None = endpoint
        while url:
            page, url = self._page(url)
            records += (page or []) if key is None else (page or {}).get(key, [])
        return records

    def write(self, method: str, endpoint: str, body: dict | None = None):
        """A POST, PATCH or DELETE with a JSON body."""
        args = ["-H", ACCEPT, "--method", method, endpoint]
        if body is not None:
            args += ["--input", "-"]
        out = self._gh(args, None if body is None else json.dumps(body))
        return json.loads(out) if out.strip() else None

    def graphql(self, query: str, **variables: str) -> dict:
        args = ["graphql", "-f", f"query={query}"]
        for key, value in variables.items():
            args += ["-f", f"{key}={value}"]
        return json.loads(self._gh(args))

    def remaining(self) -> tuple[int, datetime]:
        """REST calls left on the account and when the budget resets (not itself counted)."""
        core = self.get("rate_limit")["resources"]["core"]
        with self._lock:
            self.calls -= 1
        return core["remaining"], datetime.fromtimestamp(core["reset"], timezone.utc)

    def require_budget(self, floor: int) -> None:
        left, reset = self.remaining()
        if left < floor:
            raise GitHubError(f"the account has {left} REST calls left until "
                              f"{fmt_time(reset)}, below the floor of {floor}; rerun later "
                              "or lower --min-remaining")

    def timeline(self, number: int) -> list[dict]:
        return self.get_all(f"repos/{self.repo}/issues/{number}/timeline?per_page=100")

    def open_pulls(self) -> list[dict]:
        return self.get_all(f"repos/{self.repo}/pulls?state=open&per_page=100")

    def ref_path(self, branch: str) -> str:
        return f"repos/{self.repo}/git/refs/heads/{quote(branch, safe='/')}"


def parallel(function: Callable, items: Iterable, jobs: int) -> list:
    """`function` over `items` with at most `jobs` concurrent calls, in order."""
    items = list(items)
    if jobs <= 1 or len(items) <= 1:
        return [function(item) for item in items]
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        return list(pool.map(function, items))


def utcnow() -> datetime:
    return datetime.now(timezone.utc)


def parse_time(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def fmt_time(value: datetime) -> str:
    return value.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%MZ")


def fmt_age(now: datetime, then: datetime) -> str:
    seconds = (now - then).total_seconds()
    if seconds < 0:
        return "in " + fmt_age(then, now)
    if seconds < 2 * 3600:
        return f"{int(seconds // 60)}m"
    if seconds < 2 * 86400:
        return f"{int(seconds // 3600)}h"
    return f"{int(seconds // 86400)}d"


def parse_age(value: str) -> timedelta:
    """`14d`, `48h` or `90m`."""
    match = re.fullmatch(r"(\d+)([dhm])", value.strip())
    if not match:
        raise ValueError(f"expected an age such as 14d, 48h or 90m, not {value!r}")
    unit = {"d": "days", "h": "hours", "m": "minutes"}[match.group(2)]
    return timedelta(**{unit: int(match.group(1))})


def short(sha: str) -> str:
    return sha[:12]


def excerpt(line: str, limit: int = 160) -> str:
    line = " ".join(line.split())
    return line if len(line) <= limit else line[:limit - 3] + "..."


FENCE = re.compile(r"^(`{3,}|~{3,})")


def unfenced_lines(body: str) -> list[tuple[int, str]]:
    """`(line_number, line)` pairs of `body` outside fenced code blocks."""
    out: list[tuple[int, str]] = []
    fence: str | None = None
    for index, raw in enumerate(body.splitlines()):
        stripped = raw.strip()
        if fence is not None:
            if stripped.startswith(fence) and not stripped.lstrip(fence[0]).strip():
                fence = None
        elif match := FENCE.match(stripped):
            fence = match.group(1)
        else:
            out.append((index, raw))
    return out


@dataclass(frozen=True)
class Post:
    """A PR or issue body, comment or submitted review, in timeline order (`seq`)."""

    when: datetime
    author: str
    body: str
    url: str
    kind: str  # "body", "comment" or "review"
    seq: int = 0
    state: str = ""  # a review's state, lower case
    commit: str = ""  # a review's commit

    def lines(self) -> list[str]:
        return self.body.splitlines()

    def unfenced_lines(self) -> list[tuple[int, str]]:
        return unfenced_lines(self.body)


def posts(item: dict, events: list[dict]) -> list[Post]:
    """The body, comments and submitted reviews of a PR or issue, oldest first."""
    found = [Post(parse_time(item["created_at"]), (item.get("user") or {}).get("login", ""),
                  item.get("body") or "", item.get("html_url", ""), "body")]
    for event in events:
        kind = event.get("event")
        if kind == "commented":
            found.append(Post(parse_time(event["created_at"]),
                              (event.get("user") or event.get("actor") or {}).get("login", ""),
                              event.get("body") or "", event.get("html_url", ""), "comment"))
        elif kind == "reviewed" and event.get("submitted_at") and event.get("state") != "pending":
            found.append(Post(parse_time(event["submitted_at"]),
                              (event.get("user") or {}).get("login", ""), event.get("body") or "",
                              event.get("html_url", ""), "review", state=event.get("state", ""),
                              commit=event.get("commit_id") or ""))
    found.sort(key=lambda post: post.when)
    return [Post(p.when, p.author, p.body, p.url, p.kind, i, p.state, p.commit)
            for i, p in enumerate(found)]


# The line formats. `PREFIX` tolerates leading whitespace and a leading `**`.
PREFIX = r"^[ \t]*(?:\*\*)?"
STAMP = r"(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}Z)"
HOLD = re.compile(PREFIX + r"HOLD owner=(\S+) until=" + STAMP + r" reason=(.*)$")
RELEASE = re.compile(PREFIX + r"HOLD-RELEASED by=(\S+) reason=(.*)$")
CLAIM = re.compile(PREFIX + r"CLAIM review head=([0-9a-f]{40}) by=(\S+) until=" + STAMP
                   + r"(?:\*\*)?[ \t]*$")
PR_RELEASE = re.compile(PREFIX + r"RELEASED by=(\S+) reason=(.*)$")
TAKEOVER = re.compile(PREFIX + r"TAKEOVER by=(\S+?)(?:\*\*)?[ \t]*$")
VERDICT = re.compile(r"[ \t]*\*\*(APPROVE|REQUEST_CHANGES)\*\* at `?([0-9a-f]{7,40})(?![0-9a-f])`?"
                     r"(?: by `?([^\s`]+)`?)?")
CLAIM_LEASE = timedelta(minutes=45)


def clean_id(value: str) -> str:
    return value.strip("`*")


def clean_reviewer_id(value: str) -> str:
    return value.strip("`*").rstrip(".,;:)").strip("`*")


def clean_reason(value: str) -> str:
    return re.sub(r"\s*\*\*\s*$", "", value).strip()


def _record_time(value: str) -> datetime | None:
    try:
        return parse_time(value)
    except ValueError:
        return None


def is_record_line(line: str) -> bool:
    """Whether `line` is a well-formed `HOLD`, `HOLD-RELEASED` or `CLAIM review` record."""
    if match := HOLD.match(line):
        return _record_time(match.group(2)) is not None
    if RELEASE.match(line):
        return True
    if match := CLAIM.match(line):
        return _record_time(match.group(3)) is not None
    return False


def sha_matches(sha: str, full: str) -> bool:
    """Whether `sha` (at least seven hex digits) names the commit `full`."""
    return len(sha) >= 7 and bool(full) and full.startswith(sha)


@dataclass(frozen=True)
class Verdict:
    decision: str  # "APPROVE" or "REQUEST_CHANGES"
    sha: str
    post: Post
    formal: bool  # from the review's GitHub state rather than a verdict line
    reviewer: str = ""


def verdict_of(post: Post) -> Verdict | None:
    """The verdict a post records, if any."""
    first = next((line for line in post.lines() if line.strip()), "")
    match = VERDICT.match(first)
    if match and (post.kind != "review" or post.state != "dismissed"):
        reviewer = clean_reviewer_id(match.group(3)) if match.group(3) else ""
        return Verdict(match.group(1), match.group(2), post, False, reviewer)
    if post.kind == "review" and post.commit:
        decision = {"approved": "APPROVE", "changes_requested": "REQUEST_CHANGES"}.get(post.state)
        if decision:
            return Verdict(decision, post.commit, post, True, post.author)
    return None


def verdicts(items: list[Post]) -> list[Verdict]:
    return [v for v in map(verdict_of, items) if v]


def current_approval(items: list[Post]) -> Verdict | None:
    """The latest approval, unless a request for changes was posted after it."""
    latest = None
    for verdict in verdicts(items):
        latest = verdict
    return latest if latest and latest.decision == "APPROVE" else None


def same_owner(owner: str, releaser: str, maintainer: str = MAINTAINER) -> bool:
    names = {"maintainer", maintainer}
    return owner == releaser or (owner in names and releaser in names)


@dataclass
class Hold:
    owner: str
    until: datetime
    reason: str
    post: Post
    line: int
    released_by: Post | None = None
    other_releases: list[str] = field(default_factory=list)

    def state(self, now: datetime) -> str:
        if self.released_by:
            return "released"
        return "active" if self.until > now else "expired"


def _scan_holds(items: list[Post],
                maintainer: str = MAINTAINER) -> tuple[list[Hold], list[tuple[int, str]]]:
    found: list[Hold] = []
    unmatched_releases: list[tuple[int, str]] = []
    for post in items:
        for number, line in post.unfenced_lines():
            if match := HOLD.match(line):
                until = _record_time(match.group(2))
                if until is not None:
                    found.append(Hold(clean_id(match.group(1)), until,
                                      clean_reason(match.group(3)), post, number))
            elif match := RELEASE.match(line):
                by, reason = clean_id(match.group(1)), clean_reason(match.group(2))
                had_open = any(not h.released_by for h in found)
                matched = False
                for hold in found:
                    if hold.released_by:
                        continue
                    if (same_owner(hold.owner, by, maintainer)
                            or (reason.startswith("expired") and hold.until <= post.when)):
                        hold.released_by = post
                        matched = True
                    else:
                        hold.other_releases.append(by)
                if not matched and not had_open:
                    unmatched_releases.append((post.seq, by))
    return found, unmatched_releases


def holds(items: list[Post], maintainer: str = MAINTAINER) -> list[Hold]:
    """Every formatted hold outside fenced code blocks, with the release line that released it."""
    return _scan_holds(items, maintainer)[0]


@dataclass(frozen=True)
class Release:
    by: str
    reason: str
    post: Post


def open_release(items: list[Post]) -> Release | None:
    """The last `RELEASED` line handing the PR to coordinators, unless a `TAKEOVER` followed it."""
    found = None
    for post in items:
        for _, line in post.unfenced_lines():
            if match := PR_RELEASE.match(line):
                found = Release(clean_id(match.group(1)), clean_reason(match.group(2)), post)
            elif TAKEOVER.match(line):
                found = None
    return found


@dataclass
class Claim:
    head: str
    by: str
    until: datetime
    post: Post
    ended_by: Post | None = None

    @property
    def expires(self) -> datetime:
        return min(self.until, self.post.when + CLAIM_LEASE)

    @property
    def lease_too_long(self) -> bool:
        return self.until - self.post.when > timedelta(minutes=45, seconds=59)


def claims(items: list[Post]) -> list[Claim]:
    """Each reviewer's latest review claim per head on the PR, with the verdict that ended it.

    A verdict ends a claim when it is posted after the claim at the claimed head by the same
    reviewer (`by <id>` on its verdict line, or mentioning `<id>` when no other reviewer id is on
    the verdict line).
    """
    latest: dict[tuple[str, str], Claim] = {}
    for post in items:
        for _, line in post.unfenced_lines():
            if match := CLAIM.match(line):
                until = _record_time(match.group(3))
                if until is not None:
                    head, by = match.group(1), clean_id(match.group(2))
                    latest[(by, head)] = Claim(head, by, until, post)
    for verdict in verdicts(items):
        for claim in latest.values():
            if (claim.ended_by is not None or verdict.post.seq <= claim.post.seq
                    or not sha_matches(verdict.sha, claim.head)):
                continue
            mention = re.compile(rf"(?<![\w.-]){re.escape(claim.by)}(?![\w.-])")
            same = (verdict.reviewer == claim.by if (verdict.reviewer and not verdict.formal)
                    else (verdict.reviewer == claim.by or bool(mention.search(verdict.post.body))))
            if same:
                claim.ended_by = verdict.post
    return sorted(latest.values(), key=lambda claim: claim.post.seq)


# Wording that usually marks a free-text hold. STRONG wording (an upper-case `HOLD`, one of the
# phrases, or a request for human review, which AGENTS.md says the queueing reviewer waits for) is
# read across the PR unless an unmatched `HOLD-RELEASED` line later released it; WEAK wording,
# which also appears in ordinary discussion, only in the approval at the current head and the posts
# after it. "Agent review is not human review" matches neither.
STRONG_WORD = re.compile(r"\bHOLD\b")
HUMAN_REVIEW = re.compile(
    r"\b(?:hold|held|wait(?:s|ing)?|awaiting|needs?|requires?|request(?:s|ed|ing)?) (?:for )?"
    r"(?:an? )?human review\b|\bhuman review (?:is |was )?(?:requested|required|pending)\b",
    re.IGNORECASE)
STRONG_PHRASE = re.compile(
    r"\bon hold\b|\b(?:do not|don't) (?:yet )?(?:queue|merge)\b",
    re.IGNORECASE)
WEAK_HOLD = re.compile(
    r"\b(?:held (?:from|until|pending|for|back|off)|(?:queueing|queuing|is|remains|stays) held|"
    r"holds (?:below|above)|see holds|with holds|hold \d|"
    r"hold(?:ing)? (?:queueing|queuing|the queue|from|until|pending|on|for)|"
    r"not (?:yet )?queued)\b", re.IGNORECASE)
# Any mention of queueing, sequencing or waiting on another PR in a post after the approval at the
# head, such as another coordinator's "I'll verify the resulting delta before queueing", is also
# read as a possible hold.
QUEUE_TALK = re.compile(
    r"\bqueu(?:e|es|ed|eing|ing)\b|\bsequenc(?:e|es|ed|ing)\b|"
    r"\bwait(?:s|ing)? (?:for|on|until)\b|\bafter #\d+ (?:lands|merges)\b|"
    r"\bconflict(?:s|ing)? with #\d+", re.IGNORECASE)


def _strong(line: str) -> bool:
    return bool(STRONG_WORD.search(line) or STRONG_PHRASE.search(line) or HUMAN_REVIEW.search(line))


def free_text_holds(items: list[Post], since: Post | None,
                    maintainer: str = MAINTAINER) -> list[tuple[Post, str]]:
    """Lines outside fenced code blocks that look like holds not written in the line format.

    `since` is the approval at the current head; weak wording counts only from it on, and any
    mention of queueing, sequencing or waiting in a later post by a person (not a `[bot]`). An
    earlier free-text hold is cleared only by a later `HOLD-RELEASED` line that was not paired with
    an earlier formatted `HOLD` (and for a human-review request, only from `maintainer`).
    """
    _, unmatched_releases = _scan_holds(items, maintainer)
    found = []
    for post in items:
        weak_ok = since is not None and post.seq >= since.seq
        talk_ok = (since is not None and post.seq > since.seq and post.kind != "body"
                   and not post.author.endswith("[bot]"))
        for _, line in post.unfenced_lines():
            if is_record_line(line):
                continue
            human = bool(HUMAN_REVIEW.search(line))
            if any(seq > post.seq and (not human or same_owner("maintainer", by, maintainer))
                   for seq, by in unmatched_releases):
                continue
            if (_strong(line) or (weak_ok and WEAK_HOLD.search(line))
                    or (talk_ok and QUEUE_TALK.search(line))):
                found.append((post, excerpt(line)))
                break
    return found


def queued(events: list[dict]) -> bool:
    """Whether the last merge-queue event in a timeline added the PR to the queue."""
    state = False
    for event in events:
        if event.get("event") == "added_to_merge_queue":
            state = True
        elif event.get("event") == "removed_from_merge_queue":
            state = False
    return state


def base_changes(events: list[dict]) -> list[datetime]:
    """When the PR's base branch was changed, automatically or by hand."""
    return [parse_time(e["created_at"]) for e in events
            if e.get("event") in ("automatic_base_change_succeeded", "base_ref_changed")
            and e.get("created_at")]


def markdown_cell(text: str) -> str:
    return text.replace("|", "\\|").replace("\n", " ")
