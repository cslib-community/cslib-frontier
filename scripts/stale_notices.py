#!/usr/bin/env python3
"""Find stalled drafts, issue claims and change requests, and optionally post one notice each.

Usage: python3 scripts/stale_notices.py [--only drafts,claims,changes] [--draft-days 7]
           [--claim-days 3] [--changes-hours 48] [--json] [--repo OWNER/NAME]
           [--apply --identity TEXT [--draft-stalled]] [--marker TEXT]

Dry run by default: it reads and reports. `--apply` posts the notices it lists, `--draft-stalled`
also converts the stalled change requests to drafts, and nothing ever closes a PR or an issue.
It finds:

* **drafts**: open draft PRs with no author activity for `--draft-days` (default 7) days;
* **claims**: open issues with an `Owner:` or `Claimed by`/`Claiming` line (in the body or a
  comment, not answered by a later `Released`/`Unclaimed` line) whose claimant has shown no activity
  for `--claim-days` (default 3) days and that no open PR cross-references;
* **changes**: open non-draft PRs whose latest verdict requests changes, with no push and no author
  response for `--changes-hours` (default 48) hours.

Author activity is the PR's creation, commits and force pushes, and the author's comments and
reviews, leaving out verdict, `HOLD` and `CLAIM` lines and earlier notices. On the shared account
every agent posts as the same login, so another agent's comment there also counts as the author's.
A claimant's activity is the claim itself and later comments by the login it names or that mention
its id (the first `code span` on the claim line, otherwise the next word). A push since a change
request is a head other than the one the request names, or a commit or force push after it.

Every notice starts with `--identity` (required with `--apply`) and ends with the HTML comment
`<!-- MARKER:KIND -->`. An item that has a marked notice from the last 24 hours, or one posted at
or after its last activity, is skipped so a rerun never posts twice for the same stall; notices are
left out of activity, and the report gives the age of the last one. Under AGENTS.md (Workers, item
3) a claim, or a PR that needs author action, may be taken over 24 hours after such a notice when
its owner has not responded; this script only reports that the window has passed, and never takes
anything over.

Cost: one REST call per scanned draft, non-draft PR or issue with comments or a claim line (two for
long timelines). It refuses to start below `--min-remaining` REST calls. Exit status: 0 when the
scan (and any posting) completed, 2 when GitHub could not be read or a write failed.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timedelta, timezone
import json
from pathlib import Path
import re
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gh_records as gr  # noqa: E402

KINDS = ("drafts", "claims", "changes")
MARKER = "stale-notice"
NOTICE_GAP = timedelta(hours=24)
PUSH_EVENTS = ("head_ref_force_pushed",)
AUTHOR_EVENTS = ("head_ref_force_pushed", "ready_for_review", "convert_to_draft", "reopened")
CLAIM_LINE = re.compile(
    r"^[ \t]*(?:[-*][ \t]+)?(?:\*\*)?(?:(Owner|Claim)(?:\*\*)?:(?:\*\*)?|(Claimed|Claiming)\b"
    r"(?:\*\*)?)[ \t]*(.*)$", re.MULTILINE)
RELEASE_LINE = re.compile(
    r"^[ \t]*(?:[-*][ \t]+)?(?:\*\*)?(?:Released|Releasing|Unclaim(?:ed|ing)?|Claim released)\b",
    re.MULTILINE)
CODE = re.compile(r"`([^`\s]+)`")
# A claim line whose value starts with one of these says that nobody holds the issue.
UNOWNED = re.compile(r"(?:none|nobody|unclaimed|unassigned|available|released|open|n/a|tbd|-|—)"
                     r"(?![\w-])", re.IGNORECASE)
STATUS_WORDS = {"active", "paused", "stopped", "blocked", "idle", "done", "in-progress"}
DRAFT_MUTATION = """
mutation($id: ID!) {
  convertPullRequestToDraft(input: {pullRequestId: $id}) { pullRequest { isDraft } }
}"""


def is_notice(post: gr.Post, marker: str) -> bool:
    if post.kind == "body":
        return False
    pattern = re.compile(rf"<!-- {re.escape(marker)}(?::[\w.-]+)? -->")
    return any(bool(pattern.fullmatch(line.strip())) for _, line in post.unfenced_lines())


def is_record(post: gr.Post) -> bool:
    """A verdict, hold or claim, which on the shared account is not the author's response."""
    return gr.verdict_of(post) is not None or any(gr.is_record_line(l)
                                                  for _, l in post.unfenced_lines())


def last_notice(items: list[gr.Post], marker: str) -> datetime | None:
    return max((p.when for p in items if is_notice(p, marker)), default=None)


def author_activity(pr: dict, events: list[dict], items: list[gr.Post], marker: str) -> datetime:
    author = (pr.get("user") or {}).get("login", "")
    times = [gr.parse_time(pr["created_at"])]
    for event in events:
        if event.get("event") == "committed" and (event.get("committer") or {}).get("date"):
            times.append(gr.parse_time(event["committer"]["date"]))
        elif (event.get("event") in AUTHOR_EVENTS and event.get("created_at")
              and (event.get("actor") or {}).get("login") == author):
            times.append(gr.parse_time(event["created_at"]))
    times += [p.when for p in items if p.kind != "body" and p.author == author
              and not is_notice(p, marker) and not is_record(p)]
    return max(times)


def change_request(pr: dict, events: list[dict], items: list[gr.Post],
                   marker: str) -> gr.Verdict | None:
    """The latest verdict when it requests changes and nothing has answered it."""
    found = gr.verdicts(items)
    if not found or found[-1].decision != "REQUEST_CHANGES":
        return None
    request = found[-1]
    if not gr.sha_matches(request.sha, pr["head"]["sha"]):
        return None
    after = request.post.when
    for event in events:
        if event.get("event") == "committed":
            date = (event.get("committer") or {}).get("date")
            if date and gr.parse_time(date) > after:
                return None
        elif event.get("event") in PUSH_EVENTS and gr.parse_time(event["created_at"]) > after:
            return None
    author = (pr.get("user") or {}).get("login", "")
    if any(p.seq > request.post.seq and p.author == author and not is_notice(p, marker)
           and not is_record(p) for p in items):
        return None
    return request


def claimants(rest: str, keyword: str) -> list[str] | None:
    """The ids on a claim line: its code spans, else the word after `by` or the colon.

    None when the line says nobody holds the issue (`Owner: none`, `Owner: unclaimed`, ...).
    """
    rest = rest.strip(" *")
    if UNOWNED.match(rest):
        return None
    ids = [code for code in CODE.findall(rest) if code.lower() not in STATUS_WORDS]
    if ids:
        return ids
    if keyword in ("Claimed", "Claiming"):
        by = re.search(r"\bby\s+@?([A-Za-z0-9][\w.\-]*)", rest)
        return [by.group(1).rstrip(".-")] if by else []
    word = re.match(r"@?([A-Za-z0-9][\w.\-]*)", rest)
    who = word.group(1).rstrip(".-") if word else ""
    return [who] if who and who.lower() not in STATUS_WORDS else []


def latest_claim(items: list[gr.Post]) -> tuple[gr.Post, str, list[str]] | None:
    """The last claim line not followed by a release line: its post, line and claimant ids."""
    found = None
    for post in items:
        for _, line in post.unfenced_lines():
            if match := CLAIM_LINE.match(line):
                ids = claimants(match.group(3), match.group(1) or match.group(2))
                found = None if ids is None else (post, gr.excerpt(line, 120), ids)
            elif found and RELEASE_LINE.match(line):
                found = None
    return found


def claimant_activity(items: list[gr.Post], claim: gr.Post, ids: list[str],
                      marker: str) -> datetime:
    """The claim's time or a later post by one of `ids` or mentioning one of them."""
    times = [claim.when]
    logins = {who.lower() for who in ids}
    for post in items:
        if post.seq <= claim.seq or is_notice(post, marker):
            continue
        if post.author.lower() in logins or any(len(who) >= 4 and who in post.body for who in ids):
            times.append(post.when)
    return max(times)


def open_pr_reference(events: list[dict]) -> int | None:
    for event in events:
        source = (event.get("source") or {}).get("issue") or {}
        if (event.get("event") == "cross-referenced" and "pull_request" in source
                and source.get("state") == "open"):
            return source.get("number")
    return None


def item(kind: str, record: dict, now: datetime, activity: datetime, detail: str,
         notice: datetime | None, **extra) -> dict:
    recent = bool(notice and now - notice < NOTICE_GAP)
    unanswered = bool(notice and activity <= notice)
    return {"kind": kind, "number": record["number"], "title": record.get("title", ""),
            "url": record.get("html_url", ""), "activity": gr.fmt_time(activity),
            "idle": gr.fmt_age(now, activity), "detail": detail,
            "last_notice": gr.fmt_time(notice) if notice else "",
            "window_passed": bool(notice and now - notice >= NOTICE_GAP and unanswered),
            "skip": recent or unanswered,
            "skip_reason": ("noticed within 24 hours" if recent
                            else "already noticed (no activity since)" if unanswered else ""),
            **extra}


def notice_text(entry: dict, converted: bool = False) -> str:
    if entry["kind"] == "drafts":
        return (f"This draft has had no author activity since {entry['activity']} "
                f"({entry['idle']}): no push and no comment from its author. If it is still in "
                "progress, a push or a one-line status comment is enough. If it is superseded, "
                "please say so and link the successor. If you have stopped work on it, post "
                "`RELEASED by=<id> reason=<text>` so that a coordinator can finish it. Nothing is "
                "closed automatically.")
    if entry["kind"] == "claims":
        return (f"The claim on this issue ({entry['detail']}) has had no visible activity since "
                f"{entry['activity']} ({entry['idle']}), and no open PR references the issue. A "
                "short status comment keeps the claim. Otherwise, under AGENTS.md (Workers, item "
                "3), the claim is released 24 hours after this notice. Nothing is closed "
                "automatically.")
    text = (f"Changes were requested at `{gr.short(entry['sha'])}` ({entry['request_url']}) on "
            f"{entry['activity']}, and there has been no push or author response for "
            f"{entry['idle']}. Please push a fix or reply, or, if you have stopped, post "
            "`RELEASED by=<id> reason=<text>` so that a coordinator can finish it. Under "
            "AGENTS.md (Workers, item 3) a "
            "coordinator may reassign this PR 24 hours after this notice. Nothing is closed "
            "automatically.")
    if converted:
        text += (" The PR has been converted to a draft; mark it ready for review when it is "
                 "updated.")
    return text


def scan(gh: gr.GitHub, kinds: set[str], now: datetime, args) -> list[dict]:
    found: list[dict] = []
    marker = args.marker

    def wanted(record: dict) -> bool:
        return not args.number or record["number"] in args.number
    if kinds & {"drafts", "changes"}:
        pulls = sorted((p for p in gh.open_pulls() if wanted(p)), key=lambda p: p["number"])
        drafts = [p for p in pulls if p.get("draft")] if "drafts" in kinds else []
        ready = [p for p in pulls if not p.get("draft")] if "changes" in kinds else []
        timelines = gr.parallel(lambda p: gh.timeline(p["number"]), drafts + ready, args.jobs)
        for pr, events in zip(drafts + ready, timelines):
            items = gr.posts(pr, events)
            notice = last_notice(items, marker)
            if pr.get("draft"):
                activity = author_activity(pr, events, items, marker)
                if now - activity >= timedelta(days=args.draft_days):
                    found.append(item("drafts", pr, now, activity,
                                      f"author `{pr['user']['login']}`", notice))
            elif request := change_request(pr, events, items, marker):
                if now - request.post.when >= timedelta(hours=args.changes_hours):
                    found.append(item("changes", pr, now, request.post.when,
                                      f"requested at `{gr.short(request.sha)}`", notice,
                                      sha=request.sha, request_url=request.post.url,
                                      node_id=pr.get("node_id", "")))
    if "claims" in kinds:
        issues = [i for i in gh.get_all(f"repos/{gh.repo}/issues?state=open&per_page=100")
                  if "pull_request" not in i and wanted(i)]
        # An issue without comments is claimed only by its body, which the listing already has.
        issues = sorted((i for i in issues if i.get("comments") or latest_claim(gr.posts(i, []))),
                        key=lambda i: i["number"])
        timelines = gr.parallel(lambda i: gh.timeline(i["number"]), issues, args.jobs)
        for issue, events in zip(issues, timelines):
            items = gr.posts(issue, events)
            claim = latest_claim(items)
            if not claim or open_pr_reference(events):
                continue
            post, line, ids = claim
            activity = claimant_activity(items, post, ids, marker)
            if now - activity >= timedelta(days=args.claim_days):
                who = ", ".join(f"`{i}`" for i in ids) or "claimant not identified"
                detail = f"{who}: [{line}]({post.url})"
                found.append(item("claims", issue, now, activity, detail,
                                  last_notice(items, marker)))
    return found


def apply(gh: gr.GitHub, found: list[dict], args, sleep=time.sleep) -> bool:
    """Post the notices; record each item's outcome and return whether every write succeeded.

    With `--draft-stalled` a stalled change request is converted first, so that its notice says
    so only when the conversion succeeded.
    """
    ok = True
    for entry in found:
        if entry["skip"]:
            reason = entry.get("skip_reason") or "noticed within 24 hours"
            entry["action"] = f"skipped: {reason}"
            continue
        actions, converted = [], False
        if entry["kind"] == "changes" and args.draft_stalled and entry.get("node_id"):
            try:
                gh.graphql(DRAFT_MUTATION, id=entry["node_id"])
                actions.append("converted to draft")
                converted = True
            except gr.GitHubError as error:
                actions.append(f"conversion failed: {error}")
                ok = False
        body = (f"{args.identity}\n\n{notice_text(entry, converted)}\n\n"
                f"<!-- {args.marker}:{entry['kind']} -->")
        try:
            gh.write("POST", f"repos/{gh.repo}/issues/{entry['number']}/comments", {"body": body})
            actions.insert(0, "posted")
        except gr.GitHubError as error:
            actions.insert(0, f"failed: {error}")
            ok = False
        entry["action"] = "; ".join(actions)
        sleep(1)
    return ok


def render(found: list[dict], args, applied: bool) -> str:
    titles = {"drafts": f"Drafts with no author activity for {args.draft_days} days",
              "claims": f"Issue claims with no claimant activity for {args.claim_days} days",
              "changes": f"Change requests unanswered for {args.changes_hours} hours"}
    mode = "Applied" if applied else "Dry run: nothing was posted"
    out = [f"# Stale notices for {args.repo}", "", f"{mode}. Notice marker `<!-- {args.marker}`.",
           ""]
    for kind in args.kinds:
        rows = [e for e in found if e["kind"] == kind]
        out += [f"## {titles[kind]} ({len(rows)})", ""]
        if not rows:
            continue
        out += ["| Item | Idle since | Detail | Last notice | Action |", "|---|---|---|---|---|"]
        for e in rows:
            notice = e["last_notice"] or "none"
            if e["window_passed"]:
                notice += " (24 hours passed with no activity)"
            reason = e.get("skip_reason") or "noticed within 24 hours"
            action = e.get("action") or (f"skip: {reason}" if e["skip"] else
                                         "would post" + ("; would convert to draft"
                                                         if kind == "changes" and args.draft_stalled
                                                         else ""))
            title = gr.markdown_cell(gr.excerpt(e["title"], 60))
            out.append(f"| [#{e['number']}]({e['url']}) {title} | {e['activity']} ({e['idle']}) | "
                       f"{gr.markdown_cell(e['detail'])} | {notice} | {action} |")
        out.append("")
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--only", default=",".join(KINDS),
                        help="comma-separated kinds to scan: drafts, claims, changes")
    parser.add_argument("--draft-days", type=int, default=7)
    parser.add_argument("--claim-days", type=int, default=3)
    parser.add_argument("--changes-hours", type=int, default=48)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--dry-run", action="store_true", help="report only (the default)")
    mode.add_argument("--apply", action="store_true", help="post the notices")
    parser.add_argument("--identity", help="first paragraph of every notice; required with --apply")
    parser.add_argument("--draft-stalled", action="store_true",
                        help="with --apply, also convert stalled change requests to drafts")
    parser.add_argument("--marker", default=MARKER, help=f"notice marker (default {MARKER})")
    parser.add_argument("--number", type=int, action="append",
                        help="only this PR or issue (repeatable)")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--repo", default=gr.REPO)
    parser.add_argument("--min-remaining", type=int, default=gr.MIN_REMAINING)
    args = parser.parse_args(argv)
    args.kinds = [k.strip() for k in args.only.split(",") if k.strip()]
    if not args.kinds or set(args.kinds) - set(KINDS):
        parser.error(f"--only takes a comma-separated subset of {', '.join(KINDS)}")
    if args.apply and not (args.identity or "").strip():
        parser.error("--apply needs --identity, naming who posts the notices")
    if args.draft_stalled and not args.apply:
        parser.error("--draft-stalled needs --apply")
    if not re.fullmatch(r"[\w.:-]+", args.marker):
        parser.error("--marker takes letters, digits, '.', ':', '_' and '-'")
    args.jobs = max(1, args.jobs)
    gh = gr.GitHub(args.repo)
    ok = True
    try:
        gh.require_budget(args.min_remaining)
        found = scan(gh, set(args.kinds), gr.utcnow(), args)
        if args.apply:
            ok = apply(gh, found, args)
    except gr.GitHubError as error:
        print(f"stale_notices: {error}", file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps({"repo": args.repo, "applied": args.apply, "items": found,
                          "api_calls": gh.calls}, indent=2))
    else:
        print(render(found, args, args.apply) + f"\n_{gh.calls} REST calls._")
    return 0 if ok else 2


if __name__ == "__main__":
    sys.exit(main())
