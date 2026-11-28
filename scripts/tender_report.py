#!/usr/bin/env python3
"""List open pull requests that are ready to move but not queued, for the tender.

Usage: python3 scripts/tender_report.py [--pr N ...] [--json] [--jobs 4] [--repo OWNER/NAME]

Read-only: it never comments, queues, pushes or restacks. It reads each open non-draft PR's
timeline (comments, submitted reviews, pushes, base changes and merge-queue events) through the
REST API and reports:

* **Ready to queue**: approved at the exact current head (a submitted approving review on that
  commit, or a verdict line `**APPROVE** at <sha>` naming it), with no request for changes after
  that approval; based on `main` and not retargeted since the approval; the required checks
  (`queue_pr.REQUIRED_CHECKS`) succeeded at the head; GitHub reports it mergeable; not a draft;
  not in the merge queue; no unreleased `HOLD` line whose `until` is still ahead; and no
  free-text hold found (`gh_records.free_text_holds`). Each row prints the `queue_pr.py` command
  for a non-author to run from a trusted checkout of current `main` after reading the PR.
* **Needs a human-readable check**: otherwise ready, but with likely free-text hold wording
  (including a request for human review, or any mention of queueing, sequencing or waiting after
  the approval, such as another coordinator's sequencing note), an expired unswept `HOLD` line, a
  `HOLD-RELEASED` line from someone other than a hold's owner, a review `CLAIM` still in its lease,
  an unanswered `REQUEST_CHANGES` at the head from another reviewer, or an approval of the head
  that is not a verdict line naming a non-author reviewer.
* **Approved at the head, not ready**: an active `HOLD`, required checks pending or failed,
  a conflict, mergeability not yet computed, or a base other than `main`.
* **Restack candidates**: approved PRs whose lower PR has landed (the base branch's PR merged, or
  the PR was retargeted after its approval) and whose head is unchanged (restack it, then run
  `scripts/check_restack.py`), and approved PRs whose head moved after the approval (run
  `scripts/check_restack.py <approved> <current>` before anyone queues the new head).
* **Expired HOLD lines** that no release line answered, for a coordinator to sweep after
  checking that the condition no longer applies or that the owner was notified.
* **Expired review CLAIMs with no verdict** after them.
* **Released to coordinators**: PRs whose author posted `RELEASED by=<id> reason=<text>` with no
  later `TAKEOVER by=<id>`, for a coordinator to take over (policy/review.md, Release).

The approval, holds and claims are read from PR bodies, comments and review bodies, not inline
review comments or linked issues. "Approved" means agent or human review recorded in the PR; the
report does not judge whether the review was sufficient, and the queueing reviewer still rereads
the discussion. Mergeability is GitHub's cached answer for the current base.

Cost: about one REST call per open non-draft PR (two for long timelines), plus two per approved
candidate. It refuses to start when the account has fewer than `--min-remaining` REST calls left.
Exit status: 0 when the report was produced, 2 when GitHub could not be read.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import sys
import time
from urllib.parse import quote

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gh_records as gr  # noqa: E402
from queue_pr import REQUIRED_CHECKS  # noqa: E402

APPROVED_WORD = re.compile(r"\bAPPROVED?\b")
AUTHOR_ID = re.compile(r"^[ \t]*`([A-Za-z0-9][\w.\-/@]*)`")
TRUSTED = "/path/to/trusted-main"


@dataclass
class Analysis:
    """What a PR's timeline says about its approval, holds and claims."""

    pr: dict
    posts: list[gr.Post]
    approval: gr.Verdict | None
    at_head: bool
    holds: list[gr.Hold]
    claims: list[gr.Claim]
    free_text: list[tuple[gr.Post, str]]
    other_approval: gr.Post | None
    queued: bool
    retargeted: datetime | None  # the last base change after the approval
    notes: list[str] = field(default_factory=list)

    @property
    def number(self) -> int:
        return self.pr["number"]

    @property
    def head(self) -> str:
        return self.pr["head"]["sha"]


def other_approval(items: list[gr.Post], head: str) -> gr.Post | None:
    """A later post approving `head` in words other than a verdict line."""
    last_verdict = max((v.post.seq for v in gr.verdicts(items)), default=-1)
    for post in reversed(items):
        if post.seq <= last_verdict or post.kind == "body":
            break
        if APPROVED_WORD.search(post.body) and (head in post.body or head[:12] in post.body):
            return post
    return None


def analyze(pr: dict, events: list[dict], maintainer: str = gr.MAINTAINER) -> Analysis:
    items = gr.posts(pr, events)
    approval = gr.current_approval(items)
    head = pr["head"]["sha"]
    at_head = bool(approval and gr.sha_matches(approval.sha, head))
    changes = [t for t in gr.base_changes(events) if approval and t > approval.post.when]
    found = gr.holds(items, maintainer)
    analysis = Analysis(
        pr, items, approval, at_head, found, gr.claims(items),
        gr.free_text_holds(items, approval.post if at_head else None, maintainer),
        None if at_head else other_approval(items, head), gr.queued(events),
        changes[-1] if changes else None)
    for hold in found:
        if not hold.released_by and hold.other_releases:
            analysis.notes.append(
                f"HOLD by `{hold.owner}` was followed by a release from "
                f"{', '.join(f'`{by}`' for by in hold.other_releases)}, not its owner")
    if at_head and approval is not None:
        pr_author = ((pr.get("user") or {}).get("login") or "").strip()
        first_body = next((line for line in (pr.get("body") or "").splitlines() if line.strip()),
                          "")
        body_agent = match.group(1) if (match := AUTHOR_ID.match(first_body)) else ""
        author_ids = {who.lower() for who in (pr_author, body_agent) if who}
        if not approval.formal and not approval.reviewer:
            analysis.notes.append(
                f"{link(approval.post, 'approval')} does not name a reviewer (`by <id>`)")
        elif approval.formal and pr_author and approval.post.author.lower() == pr_author.lower():
            analysis.notes.append(
                f"{link(approval.post, 'approval')} is by the PR author (`{approval.post.author}`)")
        elif not approval.formal and approval.reviewer.lower() in author_ids:
            analysis.notes.append(
                f"{link(approval.post, 'approval')} names the PR author (`{approval.reviewer}`)")
        at_current = [v for v in gr.verdicts(items) if gr.sha_matches(v.sha, head)]
        for index, verdict in enumerate(at_current):
            if verdict.decision == "REQUEST_CHANGES" and verdict.reviewer:
                if not any(later.decision == "APPROVE" and later.reviewer == verdict.reviewer
                           for later in at_current[index + 1:]):
                    analysis.notes.append(
                        f"{link(verdict.post, 'REQUEST_CHANGES')} by `{verdict.reviewer}` at "
                        f"this head has no later approval from `{verdict.reviewer}`")
    return analysis


def ci_state(runs: list[dict]) -> tuple[str, list[str]]:
    """`success`, `pending` or `failure` for the required checks, judged like `queue_pr.py`."""
    pending, failed = False, []
    for name, app in REQUIRED_CHECKS.items():
        mine = [r for r in runs if r.get("name") == name and (r.get("app") or {}).get("id") == app]
        if not mine:
            pending = True
            continue
        latest = max(mine, key=lambda r: r.get("started_at") or "~")
        if latest.get("status") != "completed":
            pending = True
        elif latest.get("conclusion") != "success":
            failed.append(name)
    if failed:
        return "failure", failed
    return ("pending" if pending else "success"), []


def check_runs(gh: gr.GitHub, sha: str) -> list[dict]:
    runs = []
    for name in REQUIRED_CHECKS:
        runs += gh.get_all(f"repos/{gh.repo}/commits/{sha}/check-runs?check_name={quote(name)}"
                           "&filter=all&per_page=100", "check_runs")
    return runs


def mergeable(gh: gr.GitHub, number: int, sleep=time.sleep) -> bool | None:
    """GitHub's mergeability for the PR, asking once more if it is still being computed."""
    for attempt in range(2):
        value = gh.get(f"repos/{gh.repo}/pulls/{number}").get("mergeable")
        if value is not None or attempt:
            return value
        sleep(3)
    return None


def lower_pr(gh: gr.GitHub, pr: dict, open_heads: dict[str, int]) -> tuple[str, int | None]:
    """Whether the PR's base branch belongs to an `open` or `merged` PR, or is `unknown`."""
    base = pr["base"]["ref"]
    if base in open_heads:
        return "open", open_heads[base]
    owner = gh.repo.split("/")[0]
    for lower in gh.get(f"repos/{gh.repo}/pulls?state=closed&head={owner}:{quote(base, safe='')}"
                        "&per_page=100") or []:
        if lower.get("merged_at"):
            return "merged", lower["number"]
    return "unknown", None


def queue_command(number: int, sha: str, repo: str) -> str:
    return f"python3 {TRUSTED}/scripts/queue_pr.py {number} {sha} --repo {repo}"


def link(post: gr.Post, label: str) -> str:
    return f"[{label}]({post.url})" if post.url else label


def build_report(gh: gr.GitHub, now: datetime, numbers: list[int] | None = None, jobs: int = 4,
                 maintainer: str = gr.MAINTAINER, sleep=time.sleep) -> dict:
    pulls = gh.open_pulls()
    same_repo = [p for p in pulls
                 if (((p.get("head") or {}).get("repo") or {}).get("full_name") or "").lower()
                 == gh.repo.lower()]
    open_heads = {p["head"]["ref"]: p["number"] for p in same_repo}
    if numbers:
        wanted = set(numbers)
        scan = [p for p in pulls if p["number"] in wanted]
        missing = wanted - {p["number"] for p in scan}
        if missing:
            raise gr.GitHubError("not open: " + ", ".join(f"#{n}" for n in sorted(missing)))
    else:
        scan = [p for p in pulls if not p.get("draft")]
    scan.sort(key=lambda p: p["number"])
    timelines = gr.parallel(lambda p: gh.timeline(p["number"]), scan, jobs)
    analyses = [analyze(p, events, maintainer) for p, events in zip(scan, timelines)]

    report = {"repo": gh.repo, "generated_at": gr.fmt_time(now), "scanned": len(scan),
              "drafts_skipped": 0 if numbers else len(pulls) - len(scan),
              "ready": [], "needs_check": [], "blocked": [], "restack": [],
              "expired_holds": [], "stale_claims": [], "released": []}

    def row(a: Analysis, **extra) -> dict:
        approval = (a.other_approval if a.other_approval and not a.at_head
                    else a.approval.post if a.approval else None)
        return {"number": a.number, "title": a.pr.get("title", ""), "url": a.pr.get("html_url", ""),
                "head": a.head, "approval_url": approval.url if approval else "",
                "approval_age": gr.fmt_age(now, approval.when) if approval else "", **extra}

    def restack(a: Analysis, where: str) -> None:
        approved = a.approval.sha
        if a.at_head:
            report["restack"].append(row(
                a, approved=approved, situation=f"{where}; approved head unchanged",
                next=(f"restack onto `main` (scripts/restack_mechanical.py {a.number} "
                      f"--approved-head {approved} when only generated files conflict), then "
                      f"scripts/check_restack.py {approved} <new head> "
                      "--approved-base <lower head at approval>")))
        else:
            report["restack"].append(row(
                a, approved=approved, situation=f"{where}; head moved since approval",
                next=(f"scripts/check_restack.py {approved} {a.head} "
                      "--approved-base <lower head at approval>")))

    candidates = []
    for a in analyses:
        if release := gr.open_release(a.posts):
            report["released"].append(row(a, by=release.by, reason=release.reason,
                                          release_url=release.post.url,
                                          since=gr.fmt_age(now, release.post.when)))
        for hold in a.holds:
            if hold.state(now) == "expired":
                report["expired_holds"].append({
                    "number": a.number, "owner": hold.owner, "until": gr.fmt_time(hold.until),
                    "reason": hold.reason, "url": hold.post.url})
        for claim in a.claims:
            if claim.ended_by is None and claim.expires <= now:
                notes = [] if claim.head == a.head else ["head moved since the claim"]
                if claim.lease_too_long:
                    notes.append("lease longer than 45 minutes")
                report["stale_claims"].append({
                    "number": a.number, "by": claim.by, "head": claim.head,
                    "until": gr.fmt_time(claim.expires), "url": claim.post.url, "notes": notes})
        if a.queued:
            continue
        if a.pr["base"]["ref"] != "main":
            if not a.approval:
                continue
            state, lower = lower_pr(gh, a.pr, open_heads)
            if state == "merged":
                restack(a, f"lower PR #{lower} merged")
            elif a.at_head:
                where = f"open #{lower}" if state == "open" else f"`{a.pr['base']['ref']}`"
                report["blocked"].append(row(a, reasons=[f"stacked on {where}"]))
            continue
        if a.approval and a.retargeted:
            restack(a, f"retargeted to `main` at {gr.fmt_time(a.retargeted)}, after the approval")
            continue
        if not (a.at_head or a.other_approval):
            if a.approval:
                report["restack"].append(row(
                    a, approved=a.approval.sha, situation="head moved since approval",
                    next=(f"scripts/check_restack.py {a.approval.sha} {a.head}; "
                          "review any differences")))
            continue
        active = [h for h in a.holds if h.state(now) == "active"]
        if active:
            report["blocked"].append(row(a, reasons=[
                f"HOLD by `{h.owner}` until {gr.fmt_time(h.until)}: {h.reason}" for h in active]))
            continue
        candidates.append(a)

    def probe(a: Analysis) -> tuple[str, list[str], bool | None]:
        state, failed = ci_state(check_runs(gh, a.head))
        return state, failed, mergeable(gh, a.number, sleep)

    for a, (state, failed, clean) in zip(candidates, gr.parallel(probe, candidates, jobs)):
        reasons = []
        if a.pr.get("draft"):
            reasons.append("draft")
        if state == "failure":
            reasons.append("required checks failed: " + ", ".join(failed))
        elif state == "pending":
            reasons.append("required checks pending")
        if clean is False:
            reasons.append("conflicts with `main`")
        elif clean is None:
            reasons.append("GitHub has not computed mergeability yet")
        if reasons:
            report["blocked"].append(row(a, reasons=reasons))
            continue
        checks = [f"{link(post, 'possible free-text hold or sequencing note')}: {text}"
                  for post, text in a.free_text]
        checks += [f"{link(h.post, 'expired HOLD')} by `{h.owner}` "
                   f"(until {gr.fmt_time(h.until)}, unswept): {h.reason}"
                   for h in a.holds if h.state(now) == "expired"]
        checks += a.notes
        checks += [f"{link(c.post, 'review CLAIM')} by `{c.by}` active until "
                   f"{gr.fmt_time(c.expires)}" for c in a.claims
                   if c.head == a.head and c.ended_by is None and c.expires > now]
        if not a.at_head:
            checks.append(f"{link(a.other_approval, 'approval of this head')} is not a verdict "
                          "line")
        entry = row(a, command=queue_command(a.number, a.head, gh.repo))
        if checks:
            report["needs_check"].append({**entry, "reasons": checks})
        else:
            report["ready"].append(entry)
    return report


def pr_cell(entry: dict) -> str:
    title = gr.markdown_cell(gr.excerpt(entry["title"], 70))
    if not entry["url"]:
        return f"#{entry['number']}"
    return f"[#{entry['number']}]({entry['url']}) {title}"


def approval_cell(entry: dict) -> str:
    if not entry.get("approval_url"):
        return ""
    return f"[{entry['approval_age']} ago]({entry['approval_url']})"


def render(report: dict) -> str:
    out = [f"# Tender report for {report['repo']} at {report['generated_at']}", "",
           f"Scanned {report['scanned']} open PRs"
           + (f" ({report['drafts_skipped']} drafts skipped)" if report["drafts_skipped"] else "")
           + ". Read-only: nothing was queued or posted. Reread each PR before acting.", ""]

    out += [f"## Ready to queue ({len(report['ready'])})", ""]
    if report["ready"]:
        out += ["| PR | Head | Approval |", "|---|---|---|"]
        out += [f"| {pr_cell(e)} | `{gr.short(e['head'])}` | {approval_cell(e)} |"
                for e in report["ready"]]
        out += ["", "Queue commands, for a non-author, from a trusted checkout of current `main`:",
                "", "```bash"] + [e["command"] for e in report["ready"]] + ["```"]
    out.append("")

    out += [f"## Released to coordinators ({len(report['released'])})", ""]
    if report["released"]:
        out += ["| PR | Released by | Since | Reason |", "|---|---|---|---|"]
        out += [f"| {pr_cell(e)} | `{e['by']}` | [{e['since']} ago]({e['release_url']}) | "
                f"{gr.markdown_cell(gr.excerpt(e['reason'], 100))} |" for e in report["released"]]
        out.append("")

    sections = [("needs_check", "Needs a human-readable check", "reasons"),
                ("blocked", "Approved at the head, not ready", "reasons")]
    for key, title, field_name in sections:
        out += [f"## {title} ({len(report[key])})", ""]
        if report[key]:
            out += ["| PR | Head | Approval | Why |", "|---|---|---|---|"]
            out += [f"| {pr_cell(e)} | `{gr.short(e['head'])}` | {approval_cell(e)} | "
                    + gr.markdown_cell("; ".join(e[field_name])) + " |" for e in report[key]]
            out.append("")

    out += [f"## Restack candidates ({len(report['restack'])})", ""]
    if report["restack"]:
        out += ["| PR | Approved head | Current head | Situation | Next step |",
                "|---|---|---|---|---|"]
        out += [f"| {pr_cell(e)} | `{gr.short(e['approved'])}` | `{gr.short(e['head'])}` | "
                f"{gr.markdown_cell(e['situation'])} | `{gr.markdown_cell(e['next'])}` |"
                for e in report["restack"]]
        out.append("")

    out += [f"## Expired HOLD lines ({len(report['expired_holds'])})", ""]
    if report["expired_holds"]:
        out += ["| PR | Owner | Until | Reason |", "|---|---|---|---|"]
        out += [f"| #{e['number']} | `{e['owner']}` | [{e['until']}]({e['url']}) | "
                f"{gr.markdown_cell(gr.excerpt(e['reason'], 100))} |"
                for e in report["expired_holds"]]
        out.append("")

    out += [f"## Expired review CLAIMs with no verdict ({len(report['stale_claims'])})", ""]
    if report["stale_claims"]:
        out += ["| PR | Reviewer | Head | Until | Notes |", "|---|---|---|---|---|"]
        out += [f"| #{e['number']} | `{e['by']}` | `{gr.short(e['head'])}` | "
                f"[{e['until']}]({e['url']}) | {'; '.join(e['notes'])} |"
                for e in report["stale_claims"]]
        out.append("")
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--pr", type=int, action="append", help="only these PRs (repeatable)")
    parser.add_argument("--json", action="store_true", help="print JSON instead of Markdown")
    parser.add_argument("--jobs", type=int, default=4, help="concurrent API calls (default 4)")
    parser.add_argument("--repo", default=gr.REPO)
    parser.add_argument("--maintainer", default=gr.MAINTAINER,
                        help="login that `maintainer` names in HOLD lines")
    parser.add_argument("--min-remaining", type=int, default=gr.MIN_REMAINING,
                        help="refuse to start below this many REST calls left")
    args = parser.parse_args(argv)
    gh = gr.GitHub(args.repo)
    try:
        gh.require_budget(args.min_remaining)
        report = build_report(gh, gr.utcnow(), args.pr, max(1, args.jobs),
                              args.maintainer)
    except gr.GitHubError as error:
        print(f"tender_report: {error}", file=sys.stderr)
        return 2
    report["api_calls"] = gh.calls
    print(json.dumps(report, indent=2) if args.json else render(report)
          + f"\n_{gh.calls} REST calls._")
    return 0


if __name__ == "__main__":
    sys.exit(main())
