#!/usr/bin/env python3
"""Categorize the origin repository's branches and optionally delete the safe ones.

Usage: python3 scripts/branch_cleanup.py [--json] [--delete merged|closed|nopr ...]
           [--older-than 14d] [--notice-issue N [--notice-wait 7d]] [--apply] [--log PATH]
           [--notice --identity TEXT [--notice-dir DIR] | --notice-report] [--repo OWNER/NAME]

Dry run by default. Every branch of the repository falls in one category, in this order:

* `open-head`: the head of an open PR from this repository;
* `open-base`: the base of an open PR;
* `merged`: the head of a PR that merged (the most recently closed PR from that branch);
* `closed`: the head of a PR closed without merging, with its closing date;
* `nopr`: no PR has ever come from it, with its last commit's committer date and author.

Protected, and never deleted: the default branch and `main`, branches with GitHub branch
protection, merge-queue branches (`gh-readonly-queue/`), the head or base of any open PR, and a
branch that no longer points at its PR's final head commit or whose tip was committed after the PR
closed (someone has pushed to it since).

`--delete merged`, `--delete closed` and `--delete nopr` (repeatable) select unprotected branches
to delete; `closed` and `nopr` also need the closing date or last commit to be older than
`--older-than` (default 14d). Without `--apply` it lists them.

No-PR branches are announced before they are deleted. `--notice --identity TEXT` writes the
notice: Markdown comments (split to stay under GitHub's comment size limit) whose table lists each
selected no-PR branch with its last commit date, author and tip commit, ending with the marker
`<!-- branch-cleanup-notice -->`. It prints the `gh issue comment` command that posts each file and
posts nothing itself (`--notice-report` prints the Markdown table report directly to standard
output). `--notice-issue N` then restricts `--delete nopr` to branches that a marked
comment on issue N listed at their current tip at least `--notice-wait` (default 7d) earlier and
that no later comment there names; `--delete nopr --apply` requires it. With `--apply` it first writes the
plan to a JSON log (`--log`, default a new file in the system temporary directory, never in the
checkout), then lists the open PRs again and, for each branch, rereads its ref and deletes it only
if it still points at the listed commit and no open PR now uses it. The log records each outcome and
every deleted branch's commit, and a restore command is printed for each deletion:

    gh api -X POST repos/OWNER/NAME/git/refs -f ref=refs/heads/BRANCH -f sha=SHA

Commit dates and authors come from the local Git object database when it has the commits
(`--git-dir`, by default this checkout's), otherwise from one REST call per commit. Listing every PR costs about one
REST call per hundred PRs. Exit status: 0 on success, 2 when GitHub could not be read or a deletion
failed.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from datetime import datetime, timedelta
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gh_records as gr  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
KINDS = ("merged", "closed", "nopr")
CATEGORIES = ("open-head", "open-base") + KINDS
QUEUE_PREFIX = "gh-readonly-queue/"
NOTICE_MARKER = "<!-- branch-cleanup-notice -->"
NOTICE_ROW = re.compile(r"^\|\s*`([^`]+)`\s*\|.*\|\s*`([0-9a-f]{40})`\s*\|\s*$", re.MULTILINE)
NOTICE_LIMIT = 60000  # characters per comment; GitHub accepts 65536


def local_commits(shas: list[str], git_dir: Path | None) -> dict[str, tuple[datetime, str]]:
    """Committer date and author name of the commits the local object database has."""
    if not shas:
        return {}
    command = ["git", "-C", str(git_dir or ROOT), "log", "--no-walk=unsorted", "--ignore-missing",
               "--format=%H%x1f%cI%x1f%an", *shas]
    try:
        out = subprocess.run(command, check=True, capture_output=True, text=True, timeout=120,
                             env={**os.environ, "GIT_OPTIONAL_LOCKS": "0"}).stdout
    except (OSError, subprocess.SubprocessError):
        return {}
    found = {}
    for line in out.splitlines():
        parts = line.split("\x1f")
        if len(parts) == 3:
            found[parts[0]] = (gr.parse_time(parts[1]), parts[2])
    return found


def commit_info(gh: gr.GitHub, shas: list[str], git_dir: Path | None,
                jobs: int = 4) -> dict[str, tuple[datetime, str]]:
    """Committer date and author name of each commit, locally when possible."""
    shas = list(dict.fromkeys(shas))
    found = local_commits(shas, git_dir)
    missing = [sha for sha in shas if sha not in found]

    def fetch(sha: str) -> tuple[datetime, str] | None:
        try:
            commit = gh.get(f"repos/{gh.repo}/commits/{sha}")["commit"]
        except gr.GitHubError as error:
            if error.status in (404, 422):
                return None
            raise
        return gr.parse_time(commit["committer"]["date"]), (commit.get("author") or {}).get(
            "name", "")

    for sha, info in zip(missing, gr.parallel(fetch, missing, jobs)):
        if info:
            found[sha] = info
    return found


def categorize(branches: list[dict], pulls: list[dict], repo: str, default: str,
               dates: dict[str, datetime], authors: dict[str, str] | None = None) -> list[dict]:
    """One record per branch: category, protection reasons, PR, dates and tip author."""
    heads: dict[str, list[dict]] = {}
    open_bases: dict[str, int] = {}
    repo_lower = repo.lower()
    for pr in pulls:
        if pr["state"] == "open":
            open_bases.setdefault(pr["base"]["ref"], pr["number"])
        if (((pr.get("head") or {}).get("repo") or {}).get("full_name") or "").lower() == repo_lower:
            heads.setdefault(pr["head"]["ref"], []).append(pr)
    records = []
    for branch in sorted(branches, key=lambda b: b["name"]):
        name, sha = branch["name"], branch["commit"]["sha"]
        own = heads.get(name, [])
        opened = [pr for pr in own if pr["state"] == "open"]
        closed = sorted((pr for pr in own if pr["state"] != "open"),
                        key=lambda pr: pr.get("closed_at") or "")
        record = {"branch": name, "sha": sha, "category": "", "pr": None, "closed_at": None,
                  "commit_date": gr.fmt_time(dates[sha]) if sha in dates else None,
                  "commit_author": (authors or {}).get(sha), "protected": []}
        protected = record["protected"]
        if name in (default, "main"):
            protected.append("default branch")
        if branch.get("protected"):
            protected.append("branch protection")
        if name.startswith(QUEUE_PREFIX):
            protected.append("merge-queue branch")
        if opened:
            record.update(category="open-head", pr=opened[0]["number"])
            protected.append(f"head of open PR #{opened[0]['number']}")
        if name in open_bases:
            if not opened:
                record.update(category="open-base", pr=open_bases[name])
            protected.append(f"base of open PR #{open_bases[name]}")
        if not record["category"] and closed:
            last = closed[-1]
            record.update(category="merged" if last.get("merged_at") else "closed",
                          pr=last["number"], closed_at=last.get("closed_at"))
            closed_at = gr.parse_time(last["closed_at"]) if last.get("closed_at") else None
            if sha != last["head"]["sha"] or (sha in dates and closed_at
                                              and dates[sha] > closed_at):
                protected.append(f"pushed to after PR #{last['number']} closed")
        if not record["category"]:
            record["category"] = "nopr"
        records.append(record)
    return records


def eligible(record: dict, kinds: set[str], now: datetime, age: timedelta) -> bool:
    if record["protected"] or record["category"] not in kinds:
        return False
    if record["category"] == "merged":
        return True
    stamp = record["closed_at"] if record["category"] == "closed" else record["commit_date"]
    return bool(stamp) and now - gr.parse_time(stamp) >= age


def notice_rows(rows: list[dict]) -> list[str]:
    return [f"| `{r['branch']}` | {r['commit_date'] or ''} | "
            f"{gr.markdown_cell(r.get('commit_author') or '')} | `{r['sha']}` |" for r in rows]


def notice_bodies(rows: list[dict], repo: str, identity: str, older_than: str,
                  wait: str) -> list[str]:
    """The notice comments announcing the deletion of the no-PR branches in `rows`."""
    lines = notice_rows(rows)
    chunks: list[list[str]] = [[]]
    size = 0
    for line in lines:
        if chunks[-1] and size + len(line) > NOTICE_LIMIT - 3000:
            chunks.append([])
            size = 0
        chunks[-1].append(line)
        size += len(line) + 1
    bodies = []
    header = [identity.strip(), ""] if identity.strip() else []
    for number, chunk in enumerate(chunks, 1):
        part = f" (part {number} of {len(chunks)})" if len(chunks) > 1 else ""
        bodies.append("\n".join([
            *header,
            f"**No-PR branches to be deleted{part}.** These {len(chunk)} branches of `{repo}` are "
            f"not the head of any pull request and have had no commit for {older_than}. They will "
            f"be deleted at least {wait} after this notice (`scripts/branch_cleanup.py --delete "
            "nopr --notice-issue <this issue>`). To keep one, push to it, open a pull request from "
            "it, or reply here naming it. Each deletion is logged with a restore command, `gh api "
            f"-X POST repos/{repo}/git/refs -f ref=refs/heads/BRANCH -f sha=SHA`, which works while "
            "GitHub still has the commit.", "",
            "| Branch | Last commit | Author | Tip |", "|---|---|---|---|", *chunk, "",
            NOTICE_MARKER]))
    return bodies


def notice_report(rows: list[dict], repo: str, older_than: str, wait: str,
                  identity: str = "") -> str:
    """Single Markdown table report of the eligible no-PR branches."""
    header = [identity.strip(), ""] if identity.strip() else []
    return "\n".join([
        *header,
        f"**No-PR branches to be deleted.** These {len(rows)} branches of `{repo}` are "
        f"not the head of any pull request and have had no commit for {older_than}. They will "
        f"be deleted at least {wait} after this notice (`scripts/branch_cleanup.py --delete "
        "nopr --notice-issue <this issue>`). To keep one, push to it, open a pull request from "
        "it, or reply here naming it. Each deletion is logged with a restore command, `gh api "
        f"-X POST repos/{repo}/git/refs -f ref=refs/heads/BRANCH -f sha=SHA`, which works while "
        "GitHub still has the commit.", "",
        "| Branch | Last commit | Author | Tip |", "|---|---|---|---|", *notice_rows(rows), "",
        NOTICE_MARKER])


@dataclass
class Notices:
    """The marked notices and the other comments on the notice issue."""

    issue: int
    wait: timedelta
    listed: dict[str, list[tuple[str, datetime]]] = field(default_factory=dict)
    replies: list[tuple[datetime, str, str]] = field(default_factory=list)

    @classmethod
    def read(cls, comments: list[dict], issue: int, wait: timedelta) -> "Notices":
        found = cls(issue, wait)
        for comment in comments:
            when, body = gr.parse_time(comment["created_at"]), comment.get("body") or ""
            unfenced = [line for _, line in gr.unfenced_lines(body)
                        if not line.lstrip().startswith(">")]
            if any(line.strip() == NOTICE_MARKER for line in unfenced):
                for line in unfenced:
                    if match := NOTICE_ROW.match(line):
                        found.listed.setdefault(match.group(1), []).append((match.group(2), when))
            else:
                found.replies.append((when, body, comment.get("html_url", "")))
        return found

    def hold(self, record: dict, now: datetime) -> str | None:
        """Why the no-PR branch must not be deleted yet, or None."""
        name = record["branch"]
        times = [when for sha, when in self.listed.get(name, []) if sha == record["sha"]]
        if not times:
            if name in self.listed:
                return f"its tip is not the one listed on #{self.issue}"
            return f"not listed in a notice on #{self.issue}"
        first = min(times)
        if now - first < self.wait:
            return f"noticed {gr.fmt_time(first)}; deletable from {gr.fmt_time(first + self.wait)}"
        named = re.compile(r"(?<![\w./-])" + re.escape(name) + r"(?![\w./-])")
        for when, body, url in self.replies:
            if when > first and named.search(body):
                return f"named in a reply after the notice ({url})"
        return None


def restore_command(repo: str, record: dict) -> str:
    ref = shlex.quote(f"ref=refs/heads/{record['branch']}")
    return f"gh api -X POST repos/{repo}/git/refs -f {ref} -f sha={record['sha']}"


def write_log(path: Path, log: dict) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(log, indent=2) + "\n")
    temporary.replace(path)


def delete(gh: gr.GitHub, plan: list[dict], log: dict, path: Path,
           sleep=lambda seconds: time.sleep(seconds), out=None, default: str = "main") -> bool:
    """Delete each planned branch that is unchanged and unused; log every outcome."""
    out = out or sys.stdout
    fresh = gh.open_pulls()
    repo_lower = gh.repo.lower()
    used = ({p["head"]["ref"] for p in fresh
             if (((p.get("head") or {}).get("repo") or {}).get("full_name") or "").lower()
             == repo_lower}
            | {p["base"]["ref"] for p in fresh})
    ok = True
    for entry in plan:
        name = entry["branch"]
        if name in (default, "main") or name.startswith(QUEUE_PREFIX):
            entry["status"] = "kept: protected branch"
        elif name in used:
            entry["status"] = "kept: an open PR now uses it"
        else:
            try:
                current = gh.get(gh.ref_path(name).replace("/git/refs/", "/git/ref/", 1))
                sha = ((current or {}).get("object") or {}).get("sha")
                if sha != entry["sha"]:
                    entry["status"] = f"kept: it moved to {sha}"
                else:
                    gh.write("DELETE", gh.ref_path(name))
                    entry["status"] = "deleted"
                    entry["deleted_at"] = gr.fmt_time(gr.utcnow())
                    print(f"deleted {name} at {entry['sha']}; restore: {entry['restore']}",
                          file=out, flush=True)
                    sleep(1)
            except gr.GitHubError as error:
                if error.status == 404:
                    entry["status"] = "already gone"
                else:
                    entry["status"] = f"failed: {error}"
                    ok = False
        write_log(path, log)
    return ok


def render(records: list[dict], plan: list[dict], waiting: list[dict], args,
           counts: dict[str, int], notice_files: list[Path]) -> str:
    out = [f"# Branches of {args.repo}", "", "| Category | Branches | Protected |", "|---|---|---|"]
    for category in CATEGORIES:
        rows = [r for r in records if r["category"] == category]
        out.append(f"| {category} | {len(rows)} | {sum(1 for r in rows if r['protected'])} |")
    out += ["", f"Unprotected and eligible: merged {counts['merged']}, closed before "
                f"{args.older_than} ago {counts['closed']}, no PR and last commit before "
                f"{args.older_than} ago {counts['nopr']}.", ""]
    if notice_files:
        issue = args.notice_issue or "<ISSUE>"
        out += [f"## Notice of {counts['nopr']} no-PR branches: {len(notice_files)} comment(s)",
                "", "Nothing was posted. Read each file, then post it:", "", "```bash",
                *(f"gh issue comment {issue} --repo {args.repo} --body-file {shlex.quote(str(f))}"
                  for f in notice_files), "```", ""]
    if waiting:
        out += [f"## No-PR branches not yet deletable: {len(waiting)}", "",
                "| Branch | Last commit | Reason |", "|---|---|---|"]
        out += [f"| `{w['branch']}` | {w['commit_date'] or ''} | {gr.markdown_cell(w['reason'])} |"
                for w in waiting]
        out.append("")
    if not args.delete:
        out.append("No `--delete` kind selected; nothing would be deleted.")
        return "\n".join(out)
    verb = "Deletion plan" if args.apply else "Would delete (dry run)"
    out += [f"## {verb}: {len(plan)} branches", ""]
    if "nopr" in args.delete and not args.notice_issue:
        out += ["Deleting no-PR branches with `--apply` needs `--notice-issue`; see `--notice`.", ""]
    out += ["| Branch | Category | PR | Date | Restore |", "|---|---|---|---|---|"]
    for entry in plan:
        date = entry["closed_at"] if entry["category"] == "closed" else entry["commit_date"]
        pr = f"#{entry['pr']}" if entry["pr"] else ""
        out.append(f"| `{entry['branch']}` | {entry['category']} | {pr} | {date or ''} | "
                   f"`{entry['restore']}` |")
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--delete", action="append", choices=KINDS, default=[],
                        help="select unprotected branches of this kind (repeatable)")
    parser.add_argument("--older-than", default="14d",
                        help="minimum age for closed and nopr deletions (default 14d)")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--dry-run", action="store_true", help="report only (the default)")
    mode.add_argument("--apply", action="store_true", help="delete the selected branches")
    mode.add_argument("--notice", action="store_true",
                      help="write the notice of the no-PR branches to delete, for an issue")
    mode.add_argument("--notice-report", action="store_true",
                      help="print the Markdown notice table of eligible no-PR branches")
    parser.add_argument("--identity", help="first paragraph of the notice; required with --notice")
    parser.add_argument("--notice-dir", type=Path,
                        help="directory for the notice files (default: a new temporary one)")
    parser.add_argument("--notice-issue", type=int,
                        help="issue with the no-PR notices; needed by --delete nopr --apply")
    parser.add_argument("--notice-wait", default="7d",
                        help="time from a notice to deletion (default 7d)")
    parser.add_argument("--log", type=Path, help="JSON log for --apply (default: a temp file)")
    parser.add_argument("--json", action="store_true", help="print every branch's record as JSON")
    parser.add_argument("--git-dir", type=Path, help="local repository for commit dates")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--repo", default=gr.REPO)
    parser.add_argument("--min-remaining", type=int, default=gr.MIN_REMAINING)
    args = parser.parse_args(argv)
    try:
        age = gr.parse_age(args.older_than)
        wait = gr.parse_age(args.notice_wait)
    except ValueError as error:
        parser.error(str(error))
    if args.apply and not args.delete:
        parser.error("--apply needs at least one --delete kind")
    if args.apply and "nopr" in args.delete and not args.notice_issue:
        parser.error("--delete nopr --apply needs --notice-issue: no-PR branches are deleted only "
                     "after a notice (see --notice)")
    if args.notice and not (args.identity or "").strip():
        parser.error("--notice needs --identity, naming who posts the notice")
    now = gr.utcnow()
    gh = gr.GitHub(args.repo)
    try:
        gh.require_budget(args.min_remaining)
        default = gh.get(f"repos/{args.repo}")["default_branch"]
        branches = gh.get_all(f"repos/{args.repo}/branches?per_page=100")
        pulls = gh.get_all(f"repos/{args.repo}/pulls?state=all&per_page=100")
        unlinked = categorize(branches, pulls, args.repo, default, {})
        need = [r["sha"] for r in unlinked if r["category"] in KINDS]
        info = commit_info(gh, need, args.git_dir, max(1, args.jobs))
        records = categorize(branches, pulls, args.repo, default,
                             {sha: date for sha, (date, _) in info.items()},
                             {sha: author for sha, (_, author) in info.items()})
        notices = None
        if args.notice_issue and "nopr" in args.delete:
            notices = Notices.read(gh.get_all(f"repos/{args.repo}/issues/{args.notice_issue}"
                                              "/comments?per_page=100"), args.notice_issue, wait)
    except gr.GitHubError as error:
        print(f"branch_cleanup: {error}", file=sys.stderr)
        return 2
    counts = {kind: sum(eligible(r, {kind}, now, age) for r in records) for kind in KINDS}
    plan, waiting = [], []
    for record in records:
        if not eligible(record, set(args.delete), now, age):
            continue
        reason = notices.hold(record, now) if notices and record["category"] == "nopr" else None
        if reason:
            waiting.append({**record, "reason": reason})
        else:
            plan.append({**record, "restore": restore_command(args.repo, record),
                         "status": "planned"})
    notice_files: list[Path] = []
    if args.notice_report:
        rows = [r for r in records if eligible(r, {"nopr"}, now, age)]
        if args.json:
            print(json.dumps({"repo": args.repo, "generated_at": gr.fmt_time(now),
                              "older_than": args.older_than, "notice_wait": args.notice_wait,
                              "nopr_branches": rows, "api_calls": gh.calls}, indent=2))
        else:
            print(notice_report(rows, args.repo, args.older_than, args.notice_wait,
                                args.identity or ""))
        return 0
    if args.notice:
        rows = [r for r in records if eligible(r, {"nopr"}, now, age)]
        directory = args.notice_dir or Path(tempfile.mkdtemp(prefix="branch-cleanup-notice-"))
        directory.mkdir(parents=True, exist_ok=True)
        for number, body in enumerate(
                notice_bodies(rows, args.repo, args.identity, args.older_than, args.notice_wait), 1):
            notice_files.append(directory / f"notice-{number}.md")
            notice_files[-1].write_text(body + "\n")
    ok = True
    if args.apply:
        path = args.log or Path(tempfile.gettempdir()) / (
            f"branch-cleanup-{now.strftime('%Y%m%dT%H%M%SZ')}.json")
        log = {"repo": args.repo, "started_at": gr.fmt_time(now), "delete": args.delete,
               "older_than": args.older_than, "notice_issue": args.notice_issue,
               "branches": plan}
        write_log(path, log)
        out = sys.stderr if args.json else sys.stdout
        print(f"Deletion log: {path}", file=out, flush=True)
        try:
            ok = delete(gh, plan, log, path, out=out, default=default)
        except gr.GitHubError as error:
            print(f"branch_cleanup: {error}; see {path}", file=sys.stderr)
            return 2
    if args.json:
        print(json.dumps({"repo": args.repo, "generated_at": gr.fmt_time(now),
                          "branches": records, "plan": plan, "waiting": waiting,
                          "notice_files": [str(f) for f in notice_files],
                          "api_calls": gh.calls}, indent=2))
    else:
        print(render(records, plan, waiting, args, counts, notice_files)
              + f"\n\n_{gh.calls} REST calls._")
    return 0 if ok else 2


if __name__ == "__main__":
    sys.exit(main())
