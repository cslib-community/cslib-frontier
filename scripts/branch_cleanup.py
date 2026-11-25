#!/usr/bin/env python3
"""Categorize the origin repository's branches and optionally delete the safe ones.

Usage: python3 scripts/branch_cleanup.py [--json] [--delete merged|closed|nopr ...]
           [--older-than 14d] [--apply] [--log PATH] [--repo OWNER/NAME]

Dry run by default. Every branch of the repository falls in one category, in this order:

* `open-head`: the head of an open PR from this repository;
* `open-base`: the base of an open PR;
* `merged`: the head of a PR that merged (the most recently closed PR from that branch);
* `closed`: the head of a PR closed without merging, with its closing date;
* `nopr`: no PR has ever come from it, with its last commit's committer date.

Protected, and never deleted: the default branch and `main`, branches with GitHub branch
protection, merge-queue branches (`gh-readonly-queue/`), the head or base of any open PR, and a
branch that no longer points at its PR's final head commit or whose tip was committed after the PR
closed (someone has pushed to it since).

`--delete merged`, `--delete closed` and `--delete nopr` (repeatable) select unprotected branches
to delete; `closed` and `nopr` also need the closing date or last commit to be older than
`--older-than` (default 14d). Without `--apply` it lists them. With `--apply` it first writes the
plan to a JSON log (`--log`, default a new file in the system temporary directory, never in the
checkout), then lists the open PRs again and, for each branch, rereads its ref and deletes it only
if it still points at the listed commit and no open PR now uses it. The log records each outcome and
every deleted branch's commit, and a restore command is printed for each deletion:

    gh api -X POST repos/OWNER/NAME/git/refs -f ref=refs/heads/BRANCH -f sha=SHA

Commit dates come from the local Git object database when it has the commits (`--git-dir`, by
default this checkout's), otherwise from one REST call per commit. Listing every PR costs about one
REST call per hundred PRs. Exit status: 0 on success, 2 when GitHub could not be read or a deletion
failed.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timedelta, timezone
import json
import os
from pathlib import Path
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


def local_dates(shas: list[str], git_dir: Path | None) -> dict[str, datetime]:
    """Committer dates of the commits the local object database has."""
    if not shas:
        return {}
    command = ["git", "-C", str(git_dir or ROOT), "log", "--no-walk=unsorted", "--ignore-missing",
               "--format=%H %cI", *shas]
    try:
        out = subprocess.run(command, check=True, capture_output=True, text=True, timeout=120,
                             env={**os.environ, "GIT_OPTIONAL_LOCKS": "0"}).stdout
    except (OSError, subprocess.SubprocessError):
        return {}
    dates = {}
    for line in out.splitlines():
        sha, _, date = line.partition(" ")
        if date:
            dates[sha] = gr.parse_time(date)
    return dates


def commit_dates(gh: gr.GitHub, shas: list[str], git_dir: Path | None,
                 jobs: int = 4) -> dict[str, datetime]:
    shas = list(dict.fromkeys(shas))
    dates = local_dates(shas, git_dir)
    missing = [sha for sha in shas if sha not in dates]

    def fetch(sha: str) -> datetime | None:
        try:
            return gr.parse_time(gh.get(f"repos/{gh.repo}/commits/{sha}")["commit"]["committer"]
                                 ["date"])
        except gr.GitHubError as error:
            if error.status in (404, 422):
                return None
            raise

    for sha, date in zip(missing, gr.parallel(fetch, missing, jobs)):
        if date:
            dates[sha] = date
    return dates


def categorize(branches: list[dict], pulls: list[dict], repo: str, default: str,
               dates: dict[str, datetime]) -> list[dict]:
    """One record per branch: category, protection reasons, PR and dates."""
    heads: dict[str, list[dict]] = {}
    open_bases: dict[str, int] = {}
    for pr in pulls:
        if pr["state"] == "open":
            open_bases.setdefault(pr["base"]["ref"], pr["number"])
        if ((pr.get("head") or {}).get("repo") or {}).get("full_name") == repo:
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
                  "protected": []}
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


def restore_command(repo: str, record: dict) -> str:
    ref = shlex.quote(f"ref=refs/heads/{record['branch']}")
    return f"gh api -X POST repos/{repo}/git/refs -f {ref} -f sha={record['sha']}"


def write_log(path: Path, log: dict) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(log, indent=2) + "\n")
    temporary.replace(path)


def delete(gh: gr.GitHub, plan: list[dict], log: dict, path: Path,
           sleep=lambda seconds: time.sleep(seconds), out=None) -> bool:
    """Delete each planned branch that is unchanged and unused; log every outcome."""
    out = out or sys.stdout
    fresh = gh.open_pulls()
    used = ({p["head"]["ref"] for p in fresh
             if ((p.get("head") or {}).get("repo") or {}).get("full_name") == gh.repo}
            | {p["base"]["ref"] for p in fresh})
    ok = True
    for entry in plan:
        name = entry["branch"]
        if name in used:
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


def render(records: list[dict], plan: list[dict], args, counts: dict[str, int]) -> str:
    out = [f"# Branches of {args.repo}", "", "| Category | Branches | Protected |", "|---|---|---|"]
    for category in CATEGORIES:
        rows = [r for r in records if r["category"] == category]
        out.append(f"| {category} | {len(rows)} | {sum(1 for r in rows if r['protected'])} |")
    out += ["", f"Unprotected and eligible: merged {counts['merged']}, closed before "
                f"{args.older_than} ago {counts['closed']}, no PR and last commit before "
                f"{args.older_than} ago {counts['nopr']}.", ""]
    if not args.delete:
        out.append("No `--delete` kind selected; nothing would be deleted.")
        return "\n".join(out)
    verb = "Deletion plan" if args.apply else "Would delete (dry run)"
    out += [f"## {verb}: {len(plan)} branches", "", "| Branch | Category | PR | Date | Restore |",
            "|---|---|---|---|---|"]
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
    parser.add_argument("--log", type=Path, help="JSON log for --apply (default: a temp file)")
    parser.add_argument("--json", action="store_true", help="print every branch's record as JSON")
    parser.add_argument("--git-dir", type=Path, help="local repository for commit dates")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--repo", default=gr.REPO)
    parser.add_argument("--min-remaining", type=int, default=gr.MIN_REMAINING)
    args = parser.parse_args(argv)
    try:
        age = gr.parse_age(args.older_than)
    except ValueError as error:
        parser.error(str(error))
    if args.apply and not args.delete:
        parser.error("--apply needs at least one --delete kind")
    now = gr.utcnow()
    gh = gr.GitHub(args.repo)
    try:
        gh.require_budget(args.min_remaining)
        default = gh.get(f"repos/{args.repo}")["default_branch"]
        branches = gh.get_all(f"repos/{args.repo}/branches?per_page=100")
        pulls = gh.get_all(f"repos/{args.repo}/pulls?state=all&per_page=100")
        unlinked = categorize(branches, pulls, args.repo, default, {})
        need = [r["sha"] for r in unlinked if r["category"] in ("nopr", "merged", "closed")]
        dates = commit_dates(gh, need, args.git_dir, max(1, args.jobs))
        records = categorize(branches, pulls, args.repo, default, dates)
    except gr.GitHubError as error:
        print(f"branch_cleanup: {error}", file=sys.stderr)
        return 2
    counts = {kind: sum(eligible(r, {kind}, now, age) for r in records) for kind in KINDS}
    plan = [{**r, "restore": restore_command(args.repo, r), "status": "planned"}
            for r in records if eligible(r, set(args.delete), now, age)]
    ok = True
    if args.apply:
        path = args.log or Path(tempfile.gettempdir()) / (
            f"branch-cleanup-{now.strftime('%Y%m%dT%H%M%SZ')}.json")
        log = {"repo": args.repo, "started_at": gr.fmt_time(now), "delete": args.delete,
               "older_than": args.older_than, "branches": plan}
        write_log(path, log)
        out = sys.stderr if args.json else sys.stdout
        print(f"Deletion log: {path}", file=out, flush=True)
        try:
            ok = delete(gh, plan, log, path, out=out)
        except gr.GitHubError as error:
            print(f"branch_cleanup: {error}; see {path}", file=sys.stderr)
            return 2
    if args.json:
        print(json.dumps({"repo": args.repo, "generated_at": gr.fmt_time(now),
                          "branches": records, "plan": plan, "api_calls": gh.calls}, indent=2))
    else:
        print(render(records, plan, args, counts) + f"\n\n_{gh.calls} REST calls._")
    return 0 if ok else 2


if __name__ == "__main__":
    sys.exit(main())
