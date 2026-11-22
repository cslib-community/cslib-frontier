#!/usr/bin/env python3
"""Read-only checks for reviewers and the merge-queue tender."""

from __future__ import annotations

import argparse
from http.client import HTTPException
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from urllib.request import Request, urlopen

import cache_handoff
import check_restack as cr
import queue_pr
from restack_mechanical import plain_merge

sys.path.insert(0, str(Path(__file__).resolve().parent / "cache"))
import restore  # noqa: E402


QUEUE = """
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


def oid(value: str) -> str:
    if not re.fullmatch(r"[0-9a-f]{40}", value):
        raise ValueError("expected a full lowercase commit SHA")
    return value


def prefix(owner: str, name: str, number: int, approved: str,
           graphql=None) -> tuple[str, list[tuple[int, str]]]:
    """Snapshot the entries ahead of this PR, or the whole queue for a new entry."""
    call = queue_pr.gh_graphql if graphql is None else graphql
    return queue_pr.snapshot_queue_prefix(owner, name, number, approved, graphql=call)


def fetch_objects(root: Path, repo: str, commits: list[str]) -> None:
    missing = [sha for sha in dict.fromkeys(commits)
               if cr.git(root, "cat-file", "-e", sha + "^{commit}", ok=(0, 1, 128)).returncode]
    if missing:
        cr.git(root, "fetch", "--no-tags", "--no-write-fetch-head", "--no-auto-maintenance",
               "--recurse-submodules=no", f"https://github.com/{repo}.git", *missing)


def check_prefix(root: Path, main: str, entries: list[tuple[int, str]], approved: str) -> int:
    """Reproduce the queue's squash ancestry without moving a branch or creating a worktree."""
    cr.check_local_attributes(root)
    if cr.out(root, "rev-parse", "--is-shallow-repository") == "true":
        raise ValueError("prefix comparison needs full history")
    tip = main
    prefixes = [("main", tip)]
    for n, sha in entries:
        tree, conflicts = plain_merge(root, tip, sha)
        if conflicts:
            print(f"The prefix itself conflicts at #{n}: " + ", ".join(map(repr, sorted(conflicts))))
            return 1
        tip = cr.out(root, "-c", "user.name=queue-status", "-c", "user.email=queue@invalid",
                     "commit-tree", "--no-gpg-sign", tree, "-p", tip, "-m", f"Queue prefix through #{n}")
        prefixes.append((f"#{n}", tip))
    label = "main " + main[:12]
    if entries:
        label += " plus " + ", ".join(f"#{n}" for n, _ in entries)
    _, conflicts = plain_merge(root, tip, approved)
    if conflicts:
        print(f"Textual conflict against {label}:")
        remaining = set(conflicts)
        for name, commit in prefixes:
            seen = conflicts if commit == tip else plain_merge(root, commit, approved)[1]
            for path in sorted(remaining & seen):
                print(f"  {path!r} first conflicts at {name}")
                remaining.remove(path)
            if not remaining:
                break
        return 1
    print(f"No textual conflict against {label}.")
    return 0


def published(url: str) -> bool:
    """Read a bounded prefix of the mapping that publishers install after the archives."""
    request = Request(url, headers={"Range": "bytes=0-1023"})
    with urlopen(request, timeout=10) as response:
        if response.status not in (200, 206) or response.geturl() != url:
            return False
        # Only accept two complete records of the pinned format (tools/cache-origin/format.go).
        # A proxy error page or a row cut at the range boundary cannot signal readiness.
        records = response.read(1024).split(b"\n", 2)
        if len(records) != 3 or records[0] != b'"2026-03-17"':
            return False
        row = rb'\[\s*"[0-9a-f]{16}"\s*,\s*"[0-9a-f]{16}\.ltar"\s*\]'
        return re.fullmatch(row, records[1]) is not None


def published_origin(origins: list[str], toolchain: str, revision: str) -> bool:
    for origin in origins:
        url = f"{origin}/r0/{restore.SCOPE}/tc/{toolchain}/{revision}.jsonl"
        try:
            if published(url):
                print(f"Published mapping for {revision} is readable at {origin}.", flush=True)
                return True
            print(f"{origin}: no readable Lake mapping for {revision}", flush=True)
        except (OSError, HTTPException, ValueError) as error:
            print(f"{origin}: {error}", flush=True)
    return False


def compatible_main_pushes(root: Path, repo: str, revision: str):
    """A coalesced pin bump can first publish from a later main push with the same build inputs."""
    endpoint = (f"repos/{repo}/actions/workflows/lean_action_ci.yml/runs"
                "?branch=main&event=push&status=success&per_page=5")
    runs = cache_handoff.gh_get(endpoint)["workflow_runs"]
    candidates = [oid(run["head_sha"]) for run in runs if run["head_sha"] != revision]
    fetch_objects(root, repo, candidates)
    for candidate in candidates:
        # Following just first parents excludes a pin present only on a side branch. The last
        # commit before the excluded history must have the specified pin as its first parent.
        path = cr.out(root, "rev-list", "--first-parent", "--parents", f"{revision}..{candidate}")
        if path and path.splitlines()[-1].split()[1:2] == [revision] and cr.git(
                root, "diff", "--quiet", "--no-ext-diff", revision, candidate, "--",
                *cache_handoff.INPUTS, ok=(0, 1)).returncode == 0:
            yield candidate


def pin_ready(root: Path, repo: str, revision: str, wait: float) -> bool:
    if restore.disabled(os.environ):
        raise ValueError("remote cache restore is disabled")
    origins = restore.origins(os.environ)
    if not origins:
        raise ValueError("no remote cache origins configured")
    toolchain = cr.out(root, "show", f"{revision}:lean-toolchain").replace("/", "--").replace(":", "---")
    if not re.fullmatch(r"[A-Za-z0-9_.+-]+", toolchain):
        raise ValueError("unsupported toolchain scope")
    deadline = time.monotonic() + wait * 60
    while True:
        if published_origin(origins, toolchain, revision):
            return True
        for candidate in compatible_main_pushes(root, repo, revision):
            if published_origin(origins, toolchain, candidate):
                print(f"Pin {revision} is on this main revision's first-parent chain and its "
                      "build inputs match.", flush=True)
                return True
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return False
        time.sleep(min(60, remaining))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default=queue_pr.REPO)
    commands = parser.add_subparsers(dest="command", required=True)
    check = commands.add_parser("prefix", help="check an exact PR head against the current queue")
    check.add_argument("pr", type=int)
    check.add_argument("sha")
    cache = commands.add_parser("cache-ready", help="report held heads when the new pin is published")
    cache.add_argument("revision", help="full SHA of the landed pin bump on main")
    cache.add_argument("held", nargs="+", metavar="PR@SHA", help="PR number and held full head SHA")
    cache.add_argument("--wait", type=float, default=0, metavar="MINUTES")
    args = parser.parse_args(argv)
    try:
        if not re.fullmatch(r"[\w.-]+/[\w.-]+", args.repo, re.ASCII):
            parser.error("--repo must be OWNER/NAME")
        owner, name = args.repo.split("/")
        if args.command == "prefix":
            approved = oid(args.sha)
            base, entries = prefix(owner, name, args.pr, approved)
            fetch_objects(cr.ROOT, args.repo, [base, approved, *(sha for _, sha in entries)])
            return check_prefix(cr.ROOT, base, entries, approved)
        if args.repo.lower() not in {queue_pr.REPO.lower(), restore.SCOPE.lower()}:
            parser.error(f"cache-ready checks the {restore.SCOPE} cache published by {queue_pr.REPO}")
        args.repo = queue_pr.REPO  # GitHub renamed the repository; Lake retains the old scope.
        owner, name = args.repo.split("/")
        if not math.isfinite(args.wait) or args.wait < 0:
            parser.error("--wait must be a finite nonnegative number of minutes")
        revision = oid(args.revision)
        heads = []
        for value in args.held:
            number, _, sha = value.partition("@")
            if not (number.isascii() and number.isdigit() and int(number) > 0):
                parser.error("expected PR@SHA with a positive PR number")
            heads.append((int(number), oid(sha)))
        fetch_objects(cr.ROOT, args.repo, [revision])
        if not pin_ready(cr.ROOT, args.repo, revision, args.wait):
            return 1
        for number, sha in heads:
            pr = queue_pr.fetch_pr(owner, name, number)
            state, reasons = queue_pr.assess(pr, sha)
            if state == "queued":
                entry = pr["mergeQueueEntry"]
                state = f"queued at position {entry['position']} ({entry['state']})"
            if state == "ready":
                state = "recheck discussion and other holds"
            print(f"#{number} {sha}: {state}" + (" (" + ", ".join(reasons) + ")" if reasons else ""))
        return 0
    except (KeyError, TypeError, OSError, ValueError, subprocess.SubprocessError,
            queue_pr.GhError, cr.GitError) as error:
        print(f"queue_status: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
