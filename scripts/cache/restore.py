#!/usr/bin/env python3
"""Try ordered native Lake cache endpoints with a deadline per origin."""

import argparse
from collections import deque
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
from urllib.parse import urlsplit

from bounded import UnsafeShutdown, interruptible, run, seconds

DEFAULT_URLS = (
    "https://storage.googleapis.com/complexitylib-lake-cache",
    "https://complexitycache.csail.mit.edu",
)
SCOPE = "cslib-community/complexitylib"
ROOT = Path(__file__).resolve().parents[2]
MAX_REVISIONS = 100
STALLED_FALLBACK_REVISIONS = 20
# Exit status of an origin attempt that found no ancestor worth asking any origin for.
NO_COMPATIBLE_ANCESTOR = 3


def origins(env):
    # The old single-URL override remains authoritative, including empty=disable.
    if "COMPLEXITYLIB_CACHE_URL" in env:
        values = [env["COMPLEXITYLIB_CACHE_URL"]] if env["COMPLEXITYLIB_CACHE_URL"] else []
    else:
        values = env.get("COMPLEXITYLIB_CACHE_URLS", "").split() or list(DEFAULT_URLS)
    if len(values) > 8:
        raise ValueError("At most eight cache origins may be configured")
    for value in values:
        parsed = urlsplit(value)
        if (parsed.scheme not in ("https", "http") or not parsed.hostname or parsed.username
                or parsed.password or parsed.query or parsed.fragment or any(c.isspace() for c in value)):
            raise ValueError("Cache endpoints must be HTTP(S) URLs without credentials/query/fragment")
    return list(dict.fromkeys(value.rstrip("/") for value in values))


def disabled(env):
    return env.get("DISABLE_CACHE_RESTORE", "").lower() in ("1", "true")


def candidate_revisions(root, limit=MAX_REVISIONS, stalled_limit=STALLED_FALLBACK_REVISIONS):
    """Order ancestors of HEAD so descendants precede ancestors across merge parents.

    Uses wave-by-wave Kahn topological BFS over the reachable DAG of HEAD:
    - No ancestor is tried before any of its descendants (immune to timestamp skew and
      short-branch / long-main-streak diamonds).
    - Sibling lineages at a merge advance wave by wave in lockstep (so long feature
      branches do not crowd out a newly merged main parent in either parent order).
    - Within each wave, newer committer timestamps go first.
    - If a long (>limit) side branch still stalls an earlier merge base, append up to
      stalled_limit nearest stalled ancestors after the topological window.
    """
    raw = subprocess.check_output(
        ["git", "rev-list", "--parents", "--timestamp", "HEAD"],
        cwd=root, text=True,
    ).splitlines()
    if not raw:
        return []
    timestamps = {}
    parents = {}
    for line in raw:
        parts = line.split()
        ts = int(parts[0])
        rev = parts[1]
        timestamps[rev] = ts
        parents[rev] = list(dict.fromkeys(parts[2:]))

    indegree = {rev: 0 for rev in parents}
    for ps in parents.values():
        for parent in ps:
            if parent in indegree:
                indegree[parent] += 1

    # In the reachable DAG of HEAD, HEAD is the unique zero-indegree commit.
    wave = [rev for rev, deg in indegree.items() if deg == 0]
    wave.sort(key=lambda rev: timestamps[rev], reverse=True)

    ordered = []
    stalled = []
    stalled_seen = set()
    remaining_wave = []
    next_wave = []
    while wave and len(ordered) < limit:
        next_wave = []
        for idx, rev in enumerate(wave):
            ordered.append(rev)
            if len(ordered) >= limit:
                remaining_wave = wave[idx + 1:]
                break
            for parent in parents[rev]:
                if parent not in indegree:
                    continue
                indegree[parent] -= 1
                if indegree[parent] == 0:
                    next_wave.append(parent)
                elif parent not in stalled_seen:
                    stalled_seen.add(parent)
                    stalled.append(parent)
        else:
            next_wave.sort(key=lambda rev: timestamps[rev], reverse=True)
            wave = next_wave
            remaining_wave = []
            continue
        next_wave.sort(key=lambda rev: timestamps[rev], reverse=True)
        break

    if len(ordered) == limit and stalled_limit > 0:
        seen = set(ordered)
        stalled_roots = sorted((rev for rev in stalled if rev not in seen),
                               key=lambda rev: timestamps[rev], reverse=True)
        if stalled_roots:
            seeds = []
            for rev in (*remaining_wave, *next_wave, *stalled_roots):
                if rev not in seen:
                    seen.add(rev)
                    seeds.append(rev)
            fallback = deque(seeds)
            added = 0
            while fallback and added < stalled_limit:
                rev = fallback.popleft()
                ordered.append(rev)
                added += 1
                for parent in parents[rev]:
                    if parent in parents and parent not in seen:
                        seen.add(parent)
                        fallback.append(parent)
    return ordered


def mathlib_revision(manifest):
    """The Mathlib commit pinned by a `lake-manifest.json` text, or None if it cannot be read."""
    try:
        return next(package["rev"] for package in json.loads(manifest)["packages"]
                    if package["name"] == "mathlib")
    except (ValueError, KeyError, TypeError, StopIteration):
        return None


def same_mathlib(root, revisions):
    """Keep the revisions whose manifest pins the Mathlib commit this checkout pins.

    A module's input hash covers the outputs of everything it imports, so outputs built against
    another Mathlib commit match no module here: of the 3,880 to 10,469 modules published before
    each Mathlib bump up to November 2026, at most one was reusable after it. Restoring such a
    revision downloads a complete set and then compiles everything anyway. Bumps of cslib alone
    and other `lakefile.toml` changes kept 52% to 100% of outputs reusable, so only Mathlib's pin
    is compared. A revision whose pin cannot be read is kept.
    """
    try:
        current = mathlib_revision((root / "lake-manifest.json").read_text())
    except (OSError, UnicodeError):
        current = None
    if current is None or not revisions:
        return list(revisions)
    try:
        output = subprocess.run(
            ["git", "cat-file", "--batch"], cwd=root, check=True, stdout=subprocess.PIPE,
            input="".join(f"{revision}:lake-manifest.json\n" for revision in revisions).encode(),
        ).stdout
    except (OSError, subprocess.CalledProcessError):
        return list(revisions)
    kept = []
    position = 0
    for revision in revisions:
        end = output.find(b"\n", position)
        if end < 0:  # truncated answer: keep what could not be checked
            kept.append(revision)
            continue
        header = output[position:end].split()
        position = end + 1
        pinned = None
        if len(header) == 3 and header[1] == b"blob" and header[2].isdigit():
            size = int(header[2])
            pinned = mathlib_revision(output[position:position + size].decode(errors="replace"))
            position += size + 1
        if pinned is None or pinned == current:
            kept.append(revision)
    return kept


def one_origin(root, origin, work, missing):
    """This worker and all curl/Lake children share the parent's supervised group."""
    env = {**os.environ, "LAKE_CACHE_ARTIFACT_ENDPOINT": origin + "/a0",
           "LAKE_CACHE_REVISION_ENDPOINT": origin + "/r0"}
    toolchain = (root / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
    try:
        ancestors = candidate_revisions(root)
    except subprocess.CalledProcessError as error:
        print(f"Could not list candidate revisions for {origin}: {error}", flush=True)
        return 1
    revisions = same_mathlib(root, ancestors)
    if len(revisions) < len(ancestors):
        print(f"Skipping {len(ancestors) - len(revisions)} of {len(ancestors)} candidate ancestors "
              "that pin another Mathlib revision: their outputs cannot match this checkout.",
              flush=True)
        if not revisions:
            return NO_COMPATIBLE_ANCESTOR
    mapping = work / "map.jsonl"
    found = None
    checked = 0
    result = None
    for back, revision in enumerate(revisions):
        checked += 1
        mapping.unlink(missing_ok=True)
        result = subprocess.run([
            "curl", "--disable", "--fail", "--silent",
            "--connect-timeout", "5", "--max-time", "20", "--retry", "2",
            "--retry-max-time", "20", "--max-filesize", str(8 * 1024 * 1024),
            "--output", str(mapping), "--write-out", "%{http_code}",
            f"{origin}/r0/{SCOPE}/tc/{toolchain}/{revision}.jsonl"], cwd=root,
            stdout=subprocess.PIPE, text=True)
        if result.returncode == 0:
            found = (back, revision)
            break
        # Both 404 and 403 are taken to mean an unpublished revision; the public GCS bucket
        # answered 404 for one on 2026-11-17, and 403 for everything while public read is revoked.
        # Fail fast only on transport errors, timeouts, or 5xx/other errors.
        if result.stdout.strip() not in ("403", "404"):
            break
    if found is None:
        detail = (f"last lookup HTTP {result.stdout.strip() or 'unknown'}, "
                  f"curl exit {result.returncode}") if result is not None else "no revisions to check"
        print(f"No usable cached mapping among {checked} revisions at {origin} "
              f"({detail})", flush=True)
        return 1
    back, revision = found
    if missing:
        current = set()
        for trace in (root / ".lake/build").rglob("*.trace"):
            try:
                current.update(re.findall(r'"depHash": *"([0-9a-f]+)"', trace.read_text()))
            except (OSError, UnicodeError):
                pass
        try:
            lines = mapping.read_text().splitlines(keepends=True)
        except UnicodeError:
            print(f"Unreadable cached mapping for {revision} at {origin}", flush=True)
            return 1

        def already_current(line):
            try:
                row = json.loads(line)
            except ValueError:
                return False
            # Preserve unknown/malformed rows for Lake's parser, even if they
            # start with an input fingerprint already present in a local trace.
            return (isinstance(row, list) and len(row) == 2 and isinstance(row[0], str)
                    and row[0] in current and isinstance(row[1], str)
                    and re.fullmatch(r"[0-9a-f]{16}\.ltar", row[1]) is not None)

        needed = [line for line in lines if not already_current(line)]
        # Match the existing optimization: retain the original version/header and JSON rows;
        # native Lake still parses/verifies the mapping and output archives.
        mapping = work / "missing.jsonl"
        mapping.write_text("".join(needed))
        count = sum(line.startswith('["') for line in needed)
        total = sum(line.startswith('["') for line in lines)
        print(f"Remote cache: {revision} (candidate {back + 1}/{len(revisions)}) has outputs for "
              f"{total} modules; {count} of them are not current in .lake.", flush=True)
    else:
        total = sum(line.startswith(b'["') for line in mapping.read_bytes().splitlines())
        print(f"Remote cache: {revision} (candidate {back + 1}/{len(revisions)}) has outputs for "
              f"{total} modules.", flush=True)
    # Even an empty filtered mapping must pass Lake's version/syntax parser;
    # a 200 HTML error page must not suppress the next mirror.
    args = ["lake", "cache", "get", "--repo=" + SCOPE, str(mapping)]
    return subprocess.run(args, cwd=root, env=env).returncode


def restore(root, env, missing=False):
    if disabled(env):
        print("DISABLE_CACHE_RESTORE is set; skipping optional cache restoration.", flush=True)
        return False
    urls = origins(env)
    timeout = seconds(env, "COMPLEXITYLIB_CACHE_ORIGIN_TIMEOUT", 180)
    if not urls:
        print("COMPLEXITYLIB_CACHE_URL is empty; skipping the cslib-frontier cache.", flush=True)
        return False
    shallow = run(["git", "rev-parse", "--is-shallow-repository"], timeout=10,
                  cwd=root, env=env, capture_output=True)
    if shallow.returncode == 0 and shallow.stdout.strip() == "true":
        head = run(["git", "rev-parse", "HEAD"], timeout=10, cwd=root, env=env, capture_output=True)
        if head.returncode == 0:
            deepened = run(["git", "fetch", "--quiet", "--no-tags", "--depth=100", "origin",
                            head.stdout.strip()], timeout=30, cwd=root, env=env)
            if deepened.returncode:
                print("warning: could not deepen clone; using available history", file=sys.stderr)
    for index, origin in enumerate(urls, 1):
        print(f"cslib-frontier cache origin {index}/{len(urls)}: {origin}", flush=True)
        started = time.monotonic()
        with tempfile.TemporaryDirectory(prefix="cslib-frontier-cache-") as temporary:
            args = [sys.executable, "-B", str(Path(__file__).resolve()), "--one", origin,
                    "--work", temporary, "--checkout", str(root)]
            if missing:
                args.append("--missing")
            result = run(args, timeout=timeout, cwd=root, env=env)
        outcome = ("completed" if result.returncode == 0 else "timed out"
                   if result.returncode == 124 else "skipped"
                   if result.returncode == NO_COMPATIBLE_ANCESTOR
                   else f"failed (exit {result.returncode})")
        print(f"cslib-frontier cache origin {index}/{len(urls)}: {outcome} in "
              f"{time.monotonic() - started:.1f}s: {origin}", flush=True)
        if result.returncode == 0:
            return True
        if result.returncode == NO_COMPATIBLE_ANCESTOR:
            # The answer depends on the checkout alone, so no other origin can do better.
            print("note: no candidate ancestor shares this checkout's Mathlib revision; "
                  "lake build will compile missing outputs", flush=True)
            return False
        print("note: origin missed, failed or timed out; trying the next configured origin", flush=True)
    print("note: no configured origin completed restoration; lake build will compile missing outputs",
          file=sys.stderr, flush=True)
    return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--missing", action="store_true")
    parser.add_argument("--checkout", type=Path,
                        default=Path(os.environ.get("COMPLEXITYLIB_CACHE_CHECKOUT") or ROOT))
    parser.add_argument("--one", help=argparse.SUPPRESS)
    parser.add_argument("--work", type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.one is not None:
        return one_origin(args.checkout, args.one, args.work, args.missing)
    try:
        with interruptible():
            restore(args.checkout, os.environ, args.missing)
    except UnsafeShutdown as error:
        print(f"error: {error}", file=sys.stderr)
        return 125
    except KeyboardInterrupt:
        return 124
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"note: cache restoration unavailable; building from source: {error}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
