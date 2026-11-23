# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""Shared data layer for the codebase visualizations.

One pass over first-parent history records, for every commit that touches a `.lean` file, which
files changed and the blob each now points at. Every blob is read once and reduced to a small
`BlobInfo` (line counts, imports, declaration counts), cached by blob SHA, so the state of the
whole tree at any commit can be replayed cheaply.

Paths and module names from before the `Complexity` → `CslibFrontier` rename are rewritten to
their current spelling, so a file keeps one identity across the rename.
"""

from __future__ import annotations

import dataclasses
import datetime as dt
import hashlib
import json
import re
import subprocess
from collections import Counter
from pathlib import Path
from typing import Iterator

HERE = Path(__file__).resolve().parent
CACHE_VERSION = 1

# Old spelling → current spelling, longest first.
RENAMES = [
    ("ComplexityTests", "CslibFrontierTests"),
    ("ComplexityResults", "CslibFrontierResults"),
    ("Complexity", "CslibFrontier"),
]

LIBRARY_ROOT = "CslibFrontier/"

# Fixed area → colour-slot order (identity, never rank). Areas not listed fold into "Other".
AREAS = [
    "Computability",
    "Foundations",
    "Algorithms",
    "Crypto",
    "Logics",
    "DataStructure",
    "Probability",
]
OTHER = "Other"

DECL_KINDS = ("theorem", "lemma", "def", "abbrev", "instance", "structure", "inductive", "class")
_DECL_RE = re.compile(
    rb"^(?:@\[[^\]\n]*\]\s*)?"
    rb"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped)\s+)*"
    rb"(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b",
    re.MULTILINE,
)
_IMPORT_RE = re.compile(rb"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.']+)", re.MULTILINE)
_PR_RE = re.compile(r"\(#(\d+)\)\s*$")


def normalize_path(path: str) -> str:
    """Rewrite a pre-rename path to its current spelling."""
    for old, new in RENAMES:
        if path == old + ".lean" or path.startswith(old + "/"):
            return new + path[len(old):]
    return path


def normalize_module(name: str) -> str:
    for old, new in RENAMES:
        if name == old or name.startswith(old + "."):
            return new + name[len(old):]
    return name


def module_of(path: str) -> str:
    return path[: -len(".lean")].replace("/", ".")


def is_library(path: str) -> bool:
    return path.startswith(LIBRARY_ROOT)


def area_of(path: str) -> str:
    """Top-level library area of a path (`CslibFrontier/<Area>/...`), folded to `AREAS`."""
    parts = path.split("/")
    if len(parts) < 3 or not is_library(path):
        return OTHER
    return parts[1] if parts[1] in AREAS else OTHER


def subarea_of(path: str) -> str:
    """`<Area>/<Sub>` for a library path, or `<Area>` for files directly under an area."""
    parts = path.split("/")
    if len(parts) >= 4:
        return f"{parts[1]}/{parts[2]}"
    if len(parts) == 3:
        return parts[1]
    return "(root)"


@dataclasses.dataclass(frozen=True)
class BlobInfo:
    lines: int
    code: int  # non-blank lines outside comments (approximate; see `scan_blob`)
    imports: tuple[str, ...]
    decls: dict[str, int]

    def to_json(self) -> list:
        return [self.lines, self.code, list(self.imports), self.decls]

    @staticmethod
    def from_json(row: list) -> "BlobInfo":
        return BlobInfo(row[0], row[1], tuple(row[2]), row[3])


def scan_blob(data: bytes) -> BlobInfo:
    """Reduce a Lean source file to its metrics.

    `code` counts non-blank lines outside `--` line comments and `/- ... -/` block comments
    (docstrings included as comments); nesting is tracked, string literals are not.
    Declarations are counted by their unindented header keyword, the project's layout convention,
    on lines that start outside a comment.
    """
    lines = data.count(b"\n") + (0 if data.endswith(b"\n") or not data else 1)
    code = 0
    depth = 0
    code_lines: list[bytes] = []
    for raw in data.split(b"\n"):
        line = raw
        has_code = False
        i = 0
        n = len(line)
        while i < n:
            if depth:
                j = line.find(b"-/", i)
                k = line.find(b"/-", i)
                if k != -1 and (j == -1 or k < j):
                    depth += 1
                    i = k + 2
                elif j != -1:
                    depth -= 1
                    i = j + 2
                else:
                    break
            else:
                k = line.find(b"/-", i)
                c = line.find(b"--", i)
                end = n
                if c != -1 and (k == -1 or c < k):
                    end = c
                elif k != -1:
                    end = k
                if line[i:end].strip():
                    has_code = True
                if end == n or end == c:
                    break
                depth = 1
                i = k + 2
        if has_code:
            code += 1
            code_lines.append(raw)
    imports = tuple(normalize_module(m.decode()) for m in _IMPORT_RE.findall(data[:20000]))
    # Headers are matched on lines that start outside a comment, so prose is never counted.
    decls = Counter(m.decode() for m in _DECL_RE.findall(b"\n".join(code_lines)))
    return BlobInfo(lines, code, imports, dict(decls))


@dataclasses.dataclass
class Commit:
    sha: str
    time: int  # committer time, UTC epoch seconds
    author: str
    subject: str
    changes: list[tuple[str, str | None]]  # (normalized path, new blob sha or None if deleted)

    @property
    def date(self) -> dt.date:
        return dt.datetime.fromtimestamp(self.time, dt.timezone.utc).date()

    @property
    def pr(self) -> int | None:
        m = _PR_RE.search(self.subject)
        return int(m.group(1)) if m else None


def _git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True,
                          text=True).stdout


def merge_changes(raw: list[tuple[str, str | None]]) -> list[tuple[str, str | None]]:
    """Normalize and merge raw `(path, blob)` entries within one commit.

    A root-rename commit (`--no-renames`) emits both deletion of the old path and addition of the
    new one; keeping a live blob over `None` regardless of lexicographic path order preserves the
    file in `replay` and counts the commit once in `touches`."""
    merged: dict[str, str | None] = {}
    for path, blob in raw:
        p = normalize_path(path)
        if p not in merged or (blob is not None and (merged[p] is None or path == p)):
            merged[p] = blob
    return list(merged.items())


def read_commits(repo: Path, ref: str = "HEAD") -> list[Commit]:
    """First-parent commits touching `.lean` files, oldest first."""
    out = _git(repo, "log", "--reverse", "--first-parent", "--diff-merges=first-parent",
               "--no-renames", "--raw", "--no-abbrev", "--format=C%x00%H%x00%ct%x00%an%x00%s",
               ref, "--", "*.lean")
    commits: list[Commit] = []
    raw: list[tuple[str, str | None]] = []
    for line in out.splitlines():
        if line.startswith("C\x00"):
            if commits:
                commits[-1].changes = merge_changes(raw)
                raw = []
            _, sha, ct, an, subject = line.split("\x00", 4)
            commits.append(Commit(sha, int(ct), an, subject, []))
        elif line.startswith(":"):
            meta, path = line.split("\t", 1)
            fields = meta.split()
            new_sha, status = fields[3], fields[4]
            if fields[1] == "160000" or not path.endswith(".lean"):
                continue
            blob = None if status == "D" or set(new_sha) == {"0"} else new_sha
            raw.append((path, blob))
    if commits:
        commits[-1].changes = merge_changes(raw)
    return commits


class BlobCache:
    """`BlobInfo` by blob SHA, persisted as JSON under a fingerprint of the scanner source."""

    def __init__(self, path: Path):
        self.path = path
        fp = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()[:16]
        self.fingerprint = f"{CACHE_VERSION}-{fp}"
        self.data: dict[str, BlobInfo] = {}
        if path.exists():
            raw = json.loads(path.read_text())
            if raw.get("fingerprint") == self.fingerprint:
                self.data = {k: BlobInfo.from_json(v) for k, v in raw["blobs"].items()}

    def fill(self, repo: Path, shas: set[str]) -> None:
        missing = sorted(s for s in shas if s not in self.data)
        if not missing:
            return
        proc = subprocess.Popen(["git", "-C", str(repo), "cat-file", "--batch"],
                                stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        assert proc.stdin and proc.stdout
        import threading

        def feed():
            for s in missing:
                proc.stdin.write(s.encode() + b"\n")
            proc.stdin.close()

        threading.Thread(target=feed, daemon=True).start()
        for _ in missing:
            header = proc.stdout.readline().split()
            size = int(header[2])
            body = proc.stdout.read(size)
            proc.stdout.read(1)
            self.data[header[0].decode()] = scan_blob(body)
        proc.stdout.close()
        proc.wait()
        self.save()

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        tmp = self.path.with_suffix(".tmp")
        tmp.write_text(json.dumps({"fingerprint": self.fingerprint,
                                   "blobs": {k: v.to_json() for k, v in self.data.items()}}))
        tmp.replace(self.path)

    def __getitem__(self, sha: str) -> BlobInfo:
        return self.data[sha]


class History:
    """Replayable first-parent history of the repository's Lean files."""

    def __init__(self, repo: Path | str = ".", ref: str = "HEAD", cache: Path | None = None):
        self.repo = Path(_git(Path(repo).resolve(), "rev-parse", "--show-toplevel").strip())
        self.commits = read_commits(self.repo, ref)
        self.blobs = BlobCache(cache or HERE / ".cache" / "blobs.json")
        self.blobs.fill(self.repo, {b for c in self.commits for _, b in c.changes if b})

    def replay(self) -> Iterator[tuple[Commit, dict[str, str]]]:
        """Yield `(commit, tree)` after each commit; `tree` maps path → blob SHA and is mutated
        in place, so copy it to keep a snapshot."""
        tree: dict[str, str] = {}
        for c in self.commits:
            for path, blob in c.changes:
                if blob is None:
                    tree.pop(path, None)
                else:
                    tree[path] = blob
            yield c, tree

    def daily(self) -> list[tuple[dt.date, Commit, dict[str, str]]]:
        """The tree at the last commit of each UTC day that has one (snapshots are copies)."""
        out: list[tuple[dt.date, Commit, dict[str, str]]] = []
        for c, tree in self.replay():
            if out and out[-1][0] == c.date:
                out[-1] = (c.date, c, dict(tree))
            else:
                out.append((c.date, c, dict(tree)))
        return out

    def head(self) -> dict[str, str]:
        tree: dict[str, str] = {}
        for _, tree in self.replay():
            pass
        return dict(tree)

    def touches(self) -> Counter:
        """How many commits changed each (current-spelling) path."""
        return Counter(p for c in self.commits for p, _ in c.changes)


def import_graph(blobs: BlobCache, tree: dict[str, str], library_only: bool = True):
    """Module → set of imported in-tree modules for a snapshot."""
    mods = {module_of(p): b for p, b in tree.items() if not library_only or is_library(p)}
    return {m: {i for i in blobs[b].imports if i in mods} for m, b in mods.items()}


def topo_order(graph: dict[str, set[str]]) -> list[str]:
    """Modules with every import before its importers."""
    order: list[str] = []
    state: dict[str, int] = {}
    for root in graph:
        if root in state:
            continue
        stack = [(root, iter(graph[root]))]
        state[root] = 1
        while stack:
            node, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                stack.pop()
                state[node] = 2
                order.append(node)
            elif nxt not in state:
                state[nxt] = 1
                stack.append((nxt, iter(graph[nxt])))
    return order


def longest_chain(graph: dict[str, set[str]]) -> tuple[int, list[str]]:
    """Length (in modules) and one witness of the longest import chain in a DAG."""
    memo: dict[str, tuple[int, str | None]] = {}
    for node in topo_order(graph):
        best = max(((memo[d][0], d) for d in graph[node] if d in memo), default=(0, None))
        memo[node] = (best[0] + 1, best[1])
    if not memo:
        return 0, []
    start = max(memo, key=lambda m: memo[m][0])
    chain = [start]
    while memo[chain[-1]][1] is not None:
        chain.append(memo[chain[-1]][1])
    return memo[start][0], chain


def depths(graph: dict[str, set[str]]) -> dict[str, int]:
    """For each module, the number of modules on the longest import chain starting at it."""
    d: dict[str, int] = {}
    for m in topo_order(graph):
        d[m] = 1 + max((d[i] for i in graph[m]), default=0)
    return d


def reach(graph: dict[str, set[str]]) -> dict[str, int]:
    """For each module, how many modules import it directly or transitively."""
    order = topo_order(graph)
    idx = {m: i for i, m in enumerate(order)}
    importers: dict[str, list[str]] = {m: [] for m in graph}
    for m, deps in graph.items():
        for x in deps:
            importers[x].append(m)
    below: dict[str, int] = {}
    for m in reversed(order):  # importers first
        bits = 0
        for i in importers[m]:
            bits |= below[i] | (1 << idx[i])
        below[m] = bits
    return {m: below[m].bit_count() for m in graph}
