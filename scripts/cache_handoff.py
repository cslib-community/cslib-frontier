#!/usr/bin/env python3
"""Reuse a successful merge-group build on main, in a later merge group, or at a PR's base.

`restore` gives a push to main the build of its exact revision. `restore --ancestor` gives a
merge-group build the build of its nearest first-parent ancestor that has one, so that the
queue starts from the newest validated build instead of the caches that completed `main`
builds publish, which lag it. Lake then recompiles whatever the newer commits changed.
`restore --pr-base` looks up only the main parent of GitHub's checked-out PR merge commit.

This optional cache never replaces validation. Only the latest current attempt of the
authoritative Lean workflow may supply an artifact; misses leave the normal build to run.
Reusable root build outputs are validated and swapped as a unit, preserving Lake's
shared hardlinked artifacts and avoiding partially restored module/trace bundles.
Lake's transient module setup inputs and per-module `.ltar` publication archives are
omitted from handoff payloads; compilation recreates setup inputs when needed, and
swapping retains matching `.ltar` archives from any displaced local build.
"""

from __future__ import annotations

import argparse
from collections import OrderedDict
from contextlib import contextmanager
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
from urllib.parse import urlencode
import zlib

sys.path.insert(0, str(Path(__file__).resolve().parent / "cache"))
from bounded import UnsafeShutdown, interruptible, run as bounded_run  # noqa: E402


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW_FILE = "lean_action_ci.yml"
WORKFLOW_PATH = f".github/workflows/{WORKFLOW_FILE}"
INPUTS = ("lean-toolchain", "lake-manifest.json", "lakefile.toml")
# Payload bounds. On 2026-11-08 a full build was 101,848 files and 4.64 GB, packing to 1.67 GB;
# on 2026-11-21 a full build was 172,812 files and 7.53 GB, packing to 2.64 GB. These bounds
# keep ~2.9x file / ~2.9x raw / ~3.2x compressed headroom; a miss is reported as a workflow
# warning so that outgrowing them again is visible.
MAX_FILES = 500_000
MAX_BYTES = 20 * 1024 ** 3
MAX_ARCHIVE_BYTES = 8 * 1024 ** 3
MAX_METADATA_BYTES = 64 * 1024
# Download budget for an archive of up to MAX_ARCHIVE_BYTES, inside the step's 10 minutes.
DOWNLOAD_SECONDS = 480
# First-parent ancestors that `restore --ancestor` considers, nearest first. Every commit that
# lands through the queue has a handoff for two days, so the nearest one is normally one or two
# commits back: the tip of `main` when the group was formed, behind any queue entries ahead of it
# that are still building. Twenty is an operational choice, not a guarantee: it is meant to cover
# a long stacked queue and a run of failed packs, and it bounds a complete miss at one run listing
# per ancestor. Each listing is a `gh api` call with a 60-second limit, usually about a second, and
# the step's ten minutes bound the whole search whatever the API's latency.
ANCESTOR_LIMIT = 20
# Budget for deepening the depth-1 checkout far enough to see ANCESTOR_LIMIT ancestors.
DEEPEN_SECONDS = 60


class Rejected(RuntimeError):
    """The available evidence does not authorize reuse."""


def gh_get(endpoint: str, *, paginate: bool = False):
    command = [
        "gh", "api", "--hostname", "github.com", "--method", "GET",
        "-H", "Accept: application/vnd.github+json",
        "-H", "X-GitHub-Api-Version: 2022-11-28", endpoint,
    ]
    if paginate:
        command += ["--paginate", "--slurp"]
    result = subprocess.run(command, check=True, capture_output=True, text=True, timeout=60)
    return json.loads(result.stdout)


def gh_download_artifact(repository: str, run_id: int, artifact_name: str, destination: Path,
                         timeout: int = 120) -> None:
    command = [
        "gh", "run", "download", str(run_id),
        "--repo", repository,
        "--name", artifact_name,
        "--dir", str(destination),
    ]
    subprocess.run(command, check=True, capture_output=True, text=True, timeout=timeout)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Rejected(message)


def positive(value) -> bool:
    return type(value) is int and value > 0


def digest(path: Path) -> str:
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def directory(path: Path) -> None:
    require(stat.S_ISDIR(path.lstat().st_mode), f"Not a real directory: {path}")


def source_context(root: Path, env: dict, event: str) -> dict:
    recovery = str(env.get("DISABLE_CACHE_RESTORE", "")).strip().lower()
    require(recovery in ("", "0", "false", "no"),
            "Build handoff is disabled during cache recovery")
    disabled = str(env.get("DISABLE_BUILD_HANDOFF", "")).strip().lower()
    require(disabled in ("", "0", "false", "no"), "Build handoff is disabled by DISABLE_BUILD_HANDOFF")
    require(env.get("GITHUB_EVENT_NAME") == event, f"Expected {event} event")
    if event == "push":
        require(env.get("GITHUB_REF") == "refs/heads/main", "Not a push to main")
    repository, sha = env.get("GITHUB_REPOSITORY", ""), env.get("GITHUB_SHA", "")
    require(bool(re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository)),
            "Invalid repository")
    require(bool(re.fullmatch(r"[0-9a-f]{40}", sha)), "Invalid source SHA")
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    require(head == sha, "Checkout does not match event SHA")
    dirty = subprocess.check_output(
        ["git", "status", "--porcelain", "--untracked-files=no"], cwd=root, text=True,
    )
    require(not dirty.strip(), "Tracked sources are modified")
    # Exclude ImageVersion so simultaneous GitHub runner-image patch rollouts (e.g.
    # standard 4-core ubuntu-24.04 vs cslib-ubuntu-24.04-8core) share validated handoffs on
    # the same OS/ABI. lakefile.toml also sets platformIndependent = true for .olean/.ir outputs.
    platform = {key: env.get(key, "")
                for key in ("RUNNER_OS", "RUNNER_ARCH", "ImageOS")}
    require(all(isinstance(value, str) and value for value in platform.values()),
            "Runner platform is unknown")
    generation = env.get("CACHE_RECOVERY_GENERATION", "") or "0"
    require(isinstance(generation, str)
            and bool(re.fullmatch(r"[A-Za-z0-9_.-]{1,64}", generation)),
            "Invalid cache recovery generation")
    return {"version": 1, "repository": repository, "source_sha": sha,
            "cache_recovery_generation": generation,
            "inputs": {name: digest(root / name) for name in INPUTS}, "platform": platform}


def first_parents(root: Path) -> list[str]:
    """The checked-out commit and at most ANCESTOR_LIMIT first-parent ancestors, nearest first."""
    return subprocess.check_output(
        ["git", "rev-list", "--first-parent", "-n", str(ANCESTOR_LIMIT + 1), "HEAD"],
        cwd=root, text=True).split()


def deepen_history(root: Path, sha: str) -> None:
    """Fetch the history that ANCESTOR_LIMIT first-parent ancestors need, when it is missing.

    CI checks out one commit. As in scripts/cache/restore.py, a failed or timed-out fetch only
    leaves fewer ancestors to consider. The fetch runs only while the checkout holds too few
    commits, so it cannot shorten history that is already there.

    Git's transport helpers are separate processes that a timeout on `git` alone would leave
    running, so the fetch runs under the cache scripts' supervisor (scripts/cache/bounded.py): on
    a timeout, or when the step is cancelled, its whole process group is stopped before this
    returns. `UnsafeShutdown` means that could not be confirmed; it is not a miss, and the caller
    must not go on to download or install.
    """
    shallow = subprocess.check_output(["git", "rev-parse", "--is-shallow-repository"],
                                      cwd=root, text=True).strip()
    if shallow != "true" or len(first_parents(root)) > ANCESTOR_LIMIT:
        return
    with interruptible():
        result = bounded_run(["git", "fetch", "--quiet", "--no-tags",
                              f"--depth={ANCESTOR_LIMIT + 1}", "origin", sha],
                             timeout=DEEPEN_SECONDS, cwd=root, capture_output=True)
    if result.returncode:
        outcome = ("timed out" if result.returncode == 124
                   else f"failed (exit {result.returncode}): {(result.stderr or '').strip()}")
        print(f"Build handoff could not deepen the checkout; using available history: {outcome}")


def ancestor_contexts(root: Path, env: dict) -> list[dict]:
    """Contexts for the handoffs a merge-group build may reuse, nearest ancestor first.

    Each context is the current merge group's own (the same switches, repository, runner
    platform, recovery generation and, read from this checkout, input digests) with
    `source_sha` naming a first-parent ancestor of the checked-out commit. Every check that
    takes a context therefore accepts only that ancestor's merge-group run and an artifact
    recorded for that ancestor whose toolchain, manifest and lakefile equal the current ones.
    """
    current = source_context(root, env, "merge_group")
    chain = first_parents(root)
    require(bool(chain) and chain[0] == current["source_sha"]
            and all(re.fullmatch(r"[0-9a-f]{40}", sha) for sha in chain)
            and len(set(chain)) == len(chain) <= ANCESTOR_LIMIT + 1,
            "Malformed first-parent history")
    return [{**current, "source_sha": sha} for sha in chain[1:]]


def artifact_name(context: dict, run_id: int, attempt: int) -> str:
    """Advertise the same compatibility evidence that unpack() independently verifies."""
    encoded = json.dumps(context, sort_keys=True, separators=(",", ":")).encode()
    fingerprint = hashlib.sha256(encoded).hexdigest()
    return f"lean-build-{context['source_sha']}-{run_id}-{attempt}-{fingerprint}"


_ZERO_PAD = b"\0" * 512
_OMITTED_IR_SUFFIXES = (".setup.json", ".irsetup.json", ".ltar", ".ltar.hash")
_MODULE_HASH_COMPANIONS = (
    "lib/lean/{rel}.ir.trace",
    "lib/lean/{rel}.olean.server.hash",
    "lib/lean/{rel}.olean.private.hash",
    "lib/lean/{rel}.ilean.hash",
    "lib/lean/{rel}.ir.sig.hash",
    "lib/lean/{rel}.ir.hash",
    "ir/{rel}.c.hash",
    "ir/{rel}.bc.hash",
)
_MODULE_ARTIFACT_COMPANIONS = (
    "lib/lean/{rel}.olean.server",
    "lib/lean/{rel}.olean.private",
    "lib/lean/{rel}.ilean",
    "lib/lean/{rel}.ir.sig",
    "lib/lean/{rel}.ir",
    "ir/{rel}.c",
    "ir/{rel}.bc",
)


def omitted_build_output(path: Path | str) -> bool:
    """Recognize transient setup inputs and per-module `.ltar` archives under `ir/`.

    Lake's `Module.setupFile`/`irSetupFile` (`ir/**/*.setup.json`, `ir/**/*.irsetup.json`) are
    written inside compile actions and unused when reusing completed modules. Per-module
    publication archives (`ir/**/*.ltar` and their cached `ir/**/*.ltar.hash` files) are only
    consumed by `publish.py stage` on `main`, where matching archives are carried forward from
    the displaced `.lake/build` snapshot instead of shipped in every merge-group handoff.
    Other JSON outputs and every compiled module artifact, hash and trace remain in the handoff.
    """
    posix = path.as_posix() if isinstance(path, Path) else path
    parts = posix.split("/")
    return len(parts) > 1 and parts[0] == "ir" and parts[-1].endswith(_OMITTED_IR_SUFFIXES)


class _CountingWriter:
    """Track stream byte offset for `tarfile.TarFile` without `tarfile._Stream` buffering."""

    def __init__(self, raw):
        self._raw = raw
        self.pos = 0

    def tell(self) -> int:
        return self.pos

    def write(self, data) -> int:
        n = len(data)
        self._raw.write(data)
        self.pos += n
        return n

    def flush(self) -> None:
        self._raw.flush()


class _ForwardStream:
    """Expose a forward-only decompressed stream to `tarfile.TarFile` without double-buffering."""

    def __init__(self, raw):
        self._raw = raw
        self.pos = 0

    def tell(self) -> int:
        return self.pos

    def read(self, size: int = -1) -> bytes:
        try:
            if size == 0:
                return b""
            if size < 0:
                data = self._raw.read()
                self.pos += len(data)
                return data
            chunk = self._raw.read(size)
            if len(chunk) == size or not chunk:
                self.pos += len(chunk)
                return chunk
            parts = [chunk]
            rem = size - len(chunk)
            while rem > 0:
                more = self._raw.read(rem)
                if not more:
                    break
                parts.append(more)
                rem -= len(more)
            data = b"".join(parts)
            self.pos += len(data)
            return data
        except zlib.error as exc:
            raise tarfile.ReadError(str(exc)) from exc

    def seek(self, target: int, whence: int = io.SEEK_SET) -> int:
        if whence != io.SEEK_SET or target < self.pos:
            raise OSError("Backward seek on forward-only tar stream")
        skip = target - self.pos
        while skip > 0:
            chunk = self.read(min(1024 * 1024, skip))
            if not chunk:
                break
            skip -= len(chunk)
        return self.pos


@contextmanager
def gzip_bundle(archive: Path):
    """Stream the existing tar format through parallel compression workers where available."""
    pigz = shutil.which("pigz")
    if not pigz:
        print("Handoff compression: Python gzip, level 1", flush=True)
        with archive.open("wb") as raw, gzip.GzipFile(
                filename="", mode="wb", fileobj=raw, compresslevel=1, mtime=0) as gz, \
                io.BufferedWriter(gz, buffer_size=4 * 1024 * 1024) as buffered:
            writer = _CountingWriter(buffered)
            with tarfile.TarFile(fileobj=writer, mode="w") as bundle:
                yield bundle
        return
    workers = min(8, max(1, os.cpu_count() or 4))
    print(f"Handoff compression: pigz, level 1, {workers} workers", flush=True)
    with archive.open("wb") as output, subprocess.Popen(
            [pigz, "-n", "-1", "-p", str(workers), "-c"], stdin=subprocess.PIPE, stdout=output,
            bufsize=4 * 1024 * 1024, env={**os.environ, "PIGZ": "", "GZIP": ""}) as compressor:
        assert compressor.stdin is not None
        with compressor.stdin as stream:
            writer = _CountingWriter(stream)
            with tarfile.TarFile(fileobj=writer, mode="w") as bundle:
                yield bundle
        status = compressor.wait()
        if status:
            raise subprocess.CalledProcessError(status, compressor.args)


@contextmanager
def open_gzip_tar_reader(archive: Path):
    """Stream tar decompression through `pigz` when available, else Python `gzip`."""
    pigz = shutil.which("pigz")
    if not pigz:
        with gzip.open(archive, "rb") as raw:
            aborted = False
            try:
                stream = _ForwardStream(raw)
                with tarfile.TarFile(fileobj=stream, mode="r") as bundle:
                    yield bundle
            except BaseException:
                aborted = True
                raise
            finally:
                if not aborted:
                    try:
                        while raw.read(1024 * 1024):
                            pass
                    except zlib.error as exc:
                        raise tarfile.ReadError(str(exc)) from exc
        return
    decompressor = subprocess.Popen(
        [pigz, "-d", "-c", str(archive)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        bufsize=4 * 1024 * 1024,
        env={**os.environ, "PIGZ": "", "GZIP": ""},
    )
    aborted = False
    try:
        assert decompressor.stdout is not None
        stream = _ForwardStream(decompressor.stdout)
        with tarfile.TarFile(fileobj=stream, mode="r") as bundle:
            yield bundle
    except BaseException:
        aborted = True
        raise
    finally:
        if aborted:
            if decompressor.stdout is not None:
                decompressor.stdout.close()
            if decompressor.poll() is None:
                decompressor.terminate()
                try:
                    decompressor.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    decompressor.kill()
                    decompressor.wait()
            else:
                decompressor.wait()
            if decompressor.stderr is not None:
                decompressor.stderr.close()
        else:
            # Drain any trailing tar zero-block padding so pigz verifies the full gzip CRC/trailer
            # and exits 0 instead of receiving SIGPIPE.
            if decompressor.stdout is not None:
                while decompressor.stdout.read(1024 * 1024):
                    pass
                decompressor.stdout.close()
            stderr_bytes = decompressor.stderr.read() if decompressor.stderr is not None else b""
            if decompressor.stderr is not None:
                decompressor.stderr.close()
            status = decompressor.wait()
            if status:
                stderr = stderr_bytes.decode("utf-8", "replace").strip()
                raise tarfile.ReadError(f"pigz decompression failed (exit {status}): {stderr}")


def _scan_build_outputs(build: Path) -> tuple[list[tuple[str, str, os.stat_result]], int, int]:
    files: list[tuple[str, str, os.stat_result]] = []
    omitted_files = omitted_bytes = 0

    def walk(abs_dir: str, rel_prefix: str) -> None:
        nonlocal omitted_files, omitted_bytes
        with os.scandir(abs_dir) as it:
            entries = sorted(it, key=lambda item: item.name)
        for entry in entries:
            info = entry.stat(follow_symlinks=False)
            mode = info.st_mode
            rel = f"{rel_prefix}{entry.name}"
            if stat.S_ISDIR(mode):
                walk(entry.path, f"{rel}/")
                continue
            require(stat.S_ISREG(mode), f"Non-regular build output: {entry.path}")
            # Validate the file type before omitting anything: setup- or archive-named links
            # are rejected by the same boundary checks as every other build entry.
            if omitted_build_output(rel):
                omitted_files += 1
                omitted_bytes += info.st_size
                continue
            files.append((entry.path, f".lake/build/{rel}", info))

    walk(str(build), "")
    return files, omitted_files, omitted_bytes


def pack(root: Path, output: Path, env: dict) -> str:
    context = source_context(root, env, "merge_group")
    run_id, attempt = (int(env.get(key, "0")) for key in ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT"))
    require(positive(run_id) and positive(attempt), "Invalid producer run identity")
    require(not output.resolve().is_relative_to(root.resolve()),
            "Handoff output must be outside the checkout")
    require(not output.exists() and not output.is_symlink(), "Handoff output already exists")
    directory(root / ".lake")
    build = root / ".lake/build"
    directory(build)
    files, omitted_files, omitted_bytes = _scan_build_outputs(build)
    total = sum(info.st_size for _, _, info in files)
    require(0 < len(files) <= MAX_FILES and 0 < total <= MAX_BYTES,
            f"Build output count or size is outside handoff limits: {len(files)} files / "
            f"{total} bytes (limits {MAX_FILES} files / {MAX_BYTES} bytes; omitted "
            f"{omitted_files} setup/archive files / {omitted_bytes} bytes)")
    output.parent.mkdir(parents=True, exist_ok=True)
    open_ro = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    with tempfile.TemporaryDirectory(prefix="lean-handoff-pack-", dir=output.parent) as temp:
        stage = Path(temp)
        archive = stage / "build.tar.gz"
        with gzip_bundle(archive) as bundle:
            writer = bundle.fileobj
            assert isinstance(writer, _CountingWriter)
            fmt, enc, errs = bundle.format, bundle.encoding, bundle.errors
            for fpath, arcname, info in files:
                # Write every regular file's bytes, including hardlinks to Lake's artifact
                # cache. The archive must not contain links into another checkout/cache.
                size = info.st_size
                member = tarfile.TarInfo(arcname)
                member.size = size
                member.mode = 0o755 if info.st_mode & 0o111 else 0o644
                member.mtime = int(info.st_mtime)
                writer.write(member.tobuf(fmt, enc, errs))
                if size:
                    fd = os.open(fpath, open_ro)
                    try:
                        fstat = os.fstat(fd)
                        require(stat.S_ISREG(fstat.st_mode), f"Non-regular build output: {fpath}")
                        remaining = size
                        while remaining > 0:
                            chunk = os.read(fd, min(1024 * 1024, remaining))
                            require(bool(chunk), f"Build output truncated while packing: {fpath}")
                            writer.write(chunk)
                            remaining -= len(chunk)
                        require(not os.read(fd, 1), f"Build output grew while packing: {fpath}")
                    finally:
                        os.close(fd)
                    pad = (-size) & 511
                    if pad:
                        writer.write(_ZERO_PAD[:pad])
                bundle.offset = writer.pos
        compressed = archive.stat().st_size
        require(compressed <= MAX_ARCHIVE_BYTES,
                f"Handoff archive is too large: {compressed} bytes (limit {MAX_ARCHIVE_BYTES})")
        require(source_context(root, env, "merge_group") == context,
                "Sources changed while packing the build")
        metadata = {**context, "producer": {"event": "merge_group", "run_id": run_id,
                                            "run_attempt": attempt},
                    "archive": {"sha256": digest(archive), "files": len(files), "bytes": total,
                                "compressed_bytes": compressed}}
        (stage / "metadata.json").write_text(json.dumps(metadata, sort_keys=True) + "\n")
        stage.rename(output)
    name = artifact_name(context, run_id, attempt)
    if env.get("GITHUB_OUTPUT"):
        with Path(env["GITHUB_OUTPUT"]).open("a") as handle:
            handle.write(f"artifact-name={name}\n")
    print(f"Build handoff packed: {len(files)} files / {total} bytes, "
          f"{compressed} compressed bytes; omitted {omitted_files} setup/archive files / "
          f"{omitted_bytes} bytes ({name})")
    return name


def check_run(run: dict, context: dict, workflow_id: int) -> None:
    require(isinstance(run, dict), "Malformed workflow run")
    require(run.get("head_sha") == context["source_sha"] and run.get("event") == "merge_group",
            "Run is not the exact-source merge group")
    branch = run.get("head_branch", "")
    require(isinstance(branch, str) and branch.startswith("gh-readonly-queue/main/")
            and len(branch) > len("gh-readonly-queue/main/"), "Run is not from the main merge queue")
    require(run.get("workflow_id") == workflow_id and run.get("path") == WORKFLOW_PATH,
            "Wrong Lean workflow identity")
    repo, head = run.get("repository"), run.get("head_repository")
    require(isinstance(repo, dict) and isinstance(head, dict), "Missing run repositories")
    require(repo.get("full_name") == context["repository"]
            and head.get("full_name") == context["repository"]
            and positive(repo.get("id")) and repo.get("id") == head.get("id"),
            "Run came from another repository")
    require(all(positive(run.get(key)) for key in ("id", "run_number", "run_attempt")),
            "Malformed run identity")


def latest_success(api, context: dict, workflow_id: int) -> dict:
    repository = context["repository"]
    query = urlencode({"head_sha": context["source_sha"], "event": "merge_group", "per_page": 100})
    pages = api(f"repos/{repository}/actions/workflows/{workflow_id}/runs?{query}", paginate=True)
    require(isinstance(pages, list) and bool(pages), "Malformed run listing")
    runs = []
    for page in pages:
        require(isinstance(page, dict) and isinstance(page.get("workflow_runs"), list),
                "Malformed run page")
        runs.extend(page["workflow_runs"])
    require(bool(runs) and all(page.get("total_count") == len(runs) for page in pages),
            "No complete exact-source merge-group listing")
    for run in runs:
        check_run(run, context, workflow_id)
    require(len({run["id"] for run in runs}) == len(runs)
            and len({run["run_number"] for run in runs}) == len(runs), "Ambiguous latest run")
    selected = max(runs, key=lambda run: run["run_number"])
    current = api(f"repos/{repository}/actions/runs/{selected['id']}")
    check_run(current, context, workflow_id)
    require(current["id"] == selected["id"] and current["run_number"] == selected["run_number"]
            and current["run_attempt"] >= selected["run_attempt"], "Run identity changed")
    require(current.get("status") == "completed" and current.get("conclusion") == "success",
            "Latest current merge-group attempt has not succeeded")
    return current


def find_artifact(api, context: dict, run: dict) -> dict:
    name = artifact_name(context, run["id"], run["run_attempt"])
    pages = api(f"repos/{context['repository']}/actions/runs/{run['id']}/artifacts?per_page=100",
                paginate=True)
    require(isinstance(pages, list) and bool(pages), "Malformed artifact listing")
    artifacts = []
    for page in pages:
        require(isinstance(page, dict) and isinstance(page.get("artifacts"), list),
                "Malformed artifact page")
        artifacts.extend(page["artifacts"])
    require(all(page.get("total_count") == len(artifacts) for page in pages),
            "Incomplete artifact listing")
    require(all(isinstance(item, dict) for item in artifacts), "Malformed artifact record")
    matches = [item for item in artifacts if item.get("name") == name]
    require(len(matches) == 1, "Missing or ambiguous compatible run-attempt artifact")
    artifact = matches[0]
    require(positive(artifact.get("id")) and artifact.get("expired") is False
            and positive(artifact.get("size_in_bytes"))
            and artifact["size_in_bytes"] <= MAX_ARCHIVE_BYTES + MAX_METADATA_BYTES,
            "Artifact expired or exceeds handoff limits")
    identity = artifact.get("workflow_run")
    require(isinstance(identity, dict) and identity.get("id") == run["id"]
            and identity.get("head_sha") == context["source_sha"]
            and identity.get("repository_id") == run["repository"]["id"]
            and identity.get("head_repository_id") == run["head_repository"]["id"],
            "Artifact run identity mismatch")
    return artifact


_DIR_FD_CACHE_LIMIT = 64
_USE_DIR_FD = os.name == "posix"


def _extract_stream_to_fd(stream: _ForwardStream, fd: int, size: int) -> None:
    remaining = size
    while remaining > 0:
        chunk = stream.read(min(1024 * 1024, remaining))
        if not chunk:
            raise tarfile.ReadError("unexpected end of data")
        written = os.write(fd, chunk)
        while written < len(chunk):
            written += os.write(fd, memoryview(chunk)[written:])
        remaining -= len(chunk)
    pad = (-size) & 511
    if pad and len(stream.read(pad)) != pad:
        raise tarfile.ReadError("unexpected end of padding")


def unpack(download: Path, stage: Path, context: dict, run: dict) -> Path:
    require({path.name for path in download.iterdir()} == {"metadata.json", "build.tar.gz"},
            "Unexpected artifact contents")
    archive, manifest = download / "build.tar.gz", download / "metadata.json"
    for path, limit in ((archive, MAX_ARCHIVE_BYTES), (manifest, MAX_METADATA_BYTES)):
        info = path.lstat()
        require(stat.S_ISREG(info.st_mode) and 0 < info.st_size <= limit,
                "Artifact file is not regular or exceeds handoff limits")
    metadata = json.loads(manifest.read_text())
    require(isinstance(metadata, dict)
            and all(metadata.get(key) == value for key, value in context.items()),
            "Artifact source, configuration or platform mismatch")
    require(metadata.get("producer") == {"event": "merge_group", "run_id": run["id"],
                                         "run_attempt": run["run_attempt"]},
            "Artifact producer attempt mismatch")
    inventory = metadata.get("archive")
    require(isinstance(inventory, dict) and positive(inventory.get("files"))
            and inventory["files"] <= MAX_FILES and positive(inventory.get("bytes"))
            and inventory["bytes"] <= MAX_BYTES
            and inventory.get("compressed_bytes") == archive.stat().st_size
            and inventory.get("sha256") == digest(archive), "Invalid archive inventory or digest")
    expected_files, expected_bytes = inventory["files"], inventory["bytes"]
    seen, size = set(), 0
    current_umask = os.umask(0o022)
    os.umask(current_umask)
    open_flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0)
    use_dir_fd = _USE_DIR_FD
    dir_flags = (os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
                 | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0))
    root_fd: int | None = None
    dir_fds: OrderedDict[str, int] = OrderedDict()
    created_dirs: set[str] = set()

    def ensure_root_fd() -> int:
        nonlocal root_fd
        if root_fd is None:
            stage.mkdir(parents=True, exist_ok=True)
            root_fd = os.open(stage, dir_flags)
        return root_fd

    def get_dir_fd(rel_dir: str) -> int:
        if not rel_dir:
            return ensure_root_fd()
        cached = dir_fds.get(rel_dir)
        if cached is not None:
            dir_fds.move_to_end(rel_dir)
            return cached
        missing: list[tuple[str, str]] = []
        cur = rel_dir
        parent_fd: int | None = None
        while cur:
            fd = dir_fds.get(cur)
            if fd is not None:
                dir_fds.move_to_end(cur)
                parent_fd = fd
                break
            parent_rel, _, base = cur.rpartition("/")
            missing.append((cur, base))
            cur = parent_rel
        if parent_fd is None:
            parent_fd = ensure_root_fd()
        limit = max(1, _DIR_FD_CACHE_LIMIT)
        for full_rel, base in reversed(missing):
            try:
                os.mkdir(base, 0o755, dir_fd=parent_fd)
            except FileExistsError:
                pass
            try:
                child_fd = os.open(base, dir_flags, dir_fd=parent_fd)
            except (NotADirectoryError, FileExistsError, IsADirectoryError, PermissionError) as exc:
                raise Rejected("Unsafe or duplicate archive member") from exc
            dir_fds[full_rel] = child_fd
            while len(dir_fds) > limit:
                evicted_key, evicted_fd = next(
                    (k, v) for k, v in dir_fds.items() if k != full_rel
                )
                del dir_fds[evicted_key]
                os.close(evicted_fd)
            parent_fd = child_fd
        return parent_fd

    try:
        with open_gzip_tar_reader(archive) as bundle:
            stream = bundle.fileobj
            assert isinstance(stream, _ForwardStream)
            for member in bundle:
                name = member.name
                parts = name.split("/")
                require(member.type in (tarfile.REGTYPE, tarfile.AREGTYPE)
                        and member.sparse is None
                        and not bundle.pax_headers
                        and not any(key.startswith("GNU.sparse") for key in member.pax_headers)
                        and "\\" not in name
                        and parts[:2] == [".lake", "build"] and len(parts) > 2
                        and all(part not in ("", ".", "..") for part in parts)
                        and name not in seen, "Unsafe or duplicate archive member")
                seen.add(name)
                msize = member.size
                size += msize
                require(0 <= msize <= MAX_BYTES and len(seen) <= expected_files
                        and size <= expected_bytes, "Archive exceeds its declared inventory")
                padded = (msize + 511) & ~511
                require(member.offset_data == stream.pos and bundle.offset == stream.pos + padded,
                        "Unsafe or duplicate archive member")
                mtime = member.mtime
                require(type(mtime) in (int, float) and 0 <= mtime <= 2 ** 32,
                        "Invalid archive timestamp")
                mode = 0o755 if member.mode & 0o111 else 0o644
                rel_dir, _, fname = name.rpartition("/")
                if use_dir_fd:
                    dfd = get_dir_fd(rel_dir)
                    try:
                        fd = os.open(fname, open_flags, mode, dir_fd=dfd)
                    except (FileExistsError, IsADirectoryError, NotADirectoryError,
                            PermissionError) as exc:
                        raise Rejected("Unsafe or duplicate archive member") from exc
                else:
                    try:
                        if rel_dir not in created_dirs:
                            (stage / rel_dir).mkdir(parents=True, exist_ok=True)
                            created_dirs.add(rel_dir)
                        fd = os.open(stage / name, open_flags, mode)
                    except (FileExistsError, IsADirectoryError, NotADirectoryError,
                            PermissionError) as exc:
                        raise Rejected("Unsafe or duplicate archive member") from exc
                try:
                    if msize:
                        _extract_stream_to_fd(stream, fd, msize)
                    require(stream.pos == bundle.offset, "Archive framing mismatch")
                    if use_dir_fd and (mode & current_umask):
                        os.fchmod(fd, mode)
                    if not use_dir_fd:
                        os.chmod(stage / name, mode)
                        os.utime(stage / name, (mtime, mtime))
                    else:
                        os.utime(fd, (mtime, mtime))
                finally:
                    os.close(fd)
            require(not bundle.pax_headers, "Unsafe or duplicate archive member")
    finally:
        for fd in dir_fds.values():
            os.close(fd)
        if root_fd is not None:
            os.close(root_fd)
    require(len(seen) == expected_files and size == expected_bytes,
            "Archive inventory mismatch")
    return stage / ".lake/build"


def _lstat_or_none(path: str) -> os.stat_result | None:
    try:
        return os.lstat(path)
    except FileNotFoundError:
        return None


def _read_regular_nofollow(path: str, expected_size: int) -> bytes | None:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    try:
        fd = os.open(path, flags)
    except OSError:
        return None
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode) or info.st_size != expected_size:
            return None
        if expected_size == 0:
            return b"" if not os.read(fd, 1) else None
        chunks = []
        remaining = expected_size
        while remaining > 0:
            chunk = os.read(fd, min(1024 * 1024, remaining))
            if not chunk:
                return None
            chunks.append(chunk)
            remaining -= len(chunk)
        if os.read(fd, 1):
            return None
        return chunks[0] if len(chunks) == 1 else b"".join(chunks)
    except OSError:
        return None
    finally:
        os.close(fd)


def _same_regular_bytes(path_a: str, path_b: str) -> bool:
    info_a, info_b = _lstat_or_none(path_a), _lstat_or_none(path_b)
    if info_a is None or info_b is None:
        return False
    if not (stat.S_ISREG(info_a.st_mode) and stat.S_ISREG(info_b.st_mode)):
        return False
    if info_a.st_size != info_b.st_size:
        return False
    bytes_a = _read_regular_nofollow(path_a, info_a.st_size)
    if bytes_a is None:
        return False
    bytes_b = _read_regular_nofollow(path_b, info_b.st_size)
    return bytes_b is not None and bytes_a == bytes_b


def _check_real_dir_chain(root_str: str, parts: list[str], cache: dict[str, bool],
                          *, create_missing: bool) -> bool:
    cur = root_str
    root_ok = cache.get(cur)
    if root_ok is None:
        info = _lstat_or_none(cur)
        root_ok = info is not None and stat.S_ISDIR(info.st_mode)
        cache[cur] = root_ok
    if not root_ok:
        return False
    for part in parts:
        cur = f"{cur}/{part}"
        cached = cache.get(cur)
        if cached is False:
            return False
        if cached is True:
            continue
        info = _lstat_or_none(cur)
        if info is None:
            if not create_missing:
                return False
            os.mkdir(cur, 0o755)
            cache[cur] = True
            continue
        ok = stat.S_ISDIR(info.st_mode)
        cache[cur] = ok
        if not ok:
            return False
    return True


def _module_outputs_match(backup_str: str, staged_str: str, rel: str,
                          dir_cache: dict[str, bool]) -> bool:
    parts = rel.split("/")
    if any(part in ("", ".", "..") for part in parts):
        return False
    dir_parts = parts[:-1]
    if not _check_real_dir_chain(backup_str, ["lib", "lean", *dir_parts],
                                 dir_cache, create_missing=False):
        return False
    if not _check_real_dir_chain(staged_str, ["lib", "lean", *dir_parts],
                                 dir_cache, create_missing=False):
        return False
    # Check existing `staged/ir/...` prefixes are never symlinks/files even if subdirs are absent.
    cur = staged_str
    for part in ("ir", *dir_parts):
        cur = f"{cur}/{part}"
        info = _lstat_or_none(cur)
        if info is None:
            break
        if not stat.S_ISDIR(info.st_mode):
            return False
    olean_a = _lstat_or_none(f"{backup_str}/lib/lean/{rel}.olean")
    olean_b = _lstat_or_none(f"{staged_str}/lib/lean/{rel}.olean")
    if (olean_a is None or olean_b is None
            or not (stat.S_ISREG(olean_a.st_mode) and stat.S_ISREG(olean_b.st_mode))
            or olean_a.st_size <= 0 or olean_a.st_size != olean_b.st_size):
        return False
    if not _same_regular_bytes(f"{backup_str}/lib/lean/{rel}.trace",
                               f"{staged_str}/lib/lean/{rel}.trace"):
        return False
    if not _same_regular_bytes(f"{backup_str}/lib/lean/{rel}.olean.hash",
                               f"{staged_str}/lib/lean/{rel}.olean.hash"):
        return False
    for tmpl in _MODULE_HASH_COMPANIONS:
        sub = tmpl.format(rel=rel)
        pa, pb = f"{backup_str}/{sub}", f"{staged_str}/{sub}"
        ia, ib = _lstat_or_none(pa), _lstat_or_none(pb)
        if (ia is None) != (ib is None):
            return False
        if ia is not None and not _same_regular_bytes(pa, pb):
            return False
    for tmpl in _MODULE_ARTIFACT_COMPANIONS:
        sub = tmpl.format(rel=rel)
        ia = _lstat_or_none(f"{backup_str}/{sub}")
        ib = _lstat_or_none(f"{staged_str}/{sub}")
        if (ia is None) != (ib is None):
            return False
        if ia is not None and (not (stat.S_ISREG(ia.st_mode) and stat.S_ISREG(ib.st_mode))
                               or ia.st_size != ib.st_size):
            return False
    return True


def _carry_forward_ltar(src_path: str, src_info: os.stat_result, dst_path: str) -> bool:
    try:
        os.link(src_path, dst_path)
        return True
    except OSError:
        pass
    tmp_path = f"{dst_path}.handoff-tmp-{os.getpid()}"
    open_ro = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    open_wo = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0)
    src_fd = os.open(src_path, open_ro)
    try:
        verified = os.fstat(src_fd)
        if not stat.S_ISREG(verified.st_mode) or verified.st_size != src_info.st_size:
            return False
        dst_fd = os.open(tmp_path, open_wo, 0o444)
        try:
            remaining = verified.st_size
            while remaining > 0:
                chunk = os.read(src_fd, min(1024 * 1024, remaining))
                if not chunk:
                    raise OSError("Truncated .ltar during fallback copy")
                written = os.write(dst_fd, chunk)
                while written < len(chunk):
                    written += os.write(dst_fd, memoryview(chunk)[written:])
                remaining -= len(chunk)
            os.utime(dst_fd, ns=(verified.st_atime_ns, verified.st_mtime_ns))
        finally:
            os.close(dst_fd)
        os.replace(tmp_path, dst_path)
        return True
    except OSError:
        try:
            os.unlink(tmp_path)
        except OSError:
            pass
        return False
    finally:
        os.close(src_fd)


def retain_matching_ltars(backup: Path, staged: Path) -> int:
    """Carry forward `ir/<Rel>.ltar` from `backup` into `staged` when `<Rel>` is unchanged.

    Handoff archives omit `ir/**/*.ltar` so merge-group runs do not ship ~485 MB of publication
    archives. When `main` (or a later consumer) swaps `.lake/build`, retaining archives whose
    compiled module trace and output hashes in `staged` match `backup` byte-for-byte prevents
    `publish.py stage` from re-packing thousands of unchanged modules without trusting filenames
    alone or mutating shared hardlinked cache objects. Carry-over is strictly best-effort.
    """
    retained = 0
    try:
        backup_str, staged_str = str(backup), str(staged)
        ir_info = _lstat_or_none(f"{backup_str}/ir")
        staged_info = _lstat_or_none(staged_str)
        if (ir_info is None or staged_info is None
                or not (stat.S_ISDIR(ir_info.st_mode) and stat.S_ISDIR(staged_info.st_mode))):
            return 0
        dir_cache: dict[str, bool] = {backup_str: True, staged_str: True}

        def walk_ir(abs_dir: str, rel_prefix: str) -> None:
            nonlocal retained
            try:
                with os.scandir(abs_dir) as it:
                    entries = sorted(it, key=lambda item: item.name)
            except OSError:
                return
            for entry in entries:
                try:
                    info = entry.stat(follow_symlinks=False)
                except OSError:
                    continue
                mode = info.st_mode
                if stat.S_ISDIR(mode):
                    walk_ir(entry.path, f"{rel_prefix}{entry.name}/")
                    continue
                if not (stat.S_ISREG(mode) and info.st_size > 0 and entry.name.endswith(".ltar")):
                    continue
                stem = entry.name[:-len(".ltar")]
                if not stem:
                    continue
                rel = f"{rel_prefix}{stem}"
                dst_ltar = f"{staged_str}/ir/{rel}.ltar"
                if _lstat_or_none(dst_ltar) is not None or _lstat_or_none(f"{dst_ltar}.hash") is not None:
                    continue
                try:
                    if not _module_outputs_match(backup_str, staged_str, rel, dir_cache):
                        continue
                    dir_parts = rel.split("/")[:-1]
                    if not _check_real_dir_chain(staged_str, ["ir", *dir_parts],
                                                 dir_cache, create_missing=True):
                        continue
                    if _carry_forward_ltar(entry.path, info, dst_ltar):
                        retained += 1
                except OSError:
                    continue

        walk_ir(f"{backup_str}/ir", "")
    except OSError:
        return retained
    return retained


def _remove_tree(path: Path) -> None:
    """Remove a staging directory tree, preferring native `rm -rf` on POSIX for 100k-inode builds."""
    if os.name == "posix" and os.path.isabs(path) and Path("/bin/rm").is_file():
        result = subprocess.run(["/bin/rm", "-rf", "--", str(path)], capture_output=True)
        if result.returncode == 0 and not path.exists():
            return
    shutil.rmtree(path)


def _record_restored(env: dict) -> None:
    output = env.get("GITHUB_OUTPUT")
    if output:
        with Path(output).open("a", encoding="utf-8") as handle:
            handle.write("restored=true\n")


def install_build(root: Path, staged: Path, backup: Path, *, retain_ltars: bool = True) -> int:
    directory(root / ".lake")
    build = root / ".lake/build"
    if build.exists() or build.is_symlink():
        directory(build)
        build.rename(backup)
    retained = retain_matching_ltars(backup, staged) if retain_ltars and backup.exists() else 0
    try:
        staged.rename(build)
    except BaseException:
        if backup.exists():
            backup.rename(build)
        raise
    return retained


def download_handoff(repository: str, run_id: int, name: str, destination: Path) -> None:
    gh_download_artifact(repository, run_id, name, destination, timeout=DOWNLOAD_SECONDS)


def authoritative_workflow(api, repository: str) -> int:
    workflow = api(f"repos/{repository}/actions/workflows/{WORKFLOW_FILE}")
    require(isinstance(workflow, dict) and workflow.get("path") == WORKFLOW_PATH
            and workflow.get("state") == "active" and positive(workflow.get("id")),
            "Authoritative Lean workflow is unavailable")
    return workflow["id"]


def install_handoff(root: Path, context: dict, workflow_id: int, run: dict, artifact: dict,
                    recheck, restored: str, *, api, downloader,
                    retain_ltars: bool = True) -> None:
    """Download, validate and install `artifact`; `recheck` recomputes `context` afterwards."""
    directory(root / ".lake")
    stage = Path(tempfile.mkdtemp(prefix="handoff-", dir=root / ".lake"))
    backup, installed = stage / "previous", False
    try:
        download = stage / "download"
        download.mkdir()
        downloader(context["repository"], run["id"], artifact["name"], download)
        staged = unpack(download, stage / "unpacked", context, run)
        # Reclaim the ~2.6 GB compressed archive before swapping `.lake/build`.
        (download / "build.tar.gz").unlink(missing_ok=True)
        current = latest_success(api, context, workflow_id)
        require((current["id"], current["run_attempt"]) == (run["id"], run["run_attempt"]),
                "Merge-group run changed during download")
        require(find_artifact(api, context, current)["id"] == artifact["id"],
                "Artifact changed during download")
        require(recheck() == context, "Checkout changed during download")
        retained = install_build(root, staged, backup, retain_ltars=retain_ltars)
        installed = True
        archives = f" (retained {retained} matching .ltar archives)" if retained else ""
        print(f"Build handoff restored from {restored}run {run['id']} attempt "
              f"{run['run_attempt']}{archives}; normal build and checks still run")
    finally:
        # A failed rollback must leave the original build available for recovery. With the
        # build directory absent, the normal Lake invocation safely recompiles from sources.
        if backup.exists() and not installed:
            print(f"Build handoff retained original outputs at {backup}")
        else:
            _remove_tree(stage)


def pr_base_context(root: Path, env: dict) -> dict:
    """Read the base parent from GitHub's synthetic merge commit, even in a depth-one checkout."""
    require(str(env.get("DISABLE_PR_BUILD_HANDOFF", "")).strip().lower() in ("", "0", "false", "no"),
            "PR build handoff is disabled by DISABLE_PR_BUILD_HANDOFF")
    context = source_context(root, env, "pull_request")
    require(env.get("GITHUB_BASE_REF") == "main"
            and re.fullmatch(r"refs/pull/[1-9][0-9]*/merge", env.get("GITHUB_REF", "")),
            "Expected a pull request merge ref targeting main")
    commit = subprocess.check_output(["git", "cat-file", "commit", context["source_sha"]],
                                     cwd=root, text=True, errors="replace")
    parents = re.findall(r"^parent ([0-9a-f]{40})$", commit.partition("\n\n")[0], flags=re.MULTILINE)
    require(len(parents) == 2 and parents[0] != parents[1], "Expected a two-parent PR merge commit")
    return {**context, "source_sha": parents[0]}


def restore(root: Path, env: dict, *, pr_base=False, api=gh_get, downloader=download_handoff) -> None:
    def current_context():
        return pr_base_context(root, env) if pr_base else source_context(root, env, "push")

    context = current_context()
    if pr_base and env.get("RESTORED_LAKE_KEY", "").endswith("-" + context["source_sha"]):
        print("The Actions .lake snapshot already matches the PR base; skipping the build handoff")
        _record_restored(env)
        return
    workflow_id = authoritative_workflow(api, context["repository"])
    run = latest_success(api, context, workflow_id)
    artifact = find_artifact(api, context, run)
    # Only `push` to `main` runs `publish.py stage` and consumes `.ltar` archives; pull requests
    # skip scanning and copying ~14k `.ltar` files from the displaced `.lake/build`.
    install_handoff(root, context, workflow_id, run, artifact, current_context,
                    f"PR base {context['source_sha']}, " if pr_base else "",
                    api=api, downloader=downloader, retain_ltars=not pr_base)
    _record_restored(env)


def restore_ancestor(root: Path, env: dict, *, api=gh_get, downloader=download_handoff,
                     deepen=deepen_history) -> None:
    """Give a merge-group build the outputs of its nearest ancestor that has a handoff.

    The nearest ancestor whose latest merge-group run succeeded and still holds its artifact is
    chosen; ancestors without one are skipped. A failure after that choice (download, archive,
    metadata, a rerun) is a miss, not a reason to try an older build: the step has one download
    budget.
    """
    contexts = ancestor_contexts(root, env)
    if len(contexts) < ANCESTOR_LIMIT:
        deepen(root, env["GITHUB_SHA"])
        contexts = ancestor_contexts(root, env)
    require(bool(contexts), "No first-parent ancestor is available in the checkout")
    workflow_id = authoritative_workflow(api, contexts[0]["repository"])
    nearest = None
    for back, context in enumerate(contexts, 1):
        try:
            run = latest_success(api, context, workflow_id)
            artifact = find_artifact(api, context, run)
        except Rejected as miss:
            nearest = nearest or miss
            continue

        def recheck(ancestor=context["source_sha"]):
            return next((item for item in ancestor_contexts(root, env)
                         if item["source_sha"] == ancestor), None)
        # Merge-group `pack()` omits `.ltar` archives, so carrying them over here is pure overhead.
        install_handoff(root, context, workflow_id, run, artifact, recheck,
                        f"ancestor {context['source_sha']} ({back} first-parent commits back), ",
                        api=api, downloader=downloader, retain_ltars=False)
        _record_restored(env)
        return
    raise Rejected(f"None of the {len(contexts)} nearest first-parent ancestors has a usable "
                   f"merge-group build (nearest: {nearest})")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("pack").add_argument("--output", type=Path, required=True)
    mode = commands.add_parser("restore").add_mutually_exclusive_group()
    mode.add_argument("--ancestor", action="store_true",
                      help="in a merge group, restore the nearest compatible first-parent build")
    mode.add_argument("--pr-base", action="store_true",
                      help="in a main-targeting PR, restore the exact base parent's merge-group build")
    args = parser.parse_args()
    try:
        if args.command == "pack":
            pack(ROOT, args.output, os.environ)
        elif args.ancestor:
            restore_ancestor(ROOT, os.environ)
        elif args.pr_base:
            restore(ROOT, os.environ, pr_base=True)
        else:
            restore(ROOT, os.environ)
    except UnsafeShutdown as error:
        # As in scripts/cache/restore.py: a fetch whose processes could not be stopped is an
        # error, not a miss. Nothing has been downloaded or installed. Exit status 125 is the
        # only one the workflow treats as fatal: its next step fails the job on it, before any
        # other Git, cache or build step runs.
        print(f"error: {error}", file=sys.stderr)
        return 125
    except (Rejected, OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError,
            tarfile.TarError, EOFError) as error:
        message = f"Build handoff unavailable: {error}; continuing without this optional cache"
        if os.environ.get("GITHUB_ACTIONS") == "true":
            # A workflow warning shows on the run summary; the step still succeeds.
            data = message.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
            message = f"::warning title=Build handoff unavailable::{data}"
        print(message)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
