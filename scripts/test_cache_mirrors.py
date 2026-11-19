"""Exercise mirror order/deadlines with real loopback HTTP and a native-Lake facade."""

import ctypes
import json
import os
from pathlib import Path
import re
import shutil
import socket
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts/cache"))
import bounded
import restore


FAKE_LAKE = r'''#!/usr/bin/env python3
import json, os, pathlib, signal, subprocess, sys, urllib.request
args = sys.argv[1:]
root = pathlib.Path(os.environ["MIRROR_ARTIFACTS"])
root.mkdir(exist_ok=True)
endpoint = os.environ.get("LAKE_CACHE_ARTIFACT_ENDPOINT", "")
with open(os.environ["MIRROR_LOG"], "a") as log:
    log.write(json.dumps({"args": args, "endpoint": endpoint,
                          "existing": sorted(p.name for p in root.iterdir())}) + "\n")
if args[:3] == ["exe", "cache", "get"]:
    sys.exit(0)
if args[:1] == ["build"]:
    sys.exit(23)
if args[:2] != ["cache", "get"]:
    sys.exit(2)
try:
    if len(args) > 3:
        data = pathlib.Path(args[-1]).read_bytes()
    else:
        data = urllib.request.urlopen(os.environ["LAKE_CACHE_REVISION_ENDPOINT"] +
            "/cslib-community/complexitylib/tc/leanprover--lean4---fixture/" +
            os.environ["MIRROR_REVISION"] + ".jsonl").read()
    lines = data.decode().splitlines()
    if not lines or json.loads(lines[0]) != "2026-03-17":
        sys.exit(1)
    for line in lines[1:]:
        _, artifact = json.loads(line)
        name = artifact.removesuffix(".ltar") + ".art"
        if not (root / name).exists():
            contents = urllib.request.urlopen(endpoint + "/cslib-community/complexitylib/" + name).read()
            (root / name).write_bytes(contents)
except Exception:
    sys.exit(1)
'''


def run_git(root, env, *args, timestamp=None):
    if timestamp is not None:
        env = {**env, "GIT_AUTHOR_DATE": f"@{timestamp} +0000",
               "GIT_COMMITTER_DATE": f"@{timestamp} +0000"}
    return subprocess.check_output(["git", *args], cwd=root, env=env, text=True).strip()


@unittest.skipUnless(os.name == "posix" and shutil.which("curl") and shutil.which("git"),
                     "mirror integration requires POSIX, curl and git")
class MirrorTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="cache mirror ")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.artifacts = self.root / "artifacts"
        self.log = self.root / "events.jsonl"
        self.env = {k: v for k, v in os.environ.items()
                    if not k.startswith(("COMPLEXITYLIB_CACHE_", "MIRROR_", "GIT_"))
                    and k not in ("DISABLE_CACHE_RESTORE", "LAKE_CACHE_ARTIFACT_ENDPOINT",
                                  "LAKE_CACHE_REVISION_ENDPOINT")}
        self.env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                        GIT_AUTHOR_NAME="Mirror fixture", GIT_COMMITTER_NAME="Mirror fixture",
                        GIT_AUTHOR_EMAIL="fixture@example.invalid", GIT_COMMITTER_EMAIL="fixture@example.invalid",
                        MIRROR_ARTIFACTS=str(self.artifacts), MIRROR_LOG=str(self.log),
                        COMPLEXITYLIB_CACHE_ORIGIN_TIMEOUT="2")
        self.git("init", "-q")
        (self.root / "lean-toolchain").write_text("leanprover/lean4:fixture\n")
        self.git("add", "lean-toolchain")
        self.git("commit", "-qm", "fixture")
        self.env["MIRROR_REVISION"] = self.git("rev-parse", "HEAD")
        executable = self.root / "bin/lake"
        executable.parent.mkdir()
        executable.write_text(FAKE_LAKE)
        executable.chmod(0o755)
        self.env["PATH"] = str(executable.parent) + os.pathsep + self.env["PATH"]
        self.requests = []
        self.revision_mappings = {}
        self.release = threading.Event()
        fixture = self

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, *_):
                pass

            def do_GET(self):
                fixture.requests.append(self.path)
                if "/hang/" in self.path:
                    fixture.release.wait(20)
                    return
                if "/hang-art/" in self.path and self.path.endswith(".art"):
                    fixture.release.wait(20)
                    return
                if "/miss/" in self.path:
                    self.send_error(404)
                    return
                if "/forbidden/" in self.path:
                    self.send_error(403)
                    return
                if "/server-error/" in self.path:
                    self.send_error(501)
                    return
                if self.path.endswith(".jsonl"):
                    if "/by-rev/" in self.path or "/by-rev-403/" in self.path:
                        rev = self.path.rsplit("/", 1)[-1].removesuffix(".jsonl")
                        data = fixture.revision_mappings.get(rev)
                        if data is None:
                            self.send_error(403 if "/by-rev-403/" in self.path else 404)
                            return
                    else:
                        data = b'"2026-03-17"\n["0000000000000001","0000000000000001.ltar"]\n["0000000000000002","0000000000000002.ltar"]\n'
                    if "/html/" in self.path:
                        data = b"<html>maintenance</html>"
                    elif "/empty/" in self.path:
                        data = b""
                    elif "/malformed/" in self.path:
                        data += b"not json\n"
                    elif "/malformed-current/" in self.path:
                        data = b'"2026-03-17"\n["0000000000000001",BROKEN]\n'
                elif self.path.endswith("0000000000000001.art"):
                    data = b"completed first artifact"
                elif self.path.endswith("0000000000000002.art") and "/partial/" not in self.path:
                    data = b"completed second artifact"
                else:
                    self.send_error(404)
                    return
                self.send_response(200)
                self.send_header("Content-Length", str(len(data)))
                self.end_headers()
                try:
                    self.wfile.write(data)
                except BrokenPipeError:
                    pass

        self.server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.server.daemon_threads = True
        worker = threading.Thread(target=self.server.serve_forever, daemon=True)
        worker.start()
        self.base = f"http://127.0.0.1:{self.server.server_port}"
        self.addCleanup(self.close_server)

    def close_server(self):
        self.release.set()
        self.server.shutdown()
        self.server.server_close()

    def git(self, *args, timestamp=None):
        return run_git(self.root, self.env, *args, timestamp=timestamp)

    def events(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()] if self.log.exists() else []

    def fetch(self, *suffixes, missing=False, **changes):
        env = {**self.env, "COMPLEXITYLIB_CACHE_URLS": "\n".join(self.base + s for s in suffixes), **changes}
        args = [sys.executable, "-B", str(REPO / "scripts/cache/restore.py"), "--checkout", str(self.root)]
        if missing:
            args.append("--missing")
        result = subprocess.run(args, cwd=self.root, env=env, capture_output=True, text=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def test_primary_success_does_not_contact_secondary(self):
        result = self.fetch("/primary", "/fallback")
        self.assertRegex(result.stdout, r"cache origin 1/2: completed in \d+\.\ds:")
        self.assertNotIn("cache origin 2/2:", result.stdout)
        self.assertEqual(len(self.events()), 1)
        self.assertFalse(any("/fallback/" in request for request in self.requests))
        self.assertEqual(len(list(self.artifacts.iterdir())), 2)

    def test_default_origins_fall_back_after_public_access_is_revoked(self):
        for missing in (False, True):
            with self.subTest(missing=missing), patch.object(
                    restore, "DEFAULT_URLS", (self.base + "/forbidden", self.base + "/fallback")):
                self.requests.clear()
                self.log.unlink(missing_ok=True)
                shutil.rmtree(self.artifacts, ignore_errors=True)
                self.assertTrue(restore.restore(self.root, self.env, missing=missing))
                self.assertTrue(any("/forbidden/r0/" in request for request in self.requests))
                self.assertEqual(self.events()[-1]["endpoint"], self.base + "/fallback/a0")
                self.assertEqual(len(list(self.artifacts.iterdir())), 2)

    def test_partial_primary_preserves_completed_archive_for_secondary(self):
        self.fetch("/partial", "/fallback")
        self.assertEqual([event["endpoint"] for event in self.events()],
                         [self.base + "/partial/a0", self.base + "/fallback/a0"])
        self.assertEqual(self.events()[1]["existing"], ["0000000000000001.art"])
        self.assertEqual((self.artifacts / "0000000000000002.art").read_bytes(), b"completed second artifact")
        self.assertFalse(any("/fallback/a0/" in request and request.endswith("0000000000000001.art")
                             for request in self.requests))

    def test_hanging_primary_has_deadline_then_secondary_succeeds(self):
        start = time.monotonic()
        result = self.fetch("/hang", "/fallback", COMPLEXITYLIB_CACHE_ORIGIN_TIMEOUT="2")
        self.assertRegex(result.stdout, r"cache origin 1/2: timed out in \d+\.\ds:")
        self.assertRegex(result.stdout, r"cache origin 2/2: completed in \d+\.\ds:")
        self.assertLess(time.monotonic() - start, 10)
        self.assertTrue(any("/hang/r0/" in request for request in self.requests))
        self.assertEqual([event["endpoint"] for event in self.events()],
                         [self.base + "/fallback/a0"])
        self.assertEqual(len(list(self.artifacts.iterdir())), 2)

    def test_hanging_artifact_download_has_deadline_then_secondary_succeeds(self):
        start = time.monotonic()
        result = self.fetch("/hang-art", "/fallback", COMPLEXITYLIB_CACHE_ORIGIN_TIMEOUT="2")
        self.assertRegex(result.stdout, r"cache origin 1/2: timed out in \d+\.\ds:")
        self.assertRegex(result.stdout, r"cache origin 2/2: completed in \d+\.\ds:")
        self.assertLess(time.monotonic() - start, 10)
        self.assertEqual([event["endpoint"] for event in self.events()],
                         [self.base + "/hang-art/a0", self.base + "/fallback/a0"])
        self.assertEqual(len(list(self.artifacts.iterdir())), 2)

    def test_missing_output_path_has_same_order_and_bounded_mapping_lookup(self):
        self.fetch("/hang", "/partial", "/fallback", missing=True,
                   COMPLEXITYLIB_CACHE_ORIGIN_TIMEOUT="3")
        self.assertTrue(any("/hang/r0/" in request for request in self.requests))
        self.assertEqual([event["endpoint"] for event in self.events()],
                         [self.base + "/partial/a0", self.base + "/fallback/a0"])
        self.assertEqual(len(list(self.artifacts.iterdir())), 2)

    def test_all_misses_report_source_fallback(self):
        result = self.fetch("/miss", "/other/miss")
        self.assertIn("lake build will compile missing outputs", result.stderr)
        self.assertRegex(result.stdout, r"cache origin 1/2: failed \(exit 1\) in \d+\.\ds:")
        self.assertNotIn("completed in", result.stdout)
        self.assertFalse(self.artifacts.exists() and any(self.artifacts.iterdir()))

    def test_mapping_lookup_failure_reports_http_status_without_claiming_no_artifacts(self):
        for missing in (False, True):
            with self.subTest(missing=missing):
                result = self.fetch("/miss", missing=missing)
                self.assertIn("No usable cached mapping among 1 revisions", result.stdout)
                self.assertIn("last lookup HTTP 404, curl exit 22", result.stdout)
                self.assertNotIn("No uploaded outputs", result.stdout)

    def test_exhausted_mirrors_preserve_the_subsequent_strict_build(self):
        for name in ("scripts/build.sh", "scripts/cache/ensure.sh", "scripts/cache/get.sh",
                     "scripts/cache/get_mathlib.py", "scripts/cache/bounded.py", "scripts/cache/restore.py", "scripts/cache/windows_job.py"):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(REPO / name, target)
        env = {**self.env, "COMPLEXITYLIB_CACHE_URLS": self.base + "/miss " + self.base + "/other/miss"}
        result = subprocess.run([str(self.root / "scripts/build.sh"), "--wfail", "--iofail"],
                                cwd=self.root, env=env, capture_output=True, text=True, timeout=20)
        self.assertEqual(result.returncode, 23, result.stdout + result.stderr)
        self.assertTrue(any("/miss/r0/" in request for request in self.requests))
        self.assertTrue(any("/other/miss/r0/" in request for request in self.requests))
        self.assertEqual([event["args"][:2] for event in self.events()],
                         [["exe", "cache"], ["build", "--wfail"]])

    def test_missing_output_filter_preserves_current_modules(self):
        trace = self.root / ".lake/build/Current.trace"
        trace.parent.mkdir(parents=True)
        trace.write_text('{"depHash":"0000000000000001"}')
        self.fetch("/partial", "/fallback", missing=True)
        self.assertFalse(any(request.endswith("0000000000000001.art") for request in self.requests))
        self.assertEqual(sorted(path.name for path in self.artifacts.iterdir()), ["0000000000000002.art"])

    def test_malformed_primary_mapping_cannot_suppress_secondary(self):
        for missing in (False, True):
            for primary in ("/html", "/empty", "/malformed"):
                with self.subTest(missing=missing, primary=primary):
                    self.log.unlink(missing_ok=True)
                    shutil.rmtree(self.artifacts, ignore_errors=True)
                    self.fetch(primary, "/fallback", missing=missing)
                    self.assertEqual(self.events()[-1]["endpoint"], self.base + "/fallback/a0")

    def test_malformed_row_matching_a_current_trace_is_not_filtered_away(self):
        trace = self.root / ".lake/build/Current.trace"
        trace.parent.mkdir(parents=True)
        trace.write_text('{"depHash":"0000000000000001"}')
        self.fetch("/malformed-current", "/fallback", missing=True)
        self.assertEqual(self.events()[-1]["endpoint"], self.base + "/fallback/a0")

    def test_403_on_unpublished_revisions_continues_to_published_ancestor(self):
        # GCS with roles/storage.legacyObjectReader (read without list) answers missing objects
        # with HTTP 403 rather than 404. Unpublished branch/merge tips must not cause restore.py
        # to abandon the origin before reaching a published ancestor.
        self.git("checkout", "-qb", "main")
        (self.root / "base.txt").write_text("base\n")
        self.git("add", "base.txt")
        self.git("commit", "-qm", "old base B", timestamp=1_700_001_000)
        old_base = self.git("rev-parse", "HEAD")

        self.git("checkout", "-qb", "feature")
        (self.root / "feat.txt").write_text("feat\n")
        self.git("add", "feat.txt")
        self.git("commit", "-qm", "feature", timestamp=1_700_003_000)

        self.git("checkout", "-q", "main")
        (self.root / "main.txt").write_text("main\n")
        self.git("add", "main.txt")
        self.git("commit", "-qm", "published main", timestamp=1_700_002_000)
        new_main = self.git("rev-parse", "HEAD")

        self.git("checkout", "-q", "feature")
        self.git("merge", "-q", "--no-ff", "-m", "merge main", "main", timestamp=1_700_004_000)

        self.revision_mappings = {
            old_base: b'"2026-03-17"\n["0000000000000001","0000000000000001.ltar"]\n',
            new_main: b'"2026-03-17"\n["0000000000000002","0000000000000002.ltar"]\n',
        }
        for missing in (False, True):
            with self.subTest(missing=missing):
                self.requests.clear()
                self.log.unlink(missing_ok=True)
                shutil.rmtree(self.artifacts, ignore_errors=True)
                result = self.fetch("/by-rev-403", "/fallback", missing=missing)
                self.assertIn(f"Remote cache: {new_main}", result.stdout)
                self.assertFalse(any("/fallback/" in req for req in self.requests))
                self.assertEqual(sorted(p.name for p in self.artifacts.iterdir()),
                                 ["0000000000000002.art"])

    def test_all_403_origin_exhausts_candidates_and_falls_back_to_secondary(self):
        for i in range(2):
            (self.root / f"step{i}").write_text(str(i))
            self.git("add", f"step{i}")
            self.git("commit", "-qm", f"step {i}", timestamp=1_700_000_100 + i)
        for missing in (False, True):
            with self.subTest(missing=missing):
                self.requests.clear()
                self.log.unlink(missing_ok=True)
                shutil.rmtree(self.artifacts, ignore_errors=True)
                result = self.fetch("/forbidden", "/fallback", missing=missing)
                forbidden_lookups = [r for r in self.requests if "/forbidden/r0/" in r]
                self.assertEqual(len(forbidden_lookups), 3)
                self.assertIn("No usable cached mapping among 3 revisions", result.stdout)
                self.assertIn("last lookup HTTP 403", result.stdout)
                self.assertEqual(self.events()[-1]["endpoint"], self.base + "/fallback/a0")

    def test_5xx_and_transport_errors_fail_fast_without_probing_every_ancestor(self):
        for i in range(4):
            (self.root / f"step{i}").write_text(str(i))
            self.git("add", f"step{i}")
            self.git("commit", "-qm", f"step {i}", timestamp=1_700_000_100 + i)
        with socket.socket() as sock:
            sock.bind(("127.0.0.1", 0))
            closed_origin = f"http://127.0.0.1:{sock.getsockname()[1]}"
        for missing in (False, True):
            with self.subTest(kind="5xx", missing=missing):
                self.requests.clear()
                self.log.unlink(missing_ok=True)
                shutil.rmtree(self.artifacts, ignore_errors=True)
                result = self.fetch("/server-error", "/fallback", missing=missing)
                error_lookups = [r for r in self.requests if "/server-error/r0/" in r]
                self.assertEqual(len(error_lookups), 1)
                self.assertIn("No usable cached mapping among 1 revisions", result.stdout)
                self.assertIn("last lookup HTTP 501", result.stdout)
                self.assertEqual(self.events()[-1]["endpoint"], self.base + "/fallback/a0")
            with self.subTest(kind="transport", missing=missing):
                self.requests.clear()
                self.log.unlink(missing_ok=True)
                shutil.rmtree(self.artifacts, ignore_errors=True)
                env = {**self.env,
                       "COMPLEXITYLIB_CACHE_URLS": f"{closed_origin} {self.base}/fallback"}
                args = [sys.executable, "-B", str(REPO / "scripts/cache/restore.py"),
                        "--checkout", str(self.root)]
                if missing:
                    args.append("--missing")
                result = subprocess.run(args, cwd=self.root, env=env,
                                        capture_output=True, text=True, timeout=20)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("No usable cached mapping among 1 revisions", result.stdout)
                self.assertEqual(self.events()[-1]["endpoint"], self.base + "/fallback/a0")

    def test_merge_of_main_and_post_merge_commits_restore_merged_main_over_old_base(self):
        # Old base B (published with artifact 1), newer main M (published with artifact 2) followed
        # by an unpublished tip M_tip, and a feature branch with newer timestamps off B that merges
        # M_tip (and then adds a post-merge commit P1). Both default and --missing must restore M.
        self.git("checkout", "-qb", "main")
        (self.root / "base.txt").write_text("base\n")
        self.git("add", "base.txt")
        self.git("commit", "-qm", "old base B", timestamp=1_700_001_000)
        old_base = self.git("rev-parse", "HEAD")

        self.git("checkout", "-qb", "feature")
        (self.root / "feat.txt").write_text("feat 1\n")
        self.git("add", "feat.txt")
        self.git("commit", "-qm", "feature 1", timestamp=1_700_003_000)

        self.git("checkout", "-q", "main")
        (self.root / "main1.txt").write_text("main 1\n")
        self.git("add", "main1.txt")
        self.git("commit", "-qm", "main published M", timestamp=1_700_001_500)
        new_main = self.git("rev-parse", "HEAD")
        (self.root / "main2.txt").write_text("main 2\n")
        self.git("add", "main2.txt")
        self.git("commit", "-qm", "main unpublished tip", timestamp=1_700_001_600)

        self.git("checkout", "-q", "feature")
        self.git("merge", "-q", "--no-ff", "-m", "merge main", "main", timestamp=1_700_004_000)

        self.revision_mappings = {
            old_base: b'"2026-03-17"\n["0000000000000001","0000000000000001.ltar"]\n',
            new_main: b'"2026-03-17"\n["0000000000000002","0000000000000002.ltar"]\n',
        }

        for stage in ("merge-head", "post-merge"):
            if stage == "post-merge":
                (self.root / "post.txt").write_text("post merge\n")
                self.git("add", "post.txt")
                self.git("commit", "-qm", "post-merge commit", timestamp=1_700_005_000)
            for missing in (False, True):
                with self.subTest(stage=stage, missing=missing):
                    self.requests.clear()
                    self.log.unlink(missing_ok=True)
                    shutil.rmtree(self.artifacts, ignore_errors=True)
                    result = self.fetch("/by-rev", missing=missing)
                    self.assertIn(f"Remote cache: {new_main}", result.stdout)
                    self.assertEqual(sorted(p.name for p in self.artifacts.iterdir()),
                                     ["0000000000000002.art"])
                    self.assertFalse(any(old_base in req for req in self.requests))

    def pin_mathlib(self, revision, message, timestamp):
        manifest = {"version": "1.1.0", "packages": [
            {"name": "cslib", "rev": "c" * 40}, {"name": "mathlib", "rev": revision}]}
        (self.root / "lake-manifest.json").write_text(json.dumps(manifest))
        self.git("add", "lake-manifest.json")
        self.git("commit", "-qm", message, timestamp=timestamp)
        return self.git("rev-parse", "HEAD")

    def test_ancestors_pinning_another_mathlib_are_not_restored(self):
        # The incident of 17 November 2026: after a Mathlib bump, the nearest published ancestor
        # predates the bump, so its complete output set was downloaded and matched nothing.
        # An orphan history, so that every candidate has a manifest (the fixture's root has none).
        self.git("checkout", "-q", "--orphan", "main")
        before = self.pin_mathlib("a" * 40, "published before the bump", 1_700_001_000)
        self.revision_mappings = {
            before: b'"2026-03-17"\n["0000000000000001","0000000000000001.ltar"]\n'}
        bump = self.pin_mathlib("b" * 40, "unpublished Mathlib bump", 1_700_002_000)
        for missing in (False, True):
            with self.subTest(published="before the bump only", missing=missing):
                self.requests.clear()
                result = self.fetch("/by-rev", "/by-rev-403", missing=missing)
                self.assertIn("Skipping 1 of 2 candidate ancestors", result.stdout)
                # Only the bump itself is looked up, at both origins; nothing is downloaded.
                self.assertEqual(len(self.requests), 2)
                self.assertTrue(all(bump in request for request in self.requests))
                self.assertFalse(self.artifacts.exists() and any(self.artifacts.iterdir()))
        # A pin changed in the working tree but not yet committed matches no ancestor at all:
        # the first origin attempt settles that without a request, and no other origin is tried.
        self.requests.clear()
        committed = (self.root / "lake-manifest.json").read_text()
        (self.root / "lake-manifest.json").write_text(committed.replace("b" * 40, "e" * 40))
        result = self.fetch("/by-rev", "/by-rev-403")
        self.assertIn("no candidate ancestor shares this checkout's Mathlib revision", result.stdout)
        self.assertIn("origin 1/2: skipped", result.stdout)
        self.assertNotIn("origin 2/2", result.stdout)
        self.assertEqual(self.requests, [])
        (self.root / "lake-manifest.json").write_text(committed)
        # Once the bump is published it is restored, and the older set is still never requested.
        self.revision_mappings[bump] = b'"2026-03-17"\n["0000000000000002","0000000000000002.ltar"]\n'
        (self.root / "work.txt").write_text("work\n")
        self.git("add", "work.txt")
        self.git("commit", "-qm", "work after the bump", timestamp=1_700_003_000)
        result = self.fetch("/by-rev")
        self.assertIn(f"Remote cache: {bump}", result.stdout)
        self.assertEqual(sorted(p.name for p in self.artifacts.iterdir()), ["0000000000000002.art"],
                         result.stdout + result.stderr)
        self.assertFalse(any(before in request for request in self.requests))

    def test_other_manifest_changes_and_unreadable_pins_keep_the_ancestor(self):
        # A bump of cslib alone left 52% to 99.8% of outputs reusable, so it must not be skipped;
        # the fixture's first commit has no manifest at all and is kept as well.
        self.git("checkout", "-qb", "main")
        published = self.pin_mathlib("a" * 40, "published", 1_700_001_000)
        self.revision_mappings = {
            published: b'"2026-03-17"\n["0000000000000001","0000000000000001.ltar"]\n'}
        manifest = json.loads((self.root / "lake-manifest.json").read_text())
        manifest["packages"][0]["rev"] = "d" * 40
        (self.root / "lake-manifest.json").write_text(json.dumps(manifest, indent=1))
        self.git("add", "lake-manifest.json")
        self.git("commit", "-qm", "bump cslib only", timestamp=1_700_002_000)
        result = self.fetch("/by-rev")
        self.assertIn(f"Remote cache: {published}", result.stdout)
        self.assertNotIn("Skipping", result.stdout)
        self.assertEqual(restore.same_mathlib(self.root, restore.candidate_revisions(self.root)),
                         restore.candidate_revisions(self.root))
        # An unreadable manifest in the checkout disables the comparison instead of the restore.
        (self.root / "lake-manifest.json").write_text("not json")
        self.assertEqual(len(restore.same_mathlib(self.root, [published])), 1)

    def test_explicit_empty_legacy_override_disables_configured_mirrors(self):
        self.fetch("/primary", "/fallback", COMPLEXITYLIB_CACHE_URL="")
        self.assertEqual(self.events(), [])
        self.assertEqual(self.requests, [])

    def test_recovery_switch_skips_every_origin(self):
        self.fetch("/primary", "/fallback", DISABLE_CACHE_RESTORE="true")
        self.assertEqual(self.events(), [])
        self.assertEqual(self.requests, [])


@unittest.skipUnless(shutil.which("git"), "git is required")
class CandidateRevisionsTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="cache candidates ")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        self.env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                        GIT_AUTHOR_NAME="Candidate fixture", GIT_COMMITTER_NAME="Candidate fixture",
                        GIT_AUTHOR_EMAIL="fixture@example.invalid",
                        GIT_COMMITTER_EMAIL="fixture@example.invalid")
        self.git("init", "-q", "-b", "main")

    def git(self, *args, timestamp=None):
        return run_git(self.root, self.env, *args, timestamp=timestamp)

    def commit(self, path, content, message, timestamp):
        (self.root / path).write_text(content)
        self.git("add", path)
        self.git("commit", "-qm", message, timestamp=timestamp)
        return self.git("rev-parse", "HEAD")

    def test_clock_skew_still_orders_descendant_before_old_base(self):
        old_base = self.commit("base", "0", "B", timestamp=1_700_009_000)
        self.git("checkout", "-qb", "feature")
        self.commit("feat", "1", "F1", timestamp=1_700_005_000)
        self.git("checkout", "-q", "main")
        new_main = self.commit("main", "1", "M", timestamp=1_700_001_000)
        self.git("checkout", "-q", "feature")
        self.git("merge", "-q", "--no-ff", "-m", "merge", "main", timestamp=1_700_010_000)
        revs = restore.candidate_revisions(self.root)
        self.assertLess(revs.index(new_main), revs.index(old_base))

    def test_long_feature_branch_does_not_starve_merged_main_in_either_parent_order(self):
        self.commit("base", "0", "B", timestamp=1_700_001_000)
        self.git("checkout", "-qb", "feature")
        for i in range(110):
            self.commit("feat", str(i), f"F{i}", timestamp=1_700_003_000 + i)
        feat_tip = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "main")
        new_main = self.commit("main", "1", "M", timestamp=1_700_002_000)

        # Local merge: first parent is long feature branch, second parent is main.
        self.git("checkout", "-q", "feature")
        self.git("merge", "-q", "--no-ff", "-m", "merge main into feat", "main",
                 timestamp=1_700_005_000)
        local_revs = restore.candidate_revisions(self.root)
        self.assertIn(new_main, local_revs)
        self.assertLessEqual(local_revs.index(new_main), 2)

        # PR merge commit: first parent is main, second parent is long feature branch.
        self.git("checkout", "-qb", "pr-merge", new_main)
        self.git("merge", "-q", "--no-ff", "-m", "merge feat into main", feat_tip,
                 timestamp=1_700_006_000)
        pr_revs = restore.candidate_revisions(self.root)
        self.assertIn(new_main, pr_revs)
        self.assertLessEqual(pr_revs.index(new_main), 2)

    def test_unpublished_main_streak_still_precedes_short_branch_old_base(self):
        old_base = self.commit("base", "0", "B", timestamp=1_700_001_000)
        self.git("checkout", "-qb", "feature")
        self.commit("feat", "1", "F1", timestamp=1_700_001_100)
        self.git("checkout", "-q", "main")
        published_main = self.commit("main", "0", "M0", timestamp=1_700_002_000)
        for i in range(1, 21):
            self.commit("main", str(i), f"M{i}", timestamp=1_700_002_000 + i)
        self.git("checkout", "-q", "feature")
        self.git("merge", "-q", "--no-ff", "-m", "merge main", "main", timestamp=1_700_003_000)
        revs = restore.candidate_revisions(self.root)
        self.assertLess(revs.index(published_main), revs.index(old_base))

    def test_stalled_merge_base_fallback_rescues_long_branch_between_merges(self):
        self.commit("base", "0", "B", timestamp=1_700_001_000)
        self.git("checkout", "-qb", "feature")
        self.commit("feat", "0", "F0", timestamp=1_700_001_100)
        self.git("checkout", "-q", "main")
        first_main = self.commit("main", "1", "M1", timestamp=1_700_002_000)
        self.git("checkout", "-q", "feature")
        self.git("merge", "-q", "--no-ff", "-m", "merge M1", "main", timestamp=1_700_002_100)
        for i in range(1, 106):
            self.commit("feat", str(i), f"F{i}", timestamp=1_700_003_000 + i)
        self.git("checkout", "-q", "main")
        self.commit("main", "2", "M2-unpublished", timestamp=1_700_004_000)
        self.git("checkout", "-q", "feature")
        self.git("merge", "-q", "--no-ff", "-m", "merge M2", "main", timestamp=1_700_005_000)
        revs = restore.candidate_revisions(self.root)
        self.assertIn(first_main, revs)

    def test_stalled_fallback_seeds_remaining_wave_and_next_wave_before_stalled_base(self):
        base = self.commit("base", "0", "B", timestamp=1_700_001_000)
        self.git("checkout", "-qb", "left")
        self.commit("left", "1", "L1", timestamp=1_700_002_000)
        self.commit("left", "2", "L2", timestamp=1_700_002_100)
        self.git("checkout", "-qb", "extra", base)
        extra1 = self.commit("extra", "1", "X1", timestamp=1_700_002_400)
        self.commit("extra", "2", "X2", timestamp=1_700_002_500)
        self.git("checkout", "-qb", "mid", base)
        self.commit("mid", "1", "M1", timestamp=1_700_001_500)
        mid2 = self.commit("mid", "2", "M2", timestamp=1_700_001_600)
        self.git("checkout", "-qb", "right", base)
        self.commit("right", "1", "R1", timestamp=1_700_003_000)
        self.git("checkout", "-q", "left")
        self.git("merge", "-q", "--no-ff", "-m", "octopus", "extra", "mid", "right",
                 timestamp=1_700_004_000)
        # Wave 0: octopus (1).
        # Wave 1: [R1 (3000), X2 (2500), L2 (2100), M2 (1600)].
        # R1 stalls B, X2 queues X1 into next_wave, limit=4 stops on L2 leaving M2 in remaining_wave.
        revs = restore.candidate_revisions(self.root, limit=4, stalled_limit=5)
        self.assertLess(revs.index(mid2), revs.index(extra1))
        self.assertLess(revs.index(extra1), revs.index(base))


@unittest.skipUnless(os.name == "posix", "owned process-group shutdown requires POSIX")
class WatchdogTests(unittest.TestCase):
    @unittest.skipUnless(sys.platform.startswith("linux"), "Linux nested-session/subreaper regression")
    def test_outer_cancellation_during_inner_cleanup_does_not_retry_or_leave_a_writer(self):
        with tempfile.TemporaryDirectory(prefix="nested cache cleanup ") as directory:
            root = Path(directory)
            executable = root / "bin/lake"
            executable.parent.mkdir()
            executable.write_text('''#!/usr/bin/env python3
import os,pathlib,signal,time
p=pathlib.Path(os.environ["REVIEW_ROOT"])
with (p/'pids').open('a') as f: f.write(str(os.getpid())+'\\n')
signal.signal(signal.SIGTERM, signal.SIG_IGN)
while True:
 (p/'heartbeat').write_text(str(time.monotonic()))
 time.sleep(.01)
''')
            executable.chmod(0o755)
            source = ("import sys;sys.path.insert(0,sys.argv[1]);import get_mathlib as g;"
                      "sys.argv=[sys.argv[0]];g.ATTEMPT_SECONDS=.1;g.SHUTDOWN_SECONDS=.8;"
                      "g.RETRY_SECONDS=.1;raise SystemExit(g.main())")
            env = {**os.environ, "PATH": str(executable.parent) + os.pathsep + os.environ["PATH"],
                   "REVIEW_ROOT": directory, "COMPLEXITYLIB_CACHE_CHECKOUT": directory}
            env.pop("DISABLE_CACHE_RESTORE", None)
            try:
                result = bounded.run([sys.executable, "-B", "-c", source,
                                      str(REPO / "scripts/cache")], timeout=.35, grace=2, cwd=root, env=env)
                self.assertEqual(result.returncode, 124)
                self.assertEqual(len((root / "pids").read_text().splitlines()), 1, "cancelled cleanup started another retry")
                before = (root / "heartbeat").read_text()
                time.sleep(.15)
                self.assertEqual(before, (root / "heartbeat").read_text())
            finally:
                for pid in map(int, (root / "pids").read_text().splitlines() if (root / "pids").exists() else []):
                    try:
                        os.killpg(pid, 9)
                    except ProcessLookupError:
                        pass
                    try:
                        os.waitpid(pid, 0)
                    except ChildProcessError:
                        pass

    @unittest.skipUnless(sys.platform.startswith("linux"), "Linux nested-session/subreaper regression")
    def test_nested_mathlib_supervisor_reaps_orphans_before_source_fallback(self):
        with tempfile.TemporaryDirectory(prefix="nested cache reap ") as directory:
            root = Path(directory)
            executable = root / "bin/lake"
            executable.parent.mkdir()
            executable.write_text('''#!/usr/bin/env python3
import json,os,pathlib,subprocess,sys,time
p=pathlib.Path(os.environ["REVIEW_ROOT"])
c=subprocess.Popen([sys.executable,'-c','import time;time.sleep(30)'])
with (p/'pids').open('a') as f: f.write(json.dumps([os.getpid(),c.pid])+'\\n')
time.sleep(30)
''')
            executable.chmod(0o755)
            source = ("import sys;sys.path.insert(0,sys.argv[1]);import get_mathlib as g;"
                      "sys.argv=[sys.argv[0]];g.ATTEMPT_SECONDS=.15;g.SHUTDOWN_SECONDS=.15;"
                      "g.RETRY_SECONDS=.01;raise SystemExit(g.main())")
            env = {**os.environ, "PATH": str(executable.parent) + os.pathsep + os.environ["PATH"],
                   "REVIEW_ROOT": directory, "COMPLEXITYLIB_CACHE_CHECKOUT": directory}
            env.pop("DISABLE_CACHE_RESTORE", None)
            try:
                result = bounded.run([sys.executable, "-B", "-c", source,
                                      str(REPO / "scripts/cache")], timeout=5, grace=1, cwd=root, env=env)
                self.assertEqual(result.returncode, 0)
                records = [json.loads(line) for line in (root / "pids").read_text().splitlines()]
                self.assertEqual(len(records), 3)
                for pair in records:
                    for pid in pair:
                        with self.assertRaises(ProcessLookupError):
                            os.kill(pid, 0)
            finally:
                for line in (root / "pids").read_text().splitlines() if (root / "pids").exists() else []:
                    for pid in json.loads(line):
                        try:
                            os.kill(pid, 9)
                        except ProcessLookupError:
                            pass
                        try:
                            os.waitpid(pid, 0)
                        except ChildProcessError:
                            pass

    def test_timeout_drains_a_descendant_writer_before_returning(self):
        with tempfile.TemporaryDirectory(prefix="cache writer ") as directory:
            heartbeat = Path(directory) / "heartbeat"
            source = r'''
import os, pathlib, signal, subprocess, sys, time
child = subprocess.Popen([sys.executable, '-c', "import pathlib,sys,time\np=pathlib.Path(sys.argv[1])\nwhile True:\n p.write_text(str(time.monotonic()))\n time.sleep(.01)", sys.argv[1]])
def stop(*_):
 child.wait()
 sys.exit(0)
signal.signal(signal.SIGTERM, stop)
child.wait()
'''
            result = bounded.run([sys.executable, "-c", source, str(heartbeat)], timeout=.4, grace=1)
            self.assertEqual(result.returncode, 124)
            before = heartbeat.read_text()
            time.sleep(.1)
            self.assertEqual(before, heartbeat.read_text())

    def test_invalid_timeouts_and_credentialed_origins_do_not_start_downloads(self):
        for value in ("0", "-1", "inf", "nan", "601", "nonsense"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                bounded.seconds({"T": value}, "T", 180)
        for value in ("https://user:secret@example.invalid", "https://example.invalid/?secret=x"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                restore.origins({"COMPLEXITYLIB_CACHE_URL": value})


class OriginConfigurationTests(unittest.TestCase):
    def test_default_origin_order_and_explicit_overrides(self):
        defaults = ["https://storage.googleapis.com/complexitylib-lake-cache",
                    "https://complexitycache.csail.mit.edu"]
        self.assertEqual(restore.origins({}), defaults)
        self.assertEqual(restore.origins({"COMPLEXITYLIB_CACHE_URLS": ""}), defaults)
        self.assertEqual(restore.origins({"COMPLEXITYLIB_CACHE_URLS": "https://other.invalid"}),
                         ["https://other.invalid"])
        self.assertEqual(restore.origins({"COMPLEXITYLIB_CACHE_URL": "https://single.invalid",
                                        "COMPLEXITYLIB_CACHE_URLS": "https://other.invalid"}),
                         ["https://single.invalid"])
        self.assertEqual(restore.origins({"COMPLEXITYLIB_CACHE_URL": ""}), [])


class PublicationPermissionTests(unittest.TestCase):
    def test_oidc_is_exclusive_to_main_push_gcs_publisher(self):
        workflow = (REPO / ".github/workflows/lean_action_ci.yml").read_text()
        blocks = re.split(r"^  ([a-z][a-z0-9-]*):\n", workflow.split("jobs:\n", 1)[1], flags=re.M)
        jobs = dict(zip(blocks[1::2], blocks[2::2]))
        self.assertEqual([name for name, block in jobs.items() if "id-token: write" in block],
                         ["publish-gcs-cache"])
        gcs = jobs["publish-gcs-cache"]
        self.assertIn("github.event_name == 'push' && github.ref == 'refs/heads/main'", gcs)
        self.assertIn("needs.ci-checks.result == 'success'", gcs)
        self.assertIn("artifact-ids: ${{ needs.ci-checks.outputs.publication }}", gcs)
        self.assertLess(gcs.index('verify "$RUNNER_TEMP/lake-publication" --revision "$GITHUB_SHA"'),
                        gcs.index("uses: google-github-actions/auth@"))
        for name in ("source-checks", "lean-checks", "ci-checks"):
            self.assertNotIn("google-github-actions/auth@", jobs[name])
        lean = jobs["lean-checks"]
        aggregator = jobs["ci-checks"]
        self.assertIn("env.CACHE_RECOVERY_GENERATION", lean)
        self.assertIn("needs: [select-checks, source-checks, lean-checks]", aggregator)
        self.assertIn("if: always()", aggregator)
        self.assertIn("publication: ${{ needs.lean-checks.outputs.publication }}", aggregator)
        for name in ("publish-gcs-cache", "publish-mit-cache"):
            with self.subTest(publisher=name):
                publisher = jobs[name]
                self.assertIn("ci-checks", publisher.split("\n", 1)[0])
                self.assertIn("needs.ci-checks.result == 'success'", publisher)
                self.assertIn("artifact-ids: ${{ needs.ci-checks.outputs.publication }}", publisher)
        self.assertIn("CACHE_RECOVERY_GENERATION:", workflow)
        self.assertIn("COMPLEXITYLIB_CACHE_URLS:", workflow)


@unittest.skipUnless(os.name == "nt" or (sys.platform == "cygwin" and shutil.which("py.exe")),
                     "actual native Windows descendant tests require Windows or Cygwin+py launcher")
class NativeWindowsTreeTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="native cache tree ")
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.native_directory = str(self.directory)
        self.native_python = sys.executable
        if sys.platform == "cygwin":
            self.native_directory = subprocess.check_output(
                ["cygpath", "-w", str(self.directory)], text=True).strip()
            native = subprocess.check_output(
                ["py.exe", "-3", "-c", "import sys;print(sys.executable)"], text=True).strip()
            self.native_python = subprocess.check_output(["cygpath", "-u", native], text=True).strip()
        self.writer = "import pathlib,sys,time\np=pathlib.Path(sys.argv[1])\nwhile True:\n p.write_text(str(time.monotonic()))\n time.sleep(.02)"
        self.parent = '''import json,os,pathlib,subprocess,sys,time
p=pathlib.Path(sys.argv[1])
c=subprocess.Popen([sys.executable,'-c',sys.argv[2],str(p/'heartbeat')])
(p/'pids.json').write_text(json.dumps([os.getpid(),c.pid]))
while not (p/'heartbeat').exists(): time.sleep(.01)
if sys.argv[3] == 'early': sys.exit(0)
c.wait()
'''
        self.addCleanup(self.cleanup_owned_native_pids)

    def command(self, mode):
        return [self.native_python, "-c", self.parent, self.native_directory, self.writer, mode]

    def cleanup_owned_native_pids(self):
        record = self.directory / "pids.json"
        if not record.exists():
            return
        kernel = ctypes.WinDLL("kernel32") if os.name == "nt" else ctypes.CDLL("kernel32.dll")
        kernel.OpenProcess.argtypes = [ctypes.c_uint32, ctypes.c_int, ctypes.c_uint32]
        kernel.OpenProcess.restype = ctypes.c_void_p
        kernel.TerminateProcess.argtypes = [ctypes.c_void_p, ctypes.c_uint32]
        kernel.CloseHandle.argtypes = [ctypes.c_void_p]
        for pid in json.loads(record.read_text()):
            handle = kernel.OpenProcess(1, False, pid)
            if handle:
                kernel.TerminateProcess(handle, 1)
                kernel.CloseHandle(handle)
        time.sleep(.05)

    def assert_writer_stopped(self):
        heartbeat = self.directory / "heartbeat"
        before = heartbeat.read_text()
        time.sleep(.15)
        self.assertEqual(before, heartbeat.read_text(), "native grandchild continued writing after supervisor returned")

    def test_timeout_stops_native_parent_and_grandchild(self):
        result = bounded.run(self.command("wait"), timeout=1, grace=2)
        self.assertEqual(result.returncode, 124)
        self.assert_writer_stopped()

    def test_parent_early_exit_still_stops_native_grandchild(self):
        result = bounded.run(self.command("early"), timeout=5, grace=2)
        self.assertEqual(result.returncode, 0)
        self.assert_writer_stopped()

    def test_outer_timeout_also_drains_a_nested_job_and_its_native_descendants(self):
        source = ("import sys;sys.path.insert(0,sys.argv[1]);import bounded;"
                  "bounded.run(sys.argv[2:], timeout=30, grace=2)")
        result = bounded.run([sys.executable, "-B", "-c", source,
                              str(REPO / "scripts/cache"), *self.command("wait")], timeout=1, grace=2)
        self.assertEqual(result.returncode, 124)
        self.assert_writer_stopped()

    def test_supervisor_crash_closes_last_job_handle_and_stops_native_descendants(self):
        source = ("import sys;sys.path.insert(0,sys.argv[1]);import bounded;"
                  "bounded.run(sys.argv[2:], timeout=30, grace=2)")
        supervisor = subprocess.Popen([sys.executable, "-B", "-c", source,
                                       str(REPO / "scripts/cache"), *self.command("wait")])
        try:
            deadline = time.monotonic() + 5
            while not (self.directory / "heartbeat").exists():
                self.assertIsNone(supervisor.poll(), "supervisor exited before native fixture started")
                self.assertLess(time.monotonic(), deadline)
                time.sleep(.025)
            supervisor.kill()
            supervisor.wait(timeout=5)
            time.sleep(.1)
            self.assert_writer_stopped()
        finally:
            if supervisor.poll() is None:
                supervisor.kill()
                supervisor.wait(timeout=5)


if __name__ == "__main__":
    unittest.main()
