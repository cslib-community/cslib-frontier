"""Exact-attempt cache selection, archive safety and transactional build restoration."""

import contextlib
import copy
import gzip
import io
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import time
import unittest
from unittest.mock import patch

import cache_handoff as handoff


REPOSITORY = "cslib-community/cslib-frontier"


class API:
    def __init__(self, context):
        sha = context["source_sha"]
        self.workflow = {"id": 7, "path": handoff.WORKFLOW_PATH, "state": "active"}
        self.runs = [{"id": 101, "run_number": 20, "run_attempt": 1, "workflow_id": 7,
                      "path": handoff.WORKFLOW_PATH, "head_sha": sha, "event": "merge_group",
                      "head_branch": "gh-readonly-queue/main/pr-1-parent",
                      "status": "completed", "conclusion": "success",
                      "repository": {"id": 9, "full_name": REPOSITORY},
                      "head_repository": {"id": 9, "full_name": REPOSITORY}}]
        self.artifact = {
            "id": 303, "name": handoff.artifact_name(context, 101, 1), "expired": False,
            "size_in_bytes": 1000,
            "workflow_run": {"id": 101, "head_sha": sha, "repository_id": 9,
                             "head_repository_id": 9},
        }
        self.current = None
        self.calls = []

    def __call__(self, endpoint, *, paginate=False):
        self.calls.append((endpoint, paginate))
        if endpoint.endswith(handoff.WORKFLOW_FILE):
            return copy.deepcopy(self.workflow)
        if "/workflows/7/runs?" in endpoint:
            return copy.deepcopy([{"total_count": len(self.runs), "workflow_runs": self.runs}])
        if "/artifacts?" in endpoint:
            artifacts = [] if self.artifact is None else [self.artifact]
            return copy.deepcopy([{"total_count": len(artifacts), "artifacts": artifacts}])
        if "/actions/runs/" in endpoint:
            return copy.deepcopy(self.current or next(
                run for run in self.runs if endpoint.endswith(str(run["id"]))))
        raise AssertionError(f"Unexpected API request: {endpoint}")


class HandoffTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="build-handoff-test-")
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / "checkout"
        self.root.mkdir()
        for name in handoff.INPUTS:
            (self.root / name).write_text(name + "\n")
        (self.root / ".gitignore").write_text(".lake/\n")
        for command in (["git", "init", "-q"], ["git", "add", "."],
                        ["git", "-c", "commit.gpgsign=false", "-c", "user.name=Test",
                         "-c", "user.email=test@example.invalid",
                         "commit", "-qm", "Fixture"]):
            subprocess.run(command, cwd=self.root, check=True, capture_output=True)
        sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=self.root, text=True).strip()
        self.env = {"GITHUB_REPOSITORY": REPOSITORY, "GITHUB_SHA": sha,
                    "GITHUB_EVENT_NAME": "merge_group", "GITHUB_RUN_ID": "101",
                    "GITHUB_RUN_ATTEMPT": "1", "RUNNER_OS": "Linux", "RUNNER_ARCH": "X64",
                    "ImageOS": "ubuntu24", "ImageVersion": "20261017.1",
                    "GITHUB_OUTPUT": str(self.base / "outputs")}
        self.build = self.root / ".lake/build"
        (self.build / "lib/lean").mkdir(parents=True)
        (self.build / "lib/lean/Example.olean").write_bytes(b"compiled")
        os.utime(self.build / "lib/lean/Example.olean", (1_700_000_000, 1_700_000_000))
        (self.build / "lib/lean/Example.trace").write_bytes(b"trace")
        (self.build / "bin").mkdir()
        (self.build / "bin/check").write_bytes(b"executable")
        (self.build / "bin/check").chmod(0o755)
        self.output = self.base / "packed"
        self.api = API(handoff.source_context(self.root, self.env, "merge_group"))

    def pack(self):
        with contextlib.redirect_stdout(io.StringIO()):
            return handoff.pack(self.root, self.output, self.env)

    def download(self, repository, run_id, name, destination):
        self.assertEqual((repository, run_id, name),
                         (REPOSITORY, 101, self.api.artifact["name"]))
        for source in self.output.iterdir():
            shutil.copyfile(source, destination / source.name)

    def restore(self, downloader=None):
        env = {**self.env, "GITHUB_EVENT_NAME": "push", "GITHUB_REF": "refs/heads/main"}
        with contextlib.redirect_stdout(io.StringIO()):
            handoff.restore(self.root, env, api=self.api, downloader=downloader or self.download)

    def metadata(self, change):
        path = self.output / "metadata.json"
        data = json.loads(path.read_text())
        change(data)
        path.write_text(json.dumps(data))

    def test_recovery_generation_rejects_preincident_handoff_without_installing(self):
        self.pack()
        original = (self.build / "lib/lean/Example.olean").read_bytes()
        self.env["CACHE_RECOVERY_GENERATION"] = "incident-20261106-1"
        with self.assertRaisesRegex(handoff.Rejected, "compatible run-attempt"):
            self.restore(lambda *args: self.fail("Downloaded an incompatible recovery generation"))
        self.assertEqual((self.build / "lib/lean/Example.olean").read_bytes(), original)

    def test_cache_recovery_disables_handoff_before_packing_or_api_access(self):
        self.env["DISABLE_CACHE_RESTORE"] = "true"
        with self.assertRaisesRegex(handoff.Rejected, "cache recovery"):
            self.pack()
        with self.assertRaisesRegex(handoff.Rejected, "cache recovery"):
            self.restore()
        self.assertFalse(self.output.exists())
        self.assertEqual(self.api.calls, [])

    def replace_archive(self, members):
        archive = self.output / "build.tar.gz"
        size = 0
        with tarfile.open(archive, "w:gz") as bundle:
            for name, kind, data in members:
                member = tarfile.TarInfo(name)
                member.type = kind
                member.size = len(data) if kind == tarfile.REGTYPE else 0
                member.linkname = "/tmp/outside" if kind in (tarfile.SYMTYPE, tarfile.LNKTYPE) else ""
                size += member.size
                bundle.addfile(member, io.BytesIO(data))
        self.metadata(lambda meta: meta.update(archive={
            "sha256": handoff.digest(archive), "files": len(members), "bytes": max(1, size),
            "compressed_bytes": archive.stat().st_size,
        }))

    def test_roundtrip_preserves_executable_and_replaces_hardlinks_without_modifying_cache(self):
        shared = self.base / "shared-artifact"
        shared.write_bytes(b"shared")
        os.link(shared, self.build / "lib/lean/Linked.olean")
        name = self.pack()
        self.assertIn(f"artifact-name={name}", (self.base / "outputs").read_text())
        with tarfile.open(self.output / "build.tar.gz") as bundle:
            self.assertTrue(all(member.isfile() for member in bundle))
        # The consumer's old output is another hardlink to an immutable cache entry.
        old = self.base / "old-artifact"
        old.write_bytes(b"old")
        (self.build / "lib/lean/Example.olean").unlink()
        os.link(old, self.build / "lib/lean/Example.olean")
        (self.build / "stale-file").write_text("old output absent from producer")
        self.restore()
        self.assertEqual((self.build / "lib/lean/Example.olean").read_bytes(), b"compiled")
        self.assertEqual((self.build / "lib/lean/Example.olean").stat().st_mtime, 1_700_000_000)
        self.assertEqual(old.read_bytes(), b"old")
        self.assertEqual(shared.read_bytes(), b"shared")
        self.assertEqual((self.build / "lib/lean/Linked.olean").read_bytes(), b"shared")
        self.assertTrue(os.access(self.build / "bin/check", os.X_OK))
        self.assertFalse((self.build / "stale-file").exists())
        self.assertEqual([path.name for path in self.build.parent.iterdir()], ["build"])
        listings = [url for url, paginate in self.api.calls if "/runs?" in url]
        self.assertEqual(len(listings), 2)
        self.assertTrue(all("event=merge_group" in url and "status=" not in url for url in listings))

    def test_pack_requires_clean_matching_checkout_and_known_platform(self):
        for changes in ({"GITHUB_SHA": "f" * 40}, {"GITHUB_EVENT_NAME": "pull_request"},
                        {"ImageOS": ""}, {"GITHUB_RUN_ATTEMPT": "0"},
                        {"DISABLE_BUILD_HANDOFF": "1"}, {"DISABLE_BUILD_HANDOFF": "true"}):
            with self.subTest(changes=changes), self.assertRaises(handoff.Rejected):
                handoff.pack(self.root, self.output, {**self.env, **changes})
        for index, allowed in enumerate(("0", "false", "FALSE", "no")):
            with self.subTest(allowed=allowed), contextlib.redirect_stdout(io.StringIO()):
                self.assertTrue(handoff.pack(
                    self.root, self.base / f"packed-{index}-{allowed}",
                    {**self.env, "DISABLE_BUILD_HANDOFF": allowed}))
        (self.base / "outputs").unlink()
        (self.root / "lean-toolchain").write_text("changed")
        with self.assertRaises(handoff.Rejected):
            self.pack()
        self.assertFalse((self.base / "outputs").exists())

    @unittest.skipUnless(shutil.which("pigz"), "parallel gzip is optional")
    def test_parallel_and_fallback_compression_write_the_same_tar(self):
        with patch.object(handoff.shutil, "which", return_value=None):
            self.pack()
        with gzip.open(self.output / "build.tar.gz", "rb") as archive:
            expected = archive.read()
        self.output = self.base / "parallel"
        self.pack()
        with gzip.open(self.output / "build.tar.gz", "rb") as archive:
            self.assertEqual(archive.read(), expected)
        self.restore()

    def test_failed_compressor_never_advertises_partial_output(self):
        compressor = self.base / "bad-compressor"
        compressor.write_text("#!/bin/sh\ncat >/dev/null\nexit 23\n")
        compressor.chmod(0o755)
        with patch.object(handoff.shutil, "which", return_value=str(compressor)), \
                self.assertRaises(subprocess.CalledProcessError) as failed:
            self.pack()
        self.assertEqual(failed.exception.returncode, 23)
        self.assertFalse(self.output.exists())
        self.assertFalse((self.base / "outputs").exists())

    def test_kill_switch_disables_restore_before_contacting_api(self):
        for value in ("1", "true", "TRUE", "yes"):
            env = {**self.env, "GITHUB_EVENT_NAME": "push", "GITHUB_REF": "refs/heads/main",
                   "DISABLE_BUILD_HANDOFF": value}
            with self.subTest(value=value), self.assertRaises(handoff.Rejected):
                handoff.restore(
                    self.root, env,
                    api=lambda *args, **kwargs: self.fail("API called when handoff disabled"),
                    downloader=lambda *args: self.fail("Downloaded when handoff disabled"),
                )

    def test_pack_rejects_symlinks_and_empty_build(self):
        link = self.build / "linked-dir"
        link.symlink_to(self.base, target_is_directory=True)
        with self.assertRaises(handoff.Rejected):
            self.pack()
        link.unlink()
        shutil.rmtree(self.build)
        self.build.mkdir()
        with self.assertRaises(handoff.Rejected):
            self.pack()

    def test_pack_omits_only_module_setup_inputs_after_file_type_checks(self):
        omitted = ("ir/Example.setup.json", "ir/Nested/Example.irsetup.json")
        retained = ("ir/report.json", "lib/lean/Example.setup.json", "ir/Example.setup.json.hash")
        for name in omitted + retained:
            path = self.build / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"setup input" * 100 if name in omitted else b"retained")
        kept = [p for p in self.build.rglob("*") if p.is_file()
                and p.relative_to(self.build).as_posix() not in omitted]
        total = sum(p.stat().st_size for p in kept)
        # The quota still applies to the actual payload; the omitted inputs alone exceed it.
        with patch.object(handoff, "MAX_BYTES", total):
            self.pack()
        with tarfile.open(self.output / "build.tar.gz") as bundle:
            names = set(bundle.getnames())
        for name in omitted:
            self.assertNotIn(f".lake/build/{name}", names)
            self.assertTrue((self.build / name).is_file())
        for name in retained:
            self.assertIn(f".lake/build/{name}", names)
        inventory = json.loads((self.output / "metadata.json").read_text())["archive"]
        self.assertEqual((inventory["files"], inventory["bytes"]), (len(kept), total))

        for directory in (False, True):
            link = self.build / "ir/Linked.setup.json"
            link.symlink_to(self.base if directory else self.root / "lakefile.toml",
                            target_is_directory=directory)
            with self.assertRaisesRegex(handoff.Rejected, "Non-regular build output"):
                handoff.pack(self.root, self.base / f"links-{directory}", self.env)
            link.unlink()

    def test_limit_miss_reports_actual_inventory_and_omission(self):
        (self.build / "ir").mkdir()
        (self.build / "ir/Example.setup.json").write_bytes(b"setup")
        total = sum(p.stat().st_size for p in self.build.rglob("*")
                    if p.is_file() and not handoff.module_setup_input(p.relative_to(self.build)))
        with patch.object(handoff, "MAX_BYTES", 1), self.assertRaises(handoff.Rejected) as error:
            self.pack()
        self.assertIn(f"3 files / {total} bytes", str(error.exception))
        self.assertIn(f"limits {handoff.MAX_FILES} files / 1 bytes", str(error.exception))
        self.assertIn("omitted 1 module setup inputs / 5 bytes", str(error.exception))
        self.assertFalse(self.output.exists())

    def test_setup_inputs_alone_do_not_make_a_nonempty_payload(self):
        shutil.rmtree(self.build)
        path = self.build / "ir/Example.setup.json"
        path.parent.mkdir(parents=True)
        path.write_text("setup")
        with self.assertRaisesRegex(handoff.Rejected, "0 files / 0 bytes"):
            self.pack()
        self.assertTrue(path.is_file())
        self.assertFalse(self.output.exists())

    @unittest.skipUnless(os.environ.get("COMPLEXITYLIB_TEST_LAKE_HANDOFF") == "1",
                         "real Lake regression runs after Lean installation")
    def test_real_lake_reuses_module_and_native_outputs_without_setup_inputs(self):
        # No dependencies or shared artifact cache: reuse must come from the handoff itself.
        shutil.rmtree(self.build)
        (self.root / "lean-toolchain").write_bytes((handoff.ROOT / "lean-toolchain").read_bytes())
        (self.root / "lake-manifest.json").unlink()
        (self.root / "lakefile.toml").write_text(
            'name = "handoff_fixture"\nenableArtifactCache = false\n'
            '[leanOptions]\ncompiler.postponeCompile = true\n'
            '[[lean_lib]]\nname = "Fixture"\n'
            '[[lean_exe]]\nname = "fixture"\nroot = "Main"\n')
        (self.root / "Fixture").mkdir()
        basic = ("module\nnamespace Fixture\n"
                 "@[noinline] public def twice (n : Nat) : Nat := n + n\nend Fixture\n")
        (self.root / "Fixture/Basic.lean").write_text(basic)
        (self.root / "Fixture.lean").write_text(
            "module\npublic import Fixture.Basic\n"
            "namespace Fixture\npublic def answer : Nat := twice 21\nend Fixture\n")
        (self.root / "Main.lean").write_text(
            "import Fixture\ndef main : IO Unit := IO.println Fixture.answer\n")
        env = {**os.environ, "LAKE_CACHE_DIR": str(self.base / "producer-lake-cache"),
               "LEAN_NUM_THREADS": "2"}

        def run(*args, cwd=None):
            result = subprocess.run(args, cwd=cwd or self.root, env=env, text=True,
                                    capture_output=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return result.stdout

        run("lake", "build", "--wfail", "--iofail", "fixture")
        setup = [p.relative_to(self.build) for p in self.build.rglob("*.json")
                 if handoff.module_setup_input(p.relative_to(self.build))]
        self.assertTrue(any(p.name.endswith(".setup.json") for p in setup))
        self.assertTrue(any(p.name.endswith(".irsetup.json") for p in setup))
        for name in ("lib/lean/Fixture/Basic.olean.server", "lib/lean/Fixture/Basic.olean.private",
                     "lib/lean/Fixture/Basic.ir", "ir/Fixture/Basic.c", "bin/fixture"):
            self.assertTrue((self.build / name).is_file(), name)
        # Model archives inherited from an earlier main publication. An ordinary merge-group
        # build and handoff should retain them without another archive-preparation phase.
        run("lake", "build", "--no-build", "--wfail", "--iofail", "Fixture", "-o",
            str(self.base / "producer-mapping.jsonl"))
        self.assertEqual(len(list(self.build.rglob("*.ltar"))), 2)
        run("lake", "build", "--wfail", "--iofail", "fixture")
        run("git", "add", ".")
        run("git", "-c", "commit.gpgsign=false", "-c", "user.name=Test",
            "-c", "user.email=test@example.invalid", "commit", "-qm", "Real Lake fixture")
        self.env["GITHUB_SHA"] = run("git", "rev-parse", "HEAD").strip()
        self.api = API(handoff.source_context(self.root, self.env, "merge_group"))
        self.pack()
        self.assertTrue(all((self.build / p).is_file() for p in setup))

        consumer = self.base / "consumer"
        run("git", "clone", "--no-local", "-q", str(self.root), str(consumer))
        self.root = consumer
        self.build = consumer / ".lake/build"
        self.build.parent.mkdir()
        env["LAKE_CACHE_DIR"] = str(self.base / "empty-consumer-lake-cache")
        self.restore()
        self.assertTrue(all(not (self.build / p).exists() for p in setup))
        outputs = {p.relative_to(self.build): (handoff.digest(p), p.stat().st_mtime_ns)
                   for p in self.build.rglob("*") if p.is_file() and p.suffix != ".hash"}
        # --no-build rejects any required rebuild. The ordinary build must also leave the
        # compiled modules, IR, executable and saved traces unchanged, without setup inputs.
        run("lake", "build", "--no-build", "fixture")
        run("lake", "build", "fixture")
        run("lake", "build", "--no-build", "--wfail", "--iofail", "Fixture", "-o",
            str(self.base / "consumer-mapping.jsonl"))
        self.assertTrue(all(not (self.build / p).exists() for p in setup))
        for name, expected in outputs.items():
            path = self.build / name
            self.assertEqual((handoff.digest(path), path.stat().st_mtime_ns), expected, str(name))
        self.assertEqual(run(str(self.build / "bin/fixture")).strip(), "42")

        # A genuine source change still compiles and recreates both kinds of setup input.
        archive = self.build / "ir/Fixture/Basic.ltar"
        original_archive = handoff.digest(archive)
        (consumer / "Fixture/Basic.lean").write_text(basic.replace("n + n", "n + n + 1"))
        run("lake", "build", "fixture")
        self.assertTrue((self.build / "ir/Fixture/Basic.setup.json").is_file())
        self.assertTrue((self.build / "ir/Fixture/Basic.irsetup.json").is_file())
        self.assertEqual(run(str(self.build / "bin/fixture")).strip(), "43")
        self.assertFalse(archive.exists(), "Lake must invalidate the changed module's archive")
        run("lake", "build", "--no-build", "--wfail", "--iofail", "Fixture", "-o",
            str(self.base / "changed-mapping.jsonl"))
        self.assertNotEqual(handoff.digest(archive), original_archive)

    def test_identity_mismatch_or_unsuccessful_run_never_downloads(self):
        cases = ({"head_sha": "f" * 40}, {"event": "pull_request"},
                 {"event": "workflow_dispatch"}, {"workflow_id": 8},
                 {"path": ".github/workflows/fake.yml"}, {"head_branch": "feature"},
                 {"head_repository": {"id": 10, "full_name": REPOSITORY}},
                 {"repository": {"id": 9, "full_name": "other/repo"}},
                 {"run_attempt": 0}, {"status": "in_progress", "conclusion": None},
                 {"conclusion": "failure"}, {"conclusion": "cancelled"})
        for changes in cases:
            self.api = API(handoff.source_context(self.root, self.env, "merge_group"))
            self.api.runs[0].update(changes)
            with self.subTest(changes=changes), self.assertRaises(handoff.Rejected):
                self.restore(lambda *args: self.fail("Downloaded before validating the run"))

    def test_latest_failed_run_and_current_rerun_override_old_success(self):
        self.api.runs.append({**self.api.runs[0], "id": 102, "run_number": 21,
                              "conclusion": "failure"})
        with self.assertRaises(handoff.Rejected):
            self.restore()
        self.api = API(handoff.source_context(self.root, self.env, "merge_group"))
        self.api.current = {**self.api.runs[0], "run_attempt": 2,
                            "status": "in_progress", "conclusion": None}
        with self.assertRaises(handoff.Rejected):
            self.restore()

    def test_missing_expired_or_wrong_attempt_artifact_is_a_miss(self):
        for changes in (None, {"expired": True}, {"name": "old-attempt"},
                        {"size_in_bytes": handoff.MAX_ARCHIVE_BYTES + handoff.MAX_METADATA_BYTES + 1},
                        {"workflow_run": {"id": 100}}):
            self.api = API(handoff.source_context(self.root, self.env, "merge_group"))
            if changes is None:
                self.api.artifact = None
            else:
                self.api.artifact.update(changes)
            with self.subTest(changes=changes), self.assertRaises(handoff.Rejected):
                self.restore(lambda *args: self.fail("Downloaded invalid artifact"))

    def test_configuration_platform_attempt_and_digest_mismatch_leave_old_outputs(self):
        self.pack()
        original = (self.output / "metadata.json").read_bytes()
        changes = (lambda meta: meta.update(source_sha="f" * 40),
                   lambda meta: meta["inputs"].update({"lean-toolchain": "different"}),
                   lambda meta: meta["platform"].update(RUNNER_ARCH="ARM64"),
                   lambda meta: meta["platform"].update(ImageVersion="different"),
                   lambda meta: meta["producer"].update(run_attempt=2),
                   lambda meta: meta["archive"].update(sha256="0" * 64),
                   lambda meta: meta["archive"].update(files=handoff.MAX_FILES + 1))
        for change in changes:
            (self.output / "metadata.json").write_bytes(original)
            self.metadata(change)
            with self.assertRaises(handoff.Rejected):
                self.restore()
            self.assertEqual((self.build / "lib/lean/Example.olean").read_bytes(), b"compiled")

    def test_unsafe_tar_members_are_rejected_before_install(self):
        self.pack()
        bad = [("/tmp/escape", tarfile.REGTYPE, b"x"),
               (".lake/build/../../escape", tarfile.REGTYPE, b"x"),
               (".lake/build/./dot", tarfile.REGTYPE, b"x"),
               (".lake/build//double", tarfile.REGTYPE, b"x"),
               (".lake/build/a\\b", tarfile.REGTYPE, b"x"),
               (".lake/packages/injection", tarfile.REGTYPE, b"x"),
               (".lake/build/link", tarfile.SYMTYPE, b""),
               (".lake/build/link", tarfile.LNKTYPE, b""),
               (".lake/build/device", tarfile.CHRTYPE, b""),
               (".lake/build/fifo", tarfile.FIFOTYPE, b""),
               (".lake/build/directory", tarfile.DIRTYPE, b"")]
        for member in bad:
            self.replace_archive([member])
            with self.subTest(member=member), self.assertRaises(handoff.Rejected):
                self.restore()
        duplicate = (".lake/build/repeated", tarfile.REGTYPE, b"x")
        self.replace_archive([duplicate, duplicate])
        with self.assertRaises(handoff.Rejected):
            self.restore()
        self.assertEqual((self.build / "lib/lean/Example.olean").read_bytes(), b"compiled")

    def test_run_or_artifact_change_during_download_does_not_install(self):
        self.pack()
        for kind in ("run", "attempt", "failure", "artifact", "expired"):
            self.api = API(handoff.source_context(self.root, self.env, "merge_group"))
            def download(*args):
                self.download(*args)
                if kind == "run":
                    self.api.runs.append({**self.api.runs[0], "id": 102, "run_number": 21})
                elif kind == "attempt":
                    self.api.runs[0]["run_attempt"] = 2
                elif kind == "failure":
                    self.api.runs[0]["conclusion"] = "failure"
                elif kind == "artifact":
                    self.api.artifact["id"] = 304
                else:
                    self.api.artifact["expired"] = True
            with self.subTest(kind=kind), self.assertRaises(handoff.Rejected):
                self.restore(download)
        self.assertEqual((self.build / "lib/lean/Example.trace").read_bytes(), b"trace")

    def test_symlink_build_boundary_is_not_followed(self):
        self.pack()
        target = self.base / "outside"
        self.build.rename(target)
        self.build.symlink_to(target, target_is_directory=True)
        with self.assertRaises(handoff.Rejected):
            self.restore()
        self.assertTrue(self.build.is_symlink())
        self.assertEqual((target / "lib/lean/Example.olean").read_bytes(), b"compiled")

    def test_symlink_lake_boundary_is_not_followed(self):
        self.pack()
        target = self.base / "outside-lake"
        self.build.parent.rename(target)
        self.build.parent.symlink_to(target, target_is_directory=True)
        with self.assertRaises(handoff.Rejected):
            self.restore()
        self.assertEqual((target / "build/lib/lean/Example.olean").read_bytes(), b"compiled")
        self.assertEqual([path.name for path in target.iterdir()], ["build"])

    def test_missing_consumer_build_is_restored(self):
        self.pack()
        shutil.rmtree(self.build)
        self.restore()
        self.assertEqual((self.build / "lib/lean/Example.olean").read_bytes(), b"compiled")

    def test_download_failure_and_truncated_archive_leave_complete_old_build(self):
        self.pack()
        def failed_download(*args):
            raise subprocess.TimeoutExpired("gh", 120)
        with self.assertRaises(subprocess.TimeoutExpired):
            self.restore(failed_download)
        archive = self.output / "build.tar.gz"
        archive.write_bytes(archive.read_bytes()[:20])
        self.metadata(lambda meta: meta["archive"].update(
            sha256=handoff.digest(archive), compressed_bytes=archive.stat().st_size))
        with self.assertRaises((EOFError, tarfile.TarError)):
            self.restore()
        self.assertEqual((self.build / "lib/lean/Example.olean").read_bytes(), b"compiled")
        self.assertEqual((self.build / "lib/lean/Example.trace").read_bytes(), b"trace")
        self.assertEqual([path.name for path in self.build.parent.iterdir()], ["build"])

    def test_failed_install_rolls_back_complete_old_build(self):
        self.pack()
        (self.build / "lib/lean/Example.olean").write_bytes(b"old compiled")
        (self.build / "lib/lean/Example.trace").write_bytes(b"old trace")
        rename = Path.rename
        def fail_install(path, target):
            if "unpacked" in path.parts and path.name == "build":
                raise OSError("simulated install failure")
            return rename(path, target)
        with patch.object(Path, "rename", fail_install), self.assertRaises(OSError):
            self.restore()
        self.assertEqual((self.build / "lib/lean/Example.olean").read_bytes(), b"old compiled")
        self.assertEqual((self.build / "lib/lean/Example.trace").read_bytes(), b"old trace")
        self.assertEqual([path.name for path in self.build.parent.iterdir()], ["build"])

    def test_cli_errors_are_optional_cache_misses(self):
        for error in (handoff.Rejected("not green"), OSError("transport"),
                      subprocess.TimeoutExpired("gh", 60), ValueError("invalid JSON")):
            with self.subTest(error=error), patch("sys.argv", ["cache_handoff.py", "restore"]), \
                    patch.object(handoff, "restore", side_effect=error), \
                    contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertEqual(handoff.main(), 0)
                self.assertIn("continuing without this optional cache", output.getvalue())

    def test_cli_errors_are_workflow_warnings_in_actions(self):
        error = handoff.Rejected("Build output count or size is outside handoff limits: 100%\nx")
        with patch("sys.argv", ["cache_handoff.py", "pack", "--output", "/nonexistent/out"]), \
                patch.dict(os.environ, {"GITHUB_ACTIONS": "true"}), \
                patch.object(handoff, "pack", side_effect=error), \
                contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(handoff.main(), 0)
        line = output.getvalue().strip()
        self.assertTrue(line.startswith("::warning title=Build handoff unavailable::"), line)
        self.assertIn("100%25%0Ax", line)
        self.assertNotIn("\n", line)

    def test_transport_only_uses_get_and_paginates(self):
        with patch.object(subprocess, "run") as invoke:
            invoke.return_value.stdout = "[]"
            handoff.gh_get("repos/example/repo/actions/runs", paginate=True)
        command = invoke.call_args.args[0]
        self.assertIn("GET", command)
        self.assertIn("--paginate", command)
        self.assertIn("--slurp", command)
        self.assertEqual(command[command.index("--hostname") + 1], "github.com")

    def test_default_download_uses_the_handoff_budget(self):
        with patch.object(handoff, "gh_download_artifact") as download:
            handoff.download_handoff("o/r", 7, "lean-build-x", Path("/tmp/d"))
        download.assert_called_once_with("o/r", 7, "lean-build-x", Path("/tmp/d"),
                                         timeout=handoff.DOWNLOAD_SECONDS)

    def test_limits_hold_a_measured_full_build(self):
        # A full build measured on 2026-11-08; the limits must keep headroom above it.
        files, unpacked, packed = 101_848, 4_639_707_458, 1_665_078_866
        self.assertGreaterEqual(handoff.MAX_FILES, 2 * files)
        self.assertGreaterEqual(handoff.MAX_BYTES, 2 * unpacked)
        self.assertGreaterEqual(handoff.MAX_ARCHIVE_BYTES, 2 * packed)


class AncestorAPI:
    """GitHub API fake holding merge-group runs and artifacts for several commits."""

    def __init__(self):
        self.workflow = {"id": 7, "path": handoff.WORKFLOW_PATH, "state": "active"}
        self.runs, self.artifacts, self.calls = {}, {}, []

    def add(self, sha, run_id, name="no-compatible-artifact", **changes):
        run = {"id": run_id, "run_number": run_id, "run_attempt": 1, "workflow_id": 7,
               "path": handoff.WORKFLOW_PATH, "head_sha": sha, "event": "merge_group",
               "head_branch": f"gh-readonly-queue/main/pr-{run_id}-parent",
               "status": "completed", "conclusion": "success",
               "repository": {"id": 9, "full_name": REPOSITORY},
               "head_repository": {"id": 9, "full_name": REPOSITORY}, **changes}
        self.runs.setdefault(sha, []).append(run)
        self.artifacts[run_id] = {
            "id": 1000 + run_id, "name": name, "expired": False,
            "size_in_bytes": 1000,
            "workflow_run": {"id": run_id, "head_sha": sha, "repository_id": 9,
                             "head_repository_id": 9}}

    def listings(self):
        return [url for url, _ in self.calls if "/runs?" in url]

    def __call__(self, endpoint, *, paginate=False):
        self.calls.append((endpoint, paginate))
        if endpoint.endswith(handoff.WORKFLOW_FILE):
            return copy.deepcopy(self.workflow)
        if "/workflows/7/runs?" in endpoint:
            runs = next((runs for sha, runs in self.runs.items()
                         if f"head_sha={sha}&" in endpoint), [])
            return copy.deepcopy([{"total_count": len(runs), "workflow_runs": runs}])
        run_id = int(endpoint.split("/actions/runs/")[1].split("/")[0])
        if "/artifacts?" in endpoint:
            artifacts = [self.artifacts[run_id]] if self.artifacts.get(run_id) else []
            return copy.deepcopy([{"total_count": len(artifacts), "artifacts": artifacts}])
        return copy.deepcopy(next(run for runs in self.runs.values() for run in runs
                                  if run["id"] == run_id))


class AncestorHandoffTests(unittest.TestCase):
    """A merge group may reuse the build of its nearest first-parent ancestor that has one."""

    setUp = HandoffTests.setUp
    metadata = HandoffTests.metadata
    olean = "lib/lean/Example.olean"

    def git(self, *args):
        return subprocess.run(["git", "-c", "commit.gpgsign=false", "-c", "user.name=Test",
                               "-c", "user.email=test@example.invalid", *args], cwd=self.root,
                              check=True, capture_output=True, text=True).stdout.strip()

    def history(self, count, change=None):
        """Add `count` commits; `self.chain[k]` is then the commit k first-parent steps back."""
        for index in range(count):
            if change and index == count - 1:
                (self.root / change).write_text("changed\n")
                self.git("add", change)
            self.git("commit", "-q", "--allow-empty", "-m", f"Landed {index}")
        self.chain = self.git("rev-list", "--first-parent", "HEAD").split()
        self.env["GITHUB_SHA"] = self.chain[0]
        self.api, self.packed = AncestorAPI(), {}

    def handoff(self, back, **changes):
        """Pack the build of the commit `back` steps back, as its own merge-group run did."""
        sha, run_id = self.chain[back], 200 + back
        self.git("checkout", "-q", sha)
        (self.build / self.olean).write_bytes(f"built {back} back".encode())
        output = self.base / f"packed-{len(list(self.base.glob('packed-*')))}"
        with contextlib.redirect_stdout(io.StringIO()):
            name = handoff.pack(self.root, output, {**self.env, "GITHUB_SHA": sha,
                                                    "GITHUB_RUN_ID": str(run_id)})
        self.git("checkout", "-q", self.chain[0])
        (self.build / self.olean).write_bytes(b"stale snapshot")
        self.api.add(sha, run_id, name, **changes)
        self.packed[run_id] = self.output = output

    def download(self, repository, run_id, name, destination):
        self.assertEqual((repository, name), (REPOSITORY, self.api.artifacts[run_id]["name"]))
        self.downloads.append(run_id)
        for source in self.packed[run_id].iterdir():
            shutil.copyfile(source, destination / source.name)

    def restore(self, downloader=None, **arguments):
        self.downloads = []
        with contextlib.redirect_stdout(io.StringIO()) as output:
            handoff.restore_ancestor(self.root, self.env, api=self.api,
                                     downloader=downloader or self.download, **arguments)
        return output.getvalue()

    def assert_miss(self, pattern, downloader=None):
        with self.assertRaisesRegex(handoff.Rejected, pattern):
            self.restore(downloader
                         or (lambda *args: self.fail("Downloaded without a usable handoff")))
        self.assertEqual((self.build / self.olean).read_bytes(), b"stale snapshot")
        self.assertEqual([path.name for path in self.build.parent.iterdir()], ["build"])

    def test_nearest_ancestor_with_a_handoff_is_restored(self):
        self.history(4)
        self.handoff(3)
        self.handoff(2)
        (self.build / "stale-file").write_text("old output absent from producer")
        report = self.restore()
        self.assertEqual(self.downloads, [202])
        self.assertEqual((self.build / self.olean).read_bytes(), b"built 2 back")
        self.assertFalse((self.build / "stale-file").exists())
        self.assertTrue(os.access(self.build / "bin/check", os.X_OK))
        self.assertEqual([path.name for path in self.build.parent.iterdir()], ["build"])
        self.assertIn(f"Build handoff restored from ancestor {self.chain[2]} "
                      "(2 first-parent commits back), run 202 attempt 1", report)
        # One listing each for the ancestor without a run and the chosen one, then the recheck.
        listings = self.api.listings()
        self.assertEqual([url.split("head_sha=")[1][:40] for url in listings],
                         [self.chain[1], self.chain[2], self.chain[2]])
        self.assertTrue(all("event=merge_group" in url for url in listings))

    def test_ancestors_without_a_successful_run_or_artifact_are_skipped(self):
        cases = ({"conclusion": "failure"}, {"conclusion": "cancelled"},
                 {"status": "in_progress", "conclusion": None}, {"event": "pull_request"},
                 {"head_branch": "feature"}, {"workflow_id": 8},
                 {"repository": {"id": 9, "full_name": "other/repo"}})
        for changes in cases:
            with self.subTest(changes=changes):
                self.history(3)
                self.handoff(3)
                self.handoff(2, **changes)
                self.restore()
                self.assertEqual(self.downloads, [203])
                self.assertEqual((self.build / self.olean).read_bytes(), b"built 3 back")
        for changes in (None, {"expired": True}, {"name": "old-attempt"}):
            with self.subTest(artifact=changes):
                self.history(2)
                self.handoff(2)
                self.handoff(1)
                if changes is None:
                    self.api.artifacts[201] = None
                else:
                    self.api.artifacts[201].update(changes)
                self.restore()
                self.assertEqual(self.downloads, [202])

    def test_nearer_build_from_another_runner_image_is_skipped_before_downloading(self):
        self.history(2)
        self.handoff(2)
        with patch.dict(self.env, {"ImageVersion": "next-image"}):
            self.handoff(1)
        self.restore()
        self.assertEqual(self.downloads, [202])
        self.assertEqual((self.build / self.olean).read_bytes(), b"built 2 back")

    def test_a_later_failed_run_of_the_ancestor_overrides_its_old_success(self):
        self.history(2)
        self.handoff(1)
        self.api.add(self.chain[1], 301, conclusion="failure")
        self.assert_miss("None of the 2 nearest")

    def test_search_stops_at_the_ancestor_limit(self):
        self.history(4)
        self.handoff(3)
        with patch.object(handoff, "ANCESTOR_LIMIT", 2):
            self.assert_miss("None of the 2 nearest first-parent ancestors.*nearest: No complete")
        self.assertEqual(len(self.api.listings()), 2)
        with patch.object(handoff, "ANCESTOR_LIMIT", 3):
            self.restore()
        self.assertEqual(self.downloads, [203])

    def test_default_limit_bounds_the_requests_of_a_complete_miss(self):
        self.history(handoff.ANCESTOR_LIMIT + 3)
        self.handoff(handoff.ANCESTOR_LIMIT + 1)
        self.assert_miss(f"None of the {handoff.ANCESTOR_LIMIT} nearest")
        self.assertEqual(len(self.api.calls), 1 + handoff.ANCESTOR_LIMIT)
        self.assertLessEqual(handoff.ANCESTOR_LIMIT, 20)

    def test_the_current_commit_and_a_root_commit_have_no_ancestor_handoff(self):
        self.history(1)
        self.handoff(0)
        self.assert_miss("None of the 1 nearest")
        self.git("checkout", "-q", self.chain[-1])
        self.env["GITHUB_SHA"] = self.chain[-1]
        (self.build / self.olean).write_bytes(b"stale snapshot")
        self.assert_miss("No first-parent ancestor")
        self.assertEqual(self.api.calls[-1][0].split("head_sha=")[1][:40], self.chain[1])

    def test_only_first_parents_are_ancestors(self):
        self.history(1)
        main = self.chain[0]
        self.git("checkout", "-q", "-b", "side", self.chain[1])
        self.git("commit", "-q", "--allow-empty", "-m", "Side")
        side = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "--detach", main)
        self.git("merge", "-q", "--no-ff", "-m", "Merge", side)
        self.chain = self.git("rev-list", "HEAD").split()
        self.env["GITHUB_SHA"] = self.chain[0]
        self.handoff(self.chain.index(side))
        self.assert_miss("None of the 2 nearest")

    def test_changed_toolchain_manifest_or_lakefile_rejects_the_ancestor_build(self):
        for name in handoff.INPUTS:
            with self.subTest(name=name):
                self.history(2, change=name)
                self.handoff(1)
                self.assert_miss("compatible run-attempt")
                self.assertEqual(self.downloads, [])
                self.git("reset", "-q", "--hard", self.chain[2])

    def test_metadata_must_name_the_chosen_ancestor_platform_generation_and_attempt(self):
        self.history(3)
        self.handoff(1)
        original = (self.output / "metadata.json").read_bytes()
        changes = (lambda meta: meta.update(source_sha=self.chain[0]),
                   lambda meta: meta.update(source_sha=self.chain[2]),
                   lambda meta: meta.update(repository="other/repo"),
                   lambda meta: meta.update(cache_recovery_generation="1"),
                   lambda meta: meta["inputs"].update({"lakefile.toml": "different"}),
                   lambda meta: meta["platform"].update(ImageVersion="different"),
                   lambda meta: meta["producer"].update(run_attempt=2),
                   lambda meta: meta["producer"].update(event="push"),
                   lambda meta: meta["archive"].update(sha256="0" * 64))
        for change in changes:
            (self.output / "metadata.json").write_bytes(original)
            self.metadata(change)
            self.assert_miss("mismatch|Invalid archive", self.download)
        self.env["ImageVersion"] = "20261101.1"
        (self.output / "metadata.json").write_bytes(original)
        self.assert_miss("compatible run-attempt")

    def test_only_merge_group_events_may_use_an_ancestor_build(self):
        self.history(2)
        self.handoff(1)
        for changes in ({"GITHUB_EVENT_NAME": "pull_request"},
                        {"GITHUB_EVENT_NAME": "pull_request_target"},
                        {"GITHUB_EVENT_NAME": "push", "GITHUB_REF": "refs/heads/main"},
                        {"GITHUB_EVENT_NAME": "workflow_dispatch"},
                        {"DISABLE_BUILD_HANDOFF": "1"}, {"DISABLE_BUILD_HANDOFF": "true"},
                        {"DISABLE_CACHE_RESTORE": "true"}, {"GITHUB_SHA": self.chain[1]},
                        {"ImageOS": ""}):
            with self.subTest(changes=changes), self.assertRaises(handoff.Rejected):
                handoff.restore_ancestor(
                    self.root, {**self.env, **changes},
                    api=lambda *args, **kwargs: self.fail("API called for a refused event"),
                    downloader=lambda *args: self.fail("Downloaded for a refused event"),
                    deepen=lambda *args: self.fail("Fetched for a refused event"))
        (self.root / "lakefile.toml").write_text("modified\n")
        with self.assertRaisesRegex(handoff.Rejected, "Tracked sources are modified"):
            handoff.restore_ancestor(self.root, self.env, api=self.fail, downloader=self.fail)

    def test_exact_revision_restore_never_accepts_an_ancestor_build(self):
        self.history(2)
        self.handoff(1)
        push = {**self.env, "GITHUB_EVENT_NAME": "push", "GITHUB_REF": "refs/heads/main"}
        for env in (push, self.env):
            with self.subTest(event=env["GITHUB_EVENT_NAME"]), \
                    self.assertRaises(handoff.Rejected):
                handoff.restore(self.root, env, api=self.api, downloader=lambda *args: self.fail(
                    "The exact-revision path downloaded an ancestor's build"))
        self.assertEqual([url.split("head_sha=")[1][:40] for url in self.api.listings()],
                         [self.chain[0]])
        self.assertEqual((self.build / self.olean).read_bytes(), b"stale snapshot")

    def test_exact_revision_restore_keeps_its_requests_and_report(self):
        self.history(1)
        self.handoff(0)
        env = {**self.env, "GITHUB_EVENT_NAME": "push", "GITHUB_REF": "refs/heads/main"}
        self.downloads = []
        with contextlib.redirect_stdout(io.StringIO()) as output:
            handoff.restore(self.root, env, api=self.api, downloader=self.download)
        self.assertEqual(output.getvalue(), "Build handoff restored from run 200 attempt 1; "
                                            "normal build and checks still run\n")
        self.assertEqual((self.build / self.olean).read_bytes(), b"built 0 back")
        prefix, sha = f"repos/{REPOSITORY}/actions/", self.chain[0]
        listing = (f"{prefix}workflows/7/runs?head_sha={sha}&event=merge_group&per_page=100", True)
        lookup = [listing, (f"{prefix}runs/200", False),
                  (f"{prefix}runs/200/artifacts?per_page=100", True)]
        self.assertEqual(self.api.calls,
                         [(f"{prefix}workflows/{handoff.WORKFLOW_FILE}", False)] + 2 * lookup)

    def pr_merge(self):
        self.history(1)
        main = self.chain[0]
        self.git("checkout", "-qb", "feature", self.chain[1])
        self.git("commit", "--allow-empty", "-qm", "Feature")
        self.git("checkout", "-q", "--detach", main)
        self.git("merge", "-q", "--no-ff", "-m", "Test merge", "feature")
        self.chain = self.git("rev-list", "--first-parent", "HEAD").split()
        self.env["GITHUB_SHA"] = self.chain[0]
        self.handoff(1)
        return {**self.env, "GITHUB_EVENT_NAME": "pull_request", "GITHUB_BASE_REF": "main",
                "GITHUB_REF": "refs/pull/1/merge"}

    def test_pr_restores_only_the_checked_out_main_parent_even_in_a_depth_one_checkout(self):
        env = self.pr_merge()
        self.shallow_consumer()
        self.assertEqual(handoff.first_parents(self.root), self.chain[:1])
        self.downloads = []
        with contextlib.redirect_stdout(io.StringIO()) as report:
            handoff.restore(self.root, env, pr_base=True, api=self.api, downloader=self.download)
        self.assertEqual(self.downloads, [201])
        self.assertIn(f"PR base {self.chain[1]}", report.getvalue())
        self.assertEqual((self.build / self.olean).read_bytes(), b"built 1 back")
        self.assertTrue(all(f"head_sha={self.chain[1]}&event=merge_group" in url
                            for url in self.api.listings()))
        self.assertEqual(handoff.first_parents(self.root), self.chain[:1])

    def test_pr_base_requires_a_main_targeting_merge_ref_and_honors_switches_and_warm_snapshot(self):
        env = self.pr_merge()
        for changes in ({"GITHUB_BASE_REF": "stack"}, {"GITHUB_REF": "refs/pull/1/head"},
                        {"GITHUB_REF": "refs/heads/main"}, {"GITHUB_EVENT_NAME": "pull_request_target"},
                        {"DISABLE_BUILD_HANDOFF": "1"}, {"DISABLE_PR_BUILD_HANDOFF": "true"},
                        {"DISABLE_CACHE_RESTORE": "1"}):
            with self.subTest(changes=changes), self.assertRaises(handoff.Rejected):
                handoff.restore(self.root, {**env, **changes}, pr_base=True, api=self.fail,
                                downloader=self.fail)
        with contextlib.redirect_stdout(io.StringIO()):
            handoff.restore(self.root, {**env, "RESTORED_LAKE_KEY": f"lake-key-{self.chain[1]}"},
                            pr_base=True, api=self.fail, downloader=self.fail)
        self.git("checkout", "-q", self.chain[1])
        with self.assertRaisesRegex(handoff.Rejected, "two-parent"):
            handoff.restore(self.root, {**env, "GITHUB_SHA": self.chain[1]}, pr_base=True,
                            api=self.fail, downloader=self.fail)

    def test_pr_base_miss_never_uses_a_pr_artifact_or_an_earlier_ancestor(self):
        env = self.pr_merge()
        self.handoff(2)
        self.api.runs[self.chain[1]][0]["event"] = "pull_request"
        with self.assertRaisesRegex(handoff.Rejected, "exact-source merge group"):
            handoff.restore(self.root, env, pr_base=True, api=self.api, downloader=self.fail)
        self.assertEqual(len(self.api.listings()), 1)
        self.assertEqual((self.build / self.olean).read_bytes(), b"stale snapshot")

    def test_change_during_download_does_not_install(self):
        for kind in ("rerun", "failure", "expired", "checkout", "input"):
            self.history(2)
            self.handoff(1)
            def download(*args):
                self.download(*args)
                if kind == "rerun":
                    self.api.add(self.chain[1], 302)
                elif kind == "failure":
                    self.api.runs[self.chain[1]][0]["conclusion"] = "failure"
                elif kind == "expired":
                    self.api.artifacts[201]["expired"] = True
                elif kind == "checkout":
                    self.git("checkout", "-q", self.chain[1])
                else:
                    (self.root / "lean-toolchain").write_text("moved\n")
            with self.subTest(kind=kind):
                self.assert_miss(".", download)
            self.git("checkout", "-q", "--force", self.chain[0])

    def test_download_failure_does_not_fall_back_to_an_older_build(self):
        self.history(3)
        self.handoff(2)
        self.handoff(1)
        def failed_download(*args):
            self.downloads.append(args[1])
            raise subprocess.TimeoutExpired("gh", 120)
        with self.assertRaises(subprocess.TimeoutExpired):
            self.restore(failed_download)
        self.assertEqual(self.downloads, [201])
        self.assertEqual((self.build / self.olean).read_bytes(), b"stale snapshot")
        self.assertEqual([path.name for path in self.build.parent.iterdir()], ["build"])

    def shallow_consumer(self, depth=1):
        consumer = self.base / "consumer"
        subprocess.run(["git", "clone", "-q", f"--depth={depth}", self.root.as_uri(),
                        str(consumer)], check=True, capture_output=True)
        subprocess.run(["git", "checkout", "-q", "--detach", self.chain[0]], cwd=consumer,
                       check=True, capture_output=True)
        self.root, self.build = consumer, consumer / ".lake/build"
        (self.build / "lib/lean").mkdir(parents=True)
        (self.build / self.olean).write_bytes(b"stale snapshot")

    def test_depth_one_checkout_is_deepened_to_find_the_ancestor(self):
        self.history(4)
        self.handoff(3)
        self.shallow_consumer()
        self.assertEqual(handoff.first_parents(self.root), self.chain[:1])
        self.restore()
        self.assertEqual(self.downloads, [203])
        self.assertEqual((self.build / self.olean).read_bytes(), b"built 3 back")
        self.assertEqual(handoff.first_parents(self.root), self.chain)

    def test_deepening_neither_exceeds_the_limit_nor_shortens_fetched_history(self):
        self.history(6)
        self.handoff(3)
        self.shallow_consumer()
        with patch.object(handoff, "ANCESTOR_LIMIT", 2):
            self.assert_miss("None of the 2 nearest")
            self.assertEqual(self.git("rev-list", "--count", "HEAD"), "3")
        self.git("fetch", "-q", "--depth=6", "origin", self.chain[0])
        with patch.object(handoff, "ANCESTOR_LIMIT", 2):
            handoff.deepen_history(self.root, self.chain[0])
        self.assertEqual(self.git("rev-list", "--count", "HEAD"), "6")

    def test_failed_deepening_uses_available_history(self):
        self.history(3)
        self.handoff(1)
        self.shallow_consumer(depth=2)
        self.git("remote", "set-url", "origin", (self.base / "missing").as_uri())
        report = self.restore()
        self.assertIn("could not deepen the checkout", report)
        self.assertEqual(self.downloads, [201])
        self.git("fetch", "-q", "--depth=1", str(self.base / "checkout"), self.chain[0])
        (self.build / self.olean).write_bytes(b"stale snapshot")
        self.assert_miss("No first-parent ancestor")

    def stalled_fetch(self):
        """Make `git fetch origin` hang in a transport helper that has a child of its own."""
        self.history(3)
        self.handoff(1)
        self.shallow_consumer(depth=2)
        tools = self.base / "tools"
        tools.mkdir()
        helper = tools / "git-remote-stall"
        helper.write_text('#!/bin/sh\nsleep 300 &\necho $! > "$STALL_PIDS/child"\n'
                          'echo $$ > "$STALL_PIDS/helper"\nwait\n')
        helper.chmod(0o755)
        self.git("remote", "set-url", "origin", "stall::unreachable")
        def stop_fixture():  # only after a failure; a passing test has already stopped both
            for name in ("child", "helper"):
                with contextlib.suppress(OSError, ValueError):
                    os.kill(int((tools / name).read_text()), signal.SIGKILL)
        self.addCleanup(stop_fixture)
        return {"PATH": f"{tools}{os.pathsep}{os.environ['PATH']}", "STALL_PIDS": str(tools)}

    def assert_fetch_processes_stopped(self):
        def running(pid):
            try:
                return Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[0] != "Z"
            except OSError:
                return False
        pids = [int((self.base / "tools" / name).read_text()) for name in ("helper", "child")]
        deadline = time.monotonic() + 5
        while any(running(pid) for pid in pids) and time.monotonic() < deadline:
            time.sleep(.05)
        self.assertEqual([pid for pid in pids if running(pid)], [])

    @unittest.skipUnless(sys.platform.startswith("linux"), "inspects /proc")
    def test_timed_out_deepening_stops_git_helpers_before_using_available_history(self):
        environment = self.stalled_fetch()
        stop_group = handoff.bounded_run.__globals__["stop_group"]
        def checked_stop(*args):
            self.assertTrue((self.base / "tools/child").exists(), "helper did not start")
            return stop_group(*args)
        with patch.dict(os.environ, environment), patch.object(handoff, "DEEPEN_SECONDS", 2), \
                patch.dict(handoff.bounded_run.__globals__, {"stop_group": checked_stop}), \
                contextlib.redirect_stderr(io.StringIO()):
            report = self.restore(lambda *args: (self.assert_fetch_processes_stopped(),
                                                 self.download(*args)))
        self.assertIn("could not deepen the checkout; using available history: timed out", report)
        self.assertEqual(self.downloads, [201])
        self.assert_fetch_processes_stopped()

    @unittest.skipUnless(sys.platform.startswith("linux"), "inspects /proc")
    def test_cancelled_deepening_stops_git_helpers_and_does_not_continue(self):
        environment = self.stalled_fetch()
        source = ("import sys; sys.path.insert(0, sys.argv[1]); import cache_handoff as handoff\n"
                  "from pathlib import Path\n"
                  "handoff.deepen_history(Path(sys.argv[2]), sys.argv[3])\n"
                  "print('continued after cancellation')\n")
        process = subprocess.Popen(
            [sys.executable, "-B", "-c", source, str(Path(handoff.__file__).parent),
             str(self.root), self.chain[0]], env={**os.environ, **environment},
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            deadline = time.monotonic() + 10
            while not (self.base / "tools/helper").exists():
                self.assertIsNone(process.poll(), "deepening exited before the helper started")
                self.assertLess(time.monotonic(), deadline)
                time.sleep(.025)
            process.send_signal(signal.SIGTERM)
            stdout, stderr = process.communicate(timeout=20)
        finally:
            if process.poll() is None:
                process.kill()
                process.communicate()
        self.assertNotEqual(process.returncode, 0)
        self.assertIn("KeyboardInterrupt", stderr)
        self.assertNotIn("continued after cancellation", stdout)
        self.assert_fetch_processes_stopped()

    def test_unconfirmed_fetch_shutdown_is_an_error_not_a_miss(self):
        self.history(3)
        self.handoff(1)
        self.shallow_consumer(depth=2)
        def unsafe(*args, **kwargs):
            raise handoff.UnsafeShutdown("cache process group shutdown unconfirmed")
        with patch.object(handoff, "bounded_run", unsafe), \
                self.assertRaises(handoff.UnsafeShutdown):
            self.restore(lambda *args: self.fail("Downloaded after an unconfirmed shutdown"))
        self.assertEqual(self.api.calls, [])
        self.assertEqual((self.build / self.olean).read_bytes(), b"stale snapshot")
        with patch("sys.argv", ["cache_handoff.py", "restore", "--ancestor"]), \
                patch.object(handoff, "restore_ancestor", side_effect=unsafe), \
                contextlib.redirect_stdout(io.StringIO()) as output, \
                contextlib.redirect_stderr(io.StringIO()) as errors:
            self.assertEqual(handoff.main(), 125)
        self.assertEqual(output.getvalue(), "")
        self.assertIn("error: cache process group shutdown unconfirmed", errors.getvalue())

    def test_cli_selects_the_ancestor_path_only_when_asked(self):
        for arguments, called, idle in ((["restore", "--ancestor"], "restore_ancestor", "restore"),
                                        (["restore"], "restore", "restore_ancestor"),
                                        (["restore", "--pr-base"], "restore", "restore_ancestor")):
            with self.subTest(arguments=arguments), \
                    patch("sys.argv", ["cache_handoff.py", *arguments]), \
                    patch.object(handoff, called) as used, patch.object(handoff, idle) as unused:
                self.assertEqual(handoff.main(), 0)
                expected = {"pr_base": True} if "--pr-base" in arguments else {}
                used.assert_called_once_with(handoff.ROOT, os.environ, **expected)
                unused.assert_not_called()
        with patch("sys.argv", ["cache_handoff.py", "restore", "--ancestor"]), \
                patch.dict(os.environ, {"GITHUB_ACTIONS": "true"}), \
                patch.object(handoff, "restore_ancestor", side_effect=handoff.Rejected("none")), \
                contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(handoff.main(), 0)
        self.assertTrue(output.getvalue().startswith(
            "::warning title=Build handoff unavailable::Build handoff unavailable: none;"))


if __name__ == "__main__":
    unittest.main()
