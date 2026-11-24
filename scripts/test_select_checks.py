"""Regressions for scheduling expensive CI on the exact validation diff."""

from contextlib import chdir
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from scripts.ci import select_checks


class SelectionTests(unittest.TestCase):
    def test_event_and_paths(self):
        classify = select_checks.classify
        for path in ("policy/review.md", "results/arora-barak.md", "ROADMAP.md"):
            self.assertEqual(classify("pull_request", [path]), (False, False, False))
            self.assertEqual(classify("merge_group", [path]), (True, False, False))
        for path in ("CslibFrontier/Algorithms/Example.lean", "CslibFrontierTests/A.lean",
                     "CslibFrontierResults/Entries/FGLSS.lean", "CslibFrontierResults.lean",
                     "CslibFrontier.lean", "references.bib"):
            self.assertEqual(classify("pull_request", ["README.md", path]), (True, False, False))
            self.assertEqual(classify("merge_group", ["README.md", path]), (True, False, False))
        for path in ("manual/programs-crypto-and-probability/assumptions.md",
                     "manual/workflows/contributing.md", "manual/AGENT_OPERATORS.md"):
            self.assertEqual(classify("pull_request", ["README.md", path]), (True, True, False))
            self.assertEqual(classify("merge_group", ["README.md", path]), (True, True, False))
        self.assertEqual(classify("pull_request", ["CslibFrontierResults/Registry.lean"]),
                         (True, False, True))
        for path in ("lakefile.toml", "lake-manifest.json", "lean-toolchain",
                     "tools/cache-origin/main.go", "scripts/test_cache_dashboard_frontend.cjs",
                     "scripts/check_hygiene.py", "scripts/check_timem.py",
                     "manual/data/build_latex.py", "manual/data/notes.md",
                     "manual/workflows/data/models-excerpts.json",
                     "guide/Guide/Example.lean", ".github/workflows/lean_action_ci.yml",
                     "policy/nested/unknown.md"):
            self.assertEqual(classify("pull_request", ["README.md", path]), (True, True, True))
            self.assertEqual(classify("merge_group", ["README.md", path]), (True, True, True))
        for event in ("push", "workflow_dispatch", "other"):
            self.assertEqual(classify(event, ["README.md"]), (True, True, True))
        self.assertEqual(classify("pull_request", []), (True, True, True))

    def test_main_writes_all_outputs_and_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp, "github_output")
            event_file = Path(tmp, "event.json")
            event_file.write_text(json.dumps({"pull_request": {"head": {"sha": "deadbeef"}}}))
            with patch.dict(os.environ, {
                "GITHUB_EVENT_NAME": "pull_request",
                "GITHUB_EVENT_PATH": str(event_file),
                "GITHUB_SHA": "deadbeef",
                "GITHUB_OUTPUT": str(out),
                "FORCE_FULL_CI": "1",
            }, clear=False):
                select_checks.main()
            self.assertEqual(out.read_text(), "lean=true\norigin=true\ntooling=true\n")
            out.write_text("")
            with patch.dict(os.environ, {
                "GITHUB_EVENT_NAME": "pull_request",
                "GITHUB_EVENT_PATH": str(Path(tmp, "missing.json")),
                "GITHUB_SHA": "deadbeef",
                "GITHUB_OUTPUT": str(out),
                "FORCE_FULL_CI": "",
            }, clear=False):
                select_checks.main()
            self.assertEqual(out.read_text(), "lean=true\norigin=true\ntooling=true\n")

    def test_merge_parent_comparison_includes_deleted_and_renamed_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            def git(*args):
                return subprocess.check_output(["git", "-C", tmp, *args], text=True,
                                               stderr=subprocess.DEVNULL).strip()
            git("init", "-b", "main")
            git("config", "user.name", "CI fixture")
            git("config", "user.email", "ci@example.invalid")
            source = Path(tmp, "tool.py")
            source.write_text("tool\n")
            git("add", ".")
            git("commit", "-m", "base")
            base = git("rev-parse", "HEAD")
            git("switch", "-c", "topic")
            git("mv", "tool.py", "README.md")
            git("commit", "-m", "rename")
            head = git("rev-parse", "HEAD")
            git("switch", "main")
            git("merge", "--no-ff", "topic", "-m", "test merge")
            merge = git("rev-parse", "HEAD")
            payload = {"pull_request": {"head": {"sha": head}, "base": {"sha": head}}}
            with chdir(tmp):
                self.assertCountEqual(select_checks.event_paths("pull_request", payload, merge),
                                      ["README.md", "tool.py"])
                payload["pull_request"]["head"]["sha"] = base
                with self.assertRaises(ValueError):
                    select_checks.event_paths("pull_request", payload, merge)
                group = {"merge_group": {"head_sha": merge, "base_sha": base}}
                self.assertCountEqual(select_checks.event_paths("merge_group", group, merge),
                                      ["README.md", "tool.py"])
                group["merge_group"]["head_sha"] = head
                with self.assertRaises(ValueError):
                    select_checks.event_paths("merge_group", group, merge)
