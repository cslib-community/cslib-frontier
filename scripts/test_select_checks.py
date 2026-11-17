"""Regressions for scheduling expensive CI on the exact validation diff."""

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
            self.assertEqual(classify("pull_request", [path]), (False, False))
            self.assertEqual(classify("merge_group", [path]), (True, False))
        for path in ("CslibFrontier/Algorithms/Example.lean", "CslibFrontierTests/A.lean",
                     "CslibFrontier.lean", "references.bib"):
            self.assertEqual(classify("pull_request", ["README.md", path]), (True, False))
        for path in ("manual/programs-crypto-and-probability/assumptions.md", "lakefile.toml",
                     "tools/cache-origin/main.go", "scripts/test_cache_dashboard_frontend.cjs",
                     ".github/workflows/lean_action_ci.yml", "policy/nested/unknown.md"):
            self.assertEqual(classify("pull_request", ["README.md", path]), (True, True))
        for event in ("push", "workflow_dispatch", "other"):
            self.assertEqual(classify(event, ["README.md"]), (True, True))
        self.assertEqual(classify("pull_request", []), (True, True))

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
            checkout = lambda *args: subprocess.check_output(["git", "-C", tmp, *args])
            payload = {"pull_request": {"head": {"sha": head}, "base": {"sha": head}}}
            with patch.object(select_checks, "git", side_effect=checkout):
                self.assertCountEqual(select_checks.event_paths("pull_request", payload, merge),
                                      ["README.md", "tool.py"])
                payload["pull_request"]["head"]["sha"] = base
                with self.assertRaises(ValueError):
                    select_checks.event_paths("pull_request", payload, merge)
