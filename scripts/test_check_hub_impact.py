"""Unit tests for the advisory high-fan-in module impact checker.

Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
"""

from contextlib import redirect_stdout
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_hub_impact as hub  # noqa: E402


class HubImpactTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="hub-impact-test-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.name", "Test")
        self.git("config", "user.email", "test@example.invalid")

    def git(self, *args: str) -> str:
        res = subprocess.run(
            ["git", "-C", str(self.root), *args],
            text=True, capture_output=True, check=True,
        )
        return res.stdout

    def write(self, rel: str, text: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def seed_graph(self) -> str:
        self.write("CslibFrontier/Hub.lean", "module\ndef h := 1\n")
        self.write("CslibFrontier/Mid.lean",
                   "module -- shake: keep-all\npublic import\n  CslibFrontier.Hub\ndef m := h\n")
        self.write("CslibFrontier/LeafA.lean", "module\nimport CslibFrontier.Mid\n")
        self.write("CslibFrontier/LeafB.lean", "module\npublic import CslibFrontier.Mid\n")
        self.write("CslibFrontierTests/Check.lean", "module\nimport CslibFrontier.LeafA\n")
        self.git("add", ".")
        self.git("commit", "-qm", "base")
        return self.git("rev-parse", "HEAD").strip()

    def test_build_reverse_graph_and_transitive_counts(self):
        base = self.seed_graph()
        rev, total = hub.build_reverse_graph(self.root)
        self.assertEqual(total, 5)
        self.assertEqual(len(rev["CslibFrontier.Hub"]), 1)
        self.assertEqual(hub.transitive_importers(rev, "CslibFrontier.Hub"), 4)
        self.assertEqual(hub.transitive_importers(rev, "CslibFrontier.Mid"), 3)
        self.assertEqual(hub.transitive_importers(rev, "CslibFrontier.LeafA"), 1)
        self.assertEqual(hub.transitive_importers(rev, "CslibFrontier.LeafB"), 0)

        # Adding a brand-new module or editing a low-fan-in leaf stays silent.
        self.write("CslibFrontier/BrandNew.lean", "module\ndef x := 1\n")
        self.write("CslibFrontier/LeafB.lean", "module\npublic import CslibFrontier.Mid\ndef y := 2\n")
        hits, _ = hub.analyze(self.root, base, threshold=2)
        self.assertEqual(hits, [])

        # Modifying both Mid (3 trans) and Hub (4 trans) ranks Hub first.
        self.write("CslibFrontier/Hub.lean", "module\ndef h := 2\n")
        self.write("CslibFrontier/Mid.lean",
                   "module -- shake: keep-all\npublic import\n  CslibFrontier.Hub\ndef m := h + 1\n")
        hits, counted = hub.analyze(self.root, base, threshold=2)
        self.assertEqual(counted, 6)
        self.assertEqual(hits, [
            ("CslibFrontier/Hub.lean", 1, 4),
            ("CslibFrontier/Mid.lean", 2, 3),
        ])

    def test_github_output_writes_annotations_and_summary_and_never_fails(self):
        base = self.seed_graph()
        self.write("CslibFrontier/Hub.lean", "module\ndef h := 9\n")
        summary = self.root / "summary.md"
        with patch.object(hub, "HIGH_THRESHOLD", 4), \
             patch.dict(os.environ, {"GITHUB_STEP_SUMMARY": str(summary)}), \
             redirect_stdout(io.StringIO()) as buf:
            rc = hub.main(["--root", str(self.root), "--base", base, "--threshold", "2", "--github"])
        self.assertEqual(rc, 0)
        out = buf.getvalue()
        self.assertIn("::warning file=CslibFrontier/Hub.lean", out)
        self.assertIn("4 transitive importers", out)
        self.assertIn("| `CslibFrontier/Hub.lean` | 1 | 4 |", summary.read_text(encoding="utf-8"))

        # Below HIGH_THRESHOLD emits ::notice.
        with patch.object(hub, "HIGH_THRESHOLD", 10), \
             redirect_stdout(io.StringIO()) as buf:
            rc = hub.main(["--root", str(self.root), "--base", base, "--threshold", "2", "--github"])
        self.assertEqual(rc, 0)
        self.assertIn("::notice file=CslibFrontier/Hub.lean", buf.getvalue())

    def test_bad_base_ref_never_fails_advisory_job(self):
        with redirect_stdout(io.StringIO()) as buf:
            rc = hub.main(["--root", str(self.root), "--base", "does-not-exist"])
        self.assertEqual(rc, 0)
        self.assertIn("skipped", buf.getvalue())


if __name__ == "__main__":
    unittest.main()
