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

    def test_build_reverse_graph_and_private_import_cutoff(self):
        base = self.seed_graph()
        graph, total = hub.build_reverse_graph(self.root)
        self.assertEqual(total, 5)
        self.assertEqual(len(graph.any_importers["CslibFrontier.Hub"]), 1)
        # `LeafA` privately imports `Mid`, so `Check` (2 hops past private `import`) is cut off.
        self.assertEqual(
            hub.rebuilt_importers(graph, "CslibFrontier.Hub"),
            {"CslibFrontier.Mid", "CslibFrontier.LeafA", "CslibFrontier.LeafB"},
        )
        self.assertEqual(hub.transitive_importers(graph, "CslibFrontier.Hub"), 3)
        self.assertEqual(
            hub.rebuilt_importers(graph, "CslibFrontier.Mid"),
            {"CslibFrontier.LeafA", "CslibFrontier.LeafB"},
        )
        self.assertEqual(hub.transitive_importers(graph, "CslibFrontier.Mid"), 2)
        self.assertEqual(
            hub.rebuilt_importers(graph, "CslibFrontier.LeafA"),
            {"CslibFrontierTests.Check"},
        )
        self.assertEqual(hub.transitive_importers(graph, "CslibFrontier.LeafA"), 1)
        self.assertEqual(hub.transitive_importers(graph, "CslibFrontier.LeafB"), 0)

        # Adding a brand-new module or editing a low-fan-in leaf stays silent.
        self.write("CslibFrontier/BrandNew.lean", "module\ndef x := 1\n")
        self.write("CslibFrontier/LeafB.lean", "module\npublic import CslibFrontier.Mid\ndef y := 2\n")
        hits, _ = hub.analyze(self.root, base, threshold=2)
        self.assertEqual(hits, [])

        # Modifying both Mid (2 trans) and Hub (3 trans) ranks Hub first.
        self.write("CslibFrontier/Hub.lean", "module\ndef h := 2\n")
        self.write("CslibFrontier/Mid.lean",
                   "module -- shake: keep-all\npublic import\n  CslibFrontier.Hub\ndef m := h + 1\n")
        hits, counted = hub.analyze(self.root, base, threshold=2)
        self.assertEqual(counted, 6)
        self.assertEqual(hits, [
            ("CslibFrontier/Hub.lean", 1, 3),
            ("CslibFrontier/Mid.lean", 2, 2),
        ])

    def test_public_non_module_and_import_all_propagate_past_leaf(self):
        self.seed_graph()

        # 1. `LeafA` uses `public import`: `Check` now rebuilds.
        self.write("CslibFrontier/LeafA.lean", "module\npublic import CslibFrontier.Mid\n")
        graph_pub, _ = hub.build_reverse_graph(self.root)
        self.assertIn("CslibFrontierTests.Check", hub.rebuilt_importers(graph_pub, "CslibFrontier.Hub"))
        self.assertEqual(hub.transitive_importers(graph_pub, "CslibFrontier.Hub"), 4)

        # 2. `LeafA` omits `module`: classic files re-export their imports, so `Check` rebuilds.
        self.write("CslibFrontier/LeafA.lean", "import CslibFrontier.Mid\n")
        graph_legacy, _ = hub.build_reverse_graph(self.root)
        self.assertIn("CslibFrontier.LeafA", graph_legacy.non_module_files)
        self.assertIn("CslibFrontierTests.Check", hub.rebuilt_importers(graph_legacy, "CslibFrontier.Hub"))
        self.assertEqual(hub.transitive_importers(graph_legacy, "CslibFrontier.Hub"), 4)

        # 3. `LeafA` stays private (`module\nimport ...`), but `Check` uses `import all`:
        #    `Check` and `CheckAll2` (`import all Check`) rebuild, while `CheckPlain2` (`import Check`)
        #    stops because `Check` is a `module` file whose exported `.olean` stays unchanged.
        self.write("CslibFrontier/LeafA.lean", "module\nimport CslibFrontier.Mid\n")
        self.write("CslibFrontierTests/Check.lean", "module\nimport all CslibFrontier.LeafA\n")
        self.write("CslibFrontierTests/CheckAll2.lean", "module\nmeta import all CslibFrontierTests.Check\n")
        self.write("CslibFrontierTests/CheckPlain2.lean", "module\nimport CslibFrontierTests.Check\n")
        graph_all, _ = hub.build_reverse_graph(self.root)
        self.assertEqual(
            hub.rebuilt_importers(graph_all, "CslibFrontier.Hub"),
            {
                "CslibFrontier.Mid",
                "CslibFrontier.LeafA",
                "CslibFrontier.LeafB",
                "CslibFrontierTests.Check",
                "CslibFrontierTests.CheckAll2",
            },
        )

    def test_meta_imports_diamond_and_root_aggregator_exclusion(self):
        self.write("CslibFrontier/Hub.lean", "module\n")
        self.write("CslibFrontier/MetaPriv.lean", "module\nmeta import CslibFrontier.Hub\n")
        self.write("CslibFrontier/AfterMetaPriv.lean", "module\npublic import CslibFrontier.MetaPriv\n")
        self.write("CslibFrontier/MetaPub.lean", "module\npublic meta import CslibFrontier.Hub\n")
        self.write("CslibFrontier/AfterMetaPub.lean", "module\nimport CslibFrontier.MetaPub\n")
        # Diamond: `Diamond` has both a direct private import of `Hub` and a public import of `MetaPub`.
        self.write(
            "CslibFrontier/Diamond.lean",
            "module\nimport CslibFrontier.Hub\npublic import CslibFrontier.MetaPub\n",
        )
        self.write("CslibFrontier/AfterDiamond.lean", "module\nimport CslibFrontier.Diamond\n")
        # Root aggregator `CslibFrontier.lean` sits outside `CslibFrontier/` and does not link leaves.
        self.write(
            "CslibFrontier.lean",
            "public import CslibFrontier.Hub\npublic import CslibFrontier.Unrelated\n",
        )
        self.write("CslibFrontier/Unrelated.lean", "module\n")
        self.write("CslibFrontierTests/Smoke.lean", "module\nimport CslibFrontier\n")

        graph, total = hub.build_reverse_graph(self.root)
        self.assertEqual(total, 9)
        self.assertEqual(
            hub.rebuilt_importers(graph, "CslibFrontier.Hub"),
            {
                "CslibFrontier.MetaPriv",
                "CslibFrontier.MetaPub",
                "CslibFrontier.AfterMetaPub",
                "CslibFrontier.Diamond",
                "CslibFrontier.AfterDiamond",
            },
        )
        self.assertEqual(hub.rebuilt_importers(graph, "CslibFrontier.Unrelated"), set())

    def test_transitive_meta_and_legacy_non_module_traces_past_private_cutoff(self):
        # `PrivMid` privately imports `Hub`, so `UnrebuiltMid` (`public import PrivMid`) does NOT
        # rebuild; however, `metaTransTrace` and `legacyTransTrace` still change across `Reach_any+`.
        self.write("CslibFrontier/Hub.lean", "module\n")
        self.write("CslibFrontier/PrivMid.lean", "module\nimport CslibFrontier.Hub\n")
        self.write("CslibFrontier/UnrebuiltMid.lean", "module\npublic import CslibFrontier.PrivMid\n")

        # 1. Non-public `meta import` of `UnrebuiltMid` rebuilds `TacPriv`, but NOT its client.
        self.write("CslibFrontier/TacPriv.lean", "module\nmeta import CslibFrontier.UnrebuiltMid\n")
        self.write(
            "CslibFrontier/TacPrivClient.lean", "module\npublic import CslibFrontier.TacPriv\n"
        )

        # 2. `public meta import` mixes `metaTransTrace` into `TacPub.transTrace`, rebuilding
        #    `TacPub`, `Mid2`, and `TacPubClient`.
        self.write(
            "CslibFrontier/TacPub.lean", "module\npublic meta import CslibFrontier.UnrebuiltMid\n"
        )
        self.write("CslibFrontier/Mid2.lean", "module\npublic import CslibFrontier.TacPub\n")
        self.write("CslibFrontier/TacPubClient.lean", "module\nimport CslibFrontier.Mid2\n")

        # 3. `meta import all` checks `allTransTrace` (`Module.lean:352`), so on unrebuilt
        #    `UnrebuiltMid` it does NOT rebuild.
        self.write(
            "CslibFrontier/MetaAllUnrebuilt.lean",
            "module\nmeta import all CslibFrontier.UnrebuiltMid\n",
        )

        # 4. Classic test without `module` mixes `legacyTransTrace` across `Reach_any+` and
        #    rebuilds (along with downstream legacy importers), whereas `ModTest` (`module`) stops.
        self.write("CslibFrontierTests/ModTest.lean", "module\nimport CslibFrontier.UnrebuiltMid\n")
        self.write("CslibFrontierTests/LegacyTest.lean", "import CslibFrontier.UnrebuiltMid\n")
        self.write("CslibFrontierTests/LegacyTest2.lean", "import CslibFrontierTests.LegacyTest\n")

        graph, total = hub.build_reverse_graph(self.root)
        self.assertEqual(total, 12)
        self.assertEqual(
            hub.rebuilt_importers(graph, "CslibFrontier.Hub"),
            {
                "CslibFrontier.PrivMid",
                "CslibFrontier.TacPriv",
                "CslibFrontier.TacPub",
                "CslibFrontier.Mid2",
                "CslibFrontier.TacPubClient",
                "CslibFrontierTests.LegacyTest",
                "CslibFrontierTests.LegacyTest2",
            },
        )

    def test_github_output_writes_annotations_and_summary_and_never_fails(self):
        base = self.seed_graph()
        self.write("CslibFrontier/Hub.lean", "module\ndef h := 9\n")
        summary = self.root / "summary.md"
        with patch.object(hub, "HIGH_THRESHOLD", 3), \
             patch.dict(os.environ, {"GITHUB_STEP_SUMMARY": str(summary)}), \
             redirect_stdout(io.StringIO()) as buf:
            rc = hub.main(["--root", str(self.root), "--base", base, "--threshold", "2", "--github"])
        self.assertEqual(rc, 0)
        out = buf.getvalue()
        self.assertIn("::warning file=CslibFrontier/Hub.lean", out)
        self.assertIn("3 transitive importers", out)
        self.assertIn("| `CslibFrontier/Hub.lean` | 1 | 3 |", summary.read_text(encoding="utf-8"))

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
