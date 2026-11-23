# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""Unit tests for the codebase visualization data layer and layout helpers."""

from __future__ import annotations

import csv
import io
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))

import history as h  # noqa: E402
from plots_structure import squarify  # noqa: E402


class ScanBlob(unittest.TestCase):
    def test_counts_code_comments_and_declarations(self):
        src = b"""/-
Copyright header
-/
module

public import CslibFrontier.Init
import Complexity.Foundations.Data.Bits

/-! # Module doc
with /- a nested -/ comment
class of problems described in prose, not a declaration -/

/-- A docstring. -/
@[simp] theorem foo : True := trivial  -- trailing comment
private lemma bar : True := by
  trivial
noncomputable def baz : Nat := 0
instance : Inhabited Nat := \xe2\x9f\xa80\xe2\x9f\xa9
  theorem indented_is_not_counted : True := trivial
"""
        info = h.scan_blob(src)
        self.assertEqual(info.lines, src.count(b"\n"))
        self.assertEqual(info.imports, ("CslibFrontier.Init", "CslibFrontier.Foundations.Data.Bits"))
        self.assertEqual(info.decls, {"theorem": 1, "lemma": 1, "def": 1, "instance": 1})
        # module, 2 imports, foo, bar, trivial, baz, instance, indented theorem
        self.assertEqual(info.code, 9)

    def test_code_after_block_comment_on_same_line(self):
        self.assertEqual(h.scan_blob(b"/- c -/ def x := 1\n").code, 1)
        self.assertEqual(h.scan_blob(b"/- c -/\n").code, 0)
        self.assertEqual(h.scan_blob(b"").lines, 0)
        self.assertEqual(h.scan_blob(b"def x := 1").lines, 1)


class Paths(unittest.TestCase):
    def test_rename_normalisation(self):
        self.assertEqual(h.normalize_path("Complexity/Crypto/A.lean"), "CslibFrontier/Crypto/A.lean")
        self.assertEqual(h.normalize_path("ComplexityTests/A.lean"), "CslibFrontierTests/A.lean")
        self.assertEqual(h.normalize_path("Complexity.lean"), "CslibFrontier.lean")
        self.assertEqual(h.normalize_path("ComplexityFoo/A.lean"), "ComplexityFoo/A.lean")
        self.assertEqual(h.normalize_module("Complexity.Crypto.A"), "CslibFrontier.Crypto.A")

    def test_areas(self):
        self.assertEqual(h.area_of("CslibFrontier/Crypto/Primitives/A.lean"), "Crypto")
        self.assertEqual(h.area_of("CslibFrontier/GameTheory/A.lean"), h.OTHER)
        self.assertEqual(h.area_of("CslibFrontier/Init.lean"), h.OTHER)
        self.assertEqual(h.subarea_of("CslibFrontier/Crypto/Primitives/A.lean"), "Crypto/Primitives")
        self.assertEqual(h.subarea_of("CslibFrontier/Probability/A.lean"), "Probability")

    def test_root_rename_commit_when_new_prefix_precedes_old(self):
        import site_data as sd
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            repo = tmp / "repo"
            repo.mkdir()
            git = lambda *args: subprocess.run(
                ["git", "-C", str(repo), *args], check=True, capture_output=True, text=True,
                env={"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@e",
                     "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@e",
                     "HOME": tmpdir, "PATH": "/usr/bin:/bin"})
            git("init", "-q")
            (repo / "CslibFrontier" / "Crypto").mkdir(parents=True)
            (repo / "CslibFrontier" / "Crypto" / "A.lean").write_text("theorem t : True := trivial\n")
            git("add", ".")
            git("commit", "-q", "-m", "feat: add A (#1)")
            (repo / "Cslib" / "Crypto").mkdir(parents=True)
            git("mv", "CslibFrontier/Crypto/A.lean", "Cslib/Crypto/A.lean")
            git("commit", "-q", "-m", "chore: rename root (#2)")
            # "Cslib/" < "CslibFrontier/", so git --raw emits the addition before the deletion.
            with mock.patch.object(h, "RENAMES", [("CslibFrontier", "Cslib")]), \
                 mock.patch.object(h, "LIBRARY_ROOT", "Cslib/"):
                H = h.History(repo, cache=tmp / "blobs.json")
                self.assertEqual(len(H.commits[1].changes), 1)
                self.assertEqual(H.commits[1].changes[0][0], "Cslib/Crypto/A.lean")
                self.assertIsNotNone(H.commits[1].changes[0][1])
                self.assertEqual(set(H.head()), {"Cslib/Crypto/A.lean"})
                self.assertEqual(H.touches()["Cslib/Crypto/A.lean"], 2)
                mods = sd.modules(H, None)
                commits_idx = mods["fields"].index("commits")
                self.assertEqual(mods["rows"][0][commits_idx], 2)


class Graphs(unittest.TestCase):
    def test_longest_chain(self):
        g = {"a": {"b", "c"}, "b": {"d"}, "c": set(), "d": set(), "e": {"a"}}
        n, chain = h.longest_chain(g)
        self.assertEqual(n, 4)
        self.assertEqual(chain, ["e", "a", "b", "d"])
        self.assertEqual(h.longest_chain({}), (0, []))


class Census(unittest.TestCase):
    def test_summary_and_series(self):
        import lean_census as lc
        report = {"modules": {
            "CslibFrontier.Crypto.A": {"kinds": {"theorem": 3, "abbrev": 2}, "generated": 7,
                                       "uses": []},
            "CslibFrontier.GameTheory.B": {"kinds": {"structure": 1, "instance": 4},
                                           "generated": 1, "uses": []}}}
        summary = lc.summarize(report)
        self.assertEqual(summary["by_area"]["Crypto"], {"Theorems": 3, "Definitions": 2})
        self.assertEqual(summary["by_area"][h.OTHER], {"Types": 1, "Instances": 4})
        self.assertEqual(summary["generated"], 8)
        c1 = h.Commit("a" * 40, 1795000000, "x", "s", [])
        c2 = h.Commit("b" * 40, 1795000000 + 3600, "x", "s", [])  # same UTC day
        c3 = h.Commit("c" * 40, 1795000000 + 86400, "x", "s", [])
        series = lc.extend([], c1, summary)
        series = lc.extend(series, c2, summary)
        self.assertEqual([e["sha"][0] for e in series], ["b"])
        series = lc.extend(series, c3, summary)
        self.assertEqual([e["sha"][0] for e in series], ["b", "c"])

    def test_missing_previous_series_starts_empty(self):
        import lean_census as lc
        self.assertEqual(lc.load_previous(None), [])
        self.assertEqual(lc.load_previous("/nonexistent/lean-history.json"), [])

    def test_registry_fails_closed_when_required(self):
        import lean_census as lc
        failed = subprocess.CompletedProcess(["python3"], 1, stdout="", stderr="missing build")
        saved = (lc._registry, lc._registry_ok)
        try:
            lc._registry, lc._registry_ok = None, False
            with mock.patch.object(lc.subprocess, "run", return_value=failed), \
                 mock.patch("sys.stderr", io.StringIO()):
                self.assertEqual(lc.registered_results(Path("."), require=False), [])
                self.assertFalse(lc.registry_available())
                with self.assertRaises(SystemExit):
                    lc.registered_results(Path("."), require=True)
            lc._registry, lc._registry_ok = None, False
            with mock.patch.object(lc.subprocess, "run", return_value=failed):
                with self.assertRaises(SystemExit):
                    lc.registered_results(Path("."), require=True)
        finally:
            lc._registry, lc._registry_ok = saved


class Audits(unittest.TestCase):
    def test_dispositions(self):
        from plots_results import classify, parse
        self.assertEqual(classify("Covered in the native model."), "Covered")
        self.assertEqual(classify("Source issue; corrected endpoint covered"),
                         "Covered, source corrected")
        self.assertEqual(classify("Covered (corrected statement); source issue"),
                         "Covered, source corrected")
        self.assertEqual(classify("Partial (space measure)"), "Partial")
        self.assertEqual(classify("Endpoint not located; model convention needed"), "Not located")
        self.assertEqual(classify("Source issue"), "Source issue")
        self.assertEqual(classify("Unverified"), "Other")
        text = """| Draft result | Page | Disposition |
|---|---|---|
| 1.8, alphabet reduction | 19 / 35 | **Endpoint not located.** No compiler. |
| 2.3, $P\\subseteq NP$ | 41 / 57 | **Covered.** `P_subset_NP`. |
| 3.2(1) | 16 / 132 | **Partial.** Only slices. |
| 2.3, $P\\subseteq NP$ | 41 / 57 | **Partial.** Rechecked later. |
"""
        self.assertEqual(sorted(parse(text)), [(1, "Not located"), (2, "Partial"), (3, "Partial")])


class UnusedImports(unittest.TestCase):
    def test_imports_through_dependencies_count_as_used(self):
        from plots_lean import checked_imports, unused_imports
        # 0 = Lib.A imports 1 = Lib.B (which imports 3 = Mathlib.X) and 2 = Lib.C; A uses only a
        # Mathlib.X constant, so B is needed (through its own import) and C is not.
        report = {"moduleGraph": {"names": ["Lib.A", "Lib.B", "Lib.C", "Mathlib.X"],
                                  "imports": [[1, 2], [3], [], []],
                                  "used": [[3], [3], []]}}
        self.assertEqual(unused_imports(report), {"Lib.A": ["Lib.C"]})
        self.assertEqual(checked_imports(report), 3)
        # An umbrella that declares nothing imports to re-export, and is not reported or counted.
        report["modules"] = {"Lib.A": {"kinds": {}}, "Lib.B": {"kinds": {"def": 1}},
                             "Lib.C": {"kinds": {}}}
        self.assertEqual(unused_imports(report), {})
        self.assertEqual(checked_imports(report), 1)

    def test_deduplicates_phases_and_ignores_init(self):
        from plots_lean import checked_imports, unused_imports
        report = {
            "modules": {"Lib.A": {"kinds": {"theorem": 1}}, "Lib.B": {"kinds": {"def": 1}}},
            "moduleGraph": {
                "names": ["Lib.A", "Lib.B", "Init"],
                "imports": [[2, 2, 1, 1], [2, 2], []],
                "used": [[], []],
            },
        }
        self.assertEqual(checked_imports(report), 1)
        self.assertEqual(unused_imports(report), {"Lib.A": ["Lib.B"]})


class LeanPlots(unittest.TestCase):
    def test_empty_registry_empty_series_and_small_top(self):
        import plots_lean
        import style
        H = type("FakeHistory", (), {})()
        H.blobs = {"a": h.BlobInfo(4, 2, (), {"theorem": 1})}
        H.head = lambda: {"CslibFrontier/Foundations/A.lean": "a"}
        base_report = {
            "modules": {"CslibFrontier.Foundations.A": {"kinds": {"theorem": 1, "def": 1},
                                                        "generated": 2, "uses": []}},
            "cones": {},
            "results": {},
            "top": [{"name": "Cslib.foo", "module": "CslibFrontier.Foundations.A",
                     "kind": "def", "refs": 3}],
            "unused": [{"name": 'Cslib."quoted",bar', "module": "CslibFrontier.Foundations.A",
                        "kind": "def"}],
        }
        with tempfile.TemporaryDirectory() as tmpdir:
            out = Path(tmpdir)
            for theme in (style.LIGHT, style.DARK):
                style.setup(theme)
                plots_lean.declarations(H, out, (base_report, []))
                plots_lean.result_cones(H, out, (base_report, []))
                plots_lean.load_bearing(H, out, (base_report, []))
                plots_lean.load_bearing(H, out, ({**base_report, "top": []}, []))
                plots_lean.unused_definitions(H, out, (base_report, []))
            style.setup(style.LIGHT)
            with open(out / "unused-definitions.csv", newline="") as f:
                rows = list(csv.reader(f))
            self.assertEqual(rows, [["name", "kind", "module"],
                                    ['Cslib."quoted",bar', "def", "CslibFrontier.Foundations.A"]])


class PageData(unittest.TestCase):
    """The briefing's windows, on a two-commit history."""

    def setUp(self):
        info = lambda code, thm, imports=(): h.BlobInfo(code + 2, code, tuple(imports),
                                                         {"theorem": thm} if thm else {})
        self.blobs = {"a1": info(10, 1), "a2": info(14, 2), "b1": info(5, 0, ["CslibFrontier.Crypto.A"])}
        t0 = 1795000000
        self.H = type("FakeHistory", (), {})()
        self.H.blobs = self.blobs
        self.H.commits = [
            h.Commit("1" * 40, t0, "x", "feat: add A (#1)", [("CslibFrontier/Crypto/A.lean", "a1")]),
            h.Commit("2" * 40, t0 + 2 * 86400, "x", "feat: add B, grow A (#2)",
                     [("CslibFrontier/Crypto/A.lean", "a2"), ("CslibFrontier/Logics/B.lean", "b1")]),
        ]

    def test_changes_cover_only_the_window(self):
        import site_data as sd
        c = sd.changes(self.H, 1)
        self.assertEqual(c["commits"], 1)
        self.assertEqual(c["code"], 4 + 5)
        self.assertEqual(c["theorems"], 1)
        self.assertEqual(c["added"], [["CslibFrontier.Logics.B", 5]])
        self.assertEqual(c["grown"], [["CslibFrontier.Crypto.A", 4]])
        self.assertEqual(c["area_code"], {"Crypto": 4, "Logics": 5})
        self.assertEqual(c["largest"][0]["pr"], 2)

    def test_rolling_measures_before_and_after(self):
        import site_data as sd
        r = sd.rolling(self.H)
        self.assertEqual(r["1"]["lib_code"], 10)
        self.assertEqual(r["0"]["lib_code"], 19)
        self.assertEqual(r["0"]["modules"], 2)
        self.assertEqual(r["0"]["chain"], 2)
        self.assertEqual(r["commits"], {"1": 1, "7": 2})

    def test_embedded_json_cannot_close_its_script(self):
        import pages
        self.assertNotIn("</", pages._json({"s": "</script><b>"}))


class Squarify(unittest.TestCase):
    def test_areas_are_proportional_and_inside(self):
        vals = [50, 20, 13, 10, 5, 1, 1]
        rects = squarify(vals, 0, 0, 6, 4)
        total = sum(vals)
        for v, (x, y, w, hh) in zip(vals, rects):
            self.assertAlmostEqual(w * hh, v / total * 24, places=6)
            self.assertGreaterEqual(x, -1e-9)
            self.assertGreaterEqual(y, -1e-9)
            self.assertLessEqual(x + w, 6 + 1e-9)
            self.assertLessEqual(y + hh, 4 + 1e-9)


if __name__ == "__main__":
    unittest.main()
