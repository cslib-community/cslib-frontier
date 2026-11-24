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
        import json
        import pages
        for payload in ({"s": "</script><b>"}, {"s": "<!-- <script>"}):
            encoded = pages._json(payload)
            self.assertNotIn("<", encoded)
            self.assertNotIn("</", encoded)
            self.assertEqual(json.loads(encoded), payload)


class PullRequests(unittest.TestCase):
    def setUp(self):
        info = lambda code: h.BlobInfo(code + 1, code, (), {})
        self.H = type("FakeHistory", (), {})()
        self.H.blobs = {"a": info(10), "b": info(30), "c": info(4)}
        t0 = 1795000000
        self.t0 = t0
        self.H.commits = [
            h.Commit("1" * 40, t0 + 100, "x", "feat(Crypto): add A (#5)",
                     [("CslibFrontier/Crypto/Primitives/A.lean", "a")]),
            h.Commit("2" * 40, t0 + 200, "x", "refactor: grow A, add B (#6)",
                     [("CslibFrontier/Crypto/Primitives/A.lean", "b"),
                      ("CslibFrontier/Logics/B.lean", "c")]),
        ]

    def raw(self, n, title, state, created, merged=None, closed=None):
        iso = lambda t: (__import__("datetime").datetime.fromtimestamp(t, __import__("datetime").timezone.utc)
                         .isoformat().replace("+00:00", "Z")) if t else None
        return {"number": n, "title": title, "state": state, "createdAt": iso(created),
                "mergedAt": iso(merged), "closedAt": iso(closed), "author": {"login": "a"},
                "additions": 3, "deletions": 1, "changedFiles": 1, "reviews": {"totalCount": 0},
                "commits": {"totalCount": 1}}

    def test_kinds(self):
        import prs
        self.assertEqual([prs.kind(t) for t in ("feat(X): y", "refactor: y", "perf(Z): y",
                                                 "fix: y", "doc: y", "")], [0, 1, 1, 2, 2, 2])

    def test_records_join_areas_through_the_squash_commit(self):
        import prs
        t0 = self.t0
        raw = [self.raw(5, "feat(Crypto): add A", "MERGED", t0, t0 + 100),
               self.raw(6, "refactor: grow A, add B", "MERGED", t0 + 50, t0 + 200),
               self.raw(7, "feat: open", "OPEN", t0 + 150)]
        recs = {r["n"]: r for r in prs.records(self.H, raw)}
        self.assertEqual((recs[5]["area"], recs[5]["sub"]), ("Crypto", "Crypto/Primitives"))
        # #6 changed A by 20 code lines and added B with 4: Crypto is its main area.
        self.assertEqual(recs[6]["area"], "Crypto")
        self.assertIsNone(recs[7]["area"])
        self.assertEqual([recs[n]["kind"] for n in (5, 6, 7)], [0, 1, 0])
        import numpy as np
        w = prs.wip(list(recs.values()), np.array([t0 + 60, t0 + 160, t0 + 300]))
        self.assertEqual(list(w), [2, 2, 1])
        self.assertEqual(list(prs.wip([], np.array([t0]))), [0])

    def test_zero_net_delta_leaves_area_unclassified(self):
        import prs
        info = lambda code: h.BlobInfo(code + 1, code, (), {})
        H = type("FakeHistory", (), {})()
        H.blobs = {"a1": info(10), "a2": info(10)}
        H.commits = [
            h.Commit("1" * 40, self.t0, "x", "feat: add A (#1)",
                     [("CslibFrontier/Crypto/A.lean", "a1")]),
            h.Commit("2" * 40, self.t0 + 60, "x", "refactor: rewrite A (#2)",
                     [("CslibFrontier/Crypto/A.lean", "a2")]),
        ]
        recs = {r["n"]: r for r in prs.records(H, [
            self.raw(1, "feat: add A", "MERGED", self.t0 - 10, self.t0),
            self.raw(2, "refactor: rewrite A", "MERGED", self.t0 + 10, self.t0 + 60),
        ])}
        self.assertEqual(recs[1]["area"], "Crypto")
        self.assertIsNone(recs[2]["area"])

    def test_short_and_empty_charts(self):
        import prs
        import streams
        import style
        t0 = 1795003200  # divisible by 6 * 3600 (21600)
        self.assertEqual(t0 % streams.STEP, 0)
        info = lambda code: h.BlobInfo(code + 1, code, (), {})
        H = type("FakeHistory", (), {})()
        H.blobs = {"a": info(0), "b": info(10)}
        H.commits = [h.Commit("1" * 40, t0, "x", "doc: init (#1)",
                              [("CslibFrontier/Crypto/A.lean", "a")])]
        with tempfile.TemporaryDirectory() as tmpdir:
            out = Path(tmpdir)
            style.setup(style.LIGHT)
            # streams: single commit on a 6h boundary + zero total_final code
            dates, rows = streams.series(H)
            self.assertEqual(len(dates), 1)
            self.assertEqual(rows, [{"Crypto": 0}])
            self.assertTrue(all(p.exists() for p in streams.streamgraph(H, out)))
            # streams: completely empty commit history
            H_empty = type("FakeHistory", (), {})()
            H_empty.blobs = {}
            H_empty.commits = []
            self.assertEqual(streams.series(H_empty), ([], []))
            self.assertTrue(all(p.exists() for p in streams.streamgraph(H_empty, out)))
            # waterfall & growth_vs_cleanup: empty, unmerged-only, 1-3 six-hour buckets
            self.assertTrue(all(p.exists() for p in prs.waterfall(H, out, [])))
            self.assertTrue(all(p.exists() for p in prs.growth_vs_cleanup(H, out, [])))
            unmerged = prs.records(H, [self.raw(1, "feat: open", "OPEN", t0)])
            self.assertTrue(all(p.exists() for p in prs.waterfall(H, out, unmerged)))
            for buckets in (1, 2, 3):
                raw = [self.raw(i + 1, "feat: p", "MERGED", t0 - 3600, t0 - (buckets - 1 - i) * 21600)
                       for i in range(buckets)]
                H_b = type("FakeHistory", (), {})()
                H_b.blobs = {"b": info(10)}
                H_b.commits = [h.Commit("1" * 40, t0, "x", "feat: p (#1)",
                                        [("CslibFrontier/Crypto/A.lean", "b")])]
                recs = prs.records(H_b, raw)
                self.assertTrue(all(p.exists() for p in prs.waterfall(H_b, out, recs)))
                self.assertTrue(all(p.exists() for p in prs.growth_vs_cleanup(H_b, out, recs)))

    def test_stream_series_follow_sub_areas(self):
        import streams
        dates, rows = streams.series(self.H)
        self.assertEqual(rows[-1], {"Crypto/Primitives": 30, "Logics": 4})


class PullRequestUpdates(unittest.TestCase):
    def test_update_replaces_and_adds_until_older(self):
        import github_prs as g
        pr = lambda n, c, u, title="t": {"number": n, "createdAt": c, "updatedAt": u, "title": title}
        previous = [pr(1, "2026-11-01", "2026-11-02"), pr(2, "2026-11-03", "2026-11-05", "old")]
        pages = [[pr(3, "2026-11-06", "2026-11-07"), pr(2, "2026-11-03", "2026-11-06", "new")],
                 [pr(1, "2026-11-01", "2026-11-02")],  # not newer: stop here
                 [pr(9, "2026-10-01", "2026-10-02")]]  # never reached
        seen = []

        def fake_pages(query, repo, tok):
            for page in pages:
                seen.append(page)
                yield page
        orig = g._pages
        g._pages = fake_pages
        try:
            out = g.update(previous, tok="x")
        finally:
            g._pages = orig
        self.assertEqual([(p["number"], p["title"]) for p in out], [(1, "t"), (2, "new"), (3, "t")])
        self.assertEqual(len(seen), 2)

    def test_update_sends_recent_query_via_post_and_retries(self):
        import http.client
        import github_prs as g

        pr = lambda n, c, u, title="t": {"number": n, "createdAt": c, "updatedAt": u, "title": title}
        previous = [pr(1, "2026-11-01T00:00:00Z", "2026-11-02T00:00:00Z"),
                    pr(2, "2026-11-03T00:00:00Z", "2026-11-05T12:00:00Z", "old")]
        calls = []
        responses = iter([
            http.client.RemoteDisconnected("drop"),
            {"data": None},
            {"data": {"repository": {"pullRequests": {
                "pageInfo": {"hasNextPage": True, "endCursor": "c1"},
                # PR 4 updated within the 30-min overlap window (11:45 >= 11:30); PR 3 is new.
                "nodes": [pr(3, "2026-11-06T00:00:00Z", "2026-11-06T01:00:00Z"),
                          pr(4, "2026-11-05T00:00:00Z", "2026-11-05T11:45:00Z")],
            }}}},
            {"data": {"repository": {"pullRequests": {
                "pageInfo": {"hasNextPage": True, "endCursor": "c2"},
                "nodes": [pr(1, "2026-11-01T00:00:00Z", "2026-11-02T00:00:00Z")],
            }}}},
        ])

        def fake_post(body, tok):
            calls.append((body, tok))
            nxt = next(responses)
            if isinstance(nxt, BaseException):
                raise nxt
            return nxt

        with mock.patch.object(g, "_post", side_effect=fake_post), \
             mock.patch.object(g.time, "sleep"):
            out = g.update(previous, tok="secret")
        self.assertEqual([p["number"] for p in out], [1, 2, 4, 3])
        self.assertEqual(len(calls), 4)
        for body, tok in calls:
            self.assertEqual(body["query"], g.RECENT)
            self.assertNotEqual(body["query"], g.QUERY)
            self.assertIn("UPDATED_AT, direction: DESC", body["query"])
            self.assertEqual(tok, "secret")
        fetch_calls = []
        fetch_resp = {"data": {"repository": {"pullRequests": {
            "pageInfo": {"hasNextPage": False, "endCursor": None},
            "nodes": [pr(1, "2026-11-01T00:00:00Z", "2026-11-02T00:00:00Z")],
        }}}}
        with mock.patch.object(g, "_post", side_effect=lambda b, t: (fetch_calls.append(b), fetch_resp)[1]):
            self.assertEqual(len(g.fetch(tok="secret")), 1)
        self.assertEqual(fetch_calls[0]["query"], g.QUERY)

    def test_update_without_stamps_refetches(self):
        import github_prs as g
        orig = g.fetch
        g.fetch = lambda repo, tok: ["full"]
        try:
            self.assertEqual(g.update([{"number": 1, "createdAt": "x"}], tok="x"), ["full"])
        finally:
            g.fetch = orig


class AtlasLayout(unittest.TestCase):
    def test_atlas_uses_nested_layout_and_caches(self):
        import atlas
        import evolution as ev
        info = lambda code, imps=(): h.BlobInfo(code + 1, code, tuple(imps), {})
        H = type("FakeHistory", (), {})()
        H.blobs = {"a": info(10), "b": info(20, ("CslibFrontier.Crypto.A",))}
        H.commits = [
            h.Commit("1" * 40, 1795000000, "x", "feat: add (#1)",
                     [("CslibFrontier/Crypto/A.lean", "a"),
                      ("CslibFrontier/Logics/B.lean", "b")]),
        ]
        with mock.patch.object(ev, "layout", side_effect=AssertionError("evolution.layout called")):
            R = atlas.Atlas(H, 320, 180)
        self.assertEqual(R.mods, ["CslibFrontier.Crypto.A", "CslibFrontier.Logics.B"])
        st = ev.State(H)
        st.apply(H.commits[0])
        st.refresh()
        img = R.draw(1795000000, st, smooth=1)
        self.assertEqual(img.size, (320, 180))
        # Cached layout avoids recomputing on a second Atlas call when blobs expose fingerprint.
        class CachedBlobs(dict):
            fingerprint = "1-test"
        H.blobs = CachedBlobs(H.blobs)
        with tempfile.TemporaryDirectory() as tmpdir, \
             mock.patch.object(h, "HERE", Path(tmpdir)), \
             mock.patch.object(ev, "layout", side_effect=AssertionError("evolution.layout called")):
            pos1 = atlas.nested_layout(H)
            with mock.patch("networkx.spring_layout", side_effect=AssertionError("uncached")):
                pos2 = atlas.nested_layout(H)
            self.assertEqual(pos1, pos2)


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
