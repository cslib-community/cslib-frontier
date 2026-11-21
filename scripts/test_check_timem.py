"""Unit tests for scripts/check_timem.py."""

from __future__ import annotations

import json
import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_timem  # noqa: E402


class StripCommentsTests(unittest.TestCase):
    def test_line_comment_and_docstring_are_not_counted(self) -> None:
        text = "-- TimeM is not used here\n/-- no `TimeM` bound -/\ndef f : ℕ := 1\n"
        self.assertEqual(check_timem.count_uses(text), 0)

    def test_nested_block_comment(self) -> None:
        text = "/- outer /- TimeM -/ still TimeM -/\ndef f : TimeM ℕ ℕ := pure 0\n"
        self.assertEqual(check_timem.count_uses(text), 1)

    def test_tick_notation_counts(self) -> None:
        self.assertEqual(check_timem.count_uses("def f : M ℕ := do ✓ return 0\n"), 1)

    def test_comment_markers_inside_a_string_do_not_hide_code(self) -> None:
        text = 'def s := "-- not a comment"\ndef f : TimeM ℕ ℕ := pure 0\n'
        self.assertEqual(check_timem.count_uses(text), 1)

    def test_longer_identifier_is_not_a_use(self) -> None:
        self.assertEqual(check_timem.count_uses("def RunTimeMeasure := 0\n"), 0)


class RatchetTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        (self.root / "CslibFrontier").mkdir()
        self.baseline = self.root / "baseline.json"

    def write(self, rel: str, content: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")

    def run_check(self, files: dict[str, int], *flags: str) -> int:
        self.baseline.write_text(json.dumps({"files": files}), encoding="utf-8")
        return check_timem.main(
            ["--root", str(self.root), "--baseline", str(self.baseline), *flags])

    def test_new_file_fails(self) -> None:
        self.write("CslibFrontier/A.lean", "def f : TimeM ℕ ℕ := pure 0\n")
        self.assertEqual(self.run_check({}), 1)

    def test_rise_in_a_recorded_file_fails(self) -> None:
        self.write("CslibFrontier/A.lean", "def f : TimeM ℕ ℕ := do ✓ return 0\n")
        self.assertEqual(self.run_check({"CslibFrontier/A.lean": 1}), 1)

    def test_fall_and_removal_pass_without_an_update(self) -> None:
        self.write("CslibFrontier/A.lean", "def f : TimeM ℕ ℕ := pure 0\n")
        files = {"CslibFrontier/A.lean": 3, "CslibFrontier/Gone.lean": 2}
        self.assertEqual(self.run_check(files), 0)
        self.assertEqual(json.loads(self.baseline.read_text())["files"], files)

    def test_update_only_lowers(self) -> None:
        self.write("CslibFrontier/A.lean", "def f : TimeM ℕ ℕ := pure 0\n")
        files = {"CslibFrontier/A.lean": 3, "CslibFrontier/Gone.lean": 2}
        self.assertEqual(self.run_check(files, "--update"), 0)
        self.assertEqual(
            json.loads(self.baseline.read_text())["files"], {"CslibFrontier/A.lean": 1})

    def test_update_refuses_a_rise(self) -> None:
        self.write("CslibFrontier/A.lean", "def f : TimeM ℕ ℕ := do ✓ return 0\n")
        self.assertEqual(self.run_check({"CslibFrontier/A.lean": 1}, "--update"), 1)
        self.assertEqual(
            json.loads(self.baseline.read_text())["files"], {"CslibFrontier/A.lean": 1})


class RepositoryBaselineTests(unittest.TestCase):
    def test_repository_is_within_its_baseline(self) -> None:
        self.assertEqual(check_timem.main([]), 0)


if __name__ == "__main__":
    unittest.main()
