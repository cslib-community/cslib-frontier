"""Unit tests for scripts/check_timem.py."""

from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_timem  # noqa: E402


class MaskedSyntaxTests(unittest.TestCase):
    def test_line_comment_and_docstring_are_not_counted(self) -> None:
        text = "-- TimeM time_simps time_spec are not used here\n/-- no `TimeM` bound -/\ndef f : ℕ := 1\n"
        self.assertEqual(check_timem.count_uses(text), 0)

    def test_nested_block_comment(self) -> None:
        text = "/- outer /- TimeM -/ still TimeM -/\ndef f : TimeM ℕ ℕ := pure 0\n"
        self.assertEqual(check_timem.count_uses(text), 1)

    def test_comment_preserves_token_separation(self) -> None:
        text = (
            "def old : TimeM Nat Nat := pure 0\n"
            "def added : TimeM/-separator-/Nat Nat := pure 0\n"
        )
        self.assertEqual(check_timem.count_uses(text), 2)

    def test_tick_notation_counts(self) -> None:
        self.assertEqual(check_timem.count_uses("def f : M ℕ := do ✓ return 0\n"), 1)

    def test_string_raw_string_and_char_literals_are_ignored_and_do_not_hide_code(self) -> None:
        text = (
            'def s := "TimeM ✓ time_simps time_spec -- not a comment"\n'
            'def r := r#"TimeM ✓ /- not a block comment"#\n'
            "def c : Char := '✓'\n"
            "def f' : TimeM ℕ ℕ := pure 0\n"
        )
        self.assertEqual(check_timem.count_uses(text), 1)

    def test_longer_identifier_is_not_a_use(self) -> None:
        self.assertEqual(check_timem.count_uses("def RunTimeMeasure := 0\n"), 0)

    def test_forbidden_imports_and_tactics_count(self) -> None:
        for line in (
            "import Cslib.Algorithms.Lean.TimeM\n",
            "import CslibFrontier.Algorithms.Lean.TimeM.Loops\n",
            "import Cslib.Algorithms.Lean.MergeSort.MergeSort\n",
            "@[time_simps] theorem foo : True := trivial\n",
            "theorem bar : True := by time_spec baz\n",
        ):
            with self.subTest(line=line.strip()):
                self.assertGreaterEqual(check_timem.count_uses(line), 1)

    def test_query_oracle_import_remains_allowed(self) -> None:
        self.assertEqual(
            check_timem.count_uses("import Cslib.Algorithms.Lean.Query.Basic\n"),
            0,
        )


class UnconditionalBanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        (self.root / "CslibFrontier").mkdir()

    def write(self, rel: str, content: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")

    def run_check(self, *flags: str) -> int:
        return check_timem.main(["--root", str(self.root), *flags])

    def test_clean_tree_and_query_import_pass(self) -> None:
        self.write(
            "CslibFrontier/A.lean",
            "import Cslib.Algorithms.Lean.Query.Basic\n"
            "-- `TimeM` in comment\n"
            '/-- `TimeM` in docstring -/\n'
            'def s := "TimeM ✓ time_simps time_spec"\n'
            "def c : Char := '✓'\n"
            "def RunTimeMeasure := 0\n",
        )
        self.assertEqual(self.run_check("--report"), 0)

    def test_each_forbidden_construct_fails(self) -> None:
        cases = (
            ("CslibFrontier/A.lean", "import Cslib.Algorithms.Lean.TimeM\n"),
            ("CslibFrontier/A.lean", "import CslibFrontier.Algorithms.Lean.TimeM.Loops\n"),
            ("CslibFrontier/A.lean", "import Cslib.Algorithms.Lean.MergeSort.MergeSort\n"),
            ("CslibFrontier/A.lean", "def f : TimeM ℕ ℕ := pure 0\n"),
            ("CslibFrontier/A.lean", "def f : M ℕ := do ✓ return 0\n"),
            ("CslibFrontier/A.lean", "@[time_simps] theorem foo : True := trivial\n"),
            ("CslibFrontier/A.lean", "theorem bar : True := by time_spec baz\n"),
            ("CslibFrontierTests/T.lean", "def f : TimeM ℕ ℕ := pure 0\n"),
            ("CslibFrontierResults/R.lean", "def f : TimeM ℕ ℕ := pure 0\n"),
            ("CslibFrontier.lean", "import Cslib.Algorithms.Lean.TimeM\n"),
            ("scripts/Cdcl.lean", "import Cslib.Algorithms.Lean.TimeM\n"),
            ("guide/Guide/Example.lean", "import Cslib.Algorithms.Lean.TimeM\n"),
            ("tools/Tool.lean", "import Cslib.Algorithms.Lean.TimeM\n"),
        )
        for rel, content in cases:
            with self.subTest(rel=rel, content=content.strip()):
                with tempfile.TemporaryDirectory() as sub_tmp:
                    sub_root = pathlib.Path(sub_tmp)
                    p = sub_root / rel
                    p.parent.mkdir(parents=True, exist_ok=True)
                    p.write_text(content, encoding="utf-8")
                    self.assertEqual(check_timem.main(["--root", str(sub_root)]), 1)

    def test_dot_lake_directories_are_ignored(self) -> None:
        self.write(
            "guide/.lake/packages/cslib/Cslib/Algorithms/Lean/TimeM.lean",
            "def f : TimeM ℕ ℕ := pure 0\n",
        )
        self.write("guide/Guide/Clean.lean", "def ok : ℕ := 0\n")
        self.assertEqual(self.run_check(), 0)


class RepositoryBanTests(unittest.TestCase):
    def test_repository_has_no_timem_uses(self) -> None:
        self.assertEqual(check_timem.main([]), 0)


if __name__ == "__main__":
    unittest.main()
