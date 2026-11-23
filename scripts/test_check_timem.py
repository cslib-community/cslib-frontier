"""Unit tests for scripts/check_timem.py."""

from __future__ import annotations

import json
import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_timem  # noqa: E402


class MaskedSyntaxTests(unittest.TestCase):
    def test_line_comment_and_docstring_are_not_counted(self) -> None:
        text = "-- TimeM is not used here\n/-- no `TimeM` bound -/\ndef f : ℕ := 1\n"
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
            'def s := "TimeM ✓ -- not a comment"\n'
            'def r := r#"TimeM ✓ /- not a block comment"#\n'
            "def c : Char := '✓'\n"
            "def f' : TimeM ℕ ℕ := pure 0\n"
        )
        self.assertEqual(check_timem.count_uses(text), 1)

    def test_longer_identifier_is_not_a_use(self) -> None:
        self.assertEqual(check_timem.count_uses("def RunTimeMeasure := 0\n"), 0)

    def test_automation_without_explicit_monad_or_tick(self) -> None:
        text = (
            "@[time_simps] theorem ret_f : (f xs).ret = xs := by time_spec f\n"
            "attribute [time_simps] ret_g\n"
            "example : (f xs).ret = xs := by simp only [time_simps]\n"
        )
        self.assertEqual(check_timem.count_uses(text), 0)
        self.assertEqual(check_timem.count_uses(text, check_timem.AUTOMATION), 4)

    def test_automation_masks_prose_and_literals(self) -> None:
        text = (
            '/-- Replace `time_spec`; /- no time_simps -/ -/\n'
            'def s := "time_spec time_simps"\n'
            'def r := r#"time_spec time_simps"#\n'
            '-- time_spec\n'
            'example : True := by time_spec/-separator-/f\n'
        )
        self.assertEqual(check_timem.count_uses(text, check_timem.AUTOMATION), 1)

    def test_longer_automation_identifiers_are_not_uses(self) -> None:
        text = "def time_specification := 0\ndef time_simps_extra := 0\n"
        self.assertEqual(check_timem.count_uses(text, check_timem.AUTOMATION), 0)


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

    def run_check(self, files: dict[str, int], *flags: str,
                  automation: dict[str, int] | None = None) -> int:
        self.baseline.write_text(json.dumps({"files": files, "automation": automation or {}}),
                                 encoding="utf-8")
        return check_timem.main(
            ["--root", str(self.root), "--baseline", str(self.baseline), *flags])

    def test_new_file_fails(self) -> None:
        self.write("CslibFrontier/A.lean", "def f : TimeM ℕ ℕ := pure 0\n")
        self.assertEqual(self.run_check({}), 1)

    def test_rise_in_a_recorded_file_fails(self) -> None:
        self.write("CslibFrontier/A.lean", "def f : TimeM ℕ ℕ := do ✓ return 0\n")
        self.assertEqual(self.run_check({"CslibFrontier/A.lean": 1}), 1)

    def test_comment_separated_rise_in_recorded_file_fails(self) -> None:
        self.write(
            "CslibFrontier/A.lean",
            "def old : TimeM Nat Nat := pure 0\n"
            "def added : TimeM/-separator-/Nat Nat := pure 0\n",
        )
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

    def test_new_automation_fails_without_explicit_monad(self) -> None:
        for source in ("@[time_simps] theorem ret_f : (f x).ret = x := rfl\n",
                       "example : (f x).ret = x := by time_spec f\n"):
            with self.subTest(source=source):
                self.write("CslibFrontier/A.lean", source)
                self.assertEqual(self.run_check({}), 1)

    def test_less_monad_use_does_not_allow_more_automation(self) -> None:
        self.write("CslibFrontier/A.lean", "example : (f x).ret = x := by time_spec f\n")
        self.assertEqual(self.run_check({"CslibFrontier/A.lean": 10}, "--update"), 1)
        self.assertEqual(json.loads(self.baseline.read_text()),
                         {"files": {"CslibFrontier/A.lean": 10}, "automation": {}})

    def test_automation_rise_fails_and_update_preserves_both_ratchets(self) -> None:
        self.write("CslibFrontier/A.lean", "@[time_simps] theorem ret_f : P := by time_spec f\n")
        baseline = {"files": {"CslibFrontier/A.lean": 3},
                    "automation": {"CslibFrontier/A.lean": 1}}
        self.assertEqual(self.run_check(baseline["files"], "--update",
                                       automation=baseline["automation"]), 1)
        self.assertEqual(json.loads(self.baseline.read_text()), baseline)

    def test_automation_fall_and_removal_pass_then_update_lowers(self) -> None:
        self.write("CslibFrontier/A.lean", "example : P := by time_spec f\n")
        recorded = {"CslibFrontier/A.lean": 3, "CslibFrontier/Gone.lean": 1}
        self.assertEqual(self.run_check({}, automation=recorded), 0)
        self.assertEqual(json.loads(self.baseline.read_text())["automation"], recorded)
        self.assertEqual(self.run_check({}, "--update", automation=recorded), 0)
        self.assertEqual(json.loads(self.baseline.read_text())["automation"],
                         {"CslibFrontier/A.lean": 1})

    def test_automation_scans_test_results_and_aggregates(self) -> None:
        for path in ("CslibFrontierTests/A.lean", "CslibFrontierResults/A.lean",
                     "CslibFrontier.lean", "CslibFrontierTests.lean", "CslibFrontierResults.lean"):
            self.write(path, "example : P := by time_spec f\n")
        self.assertEqual(len(check_timem.scan(self.root)["automation"]), 5)
        self.assertEqual(self.run_check({}), 1)


class RepositoryBaselineTests(unittest.TestCase):
    def test_repository_is_within_its_baseline(self) -> None:
        self.assertEqual(check_timem.main([]), 0)


if __name__ == "__main__":
    unittest.main()
