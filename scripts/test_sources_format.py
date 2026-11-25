"""Tests for scripts/sources_format.py."""

from __future__ import annotations

import contextlib
import io
import pathlib
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import sources_format as sf  # noqa: E402


class CanonicalTest(unittest.TestCase):
    def assertSplits(self, text: str, *lines: str) -> None:
        self.assertEqual(sf.canonical(text), "".join(f"{line}\n" for line in lines))

    def test_sentences_start_lines(self) -> None:
        self.assertSplits("One sentence. Another? A third! [Link](x.md) too. (An aside.) More.",
                          "One sentence.", "Another?", "A third!", "[Link](x.md) too.",
                          "(An aside.)", "More.")
        self.assertSplits('He said "Stop." Then *Emphasis.* Then `code` ends. § 2 follows.',
                          'He said "Stop."', "Then *Emphasis.*", "Then `code` ends.",
                          "§ 2 follows.")

    def test_lines_of_a_paragraph_are_joined_first(self) -> None:
        self.assertSplits("One sentence\nthat wraps. And\nanother.\n\nNext paragraph.",
                          "One sentence that wraps.", "And another.", "", "Next paragraph.")

    def test_abbreviations_initials_and_lowercase_do_not_split(self) -> None:
        self.assertSplits("By J. R. Smith et al. In Thm. 3, e.g. Lemma 2, cf. Section 4 on "
                          "p. 12. Then version 2. is cited. Ends here.",
                          "By J. R. Smith et al. In Thm. 3, e.g. Lemma 2, cf. Section 4 on p. 12.",
                          "Then version 2. is cited.", "Ends here.")

    def test_code_math_and_html_are_not_split(self) -> None:
        self.assertSplits("See `a. B` and ``x. `Y` z`` here. Math $x. Y$ and <span title=\"a. B\">"
                          "t</span> stay. Done.",
                          "See `a. B` and ``x. `Y` z`` here.",
                          "Math $x. Y$ and <span title=\"a. B\">t</span> stay.", "Done.")

    def test_no_line_starts_another_block(self) -> None:
        for text in ("Ends. * not a list item", "Ends. 1. not a list", "Ends. # Not a heading",
                     "Ends. > Not a quote", "Ends. ```not a fence``` here", "Ends. [^1] note",
                     "Ends. [label]: not a definition", "Ends. ***", "Ends. | not a table"):
            with self.subTest(text):
                self.assertSplits(text, text)

    def test_list_items_split_with_continuation_indent(self) -> None:
        self.assertSplits("Intro.\n\n- First one. Second\n  one.\n- Next. Last.\n10. Ten. Eleven.",
                          "Intro.", "", "- First one.", "  Second one.", "- Next.", "  Last.",
                          "10. Ten.", "    Eleven.")

    def test_other_blocks_are_kept(self) -> None:
        kept = ('<a id="key"></a>\n## key. Not split. Really.\n\n> Quote. Kept.\n\n'
                "| A. B | C. D |\n\n```\nCode. Kept.\n```\n\n    Indented. Kept.\n\n"
                "<!-- A comment.\nKept. As is.\n-->\n\n"
                "Hard break.  \nKept. As is.\n\n- Item. Nested:\n  - Inner. Kept.\n")
        self.assertEqual(sf.canonical(kept), kept)

    def test_formatting_is_idempotent_and_keeps_the_words(self) -> None:
        text = sf.SOURCES.read_text(encoding="utf-8")
        formatted = sf.canonical(text)
        self.assertEqual(sf.compare(text, formatted), [])
        self.assertEqual(sf.canonical(formatted), formatted)
        self.assertEqual(sf.unformatted(formatted), [])

    def test_a_change_of_words_is_refused(self) -> None:
        with patch.object(sf, "sentences", lambda text: text.split(". ")):
            with self.assertRaisesRegex(ValueError, "would change the text"):
                sf.canonical("One sentence. Another one.\n")


class CommandTest(unittest.TestCase):
    def run_main(self, *args: str) -> tuple[int, str]:
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            status = sf.main(list(args))
        return status, output.getvalue()

    def test_check_write_and_compare(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "sources.md"
            original = "# Sources\n\nOne. Two.\nThree.\n"
            path.write_text(original, encoding="utf-8")
            status, output = self.run_main("--check", str(path))
            self.assertEqual(status, 1)
            self.assertIn("not one sentence per line at line 3;", output)
            self.assertEqual(self.run_main("--write", str(path)), (0, ""))
            self.assertEqual(path.read_text(encoding="utf-8"), "# Sources\n\nOne.\nTwo.\nThree.\n")
            self.assertEqual(self.run_main("--check", str(path)), (0, ""))
            old = pathlib.Path(tmp) / "old.md"
            old.write_text(original, encoding="utf-8")
            status, output = self.run_main("--compare", str(old), str(path))
            self.assertEqual(status, 0)
            self.assertIn("(5 words) apart from line breaks", output)
            path.write_text("# Sources\n\nOne.\nTwo, changed.\nThree.\n", encoding="utf-8")
            status, output = self.run_main("--compare", str(old), str(path))
            self.assertEqual(status, 1)
            self.assertIn("word 4 differs", output)


if __name__ == "__main__":
    unittest.main()
