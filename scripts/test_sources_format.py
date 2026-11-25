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
        self.assertSplits("Published in\n2024. Second sentence.",
                          "Published in", "2024. Second sentence.")
        self.assertSplits("See issue\n#123. And\n<i>brief</i> note. Plus\n```code``` span. Done.",
                          "See issue #123.", "And <i>brief</i> note.", "Plus ```code``` span.",
                          "Done.")

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
        self.assertSplits("See $$ a. B $$ and $c. D$ here. Next.",
                          "See $$ a. B $$ and $c. D$ here.", "Next.")
        self.assertSplits("$$a = 1$$ is proved. Next.",
                          "$$a = 1$$ is proved.", "Next.")

    def test_no_line_starts_another_block(self) -> None:
        for text in ("Ends. * not a list item", "Ends. *\tnot a list item", "Ends. 1. not a list",
                     "Ends. (1) not a list", "Ends. A) not a list", "Ends. II. not a list",
                     "Ends. # Not a heading", "Ends. > Not a quote", "Ends. ```not a fence``` here",
                     "Ends. [^1] note", "Ends. [label]: not a definition", "Ends. ***",
                     "Ends. | not a table"):
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

    def test_setext_headings_and_reference_definitions_are_kept(self) -> None:
        for text in ("Source note. Heading\n===\n",
                     "Source note. Heading\n---\n",
                     "Heading\n--\n",
                     "  Heading. Two.\n   ===\n",
                     "- Item. Heading\n  ===\n",
                     '[key]: https://example.org "One. Two."\n[key2]: https://example.org/2\n'):
            with self.subTest(text):
                self.assertEqual(sf.canonical(text), text)
                self.assertEqual(sf.compare(text, sf.canonical(text)), [])
        # Turning a Setext heading into a paragraph keeps the words yet changes the block structure.
        self.assertTrue(any("block 1 differs" in d
                            for d in sf.compare("Source note. Heading\n===\n",
                                                "Source note.\nHeading ===\n")))

    def test_compare_distinguishes_paragraph_breaks_from_sentence_wraps(self) -> None:
        self.assertEqual(sf.compare("One. Two.\nThree.\n", "One.\nTwo.\nThree.\n"), [])
        for old, new in (("One. Two.\n\nThree.\n", "One.\nTwo.\nThree.\n"),
                         ("One. Two. Three.\n", "One.\n\nTwo.\nThree.\n"),
                         ("- One.\n- Two.\n", "- One. - Two.\n")):
            with self.subTest((old, new)):
                self.assertTrue(any("block " in d for d in sf.compare(old, new)))

    def test_multiline_html_display_math_and_pipe_tables_are_kept(self) -> None:
        cases = (
            # CommonMark §4.6 Type 1 (`<pre>`, `<script>`, `<style>`, `<textarea>`) across blanks.
            (
                "<pre>\nSource note. Keep it on one physical line.\n\n"
                "Second block. Also kept.\n</pre>\n",
                "<pre>\nSource note.\nKeep it on one physical line.\n\n"
                "Second block. Also kept.\n</pre>\n",
            ),
            (
                "<SCRIPT>\nvar x = 1. Y = 2.\n</SCRIPT>\n",
                "<SCRIPT>\nvar x = 1.\nY = 2.\n</SCRIPT>\n",
            ),
            # CommonMark §4.6 Types 3–5 (`<?...?>`, `<![A-Za-z]...>` declarations, `<![CDATA[...]>`).
            (
                "<?xml version=\"1.0\"\nfoo. Bar.\n?>\n",
                "<?xml version=\"1.0\"\nfoo.\nBar.\n?>\n",
            ),
            (
                "<!DOCTYPE\nhtml. Here.\n>\n",
                "<!DOCTYPE\nhtml.\nHere.\n>\n",
            ),
            (
                "<![CDATA[\nSource note. Keep it.\n\nAcross blank lines.\n]]>\n",
                "<![CDATA[\nSource note.\nKeep it.\n\nAcross blank lines.\n]]>\n",
            ),
            # CommonMark §4.6 Types 6–7 (block/standalone HTML tags up to the next blank line).
            (
                "<div>\nSource note. Keep HTML block.\n</div>\n",
                "<div>\nSource note.\nKeep HTML block.\n</div>\n",
            ),
            (
                "<widget>\nSource note. Keep standalone tag block.\n</widget>\n",
                "<widget>\nSource note.\nKeep standalone tag block.\n</widget>\n",
            ),
            # Display-math `$$...$$` blocks.
            (
                "$$\nf(x) = 1. G(x) = 2.\n$$\n",
                "$$ f(x) = 1. G(x) = 2. $$\n",
            ),
            (
                "$$\nf(x) = 1. G(x) = 2.\n$$\n",
                "$$\nf(x) = 1.\nG(x) = 2.\n$$\n",
            ),
            # GFM pipe tables without a leading `|` (and body rows without a leading `|`).
            (
                "Col A | Col B\n--- | ---\nCell 1. More. | Cell 2\n",
                "Col A | Col B --- | --- Cell 1.\nMore. | Cell 2\n",
            ),
            (
                "| Col A | Col B |\n| --- | --- |\nCell 1. More. | Cell 2\n",
                "| Col A | Col B |\n| --- | --- |\nCell 1.\nMore. | Cell 2\n",
            ),
            # GFM §4.10 single-cell table body row with no `|` at all, and headers/rows starting
            # with `#tag`, inline HTML (`<i>...</i>`) or inline triple-backtick code spans.
            (
                "A | B\n--- | ---\nSource note. Keep it in one cell.\n",
                "A | B\n--- | ---\nSource note.\nKeep it in one cell.\n",
            ),
            (
                "A | B\n--- | ---\n#tag. Single cell.\nAnother line. Still a cell.\n",
                "A | B\n--- | ---\n#tag. Single cell.\nAnother line.\nStill a cell.\n",
            ),
            (
                "#tag | B\n--- | ---\nAnother line. Still a cell.\n",
                "#tag | B\n--- | ---\nAnother line.\nStill a cell.\n",
            ),
            (
                "A | B\n--- | ---\n<i>brief</i> | B\nAnother line. Still a cell.\n",
                "A | B\n--- | ---\n<i>brief</i> | B\nAnother line.\nStill a cell.\n",
            ),
            (
                "<i>brief</i> | B\n--- | ---\nAnother line. Still a cell.\n",
                "<i>brief</i> | B\n--- | ---\nAnother line.\nStill a cell.\n",
            ),
            (
                "A | B\n--- | ---\n<i>\nAnother line. Still a cell.\n",
                "A | B\n--- | ---\n<i>\nAnother line.\nStill a cell.\n",
            ),
            (
                "A | B\n--- | ---\n```code``` | B\nAnother line. Still a cell.\n",
                "A | B\n--- | ---\n```code``` | B\nAnother line.\nStill a cell.\n",
            ),
            (
                "```code``` | B\n--- | ---\nAnother line. Still a cell.\n",
                "```code``` | B\n--- | ---\nAnother line.\nStill a cell.\n",
            ),
            # GFM §4.10 tables with Pandoc-only `:::` divs or `$$...$$` math in headers or rows.
            (
                "A | B\n--- | ---\n:::note\nAnother line. Still a cell.\n",
                "A | B\n--- | ---\n:::note\nAnother line.\nStill a cell.\n",
            ),
            (
                "A | B\n--- | ---\n$$x = 1.$$\nAnother line. Still a cell.\n",
                "A | B\n--- | ---\n$$x = 1.$$\nAnother line.\nStill a cell.\n",
            ),
            (
                ":::note | B\n--- | ---\nAnother line. Still a cell.\n",
                ":::note | B\n--- | --- Another line.\nStill a cell.\n",
            ),
            (
                ":::note | B\n--- | ---\nAnother line. Still a cell.\n",
                ":::note | B\n--- | ---\nAnother line.\nStill a cell.\n",
            ),
            (
                "$$x$$\n| --- |\nAnother line. Still a cell.\n",
                "$$x$$\n| --- |\nAnother line.\nStill a cell.\n",
            ),
            (
                "$$x$$ | B\n--- | ---\nAnother line. Still a cell.\n",
                "$$x$$ | B\n--- | ---\nAnother line.\nStill a cell.\n",
            ),
            # Blocks opened on the first line of a list item (`- <pre>`, `- ``` `, `- $$`,
            # `- #`, `- >`, `- A | B`), including unindented raw-HTML continuations.
            (
                "- <pre>\nSource note. Keep it on one physical line.\n</pre>\n",
                "- <pre>\nSource note.\nKeep it on one physical line.\n</pre>\n",
            ),
            (
                "- <pre>\n  Source note. Keep it on one physical line.\n  </pre>\n",
                "- <pre> Source note.\n  Keep it on one physical line.\n  </pre>\n",
            ),
            (
                "- <pre>\n  Source note. Keep it.\n\n  After blank.\n  </pre>\n",
                "- <pre>\n  Source note.\n  Keep it.\n\n  After blank.\n  </pre>\n",
            ),
            (
                "- ```\n  Code. Line.\n  ```\n",
                "- ``` Code.\n  Line.\n  ```\n",
            ),
            (
                "- $$\n  f(x) = 1. G(x) = 2.\n  $$\n",
                "- $$ f(x) = 1.\n  G(x) = 2. $$\n",
            ),
            (
                "- # Heading. Two.\n",
                "- # Heading.\n  Two.\n",
            ),
            (
                "- > Quote. Two.\n  Continuation. Three.\n",
                "- > Quote.\n  Two. Continuation. Three.\n",
            ),
            (
                "- A | B\n  --- | ---\n  Source note. Keep it in one cell.\n",
                "- A | B\n  --- | ---\n  Source note.\n  Keep it in one cell.\n",
            ),
            # Block quote with lazy continuation lines (including across `:::`, `$$` and `#`).
            (
                "> Quote starts.\nLazy continuation. Keep it.\n",
                "> Quote starts.\nLazy continuation.\nKeep it.\n",
            ),
            (
                "> Quote.\n:::note\nLazy line. Still quote.\n",
                "> Quote.\n:::note\nLazy line.\nStill quote.\n",
            ),
            (
                "> Quote.\n$$x = 1.$$\nLazy line. Still quote.\n",
                "> Quote.\n$$x = 1.$$\nLazy line.\nStill quote.\n",
            ),
            (
                "> Quote.\n# Not a heading in Pandoc.\nLazy line. Still quote.\n",
                "> Quote.\n# Not a heading in Pandoc.\nLazy line.\nStill quote.\n",
            ),
        )
        for original, mutated in cases:
            with self.subTest(original=original):
                self.assertEqual(sf.canonical(original), original)
                self.assertEqual(sf.compare(original, sf.canonical(original)), [])
                self.assertTrue(any("block " in d for d in sf.compare(original, mutated)))
        # Paragraphs preceding a multi-line block still split cleanly while keeping the block.
        self.assertSplits(
            "Intro. More.\nCol A | Col B\n--- | ---\nCell 1. More. | Cell 2\n",
            "Intro.", "More.", "Col A | Col B", "--- | ---", "Cell 1. More. | Cell 2")
        self.assertSplits(
            '<a id="key"></a>\n## key\n\nFirst. Second.\n',
            '<a id="key"></a>', "## key", "", "First.", "Second.")

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
            path.write_text("# Sources\n\nOne.\n\nTwo.\nThree.\n", encoding="utf-8")
            status, output = self.run_main("--compare", str(old), str(path))
            self.assertEqual(status, 1)
            self.assertIn("block 3 differs", output)
            old_pre = pathlib.Path(tmp) / "pre_old.md"
            new_pre = pathlib.Path(tmp) / "pre_new.md"
            old_pre.write_text("<pre>\nSource note. Keep it on one physical line.\n</pre>\n",
                               encoding="utf-8")
            new_pre.write_text("<pre>\nSource note.\nKeep it on one physical line.\n</pre>\n",
                               encoding="utf-8")
            status, output = self.run_main("--compare", str(old_pre), str(new_pre))
            self.assertEqual(status, 1)
            self.assertIn("block 1 differs", output)
            for cell_row in ("#tag. Single cell.", "<i>brief</i> | B", "```code``` | B",
                             ":::note", "$$x = 1.$$"):
                old_tbl = pathlib.Path(tmp) / "tbl_old.md"
                new_tbl = pathlib.Path(tmp) / "tbl_new.md"
                old_tbl.write_text(f"A | B\n--- | ---\n{cell_row}\nAnother line. Still a cell.\n",
                                   encoding="utf-8")
                new_tbl.write_text(f"A | B\n--- | ---\n{cell_row}\nAnother line.\nStill a cell.\n",
                                   encoding="utf-8")
                status, output = self.run_main("--compare", str(old_tbl), str(new_tbl))
                self.assertEqual(status, 1)
                self.assertIn("block 1 differs", output)


if __name__ == "__main__":
    unittest.main()
