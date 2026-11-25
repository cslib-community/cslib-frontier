"""Tests for scripts/resolve_sources_conflict.py."""

from __future__ import annotations

import os
import pathlib
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import resolve_sources_conflict as rsc  # noqa: E402
import sources_format  # noqa: E402

SCRIPT = pathlib.Path(rsc.__file__).resolve()
SOURCES = pathlib.Path(sources_format.SOURCES)
PREAMBLE = "# Primary sources and provenance\n\nThe preamble's first sentence.\nIts second one."


def entry(key: str, *paragraphs: str) -> str:
    return f'<a id="{key}"></a>\n## {key}\n\n' + "\n\n".join(paragraphs)


def page(*entries: str, preamble: str = PREAMBLE) -> str:
    return "\n\n".join((preamble, *entries)) + "\n"


ALPHA = "Alpha one.\nAlpha two.\nAlpha three."
BASE = page(entry("alpha", ALPHA), entry("beta", "Beta one.\nBeta two."))


def edit(text: str, old: str, new: str) -> str:
    assert text.count(old) == 1, old
    return text.replace(old, new)


def merge_file_conflicts(base: str, ours: str, theirs: str) -> int:
    """The number of conflicts that git's text merge reports."""
    with tempfile.TemporaryDirectory() as tmp:
        paths = [os.path.join(tmp, name) for name in ("base", "ours", "theirs")]
        for path, text in zip(paths, (base, ours, theirs)):
            pathlib.Path(path).write_text(text, encoding="utf-8")
        return subprocess.run(["git", "merge-file", "-p", paths[1], paths[0], paths[2]],
                              capture_output=True).returncode


class MergeTest(unittest.TestCase):
    def merged(self, base: str, ours: str, theirs: str) -> str:
        """The merge, checked to be the same with the sides swapped."""
        result = rsc.merge_sources(base, ours, theirs)
        self.assertEqual(rsc.merge_sources(base, theirs, ours), result)
        return result

    def test_edits_of_adjacent_sentences_merge(self) -> None:
        ours = edit(BASE, "Alpha one.", "Alpha one, revised.")
        theirs = edit(BASE, "Alpha two.", "Alpha two, revised.")
        self.assertEqual(merge_file_conflicts(BASE, ours, theirs), 1)
        self.assertEqual(self.merged(BASE, ours, theirs),
                         edit(ours, "Alpha two.", "Alpha two, revised."))

    def test_sentences_added_at_one_place_are_kept_in_text_order(self) -> None:
        ours = edit(BASE, "Alpha three.", "Alpha three.\nZeta, added by ours.")
        theirs = edit(BASE, "Alpha three.", "Alpha three.\nGamma, added by theirs.")
        self.assertEqual(self.merged(BASE, ours, theirs), edit(
            BASE, "Alpha three.", "Alpha three.\nGamma, added by theirs.\nZeta, added by ours."))

    def test_a_new_paragraph_follows_a_continued_one(self) -> None:
        ours = edit(BASE, "Alpha three.", "Alpha three.\n\nA new paragraph.")
        theirs = edit(BASE, "Alpha three.", "Alpha three.\nZeta continues it.")
        self.assertEqual(self.merged(BASE, ours, theirs), edit(
            BASE, "Alpha three.", "Alpha three.\nZeta continues it.\n\nA new paragraph."))

    def test_entries_added_at_one_place_interleave_in_key_order(self) -> None:
        ours = edit(BASE, "\n\n<a id=\"beta\">",
                    "\n\n" + entry("alphb", "B.") + "\n\n" + entry("alphd", "D.")
                    + "\n\n<a id=\"beta\">")
        theirs = edit(BASE, "\n\n<a id=\"beta\">",
                      "\n\n" + entry("alphc", "C.") + "\n\n<a id=\"beta\">")
        self.assertEqual(rsc.parse(self.merged(BASE, ours, theirs), "merged")[1],
                         ["alpha", "alphb", "alphc", "alphd", "beta"])

    def test_one_sided_and_identical_changes_are_taken(self) -> None:
        ours = edit(edit(BASE, "Beta two.", "Beta two, revised."), "Its second one.",
                    "Its second one.\nA third.")
        theirs = edit(BASE, "\n\n" + entry("beta", "Beta one.\nBeta two."), "")
        self.assertEqual(self.merged(BASE, ours, ours), ours)
        self.assertEqual(self.merged(BASE, BASE, theirs), theirs)
        both = edit(BASE, "Alpha one.", "Alpha one, revised.")
        self.assertEqual(self.merged(BASE, both, both), both)

    def test_changes_to_the_preamble_and_an_entry_merge(self) -> None:
        ours = edit(BASE, "Its second one.", "Its second one, revised.")
        theirs = edit(BASE, "Beta one.", "Beta one, revised.")
        self.assertEqual(self.merged(BASE, ours, theirs),
                         edit(ours, "Beta one.", "Beta one, revised."))

    def test_conflicting_changes_are_refused(self) -> None:
        cases = {
            "same lines": (edit(BASE, "Alpha two.", "Alpha 2."),
                           edit(BASE, "Alpha two.", "Alpha II.")),
            "deleted entry `beta`": (
                edit(BASE, "\n\n" + entry("beta", "Beta one.\nBeta two."), ""),
                edit(BASE, "Beta two.", "Beta two, revised.")),
            "entry `gamma` with different text": (
                BASE + "\n" + entry("gamma", "Ours.") + "\n",
                BASE + "\n" + entry("gamma", "Theirs.") + "\n"),
            "entry `gamma` to different places": (
                BASE + "\n" + entry("gamma", "G.") + "\n",
                edit(BASE, "\n\n<a id=\"beta\">", "\n\n" + entry("gamma", "G.")
                     + "\n\n<a id=\"beta\">")),
        }
        for reason, (ours, theirs) in cases.items():
            with self.subTest(reason):
                for sides in ((ours, theirs), (theirs, ours)):
                    with self.assertRaisesRegex(rsc.Refusal, reason):
                        rsc.merge_sources(BASE, *sides)

    def test_partial_overlap_insertions_are_refused_symmetrically(self) -> None:
        unconverted = page(entry("alpha", "Alpha one. Alpha two."), preamble="# Sources")
        cases = {
            "shared paragraph lead-in": (
                BASE,
                edit(BASE, "Alpha three.",
                     "Alpha three.\n\nRead in the same edition.\nTheorem 1.1 is proved in Foo."),
                edit(BASE, "Alpha three.",
                     "Alpha three.\n\nRead in the same edition.\nTheorem 2.2 is proved in Bar."),
            ),
            "shared lead-in before conversion": (
                unconverted,
                edit(unconverted, "Alpha two.",
                     "Alpha two.\n\nRead in the same edition. Theorem 1.1 is proved in Foo."),
                edit(unconverted, "Alpha two.",
                     "Alpha two.\n\nRead in the same edition. Theorem 2.2 is proved in Bar."),
            ),
            "shared sentence continuing a paragraph": (
                BASE,
                edit(BASE, "Alpha three.",
                     "Alpha three.\nRead in the same edition.\nTheorem 1.1 is proved in Foo."),
                edit(BASE, "Alpha three.",
                     "Alpha three.\nRead in the same edition.\nTheorem 2.2 is proved in Bar."),
            ),
            "subset insertion": (
                BASE,
                edit(BASE, "Alpha three.", "Alpha three.\nShared note."),
                edit(BASE, "Alpha three.", "Alpha three.\nShared note.\nExtra note."),
            ),
            "adjacent replace and insert adding the same sentence": (
                BASE,
                edit(BASE, "Alpha three.", "Alpha three, revised.\nRead in the same edition."),
                edit(BASE, "Alpha three.", "Alpha three.\nRead in the same edition."),
            ),
        }
        for label, (base, ours, theirs) in cases.items():
            with self.subTest(label):
                for sides in ((ours, theirs), (theirs, ours)):
                    with self.assertRaisesRegex(rsc.Refusal,
                                                r"overlapping (?:lines|sentences) in entry `alpha`"):
                        rsc.merge_sources(base, *sides)

    def test_setext_headings_are_preserved_or_refused_in_merge(self) -> None:
        ours = edit(BASE, "Alpha three.", "Alpha three.\n\nSource note. Heading\n===")
        theirs = edit(BASE, "Beta one.", "Beta one, revised.")
        merged = self.merged(BASE, ours, theirs)
        self.assertIn("Source note. Heading\n===\n", merged)
        # Synthesizing a Setext heading from one side's text and the other side's `===` is refused.
        ours_text = edit(BASE, "Alpha three.", "Alpha three.\nHeading")
        theirs_bar = edit(BASE, "Alpha three.", "Alpha three.\n===")
        for sides in ((ours_text, theirs_bar), (theirs_bar, ours_text)):
            with self.assertRaisesRegex(rsc.Refusal, "Setext heading"):
                rsc.merge_sources(BASE, *sides)

    def test_malformed_versions_are_refused(self) -> None:
        cases = {
            "duplicate entries": BASE + "\n" + entry("alpha", "Again.") + "\n",
            "not on a line of its own": edit(BASE, "Beta one.", 'Beta <a id="x"></a> one.'),
        }
        for reason, theirs in cases.items():
            with self.subTest(reason), self.assertRaisesRegex(rsc.Refusal, reason):
                rsc.merge_sources(BASE, edit(BASE, "Alpha one.", "Alpha 1."), theirs)

    def test_a_branch_from_before_the_conversion_merges_sentence_by_sentence(self) -> None:
        base = page(entry("alpha", "Alpha one. Alpha two. Alpha three."),
                    entry("beta", "Beta one. Beta two."), preamble="# Sources")
        ours = edit(base, "Alpha three.", "Alpha three. Alpha four, added before the conversion.")
        theirs = edit(sources_format.canonical(base), "Alpha two.", "Alpha two, revised.")
        self.assertNotEqual(sources_format.canonical(base), base)
        self.assertEqual(merge_file_conflicts(base, ours, theirs), 1)
        self.assertEqual(self.merged(base, ours, theirs), edit(
            theirs, "Alpha three.", "Alpha three.\nAlpha four, added before the conversion."))

    def test_without_the_format_whole_lines_are_merged(self) -> None:
        base = page(entry("alpha", "Alpha one. Alpha two."), entry("beta", "Beta."),
                    preamble="# Sources")
        ours = edit(base, "Alpha one.", "Alpha 1.")
        theirs = edit(base, "Alpha two.", "Alpha 2.")
        with self.assertRaisesRegex(rsc.Refusal, "same lines"):
            rsc.merge_sources(base, ours, theirs)
        self.assertEqual(self.merged(base, ours, edit(base, "Beta.", "Beta, revised.")),
                         edit(ours, "Beta.", "Beta, revised."))

    def test_the_repository_page_round_trips(self) -> None:
        text = SOURCES.read_text(encoding="utf-8")
        for version in (text, sources_format.canonical(text)):
            self.assertEqual(rsc.merge_sources(version, version, version), version)


class DriverTest(unittest.TestCase):
    def run_driver(self, base: str, ours: str, theirs: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmp:
            paths = [os.path.join(tmp, name) for name in ("base", "ours", "theirs")]
            for path, text in zip(paths, (base, ours, theirs)):
                pathlib.Path(path).write_text(text, encoding="utf-8")
            status = subprocess.run([sys.executable, str(SCRIPT), "--driver", *paths],
                                    capture_output=True).returncode
            return status, pathlib.Path(paths[1]).read_text(encoding="utf-8")

    def test_driver_writes_the_merge(self) -> None:
        ours = edit(BASE, "Alpha one.", "Alpha 1.")
        theirs = edit(BASE, "Alpha two.", "Alpha 2.")
        self.assertEqual(self.run_driver(BASE, ours, theirs),
                         (0, edit(ours, "Alpha two.", "Alpha 2.")))

    def test_a_refused_merge_leaves_sentence_conflict_markers(self) -> None:
        base = page(entry("alpha", "Alpha one. Alpha two. Alpha three."), preamble="# Sources")
        ours = edit(base, "Alpha two.", "Alpha 2.")
        theirs = edit(sources_format.canonical(base), "Alpha two.", "Alpha II.")
        status, text = self.run_driver(base, ours, theirs)
        self.assertEqual(status, 1)
        self.assertIn("<<<<<<< ours\nAlpha 2.\n=======\nAlpha II.\n>>>>>>> theirs\n", text)

    def test_git_merge_uses_the_configured_driver(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)

            def git(*args: str) -> subprocess.CompletedProcess:
                return subprocess.run(
                    ["git", "-c", "user.name=t", "-c", "user.email=t@invalid", "-c",
                     f"merge.sourcesmd.driver={sys.executable} {SCRIPT} --driver %O %A %B",
                     *args], cwd=root, capture_output=True, text=True)

            def commit(text: str, message: str) -> None:
                (root / "manual").mkdir(exist_ok=True)
                (root / "manual" / "sources.md").write_text(text, encoding="utf-8")
                git("add", "-A")
                git("commit", "-q", "-m", message)

            git("init", "-q", "-b", "main")
            (root / ".gitattributes").write_text("manual/sources.md merge=sourcesmd\n")
            commit(BASE, "base")
            git("checkout", "-q", "-b", "side")
            commit(edit(BASE, "Alpha one.", "Alpha 1."), "side")
            git("checkout", "-q", "main")
            commit(edit(BASE, "Alpha two.", "Alpha 2."), "main")
            result = git("merge", "-q", "--no-edit", "side")
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual((root / "manual" / "sources.md").read_text(encoding="utf-8"),
                             edit(edit(BASE, "Alpha one.", "Alpha 1."), "Alpha two.", "Alpha 2."))


if __name__ == "__main__":
    unittest.main()
