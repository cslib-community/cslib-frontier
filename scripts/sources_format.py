#!/usr/bin/env python3
"""The line format of `manual/sources.md`: each sentence of a paragraph or list item on its own
line.

Many pull requests add a sentence to the same bibliography entry, and when an entry's prose is
one long line any two of them conflict, even when they add different sentences. In the line
format each sentence starts a line, so independent edits touch different lines. GitHub's
Markdown and the Pandoc reader of the PDF build both join the lines of a paragraph with spaces,
so the file renders exactly as it would with each paragraph on one line.

`canonical(text)` writes `text` in this format. It joins the lines of each paragraph and of
each list item and splits the result after every sentence end: `.`, `?` or `!`, possibly followed
by closing quotes, brackets or emphasis, then one space and the start of a sentence (a capital
letter, `[`, `(`, `*`, `` ` ``, `§` or an opening quote). It does not split inside code spans,
`$...$` math or HTML tags, after an initial or a common abbreviation, or where the next line
could start another Markdown block. Continuation lines of a list item are indented to its text.
Headings (ATX and Setext), HTML blocks (`<pre>`, comments, `<div>`, standalone tags), display
math (`$$...$$`), GFM pipe tables, fenced code, blank lines, reference definitions and every
other kind of block are kept as they are. The result has the same Markdown block structure and
joins back to the same text: `canonical` refuses to return output whose blocks, paragraph breaks,
words or punctuation differ from its input apart from soft line breaks and the indentation of list
continuation lines.

    python3 scripts/sources_format.py --check [FILE]      # exit 1 if FILE is not in the format
    python3 scripts/sources_format.py --write [FILE]      # rewrite FILE in the format
    python3 scripts/sources_format.py --compare OLD NEW   # same blocks and words?

FILE defaults to `manual/sources.md`. `scripts/resolve_sources_conflict.py`, the file's merge
driver, uses `canonical` to merge versions written before and after the conversion.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ROOT / "manual" / "sources.md"

# A list item: its marker and the text after it.
LIST_ITEM = re.compile(r"(?P<marker>(?:[-*+]|\d{1,9}[.)])[ ]+)(?P<text>\S.*)")
# A Setext heading underline: `=` or `-` characters after at most three spaces.
SETEXT = re.compile(r" {0,3}(?:=+|-+)[ \t]*$")
# A link or footnote reference definition (`[label]: url`), kept as its own line at block start.
REFERENCE_DEF = re.compile(r" {0,3}\[[^\]]+\]:(?:\s|$)")
# Lines that open another Markdown block (after up to three spaces) and end any paragraph:
# anchors and other HTML, ATX headings, block quotes, tables, fences, thematic breaks and
# Pandoc's `:::` divs.
BLOCK_OPENER = re.compile(r" {0,3}(?:<|#|>|\||`{3,}|~{3,}|:::|([-*_])( *\1){2,}[ \t]*$)")
# The opening line of a fenced code block, whose lines up to the closing fence are kept.
FENCE = re.compile(r" {0,3}(`{3,}|~{3,})")
# Display math (`$$...$$`) and CommonMark §4.6 HTML block forms, kept across their full spans.
DISPLAY_MATH = re.compile(r" {0,3}\$\$")
HTML_RAW_OPEN = re.compile(r" {0,3}<(?:pre|script|style|textarea)(?:\s|>|$)", re.I)
HTML_RAW_CLOSE = re.compile(r"</(?:pre|script|style|textarea)>", re.I)
HTML_DECL_OPEN = re.compile(r" {0,3}<![A-Za-z]")
HTML_BLOCK_TAG = re.compile(
    r" {0,3}</?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup"
    r"|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset"
    r"|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|nav|noframes|ol"
    r"|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr"
    r"|track|ul)(?:\s|/?>|$)",
    re.I,
)
HTML_SINGLE_TAG = re.compile(
    r" {0,3}(?:<[A-Za-z][A-Za-z0-9-]*(?:\s+(?:[^<>\"']|\"[^\"]*\"|'[^']*')*)?/?>|"
    r"</[A-Za-z][A-Za-z0-9-]*\s*>)[ \t]*$"
)
TABLE_CELL = re.compile(r"\s*:?-+:?\s*")
# The end of a sentence: the last word before a split ends this way.
SENTENCE_END = re.compile(r"(?P<word>\S*?)[.?!][\"”’)\]*_]*")
# Words that end with a period without ending a sentence, compared without case: Pandoc's own
# list (`pandoc --print-default-data-file abbreviations`), after which its `smart` extension
# writes a non-breaking space that a line break would lose, and a few more.
ABBREVIATIONS = frozenset("""
    aet aetat al apr aug bk bros c capt cf ch chap chs co col corp cp d dec dr e.g ed eds esp f
    fasc feb ff fig fl fol fols fr gen gov hon i.e ill inc incl jan jr jul jun ltd m.a m.d mar mr
    mrs ms n n.b nn no nov oct p ph.d pp pres prof pt q.v rep rev s.v s.vv saec sec sen sep sept
    sgt sr st univ viz vol vs
    approx art cor def dept eq eqs etc ex figs lem nos op prop resp secs thm vols""".split())
# Characters that may start a sentence line (with the exceptions in `starts_sentence`).
STARTERS = frozenset("[(*_`§\"“‘")
# How much of the text after a space `starts_sentence` reads.
LOOKAHEAD = 200


def protected(text: str) -> list[tuple[int, int]]:
    """The spans of `text` that are never split: code spans, `$...$` math and HTML tags."""
    spans: list[tuple[int, int]] = []
    # A code span runs from a backtick string to the next one of the same length.
    runs = list(re.finditer(r"`+", text))
    following, latest = [None] * len(runs), {}
    for k in range(len(runs) - 1, -1, -1):
        following[k] = latest.get(len(runs[k].group()))
        latest[len(runs[k].group())] = k
    k = 0
    while k < len(runs):
        close = following[k]
        if close is None:
            k += 1
            continue
        spans.append((runs[k].start(), runs[close].end()))
        k = close + 1

    def free(i: int) -> bool:
        return not any(a <= i < b for a, b in spans)

    # Shield `$$...$$` before single-`$` math so `$$` never splits or leaves a stray `$`.
    i, double_math = 0, []
    while (start := text.find("$$", i)) != -1:
        i = start + 2
        if not free(start) or (start and text[start - 1] == "\\"):
            continue
        end = start + 2
        while (end := text.find("$$", end)) != -1:
            if text[end - 1] != "\\":
                break
            end += 1
        if end == -1:
            continue
        double_math.append((start, end + 2))
        i = end + 2
    spans += double_math

    # Pandoc's `tex_math_dollars`: `$` before a non-space opens, `$` after one closes unless a
    # digit follows.
    i, math = 0, []
    while (start := text.find("$", i)) != -1:
        i = start + 1
        if not free(start) or (start and text[start - 1] == "\\"):
            continue
        if start + 1 >= len(text) or text[start + 1].isspace():
            continue
        end = start + 1
        while (end := text.find("$", end + 1)) != -1:
            if (not text[end - 1].isspace() and text[end - 1] != "\\"
                    and not text[end + 1:end + 2].isdigit()):
                break
        if end == -1:
            continue
        math.append((start, end + 1))
        i = end + 1
    spans += math
    spans += [(m.start(), m.end()) for m in re.finditer(r"<[^<>]*>", text) if free(m.start())]
    return spans


def ends_sentence(word: str) -> bool:
    """Whether `word`, the last word before a space, ends a sentence."""
    match = SENTENCE_END.fullmatch(word)
    if not match:
        return False
    word = match.group("word").lstrip("([\"“‘*_").rstrip(".")
    if not word:
        return False
    if len(word) == 1 and word.isalpha():  # an initial, or `p.` before a page number
        return False
    return word.casefold() not in ABBREVIATIONS


def starts_sentence(after: str) -> bool:
    """Whether `after`, the text after a space, may start a line inside a paragraph without
    starting another Markdown block in GitHub's or Pandoc's reading."""
    first = after[:1]
    if not first or SETEXT.match(after) or LIST_ITEM.match(after):
        return False
    if first.isupper():
        return True
    if first not in STARTERS:
        return False
    if first in "*_" and (after[1:2] in ("", " ") or BLOCK_OPENER.match(after)):
        return False
    if first == "`" and after.startswith("```"):
        return False
    if first == "[" and (after.startswith("[^") or REFERENCE_DEF.match(after)):
        return False
    return True


def sentences(text: str) -> list[str]:
    """Split one paragraph's text into sentence lines; joining them with spaces gives `text`."""
    shielded = bytearray(len(text))
    for a, b in protected(text):
        shielded[a:b] = b"\1" * (b - a)
    pieces, start = [], 0
    for space in re.finditer(r" (?=\S)", text):
        i = space.start()
        if shielded[i]:
            continue
        word = max(start, text.rfind(" ", start, i) + 1)
        if ends_sentence(text[word:i]) and starts_sentence(text[i + 1:i + 1 + LOOKAHEAD]):
            pieces.append(text[start:i])
            start = i + 1
    pieces.append(text[start:])
    return pieces


def hard_break(line: str) -> bool:
    """Whether a line ends with a hard line break, which joining would remove."""
    return line.endswith("  ") or line.endswith("\\")


def html_block_end(lines: list[str], i: int, *, in_paragraph: bool = False) -> int | None:
    """Exclusive end line of a CommonMark §4.6 HTML block starting at `lines[i]`, else None."""
    line = lines[i]
    stripped = line.lstrip(" ")
    if len(line) - len(stripped) > 3 or not stripped.startswith("<"):
        return None
    if HTML_RAW_OPEN.match(line):  # Type 1: `<pre>`, `<script>`, `<style>`, `<textarea>`
        close = next((k for k in range(i, len(lines)) if HTML_RAW_CLOSE.search(lines[k])),
                     len(lines) - 1)
        return close + 1
    for prefix, closing in (("<!--", "-->"), ("<?", "?>"), ("<![CDATA[", "]]>")):  # Types 2, 3, 5
        if stripped.startswith(prefix):
            close = next((k for k in range(i, len(lines))
                          if closing in (stripped[len(prefix):] if k == i else lines[k])),
                         len(lines) - 1)
            return close + 1
    if HTML_DECL_OPEN.match(line):  # Type 4: `<!DOCTYPE ...>`
        close = next((k for k in range(i, len(lines))
                      if ">" in (stripped[2:] if k == i else lines[k])), len(lines) - 1)
        return close + 1
    if HTML_BLOCK_TAG.match(line) or (not in_paragraph and HTML_SINGLE_TAG.match(line)):
        # Types 6 and 7 run until the next blank line.
        return next((k for k in range(i + 1, len(lines)) if not lines[k].strip()), len(lines))
    return None


def display_math_end(lines: list[str], i: int) -> int | None:
    """Exclusive end line of a `$$...$$` display-math block starting at `lines[i]`, else None."""
    match = DISPLAY_MATH.match(lines[i])
    if not match:
        return None
    rest = lines[i][match.end():]
    if "$$" in rest:
        return i + 1 if rest.count("$$") == 1 and rest.rstrip(" \t").endswith("$$") else None
    close = next((k for k in range(i + 1, len(lines)) if "$$" in lines[k]), len(lines) - 1)
    return close + 1


def is_table_delimiter(line: str) -> bool:
    """Whether `line` is a GFM pipe-table delimiter row (`| --- |` or `--- | ---`)."""
    if len(line) - len(line.lstrip(" ")) > 3 or "|" not in line:
        return False
    stripped = line.strip()
    cells = stripped.split("|")
    if stripped.startswith("|"):
        cells = cells[1:]
    if stripped.endswith("|"):
        cells = cells[:-1]
    return bool(cells) and all(TABLE_CELL.fullmatch(cell) for cell in cells)


def table_end(lines: list[str], i: int) -> int | None:
    """Exclusive end line of a GFM pipe table starting at header `lines[i]`, else None."""
    if i + 1 >= len(lines) or not is_table_delimiter(lines[i + 1]):
        return None
    header = lines[i]
    if (not header.strip() or len(header) - len(header.lstrip(" ")) > 3 or "|" not in header
            or FENCE.match(header) or SETEXT.match(header) or LIST_ITEM.fullmatch(header)):
        return None
    j = i + 2
    while (j < len(lines) and lines[j].strip() and "|" in lines[j]
           and not FENCE.match(lines[j]) and html_block_end(lines, j, in_paragraph=True) is None
           and display_math_end(lines, j) is None):
        j += 1
    return j


def _iter_blocks(lines: list[str]):
    """Yield `('blank', lines)`, `('opaque', lines)` or `('prose', (marker, lines))` in order."""
    i = 0
    while i < len(lines):
        line = lines[i]
        if not line.strip():
            j = i + 1
            while j < len(lines) and not lines[j].strip():
                j += 1
            yield ("blank", lines[i:j])
            i = j
            continue
        item = LIST_ITEM.fullmatch(line)
        if fence := FENCE.match(line):  # a fenced code block, kept up to its closing fence
            close = re.compile(rf" {{0,3}}{re.escape(fence.group(1)[0])}{{{len(fence.group(1))},}}"
                               r"\s*$")
            j = next((k for k in range(i + 1, len(lines)) if close.match(lines[k])), len(lines))
            yield ("opaque", lines[i:j + 1])
            i = j + 1
            continue
        if end := (html_block_end(lines, i) or display_math_end(lines, i)
                   or table_end(lines, i)):
            yield ("opaque", lines[i:end])
            i = end
            continue
        if ((BLOCK_OPENER.match(line) and not item) or SETEXT.match(line)
                or REFERENCE_DEF.match(line) or line[:1].isspace()):
            yield ("opaque", [line])
            i += 1
            continue
        # A paragraph or top-level list item: this line and its continuation lines, up to a
        # blank line, another list item, a Setext underline or a line that opens another block.
        j = i + 1
        while (j < len(lines) and lines[j].strip() and not LIST_ITEM.fullmatch(lines[j])
               and not (not item and SETEXT.match(lines[j]))
               and html_block_end(lines, j, in_paragraph=True) is None
               and display_math_end(lines, j) is None
               and table_end(lines, j) is None
               and not BLOCK_OPENER.match(lines[j])):
            j += 1
        if not item and j < len(lines) and SETEXT.match(lines[j]):
            # A Setext heading (`Heading\n===` or `Heading\n---`): keep heading and underline.
            yield ("opaque", lines[i:j + 1])
            i = j + 1
            continue
        block = lines[i:j]
        marker = item.group("marker") if item else ""
        indent = " " * len(marker)
        # Kept as they are: a hard line break (which joining would remove), a Setext underline,
        # nested list or embedded block inside a list item, and indentation other than `indent`.
        if any(hard_break(part) for part in block[:-1]) or any(
                SETEXT.match(part.lstrip(" ")) or LIST_ITEM.fullmatch(part.lstrip(" "))
                or (item and part.startswith(indent)
                    and (BLOCK_OPENER.match(part[len(indent):])
                         or DISPLAY_MATH.match(part[len(indent):])
                         or is_table_delimiter(part[len(indent):])))
                or (part[:1].isspace() and (not item or not part.startswith(indent)
                                            or part[len(indent):][:1].isspace()))
                for part in block[1:]):
            yield ("opaque", block)
        else:
            yield ("prose", (marker, block))
        i = j


def blocks(text: str) -> list[tuple[str, ...]]:
    """`text`'s Markdown block structure, normalizing only soft wraps and list continuation
    indentation inside plain paragraphs and simple top-level list items."""
    if text and not text.endswith("\n"):
        text += "\n"
    out: list[tuple[str, ...]] = []
    for kind, payload in _iter_blocks(text.split("\n")[:-1]):
        if kind in ("blank", "opaque"):
            out.append((kind, *payload))
        else:
            marker, block = payload
            joined = " ".join(part.strip() for part in [block[0][len(marker):], *block[1:]])
            out.append(("prose", marker.strip(), *joined.split()))
    return out


def canonical(text: str) -> str:
    """`text` in the line format; see the module docstring."""
    if text and not text.endswith("\n"):
        text += "\n"
    out: list[str] = []
    for kind, payload in _iter_blocks(text.split("\n")[:-1]):
        if kind in ("blank", "opaque"):
            out.extend(payload)
        else:
            marker, block = payload
            indent = " " * len(marker)
            joined = " ".join(part.strip() for part in [block[0][len(marker):], *block[1:]])
            split = sentences(joined)
            out.append(marker + split[0])
            out.extend(indent + piece for piece in split[1:])
    result = "".join(f"{line}\n" for line in out)
    if words(result) != words(text) or blocks(result) != blocks(text):
        raise ValueError("the line format would change the text; this is a bug in sources_format")
    return result


def words(text: str) -> list[str]:
    """`text` without line structure: its whitespace-separated words, in order."""
    return text.split()


def compare(old: str, new: str) -> list[str]:
    """Differences between `old` and `new` other than sentence line breaks and list continuation
    indentation."""
    a_words, b_words = words(old), words(new)
    if a_words != b_words:
        k = next((i for i, (x, y) in enumerate(zip(a_words, b_words)) if x != y),
                 min(len(a_words), len(b_words)))
        return [f"word {k + 1} differs: {' '.join(a_words[max(0, k - 5):k + 5])!r} became "
                f"{' '.join(b_words[max(0, k - 5):k + 5])!r} "
                f"({len(a_words)} words before, {len(b_words)} after)"]
    a_blocks, b_blocks = blocks(old), blocks(new)
    if a_blocks == b_blocks:
        return []
    k = next((i for i, (x, y) in enumerate(zip(a_blocks, b_blocks)) if x != y),
             min(len(a_blocks), len(b_blocks)))
    before = " ".join(a_blocks[k][:8]) if k < len(a_blocks) else "<end>"
    after = " ".join(b_blocks[k][:8]) if k < len(b_blocks) else "<end>"
    return [f"block {k + 1} differs (paragraph break or Markdown block changed): "
            f"{before!r} became {after!r} ({len(a_blocks)} blocks before, {len(b_blocks)} after)"]


def unformatted(text: str) -> list[int]:
    """The 1-based numbers of the lines that `canonical` would change."""
    import difflib

    old, new = text.split("\n"), canonical(text).split("\n")
    changed: list[int] = []
    for tag, i1, i2, _, _ in difflib.SequenceMatcher(None, old, new, autojunk=False).get_opcodes():
        if tag != "equal":
            changed.extend(range(i1 + 1, max(i1, i2 - 1) + 2))
    return sorted(set(changed))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="report lines not in the format")
    mode.add_argument("--write", action="store_true", help="rewrite the file in the format")
    mode.add_argument("--compare", nargs=2, metavar=("OLD", "NEW"), type=Path,
                      help="check that NEW has the text of OLD apart from line breaks")
    parser.add_argument("file", nargs="?", type=Path, default=SOURCES)
    args = parser.parse_args(argv)
    if args.compare:
        old, new = (path.read_text(encoding="utf-8") for path in args.compare)
        differences = compare(old, new)
        for difference in differences:
            print(f"sources_format: {difference}")
        if not differences:
            print(f"sources_format: {args.compare[1]} has the text of {args.compare[0]} "
                  f"({len(words(old))} words) apart from line breaks and indentation")
        return 1 if differences else 0
    text = args.file.read_text(encoding="utf-8")
    if args.write:
        formatted = canonical(text)
        if formatted != text:
            args.file.write_text(formatted, encoding="utf-8")
        return 0
    lines = unformatted(text)
    if lines:
        shown = ", ".join(map(str, lines[:20])) + (", ..." if len(lines) > 20 else "")
        print(f"{args.file}: not one sentence per line at line {shown}; "
              f"run `python3 scripts/sources_format.py --write {args.file}`")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
