#!/usr/bin/env python3
"""Check current manual links, book chapter lists and Lean excerpt identity (stdlib only).

Relative `File.lean#L<n>` links must also start on a declaration, attribute, docstring or (for
ranges) section header, and an inline link whose text names a declaration of the linked file
(`[Ns.name](…#L<n>)`) must start on that declaration's header. Pass `--fix-anchors` to repoint
drifted `[Ns.name](File.lean#Ln)` links at the declaration's current header start line before
running the check. It also reports a list item directly after a paragraph line, which the PDF
build's Pandoc reader absorbs into that paragraph, and a locator (`Section 5.6`, `p. 12`,
`Theorem 4.17`) inside the label of a link into `sources.md`, which the PDF replaces by a citation
number. This does not fetch URLs, elaborate Lean, audit
mathematical meaning, check links whose text names no declaration of the linked file (prose, a
file, a module, a declaration that moved elsewhere), or assert that historical evidence describes
the current checkout. Run from any working directory.

The reference chapters listed in `FROZEN` are not kept current. A frozen page keeps the checks of
its own text (markup, lists, reference definitions, links that leave the repository), of its links
to other frozen pages, and of its place in the book and the link graph. Its links to Lean source
and to maintained pages are not checked, because edits elsewhere would break them, and
`--fix-anchors` does not rewrite it. Links from maintained pages into frozen ones are checked.
"""
from __future__ import annotations

import argparse
import html
import importlib.util
import json
import re
import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'manual/data'))
from build_latex import FROZEN, frozen
from visuals import check_markup

EXCLUDED = {"_build", "_generated", "__pycache__"}
FENCE = re.compile(r"^\s*(`{3,}|~{3,})(.*)$")

# A relative `File.lean#L<a>[-L<b>]` link must start where the cited Lean text starts (#3991):
# an unindented declaration (after optional modifiers), attribute or docstring outside any
# comment, so not a structure field's docstring. Ranges may also start at a section header;
# `#L1` links the whole file.
DECLARATION_START = re.compile(
    r"(?:@\[|/--|(?:(?:private|protected|public|noncomputable|partial|unsafe|nonrec|meta|scoped"
    r"|local)\s+)*(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|example)\b)")
SECTION_START = re.compile(r"(?:/-!|(?:(?:public|noncomputable)\s+)*(?:section|namespace)\b)")
STALE_SOURCE_ANCHOR = "source line anchor does not start a declaration"
# When the text of an inline link into a Lean file names a declaration of that file, the link
# must start on that declaration's header (docstring, attributes or the line naming it); a
# range must overlap it. Names match up to namespace qualification: `[Ns.name]` matches a
# declared `name` and vice versa. Text naming no declaration of the file (prose, a file or
# module, a declaration that moved to another file) is not checked.
MISNAMED_SOURCE_ANCHOR = "source line anchor does not start the declaration its link text names"
DECLARED_NAME = re.compile(
    r"(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|noncomputable|partial|unsafe|nonrec|meta"
    r"|scoped|local)\s+)*(?:class\s+(?:inductive|abbrev)|theorem|lemma|def|abbrev|structure|class"
    r"|inductive|opaque|instance(?:\s+\(priority\s*:=[^)]*\))?)\s+([^\s:({\[]+)")
CODE_SPAN = re.compile(r"(`+).*?\1")
# Anchors, as (Lean file, start line), that are stale or that queued pull requests will make
# stale; the check tolerates them until they can be repointed without conflicting with or
# ejecting those pull requests. Repoint the manual link and delete the entry (#3991). An entry
# that no longer matches is listed in the result, not reported as an error, so a pull request
# that repoints a link does not have to edit this list.
STALE_SOURCE_ANCHORS: set[tuple[str, int]] = set()


def fenced_lines(text: str):
    """Yield `(line number, line, fenced)`, where `fenced` marks fences and their contents."""
    fence = None
    for number, line in enumerate(text.splitlines(), 1):
        match = FENCE.match(line)
        if fence is not None:
            if match and match[1][0] == fence[0] and len(match[1]) >= len(fence):
                fence = None
            yield number, line, True
            continue
        if match:
            fence = match[1]
        yield number, line, fence is not None


def prose(text: str) -> str:
    """Ignore fenced and inline code when scanning Markdown links/headings."""
    return "\n".join(re.sub(r"(`+).*?\1", "", line)
                     for _, line, fenced in fenced_lines(text) if not fenced)


# Pandoc, which builds the PDFs, reads a list item directly after a paragraph line (including a
# quotation, inline HTML or `#…` line) as more of that paragraph, while GitHub starts a list there.
# Items of an open list need no blank line, including nested items and items after an indented
# fence in an earlier item; nor does a list after a heading, table row, HTML block or comment,
# thematic break or reference definition. Lists inside block quotes are not checked.
LIST_ITEM = re.compile(r" {0,3}(?:[-+*]|[0-9]{1,9}[.)])(?:[ \t]|$)")
HEADING = re.compile(r"\s*#{1,6}(?:[ \t]|$)")
BLOCK_LINE = re.compile(
    r"\s*(?:\||=+\s*$|<!--|</?(?:address|article|aside|blockquote|details|div|dl|figure|footer"
    r"|form|h[1-6]|header|hr|ol|p|pre|section|summary|table|ul)\b)|(?: {0,3}[-*_][ \t]*){3,}$",
    re.I)
REFERENCE = re.compile(r" {0,3}\[[^\]]+\]:\s")
LIST_AFTER_PARAGRAPH = ("list item directly after a paragraph line (add a blank line before the "
                        "list, or rewrap a line that only looks like an item)")

# The PDF build prints a link into `sources.md#key` as a numbered citation and drops its label
# (`manual/data/build_latex.py`), so `[Boneh and Shoup, Section 5.6][bs23]` prints as `[67]` and
# the locator is lost. A label must not carry a section, chapter, page, statement, figure, table,
# equation, part or step number, spelled out or abbreviated and in either case, nor a bare dotted
# number (`CLRS 15.5`, also a version such as `TLS 1.3`, which `v1.3` avoids); write the locator
# after the link. A year, or a title word after a keyword (`Algorithm Design`), is not a locator.
CITATION_LOCATOR = re.compile(
    r"§|\b(?:pp?\.|[Pp]ages?)\s*\d|(?<![\w.])\d+\.\d+|\b(?i:Sections?|Subsections?|Sec\.|Sect\."
    r"|Chapters?|Ch\.|Chap\.|Parts?|Volumes?|Vol\.|Lectures?|Appendix|Theorems?|Thm\.|Lemmas?"
    r"|Lem\.|Definitions?|Def\.|Corollar(?:y|ies)|Cor\.|Propositions?|Prop\.|Remarks?|Claims?"
    r"|Facts?|Examples?|Exercises?|Problems?|Algorithms?|Protocols?|Constructions?|Games?|Steps?"
    r"|Figures?|Fig\.|Tables?|Equations?|Eqs?\.)\s*\(?(?:[0-9]|[IVXLC]+\b|[A-Z]\b)")
LABEL_LOCATOR = ("locator inside a citation link label, which the PDF drops (write it after the "
                 "link: `[Author][key], Section 5.6`)")
# A label may wrap over a line break, but not over a blank line.
WRAPPED_LABEL = r"\[((?:[^\[\]\n]|\n(?![ \t]*\n))+)\]"
WRAPPED_INLINE_LINK = re.compile(WRAPPED_LABEL + r"\(\s*(?:<([^>\n]+)>|([^\s)]+))")
REFERENCE_LINK = re.compile(WRAPPED_LABEL + r"\[([^\]\n]*)\]")


def _mask_non_prose(text: str) -> str:
    """Replace fenced blocks and inline code spans with spaces, preserving offsets and newlines."""
    out: list[str] = []
    fence = None
    for line in text.splitlines(keepends=True):
        body = line.rstrip("\r\n")
        ending = line[len(body):]
        match = FENCE.match(body)
        if fence is not None:
            if match and match[1][0] == fence[0] and len(match[1]) >= len(fence):
                fence = None
            out.append(" " * len(body) + ending)
        elif match:
            fence = match[1]
            out.append(" " * len(body) + ending)
        else:
            out.append(CODE_SPAN.sub(lambda span: " " * len(span[0]), body) + ending)
    return "".join(out)


def labelled_links(text: str) -> list[tuple[int, str, str]]:
    """`(line number, label, URL)` of each inline and full or collapsed reference link outside
    code, with the label's whitespace collapsed; a wrapped label reports its first line. Code
    spans are blanked, so code showing a locator is not reported."""
    definitions = {key.casefold(): url for key, url in re.findall(
        r"^\s{0,3}\[([^\]]+)\]:\s*<?([^\s>]+)>?", prose(text), re.M)}
    masked = _mask_non_prose(text)
    found = []
    for link in WRAPPED_INLINE_LINK.finditer(masked):
        found.append((link.start(), " ".join(link[1].split()), link[2] or link[3]))
    for link in REFERENCE_LINK.finditer(masked):
        label = " ".join(link[1].split())
        url = definitions.get((link[2] or label).casefold())
        if url is not None:
            found.append((link.start(), label, url))
    return [(masked.count("\n", 0, start) + 1, label, url) for start, label, url in sorted(found)]


def lists_after_paragraphs(text: str) -> list[int]:
    """Line numbers of list items that pandoc would read as part of the paragraph above them."""
    found, paragraph, in_list, after_blank = [], False, False, True
    for number, line, fenced in fenced_lines(text):
        indented = line[:1].isspace()
        if not line.strip():
            paragraph, after_blank = False, True
            continue
        if fenced:
            # A fence and its contents stay inside an open list only when indented under its item.
            paragraph, after_blank, in_list = False, False, in_list and indented
            continue
        if LIST_ITEM.match(line):
            if paragraph and not in_list:
                found.append(number)
            paragraph, in_list = False, True
        elif BLOCK_LINE.match(line) or HEADING.match(line) and not paragraph:
            paragraph, in_list = False, in_list and indented
        elif paragraph or not REFERENCE.match(line):
            in_list = in_list and not (after_blank and not indented)
            paragraph = True
        after_blank = False
    return found


def anchors(text: str) -> set[str]:
    # GitHub-style heading IDs, including repeated headings and explicit HTML IDs.
    active = prose(text)
    found = set(re.findall(r'<a\s+(?:[^>]*?\s)?id=["\']([^"\']+)', active))
    counts: dict[str, int] = {}
    for heading in re.findall(r"^\s{0,3}#{1,6}\s+(.+?)\s*#*\s*$", active, re.M):
        heading = re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", heading)
        heading = re.sub(r"<[^>]+>", "", html.unescape(heading)).lower()
        slug = re.sub(r"[^\w\-\s]", "", heading).replace(" ", "-")
        number = counts.get(slug, 0)
        counts[slug] = number + 1
        found.add(slug if number == 0 else f"{slug}-{number}")
    return found


def links(text: str) -> tuple[list[str], list[str]]:
    active = prose(text)
    definitions = {k.casefold(): v for k, v in re.findall(
        r"^\s{0,3}\[([^\]]+)\]:\s*<?([^\s>]+)>?", active, re.M)}
    targets = re.findall(r"\]\(\s*(?:<([^>]+)>|([^\s)]+))", active)
    urls = [a or b for a, b in targets] + list(definitions.values())
    missing = []
    for display, key in re.findall(r"\[([^\]\n]+)\]\[([^\]\n]*)\]", active):
        key = (key or display).casefold()
        if key not in definitions:
            missing.append(key)
        else:
            urls.append(definitions[key])
    return urls, missing


def within(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
        return True
    except ValueError:
        return False


def comment_depths(lines: list[str]) -> list[int]:
    """Nesting depth of Lean block comments (`/- … -/`, docstrings included) at each line start.

    Line comments and string literals are skipped so that `--`, `"/-"` or `"-/"` do not count.
    """
    depths, depth = [], 0
    for line in lines:
        depths.append(depth)
        i, in_string = 0, False
        while i < len(line):
            pair = line[i:i + 2]
            if depth:
                depth += (pair == "/-") - (pair == "-/")
                i += 2 if pair in ("/-", "-/") else 1
            elif in_string:
                in_string = line[i] != '"'
                i += 2 if line[i] == "\\" else 1
            elif pair == "--":
                break
            elif pair == "/-":
                depth, i = 1, i + 2
            elif line[i:i + 3] == "'\"'":
                i += 3
            else:
                in_string = line[i] == '"'
                i += 1
    return depths


def source_anchor_error(fragment: str, lines: list[str]) -> str | None:
    """Problem with a `L<a>[-L<b>]` fragment into a Lean file with these lines, or `None`."""
    bounds = [int(n) for n in re.findall(r"\d+", fragment)]
    if min(bounds) < 1 or max(bounds) > len(lines):
        return "source line anchor out of bounds"
    start = bounds[0]
    if start == 1:
        return None
    line = lines[start - 1]
    if comment_depths(lines[:start])[-1] == 0 and (
            DECLARATION_START.match(line) or len(bounds) > 1 and SECTION_START.match(line)):
        return None
    return STALE_SOURCE_ANCHOR


def declarations(lines: list[str]) -> dict[str, list[tuple[int, int]]]:
    """Header lines `(first, last)`, 1-based, of each named unindented declaration by name.

    A header runs from the declaration's docstring opener or first attribute to the line naming
    it, across line comments and `… in` lines; anonymous declarations (`example`, unnamed
    `instance`) and commented-out code are absent.
    """
    found: dict[str, list[tuple[int, int]]] = {}
    lead = None
    for number, (line, depth) in enumerate(zip(lines, comment_depths(lines)), 1):
        if depth:
            continue
        if match := DECLARED_NAME.match(line):
            found.setdefault(match[1].rstrip("."), []).append((lead or number, number))
            lead = None
        elif line.startswith(("/--", "@[")):
            lead = lead or number
        elif line[:1].strip() and not line.startswith("--") and not line.rstrip().endswith(" in"):
            lead = None
    return found


def _iter_inline_links(text: str):
    """Yield `(display, url, url_start, url_end)` for non-code inline links (including wrapped)."""
    masked = _mask_non_prose(text)
    for link in WRAPPED_INLINE_LINK.finditer(masked):
        url_group = 2 if link[2] is not None else 3
        display = " ".join(text[link.start(1):link.end(1)].split())
        yield display, link[url_group], link.start(url_group), link.end(url_group)


def link_texts(text: str) -> list[tuple[str, str]]:
    """`(display text, URL)` of each inline Markdown link, found as `links()` finds them.

    Fenced code and code spans are skipped, so code showing a link is not a link, while a
    code-formatted label (`` [`name`](…) ``) keeps its text. An optional `<…>` around the URL is
    dropped.
    """
    return [(display, url) for display, url, _, _ in _iter_inline_links(text)]


def names_declaration(text: str, name: str) -> bool:
    """Whether link text and a declared name agree up to namespace qualification."""
    name = name.removeprefix("_root_.")
    return text == name or text.endswith("." + name) or name.endswith("." + text)


def named_headers(display: str, module: str,
                  found: dict[str, list[tuple[int, int]]]) -> list[tuple[int, int]]:
    """Header spans `(first, last)` in `found` matching link `display`, or `[]`."""
    text = display.strip().strip("`").removeprefix("_root_.")
    if text.endswith((".lean", ".md")):
        return []
    # An exact name match takes precedence, so `[toX]` and `[Complete.toX]` stay distinct when
    # the file declares both, and `[Foo](…/Foo.lean#L…)` is checked when `Foo.lean` declares
    # `Foo`. Otherwise text naming the linked module is not checked, and qualified matches keep
    # only the declared names sharing the most trailing components with the text, so
    # `[Corr.Valid.add]` needs `Valid.add`, not a bare `add`.
    headers = found.get(text)
    if not headers:
        if module == text or module.endswith("." + text):
            return []
        shared = {name: min(text.count("."), name.removeprefix("_root_.").count("."))
                  for name in found if names_declaration(text, name)}
        headers = [header for name, spans in found.items()
                   if name in shared and shared[name] == max(shared.values()) for header in spans]
    return headers or []


def misnamed_anchor(display: str, module: str, fragment: str,
                    found: dict[str, list[tuple[int, int]]]) -> list[int] | None:
    """Header starts of the declaration the link text names, if the `L<a>[-L<b>]` fragment
    misses all of them; `None` when the anchor is right or the text names no declaration."""
    headers = named_headers(display, module, found)
    bounds = [int(n) for n in re.findall(r"\d+", fragment)]
    # Line 1 links the whole file.
    if not headers or bounds[0] == 1 or any(
            first <= bounds[-1] and bounds[0] <= last for first, last in headers):
        return None
    return sorted(first for first, _ in headers)


def load_book_builder(data: Path):
    """Import `data/build_manual.py` with its own sibling modules, leaving `sys.modules` as found."""
    siblings = {path.stem for path in data.glob("*.py")}
    saved = {name: sys.modules.pop(name) for name in siblings if name in sys.modules}
    sys.path.insert(0, str(data))
    try:
        spec = importlib.util.spec_from_file_location("checked_build_manual", data / "build_manual.py")
        book = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(book)
        return book
    finally:
        sys.path.remove(str(data))
        for name in siblings:
            sys.modules.pop(name, None)
        sys.modules.update(saved)


def book_input_errors(repo: Path, manual: Path) -> list[str]:
    """Run the PDF builder's chapter-list check, which otherwise fails only in the Pandoc build."""
    data = manual / "data"
    book = load_book_builder(data)
    try:
        book.validate_inputs(manual, book.FILES)
    except ValueError as error:
        place = data.relative_to(repo).as_posix() if within(data, repo) else str(data)
        return [f"{error}. The book's chapter lists are ORDER in {place}/build_latex.py (reference "
                f"and history chapters) and WORKFLOWS or APPENDICES in {place}/build_manual.py: "
                "add each 'missing' page there and remove 'extra' or duplicate entries."]
    return []


def check(repo: Path, manual: Path | None = None) -> dict:
    repo = repo.resolve()
    manual = (manual or repo / "manual").resolve()
    errors: list[str] = []
    documents = sorted(p for p in manual.rglob("*.md")
                       if not EXCLUDED.intersection(p.relative_to(manual).parts))
    document_set = set(documents)
    edges = {p: set() for p in documents}
    link_count = 0
    allowed_stale: set[tuple[str, int]] = set()
    sources: dict[Path, dict[str, list[tuple[int, int]]]] = {}
    unnamed: set[tuple[Path, str]] = set()
    visual_counts = {'diagrams': 0, 'worked_examples': 0}

    def is_frozen(path: Path) -> bool:
        return within(path, manual) and frozen(path.relative_to(manual).as_posix())

    for doc in documents:
        doc_frozen = is_frozen(doc)
        try:
            for key, value in check_markup(doc.read_text()).items():
                visual_counts[key] += value
        except ValueError as error:
            errors.append(f'{doc.relative_to(manual)}: {error}')
        errors.extend(f"{doc.relative_to(manual)}: Line {number}: {LIST_AFTER_PARAGRAPH}"
                      for number in lists_after_paragraphs(doc.read_text()))
        urls, undefined = links(doc.read_text())
        errors.extend(f"{doc.relative_to(manual)}: undefined reference [{key}]" for key in undefined)
        for number, label, url in labelled_links(doc.read_text()):
            parsed = urlsplit(html.unescape(url))
            locator = CITATION_LOCATOR.search(label)
            if parsed.scheme or parsed.netloc or not parsed.fragment or not locator:
                continue
            target = (doc.parent / unquote(parsed.path)).resolve() if parsed.path else doc
            if target == manual / "sources.md":
                errors.append(f"{doc.relative_to(manual)}: Line {number}: {LABEL_LOCATOR}: "
                              f"[{label}] (`{locator[0]}`)")
        for url in urls:
            parsed = urlsplit(html.unescape(url))
            if parsed.scheme or parsed.netloc:
                continue
            link_count += 1
            target = (doc.parent / unquote(parsed.path)).resolve() if parsed.path else doc
            if not within(target, repo):
                errors.append(f"{doc.relative_to(manual)}: local link escapes repository: {url}")
                continue
            # Only another frozen page is a target that a frozen page can rely on.
            unchecked = doc_frozen and not is_frozen(target)
            if not target.exists():
                if not unchecked:
                    errors.append(f"{doc.relative_to(manual)}: missing local link: {url}")
                continue
            if target in document_set:
                edges[doc].add(target)
            fragment = unquote(parsed.fragment)
            if unchecked:
                continue
            if fragment and target.suffix == ".md" and fragment not in anchors(target.read_text()):
                errors.append(f"{doc.relative_to(manual)}: missing Markdown anchor: {url}")
            elif fragment and target.suffix == ".lean" and re.fullmatch(r"L\d+(?:-L\d+)?", fragment):
                problem = source_anchor_error(fragment, target.read_text().splitlines())
                known = (target.relative_to(repo).as_posix(), int(re.match(r"L(\d+)", fragment)[1]))
                if problem == STALE_SOURCE_ANCHOR and known in STALE_SOURCE_ANCHORS:
                    allowed_stale.add(known)
                elif problem:
                    errors.append(f"{doc.relative_to(manual)}: {problem}: {url}")
                if problem:
                    unnamed.add((target, fragment))
        # Name check, for anchors that start some declaration. A `STALE_SOURCE_ANCHORS` entry
        # also tolerates an anchor that fails only this check.
        for display, url in () if doc_frozen else link_texts(doc.read_text()):
            parsed = urlsplit(html.unescape(url))
            fragment = unquote(parsed.fragment)
            if parsed.scheme or parsed.netloc or not parsed.path.endswith(".lean") or \
                    not re.fullmatch(r"L\d+(?:-L\d+)?", fragment):
                continue
            target = (doc.parent / unquote(parsed.path)).resolve()
            if (target, fragment) in unnamed or not within(target, repo) or not target.is_file():
                continue
            if target not in sources:
                sources[target] = declarations(target.read_text().splitlines())
            module = target.relative_to(repo).with_suffix("").as_posix().replace("/", ".")
            starts = misnamed_anchor(display, module, fragment, sources[target])
            known = (target.relative_to(repo).as_posix(), int(re.match(r"L(\d+)", fragment)[1]))
            if starts is not None and known in STALE_SOURCE_ANCHORS:
                allowed_stale.add(known)
            elif starts is not None:
                errors.append(f"{doc.relative_to(manual)}: {MISNAMED_SOURCE_ANCHOR} (declared at "
                              f"{', '.join(f'L{n}' for n in starts)}): {url}")
    start = manual / "README.md"
    if start not in document_set:
        errors.append("Missing manual/README.md entry page")
    if manual / "AGENT_OPERATORS.md" not in document_set:
        errors.append("Missing manual/AGENT_OPERATORS.md human driver manual")
    # Manuals without the builder (test fixtures) skip the chapter-list check; the builder's
    # check also requires AGENT_OPERATORS.md, which is reported above when absent.
    book_checked = ((manual / "data/build_manual.py").is_file()
                    and manual / "AGENT_OPERATORS.md" in document_set)
    if book_checked:
        errors.extend(book_input_errors(repo, manual))
    pending, reachable = [start], set()
    while pending:
        path = pending.pop()
        if path in reachable:
            continue
        reachable.add(path)
        pending.extend(edges.get(path, set()) - reachable)
    errors.extend(f"Unreachable manual page: {p.relative_to(manual)}"
                  for p in sorted(document_set - reachable))

    rows = []
    for manifest in sorted((manual / "workflows/data").glob("*-excerpts.json")):
        try:
            data = json.loads(manifest.read_text())
            if not isinstance(data, list):
                raise ValueError("expected a list")
            rows.extend(data)
        except (ValueError, OSError) as exc:
            errors.append(f"{manifest.relative_to(manual)}: {exc}")
    ids, observed, excerpt_results = set(), {}, []
    for doc in (manual / "workflows").glob("*.md"):
        text = doc.read_text()
        blocks = re.findall(r"<!-- excerpt: ([\w-]+) -->\s*```lean\n(.*?)\n```", text, re.S)
        lean_blocks = re.findall(r"^```lean\s*\n", text, re.M)
        if len(blocks) != len(lean_blocks):
            errors.append(f"{doc.relative_to(manual)}: unregistered Lean block")
        for key, body in blocks:
            if key in observed:
                errors.append(f"Duplicate excerpt marker: {key}")
            observed[key] = (doc, body)
    for row in rows:
        if not isinstance(row, dict) or not all(isinstance(row.get(k), str)
                                               for k in ("id", "document", "source_path")):
            errors.append("Invalid excerpt manifest row: expected id, document and source_path")
            continue
        key = row["id"]
        if key in ids:
            errors.append(f"Duplicate excerpt manifest ID: {key}")
        ids.add(key)
        doc = (manual / row["document"]).resolve()
        source = (repo / row["source_path"]).resolve()
        if not within(doc, manual) or not within(source, repo):
            errors.append(f"{key}: excerpt path escapes its root")
            continue
        if key not in observed or observed[key][0] != doc:
            errors.append(f"{key}: missing marker in {row['document']}")
            continue
        if not source.is_file():
            errors.append(f"{key}: missing source file {row['source_path']}")
            continue
        body = observed[key][1]
        excerpt_lines, source_lines = body.splitlines(), source.read_text().splitlines()
        positions = [i for i in range(len(source_lines) - len(excerpt_lines) + 1)
                     if source_lines[i:i + len(excerpt_lines)] == excerpt_lines]
        if len(positions) != 1:
            errors.append(f"{key}: expected one exact source match, found {len(positions)} in {row['source_path']}")
            continue
        doc_urls, _ = links(doc.read_text())
        linked = any(not urlsplit(url).scheme and
                     (doc.parent / unquote(urlsplit(url).path)).resolve() == source
                     for url in doc_urls)
        if not linked:
            errors.append(f"{key}: document must link the complete source client")
        excerpt_results.append({"id": key, "source_path": row["source_path"],
                                "start_line": positions[0] + 1,
                                "end_line": positions[0] + len(excerpt_lines)})
    errors.extend(f"Excerpt marker absent from manifests: {key}" for key in sorted(set(observed) - ids))
    if not rows:
        errors.append("No contextual Lean excerpts registered")
    return {"status": "fail" if errors else "pass", "manual_documents": len(documents),
            "frozen_documents": sum(map(is_frozen, documents)),
            "local_links_checked": link_count, "excerpts_checked": len(excerpt_results),
            "book_inputs_checked": book_checked, **visual_counts,
            "allowed_stale_source_anchors": sorted(f"{path}#L{line}" for path, line in allowed_stale),
            "unused_stale_source_anchor_entries": sorted(
                f"{path}#L{line}" for path, line in STALE_SOURCE_ANCHORS - allowed_stale),
            "excerpts": excerpt_results, "errors": errors, "lean_compilation": False,
            "external_links_fetched": False, "historical_revision_checked": False}


def fix_anchors(repo: Path, manual: Path | None = None) -> list[dict[str, str]]:
    """Repoint drifted `[Ns.name](File.lean#Ln)` links to the declaration's current header start
    line when uniquely identified.

    Leaves valid anchors, whole-file (`#L1`) and range (`#La-Lb`) links, allowlisted
    `STALE_SOURCE_ANCHORS`, links whose text names no declaration, ambiguous multiple-match
    declarations and every `FROZEN` page unchanged.
    """
    repo = repo.resolve()
    manual = (manual or repo / "manual").resolve()
    documents = sorted(p for p in manual.rglob("*.md")
                       if not EXCLUDED.intersection(p.relative_to(manual).parts)
                       and not frozen(p.relative_to(manual).as_posix()))
    file_lines: dict[Path, list[str]] = {}
    sources: dict[Path, dict[str, list[tuple[int, int]]]] = {}
    fixed: list[dict[str, str]] = []
    for doc in documents:
        original = doc.read_text()
        edits: list[tuple[int, int, str]] = []
        for display, url, url_start, url_end in _iter_inline_links(original):
            parsed = urlsplit(html.unescape(url))
            fragment = unquote(parsed.fragment)
            if parsed.scheme or parsed.netloc or not parsed.path.endswith(".lean") or \
                    not re.fullmatch(r"L\d+", fragment):
                continue
            start = int(fragment[1:])
            if start == 1:
                continue
            target = (doc.parent / unquote(parsed.path)).resolve()
            if not within(target, repo) or not target.is_file():
                continue
            rel_target = target.relative_to(repo).as_posix()
            if (rel_target, start) in STALE_SOURCE_ANCHORS or "#" not in url:
                continue
            prefix, raw_frag = url.rsplit("#", 1)
            if raw_frag != fragment:
                continue
            if target not in file_lines:
                target_lines = target.read_text().splitlines()
                file_lines[target] = target_lines
                sources[target] = declarations(target_lines)
            target_lines = file_lines[target]
            found = sources[target]
            module = target.relative_to(repo).with_suffix("").as_posix().replace("/", ".")
            if source_anchor_error(fragment, target_lines) is None and \
                    misnamed_anchor(display, module, fragment, found) is None:
                continue
            headers = named_headers(display, module, found)
            if len(headers) != 1:
                continue
            new_frag = f"L{headers[0][0]}"
            if new_frag == fragment:
                continue
            edits.append((url_start, url_end, f"{prefix}#{new_frag}"))
            fixed.append({
                "document": doc.relative_to(manual).as_posix(),
                "display": display,
                "target": rel_target,
                "old": fragment,
                "new": new_frag,
            })
        if edits:
            updated = original
            for start_idx, end_idx, new_url in reversed(edits):
                updated = updated[:start_idx] + new_url + updated[end_idx:]
            doc.write_text(updated)
    return fixed


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=ROOT)
    parser.add_argument("--manual", type=Path, help="Manual root (default: REPO/manual)")
    parser.add_argument("--output", type=Path, help="Optional JSON result path")
    parser.add_argument("--fix-anchors", action="store_true",
                        help="Repoint drifted `[Ns.name](File.lean#Ln)` links to current headers")
    args = parser.parse_args(argv)
    fixes = fix_anchors(args.repo, args.manual) if args.fix_anchors else None
    result = check(args.repo, args.manual)
    if fixes is not None:
        result["fixed_anchors"] = fixes
    encoded = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")
    return int(bool(result["errors"]))


if __name__ == "__main__":
    raise SystemExit(main())
