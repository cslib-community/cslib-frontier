# Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Samuel Schlesinger
"""The source-pinned textbook audits under `results/`: one row per audited numbered result."""

from __future__ import annotations

import dataclasses
import re
from pathlib import Path

BOOKS = [
    ("arora-barak", "results/arora-barak-2007.md", "Arora–Barak (2007 draft)"),
    ("goldreich", "results/goldreich-2007.md", "Goldreich (2007 draft)"),
]
# Disposition classes, best first.
CLASSES = ["Covered", "Covered, source corrected", "Partial", "Source issue", "Not located",
           "Other"]
_ROW = re.compile(r"^\|\s*((\d+)\.[^|,]*?)\s*(?:,\s*([^|]*?))?\s*\|[^|]*\|\s*\*\*([^*]+)\*\*(.*)$")
_CODE = re.compile(r"`([A-Za-z_][\w.'₀-₉]*)`")


@dataclasses.dataclass(frozen=True)
class Row:
    book: str
    id: str  # "4.11" or "3.2(1)"
    chapter: int
    title: str
    cls: str
    status: str  # the bold disposition, verbatim
    line: int  # 1-based line in the audit file
    theorems: tuple[str, ...]  # identifiers quoted in the row that look like declarations


def classify(status: str) -> str:
    st = status.strip().rstrip(".").lower()
    if "covered" in st and "source issue" in st:
        return "Covered, source corrected"
    if st.startswith("covered"):
        return "Covered"
    if st.startswith("partial"):
        return "Partial"
    if "not located" in st:
        return "Not located"
    if st.startswith("source issue"):
        return "Source issue"
    return "Other"


def parse(text: str, book: str = "") -> list[Row]:
    """Every audited result; a result recorded twice keeps its last row."""
    rows: dict[str, Row] = {}
    for n, line in enumerate(text.splitlines(), 1):
        m = _ROW.match(line)
        if not m:
            continue
        rid, ch, title, status, rest = m.groups()
        names = tuple(dict.fromkeys(x for x in _CODE.findall(rest)
                                    if "." in x or "_" in x))
        rows[rid.strip()] = Row(book, rid.strip(), int(ch), (title or "").strip(), classify(status),
                                status.strip().rstrip("."), n, names)
    return list(rows.values())


def load(repo: Path) -> dict[str, list[Row]]:
    return {key: parse((repo / path).read_text(), key) for key, path, _ in BOOKS}
