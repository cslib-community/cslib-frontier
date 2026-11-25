#!/usr/bin/env python3
"""The order in which `lake exe mk_all` writes the imports of an aggregate.

`scripts/MkAll.lean` orders an aggregate's import lines by `import_hash` of the module name,
breaking ties by name, instead of alphabetically. Alphabetical order puts the modules of one
directory next to each other, so two pull requests that add modules to the same directory insert
lines into the same gap, and GitHub's text merge (which ignores the local `leanagg` driver)
reports a conflict. Hash order scatters those lines over the whole file (#8486). The Python tools
that derive or merge aggregates order them with `import_key`.
"""

from __future__ import annotations

MASK = (1 << 64) - 1


def import_hash(module: str) -> int:
    """The 64-bit FNV-1a hash of the UTF-8 bytes of `module`, followed by MurmurHash3's `fmix64`
    finalizer. FNV-1a alone leaves names that differ only in their last characters (`Part1`,
    `Part2`) close together; the finalizer spreads them over the whole range."""
    value = 0xCBF29CE484222325
    for byte in module.encode():
        value = ((value ^ byte) * 0x100000001B3) & MASK
    value ^= value >> 33
    value = (value * 0xFF51AFD7ED558CCD) & MASK
    value ^= value >> 33
    value = (value * 0xC4CEB9FE1A85EC53) & MASK
    return value ^ (value >> 33)


def import_key(module: str) -> tuple[int, str]:
    """The sort key of `module`'s import line: its hash, then its name."""
    return import_hash(module), module
