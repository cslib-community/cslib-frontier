# Complexity Zoo coverage audit

The first pass records **119 matches in cslib-frontier** and **5 matches in its pinned
dependencies** at [main revision `c74b96b52f`](https://github.com/cslib-community/cslib-frontier/tree/c74b96b52fbba69d47652ae4a791d9527cc293f4).
These are verified lower bounds. The 469 unassessed headings remain to be checked.
The [requested batch](requested.csv) adds **95 distinct matched entries in submitted PRs**
beyond the pinned main snapshot. This gives a lower bound of **214 entries defined
in cslib-frontier on main or in those PRs**, with five further matches in dependencies.
The request itself names 114 entries, including aliases. Of these, 111 have definitions,
CLOG needs the continuous-time model, and two names need a definition convention.
See [#6641](https://github.com/cslib-community/cslib-frontier/issues/6641).

The [Zoo homepage](https://complexityzoo.net/index.php?oldid=20341) advertises **553
classes**. Its All Classes index has 585 links to 583 distinct anchors. The link
labelled IOP points to IP, and UCFL points to UCC. Counting the distinct red-labelled
headings on the letter and Symbols pages gives **614 heading records**, including
31 outside the index destinations and both correct headings. These totals describe
different parts of the site. The headings include aliases, families, operators, and
other entries that need classification before they can be counted as distinct classes.

[Source revisions](revisions.csv) pins each page in the snapshot. [Entries](entries.csv)
records one row per source anchor, its number of index links, and the Lean declaration
or expression and module where one has been identified. A fixed level of a generic
definition counts when the bounds and other conventions match. A pure alias points
to the canonical entry and shares its count. Alternate mathematical presentations
are included when the cited equivalence applies to the documented model.

| Status | Rows | Meaning |
| --- | ---: | --- |
| `main` | 119 | Matched to a declaration or specialization on the pinned main revision |
| `dependency` | 5 | Matched to a declaration in a pinned dependency |
| `alias` | 8 | Explicit alternate name or redirect identified so far |
| `related` | 9 | Candidate with a model or convention mismatch, or unverified correspondence |
| `gap` | 2 | Missing prerequisite identified |
| `logical` | 2 | Universal or empty class expressed directly as a set |
| `unassessed` | 469 | Pending semantic audit |

The remaining work is tracked in
[#6741](https://github.com/cslib-community/cslib-frontier/issues/6741).
