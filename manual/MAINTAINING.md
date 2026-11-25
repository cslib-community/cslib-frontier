# Maintain the manuals

The Operator's Manual serves humans and agents working in the codebase. Its acceptance goal
is operational: a Lean-literate human can select the intended
model, find and apply its API, diagnose a failed proof, validate a change and prepare a
reviewable contribution using the checked-out source and ordinary development tools.
Readability and complete context are part of that goal. A list of declaration names alone
is not an operating procedure.

The [Agent Operator's Manual](AGENT_OPERATORS.md) serves the human directing agents. Its
acceptance goal is that the human can assign a clear task, obtain trustworthy review, recognize
when to intervene and preserve a useful handoff. It links to codebase procedures in the
Operator's Manual rather than repeating them.

## What is maintained

The [repository policy](../CONTRIBUTING.md#maintaining-the-manuals) sorts the pages into three
groups.

- Registries are kept current: the
  [assumptions inventory](programs-crypto-and-probability/assumptions.md), the
  [bibliography](sources.md) and the [results inventory](../results/README.md). A change to a
  fact one of them records updates it in the same PR.
- Procedure pages are updated only when a procedure or role changes: the
  [workflows](workflows/index.md), [README.md](README.md), [BUILD.md](BUILD.md),
  [COMMANDS.md](COMMANDS.md), this page and the [Agent Operator's Manual](AGENT_OPERATORS.md).
- The reference chapters are frozen: the [reference index](index.md), the
  [model map](model-map.md) and the other pages of the five chapter directories. PRs do not
  update or review them. The Lean source, its docstrings and the API documentation are
  authoritative.

A change to a theorem, model, encoding or API explains itself in its docstrings and PR
description. The rest of this page applies to procedure pages and registries.

Keep one source of truth. Explain the task here; link to current [policy](../AGENTS.md),
[cache documentation](../scripts/cache/README.md), [guide](../guide/CslibFrontierGuide.lean),
module docstrings and complete tests for their details. Do not copy a new body of Lean code
into this manual without a checked source client. The workflow snippets are contextual
excerpts, each declared in `workflows/data/*-excerpts.json`. They retain source authorship
and require the linked client's imports, namespace and local assumptions.

A new page also needs a place in the book. Add a workflow or appendix page to `WORKFLOWS` or
`APPENDICES` in [build_manual.py](data/build_manual.py), and link it from an existing page. A
page deliberately kept out of the book belongs in `NON_CHAPTER_DOCUMENTS` in `build_manual.py`.
The reference and history chapters are listed in `ORDER` in [build_latex.py](data/build_latex.py),
and the frozen pages in `FROZEN` beside it. Chapter order is an editorial choice, so the lists
are maintained by hand; the checker reports any page missing from them.

Worked-example panels should make the goal, context, result and recovery easy to find while
preserving the canonical excerpt. Review the meaning of every changed arrow and resource label
of a diagram against the referenced definitions. Follow the
[source conventions](BUILD.md#maintain-diagrams-and-worked-examples); generated graphics stay
with the untracked book products.

## Check the affected reader path

1. Read the changed instructions using only the repository and its declared tools. Check
   that the entry page leads to the task, prerequisites, command, expected result and next step.
2. Open the complete client. Verify that the model, encoding, hypotheses and resource claim
   agree with the explanation; inspect a meaningful edge or failure case.
3. Run `python3 scripts/check_operator_manual.py` and `python3 scripts/test_operator_manual.py`.
   The checker validates local paths and Markdown anchors, source line anchors (each starts a
   declaration and, when its link text names a declaration of the linked file, that one), visual
   markup, lists that would print as running text (a list item directly after a paragraph line),
   locators inside citation link labels (which the PDF drops), that `sources.md` has one
   sentence per line (`python3 scripts/sources_format.py --write`),
   the book's chapter lists, excerpt registration and unique exact excerpt matches in
   current source; its controls exercise failure and recovery. In a frozen page it checks the
   page's own markup and its links to other frozen pages, but not its links to Lean source or
   to maintained pages, and `--fix-anchors` leaves frozen pages alone. Links from maintained
   pages into frozen ones are checked.
   Both are required in CI and run before Lean work in full and quick `scripts/check.sh` modes.
   They need only Python, without publishing tools or regenerated research data. Inserting unrelated
   lines above an excerpt is allowed. Changing, removing or duplicating its text needs attention.
   A relative source link such as `File.lean#L120` or `File.lean#L120-L180` must also start where
   the cited text starts: an unindented declaration (after modifiers such as `private` or
   `noncomputable`), an `@[…]` attribute or a `/--` docstring, outside any comment. A range may
   instead start at `/-!`, `section` or `namespace`, and `#L1` links a whole file. An edit that
   adds or removes lines above an anchored declaration, even inside a proof, moves it: run
   `python3 scripts/check_operator_manual.py --fix-anchors` to repoint `[Ns.name](File.lean#Ln)`
   links at the current header line of the declaration they name, and find any remaining prose,
   range or ambiguous links with `git grep -n 'File.lean#L' manual/` to update by hand.
   `STALE_SOURCE_ANCHORS` in the checker lists links that are stale, or that queued pull requests
   will make stale, and tolerates them until those pull requests land
   ([#3991](https://github.com/cslib-community/cslib-frontier/issues/3991)); repointing one of
   those links needs no edit to the list.
4. When Lean examples or their imports change, check the complete affected source clients under
   the [validation policy](../AGENTS.md#validation-sequence). The documentation checker is not
   a Lean build. Existing hosted validation can cover unchanged examples at the same revision.
5. When publishing either book or changing its converter/layout, follow [BUILD.md](BUILD.md),
   inspect the affected rendered pages and check the build log. A prose edit need not force a
   whole-library rebuild or a new full-book layout review.

Review a changed procedure page with the change that alters the procedure: the human
agent-driving route when roles, task assignment, review, handoffs, intervention or permissions
change, and the codebase route when its operating procedures change. A passing link check
cannot approve usability or completeness.
Record any missing route or prerequisite as a concrete defect, not an instruction to ask an
agent to fill it in.

## Preserve the research record

The model reference began as a source survey at `13e6a319` and is now frozen with its pinned
evidence. Source identity is evidence, not agreement with a textbook definition.

The [history](history/index.md) measurements and quantitative census are historical. New
measurements belong to a separately dated observation with defined coverage, units and denominators. Keep
their scripts and methods in the repository; write generated exports, API responses, dependency
copies and plots to ignored directories, as described in [BUILD.md](BUILD.md#regenerating-research-outputs).
The small excerpt registrations are handwritten source inputs and stay versioned.

The optional fixed-snapshot audit is described with the
[survey's supplementary code](history/survey.md#supplementary-code). It is not a merge check
against the moving repository and must not be run as a substitute for the live manual checker.
Public Git evidence can be regenerated from complete history; private logs and the original
mutable GitHub responses are separate reproduction requirements.
