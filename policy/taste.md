# Taste: what earns a place in the library

This file is part of the project instructions ([AGENTS.md](../AGENTS.md)). The other policy files
say what is required. This one says what good looks like, through patterns that have landed on
`main`, passed review, and should not have. Authors check their change against it before
requesting review; reviewers use it to answer "what should not exist?" and "what is the first
real property?" ([Review cycle](../AGENTS.md#review-cycle)).

A reader of this library wants a small number of statements they can trust and apply. Every extra
public name is something they must read, tell apart from its neighbours and keep working. Prefer
the change that leaves fewer declarations and one way to say each thing.

## A result is something a reader could not have written down for free

Not results, and not listed under "Main results":

- **Unfoldings.** `Desc.runOracle_eq_toMachine`, where `Desc.runOracle` is defined as the
  right-hand side, is `rfl`. So is an `X_iff` that is `Iff.rfl` against the definition's body.
- **Restated library lemmas.** A `simpa` wrapper around `Fin.findSome?_eq_none_iff`,
  `List.length_map` or `Embedding.injective` under a domain name.
- **Properties true by construction.** A predicate defined to describe a list, with one theorem
  saying that the list just built satisfies it.
- **Tests.** `decide` or `#guard` on a toy instance shows a definition computes; it does not
  establish the general property.

Interface lemmas are a different thing. Under the module system a public definition's body is
not exposed, so clients cannot unfold it and rely on its `@[simp]`, `_apply` and `_iff`
specifications, including those `enc_structure` generates; their proofs are `rfl` inside the
defining module, and they are legitimate API. They are still not listed under "Main results". What
should not exist is a bare `rfl` restatement of an exposed definition or `abbrev` that plays no
part in a `simp` normal form.

If a module has definitions and none of its theorems would survive this list, say so: the PR
title and module documentation call it definitions only.

## Prove the first real property with the definition

A transcribed algorithm or new construction comes with the property that shows the transcription
means something: a signer's signatures verify; padding is block-aligned; no revealed tree node is
an ancestor of the hidden leaf; a simulator's output is close to the real view. A faithful
transcription with no such theorem is unvalidated, however careful its source mapping. Where the
model has subtle boundaries, pair that theorem with a checked boundary witness in the test file
([New statements and definitions](statements.md#new-statements-and-definitions)), never under
"Main results".

## One name per fact

- **No negated or weakened companions.** If `A ⊂ B` is a theorem, do not add `¬ B ⊆ A`; callers
  write `h.not_superset`. If `=` is proved, do not add `⊆` in each direction.
- **No corollary grids.** Do not enumerate {subset, equality} × {each class} × {each encoding}.
  State the general theorem and the one or two instances that a caller or a cited source needs.
- **No eta-copies or re-exports** of a theorem under a second name or namespace.
- **No arity series.** After `_pair` and `_triple`, the next lemma is the `k`-ary one, not `_six`.
- **No wrapper definitions** that only rename a library function (`FixedBytes.take` for
  `Fin.take`, `addInt` for `+`, `leafCount h` for `2 ^ h`). Introduce a named operation when it
  carries content or when a second implementation exists, not because one might.

## A declaration has a caller

A public declaration is used by another module, by the stated next step of its issue, or by a
reader applying the cited result. Its own test file is not a caller. "Prerequisite" and "layer 1"
do not license surface that nothing consumes: land it with its first consumer, or keep it private
until then. Efficiency certificates follow the same rule: a certificate for an experiment that no
theorem consumes is not needed.

Public is a decision, not the default. A declaration is public when another module uses it, when
the module documentation names it as something the file offers, when it is a cited result, or when
it is part of the interface of a public definition that a user of that definition would expect
(its characterizations, bounds and `simp` equations:
[What stays public](../CONTRIBUTING.md#public-surface-under-the-module-system)). A proof step or sub-program that only its
own file uses is `private`. A test is not a caller, so a result that only its test names is listed
in the module documentation. Reference counts are evidence, not the criterion: the aim is that a
reader can take a file's public names as the things it offers.

## Replace, do not accumulate

When a change introduces a better notion, it migrates the old one's clients and deletes it,
except under an accepted deferral
([Improving library ergonomics](../AGENTS.md#improving-library-ergonomics)). A third eavesdropping game beside two existing ones, a second
CPA formalism bridged to the first, a new first-success construction beside two others: each
leaves the reader to work out which is authoritative. Bridging lemmas between parallel notions
are a sign that one of them should go ([Faithful headlines](../AGENTS.md#faithful-headlines),
rule 4).

## Hypotheses are checked one at a time

- Every hypothesis of a corollary is needed by that corollary, not inherited from the headline it
  follows. Ask whether a stronger lemma already on `main` removes it.
- No proof arguments the definition ignores (`sha256 input (_h : Valid input)`).
- No hypothesis whose variables do not appear in the conclusion or in another hypothesis that
  does.
- A hypothesis bundle repeated across many theorems becomes a `structure` or a `variable` block.
- No auto-param (`:= by fun_prop`) on a mathematical hypothesis of a headline.

## Words match what is proved

- "Exact", "complete", "native", "uniform" and "secure" describe the theorem, not the intent. If
  only the exponent draw is native, the title does not say the scheme is.
- A module docstring describes mathematics, not the process that produced it: no review notes,
  provenance of checks or status of other PRs.
- A sentence about the source's theorem is not placed where it reads as a claim about the Lean
  one.
- A locator names the line, page or section you looked at in the pinned source.

## A stated limitation is tracked

A docstring that says what is not proved or what stands in for the real thing is welcome, and it
is not a resolution. It makes the gap a known one; it does not make the theorem say what its name
says ([Faithful headlines](../AGENTS.md#faithful-headlines), rule 2: listing a gap under
"Limitations" does not meet the rule).

This section is about unresolved gaps: a cited result not yet reached, a stand-in or step landed
under rule 2, a missing efficiency certificate, a hypothesis that stands for unfinished work, a
superseded version not yet removed. It is not about a source's own hypothesis, a named standard
assumption, or a deliberate boundary of the model, such as a query-count theorem that says it
makes no claim about running time. Those are documented and need no issue.

- A sentence that states an unresolved gap cites the issue that tracks it, or its declaration has
  an entry in the baseline of the check that covers it
  ([reduction witnesses and security premises](../CONTRIBUTING.md)). Rule 2 already requires that
  the cited objective stay open; the issue number is where it stays open. A gap with neither is
  found again only by someone rereading the prose.
- The name and the first sentence carry the gap, as rule 2 requires of a step: an ideal-sampling
  result has `ideal` in its name, a bound for a stand-in scheme names the stand-in, and a helper
  whose hypothesis assumes the substance of the cited result does not open with that result in
  bold.
- A step that nothing in the library consumes, and that no open issue plans to consume, has no
  caller ([A declaration has a caller](#a-declaration-has-a-caller)) and is removed.
- A superseded version goes when its replacement lands (rule 4;
  [Replace, do not accumulate](#replace-do-not-accumulate)); a comment saying which theorem is the
  faithful one is not a substitute.

## Small facts are shared

An arithmetic identity needed in a second file is a lemma in a shared module, not a second inline
`have` (`((q - a % q : ℕ) : ZMod q) = -a` appeared in five files). A migration that makes helper
lemmas into pass-throughs deletes them and tidies their call sites in the same change.
