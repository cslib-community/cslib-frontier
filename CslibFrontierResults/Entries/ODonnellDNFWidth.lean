/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.DNFWidth

/-!
# Collected results: small DNFs are close to narrow ones
-/

register_result "odonnell-small-dnf-close-to-narrow" where
  title := "Small DNFs and CNFs are close to narrow ones"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Proposition 4.9",
      locator := "arXiv:2105.10386v1, §4.1, printed pp. 95–96" }
  ]
  theorems := [Cslib.BitString.exists_dnf_hammingDist_div_le,
    Cslib.BitString.exists_cnf_hammingDist_div_le]
  scope := "For every formula φ in disjunctive (or conjunctive) normal form with s terms \
    (clauses) over a finite variable type ι and every ε > 0: some formula of the same kind with \
    at most s terms (clauses), each of at most log₂ (s / ε) literals, computes a function at \
    relative Hamming distance at most ε from φ's on ι → Bool. Each term of the narrow DNF has \
    no repeated literal and is consistent (Term.consistent), and each clause of the narrow CNF \
    has no repeated literal and is not a tautology (CNF.isTautClause): Definition 4.1's \
    restriction, carried to clauses by Definition 4.4, so the length bound counts the book's \
    literals. The book takes ε ∈ (0, 1] and states the CNF case as \"(or CNF)\"; it is \
    read, following the proof, as giving a CNF."
