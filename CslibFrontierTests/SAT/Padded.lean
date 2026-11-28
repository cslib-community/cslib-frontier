/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.SAT.Padded
import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT

/-! Checked clients of the padded witness relation of `SAT` (Goldreich, Exercises 6.35 and
6.36(a)): its unique-solution set is empty, a formula with an empty clause is a no instance of
the promise, satisfiable formulas lie outside the promise, the relation's language is NP-hard,
and a polynomial-time algorithm for its count would put all of #P in polynomial time. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SATPadded

open Cslib.Complexity Cslib.Complexity.SAT Cslib.Logic.PL Turing.MultiTapeTM

/-- No formula has a unique solution: `US_R` is empty. -/
example (φ : CNF ℕ) : searchCount paddedRelation.IsWitness φ ≠ 1 := by
  rw [searchCount_paddedRelation]
  omega

/-- A formula containing the empty clause has no solution, so it is a no instance. -/
example : searchCount paddedRelation.IsWitness [[]] = 0 := by
  rw [searchCount_paddedRelation, SharpSAT,
    modelCount_eq_zero_of_nil_mem (List.mem_singleton_self _)]

/-- A satisfiable formula has at least two solutions, so it lies outside the promise. -/
example {φ : CNF ℕ} (h : φ ∈ Cslib.Complexity.SAT) :
    2 ≤ searchCount paddedRelation.IsWitness φ := by
  have := SharpSAT.mem_SAT_iff.1 h
  rw [searchCount_paddedRelation]
  omega

/-- The language of the padded relation is NP-hard. -/
example : NPHard encCNF paddedRelation.language :=
  paddedRelation_levinHard.npHard

/-- A polynomial-time algorithm for the padded count would put #SAT in polynomial time. -/
example (h : ComputableInPolyTime (searchCount paddedRelation.IsWitness) encCNF encNat) :
    ComputableInPolyTime SharpSAT encCNF encNat :=
  searchCount_paddedRelation_sharpPMetricComplete.2.computableInPolyTime h
    SharpSAT.mem_SharpP

end CslibFrontierTests.SATPadded
