/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.Approximation.GapLin

/-! Checked uses of Goldreich's Exercise 10.5 (`gapLin_{L,s}` is NP-hard): the constants of the
packaged instance lie in the source's range `1 / 2 < s < L < 1`, the seven equations of a clause
are counted on a concrete clause with repeated variables, and the reduction applies to every
MAX-E3SAT soundness below one. -/

set_option linter.privateModule false

namespace CslibFrontierTests.GapLin

open Cslib.Complexity Cslib.Logic.PL

/-- The packaged constants satisfy Goldreich's constraints. -/
example : (1 : ℝ) / 2 < 4 / 7 * (1 - 1 / (6 * 2 ^ 77)) ∧
    (4 / 7 * (1 - 1 / (6 * 2 ^ 77)) : ℝ) < 4 / 7 ∧ (4 : ℝ) / 7 < 1 := by
  norm_num

/-- The headline existential, unfolded at the packaged constants. -/
example : PromiseProblem.NPHard XORSAT.encoding (GapLin (4 / 7) (4 / 7 * (1 - 1 / (6 * 2 ^ 77)))) :=
  GapLin_npHard

example : ∃ L s : ℝ, 1 / 2 < s ∧ s < L ∧ L < 1 ∧
    PromiseProblem.NPHard XORSAT.encoding (GapLin L s) :=
  exists_GapLin_npHard

/-- The clause `x₀ ∨ ¬x₀ ∨ x₁` is satisfied by every assignment, so four of its seven equations
hold, even though a variable repeats. -/
example (σ : ℕ → Bool) :
    (GapLin.clauseEquations [(0, true), (0, false), (1, true)]).countSat σ = 4 := by
  rw [GapLin.countSat_clauseEquations]
  cases h : σ 0 <;> simp [Clause.eval, Literal.eval, h]

/-- The all-false assignment falsifies `x₀ ∨ x₁ ∨ x₂`, and none of its seven equations hold. -/
example :
    (GapLin.clauseEquations [(0, true), (1, true), (2, true)]).countSat (fun _ => false) = 0 := by
  rw [GapLin.countSat_clauseEquations]
  simp [Clause.eval, Literal.eval]

/-- Any MAX-E3SAT soundness below one gives a reduction, here `s₀ = 9 / 10`. -/
example : PromiseProblem.PolyTimeReducible encCNF XORSAT.encoding (GapExactThreeSAT (9 / 10))
    (GapLin (4 / 7) (11 / 20)) :=
  polyTimeReducible_GapExactThreeSAT_GapLin (by norm_num) (by norm_num) (by norm_num)

end CslibFrontierTests.GapLin
