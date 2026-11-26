/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Foundations.Algebra.BigOperators.WriteSteps
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Fintype.Basic

/-! Tests of sums over contents, as a client: two cells with contents in `Bool`. The first step
guesses the first cell, with the weight `2` or `3`; the second step reads the first cell and
writes its negation in the second one, with the weight `5` or `7`. The sum over the executions is
computed, the two steps are sequential by the criterion of the cells read, and so the sum over all
contents of the product of the two factors is the same number. -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Foundations.Algebra.BigOperators.WriteSteps

open Finset

/-- Guess the cell `false`: the content `true` has the weight `2`, and `false` the weight `3`. -/
def guess : WriteStep ℤ Bool Bool where
  Choice := Bool
  choices := univ
  written := {false}
  weight ω _ := if ω then 2 else 3
  contents ω _ _ := ω
  read := ∅

/-- Write the negation of the cell `false` in the cell `true`, with the weight `5` or `7`. -/
def negate : WriteStep ℤ Bool Bool where
  Choice := Unit
  choices := univ
  written := {true}
  weight _ y := if y false then 5 else 7
  contents _ y _ := !y false
  read := {false}

/-- The weight of the executions that end with `true` in the second cell: `3 * 7`. -/
theorem exec_eq (σ : Bool → Bool) :
    WriteStep.exec [guess, negate] (fun y => if y true then 1 else 0) σ = 21 := by
  simp [guess, negate, Finset.piecewise]

theorem sequential : WriteStep.Sequential [guess, negate] := by
  refine WriteStep.Sequential.of_pairwise ?_ ?_
  · simp [guess, negate]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨by simp [guess], fun _ _ _ _ _ => ⟨rfl, fun _ _ => rfl⟩⟩,
      by simp [negate], fun _ _ y y' h => by simp [negate, h false]⟩

/-- The sum over the contents of the two cells of the product of the factors. -/
example (σ : Bool → Bool) :
    ∑ y with ∀ c ∉ WriteStep.writtenCells [guess, negate], y c = σ c,
      ([guess, negate].map fun s => s.factor y).prod * (if y true then 1 else 0) = 21 :=
  (WriteStep.sum_prod_factor_mul_eq_exec sequential _ σ).trans (exec_eq σ)

end CslibFrontierTests.Foundations.Algebra.BigOperators.WriteSteps
