/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

import CslibFrontier.GameTheory.Strategic.Semialgebraic

/-!
# Nash equilibrium sets of matching pennies

Matching pennies in cost form has exactly one totally mixed Nash equilibrium, uniform mixing. The
proof goes through equation (1) of [Datta2003] (`CostGame.isTotallyMixedNash_iff`): each player's
two pure strategies must have equal expected cost, which pins the other player's weights to `1/2`.
The general results then say that its mixed and totally mixed equilibria form semialgebraic sets,
and that player `0`'s expected cost polynomial for a pure strategy involves only player `1`'s
coordinates.
-/

namespace CslibFrontierTests.GameTheory.Semialgebraic

open Cslib Cslib.GameTheory

/-- Matching pennies in cost form: player `0` wants to match, player `1` to mismatch. -/
def pennies : CostGame (Fin 2) (fun _ => Bool) where
  cost i s := if (s 0 == s 1) = (i == 0) then 0 else 1

/-- Expected cost of each pure strategy, written over the four pure profiles. -/
private theorem pennies_deviationCost_eq (p : Fin 2 → Bool → ℝ) (i : Fin 2) (a : Bool) :
    pennies.deviationCost p i a =
      ∑ s : Bool × Bool, p 0 s.1 * p 1 s.2 *
        pennies.cost i (Function.update ![s.1, s.2] i a) := by
  rw [CostGame.deviationCost_def, ← (piFinTwoEquiv fun _ => Bool).symm.sum_comp]
  simp [productWeight, Fin.prod_univ_two]
  rfl

/-- Matching pennies has exactly one totally mixed Nash equilibrium: uniform mixing. -/
theorem pennies_isTotallyMixedNash_iff (p : Fin 2 → Bool → ℝ) :
    pennies.IsTotallyMixedNash p ↔ ∀ i b, p i b = 1 / 2 := by
  rw [CostGame.isTotallyMixedNash_iff]
  simp only [pennies_deviationCost_eq, Fintype.sum_prod_type, Fintype.sum_bool, Fin.forall_fin_two,
    Bool.forall_bool]
  norm_num [pennies, Function.update, Fin.forall_fin_two]
  constructor
  · rintro ⟨-, ⟨h0, h1⟩, e0, e1⟩
    have k1 : p 1 true = p 1 false := by
      linear_combination e0.1 - (p 1 true - p 1 false) * h0
    have k0 : p 0 false = p 0 true := by
      linear_combination e1.1 - (p 0 false - p 0 true) * h1
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rintro ⟨⟨h00, h01⟩, h10, h11⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [h00, h01, h10, h11] <;> norm_num

example : IsSemialgebraic {x : (Σ _ : Fin 2, Bool) → ℝ | pennies.IsMixedNash (Sigma.curry x)} :=
  pennies.isSemialgebraic_setOf_isMixedNash

/-- The mixed equilibria of matching pennies are cut out by finitely many polynomial
inequalities. -/
example : ∃ F : Finset (MvPolynomial (Σ _ : Fin 2, Bool) ℝ),
    {x | pennies.IsMixedNash (Sigma.curry x)} = {x | ∀ f ∈ F, 0 ≤ MvPolynomial.eval x f} :=
  pennies.exists_finset_setOf_isMixedNash_eq

example : IsSemialgebraic
    {x : (Σ _ : Fin 2, Bool) → ℝ | pennies.IsTotallyMixedNash (Sigma.curry x)} :=
  pennies.isSemialgebraic_setOf_isTotallyMixedNash

/-- Player `0`'s expected cost polynomial for a pure strategy involves only player `1`. -/
example {a : Bool} {v : Σ _ : Fin 2, Bool} (hv : v ∈ (pennies.deviationCostPoly 0 a).vars) :
    v.1 = 1 := by
  have := pennies.vars_deviationCostPoly hv
  omega

end CslibFrontierTests.GameTheory.Semialgebraic
