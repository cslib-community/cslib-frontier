/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Strategic.Universality.StableUniversality
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The change of variables of Theorem 1 on the source's counterexample

For `V = {-1} ⊂ ℝ`, given by `t + 1 = 0`, the box coordinate of `-1` is
`toUnit (-1) = (3 − √5) / 2`, the root in `(0, 1)` of the cleared equation
`u (1 − u) (ρ(u / (1 − u)) + 1) = −u² + 3u − 1`. The other root `(3 + √5) / 2` lies outside the
box. Datta's map `t ↦ t / (1 − t²)` instead gives the cleared equation `t + 1 − t² = 0`, whose
extra root `(1 + √5) / 2` survives the rescaling into the box (the counterexample
`V = {(−1, 0)}` of the issue's source notes).

Both homeomorphisms applied to the point `-1` give actual totally mixed Nash equilibria: in the
binary game the variable player plays `true`, and in the three-player game Alice plays her
strategy `0`, with probability `(3 − √5) / 2`. `StablyIsomorphic.nonempty_iff` transfers the
nonemptiness of `V` to the binary game's equilibrium set.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.StableUniversality

open Cslib.GameTheory.DattaUniversality

/-- The three players. -/
example : Fintype.card Cslib.GameTheory.DattaThree.Who = 3 := rfl

theorem ratioInv_neg_one : ratioInv (-1) = (√5 - 1) / 2 := by
  rw [ratioInv]
  norm_num
  ring

/-- The box coordinate of `-1`. -/
theorem toUnit_neg_one : toUnit (-1) = (3 - √5) / 2 := by
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hlt : (1 : ℝ) < √5 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [toUnit, ratioInv_neg_one, div_eq_iff (by linarith)]
  nlinarith

/-- It is a root of the cleared equation `−u² + 3u − 1`, and maps back to `-1`. -/
example : -toUnit (-1) ^ 2 + 3 * toUnit (-1) - 1 = 0 ∧
    ratioCoord (toUnit (-1)) (1 - toUnit (-1)) = -1 := by
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  refine ⟨?_, ratioCoord_toUnit _⟩
  rw [toUnit_neg_one]
  nlinarith

/-! ### An actual equilibrium -/

open MvPolynomial Cslib

/-- `t + 1`, whose zero set is `V = {-1}`. -/
noncomputable def plusOne : Fin 1 → MvPolynomial (Fin 1) ℝ := fun _ => X 0 + 1

/-- The point `-1` of `V`, with no free coordinates (`m − n = 0`). -/
noncomputable def pt : {z : Fin 1 ⊕ Fin (1 - 1) → ℝ |
    z ∘ Sum.inl ∈ {x | ∀ j, eval x (plusOne j) = 0}} :=
  ⟨Sum.elim (fun _ => -1) Fin.elim0, fun _ => by simp [plusOne]⟩

/-- The binary homeomorphism sends `-1` to a totally mixed Nash equilibrium of `binaryGame`, in
which the variable player plays `true` with probability `toUnit (-1) = (3 − √5) / 2`. -/
example : (binaryGame plusOne).IsTotallyMixedNash
      (Sigma.curry ((binaryHomeomorph plusOne one_pos).toHomeomorph pt).val) ∧
    ((binaryHomeomorph plusOne one_pos).toHomeomorph pt).val
      ⟨Cslib.GameTheory.DattaBinary.var 0, true⟩ = (3 - √5) / 2 := by
  refine ⟨((binaryHomeomorph plusOne one_pos).toHomeomorph pt).property, ?_⟩
  rw [coe_binaryHomeomorph_apply]
  simp [Sigma.uncurry, Cslib.GameTheory.binaryProfile, binaryPoint, pt, toUnit_neg_one]

/-- The point `-1` of `V`, with no free Critter coordinates (`Extra 1 1` is empty). -/
noncomputable def ptH : {z : Fin 1 ⊕ Extra 1 1 → ℝ |
    z ∘ Sum.inl ∈ {x | ∀ j, eval x (plusOne j) = 0}} :=
  ⟨Sum.elim (fun _ => -1) fun j => absurd j.property (by omega), fun _ => by simp [plusOne]⟩

/-- The three-player homeomorphism sends `-1` to a totally mixed Nash equilibrium of
`hornerGame`, in which Alice plays her strategy `0` with probability `(3 − √5) / 2`. -/
example : (hornerGame plusOne).IsTotallyMixedNash
      (Sigma.curry ((hornerHomeomorph plusOne).toHomeomorph ptH).val) ∧
    ((hornerHomeomorph plusOne).toHomeomorph ptH).val ⟨.alice, some 0⟩ = (3 - √5) / 2 := by
  refine ⟨((hornerHomeomorph plusOne).toHomeomorph ptH).property, ?_⟩
  rw [coe_hornerHomeomorph_apply, ← toUnit_neg_one]
  simp [Sigma.uncurry, Cslib.GameTheory.simplexProfile, hornerPoint, simplexPoint,
    toUnit, ptH]

/-- `V` is nonempty, so the equilibrium set of `binaryGame` is too
(`StablyIsomorphic.nonempty_iff`). -/
example : {x : (Σ _ : Cslib.GameTheory.DattaBinary.Player 1 (boxDegree plusOne) 1, Bool) → ℝ |
    (binaryGame plusOne).IsTotallyMixedNash (Sigma.curry x)}.Nonempty :=
  (StablyIsomorphic.nonempty_iff (stablyIsomorphic_binaryGame plusOne one_pos)).1
    ⟨fun _ => -1, fun _ => by simp [plusOne]⟩

end CslibFrontierTests.GameTheory.StableUniversality
