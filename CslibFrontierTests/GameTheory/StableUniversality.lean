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

end CslibFrontierTests.GameTheory.StableUniversality
