/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Act
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Block

/-! Tests of the Flag layer: projections to fixed points of a finite isometry group, and the
block decomposition of the unitriangular group. -/

namespace CslibFrontierTests.FlagAct

open Cslib.Circuits.Arithmetic.Separation.Flag

/-- `ℤˣ = {1, -1}` acts on `ℝ` by multiplication, by isometries. -/
noncomputable def signAct : IsoAct ℤˣ ℝ where
  toFun u := IsometryEquiv.mk (Equiv.mulLeft₀ ((u : ℤ) : ℝ) (by
      rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num))
    (Isometry.of_dist_eq fun z z' => by
      rw [Real.dist_eq, Real.dist_eq]
      change |((u : ℤ) : ℝ) * z - ((u : ℤ) : ℝ) * z'| = |z - z'|
      rw [← mul_sub, abs_mul]
      rcases Int.units_eq_one_or u with rfl | rfl <;> simp)
  map_one' := by ext z; simp
  map_mul' g h := by ext z; simp [IsometryEquiv.mul_apply, mul_assoc]

/-- The projection of any point to the fixed points of the sign action is `0`, the barycenter of
`z` and `-z`. -/
example (z : ℝ) : signAct.P z = 0 := by
  have h := signAct.P_fix z (-1)
  change ((-1 : ℤˣ) : ℤ) * signAct.P z = signAct.P z at h
  push_cast at h
  linarith

/-- The block decomposition `U (a + b) ≃ U a × M_{a×b} × U b` is a bijection, for `a = b = 1`. -/
example : Function.Bijective
    (blk : Cslib.SLTower.U 1 × Matrix (Fin 1) (Fin 1) F2 × Cslib.SLTower.U 1 →
      Cslib.SLTower.U (1 + 1)) :=
  blk_bijective

end CslibFrontierTests.FlagAct
