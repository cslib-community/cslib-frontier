/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/PosDef.lean`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Positive (semi)definiteness criteria

A symmetric `2 × 2` real matrix `!![a, b; b, c]` with `a, c ≥ 0` and `b² ≤ ac` is positive
semidefinite (`Matrix.posSemidef_fin_two`). An `LDLᴴ` product `L * diagonal d * Lᴴ` with `L`
unit lower triangular is positive definite exactly when every `d i` is positive, and positive
semidefinite exactly when every `d i` is nonnegative. Since `L` is invertible, this is a case of
Sylvester's law of inertia for the congruence by `L`.

## Main results

* `Matrix.posSemidef_fin_two`: the diagonal-and-determinant criterion for a symmetric `2 × 2` real
  matrix to be positive semidefinite.
* `Matrix.posDef_mul_diagonal_mul_conjTranspose_iff`,
  `Matrix.posSemidef_mul_diagonal_mul_conjTranspose_iff`: the `LDLᴴ` criteria.
-/

public section

namespace Matrix

/-- A symmetric `2 × 2` real matrix with nonnegative diagonal and nonnegative determinant is
positive semidefinite. -/
theorem posSemidef_fin_two {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (h : b ^ 2 ≤ a * c) :
    (!![a, b; b, c]).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · simp only [mulVec, dotProduct, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, star_trivial]
    rcases ha.eq_or_lt with rfl | hapos
    · have hb : b = 0 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm (by simpa using h)
        (sq_nonneg b))
      subst hb
      nlinarith [mul_nonneg hc (sq_nonneg (x 1))]
    · refine (mul_nonneg_iff_of_pos_left hapos).1 ?_
      nlinarith [sq_nonneg (a * x 0 + b * x 1), mul_nonneg (sub_nonneg.2 h) (sq_nonneg (x 1))]

section LDL

variable {n R : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] [CommRing R]
  {L : Matrix n n R} {d : n → R}

/-- A unit lower-triangular matrix is a unit: its determinant is the product of its
diagonal. -/
private theorem isUnit_of_isLowerTriangular (hL : L.IsLowerTriangular) (h1 : ∀ i, L i i = 1) :
    IsUnit L :=
  (isUnit_iff_isUnit_det L).2 <| by simp [det_of_isLowerTriangular L hL, h1]

/-- An `LDLᴴ` product with `L` unit lower triangular is positive definite exactly when every
diagonal entry `d i` is positive. -/
theorem posDef_mul_diagonal_mul_conjTranspose_iff [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [NoZeroDivisors R] [Nontrivial R] (hL : L.IsLowerTriangular)
    (h1 : ∀ i, L i i = 1) :
    (L * diagonal d * Lᴴ).PosDef ↔ ∀ i, 0 < d i := by
  rw [← star_eq_conjTranspose,
    IsUnit.posDef_star_right_conjugate_iff (isUnit_of_isLowerTriangular hL h1), posDef_diagonal_iff]

/-- An `LDLᴴ` product with `L` unit lower triangular is positive semidefinite exactly when every
diagonal entry `d i` is nonnegative. -/
theorem posSemidef_mul_diagonal_mul_conjTranspose_iff [PartialOrder R] [StarRing R]
    [StarOrderedRing R] (hL : L.IsLowerTriangular) (h1 : ∀ i, L i i = 1) :
    (L * diagonal d * Lᴴ).PosSemidef ↔ ∀ i, 0 ≤ d i := by
  rw [← star_eq_conjTranspose,
    IsUnit.posSemidef_star_right_conjugate_iff (isUnit_of_isLowerTriangular hL h1),
    posSemidef_diagonal_iff]

end LDL

end Matrix
