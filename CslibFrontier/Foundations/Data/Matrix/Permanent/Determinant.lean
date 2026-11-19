/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, next to `LinearAlgebra/Matrix/Permanent`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.CharP.Lemmas

/-!
# Determinants and permanents in characteristic two

The signs in the determinant expansion vanish over a commutative ring of characteristic two.

## Main results

* `Matrix.det_eq_permanent_of_charTwo`: determinant and permanent agree in characteristic two.
-/

public section

/-- In characteristic two the determinant of a matrix is its permanent. -/
theorem Matrix.det_eq_permanent_of_charTwo {R ι : Type*} [CommRing R] [CharP R 2]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) : M.det = M.permanent := by
  rw [Matrix.det_apply, Matrix.permanent]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul, CharTwo.neg_eq]
