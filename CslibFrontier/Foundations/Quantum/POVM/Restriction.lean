/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.POVM

/-!
# Restricting a measurement to a coordinate subspace

A principal submatrix of a positive operator remains positive. Taking the principal
submatrix of each effect gives a POVM on the selected coordinates.
-/

public section

namespace Cslib.Quantum.POVM

open Matrix
open scoped ComplexOrder

variable {A ι κ : Type*} [Fintype A] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Restrict a POVM to the subspace spanned by the selected basis vectors. -/
noncomputable def restrictBasis (M : POVM A κ) (e : ι ↪ κ) : POVM A ι where
  effect a := (M.effect a).submatrix e e
  posSemidef a := (M.posSemidef a).submatrix e
  sum_effect := by
    rw [← Matrix.submatrix_one_embedding e, ← M.sum_effect]
    ext i j
    simp only [Matrix.sum_apply, Matrix.submatrix_apply]

@[simp] theorem restrictBasis_effect (M : POVM A κ) (e : ι ↪ κ) (a : A) :
    (M.restrictBasis e).effect a = (M.effect a).submatrix e e := by
  unfold restrictBasis
  rfl

end Cslib.Quantum.POVM
