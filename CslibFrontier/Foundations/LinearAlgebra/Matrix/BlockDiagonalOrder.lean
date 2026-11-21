/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, block-diagonal matrix order)

public import CslibFrontier.Init
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Data.Matrix.Block

/-!
# Loewner order on block-diagonal matrices

Positivity of each block implies positivity of the block diagonal. Consequently
block diagonalization is monotone for the pointwise Loewner order.
-/

public section

namespace Matrix

open scoped ComplexOrder MatrixOrder

variable {ι α : Type*} [Finite ι] [Finite α] [DecidableEq α]

/-- A block diagonal of positive semidefinite matrices is positive semidefinite. -/
theorem posSemidef_blockDiagonal {A : α → Matrix ι ι ℂ} (hA : ∀ a, (A a).PosSemidef) :
    (blockDiagonal A).PosSemidef := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite α
  choose B hB using fun a => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hA a).nonneg
  have h : blockDiagonal A = (blockDiagonal B)ᴴ * blockDiagonal B := by
    rw [blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    exact congrArg blockDiagonal (funext hB)
  rw [h]
  exact posSemidef_conjTranspose_mul_self _

/-- A comparison in each block implies a comparison of the full matrices. -/
theorem blockDiagonal_mono {A B : α → Matrix ι ι ℂ} (h : ∀ a, A a ≤ B a) :
    blockDiagonal A ≤ blockDiagonal B := by
  rw [Matrix.le_iff, ← blockDiagonal_sub]
  exact posSemidef_blockDiagonal fun a => Matrix.le_iff.mp (h a)

end Matrix
