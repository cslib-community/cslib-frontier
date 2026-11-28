/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, matrix Loewner order)

public import CslibFrontier.Init
public import Mathlib.Analysis.Matrix.Order

/-!
# Nonnegative rational scaling in the Loewner order

Multiplication by a nonnegative rational is monotone for the matrix order. This lets
uniform averages use the Loewner order with the usual scalar action on matrices.
-/

public section

namespace MatrixOrder

open scoped ComplexOrder MatrixOrder

/-- Nonnegative rational scaling preserves the Loewner order. -/
scoped instance instPosSMulMonoNNRat {n 𝕜 : Type*} [RCLike 𝕜] :
    PosSMulMono ℚ≥0 (Matrix n n 𝕜) :=
  .of_smul_nonneg fun q _ M hM => by
    rw [← NNRat.cast_smul_eq_nnqsmul 𝕜, Matrix.nonneg_iff_posSemidef]
    have hq : 0 ≤ (q : 𝕜) := by
      rw [← RCLike.ofReal_nnratCast (K := 𝕜), RCLike.ofReal_nonneg]
      exact q.cast_nonneg
    exact (Matrix.nonneg_iff_posSemidef.mp hM).smul hq

end MatrixOrder
