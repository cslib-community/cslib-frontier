/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Matrix/Mul.lean`, next to `Matrix.vecMul_eq_sum`)

public import CslibFrontier.Init
public import Mathlib.Data.Matrix.Mul

/-!
# Row combinations as columns of the transposed word

`Matrix.vecMul_eq_sum_smul_swap` writes `v ᵥ* M` entrywise as the `v`-weighted combination of
the rows of `M`, read through the column-indexed word `Function.swap M`. This is the form in
which interleaved-code proximity bounds (`Cslib.Code.interleavedLinear`) state random row
combinations, so it converts encodings `v ᵥ* G` and row combinations of a matrix to that API.
-/

public section

namespace Matrix

variable {m n α : Type*} [Fintype m] [NonUnitalNonAssocSemiring α]

/-- Entry `j` of `v ᵥ* M` is the `v`-weighted sum of the entries of column `j`, read from the
column-indexed word `Function.swap M`. -/
theorem vecMul_eq_sum_smul_swap (v : m → α) (M : Matrix m n α) :
    v ᵥ* M = fun j => ∑ i, v i • Function.swap M j i := by
  funext j
  simp only [vecMul, dotProduct, Function.swap, smul_eq_mul]

end Matrix
