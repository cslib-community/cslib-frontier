/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, traces of products of positive semidefinite matrices)

public import CslibFrontier.Init
public import Mathlib.Analysis.Matrix.Order

/-!
# Traces of products of positive semidefinite matrices

The product of positive semidefinite matrices need not be positive semidefinite, but its trace
is nonnegative. Factor one matrix as `Cᴴ C` and rotate the trace to the positive sandwich `C A Cᴴ`.
For complex matrices, nonnegativity in `ComplexOrder` also asserts that the imaginary part is zero.

## Main results

* `Matrix.PosSemidef.trace_mul_nonneg`: the trace of a product of positive semidefinite matrices
  is nonnegative, over either the real or the complex numbers.
* `Matrix.PosSemidef.trace_mul_eq_zero_iff`: vanishing trace is equivalent to vanishing product.
-/

public section

namespace Matrix.PosSemidef

open scoped MatrixOrder ComplexOrder

/-- The trace of the product of two positive semidefinite matrices is nonnegative. -/
theorem trace_mul_nonneg {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]
    {A B : Matrix ι ι 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  classical
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.star_eq_conjTranspose]
  exact (hA.mul_mul_conjTranspose_same C).trace_nonneg

/-- Two positive semidefinite matrices have zero product exactly when it has zero trace. -/
theorem trace_mul_eq_zero_iff {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]
    {A B : Matrix ι ι 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A * B).trace = 0 ↔ A * B = 0 := by
  classical
  refine ⟨fun h => ?_, fun h => by rw [h, Matrix.trace_zero]⟩
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨D, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  simp only [Matrix.star_eq_conjTranspose] at h ⊢
  have ht : ((C * Dᴴ)ᴴ * (C * Dᴴ)).trace = (Cᴴ * C * (Dᴴ * D)).trace := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm D]
    simp only [Matrix.mul_assoc]
  have hz := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (ht.trans h)
  calc
    _ = Cᴴ * (C * Dᴴ) * D := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hz, Matrix.mul_zero, Matrix.zero_mul]

end Matrix.PosSemidef
