/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/InnerProductSpace/PiL2.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Norms of matrix-vector products on `EuclideanSpace ℂ ι`

The squared norm of `ψ : EuclideanSpace ℂ ι` is the quadratic form `ψ† ψ`
(`EuclideanSpace.star_dotProduct_self_eq_norm_sq`). Hence a matrix `M` with `Mᴴ M ≤ 1`, that is
with `1 - Mᴴ M` positive semidefinite, does not increase norms
(`Matrix.norm_toLp_mulVec_le_of_posSemidef`).

## Main results

* `EuclideanSpace.star_dotProduct_self_eq_norm_sq`: `ψ† ψ = ‖ψ‖²`.
* `Matrix.norm_toLp_mulVec_le_of_posSemidef`: a matrix `M` with `Mᴴ M ≤ 1` does not increase
  norms.
* `Matrix.norm_toLp_mulVec_of_conjTranspose_mul_self`: an isometry, `Kᴴ K = 1`, preserves norms.
-/

public section

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι]

/-- The squared norm of a vector as a quadratic form: `ψ† ψ = ‖ψ‖²`. -/
theorem EuclideanSpace.star_dotProduct_self_eq_norm_sq (ψ : EuclideanSpace ℂ ι) :
    star ψ.ofLp ⬝ᵥ ψ.ofLp = (‖ψ‖ : ℂ) ^ 2 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
  rfl

private theorem gram_apply_eq_norm_sq {m : Type*} [Fintype m]
    (M : Matrix m ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    star ψ.ofLp ⬝ᵥ ((Mᴴ * M) *ᵥ ψ.ofLp) =
      (‖(WithLp.toLp 2 (M *ᵥ ψ.ofLp) : EuclideanSpace ℂ m)‖ : ℂ) ^ 2 := by
  rw [← EuclideanSpace.star_dotProduct_self_eq_norm_sq, WithLp.ofLp_toLp, star_mulVec,
    ← dotProduct_mulVec, mulVec_mulVec]

/-- A positive semidefinite bound on Gram matrices gives a pointwise bound on vector norms. -/
theorem Matrix.norm_toLp_mulVec_le_of_gram_le {l m : Type*} [Fintype l] [Fintype m]
    {M : Matrix l ι ℂ} {N : Matrix m ι ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : (c • (Nᴴ * N) - Mᴴ * M).PosSemidef) (ψ : EuclideanSpace ℂ ι) :
    ‖(WithLp.toLp 2 (M *ᵥ ψ.ofLp) : EuclideanSpace ℂ l)‖ ≤
      Real.sqrt c * ‖(WithLp.toLp 2 (N *ᵥ ψ.ofLp) : EuclideanSpace ℂ m)‖ := by
  have h0 := (Complex.nonneg_iff.mp (h.dotProduct_mulVec_nonneg ψ.ofLp)).1
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
    gram_apply_eq_norm_sq, gram_apply_eq_norm_sq, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    Complex.sub_re, Complex.real_smul, Complex.mul_re] at h0
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h0
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hc]
  exact sub_nonneg.mp h0

/-- A matrix `M` with `Mᴴ M ≤ 1` does not increase norms: `‖M ψ‖ ≤ ‖ψ‖`. -/
theorem Matrix.norm_toLp_mulVec_le_of_posSemidef [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : (1 - Mᴴ * M).PosSemidef) (ψ : EuclideanSpace ℂ ι) :
    ‖(WithLp.toLp 2 (M *ᵥ ψ.ofLp) : EuclideanSpace ℂ ι)‖ ≤ ‖ψ‖ := by
  have h : ((1 : ℝ) • ((1 : Matrix ι ι ℂ)ᴴ * 1) - Mᴴ * M).PosSemidef := by
    simpa only [conjTranspose_one, one_mul, one_smul] using hM
  simpa only [Real.sqrt_one, one_mulVec, WithLp.toLp_ofLp, one_mul] using
    Matrix.norm_toLp_mulVec_le_of_gram_le zero_le_one h ψ

/-- An isometry preserves the norm of vectors. -/
theorem Matrix.norm_toLp_mulVec_of_conjTranspose_mul_self {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] {K : Matrix m n ℂ} (hK : Kᴴ * K = 1) (ψ : EuclideanSpace ℂ n) :
    ‖(WithLp.toLp 2 (K *ᵥ ψ.ofLp) : EuclideanSpace ℂ m)‖ = ‖ψ‖ := by
  have h := gram_apply_eq_norm_sq K ψ
  rw [hK, one_mulVec, EuclideanSpace.star_dotProduct_self_eq_norm_sq,
    ← Complex.ofReal_pow, ← Complex.ofReal_pow] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (Complex.ofReal_injective h.symm)
