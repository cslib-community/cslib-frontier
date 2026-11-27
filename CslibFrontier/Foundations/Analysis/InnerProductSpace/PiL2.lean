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

/-- The squared norm of the image of a vector is the real quadratic form of the Gram matrix. -/
theorem Matrix.norm_toLp_mulVec_sq_eq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (ψ : EuclideanSpace ℂ n) :
    ‖(WithLp.toLp 2 (A *ᵥ ψ.ofLp) : EuclideanSpace ℂ m)‖ ^ 2 =
      (star ψ.ofLp ⬝ᵥ ((Aᴴ * A) *ᵥ ψ.ofLp)).re := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  have h := EuclideanSpace.star_dotProduct_self_eq_norm_sq
    (WithLp.toLp 2 (A *ᵥ ψ.ofLp) : EuclideanSpace ℂ m)
  rw [WithLp.ofLp_toLp, ← Complex.ofReal_pow] at h
  rw [h, Complex.ofReal_re]

/-- A matrix `M` with `Mᴴ M ≤ 1` does not increase norms: `‖M ψ‖ ≤ ‖ψ‖`. -/
theorem Matrix.norm_toLp_mulVec_le_of_posSemidef [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : (1 - Mᴴ * M).PosSemidef) (ψ : EuclideanSpace ℂ ι) :
    ‖(WithLp.toLp 2 (M *ᵥ ψ.ofLp) : EuclideanSpace ℂ ι)‖ ≤ ‖ψ‖ := by
  have h0 := (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg ψ.ofLp)).1
  rw [sub_mulVec, one_mulVec, dotProduct_sub, Complex.sub_re,
    ← Matrix.norm_toLp_mulVec_sq_eq, EuclideanSpace.star_dotProduct_self_eq_norm_sq,
    ← Complex.ofReal_pow, Complex.ofReal_re] at h0
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)

/-- An isometry preserves the norm of vectors. -/
theorem Matrix.norm_toLp_mulVec_of_conjTranspose_mul_self {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] {K : Matrix m n ℂ} (hK : Kᴴ * K = 1) (ψ : EuclideanSpace ℂ n) :
    ‖(WithLp.toLp 2 (K *ᵥ ψ.ofLp) : EuclideanSpace ℂ m)‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Matrix.norm_toLp_mulVec_sq_eq, hK, one_mulVec,
    EuclideanSpace.star_dotProduct_self_eq_norm_sq, ← Complex.ofReal_pow, Complex.ofReal_re]
