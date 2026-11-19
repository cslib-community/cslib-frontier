/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.PolarDecomposition
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Kronecker

/-!
# Local unitary overlap of purifications

The coefficient matrix of a bipartite vector factors its left reduced density matrix.
A unitary acting on the right changes only that choice of factor, and optimizing the
overlap of two bipartite vectors becomes the trace-norm variational problem. This is the
finite-dimensional purification comparison used in
[Bavarian, Vidick and Yuen, Theorem 5.11][BavarianVidickYuen2022].

## Main results

* `exists_localUnitary_of_partialTraceRight_eq`: exact local alignment for equal left reductions.
* `exists_localUnitary_inner_eq_rootFidelity`: a local unitary attains the root fidelity.
* `inner_localUnitary_re_le_rootFidelity`: every local unitary obeys the fidelity upper bound.
-/

public section

namespace Cslib.Quantum

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- View the coordinates of a bipartite vector as a rectangular matrix. -/
@[expose] def coefficients (ψ : EuclideanSpace ℂ (ι × κ)) : Matrix ι κ ℂ :=
  fun i k => ψ.ofLp (i, k)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- The left reduced density is the row Gram matrix of the coefficient matrix. -/
theorem partialTraceRight_pureState_eq_coefficients (ψ : EuclideanSpace ℂ (ι × κ)) :
    partialTraceRight (pureState ψ) = coefficients ψ * (coefficients ψ)ᴴ := by
  ext i j
  simp only [partialTraceRight_apply, pureState_apply, Matrix.mul_apply, conjTranspose_apply,
    coefficients]

omit [DecidableEq κ] in
/-- Acting on the right factor is right multiplication by the transpose on coefficients. -/
theorem coefficients_one_kronecker (U : Matrix κ κ ℂ) (ψ : EuclideanSpace ℂ (ι × κ)) :
    coefficients (WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ ψ.ofLp)) =
      coefficients ψ * Uᵀ := by
  ext i k
  change (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ ψ.ofLp) (i, k) = _
  rw [one_kronecker_mulVec_apply]
  simp only [mulVec, dotProduct, Matrix.mul_apply, coefficients, transpose_apply, mul_comm]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The inner product of two bipartite vectors is the trace pairing of their coefficients. -/
theorem inner_eq_trace_coefficients (ψ φ : EuclideanSpace ℂ (ι × κ)) :
    inner ℂ ψ φ = ((coefficients ψ)ᴴ * coefficients φ).trace := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, Matrix.trace,
    Fintype.sum_prod_type, Matrix.diag_apply, Matrix.mul_apply, conjTranspose_apply, coefficients]
  simp only [mul_comm]
  rw [Finset.sum_comm]

/-- Two purifications with equal left marginal can be aligned by a unitary on the right. -/
theorem exists_localUnitary_of_partialTraceRight_eq (ψ φ : EuclideanSpace ℂ (ι × κ))
    (h : partialTraceRight (pureState ψ) = partialTraceRight (pureState φ)) :
    ∃ U ∈ unitaryGroup κ ℂ,
      WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ ψ.ofLp) = φ := by
  simp only [partialTraceRight_pureState_eq_coefficients] at h
  have hGram : ((coefficients ψ)ᴴ)ᴴ * (coefficients ψ)ᴴ =
      ((coefficients φ)ᴴ)ᴴ * (coefficients φ)ᴴ := by
    simpa only [conjTranspose_conjTranspose] using h
  obtain ⟨V, hV, he⟩ :=
    exists_unitary_mul_eq_of_conjTranspose_mul_eq (coefficients ψ)ᴴ (coefficients φ)ᴴ hGram
  have hUV : Vᴴᵀ ∈ unitaryGroup κ ℂ := by
    rw [transpose_mem_unitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose,
      conjTranspose_conjTranspose]
    exact (mem_unitaryGroup_iff').mp hV
  refine ⟨Vᴴᵀ, hUV, ?_⟩
  have ha := congrArg Matrix.conjTranspose he
  simp only [conjTranspose_mul, conjTranspose_conjTranspose] at ha
  have hcoeff := coefficients_one_kronecker (ι := ι) Vᴴᵀ ψ
  rw [transpose_transpose, ha] at hcoeff
  ext ⟨i, k⟩
  exact congrFun (congrFun hcoeff i) k

/-- Root fidelity, the trace norm of the product of the positive square roots.
This convention leaves fidelity unsquared. -/
noncomputable def rootFidelity (ρ σ : Matrix ι ι ℂ) : ℝ :=
  (CFC.sqrt ρ * CFC.sqrt σ).traceNorm

/-- The trace norm of the rectangular cross pairing equals the root fidelity
of the two left reductions. -/
theorem traceNorm_coefficients_cross (ψ φ : EuclideanSpace ℂ (ι × κ)) :
    ((coefficients ψ)ᴴ * coefficients φ).traceNorm =
      rootFidelity (partialTraceRight (pureState ψ)) (partialTraceRight (pureState φ)) := by
  let M := coefficients ψ
  let N := coefficients φ
  let A := CFC.sqrt (M * Mᴴ)
  let B := CFC.sqrt (N * Nᴴ)
  have hA : Aᴴ = A := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian.eq
  have hB : Bᴴ = B := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian.eq
  have hAsq : A * A = M * Mᴴ :=
    CFC.sqrt_mul_sqrt_self _ (posSemidef_self_mul_conjTranspose M).nonneg
  have hBsq : B * B = N * Nᴴ :=
    CFC.sqrt_mul_sqrt_self _ (posSemidef_self_mul_conjTranspose N).nonneg
  have h₁ : (Mᴴ * N).traceNorm = (A * N).traceNorm := by
    unfold Matrix.traceNorm
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc M Mᴴ, ← hAsq, Matrix.mul_assoc]
  have h₂ : (A * N).traceNorm = (A * B).traceNorm := by
    rw [← traceNorm_conjTranspose (A * N), ← traceNorm_conjTranspose (A * B)]
    unfold Matrix.traceNorm
    simp only [conjTranspose_conjTranspose, conjTranspose_mul, hA, hB, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc N Nᴴ, ← hBsq, Matrix.mul_assoc]
  rw [partialTraceRight_pureState_eq_coefficients, partialTraceRight_pureState_eq_coefficients]
  exact h₁.trans h₂

omit [DecidableEq κ] in
private theorem inner_localUnitary_eq_trace (ψ φ : EuclideanSpace ℂ (ι × κ)) (U : Matrix κ κ ℂ) :
    inner ℂ (WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ ψ.ofLp)) φ =
      (Uᵀᴴ * ((coefficients ψ)ᴴ * coefficients φ)).trace := by
  rw [inner_eq_trace_coefficients, coefficients_one_kronecker, conjTranspose_mul, Matrix.mul_assoc]

/-- Uhlmann's variational upper bound for the real overlap of fixed purifications. -/
theorem inner_localUnitary_re_le_rootFidelity (ψ φ : EuclideanSpace ℂ (ι × κ))
    (U : Matrix κ κ ℂ) (hU : U ∈ unitaryGroup κ ℂ) :
    (inner ℂ (WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ ψ.ofLp)) φ).re ≤
      rootFidelity (partialTraceRight (pureState ψ)) (partialTraceRight (pureState φ)) := by
  rw [inner_localUnitary_eq_trace, ← traceNorm_coefficients_cross]
  exact re_trace_conjTranspose_mul_le_traceNorm _ _ (transpose_mem_unitaryGroup_iff.mpr hU)

/-- Uhlmann's overlap theorem for purifications on the same bipartite space. -/
theorem exists_localUnitary_inner_eq_rootFidelity (ψ φ : EuclideanSpace ℂ (ι × κ)) :
    ∃ U ∈ unitaryGroup κ ℂ,
      inner ℂ (WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ ψ.ofLp)) φ =
        (rootFidelity (partialTraceRight (pureState ψ))
          (partialTraceRight (pureState φ)) : ℂ) := by
  let A := (coefficients ψ)ᴴ * coefficients φ
  obtain ⟨U, hU, h⟩ := A.exists_unitary_polar
  refine ⟨Uᵀ, transpose_mem_unitaryGroup_iff.mpr hU, ?_⟩
  rw [inner_localUnitary_eq_trace, transpose_transpose,
    trace_conjTranspose_mul_eq_traceNorm_of_polar _ _ hU h, traceNorm_coefficients_cross]

/-- The real-part equality of the attaining unitary. -/
theorem exists_localUnitary_inner_re_eq_rootFidelity (ψ φ : EuclideanSpace ℂ (ι × κ)) :
    ∃ U ∈ unitaryGroup κ ℂ,
      (inner ℂ (WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ ψ.ofLp)) φ).re =
        rootFidelity (partialTraceRight (pureState ψ)) (partialTraceRight (pureState φ)) := by
  obtain ⟨U, hU, h⟩ := exists_localUnitary_inner_eq_rootFidelity ψ φ
  exact ⟨U, hU, by simpa only [Complex.ofReal_re] using congrArg Complex.re h⟩

/-- The local unitary furnished by Uhlmann's theorem has a squared vector error of
twice one minus the root fidelity for unit purifications. -/
theorem exists_localUnitary_norm_sub_sq_eq (ψ φ : EuclideanSpace ℂ (ι × κ))
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    ∃ U ∈ unitaryGroup κ ℂ,
      ‖WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ ψ.ofLp) - φ‖ ^ 2 =
        2 * (1 - rootFidelity (partialTraceRight (pureState ψ))
          (partialTraceRight (pureState φ))) := by
  obtain ⟨U, hU, hoverlap⟩ := exists_localUnitary_inner_re_eq_rootFidelity ψ φ
  have h1 : (1 : Matrix ι ι ℂ) ⊗ₖ U ∈ unitaryGroup (ι × κ) ℂ := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_kronecker,
      conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul,
      show Uᴴ * U = 1 from (mem_unitaryGroup_iff').mp hU, one_kronecker_one]
  have hn : ‖(WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ ψ.ofLp) :
      EuclideanSpace ℂ (ι × κ))‖ = ‖ψ‖ :=
    (mem_unitaryGroup_iff_forall_norm_toEuclideanCLM _).mp h1 ψ
  refine ⟨U, hU, ?_⟩
  have hr : RCLike.re (inner ℂ
      (WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ ψ.ofLp)) φ) = _ := hoverlap
  rw [norm_sub_sq (𝕜 := ℂ), hn, hψ, hφ, hr]
  change (1 : ℝ) ^ 2 - 2 * _ + 1 ^ 2 = _
  ring

end Cslib.Quantum
