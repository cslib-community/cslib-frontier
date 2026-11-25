/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.PurificationOverlap
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PowersStormer

/-!
# Trace distance bounds for fidelity and purification alignment

The lower Fuchs–van de Graaf inequality follows from the Powers–Størmer square-root bound.
For the upper inequality, polar alignment makes the overlap of the square-root factors
attain fidelity, and Cauchy–Schwarz bounds the trace norm of the difference.
Combining it with Uhlmann's theorem controls the vector error after applying a unitary on the
purifying system. This is the direction needed in
[Bavarian, Vidick and Yuen, equation (28) and Theorem 5.11][BavarianVidickYuen2022].

## Main results

* `one_sub_rootFidelity_le_traceDistance`: the lower Fuchs–van de Graaf inequality.
* `traceDistance_le_sqrt_one_sub_rootFidelity_sq`: the upper Fuchs–van de Graaf inequality.
* `exists_localUnitary_norm_sub_sq_le_traceNorm`: the squared error of purification alignment
  is at most the trace norm of the difference of the reduced states.
-/

public section

namespace Cslib.Quantum

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Trace distance, with the factor of one half used for distinguishing states. -/
@[expose] noncomputable def traceDistance (ρ σ : Matrix ι ι ℂ) : ℝ :=
  (ρ - σ).traceNorm / 2

/-- The lower Fuchs–van de Graaf inequality for normalized, possibly singular states. -/
theorem one_sub_rootFidelity_le_traceDistance {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    1 - rootFidelity ρ σ ≤ traceDistance ρ σ := by
  let P := CFC.sqrt ρ
  let Q := CFC.sqrt σ
  have hp : P * P = ρ := CFC.sqrt_mul_sqrt_self _ hρ.posSemidef.nonneg
  have hq : Q * Q = σ := CFC.sqrt_mul_sqrt_self _ hσ.posSemidef.nonneg
  have h := trace_sub_mul_self_le_traceNorm_mul_self_sub P Q
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ))
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ))
  rw [hp, hq, sub_mul, mul_sub, mul_sub, hp, hq, trace_sub, trace_sub, trace_sub,
    hρ.trace_eq_one, hσ.trace_eq_one, trace_mul_comm Q P] at h
  simp only [Complex.sub_re, Complex.one_re] at h
  have hf := re_trace_conjTranspose_mul_le_traceNorm (P * Q) 1 (one_mem _)
  rw [conjTranspose_one, Matrix.one_mul] at hf
  change (P * Q).trace.re ≤ rootFidelity ρ σ at hf
  unfold traceDistance; linarith

omit [DecidableEq ι] in
private theorem re_trace_mul_conjTranspose_le (A B : Matrix ι ι ℂ) :
    (A * Bᴴ).trace.re ≤
      Real.sqrt (A * Aᴴ).trace.re * Real.sqrt (B * Bᴴ).trace.re := by
  let a : EuclideanSpace ℂ (ι × ι) := WithLp.toLp 2 fun ij => A ij.1 ij.2
  let b : EuclideanSpace ℂ (ι × ι) := WithLp.toLp 2 fun ij => B ij.1 ij.2
  have hn (x : EuclideanSpace ℂ (ι × ι)) :
      ‖x‖ = Real.sqrt ((coefficients x) * (coefficients x)ᴴ).trace.re := by
    rw [trace_mul_comm, ← inner_eq_trace_coefficients]
    change ‖x‖ = Real.sqrt (RCLike.re (inner ℂ x x))
    rw [← norm_sq_eq_re_inner, Real.sqrt_sq (norm_nonneg _)]
  have h := re_inner_le_norm (𝕜 := ℂ) b a
  change (inner ℂ b a).re ≤ _ at h
  rw [inner_eq_trace_coefficients, trace_mul_comm, hn b, hn a] at h
  exact (show (A * Bᴴ).trace.re ≤ _ from h).trans_eq (mul_comm _ _)

private theorem re_trace_unitary_mul_conjTranspose_le (U A B : Matrix ι ι ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) :
    (Uᴴ * (A * Bᴴ)).trace.re ≤
      Real.sqrt (A * Aᴴ).trace.re * Real.sqrt (B * Bᴴ).trace.re := by
  rw [← Matrix.mul_assoc]
  simpa only [show ((Uᴴ * A) * (Uᴴ * A)ᴴ).trace = (A * Aᴴ).trace by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc A Aᴴ,
      trace_mul_comm Uᴴ, Matrix.mul_assoc, show U * Uᴴ = 1 from mem_unitaryGroup_iff.mp hU,
      Matrix.mul_one]]
    using re_trace_mul_conjTranspose_le (Uᴴ * A) B

private theorem traceNorm_gram_sub_le (A B : Matrix ι ι ℂ) :
    (A * Aᴴ - B * Bᴴ).traceNorm ≤
      Real.sqrt (((A - B) * (A - B)ᴴ).trace.re) *
        Real.sqrt (((A + B) * (A + B)ᴴ).trace.re) := by
  obtain ⟨U, hU, h, _⟩ := traceNorm_eq_max_re_trace (A * Aᴴ - B * Bᴴ)
  have h₁ := re_trace_unitary_mul_conjTranspose_le U (A - B) (A + B) hU
  have h₂ := (re_trace_unitary_mul_conjTranspose_le U (A + B) (A - B) hU).trans_eq (mul_comm _ _)
  have hr := congrArg (fun M : Matrix ι ι ℂ => M.trace.re)
    (show Uᴴ * ((A - B) * (A + B)ᴴ) + Uᴴ * ((A + B) * (A - B)ᴴ) =
      Uᴴ * (A * Aᴴ - B * Bᴴ) + Uᴴ * (A * Aᴴ - B * Bᴴ) by
      rw [conjTranspose_add, conjTranspose_sub]; noncomm_ring)
  simp only [trace_add, Complex.add_re] at hr; linarith

/-- The upper Fuchs–van de Graaf inequality for finite, possibly singular density matrices. -/
theorem traceDistance_le_sqrt_one_sub_rootFidelity_sq {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    traceDistance ρ σ ≤ Real.sqrt (1 - rootFidelity ρ σ ^ 2) := by
  let P := CFC.sqrt ρ
  let Q := CFC.sqrt σ
  have hP : Pᴴ = P := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).isHermitian.eq
  have hQ : Qᴴ = Q := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)).isHermitian.eq
  obtain ⟨U, hU, hF, _⟩ := traceNorm_eq_max_re_trace (P * Q)
  change (Uᴴ * (P * Q)).trace.re = rootFidelity ρ σ at hF
  let A := P * U
  have hA : A * Aᴴ = ρ := by
    rw [show A = P * U from rfl, conjTranspose_mul, hP, ← Matrix.mul_assoc, Matrix.mul_assoc P,
      show U * Uᴴ = 1 from mem_unitaryGroup_iff.mp hU, Matrix.mul_one]
    exact CFC.sqrt_mul_sqrt_self _ hρ.posSemidef.nonneg
  have hB : Q * Qᴴ = σ := by rw [hQ]; exact CFC.sqrt_mul_sqrt_self _ hσ.posSemidef.nonneg
  have hf : (Q * Aᴴ).trace.re = rootFidelity ρ σ := by
    rw [trace_mul_comm]; simpa only [A, conjTranspose_mul, hP, Matrix.mul_assoc] using hF
  have h'f : (A * Qᴴ).trace.re = rootFidelity ρ σ := by
    rw [← conjTranspose_conjTranspose (A * Qᴴ), trace_conjTranspose, Complex.star_def,
      Complex.conj_re, conjTranspose_mul, conjTranspose_conjTranspose, hf]
  have hsub : ((A - Q) * (A - Q)ᴴ).trace.re = 2 - 2 * rootFidelity ρ σ := by
    rw [conjTranspose_sub, sub_mul, mul_sub, mul_sub, trace_sub, trace_sub, trace_sub,
      Complex.sub_re, Complex.sub_re, Complex.sub_re, hA, hB, hf, h'f,
      hρ.trace_eq_one, hσ.trace_eq_one, Complex.one_re]; ring
  have hadd : ((A + Q) * (A + Q)ᴴ).trace.re = 2 + 2 * rootFidelity ρ σ := by
    rw [conjTranspose_add, add_mul, mul_add, mul_add, trace_add, trace_add, trace_add,
      Complex.add_re, Complex.add_re, Complex.add_re, hA, hB, hf, h'f,
      hρ.trace_eq_one, hσ.trace_eq_one, Complex.one_re]; ring
  have h := traceNorm_gram_sub_le A Q
  rw [hA, hB, hsub, hadd,
    ← Real.sqrt_mul (hsub ▸ (Complex.nonneg_iff.mp
      (posSemidef_self_mul_conjTranspose (A - Q)).trace_nonneg).1),
    show (2 - 2 * rootFidelity ρ σ) * (2 + 2 * rootFidelity ρ σ) =
      4 * (1 - rootFidelity ρ σ ^ 2) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  unfold traceDistance; linarith

/-- Two unit purifications on the same space can be aligned with squared vector error
bounded by the trace norm of the marginal difference. -/
theorem exists_localUnitary_norm_sub_sq_le_traceNorm (ψ φ : EuclideanSpace ℂ (ι × κ))
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    ∃ U ∈ unitaryGroup κ ℂ,
      ‖WithLp.toLp 2 (((1 : Matrix ι ι ℂ) ⊗ₖ U) *ᵥ ψ.ofLp) - φ‖ ^ 2 ≤
        (partialTraceRight (pureState ψ) - partialTraceRight (pureState φ)).traceNorm := by
  obtain ⟨U, hU, h⟩ := exists_localUnitary_norm_sub_sq_eq ψ φ hψ hφ
  refine ⟨U, hU, h.le.trans ?_⟩
  have hf := one_sub_rootFidelity_le_traceDistance
    (isDensityMatrix_pureState hψ).partialTraceRight
    (isDensityMatrix_pureState hφ).partialTraceRight
  unfold traceDistance at hf; linarith

end Cslib.Quantum
