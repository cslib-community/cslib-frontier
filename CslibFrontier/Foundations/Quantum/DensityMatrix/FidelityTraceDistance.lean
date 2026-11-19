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
Combining it with Uhlmann's theorem controls the vector error after applying a unitary on the
purifying system. This is the direction needed in
[Bavarian, Vidick and Yuen, equation (28) and Theorem 5.11][BavarianVidickYuen2022].

## Main results

* `one_sub_rootFidelity_le_traceDistance`: the lower Fuchs–van de Graaf inequality.
* `exists_localUnitary_norm_sub_sq_le_traceNorm`: the squared error of purification alignment
  is at most the trace norm of the difference of the reduced states.
-/

public section

namespace Cslib.Quantum

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Trace distance, with the factor of one half used for distinguishing states. -/
noncomputable def traceDistance (ρ σ : Matrix ι ι ℂ) : ℝ :=
  (ρ - σ).traceNorm / 2

/-- The lower Fuchs–van de Graaf inequality for normalized, possibly singular states. -/
theorem one_sub_rootFidelity_le_traceDistance {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    1 - rootFidelity ρ σ ≤ traceDistance ρ σ := by
  let P := CFC.sqrt ρ
  let Q := CFC.sqrt σ
  have hP : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)
  have hQ : Q.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)
  have hp : P * P = ρ := CFC.sqrt_mul_sqrt_self _ hρ.posSemidef.nonneg
  have hq : Q * Q = σ := CFC.sqrt_mul_sqrt_self _ hσ.posSemidef.nonneg
  have h := trace_sub_mul_self_le_traceNorm_mul_self_sub P Q hP hQ
  rw [hp, hq, sub_mul, mul_sub, mul_sub, hp, hq, trace_sub, trace_sub, trace_sub,
    hρ.trace_eq_one, hσ.trace_eq_one, trace_mul_comm Q P] at h
  simp only [Complex.sub_re, Complex.one_re] at h
  have hf := re_trace_conjTranspose_mul_le_traceNorm (P * Q) 1 (one_mem _)
  rw [conjTranspose_one, Matrix.one_mul] at hf
  change (P * Q).trace.re ≤ rootFidelity ρ σ at hf
  unfold traceDistance
  linarith

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
  unfold traceDistance at hf
  linarith

end Cslib.Quantum
