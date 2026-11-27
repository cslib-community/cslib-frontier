/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropy
import CslibFrontier.Foundations.Quantum.DensityMatrix.PartialTracePairing
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyConvexity

/-!
# Data processing under partial trace

Discarding one register can only decrease quantum relative entropy. This is
[Bavarian, Vidick and Yuen, Proposition 5.5][BavarianVidickYuen2022]
(arXiv:1509.07466v2, printed p. 19), in nats and with extended divergence.
The proof compares resolvents by lifting a test matrix on the retained system
with the identity on the discarded system. The statement includes arbitrary finite positive
semidefinite inputs, so normalization and invertibility are unnecessary.

## Main results

* `relativeEntropy_partialTraceRight_le`, `relativeEntropy_partialTraceLeft_le`:
  relative entropy is monotone under partial trace.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped ComplexOrder Kronecker MatrixOrder

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Support inclusion persists on the retained system after tracing out the other system. -/
theorem SupportLE.partialTraceRight {ρ σ : Matrix (ι × κ) (ι × κ) ℂ}
    (h : SupportLE ρ σ) (hσ : σ.PosSemidef) :
    SupportLE (partialTraceRight ρ) (partialTraceRight σ) := by
  rw [partialTraceRight_eq_sum_submatrix, partialTraceRight_eq_sum_submatrix]
  have hsum := SupportLE.sum_smul (fun _ : κ => (1 : ℝ)) (fun _ => zero_le_one)
    (fun k => hσ.submatrix (fun i => (i, k)))
    (fun k => h.submatrix hσ (fun i => (i, k)))
  simpa only [one_smul] using hsum

variable [DecidableEq ι] [DecidableEq κ]

private theorem relativeEntropyResolvent_partialTraceRight_le
    {ρ σ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {t : ℝ} (ht : 0 < t) :
    relativeEntropyResolvent t (partialTraceRight ρ) (partialTraceRight σ) ≤
      relativeEntropyResolvent t ρ σ := by
  let Xρ := partialTraceRight ρ
  let Xσ := partialTraceRight σ
  obtain ⟨X, hX⟩ := (relativeEntropyResolvent_isGreatest ht
    (posSemidef_partialTraceRight hρ) (posSemidef_partialTraceRight hσ)).1
  let Y := X ⊗ₖ (1 : Matrix κ κ ℂ)
  have htrace (A : Matrix (ι × κ) (ι × κ) ℂ) :
      (Yᴴ * A).trace = (Xᴴ * partialTraceRight A).trace := by
    dsimp only [Y]
    rw [conjTranspose_kronecker, conjTranspose_one, trace_kronecker_one_mul]
  have hvalue : (Yᴴ * (σ * Y + t • (Y * ρ))).trace =
      (Xᴴ * (Xσ * X + t • (X * Xρ))).trace := by
    simp only [Matrix.mul_add, trace_add, Matrix.mul_smul, trace_smul, htrace]
    dsimp only [Y, Xσ, Xρ]
    rw [partialTraceRight_mul_kronecker_one, partialTraceRight_kronecker_one_mul]
  apply (relativeEntropyResolvent_isGreatest ht hρ hσ).2
  refine ⟨Y, ?_⟩
  change 2 * (Yᴴ * ρ).trace.re - (Yᴴ * (σ * Y + t • (Y * ρ))).trace.re = _
  rw [htrace, hvalue]
  exact hX

/-- Relative entropy cannot increase upon discarding the second register. A singular
reference gives finite divergence exactly when the source is supported in it. -/
theorem relativeEntropy_partialTraceRight_le {ρ σ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    relativeEntropy (partialTraceRight ρ) (partialTraceRight σ) ≤ relativeEntropy ρ σ :=
  relativeEntropy_le_of_resolvent_le (posSemidef_partialTraceRight hρ)
    (posSemidef_partialTraceRight hσ) hρ hσ
    (congrArg Complex.re (trace_partialTraceRight ρ))
    (fun hs => hs.partialTraceRight hσ)
    (fun _ ht => relativeEntropyResolvent_partialTraceRight_le hρ hσ ht)

/-- Relative entropy cannot increase upon discarding the first register. -/
theorem relativeEntropy_partialTraceLeft_le {ρ σ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    relativeEntropy (partialTraceLeft ρ) (partialTraceLeft σ) ≤ relativeEntropy ρ σ := by
  let e := Equiv.prodComm ι κ
  have h := relativeEntropy_partialTraceRight_le
    (ρ := reindex e e ρ) (σ := reindex e e σ) (hρ.submatrix _) (hσ.submatrix _)
  rwa [relativeEntropy_reindex e hρ.isHermitian hσ, partialTraceRight_reindex_prodComm,
    partialTraceRight_reindex_prodComm] at h

end Cslib.Quantum
