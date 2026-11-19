/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumMarginal
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Normalize

/-!
# Grouping quantum states after postselection

Postselection weights a classical label by the trace of its unnormalized quantum block.
After observing any function of the label, average the unnormalized blocks under the
original conditional law, then normalize once. This agrees with averaging normalized
blocks under the postselected conditional law on all supported observations.

## Main results

* `quantumMarginalGivenMap_eq_normalize_of_weighted`: the posterior state equals the
  normalized prior conditional average.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped ComplexOrder

variable {ι X Y : Type*} [Fintype ι] [Fintype X] [DecidableEq X]

/-- On a supported observation, the posterior of normalized blocks is the normalized
prior average of the unnormalized blocks on the same observation. -/
theorem quantumMarginalGivenMap_eq_normalize_of_weighted
    (p q : PMF X) {M σ : X → Matrix ι ι ℂ} (hM : ∀ x, (M x).PosSemidef)
    (hσ : ∀ x, IsDensityMatrix (σ x))
    (hstate : ∀ x ∈ q.support, σ x = normalizeDensity (M x))
    {c : ℝ} (hc : ∀ x, (q x).toReal = c * (p x).toReal * (M x).trace.re)
    (f : X → Y) {y : Y} (hy : y ∈ (q.map f).support) :
    quantumMarginalGivenMap q σ f y = normalizeDensity (quantumMarginalGivenMap p M f y) := by
  classical
  let τ := quantumMarginalGivenMap q σ f y
  let B := quantumMarginalGivenMap p M f y
  let d := ((q.map f) y).toReal
  let k := c * ((p.map f) y).toReal
  have hτ : IsDensityMatrix τ := isDensityMatrix_quantumMarginalGivenMap q hσ f y
  have hd : d ≠ 0 :=
    (ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hy) (PMF.apply_ne_top _ _)).ne'
  have hterm (x : X) : (q x).toReal • σ x = c • ((p x).toReal • M x) := by
    calc
      _ = (q x).toReal • normalizeDensity (M x) := by
        by_cases hx : x ∈ q.support
        · rw [hstate x hx]
        · simp [(PMF.apply_eq_zero_iff _ _).mpr hx]
      _ = _ := by
        rw [hc, mul_smul, trace_smul_normalizeDensity (hM x), mul_smul]
  have hmix : d • τ = k • B := by
    change ((q.map f) y).toReal • τ = k • B
    rw [show τ = quantumMarginalGivenMap q σ f y from rfl, smul_quantumMarginalGivenMap]
    simp_rw [hterm]
    rw [← smul_sum, ← smul_quantumMarginalGivenMap p M f y, smul_smul]
  have htrace : d = k * B.trace.re := by
    have h := congrArg (fun H : Matrix ι ι ℂ => H.trace.re) hmix
    simpa only [trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hτ.trace_eq_one, Complex.one_re, mul_one] using h
  have hb : B.trace.re ≠ 0 := fun hB => hd (htrace.trans (by rw [hB, mul_zero]))
  change τ = normalizeDensity B
  apply smul_right_injective (Matrix ι ι ℂ) hd
  change d • τ = d • normalizeDensity B
  rw [hmix, normalizeDensity_apply, smul_smul, htrace, mul_assoc, mul_inv_cancel₀ hb, mul_one]

end Cslib.Quantum
