/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropy
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyConvexity

/-!
# Relative entropy under domination of the reference

Increasing the reference in the Loewner order decreases quantum relative entropy.
A positive scalar comparison of two references therefore incurs an additive logarithmic cost.
The latter is the inequality proved and used in [Bavarian, Vidick and Yuen,
Proposition 5.8][BavarianVidickYuen2022].

## Main results

* `relativeEntropy_antitone_reference`: comparison in the Loewner order.
* `relativeEntropy_le_add_log_of_le_smul`: scalar domination of the reference.
* `relativeEntropy_le_neg_log_weight`: the cost of selecting a component of a mixture.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped ComplexOrder MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Quantum relative entropy decreases when its positive semidefinite reference increases
in the Loewner order. This includes singular references and infinite divergence. -/
theorem relativeEntropy_antitone_reference {ρ σ τ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hτ : τ.PosSemidef) (h : σ ≤ τ) :
    relativeEntropy ρ τ ≤ relativeEntropy ρ σ := by
  refine relativeEntropy_le_of_resolvent_le hρ hτ hρ hσ rfl
    (fun hs => hs.trans (SupportLE.of_le hσ h)) fun t ht => ?_
  obtain ⟨X, hX⟩ := (relativeEntropyResolvent_isGreatest ht hρ hτ).1
  change 2 * (Xᴴ * ρ).trace.re - (Xᴴ * (τ * X + t • (X * ρ))).trace.re = _ at hX
  refine le_trans ?_ ((relativeEntropyResolvent_isGreatest ht hρ hσ).2 (Set.mem_range_self X))
  rw [← hX]
  change _ ≤ 2 * (Xᴴ * ρ).trace.re - (Xᴴ * (σ * X + t • (X * ρ))).trace.re
  apply sub_le_sub_left
  have htrace := ((Matrix.le_iff.mp h).conjTranspose_mul_mul_same X).trace_nonneg
  rw [Matrix.mul_sub, Matrix.sub_mul, trace_sub, Complex.nonneg_iff, Complex.sub_re,
    sub_nonneg] at htrace
  simp only [Matrix.mul_add, trace_add, Complex.add_re]
  simpa only [Matrix.mul_assoc] using add_le_add_left htrace.1 (Xᴴ * t • (X * ρ)).trace.re

/-- If `σ ≤ c • τ` for `c > 0`, changing the reference from `σ` to `τ` adds at most
`log c` to the relative entropy of a density matrix. This is the Umegaki-divergence
conclusion of the proof of [Bavarian, Vidick and Yuen, Proposition 5.8][BavarianVidickYuen2022]. -/
theorem relativeEntropy_le_add_log_of_le_smul {ρ σ τ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : σ.PosSemidef) (hτ : τ.PosSemidef)
    {c : ℝ} (hc : 0 < c) (h : σ ≤ c • τ) :
    relativeEntropy ρ τ ≤ relativeEntropy ρ σ + (Real.log c : WithTop ℝ) := by
  have hbound := relativeEntropy_antitone_reference hρ.posSemidef hσ (hτ.smul hc.le) h
  rw [relativeEntropy_smul_right hρ.posSemidef.isHermitian hτ.isHermitian hc,
    hρ.trace_eq_one, Complex.one_re, mul_one] at hbound
  have hcancel : ((-Real.log c : ℝ) : WithTop ℝ) + (Real.log c : WithTop ℝ) = 0 := by
    rw [← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero]
  simpa only [add_assoc, hcancel, add_zero] using add_le_add_left hbound (Real.log c : WithTop ℝ)

/-- A density matrix that occurs with positive weight `p` inside a positive
semidefinite reference is at relative entropy at most `-log p` from that reference. -/
theorem relativeEntropy_le_neg_log_of_smul_le {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : σ.PosSemidef) {p : ℝ} (hp : 0 < p) (h : p • ρ ≤ σ) :
    relativeEntropy ρ σ ≤ ((-Real.log p : ℝ) : WithTop ℝ) := by
  calc
    relativeEntropy ρ σ ≤ relativeEntropy ρ (p • ρ) :=
      relativeEntropy_antitone_reference hρ.posSemidef (hρ.posSemidef.smul hp.le) hσ h
    _ = _ := by
      rw [relativeEntropy_smul_right hρ.posSemidef.isHermitian hρ.posSemidef.isHermitian hp,
        relativeEntropy_self, hρ.trace_eq_one, Complex.one_re, mul_one, zero_add]

/-- The relative entropy from a component to its mixture is at most the negative
logarithm of its positive mixing weight. The other components may be unnormalized. -/
theorem relativeEntropy_le_neg_log_weight {κ : Type*} [Fintype κ]
    (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (σ : κ → Matrix ι ι ℂ)
    (hσ : ∀ k, (σ k).PosSemidef) (k : κ) (hk : 0 < w k) (hkσ : IsDensityMatrix (σ k)) :
    relativeEntropy (σ k) (∑ j, w j • σ j) ≤ ((-Real.log (w k) : ℝ) : WithTop ℝ) := by
  have hterms (j : κ) : (w j • σ j).PosSemidef := (hσ j).smul (hw j)
  exact relativeEntropy_le_neg_log_of_smul_le hkσ (posSemidef_sum _ fun j _ => hterms j) hk
    (single_le_sum (f := fun j => w j • σ j) (fun j _ => (hterms j).nonneg) (mem_univ k))

end Cslib.Quantum
