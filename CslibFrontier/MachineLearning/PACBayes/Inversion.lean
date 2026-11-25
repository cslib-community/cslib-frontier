/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACBayes.KL
import Mathlib.Tactic.Linarith

/-!
# Analytical inversions of the PAC-Bayes-kl bound (Pinsker and fast-rate forms)

Derives explicit risk bounds from the implicit binary-relative-entropy inequality
`binaryKL q p ≤ c` of `CslibFrontier.MachineLearning.PACBayes.KL`
[Seeger2002] [Maurer2004] [TolstikhinSeldin2013], building on the pure `binaryKL` lower bounds
and analytical inversions in `CslibFrontier.Probability.BinaryKL`:

- Pinsker-inverted McAllester form (`measure_pi_exists_pinsker_risk_gt_of_binaryKL`) with
  denominator `2 * m` (`log ((m + 1) / δ) / (2 * m)`).
- Sharp quadratic fast-rate bound (`measure_pi_exists_fastRate_risk_gt_of_binaryKL`):
  `𝔼_Q L_D ≤ q + c + √(c² + 2 q c)`.
- Relaxed square-root fast-rate bound (`measure_pi_exists_tolstikhin_risk_gt_of_binaryKL`):
  `𝔼_Q L_D ≤ q + √(2 q c) + 2 c` [TolstikhinSeldin2013].
- Realizable zero-empirical-risk corollary (`measure_pi_exists_zero_risk_gt_of_binaryKL`):
  `𝔼_Q L_D ≤ 1 - exp (-c) ≤ c`.

All four handle the boundary `p = 1` (where `binaryKL` takes a finite junk value) via the shared
almost-everywhere boundary lemma `Cslib.MachineLearning.PACBayes.ae_forall_empiricalRisk_eq` from
`CslibFrontier.MachineLearning.PACBayes.KL`.

## Main results

* `Cslib.MachineLearning.PACBayes.measure_pi_exists_pinsker_risk_gt_of_binaryKL`: explicit
  Pinsker inversion of the PAC-Bayes-kl bound (denominator `2 * m`).
* `Cslib.MachineLearning.PACBayes.measure_pi_exists_fastRate_risk_gt_of_binaryKL`: sharp
  quadratic fast-rate inversion of the PAC-Bayes-kl bound (`q + c + √(c² + 2 q c)`).
* `Cslib.MachineLearning.PACBayes.measure_pi_exists_tolstikhin_risk_gt_of_binaryKL`: relaxed
  Tolstikhin–Seldin inversion (`q + √(2 q c) + 2 c`).
* `Cslib.MachineLearning.PACBayes.measure_pi_exists_zero_risk_gt_of_binaryKL`: explicit
  realizable `1 - exp (-c)` bound from PAC-Bayes-kl.

## References

Exact section and page locators below are unverified against primary PDFs (pending an
outside-fleet source check).

* [M. Seeger, *PAC-Bayesian generalisation error bounds for Gaussian process
  classification*][Seeger2002] (locator unverified)
* [A. Maurer, *A note on the PAC Bayesian theorem*][Maurer2004] (locator unverified)
* [I. O. Tolstikhin, Y. Seldin, *PAC-Bayes-Empirical-Bernstein Inequality*][TolstikhinSeldin2013]
  (locator unverified)
-/

public section

namespace Cslib.MachineLearning.PACBayes

open MeasureTheory InformationTheory Real Set
open Cslib.Probability
open scoped ENNReal

variable {ι Z : Type*} [MeasurableSpace Z] {D : Measure Z} [IsProbabilityMeasure D]
  {ℓ : ι → Z → ℝ} [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]

private theorem integral_empiricalRisk_eq_one_of_integral_trueRisk_eq_one {m : ℕ}
    (hℓ01 : ∀ i z, ℓ i z ∈ Icc (0 : ℝ) 1) {S : Fin m → Z}
    (hS : ∀ i, trueRisk ℓ D i = 1 → empiricalRisk ℓ S i = 1)
    {Q : Measure ι} [IsProbabilityMeasure Q] (h1 : ∫ i, trueRisk ℓ D i ∂Q = 1) :
    ∫ i, empiricalRisk ℓ S i ∂Q = 1 := by
  have hint_tr : Integrable (trueRisk ℓ D) Q :=
    Integrable.of_mem_Icc 0 1 (measurable_of_countable _).aemeasurable
      (ae_of_all _ fun i => trueRisk_mem_Icc ℓ D (hℓ01 i))
  have hzero : ∫ i, (1 - trueRisk ℓ D i) ∂Q = 0 := by
    rw [integral_sub (integrable_const 1) hint_tr, integral_const, probReal_univ, smul_eq_mul,
      one_mul, h1, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun i => sub_nonneg.2 (trueRisk_mem_Icc ℓ D (hℓ01 i)).2) ((integrable_const 1).sub hint_tr)).1
    hzero
  rw [integral_congr_ae (g := fun _ => (1 : ℝ)) (by
    filter_upwards [hae] with i hi
    exact hS i (by simp only [Pi.zero_apply] at hi; linarith))]
  simp

private theorem integral_risk_mem_Icc {g : ι → ℝ} (hg : ∀ i, g i ∈ Icc (0 : ℝ) 1)
    (Q : Measure ι) [IsProbabilityMeasure Q] :
    ∫ i, g i ∂Q ∈ Icc (0 : ℝ) 1 :=
  ⟨integral_nonneg fun i => (hg i).1,
    (integral_mono (Integrable.of_mem_Icc 0 1 (measurable_of_countable _).aemeasurable
      (ae_of_all _ hg)) (integrable_const 1) fun i => (hg i).2).trans_eq (by simp)⟩

omit [Countable ι] [MeasurableSingletonClass ι] in
private theorem kl_rhs_nonneg {m : ℕ} (hm : 0 < m) (P Q : Measure ι)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ ((klDiv Q P).toReal + log ((m + 1) / δ)) / m :=
  div_nonneg (add_nonneg ENNReal.toReal_nonneg
    (log_nonneg ((one_le_div hδ).2 (by linarith [Nat.cast_nonneg (α := ℝ) m]))))
    (Nat.cast_pos.2 hm).le

/-- Shared almost-everywhere reduction from a risk inequality on `(q, p, c)` to the PAC-Bayes-kl
bound, excluding the `p = 1` boundary via `ae_forall_empiricalRisk_eq`. -/
private theorem measure_pi_exists_risk_gt_of_binaryKL_step (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) (P : Measure ι)
    [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) (E : ℝ → ℝ → ℝ → Prop)
    (hstep : ∀ q p c : ℝ, q ∈ Icc (0 : ℝ) 1 → p ∈ Icc (0 : ℝ) 1 → 0 ≤ c →
      (p = 1 → q = 1) → E q p c → c < binaryKL q p) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure ι, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧
        E (∫ i, empiricalRisk ℓ S i ∂Q) (∫ i, trueRisk ℓ D i ∂Q)
          (((klDiv Q P).toReal + log ((m + 1) / δ)) / m)} ≤ ENNReal.ofReal δ := by
  rcases le_or_gt δ 1 with hδ1 | hδ1
  · refine le_trans (measure_mono_ae ?_)
      (measure_pi_exists_binaryKL_integral_risk_gt hℓ hℓ01 hm P hδ)
    filter_upwards [ae_forall_empiricalRisk_eq hℓ hℓ01 hm] with S hS hbad
    obtain ⟨Q, hQ, hQP, hE⟩ := hbad
    refine ⟨Q, hQ, hQP, hstep _ _ _
      (integral_risk_mem_Icc (fun i => empiricalRisk_mem_Icc ℓ S (hℓ01 i)) Q)
      (integral_risk_mem_Icc (fun i => trueRisk_mem_Icc ℓ D (hℓ01 i)) Q)
      (kl_rhs_nonneg hm P Q hδ hδ1)
      (fun hp1 => integral_empiricalRisk_eq_one_of_integral_trueRisk_eq_one hℓ01
        (fun i hi => (hS i).2 hi) hp1)
      hE⟩
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 hδ1.le)

/-- **Boundary-qualified Pinsker conversion of the PAC-Bayes-kl bound** [Seeger2002] [Maurer2004]
(locators unverified): for `m ≥ 1` and `0 < δ`, with probability at least `1 - δ`, every posterior
`Q` with `KL(Q ‖ P) < ∞` satisfies
`𝔼_Q L_D ≤ 𝔼_Q L_S + √((KL(Q ‖ P) + log ((m + 1) / δ)) / (2 * m))`.
(Denominator `2 * m`, replacing `2 * (m - 1)` from McAllester's form in
`CslibFrontier.MachineLearning.PACBayes.Basic`.) -/
theorem measure_pi_exists_pinsker_risk_gt_of_binaryKL (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) (P : Measure ι)
    [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure ι, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ ∫ i, empiricalRisk ℓ S i ∂Q +
        sqrt (((klDiv Q P).toReal + log ((m + 1) / δ)) / (2 * m)) <
        ∫ i, trueRisk ℓ D i ∂Q} ≤ ENNReal.ofReal δ := by
  simp_rw [show ∀ Q : Measure ι, ((klDiv Q P).toReal + log ((m + 1) / δ)) / (2 * m) =
    (((klDiv Q P).toReal + log ((m + 1) / δ)) / m) / 2 from fun _ => by ring]
  refine measure_pi_exists_risk_gt_of_binaryKL_step hℓ hℓ01 hm P hδ
    (fun q p c => q + sqrt (c / 2) < p) fun q p c hq hp _ h1 hlt => ?_
  have hp0 : 0 < p := lt_of_le_of_lt (add_nonneg hq.1 (sqrt_nonneg _)) hlt
  have hp1 : p < 1 := hp.2.lt_of_ne fun hpeq => by linarith [h1 hpeq, sqrt_nonneg (c / 2)]
  by_contra! hkle
  linarith [(abs_le.mp (abs_sub_le_sqrt_of_binaryKL_le hq hp0 hp1 hkle)).2]

/-- **Sharp quadratic fast-rate inversion of PAC-Bayes-kl** [TolstikhinSeldin2013] (locator
unverified): setting `c = (KL(Q ‖ P) + log ((m + 1) / δ)) / m`, with probability at least `1 - δ`,
every posterior `Q` with `KL(Q ‖ P) < ∞` satisfies
`𝔼_Q L_D ≤ 𝔼_Q L_S + c + √(c ^ 2 + 2 * (𝔼_Q L_S) * c)`. -/
theorem measure_pi_exists_fastRate_risk_gt_of_binaryKL (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) (P : Measure ι)
    [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure ι, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧
        let q := ∫ i, empiricalRisk ℓ S i ∂Q
        let c := ((klDiv Q P).toReal + log ((m + 1) / δ)) / m
        q + c + sqrt (c ^ 2 + 2 * q * c) < ∫ i, trueRisk ℓ D i ∂Q} ≤ ENNReal.ofReal δ := by
  refine measure_pi_exists_risk_gt_of_binaryKL_step hℓ hℓ01 hm P hδ
    (fun q p c => q + c + sqrt (c ^ 2 + 2 * q * c) < p) fun q p c hq hp hc h1 hlt => ?_
  have hp1 : p < 1 := hp.2.lt_of_ne fun hpeq => by
    linarith [h1 hpeq, sqrt_nonneg (c ^ 2 + 2 * q * c)]
  by_contra! hkle
  linarith [le_add_add_sqrt_of_binaryKL_le hq.1 hp1 hc hkle]

/-- **Relaxed square-root fast-rate PAC-Bayes bound** [TolstikhinSeldin2013] (locator unverified):
`𝔼_Q L_D ≤ 𝔼_Q L_S + √(2 * 𝔼_Q L_S * c) + 2 * c` where
`c = (KL(Q ‖ P) + log ((m + 1) / δ)) / m`. -/
theorem measure_pi_exists_tolstikhin_risk_gt_of_binaryKL (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) (P : Measure ι)
    [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure ι, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧
        let q := ∫ i, empiricalRisk ℓ S i ∂Q
        let c := ((klDiv Q P).toReal + log ((m + 1) / δ)) / m
        q + sqrt (2 * q * c) + 2 * c < ∫ i, trueRisk ℓ D i ∂Q} ≤ ENNReal.ofReal δ := by
  refine measure_pi_exists_risk_gt_of_binaryKL_step hℓ hℓ01 hm P hδ
    (fun q p c => q + sqrt (2 * q * c) + 2 * c < p) fun q p c hq hp hc h1 hlt => ?_
  have hp1 : p < 1 := hp.2.lt_of_ne fun hpeq => by
    linarith [h1 hpeq, sqrt_nonneg (2 * q * c)]
  by_contra! hkle
  linarith [le_add_sqrt_two_mul_add_two_mul_of_binaryKL_le hq.1 hp1 hc hkle]

/-- **Realizable `1 - exp (-c)` corollary of the PAC-Bayes-kl bound**: when `𝔼_Q L_S = 0`,
`𝔼_Q L_D ≤ 1 - exp (-((KL(Q ‖ P) + log ((m + 1) / δ)) / m))` (strictly tighter than `c`). -/
theorem measure_pi_exists_zero_risk_gt_of_binaryKL (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) (P : Measure ι)
    [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure ι, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ ∫ i, empiricalRisk ℓ S i ∂Q = 0 ∧
        1 - exp (-(((klDiv Q P).toReal + log ((m + 1) / δ)) / m)) <
          ∫ i, trueRisk ℓ D i ∂Q} ≤ ENNReal.ofReal δ := by
  refine (measure_mono_ae ?_).trans (measure_pi_exists_binaryKL_integral_risk_gt hℓ hℓ01 hm P hδ)
  filter_upwards [ae_forall_empiricalRisk_eq hℓ hℓ01 hm] with S hS ⟨Q, hQ, hQP, hq0, hlt⟩
  have hp := integral_risk_mem_Icc (fun i => trueRisk_mem_Icc ℓ D (hℓ01 i)) Q
  have hp1 : ∫ i, trueRisk ℓ D i ∂Q < 1 := hp.2.lt_of_ne fun hpeq => by
    linarith [integral_empiricalRisk_eq_one_of_integral_trueRisk_eq_one hℓ01
      (fun i hi => (hS i).2 hi) hpeq]
  refine ⟨Q, hQ, hQP, ?_⟩
  rw [hq0]
  by_contra! hkle
  linarith [le_one_sub_exp_neg_of_binaryKL_zero_le hp.1 hp1 hkle]

end Cslib.MachineLearning.PACBayes
