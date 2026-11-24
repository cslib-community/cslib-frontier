/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACBayes.KL
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analytical inversions of the PAC-Bayes-kl bound (Pinsker and fast-rate forms)

Derives explicit risk bounds from the implicit binary-relative-entropy inequality
`binaryKL q p ≤ c` of `CslibFrontier.MachineLearning.PACBayes.KL`
[Seeger2002] [Maurer2004] [TolstikhinSeldin2013]:

1. **Binary Pinsker inequality (`two_mul_sq_le_binaryKL`).** For `q ∈ [0, 1]` and `p ∈ (0, 1)`,
   `2 * (q - p) ^ 2 ≤ binaryKL q p`, yielding the explicit upper/lower risk inversion
   `|q - p| ≤ √(c / 2)`.
2. **Bernstein / Tolstikhin–Seldin quadratic lower bound (`sub_sq_div_two_mul_le_binaryKL`).** For
   `0 ≤ q ≤ p < 1` (`0 < p`), `(p - q) ^ 2 / (2 * p) ≤ binaryKL q p`. Solving the resulting
   quadratic in `p` yields both the sharp inversion
   `p ≤ q + c + √(c ^ 2 + 2 * q * c)`
   and the standard relaxed square-root bound
   `p ≤ q + √(2 * q * c) + 2 * c` [TolstikhinSeldin2013], interpolating smoothly from `O(c)` when
   `q = 0` to `O(√(q c))` for small `q`.
3. **Zero-empirical-risk inversion (`le_one_sub_exp_neg_of_binaryKL_zero_le`).** For `p ∈ [0, 1)`,
   `binaryKL 0 p = -log (1 - p) ≤ c` gives `p ≤ 1 - exp (-c) ≤ c`.
4. **Boundary-qualified PAC-Bayes-kl corollaries.** Combining these inversions with
   `measure_pi_exists_binaryKL_integral_risk_gt` yields:
   - Pinsker-inverted McAllester form with denominator **`2 * m`** (`log ((m + 1) / δ) / (2 * m)`),
   - Fast-rate quadratic PAC-Bayes bound (`𝔼_Q L_D ≤ q + c + √(c² + 2 q c) ≤ q + √(2 q c) + 2 c`),
   - Realizable `q = 0` corollary (`𝔼_Q L_D ≤ 1 - exp (-c) ≤ c`).
   All three handle the boundary cases `p = 0` and `p = 1` where `binaryKL` takes junk values by
   noting `L_D(i) = 1 ⟹ L_S(i) = 1` almost surely under `D^m`.

## Main results

* `Cslib.MachineLearning.PACBayes.two_mul_sq_le_binaryKL`: Pinsker's inequality for `binaryKL`.
* `Cslib.MachineLearning.PACBayes.sub_sq_div_two_mul_le_binaryKL`: `(p - q)² / (2 p) ≤ kl(q ‖ p)`.
* `Cslib.MachineLearning.PACBayes.le_add_sqrt_two_mul_of_binaryKL_le`:
  `kl(q ‖ p) ≤ c ⟹ p ≤ q + c + √(c² + 2 q c)`.
* `Cslib.MachineLearning.PACBayes.measure_pi_exists_pinsker_risk_gt_of_binaryKL`: explicit
  Pinsker inversion of the PAC-Bayes-kl bound (`denominator 2 * m`).
* `Cslib.MachineLearning.PACBayes.measure_pi_exists_fastRate_risk_gt_of_binaryKL`,
  `Cslib.MachineLearning.PACBayes.measure_pi_exists_tolstikhin_risk_gt_of_binaryKL`:
  explicit fast-rate empirical-variance inversions of the PAC-Bayes-kl bound.
* `Cslib.MachineLearning.PACBayes.measure_pi_exists_zero_risk_gt_of_binaryKL`:
  explicit realizable `1 - exp (-c)` bound from PAC-Bayes-kl.

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

/-! ### Elementary `binaryKL` lower bounds -/

/-- The `p`-derivative of `binaryKL q p` on `(0, 1)` is `(p - q) / (p * (1 - p))`. -/
private theorem hasDerivAt_binaryKL_right {q p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun t => binaryKL q t) ((p - q) / (p * (1 - p))) p := by
  have heq : (fun t => binaryKL q t) =ᶠ[nhds p]
      fun t => q * log (q / t) + (1 - q) * log ((1 - q) / (1 - t)) := by
    filter_upwards [Ioo_mem_nhds hp0 hp1] with t ht
    exact binaryKL_eq_mul_log ht.1 ht.2
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  have hterm1 : HasDerivAt (fun t => q * log (q / t)) (-q / p) p := by
    by_cases hq : q = 0
    · subst hq; simp [hasDerivAt_const]
    · have heq1 : (fun t : ℝ => q * log (q / t)) =ᶠ[nhds p] fun t => q * (log q - log t) := by
        filter_upwards [Ioi_mem_nhds hp0] with t ht
        rw [log_div hq ht.ne']
      refine HasDerivAt.congr_of_eventuallyEq ?_ heq1
      have hd : HasDerivAt (fun t : ℝ => q * (log q - log t)) (q * (-p⁻¹)) p := by
        simpa [sub_eq_add_neg] using ((hasDerivAt_log hp0.ne').neg.const_add (log q)).const_mul q
      convert hd using 1
      field_simp
  have hterm2 : HasDerivAt (fun t => (1 - q) * log ((1 - q) / (1 - t))) ((1 - q) / (1 - p)) p := by
    by_cases hq : 1 - q = 0
    · simp only [hq, zero_mul, zero_div]; exact hasDerivAt_const p 0
    · have heq2 : (fun t : ℝ => (1 - q) * log ((1 - q) / (1 - t))) =ᶠ[nhds p]
          fun t => (1 - q) * (log (1 - q) - log (1 - t)) := by
        filter_upwards [Iio_mem_nhds hp1] with t ht
        rw [log_div hq (sub_pos.mpr ht).ne']
      refine HasDerivAt.congr_of_eventuallyEq ?_ heq2
      have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) p := (hasDerivAt_id p).const_sub 1
      have hlog : HasDerivAt (fun t : ℝ => log (1 - t)) (-1 / (1 - p)) p := h1.log h1p.ne'
      have hd : HasDerivAt (fun t : ℝ => (1 - q) * (log (1 - q) - log (1 - t)))
          ((1 - q) * -(-1 / (1 - p))) p :=
        (hlog.const_sub (log (1 - q))).const_mul (1 - q)
      convert hd using 1
      field_simp
  convert hterm1.add hterm2 using 1
  field_simp
  ring

/-- **Bernoulli Pinsker's inequality**: for `q ∈ [0, 1]` and `p ∈ (0, 1)`,
`2 * (q - p) ^ 2 ≤ binaryKL q p`. -/
theorem two_mul_sq_le_binaryKL {q p : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p) (hp1 : p < 1) :
    2 * (q - p) ^ 2 ≤ binaryKL q p := by
  let g : ℝ → ℝ := fun t => binaryKL q t - 2 * (q - t) ^ 2
  have hg_deriv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt g ((t - q) * (1 - 4 * t * (1 - t)) / (t * (1 - t))) t := by
    intro t ht
    have hq_d : HasDerivAt (fun s : ℝ => 2 * (q - s) ^ 2) (4 * (t - q)) t := by
      have hd : HasDerivAt (fun s : ℝ => q - s) (-1) t := (hasDerivAt_id t).const_sub q
      have hsq : HasDerivAt (fun s : ℝ => (q - s) ^ 2) (2 * (q - t) ^ 1 * (-1)) t := hd.pow 2
      convert hsq.const_mul 2 using 1
      ring
    convert (hasDerivAt_binaryKL_right ht.1 ht.2).sub hq_d using 1
    have h1 : t ≠ 0 := ht.1.ne'
    have h2 : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
    field_simp
  have h1m4 : ∀ t : ℝ, 0 ≤ 1 - 4 * t * (1 - t) := fun t => by
    nlinarith [sq_nonneg (2 * t - 1)]
  rcases eq_or_lt_of_le hq.1 with rfl | hq0
  · -- `q = 0`: `binaryKL 0 p = -log (1 - p)`
    rw [binaryKL_eq_mul_log hp0 hp1, zero_mul, zero_add, sub_zero, one_mul, one_div, log_inv,
      zero_sub, neg_sq]
    let h : ℝ → ℝ := fun t => -log (1 - t) - 2 * t ^ 2
    have hh_c : ContinuousOn h (Icc 0 p) := by
      refine ContinuousOn.sub ?_ (by fun_prop)
      refine ContinuousOn.neg (ContinuousOn.log (by fun_prop) fun t ht => ?_)
      exact (sub_pos.mpr (ht.2.trans_lt hp1)).ne'
    have hh_hd : ∀ t ∈ Ioo 0 p, HasDerivAt h ((1 - 4 * t * (1 - t)) / (1 - t)) t := by
      intro t ht
      have ht1 : 0 < 1 - t := sub_pos.mpr (ht.2.trans hp1)
      have hd1 : HasDerivAt (fun s : ℝ => -log (1 - s)) (-(-1 / (1 - t))) t :=
        (((hasDerivAt_id t).const_sub 1).log ht1.ne').neg
      have hd2 : HasDerivAt (fun s : ℝ => 2 * s ^ 2) (2 * (↑(2 : ℕ) * t ^ (2 - 1) * 1)) t :=
        ((hasDerivAt_id t).pow 2).const_mul (2 : ℝ)
      convert hd1.sub hd2 using 1
      have : 1 - t ≠ 0 := ht1.ne'
      field_simp
      ring
    have h0le := monotoneOn_of_deriv_nonneg (convex_Icc 0 p) hh_c
      (fun t ht => by
        rw [interior_Icc] at ht
        exact (hh_hd t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hh_hd t ht).deriv]
        exact div_nonneg (h1m4 t) (sub_pos.mpr (ht.2.trans hp1)).le)
      ⟨le_rfl, hp0.le⟩ ⟨hp0.le, le_rfl⟩ hp0.le
    dsimp [h] at h0le
    simp only [sub_zero, log_one, neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero] at h0le
    linarith
  · rcases eq_or_lt_of_le hq.2 with rfl | hq1
    · -- `q = 1`: `binaryKL 1 p = -log p`
      rw [binaryKL_eq_mul_log hp0 hp1, sub_self, zero_mul, add_zero, one_mul, one_div, log_inv]
      let h : ℝ → ℝ := fun t => -log t - 2 * (1 - t) ^ 2
      have hh_c : ContinuousOn h (Icc p 1) := by
        refine ContinuousOn.sub ?_ (by fun_prop)
        refine ContinuousOn.neg (ContinuousOn.log continuousOn_id fun t ht => ?_)
        exact (hp0.trans_le ht.1).ne'
      have hh_hd : ∀ t ∈ Ioo p 1, HasDerivAt h (-(1 - 4 * t * (1 - t)) / t) t := fun t ht => by
        have ht0 : 0 < t := hp0.trans ht.1
        have hd1 : HasDerivAt (fun s : ℝ => -log s) (-(t⁻¹)) t := (hasDerivAt_log ht0.ne').neg
        have hd2 : HasDerivAt (fun s : ℝ => 2 * (1 - s) ^ 2)
            (2 * (2 * (1 - t) ^ 1 * (-1))) t :=
          (((hasDerivAt_id t).const_sub 1).pow 2).const_mul 2
        convert hd1.sub hd2 using 1
        field_simp
        ring
      have hh_anti := antitoneOn_of_deriv_nonpos (convex_Icc p 1) hh_c
        (fun t ht => by
          rw [interior_Icc] at ht
          exact (hh_hd t ht).differentiableAt.differentiableWithinAt)
        (fun t ht => by
          rw [interior_Icc] at ht
          rw [(hh_hd t ht).deriv]
          exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (h1m4 t)) (hp0.trans ht.1).le)
        ⟨le_rfl, hp1.le⟩ ⟨hp1.le, le_rfl⟩ hp1.le
      dsimp [h] at hh_anti
      simp only [log_one, neg_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero] at hh_anti
      linarith
    · -- Interior `q ∈ (0, 1)`: compare `p` against `q`.
      rcases le_total q p with hqp | hpq
      · have hmono := monotoneOn_of_deriv_nonneg (convex_Icc q p)
          (fun t ht => (hg_deriv t ⟨hq0.trans_le ht.1, ht.2.trans_lt hp1⟩).continuousAt
            |>.continuousWithinAt)
          (fun t ht => by
            rw [interior_Icc] at ht
            exact (hg_deriv t ⟨hq0.trans ht.1, ht.2.trans hp1⟩).differentiableAt
              |>.differentiableWithinAt)
          (fun t ht => by
            rw [interior_Icc] at ht
            have ht_mem : t ∈ Ioo (0 : ℝ) 1 := ⟨hq0.trans ht.1, ht.2.trans hp1⟩
            rw [(hg_deriv t ht_mem).deriv]
            exact div_nonneg (mul_nonneg (sub_nonneg.mpr ht.1.le) (h1m4 t))
              (mul_nonneg ht_mem.1.le (sub_pos.mpr ht_mem.2).le))
          ⟨le_rfl, hqp⟩ ⟨hqp, le_rfl⟩ hqp
        dsimp [g] at hmono
        simp only [binaryKL_self, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          mul_zero] at hmono
        linarith
      · have hanti := antitoneOn_of_deriv_nonpos (convex_Icc p q)
          (fun t ht => (hg_deriv t ⟨hp0.trans_le ht.1, ht.2.trans_lt hq1⟩).continuousAt
            |>.continuousWithinAt)
          (fun t ht => by
            rw [interior_Icc] at ht
            exact (hg_deriv t ⟨hp0.trans ht.1, ht.2.trans hq1⟩).differentiableAt
              |>.differentiableWithinAt)
          (fun t ht => by
            rw [interior_Icc] at ht
            have ht_mem : t ∈ Ioo (0 : ℝ) 1 := ⟨hp0.trans ht.1, ht.2.trans hq1⟩
            rw [(hg_deriv t ht_mem).deriv]
            exact div_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht.2.le) (h1m4 t))
              (mul_nonneg ht_mem.1.le (sub_pos.mpr ht_mem.2).le))
          ⟨le_rfl, hpq⟩ ⟨hpq, le_rfl⟩ hpq
        dsimp [g] at hanti
        simp only [binaryKL_self, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          mul_zero] at hanti
        linarith

/-- **Quadratic empirical-Bernstein lower bound on `binaryKL`**: for `0 ≤ q ≤ p < 1` (`0 < p`),
`(p - q) ^ 2 / (2 * p) ≤ binaryKL q p`. Sharp for small `q` (`O(p)` at `q = 0`), yielding the
fast-rate PAC-Bayes inversion [TolstikhinSeldin2013] (locator unverified). -/
theorem sub_sq_div_two_mul_le_binaryKL {q p : ℝ} (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp0 : 0 < p)
    (hp1 : p < 1) :
    (p - q) ^ 2 / (2 * p) ≤ binaryKL q p := by
  rcases eq_or_lt_of_le hq0 with rfl | hqpos
  · -- At `q = 0`: `binaryKL 0 p = -log (1 - p) ≥ p ≥ p / 2 = (p - 0)² / (2 p)`.
    rw [binaryKL_eq_mul_log hp0 hp1]
    simp only [zero_mul, zero_add, sub_zero, one_mul, one_div, log_inv]
    have hlog : log (1 - p) ≤ (1 - p) - 1 := log_le_sub_one_of_pos (sub_pos.mpr hp1)
    have hdiv : p ^ 2 / (2 * p) = p / 2 := by field_simp
    linarith [hp0]
  · let g : ℝ → ℝ := fun t => binaryKL q t - (t - q) ^ 2 / (2 * t)
    have hderiv : ∀ t ∈ Ioo q 1,
        HasDerivAt g ((t - q) * (t - q + t ^ 2 + t * q) / (2 * t ^ 2 * (1 - t))) t := by
      intro t ht
      have ht0 : 0 < t := hqpos.trans ht.1
      have hd_kl := hasDerivAt_binaryKL_right (q := q) ht0 ht.2
      have hnum : HasDerivAt (fun s : ℝ => (s - q) ^ 2) (2 * (t - q) ^ 1 * 1) t :=
        ((hasDerivAt_id t).sub_const q).pow 2
      have hden : HasDerivAt (fun s : ℝ => 2 * s) (2 * 1) t := (hasDerivAt_id t).const_mul 2
      have hrat := hnum.div hden (by linarith : 2 * t ≠ 0)
      convert hd_kl.sub hrat using 1
      have htn0 : t ≠ 0 := ht0.ne'
      have h1t : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
      field_simp
      ring
    have hcont : ContinuousOn g (Icc q p) := by
      intro t ht
      have ht0 : 0 < t := hqpos.trans_le ht.1
      have ht1 : t < 1 := ht.2.trans_lt hp1
      exact ((hasDerivAt_binaryKL_right ht0 ht1).continuousAt.sub
        (by fun_prop (disch := positivity))).continuousWithinAt
    have hmono := monotoneOn_of_deriv_nonneg (convex_Icc q p) hcont
      (fun t ht => by
        rw [interior_Icc] at ht
        exact (hderiv t ⟨ht.1, ht.2.trans hp1⟩).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hderiv t ⟨ht.1, ht.2.trans hp1⟩).deriv]
        have ht0 : 0 < t := hqpos.trans ht.1
        have hnum_nn : 0 ≤ (t - q) * (t - q + t ^ 2 + t * q) := by
          have : 0 ≤ t - q := sub_nonneg.mpr ht.1.le
          have : 0 ≤ t - q + t ^ 2 + t * q := by nlinarith [hqpos.le, ht0.le]
          exact mul_nonneg (by assumption) (by assumption)
        exact div_nonneg hnum_nn (by positivity [sub_pos.mpr (ht.2.trans hp1)]))
      ⟨le_rfl, hqp⟩ ⟨hqp, le_rfl⟩ hqp
    dsimp [g] at hmono
    simp only [binaryKL_self, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div] at hmono
    linarith

/-! ### Explicit risk inversions -/

/-- Exact Pinsker inversion: for `q ∈ [0, 1]` and `p ∈ (0, 1)`, `binaryKL q p ≤ c` implies
`|p - q| ≤ √(c / 2)`. -/
theorem abs_sub_le_sqrt_of_binaryKL_le {q p c : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p)
    (hp1 : p < 1) (hle : binaryKL q p ≤ c) :
    |p - q| ≤ sqrt (c / 2) := by
  have h := two_mul_sq_le_binaryKL hq hp0 hp1
  refine abs_le_sqrt ?_
  have : (p - q) ^ 2 = (q - p) ^ 2 := by ring
  linarith

/-- Sharp quadratic inversion of `binaryKL q p ≤ c`: for `0 ≤ q`, `0 ≤ p < 1`, and `0 ≤ c`,
`p ≤ q + c + √(c ^ 2 + 2 * q * c)`. -/
theorem le_add_add_sqrt_of_binaryKL_le {q p c : ℝ} (hq0 : 0 ≤ q) (hp1 : p < 1)
    (hc : 0 ≤ c) (hle : binaryKL q p ≤ c) :
    p ≤ q + c + sqrt (c ^ 2 + 2 * q * c) := by
  rcases le_or_gt p q with hle_pq | hgt
  · have : 0 ≤ c + sqrt (c ^ 2 + 2 * q * c) := add_nonneg hc (sqrt_nonneg _)
    linarith
  have hp_pos : 0 < p := lt_of_le_of_lt hq0 hgt
  have hbern := (sub_sq_div_two_mul_le_binaryKL hq0 hgt.le hp_pos hp1).trans hle
  rw [div_le_iff₀ (by linarith : 0 < 2 * p)] at hbern
  have hsq : (p - (q + c)) ^ 2 ≤ c ^ 2 + 2 * q * c := by nlinarith
  have habs := abs_le_sqrt hsq
  linarith [(abs_le.mp habs).2]

private theorem sqrt_sq_add_two_mul_le {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) :
    sqrt (c ^ 2 + 2 * q * c) ≤ c + sqrt (2 * q * c) := by
  refine sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  have h0 : 0 ≤ c * sqrt (2 * q * c) := mul_nonneg hc (sqrt_nonneg _)
  have hsq : sqrt (2 * q * c) ^ 2 = 2 * q * c := sq_sqrt (by positivity)
  nlinarith

/-- Standard relaxed fast-rate inversion [TolstikhinSeldin2013] (locator unverified):
`binaryKL q p ≤ c ⟹ p ≤ q + √(2 * q * c) + 2 * c`. -/
theorem le_add_sqrt_two_mul_add_two_mul_of_binaryKL_le {q p c : ℝ} (hq0 : 0 ≤ q)
    (hp1 : p < 1) (hc : 0 ≤ c) (hle : binaryKL q p ≤ c) :
    p ≤ q + sqrt (2 * q * c) + 2 * c :=
  (le_add_add_sqrt_of_binaryKL_le hq0 hp1 hc hle).trans
    (by linarith [sqrt_sq_add_two_mul_le hq0 hc])

/-- Zero-empirical-risk inversion: for `p ∈ [0, 1)`, `binaryKL 0 p ≤ c` gives
`p ≤ 1 - exp (-c)` (and hence `p ≤ c`). -/
theorem le_one_sub_exp_neg_of_binaryKL_zero_le {p c : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hle : binaryKL 0 p ≤ c) :
    p ≤ 1 - exp (-c) := by
  rcases eq_or_lt_of_le hp0 with rfl | hp_pos
  · rw [binaryKL_self] at hle
    have : exp (-c) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr hle)
    linarith
  · rw [binaryKL_eq_mul_log hp_pos hp1, zero_mul, zero_add, sub_zero, one_mul, one_div,
      log_inv] at hle
    have hlog : -c ≤ log (1 - p) := by linarith
    have hexp := exp_le_exp.mpr hlog
    rw [exp_log (sub_pos.mpr hp1)] at hexp
    linarith

/-! ### Explicit PAC-Bayes-kl risk-bound corollaries -/

section Corollaries

variable {ι Z : Type*} [MeasurableSpace Z] {D : Measure Z} [IsProbabilityMeasure D]
  {ℓ : ι → Z → ℝ} [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
private theorem ae_empiricalRisk_eq_one_of_trueRisk_eq_one (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) :
    ∀ᵐ S ∂Measure.pi (fun _ : Fin m => D),
      ∀ i, trueRisk ℓ D i = 1 → empiricalRisk ℓ S i = 1 := by
  refine ae_all_iff.2 fun i => ?_
  by_cases h1 : trueRisk ℓ D i = 1
  · have hint : Integrable (fun z => 1 - ℓ i z) D :=
      Integrable.of_mem_Icc 0 1 (measurable_const.sub (hℓ i)).aemeasurable
        (ae_of_all _ fun z => ⟨sub_nonneg.2 (hℓ01 i z).2, sub_le_self _ (hℓ01 i z).1⟩)
    have h0 : ∫ z, (1 - ℓ i z) ∂D = 0 := by
      have hi : Integrable (ℓ i) D :=
        Integrable.of_mem_Icc 0 1 (hℓ i).aemeasurable (ae_of_all _ fun z => hℓ01 i z)
      rw [integral_sub (integrable_const 1) hi, integral_const, probReal_univ, smul_eq_mul,
        one_mul, ← trueRisk_def, h1, sub_self]
    have hdz : ∀ᵐ z ∂D, ℓ i z = 1 := by
      filter_upwards [(integral_eq_zero_iff_of_nonneg (fun z => sub_nonneg.2 (hℓ01 i z).2)
        hint).1 h0] with z hz
      rw [Pi.zero_apply] at hz
      linarith
    have hS : ∀ᵐ S ∂Measure.pi (fun _ : Fin m => D), ∀ j, ℓ i (S j) = 1 :=
      ae_all_iff.2 fun j => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin m => D)
        (i := j)).eventually (p := fun z => ℓ i z = 1) hdz
    filter_upwards [hS] with S hSj _
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    simp [empiricalRisk_eq_sum_div, hSj, hmR]
  · exact ae_of_all _ fun _ h => absurd h h1

private theorem integral_empiricalRisk_eq_one_of_integral_trueRisk_eq_one {m : ℕ}
    (hℓ01 : ∀ i z, ℓ i z ∈ Icc (0 : ℝ) 1) {S : Fin m → Z}
    (hS : ∀ i, trueRisk ℓ D i = 1 → empiricalRisk ℓ S i = 1)
    {Q : Measure ι} [IsProbabilityMeasure Q]
    (h1 : ∫ i, trueRisk ℓ D i ∂Q = 1) :
    ∫ i, empiricalRisk ℓ S i ∂Q = 1 := by
  have hint_sub : Integrable (fun i => 1 - trueRisk ℓ D i) Q :=
    Integrable.of_mem_Icc 0 1 (measurable_of_countable _).aemeasurable
      (ae_of_all _ fun i => ⟨sub_nonneg.2 (trueRisk_mem_Icc ℓ D (hℓ01 i)).2,
        sub_le_self _ (trueRisk_mem_Icc ℓ D (hℓ01 i)).1⟩)
  have hint_tr : Integrable (trueRisk ℓ D) Q :=
    Integrable.of_mem_Icc 0 1 (measurable_of_countable _).aemeasurable
      (ae_of_all _ fun i => trueRisk_mem_Icc ℓ D (hℓ01 i))
  have hzero : ∫ i, (1 - trueRisk ℓ D i) ∂Q = 0 := by
    rw [integral_sub (integrable_const 1) hint_tr, integral_const, probReal_univ, smul_eq_mul,
      one_mul, h1, sub_self]
  have hae : ∀ᵐ i ∂Q, trueRisk ℓ D i = 1 := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg
      (fun i => sub_nonneg.2 (trueRisk_mem_Icc ℓ D (hℓ01 i)).2) hint_sub).1 hzero] with i hi
    rw [Pi.zero_apply] at hi
    linarith
  have hae_emp : empiricalRisk ℓ S =ᵐ[Q] fun _ => (1 : ℝ) := by
    filter_upwards [hae] with i hi
    exact hS i hi
  rw [integral_congr_ae hae_emp]
  simp

private theorem integral_risk_mem_Icc {g : ι → ℝ} (hg : ∀ i, g i ∈ Icc (0 : ℝ) 1)
    (Q : Measure ι) [IsProbabilityMeasure Q] :
    ∫ i, g i ∂Q ∈ Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg fun i => (hg i).1, ?_⟩
  have hint : Integrable g Q :=
    Integrable.of_mem_Icc 0 1 (measurable_of_countable _).aemeasurable (ae_of_all _ hg)
  calc ∫ i, g i ∂Q ≤ ∫ _ : ι, (1 : ℝ) ∂Q :=
        integral_mono hint (integrable_const 1) fun i => (hg i).2
    _ = 1 := by simp

omit [Countable ι] [MeasurableSingletonClass ι] in
private theorem kl_rhs_nonneg_or_gt_one {m : ℕ} (hm : 0 < m) (P Q : Measure ι)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ m + 1) :
    0 ≤ ((klDiv Q P).toReal + log ((m + 1) / δ)) / m := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hlog : 0 ≤ log ((m + 1) / δ) :=
    log_nonneg ((one_le_div hδ).2 (by exact_mod_cast hδ1))
  exact div_nonneg (add_nonneg ENNReal.toReal_nonneg hlog) hmR.le

/-- **Boundary-qualified Pinsker conversion of the PAC-Bayes-kl bound** [Seeger2002] [Maurer2004]
(locators unverified): for `m ≥ 1` and `0 < δ ≤ m + 1`, with probability at least `1 - δ`, every
posterior `Q` with `KL(Q ‖ P) < ∞` satisfies
`𝔼_Q L_D ≤ 𝔼_Q L_S + √((KL(Q ‖ P) + log ((m + 1) / δ)) / (2 * m))`.
(Denominator **`2 * m`**, replacing `2 * (m - 1)` from McAllester's form in `PACBayes/Basic.lean`.)
-/
theorem measure_pi_exists_pinsker_risk_gt_of_binaryKL (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) (P : Measure ι)
    [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure ι, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ ∫ i, empiricalRisk ℓ S i ∂Q +
        sqrt (((klDiv Q P).toReal + log ((m + 1) / δ)) / (2 * m)) <
        ∫ i, trueRisk ℓ D i ∂Q} ≤ ENNReal.ofReal δ := by
  rcases le_or_gt δ 1 with hδ1 | hδ1
  · refine le_trans (measure_mono_ae ?_)
      (measure_pi_exists_binaryKL_integral_risk_gt hℓ hℓ01 hm P hδ)
    filter_upwards [ae_empiricalRisk_eq_one_of_trueRisk_eq_one hℓ hℓ01 hm] with S hS hbad
    obtain ⟨Q, hQ, hQP, hlt⟩ := hbad
    refine ⟨Q, hQ, hQP, ?_⟩
    set q := ∫ i, empiricalRisk ℓ S i ∂Q
    set p := ∫ i, trueRisk ℓ D i ∂Q
    set c := ((klDiv Q P).toReal + log ((m + 1) / δ)) / m
    have hq := integral_risk_mem_Icc (fun i => empiricalRisk_mem_Icc ℓ S (hℓ01 i)) Q
    have hp := integral_risk_mem_Icc (fun i => trueRisk_mem_Icc ℓ D (hℓ01 i)) Q
    have hp0 : 0 < p := by
      have : 0 ≤ q + sqrt (((klDiv Q P).toReal + log ((m + 1) / δ)) / (2 * m)) :=
        add_nonneg hq.1 (sqrt_nonneg _)
      linarith
    have hp1 : p < 1 := by
      by_contra hge
      have hpeq : p = 1 := le_antisymm hp.2 (le_of_not_gt hge)
      have hqeq : q = 1 :=
        integral_empiricalRisk_eq_one_of_integral_trueRisk_eq_one hℓ01 hS hpeq
      have hsqnn : 0 ≤ sqrt (((klDiv Q P).toReal + log ((m + 1) / δ)) / (2 * m)) := sqrt_nonneg _
      linarith
    by_contra hkle
    push Not at hkle
    have habs := abs_sub_le_sqrt_of_binaryKL_le hq hp0 hp1 hkle
    have hdiv_eq : c / 2 = ((klDiv Q P).toReal + log ((m + 1) / δ)) / (2 * m) := by
      dsimp [c]; ring
    rw [hdiv_eq] at habs
    linarith [(abs_le.mp habs).2]
  · calc Measure.pi (fun _ : Fin m => D) _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hδ1.le

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
  rcases le_or_gt δ 1 with hδ1 | hδ1
  · refine le_trans (measure_mono_ae ?_)
      (measure_pi_exists_binaryKL_integral_risk_gt hℓ hℓ01 hm P hδ)
    filter_upwards [ae_empiricalRisk_eq_one_of_trueRisk_eq_one hℓ hℓ01 hm] with S hS hbad
    obtain ⟨Q, hQ, hQP, hlt⟩ := hbad
    dsimp only at hlt
    set q := ∫ i, empiricalRisk ℓ S i ∂Q
    set p := ∫ i, trueRisk ℓ D i ∂Q
    set c := ((klDiv Q P).toReal + log ((m + 1) / δ)) / m
    have hc : 0 ≤ c := kl_rhs_nonneg_or_gt_one hm P Q hδ (by linarith [Nat.cast_nonneg (α := ℝ) m])
    have hq := integral_risk_mem_Icc (fun i => empiricalRisk_mem_Icc ℓ S (hℓ01 i)) Q
    have hp := integral_risk_mem_Icc (fun i => trueRisk_mem_Icc ℓ D (hℓ01 i)) Q
    have hp1 : p < 1 := by
      by_contra hge
      have hpeq : p = 1 := le_antisymm hp.2 (le_of_not_gt hge)
      have hqeq : q = 1 :=
        integral_empiricalRisk_eq_one_of_integral_trueRisk_eq_one hℓ01 hS hpeq
      have hsr : 0 ≤ sqrt (c ^ 2 + 2 * q * c) := sqrt_nonneg _
      linarith
    refine ⟨Q, hQ, hQP, ?_⟩
    by_contra hkle
    push Not at hkle
    have hbound := le_add_add_sqrt_of_binaryKL_le hq.1 hp1 hc hkle
    linarith
  · calc Measure.pi (fun _ : Fin m => D) _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hδ1.le

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
  rcases le_or_gt δ 1 with hδ1 | hδ1
  · refine le_trans (measure_mono fun S hS => ?_)
      (measure_pi_exists_fastRate_risk_gt_of_binaryKL hℓ hℓ01 hm P hδ)
    obtain ⟨Q, hQ, hQP, hlt⟩ := hS
    dsimp only at hlt
    refine ⟨Q, hQ, hQP, ?_⟩
    dsimp only
    set q := ∫ i, empiricalRisk ℓ S i ∂Q
    set c := ((klDiv Q P).toReal + log ((m + 1) / δ)) / m
    have hc : 0 ≤ c := kl_rhs_nonneg_or_gt_one hm P Q hδ (by linarith [Nat.cast_nonneg (α := ℝ) m])
    have hq0 : 0 ≤ q := (integral_risk_mem_Icc (fun i => empiricalRisk_mem_Icc ℓ S (hℓ01 i)) Q).1
    have hsub := sqrt_sq_add_two_mul_le hq0 hc
    linarith
  · calc Measure.pi (fun _ : Fin m => D) _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hδ1.le

/-- **Realizable `1 - exp (-c)` corollary of the PAC-Bayes-kl bound**: when `𝔼_Q L_S = 0`,
`𝔼_Q L_D ≤ 1 - exp (-((KL(Q ‖ P) + log ((m + 1) / δ)) / m))` (strictly tighter than `c`). -/
theorem measure_pi_exists_zero_risk_gt_of_binaryKL (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) (P : Measure ι)
    [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure ι, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ ∫ i, empiricalRisk ℓ S i ∂Q = 0 ∧
        1 - exp (-(((klDiv Q P).toReal + log ((m + 1) / δ)) / m)) <
          ∫ i, trueRisk ℓ D i ∂Q} ≤ ENNReal.ofReal δ := by
  refine le_trans (measure_mono_ae ?_)
    (measure_pi_exists_binaryKL_integral_risk_gt hℓ hℓ01 hm P hδ)
  filter_upwards [ae_empiricalRisk_eq_one_of_trueRisk_eq_one hℓ hℓ01 hm] with S hS hbad
  obtain ⟨Q, hQ, hQP, hq0, hlt⟩ := hbad
  have hp := integral_risk_mem_Icc (fun i => trueRisk_mem_Icc ℓ D (hℓ01 i)) Q
  have hp1 : ∫ i, trueRisk ℓ D i ∂Q < 1 := by
    by_contra hge
    have hpeq : ∫ i, trueRisk ℓ D i ∂Q = 1 := le_antisymm hp.2 (le_of_not_gt hge)
    have hq1 : ∫ i, empiricalRisk ℓ S i ∂Q = 1 :=
      integral_empiricalRisk_eq_one_of_integral_trueRisk_eq_one hℓ01 hS hpeq
    linarith
  refine ⟨Q, hQ, hQP, ?_⟩
  rw [hq0]
  by_contra hkle
  push Not at hkle
  have := le_one_sub_exp_neg_of_binaryKL_zero_le hp.1 hp1 hkle
  linarith

end Corollaries

end Cslib.MachineLearning.PACBayes
