/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACBayes.Basic
import CslibFrontier.Probability.DonskerVaradhan
import CslibFrontier.Probability.SubGaussian
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# PAC-Bayes bounds for general measurable spaces: Catoni, Hoeffding, and Gibbs oracle bounds

Extends `CslibFrontier.MachineLearning.PACBayes.Basic` on **arbitrary measurable hypothesis
spaces** `(Θ, mΘ)` (including uncountable/continuous parameter spaces such as `ℝᵈ` with a Gaussian
or uniform prior), assuming joint measurability `Measurable (Function.uncurry ℓ)` of the
`[0, 1]`-bounded loss `ℓ : Θ → Z → ℝ`.

Using the Donsker–Varadhan change-of-measure inequality
(`CslibFrontier.Probability.ChangeOfMeasure`), the shared Tonelli–Markov and joint-measurability
helpers in `CslibFrontier.MachineLearning.PACBayes.Basic`, and Gibbs variational optimality
(`CslibFrontier.Probability.DonskerVaradhan`), this module proves:

1. **Catoni's PAC-Bayes bound** [Catoni2007, Theorem 1.2.6] (exact constant `1` — no `log m` or
   `log (m + 1)` slack!). For any scale `c > 0`, define the convex, strictly increasing potential
   `catoniPhi c p = -log (1 - p * (1 - exp (-c))) / c` on `[0, 1]` with inverse
   `catoniInv c y = (1 - exp (-c * y)) / (1 - exp (-c))`. With probability at least `1 - δ` over
   `S ~ D^m`, every posterior `Q` with `KL(Q ‖ P) < ∞` satisfies
   `catoniPhi c (𝔼_Q L_D) ≤ 𝔼_Q L_S + (KL(Q ‖ P) + log (1 / δ)) / (c * m)`,
   equivalently
   `𝔼_Q L_D ≤ catoniInv c (𝔼_Q L_S + (KL(Q ‖ P) + log (1 / δ)) / (c * m))`
   and the linearized form
   `𝔼_Q L_D ≤ (c / (1 - exp (-c))) * 𝔼_Q L_S + (KL(Q ‖ P) + log (1 / δ)) / (m * (1 - exp (-c)))`.
2. **Realizable `O(1 / m)` fast-rate PAC-Bayes bound.** With probability at least `1 - δ` over
   `S ~ D^m`, every posterior `Q` with `KL(Q ‖ P) < ∞` and **zero empirical risk**
   (`∫ θ, L_S(θ) ∂Q = 0`) satisfies `𝔼_Q L_D ≤ (KL(Q ‖ P) + log (1 / δ)) / m` — without any
   `log m` factor.
3. **Linear PAC-Bayes–Hoeffding (`PAC-Bayes-λ`) bounds** [Catoni2007] [Alquier2024, Theorem 2.1].
   Upper and lower two-sided deviations for any inverse temperature `lam > 0`:
   `𝔼_Q L_D ≤ 𝔼_Q L_S + (KL(Q ‖ P) + log (1 / δ)) / lam + lam / (8 * m)` (and reversed).
4. **Gibbs posterior excess-risk oracle inequalities** [Alquier2024]. With probability at least
   `1 - δ`, the Gibbs posterior `Q̂ S = P.tilted (-lam * L_S)` satisfies:
   - for any **fixed** comparator `Q` with `KL(Q ‖ P) < ∞`:
     `𝔼_{Q̂} L_D ≤ 𝔼_Q L_D + KL(Q ‖ P) / lam + lam / (4 * m) + 2 * log (2 / δ) / lam`;
   - **simultaneously** for **every** (even data-dependent) `Q` with `KL(Q ‖ P) < ∞`:
     `𝔼_{Q̂} L_D ≤ 𝔼_Q L_D + 2 * KL(Q ‖ P) / lam + lam / (4 * m) + 2 * log (2 / δ) / lam`.

(The general measurable McAllester `log (√m / δ)` bound
`measure_pi_exists_integral_risk_gt_of_measurable` lives directly in
`CslibFrontier.MachineLearning.PACBayes.Basic`.)

Differences from the sources: `δ < 1` is not required; posteriors with `klDiv Q P = ⊤` are
excluded (for which the bounds are vacuous); losses are required to be jointly measurable in
`Θ × Z` and valued in `[0, 1]`.

## Main definitions

* `Cslib.MachineLearning.PACBayes.catoniPhi`: Catoni's log-Laplace potential `Φ_c`.
* `Cslib.MachineLearning.PACBayes.catoniInv`: inverse `Φ_c⁻¹`.

## Main results

* `Cslib.MachineLearning.PACBayes.convexOn_catoniPhi`: convexity of `catoniPhi c` on `[0, 1]`.
* `Cslib.MachineLearning.PACBayes.measure_pi_exists_catoniPhi_integral_risk_gt`,
  `Cslib.MachineLearning.PACBayes.measure_pi_exists_catoni_integral_risk_gt`,
  `Cslib.MachineLearning.PACBayes.measure_pi_exists_catoni_linear_integral_risk_gt`: Catoni's
  PAC-Bayes bound [Catoni2007, Theorem 1.2.6].
* `Cslib.MachineLearning.PACBayes.measure_pi_exists_realizable_integral_risk_gt`: fast-rate
  `O(1 / m)` PAC-Bayes bound for zero-empirical-risk posteriors.
* `Cslib.MachineLearning.PACBayes.measure_pi_exists_hoeffding_integral_risk_gt`,
  `Cslib.MachineLearning.PACBayes.measure_pi_exists_hoeffding_integral_risk_lt`: upper and lower
  linear PAC-Bayes–Hoeffding bounds [Alquier2024, Theorem 2.1].
* `Cslib.MachineLearning.PACBayes.measure_pi_gibbs_fixed_oracle_gt`,
  `Cslib.MachineLearning.PACBayes.measure_pi_gibbs_oracle_gt`: excess-risk oracle inequalities for
  the Gibbs posterior `P.tilted (fun θ => -lam * empiricalRisk ℓ S θ)`.

## References

Exact section and page locators below are unverified against primary PDFs (pending an
outside-fleet source check).

* [O. Catoni, *PAC-Bayesian Supervised Classification: The Thermodynamics of Statistical
  Learning*][Catoni2007], Theorem 1.2.6 (locator unverified against primary PDF)
* [P. Alquier, *User-friendly Introduction to PAC-Bayes Bounds*][Alquier2024], Theorem 2.1
  (locator unverified against primary PDF)
-/

public section

namespace Cslib.MachineLearning.PACBayes

open MeasureTheory ProbabilityTheory InformationTheory Real Set Finset
open scoped ENNReal BigOperators

/-! ### Catoni potential `Φ_c` and its inverse -/

/-- Catoni's log-Laplace potential `Φ_c(p) = -log (1 - p * (1 - exp (-c))) / c` for `c > 0`
and `p ∈ [0, 1]` [Catoni2007] (locator unverified). -/
noncomputable def catoniPhi (c p : ℝ) : ℝ :=
  -log (1 - p * (1 - exp (-c))) / c

/-- Defining equation of `catoniPhi`. -/
theorem catoniPhi_def (c p : ℝ) :
    catoniPhi c p = -log (1 - p * (1 - exp (-c))) / c := by rw [catoniPhi]

/-- Inverse of Catoni's potential: `Φ_c⁻¹(y) = (1 - exp (-c * y)) / (1 - exp (-c))`. -/
noncomputable def catoniInv (c y : ℝ) : ℝ :=
  (1 - exp (-c * y)) / (1 - exp (-c))

/-- Defining equation of `catoniInv`. -/
theorem catoniInv_def (c y : ℝ) :
    catoniInv c y = (1 - exp (-c * y)) / (1 - exp (-c)) := by rw [catoniInv]

private theorem one_sub_exp_neg_pos {c : ℝ} (hc : 0 < c) : 0 < 1 - exp (-c) :=
  sub_pos.mpr (exp_lt_one_iff.mpr (neg_neg_of_pos hc))

private theorem catoniArg_mem_Icc {c p : ℝ} (hc : 0 < c) (hp : p ∈ Icc (0 : ℝ) 1) :
    1 - p * (1 - exp (-c)) ∈ Icc (exp (-c)) 1 := by
  have h1e : 0 < 1 - exp (-c) := one_sub_exp_neg_pos hc
  constructor
  · have h : p * (1 - exp (-c)) ≤ 1 * (1 - exp (-c)) :=
      mul_le_mul_of_nonneg_right hp.2 h1e.le
    linarith
  · have h : 0 ≤ p * (1 - exp (-c)) := mul_nonneg hp.1 h1e.le
    linarith

private theorem catoniArg_pos {c p : ℝ} (hc : 0 < c) (hp : p ∈ Icc (0 : ℝ) 1) :
    0 < 1 - p * (1 - exp (-c)) :=
  lt_of_lt_of_le (exp_pos _) (catoniArg_mem_Icc hc hp).1

@[simp] theorem catoniPhi_zero (c : ℝ) : catoniPhi c 0 = 0 := by
  simp [catoniPhi]

theorem catoniPhi_one {c : ℝ} (hc : c ≠ 0) : catoniPhi c 1 = 1 := by
  rw [catoniPhi, one_mul, sub_sub_cancel, log_exp, neg_neg, div_self hc]

theorem catoniPhi_mem_Icc {c p : ℝ} (hc : 0 < c) (hp : p ∈ Icc (0 : ℝ) 1) :
    catoniPhi c p ∈ Icc (0 : ℝ) 1 := by
  have hmem := catoniArg_mem_Icc hc hp
  have hpos : 0 < 1 - p * (1 - exp (-c)) := catoniArg_pos hc hp
  rw [catoniPhi]
  constructor
  · refine div_nonneg (neg_nonneg.mpr (log_nonpos hpos.le hmem.2)) hc.le
  · have hlog : -c ≤ log (1 - p * (1 - exp (-c))) :=
      (log_exp (-c)).symm.trans_le (log_le_log (exp_pos _) hmem.1)
    exact (div_le_one hc).mpr (by linarith)

/-- `catoniPhi c` lies below the identity on `[0, 1]` (via convexity of `exp`). -/
theorem catoniPhi_le_self {c p : ℝ} (hc : 0 < c) (hp : p ∈ Icc (0 : ℝ) 1) :
    catoniPhi c p ≤ p := by
  have hconv : exp (-c * p) ≤ 1 - p * (1 - exp (-c)) := by
    have h := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (-c))
      (sub_nonneg.mpr hp.2) hp.1 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at h
    have heq1 : p * -c = -c * p := by ring
    have heq2 : (1 - p) + p * exp (-c) = 1 - p * (1 - exp (-c)) := by ring
    rwa [heq1, heq2] at h
  have hlog : -c * p ≤ log (1 - p * (1 - exp (-c))) := by
    calc -c * p = log (exp (-c * p)) := (log_exp _).symm
      _ ≤ log (1 - p * (1 - exp (-c))) := log_le_log (exp_pos _) hconv
  rw [catoniPhi, div_le_iff₀ hc]
  linarith

/-- Left inverse relation: `catoniInv c (catoniPhi c p) = p` for `p ∈ [0, 1]` and `c > 0`. -/
theorem catoniInv_catoniPhi {c p : ℝ} (hc : 0 < c) (hp : p ∈ Icc (0 : ℝ) 1) :
    catoniInv c (catoniPhi c p) = p := by
  have hpos : 0 < 1 - p * (1 - exp (-c)) := catoniArg_pos hc hp
  have h1e : 1 - exp (-c) ≠ 0 := (one_sub_exp_neg_pos hc).ne'
  rw [catoniInv, catoniPhi]
  have harg : -c * (-log (1 - p * (1 - exp (-c))) / c) = log (1 - p * (1 - exp (-c))) := by
    field_simp
  rw [harg, exp_log hpos]
  field_simp
  ring

/-- `catoniInv c` is strictly increasing for `c > 0`. -/
theorem strictMono_catoniInv {c : ℝ} (hc : 0 < c) : StrictMono (catoniInv c) := by
  intro a b hab
  refine div_lt_div_of_pos_right ?_ (one_sub_exp_neg_pos hc)
  have : -c * b < -c * a := by nlinarith
  linarith [exp_lt_exp.mpr this]

/-- Linear upper bound: `catoniInv c y ≤ c * y / (1 - exp (-c))` (since `1 - exp (-x) ≤ x`). -/
theorem catoniInv_le_linear {c : ℝ} (hc : 0 < c) (y : ℝ) :
    catoniInv c y ≤ c * y / (1 - exp (-c)) := by
  refine div_le_div_of_nonneg_right ?_ (one_sub_exp_neg_pos hc).le
  linarith [add_one_le_exp (-c * y)]

/-- `catoniPhi c` is convex on `[0, 1]` for `c > 0`, as the composition of `-log / c` with an
affine map into `(0, ∞)`. -/
theorem convexOn_catoniPhi {c : ℝ} (hc : 0 < c) : ConvexOn ℝ (Icc 0 1) (catoniPhi c) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2
    (show 0 < 1 - x * (1 - exp (-c)) from catoniArg_pos hc hx)
    (show 0 < 1 - y * (1 - exp (-c)) from catoniArg_pos hc hy) ha hb hab
  have haff : a * (1 - x * (1 - exp (-c))) + b * (1 - y * (1 - exp (-c))) =
      1 - (a * x + b * y) * (1 - exp (-c)) := by
    calc a * (1 - x * (1 - exp (-c))) + b * (1 - y * (1 - exp (-c)))
        = (a + b) - (a * x + b * y) * (1 - exp (-c)) := by ring
      _ = 1 - (a * x + b * y) * (1 - exp (-c)) := by rw [hab]
  simp only [smul_eq_mul] at hconc ⊢
  rw [haff] at hconc
  rw [catoniPhi, catoniPhi, catoniPhi]
  have hneg : -log (1 - (a * x + b * y) * (1 - exp (-c))) ≤
      a * (-log (1 - x * (1 - exp (-c)))) + b * (-log (1 - y * (1 - exp (-c)))) := by
    linarith
  have hdiv := div_le_div_of_nonneg_right hneg hc.le
  refine hdiv.trans_eq ?_
  ring

private theorem continuousOn_catoniPhi {c : ℝ} (hc : 0 < c) :
    ContinuousOn (catoniPhi c) (Icc 0 1) := by
  refine ContinuousOn.div_const ?_ c
  refine ContinuousOn.neg ?_
  refine ContinuousOn.log ?_ fun p hp => (catoniArg_pos hc hp).ne'
  fun_prop

/-! ### Exponential moment bounds -/

section Moments

variable {Θ Z : Type*} [MeasurableSpace Θ] [MeasurableSpace Z]
  {D : Measure Z} [IsProbabilityMeasure D] {ℓ : Θ → Z → ℝ}

omit [MeasurableSpace Θ] in
/-- Single-hypothesis Catoni exponential moment:
`𝔼_S [exp (m * c * (catoniPhi c (L_D θ) - L_S θ))] ≤ 1` for every `c > 0` and `m : ℕ`, with
**no `m + 1` or `√m` factor** [Catoni2007] (locator unverified). -/
private theorem lintegral_exp_catoni_le_one {θ : Θ} (hℓ : ∀ z, ℓ θ z ∈ Icc (0 : ℝ) 1)
    (hℓm : Measurable (ℓ θ)) {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∫⁻ S : Fin m → Z,
        ENNReal.ofReal (exp (m * c * (catoniPhi c (trueRisk ℓ D θ) - empiricalRisk ℓ S θ)))
      ∂Measure.pi (fun _ : Fin m => D) ≤ ENNReal.ofReal 1 := by
  have hp : trueRisk ℓ D θ ∈ Icc (0 : ℝ) 1 := trueRisk_mem_Icc ℓ D hℓ
  have h1 : ∀ z, exp (-c * ℓ θ z) ≤ 1 - ℓ θ z * (1 - exp (-c)) := fun z => by
    have hz := hℓ z
    have h := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (-c))
      (sub_nonneg.mpr hz.2) hz.1 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at h
    rw [show ℓ θ z * -c = -c * ℓ θ z by ring] at h
    linarith [show (1 : ℝ) - ℓ θ z + ℓ θ z * exp (-c) = 1 - ℓ θ z * (1 - exp (-c)) by ring]
  have hint_exp : Integrable (fun z => exp (-c * ℓ θ z)) D :=
    Integrable.of_mem_Icc 0 1 (measurable_const.mul hℓm).exp.aemeasurable
      (ae_of_all _ fun z => ⟨(exp_pos _).le,
        exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (hℓ z).1)⟩)
  have hint_ell : Integrable (ℓ θ) D :=
    Integrable.of_mem_Icc 0 1 hℓm.aemeasurable (ae_of_all _ hℓ)
  have hsingle : ∫ z, exp (-c * ℓ θ z) ∂D ≤ exp (-c * catoniPhi c (trueRisk ℓ D θ)) := by
    have hmono : ∫ z, exp (-c * ℓ θ z) ∂D ≤
        ∫ z, (1 - ℓ θ z * (1 - exp (-c))) ∂D :=
      integral_mono hint_exp
        ((integrable_const 1).sub (hint_ell.mul_const _)) h1
    have hrhs : ∫ z, (1 - ℓ θ z * (1 - exp (-c))) ∂D =
        1 - trueRisk ℓ D θ * (1 - exp (-c)) := by
      rw [integral_sub (integrable_const 1) (hint_ell.mul_const _), integral_mul_const,
        integral_const, probReal_univ, smul_eq_mul, one_mul, trueRisk_def]
    have hpos : 0 < 1 - trueRisk ℓ D θ * (1 - exp (-c)) := catoniArg_pos hc hp
    have hexp_eq : exp (-c * catoniPhi c (trueRisk ℓ D θ)) =
        1 - trueRisk ℓ D θ * (1 - exp (-c)) := by
      rw [catoniPhi, show -c * (-log (1 - trueRisk ℓ D θ * (1 - exp (-c))) / c) =
        log (1 - trueRisk ℓ D θ * (1 - exp (-c))) by field_simp, exp_log hpos]
    linarith
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hprod_eq (S : Fin m → Z) :
      exp (m * c * (catoniPhi c (trueRisk ℓ D θ) - empiricalRisk ℓ S θ)) =
        exp (m * c * catoniPhi c (trueRisk ℓ D θ)) * ∏ j : Fin m, exp (-c * ℓ θ (S j)) := by
    rw [← exp_sum, ← exp_add, empiricalRisk_eq_sum_div]
    congr 1
    rw [← mul_sum]
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    field_simp
    ring
  have hprod_meas : Measurable fun S : Fin m → Z =>
      exp (m * c * (catoniPhi c (trueRisk ℓ D θ) - empiricalRisk ℓ S θ)) := by
    simp_rw [hprod_eq]
    refine measurable_const.mul (Finset.measurable_prod _ fun j _ => ?_)
    exact (measurable_const.mul (hℓm.comp (measurable_pi_apply j))).exp
  have hbound (S : Fin m → Z) :
      exp (m * c * (catoniPhi c (trueRisk ℓ D θ) - empiricalRisk ℓ S θ)) ≤ exp (m * c) := by
    refine exp_le_exp.mpr ?_
    have hphi := catoniPhi_mem_Icc hc hp
    have hemp := empiricalRisk_mem_Icc ℓ S hℓ
    have hdiff : catoniPhi c (trueRisk ℓ D θ) - empiricalRisk ℓ S θ ≤ 1 := by
      linarith [hphi.2, hemp.1]
    have hmul : (m : ℝ) * c * (catoniPhi c (trueRisk ℓ D θ) - empiricalRisk ℓ S θ) ≤
        (m : ℝ) * c * 1 :=
      mul_le_mul_of_nonneg_left hdiff (by positivity)
    linarith
  have hpi_int : Integrable (fun S : Fin m → Z =>
      exp (m * c * (catoniPhi c (trueRisk ℓ D θ) - empiricalRisk ℓ S θ)))
      (Measure.pi fun _ : Fin m => D) :=
    Integrable.of_mem_Icc 0 (exp (m * c)) hprod_meas.aemeasurable
      (ae_of_all _ fun S => ⟨(exp_pos _).le, hbound S⟩)
  rw [← ofReal_integral_eq_lintegral_ofReal hpi_int (ae_of_all _ fun _ => (exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp_rw [hprod_eq]
  rw [integral_const_mul, integral_fintype_prod_eq_prod fun _ z => exp (-c * ℓ θ z),
    prod_const, card_univ, Fintype.card_fin]
  have hpow : (∫ z, exp (-c * ℓ θ z) ∂D) ^ m ≤
      (exp (-c * catoniPhi c (trueRisk ℓ D θ))) ^ m :=
    pow_le_pow_left₀ (integral_nonneg fun _ => (exp_pos _).le) hsingle m
  calc exp (m * c * catoniPhi c (trueRisk ℓ D θ)) * (∫ z, exp (-c * ℓ θ z) ∂D) ^ m
      ≤ exp (m * c * catoniPhi c (trueRisk ℓ D θ)) *
          (exp (-c * catoniPhi c (trueRisk ℓ D θ))) ^ m :=
        mul_le_mul_of_nonneg_left hpow (exp_pos _).le
    _ = exp (m * c * catoniPhi c (trueRisk ℓ D θ)) *
          exp (m * (-c * catoniPhi c (trueRisk ℓ D θ))) := by rw [← exp_nat_mul]
    _ = 1 := by
        rw [← exp_add, show (m : ℝ) * c * catoniPhi c (trueRisk ℓ D θ) +
          m * (-c * catoniPhi c (trueRisk ℓ D θ)) = 0 by ring, exp_zero]

omit [MeasurableSpace Θ] in
/-- Single-hypothesis realizable exponential moment:
`𝔼_S [1_{L_S(θ) = 0} * exp (m * L_D(θ))] ≤ 1` for every `m : ℕ`. -/
private theorem lintegral_indicator_zero_exp_le_one {θ : Θ} (hℓ : ∀ z, ℓ θ z ∈ Icc (0 : ℝ) 1)
    (hℓm : Measurable (ℓ θ)) (m : ℕ) :
    ∫⁻ S : Fin m → Z,
        ENNReal.ofReal (if empiricalRisk ℓ S θ = 0 then exp (m * trueRisk ℓ D θ) else 0)
      ∂Measure.pi (fun _ : Fin m => D) ≤ ENNReal.ofReal 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · calc ∫⁻ S : Fin 0 → Z,
          ENNReal.ofReal (if empiricalRisk ℓ S θ = 0 then exp ((0 : ℕ) * trueRisk ℓ D θ) else 0)
            ∂Measure.pi (fun _ : Fin 0 => D)
        ≤ ∫⁻ _ : Fin 0 → Z, (1 : ℝ≥0∞) ∂Measure.pi (fun _ : Fin 0 => D) :=
          lintegral_mono fun S => by
            simp only [Nat.cast_zero, zero_mul, exp_zero]; split_ifs <;> simp
      _ = ENNReal.ofReal 1 := by simp
  have hprod_le (S : Fin m → Z) :
      (if empiricalRisk ℓ S θ = 0 then (1 : ℝ) else 0) ≤ ∏ j : Fin m, (1 - ℓ θ (S j)) := by
    split_ifs with h0
    · rw [empiricalRisk_eq_sum_div, div_eq_zero_iff] at h0
      have hsum : ∑ j : Fin m, ℓ θ (S j) = 0 :=
        h0.resolve_right (Nat.cast_ne_zero.mpr hm.ne')
      have hall : ∀ j : Fin m, ℓ θ (S j) = 0 := fun j =>
        (sum_eq_zero_iff_of_nonneg fun i _ => (hℓ (S i)).1).mp hsum j (mem_univ j)
      simp [hall]
    · exact prod_nonneg fun j _ => sub_nonneg.mpr (hℓ (S j)).2
  have hprod_meas : Measurable fun S : Fin m → Z => ∏ j : Fin m, (1 - ℓ θ (S j)) :=
    Finset.measurable_prod _ fun j _ => measurable_const.sub (hℓm.comp (measurable_pi_apply j))
  have hprod_int : Integrable (fun S : Fin m → Z => ∏ j : Fin m, (1 - ℓ θ (S j)))
      (Measure.pi fun _ : Fin m => D) :=
    Integrable.of_mem_Icc 0 1 hprod_meas.aemeasurable (ae_of_all _ fun S =>
      ⟨prod_nonneg fun j _ => sub_nonneg.mpr (hℓ (S j)).2,
       prod_le_one₀ (fun j _ => sub_nonneg.mpr (hℓ (S j)).2)
         fun j _ => sub_le_self _ (hℓ (S j)).1⟩)
  have hind_le (S : Fin m → Z) :
      (if empiricalRisk ℓ S θ = 0 then exp (m * trueRisk ℓ D θ) else 0) ≤
        exp (m * trueRisk ℓ D θ) * ∏ j : Fin m, (1 - ℓ θ (S j)) := by
    have := mul_le_mul_of_nonneg_left (hprod_le S) (exp_pos (m * trueRisk ℓ D θ)).le
    simpa [mul_ite] using this
  calc ∫⁻ S, ENNReal.ofReal (if empiricalRisk ℓ S θ = 0 then exp (m * trueRisk ℓ D θ) else 0)
        ∂Measure.pi (fun _ : Fin m => D)
      ≤ ∫⁻ S, ENNReal.ofReal (exp (m * trueRisk ℓ D θ) * ∏ j : Fin m, (1 - ℓ θ (S j)))
          ∂Measure.pi (fun _ : Fin m => D) :=
          lintegral_mono fun S => ENNReal.ofReal_le_ofReal (hind_le S)
    _ = ENNReal.ofReal (∫ S, exp (m * trueRisk ℓ D θ) * ∏ j : Fin m, (1 - ℓ θ (S j))
          ∂Measure.pi (fun _ : Fin m => D)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hprod_int.const_mul _)
          (ae_of_all _ fun S => mul_nonneg (exp_pos _).le
            (prod_nonneg fun j _ => sub_nonneg.mpr (hℓ (S j)).2))]
    _ ≤ ENNReal.ofReal 1 := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul, integral_fintype_prod_eq_prod fun _ z => 1 - ℓ θ z,
          prod_const, card_univ, Fintype.card_fin]
        have hint_ell : Integrable (ℓ θ) D :=
          Integrable.of_mem_Icc 0 1 hℓm.aemeasurable (ae_of_all _ hℓ)
        have h1m : ∫ z, (1 - ℓ θ z) ∂D = 1 - trueRisk ℓ D θ := by
          rw [integral_sub (integrable_const 1) hint_ell, integral_const, probReal_univ,
            smul_eq_mul, one_mul, trueRisk_def]
        rw [h1m]
        have hp := trueRisk_mem_Icc ℓ D hℓ
        have hstep : (1 - trueRisk ℓ D θ) ^ m ≤ (exp (-trueRisk ℓ D θ)) ^ m :=
          pow_le_pow_left₀ (sub_nonneg.mpr hp.2)
            (by linarith [add_one_le_exp (-trueRisk ℓ D θ)]) m
        calc exp (m * trueRisk ℓ D θ) * (1 - trueRisk ℓ D θ) ^ m
            ≤ exp (m * trueRisk ℓ D θ) * (exp (-trueRisk ℓ D θ)) ^ m :=
              mul_le_mul_of_nonneg_left hstep (exp_pos _).le
          _ = exp (m * trueRisk ℓ D θ) * exp (m * -trueRisk ℓ D θ) := by rw [← exp_nat_mul]
          _ = 1 := by rw [← exp_add]; simp [mul_neg]

end Moments

/-! ### Catoni's PAC-Bayes theorem -/

section GeneralPACBayes

variable {Θ Z : Type*} [MeasurableSpace Θ] [MeasurableSpace Z]
  {D : Measure Z} [IsProbabilityMeasure D] {ℓ : Θ → Z → ℝ}

/-- **Catoni's PAC-Bayes bound (`Φ_c` form)** [Catoni2007, Theorem 1.2.6] (locator unverified):
for **any** measurable hypothesis space `Θ` (countable or uncountable), jointly measurable loss
`ℓ : Θ → Z → ℝ` valued in `[0, 1]`, probability prior `P` on `Θ`, `m ≥ 1`, scale `c > 0`, and
`δ > 0`, with probability at least `1 - δ` over `S ~ D^m`, every probability posterior `Q` with
`KL(Q ‖ P) < ∞` satisfies
`catoniPhi c (𝔼_Q L_D) ≤ 𝔼_Q L_S + (KL(Q ‖ P) + log (1 / δ)) / (c * m)`. -/
theorem measure_pi_exists_catoniPhi_integral_risk_gt
    (hℓ : Measurable (Function.uncurry ℓ)) (hℓ01 : ∀ θ z, ℓ θ z ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 0 < c) (P : Measure Θ) [IsProbabilityMeasure P]
    {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure Θ, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ ∫ θ, empiricalRisk ℓ S θ ∂Q +
        ((klDiv Q P).toReal + log (1 / δ)) / (c * m) <
        catoniPhi c (∫ θ, trueRisk ℓ D θ ∂Q)} ≤ ENNReal.ofReal δ := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hcm : 0 < (m : ℝ) * c := mul_pos hmR hc
  set F : (Fin m → Z) → Θ → ℝ≥0∞ := fun S θ =>
    ENNReal.ofReal (exp (m * c * (catoniPhi c (trueRisk ℓ D θ) - empiricalRisk ℓ S θ)))
  have hphi_meas : Measurable fun θ => catoniPhi c (trueRisk ℓ D θ) := by
    have htr := measurable_trueRisk_of_measurable (D := D) hℓ hℓ01
    refine (((measurable_const.sub (htr.mul measurable_const)).log.neg).div_const c)
  have hFm : Measurable (Function.uncurry F) := by
    refine Measurable.ennreal_ofReal (Measurable.exp (measurable_const.mul ?_))
    exact (hphi_meas.comp measurable_snd).sub (measurable_empiricalRisk_prod hℓ m)
  have hmom (θ : Θ) : ∫⁻ S, F S θ ∂Measure.pi (fun _ : Fin m => D) ≤ ENNReal.ofReal 1 :=
    lintegral_exp_catoni_le_one (D := D) (hℓ01 θ)
      (hℓ.comp (measurable_const.prodMk measurable_id)) hc m
  have hmarkov := measure_ofReal_div_le_lintegral_le_of_measurable
    (Measure.pi fun _ : Fin m => D) P hFm hmom one_pos hδ
  refine (measure_mono fun S hS => ?_).trans hmarkov
  obtain ⟨Q, hQ, hQP, hlt⟩ := hS
  by_contra hB
  rw [Set.mem_ofPred_eq, not_le] at hB
  set f : Θ → ℝ := fun θ => m * c * (catoniPhi c (trueRisk ℓ D θ) - empiricalRisk ℓ S θ)
  have hf_meas : Measurable f :=
    measurable_const.mul (hphi_meas.sub (measurable_empiricalRisk_arg hℓ S))
  have hf_bd (θ : Θ) : |f θ| ≤ (m : ℝ) * c := by
    have h1 := catoniPhi_mem_Icc hc (trueRisk_mem_Icc ℓ D (hℓ01 θ))
    have h2 := empiricalRisk_mem_Icc ℓ S (hℓ01 θ)
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hfQ : Integrable f Q := Integrable.of_bound hf_meas.aestronglyMeasurable (m * c)
    (ae_of_all _ fun θ => by simpa [Real.norm_eq_abs] using hf_bd θ)
  have hexpP : Integrable (fun θ => exp (f θ)) P :=
    Integrable.of_bound hf_meas.exp.aestronglyMeasurable (exp (m * c))
      (ae_of_all _ fun θ => by
        rw [Real.norm_of_nonneg (exp_pos _).le]
        exact exp_le_exp.mpr (le_trans (le_abs_self _) (hf_bd θ)))
  have hcm_ineq := Cslib.Probability.integral_le_toReal_klDiv_add_log_integral_exp hQP hfQ hexpP
  have hpos : 0 < ∫ θ, exp (f θ) ∂P := integral_exp_pos hexpP
  rw [← ofReal_integral_eq_lintegral_ofReal hexpP (ae_of_all _ fun _ => (exp_pos _).le),
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hpos.le] at hB
  have hlog : log (∫ θ, exp (f θ) ∂P) < log (1 / δ) := log_lt_log hpos hB
  have hphi_int : Integrable (fun θ => catoniPhi c (trueRisk ℓ D θ)) Q :=
    Integrable.of_mem_Icc 0 1 hphi_meas.aemeasurable
      (ae_of_all _ fun θ => catoniPhi_mem_Icc hc (trueRisk_mem_Icc ℓ D (hℓ01 θ)))
  have htr_int : Integrable (trueRisk ℓ D) Q := integrable_trueRisk_of_measurable hℓ hℓ01 Q
  have hemp_int : Integrable (empiricalRisk ℓ S) Q :=
    integrable_empiricalRisk_of_measurable hℓ hℓ01 S Q
  have hjensen : catoniPhi c (∫ θ, trueRisk ℓ D θ ∂Q) ≤
      ∫ θ, catoniPhi c (trueRisk ℓ D θ) ∂Q :=
    (convexOn_catoniPhi hc).map_integral_le (continuousOn_catoniPhi hc) isClosed_Icc
      (ae_of_all _ fun θ => trueRisk_mem_Icc ℓ D (hℓ01 θ)) htr_int hphi_int
  have hf_eq : ∫ θ, f θ ∂Q =
      (m : ℝ) * c * (∫ θ, catoniPhi c (trueRisk ℓ D θ) ∂Q - ∫ θ, empiricalRisk ℓ S θ ∂Q) := by
    simp only [f, integral_const_mul, integral_sub hphi_int hemp_int]
  have hdiv := hlt
  rw [show (c * (m : ℝ)) = (m : ℝ) * c by ring] at hdiv
  have h1 : (m : ℝ) * c * ∫ θ, empiricalRisk ℓ S θ ∂Q +
      ((klDiv Q P).toReal + log (1 / δ)) <
      (m : ℝ) * c * catoniPhi c (∫ θ, trueRisk ℓ D θ ∂Q) := by
    have := mul_lt_mul_of_pos_left hdiv hcm
    field_simp at this
    linarith
  have h2 : (m : ℝ) * c * catoniPhi c (∫ θ, trueRisk ℓ D θ ∂Q) ≤
      (m : ℝ) * c * ∫ θ, catoniPhi c (trueRisk ℓ D θ) ∂Q :=
    mul_le_mul_of_nonneg_left hjensen hcm.le
  linarith

/-- **Catoni's PAC-Bayes bound (inverted explicit risk bound)** [Catoni2007, Theorem 1.2.6]
(locator unverified): for any measurable hypothesis space `Θ`, scale `c > 0`, `m ≥ 1`, and `δ > 0`,
with probability at least `1 - δ`, every posterior `Q` with `KL(Q ‖ P) < ∞` satisfies
`𝔼_Q L_D ≤ catoniInv c (𝔼_Q L_S + (KL(Q ‖ P) + log (1 / δ)) / (c * m))`. -/
theorem measure_pi_exists_catoni_integral_risk_gt
    (hℓ : Measurable (Function.uncurry ℓ)) (hℓ01 : ∀ θ z, ℓ θ z ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 0 < c) (P : Measure Θ) [IsProbabilityMeasure P]
    {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure Θ, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ catoniInv c (∫ θ, empiricalRisk ℓ S θ ∂Q +
        ((klDiv Q P).toReal + log (1 / δ)) / (c * m)) <
        ∫ θ, trueRisk ℓ D θ ∂Q} ≤ ENNReal.ofReal δ := by
  refine (measure_mono fun S hS => ?_).trans
    (measure_pi_exists_catoniPhi_integral_risk_gt hℓ hℓ01 hm hc P hδ)
  obtain ⟨Q, hQ, hQP, hlt⟩ := hS
  refine ⟨Q, hQ, hQP, ?_⟩
  have htr_mem : ∫ θ, trueRisk ℓ D θ ∂Q ∈ Icc (0 : ℝ) 1 :=
    ⟨integral_nonneg fun θ => (trueRisk_mem_Icc ℓ D (hℓ01 θ)).1, by
      calc ∫ θ, trueRisk ℓ D θ ∂Q ≤ ∫ _ : Θ, (1 : ℝ) ∂Q :=
            integral_mono (integrable_trueRisk_of_measurable hℓ hℓ01 Q) (integrable_const 1)
              fun θ => (trueRisk_mem_Icc ℓ D (hℓ01 θ)).2
        _ = 1 := by simp⟩
  by_contra hle
  push Not at hle
  have hinv := (strictMono_catoniInv hc).monotone hle
  rw [catoniInv_catoniPhi hc htr_mem] at hinv
  linarith

/-- **Linearized Catoni PAC-Bayes bound**: replacing `catoniInv c y` by `c * y / (1 - exp (-c))`
yields
`𝔼_Q L_D ≤ (c / (1 - exp (-c))) * 𝔼_Q L_S + (KL(Q ‖ P) + log (1 / δ)) / (m * (1 - exp (-c)))`. -/
theorem measure_pi_exists_catoni_linear_integral_risk_gt
    (hℓ : Measurable (Function.uncurry ℓ)) (hℓ01 : ∀ θ z, ℓ θ z ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 0 < c) (P : Measure Θ) [IsProbabilityMeasure P]
    {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure Θ, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ (c / (1 - exp (-c))) * ∫ θ, empiricalRisk ℓ S θ ∂Q +
        ((klDiv Q P).toReal + log (1 / δ)) / (m * (1 - exp (-c))) <
        ∫ θ, trueRisk ℓ D θ ∂Q} ≤ ENNReal.ofReal δ := by
  refine (measure_mono fun S hS => ?_).trans
    (measure_pi_exists_catoni_integral_risk_gt hℓ hℓ01 hm hc P hδ)
  obtain ⟨Q, hQ, hQP, hlt⟩ := hS
  refine ⟨Q, hQ, hQP, lt_of_le_of_lt (catoniInv_le_linear hc _) ?_⟩
  have h1e : 1 - exp (-c) ≠ 0 := (one_sub_exp_neg_pos hc).ne'
  have heq : c * (∫ θ, empiricalRisk ℓ S θ ∂Q + ((klDiv Q P).toReal + log (1 / δ)) / (c * m)) /
      (1 - exp (-c)) =
      (c / (1 - exp (-c))) * ∫ θ, empiricalRisk ℓ S θ ∂Q +
        ((klDiv Q P).toReal + log (1 / δ)) / (m * (1 - exp (-c))) := by
    have hcne : c ≠ 0 := hc.ne'
    field_simp
  rwa [heq]

/-- **Realizable fast-rate `O(1 / m)` PAC-Bayes bound** (zero `log m` factor): on an arbitrary
measurable hypothesis space `Θ`, with probability at least `1 - δ` over `S ~ D^m`, every
posterior `Q` with `KL(Q ‖ P) < ∞` and zero empirical risk (`∫ θ, L_S(θ) ∂Q = 0`) satisfies
`𝔼_Q L_D ≤ (KL(Q ‖ P) + log (1 / δ)) / m`. -/
theorem measure_pi_exists_realizable_integral_risk_gt
    (hℓ : Measurable (Function.uncurry ℓ)) (hℓ01 : ∀ θ z, ℓ θ z ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) (P : Measure Θ) [IsProbabilityMeasure P]
    {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure Θ, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ ∫ θ, empiricalRisk ℓ S θ ∂Q = 0 ∧
        ((klDiv Q P).toReal + log (1 / δ)) / m < ∫ θ, trueRisk ℓ D θ ∂Q} ≤
      ENNReal.ofReal δ := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set F : (Fin m → Z) → Θ → ℝ≥0∞ := fun S θ =>
    ENNReal.ofReal (if empiricalRisk ℓ S θ = 0 then exp (m * trueRisk ℓ D θ) else 0)
  have htr_meas : Measurable (trueRisk ℓ D) := measurable_trueRisk_of_measurable hℓ hℓ01
  have hFm : Measurable (Function.uncurry F) := by
    refine Measurable.ennreal_ofReal (Measurable.ite ?_ ?_ measurable_const)
    · exact (measurable_empiricalRisk_prod hℓ m) (measurableSet_singleton 0)
    · exact (measurable_const.mul (htr_meas.comp measurable_snd)).exp
  have hmom (θ : Θ) : ∫⁻ S, F S θ ∂Measure.pi (fun _ : Fin m => D) ≤ ENNReal.ofReal 1 :=
    lintegral_indicator_zero_exp_le_one (D := D) (hℓ01 θ)
      (hℓ.comp (measurable_const.prodMk measurable_id)) m
  have hmarkov := measure_ofReal_div_le_lintegral_le_of_measurable
    (Measure.pi fun _ : Fin m => D) P hFm hmom one_pos hδ
  refine (measure_mono fun S hS => ?_).trans hmarkov
  obtain ⟨Q, hQ, hQP, hzero, hlt⟩ := hS
  by_contra hB
  rw [Set.mem_ofPred_eq, not_le] at hB
  have hAe0 : ∀ᵐ θ ∂Q, empiricalRisk ℓ S θ = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun θ => (empiricalRisk_mem_Icc ℓ S (hℓ01 θ)).1)
      (integrable_empiricalRisk_of_measurable hℓ hℓ01 S Q)).mp hzero
  set g : Θ → ℝ := fun θ => if empiricalRisk ℓ S θ = 0 then exp (m * trueRisk ℓ D θ) else 0
  have hg_meas : Measurable g :=
    Measurable.ite ((measurable_empiricalRisk_arg hℓ S) (measurableSet_singleton 0))
      (measurable_const.mul htr_meas).exp measurable_const
  have hg_nn (θ : Θ) : 0 ≤ g θ := by dsimp [g]; split_ifs <;> positivity
  have hg_bd (θ : Θ) : g θ ≤ exp m := by
    dsimp [g]
    split_ifs
    · exact exp_le_exp.mpr (by nlinarith [(trueRisk_mem_Icc ℓ D (hℓ01 θ)).2])
    · exact (exp_pos _).le
  have hg_int : Integrable g P :=
    Integrable.of_mem_Icc 0 (exp m) hg_meas.aemeasurable (ae_of_all _ fun θ => ⟨hg_nn θ, hg_bd θ⟩)
  rw [← ofReal_integral_eq_lintegral_ofReal hg_int (ae_of_all _ hg_nn),
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (integral_nonneg hg_nn)] at hB
  -- Truncate outside `{L_S = 0}` to `log ε` so change of measure applies directly to `P`.
  have hfor (ε : ℝ) (hε : 0 < ε) :
      (m : ℝ) * ∫ θ, trueRisk ℓ D θ ∂Q ≤
        (klDiv Q P).toReal + log (1 / δ + ε) := by
    let f : Θ → ℝ := fun θ => if empiricalRisk ℓ S θ = 0 then m * trueRisk ℓ D θ else log ε
    have hf_meas : Measurable f :=
      Measurable.ite ((measurable_empiricalRisk_arg hℓ S) (measurableSet_singleton 0))
        (measurable_const.mul htr_meas) measurable_const
    have hf_ae : f =ᵐ[Q] fun θ => (m : ℝ) * trueRisk ℓ D θ := by
      filter_upwards [hAe0] with θ hθ
      simp [f, hθ]
    have hfQ : Integrable f Q :=
      ((integrable_trueRisk_of_measurable hℓ hℓ01 Q).const_mul (m : ℝ)).congr hf_ae.symm
    have hexp_le (θ : Θ) : exp (f θ) ≤ g θ + ε := by
      dsimp only [f, g]
      split_ifs
      · linarith
      · rw [exp_log hε, zero_add]
    have hexpP : Integrable (fun θ => exp (f θ)) P :=
      Integrable.of_mem_Icc 0 (exp m + ε) hf_meas.exp.aemeasurable
        (ae_of_all _ fun θ => ⟨(exp_pos _).le, (hexp_le θ).trans (by linarith [hg_bd θ])⟩)
    have hcm := Cslib.Probability.integral_le_toReal_klDiv_add_log_integral_exp hQP hfQ hexpP
    have hfq_eq : ∫ θ, f θ ∂Q = (m : ℝ) * ∫ θ, trueRisk ℓ D θ ∂Q := by
      rw [integral_congr_ae hf_ae, integral_const_mul]
    have hmono : ∫ θ, exp (f θ) ∂P ≤ ∫ θ, g θ ∂P + ε := by
      calc ∫ θ, exp (f θ) ∂P ≤ ∫ θ, (g θ + ε) ∂P :=
            integral_mono hexpP (hg_int.add (integrable_const ε)) hexp_le
        _ = ∫ θ, g θ ∂P + ε := by rw [integral_add hg_int (integrable_const ε)]; simp
    have hpos_int : 0 < ∫ θ, exp (f θ) ∂P := integral_exp_pos hexpP
    have hlog_le : log (∫ θ, exp (f θ) ∂P) ≤ log (1 / δ + ε) :=
      log_le_log hpos_int (by linarith)
    linarith
  have h1d : 0 < 1 / δ := one_div_pos.mpr hδ
  have hlim : (m : ℝ) * ∫ θ, trueRisk ℓ D θ ∂Q ≤ (klDiv Q P).toReal + log (1 / δ) := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    set ε : ℝ := (1 / δ) * (exp η - 1)
    have hε : 0 < ε := mul_pos h1d (sub_pos.mpr (one_lt_exp_iff.mpr hη))
    have hstep := hfor ε hε
    have heq : 1 / δ + ε = (1 / δ) * exp η := by dsimp [ε]; ring
    rw [heq, log_mul h1d.ne' (exp_pos _).ne', log_exp] at hstep
    linarith
  rw [div_lt_iff₀ hmR] at hlt
  linarith

/-! ### Linear PAC-Bayes–Hoeffding (`PAC-Bayes-λ`) and McAllester bounds -/

omit [MeasurableSpace Θ] in
private theorem abs_trueRisk_sub_empiricalRisk_le_one {θ : Θ} {m : ℕ} (S : Fin m → Z)
    (hℓ01 : ∀ z, ℓ θ z ∈ Icc (0 : ℝ) 1) :
    |trueRisk ℓ D θ - empiricalRisk ℓ S θ| ≤ 1 := by
  have h1 := trueRisk_mem_Icc ℓ D hℓ01
  have h2 := empiricalRisk_mem_Icc ℓ S hℓ01
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Shared Hoeffding–Donsker–Varadhan bound for any signed temperature `t : ℝ` (`t > 0` for the
upper tail `L_D - L_S`, `t < 0` for the lower tail `L_S - L_D`). -/
private theorem measure_pi_hoeffding_core
    (hℓ : Measurable (Function.uncurry ℓ)) (hℓ01 : ∀ θ z, ℓ θ z ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) (t : ℝ) (P : Measure Θ) [IsProbabilityMeasure P]
    {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure Θ, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ (klDiv Q P).toReal + log (1 / δ) + t ^ 2 / (8 * m) <
        t * (∫ θ, trueRisk ℓ D θ ∂Q - ∫ θ, empiricalRisk ℓ S θ ∂Q)} ≤ ENNReal.ofReal δ := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set B : ℝ := exp (t ^ 2 / (8 * m))
  have hB_pos : 0 < B := exp_pos _
  have htr_meas : Measurable (trueRisk ℓ D) := measurable_trueRisk_of_measurable hℓ hℓ01
  set F : (Fin m → Z) → Θ → ℝ≥0∞ := fun S θ =>
    ENNReal.ofReal (exp (t * (trueRisk ℓ D θ - empiricalRisk ℓ S θ)))
  have hFm : Measurable (Function.uncurry F) :=
    (measurable_const.mul ((htr_meas.comp measurable_snd).sub
      (measurable_empiricalRisk_prod hℓ m))).exp.ennreal_ofReal
  have hmom (θ : Θ) : ∫⁻ S, F S θ ∂Measure.pi (fun _ : Fin m => D) ≤ ENNReal.ofReal B := by
    have hθm : Measurable (ℓ θ) := hℓ.comp (measurable_const.prodMk measurable_id)
    have hsg := Cslib.Probability.hasSubgaussianMGF_integral_sub_sum_div D hθm (hℓ01 θ) hm
    have hmgf := hsg.mgf_le t
    have hbd (S : Fin m → Z) :
        exp (t * (trueRisk ℓ D θ - empiricalRisk ℓ S θ)) ≤ exp |t| := by
      refine exp_le_exp.mpr ?_
      calc t * (trueRisk ℓ D θ - empiricalRisk ℓ S θ)
          ≤ |t * (trueRisk ℓ D θ - empiricalRisk ℓ S θ)| := le_abs_self _
        _ = |t| * |trueRisk ℓ D θ - empiricalRisk ℓ S θ| := abs_mul _ _
        _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left
              (abs_trueRisk_sub_empiricalRisk_le_one S (hℓ01 θ)) (abs_nonneg t)
        _ = |t| := mul_one _
    have hint : Integrable (fun S : Fin m → Z =>
        exp (t * (trueRisk ℓ D θ - empiricalRisk ℓ S θ)))
        (Measure.pi fun _ : Fin m => D) :=
      Integrable.of_mem_Icc 0 (exp |t|)
        ((measurable_const.mul (measurable_const.sub
          (measurable_empiricalRisk (ℓ := ℓ) m hθm))).exp.aemeasurable)
        (ae_of_all _ fun S => ⟨(exp_pos _).le, hbd S⟩)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (exp_pos _).le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : B = exp ((((4 * m : NNReal)⁻¹ : NNReal) : ℝ) * t ^ 2 / 2) := by
      dsimp [B]
      congr 1
      push_cast
      field_simp
      ring
    rw [heq]
    simpa only [mgf, trueRisk_def, empiricalRisk_eq_sum_div] using hmgf
  have hmarkov := measure_ofReal_div_le_lintegral_le_of_measurable
    (Measure.pi fun _ : Fin m => D) P hFm hmom hB_pos hδ
  refine (measure_mono fun S hS => ?_).trans hmarkov
  obtain ⟨Q, hQ, hQP, hlt⟩ := hS
  by_contra hB'
  rw [Set.mem_ofPred_eq, not_le] at hB'
  set f : Θ → ℝ := fun θ => t * (trueRisk ℓ D θ - empiricalRisk ℓ S θ)
  have hf_meas : Measurable f :=
    measurable_const.mul (htr_meas.sub (measurable_empiricalRisk_arg hℓ S))
  have hf_bd (θ : Θ) : |f θ| ≤ |t| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_trueRisk_sub_empiricalRisk_le_one S (hℓ01 θ))
      (abs_nonneg t)).trans_eq (mul_one _)
  have hfQ : Integrable f Q := Integrable.of_bound hf_meas.aestronglyMeasurable |t|
    (ae_of_all _ fun θ => by simpa [Real.norm_eq_abs] using hf_bd θ)
  have hexpP : Integrable (fun θ => exp (f θ)) P :=
    Integrable.of_bound hf_meas.exp.aestronglyMeasurable (exp |t|) (ae_of_all _ fun θ => by
      rw [Real.norm_of_nonneg (exp_pos _).le]
      exact exp_le_exp.mpr (le_trans (le_abs_self _) (hf_bd θ)))
  have hcm := Cslib.Probability.integral_le_toReal_klDiv_add_log_integral_exp hQP hfQ hexpP
  have hpos : 0 < ∫ θ, exp (f θ) ∂P := integral_exp_pos hexpP
  rw [← ofReal_integral_eq_lintegral_ofReal hexpP (ae_of_all _ fun _ => (exp_pos _).le),
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hpos.le] at hB'
  have hlog : log (∫ θ, exp (f θ) ∂P) < log (B / δ) := log_lt_log hpos hB'
  have hlog_eq : log (B / δ) = t ^ 2 / (8 * m) + log (1 / δ) := by
    rw [show B / δ = B * (1 / δ) by ring, log_mul hB_pos.ne' (one_div_pos.mpr hδ).ne', log_exp]
  have hf_eq : ∫ θ, f θ ∂Q = t * (∫ θ, trueRisk ℓ D θ ∂Q - ∫ θ, empiricalRisk ℓ S θ ∂Q) := by
    simp only [f, integral_const_mul,
      integral_sub (integrable_trueRisk_of_measurable hℓ hℓ01 Q)
        (integrable_empiricalRisk_of_measurable hℓ hℓ01 S Q)]
  linarith

/-- **Linear PAC-Bayes–Hoeffding bound (`PAC-Bayes-λ`, upper tail)** [Catoni2007]
[Alquier2024, Theorem 2.1] (locators unverified): for any measurable `Θ`, inverse temperature
`lam > 0`, `m ≥ 1`, and `δ > 0`, with probability at least `1 - δ`, every posterior `Q` with
`KL(Q ‖ P) < ∞` satisfies
`𝔼_Q L_D ≤ 𝔼_Q L_S + (KL(Q ‖ P) + log (1 / δ)) / lam + lam / (8 * m)`. -/
theorem measure_pi_exists_hoeffding_integral_risk_gt
    (hℓ : Measurable (Function.uncurry ℓ)) (hℓ01 : ∀ θ z, ℓ θ z ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam) (P : Measure Θ) [IsProbabilityMeasure P]
    {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure Θ, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ ∫ θ, empiricalRisk ℓ S θ ∂Q +
        ((klDiv Q P).toReal + log (1 / δ)) / lam + lam / (8 * m) <
        ∫ θ, trueRisk ℓ D θ ∂Q} ≤ ENNReal.ofReal δ := by
  refine (measure_mono fun S hS => ?_).trans (measure_pi_hoeffding_core hℓ hℓ01 hm lam P hδ)
  obtain ⟨Q, hQ, hQP, hlt⟩ := hS
  refine ⟨Q, hQ, hQP, ?_⟩
  have hmul := mul_lt_mul_of_pos_left hlt hlam
  have heq : lam * (lam / (8 * (m : ℝ))) = lam ^ 2 / (8 * m) := by ring
  have hdiv : lam * (((klDiv Q P).toReal + log (1 / δ)) / lam) =
      (klDiv Q P).toReal + log (1 / δ) := mul_div_cancel₀ _ hlam.ne'
  linarith [show lam * (∫ θ, empiricalRisk ℓ S θ ∂Q +
      ((klDiv Q P).toReal + log (1 / δ)) / lam + lam / (8 * m)) =
      lam * ∫ θ, empiricalRisk ℓ S θ ∂Q +
        lam * (((klDiv Q P).toReal + log (1 / δ)) / lam) + lam * (lam / (8 * m)) by ring]

/-- **Linear PAC-Bayes–Hoeffding bound (`PAC-Bayes-λ`, lower tail)** [Catoni2007]
[Alquier2024, Theorem 2.1] (locators unverified): with probability at least `1 - δ`, every
posterior `Q` with `KL(Q ‖ P) < ∞` satisfies
`𝔼_Q L_S ≤ 𝔼_Q L_D + (KL(Q ‖ P) + log (1 / δ)) / lam + lam / (8 * m)`. -/
theorem measure_pi_exists_hoeffding_integral_risk_lt
    (hℓ : Measurable (Function.uncurry ℓ)) (hℓ01 : ∀ θ z, ℓ θ z ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam) (P : Measure Θ) [IsProbabilityMeasure P]
    {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure Θ, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ ∫ θ, trueRisk ℓ D θ ∂Q +
        ((klDiv Q P).toReal + log (1 / δ)) / lam + lam / (8 * m) <
        ∫ θ, empiricalRisk ℓ S θ ∂Q} ≤ ENNReal.ofReal δ := by
  refine (measure_mono fun S hS => ?_).trans (measure_pi_hoeffding_core hℓ hℓ01 hm (-lam) P hδ)
  obtain ⟨Q, hQ, hQP, hlt⟩ := hS
  refine ⟨Q, hQ, hQP, ?_⟩
  have hmul := mul_lt_mul_of_pos_left hlt hlam
  have hdiv : lam * (((klDiv Q P).toReal + log (1 / δ)) / lam) =
      (klDiv Q P).toReal + log (1 / δ) := mul_div_cancel₀ _ hlam.ne'
  have hsq : (-lam) ^ 2 / (8 * (m : ℝ)) = lam * (lam / (8 * m)) := by ring
  have hneg : -lam * (∫ θ, trueRisk ℓ D θ ∂Q - ∫ θ, empiricalRisk ℓ S θ ∂Q) =
      lam * ∫ θ, empiricalRisk ℓ S θ ∂Q - lam * ∫ θ, trueRisk ℓ D θ ∂Q := by ring
  linarith [show lam * (∫ θ, trueRisk ℓ D θ ∂Q +
      ((klDiv Q P).toReal + log (1 / δ)) / lam + lam / (8 * m)) =
      lam * ∫ θ, trueRisk ℓ D θ ∂Q +
        lam * (((klDiv Q P).toReal + log (1 / δ)) / lam) + lam * (lam / (8 * m)) by ring]

/-! ### Gibbs posterior excess-risk oracle inequalities -/

private theorem integrable_exp_neg_empiricalRisk {ℓ : Θ → Z → ℝ}
    (hℓ : Measurable (Function.uncurry ℓ)) (hℓ01 : ∀ θ z, ℓ θ z ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (S : Fin m → Z) {lam : ℝ} (hlam : 0 < lam)
    (P : Measure Θ) [IsProbabilityMeasure P] :
    Integrable (fun θ => exp (-lam * empiricalRisk ℓ S θ)) P :=
  Integrable.of_mem_Icc 0 1
    (measurable_const.mul (measurable_empiricalRisk_arg hℓ S)).exp.aemeasurable
    (ae_of_all _ fun θ => ⟨(exp_pos _).le,
      exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam.le)
        (empiricalRisk_mem_Icc ℓ S (hℓ01 θ)).1)⟩)

omit [IsProbabilityMeasure D] in
/-- Shared sample-wise step deriving an excess-risk inequality for the Gibbs posterior `Q̂ S`
from the upper Hoeffding bound on `Q̂ S` and any empirical-risk bound on a comparator `Q`. -/
private theorem gibbs_oracle_combine
    (hℓ : Measurable (Function.uncurry ℓ)) (hℓ01 : ∀ θ z, ℓ θ z ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (S : Fin m → Z) {lam δ : ℝ} (hlam : 0 < lam)
    {P Q : Measure Θ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hQP : klDiv Q P ≠ ⊤)
    (hnot1 : S ∉ {S' | ∃ Q' : Measure Θ, IsProbabilityMeasure Q' ∧ klDiv Q' P ≠ ⊤ ∧
      ∫ θ, empiricalRisk ℓ S' θ ∂Q' +
        ((klDiv Q' P).toReal + log (1 / (δ / 2))) / lam + lam / (8 * m) <
      ∫ θ, trueRisk ℓ D θ ∂Q'})
    {b : ℝ} (hgood2 : ∫ θ, empiricalRisk ℓ S θ ∂Q ≤
      ∫ θ, trueRisk ℓ D θ ∂Q + (b + log (1 / (δ / 2))) / lam + lam / (8 * m)) :
    ∫ θ, trueRisk ℓ D θ ∂(P.tilted fun θ => -lam * empiricalRisk ℓ S θ) ≤
      ∫ θ, trueRisk ℓ D θ ∂Q + ((klDiv Q P).toReal + b) / lam +
        lam / (4 * m) + 2 * log (2 / δ) / lam := by
  set Qhat := P.tilted fun θ => -lam * empiricalRisk ℓ S θ
  have hexp := integrable_exp_neg_empiricalRisk hℓ hℓ01 S hlam P
  have : IsProbabilityMeasure Qhat := isProbabilityMeasure_tilted hexp
  have hhat_emp : Integrable (empiricalRisk ℓ S) Qhat :=
    integrable_empiricalRisk_of_measurable hℓ hℓ01 S Qhat
  have hhat_kl : klDiv Qhat P ≠ ⊤ :=
    Cslib.Probability.klDiv_tilted_self_ne_top hexp (hhat_emp.const_mul (-lam))
  have hgood1 : ∫ θ, trueRisk ℓ D θ ∂Qhat ≤ ∫ θ, empiricalRisk ℓ S θ ∂Qhat +
      ((klDiv Qhat P).toReal + log (1 / (δ / 2))) / lam + lam / (8 * m) := by
    by_contra hbad
    push Not at hbad
    exact hnot1 ⟨Qhat, inferInstance, hhat_kl, hbad⟩
  have hopt : ∫ θ, empiricalRisk ℓ S θ ∂Qhat + (klDiv Qhat P).toReal / lam ≤
      ∫ θ, empiricalRisk ℓ S θ ∂Q + (klDiv Q P).toReal / lam :=
    Cslib.Probability.freeEnergy_tilted_le (g := empiricalRisk ℓ S) hQP hlam
      (integrable_empiricalRisk_of_measurable hℓ hℓ01 S Q) hexp hhat_emp
  have hlog_eq : 1 / (δ / 2) = 2 / δ := by ring
  rw [hlog_eq] at hgood1 hgood2
  have h1' : ((klDiv Qhat P).toReal + log (2 / δ)) / lam =
      (klDiv Qhat P).toReal / lam + log (2 / δ) / lam := add_div _ _ _
  have h2' : (b + log (2 / δ)) / lam = b / lam + log (2 / δ) / lam := add_div _ _ _
  have h3' : ((klDiv Q P).toReal + b) / lam = (klDiv Q P).toReal / lam + b / lam := add_div _ _ _
  have hm_eq : lam / (8 * (m : ℝ)) + lam / (8 * (m : ℝ)) = lam / (4 * (m : ℝ)) := by ring
  have hlg2 : 2 * log (2 / δ) / lam = log (2 / δ) / lam + log (2 / δ) / lam := by ring
  linarith

/-- **Uniform oracle inequality for the Gibbs posterior** [Alquier2024] [Catoni2007] (locators
unverified): letting `Q̂ S := P.tilted (fun θ => -lam * empiricalRisk ℓ S θ)`, with probability
at least `1 - δ` over `S ~ D^m`, **simultaneously for every** comparator probability measure `Q`
with `KL(Q ‖ P) < ∞`,
`𝔼_{Q̂} L_D ≤ 𝔼_Q L_D + 2 * KL(Q ‖ P) / lam + lam / (4 * m) + 2 * log (2 / δ) / lam`. -/
theorem measure_pi_gibbs_oracle_gt
    (hℓ : Measurable (Function.uncurry ℓ)) (hℓ01 : ∀ θ z, ℓ θ z ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam) (P : Measure Θ) [IsProbabilityMeasure P]
    {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure Θ, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ ∫ θ, trueRisk ℓ D θ ∂Q + 2 * (klDiv Q P).toReal / lam +
        lam / (4 * m) + 2 * log (2 / δ) / lam <
        ∫ θ, trueRisk ℓ D θ ∂(P.tilted fun θ => -lam * empiricalRisk ℓ S θ)} ≤
      ENNReal.ofReal δ := by
  let E₁ : Set (Fin m → Z) := {S | ∃ Q : Measure Θ, IsProbabilityMeasure Q ∧
    klDiv Q P ≠ ⊤ ∧ ∫ θ, empiricalRisk ℓ S θ ∂Q +
      ((klDiv Q P).toReal + log (1 / (δ / 2))) / lam + lam / (8 * m) <
      ∫ θ, trueRisk ℓ D θ ∂Q}
  let E₂ : Set (Fin m → Z) := {S | ∃ Q : Measure Θ, IsProbabilityMeasure Q ∧
    klDiv Q P ≠ ⊤ ∧ ∫ θ, trueRisk ℓ D θ ∂Q +
      ((klDiv Q P).toReal + log (1 / (δ / 2))) / lam + lam / (8 * m) <
      ∫ θ, empiricalRisk ℓ S θ ∂Q}
  refine (measure_mono (t := E₁ ∪ E₂) ?_).trans ((measure_union_le E₁ E₂).trans ?_)
  · rintro S ⟨Q, hQ, hQP, hlt⟩
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    have hgood2 : ∫ θ, empiricalRisk ℓ S θ ∂Q ≤ ∫ θ, trueRisk ℓ D θ ∂Q +
        ((klDiv Q P).toReal + log (1 / (δ / 2))) / lam + lam / (8 * m) := by
      by_contra hbad; push Not at hbad; exact hnot.2 ⟨Q, hQ, hQP, hbad⟩
    have hc := gibbs_oracle_combine (D := D) hℓ hℓ01 S hlam hQP hnot.1 hgood2
    have hkl : ((klDiv Q P).toReal + (klDiv Q P).toReal) / lam =
        2 * (klDiv Q P).toReal / lam := by ring
    linarith
  · refine (add_le_add
      (measure_pi_exists_hoeffding_integral_risk_gt (D := D) hℓ hℓ01 hm hlam P (half_pos hδ))
      (measure_pi_exists_hoeffding_integral_risk_lt (D := D) hℓ hℓ01 hm hlam P (half_pos hδ))
      ).trans_eq ?_
    rw [← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le, add_halves]

/-- **Sharp oracle inequality for the Gibbs posterior against a fixed comparator `Q`**
[Alquier2024] (locator unverified): because `Q` is fixed before observing `S`, Hoeffding's lower
tail applies with prior `Q` (`KL(Q ‖ Q) = 0`), reducing the factor on `KL(Q ‖ P)` from `2` to
**`1`**:
`𝔼_{Q̂} L_D ≤ 𝔼_Q L_D + KL(Q ‖ P) / lam + lam / (4 * m) + 2 * log (2 / δ) / lam`. -/
theorem measure_pi_gibbs_fixed_oracle_gt
    (hℓ : Measurable (Function.uncurry ℓ)) (hℓ01 : ∀ θ z, ℓ θ z ∈ Icc (0 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam) (P Q : Measure Θ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hQP : klDiv Q P ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∫ θ, trueRisk ℓ D θ ∂Q +
        (klDiv Q P).toReal / lam + lam / (4 * m) + 2 * log (2 / δ) / lam <
        ∫ θ, trueRisk ℓ D θ ∂(P.tilted fun θ => -lam * empiricalRisk ℓ S θ)} ≤
      ENNReal.ofReal δ := by
  let E₁ : Set (Fin m → Z) := {S | ∃ Q' : Measure Θ, IsProbabilityMeasure Q' ∧
    klDiv Q' P ≠ ⊤ ∧ ∫ θ, empiricalRisk ℓ S θ ∂Q' +
      ((klDiv Q' P).toReal + log (1 / (δ / 2))) / lam + lam / (8 * m) <
      ∫ θ, trueRisk ℓ D θ ∂Q'}
  let E₂ : Set (Fin m → Z) := {S | ∃ Q' : Measure Θ, IsProbabilityMeasure Q' ∧
    klDiv Q' Q ≠ ⊤ ∧ ∫ θ, trueRisk ℓ D θ ∂Q' +
      ((klDiv Q' Q).toReal + log (1 / (δ / 2))) / lam + lam / (8 * m) <
      ∫ θ, empiricalRisk ℓ S θ ∂Q'}
  refine (measure_mono (t := E₁ ∪ E₂) ?_).trans ((measure_union_le E₁ E₂).trans ?_)
  · intro S hlt
    change ∫ θ, trueRisk ℓ D θ ∂Q + (klDiv Q P).toReal / lam + lam / (4 * m) +
        2 * log (2 / δ) / lam <
      ∫ θ, trueRisk ℓ D θ ∂(P.tilted fun θ => -lam * empiricalRisk ℓ S θ) at hlt
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    have hgood2 : ∫ θ, empiricalRisk ℓ S θ ∂Q ≤ ∫ θ, trueRisk ℓ D θ ∂Q +
        (0 + log (1 / (δ / 2))) / lam + lam / (8 * m) := by
      by_contra hbad
      push Not at hbad
      exact hnot.2 ⟨Q, inferInstance, by simp, by simpa using hbad⟩
    have hc := gibbs_oracle_combine (D := D) hℓ hℓ01 S hlam hQP hnot.1 hgood2
    rw [add_zero] at hc
    linarith
  · refine (add_le_add
      (measure_pi_exists_hoeffding_integral_risk_gt (D := D) hℓ hℓ01 hm hlam P (half_pos hδ))
      (measure_pi_exists_hoeffding_integral_risk_lt (D := D) hℓ hℓ01 hm hlam Q (half_pos hδ))
      ).trans_eq ?_
    rw [← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le, add_halves]

end GeneralPACBayes

end Cslib.MachineLearning.PACBayes
