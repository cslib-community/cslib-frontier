/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.BernsteinPi
public import CslibFrontier.MachineLearning.LossMinimization.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Variance-sensitive Bernstein online-to-batch conversion

Refines the Azuma–Hoeffding high-probability online-to-batch conversion in
`CslibFrontier.MachineLearning.OnlineLearning.HighProbabilityOnlineToBatch` by replacing worst-case
sub-Gaussian step widths with the product-filtration Bernstein bound
(`ProbabilityTheory.measure_sum_gt_sqrt_add_le_pi`):

Run an online learner on an i.i.d. sample `S = (z₀, …, z_{T-1})` from `D`. In round `t` the learner
commits to a function `f t S : Z → ℝ` depending only on `z₀, …, z_{t-1}` with values in `[a, b]`
and conditional variance `∫ z, (f t S z - ∫ z', f t S z' ∂D)² ∂D ≤ s2 t`. With probability at least
`1 - δ`,

  `(1 / T) ∑ t, ∫ f t S dD ≤ (1 / T) ∑ t, f t S (S t) +
    (1 / T) √(2 (∑ t, s2 t) ln (1 / δ)) + 2 (b - a) ln (1 / δ) / (3 T)`

(`measureReal_average_integral_gt_le_bernstein`). Under uniform variance bound `s2` across rounds,
the leading deviation term scales with `√(2 s2 ln (1 / δ) / T)` instead of `(b - a) √(ln (1 / δ) /
(2 T))`, and vanishes completely (`2 (b - a) ln (1 / δ) / (3 T)`) in the zero-variance regime
`s2 = 0` ([CesaBianchiConconiGentile2004, Section III]).

## Main results

* `Cslib.MachineLearning.OnlineLearning.measureReal_sum_integral_gt_le_bernstein`,
  `Cslib.MachineLearning.OnlineLearning.measureReal_average_integral_gt_le_bernstein`: Bernstein
  online-to-batch conversion in sum and average form with per-round variance bounds `s2 t`.
* `Cslib.MachineLearning.OnlineLearning.measureReal_average_trueRisk_gt_le_bernstein`:
  specialization to the true risks of an online learner's iterates under uniform conditional
  variance `s2`.
* `Cslib.MachineLearning.OnlineLearning.measureReal_trueRisk_average_gt_le_bernstein`: excess true
  risk bound `L_D u + R / T + √(2 s2 ln (1 / δ) / T) + 4 c ln (1 / δ) / (3 T)` for the average
  iterate on convex losses.

## References

* [N. Cesa-Bianchi, A. Conconi, C. Gentile, *On the generalization ability of on-line learning
  algorithms*][CesaBianchiConconiGentile2004]
* [D. A. Freedman, *On tail probabilities for martingales*][Freedman1975]
-/

public section

open MeasureTheory ProbabilityTheory Real Finset
open scoped BigOperators

namespace Cslib.MachineLearning.OnlineLearning

variable {Z : Type*} [MeasurableSpace Z] {D : Measure Z} [IsProbabilityMeasure D] {T : ℕ}

/-- **Bernstein online-to-batch conversion, sum form**: if `f t S` depends only on examples before
round `t`, takes values in `[a, b]` (`a ≤ b`), and has conditional variance at most `s2 t ≥ 0`
under `D`, then with probability at least `1 - δ` (`δ ∈ (0, 1]`),
`∑ t, ∫ f t S dD ≤ ∑ t, f t S (S t) + √(2 (∑ t, s2 t) ln (1 / δ)) + 2 (b - a) ln (1 / δ) / 3`. -/
theorem measureReal_sum_integral_gt_le_bernstein {f : Fin T → (Fin T → Z) → Z → ℝ}
    (hf : ∀ t, Measurable (Function.uncurry (f t)))
    (hfresh : ∀ t s, t ≤ s → ∀ S z, f t (Function.update S s z) = f t S)
    {a b : ℝ} (hab_le : a ≤ b) (hab : ∀ t S z, f t S z ∈ Set.Icc a b)
    {s2 : Fin T → ℝ} (hσ : ∀ t, 0 ≤ s2 t)
    (hvar : ∀ t S, ∫ z, (f t S z - ∫ z', f t S z' ∂D) ^ 2 ∂D ≤ s2 t)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let L := log (1 / δ)
    (Measure.pi fun _ : Fin T => D).real
      {S | ∑ t, f t S (S t) + √(2 * (∑ t, s2 t) * L) + 2 * (b - a) * L / 3 <
        ∑ t, ∫ z, f t S z ∂D} ≤ δ := by
  intro L
  have hint_f (t : Fin T) (S : Fin T → Z) : Integrable (f t S) D :=
    Integrable.of_mem_Icc a b ((hf t).comp (measurable_const.prodMk measurable_id)).aemeasurable
      (Filter.Eventually.of_forall (hab t S))
  set Y : Fin T → (Fin T → Z) → ℝ := fun t S => ∫ z, f t S z ∂D - f t S (S t)
  have hY_meas (t : Fin T) : Measurable (Y t) :=
    (hf t).stronglyMeasurable.integral_prod_right'.measurable.sub
      ((hf t).comp (measurable_id.prodMk (measurable_pi_apply t)))
  have hY_Icc (t : Fin T) (S : Fin T → Z) (z : Z) :
      Y t (Function.update S t z) ∈ Set.Icc (a - b) (b - a) := by
    simp only [Y, hfresh t t le_rfl, Function.update_self, Set.mem_Icc]
    have hlo : a ≤ ∫ z', f t S z' ∂D := by
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
        integral_mono (integrable_const a) (hint_f t S) fun z' => (hab t S z').1
    have hhi : ∫ z', f t S z' ∂D ≤ b := by
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
        integral_mono (hint_f t S) (integrable_const b) fun z' => (hab t S z').2
    exact ⟨by linarith [(hab t S z).2], by linarith [(hab t S z).1]⟩
  have hbern := measure_sum_gt_sqrt_add_le_pi (μ := fun _ : Fin T => D) (Y := Y)
    (b := b - a) (s2 := s2) (sub_nonneg.mpr hab_le) hσ hδ hδ1 hY_meas
    (fun t s hts S z => by simp only [Y, hfresh t s hts.le, Function.update_of_ne hts.ne])
    (fun t S => Integrable.of_mem_Icc (a - b) (b - a)
      ((hY_meas t).comp (measurable_update S)).aemeasurable
      (Filter.Eventually.of_forall (hY_Icc t S)))
    (fun t S => Integrable.of_mem_Icc 0 ((b - a) ^ 2)
      (((hY_meas t).comp (measurable_update S)).pow_const 2).aemeasurable
      (Filter.Eventually.of_forall fun z => ⟨sq_nonneg _, by
        have hz := hY_Icc t S z
        nlinarith [hz.1, hz.2]⟩))
    (fun t S => by
      simp only [Y, hfresh t t le_rfl, Function.update_self]
      rw [integral_sub (integrable_const _) (hint_f t S), integral_const, probReal_univ,
        smul_eq_mul, one_mul, sub_self])
    (fun t S => by
      have hz := hY_Icc t S (S t)
      rw [Function.update_eq_self] at hz
      exact hz.2)
    (fun t S => by
      simp only [Y, hfresh t t le_rfl, Function.update_self]
      have hsq_eq : (fun z => (∫ z', f t S z' ∂D - f t S z) ^ 2) =
          fun z => (f t S z - ∫ z', f t S z' ∂D) ^ 2 := funext fun z => by ring
      rw [hsq_eq]
      exact hvar t S)
  refine le_trans (measureReal_mono fun S hS => ?_) hbern
  simp only [Set.mem_ofPred_eq, Y, Finset.sum_sub_distrib] at hS ⊢
  linarith

/-- **Bernstein online-to-batch conversion, average form**: if `f t S` depends only on examples
before round `t`, takes values in `[a, b]`, and has conditional variance at most `s2 t ≥ 0`, then
with probability at least `1 - δ` (`δ ∈ (0, 1]`),
`(1 / T) ∑ t, ∫ f t S dD ≤ (1 / T) ∑ t, f t S (S t) +
  (1 / T) √(2 (∑ t, s2 t) ln (1 / δ)) + 2 (b - a) ln (1 / δ) / (3 T)`. -/
theorem measureReal_average_integral_gt_le_bernstein {f : Fin T → (Fin T → Z) → Z → ℝ}
    (hf : ∀ t, Measurable (Function.uncurry (f t)))
    (hfresh : ∀ t s, t ≤ s → ∀ S z, f t (Function.update S s z) = f t S)
    {a b : ℝ} (hab : ∀ t S z, f t S z ∈ Set.Icc a b)
    {s2 : Fin T → ℝ} (hσ : ∀ t, 0 ≤ s2 t)
    (hvar : ∀ t S, ∫ z, (f t S z - ∫ z', f t S z' ∂D) ^ 2 ∂D ≤ s2 t)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let L := log (1 / δ)
    (Measure.pi fun _ : Fin T => D).real
      {S | (T : ℝ)⁻¹ * ∑ t, f t S (S t) + (T : ℝ)⁻¹ * √(2 * (∑ t, s2 t) * L) +
        2 * (b - a) * L / (3 * T) < (T : ℝ)⁻¹ * ∑ t, ∫ z, f t S z ∂D} ≤ δ := by
  intro L
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [hδ.le]
  · have hTr : (0 : ℝ) < T := by exact_mod_cast hT
    have hab_le : a ≤ b := by
      obtain ⟨z⟩ := nonempty_of_isProbabilityMeasure D
      obtain ⟨S⟩ := nonempty_of_isProbabilityMeasure (Measure.pi fun _ : Fin T => D)
      exact (hab ⟨0, hT⟩ S z).1.trans (hab ⟨0, hT⟩ S z).2
    refine le_trans (measureReal_mono fun S hS => ?_)
      (measureReal_sum_integral_gt_le_bernstein hf hfresh hab_le hab hσ hvar hδ hδ1)
    simp only [Set.mem_ofPred_eq] at hS ⊢
    have hmul := mul_lt_mul_of_pos_left hS hTr
    have hcancel (x : ℝ) : (T : ℝ) * ((T : ℝ)⁻¹ * x) = x := by
      rw [← mul_assoc, mul_inv_cancel₀ hTr.ne', one_mul]
    have hdiv : (T : ℝ) * (2 * (b - a) * L / (3 * T)) = 2 * (b - a) * L / 3 := by
      field_simp [hTr.ne']
    rw [mul_add, mul_add, hcancel, hcancel, hcancel, hdiv] at hmul
    exact hmul

/-- **Bernstein online-to-batch conversion for the iterates of an online learner**: if `w t S`
depends only on examples before round `t`, `ℓ (w t S) z ∈ [a, b]`, and the conditional variance of
`ℓ (w t S)` under `D` is at most `s2 ≥ 0`, then with probability at least `1 - δ` (`δ ∈ (0, 1]`),
`(1 / T) ∑ t, L_D (w t S) ≤ (1 / T) ∑ t, ℓ (w t S) (S t) +
  √(2 s2 ln (1 / δ) / T) + 2 (b - a) ln (1 / δ) / (3 T)`. -/
theorem measureReal_average_trueRisk_gt_le_bernstein {W : Type*} [MeasurableSpace W]
    {ℓ : W → Z → ℝ} (hℓ : Measurable (Function.uncurry ℓ)) {w : Fin T → (Fin T → Z) → W}
    (hwm : ∀ t, Measurable (w t))
    (hfresh : ∀ t s, t ≤ s → ∀ S z, w t (Function.update S s z) = w t S)
    {a b s2 : ℝ} (hab : ∀ t S z, ℓ (w t S) z ∈ Set.Icc a b) (hσ : 0 ≤ s2)
    (hvar : ∀ t S, ∫ z, (ℓ (w t S) z - trueRisk ℓ D (w t S)) ^ 2 ∂D ≤ s2)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let L := log (1 / δ)
    (Measure.pi fun _ : Fin T => D).real
      {S | (T : ℝ)⁻¹ * ∑ t, ℓ (w t S) (S t) + √(2 * s2 * L / T) +
        2 * (b - a) * L / (3 * T) < (T : ℝ)⁻¹ * ∑ t, trueRisk ℓ D (w t S)} ≤ δ := by
  intro L
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [hδ.le]
  · have hTr : (0 : ℝ) < T := by exact_mod_cast hT
    have hL : 0 ≤ L := log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    have hgen := measureReal_average_integral_gt_le_bernstein (D := D)
      (f := fun t S z => ℓ (w t S) z) (s2 := fun _ => s2)
      (fun t => hℓ.comp (((hwm t).comp measurable_fst).prodMk measurable_snd))
      (fun t s hts S z => by simp only [hfresh t s hts]) hab (fun _ => hσ)
      (fun t S => by simpa only [trueRisk_def] using hvar t S) hδ hδ1
    refine le_trans (measureReal_mono fun S hS => ?_) hgen
    have hsqrt : (T : ℝ)⁻¹ * √(2 * (∑ _ : Fin T, s2) * L) = √(2 * s2 * L / T) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [show (T : ℝ)⁻¹ = √(((T : ℝ)⁻¹) ^ 2) by rw [sqrt_sq (inv_nonneg.mpr hTr.le)],
        ← sqrt_mul (by positivity)]
      congr 1
      field_simp [hTr.ne']
    simp only [Set.mem_ofPred_eq, trueRisk_def] at hS ⊢
    rw [hsqrt]
    exact hS

/-- **Bernstein online-to-batch conversion for convex losses**: let `ℓ · z` be convex on a convex
set `K`, `u ∈ K` with `ℓ u` integrable, `|ℓ w z - ℓ u z| ≤ c` on `K`, and let the excess loss
`z ↦ ℓ (w t S) z - ℓ u z` have conditional variance at most `s2 ≥ 0`. If `w t S ∈ K` depends only on
examples before round `t` and has cumulative online regret at most `R`, then for `T > 0` and
`δ ∈ (0, 1]`, with probability at least `1 - δ`, the average iterate has true risk at most
`L_D u + R / T + √(2 s2 ln (1 / δ) / T) + 4 c ln (1 / δ) / (3 T)`. -/
theorem measureReal_trueRisk_average_gt_le_bernstein (hT : 0 < T) {E : Type*} [AddCommGroup E]
    [Module ℝ E] [MeasurableSpace E] {K : Set E} (hK : Convex ℝ K) {ℓ : E → Z → ℝ}
    (hℓ : Measurable (Function.uncurry ℓ)) (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z)
    {u : E} (hui : Integrable (ℓ u) D) {c s2 : ℝ}
    (hc : ∀ w ∈ K, ∀ z, |ℓ w z - ℓ u z| ≤ c) (hσ : 0 ≤ s2)
    {w : Fin T → (Fin T → Z) → E} (hwK : ∀ t S, w t S ∈ K) (hwm : ∀ t, Measurable (w t))
    (hfresh : ∀ t s, t ≤ s → ∀ S z, w t (Function.update S s z) = w t S)
    (hvar : ∀ t S, ∫ z, ((ℓ (w t S) z - ℓ u z) -
      ∫ z', (ℓ (w t S) z' - ℓ u z') ∂D) ^ 2 ∂D ≤ s2)
    {R : ℝ} (hR : ∀ S, ∑ t, (ℓ (w t S) (S t) - ℓ u (S t)) ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let L := log (1 / δ)
    (Measure.pi fun _ : Fin T => D).real
      {S | trueRisk ℓ D u + R / T + √(2 * s2 * L / T) + 4 * c * L / (3 * T) <
        trueRisk ℓ D ((T : ℝ)⁻¹ • ∑ t, w t S)} ≤ δ := by
  intro L
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hL : 0 ≤ L := log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hint : ∀ v ∈ K, Integrable (ℓ v) D := fun v hv =>
    (hui.norm.add (integrable_const c)).mono'
      (hℓ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        have h1 := hc v hv z
        have h2 := abs_sub_abs_le_abs_sub (ℓ v z) (ℓ u z)
        simp only [Real.norm_eq_abs, Pi.add_apply]
        linarith)
  have hgen := measureReal_average_trueRisk_gt_le_bernstein (D := D)
    (ℓ := fun w z => ℓ w z - ℓ u z)
    (hℓ.sub (hℓ.comp ((measurable_const (a := u)).prodMk measurable_snd)))
    hwm hfresh (a := -c) (b := c) (s2 := s2)
    (fun t S z => abs_le.1 (hc _ (hwK t S) z)) hσ
    (fun t S => by simpa only [trueRisk_def] using hvar t S) hδ hδ1
  dsimp only at hgen
  refine le_trans (measureReal_mono (Set.ofPred_subset_ofPred.2 fun S hS => ?_)) hgen
  have hjensen : trueRisk ℓ D ((T : ℝ)⁻¹ • ∑ t, w t S) ≤
      (T : ℝ)⁻¹ * ∑ t, trueRisk ℓ D (w t S) := by
    have h := (convexOn_trueRisk hK hconv hint).map_sum_le (t := Finset.univ)
      (w := fun _ => (T : ℝ)⁻¹) (p := fun t => w t S) (fun _ _ => inv_nonneg.2 hTr.le)
      (by simp [hTr.ne']) (fun t _ => hwK t S)
    simpa only [Finset.smul_sum, Finset.mul_sum, smul_eq_mul] using h
  have hrisk (t : Fin T) : trueRisk (fun w z => ℓ w z - ℓ u z) D (w t S) =
      trueRisk ℓ D (w t S) - trueRisk ℓ D u := by
    simp only [trueRisk_def]
    exact integral_sub (hint _ (hwK t S)) hui
  have hsum_risk : (T : ℝ)⁻¹ * ∑ t, trueRisk (fun w z => ℓ w z - ℓ u z) D (w t S) =
      (T : ℝ)⁻¹ * ∑ t, trueRisk ℓ D (w t S) - trueRisk ℓ D u := by
    simp only [hrisk, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hTr.ne', one_mul]
  have honline : (T : ℝ)⁻¹ * ∑ t, (ℓ (w t S) (S t) - ℓ u (S t)) ≤ R / T := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hR S) (inv_nonneg.2 hTr.le)
  have hlin : 2 * (c - -c) * L / (3 * T) = 4 * c * L / (3 * T) := by ring
  rw [hsum_risk, hlin]
  linarith

end Cslib.MachineLearning.OnlineLearning
