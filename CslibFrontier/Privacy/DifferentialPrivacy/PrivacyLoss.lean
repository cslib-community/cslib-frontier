/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Privacy.DifferentialPrivacy.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Hyperbolic
import CslibFrontier.Tactic.ENNRealToReal
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Moments of the privacy loss

For mass functions `p`, `q` on a countable type, `lossMoment t p q = ∑ a, p a · (p a / q a) ^ t`
is the moment generating function of the privacy loss `ln (p a / q a)` [DworkRoth2014, §2.3].
Markov's inequality (`Cslib.Probability.tsum_tsub_le_mul_rpow_tsum`) turns a moment bound directly
into a truncated-excess / hockey-stick bound (`tsum_tsub_le_lossMoment`,
`hockeyStick_le_lossMoment`). When the likelihood ratio lies in `[e^{-ε}, e^ε]`, convexity of
`x ↦ x ^ (1 + t)` bounds the moment by `cosh (ε t) + tanh (ε / 2) · sinh (ε t)` per unit of mass
(`lossMoment_le_of_le_mul`), hence by `exp (tanh (ε / 2) · ε t + (ε t)² / 2)`
(`lossMoment_le_exp`). The last step is Hoeffding's lemma for the two-point law on `±ε t`
(`Real.cosh_add_mul_sinh_le_exp`; compare `Cslib.one_sub_mul_exp_add_mul_exp_le`). This is the
per-round step of the proof of advanced composition; the approximate-DP sub-probability splitting
lives in `CslibFrontier.Probability.HockeyStick` (`exists_subprob_of_hockeyStick_le`).

## Main definitions

* `Cslib.Privacy.lossMoment`: the moment generating function of the privacy loss.

## Main results

* `Cslib.Privacy.tsum_tsub_le_lossMoment`, `Cslib.Privacy.hockeyStick_le_lossMoment`: Markov's
  inequality from the privacy-loss moment to truncated excess and `PMF.hockeyStick`.
* `Cslib.Privacy.lossMoment_le_of_le_mul`, `Cslib.Privacy.lossMoment_le_exp`: the moment bound
  for an `ε`-close pair.

## References

* [DworkRoth2014]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

universe u

variable {α : Type u}

section Moment

/-- The privacy-loss moment `∑ a, p a · (p a / q a) ^ t`: for probability mass functions `p`
and `q`, the moment generating function `E_{a ∼ p}[exp (t · L(a))]` of the privacy loss
`L(a) = ln (p a / q a)` [DworkRoth2014, §2.3]. The masses may be sub-probabilities. -/
noncomputable def lossMoment (t : ℝ) (p q : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, p a * (p a / q a) ^ t

theorem lossMoment_def (t : ℝ) (p q : α → ℝ≥0∞) :
    lossMoment t p q = ∑' a, p a * (p a / q a) ^ t := by
  rw [lossMoment]

/-- Markov's inequality for the privacy loss: for `t ≥ 0` and any mass functions `p, q`,
`∑' a, (p a - e^{ε'} · q a) ≤ e^{-t ε'} · lossMoment t p q`. -/
theorem tsum_tsub_le_lossMoment {t : ℝ} (ht : 0 ≤ t) (ε' : ℝ) (p q : α → ℝ≥0∞) :
    ∑' a, (p a - ENNReal.ofReal (Real.exp ε') * q a) ≤
      ENNReal.ofReal (Real.exp (-(t * ε'))) * lossMoment t p q :=
  Probability.tsum_tsub_le_mul_rpow_tsum ht ε' p q

/-- Markov's inequality for `PMF`s: `hockeyStick (e^{ε'}) p q ≤ e^{-t ε'} · lossMoment t p q`. -/
theorem hockeyStick_le_lossMoment {t : ℝ} (ht : 0 ≤ t) (ε' : ℝ) (p q : PMF α) :
    Probability.PMF.hockeyStick (ENNReal.ofReal (Real.exp ε')) p q ≤
      ENNReal.ofReal (Real.exp (-(t * ε'))) * lossMoment t p q :=
  Probability.PMF.hockeyStick_le_mul_rpow_tsum ht ε' p q

end Moment

section Chord

/-- The chord bound for `x ↦ x ^ (1 + t)` on `[E⁻¹, E]`, in real numbers. -/
private theorem mul_div_rpow_add_le {E t P Q : ℝ} (hE : 1 < E) (ht : 0 ≤ t) (hP : 0 < P)
    (hQ : 0 < Q) (hPQ : P ≤ E * Q) (hQP : Q ≤ E * P) :
    P * (P / Q) ^ t + (E ^ t - (E ^ t)⁻¹) / (E - E⁻¹) * Q ≤
      (E * E ^ t - (E * E ^ t)⁻¹) / (E - E⁻¹) * P := by
  have hE0 : 0 < E := by linarith
  have hEinv : E⁻¹ < E := (inv_lt_one_of_one_lt₀ hE).trans hE
  have hD : 0 < E - E⁻¹ := sub_pos.mpr hEinv
  have hw0 : 0 < P / Q := div_pos hP hQ
  have hwle : P / Q ≤ E := by rw [div_le_iff₀ hQ]; exact hPQ
  have hwge : E⁻¹ ≤ P / Q := by
    rw [le_div_iff₀ hQ, inv_mul_le_iff₀ hE0]
    exact hQP
  have ha : 0 ≤ (E - P / Q) / (E - E⁻¹) := div_nonneg (by linarith) hD.le
  have hb : 0 ≤ (P / Q - E⁻¹) / (E - E⁻¹) := div_nonneg (by linarith) hD.le
  have hab : (E - P / Q) / (E - E⁻¹) + (P / Q - E⁻¹) / (E - E⁻¹) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hD.ne']
    ring
  have hconv := (convexOn_rpow (p := 1 + t) (by linarith)).2
    (Set.mem_Ici.mpr (inv_pos.mpr hE0).le) (Set.mem_Ici.mpr hE0.le) ha hb hab
  have hcomb : (E - P / Q) / (E - E⁻¹) * E⁻¹ + (P / Q - E⁻¹) / (E - E⁻¹) * E = P / Q := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD.ne']
    ring
  simp only [smul_eq_mul] at hconv
  rw [hcomb] at hconv
  rw [Real.rpow_add hw0, Real.rpow_one, Real.rpow_add (inv_pos.mpr hE0), Real.rpow_one,
    Real.rpow_add hE0, Real.rpow_one, Real.inv_rpow hE0.le] at hconv
  have hkey : P * (P / Q) ^ t = Q * (P / Q * (P / Q) ^ t) := by
    field_simp
  rw [hkey]
  calc Q * (P / Q * (P / Q) ^ t) + (E ^ t - (E ^ t)⁻¹) / (E - E⁻¹) * Q
      ≤ Q * ((E - P / Q) / (E - E⁻¹) * (E⁻¹ * (E ^ t)⁻¹) +
          (P / Q - E⁻¹) / (E - E⁻¹) * (E * E ^ t)) +
          (E ^ t - (E ^ t)⁻¹) / (E - E⁻¹) * Q := by gcongr
    _ = (E * E ^ t - (E * E ^ t)⁻¹) / (E - E⁻¹) * P := by
        generalize hDdef : E - E⁻¹ = D at *
        have hD0 : D ≠ 0 := hD.ne'
        field_simp
        ring

end Chord

section SingleRound

/-- The moment bound for one round: if the likelihood ratio of `p` and `q` lies in
`[e^{-ε}, e^ε]` and `p` has at most the mass of `q`, then
`lossMoment t p q ≤ (cosh (ε t) + tanh (ε / 2) · sinh (ε t)) · ∑ p`. The bound comes from the
chord of the convex function `x ↦ x ^ (1 + t)` between `e^{-ε}` and `e^ε`, and is attained by
two-point distributions whose likelihood ratio takes only the values `e^{±ε}`. -/
theorem lossMoment_le_of_le_mul {p q : α → ℝ≥0∞} {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hpq : ∀ a, p a ≤ ENNReal.ofReal (Real.exp ε) * q a)
    (hqp : ∀ a, q a ≤ ENNReal.ofReal (Real.exp ε) * p a)
    (hsum : ∑' a, p a ≤ ∑' a, q a) (hfin : ∑' a, q a ≠ ⊤) :
    lossMoment t p q ≤ ENNReal.ofReal (Real.cosh (ε * t) +
      Real.tanh (ε / 2) * Real.sinh (ε * t)) * ∑' a, p a := by
  rw [Real.tanh_half_eq_exp_sub_one_div]
  have hq : ∀ a, q a ≠ ⊤ := ne_top_of_tsum_ne_top hfin
  have hp : ∀ a, p a ≠ ⊤ := fun a => ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq a)) (hpq a)
  rcases hε.eq_or_lt with rfl | hε
  · have heq : ∀ a, p a = q a := fun a => le_antisymm
      (by simpa using hpq a) (by simpa using hqp a)
    simp only [zero_mul, Real.cosh_zero, Real.sinh_zero, mul_zero, add_zero, ENNReal.ofReal_one,
      one_mul, lossMoment]
    refine tsum_le_tsum fun a => ?_
    rw [heq a]
    rcases eq_or_ne (q a) 0 with h0 | h0
    · simp [h0]
    · rw [ENNReal.div_self h0 (hq a), ENNReal.one_rpow, mul_one]
  set E := Real.exp ε
  have hE : 1 < E := Real.one_lt_exp_iff.mpr hε
  have hEinv : E⁻¹ < E := (inv_lt_one_of_one_lt₀ hE).trans hE
  have hD : 0 < E - E⁻¹ := sub_pos.mpr hEinv
  set Y := (E ^ t - (E ^ t)⁻¹) / (E - E⁻¹) with hYdef
  set A := (E * E ^ t - (E * E ^ t)⁻¹) / (E - E⁻¹) with hAdef
  have hF1 : 1 ≤ E ^ t := Real.one_le_rpow hE.le ht
  have hEF1 : 1 ≤ E * E ^ t := one_le_mul_of_one_le_of_one_le hE.le hF1
  have hY : 0 ≤ Y := div_nonneg (sub_nonneg.mpr ((inv_le_one_of_one_le₀ hF1).trans hF1)) hD.le
  have hA : 0 ≤ A := div_nonneg (sub_nonneg.mpr ((inv_le_one_of_one_le₀ hEF1).trans hEF1)) hD.le
  have hpt : ∀ a, p a * (p a / q a) ^ t + ENNReal.ofReal Y * q a ≤ ENNReal.ofReal A * p a := by
    intro a
    rcases eq_or_ne (q a) 0 with hq0 | hq0
    · have hp0 : p a = 0 := by simpa [hq0] using hpq a
      simp [hp0, hq0]
    rcases eq_or_ne (p a) 0 with hp0 | hp0
    · have : q a = 0 := by simpa [hp0] using hqp a
      exact absurd this hq0
    have hP : 0 < (p a).toReal := ENNReal.toReal_pos hp0 (hp a)
    have hQ : 0 < (q a).toReal := ENNReal.toReal_pos hq0 (hq a)
    have hPQ : (p a).toReal ≤ E * (q a).toReal := by ennreal_to_real using hpq a
    have hQP : (q a).toReal ≤ E * (p a).toReal := by ennreal_to_real using hqp a
    have hreal := mul_div_rpow_add_le hE ht hP hQ hPQ hQP
    rw [← ENNReal.ofReal_toReal (hp a), ← ENNReal.ofReal_toReal (hq a),
      ← ENNReal.ofReal_div_of_pos hQ, ENNReal.ofReal_rpow_of_nonneg (div_pos hP hQ).le ht,
      ← ENNReal.ofReal_mul hP.le, ← ENNReal.ofReal_mul hY,
      ← ENNReal.ofReal_add (by positivity) (mul_nonneg hY hQ.le),
      ← ENNReal.ofReal_mul hA]
    exact ENNReal.ofReal_le_ofReal (by simpa only [hYdef, hAdef] using hreal)
  have hsum' : lossMoment t p q + ENNReal.ofReal Y * ∑' a, p a ≤ ENNReal.ofReal A * ∑' a, p a :=
    calc lossMoment t p q + ENNReal.ofReal Y * ∑' a, p a
        ≤ lossMoment t p q + ENNReal.ofReal Y * ∑' a, q a := by gcongr
      _ = ∑' a, (p a * (p a / q a) ^ t + ENNReal.ofReal Y * q a) := by
          rw [lossMoment, ← ENNReal.tsum_mul_left, ← tsum_add]
      _ ≤ ∑' a, ENNReal.ofReal A * p a := tsum_le_tsum hpt
      _ = ENNReal.ofReal A * ∑' a, p a := ENNReal.tsum_mul_left
  have hfinp : ∑' a, p a ≠ ⊤ := ne_top_of_le_ne_top hfin hsum
  calc lossMoment t p q ≤ ENNReal.ofReal A * ∑' a, p a - ENNReal.ofReal Y * ∑' a, p a :=
        ENNReal.le_sub_of_add_le_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinp) hsum'
    _ = ENNReal.ofReal (A - Y) * ∑' a, p a := by
        rw [ENNReal.ofReal_sub _ hY, ENNReal.sub_mul fun _ _ => hfinp]
    _ = _ := by
        congr 2
        rw [hAdef, hYdef, Real.cosh_eq, Real.sinh_eq, Real.exp_neg, Real.exp_mul]
        rw [← sub_div, div_eq_iff hD.ne']
        have hE1 : E + 1 ≠ 0 := by positivity
        field_simp
        ring

/-- The moment bound in exponential form: with `s = ε t`,
`lossMoment t p q ≤ exp (tanh (ε / 2) · s + s² / 2) · ∑ p`. -/
theorem lossMoment_le_exp {p q : α → ℝ≥0∞} {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hpq : ∀ a, p a ≤ ENNReal.ofReal (Real.exp ε) * q a)
    (hqp : ∀ a, q a ≤ ENNReal.ofReal (Real.exp ε) * p a)
    (hsum : ∑' a, p a ≤ ∑' a, q a) (hfin : ∑' a, q a ≠ ⊤) :
    lossMoment t p q ≤
      ENNReal.ofReal (Real.exp (Real.tanh (ε / 2) * (ε * t) + (ε * t) ^ 2 / 2)) * ∑' a, p a := by
  refine (lossMoment_le_of_le_mul hε ht hpq hqp hsum hfin).trans (mul_le_mul' ?_ le_rfl)
  refine ENNReal.ofReal_le_ofReal (Real.cosh_add_mul_sinh_le_exp ?_ (mul_nonneg hε ht))
  exact Real.tanh_nonneg_iff.mpr (by linarith)

end SingleRound

end Cslib.Privacy
