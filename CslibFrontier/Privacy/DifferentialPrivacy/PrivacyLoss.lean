/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Privacy.DifferentialPrivacy.Basic
public import CslibFrontier.Probability.Renyi
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Hyperbolic
import CslibFrontier.Tactic.ENNRealToReal
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Privacy-loss bounds on Rényi moments and Rényi divergence

For mass functions `p`, `q` on a countable type, the order-`α` Rényi moment
`Probability.renyiMoment α p q = ∑ r, p r · (p r / q r) ^ (α - 1)` is the moment generating
function `E_{r ∼ p}[exp ((α - 1) · L(r))]` of the privacy loss `L(r) = ln (p r / q r)`
[DworkRoth2014, §2.3; Mironov2017, Definition 3]. When the likelihood ratio lies in
`[e^{-ε}, e^ε]`, convexity of `x ↦ x ^ α` bounds the moment by
`cosh (ε (α - 1)) + tanh (ε / 2) · sinh (ε (α - 1))` per unit of mass (`renyiMoment_le_of_le_mul`),
hence by `exp (tanh (ε / 2) · ε (α - 1) + (ε (α - 1))² / 2)` (`renyiMoment_le_exp`). Taking
logarithms gives the privacy-loss refinement `D_α(p ‖ q) ≤ ε tanh (ε / 2) + (α - 1) ε² / 2`
(`renyiDiv_le_of_le_mul`), which yields both the quadratic pure-DP to Rényi divergence bound
`α ε² / 2` of [BunSteinke2016, Proposition 3.3] (cited in [Mironov2017, Section V]) and the
per-round step of advanced composition.

## Main results

* `Cslib.Privacy.renyiMoment_le_of_le_mul`, `Cslib.Privacy.renyiMoment_le_exp`: the Rényi moment
  bounds for an `ε`-close pair of mass functions.
* `Cslib.Privacy.renyiDiv_le_of_le_mul`: the `ε tanh (ε / 2) + (α - 1) ε² / 2` Rényi divergence
  refinement on `PMF`s.

## References

* [BunSteinke2016]
* [DworkRoth2014]
* [Mironov2017]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

universe u

variable {R : Type u}

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
  have hwle : P / Q ≤ E := (div_le_iff₀ hQ).2 hPQ
  have hwge : E⁻¹ ≤ P / Q := (le_div_iff₀ hQ).2 ((inv_mul_le_iff₀ hE0).2 hQP)
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

/-- The Rényi moment bound for one round: if the likelihood ratio of `p` and `q` lies in
`[e^{-ε}, e^ε]` and `p` has at most the mass of `q`, then for `1 ≤ α`,
`renyiMoment α p q ≤ (cosh (ε (α - 1)) + tanh (ε / 2) · sinh (ε (α - 1))) · ∑ p`. The bound comes
from the chord of the convex function `x ↦ x ^ α` between `e^{-ε}` and `e^ε`, and is attained by
two-point distributions whose likelihood ratio takes only the values `e^{±ε}`. -/
theorem renyiMoment_le_of_le_mul {p q : R → ℝ≥0∞} {ε α : ℝ} (hε : 0 ≤ ε) (hα : 1 ≤ α)
    (hpq : ∀ r, p r ≤ ENNReal.ofReal (Real.exp ε) * q r)
    (hqp : ∀ r, q r ≤ ENNReal.ofReal (Real.exp ε) * p r)
    (hsum : ∑' r, p r ≤ ∑' r, q r) (hfin : ∑' r, q r ≠ ⊤) :
    Probability.renyiMoment α p q ≤ ENNReal.ofReal (Real.cosh (ε * (α - 1)) +
      Real.tanh (ε / 2) * Real.sinh (ε * (α - 1))) * ∑' r, p r := by
  set t : ℝ := α - 1
  have ht : 0 ≤ t := sub_nonneg.mpr hα
  rw [Real.tanh_half_eq_exp_sub_one_div]
  have hq : ∀ r, q r ≠ ⊤ := ne_top_of_tsum_ne_top hfin
  have hp : ∀ r, p r ≠ ⊤ := fun r => ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq r)) (hpq r)
  rcases hε.eq_or_lt with rfl | hε
  · have heq : ∀ r, p r = q r := fun r => le_antisymm
      (by simpa using hpq r) (by simpa using hqp r)
    simp only [zero_mul, Real.cosh_zero, Real.sinh_zero, mul_zero, add_zero, ENNReal.ofReal_one,
      one_mul, Probability.renyiMoment]
    refine tsum_le_tsum fun r => ?_
    rw [heq r]
    rcases eq_or_ne (q r) 0 with h0 | h0
    · simp [h0]
    · rw [ENNReal.div_self h0 (hq r), ENNReal.one_rpow, mul_one]
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
  have hpt : ∀ r, p r * (p r / q r) ^ t + ENNReal.ofReal Y * q r ≤ ENNReal.ofReal A * p r := by
    intro r
    rcases eq_or_ne (q r) 0 with hq0 | hq0
    · have hp0 : p r = 0 := by simpa [hq0] using hpq r
      simp [hp0, hq0]
    have hp0 : p r ≠ 0 := fun hp0 => hq0 (by simpa [hp0] using hqp r)
    have hP : 0 < (p r).toReal := by ennreal_to_real using pos_iff_ne_zero.mpr hp0
    have hQ : 0 < (q r).toReal := by ennreal_to_real using pos_iff_ne_zero.mpr hq0
    have hPQ : (p r).toReal ≤ E * (q r).toReal := by ennreal_to_real using hpq r
    have hQP : (q r).toReal ≤ E * (p r).toReal := by ennreal_to_real using hqp r
    have hdiv : (p r / q r) ^ t ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg ht (ENNReal.div_ne_top (hp r) hq0)
    have hreal : (p r).toReal * ((p r).toReal / (q r).toReal) ^ t + Y * (q r).toReal ≤
        A * (p r).toReal := by
      simpa only [hYdef, hAdef] using mul_div_rpow_add_le hE ht hP hQ hPQ hQP
    ennreal_to_real using hreal
  have hsum' : Probability.renyiMoment α p q + ENNReal.ofReal Y * ∑' r, p r ≤
      ENNReal.ofReal A * ∑' r, p r :=
    calc Probability.renyiMoment α p q + ENNReal.ofReal Y * ∑' r, p r
        ≤ Probability.renyiMoment α p q + ENNReal.ofReal Y * ∑' r, q r := by gcongr
      _ = ∑' r, (p r * (p r / q r) ^ t + ENNReal.ofReal Y * q r) := by
          rw [Probability.renyiMoment, ← ENNReal.tsum_mul_left, ← tsum_add]
      _ ≤ ∑' r, ENNReal.ofReal A * p r := tsum_le_tsum hpt
      _ = ENNReal.ofReal A * ∑' r, p r := ENNReal.tsum_mul_left
  have hfinp : ∑' r, p r ≠ ⊤ := ne_top_of_le_ne_top hfin hsum
  calc Probability.renyiMoment α p q
      ≤ ENNReal.ofReal A * ∑' r, p r - ENNReal.ofReal Y * ∑' r, p r :=
        ENNReal.le_sub_of_add_le_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinp) hsum'
    _ = ENNReal.ofReal (A - Y) * ∑' r, p r := by
        rw [ENNReal.ofReal_sub _ hY, ENNReal.sub_mul fun _ _ => hfinp]
    _ = _ := by
        congr 2
        rw [hAdef, hYdef, Real.cosh_eq, Real.sinh_eq, Real.exp_neg, Real.exp_mul]
        rw [← sub_div, div_eq_iff hD.ne']
        have hE1 : E + 1 ≠ 0 := by positivity
        field_simp
        ring

/-- The Rényi moment bound in exponential form: with `s = ε (α - 1)`,
`renyiMoment α p q ≤ exp (tanh (ε / 2) · s + s² / 2) · ∑ p`. -/
theorem renyiMoment_le_exp {p q : R → ℝ≥0∞} {ε α : ℝ} (hε : 0 ≤ ε) (hα : 1 ≤ α)
    (hpq : ∀ r, p r ≤ ENNReal.ofReal (Real.exp ε) * q r)
    (hqp : ∀ r, q r ≤ ENNReal.ofReal (Real.exp ε) * p r)
    (hsum : ∑' r, p r ≤ ∑' r, q r) (hfin : ∑' r, q r ≠ ⊤) :
    Probability.renyiMoment α p q ≤
      ENNReal.ofReal (Real.exp (Real.tanh (ε / 2) * (ε * (α - 1)) +
        (ε * (α - 1)) ^ 2 / 2)) * ∑' r, p r := by
  refine (renyiMoment_le_of_le_mul hε hα hpq hqp hsum hfin).trans (mul_le_mul' ?_ le_rfl)
  refine ENNReal.ofReal_le_ofReal (Real.cosh_add_mul_sinh_le_exp ?_
    (mul_nonneg hε (sub_nonneg.mpr hα)))
  exact Real.tanh_nonneg_iff.mpr (by linarith)

/-- For `1 < α`, if two discrete distributions `p, q : PMF R` have likelihood ratio in
`[e^{-ε}, e^ε]`, their order-`α` Rényi divergence is at most
`ε tanh (ε / 2) + (α - 1) ε² / 2`. -/
theorem renyiDiv_le_of_le_mul {p q : PMF R} {ε α : ℝ} (hε : 0 ≤ ε) (hα : 1 < α)
    (hpq : ∀ r, p r ≤ ENNReal.ofReal (Real.exp ε) * q r)
    (hqp : ∀ r, q r ≤ ENNReal.ofReal (Real.exp ε) * p r) :
    Probability.PMF.renyiDiv α p q ≤
      ENNReal.ofReal (ε * Real.tanh (ε / 2) + (α - 1) * ε ^ 2 / 2) := by
  have ht : 0 ≤ α - 1 := (sub_pos.mpr hα).le
  have hε_rhs : 0 ≤ ε * Real.tanh (ε / 2) + (α - 1) * ε ^ 2 / 2 :=
    add_nonneg (mul_nonneg hε (Real.tanh_nonneg_iff.mpr (by linarith))) (by positivity)
  rw [Probability.PMF.renyiDiv_le_ofReal_iff hα p q hε_rhs]
  have hmom := renyiMoment_le_exp hε hα.le hpq hqp (by rw [p.tsum_coe, q.tsum_coe])
    (by rw [q.tsum_coe]; exact ENNReal.one_ne_top)
  rw [p.tsum_coe, mul_one] at hmom
  exact hmom.trans_eq (congrArg (ENNReal.ofReal ∘ Real.exp) (by ring))

end SingleRound

end Cslib.Privacy
