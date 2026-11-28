/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.SupportTsum

/-!
# Markov's inequality for discrete distributions

For a discrete distribution `p` and an extended nonnegative score `f`, the probability that `f` is
at least `t`, scaled by `t`, is at most the expectation `∑' i, p i * f i`. The statement needs no
measurable structure. Mathlib's `MeasureTheory.mul_meas_ge_le_lintegral` is the measure-theoretic
form, and `Fintype.mul_dens_filter_le_expect` the uniform finite form.

## Main results

* `Cslib.Probability.PMF.mul_toOuterMeasure_le_tsum`: `t · Pr[t ≤ f] ≤ E[f]`.
* `Cslib.Probability.PMF.toOuterMeasure_toReal_le_tsum_div`: `Pr[t ≤ f] ≤ E[f] / t` for a real
  score with values in `[0, 1]`.
* `Cslib.Probability.PMF.toOuterMeasure_bind_le_tsum_nat`: one-step integer Markov bound when
  `f = 0` absorbs away from `bad`.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {ι : Type*}

/-- **Markov's inequality** for a probability mass function and an extended nonnegative score:
`t · Pr[t ≤ f] ≤ E[f]`. -/
theorem mul_toOuterMeasure_le_tsum (p : PMF ι) (f : ι → ℝ≥0∞) (t : ℝ≥0∞) :
    t * p.toOuterMeasure {i | t ≤ f i} ≤ ∑' i, p i * f i := by
  rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun i => ?_
  by_cases hi : i ∈ {i | t ≤ f i}
  · rw [Set.indicator_of_mem hi, mul_comm]
    exact mul_le_mul_of_nonneg_left hi zero_le
  · simp [Set.indicator_of_notMem hi]

/-- **Markov's inequality** for a real score with values in `[0, 1]`:
`Pr[t ≤ f] ≤ E[f] / t`. -/
theorem toOuterMeasure_toReal_le_tsum_div (p : PMF ι) {f : ι → ℝ} (hf₀ : ∀ i, 0 ≤ f i)
    (hf₁ : ∀ i, f i ≤ 1) {t : ℝ} (ht : 0 < t) :
    (p.toOuterMeasure {i | t ≤ f i}).toReal ≤ (∑' i, (p i).toReal * f i) / t := by
  have hmarkov := mul_toOuterMeasure_le_tsum p (fun i => ENNReal.ofReal (f i)) (ENNReal.ofReal t)
  have hset : {i | ENNReal.ofReal t ≤ ENNReal.ofReal (f i)} = {i | t ≤ f i} :=
    Set.ext fun i => ENNReal.ofReal_le_ofReal_iff (hf₀ i)
  rw [hset] at hmarkov
  have hne : (∑' i, p i * ENNReal.ofReal (f i)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∑' i, p i * ENNReal.ofReal (f i)
        ≤ ∑' i, p i :=
          tsum_le_tsum fun i => mul_le_of_le_one_right' (ENNReal.ofReal_le_one.mpr (hf₁ i))
      _ = 1 := p.tsum_coe
  have hreal := ENNReal.toReal_mono hne hmarkov
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le,
    ENNReal.tsum_toReal_eq fun i => ENNReal.mul_ne_top (p.apply_ne_top i) ENNReal.ofReal_ne_top]
    at hreal
  rw [le_div_iff₀ ht, mul_comm]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf₀ _)] using hreal

/-- **One-step integer Markov bound**: if an integer potential `f : ι → ℕ` vanishes on supported
states only where the next step `step` never lands in `bad`, then the probability of `bad` after
`p.bind step` is at most the expected value of `f` under `p`. -/
theorem toOuterMeasure_bind_le_tsum_nat {β : Type*} (p : PMF ι) (step : ι → PMF β)
    (bad : Set β) (f : ι → ℕ)
    (hzero : ∀ a ∈ p.support, f a = 0 → ∀ b ∈ (step a).support, b ∉ bad) :
    (p.bind step).toOuterMeasure bad ≤ ∑' a, p a * (f a : ℝ≥0∞) := by
  rw [PMF.toOuterMeasure_bind_apply]
  refine tsum_mul_mono_support p fun a ha => ?_
  rcases Nat.eq_zero_or_pos (f a) with h0 | hpos
  · simp [h0, (PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 (Set.disjoint_left.2 (hzero a ha h0))]
  · exact (toOuterMeasure_le_one _ _).trans (Nat.one_le_cast.2 hpos)

end Cslib.Probability.PMF
