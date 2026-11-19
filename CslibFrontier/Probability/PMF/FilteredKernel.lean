/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Conditioning
public import Cslib.Probability.StatisticalDistance
import CslibFrontier.Probability.StatisticalDistance.Event
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map

/-!
# Comparing unnormalized kernels after conditioning

For a joint law with a sampled first coordinate and a second-coordinate kernel, condition on
an event in the second coordinate. The filtered joint masses recover the original restricted
kernel masses after multiplication by the event probability. This relates total variation on
the filtered laws to an absolute difference of the original kernel masses.

## Main results

* `Cslib.Probability.PMF.mul_filter_bind_pair_apply_toReal`: the restricted joint mass identity.
* `Cslib.Probability.PMF.restrictedKernelL1_le`: recover the absolute difference on the
  original event from filtered joint and marginal distances.
-/

public section

open Finset

namespace Cslib.Probability.PMF

variable {U R : Type*}

/-- Multiplying the filtered joint mass by the event probability recovers the restricted
joint mass, even for a null first-coordinate slice. -/
theorem mul_filter_bind_pair_apply_toReal (μ : PMF U) (K : U → PMF R) (E : Set R)
    [DecidablePred (· ∈ E)]
    (hE : ∃ z ∈ Prod.snd ⁻¹' E, z ∈ (μ.bind fun q => (K q).map (q, ·)).support)
    (q : U) (r : R) :
    let J := μ.bind fun u => (K u).map (u, ·)
    let p := (J.toOuterMeasure (Prod.snd ⁻¹' E)).toReal
    let Q := J.filter (Prod.snd ⁻¹' E) hE
    p * (Q (q, r)).toReal = if r ∈ E then (μ q).toReal * (K q r).toReal else 0 := by
  classical
  intro J p Q
  have hp : 0 < p := (toOuterMeasure_toReal_pos_iff _ _).mpr hE
  unfold Q
  rw [filter_apply_toReal]
  by_cases hr : r ∈ E
  · have hmem : (q, r) ∈ Prod.snd ⁻¹' E := hr
    rw [ite_eq_left hmem, ite_eq_left hr, mul_comm p, div_mul_cancel₀ _ hp.ne']
    rw [show J (q, r) = μ q * K q r from bind_map_prodMk_apply _ _ _, ENNReal.toReal_mul]
  · have hmem : (q, r) ∉ Prod.snd ⁻¹' E := hr
    simp only [hmem, hr, ite_false, mul_zero]

variable [Fintype U] [Fintype R]

/-- Compare the original kernels on the retained event. The factor `μ a` pays for
using the filtered conditional law of one particular first coordinate. The weight of
the event in that slice may be zero. -/
theorem restrictedKernelL1_le (μ : PMF U) (K : U → PMF R) (E : Set R)
    [DecidablePred (· ∈ E)] (J : PMF (U × R))
    (hJ : J = μ.bind fun q => (K q).map (q, ·))
    (hE : ∃ z ∈ Prod.snd ⁻¹' E, z ∈ J.support) (a : U) :
    let p := (J.toOuterMeasure (Prod.snd ⁻¹' E)).toReal
    let Q := J.filter (Prod.snd ⁻¹' E) hE
    let Q₀ := μ.bind fun q => (conditionalSnd Q a).map (q, ·)
    (μ a).toReal * (∑ q, (μ q).toReal * ∑ r ∈ univ.filter (· ∈ E),
      |(K q r).toReal - (K a r).toReal|) ≤
      p * (2 * (μ a).toReal * dist Q Q₀ + dist (Q.map Prod.fst) μ) := by
  classical
  subst J
  let J := μ.bind fun q => (K q).map (q, ·)
  intro p Q Q₀
  let p₀ := ((K a).toOuterMeasure E).toReal
  let P := Q.map Prod.fst
  let b := (μ a).toReal
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hmass (q : U) (r : R) :
      p * (Q (q, r)).toReal = if r ∈ E then (μ q).toReal * (K q r).toReal else 0 := by
    have h := mul_filter_bind_pair_apply_toReal μ K E hE q r
    exact h
  have ha : b * p₀ = p * (P a).toReal := by
    change (μ a).toReal * ((K a).toOuterMeasure E).toReal = p * ((Q.map Prod.fst) a).toReal
    rw [toOuterMeasure_apply_toReal, map_fst_apply, tsum_fintype,
      ENNReal.toReal_sum (fun r _ => PMF.apply_ne_top Q (a, r)), mul_sum, mul_sum]
    apply sum_congr rfl
    intro r _
    rw [hmass]
    split <;> simp
  have htail : b * |p - p₀| ≤ p * dist P μ := by
    have h := abs_toOuterMeasure_toReal_sub_le_dist P μ {a}
    simp only [PMF.toOuterMeasure_apply_singleton] at h
    rw [← abs_of_nonneg hb, ← abs_mul, mul_sub, ha, mul_comm b p, ← mul_sub,
      abs_mul, abs_of_nonneg hp, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left h hp
  change b * _ ≤ p * (2 * b * dist Q Q₀ + dist P μ)
  by_cases hb0 : b = 0
  · rw [hb0, zero_mul]
    positivity
  have hanchor (r : R) (hr : r ∈ E) :
      (K a r).toReal = p₀ * (conditionalSnd Q a r).toReal := by
    apply mul_left_cancel₀ hb0
    have h := congrArg ENNReal.toReal (marginal_mul_conditionalSnd Q a r)
    rw [ENNReal.toReal_mul] at h
    rw [← mul_assoc, ha, mul_assoc]
    change b * (K a r).toReal = p * ((P a).toReal * (conditionalSnd Q a r).toReal)
    rw [show (P a).toReal * (conditionalSnd Q a r).toReal = (Q (a, r)).toReal from h,
      hmass, ite_eq_left hr]
  have hpoint (q : U) (r : R) (hr : r ∈ E) :
      (μ q).toReal * |(K q r).toReal - (K a r).toReal| ≤
        p * |(Q (q, r)).toReal - (Q₀ (q, r)).toReal| + |p - p₀| * (Q₀ (q, r)).toReal := by
    have h₀ : (Q₀ (q, r)).toReal = (μ q).toReal * (conditionalSnd Q a r).toReal := by
      unfold Q₀
      rw [bind_map_prodMk_apply, ENNReal.toReal_mul]
    calc
      _ = |p * (Q (q, r)).toReal - p₀ * (Q₀ (q, r)).toReal| := by
        rw [hmass, ite_eq_left hr, h₀, hanchor r hr]
        conv_lhs => rw [← abs_of_nonneg (show 0 ≤ (μ q).toReal from ENNReal.toReal_nonneg),
          ← abs_mul]
        congr 1; ring
      _ ≤ _ := by
        rw [show p * (Q (q, r)).toReal - p₀ * (Q₀ (q, r)).toReal =
            p * ((Q (q, r)).toReal - (Q₀ (q, r)).toReal) + (p - p₀) * (Q₀ (q, r)).toReal
          by ring]
        simpa only [abs_mul, abs_of_nonneg hp, abs_of_nonneg ENNReal.toReal_nonneg] using
          abs_add_le (p * ((Q (q, r)).toReal - (Q₀ (q, r)).toReal))
            ((p - p₀) * (Q₀ (q, r)).toReal)
  have hsum : (∑ q, (μ q).toReal * ∑ r ∈ univ.filter (· ∈ E),
      |(K q r).toReal - (K a r).toReal|) ≤ 2 * p * dist Q Q₀ + |p - p₀| := by
    calc
      _ ≤ ∑ q, ∑ r, (p * |(Q (q, r)).toReal - (Q₀ (q, r)).toReal| +
          |p - p₀| * (Q₀ (q, r)).toReal) := by
        refine sum_le_sum fun q _ => ?_
        rw [mul_sum]
        refine (sum_le_sum fun r hr => hpoint q r (mem_filter.mp hr).2).trans
          (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun r _ _ =>
            add_nonneg (mul_nonneg hp (abs_nonneg _))
              (mul_nonneg (abs_nonneg _) ENNReal.toReal_nonneg))
      _ = _ := by
        let f (z : U × R) :=
          p * |(Q z).toReal - (Q₀ z).toReal| + |p - p₀| * (Q₀ z).toReal
        change (∑ q, ∑ r, f (q, r)) = _
        rw [← Fintype.sum_prod_type f]
        simp only [f, sum_add_distrib, ← mul_sum, sum_toReal, mul_one, dist_eq]
        ring
  exact (mul_le_mul_of_nonneg_left hsum hb).trans (by
    rw [mul_add]
    linarith only [htail])

end Cslib.Probability.PMF
