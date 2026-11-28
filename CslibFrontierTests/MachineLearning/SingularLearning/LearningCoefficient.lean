/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.MachineLearning.SingularLearning.LearningCoefficient
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Tests for the local learning coefficient

Two extreme cases of
`CslibFrontier/MachineLearning/SingularLearning/LearningCoefficient.lean`:

* a function bounded below by a positive constant has no small sublevel sets, so its
  coefficient is `⊤` everywhere;
* the zero function on the real line has every ball as its sublevel set, so its volume exponent
  in a ball is not positive;
* the square on the real line has coefficient `1 / 2` at the origin, the value at a
  nondegenerate minimum in one dimension. This checks the normalization of the definition.
-/

public section

namespace CslibFrontierTests.LearningCoefficient

open Cslib.MachineLearning Filter MeasureTheory
open scoped ENNReal Topology

/-- A function bounded below by a positive constant has coefficient `⊤` at every point. -/
example {E : Type*} [PseudoMetricSpace E] [MeasureSpace E] (K : E → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hK : ∀ x, δ ≤ K x) (w : E) : learningCoeff K w = ⊤ := by
  refine top_le_iff.1 (le_trans ?_ (volumeExponent_le_learningCoeff K w one_pos))
  refine top_le_iff.2 ((EReal.eq_top_iff_forall_lt _).2 fun a => ?_)
  refine (EReal.coe_lt_coe_iff.2 (lt_add_one a)).trans_le (le_volumeExponent_of_eventually_le ?_)
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with ε hε
  have hempty : Metric.ball w 1 ∩ {x | K x ≤ ε} = ∅ :=
    Set.eq_empty_of_forall_notMem fun x hx => absurd (hK x) (not_le.2 (lt_of_le_of_lt hx.2 hε))
  rw [sublevelVolume, hempty, measure_empty]
  exact zero_le

/-- The zero function on the real line has volume exponent at most `0` in the unit ball: the
sublevel set is the whole ball, whose length does not shrink. -/
example : volumeExponent (fun _ : ℝ => (0 : ℝ)) 0 1 ≤ 0 := by
  refine not_lt.1 fun h => ?_
  obtain ⟨b, hb, hev⟩ := lt_volumeExponent_iff.1 (by exact_mod_cast h)
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ b < 2 := by
    have h0 := ((Real.continuousAt_rpow_const 0 b (Or.inr hb.le)).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rw [Real.zero_rpow hb.ne'] at h0
    exact h0.eventually (Iio_mem_nhds zero_lt_two)
  obtain ⟨ε, hε, hε2, hpos⟩ := (hev.and (hsmall.and self_mem_nhdsWithin)).exists
  have hball : Metric.ball (0 : ℝ) 1 ∩ {x | (0 : ℝ) ≤ ε} = Metric.ball 0 1 :=
    Set.inter_eq_left.2 fun _ _ => le_of_lt hpos
  rw [sublevelVolume, hball, Real.volume_ball] at hε
  have : ENNReal.ofReal (2 * 1) < ENNReal.ofReal 2 := hε.trans ((ENNReal.ofReal_lt_ofReal_iff
    zero_lt_two).2 hε2)
  simp at this

private theorem tendsto_rpow_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ε : ℝ => ε ^ c) (𝓝[>] 0) (𝓝 0) := by
  have h := ((Real.continuousAt_rpow_const 0 c (Or.inr hc.le)).tendsto).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi 0))
  rwa [Real.zero_rpow hc.ne'] at h

/-- The square on the real line has local learning coefficient `1 / 2` at the origin: the part
of a ball where `x ^ 2 ≤ ε` is the interval of length `2 √ε`. -/
theorem learningCoeff_sq : learningCoeff (fun x : ℝ => x ^ 2) 0 = ((1 / 2 : ℝ) : EReal) := by
  have hupper : ∀ r ε : ℝ, sublevelVolume (fun x : ℝ => x ^ 2) 0 r ε ≤
      ENNReal.ofReal (2 * ε ^ (1 / 2 : ℝ)) := by
    intro r ε
    refine (measure_mono (fun x hx => ?_ : _ ⊆ Set.Icc (-√ε) (√ε))).trans_eq ?_
    · exact abs_le.1 (Real.abs_le_sqrt hx.2)
    · rw [Real.volume_Icc, Real.sqrt_eq_rpow]
      congr 1
      ring
  have hlower : ∀ r ε : ℝ, 0 < ε → ε ^ (1 / 2 : ℝ) < r →
      ENNReal.ofReal (2 * ε ^ (1 / 2 : ℝ)) ≤ sublevelVolume (fun x : ℝ => x ^ 2) 0 r ε := by
    intro r ε hε hr
    rw [← Real.sqrt_eq_rpow] at hr ⊢
    refine (le_of_eq ?_).trans (measure_mono (fun x hx => ?_ : Set.Icc (-√ε) (√ε) ⊆ _))
    · rw [Real.volume_Icc]
      congr 1
      ring
    · refine ⟨?_, (Real.sq_le hε.le).2 hx⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      exact (abs_le.2 hx).trans_lt hr
  refine le_antisymm (learningCoeff_le_iff.2 fun r hr0 => not_lt.1 fun h => ?_) ?_
  · -- An exponent above `1 / 2` would put `2 √ε` below `ε ^ b` with `b > 1 / 2`.
    obtain ⟨b, hb, hev⟩ := lt_volumeExponent_iff.1 h
    have hr : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (1 / 2 : ℝ) < r :=
      (tendsto_rpow_zero (by norm_num)).eventually (Iio_mem_nhds hr0)
    have hone : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    have hmem : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    obtain ⟨ε, hε, hεr, hε1, hpos⟩ := (hev.and (hr.and (hone.and hmem))).exists
    have hpos' : (0 : ℝ) < ε := hpos
    have hlt := (hlower r ε hpos' hεr).trans_lt hε
    rw [ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hpos' b)] at hlt
    have hle : ε ^ b ≤ ε ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hpos' (le_of_lt hε1) hb.le
    linarith [Real.rpow_pos_of_pos hpos' (1 / 2 : ℝ)]
  · -- Below `1 / 2`, the length `2 √ε` is eventually at most `ε ^ a`.
    refine le_trans ?_ (volumeExponent_le_learningCoeff _ 0 one_pos)
    refine EReal.ge_of_forall_gt_iff_ge.1 fun a ha => ?_
    have ha' : a < 1 / 2 := EReal.coe_lt_coe_iff.1 ha
    refine le_volumeExponent_of_eventually_le ?_
    have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * ε ^ (1 / 2 - a) ≤ 1 := by
      have h0 := (tendsto_rpow_zero (sub_pos.2 ha')).const_mul 2
      rw [mul_zero] at h0
      exact h0.eventually (Iic_mem_nhds zero_lt_one)
    filter_upwards [hsmall, self_mem_nhdsWithin] with ε hε hpos
    have hpos' : (0 : ℝ) < ε := hpos
    refine (hupper 1 ε).trans (ENNReal.ofReal_le_ofReal ?_)
    calc 2 * ε ^ (1 / 2 : ℝ) = 2 * ε ^ (1 / 2 - a) * ε ^ a := by
          rw [mul_assoc, ← Real.rpow_add hpos', sub_add_cancel]
      _ ≤ 1 * ε ^ a := by gcongr
      _ = ε ^ a := one_mul _

end CslibFrontierTests.LearningCoefficient
