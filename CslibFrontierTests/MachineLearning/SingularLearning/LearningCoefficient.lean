/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.MachineLearning.SingularLearning.LearningCoefficient
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Tests for the local learning coefficient

Two extreme cases of
`CslibFrontier/MachineLearning/SingularLearning/LearningCoefficient.lean`:

* a function bounded below by a positive constant has no small sublevel sets, so its
  coefficient is `⊤` everywhere;
* the zero function on the real line has every ball as its sublevel set, so its volume exponent
  in a ball is not positive.
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

end CslibFrontierTests.LearningCoefficient
