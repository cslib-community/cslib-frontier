/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The local learning coefficient as a volume exponent

For a function `K` on a space with a distance and a volume, the *local learning coefficient* of
`K` at a point `w` measures how fast the volume of the nearby points with `K ≤ ε` shrinks as
`ε → 0`. When that volume behaves like `ε ^ λ`, up to factors that grow or decay more slowly
than every power, the coefficient is `λ`; for an arbitrary function it is a lower limit and no
such behaviour is implied. For a nonnegative `K` vanishing at `w`, a smaller coefficient means
that near `w` more of the space has `K` small.

In singular learning theory [Watanabe2009] `K` is the Kullback-Leibler divergence from the true
distribution to the model at parameter `w`. The coefficient is defined there, for real-analytic
`K`, as the exponent `λ` of the asymptotic form `c ε ^ λ (log (1 / ε)) ^ (m - 1)` of the volume
of `{K ≤ ε}`, equivalently through the largest pole of the zeta function `∫ K ^ z`; the
existence of that form rests on resolution of singularities. The local coefficient at a point is
the same invariant computed in a small ball about it [LauFurmanWangMurfetWei2025], and measures
how degenerate that one solution is. Under the hypotheses of [Watanabe2009], its smallest value
over the optimal parameters governs the asymptotics of the Bayes free energy and of the
generalization error.

## Deviation from the sources

The definition here needs no analyticity and no resolution of singularities: `volumeExponent` is
the lower limit of `log vol / log ε`, which exists for every function, and `learningCoeff` is
its limit as the ball shrinks. When the volume has the asymptotic form above, this is the `λ` of
the sources. In the sources that is the case for the germ of a real-analytic `K ≥ 0` that is not
identically zero, at a zero of `K`, with Lebesgue measure or a smooth positive density. That
agreement is not proved here, and neither is the existence of the asymptotic form. The
multiplicity `m` is not defined.

The values lie in `EReal`. If `K` has a positive lower bound near a point, as when `K` is
continuous and positive there, then the sublevel sets in small balls are eventually empty and
the coefficient is `⊤`.

## Main definitions

* `Cslib.MachineLearning.sublevelVolume`: the volume of the part of a ball where `K ≤ ε`.
* `Cslib.MachineLearning.volumeExponent`: the volume exponent in a ball of a given radius.
* `Cslib.MachineLearning.learningCoeff`: the local learning coefficient.

## Main results

* `Cslib.MachineLearning.lt_volumeExponent_iff`: the exponent exceeds `a` exactly when, for some
  `b > a`, the volume is eventually below `ε ^ b`.
* `Cslib.MachineLearning.volumeExponent_anti`: the exponent grows as the ball shrinks.
* `Cslib.MachineLearning.learningCoeff_le_of_le`: if `K ≤ C K'` near `w` then the coefficient of
  `K` is at most that of `K'`.
* `Cslib.MachineLearning.learningCoeff_const_mul`: a positive multiple has the same coefficient.
* `Cslib.MachineLearning.lowerSemicontinuous_learningCoeff`: the coefficient is lower
  semicontinuous in the point.
* `Cslib.MachineLearning.exists_isMinOn_learningCoeff`: on a nonempty compact set the smallest
  coefficient is attained.

## References

* [S. Watanabe, *Algebraic Geometry and Statistical Learning Theory*][Watanabe2009]
* [E. Lau, Z. Furman, G. Wang, D. Murfet, S. Wei, *The local learning coefficient: a
  singularity-aware complexity measure*][LauFurmanWangMurfetWei2025]
-/

public section

namespace Cslib.MachineLearning

open Filter MeasureTheory
open scoped ENNReal Topology

variable {E : Type*} [PseudoMetricSpace E] [MeasureSpace E]

/-- The volume of the part of the ball of radius `r` about `w` where `K ≤ ε`. -/
@[expose] noncomputable def sublevelVolume (K : E → ℝ) (w : E) (r ε : ℝ) : ℝ≥0∞ :=
  volume (Metric.ball w r ∩ {x | K x ≤ ε})

/-- The volume exponent of `K` in the ball of radius `r` about `w`: the lower limit of
`log vol / log ε` as `ε → 0` from above, where `vol` is the volume of the part of the ball where
`K ≤ ε`. If the volume is `c ε ^ λ (log (1 / ε)) ^ (m - 1)` to leading order, this is `λ`. -/
noncomputable def volumeExponent (K : E → ℝ) (w : E) (r : ℝ) : EReal :=
  liminf (fun ε : ℝ => (sublevelVolume K w r ε).log / (Real.log ε : EReal)) (𝓝[>] 0)

/-- The local learning coefficient of `K` at `w`: the supremum over `r > 0` of the volume
exponents of `K` in the balls of radius `r` about `w`, which is their limit as `r → 0`
(`volumeExponent_anti`). For a real-analytic `K ≥ 0` that is not identically zero near a zero
`w`, with Lebesgue measure or a smooth positive density, this is the local learning coefficient
of [LauFurmanWangMurfetWei2025], also called the real log canonical threshold of `K` at `w`
[Watanabe2009]; that agreement is not proved here. -/
noncomputable def learningCoeff (K : E → ℝ) (w : E) : EReal :=
  ⨆ r : {r : ℝ // 0 < r}, volumeExponent K w r

private theorem sublevelVolume_mono_of_subset {K K' : E → ℝ} {w w' : E} {r r' ε ε' : ℝ}
    (h : Metric.ball w' r' ∩ {x | K' x ≤ ε'} ⊆ Metric.ball w r ∩ {x | K x ≤ ε}) :
    sublevelVolume K' w' r' ε' ≤ sublevelVolume K w r ε :=
  measure_mono h

/-- For `0 < ε < 1`, the ratio `log v / log ε` exceeds `a` exactly when `v < ε ^ a`. -/
private theorem lt_log_div_log_iff {v : ℝ≥0∞} {ε a : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (a : EReal) < v.log / (Real.log ε : EReal) ↔ v < ENNReal.ofReal (ε ^ a) := by
  have hlog : Real.log ε < 0 := Real.log_neg h0 h1
  have hlog' : (Real.log ε : EReal) < 0 := by exact_mod_cast hlog
  rw [← ENNReal.log_lt_log_iff, ENNReal.log_ofReal_of_pos (Real.rpow_pos_of_pos h0 a),
    Real.log_rpow h0]
  induction v.log with
  | bot =>
    rw [EReal.bot_div_of_neg_ne_bot hlog' (EReal.coe_ne_bot _)]
    exact iff_of_true (EReal.coe_lt_top _) (EReal.bot_lt_coe _)
  | coe x =>
    rw [← EReal.coe_div, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff, lt_div_iff_of_neg hlog]
  | top =>
    rw [EReal.top_div_of_neg_ne_bot hlog' (EReal.coe_ne_bot _)]
    exact iff_of_false not_lt_bot not_top_lt

/-- If the exponent exceeds `a`, the volume is eventually below `ε ^ a`. -/
theorem eventually_sublevelVolume_lt_of_lt_volumeExponent {K : E → ℝ} {w : E} {r a : ℝ}
    (h : (a : EReal) < volumeExponent K w r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sublevelVolume K w r ε < ENNReal.ofReal (ε ^ a) := by
  filter_upwards [eventually_lt_of_lt_liminf h, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with ε hε h0 h1
  exact (lt_log_div_log_iff h0 h1).1 hε

/-- If the volume is eventually at most `ε ^ a`, the exponent is at least `a`. -/
theorem le_volumeExponent_of_eventually_le {K : E → ℝ} {w : E} {r a : ℝ}
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), sublevelVolume K w r ε ≤ ENNReal.ofReal (ε ^ a)) :
    (a : EReal) ≤ volumeExponent K w r := by
  refine EReal.ge_of_forall_gt_iff_ge.1 fun b hb => ?_
  have hba : b < a := EReal.coe_lt_coe_iff.1 hb
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [h, self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)]
    with ε hε h0 h1
  refine ((lt_log_div_log_iff h0 h1).2 (hε.trans_lt ?_)).le
  exact (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos h0 b)).2
    (Real.rpow_lt_rpow_of_exponent_gt h0 h1 hba)

/-- **Characterization of the volume exponent.** The exponent exceeds `a` exactly when, for some
`b > a`, the volume of the part of the ball where `K ≤ ε` is eventually below `ε ^ b`. -/
theorem lt_volumeExponent_iff {K : E → ℝ} {w : E} {r a : ℝ} :
    (a : EReal) < volumeExponent K w r ↔
      ∃ b : ℝ, a < b ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), sublevelVolume K w r ε < ENNReal.ofReal (ε ^ b) := by
  constructor
  · intro h
    obtain ⟨b, hab, hb⟩ := EReal.lt_iff_exists_real_btwn.1 h
    exact ⟨b, EReal.coe_lt_coe_iff.1 hab, eventually_sublevelVolume_lt_of_lt_volumeExponent hb⟩
  · rintro ⟨b, hab, hb⟩
    exact (EReal.coe_lt_coe_iff.2 hab).trans_le
      (le_volumeExponent_of_eventually_le (hb.mono fun _ h => h.le))

/-- Comparison of volume exponents: if for small `ε` the part of one ball where `K' ≤ ε` lies in
the part of another where `K ≤ C ε`, then the exponent of `K` is at most that of `K'`. -/
theorem volumeExponent_le_of_subset {K K' : E → ℝ} {w w' : E} {r r' C : ℝ} (hC : 0 < C)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Metric.ball w' r' ∩ {x | K' x ≤ ε} ⊆ Metric.ball w r ∩ {x | K x ≤ C * ε}) :
    volumeExponent K w r ≤ volumeExponent K' w' r' := by
  refine EReal.ge_of_forall_gt_iff_ge.1 fun b hb => ?_
  obtain ⟨a, hba, ha⟩ := EReal.lt_iff_exists_real_btwn.1 hb
  have hba' : b < a := EReal.coe_lt_coe_iff.1 hba
  refine le_volumeExponent_of_eventually_le ?_
  -- The volume for `K` at `C ε` is below `(C ε) ^ a`, which is eventually below `ε ^ b`.
  have hscale : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 := (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul C
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε using mul_pos hC hε
  have hpow : ∀ᶠ ε in 𝓝[>] (0 : ℝ), C ^ a * ε ^ (a - b) ≤ 1 := by
    have hab : 0 < a - b := sub_pos.2 hba'
    have h0 : Tendsto (fun ε : ℝ => C ^ a * ε ^ (a - b)) (𝓝[>] 0) (𝓝 (C ^ a * 0 ^ (a - b))) :=
      (((Real.continuousAt_rpow_const 0 (a - b) (Or.inr hab.le)).tendsto).mono_left
        nhdsWithin_le_nhds).const_mul (C ^ a)
    rw [Real.zero_rpow hab.ne', mul_zero] at h0
    exact h0.eventually (Iic_mem_nhds zero_lt_one)
  filter_upwards [h, hscale.eventually (eventually_sublevelVolume_lt_of_lt_volumeExponent ha),
    hpow, self_mem_nhdsWithin] with ε hsub hvol hp h0
  have h0' : (0 : ℝ) < ε := h0
  refine (sublevelVolume_mono_of_subset hsub).trans (hvol.le.trans
    (ENNReal.ofReal_le_ofReal ?_))
  calc (C * ε) ^ a = C ^ a * ε ^ (a - b) * ε ^ b := by
        rw [Real.mul_rpow hC.le h0'.le, mul_assoc, ← Real.rpow_add h0', sub_add_cancel]
    _ ≤ 1 * ε ^ b := by gcongr
    _ = ε ^ b := one_mul _

/-- The exponent of a ball is at most that of any ball it contains. -/
theorem volumeExponent_le_of_ball_subset (K : E → ℝ) {w w' : E} {r r' : ℝ}
    (h : Metric.ball w' r' ⊆ Metric.ball w r) :
    volumeExponent K w r ≤ volumeExponent K w' r' :=
  volumeExponent_le_of_subset one_pos (Eventually.of_forall fun ε => by
    rw [one_mul]
    exact Set.inter_subset_inter_left _ h)

/-- The volume exponent grows as the ball shrinks. -/
theorem volumeExponent_anti (K : E → ℝ) (w : E) {r s : ℝ} (h : r ≤ s) :
    volumeExponent K w s ≤ volumeExponent K w r :=
  volumeExponent_le_of_ball_subset K (Metric.ball_subset_ball h)

/-- The volume exponent in any ball is at most the local learning coefficient. -/
theorem volumeExponent_le_learningCoeff (K : E → ℝ) (w : E) {r : ℝ} (hr : 0 < r) :
    volumeExponent K w r ≤ learningCoeff K w :=
  le_iSup (fun r : {r : ℝ // 0 < r} => volumeExponent K w r) ⟨r, hr⟩

/-- The local learning coefficient is at most `a` exactly when every volume exponent is. -/
theorem learningCoeff_le_iff {K : E → ℝ} {w : E} {a : EReal} :
    learningCoeff K w ≤ a ↔ ∀ r : ℝ, 0 < r → volumeExponent K w r ≤ a := by
  rw [learningCoeff, iSup_le_iff]
  exact ⟨fun h r hr => h ⟨r, hr⟩, fun h r => h r.val r.property⟩

/-- **Comparison.** If `K ≤ C K'` near `w` for a constant `C > 0`, then the local learning
coefficient of `K` at `w` is at most that of `K'`: the smaller function has the larger sublevel
sets. -/
theorem learningCoeff_le_of_le {K K' : E → ℝ} {w : E} {C : ℝ} (hC : 0 < C)
    (h : ∀ᶠ x in 𝓝 w, K x ≤ C * K' x) : learningCoeff K w ≤ learningCoeff K' w := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 h
  refine learningCoeff_le_iff.2 fun r hr => ?_
  -- Shrink the ball to one on which the comparison holds.
  have hmin : 0 < min r δ := lt_min hr hδ
  refine (volumeExponent_anti K w (min_le_left r δ)).trans
    (le_trans ?_ (volumeExponent_le_learningCoeff K' w hmin))
  refine volumeExponent_le_of_subset hC (Eventually.of_forall fun ε x hx => ⟨hx.1, ?_⟩)
  exact (hball x (Metric.ball_subset_ball (min_le_right _ _) hx.1)).trans
    (mul_le_mul_of_nonneg_left hx.2 hC.le)

/-- A positive multiple of `K` has the same local learning coefficient as `K`. -/
theorem learningCoeff_const_mul (K : E → ℝ) (w : E) {c : ℝ} (hc : 0 < c) :
    learningCoeff (fun x => c * K x) w = learningCoeff K w :=
  le_antisymm (learningCoeff_le_of_le hc (Eventually.of_forall fun _ => le_rfl))
    (learningCoeff_le_of_le (inv_pos.2 hc) (Eventually.of_forall fun x => by
      rw [inv_mul_cancel_left₀ hc.ne']))

/-- **The local learning coefficient is lower semicontinuous in the point.** A small ball about
a point near `w` lies in a ball about `w`, and shrinking the ball only raises the exponent. -/
theorem lowerSemicontinuous_learningCoeff (K : E → ℝ) :
    LowerSemicontinuous (learningCoeff K) := by
  intro w y hy
  obtain ⟨r, hr⟩ := lt_iSup_iff.1 hy
  have hr2 : 0 < r.val / 2 := half_pos r.property
  filter_upwards [Metric.ball_mem_nhds w hr2] with w' hw'
  refine hr.trans_le (le_trans ?_ (volumeExponent_le_learningCoeff K w' hr2))
  refine volumeExponent_le_of_ball_subset K fun x hx => ?_
  rw [Metric.mem_ball] at hx hw' ⊢
  linarith [dist_triangle x w' w]

/-- **Attainment.** On a nonempty compact set the smallest local learning coefficient is
attained. -/
theorem exists_isMinOn_learningCoeff (K : E → ℝ) {S : Set E} (hS : IsCompact S)
    (hne : S.Nonempty) : ∃ w ∈ S, IsMinOn (learningCoeff K) S w :=
  (lowerSemicontinuous_learningCoeff K).lowerSemicontinuousOn S |>.exists_isMinOn hne hS

end Cslib.MachineLearning
