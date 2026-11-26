/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.Strategic.Basic
public import CslibFrontier.GameTheory.Strategic.Smooth
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Basic.NNReal.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# System reliability and free-riding games

Varian [Varian2004] (surveyed in [AndersonMooreNagarajaOzment2007], §25.2.1, p. 635) models
information security and system dependability as public-goods provision under three canonical
Hirshleifer effort-aggregation technologies. Each agent `i : ι` chooses a nonnegative effort
`x i : ℝ≥0` at marginal cost `unitCost i`, receives benefit `val i` when the system operates, and
faces system reliability `prob (agg x)`. Equivalently, in `Cslib.GameTheory.CostGame` form, agent
`i` minimizes expected failure loss plus effort expenditure
`val i * (1 - prob (agg x)) + unitCost i * x i`, which differs from negated net payoff
`-(val i * prob (agg x) - unitCost i * x i)` by the profile-independent constant `val i` and stays
nonnegative whenever `prob (agg x) ≤ 1`.

## Main definitions

* `Cslib.GameTheory.SystemReliabilitySpec`: valuations, unit effort costs, and reliability curve
  `prob : ℝ → ℝ` for an `ι`-player system reliability problem.
* `Cslib.GameTheory.totalEffort`, `Cslib.GameTheory.weakestLink`, `Cslib.GameTheory.bestShot`:
  sum, minimum, and maximum effort aggregators over `ι → ℝ≥0`.
* `Cslib.GameTheory.SystemReliabilitySpec.toCostGame`, `totalEffortGame`, `weakestLinkGame`,
  `bestShotGame`: the strategic cost games induced by each aggregator.
* `Cslib.GameTheory.IsStandaloneOpt`: characterization of an agent's standalone optimal effort
  `zStar` minimizing `V * (1 - P z) + C * z` on `ℝ≥0`.
* `Cslib.GameTheory.SystemReliabilitySpec.totalEffortLiabilityGame`,
  `Cslib.GameTheory.SystemReliabilitySpec.weakestLinkNegligenceGame`: Varian's §7.1 strict
  liability fine on a least-cost avoider and §7.2 negligence rule with due-care standard.

## Main results

* `Cslib.GameTheory.isStandaloneOpt_of_hasDerivAt`,
  `Cslib.GameTheory.IsStandaloneOpt.le_of_ratio_lt`,
  `Cslib.GameTheory.IsStandaloneOpt.lt_of_ratio_lt_of_hasDerivAt`: first-order sufficiency and
  monotone / strict comparative statics of standalone effort in the benefit-cost ratio `V / C`.
* `Cslib.GameTheory.SystemReliabilitySpec.isPureNash_totalEffortGame_iff`,
  `Cslib.GameTheory.SystemReliabilitySpec.isPureNash_totalEffortGame_single`,
  `Cslib.GameTheory.SystemReliabilitySpec.eq_single_of_isPureNash_totalEffortGame` ([Varian2004],
  §3.1, Fact 1): in the total-effort game, pure Nash equilibria have aggregate effort
  `sup_i xBar i` with all sub-champion agents free-riding (`x i = 0`), and a unique ratio champion
  yields a unique pure Nash equilibrium.
* `Cslib.GameTheory.SystemReliabilitySpec.socialCost_totalEffortGame_single_le`,
  `Cslib.GameTheory.SystemReliabilitySpec.totalEffort_le_socialOpt_of_isPureNash`,
  `Cslib.GameTheory.SystemReliabilitySpec.totalEffort_lt_socialOpt_of_isPureNash`,
  `Cslib.GameTheory.SystemReliabilitySpec.wrongAgent_support_disjoint` ([Varian2004], §4.1,
  Fact 3): social optimality concentrates effort on least-cost agents, Nash equilibrium
  underprovides total effort, and when `c₁ < c₂` while `v₁ / c₁ < v₂ / c₂` the Nash contributor
  and socially optimal contributor are disjoint ("the wrong agent exerts the effort").
* `Cslib.GameTheory.SystemReliabilitySpec.isPureNash_weakestLinkGame_const_inf`,
  `Cslib.GameTheory.SystemReliabilitySpec.isPureNash_weakestLinkGame_iff`,
  `Cslib.GameTheory.SystemReliabilitySpec.cost_weakestLinkGame_const_inf_le_of_isPureNash`
  ([Varian2004], §3.2, Fact 2): weakest-link pure Nash equilibria form the constant-effort
  continuum `[0, inf_i xBar i]` (for `|ι| ≥ 2`), Pareto-dominated by `inf_i xBar i`.
* `Cslib.GameTheory.SystemReliabilitySpec.weakestLink_socialOpt_le_totalEffort_socialOpt`,
  `Cslib.GameTheory.SystemReliabilitySpec.prob_totalEffort_le_of_subset_of_isPureNash`,
  `Cslib.GameTheory.SystemReliabilitySpec.prob_weakestLink_le_of_subset_of_isPureNash`,
  `Cslib.GameTheory.SystemReliabilitySpec.identicalAgents_weakestLink_socialOpt_isPureNash`
  ([Varian2004], §4.3–§6, Facts 4, 5, and 7): socially optimal weakest-link effort never exceeds
  socially optimal total effort, adding agents (`S ⊆ T`) weakly raises equilibrium total-effort
  reliability while weakly lowering equilibrium weakest-link reliability, and identical weakest-link
  agents achieve social optimality in Nash equilibrium (Price of Stability `1`).
* `Cslib.GameTheory.SystemReliabilitySpec.isPureNash_totalEffortLiabilityGame_single`,
  `Cslib.GameTheory.SystemReliabilitySpec.isPureNash_weakestLinkNegligenceGame_const`
  ([Varian2004], §7.1–§7.2, Facts 8 and 9): internalizing failure externalities via a Pigouvian
  liability fine in total effort, or a due-care negligence rule in weakest link, induces the
  socially optimal profile as a pure Nash equilibrium.
* `Cslib.GameTheory.SystemReliabilitySpec.isPureNash_bestShotGame_single_iff`,
  `Cslib.GameTheory.SystemReliabilitySpec.isPureNash_bestShotGame_champion`,
  `Cslib.GameTheory.SystemReliabilitySpec.exists_eq_single_of_isPureNash_bestShotGame`
  ([Varian2004], §3.3): every nonzero pure Nash equilibrium of the best-shot game is supported on
  a single contributor `Pi.single k (xBar k)`, including both the champion equilibrium and
  asymmetric "slacker" equilibria.
* `Cslib.GameTheory.SystemReliabilitySpec.expected_socialCost_le_of_isCoarseCorrelatedEquilibrium`,
  `Cslib.GameTheory.SystemReliabilitySpec.socialCost_totalEffortGame_le_card_mul`,
  `Cslib.GameTheory.SystemReliabilitySpec.socialCost_bestShotGame_le_card_mul`,
  `Cslib.GameTheory.exists_totalEffortGame_socialCost_gt_mul` (original): tight
  `(∑ i, c_i) / c_min` (equal to `|ι|` for identical unit costs) robust Price of Anarchy over all
  coarse correlated equilibria for both total-effort and best-shot reliability games, with matching
  `n / (1 + ε)` pure-Nash tightness.

## References

* [R. Anderson, T. Moore, S. Nagaraja, and A. Ozment, *Incentives and Information
  Security*][AndersonMooreNagarajaOzment2007]
* [H. R. Varian, *System Reliability and Free Riding*][Varian2004]
-/

public noncomputable section

open Finset
open scoped NNReal

namespace Cslib.GameTheory

/-- Parameters of a Varian system-reliability public-goods game ([Varian2004], §2, p. 2):
each agent `i : ι` values successful system operation at `val i`, pays marginal cost `unitCost i`
per unit of effort in `ℝ≥0`, and faces system reliability `prob F` at aggregate effort `F`. -/
structure SystemReliabilitySpec (ι : Type*) where
  /-- Benefit `v_i` obtained by agent `i` when the system succeeds. -/
  val : ι → ℝ
  /-- Marginal effort cost `c_i` per unit of effort by agent `i`. -/
  unitCost : ι → ℝ
  /-- System reliability (or concave benefit) `P(F)` as a function of aggregate effort `F ≥ 0`. -/
  prob : ℝ → ℝ

/-- **Total-effort aggregator** ([Varian2004], §2, p. 3): aggregate effort is the sum `∑ i, x i`. -/
abbrev totalEffort {ι : Type*} [Fintype ι] (x : ι → ℝ≥0) : ℝ≥0 :=
  ∑ i, x i

/-- **Weakest-link aggregator** ([Varian2004], §2, p. 3): aggregate effort is `min_i x i`. -/
abbrev weakestLink {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ≥0) : ℝ≥0 :=
  univ.inf' univ_nonempty x

/-- **Best-shot aggregator** ([Varian2004], §2, p. 3): aggregate effort is `max_i x i`. -/
abbrev bestShot {ι : Type*} [Fintype ι] (x : ι → ℝ≥0) : ℝ≥0 :=
  univ.sup x

/-! ### Standalone effort optimization and comparative statics -/

/-- `IsStandaloneOpt P V C zStar` means `zStar : ℝ≥0` minimizes the standalone expected failure
plus effort cost `V * (1 - P z) + C * z` (equivalently maximizes `V * P z - C * z`) over all
nonnegative efforts `z : ℝ≥0`. -/
@[expose] def IsStandaloneOpt (P : ℝ → ℝ) (V C : ℝ) (zStar : ℝ≥0) : Prop :=
  ∀ z : ℝ≥0, V * (1 - P zStar) + C * (zStar : ℝ) ≤ V * (1 - P z) + C * (z : ℝ)

theorem isStandaloneOpt_iff_payoff_le {P : ℝ → ℝ} {V C : ℝ} {zStar : ℝ≥0} :
    IsStandaloneOpt P V C zStar ↔
      ∀ z : ℝ≥0, V * P z - C * (z : ℝ) ≤ V * P zStar - C * (zStar : ℝ) :=
  ⟨fun h z => by linarith [h z], fun h z => by linarith [h z]⟩

/-- Under strict concavity of `P` on `[0, ∞)` and `0 < V`, a standalone optimum strictly beats
every other effort level. -/
theorem IsStandaloneOpt.strict_lt_of_ne {P : ℝ → ℝ} {V C : ℝ} {zStar z : ℝ≥0}
    (hOpt : IsStandaloneOpt P V C zStar) (hConc : StrictConcaveOn ℝ (Set.Ici 0) P)
    (hV : 0 < V) (hne : z ≠ zStar) :
    V * (1 - P zStar) + C * (zStar : ℝ) < V * (1 - P z) + C * (z : ℝ) := by
  let m : ℝ≥0 := ⟨(1 / 2 : ℝ) * (zStar : ℝ) + (1 / 2 : ℝ) * (z : ℝ), by positivity⟩
  have hsc := @hConc.2 (zStar : ℝ) zStar.coe_nonneg (z : ℝ) z.coe_nonneg
    (fun h => hne (NNReal.coe_inj.mp h.symm))
    (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hsc
  have hVsc : V * ((1 / 2 : ℝ) * P zStar + (1 / 2 : ℝ) * P z) < V * P m :=
    mul_lt_mul_of_pos_left hsc hV
  have hCm : C * (m : ℝ) = (1 / 2 : ℝ) * (C * (zStar : ℝ)) + (1 / 2 : ℝ) * (C * (z : ℝ)) := by
    change C * ((1 / 2 : ℝ) * (zStar : ℝ) + (1 / 2 : ℝ) * (z : ℝ)) = _
    ring
  linarith [hOpt m]

/-- Under strict concavity of `P` on `[0, ∞)` and `0 < V`, the standalone optimal effort is
unique. -/
theorem IsStandaloneOpt.unique {P : ℝ → ℝ} {V C : ℝ} {z₁ z₂ : ℝ≥0}
    (h₁ : IsStandaloneOpt P V C z₁) (h₂ : IsStandaloneOpt P V C z₂)
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) P) (hV : 0 < V) : z₁ = z₂ := by
  by_contra hne
  linarith [h₁.strict_lt_of_ne hConc hV (Ne.symm hne), h₂ z₁]

private theorem IsStandaloneOpt.lt_of_open_segment {P : ℝ → ℝ} {V C : ℝ} {zStar u m : ℝ≥0}
    (hOpt : IsStandaloneOpt P V C zStar) (hConc : StrictConcaveOn ℝ (Set.Ici 0) P)
    (hV : 0 < V) (hne : (u : ℝ) ≠ (zStar : ℝ)) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : 0 < 1 - θ)
    (hcomb : θ * (u : ℝ) + (1 - θ) * (zStar : ℝ) = (m : ℝ)) :
    V * (1 - P m) + C * (m : ℝ) < V * (1 - P u) + C * (u : ℝ) := by
  have hsc := @hConc.2 (u : ℝ) u.coe_nonneg (zStar : ℝ) zStar.coe_nonneg hne
    θ (1 - θ) hθ0 hθ1 (by ring)
  simp only [smul_eq_mul, hcomb] at hsc
  have hVsc := mul_lt_mul_of_pos_left hsc hV
  have hlin : C * (m : ℝ) = θ * (C * (u : ℝ)) + (1 - θ) * (C * (zStar : ℝ)) := by
    rw [← hcomb]; ring
  nlinarith [hOpt u]

/-- Under strict concavity of `P` on `[0, ∞)` and `0 < V`, standalone cost strictly decreases on
`[0, zStar]`. -/
theorem IsStandaloneOpt.lt_of_lt_of_le {P : ℝ → ℝ} {V C : ℝ} {zStar a b : ℝ≥0}
    (hOpt : IsStandaloneOpt P V C zStar) (hConc : StrictConcaveOn ℝ (Set.Ici 0) P)
    (hV : 0 < V) (hab : a < b) (hb : b ≤ zStar) :
    V * (1 - P b) + C * (b : ℝ) < V * (1 - P a) + C * (a : ℝ) := by
  rcases eq_or_lt_of_le hb with rfl | hbz
  · exact hOpt.strict_lt_of_ne hConc hV hab.ne
  · have habR : (a : ℝ) < (b : ℝ) := hab
    have hbzR : (b : ℝ) < (zStar : ℝ) := hbz
    have hden : 0 < (zStar : ℝ) - (a : ℝ) := sub_pos.mpr (habR.trans hbzR)
    set θ : ℝ := ((zStar : ℝ) - (b : ℝ)) / ((zStar : ℝ) - (a : ℝ))
    refine hOpt.lt_of_open_segment hConc hV (habR.trans hbzR).ne θ
      (div_pos (sub_pos.mpr hbzR) hden)
      (sub_pos.mpr ((div_lt_one hden).mpr (sub_lt_sub_left habR _))) ?_
    simp only [θ]
    field_simp; ring

/-- Under strict concavity of `P` on `[0, ∞)` and `0 < V`, standalone cost strictly increases on
`[zStar, ∞)`. -/
theorem IsStandaloneOpt.lt_of_le_of_lt {P : ℝ → ℝ} {V C : ℝ} {zStar a b : ℝ≥0}
    (hOpt : IsStandaloneOpt P V C zStar) (hConc : StrictConcaveOn ℝ (Set.Ici 0) P)
    (hV : 0 < V) (ha : zStar ≤ a) (hab : a < b) :
    V * (1 - P a) + C * (a : ℝ) < V * (1 - P b) + C * (b : ℝ) := by
  rcases eq_or_lt_of_le ha with rfl | haz
  · exact hOpt.strict_lt_of_ne hConc hV hab.ne'
  · have hazR : (zStar : ℝ) < (a : ℝ) := haz
    have habR : (a : ℝ) < (b : ℝ) := hab
    have hden : 0 < (b : ℝ) - (zStar : ℝ) := sub_pos.mpr (hazR.trans habR)
    set θ : ℝ := ((a : ℝ) - (zStar : ℝ)) / ((b : ℝ) - (zStar : ℝ))
    refine hOpt.lt_of_open_segment hConc hV (hazR.trans habR).ne' θ
      (div_pos (sub_pos.mpr hazR) hden)
      (sub_pos.mpr ((div_lt_one hden).mpr (sub_lt_sub_right habR _))) ?_
    simp only [θ]
    field_simp; ring

/-- Monotone comparative statics of standalone optimal effort in the benefit-cost ratio `V / C`:
if `V₁ / C₁ < V₂ / C₂`, then any standalone optimum for `(V₁, C₁)` is at most any standalone
optimum for `(V₂, C₂)`. -/
theorem IsStandaloneOpt.le_of_ratio_lt {P : ℝ → ℝ} {V₁ C₁ V₂ C₂ : ℝ} {z₁ z₂ : ℝ≥0}
    (h₁ : IsStandaloneOpt P V₁ C₁ z₁) (h₂ : IsStandaloneOpt P V₂ C₂ z₂)
    (hV₁ : 0 < V₁) (hC₁ : 0 < C₁) (hV₂ : 0 < V₂) (hC₂ : 0 < C₂)
    (hratio : V₁ / C₁ < V₂ / C₂) : z₁ ≤ z₂ := by
  by_contra hlt
  have hz : (z₂ : ℝ) < (z₁ : ℝ) := lt_of_not_ge hlt
  have hcross : V₁ * C₂ < V₂ * C₁ := (div_lt_div_iff₀ hC₁ hC₂).mp hratio
  have hmul1 := mul_le_mul_of_nonneg_left
    (show C₁ * ((z₁ : ℝ) - (z₂ : ℝ)) ≤ V₁ * (P z₁ - P z₂) by linarith [h₁ z₂]) hV₂.le
  have hmul2 := mul_le_mul_of_nonneg_left
    (show V₂ * (P z₁ - P z₂) ≤ C₂ * ((z₁ : ℝ) - (z₂ : ℝ)) by linarith [h₂ z₁]) hV₁.le
  nlinarith

/-- First-order sufficient condition for standalone optimality ([Varian2004], §3.1, p. 3): if `P`
has antitone derivative `P'` on `[0, ∞)`, then `zStar` is a standalone optimum whenever either
`zStar = 0` and `V * P' 0 ≤ C`, or the interior condition `V * P' zStar = C` holds. -/
theorem isStandaloneOpt_of_hasDerivAt {P P' : ℝ → ℝ} {V C : ℝ} {zStar : ℝ≥0}
    (hDeriv : ∀ t : ℝ, 0 ≤ t → HasDerivAt P (P' t) t)
    (hAnti : AntitoneOn P' (Set.Ici 0)) (hV : 0 ≤ V)
    (hFOC : (zStar = 0 ∧ V * P' 0 ≤ C) ∨ V * P' zStar = C) :
    IsStandaloneOpt P V C zStar := by
  have hmvt : ∀ {a b : ℝ≥0}, (a : ℝ) < (b : ℝ) →
      ∃ ξ ∈ Set.Ioo (a : ℝ) (b : ℝ), P b - P a = P' ξ * ((b : ℝ) - (a : ℝ)) := fun {a b} hab => by
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope P P' hab
      (fun x hx => (hDeriv x (a.coe_nonneg.trans hx.1)).continuousAt.continuousWithinAt)
      (fun x hx => hDeriv x (a.coe_nonneg.trans hx.1.le))
    exact ⟨ξ, hξ, by rw [hslope, div_mul_cancel₀ _ (sub_pos.mpr hab).ne']⟩
  intro z
  rcases lt_trichotomy (z : ℝ) (zStar : ℝ) with hlt | heq | hgt
  · have hFOC_eq : V * P' zStar = C := hFOC.resolve_left fun h =>
      not_lt_of_ge z.coe_nonneg (by rwa [h.1, NNReal.coe_zero] at hlt)
    obtain ⟨ξ, hξ, hsub⟩ := hmvt hlt
    have hξ_ge := hAnti (z.coe_nonneg.trans hξ.1.le) zStar.coe_nonneg hξ.2.le
    nlinarith [mul_le_mul_of_nonneg_left hξ_ge hV]
  · rw [heq]
  · obtain ⟨ξ, hξ, hsub⟩ := hmvt hgt
    have hξ_le := hAnti zStar.coe_nonneg (zStar.coe_nonneg.trans hξ.1.le) hξ.1.le
    have hVP : V * P' zStar ≤ C := hFOC.elim (fun ⟨hz, h0⟩ => by rwa [hz, NNReal.coe_zero]) le_of_eq
    nlinarith [mul_le_mul_of_nonneg_left hξ_le hV]

/-- Strict comparative statics of interior standalone optima: if `V₁ / C₁ < V₂ / C₂` and `z₂ > 0`
where `P` is differentiable at `z₂` with `V₂ * P'₂ = C₂`, then `z₁ < z₂`. -/
theorem IsStandaloneOpt.lt_of_ratio_lt_of_hasDerivAt {P : ℝ → ℝ} {P'₂ : ℝ}
    {V₁ C₁ V₂ C₂ : ℝ} {z₁ z₂ : ℝ≥0}
    (h₁ : IsStandaloneOpt P V₁ C₁ z₁) (h₂ : IsStandaloneOpt P V₂ C₂ z₂)
    (hV₁ : 0 < V₁) (hC₁ : 0 < C₁) (hV₂ : 0 < V₂) (hC₂ : 0 < C₂)
    (hratio : V₁ / C₁ < V₂ / C₂) (hz₂ : 0 < z₂)
    (hDeriv : HasDerivAt P P'₂ z₂) (hFOC₂ : V₂ * P'₂ = C₂) : z₁ < z₂ := by
  refine lt_of_le_of_ne (h₁.le_of_ratio_lt h₂ hV₁ hC₁ hV₂ hC₂ hratio) fun heq => ?_
  subst heq
  have hcross : V₁ * C₂ < V₂ * C₁ := (div_lt_div_iff₀ hC₁ hC₂).mp hratio
  have hP'_lt : P'₂ < C₁ / V₁ := (lt_div_iff₀ hV₁).mpr (by nlinarith)
  have hmem := (hasDerivAt_iff_tendsto_slope.mp hDeriv).eventually (Iio_mem_nhds hP'_lt)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hmem
  obtain ⟨δ, hδ, hball⟩ := hmem
  set yR : ℝ := max 0 ((z₁ : ℝ) - δ / 2)
  have hy_lt : yR < (z₁ : ℝ) := max_lt hz₂ (by linarith)
  have hy_dist : dist yR (z₁ : ℝ) < δ := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hy_lt)]; linarith [le_max_right 0 ((z₁ : ℝ) - δ / 2)]
  have hslope_lt := hball hy_dist (Set.mem_compl_singleton_iff.mpr hy_lt.ne)
  rw [slope_def_field] at hslope_lt
  have hden_pos : 0 < (z₁ : ℝ) - yR := sub_pos.mpr hy_lt
  have hslope_eq : (P yR - P z₁) / (yR - (z₁ : ℝ)) = (P z₁ - P yR) / ((z₁ : ℝ) - yR) := by
    field_simp [sub_ne_zero.mpr hy_lt.ne, hden_pos.ne']; ring
  rw [hslope_eq, div_lt_div_iff₀ hden_pos hV₁] at hslope_lt
  have hy_opt : V₁ * (1 - P z₁) + C₁ * (z₁ : ℝ) ≤ V₁ * (1 - P yR) + C₁ * yR :=
    h₁ ⟨yR, le_max_left _ _⟩
  nlinarith

private theorem self_lt_sum_of_pos {ι : Type*} [Fintype ι] [Nontrivial ι] {f : ι → ℝ}
    (hf : ∀ k, 0 < f k) (i : ι) : f i < ∑ k, f k := by
  classical
  obtain ⟨j, hj⟩ := exists_ne i
  rw [← add_sum_erase _ _ (mem_univ i)]
  have hj_pos : 0 < ∑ k ∈ univ.erase i, f k :=
    sum_pos' (fun k _ => (hf k).le) ⟨j, mem_erase.mpr ⟨hj, mem_univ j⟩, hf j⟩
  linarith

namespace SystemReliabilitySpec

variable {ι : Type*} (R : SystemReliabilitySpec ι)

/-- The `CostGame` induced by an effort aggregator `agg : (ι → ℝ≥0) → ℝ≥0`: player `i` minimizes
expected failure loss plus effort expenditure `val i * (1 - prob (agg x)) + unitCost i * x i`. -/
@[expose] def toCostGame (agg : (ι → ℝ≥0) → ℝ≥0) : CostGame ι (fun _ => ℝ≥0) where
  cost i x := R.val i * (1 - R.prob (agg x)) + R.unitCost i * (x i : ℝ)

/-- Varian's expected net payoff `v_i P(F(x)) - c_i x_i` ([Varian2004], §2, p. 2). -/
def payoff (agg : (ι → ℝ≥0) → ℝ≥0) (i : ι) (x : ι → ℝ≥0) : ℝ :=
  R.val i * R.prob (agg x) - R.unitCost i * (x i : ℝ)

/-- Varian's expected social payoff `(∑ i, v_i) P(F(x)) - ∑ i, c_i x_i` ([Varian2004], §2, p. 2). -/
def socialPayoff [Fintype ι] (agg : (ι → ℝ≥0) → ℝ≥0) (x : ι → ℝ≥0) : ℝ :=
  (∑ i, R.val i) * R.prob (agg x) - ∑ i, R.unitCost i * (x i : ℝ)

@[simp] theorem cost_eq_val_sub_payoff (agg : (ι → ℝ≥0) → ℝ≥0) (i : ι) (x : ι → ℝ≥0) :
    (R.toCostGame agg).cost i x = R.val i - R.payoff agg i x := by
  simp only [toCostGame, payoff]
  ring

theorem socialCost_eq_sum_val_sub_socialPayoff [Fintype ι] (agg : (ι → ℝ≥0) → ℝ≥0)
    (x : ι → ℝ≥0) :
    (R.toCostGame agg).socialCost x = (∑ i, R.val i) - R.socialPayoff agg x := by
  simp only [CostGame.socialCost, cost_eq_val_sub_payoff, socialPayoff, sum_sub_distrib,
    payoff, ← sum_mul]

/-- The **total-effort system reliability game** ([Varian2004], §3.1). -/
abbrev totalEffortGame [Fintype ι] : CostGame ι (fun _ => ℝ≥0) :=
  R.toCostGame totalEffort

/-- The **weakest-link system reliability game** ([Varian2004], §3.2). -/
abbrev weakestLinkGame [Fintype ι] [Nonempty ι] : CostGame ι (fun _ => ℝ≥0) :=
  R.toCostGame weakestLink

/-- The **best-shot system reliability game** ([Varian2004], §3.3). -/
abbrev bestShotGame [Fintype ι] : CostGame ι (fun _ => ℝ≥0) :=
  R.toCostGame bestShot

/-! ### Total-effort Nash equilibria, underprovision, and wrong-agent allocation -/

section TotalEffort

variable [Fintype ι] [DecidableEq ι]

private theorem sum_pi_single_nnreal (i : ι) (v : ℝ≥0) :
    ∑ j : ι, (Pi.single i v : ι → ℝ≥0) j = v := by
  rw [Fintype.sum_eq_single i fun j hj => Pi.single_eq_of_ne (M := fun _ => ℝ≥0) hj v,
    Pi.single_eq_same]

private theorem sum_mul_pi_single (c : ι → ℝ) (i : ι) (v : ℝ≥0) :
    ∑ j : ι, c j * ((Pi.single i v : ι → ℝ≥0) j : ℝ) = c i * (v : ℝ) := by
  rw [Fintype.sum_eq_single i fun j hj => by
    simp only [Pi.single_eq_of_ne hj, NNReal.coe_zero, mul_zero], Pi.single_eq_same]

private theorem totalEffort_update_aux (x : ι → ℝ≥0) (i : ι) (a : ℝ≥0) :
    totalEffort (Function.update x i a) = ∑ j ∈ univ.erase i, x j + a := by
  simp only [totalEffort]
  rw [← add_sum_erase _ _ (mem_univ i), Function.update_self, add_comm]
  congr 1
  exact sum_congr rfl fun j hj => Function.update_of_ne (ne_of_mem_erase hj) _ _

private theorem totalEffort_eq_erase_add (x : ι → ℝ≥0) (i : ι) :
    totalEffort x = ∑ j ∈ univ.erase i, x j + x i := by
  simpa only [Function.update_eq_self] using totalEffort_update_aux x i (x i)

private theorem cost_totalEffortGame_update (x : ι → ℝ≥0) (i : ι) (a : ℝ≥0) :
    R.totalEffortGame.cost i (Function.update x i a) =
      (R.val i * (1 - R.prob (((∑ j ∈ univ.erase i, x j) + a : ℝ≥0) : ℝ)) +
        R.unitCost i * (((∑ j ∈ univ.erase i, x j) + a : ℝ≥0) : ℝ)) -
        R.unitCost i * ((∑ j ∈ univ.erase i, x j : ℝ≥0) : ℝ) := by
  simp only [totalEffortGame, toCostGame, totalEffort_update_aux, Function.update_self,
    NNReal.coe_add]
  ring

/-- In the total-effort game, player `i`'s unique best response to opponents' aggregate effort
`X_{-i} = ∑ j ≠ i, x j` is truncated subtraction `xBar i - X_{-i}` (`max(xBar i - X_{-i}, 0)`),
as in [Varian2004], §3.1, p. 3. -/
theorem cost_totalEffortGame_bestResponse_le {xBar : ι → ℝ≥0}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob) (hVal : ∀ i, 0 < R.val i)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i))
    (x : ι → ℝ≥0) (i : ι) (a : ℝ≥0) :
    R.totalEffortGame.cost i (Function.update x i (xBar i - ∑ j ∈ univ.erase i, x j)) ≤
      R.totalEffortGame.cost i (Function.update x i a) := by
  set Xminus : ℝ≥0 := ∑ j ∈ univ.erase i, x j
  rw [cost_totalEffortGame_update, cost_totalEffortGame_update]
  by_cases hle : Xminus ≤ xBar i
  · rw [add_tsub_cancel_of_le hle]
    linarith [hOpt i (Xminus + a)]
  · have hgt : xBar i < Xminus := lt_of_not_ge hle
    rw [tsub_eq_zero_of_le hgt.le, add_zero]
    rcases eq_or_ne a 0 with rfl | ha
    · rw [add_zero]
    · have hlt : Xminus < Xminus + a := lt_add_of_pos_right _ (pos_iff_ne_zero.mpr ha)
      linarith [(hOpt i).lt_of_le_of_lt hConc (hVal i) hgt.le hlt]

private theorem bestResponse_eq_iff_of_strictConcave {xBar : ι → ℝ≥0}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob) (hVal : ∀ i, 0 < R.val i)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i))
    (x : ι → ℝ≥0) (i : ι) :
    (∀ a : ℝ≥0, R.totalEffortGame.cost i x ≤
      R.totalEffortGame.cost i (Function.update x i a)) ↔
      x i = xBar i - ∑ j ∈ univ.erase i, x j := by
  set Xminus : ℝ≥0 := ∑ j ∈ univ.erase i, x j
  set br : ℝ≥0 := xBar i - Xminus
  refine ⟨fun h => ?_, fun hx a => ?_⟩
  · by_contra hne
    have hle := h br
    have hself : x = Function.update x i (x i) := (Function.update_eq_self i x).symm
    conv_lhs at hle => rw [hself]
    rw [cost_totalEffortGame_update, cost_totalEffortGame_update] at hle
    by_cases hX : Xminus ≤ xBar i
    · have hbr : Xminus + br = xBar i := add_tsub_cancel_of_le hX
      have hne' : Xminus + x i ≠ xBar i := by
        intro heq
        apply hne
        calc x i = Xminus + x i - Xminus := (add_tsub_cancel_left _ _).symm
          _ = br := by rw [heq]
      rw [hbr] at hle
      linarith [(hOpt i).strict_lt_of_ne hConc (hVal i) hne']
    · have hgt : xBar i < Xminus := lt_of_not_ge hX
      have hbr0 : br = 0 := tsub_eq_zero_of_le hgt.le
      have hxi_pos : 0 < x i := pos_iff_ne_zero.mpr (by rwa [hbr0] at hne)
      rw [hbr0, add_zero] at hle
      linarith [(hOpt i).lt_of_le_of_lt hConc (hVal i) hgt.le (lt_add_of_pos_right _ hxi_pos)]
  · have hself : x = Function.update x i br := funext fun j => by
      rcases eq_or_ne i j with rfl | hj
      · simpa only [Function.update_self] using hx
      · simp only [Function.update_of_ne hj.symm]
    conv_lhs => rw [hself]
    exact R.cost_totalEffortGame_bestResponse_le hConc hVal hOpt x i a

/-- **Varian's Fact 1, complete characterization** ([Varian2004], §3.1, p. 3): in the `ι`-agent
total-effort game with strictly concave reliability, a profile `x` is a pure Nash equilibrium if and
only if aggregate effort equals `sup_i xBar i` and every agent with `xBar i < sup_j xBar j`
completely free-rides (`x i = 0`). -/
theorem isPureNash_totalEffortGame_iff {xBar : ι → ℝ≥0}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob) (hVal : ∀ i, 0 < R.val i)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i)) (x : ι → ℝ≥0) :
    R.totalEffortGame.IsPureNash x ↔
      totalEffort x = univ.sup xBar ∧ ∀ i, xBar i < univ.sup xBar → x i = 0 := by
  refine ⟨fun hN => ?_, fun ⟨htot, hzero⟩ i => ?_⟩
  · have hbr : ∀ i, x i = xBar i - ∑ j ∈ univ.erase i, x j := fun i =>
      (R.bestResponse_eq_iff_of_strictConcave hConc hVal hOpt x i).mp (hN i)
    have hpos_eq : ∀ i, 0 < x i → totalEffort x = xBar i := fun i hxi => by
      rw [hbr i, tsub_pos_iff_lt] at hxi
      rw [totalEffort_eq_erase_add x i, hbr i, add_tsub_cancel_of_le hxi.le]
    have hsup_le : univ.sup xBar ≤ totalEffort x := Finset.sup_le fun i _ => by
      rw [totalEffort_eq_erase_add x i, hbr i]
      exact le_add_tsub
    have hle_sup : totalEffort x ≤ univ.sup xBar := by
      rcases eq_or_ne (totalEffort x) 0 with hpos | hpos
      · simp only [hpos, zero_le]
      · obtain ⟨i, -, hxi⟩ := exists_ne_zero_of_sum_ne_zero hpos
        exact (hpos_eq i (pos_iff_ne_zero.mpr hxi)).trans_le (le_sup (mem_univ i))
    have htot_eq : totalEffort x = univ.sup xBar := le_antisymm hle_sup hsup_le
    refine ⟨htot_eq, fun i hlt => ?_⟩
    by_contra hne
    exact hlt.ne (htot_eq.symm.trans (hpos_eq i (pos_iff_ne_zero.mpr hne))).symm
  · refine (R.bestResponse_eq_iff_of_strictConcave hConc hVal hOpt x i).mpr ?_
    have hsum := totalEffort_eq_erase_add x i
    by_cases hchamp : xBar i = univ.sup xBar
    · rw [← hchamp] at htot
      calc x i = totalEffort x - ∑ j ∈ univ.erase i, x j := by
            rw [hsum, add_tsub_cancel_left]
        _ = xBar i - ∑ j ∈ univ.erase i, x j := by rw [htot]
    · have hlt : xBar i < univ.sup xBar := lt_of_le_of_ne (le_sup (mem_univ i)) hchamp
      rw [hzero i hlt, add_zero, htot] at hsum
      rw [hzero i hlt, ← hsum, tsub_eq_zero_of_le hlt.le]

/-- **Varian's Fact 1, champion equilibrium** ([Varian2004], §3.1, p. 3): if `iStar` achieves the
maximum standalone effort `xBar iStar` across all agents, then `Pi.single iStar (xBar iStar)` is a
pure Nash equilibrium of `R.totalEffortGame` in which all other agents exert zero effort. -/
theorem isPureNash_totalEffortGame_single {xBar : ι → ℝ≥0} {iStar : ι}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob) (hVal : ∀ i, 0 < R.val i)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i))
    (hMax : ∀ j, xBar j ≤ xBar iStar) :
    R.totalEffortGame.IsPureNash (Pi.single iStar (xBar iStar)) := by
  have hsup : univ.sup xBar = xBar iStar :=
    le_antisymm (Finset.sup_le fun j _ => hMax j) (le_sup (mem_univ iStar))
  rw [R.isPureNash_totalEffortGame_iff hConc hVal hOpt]
  exact ⟨by rw [totalEffort, sum_pi_single_nnreal, hsup],
    fun i hlt => Pi.single_eq_of_ne (fun h => hlt.ne (by rw [h, hsup])) _⟩

/-- **Varian's Fact 1, uniqueness** ([Varian2004], §3.1, p. 3): when a single agent `iStar` has a
strictly larger standalone target effort than every other agent, `Pi.single iStar (xBar iStar)` is
the unique pure Nash equilibrium of `R.totalEffortGame`. -/
theorem eq_single_of_isPureNash_totalEffortGame {xBar : ι → ℝ≥0} {iStar : ι}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob) (hVal : ∀ i, 0 < R.val i)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i))
    (hStrict : ∀ j, j ≠ iStar → xBar j < xBar iStar) {x : ι → ℝ≥0}
    (hx : R.totalEffortGame.IsPureNash x) :
    x = Pi.single iStar (xBar iStar) := by
  have hsup : univ.sup xBar = xBar iStar := le_antisymm
    (Finset.sup_le fun j _ => if hj : j = iStar then hj ▸ le_rfl else (hStrict j hj).le)
    (le_sup (mem_univ iStar))
  obtain ⟨htot, hzero⟩ := (R.isPureNash_totalEffortGame_iff hConc hVal hOpt x).mp hx
  have hsum := totalEffort_eq_erase_add x iStar
  rw [htot, hsup,
    sum_eq_zero fun j hj => hzero j (hsup.symm ▸ hStrict j (ne_of_mem_erase hj)),
    zero_add] at hsum
  refine funext fun j => ?_
  rcases eq_or_ne iStar j with rfl | hj
  · simpa only [Pi.single_eq_same] using hsum.symm
  · rw [Pi.single_eq_of_ne hj.symm, hzero j (hsup.symm ▸ hStrict j hj.symm)]

/-- **Total-effort social optimum** ([Varian2004], §4.1, eq. (5), p. 6): if `iMin` has the minimum
marginal effort cost among all agents and `xOpt` is the standalone optimum for total valuation
`∑ i, R.val i` and unit cost `R.unitCost iMin`, then `Pi.single iMin xOpt` minimizes social cost
over all effort profiles. -/
theorem socialCost_totalEffortGame_single_le {iMin : ι} {xOpt : ℝ≥0}
    (hMin : ∀ j, R.unitCost iMin ≤ R.unitCost j)
    (hOpt : IsStandaloneOpt R.prob (∑ i, R.val i) (R.unitCost iMin) xOpt)
    (x : ι → ℝ≥0) :
    R.totalEffortGame.socialCost (Pi.single iMin xOpt) ≤ R.totalEffortGame.socialCost x := by
  have hcost_lb : R.unitCost iMin * (totalEffort x : ℝ) ≤ ∑ i, R.unitCost i * (x i : ℝ) := by
    simp only [totalEffort, NNReal.coe_sum, mul_sum]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hMin j) (x j).coe_nonneg
  simp only [CostGame.socialCost, totalEffortGame, toCostGame, sum_add_distrib, ← sum_mul,
    totalEffort, sum_pi_single_nnreal, sum_mul_pi_single]
  linarith [hOpt (totalEffort x)]

omit [DecidableEq ι] in
private theorem val_div_unitCost_lt_sum_div_min [Nontrivial ι] {iMin : ι}
    (hVal : ∀ i, 0 < R.val i) (hCost : ∀ i, 0 < R.unitCost i)
    (hMin : ∀ j, R.unitCost iMin ≤ R.unitCost j) (i : ι) :
    0 < ∑ k, R.val k ∧ R.val i / R.unitCost i < (∑ k, R.val k) / R.unitCost iMin := by
  have hVsum : R.val i < ∑ k, R.val k := self_lt_sum_of_pos hVal i
  exact ⟨lt_trans (hVal i) hVsum,
    (div_lt_div_iff₀ (hCost i) (hCost iMin)).mpr <|
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hMin i) (hVal i).le)
        (mul_lt_mul_of_pos_right hVsum (hCost i))⟩

/-- **Varian's Fact 3a, weak underprovision** ([Varian2004], §4.1, p. 6): in any pure Nash
equilibrium `x` of the total-effort game with `|ι| ≥ 2` positive-valuation agents, total effort
never exceeds the socially optimal total effort `xOpt`. -/
theorem totalEffort_le_socialOpt_of_isPureNash [Nontrivial ι] {xBar : ι → ℝ≥0}
    {iMin : ι} {xOpt : ℝ≥0}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob)
    (hVal : ∀ i, 0 < R.val i) (hCost : ∀ i, 0 < R.unitCost i)
    (hMin : ∀ j, R.unitCost iMin ≤ R.unitCost j)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i))
    (hSoc : IsStandaloneOpt R.prob (∑ i, R.val i) (R.unitCost iMin) xOpt)
    {x : ι → ℝ≥0} (hx : R.totalEffortGame.IsPureNash x) :
    totalEffort x ≤ xOpt := by
  obtain ⟨htot, _⟩ := (R.isPureNash_totalEffortGame_iff hConc hVal hOpt x).mp hx
  rw [htot]
  refine Finset.sup_le fun i _ => ?_
  obtain ⟨hVpos, hratio⟩ := R.val_div_unitCost_lt_sum_div_min hVal hCost hMin i
  exact (hOpt i).le_of_ratio_lt hSoc (hVal i) (hCost i) hVpos (hCost iMin) hratio

/-- **Varian's Fact 3a, strict underprovision** ([Varian2004], §4.1, p. 6): when `|ι| ≥ 2` and the
social optimum `xOpt > 0` satisfies the interior first-order condition, every pure Nash equilibrium
exerts strictly less aggregate effort than `xOpt`. -/
theorem totalEffort_lt_socialOpt_of_isPureNash [Nontrivial ι] {xBar : ι → ℝ≥0}
    {iMin : ι} {xOpt : ℝ≥0} {P' : ℝ}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob)
    (hVal : ∀ i, 0 < R.val i) (hCost : ∀ i, 0 < R.unitCost i)
    (hMin : ∀ j, R.unitCost iMin ≤ R.unitCost j)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i))
    (hSoc : IsStandaloneOpt R.prob (∑ i, R.val i) (R.unitCost iMin) xOpt)
    (hxOpt_pos : 0 < xOpt) (hDeriv : HasDerivAt R.prob P' xOpt)
    (hFOC : (∑ i, R.val i) * P' = R.unitCost iMin)
    {x : ι → ℝ≥0} (hx : R.totalEffortGame.IsPureNash x) :
    totalEffort x < xOpt := by
  obtain ⟨htot, _⟩ := (R.isPureNash_totalEffortGame_iff hConc hVal hOpt x).mp hx
  rw [htot]
  obtain ⟨iStar, _, hiStar⟩ := exists_mem_eq_sup univ univ_nonempty xBar
  rw [hiStar]
  obtain ⟨hVpos, hratio⟩ := R.val_div_unitCost_lt_sum_div_min hVal hCost hMin iStar
  exact (hOpt iStar).lt_of_ratio_lt_of_hasDerivAt hSoc (hVal iStar) (hCost iStar) hVpos
    (hCost iMin) hratio hxOpt_pos hDeriv hFOC

/-- **Varian's Fact 3b, wrong-agent theorem** ([Varian2004], §4.1, p. 6): when agent `iMin` has a
strictly smaller unit cost than the ratio champion `iStar` (`unitCost iMin < unitCost iStar` while
`xBar j < xBar iStar` for `j ≠ iStar`), every pure Nash equilibrium places zero effort on `iMin`,
whereas every social-cost-minimizing profile `y` places zero effort on `iStar`. -/
theorem wrongAgent_support_disjoint {xBar : ι → ℝ≥0} {iMin iStar : ι}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob) (hVal : ∀ i, 0 < R.val i)
    (hMin : ∀ j, R.unitCost iMin ≤ R.unitCost j)
    (hCostLt : R.unitCost iMin < R.unitCost iStar)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i))
    (hStrict : ∀ j, j ≠ iStar → xBar j < xBar iStar)
    {x y : ι → ℝ≥0} (hx : R.totalEffortGame.IsPureNash x)
    (hy : ∀ z, R.totalEffortGame.socialCost y ≤ R.totalEffortGame.socialCost z) :
    x iMin = 0 ∧ y iStar = 0 := by
  have hne : iMin ≠ iStar := fun h => lt_irrefl _ (h ▸ hCostLt)
  refine ⟨by rw [R.eq_single_of_isPureNash_totalEffortGame hConc hVal hOpt hStrict hx,
    Pi.single_eq_of_ne hne], ?_⟩
  by_contra hy_ne
  have hy_pos : 0 < (y iStar : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hy_ne)
  have hstrict_cost : R.unitCost iMin * (totalEffort y : ℝ) <
      ∑ j, R.unitCost j * (y j : ℝ) := by
    simp only [totalEffort, NNReal.coe_sum, mul_sum]
    exact sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_right (hMin j) (y j).coe_nonneg)
      ⟨iStar, mem_univ iStar, mul_lt_mul_of_pos_right hCostLt hy_pos⟩
  have hle_single := hy (Pi.single iMin (totalEffort y))
  simp only [CostGame.socialCost, totalEffortGame, toCostGame, sum_add_distrib, ← sum_mul,
    totalEffort, sum_pi_single_nnreal, sum_mul_pi_single] at hle_single
  linarith

/-- Total-effort game with Varian's §7.1 Pigouvian failure fine: the designated least-cost avoider
`iMin` additionally pays the failure externality `(∑ j ≠ iMin, val j) * (1 - prob (totalEffort x))`
when the system fails. -/
@[expose] def totalEffortLiabilityGame (iMin : ι) : CostGame ι (fun _ => ℝ≥0) where
  cost i x :=
    if i = iMin then
      (∑ j, R.val j) * (1 - R.prob (totalEffort x)) + R.unitCost i * (x i : ℝ)
    else
      R.val i * (1 - R.prob (totalEffort x)) + R.unitCost i * (x i : ℝ)

/-- **Varian's Fact 8** ([Varian2004], §7.1, pp. 8–9): imposing a failure fine equal to the losses
of all other agents on a least-cost avoider `iMin` makes the socially optimal profile
`Pi.single iMin xOpt` a pure Nash equilibrium. -/
theorem isPureNash_totalEffortLiabilityGame_single {xBar : ι → ℝ≥0} {iMin : ι} {xOpt : ℝ≥0}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob)
    (hVal : ∀ i, 0 < R.val i) (hCost : ∀ i, 0 < R.unitCost i)
    (hMin : ∀ j, R.unitCost iMin ≤ R.unitCost j)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i))
    (hSoc : IsStandaloneOpt R.prob (∑ i, R.val i) (R.unitCost iMin) xOpt) :
    (R.totalEffortLiabilityGame iMin).IsPureNash (Pi.single iMin xOpt) := by
  intro i a
  have h1 : totalEffort (Pi.single iMin xOpt : ι → ℝ≥0) = xOpt := sum_pi_single_nnreal iMin xOpt
  by_cases hi : i = iMin
  · subst hi
    have h2 : totalEffort (Function.update (Pi.single i xOpt : ι → ℝ≥0) i a) = a := by
      rw [totalEffort_update_aux,
        sum_eq_zero fun j hj => Pi.single_eq_of_ne (ne_of_mem_erase hj) _, zero_add]
    simpa only [totalEffortLiabilityGame, ↓reduceIte, Pi.single_eq_same, Function.update_self,
      h1, h2] using hSoc a
  · have h2 : totalEffort (Function.update (Pi.single iMin xOpt : ι → ℝ≥0) i a) = xOpt + a := by
      rw [totalEffort_update_aux, ← add_sum_erase _ _ (mem_erase.mpr ⟨Ne.symm hi, mem_univ iMin⟩),
        Pi.single_eq_same, sum_eq_zero fun j hj => Pi.single_eq_of_ne (mem_erase.mp hj).1 _,
        add_zero]
    simp only [totalEffortLiabilityGame, hi, ↓reduceIte, Pi.single_eq_of_ne hi, NNReal.coe_zero,
      mul_zero, add_zero, Function.update_self, h1, h2]
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · have : Nontrivial ι := ⟨⟨i, iMin, hi⟩⟩
      obtain ⟨hVpos, hratio⟩ := R.val_div_unitCost_lt_sum_div_min hVal hCost hMin i
      have hxle := (hOpt i).le_of_ratio_lt hSoc (hVal i) (hCost i) hVpos (hCost iMin) hratio
      have hlt := (hOpt i).lt_of_le_of_lt hConc (hVal i) hxle
        (lt_add_of_pos_right xOpt (pos_iff_ne_zero.mpr ha))
      simp only [NNReal.coe_add] at hlt ⊢
      linarith [mul_nonneg (hCost i).le xOpt.coe_nonneg]

end TotalEffort

/-! ### Weakest-link Nash equilibria, social optimum, and negligence due-care rule -/

section WeakestLink

variable [Fintype ι] [Nonempty ι]

private theorem weakestLink_const (z : ℝ≥0) : weakestLink (fun _ : ι => z) = z :=
  inf'_const univ_nonempty z

/-- **Weakest-link social optimum** ([Varian2004], §4.3, eq. (6), p. 6): when `0 ≤ R.unitCost i`
and `zOpt` is a standalone optimum for `(∑ i, R.val i, ∑ i, R.unitCost i)`, the symmetric profile
`fun _ => zOpt` minimizes `R.weakestLinkGame.socialCost` over all profiles. -/
theorem socialCost_weakestLinkGame_const_le {zOpt : ℝ≥0}
    (hCost : ∀ i, 0 ≤ R.unitCost i)
    (hSoc : IsStandaloneOpt R.prob (∑ i, R.val i) (∑ i, R.unitCost i) zOpt)
    (x : ι → ℝ≥0) :
    R.weakestLinkGame.socialCost (fun _ => zOpt) ≤ R.weakestLinkGame.socialCost x := by
  have hcost_lb : (∑ i, R.unitCost i) * (weakestLink x : ℝ) ≤ ∑ i, R.unitCost i * (x i : ℝ) := by
    rw [sum_mul]
    exact sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (inf'_le x (mem_univ i))) (hCost i)
  simp only [CostGame.socialCost, weakestLinkGame, toCostGame, sum_add_distrib, ← sum_mul,
    weakestLink_const]
  linarith [hSoc (weakestLink x)]

omit [Nonempty ι] in
/-- **Varian's Fact 4** ([Varian2004], §4.3, p. 7): with at least two positive-cost agents, the
socially optimal weakest-link effort `zOpt` never exceeds the socially optimal total effort
`xOpt`. -/
theorem weakestLink_socialOpt_le_totalEffort_socialOpt [Nontrivial ι] {iMin : ι}
    {zOpt xOpt : ℝ≥0}
    (hVal : 0 < ∑ i, R.val i) (hCost : ∀ i, 0 < R.unitCost i)
    (hWeak : IsStandaloneOpt R.prob (∑ i, R.val i) (∑ i, R.unitCost i) zOpt)
    (hTot : IsStandaloneOpt R.prob (∑ i, R.val i) (R.unitCost iMin) xOpt) :
    zOpt ≤ xOpt := by
  have hCsum : R.unitCost iMin < ∑ k, R.unitCost k := self_lt_sum_of_pos hCost iMin
  exact hWeak.le_of_ratio_lt hTot hVal (lt_trans (hCost iMin) hCsum) hVal (hCost iMin)
    (div_lt_div_of_pos_left hVal (hCost iMin) hCsum)

variable [DecidableEq ι]

private theorem weakestLink_update_const_of_le {z a : ℝ≥0} (i : ι) (ha : a ≤ z) :
    weakestLink (Function.update (fun _ : ι => z) i a) = a := by
  refine le_antisymm ?_ (le_inf' _ _ fun k _ => ?_)
  · simpa only [weakestLink, Function.update_self] using
      inf'_le (Function.update (fun _ : ι => z) i a) (mem_univ i)
  · by_cases hk : k = i
    · subst hk; simp only [Function.update_self, le_rfl]
    · simp only [Function.update_of_ne hk, ha]

private theorem weakestLink_update_const_of_ge {z a : ℝ≥0} {i j : ι} (hj : j ≠ i) (ha : z ≤ a) :
    weakestLink (Function.update (fun _ : ι => z) i a) = z := by
  refine le_antisymm ?_ (le_inf' _ _ fun k _ => ?_)
  · simpa only [weakestLink, Function.update_of_ne hj] using
      inf'_le (Function.update (fun _ : ι => z) i a) (mem_univ j)
  · by_cases hk : k = i
    · subst hk; simp only [Function.update_self, ha]
    · simp only [Function.update_of_ne hk, le_rfl]

private theorem weakestLink_update_const_of_subsingleton {z a : ℝ≥0} {i : ι}
    (hother : ∀ k, k = i) :
    weakestLink (Function.update (fun _ : ι => z) i a) = a :=
  le_antisymm
    (by simpa only [weakestLink, Function.update_self] using
      inf'_le (Function.update (fun _ : ι => z) i a) (mem_univ i))
    (le_inf' _ _ fun k _ => by rw [hother k, Function.update_self])

/-- **Varian's Fact 2, focal equilibrium** ([Varian2004], §3.2, p. 4): for any nonempty finite set
of agents, the constant profile `fun _ => inf_i xBar i` is a pure Nash equilibrium of the
weakest-link game. -/
theorem isPureNash_weakestLinkGame_const_inf {xBar : ι → ℝ≥0}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob)
    (hVal : ∀ i, 0 < R.val i) (hCost : ∀ i, 0 ≤ R.unitCost i)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i)) :
    R.weakestLinkGame.IsPureNash (fun _ => univ.inf' univ_nonempty xBar) := by
  set z : ℝ≥0 := univ.inf' univ_nonempty xBar
  intro i a
  rcases le_or_gt a z with ha | ha
  · simp only [weakestLinkGame, toCostGame, weakestLink_const, weakestLink_update_const_of_le i ha,
      Function.update_self]
    rcases eq_or_lt_of_le ha with rfl | hlt
    · exact le_rfl
    · exact ((hOpt i).lt_of_lt_of_le hConc (hVal i) hlt (inf'_le xBar (mem_univ i))).le
  · by_cases hother : ∃ j, j ≠ i
    · obtain ⟨j, hj⟩ := hother
      simp only [weakestLinkGame, toCostGame, weakestLink_const,
        weakestLink_update_const_of_ge hj ha.le, Function.update_self]
      exact add_le_add_right (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ha.le) (hCost i)) _
    · push Not at hother
      have hz_eq : z = xBar i :=
        le_antisymm (inf'_le xBar (mem_univ i)) (le_inf' _ _ fun k _ => by rw [hother k])
      dsimp only [weakestLinkGame, toCostGame]
      rw [weakestLink_const, weakestLink_update_const_of_subsingleton hother, Function.update_self,
        hz_eq]
      exact hOpt i a

/-- **Varian's Fact 2, continuum characterization** ([Varian2004], §3.2, eqs. (1)–(2), p. 4): with
at least two agents (`[Nontrivial ι]`), a profile `x` is a pure Nash equilibrium of the
weakest-link game if and only if all agents exert the same effort `z ≤ inf_i xBar i`. -/
theorem isPureNash_weakestLinkGame_iff [Nontrivial ι] {xBar : ι → ℝ≥0}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob)
    (hVal : ∀ i, 0 < R.val i) (hCost : ∀ i, 0 < R.unitCost i)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i)) (x : ι → ℝ≥0) :
    R.weakestLinkGame.IsPureNash x ↔
      ∃ z ≤ univ.inf' univ_nonempty xBar, x = fun _ => z := by
  refine ⟨fun hN => ?_, ?_⟩
  · set z : ℝ≥0 := weakestLink x
    obtain ⟨jMin, _, hjMin⟩ := exists_mem_eq_inf' univ_nonempty x
    have hconst : ∀ i, x i = z := fun i => le_antisymm (by
      by_contra hlt
      have hgt : z < x i := lt_of_not_ge hlt
      have hij : jMin ≠ i := fun h => hgt.ne (h ▸ hjMin)
      have hw_upd : weakestLink (Function.update x i z) = z := by
        refine le_antisymm ?_ (le_inf' _ _ fun k _ => ?_)
        · simpa only [weakestLink, Function.update_of_ne hij, hjMin.symm] using
            inf'_le (Function.update x i z) (mem_univ jMin)
        · rcases eq_or_ne i k with rfl | hk
          · simp
          · simpa only [Function.update_of_ne hk.symm] using inf'_le x (mem_univ k)
      have hle := hN i z
      dsimp only [weakestLinkGame, toCostGame] at hle
      rw [hw_upd, Function.update_self, show weakestLink x = z from rfl] at hle
      nlinarith [NNReal.coe_lt_coe.mpr hgt, hCost i]) (inf'_le x (mem_univ i))
    have hx_eq : x = fun _ => z := funext hconst
    refine ⟨z, le_inf' _ _ fun i _ => by
      by_contra hlt
      have hgt : xBar i < z := lt_of_not_ge hlt
      have hle := hN i (xBar i)
      dsimp only [weakestLinkGame, toCostGame] at hle
      rw [hx_eq, weakestLink_update_const_of_le i hgt.le, weakestLink_const,
        Function.update_self] at hle
      linarith [(hOpt i).strict_lt_of_ne hConc (hVal i) hgt.ne'], hx_eq⟩
  · rintro ⟨z, hz, rfl⟩ i a
    rcases le_or_gt a z with ha | ha
    · dsimp only [weakestLinkGame, toCostGame]
      rw [weakestLink_const, weakestLink_update_const_of_le i ha, Function.update_self]
      rcases eq_or_lt_of_le ha with rfl | hlt
      · exact le_rfl
      · exact ((hOpt i).lt_of_lt_of_le hConc (hVal i) hlt
          (hz.trans (inf'_le xBar (mem_univ i)))).le
    · obtain ⟨j, hj⟩ := exists_ne i
      dsimp only [weakestLinkGame, toCostGame]
      rw [weakestLink_const, weakestLink_update_const_of_ge hj ha.le, Function.update_self]
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ha.le) (hCost i).le) _

/-- **Pareto dominance of the maximal weakest-link equilibrium** ([Varian2004], §3.2, p. 4): the
profile `fun _ => inf_j xBar j` gives every player weakly lower cost than any other pure Nash
equilibrium of `R.weakestLinkGame` (and strictly lower cost for every player whenever the two
profiles differ). -/
theorem cost_weakestLinkGame_const_inf_le_of_isPureNash [Nontrivial ι] {xBar : ι → ℝ≥0}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob)
    (hVal : ∀ i, 0 < R.val i) (hCost : ∀ i, 0 < R.unitCost i)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i))
    {x : ι → ℝ≥0} (hx : R.weakestLinkGame.IsPureNash x) (i : ι) :
    R.weakestLinkGame.cost i (fun _ => univ.inf' univ_nonempty xBar) ≤
      R.weakestLinkGame.cost i x := by
  obtain ⟨z, hz, rfl⟩ := (R.isPureNash_weakestLinkGame_iff hConc hVal hCost hOpt x).mp hx
  dsimp only [weakestLinkGame, toCostGame]
  rw [weakestLink_const, weakestLink_const]
  rcases eq_or_lt_of_le hz with heq | hlt
  · rw [heq]
  · exact ((hOpt i).lt_of_lt_of_le hConc (hVal i) hlt (inf'_le xBar (mem_univ i))).le

/-- **Varian's Fact 7, identical-agent efficiency** ([Varian2004], §6, p. 8): when all agents share
the same valuation `v > 0` and unit cost `c > 0`, any standalone optimum `xStar` for `(v, c)` makes
`fun _ => xStar` simultaneously a pure Nash equilibrium and a global social-cost minimizer of the
weakest-link game (Price of Stability = `1` for every `|ι| ≥ 1`). -/
theorem identicalAgents_weakestLink_socialOpt_isPureNash {v c : ℝ} {xStar : ℝ≥0}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob)
    (hv : 0 < v) (hc : 0 < c)
    (hVal_eq : ∀ i, R.val i = v) (hCost_eq : ∀ i, R.unitCost i = c)
    (hOpt : IsStandaloneOpt R.prob v c xStar) :
    R.weakestLinkGame.IsPureNash (fun _ => xStar) ∧
      ∀ x, R.weakestLinkGame.socialCost (fun _ => xStar) ≤ R.weakestLinkGame.socialCost x := by
  have hOpt_i : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) xStar := fun i => by
    simpa only [hVal_eq i, hCost_eq i] using hOpt
  have hCost0 : ∀ i, 0 ≤ R.unitCost i := fun i => (hCost_eq i).symm ▸ hc.le
  have hNash : R.weakestLinkGame.IsPureNash (fun _ => xStar) := by
    simpa only [inf'_const] using
      R.isPureNash_weakestLinkGame_const_inf hConc (fun i => (hVal_eq i).symm ▸ hv) hCost0 hOpt_i
  have hSoc : IsStandaloneOpt R.prob (∑ i, R.val i) (∑ i, R.unitCost i) xStar := fun z => by
    simp only [hVal_eq, hCost_eq, sum_const, card_univ, nsmul_eq_mul]
    linarith [mul_le_mul_of_nonneg_left (hOpt z) (Nat.cast_nonneg (Fintype.card ι))]
  exact ⟨hNash, R.socialCost_weakestLinkGame_const_le hCost0 hSoc⟩

/-- Weakest-link game under Varian's §7.2 **negligence rule** with due-care threshold `zDue`
([Varian2004], §7.2, pp. 10–11): an agent meeting due care (`zDue ≤ x i`) bears no external
liability, whereas an agent choosing `x i < zDue` must compensate the other agents' failure losses
`(∑ j ≠ i, val j) * (1 - prob (weakestLink x))`. -/
@[expose] def weakestLinkNegligenceGame (zDue : ℝ≥0) : CostGame ι (fun _ => ℝ≥0) where
  cost i x :=
    if zDue ≤ x i then
      R.val i * (1 - R.prob (weakestLink x)) + R.unitCost i * (x i : ℝ)
    else
      (∑ j, R.val j) * (1 - R.prob (weakestLink x)) + R.unitCost i * (x i : ℝ)

/-- **Varian's Fact 9** ([Varian2004], §7.2, pp. 10–11): under the negligence rule with due-care
standard set to the socially optimal weakest-link effort `zOpt`, the symmetric socially optimal
profile `fun _ => zOpt` is a pure Nash equilibrium for arbitrary heterogeneous `(val, unitCost)`
with `0 ≤ val i`, `0 ≤ unitCost i`, and `prob ≤ 1` at `zOpt`. -/
theorem isPureNash_weakestLinkNegligenceGame_const {zOpt : ℝ≥0}
    (hVal : ∀ i, 0 ≤ R.val i) (hCost : ∀ i, 0 ≤ R.unitCost i)
    (hProb_le_one : R.prob zOpt ≤ 1)
    (hSoc : IsStandaloneOpt R.prob (∑ i, R.val i) (∑ i, R.unitCost i) zOpt) :
    (R.weakestLinkNegligenceGame zOpt).IsPureNash (fun _ => zOpt) := by
  intro i a
  by_cases ha : zOpt ≤ a
  · by_cases hother : ∃ j, j ≠ i
    · obtain ⟨j, hj⟩ := hother
      simp only [weakestLinkNegligenceGame, le_rfl, ha, ↓reduceIte, weakestLink_const,
        weakestLink_update_const_of_ge hj ha, Function.update_self]
      exact add_le_add_right (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ha) (hCost i)) _
    · push Not at hother
      simp only [weakestLinkNegligenceGame, le_rfl, ha, ↓reduceIte, weakestLink_const,
        weakestLink_update_const_of_subsingleton hother, Function.update_self]
      simpa only [Fintype.sum_eq_single i fun j hj => (hj (hother j)).elim] using hSoc a
  · have hlt : a < zOpt := lt_of_not_ge ha
    simp only [weakestLinkNegligenceGame, le_rfl, ha, ↓reduceIte, weakestLink_const,
      weakestLink_update_const_of_le i hlt.le, Function.update_self]
    have hV_gap := mul_le_mul_of_nonneg_right (single_le_sum (fun j _ => hVal j) (mem_univ i))
      (sub_nonneg.mpr hProb_le_one)
    have hC_other : 0 ≤ (∑ j ∈ univ.erase i, R.unitCost j) * ((zOpt : ℝ) - (a : ℝ)) :=
      mul_nonneg (sum_nonneg fun j _ => hCost j) (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hlt.le))
    have hC_split : (∑ j, R.unitCost j) * (zOpt : ℝ) - (∑ j, R.unitCost j) * (a : ℝ) =
        R.unitCost i * ((zOpt : ℝ) - (a : ℝ)) +
          (∑ j ∈ univ.erase i, R.unitCost j) * ((zOpt : ℝ) - (a : ℝ)) := by
      rw [← add_sum_erase _ _ (mem_univ i)]; ring
    linarith [hSoc a]

end WeakestLink

/-! ### Group-size comparative statics (Varian's Fact 5) -/

/-- Restriction of `R` to a finite sub-population `S : Finset ι`. -/
abbrev restrict (S : Finset ι) : SystemReliabilitySpec S where
  val i := R.val i
  unitCost i := R.unitCost i
  prob := R.prob

/-- **Varian's Fact 5, total-effort direction** ([Varian2004], §5, p. 7): for finite agent pools
`S ⊆ T`, the system reliability `R.prob (totalEffort xS)` at any pure Nash equilibrium `xS` of the
total-effort game on `S` is at most `R.prob (totalEffort xT)` at any pure Nash equilibrium `xT` on
`T`. -/
theorem prob_totalEffort_le_of_subset_of_isPureNash [DecidableEq ι]
    {S T : Finset ι} (hST : S ⊆ T) {xBar : ι → ℝ≥0}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob)
    (hMono : MonotoneOn R.prob (Set.Ici 0))
    (hVal : ∀ i, 0 < R.val i)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i))
    {xS : S → ℝ≥0} (hxS : (R.restrict S).totalEffortGame.IsPureNash xS)
    {xT : T → ℝ≥0} (hxT : (R.restrict T).totalEffortGame.IsPureNash xT) :
    R.prob (totalEffort xS) ≤ R.prob (totalEffort xT) := by
  have hle : totalEffort xS ≤ totalEffort xT := by
    rw [(((R.restrict S).isPureNash_totalEffortGame_iff hConc (fun i => hVal i)
        (fun i => hOpt i) xS).mp hxS).1,
      (((R.restrict T).isPureNash_totalEffortGame_iff hConc (fun i => hVal i)
        (fun i => hOpt i) xT).mp hxT).1]
    exact Finset.sup_le fun i _ =>
      Finset.le_sup (f := fun j : T => xBar j.1) (mem_univ ⟨i.1, hST i.2⟩)
  exact hMono (totalEffort xS).coe_nonneg (totalEffort xT).coe_nonneg (NNReal.coe_le_coe.mpr hle)

private theorem weakestLink_le_inf_of_isPureNash [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {xBar : ι → ℝ≥0} (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob)
    (hVal : ∀ i, 0 < R.val i) (hCost : ∀ i, 0 ≤ R.unitCost i)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i))
    {x : ι → ℝ≥0} (hx : R.weakestLinkGame.IsPureNash x) :
    weakestLink x ≤ univ.inf' univ_nonempty xBar := by
  by_contra hlt
  have hgt : univ.inf' univ_nonempty xBar < weakestLink x := lt_of_not_ge hlt
  obtain ⟨i, _, hi⟩ := exists_mem_eq_inf' univ_nonempty xBar
  have hxi_gt : xBar i < weakestLink x := hi ▸ hgt
  have hw_upd : weakestLink (Function.update x i (xBar i)) = xBar i := by
    refine le_antisymm ?_ (le_inf' univ_nonempty _ fun k _ => ?_)
    · simpa only [weakestLink, Function.update_self] using
        inf'_le (Function.update x i (xBar i)) (mem_univ i)
    · by_cases hk : k = i
      · subst hk; simp only [Function.update_self, le_rfl]
      · simp only [Function.update_of_ne hk]
        exact hxi_gt.le.trans (inf'_le x (mem_univ k))
  have hdev := hx i (xBar i)
  dsimp only [weakestLinkGame, toCostGame] at hdev
  rw [hw_upd, Function.update_self] at hdev
  have hstrict := (hOpt i).strict_lt_of_ne hConc (hVal i) hxi_gt.ne'
  have hc_le : R.unitCost i * (weakestLink x : ℝ) ≤ R.unitCost i * (x i : ℝ) :=
    mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (inf'_le x (mem_univ i))) (hCost i)
  linarith

/-- **Varian's Fact 5, weakest-link direction** ([Varian2004], §5, p. 7): for nonempty finite agent
pools `S ⊆ T`, the Pareto-dominant focal profile
`fun _ : S => univ.inf' univ_nonempty (fun i : S => xBar i)` is a pure Nash equilibrium of the
weakest-link game on `S`, and its system reliability `R.prob (weakestLink ...)` upper-bounds
`R.prob (weakestLink xT)` at every pure Nash equilibrium `xT` on the larger pool `T`. -/
theorem prob_weakestLink_le_of_subset_of_isPureNash [DecidableEq ι]
    {S T : Finset ι} [Nonempty S] [Nonempty T] (hST : S ⊆ T) {xBar : ι → ℝ≥0}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob)
    (hMono : MonotoneOn R.prob (Set.Ici 0))
    (hVal : ∀ i, 0 < R.val i) (hCost : ∀ i, 0 ≤ R.unitCost i)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i))
    {xT : T → ℝ≥0} (hxT : (R.restrict T).weakestLinkGame.IsPureNash xT) :
    let xS : S → ℝ≥0 := fun _ => univ.inf' univ_nonempty (fun i : S => xBar i)
    (R.restrict S).weakestLinkGame.IsPureNash xS ∧
      R.prob (weakestLink xT) ≤ R.prob (weakestLink xS) := by
  intro xS
  refine ⟨(R.restrict S).isPureNash_weakestLinkGame_const_inf hConc (fun i => hVal i)
    (fun i => hCost i) (fun i => hOpt i), ?_⟩
  have hwT : weakestLink xT ≤ univ.inf' univ_nonempty (fun j : T => xBar j.1) :=
    (R.restrict T).weakestLink_le_inf_of_isPureNash hConc (fun j => hVal j) (fun j => hCost j)
      (fun j => hOpt j) hxT
  have hinf_le : univ.inf' univ_nonempty (fun j : T => xBar j.1) ≤
      univ.inf' univ_nonempty (fun i : S => xBar i.1) :=
    le_inf' univ_nonempty _ fun i _ =>
      inf'_le (fun j : T => xBar j.1) (mem_univ ⟨i.1, hST i.2⟩)
  have hwS : weakestLink xS = univ.inf' univ_nonempty (fun i : S => xBar i.1) := by
    simp only [xS, weakestLink, inf'_const]
  exact hMono (weakestLink xT).coe_nonneg (weakestLink xS).coe_nonneg
    (NNReal.coe_le_coe.mpr (hwT.trans (hinf_le.trans_eq hwS.symm)))

/-! ### Best-shot Nash equilibria: champion and slacker equilibria -/

section BestShot

variable [Fintype ι] [DecidableEq ι]

private theorem bestShot_pi_single (k : ι) (v : ℝ≥0) :
    bestShot (Pi.single k v : ι → ℝ≥0) = v := by
  refine le_antisymm (Finset.sup_le fun j _ => ?_) ?_
  · rcases eq_or_ne j k with rfl | hj
    · simp only [Pi.single_eq_same, le_rfl]
    · simp only [Pi.single_eq_of_ne hj, zero_le]
  · simpa only [bestShot, Pi.single_eq_same] using le_sup (f := Pi.single k v) (mem_univ k)

private theorem bestShot_update_single_ne {k i : ι} (hik : i ≠ k) (v a : ℝ≥0) :
    bestShot (Function.update (Pi.single k v : ι → ℝ≥0) i a) = max v a := by
  refine le_antisymm (Finset.sup_le fun j _ => ?_) (max_le ?_ ?_)
  · by_cases hji : j = i
    · subst hji; simp only [Function.update_self, le_max_right]
    · rw [Function.update_of_ne hji]
      by_cases hjk : j = k
      · subst hjk; simp only [Pi.single_eq_same, le_max_left]
      · simp only [Pi.single_eq_of_ne hjk, zero_le]
  · simpa only [bestShot, Function.update_of_ne (Ne.symm hik), Pi.single_eq_same] using
      le_sup (f := Function.update (Pi.single k v : ι → ℝ≥0) i a) (mem_univ k)
  · simpa only [bestShot, Function.update_self] using
      le_sup (f := Function.update (Pi.single k v : ι → ℝ≥0) i a) (mem_univ i)

/-- **Characterization of single-contributor best-shot pure Nash equilibria** ([Varian2004], §3.3,
pp. 4–5): under nondecreasing reliability `prob` and nonnegative costs, `Pi.single k (xBar k)` is a
pure Nash equilibrium of `R.bestShotGame` if and only if every other agent `i ≠ k` prefers
free-riding on `xBar k` to exerting its own standalone optimum `xBar i`. -/
theorem isPureNash_bestShotGame_single_iff {xBar : ι → ℝ≥0} {k : ι}
    (hMono : MonotoneOn R.prob (Set.Ici 0))
    (hVal : ∀ i, 0 ≤ R.val i) (hCost : ∀ i, 0 ≤ R.unitCost i)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i)) :
    R.bestShotGame.IsPureNash (Pi.single k (xBar k)) ↔
      ∀ i, i ≠ k →
        R.val i * (1 - R.prob (xBar k)) ≤
          R.val i * (1 - R.prob (xBar i)) + R.unitCost i * (xBar i : ℝ) := by
  set sK : ι → ℝ≥0 := Pi.single k (xBar k)
  have hsup_single : bestShot sK = xBar k := bestShot_pi_single k (xBar k)
  refine ⟨fun hN i hik => ?_, fun hFree i a => ?_⟩
  · rcases le_or_gt (xBar i) (xBar k) with hle | hgt
    · have hP : R.prob (xBar i) ≤ R.prob (xBar k) :=
        hMono (xBar i).coe_nonneg (xBar k).coe_nonneg hle
      have hc0 : 0 ≤ R.unitCost i * (xBar i : ℝ) := mul_nonneg (hCost i) (xBar i).coe_nonneg
      nlinarith [hVal i]
    · have hle := hN i (xBar i)
      dsimp only [bestShotGame, toCostGame] at hle
      rwa [hsup_single, bestShot_update_single_ne hik (xBar k) (xBar i), max_eq_right hgt.le,
        show sK i = 0 from Pi.single_eq_of_ne hik _, NNReal.coe_zero, mul_zero, add_zero,
        Function.update_self] at hle
  · by_cases hik : i = k
    · subst hik
      have hupd : Function.update sK i a = Pi.single i a :=
        funext fun j => by by_cases hj : j = i <;> simp [sK, hj]
      dsimp only [bestShotGame, toCostGame]
      rw [hsup_single, hupd, bestShot_pi_single,
        show sK i = xBar i by simp only [sK, Pi.single_eq_same], Pi.single_eq_same]
      exact hOpt i a
    · dsimp only [bestShotGame, toCostGame]
      rw [hsup_single, bestShot_update_single_ne hik (xBar k) a,
        show sK i = 0 from Pi.single_eq_of_ne hik _, NNReal.coe_zero, mul_zero, add_zero,
        Function.update_self]
      rcases le_or_gt a (xBar k) with ha | ha
      · rw [max_eq_left ha]
        exact le_add_of_nonneg_right (mul_nonneg (hCost i) a.coe_nonneg)
      · rw [max_eq_right ha.le]
        exact (hFree i hik).trans (hOpt i a)

/-- **Best-shot champion pure Nash equilibrium** ([Varian2004], §3.3, p. 4): when `iStar` has the
largest standalone effort `xBar iStar` and `prob` is nondecreasing on `[0, ∞)`,
`Pi.single iStar (xBar iStar)` is always a pure Nash equilibrium of `R.bestShotGame`. -/
theorem isPureNash_bestShotGame_champion {xBar : ι → ℝ≥0} {iStar : ι}
    (hMono : MonotoneOn R.prob (Set.Ici 0))
    (hVal : ∀ i, 0 ≤ R.val i) (hCost : ∀ i, 0 ≤ R.unitCost i)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i))
    (hMax : ∀ i, xBar i ≤ xBar iStar) :
    R.bestShotGame.IsPureNash (Pi.single iStar (xBar iStar)) := by
  rw [R.isPureNash_bestShotGame_single_iff hMono hVal hCost hOpt]
  intro i _
  have hP : R.prob (xBar i) ≤ R.prob (xBar iStar) :=
    hMono (xBar i).coe_nonneg (xBar iStar).coe_nonneg (hMax i)
  have hc0 : 0 ≤ R.unitCost i * (xBar i : ℝ) := mul_nonneg (hCost i) (xBar i).coe_nonneg
  nlinarith [hVal i]

/-- **Single-contributor support of nonzero best-shot pure Nash equilibria** ([Varian2004], §3.3,
pp. 4–5): every pure Nash equilibrium `x` of `R.bestShotGame` with `bestShot x > 0` concentrates
all effort on a single agent `k`, setting `x = Pi.single k (xBar k)`. -/
theorem exists_eq_single_of_isPureNash_bestShotGame [Nonempty ι] {xBar : ι → ℝ≥0}
    (hConc : StrictConcaveOn ℝ (Set.Ici 0) R.prob)
    (hVal : ∀ i, 0 < R.val i) (hCost : ∀ i, 0 < R.unitCost i)
    (hOpt : ∀ i, IsStandaloneOpt R.prob (R.val i) (R.unitCost i) (xBar i))
    {x : ι → ℝ≥0} (hx : R.bestShotGame.IsPureNash x) (_hpos : 0 < bestShot x) :
    ∃ k, x = Pi.single k (xBar k) := by
  obtain ⟨k, _, hk⟩ := exists_mem_eq_sup univ univ_nonempty x
  have hx_k : x k = bestShot x := hk.symm
  have hzero : ∀ j, j ≠ k → x j = 0 := fun j hjk => by
    by_contra hj_ne
    have hj_pos : 0 < x j := pos_iff_ne_zero.mpr hj_ne
    have hsup_upd : bestShot (Function.update x j 0) = bestShot x := by
      refine le_antisymm (Finset.sup_le fun m _ => ?_) ?_
      · rcases eq_or_ne j m with rfl | hmj
        · simp only [Function.update_self, zero_le]
        · simpa only [Function.update_of_ne hmj.symm] using le_sup (mem_univ m)
      · simpa only [bestShot, Function.update_of_ne (Ne.symm hjk), hx_k] using
          le_sup (f := Function.update x j 0) (mem_univ k)
    have hle := hx j 0
    dsimp only [bestShotGame, toCostGame] at hle
    rw [hsup_upd, Function.update_self, NNReal.coe_zero, mul_zero, add_zero] at hle
    nlinarith [NNReal.coe_pos.mpr hj_pos, hCost j]
  have hk_opt : x k = xBar k := by
    by_contra hne
    have hupd : Function.update x k (xBar k) = Pi.single k (xBar k) :=
      funext fun m => by by_cases hm : m = k <;> simp [hm, hzero m]
    have hle := hx k (xBar k)
    dsimp only [bestShotGame, toCostGame] at hle
    rw [← hx_k, hupd, bestShot_pi_single, Pi.single_eq_same] at hle
    linarith [(hOpt k).strict_lt_of_ne hConc (hVal k) hne]
  refine ⟨k, funext fun j => ?_⟩
  rcases eq_or_ne k j with rfl | hjk
  · simpa only [Pi.single_eq_same] using hk_opt
  · rw [Pi.single_eq_of_ne hjk.symm, hzero j hjk.symm]

end BestShot

/-! ### Tight robust Price of Anarchy for total-effort and best-shot reliability games -/

section PriceOfAnarchy

variable [Fintype ι] [DecidableEq ι]

/-- **Robust coarse-correlated Price of Anarchy** (original) for monotone reliability games whose
aggregator dominates individual efforts (`x i ≤ agg x`) and has least-cost bound
`cMin * agg x ≤ ∑ j, unitCost j * x j` (which holds simultaneously for `totalEffort` and
`bestShot`): every coarse correlated equilibrium `σ` has expected social cost at most
`((∑ i, unitCost i) / cMin) * socialCost x'` for every profile `x'`. -/
theorem expected_socialCost_le_of_isCoarseCorrelatedEquilibrium [Nonempty ι]
    {agg : (ι → ℝ≥0) → ℝ≥0} {cMin : ℝ}
    (hVal : ∀ i, 0 ≤ R.val i) (hMono : MonotoneOn R.prob (Set.Ici 0))
    (hProb_le_one : ∀ z : ℝ≥0, R.prob z ≤ 1)
    (hMin_pos : 0 < cMin) (hMin_le : ∀ i, cMin ≤ R.unitCost i)
    (hAgg_ge : ∀ (s : ι → ℝ≥0) (i : ι), s i ≤ agg s)
    (hAgg_cost : ∀ x' : ι → ℝ≥0, cMin * (agg x' : ℝ) ≤ ∑ j, R.unitCost j * (x' j : ℝ))
    {σ : Convexity.StdSimplex ℝ (ι → ℝ≥0)}
    (hσ : (R.toCostGame agg).IsCoarseCorrelatedEquilibrium σ) (x' : ι → ℝ≥0) :
    σ.weights.sum (fun s w => w * (R.toCostGame agg).socialCost s) ≤
      ((∑ i, R.unitCost i) / cMin) * (R.toCostGame agg).socialCost x' := by
  set X' : ℝ≥0 := agg x'
  have hsum_i : ∀ i : ι,
      σ.weights.sum (fun s w => w * (R.toCostGame agg).cost i s) ≤
        R.val i * (1 - R.prob X') + R.unitCost i * (X' : ℝ) := fun i =>
    calc σ.weights.sum (fun s w => w * (R.toCostGame agg).cost i s)
        ≤ σ.weights.sum (fun s w => w * (R.toCostGame agg).cost i (Function.update s i X')) :=
          hσ i X'
      _ ≤ σ.weights.sum (fun _ w => w * (R.val i * (1 - R.prob X') + R.unitCost i * (X' : ℝ))) := by
          simp only [Finsupp.sum]
          exact sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (by
            have hge : X' ≤ agg (Function.update s i X') := by
              simpa only [Function.update_self] using hAgg_ge (Function.update s i X') i
            have hP := hMono X'.coe_nonneg (agg (Function.update s i X')).coe_nonneg hge
            simp only [toCostGame, Function.update_self]
            nlinarith [hVal i]) (Convexity.StdSimplex.weights_nonneg s)
      _ = R.val i * (1 - R.prob X') + R.unitCost i * (X' : ℝ) := by
          rw [Finsupp.sum, ← sum_mul, show ∑ s ∈ σ.support, σ.weights s = 1 from σ.total, one_mul]
  have hExp : σ.weights.sum (fun s w => w * (R.toCostGame agg).socialCost s) ≤
      (∑ i, R.val i) * (1 - R.prob X') + (∑ i, R.unitCost i) * (X' : ℝ) := by
    calc σ.weights.sum (fun s w => w * (R.toCostGame agg).socialCost s)
        = ∑ i, σ.weights.sum (fun s w => w * (R.toCostGame agg).cost i s) := by
          simp only [Finsupp.sum, CostGame.socialCost, mul_sum]
          exact sum_comm
      _ ≤ ∑ i, (R.val i * (1 - R.prob X') + R.unitCost i * (X' : ℝ)) :=
          sum_le_sum fun i _ => hsum_i i
      _ = _ := by rw [sum_add_distrib, ← sum_mul, ← sum_mul]
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hsum_cost_ge : cMin ≤ ∑ i, R.unitCost i :=
    (hMin_le i₀).trans (single_le_sum (fun j _ => hMin_pos.le.trans (hMin_le j)) (mem_univ i₀))
  have hratio_ge_one : 1 ≤ (∑ i, R.unitCost i) / cMin := (one_le_div hMin_pos).mpr hsum_cost_ge
  have hfail_nonneg : 0 ≤ (∑ i, R.val i) * (1 - R.prob X') :=
    mul_nonneg (sum_nonneg fun i _ => hVal i) (sub_nonneg.mpr (hProb_le_one X'))
  have hcost_scaled : (∑ i, R.unitCost i) * (X' : ℝ) ≤
      ((∑ i, R.unitCost i) / cMin) * ∑ j, R.unitCost j * (x' j : ℝ) :=
    calc (∑ i, R.unitCost i) * (X' : ℝ)
        = ((∑ i, R.unitCost i) / cMin) * (cMin * (X' : ℝ)) := by
            field_simp [hMin_pos.ne']
      _ ≤ ((∑ i, R.unitCost i) / cMin) * ∑ j, R.unitCost j * (x' j : ℝ) :=
          mul_le_mul_of_nonneg_left (hAgg_cost x')
            (div_nonneg (hMin_pos.le.trans hsum_cost_ge) hMin_pos.le)
  have hsoc_x' : (R.toCostGame agg).socialCost x' =
      (∑ i, R.val i) * (1 - R.prob X') + ∑ j, R.unitCost j * (x' j : ℝ) := by
    simp only [CostGame.socialCost, toCostGame, sum_add_distrib, ← sum_mul, X']
  rw [hsoc_x']; nlinarith

/-- **Pure-Nash `|ι|` Price of Anarchy for identical-cost total-effort games** (original): when
every agent has `0 ≤ val i`, `unitCost i = c > 0`, and `prob` is nondecreasing with `prob ≤ 1`,
every pure Nash equilibrium costs at most `(Fintype.card ι : ℝ)` times any profile `x'`. -/
theorem socialCost_totalEffortGame_le_card_mul [Nonempty ι] {c : ℝ}
    (hVal : ∀ i, 0 ≤ R.val i) (hMono : MonotoneOn R.prob (Set.Ici 0))
    (hProb_le_one : ∀ z : ℝ≥0, R.prob z ≤ 1)
    (hc : 0 < c) (hCost_eq : ∀ i, R.unitCost i = c)
    {x : ι → ℝ≥0} (hx : R.totalEffortGame.IsPureNash x) (x' : ι → ℝ≥0) :
    R.totalEffortGame.socialCost x ≤ (Fintype.card ι : ℝ) * R.totalEffortGame.socialCost x' := by
  simpa only [Convexity.StdSimplex.weights_single, Finsupp.sum_single_index, zero_mul, one_mul,
    hCost_eq, sum_const, card_univ, nsmul_eq_mul, mul_div_cancel_right₀ _ hc.ne'] using
    R.expected_socialCost_le_of_isCoarseCorrelatedEquilibrium hVal hMono hProb_le_one hc
      (fun i => (hCost_eq i).ge) (fun s i => single_le_sum (fun _ _ => zero_le) (mem_univ i))
      (fun y => by simp only [NNReal.coe_sum, hCost_eq, mul_sum, le_rfl])
      hx.isCoarseCorrelatedEquilibrium x'

/-- **Pure-Nash `|ι|` Price of Anarchy for identical-cost best-shot games** (original): when every
agent has `0 ≤ val i`, `unitCost i = c > 0`, and `prob` is nondecreasing with `prob ≤ 1`, every pure
Nash equilibrium costs at most `(Fintype.card ι : ℝ)` times any profile `x'`. -/
theorem socialCost_bestShotGame_le_card_mul [Nonempty ι] {c : ℝ}
    (hVal : ∀ i, 0 ≤ R.val i) (hMono : MonotoneOn R.prob (Set.Ici 0))
    (hProb_le_one : ∀ z : ℝ≥0, R.prob z ≤ 1)
    (hc : 0 < c) (hCost_eq : ∀ i, R.unitCost i = c)
    {x : ι → ℝ≥0} (hx : R.bestShotGame.IsPureNash x) (x' : ι → ℝ≥0) :
    R.bestShotGame.socialCost x ≤ (Fintype.card ι : ℝ) * R.bestShotGame.socialCost x' := by
  simpa only [Convexity.StdSimplex.weights_single, Finsupp.sum_single_index, zero_mul, one_mul,
    hCost_eq, sum_const, card_univ, nsmul_eq_mul, mul_div_cancel_right₀ _ hc.ne'] using
    R.expected_socialCost_le_of_isCoarseCorrelatedEquilibrium hVal hMono hProb_le_one hc
      (fun i => (hCost_eq i).ge) (fun s i => le_sup (mem_univ i))
      (fun y => by
        obtain ⟨j, _, hj⟩ := exists_mem_eq_sup univ univ_nonempty y
        rw [hj]
        simp only [hCost_eq]
        exact single_le_sum (fun k _ => mul_nonneg hc.le (y k).coe_nonneg) (mem_univ j))
      hx.isCoarseCorrelatedEquilibrium x'

end PriceOfAnarchy

end SystemReliabilitySpec

/-- **Asymptotic tightness of the `n` Price-of-Anarchy bound** (original): for every `n ≥ 1` and
every ratio `β < n`, there exists an `n`-agent identical-valuation, identical-cost
`SystemReliabilitySpec` with concave, monotone, `[0, 1]`-valued reliability whose unique pure Nash
equilibrium `0` strictly exceeds `β` times the social cost of `Pi.single ⟨0, hn⟩ 1`. -/
theorem exists_totalEffortGame_socialCost_gt_mul {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : β < n) :
    ∃ (R : SystemReliabilitySpec (Fin n)) (x x' : Fin n → ℝ≥0),
      (∀ i, 0 < R.val i) ∧ (∀ i, R.unitCost i = R.unitCost ⟨0, hn⟩) ∧ 0 < R.unitCost ⟨0, hn⟩ ∧
      ConcaveOn ℝ (Set.Ici 0) R.prob ∧ MonotoneOn R.prob (Set.Ici 0) ∧
      (∀ z : ℝ≥0, R.prob z ≤ 1) ∧
      R.totalEffortGame.IsPureNash x ∧ (∀ y, R.totalEffortGame.IsPureNash y → y = x) ∧
      β * R.totalEffortGame.socialCost x' < R.totalEffortGame.socialCost x := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set ε : ℝ := if β ≤ 0 then 1 else ((n : ℝ) - β) / (2 * β)
  have hε : 0 < ε := by
    by_cases h0 : β ≤ 0
    · simp only [ε, h0, ↓reduceIte, zero_lt_one]
    · simp only [ε, h0, ↓reduceIte]
      exact div_pos (sub_pos.mpr hβ) (by linarith)
  let R : SystemReliabilitySpec (Fin n) :=
    { val := fun _ => 1, unitCost := fun _ => 1 + ε, prob := fun z => min z 1 }
  have htot0 : totalEffort (0 : Fin n → ℝ≥0) = 0 := by simp [totalEffort]
  have hNash0 : R.totalEffortGame.IsPureNash 0 := fun i a => by
    have h2 : totalEffort (Function.update (0 : Fin n → ℝ≥0) i a) = a := by
      simp [SystemReliabilitySpec.totalEffort_update_aux]
    simp only [SystemReliabilitySpec.totalEffortGame, SystemReliabilitySpec.toCostGame, R, htot0,
      h2, Pi.zero_apply, NNReal.coe_zero, min_eq_left zero_le_one, sub_zero, mul_zero, add_zero,
      Function.update_self, one_mul]
    nlinarith [min_le_left (a : ℝ) 1, a.coe_nonneg]
  have hUnique : ∀ y : Fin n → ℝ≥0, R.totalEffortGame.IsPureNash y → y = 0 := fun y hy =>
    funext fun i => by
      by_contra hyi
      have hyi_pos : 0 < (y i : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hyi)
      have hle := hy i 0
      simp only [SystemReliabilitySpec.totalEffortGame, SystemReliabilitySpec.toCostGame, R,
        SystemReliabilitySpec.totalEffort_eq_erase_add y i, NNReal.coe_add,
        SystemReliabilitySpec.totalEffort_update_aux, add_zero, one_mul, Function.update_self,
        NNReal.coe_zero, mul_zero] at hle
      set Xm : ℝ := ((∑ j ∈ univ.erase i, y j : ℝ≥0) : ℝ)
      have hgap : min (Xm + (y i : ℝ)) 1 - min Xm 1 ≤ (y i : ℝ) := by
        rcases le_total Xm 1 with hX | hX
        · rw [min_eq_left hX]; linarith [min_le_left (Xm + (y i : ℝ)) 1]
        · rw [min_eq_right hX, min_eq_right (by linarith)]; linarith
      nlinarith
  let x' : Fin n → ℝ≥0 := Pi.single ⟨0, hn⟩ 1
  have hsoc0 : R.totalEffortGame.socialCost 0 = (n : ℝ) := by
    simp [CostGame.socialCost, SystemReliabilitySpec.totalEffortGame,
      SystemReliabilitySpec.toCostGame, R]
  have hsoc' : R.totalEffortGame.socialCost x' = 1 + ε := by
    simpa only [CostGame.socialCost, SystemReliabilitySpec.totalEffortGame,
      SystemReliabilitySpec.toCostGame, totalEffort, R, x',
      SystemReliabilitySpec.sum_pi_single_nnreal, NNReal.coe_one, min_self, sub_self, mul_zero,
      zero_add, mul_one] using
      SystemReliabilitySpec.sum_mul_pi_single (fun _ : Fin n => 1 + ε) ⟨0, hn⟩ (1 : ℝ≥0)
  refine ⟨R, 0, x', fun _ => zero_lt_one, fun _ => rfl, by linarith,
    (concaveOn_id (convex_Ici 0)).inf (concaveOn_const 1 (convex_Ici 0)),
    fun _ _ _ _ hab => min_le_min_right 1 hab, fun _ => min_le_right _ _, hNash0, hUnique, ?_⟩
  rw [hsoc0, hsoc']
  by_cases h0 : β ≤ 0
  · linarith [mul_nonpos_of_nonpos_of_nonneg h0 (by linarith : 0 ≤ 1 + ε)]
  · have hb : 0 < β := lt_of_not_ge h0
    simp only [ε, h0, ↓reduceIte]
    have : β * (1 + ((n : ℝ) - β) / (2 * β)) = (β + (n : ℝ)) / 2 := by
      field_simp [hb.ne']; ring
    linarith

end Cslib.GameTheory
