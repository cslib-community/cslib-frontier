/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF.Expect
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.ProbabilityMassFunction.Monad
import CslibFrontier.Foundations.Data.Fintype.UpdateInduction
import CslibFrontier.Probability.PMF.ToMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic.Linarith

/-!
# Randomized facility-location mechanisms on metric spaces

A *randomized facility-location mechanism* ([ProcacciaTennenholtz2013] §3, p. 18:7;
[AlonFeldmanProcacciaTennenholtz2010] §2, arXiv:0907.2049v1 p. 4; see also [SchummerVohra2007])
collects reported locations `x : ι → G` from finitely many agents on a `PseudoMetricSpace G`
(slightly generalizing the metric-space and graph-distance settings in those papers) and outputs
a probability measure `M x : ProbabilityMeasure G` for the facility location. Agent `i` at true
location `x i` incurs distance cost `dist (x i) y` when the facility is placed at `y`.

## Design choices

* **Extended-real expected costs as the primary semantics.** A general `ProbabilityMeasure G` on an
  unbounded metric space such as `ℝ` need not have a finite first moment. We define
  `expectedECost μ a = ∫⁻ y, edist a y ∂(μ : Measure G)` in `ℝ≥0∞` (`lintegral`), which is finite if
  and only if `y ↦ dist a y` is integrable (`expectedECost_lt_top_iff_integrable`), and equals
  `⊤` when the integral diverges (preventing heavy-tailed distributions from silently evaluating to
  zero under Bochner integration). The real-valued Bochner expectation `expectedCost` and
  `expectedSocialCost` agree with `expectedECost` and `expectedSocialECost` whenever `HasFiniteCost`
  holds (in particular, for every deterministic mechanism, every finitely supported `PMF` mechanism,
  and every mechanism on a `CompactSpace`).
* **Direct-revelation incentive notions.** Strategyproofness (`Mechanism.IsStrategyProof`) says no
  single agent can strictly decrease its expected cost by misreporting. Following
  [ProcacciaTennenholtz2013] (§3, p. 18:7) and [AlonFeldmanProcacciaTennenholtz2010] (§2,
  arXiv:0907.2049v1 p. 4), we provide two coalitional notions mirroring
  `Cslib.GameTheory.CostGame.IsStrongEquilibrium` and `Cslib.GameTheory.CostGame.IsStrongNash`:
  `Mechanism.IsWeakGroupStrategyProof` (no nonempty coalition can make every member strictly better
  off—what PT and AFPT call "group strategyproofness") and `Mechanism.IsGroupStrategyProof` (the
  stronger variant noted in passing in PT §3, p. 18:7, where no coalition can make every member
  weakly better off and at least one strictly better off). Obvious strategyproofness requires
  extensive-form game trees and is out of scope here.
* **Bridges for deterministic and `PMF` mechanisms.** `Mechanism.deterministic` embeds
  deterministic rules `(ι → G) → G` via `Measure.dirac`, and `Mechanism.ofPMF` embeds discrete
  randomized rules `(ι → G) → PMF G` via `PMF.toMeasure`, with exact reduction lemmas to `dist`,
  `tsum`, and finite sums over `Finset`s or mapped finite distributions.

## Main definitions

* `Cslib.GameTheory.FacilityLocation.socialCost`, `Cslib.GameTheory.FacilityLocation.socialECost`:
  total agent distance `∑ i, dist (x i) y` (and `edist` version) at a facility location `y`.
* `Cslib.GameTheory.FacilityLocation.optSocialCost`,
  `Cslib.GameTheory.FacilityLocation.optSocialECost`: the optimal social cost `⨅ y, socialCost x y`
  (and `edist` version).
* `Cslib.GameTheory.FacilityLocation.IsOptimal`: `y` minimizes `socialCost x`.
* `Cslib.GameTheory.FacilityLocation.Mechanism`: randomized mechanism
  `(ι → G) → ProbabilityMeasure G`.
* `Cslib.GameTheory.FacilityLocation.expectedECost`,
  `Cslib.GameTheory.FacilityLocation.expectedCost`: expected cost of a distribution for a point.
* `Cslib.GameTheory.FacilityLocation.HasFiniteCost`: all point-distance functions are integrable.
* `Cslib.GameTheory.FacilityLocation.expectedSocialECost`,
  `Cslib.GameTheory.FacilityLocation.expectedSocialCost`: expected total agent cost.
* `Cslib.GameTheory.FacilityLocation.Mechanism.IsStrategyProof`: unilateral truthfulness.
* `Cslib.GameTheory.FacilityLocation.Mechanism.IsWeakGroupStrategyProof`,
  `Cslib.GameTheory.FacilityLocation.Mechanism.IsGroupStrategyProof`: coalitional truthfulness.
* `Cslib.GameTheory.FacilityLocation.Mechanism.HasApproxRatio`: worst-case approximation factor
  against `optSocialECost`.
* `Cslib.GameTheory.FacilityLocation.Mechanism.deterministic`,
  `Cslib.GameTheory.FacilityLocation.Mechanism.ofPMF`: embeddings of deterministic and `PMF` rules.

## Main results

* `Cslib.GameTheory.FacilityLocation.expectedECost_lt_top_iff_integrable`,
  `Cslib.GameTheory.FacilityLocation.expectedECost_eq_ofReal_expectedCost`: equivalence between
  finite `expectedECost` and Bochner integrability of `dist`.
* `Cslib.GameTheory.FacilityLocation.expectedSocialECost_eq_lintegral`,
  `Cslib.GameTheory.FacilityLocation.optSocialECost_le_expectedSocialECost`: linearity of expected
  social cost and lower bound by `optSocialECost`.
* `Cslib.GameTheory.FacilityLocation.Mechanism.isStrategyProof_iff_expectedCost_le`,
  `Cslib.GameTheory.FacilityLocation.Mechanism.hasApproxRatio_iff_expectedSocialCost_le`:
  real-valued characterizations under `HasFiniteCost`.
* `Cslib.GameTheory.FacilityLocation.Mechanism.IsGroupStrategyProof.isWeakGroupStrategyProof`,
  `Cslib.GameTheory.FacilityLocation.Mechanism.IsWeakGroupStrategyProof.isStrategyProof`:
  hierarchy of truthfulness notions.
* `Cslib.GameTheory.FacilityLocation.Mechanism.HasApproxRatio.one_le_of_pos`,
  `Cslib.GameTheory.FacilityLocation.Mechanism.HasApproxRatio.one_le`: any approximation ratio
  on a profile with positive optimal cost (or on any nontrivial metric space with at least two
  agents) is at least `1`.
* `Cslib.GameTheory.FacilityLocation.Mechanism.isStrategyProof_deterministic_iff`,
  `Cslib.GameTheory.FacilityLocation.Mechanism.hasApproxRatio_deterministic_iff`: deterministic
  reductions to metric distances.
* `Cslib.GameTheory.FacilityLocation.expectedECost_ofPMF`,
  `Cslib.GameTheory.FacilityLocation.expectedCost_ofPMF_map_fintype`: `PMF` evaluation lemmas.
* `Cslib.GameTheory.FacilityLocation.unanimous_of_surjective_isStrategyProof`: every deterministic,
  surjective, strategyproof mechanism on a metric space is unanimous.

## References

* [A. D. Procaccia and M. Tennenholtz, *Approximate Mechanism Design without
  Money*][ProcacciaTennenholtz2013]
* [J. Schummer and R. V. Vohra, *Mechanism Design without Money*][SchummerVohra2007]
-/

public section

namespace Cslib.GameTheory.FacilityLocation

open MeasureTheory Finset
open scoped BigOperators ENNReal

/-! ### Deterministic social cost and optimality -/

section SocialCost

variable {ι G : Type*} [PseudoMetricSpace G] [Fintype ι]

/-- The **social cost** of placing a facility at `y` for agent profile `x`: `∑ i, dist (x i) y`. -/
@[expose] def socialCost (x : ι → G) (y : G) : ℝ :=
  ∑ i, dist (x i) y

/-- The extended nonnegative **social cost** `∑ i, edist (x i) y` of placing a facility at `y`. -/
@[expose] noncomputable def socialECost (x : ι → G) (y : G) : ℝ≥0∞ :=
  ∑ i, edist (x i) y

/-- The **optimal social cost** `⨅ y, socialCost x y` on agent profile `x`. -/
@[expose] noncomputable def optSocialCost (x : ι → G) : ℝ :=
  ⨅ y : G, socialCost x y

/-- The optimal extended nonnegative social cost `⨅ y, socialECost x y` on agent profile `x`. -/
@[expose] noncomputable def optSocialECost (x : ι → G) : ℝ≥0∞ :=
  ⨅ y : G, socialECost x y

/-- A location `y` is **optimal** for profile `x` if it minimizes `socialCost x` over `G`. -/
@[expose] def IsOptimal (x : ι → G) (y : G) : Prop :=
  ∀ z : G, socialCost x y ≤ socialCost x z

/-- The deterministic social cost `socialCost x y` is nonnegative. -/
theorem socialCost_nonneg (x : ι → G) (y : G) : 0 ≤ socialCost x y :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

/-- The extended social cost equals `ENNReal.ofReal` of the real-valued social cost. -/
theorem socialECost_eq_ofReal_socialCost (x : ι → G) (y : G) :
    socialECost x y = ENNReal.ofReal (socialCost x y) := by
  simp only [socialECost, socialCost, edist_dist]
  exact (ENNReal.ofReal_sum_of_nonneg fun _ _ => dist_nonneg).symm

/-- The range of `socialCost x` is bounded below by `0`. -/
theorem bddBelow_range_socialCost (x : ι → G) : BddBelow (Set.range (socialCost x)) :=
  ⟨0, by rintro _ ⟨y, rfl⟩; exact socialCost_nonneg x y⟩

/-- The optimal social cost `optSocialCost x` is nonnegative. -/
theorem optSocialCost_nonneg (x : ι → G) : 0 ≤ optSocialCost x := by
  rcases isEmpty_or_nonempty G with hG | hG
  · rw [optSocialCost, Real.iInf_of_isEmpty]
  · exact le_ciInf fun y => socialCost_nonneg x y

/-- The optimal social cost is at most the social cost at any location `y`. -/
theorem optSocialCost_le_socialCost (x : ι → G) (y : G) :
    optSocialCost x ≤ socialCost x y :=
  ciInf_le (bddBelow_range_socialCost x) y

/-- A real number `c` bounds `optSocialCost x` below iff it bounds `socialCost x y` for all `y`. -/
theorem le_optSocialCost_iff [Nonempty G] {x : ι → G} {c : ℝ} :
    c ≤ optSocialCost x ↔ ∀ y : G, c ≤ socialCost x y :=
  le_ciInf_iff (bddBelow_range_socialCost x)

/-- Any uniform lower bound `c ≤ α * socialCost x y` with `0 ≤ α` transfers to
`α * optSocialCost x`. -/
theorem le_mul_optSocialCost [Nonempty G] {x : ι → G} {α c : ℝ} (hα : 0 ≤ α)
    (h : ∀ y : G, c ≤ α * socialCost x y) : c ≤ α * optSocialCost x := by
  rcases hα.eq_or_lt with rfl | hpos
  · obtain ⟨y⟩ := ‹Nonempty G›
    simpa only [zero_mul] using h y
  · rw [mul_comm, ← div_le_iff₀ hpos, le_optSocialCost_iff]
    exact fun y => by rw [div_le_iff₀ hpos, mul_comm]; exact h y

/-- The optimal extended social cost is at most the extended social cost at any location `y`. -/
theorem optSocialECost_le_socialECost (x : ι → G) (y : G) :
    optSocialECost x ≤ socialECost x y :=
  iInf_le (socialECost x) y

/-- On a nonempty pseudometric space, the optimal extended social cost is finite. -/
theorem optSocialECost_lt_top [Nonempty G] (x : ι → G) :
    optSocialECost x < ⊤ := by
  obtain ⟨y⟩ := ‹Nonempty G›
  exact (optSocialECost_le_socialECost x y).trans_lt
    (by rw [socialECost_eq_ofReal_socialCost]; exact ENNReal.ofReal_lt_top)

/-- On a nonempty space, `optSocialECost x` equals `ENNReal.ofReal (optSocialCost x)`. -/
theorem optSocialECost_eq_ofReal_optSocialCost [Nonempty G] (x : ι → G) :
    optSocialECost x = ENNReal.ofReal (optSocialCost x) := by
  refine le_antisymm ?_ (le_iInf fun y => ?_)
  · rw [← ENNReal.toReal_le_toReal (optSocialECost_lt_top x).ne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (optSocialCost_nonneg x)]
    exact le_ciInf fun y => ENNReal.toReal_le_of_le_ofReal (socialCost_nonneg x y)
      (socialECost_eq_ofReal_socialCost x y ▸ optSocialECost_le_socialECost x y)
  · rw [socialECost_eq_ofReal_socialCost]
    exact ENNReal.ofReal_le_ofReal (optSocialCost_le_socialCost x y)

/-- A location `y` is optimal for `x` iff its social cost equals `optSocialCost x`. -/
theorem isOptimal_iff_socialCost_eq_optSocialCost [Nonempty G] {x : ι → G} {y : G} :
    IsOptimal x y ↔ socialCost x y = optSocialCost x :=
  ⟨fun h => le_antisymm (le_ciInf h) (optSocialCost_le_socialCost x y),
   fun h z => h ▸ optSocialCost_le_socialCost x z⟩

/-- An optimal location attains the optimal social cost `optSocialCost x`. -/
theorem IsOptimal.socialCost_eq_optSocialCost [Nonempty G] {x : ι → G} {y : G}
    (h : IsOptimal x y) : socialCost x y = optSocialCost x :=
  isOptimal_iff_socialCost_eq_optSocialCost.1 h

end SocialCost

/-! ### Randomized mechanisms and expected costs -/

/-- A **randomized facility-location mechanism** maps each agent location profile `x : ι → G` to a
probability measure over facility locations `G` ([ProcacciaTennenholtz2013]). -/
abbrev Mechanism (ι G : Type*) [MeasurableSpace G] := (ι → G) → ProbabilityMeasure G

section ExpectedCost

section Continuous

variable {G : Type*} [PseudoMetricSpace G]

private theorem continuous_dist_left (a : G) : Continuous fun y : G => dist a y :=
  continuous_const.dist continuous_id

private theorem continuous_edist_left (a : G) : Continuous fun y : G => edist a y :=
  continuous_const.edist continuous_id

end Continuous

variable {ι G : Type*} [PseudoMetricSpace G] [MeasurableSpace G]

/-- The extended nonnegative expected distance cost `∫⁻ y, edist loc y ∂μ` experienced by an agent
at `loc` under facility distribution `μ`. -/
@[expose] noncomputable def expectedECost (μ : ProbabilityMeasure G) (loc : G) : ℝ≥0∞ :=
  ∫⁻ y, edist loc y ∂(μ : Measure G)

/-- The real-valued Bochner expected distance cost `∫ y, dist loc y ∂μ` experienced by an agent at
`loc` under facility distribution `μ`. Evaluates to `0` when `y ↦ dist loc y` is not integrable. -/
@[expose] noncomputable def expectedCost (μ : ProbabilityMeasure G) (loc : G) : ℝ :=
  ∫ y, dist loc y ∂(μ : Measure G)

/-- A probability measure on `G` has **finite expected distance cost** if `y ↦ dist a y` is
integrable for every `a : G`. By the triangle inequality (`hasFiniteCost_of_exists_integrable`),
integrability at a single reference point implies integrability everywhere. -/
@[expose] def HasFiniteCost (μ : ProbabilityMeasure G) : Prop :=
  ∀ a : G, Integrable (fun y => dist a y) (μ : Measure G)

/-- The extended nonnegative expected social cost `∑ i, expectedECost μ (x i)`. -/
@[expose] noncomputable def expectedSocialECost [Fintype ι] (μ : ProbabilityMeasure G)
    (x : ι → G) : ℝ≥0∞ :=
  ∑ i, expectedECost μ (x i)

/-- The real-valued expected social cost `∑ i, expectedCost μ (x i)`. -/
@[expose] noncomputable def expectedSocialCost [Fintype ι] (μ : ProbabilityMeasure G)
    (x : ι → G) : ℝ :=
  ∑ i, expectedCost μ (x i)

/-- The real-valued expected distance cost `expectedCost μ loc` is nonnegative. -/
theorem expectedCost_nonneg (μ : ProbabilityMeasure G) (loc : G) : 0 ≤ expectedCost μ loc :=
  integral_nonneg fun _ => dist_nonneg

/-- The real-valued expected social cost `expectedSocialCost μ x` is nonnegative. -/
theorem expectedSocialCost_nonneg [Fintype ι] (μ : ProbabilityMeasure G) (x : ι → G) :
    0 ≤ expectedSocialCost μ x :=
  Finset.sum_nonneg fun _ _ => expectedCost_nonneg μ (x _)

/-- When `y ↦ dist a y` is integrable under `μ`, `expectedECost μ a` agrees with
`ENNReal.ofReal (expectedCost μ a)`. -/
theorem expectedECost_eq_ofReal_expectedCost {μ : ProbabilityMeasure G} {a : G}
    (h : Integrable (fun y => dist a y) (μ : Measure G)) :
    expectedECost μ a = ENNReal.ofReal (expectedCost μ a) := by
  rw [expectedCost,
    ofReal_integral_eq_lintegral_ofReal h (Filter.Eventually.of_forall fun _ => dist_nonneg)]
  exact lintegral_congr fun y => edist_dist a y

/-- When `y ↦ dist a y` is integrable under both `μ` and `ν`, `expectedECost` and `expectedCost`
have the same weak ordering. -/
theorem expectedECost_le_iff_expectedCost_le {μ ν : ProbabilityMeasure G} {a : G}
    (hμ : Integrable (fun y => dist a y) (μ : Measure G))
    (hν : Integrable (fun y => dist a y) (ν : Measure G)) :
    expectedECost μ a ≤ expectedECost ν a ↔ expectedCost μ a ≤ expectedCost ν a := by
  rw [expectedECost_eq_ofReal_expectedCost hμ, expectedECost_eq_ofReal_expectedCost hν,
    ENNReal.ofReal_le_ofReal_iff (expectedCost_nonneg ν a)]

/-- When `y ↦ dist a y` is integrable under both `μ` and `ν`, `expectedECost` and `expectedCost`
have the same strict ordering. -/
theorem expectedECost_lt_iff_expectedCost_lt {μ ν : ProbabilityMeasure G} {a : G}
    (hμ : Integrable (fun y => dist a y) (μ : Measure G))
    (hν : Integrable (fun y => dist a y) (ν : Measure G)) :
    expectedECost μ a < expectedECost ν a ↔ expectedCost μ a < expectedCost ν a := by
  rw [← not_le, expectedECost_le_iff_expectedCost_le hν hμ, not_le]

/-- Linearity of `expectedSocialCost`: when every agent's distance function is integrable under `μ`,
the sum of expected costs equals the Bochner integral of `socialCost x`. -/
theorem expectedSocialCost_eq_integral [Fintype ι] {μ : ProbabilityMeasure G} {x : ι → G}
    (h : ∀ i, Integrable (fun y => dist (x i) y) (μ : Measure G)) :
    expectedSocialCost μ x = ∫ y, socialCost x y ∂(μ : Measure G) := by
  simp only [expectedSocialCost, expectedCost, socialCost]
  exact (integral_finsetSum Finset.univ fun i _ => h i).symm

/-- When every agent's distance function is integrable under `μ`, `expectedSocialECost μ x` equals
`ENNReal.ofReal (expectedSocialCost μ x)`. -/
theorem expectedSocialECost_eq_ofReal_expectedSocialCost [Fintype ι] {μ : ProbabilityMeasure G}
    {x : ι → G} (h : ∀ i, Integrable (fun y => dist (x i) y) (μ : Measure G)) :
    expectedSocialECost μ x = ENNReal.ofReal (expectedSocialCost μ x) := by
  simp only [expectedSocialECost, expectedSocialCost]
  rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => expectedCost_nonneg μ _]
  exact Finset.sum_congr rfl fun i _ => expectedECost_eq_ofReal_expectedCost (h i)

section Measurable

variable [OpensMeasurableSpace G]

private theorem measurable_edist_left (a : G) : Measurable fun y : G => edist a y :=
  (continuous_edist_left a).measurable

private theorem stronglyMeasurable_dist_left (a : G) : StronglyMeasurable fun y : G => dist a y :=
  (continuous_dist_left a).stronglyMeasurable

/-- Integrability of distance from a single reference point `b` gives `HasFiniteCost μ`. -/
theorem hasFiniteCost_of_exists_integrable {μ : ProbabilityMeasure G}
    (h : ∃ b : G, Integrable (fun y => dist b y) (μ : Measure G)) : HasFiniteCost μ := by
  obtain ⟨b, hb⟩ := h
  refine fun a => ((integrable_const (dist a b)).add hb).mono'
    (stronglyMeasurable_dist_left a).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
  exact dist_triangle a b y

/-- On a compact metric space, every probability measure has finite expected distance cost. -/
theorem hasFiniteCost_of_compactSpace [CompactSpace G] (μ : ProbabilityMeasure G) :
    HasFiniteCost μ :=
  fun a => (continuous_dist_left a).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- `expectedECost μ a < ⊤` holds if and only if `y ↦ dist a y` is integrable under `μ`. -/
theorem expectedECost_lt_top_iff_integrable (μ : ProbabilityMeasure G) (a : G) :
    expectedECost μ a < ⊤ ↔ Integrable (fun y => dist a y) (μ : Measure G) := by
  have heq : expectedECost μ a = ∫⁻ y, ‖dist a y‖ₑ ∂(μ : Measure G) :=
    lintegral_congr fun y => by
      rw [Real.eNorm_eq_ofReal_abs, abs_of_nonneg dist_nonneg, edist_dist]
  rw [heq]
  exact ⟨fun h => ⟨(stronglyMeasurable_dist_left a).aestronglyMeasurable, h⟩,
    fun h => h.hasFiniteIntegral⟩

/-- Under `HasFiniteCost μ`, the extended expected cost from any location `a` is finite. -/
theorem HasFiniteCost.expectedECost_lt_top {μ : ProbabilityMeasure G} (h : HasFiniteCost μ)
    (a : G) : expectedECost μ a < ⊤ :=
  (expectedECost_lt_top_iff_integrable μ a).2 (h a)

/-- Under `HasFiniteCost μ`, the extended expected social cost of any profile `x` is finite. -/
theorem HasFiniteCost.expectedSocialECost_lt_top [Fintype ι] {μ : ProbabilityMeasure G}
    (h : HasFiniteCost μ) (x : ι → G) : expectedSocialECost μ x < ⊤ :=
  ENNReal.sum_lt_top.2 fun i _ => h.expectedECost_lt_top (x i)

/-- The Bochner expected cost equals `(expectedECost μ a).toReal` (returning `0` when the extended
integral is `⊤`). -/
theorem expectedCost_eq_toReal_expectedECost (μ : ProbabilityMeasure G) (a : G) :
    expectedCost μ a = (expectedECost μ a).toReal := by
  rw [expectedCost, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun _ => dist_nonneg)
    (stronglyMeasurable_dist_left a).aestronglyMeasurable]
  exact congrArg ENNReal.toReal (lintegral_congr fun y => (edist_dist a y).symm)

/-- Linearity of `expectedSocialECost`: the sum of extended expected costs equals
`∫⁻ y, socialECost x y ∂μ`. -/
theorem expectedSocialECost_eq_lintegral [Fintype ι] (μ : ProbabilityMeasure G) (x : ι → G) :
    expectedSocialECost μ x = ∫⁻ y, socialECost x y ∂(μ : Measure G) := by
  simp only [expectedSocialECost, expectedECost, socialECost]
  exact (lintegral_finsetSum Finset.univ fun i _ => measurable_edist_left (x i)).symm

/-- Every distribution `μ` has extended expected social cost at least `optSocialECost x`. -/
theorem optSocialECost_le_expectedSocialECost [Fintype ι] (μ : ProbabilityMeasure G)
    (x : ι → G) : optSocialECost x ≤ expectedSocialECost μ x := by
  rw [expectedSocialECost_eq_lintegral]
  calc optSocialECost x = ∫⁻ _, optSocialECost x ∂(μ : Measure G) := by simp
    _ ≤ ∫⁻ y, socialECost x y ∂(μ : Measure G) :=
      lintegral_mono fun y => optSocialECost_le_socialECost x y

/-- On a nonempty space, `optSocialCost x ≤ expectedSocialCost μ x` when each agent's distance
function is integrable under `μ`. -/
theorem optSocialCost_le_expectedSocialCost [Fintype ι] [Nonempty G] {μ : ProbabilityMeasure G}
    {x : ι → G} (h : ∀ i, Integrable (fun y => dist (x i) y) (μ : Measure G)) :
    optSocialCost x ≤ expectedSocialCost μ x := by
  have hle := optSocialECost_le_expectedSocialECost μ x
  rw [optSocialECost_eq_ofReal_optSocialCost,
    expectedSocialECost_eq_ofReal_expectedSocialCost h] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (expectedSocialCost_nonneg μ x)).1 hle

end Measurable

end ExpectedCost

/-! ### Strategyproofness and approximation ratio -/

namespace Mechanism

section Properties

variable {ι G : Type*} [PseudoMetricSpace G] [MeasurableSpace G]

/-- A randomized facility-location mechanism `M` is **strategyproof** if no agent `i` can strictly
reduce its expected distance to the facility by misreporting a location `z` instead of its true
location `x i` ([ProcacciaTennenholtz2013] §3, p. 18:7;
[AlonFeldmanProcacciaTennenholtz2010] §2, arXiv:0907.2049v1 p. 4). -/
@[expose] def IsStrategyProof [DecidableEq ι] (M : Mechanism ι G) : Prop :=
  ∀ (x : ι → G) (i : ι) (z : G),
    expectedECost (M x) (x i) ≤ expectedECost (M (Function.update x i z)) (x i)

/-- A randomized mechanism `M` is **weakly group strategyproof** if no nonempty coalition `A` can
jointly misreport so that every member of `A` strictly decreases its expected cost. This is what
[ProcacciaTennenholtz2013] (§3, p. 18:7) and [AlonFeldmanProcacciaTennenholtz2010] (§2,
arXiv:0907.2049v1 p. 4) call "group strategyproofness". -/
@[expose] def IsWeakGroupStrategyProof [DecidableEq ι] (M : Mechanism ι G) : Prop :=
  ∀ (x z : ι → G) (A : Finset ι), A.Nonempty →
    ∃ i ∈ A, expectedECost (M x) (x i) ≤ expectedECost (M (A.piecewise z x)) (x i)

/-- A randomized mechanism `M` is **(strongly) group strategyproof** if no coalition `A` can
jointly misreport so that no member of `A` increases its expected cost and at least one member
strictly decreases its expected cost (the stronger variant noted in passing in
[ProcacciaTennenholtz2013] §3, p. 18:7). -/
@[expose] def IsGroupStrategyProof [DecidableEq ι] (M : Mechanism ι G) : Prop :=
  ∀ (x z : ι → G) (A : Finset ι),
    ¬ ((∀ i ∈ A, expectedECost (M (A.piecewise z x)) (x i) ≤ expectedECost (M x) (x i)) ∧
      ∃ i ∈ A, expectedECost (M (A.piecewise z x)) (x i) < expectedECost (M x) (x i))

/-- A randomized mechanism `M` has **approximation ratio `α`** (for expected social cost) if on
every profile `x`, its expected social cost is at most `α * optSocialECost x`
([ProcacciaTennenholtz2013] §3, p. 18:7; [AlonFeldmanProcacciaTennenholtz2010] §2,
arXiv:0907.2049v1 p. 4). -/
@[expose] def HasApproxRatio [Fintype ι] (M : Mechanism ι G) (α : ℝ) : Prop :=
  ∀ x : ι → G, expectedSocialECost (M x) x ≤ ENNReal.ofReal α * optSocialECost x

/-- Characterize strategyproofness using pairs of profiles `x, y` that agree outside a single
agent `i`. -/
theorem isStrategyProof_iff [DecidableEq ι] {M : Mechanism ι G} :
    M.IsStrategyProof ↔ ∀ (x y : ι → G) (i : ι), (∀ j, j ≠ i → x j = y j) →
      expectedECost (M x) (x i) ≤ expectedECost (M y) (x i) := by
  refine ⟨fun h x y i hxy => ?_, fun h x i z =>
    h x (Function.update x i z) i fun j hj => (Function.update_of_ne hj _ _).symm⟩
  rw [show y = Function.update x i (y i) from funext fun j => by
    by_cases hj : j = i <;> simp [Function.update, hj, hxy]]
  exact h x i (y i)

/-- Weak group strategyproofness stated in negated form: no nonempty coalition `A` can deviate so
that every member strictly lowers its expected cost. -/
theorem isWeakGroupStrategyProof_iff_not_forall_lt [DecidableEq ι] {M : Mechanism ι G} :
    M.IsWeakGroupStrategyProof ↔ ∀ (x z : ι → G) (A : Finset ι),
      ¬ (A.Nonempty ∧
        ∀ i ∈ A, expectedECost (M (A.piecewise z x)) (x i) < expectedECost (M x) (x i)) := by
  refine ⟨fun h x z A ⟨hA, hlt⟩ => ?_, fun h x z A hA => ?_⟩
  · obtain ⟨i, hi, hle⟩ := h x z A hA
    exact (hlt i hi).not_ge hle
  · by_contra! hne
    exact h x z A ⟨hA, hne⟩

/-- Strong group strategyproofness restated as an implication: any coalitional deviation leaving no
member of `A` strictly worse off must keep every member's expected cost unchanged. -/
theorem isGroupStrategyProof_iff_forall_eq [DecidableEq ι] {M : Mechanism ι G} :
    M.IsGroupStrategyProof ↔ ∀ (x z : ι → G) (A : Finset ι),
      (∀ i ∈ A, expectedECost (M (A.piecewise z x)) (x i) ≤ expectedECost (M x) (x i)) →
      ∀ i ∈ A, expectedECost (M (A.piecewise z x)) (x i) = expectedECost (M x) (x i) := by
  refine ⟨fun h x z A hle i hi => le_antisymm (hle i hi) ?_,
    fun h x z A ⟨hle, i, hi, hlt⟩ => hlt.ne (h x z A hle i hi)⟩
  by_contra! hlt
  exact h x z A ⟨hle, i, hi, hlt⟩

/-- Strong group strategyproofness implies weak group strategyproofness. -/
theorem IsGroupStrategyProof.isWeakGroupStrategyProof [DecidableEq ι] {M : Mechanism ι G}
    (h : M.IsGroupStrategyProof) : M.IsWeakGroupStrategyProof := by
  rintro x z A ⟨i, hi⟩
  by_contra! hne
  exact h x z A ⟨fun j hj => (hne j hj).le, i, hi, hne i hi⟩

/-- Weak group strategyproofness implies unilateral strategyproofness (via singleton coalitions). -/
theorem IsWeakGroupStrategyProof.isStrategyProof [DecidableEq ι] {M : Mechanism ι G}
    (h : M.IsWeakGroupStrategyProof) : M.IsStrategyProof := by
  intro x i z
  obtain ⟨j, hj, hle⟩ := h x (Function.const ι z) {i} (Finset.singleton_nonempty i)
  simpa only [Finset.mem_singleton.1 hj, Finset.piecewise_singleton, Function.const_apply] using hle

/-- Strong group strategyproofness implies unilateral strategyproofness. -/
theorem IsGroupStrategyProof.isStrategyProof [DecidableEq ι] {M : Mechanism ι G}
    (h : M.IsGroupStrategyProof) : M.IsStrategyProof :=
  h.isWeakGroupStrategyProof.isStrategyProof

/-- Approximation ratio is upward-closed: `M.HasApproxRatio α` and `α ≤ β` imply
`M.HasApproxRatio β`. -/
theorem HasApproxRatio.mono [Fintype ι] {M : Mechanism ι G} {α β : ℝ} (hαβ : α ≤ β)
    (h : M.HasApproxRatio α) : M.HasApproxRatio β := fun x =>
  (h x).trans (by gcongr)

/-- Real-valued characterization of strategyproofness under `HasFiniteCost`. -/
theorem isStrategyProof_iff_expectedCost_le [DecidableEq ι] {M : Mechanism ι G}
    (hfin : ∀ x, HasFiniteCost (M x)) :
    M.IsStrategyProof ↔ ∀ (x : ι → G) (i : ι) (z : G),
      expectedCost (M x) (x i) ≤ expectedCost (M (Function.update x i z)) (x i) :=
  forall₃_congr fun x i z =>
    expectedECost_le_iff_expectedCost_le (hfin x (x i)) (hfin (Function.update x i z) (x i))

/-- Real-valued characterization of `HasApproxRatio α` (for `0 ≤ α`) on a nonempty space under
`HasFiniteCost`. -/
theorem hasApproxRatio_iff_expectedSocialCost_le [Fintype ι] [Nonempty G] {M : Mechanism ι G}
    {α : ℝ} (hα : 0 ≤ α) (hfin : ∀ x, HasFiniteCost (M x)) :
    M.HasApproxRatio α ↔ ∀ x : ι → G, expectedSocialCost (M x) x ≤ α * optSocialCost x := by
  refine forall_congr' fun x => ?_
  rw [expectedSocialECost_eq_ofReal_expectedSocialCost (fun i => hfin x (x i)),
    optSocialECost_eq_ofReal_optSocialCost, ← ENNReal.ofReal_mul hα]
  exact ENNReal.ofReal_le_ofReal_iff (mul_nonneg hα (optSocialCost_nonneg x))

section FiniteMoment

variable [OpensMeasurableSpace G]

/-- A mechanism achieves approximation ratio `1` iff its extended expected social cost matches
`optSocialECost x` on every profile `x`. -/
theorem hasApproxRatio_one_iff_eq [Fintype ι] {M : Mechanism ι G} :
    M.HasApproxRatio 1 ↔ ∀ x : ι → G, expectedSocialECost (M x) x = optSocialECost x := by
  refine forall_congr' fun x => ?_
  simp only [ENNReal.ofReal_one, one_mul]
  exact ⟨fun h => le_antisymm h (optSocialECost_le_expectedSocialECost (M x) x), fun h => h.le⟩

/-- Any approximation ratio witnessed on a profile `x` with positive optimal social cost is at
least `1`. -/
theorem HasApproxRatio.one_le_of_pos [Fintype ι] {M : Mechanism ι G} {α : ℝ}
    (h : M.HasApproxRatio α) {x : ι → G} (hx : 0 < optSocialECost x) : 1 ≤ α := by
  have : Nonempty G := (M x).nonempty
  by_contra! hlt1
  have hmul := ENNReal.mul_lt_mul_right hx.ne' (optSocialECost_lt_top x).ne
    (ENNReal.ofReal_lt_one.2 hlt1)
  rw [mul_comm, mul_one] at hmul
  exact (hmul.trans_le ((optSocialECost_le_expectedSocialECost (M x) x).trans (h x))).false

/-- On a nontrivial metric space with at least two agents, any approximation ratio is at least
`1`. -/
theorem HasApproxRatio.one_le {G : Type*} [MetricSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [Nontrivial G] [Fintype ι] (hcard : 2 ≤ Fintype.card ι)
    {M : Mechanism ι G} {α : ℝ} (h : M.HasApproxRatio α) : 1 ≤ α := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne G
  obtain ⟨i, j, hij⟩ := Fintype.one_lt_card_iff.1 (by omega : 1 < Fintype.card ι)
  classical
  let x : ι → G := fun k => if k = i then a else b
  refine h.one_le_of_pos (x := x) (lt_of_lt_of_le (edist_pos.2 hab) (le_iInf fun y => ?_))
  calc edist a b ≤ edist a y + edist y b := edist_triangle a y b
    _ = edist (x i) y + edist (x j) y := by simp only [x, hij.symm, ↓reduceIte, edist_comm y b]
    _ ≤ ∑ k, edist (x k) y := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩), ← add_assoc]
      exact le_self_add

end FiniteMoment

end Properties

/-! ### Deterministic and PMF mechanisms -/

section Embeddings

variable {ι G : Type*} [MeasurableSpace G]

/-- Lift a deterministic rule `f : (ι → G) → G` to a randomized mechanism via `Measure.dirac`. -/
@[expose] noncomputable def deterministic (f : (ι → G) → G) : Mechanism ι G :=
  fun x => (Measure.dirac (f x)).toProbabilityMeasure

/-- Lift a discrete `PMF`-valued rule `p : (ι → G) → PMF G` to a `ProbabilityMeasure` mechanism. -/
@[expose] noncomputable def ofPMF (p : (ι → G) → PMF G) : Mechanism ι G :=
  fun x => (p x).toMeasure.toProbabilityMeasure

/-- Embedding a deterministic rule via `Measure.dirac` agrees with lifting `PMF.pure`. -/
theorem deterministic_eq_ofPMF_pure (f : (ι → G) → G) :
    deterministic f = ofPMF (fun x => PMF.pure (f x)) := by
  funext x
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.dirac (f x) = (PMF.pure (f x)).toMeasure
  exact (PMF.toMeasure_pure (f x)).symm

@[simp]
theorem deterministic_apply_toMeasure (f : (ι → G) → G) (x : ι → G) :
    ((deterministic f x : ProbabilityMeasure G) : Measure G) = Measure.dirac (f x) :=
  rfl

@[simp]
theorem ofPMF_apply_toMeasure (p : (ι → G) → PMF G) (x : ι → G) :
    ((ofPMF p x : ProbabilityMeasure G) : Measure G) = (p x).toMeasure :=
  rfl

end Embeddings

end Mechanism

section Evaluation

variable {ι G : Type*} [PseudoMetricSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]

/-- A Dirac point-mass distribution has finite expected distance cost everywhere. -/
theorem hasFiniteCost_dirac (a : G) :
    HasFiniteCost ((Measure.dirac a).toProbabilityMeasure) :=
  fun b => integrable_dirac' (stronglyMeasurable_dist_left b) (a := a) eNorm_lt_top

@[simp]
theorem expectedECost_dirac (a loc : G) :
    expectedECost ((Measure.dirac a).toProbabilityMeasure) loc = edist loc a := by
  simp only [expectedECost, Measure.coe_toProbabilityMeasure]
  exact lintegral_dirac' a (measurable_edist_left loc)

@[simp]
theorem expectedCost_dirac (a loc : G) :
    expectedCost ((Measure.dirac a).toProbabilityMeasure) loc = dist loc a := by
  simp only [expectedCost, Measure.coe_toProbabilityMeasure]
  exact integral_dirac' _ a (stronglyMeasurable_dist_left loc)

@[simp]
theorem expectedSocialECost_dirac [Fintype ι] (a : G) (x : ι → G) :
    expectedSocialECost ((Measure.dirac a).toProbabilityMeasure) x = socialECost x a := by
  simp only [expectedSocialECost, expectedECost_dirac, socialECost]

@[simp]
theorem expectedSocialCost_dirac [Fintype ι] (a : G) (x : ι → G) :
    expectedSocialCost ((Measure.dirac a).toProbabilityMeasure) x = socialCost x a := by
  simp only [expectedSocialCost, expectedCost_dirac, socialCost]

namespace Mechanism

/-- Every deterministic mechanism produces distributions with finite expected distance cost. -/
theorem hasFiniteCost_deterministic (f : (ι → G) → G) (x : ι → G) :
    HasFiniteCost (deterministic f x) :=
  hasFiniteCost_dirac (f x)

@[simp]
theorem expectedECost_deterministic (f : (ι → G) → G) (x : ι → G) (loc : G) :
    expectedECost (deterministic f x) loc = edist loc (f x) :=
  expectedECost_dirac (f x) loc

@[simp]
theorem expectedCost_deterministic (f : (ι → G) → G) (x : ι → G) (loc : G) :
    expectedCost (deterministic f x) loc = dist loc (f x) :=
  expectedCost_dirac (f x) loc

@[simp]
theorem expectedSocialECost_deterministic [Fintype ι] (f : (ι → G) → G) (x : ι → G) :
    expectedSocialECost (deterministic f x) x = socialECost x (f x) :=
  expectedSocialECost_dirac (f x) x

@[simp]
theorem expectedSocialCost_deterministic [Fintype ι] (f : (ι → G) → G) (x : ι → G) :
    expectedSocialCost (deterministic f x) x = socialCost x (f x) :=
  expectedSocialCost_dirac (f x) x

/-- For a deterministic rule `f`, strategyproofness reduces to pointwise `dist` inequalities. -/
theorem isStrategyProof_deterministic_iff [DecidableEq ι] (f : (ι → G) → G) :
    (deterministic f).IsStrategyProof ↔
      ∀ (x : ι → G) (i : ι) (z : G), dist (x i) (f x) ≤ dist (x i) (f (Function.update x i z)) :=
  forall₃_congr fun _ _ _ => by
    simp [deterministic, edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg]

/-- For a deterministic rule `f`, weak group strategyproofness reduces to `dist` inequalities. -/
theorem isWeakGroupStrategyProof_deterministic_iff [DecidableEq ι] (f : (ι → G) → G) :
    (deterministic f).IsWeakGroupStrategyProof ↔
      ∀ (x z : ι → G) (A : Finset ι), A.Nonempty →
        ∃ i ∈ A, dist (x i) (f x) ≤ dist (x i) (f (A.piecewise z x)) :=
  forall₄_congr fun _ _ _ _ => exists_congr fun _ => and_congr_right fun _ => by
    simp [deterministic, edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg]

/-- For a deterministic rule `f`, strong group strategyproofness reduces to `dist` inequalities. -/
theorem isGroupStrategyProof_deterministic_iff [DecidableEq ι] (f : (ι → G) → G) :
    (deterministic f).IsGroupStrategyProof ↔
      ∀ (x z : ι → G) (A : Finset ι),
        ¬ ((∀ i ∈ A, dist (x i) (f (A.piecewise z x)) ≤ dist (x i) (f x)) ∧
          ∃ i ∈ A, dist (x i) (f (A.piecewise z x)) < dist (x i) (f x)) :=
  forall₃_congr fun _ _ _ => not_congr <| and_congr
    (forall₂_congr fun _ _ => by
      simp [deterministic, edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg])
    (exists_congr fun _ => and_congr_right fun _ => by
      simp [deterministic, edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg])

/-- On a nonempty space, a deterministic rule `f` has approximation ratio `α ≥ 0` iff
`socialCost x (f x) ≤ α * optSocialCost x` for every profile `x`. -/
theorem hasApproxRatio_deterministic_iff [Fintype ι] [Nonempty G] (f : (ι → G) → G)
    {α : ℝ} (hα : 0 ≤ α) :
    (deterministic f).HasApproxRatio α ↔ ∀ x : ι → G, socialCost x (f x) ≤ α * optSocialCost x := by
  simpa only [deterministic, expectedSocialCost_dirac] using
    hasApproxRatio_iff_expectedSocialCost_le (M := deterministic f) hα
      fun x => hasFiniteCost_dirac (f x)

end Mechanism

/-- Evaluate the extended expected distance cost of a `PMF` as a `tsum`. -/
theorem expectedECost_ofPMF (p : PMF G) (loc : G) :
    expectedECost (p.toMeasure.toProbabilityMeasure) loc = ∑' y, p y * edist loc y :=
  PMF.lintegral_toMeasure p (measurable_edist_left loc)

/-- Evaluate the extended expected distance cost of a `PMF` supported on a finite set `s`. -/
theorem expectedECost_ofPMF_finset (p : PMF G) {s : Finset G} (hs : ∀ y, y ∉ s → p y = 0)
    (loc : G) :
    expectedECost (p.toMeasure.toProbabilityMeasure) loc = ∑ y ∈ s, p y * edist loc y := by
  rw [expectedECost_ofPMF]
  exact tsum_eq_sum fun y hy => by rw [hs y hy, zero_mul]

/-- Evaluate the extended expected distance cost of a mapped distribution `q.map g`. -/
theorem expectedECost_ofPMF_map {α : Type*} (q : PMF α) (g : α → G) (loc : G) :
    expectedECost ((q.map g).toMeasure.toProbabilityMeasure) loc = ∑' a, q a * edist loc (g a) := by
  rw [expectedECost_ofPMF]
  exact Cslib.Probability.PMF.tsum_map_mul q g (fun y => edist loc y)

/-- Evaluate the extended expected distance cost of a mapped distribution `q.map g` on a finite
index type `α`. -/
theorem expectedECost_ofPMF_map_fintype {α : Type*} [Fintype α] (q : PMF α) (g : α → G)
    (loc : G) :
    expectedECost ((q.map g).toMeasure.toProbabilityMeasure) loc =
      ∑ a : α, q a * edist loc (g a) := by
  rw [expectedECost_ofPMF_map, tsum_fintype]

/-- Every finitely supported `PMF` induces a probability measure with finite expected cost. -/
theorem hasFiniteCost_ofPMF_of_finite_support (p : PMF G) (hp : p.support.Finite) :
    HasFiniteCost (p.toMeasure.toProbabilityMeasure) := fun a => by
  rw [← expectedECost_lt_top_iff_integrable,
    expectedECost_ofPMF_finset p (fun y hy => (p.apply_eq_zero_iff y).2 (hp.mem_toFinset.not.1 hy))]
  exact ENNReal.sum_lt_top.2 fun y _ => ENNReal.mul_lt_top (p.apply_lt_top y) (edist_lt_top a y)

/-- A mapped `PMF` over a `Finite` type has finite expected cost. -/
theorem hasFiniteCost_ofPMF_map_finite {α : Type*} [Finite α] (q : PMF α) (g : α → G) :
    HasFiniteCost ((q.map g).toMeasure.toProbabilityMeasure) := by
  refine hasFiniteCost_ofPMF_of_finite_support _ ?_
  rw [PMF.support_map]
  exact (Set.toFinite q.support).image g

/-- Evaluate the real-valued expected distance cost of a `PMF` as a `tsum` when the weighted
distances are summable. -/
theorem expectedCost_ofPMF_of_summable (p : PMF G) (loc : G)
    (hsum : Summable fun y => (p y).toReal * dist loc y) :
    expectedCost (p.toMeasure.toProbabilityMeasure) loc = ∑' y, (p y).toReal * dist loc y := by
  have hnn : ∀ y, 0 ≤ (p y).toReal * dist loc y := fun _ =>
    mul_nonneg ENNReal.toReal_nonneg dist_nonneg
  have htsum : ∑' y, p y * edist loc y = ENNReal.ofReal (∑' y, (p y).toReal * dist loc y) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum]
    refine tsum_congr fun y => ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (p.apply_ne_top y),
      edist_dist]
  rw [expectedCost_eq_toReal_expectedECost, expectedECost_ofPMF, htsum,
    ENNReal.toReal_ofReal (tsum_nonneg hnn)]

/-- Evaluate the real-valued expected distance cost of a `PMF` supported on a finite set `s`. -/
theorem expectedCost_ofPMF_finset (p : PMF G) {s : Finset G} (hs : ∀ y, y ∉ s → p y = 0)
    (loc : G) :
    expectedCost (p.toMeasure.toProbabilityMeasure) loc =
      ∑ y ∈ s, (p y).toReal * dist loc y := by
  have hzero : ∀ y ∉ s, (p y).toReal * dist loc y = 0 := fun y hy => by
    rw [hs y hy, ENNReal.toReal_zero, zero_mul]
  rw [expectedCost_ofPMF_of_summable p loc (summable_of_ne_finset_zero hzero), tsum_eq_sum hzero]

/-- Evaluate the real-valued expected distance cost of a `PMF` on a finite space `G`. -/
theorem expectedCost_ofPMF_fintype [Fintype G] (p : PMF G) (loc : G) :
    expectedCost (p.toMeasure.toProbabilityMeasure) loc = ∑ y : G, (p y).toReal * dist loc y :=
  expectedCost_ofPMF_finset p (fun y hy => absurd (Finset.mem_univ y) hy) loc

/-- Evaluate the real-valued expected distance cost of a mapped distribution `q.map g` on a finite
index type `α`. -/
theorem expectedCost_ofPMF_map_fintype {α : Type*} [Fintype α] (q : PMF α) (g : α → G)
    (loc : G) :
    expectedCost ((q.map g).toMeasure.toProbabilityMeasure) loc =
      ∑ a : α, (q a).toReal * dist loc (g a) := by
  have hfin := ENNReal.toReal_sum fun a (_ : a ∈ Finset.univ) =>
    (ENNReal.mul_lt_top (q.apply_lt_top a) (edist_lt_top loc (g a))).ne
  rw [expectedCost_eq_toReal_expectedECost, expectedECost_ofPMF_map_fintype, hfin]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.toReal_mul, edist_dist, ENNReal.toReal_ofReal dist_nonneg]

/-- Evaluate the real-valued expected social cost of a mapped distribution `q.map g` on a finite
index type `α`. -/
theorem expectedSocialCost_ofPMF_map_fintype {α : Type*} [Fintype α] [Fintype ι] (q : PMF α)
    (g : α → G) (x : ι → G) :
    expectedSocialCost ((q.map g).toMeasure.toProbabilityMeasure) x =
      ∑ i, ∑ a : α, (q a).toReal * dist (x i) (g a) := by
  simp only [expectedSocialCost, expectedCost_ofPMF_map_fintype]

namespace Mechanism

/-- Evaluate the extended expected distance cost of `ofPMF p x` as a `tsum`. -/
@[simp]
theorem expectedECost_ofPMF (p : (ι → G) → PMF G) (x : ι → G) (loc : G) :
    expectedECost (ofPMF p x) loc = ∑' y, p x y * edist loc y :=
  _root_.Cslib.GameTheory.FacilityLocation.expectedECost_ofPMF (p x) loc

end Mechanism

end Evaluation

/-! ### Unanimity -/

section Unanimity

/-- Every surjective, strategyproof deterministic facility-location mechanism on a metric space is
unanimous: when all agents report the same location `y`, the mechanism places the facility at
`y`. -/
theorem unanimous_of_surjective_isStrategyProof {ι G : Type*} [Finite ι] [DecidableEq ι]
    [MetricSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    {f : (ι → G) → G} (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f) (y : G) :
    f (fun _ => y) = y := by
  obtain ⟨x, hx⟩ := hf_onto y
  refine Function.update_induction (P := fun z => f z = y) (y := fun _ => y) hx ?_
  intro z _ hz i _ _
  have h := (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp
    (Function.update z i y) i (z i)
  rw [Function.update_self, Function.update_idem, Function.update_eq_self, hz, dist_self] at h
  exact (dist_le_zero.mp h).symm

end Unanimity

end Cslib.GameTheory.FacilityLocation
