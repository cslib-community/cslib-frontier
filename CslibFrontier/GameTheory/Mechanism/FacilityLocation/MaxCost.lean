/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Dictatorship
public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Median
public import Mathlib.Data.Fin.VecNotation
import CslibFrontier.Probability.PMF.ToMeasure
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Maximum-cost facility location without money and the LRM mechanism

This module formalizes the **maximum-cost** (minimax / `1`-center) objective for facility-location
mechanisms without money from Section 3.2 of [ProcacciaTennenholtz2013] (pp. 18:7–18:11, Table I),
extending `CslibFrontier.GameTheory.Mechanism.FacilityLocation.Basic` and `Median`:

1. **Metric maximum-cost framework**: for a finite agent profile `x : ι → G` on a
   `PseudoMetricSpace G`, `maxCost x y` (and extended nonnegative `maxECost x y`) measures the
   worst-off agent's distance `sup_i dist (x i) y`, with optimum `optMaxCost x` (`optMaxECost x`),
   expected maximum cost `expectedMaxECost μ x = ∫⁻ y, maxECost x y ∂μ` (and Bochner counterpart
   `expectedMaxCost μ x`), and worst-case approximation predicate `Mechanism.HasMaxCostApproxRatio`.
   Integrability of `maxCost x` holds under the existing `HasFiniteCost μ` predicate, and every
   mechanism satisfying `M.HasMaxCostApproxRatio α` on a nonempty profile automatically has
   `HasFiniteCost (M x)` on all profiles.
2. **Real-line geometry and Lemmas 3.5–3.6**: on `ℝ` for nonempty finite `ι`, with extreme reports
   `leftmost x` and `rightmost x` and midpoint `center x = (leftmost x + rightmost x) / 2`,
   `maxCost x y = |y - center x| + (rightmost x - leftmost x) / 2` (`maxCost_real_eq`). Thus
   `center x` uniquely attains `optMaxCost x = (rightmost x - leftmost x) / 2`
   (`center_isMinimaxOptimal`, `optMaxCost_real_eq`), although `centerMechanism` is not
   strategyproof for `2 ≤ Fintype.card ι` (`not_isStrategyProof_centerMechanism`), and every
   finite-cost distribution satisfies
   `expectedMaxCost μ x = expectedCost μ (center x) + optMaxCost x`
   (`expectedMaxCost_eq_expectedCost_center_add`, generalizing Lemma 3.5 from `n = 2` to all `n`).
3. **Tight deterministic `2`-approximation (Theorems 3.1 and 3.2)**: every point in
   `[leftmost x, rightmost x]` achieves `maxCost x y ≤ 2 * optMaxCost x`, so every
   `orderStatisticMechanism k`—in particular `leftmostMechanism` (Theorem 3.1) and
   `medianMechanism`—as well as `dictatorship i₀` is strongly group strategyproof and
   `2`-approximate for maximum cost. Conversely, for `2 ≤ Fintype.card ι`, every deterministic
   strategyproof mechanism has maximum-cost approximation ratio at least `2`
   (`two_le_of_deterministic_isStrategyProof`, Theorem 3.2).
4. **Randomized Left–Right–Midpoint (`lrmMechanism`) and tight `3/2` bound (Mechanism 1, Theorems
   3.3 and 3.4)**: `lrmMechanism` places probability `1/4` at `leftmost x`, `1/4` at `rightmost x`,
   and `1/2` at `center x`. It is weakly group strategyproof
   (`lrmMechanism_isWeakGroupStrategyProof`, matching what [ProcacciaTennenholtz2013] call "group
   strategyproofness"), strategyproof, and has exact expected maximum cost
   `(3 / 2) * optMaxCost x` on every profile (`expectedMaxCost_lrmMechanism`,
   `lrmMechanism_hasMaxCostApproxRatio`, Theorem 3.3), while failing strong group strategyproofness
   whenever `3 ≤ Fintype.card ι` (`not_isGroupStrategyProof_lrmMechanism`, witnessing the §3 remark
   on p. 18:7). Conversely, for `2 ≤ Fintype.card ι`, every randomized strategyproof mechanism has
   maximum-cost approximation ratio at least `3 / 2`
   (`three_halves_le_of_isStrategyProof`, Theorem 3.4).

## Main definitions

* `Cslib.GameTheory.FacilityLocation.maxCost`, `Cslib.GameTheory.FacilityLocation.maxECost`:
  deterministic maximum agent distance `sup_i dist (x i) y` (and `edist` version).
* `Cslib.GameTheory.FacilityLocation.optMaxCost`, `Cslib.GameTheory.FacilityLocation.optMaxECost`,
  `Cslib.GameTheory.FacilityLocation.IsMinimaxOptimal`: optimal maximum cost and minimax optimality.
* `Cslib.GameTheory.FacilityLocation.expectedMaxECost`,
  `Cslib.GameTheory.FacilityLocation.expectedMaxCost`: expected maximum cost of a facility
  distribution.
* `Cslib.GameTheory.FacilityLocation.Mechanism.HasMaxCostApproxRatio`: worst-case approximation
  ratio for expected maximum cost.
* `Cslib.GameTheory.FacilityLocation.leftmost`, `Cslib.GameTheory.FacilityLocation.rightmost`,
  `Cslib.GameTheory.FacilityLocation.center`, `Cslib.GameTheory.FacilityLocation.leftmostMechanism`,
  `Cslib.GameTheory.FacilityLocation.centerMechanism`: extreme reports and interval midpoint on `ℝ`.
* `Cslib.GameTheory.FacilityLocation.lrmPMF`, `Cslib.GameTheory.FacilityLocation.lrmMechanism`: the
  randomized Left–Right–Midpoint mechanism (`1/4` leftmost, `1/4` rightmost, `1/2` center).

## Main results

* `Cslib.GameTheory.FacilityLocation.Mechanism.HasMaxCostApproxRatio.hasFiniteCost`,
  `Cslib.GameTheory.FacilityLocation.Mechanism.HasMaxCostApproxRatio.one_le`: automatic finite
  expected cost on nonempty spaces and general `1 ≤ α` lower bound for `2 ≤ Fintype.card ι`.
* `Cslib.GameTheory.FacilityLocation.exists_expectedCost_ge_half_dist`: Lemma 3.6 on arbitrary
  pseudometric spaces.
* `Cslib.GameTheory.FacilityLocation.maxCost_real_eq`,
  `Cslib.GameTheory.FacilityLocation.center_isMinimaxOptimal`,
  `Cslib.GameTheory.FacilityLocation.optMaxCost_real_eq`,
  `Cslib.GameTheory.FacilityLocation.expectedMaxCost_eq_expectedCost_center_add`: midpoint formula,
  minimax optimality of `center`, and generalized Lemma 3.5 on `ℝ`.
* `Cslib.GameTheory.FacilityLocation.not_isStrategyProof_centerMechanism`: non-strategyproofness of
  the midpoint mechanism for `2 ≤ Fintype.card ι`.
* `Cslib.GameTheory.FacilityLocation.orderStatisticMechanism_hasMaxCostApproxRatio_two`,
  `Cslib.GameTheory.FacilityLocation.leftmostMechanism_hasMaxCostApproxRatio_two`,
  `Cslib.GameTheory.FacilityLocation.medianMechanism_hasMaxCostApproxRatio_two`,
  `Cslib.GameTheory.FacilityLocation.dictatorship_hasMaxCostApproxRatio_two`: deterministic
  `2`-approximation upper bounds (Theorem 3.1 and median/order-statistic corollaries).
* `Cslib.GameTheory.FacilityLocation.two_le_of_deterministic_isStrategyProof`: tight `2` lower bound
  for deterministic strategyproof mechanisms when `2 ≤ Fintype.card ι` (Theorem 3.2).
* `Cslib.GameTheory.FacilityLocation.expectedMaxCost_lrmMechanism`,
  `Cslib.GameTheory.FacilityLocation.lrmMechanism_hasMaxCostApproxRatio`,
  `Cslib.GameTheory.FacilityLocation.lrmMechanism_isWeakGroupStrategyProof`,
  `Cslib.GameTheory.FacilityLocation.not_isGroupStrategyProof_lrmMechanism`: exact `(3/2)` expected
  maximum cost, weak group strategyproofness (Theorem 3.3), and failure of strong group
  strategyproofness for `3 ≤ Fintype.card ι`.
* `Cslib.GameTheory.FacilityLocation.three_halves_le_of_isStrategyProof`: tight `3 / 2` lower bound
  for randomized strategyproof mechanisms when `2 ≤ Fintype.card ι` (Theorem 3.4).

## References

* [A. D. Procaccia and M. Tennenholtz, *Approximate Mechanism Design without
  Money*][ProcacciaTennenholtz2013]
-/

public section

namespace Cslib.GameTheory.FacilityLocation

open MeasureTheory Finset
open scoped BigOperators ENNReal NNReal

/-! ### Maximum cost on pseudometric spaces -/

section MaxCost

variable {ι G : Type*} [PseudoMetricSpace G] [Fintype ι]

/-- The **maximum cost** `sup_i dist (x i) y` of placing a facility at `y` for agent profile `x`
([ProcacciaTennenholtz2013] §3, p. 18:7; equals `0` when `ι` is empty). -/
@[expose] noncomputable def maxCost (x : ι → G) (y : G) : ℝ :=
  ((Finset.univ.sup fun i => nndist (x i) y : ℝ≥0) : ℝ)

/-- The extended nonnegative **maximum cost** `sup_i edist (x i) y` of placing a facility at `y`. -/
@[expose] noncomputable def maxECost (x : ι → G) (y : G) : ℝ≥0∞ :=
  Finset.univ.sup fun i => edist (x i) y

/-- The **optimal maximum cost** `⨅ y, maxCost x y` on agent profile `x`. -/
@[expose] noncomputable def optMaxCost (x : ι → G) : ℝ :=
  ⨅ y : G, maxCost x y

/-- The optimal extended nonnegative maximum cost `⨅ y, maxECost x y` on agent profile `x`. -/
@[expose] noncomputable def optMaxECost (x : ι → G) : ℝ≥0∞ :=
  ⨅ y : G, maxECost x y

/-- A location `y` is **minimax-optimal** for profile `x` if it minimizes `maxCost x` over `G`. -/
@[expose] def IsMinimaxOptimal (x : ι → G) (y : G) : Prop :=
  ∀ z : G, maxCost x y ≤ maxCost x z

/-- The deterministic maximum cost `maxCost x y` is nonnegative. -/
theorem maxCost_nonneg (x : ι → G) (y : G) : 0 ≤ maxCost x y :=
  NNReal.coe_nonneg _

/-- Every agent's distance `dist (x i) y` is at most `maxCost x y`. -/
theorem dist_le_maxCost (x : ι → G) (y : G) (i : ι) : dist (x i) y ≤ maxCost x y := by
  rw [dist_nndist]
  exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun j => nndist (x j) y) (Finset.mem_univ i))

/-- Every agent's extended distance `edist (x i) y` is at most `maxECost x y`. -/
theorem edist_le_maxECost (x : ι → G) (y : G) (i : ι) : edist (x i) y ≤ maxECost x y :=
  Finset.le_sup (f := fun j => edist (x j) y) (Finset.mem_univ i)

/-- For `0 ≤ c`, `maxCost x y ≤ c` holds iff every agent is within distance `c` of `y`. -/
theorem maxCost_le_iff_of_nonneg {x : ι → G} {y : G} {c : ℝ} (hc : 0 ≤ c) :
    maxCost x y ≤ c ↔ ∀ i : ι, dist (x i) y ≤ c := by
  refine ⟨fun h i => (dist_le_maxCost x y i).trans h, fun h => ?_⟩
  lift c to ℝ≥0 using hc
  exact NNReal.coe_le_coe.mpr <| Finset.sup_le fun i _ =>
    NNReal.coe_le_coe.mp (dist_nndist (x i) y ▸ h i)

/-- When `ι` is nonempty, `maxCost x y ≤ c` holds iff every agent is within distance `c` of `y`. -/
theorem maxCost_le_iff [Nonempty ι] {x : ι → G} {y : G} {c : ℝ} :
    maxCost x y ≤ c ↔ ∀ i : ι, dist (x i) y ≤ c :=
  ⟨fun h i => (dist_le_maxCost x y i).trans h, fun h =>
    have ⟨i₀⟩ := ‹Nonempty ι›
    (maxCost_le_iff_of_nonneg (dist_nonneg.trans (h i₀))).mpr h⟩

/-- When `ι` is nonempty, some agent attains `maxCost x y`. -/
theorem exists_dist_eq_maxCost [Nonempty ι] (x : ι → G) (y : G) :
    ∃ i : ι, dist (x i) y = maxCost x y := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun j => nndist (x j) y)
  exact ⟨i, by rw [maxCost, hi, dist_nndist]⟩

/-- Triangle-inequality Lipschitz bound for `maxCost x`: shifting `y` to `z` changes `maxCost x`
by at most `dist y z`. -/
theorem maxCost_le_maxCost_add_dist (x : ι → G) (y z : G) :
    maxCost x y ≤ maxCost x z + dist y z :=
  (maxCost_le_iff_of_nonneg (add_nonneg (maxCost_nonneg x z) dist_nonneg)).mpr fun i =>
    (dist_triangle (x i) z y).trans
      (add_le_add (dist_le_maxCost x z i) (by rw [dist_comm z y]))

/-- `y ↦ maxCost x y` is `1`-Lipschitz in `y`: `|maxCost x y - maxCost x z| ≤ dist y z`. -/
theorem abs_maxCost_sub_maxCost_le (x : ι → G) (y z : G) :
    |maxCost x y - maxCost x z| ≤ dist y z :=
  abs_sub_le_iff.mpr ⟨by linarith [maxCost_le_maxCost_add_dist x y z],
    by linarith [dist_comm z y ▸ maxCost_le_maxCost_add_dist x z y]⟩

/-- `y ↦ maxCost x y` is continuous on `G`. -/
theorem continuous_maxCost (x : ι → G) : Continuous (maxCost x) :=
  Metric.continuous_iff.mpr fun y ε hε => ⟨ε, hε, fun z hzy => by
    rw [Real.dist_eq]
    exact (abs_maxCost_sub_maxCost_le x z y).trans_lt hzy⟩

/-- The extended maximum cost equals `ENNReal.ofReal (maxCost x y)`. -/
theorem maxECost_eq_ofReal_maxCost (x : ι → G) (y : G) :
    maxECost x y = ENNReal.ofReal (maxCost x y) := by
  refine le_antisymm (Finset.sup_le fun i _ => edist_dist (x i) y ▸
    ENNReal.ofReal_le_ofReal (dist_le_maxCost x y i)) ?_
  rcases isEmpty_or_nonempty ι with _ | _
  · simp [maxCost]
  · obtain ⟨i, hi⟩ := exists_dist_eq_maxCost x y
    rw [← hi, ← edist_dist]
    exact edist_le_maxECost x y i

/-- `y ↦ maxECost x y` is continuous on `G`. -/
theorem continuous_maxECost (x : ι → G) : Continuous (maxECost x) := by
  rw [funext (maxECost_eq_ofReal_maxCost x)]
  exact ENNReal.continuous_ofReal.comp (continuous_maxCost x)

/-- The range of `maxCost x` is bounded below by `0`. -/
theorem bddBelow_range_maxCost (x : ι → G) : BddBelow (Set.range (maxCost x)) :=
  ⟨0, by rintro _ ⟨y, rfl⟩; exact maxCost_nonneg x y⟩

/-- The optimal maximum cost `optMaxCost x` is nonnegative. -/
theorem optMaxCost_nonneg (x : ι → G) : 0 ≤ optMaxCost x := by
  rcases isEmpty_or_nonempty G with hG | hG
  · rw [optMaxCost, Real.iInf_of_isEmpty]
  · exact le_ciInf fun y => maxCost_nonneg x y

/-- `optMaxCost x` is at most `maxCost x y` for every location `y`. -/
theorem optMaxCost_le_maxCost (x : ι → G) (y : G) : optMaxCost x ≤ maxCost x y :=
  ciInf_le (bddBelow_range_maxCost x) y

/-- On a nonempty space, `c ≤ optMaxCost x` iff `c ≤ maxCost x y` for all `y`. -/
theorem le_optMaxCost_iff [Nonempty G] {x : ι → G} {c : ℝ} :
    c ≤ optMaxCost x ↔ ∀ y : G, c ≤ maxCost x y :=
  le_ciInf_iff (bddBelow_range_maxCost x)

/-- Any uniform bound `c ≤ α * maxCost x y` with `0 ≤ α` transfers to `α * optMaxCost x`. -/
theorem le_mul_optMaxCost [Nonempty G] {x : ι → G} {α c : ℝ} (hα : 0 ≤ α)
    (h : ∀ y : G, c ≤ α * maxCost x y) : c ≤ α * optMaxCost x := by
  rcases hα.eq_or_lt with rfl | hpos
  · exact ‹Nonempty G›.elim fun y => by simpa only [zero_mul] using h y
  · exact (div_le_iff₀' hpos).mp (le_optMaxCost_iff.mpr fun y => (div_le_iff₀' hpos).mpr (h y))

/-- `optMaxECost x` is at most `maxECost x y` for every location `y`. -/
theorem optMaxECost_le_maxECost (x : ι → G) (y : G) : optMaxECost x ≤ maxECost x y :=
  iInf_le (maxECost x) y

/-- On a nonempty space, `optMaxECost x < ⊤`. -/
theorem optMaxECost_lt_top [Nonempty G] (x : ι → G) : optMaxECost x < ⊤ := by
  obtain ⟨y⟩ := ‹Nonempty G›
  exact (optMaxECost_le_maxECost x y).trans_lt
    (maxECost_eq_ofReal_maxCost x y ▸ ENNReal.ofReal_lt_top)

/-- On a nonempty space, `optMaxECost x = ENNReal.ofReal (optMaxCost x)`. -/
theorem optMaxECost_eq_ofReal_optMaxCost [Nonempty G] (x : ι → G) :
    optMaxECost x = ENNReal.ofReal (optMaxCost x) := by
  refine le_antisymm ?_ (le_iInf fun y => maxECost_eq_ofReal_maxCost x y ▸
    ENNReal.ofReal_le_ofReal (optMaxCost_le_maxCost x y))
  rw [← ENNReal.toReal_le_toReal (optMaxECost_lt_top x).ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (optMaxCost_nonneg x)]
  exact le_ciInf fun y => ENNReal.toReal_le_of_le_ofReal (maxCost_nonneg x y)
    (maxECost_eq_ofReal_maxCost x y ▸ optMaxECost_le_maxECost x y)

/-- A location `y` is minimax-optimal for `x` iff `maxCost x y = optMaxCost x`. -/
theorem isMinimaxOptimal_iff_maxCost_eq_optMaxCost [Nonempty G] {x : ι → G} {y : G} :
    IsMinimaxOptimal x y ↔ maxCost x y = optMaxCost x :=
  ⟨fun h => le_antisymm (le_ciInf h) (optMaxCost_le_maxCost x y),
   fun h z => h ▸ optMaxCost_le_maxCost x z⟩

/-- A minimax-optimal location attains `optMaxCost x`. -/
theorem IsMinimaxOptimal.maxCost_eq_optMaxCost [Nonempty G] {x : ι → G} {y : G}
    (h : IsMinimaxOptimal x y) : maxCost x y = optMaxCost x :=
  isMinimaxOptimal_iff_maxCost_eq_optMaxCost.mp h

end MaxCost

/-! ### Expected maximum cost and approximation ratio -/

section ExpectedMaxCost

variable {ι G : Type*} [PseudoMetricSpace G] [MeasurableSpace G] [Fintype ι]

/-- The extended nonnegative expected maximum cost `∫⁻ y, maxECost x y ∂μ`
([ProcacciaTennenholtz2013] §3, p. 18:7). -/
@[expose] noncomputable def expectedMaxECost (μ : ProbabilityMeasure G) (x : ι → G) : ℝ≥0∞ :=
  ∫⁻ y, maxECost x y ∂(μ : Measure G)

/-- The real-valued Bochner expected maximum cost `∫ y, maxCost x y ∂μ`. -/
@[expose] noncomputable def expectedMaxCost (μ : ProbabilityMeasure G) (x : ι → G) : ℝ :=
  ∫ y, maxCost x y ∂(μ : Measure G)

/-- The real-valued expected maximum cost `expectedMaxCost μ x` is nonnegative. -/
theorem expectedMaxCost_nonneg (μ : ProbabilityMeasure G) (x : ι → G) :
    0 ≤ expectedMaxCost μ x :=
  integral_nonneg fun y => maxCost_nonneg x y

/-- Every distribution `μ` has extended expected maximum cost at least `optMaxECost x`. -/
theorem optMaxECost_le_expectedMaxECost (μ : ProbabilityMeasure G) (x : ι → G) :
    optMaxECost x ≤ expectedMaxECost μ x := by
  calc optMaxECost x = ∫⁻ _, optMaxECost x ∂(μ : Measure G) := by simp
    _ ≤ ∫⁻ y, maxECost x y ∂(μ : Measure G) :=
      lintegral_mono fun y => optMaxECost_le_maxECost x y

/-- Every agent's extended expected cost under `μ` is bounded above by `expectedMaxECost μ x`. -/
theorem expectedECost_le_expectedMaxECost (μ : ProbabilityMeasure G) (x : ι → G) (i : ι) :
    expectedECost μ (x i) ≤ expectedMaxECost μ x :=
  lintegral_mono fun y => edist_le_maxECost x y i

/-- When `y ↦ maxCost x y` is integrable under `μ`, `expectedMaxECost μ x` equals
`ENNReal.ofReal (expectedMaxCost μ x)`. -/
theorem expectedMaxECost_eq_ofReal_expectedMaxCost {μ : ProbabilityMeasure G} {x : ι → G}
    (h : Integrable (maxCost x) (μ : Measure G)) :
    expectedMaxECost μ x = ENNReal.ofReal (expectedMaxCost μ x) := by
  rw [expectedMaxCost,
    ofReal_integral_eq_lintegral_ofReal h (Filter.Eventually.of_forall (maxCost_nonneg x))]
  exact lintegral_congr fun y => maxECost_eq_ofReal_maxCost x y

section Measurable

variable [OpensMeasurableSpace G]

private theorem measurable_maxECost (x : ι → G) : Measurable (maxECost x) :=
  (continuous_maxECost x).measurable

private theorem stronglyMeasurable_maxCost (x : ι → G) : StronglyMeasurable (maxCost x) :=
  (continuous_maxCost x).stronglyMeasurable

/-- Under `HasFiniteCost μ`, `maxCost x` is Bochner integrable on `G`. -/
theorem HasFiniteCost.integrable_maxCost {μ : ProbabilityMeasure G} (h : HasFiniteCost μ)
    (x : ι → G) : Integrable (maxCost x) (μ : Measure G) := by
  let a := μ.nonempty.some
  have hbound : Integrable (fun y => maxCost x a + dist a y) (μ : Measure G) :=
    (integrable_const _).add (h a)
  refine hbound.mono' (stronglyMeasurable_maxCost x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (maxCost_nonneg x y)]
  simpa only [dist_comm y a] using maxCost_le_maxCost_add_dist x y a

/-- On a nonempty space under `HasFiniteCost μ`, `optMaxCost x ≤ expectedMaxCost μ x`. -/
theorem optMaxCost_le_expectedMaxCost [Nonempty G] {μ : ProbabilityMeasure G}
    (h : HasFiniteCost μ) (x : ι → G) : optMaxCost x ≤ expectedMaxCost μ x := by
  have hle := optMaxECost_le_expectedMaxECost μ x
  rw [optMaxECost_eq_ofReal_optMaxCost,
    expectedMaxECost_eq_ofReal_expectedMaxCost (h.integrable_maxCost x)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (expectedMaxCost_nonneg μ x)).mp hle

@[simp]
theorem expectedMaxECost_dirac (a : G) (x : ι → G) :
    expectedMaxECost ((Measure.dirac a).toProbabilityMeasure) x = maxECost x a := by
  simp only [expectedMaxECost, Measure.coe_toProbabilityMeasure]
  exact lintegral_dirac' a (measurable_maxECost x)

@[simp]
theorem expectedMaxCost_dirac (a : G) (x : ι → G) :
    expectedMaxCost ((Measure.dirac a).toProbabilityMeasure) x = maxCost x a := by
  simp only [expectedMaxCost, Measure.coe_toProbabilityMeasure]
  exact integral_dirac' _ a (stronglyMeasurable_maxCost x)

/-- Evaluate `expectedMaxECost` of a mapped `PMF` over a finite index type `α`. -/
theorem expectedMaxECost_ofPMF_map_fintype {α : Type*} [Fintype α] (q : PMF α) (g : α → G)
    (x : ι → G) :
    expectedMaxECost ((q.map g).toMeasure.toProbabilityMeasure) x =
      ∑ a : α, q a * maxECost x (g a) := by
  rw [expectedMaxECost, Measure.coe_toProbabilityMeasure,
    PMF.lintegral_toMeasure _ (measurable_maxECost x),
    Cslib.Probability.PMF.tsum_map_mul q g (maxECost x), tsum_fintype]

/-- Evaluate `expectedMaxCost` of a mapped `PMF` over a finite index type `α`. -/
theorem expectedMaxCost_ofPMF_map_fintype {α : Type*} [Fintype α] (q : PMF α) (g : α → G)
    (x : ι → G) :
    expectedMaxCost ((q.map g).toMeasure.toProbabilityMeasure) x =
      ∑ a : α, (q a).toReal * maxCost x (g a) := by
  have hfin : HasFiniteCost ((q.map g).toMeasure.toProbabilityMeasure) :=
    hasFiniteCost_ofPMF_map_finite q g
  have h1 := congrArg ENNReal.toReal
    (expectedMaxECost_eq_ofReal_expectedMaxCost (hfin.integrable_maxCost x))
  rw [ENNReal.toReal_ofReal (expectedMaxCost_nonneg _ x), expectedMaxECost_ofPMF_map_fintype,
    ENNReal.toReal_sum fun a _ =>
      (ENNReal.mul_lt_top (q.apply_lt_top a)
        (by rw [maxECost_eq_ofReal_maxCost]; exact ENNReal.ofReal_lt_top)).ne] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.toReal_mul, maxECost_eq_ofReal_maxCost, ENNReal.toReal_ofReal (maxCost_nonneg x _)]

omit [OpensMeasurableSpace G] in
/-- **Lemma 3.6** of [ProcacciaTennenholtz2013] (§3.2, p. 18:10), generalized to arbitrary
pseudometric spaces: under any finite-cost distribution `μ` and any two locations `a, b : G`, at
least one of `a` and `b` incurs expected distance at least `dist a b / 2`. -/
theorem exists_expectedCost_ge_half_dist {μ : ProbabilityMeasure G} (hfin : HasFiniteCost μ)
    (a b : G) :
    dist a b / 2 ≤ expectedCost μ a ∨ dist a b / 2 ≤ expectedCost μ b := by
  have hsum : dist a b ≤ expectedCost μ a + expectedCost μ b := by
    calc dist a b
        = ∫ _ : G, dist a b ∂(μ : Measure G) := by simp
      _ ≤ ∫ y : G, (dist a y + dist b y) ∂(μ : Measure G) := by
          refine integral_mono (integrable_const _) ((hfin a).add (hfin b)) fun y => ?_
          simpa only [dist_comm y b] using dist_triangle a y b
      _ = expectedCost μ a + expectedCost μ b := integral_add (hfin a) (hfin b)
  by_contra! h
  linarith

end Measurable

end ExpectedMaxCost

namespace Mechanism

section MaxCostApprox

variable {ι G : Type*} [PseudoMetricSpace G] [MeasurableSpace G] [Fintype ι]

/-- A randomized mechanism `M` has **maximum-cost approximation ratio `α`** if on every profile `x`,
its expected maximum cost is at most `α * optMaxECost x`
([ProcacciaTennenholtz2013] §3, p. 18:7). -/
@[expose] def HasMaxCostApproxRatio (M : Mechanism ι G) (α : ℝ) : Prop :=
  ∀ x : ι → G, expectedMaxECost (M x) x ≤ ENNReal.ofReal α * optMaxECost x

/-- `HasMaxCostApproxRatio` is upward-closed in the ratio `α`. -/
theorem HasMaxCostApproxRatio.mono {M : Mechanism ι G} {α β : ℝ} (hαβ : α ≤ β)
    (h : M.HasMaxCostApproxRatio α) : M.HasMaxCostApproxRatio β := fun x =>
  (h x).trans (by gcongr)

section Measurable

variable [OpensMeasurableSpace G]

@[simp]
theorem expectedMaxECost_deterministic (f : (ι → G) → G) (x : ι → G) :
    expectedMaxECost (deterministic f x) x = maxECost x (f x) :=
  expectedMaxECost_dirac (f x) x

@[simp]
theorem expectedMaxCost_deterministic (f : (ι → G) → G) (x : ι → G) :
    expectedMaxCost (deterministic f x) x = maxCost x (f x) :=
  expectedMaxCost_dirac (f x) x

/-- When `ι` is nonempty, any mechanism satisfying `M.HasMaxCostApproxRatio α` automatically has
finite expected distance cost `HasFiniteCost (M x)` on every profile `x`. -/
theorem HasMaxCostApproxRatio.hasFiniteCost [Nonempty ι] {M : Mechanism ι G} {α : ℝ}
    (h : M.HasMaxCostApproxRatio α) (x : ι → G) : HasFiniteCost (M x) := by
  have : Nonempty G := (M x).nonempty
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hlt : expectedECost (M x) (x i₀) < ⊤ :=
    (expectedECost_le_expectedMaxECost (M x) x i₀).trans_lt
      ((h x).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (optMaxECost_lt_top x)))
  exact hasFiniteCost_of_exists_integrable
    ⟨x i₀, (expectedECost_lt_top_iff_integrable (M x) (x i₀)).mp hlt⟩

/-- Real-valued characterization of `HasMaxCostApproxRatio α` (`0 ≤ α`) under `HasFiniteCost`. -/
theorem hasMaxCostApproxRatio_iff_expectedMaxCost_le [Nonempty G] {M : Mechanism ι G}
    {α : ℝ} (hα : 0 ≤ α) (hfin : ∀ x, HasFiniteCost (M x)) :
    M.HasMaxCostApproxRatio α ↔ ∀ x : ι → G, expectedMaxCost (M x) x ≤ α * optMaxCost x := by
  refine forall_congr' fun x => ?_
  rw [expectedMaxECost_eq_ofReal_expectedMaxCost ((hfin x).integrable_maxCost x),
    optMaxECost_eq_ofReal_optMaxCost, ← ENNReal.ofReal_mul hα]
  exact ENNReal.ofReal_le_ofReal_iff (mul_nonneg hα (optMaxCost_nonneg x))

/-- Deterministic characterization of `HasMaxCostApproxRatio α` (`0 ≤ α`) on a nonempty space. -/
theorem hasMaxCostApproxRatio_deterministic_iff [Nonempty G] (f : (ι → G) → G)
    {α : ℝ} (hα : 0 ≤ α) :
    (deterministic f).HasMaxCostApproxRatio α ↔
      ∀ x : ι → G, maxCost x (f x) ≤ α * optMaxCost x := by
  rw [hasMaxCostApproxRatio_iff_expectedMaxCost_le (M := deterministic f) hα
    fun x => hasFiniteCost_dirac (f x)]
  refine forall_congr' fun x => ?_
  simp only [expectedMaxCost_deterministic]

end Measurable

/-- Any maximum-cost approximation ratio witnessed on a profile `x` with `0 < optMaxECost x`
satisfies `1 ≤ α`. -/
theorem HasMaxCostApproxRatio.one_le_of_pos {M : Mechanism ι G} {α : ℝ}
    (h : M.HasMaxCostApproxRatio α) {x : ι → G} (hx : 0 < optMaxECost x) : 1 ≤ α := by
  have : Nonempty G := (M x).nonempty
  by_contra hlt1
  have hmul := ENNReal.mul_lt_mul_right hx.ne' (optMaxECost_lt_top x).ne
    (ENNReal.ofReal_lt_one.mpr (lt_of_not_ge hlt1))
  rw [mul_comm, mul_comm _ 1, one_mul] at hmul
  exact (hmul.trans_le ((optMaxECost_le_expectedMaxECost (M x) x).trans (h x))).false

/-- On a nontrivial metric space with at least two agents, any maximum-cost approximation ratio is
at least `1`. -/
theorem HasMaxCostApproxRatio.one_le {G : Type*} [MetricSpace G] [MeasurableSpace G]
    [Nontrivial G] (hcard : 2 ≤ Fintype.card ι)
    {M : Mechanism ι G} {α : ℝ} (h : M.HasMaxCostApproxRatio α) : 1 ≤ α := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne G
  obtain ⟨i, j, hij⟩ := Fintype.one_lt_card_iff.mp hcard
  let x : ι → G := fun k => if k = i then a else b
  refine h.one_le_of_pos (x := x) (lt_of_lt_of_le
    (ENNReal.div_pos (edist_pos.mpr hab).ne' (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)) (le_iInf fun y => ?_))
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_comm, two_mul]
  calc edist a b ≤ edist a y + edist y b := edist_triangle a y b
    _ = edist (x i) y + edist (x j) y := by simp [x, hij.symm, edist_comm y b]
    _ ≤ maxECost x y + maxECost x y :=
        add_le_add (edist_le_maxECost x y i) (edist_le_maxECost x y j)

end MaxCostApprox

end Mechanism

/-! ### Extreme locations, midpoint geometry, and Lemma 3.5 on ℝ -/

section RealMaxCost

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The **leftmost** reported location `lt(x) = min_i x i` on `ℝ`
([ProcacciaTennenholtz2013] §3.2, p. 18:8). -/
@[expose] noncomputable def leftmost (x : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty x

/-- The **rightmost** reported location `rt(x) = max_i x i` on `ℝ`
([ProcacciaTennenholtz2013] §3.2, p. 18:8). -/
@[expose] noncomputable def rightmost (x : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty x

/-- The **center** (midpoint) `cen(x) = (lt(x) + rt(x)) / 2` of `[leftmost x, rightmost x]`
([ProcacciaTennenholtz2013] §3.2, p. 18:8). -/
@[expose] noncomputable def center (x : ι → ℝ) : ℝ :=
  (leftmost x + rightmost x) / 2

/-- The deterministic **leftmost mechanism** `f(x) = lt(x)`
([ProcacciaTennenholtz2013] §3.2, Theorem 3.1, p. 18:8). -/
@[expose] noncomputable def leftmostMechanism : Mechanism ι ℝ :=
  Mechanism.deterministic leftmost

/-- The deterministic **center (midpoint) mechanism** `f(x) = cen(x)`
([ProcacciaTennenholtz2013] §3.2, p. 18:8). -/
@[expose] noncomputable def centerMechanism : Mechanism ι ℝ :=
  Mechanism.deterministic center

theorem leftmost_le (x : ι → ℝ) (i : ι) : leftmost x ≤ x i :=
  Finset.inf'_le x (Finset.mem_univ i)

theorem le_rightmost (x : ι → ℝ) (i : ι) : x i ≤ rightmost x :=
  Finset.le_sup' x (Finset.mem_univ i)

theorem leftmost_le_rightmost (x : ι → ℝ) : leftmost x ≤ rightmost x := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact (leftmost_le x i₀).trans (le_rightmost x i₀)

theorem exists_eq_leftmost (x : ι → ℝ) : ∃ i : ι, x i = leftmost x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x
  exact ⟨i, hi.symm⟩

theorem exists_eq_rightmost (x : ι → ℝ) : ∃ i : ι, x i = rightmost x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  exact ⟨i, hi.symm⟩

theorem le_leftmost_iff {x : ι → ℝ} {c : ℝ} : c ≤ leftmost x ↔ ∀ i : ι, c ≤ x i := by
  simpa only [leftmost, Finset.mem_univ, forall_true_left] using
    (Finset.le_inf'_iff (s := Finset.univ) (H := Finset.univ_nonempty) (f := x) (a := c))

theorem rightmost_le_iff {x : ι → ℝ} {c : ℝ} : rightmost x ≤ c ↔ ∀ i : ι, x i ≤ c := by
  simpa only [rightmost, Finset.mem_univ, forall_true_left] using
    (Finset.sup'_le_iff (s := Finset.univ) (H := Finset.univ_nonempty) (f := x) (a := c))

/-- When `x i₀ = l`, `x i₁ = r`, and all agents lie in `[l, r]`, `leftmost x = l` and
`rightmost x = r`. -/
theorem leftmost_rightmost_of_bounds {x : ι → ℝ} {l r : ℝ}
    {i₀ i₁ : ι} (hi₀ : x i₀ = l) (hi₁ : x i₁ = r) (hb : ∀ j : ι, l ≤ x j ∧ x j ≤ r) :
    leftmost x = l ∧ rightmost x = r :=
  ⟨le_antisymm (hi₀ ▸ leftmost_le x i₀) (le_leftmost_iff.mpr fun j => (hb j).1),
   le_antisymm (rightmost_le_iff.mpr fun j => (hb j).2) (hi₁ ▸ le_rightmost x i₁)⟩

/-- Every order statistic `Fintype.orderStatistic x k` lies in `[leftmost x, rightmost x]`. -/
theorem orderStatistic_mem_Icc_leftmost_rightmost (x : ι → ℝ) (k : ℕ) :
    Fintype.orderStatistic x k ∈ Set.Icc (leftmost x) (rightmost x) := by
  rw [Fintype.orderStatistic_eq_min]
  have hk : min k (Fintype.card ι - 1) < Fintype.card ι :=
    Nat.lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt Fintype.card_pos zero_lt_one)
  obtain ⟨i, hi⟩ := (Fintype.orderStatistic_isOrderStatistic x hk).1
  exact ⟨hi ▸ leftmost_le x i, hi ▸ le_rightmost x i⟩

/-- `leftmost x` coincides with the `0`-th order statistic `Fintype.orderStatistic x 0`. -/
theorem leftmost_eq_orderStatistic_zero (x : ι → ℝ) :
    leftmost x = Fintype.orderStatistic x 0 := by
  symm
  obtain ⟨i, hi⟩ := exists_eq_leftmost x
  refine Fintype.orderStatistic_eq_of_isOrderStatistic Fintype.card_pos
    ⟨⟨i, hi⟩, ?_, Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi.le⟩⟩⟩
  rw [Finset.filter_eq_empty_iff.mpr fun j _ => not_lt.mpr (leftmost_le x j)]
  simp

/-- `leftmostMechanism` equals `orderStatisticMechanism 0`. -/
theorem leftmostMechanism_eq_orderStatisticMechanism :
    leftmostMechanism (ι := ι) = orderStatisticMechanism 0 := by
  simp only [leftmostMechanism, orderStatisticMechanism, funext leftmost_eq_orderStatistic_zero]

/-- On `ℝ`, the maximum cost at `y` equals `|y - center x| + (rightmost x - leftmost x) / 2`. -/
theorem maxCost_real_eq (x : ι → ℝ) (y : ℝ) :
    maxCost x y = |y - center x| + (rightmost x - leftmost x) / 2 := by
  obtain ⟨il, hil⟩ := exists_eq_leftmost x
  obtain ⟨ir, hir⟩ := exists_eq_rightmost x
  have hcen_def : center x = (leftmost x + rightmost x) / 2 := rfl
  refine le_antisymm (maxCost_le_iff.mpr fun i => ?_) ?_
  · rw [Real.dist_eq, abs_le]
    exact ⟨by linarith [leftmost_le x i, le_abs_self (y - center x)],
      by linarith [le_rightmost x i, neg_le_abs (y - center x)]⟩
  · have hdl := Real.dist_eq (x il) y ▸ dist_le_maxCost x y il
    have hdr := Real.dist_eq (x ir) y ▸ dist_le_maxCost x y ir
    have habs : |y - center x| ≤ maxCost x y - (rightmost x - leftmost x) / 2 :=
      abs_le.mpr ⟨by linarith [hir, le_abs_self (x ir - y)],
        by linarith [hil, neg_le_abs (x il - y)]⟩
    linarith

/-- The midpoint `center x` minimizes `maxCost x` on `ℝ`
([ProcacciaTennenholtz2013] §3.2, p. 18:8). -/
theorem center_isMinimaxOptimal (x : ι → ℝ) : IsMinimaxOptimal x (center x) := by
  intro z
  rw [maxCost_real_eq, maxCost_real_eq, sub_self, abs_zero, zero_add]
  linarith [abs_nonneg (z - center x)]

/-- On `ℝ`, the optimal maximum cost equals `(rightmost x - leftmost x) / 2`. -/
theorem optMaxCost_real_eq (x : ι → ℝ) :
    optMaxCost x = (rightmost x - leftmost x) / 2 := by
  rw [← (center_isMinimaxOptimal x).maxCost_eq_optMaxCost, maxCost_real_eq, sub_self, abs_zero,
    zero_add]

/-- **Lemma 3.5** of [ProcacciaTennenholtz2013] (§3.2, p. 18:10), generalized from `2` agents to
any finite nonempty `ι`: for any probability distribution `μ` on `ℝ` with `HasFiniteCost μ`,
`expectedMaxCost μ x = expectedCost μ (center x) + optMaxCost x`. -/
theorem expectedMaxCost_eq_expectedCost_center_add {μ : ProbabilityMeasure ℝ}
    (hfin : HasFiniteCost μ) (x : ι → ℝ) :
    expectedMaxCost μ x = expectedCost μ (center x) + optMaxCost x := by
  have hfun : maxCost x = fun y => dist (center x) y + optMaxCost x := by
    funext y
    rw [maxCost_real_eq, optMaxCost_real_eq, Real.dist_eq, abs_sub_comm]
  rw [expectedMaxCost, hfun, integral_add (hfin (center x)) (integrable_const _)]
  simp [expectedCost]

private lemma leftmost_rightmost_two_plus_mid [DecidableEq ι] {i₁ i₂ : ι} (h12 : i₁ ≠ i₂)
    {a b m : ℝ} (ham : a ≤ m) (hmb : m ≤ b) :
    leftmost (fun j : ι => if j = i₁ then a else if j = i₂ then b else m) = a ∧
      rightmost (fun j : ι => if j = i₁ then a else if j = i₂ then b else m) = b := by
  refine leftmost_rightmost_of_bounds (i₀ := i₁) (i₁ := i₂) (by simp) (by simp [h12.symm]) ?_
  intro j
  by_cases hj1 : j = i₁ <;> by_cases hj2 : j = i₂ <;>
    simp [hj1, hj2, h12.symm, ham, hmb, ham.trans hmb]

private lemma leftmost_rightmost_update_first [DecidableEq ι] {i₁ i₂ : ι} (h12 : i₁ ≠ i₂)
    {a₀ a b m : ℝ} (ham : a ≤ m) (hmb : m ≤ b) :
    leftmost (Function.update (fun j => if j = i₁ then a₀ else if j = i₂ then b else m) i₁ a) = a ∧
      rightmost (Function.update (fun j => if j = i₁ then a₀ else if j = i₂ then b else m) i₁ a) =
        b := by
  have heq : Function.update (fun j => if j = i₁ then a₀ else if j = i₂ then b else m) i₁ a =
      fun j => if j = i₁ then a else if j = i₂ then b else m := by
    funext j
    by_cases h : j = i₁ <;> simp [h]
  exact heq ▸ leftmost_rightmost_two_plus_mid h12 ham hmb

private lemma leftmost_rightmost_update_second [DecidableEq ι] {i₁ i₂ : ι} (h12 : i₁ ≠ i₂)
    {a b₀ b m : ℝ} (ham : a ≤ m) (hmb : m ≤ b) :
    leftmost (Function.update (fun j => if j = i₁ then a else if j = i₂ then b₀ else m) i₂ b) = a ∧
      rightmost (Function.update (fun j => if j = i₁ then a else if j = i₂ then b₀ else m) i₂ b) =
        b := by
  have heq : Function.update (fun j => if j = i₁ then a else if j = i₂ then b₀ else m) i₂ b =
      fun j => if j = i₁ then a else if j = i₂ then b else m := by
    funext j
    by_cases h : j = i₂ <;> simp [h, h12.symm]
  exact heq ▸ leftmost_rightmost_two_plus_mid h12 ham hmb

/-- For `2 ≤ Fintype.card ι`, the midpoint mechanism `centerMechanism` is not strategyproof
([ProcacciaTennenholtz2013] §3.2, p. 18:8): on the profile with agent `i₁` at `0` and all other
agents (including `i₂`) at `1`, agent `i₂` moves the facility from `1/2` to its true location `1`
by reporting `2`. -/
theorem not_isStrategyProof_centerMechanism [DecidableEq ι] (hcard : 2 ≤ Fintype.card ι) :
    ¬ (centerMechanism (ι := ι)).IsStrategyProof := by
  rw [centerMechanism, Mechanism.isStrategyProof_deterministic_iff]
  intro hsp
  obtain ⟨i₁, i₂, h12⟩ := Fintype.one_lt_card_iff.mp hcard
  let x : ι → ℝ := fun j => if j = i₁ then 0 else if j = i₂ then 1 else 1
  have hx : leftmost x = 0 ∧ rightmost x = 1 :=
    leftmost_rightmost_two_plus_mid h12 zero_le_one le_rfl
  have hx' : leftmost (Function.update x i₂ 2) = 0 ∧ rightmost (Function.update x i₂ 2) = 2 :=
    leftmost_rightmost_update_second h12 zero_le_one one_le_two
  have hx2 : x i₂ = 1 := by simp [x, h12.symm]
  have hle := hsp x i₂ 2
  rw [hx2, center, hx.1, hx.2, center, hx'.1, hx'.2, Real.dist_eq, Real.dist_eq] at hle
  norm_num at hle

/-! ### Tight deterministic `2`-approximation (Theorems 3.1 and 3.2) -/

/-- Any location `y ∈ [leftmost x, rightmost x]` achieves `maxCost x y ≤ 2 * optMaxCost x`
([ProcacciaTennenholtz2013] §3.2, p. 18:8). -/
theorem maxCost_le_two_mul_optMaxCost_of_mem_Icc {x : ι → ℝ} {y : ℝ}
    (hy : y ∈ Set.Icc (leftmost x) (rightmost x)) :
    maxCost x y ≤ 2 * optMaxCost x := by
  rw [maxCost_real_eq, optMaxCost_real_eq, center]
  have habs : |y - (leftmost x + rightmost x) / 2| ≤ (rightmost x - leftmost x) / 2 := by
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  linarith

/-- Every fixed `k`-th order-statistic mechanism on `ℝ` is `2`-approximate for maximum cost. -/
theorem orderStatisticMechanism_hasMaxCostApproxRatio_two (k : ℕ) :
    (orderStatisticMechanism (ι := ι) k).HasMaxCostApproxRatio 2 := by
  rw [orderStatisticMechanism, Mechanism.hasMaxCostApproxRatio_deterministic_iff _ (by norm_num)]
  intro x
  exact maxCost_le_two_mul_optMaxCost_of_mem_Icc (orderStatistic_mem_Icc_leftmost_rightmost x k)

/-- **Theorem 3.1** of [ProcacciaTennenholtz2013] (§3.2, p. 18:8), part 1: `leftmostMechanism` is
strongly group strategyproof (and hence weakly group strategyproof and strategyproof). -/
theorem leftmostMechanism_isGroupStrategyProof [DecidableEq ι] :
    (leftmostMechanism (ι := ι)).IsGroupStrategyProof := by
  rw [leftmostMechanism_eq_orderStatisticMechanism]
  exact orderStatisticMechanism_isGroupStrategyProof 0

/-- **Theorem 3.1** of [ProcacciaTennenholtz2013] (§3.2, p. 18:8), part 2: `leftmostMechanism` is a
`2`-approximation mechanism for the maximum cost. -/
theorem leftmostMechanism_hasMaxCostApproxRatio_two :
    (leftmostMechanism (ι := ι)).HasMaxCostApproxRatio 2 := by
  rw [leftmostMechanism_eq_orderStatisticMechanism]
  exact orderStatisticMechanism_hasMaxCostApproxRatio_two 0

/-- The **median mechanism** on `ℝ`—already optimal (`1`-approximate) for social cost and strongly
group strategyproof (`Median.lean`)—is simultaneously `2`-approximate for maximum cost. -/
theorem medianMechanism_hasMaxCostApproxRatio_two :
    (medianMechanism (ι := ι)).HasMaxCostApproxRatio 2 := by
  simpa only [medianMechanism, funext Fintype.lowerMedian_def, orderStatisticMechanism] using
    orderStatisticMechanism_hasMaxCostApproxRatio_two (ι := ι) ((Fintype.card ι - 1) / 2)

/-- Deterministic dictatorship of any agent `i₀` on `ℝ` is also `2`-approximate for maximum cost. -/
theorem dictatorship_hasMaxCostApproxRatio_two (i₀ : ι) :
    (dictatorship (G := ℝ) i₀).HasMaxCostApproxRatio 2 := by
  rw [dictatorship, Mechanism.hasMaxCostApproxRatio_deterministic_iff _ (by norm_num)]
  intro x
  exact maxCost_le_two_mul_optMaxCost_of_mem_Icc ⟨leftmost_le x i₀, le_rightmost x i₀⟩

omit [Nonempty ι] in
/-- **Theorem 3.2** of [ProcacciaTennenholtz2013] (§3.2, p. 18:8): for `2 ≤ Fintype.card ι`, every
deterministic strategyproof mechanism `f : (ι → ℝ) → ℝ` has maximum-cost approximation ratio at
least `2`. -/
theorem two_le_of_deterministic_isStrategyProof [DecidableEq ι] (hcard : 2 ≤ Fintype.card ι)
    {f : (ι → ℝ) → ℝ} (hsp : (Mechanism.deterministic f).IsStrategyProof)
    {α : ℝ} (happrox : (Mechanism.deterministic f).HasMaxCostApproxRatio α) :
    2 ≤ α := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide) hcard)
  have hdet := (Mechanism.hasMaxCostApproxRatio_deterministic_iff f
    (zero_le_one.trans (happrox.one_le hcard))).mp happrox
  have hsp_det := (Mechanism.isStrategyProof_deterministic_iff f).mp hsp
  obtain ⟨i₁, i₂, h12⟩ := Fintype.one_lt_card_iff.mp hcard
  let x : ι → ℝ := fun j => if j = i₁ then 0 else if j = i₂ then 1 else 1 / 2
  set y := f x
  have hfix : ∀ i c, x i = c → f (Function.update x i y) = y := fun i c hxi => by
    have h := hsp_det (Function.update x i y) i c
    rw [Function.update_self, Function.update_idem, ← hxi, Function.update_eq_self,
      dist_self] at h
    exact (dist_le_zero.mp h).symm
  rcases le_total (1 / 2) y with hy | hy
  · let x' := Function.update x i₂ y
    have hx' : leftmost x' = 0 ∧ rightmost x' = y :=
      leftmost_rightmost_update_second h12 (by norm_num) hy
    have hbd := hdet x'
    rw [hfix i₂ 1 (by simp [x, h12.symm]), maxCost_real_eq, optMaxCost_real_eq, center,
      hx'.1, hx'.2, abs_of_nonneg (by linarith)] at hbd
    have hy_ne : y ≠ 0 := by linarith
    calc (2 : ℝ) = y / (y / 2) := by field_simp [hy_ne]
      _ ≤ α := (div_le_iff₀ (by linarith)).mpr (by linarith)
  · let x' := Function.update x i₁ y
    have hx' : leftmost x' = y ∧ rightmost x' = 1 :=
      leftmost_rightmost_update_first h12 hy (by norm_num)
    have hbd := hdet x'
    rw [hfix i₁ 0 (by simp [x]), maxCost_real_eq, optMaxCost_real_eq, center,
      hx'.1, hx'.2, abs_of_nonpos (by linarith)] at hbd
    have hy_ne : 1 - y ≠ 0 := by linarith
    calc (2 : ℝ) = (1 - y) / ((1 - y) / 2) := by field_simp [hy_ne]
      _ ≤ α := (div_le_iff₀ (by linarith)).mpr (by linarith)

/-! ### Randomized Left–Right–Midpoint (`lrmMechanism`) and tight `3/2` bound -/

/-- Probability mass function of **Mechanism 1** (Left–Right–Midpoint) of
[ProcacciaTennenholtz2013] (§3.2, p. 18:8): returns `leftmost x` with probability `1/4`,
`rightmost x` with probability `1/4`, and `center x` with probability `1/2` (collapsing to point
mass `1` when all agents share the same location). -/
@[expose] noncomputable def lrmPMF (x : ι → ℝ) : PMF ℝ :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin 4)).map
    ![leftmost x, rightmost x, center x, center x]

/-- The randomized **Left–Right–Midpoint (`lrmMechanism`)** facility-location mechanism
(Mechanism 1 of [ProcacciaTennenholtz2013] §3.2, p. 18:8). -/
@[expose] noncomputable def lrmMechanism : Mechanism ι ℝ :=
  Mechanism.ofPMF lrmPMF

/-- When `leftmost x < rightmost x`, `lrmPMF x` assigns exact probabilities `1/4`, `1/4`, and `1/2`
to `leftmost x`, `rightmost x`, and `center x` respectively. -/
theorem lrmPMF_apply_of_lt {x : ι → ℝ} (hlt : leftmost x < rightmost x) :
    lrmPMF x (leftmost x) = 1 / 4 ∧
      lrmPMF x (rightmost x) = 1 / 4 ∧
      lrmPMF x (center x) = 1 / 2 := by
  have hlc : leftmost x < center x := by rw [center]; linarith
  have hcr : center x < rightmost x := by rw [center]; linarith
  have happly (y : ℝ) : lrmPMF x y =
      (if y = leftmost x then 4⁻¹ else 0) + (if y = rightmost x then 4⁻¹ else 0) +
        (if y = center x then 4⁻¹ else 0) + (if y = center x then 4⁻¹ else 0) := by
    rw [lrmPMF, PMF.map_apply, tsum_fintype, Fin.sum_univ_four]
    simp only [Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_fin,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [happly, ↓reduceIte, hlt.ne, hlc.ne, add_zero]; norm_num
  · simp only [happly, ↓reduceIte, hlt.ne', hcr.ne', zero_add, add_zero]; norm_num
  · simp only [happly, ↓reduceIte, hlc.ne', hcr.ne, zero_add]
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
      ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top),
      ← mul_add, ENNReal.inv_two_add_inv_two, mul_one, one_div]

theorem lrmMechanism_hasFiniteCost (x : ι → ℝ) : HasFiniteCost (lrmMechanism x) :=
  hasFiniteCost_ofPMF_map_finite _ _

/-- Explicit expected distance of any location `loc : ℝ` under `lrmMechanism x`:
`1/4 * |loc - leftmost x| + 1/4 * |loc - rightmost x| + 1/2 * |loc - center x|`. -/
theorem expectedCost_lrmMechanism (x : ι → ℝ) (loc : ℝ) :
    expectedCost (lrmMechanism x) loc =
      1 / 4 * |loc - leftmost x| + 1 / 4 * |loc - rightmost x| + 1 / 2 * |loc - center x| := by
  dsimp only [lrmMechanism, Mechanism.ofPMF, lrmPMF]
  rw [expectedCost_ofPMF_map_fintype, Fin.sum_univ_four]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_fin,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Real.dist_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  norm_num
  ring

/-- On every profile `x : ι → ℝ`, `lrmMechanism` incurs expected maximum cost identically equal to
`(3 / 2) * optMaxCost x` ([ProcacciaTennenholtz2013] §3.2, proof of Theorem 3.3, p. 18:9). -/
theorem expectedMaxCost_lrmMechanism (x : ι → ℝ) :
    expectedMaxCost (lrmMechanism x) x = (3 / 2) * optMaxCost x := by
  have hle := leftmost_le_rightmost x
  rw [expectedMaxCost_eq_expectedCost_center_add (lrmMechanism_hasFiniteCost x) x,
    expectedCost_lrmMechanism, optMaxCost_real_eq, center, sub_self, abs_zero,
    abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  ring

/-- **Theorem 3.3** of [ProcacciaTennenholtz2013] (§3.2, p. 18:9), approximation part:
`lrmMechanism` achieves maximum-cost approximation ratio `3 / 2`. -/
theorem lrmMechanism_hasMaxCostApproxRatio :
    (lrmMechanism (ι := ι)).HasMaxCostApproxRatio (3 / 2) := by
  rw [Mechanism.hasMaxCostApproxRatio_iff_expectedMaxCost_le (by norm_num)
    lrmMechanism_hasFiniteCost]
  intro x
  rw [expectedMaxCost_lrmMechanism]

private theorem expectedCost_lrm_leftmost (x : ι → ℝ) :
    expectedCost (lrmMechanism x) (leftmost x) = (rightmost x - leftmost x) / 2 := by
  have hle := leftmost_le_rightmost x
  rw [expectedCost_lrmMechanism, center, sub_self, abs_zero,
    abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  ring

private theorem expectedCost_lrm_rightmost (x : ι → ℝ) :
    expectedCost (lrmMechanism x) (rightmost x) = (rightmost x - leftmost x) / 2 := by
  have hle := leftmost_le_rightmost x
  rw [expectedCost_lrmMechanism, center, sub_self, abs_zero,
    abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  ring

/-- **Theorem 3.3** of [ProcacciaTennenholtz2013] (§3.2, pp. 18:9–18:10), incentive part:
`lrmMechanism` is weakly group strategyproof (what Procaccia and Tennenholtz call "group
strategyproof"). -/
theorem lrmMechanism_isWeakGroupStrategyProof [DecidableEq ι] :
    (lrmMechanism (ι := ι)).IsWeakGroupStrategyProof := by
  intro x z A hA
  set x' := A.piecewise z x
  suffices h : ∃ i ∈ A,
      expectedCost (lrmMechanism x) (x i) ≤ expectedCost (lrmMechanism x') (x i) by
    obtain ⟨i, hi, hle⟩ := h
    exact ⟨i, hi, (expectedECost_le_iff_expectedCost_le
      (lrmMechanism_hasFiniteCost x (x i)) (lrmMechanism_hasFiniteCost x' (x i))).mpr hle⟩
  set l := leftmost x
  set r := rightmost x
  set l' := leftmost x'
  set r' := rightmost x'
  have hlr : l ≤ r := leftmost_le_rightmost x
  have hlr' : l' ≤ r' := leftmost_le_rightmost x'
  have hleft_mem : l < l' → ∃ i ∈ A, x i = l := fun _ => by
    obtain ⟨i, hi⟩ := exists_eq_leftmost x
    refine ⟨i, by_contra fun hni => ?_, hi⟩
    linarith [leftmost_le x' i, (Finset.piecewise_eq_of_notMem A z x hni).trans hi]
  have hright_mem : r' < r → ∃ i ∈ A, x i = r := fun _ => by
    obtain ⟨i, hi⟩ := exists_eq_rightmost x
    refine ⟨i, by_contra fun hni => ?_, hi⟩
    linarith [le_rightmost x' i, (Finset.piecewise_eq_of_notMem A z x hni).trans hi]
  have hcL : l ≤ l' → expectedCost (lrmMechanism x') l = (l' + r') / 2 - l := fun _ => by
    rw [expectedCost_lrmMechanism, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
      abs_of_nonpos (by dsimp [center]; linarith)]
    dsimp [center]; ring
  have hcR : r' ≤ r → expectedCost (lrmMechanism x') r = r - (l' + r') / 2 := fun _ => by
    rw [expectedCost_lrmMechanism, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
      abs_of_nonneg (by dsimp [center]; linarith)]
    dsimp [center]; ring
  rcases le_or_gt l' l with hll | hll
  · rcases le_or_gt r r' with hrr | hrr
    · -- Case 1: `l' ≤ l` and `r ≤ r'` (interval expands on both sides).
      obtain ⟨i, hiA⟩ := hA
      refine ⟨i, hiA, ?_⟩
      have hxi_l := leftmost_le x i
      have hxi_r := le_rightmost x i
      rw [expectedCost_lrmMechanism, expectedCost_lrmMechanism,
        abs_of_nonneg (sub_nonneg.mpr hxi_l), abs_of_nonpos (sub_nonpos.mpr hxi_r),
        abs_of_nonneg (a := x i - l') (by linarith),
        abs_of_nonpos (a := x i - r') (by linarith)]
      have hcen_diff : |center x' - center x| ≤ ((l - l') + (r' - r)) / 2 := by
        rw [center, center, abs_le]
        exact ⟨by linarith, by linarith⟩
      change 1 / 4 * (x i - l) + 1 / 4 * -(x i - r) + 1 / 2 * |x i - center x| ≤
        1 / 4 * (x i - l') + 1 / 4 * -(x i - r') + 1 / 2 * |x i - center x'|
      linarith [abs_sub_le (x i) (center x') (center x)]
    · -- Case 3: `l' ≤ l` and `r' < r` (rightmost agent must be in `A` and strictly loses).
      obtain ⟨i, hiA, hxi⟩ := hright_mem hrr
      exact ⟨i, hiA, by rw [hxi, expectedCost_lrm_rightmost, hcR hrr.le]; linarith⟩
  · rcases le_or_gt r r' with hrr | hrr
    · -- Case 2: `l < l'` and `r ≤ r'` (leftmost agent must be in `A` and strictly loses).
      obtain ⟨i, hiA, hxi⟩ := hleft_mem hll
      exact ⟨i, hiA, by rw [hxi, expectedCost_lrm_leftmost, hcL hll.le]; linarith⟩
    · -- Case 4: `l < l'` and `r' < r` (both boundary agents lie in `A`, and their cost sum is
      -- invariant `r - l`, so they cannot both strictly gain).
      obtain ⟨iL, hiLA, hxiL⟩ := hleft_mem hll
      obtain ⟨iR, hiRA, hxiR⟩ := hright_mem hrr
      by_cases hL : expectedCost (lrmMechanism x) (x iL) ≤ expectedCost (lrmMechanism x') (x iL)
      · exact ⟨iL, hiLA, hL⟩
      · refine ⟨iR, hiRA, ?_⟩
        have hsum : expectedCost (lrmMechanism x') (x iL) +
            expectedCost (lrmMechanism x') (x iR) =
            expectedCost (lrmMechanism x) (x iL) + expectedCost (lrmMechanism x) (x iR) := by
          rw [hxiL, hxiR, hcL hll.le, hcR hrr.le, expectedCost_lrm_leftmost,
            expectedCost_lrm_rightmost]
          ring
        linarith

/-- `lrmMechanism` is unilaterally strategyproof. -/
theorem lrmMechanism_isStrategyProof [DecidableEq ι] :
    (lrmMechanism (ι := ι)).IsStrategyProof :=
  lrmMechanism_isWeakGroupStrategyProof.isStrategyProof

/-- Witnessing the §3 remark of [ProcacciaTennenholtz2013] (p. 18:7): for `3 ≤ Fintype.card ι`,
`lrmMechanism` is **not** strongly group strategyproof (`IsGroupStrategyProof`). When one agent is
at `0`, one is at `1`, and the remaining agent(s) are at `1/2`, the grand coalition reporting
`1/2` keeps the two boundary agents' expected costs unchanged at `1/2` while strictly reducing an
interior agent's expected cost from `1/4` to `0`. -/
theorem not_isGroupStrategyProof_lrmMechanism [DecidableEq ι] (hcard : 3 ≤ Fintype.card ι) :
    ¬ (lrmMechanism (ι := ι)).IsGroupStrategyProof := by
  intro hgsp
  obtain ⟨i₁, i₂, h12⟩ := Fintype.one_lt_card_iff.mp (lt_of_lt_of_le (by decide) hcard)
  have hcard_lt : ({i₁, i₂} : Finset ι).card < (Finset.univ : Finset ι).card :=
    lt_of_le_of_lt Finset.card_le_two (by rw [Finset.card_univ]; omega)
  obtain ⟨i₃, _, hi₃⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi₃
  let x : ι → ℝ := fun j => if j = i₁ then 0 else if j = i₂ then 1 else 1 / 2
  let z : ι → ℝ := fun _ => 1 / 2
  have hx : leftmost x = 0 ∧ rightmost x = 1 :=
    leftmost_rightmost_two_plus_mid h12 (by norm_num) (by norm_num)
  have hz : leftmost z = 1 / 2 ∧ rightmost z = 1 / 2 :=
    leftmost_rightmost_of_bounds (i₀ := i₁) (i₁ := i₁) rfl rfl fun _ => ⟨le_rfl, le_rfl⟩
  have hcen_x : center x = 1 / 2 := by rw [center, hx.1, hx.2]; norm_num
  have hcen_z : center z = 1 / 2 := by rw [center, hz.1, hz.2]; norm_num
  refine hgsp x z Finset.univ ⟨fun j _ => ?_, i₃, Finset.mem_univ i₃, ?_⟩
  · rw [Finset.piecewise_univ, expectedECost_le_iff_expectedCost_le
      (lrmMechanism_hasFiniteCost z (x j)) (lrmMechanism_hasFiniteCost x (x j)),
      expectedCost_lrmMechanism, expectedCost_lrmMechanism, hx.1, hx.2, hcen_x, hz.1, hz.2, hcen_z]
    by_cases hj1 : j = i₁ <;> by_cases hj2 : j = i₂ <;> simp [x, hj1, hj2, h12.symm] <;> norm_num
  · rw [Finset.piecewise_univ, expectedECost_lt_iff_expectedCost_lt
      (lrmMechanism_hasFiniteCost z (x i₃)) (lrmMechanism_hasFiniteCost x (x i₃)),
      expectedCost_lrmMechanism, expectedCost_lrmMechanism, hx.1, hx.2, hcen_x, hz.1, hz.2, hcen_z]
    simp [x, hi₃.1, hi₃.2]; norm_num

omit [Nonempty ι] in
/-- **Theorem 3.4** of [ProcacciaTennenholtz2013] (§3.2, p. 18:10): for `2 ≤ Fintype.card ι`, every
randomized strategyproof mechanism `M : Mechanism ι ℝ` has maximum-cost approximation ratio at
least `3 / 2`. -/
theorem three_halves_le_of_isStrategyProof [DecidableEq ι] (hcard : 2 ≤ Fintype.card ι)
    {M : Mechanism ι ℝ} (hsp : M.IsStrategyProof)
    {α : ℝ} (happrox : M.HasMaxCostApproxRatio α) :
    3 / 2 ≤ α := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide) hcard)
  have hfin : ∀ w : ι → ℝ, HasFiniteCost (M w) := happrox.hasFiniteCost
  have hsp_real := (Mechanism.isStrategyProof_iff_expectedCost_le hfin).mp hsp
  have happrox_real := (Mechanism.hasMaxCostApproxRatio_iff_expectedMaxCost_le
    (zero_le_one.trans (happrox.one_le hcard)) hfin).mp happrox
  obtain ⟨i₁, i₂, h12⟩ := Fintype.one_lt_card_iff.mp hcard
  let x : ι → ℝ := fun j => if j = i₁ then 0 else if j = i₂ then 1 else 1 / 2
  have hhalf := exists_expectedCost_ge_half_dist (hfin x) (0 : ℝ) 1
  rw [show dist (0 : ℝ) 1 / 2 = 1 / 2 by rw [Real.dist_eq]; norm_num] at hhalf
  have hdev (i : ι) (z : ℝ) {c l r : ℝ}
      (hx' : leftmost (Function.update x i z) = l ∧ rightmost (Function.update x i z) = r)
      (hxi : x i = c) (hge : 1 / 2 ≤ expectedCost (M x) c)
      (hlr : r - l = 2 ∧ (l + r) / 2 = c) : 3 / 2 ≤ α := by
    set x' := Function.update x i z
    have hsp' : expectedCost (M x) c ≤ expectedCost (M x') c := hxi ▸ hsp_real x i z
    have hmc := expectedMaxCost_eq_expectedCost_center_add (hfin x') x'
    have hbd := happrox_real x'
    rw [center, optMaxCost_real_eq, hx'.1, hx'.2, hlr.1, hlr.2] at hmc
    rw [optMaxCost_real_eq, hx'.1, hx'.2, hlr.1] at hbd
    linarith
  rcases hhalf with h0 | h1
  · -- `1/2 ≤ expectedCost (M x) 0`: deviate agent `i₁` from `0` to `-1` (center `0`, opt `1`).
    refine hdev i₁ (-1) (leftmost_rightmost_update_first h12 ?_ ?_) (by simp [x]) h0 ?_
    all_goals norm_num
  · -- `1/2 ≤ expectedCost (M x) 1`: deviate agent `i₂` from `1` to `2` (center `1`, opt `1`).
    refine hdev i₂ 2 (leftmost_rightmost_update_second h12 ?_ ?_) (by simp [x, h12.symm]) h1 ?_
    all_goals norm_num

end RealMaxCost

end Cslib.GameTheory.FacilityLocation
