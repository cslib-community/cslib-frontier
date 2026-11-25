/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Congestion.Nonatomic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# Priced Wardrop equilibria, Pigovian tolls, and monopoly efficiency

In a communication network with congestion externalities and per-unit bandwidth prices `p i`,
nonatomic end users route up to `d` units of flow across parallel links `Link` along paths of
minimum effective cost `latency i (x i) + p i`, declining to transmit when the minimum effective
cost exceeds their reservation utility `R` ([Ozdaglar and Srikant, Section 22.2.2,
Eq. (22.22), p. 581][OzdaglarSrikant2007]).

When all `d` units are routed, a priced Wardrop equilibrium coincides with an ordinary Wardrop
equilibrium of `Cslib.GameTheory.NonatomicCongestionGame` under effective latencies
`latency i · + p i`. Minimizing Beckmann's convex potential over the compact feasible simplex
yields existence of a priced Wardrop equilibrium for every price vector and continuous latency
family.

For smooth convex nondecreasing latencies with `latency i 0 = 0`:

1. **Pigovian marginal-congestion pricing** ([Ozdaglar and Srikant, Section 22.2.2, Eq. (22.24),
   p. 581][OzdaglarSrikant2007]): charging `pigovianPrice latencyDeriv xS i = xS i *
   latencyDeriv i (xS i)` decentralizes every social-surplus-maximizing flow `xS` when full demand
   `d` is routed.
2. **Monopoly efficiency** ([Ozdaglar and Srikant, Section 22.2.3, p. 582][OzdaglarSrikant2007];
   [Acemoglu and Ozdaglar, Proposition 3.2, p. 7][AcemogluOzdaglar2007MOR]): a flow vector `x` is
   supported by a two-stage Monopoly Equilibrium `(p, x)` if and only if `x` maximizes social
   surplus, and at every Monopoly Equilibrium active links charge `p i = R - latency i (x i)`,
   extracting all consumer surplus.

## Main definitions

* `Cslib.GameTheory.pricedParallelCongestionGame`: parallel-link `NonatomicCongestionGame` with
  effective latencies `latency i u + p i`.
* `Cslib.GameTheory.IsFeasiblePricedFlow`, `IsPricedWardrop`: feasible flows with elastic cutoff at
  demand `d` and priced Wardrop equilibria ([OzdaglarSrikant2007], Eq. (22.22), p. 581).
* `Cslib.GameTheory.socialSurplus`, `consumerSurplus`, `monopolyProfit`, `IsSocialOptimum`:
  welfare and revenue functionals ([OzdaglarSrikant2007], Eqs. (22.23), (22.25), pp. 581–582).
* `Cslib.GameTheory.SmoothConvexLatencies`: standard regularity bundle (zero latency at zero flow,
  monotone, convex, differentiable on `[0, ∞)`).
* `Cslib.GameTheory.pigovianPrice`: marginal-congestion toll `x i * latencyDeriv i (x i)`.
* `Cslib.GameTheory.IsMonopolyEquilibrium`: two-stage Monopoly Equilibrium ([OzdaglarSrikant2007],
  Section 22.2.3, p. 582; [AcemogluOzdaglar2007MOR], Definition 3.1, p. 7).

## Main results

* `Cslib.GameTheory.isPricedWardrop_iff_isWardrop_of_sum_eq`: equivalence with
  `NonatomicCongestionGame.IsWardrop` when full demand `d` is routed.
* `Cslib.GameTheory.exists_isPricedWardrop`: existence of a priced Wardrop equilibrium for
  continuous latencies.
* `Cslib.GameTheory.exists_isSocialOptimum`: existence of a social-surplus-maximizing flow.
* `Cslib.GameTheory.SmoothConvexLatencies.isSocialOptimum_iff_kkt`: first-order KKT
  characterization of social optima.
* `Cslib.GameTheory.SmoothConvexLatencies.isPricedWardrop_pigovianPrice_of_sum_eq`: Pigovian
  marginal-congestion tolls decentralize full-demand social optima ([OzdaglarSrikant2007],
  Eq. (22.24), p. 581).
* `Cslib.GameTheory.IsMonopolyEquilibrium.price_eq_sub_latency`,
  `Cslib.GameTheory.IsMonopolyEquilibrium.consumerSurplus_eq_zero`,
  `Cslib.GameTheory.exists_isMonopolyEquilibrium_iff_isSocialOptimum`: Acemoglu–Ozdaglar monopoly
  efficiency and full surplus extraction ([AcemogluOzdaglar2007MOR], Proposition 3.2, p. 7).

## References

* [AcemogluOzdaglar2007MOR]
* [OzdaglarSrikant2007]
-/

public section

namespace Cslib.GameTheory

section Definitions

/-- The single-commodity parallel-link `NonatomicCongestionGame` routing `d` units of traffic across
`Link` under effective latencies `latency i u + p i`. -/
@[expose] def pricedParallelCongestionGame {Link : Type*} (d : ℝ) (latency : Link → ℝ → ℝ)
    (p : Link → ℝ) : NonatomicCongestionGame Unit Link Link where
  commodity _ := ()
  resources i := {i}
  rate _ := d
  latency i u := latency i u + p i

variable {Link : Type*} [Fintype Link]

@[simp]
theorem edgeFlow_pricedParallelCongestionGame [DecidableEq Link] (d : ℝ) (latency : Link → ℝ → ℝ)
    (p f : Link → ℝ) (i : Link) :
    (pricedParallelCongestionGame d latency p).edgeFlow f i = f i := by
  simp only [pricedParallelCongestionGame, NonatomicCongestionGame.edgeFlow,
    Finset.mem_singleton, Finset.sum_filter]
  simp

@[simp]
theorem pathLatency_pricedParallelCongestionGame [DecidableEq Link] (d : ℝ)
    (latency : Link → ℝ → ℝ) (p f : Link → ℝ) (i : Link) :
    (pricedParallelCongestionGame d latency p).pathLatency f i = latency i (f i) + p i := by
  simp only [NonatomicCongestionGame.pathLatency, edgeFlow_pricedParallelCongestionGame]
  simp [pricedParallelCongestionGame]

/-- A link flow `x` is **feasible** up to total demand `d` when link flows are nonnegative and sum
to at most `d`. -/
@[expose] def IsFeasiblePricedFlow (d : ℝ) (x : Link → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ d

/-- A **priced Wardrop equilibrium** at price vector `p` with demand `d` and reservation utility `R`
([Ozdaglar and Srikant, Section 22.2.2, Eq. (22.22), p. 581][OzdaglarSrikant2007]): active links
minimize effective cost `latency i (x i) + p i`, never exceed `R`, and route all `d` units whenever
some link has effective cost strictly below `R`. -/
@[expose] def IsPricedWardrop (d R : ℝ) (latency : Link → ℝ → ℝ) (p x : Link → ℝ) : Prop :=
  IsFeasiblePricedFlow d x ∧
    (∀ i j, 0 < x i → latency i (x i) + p i ≤ latency j (x j) + p j) ∧
    (∀ i, 0 < x i → latency i (x i) + p i ≤ R) ∧
    ((∃ j, latency j (x j) + p j < R) → ∑ i, x i = d)

/-- **Social surplus** `∑ i, (R - latency i (x i)) * x i` ([Ozdaglar and Srikant, Eq. (22.25),
p. 582][OzdaglarSrikant2007]). -/
@[expose] def socialSurplus (R : ℝ) (latency : Link → ℝ → ℝ) (x : Link → ℝ) : ℝ :=
  ∑ i, (R - latency i (x i)) * x i

/-- **Consumer surplus** `∑ i, (R - latency i (x i) - p i) * x i` ([Ozdaglar and Srikant,
Section 22.2.1, Footnote 3, p. 580][OzdaglarSrikant2007]; [Acemoglu and Ozdaglar, Section 3,
p. 8][AcemogluOzdaglar2007MOR]). -/
@[expose] def consumerSurplus (R : ℝ) (latency : Link → ℝ → ℝ) (p x : Link → ℝ) : ℝ :=
  ∑ i, (R - latency i (x i) - p i) * x i

/-- Total **monopoly profit** `∑ i, p i * x i` across all links ([Ozdaglar and Srikant,
Section 22.2.3, p. 582][OzdaglarSrikant2007]). -/
@[expose] def monopolyProfit (p x : Link → ℝ) : ℝ :=
  ∑ i, p i * x i

/-- A flow `xS` is a **social optimum** if it maximizes `socialSurplus R latency` over feasible
flows ([Ozdaglar and Srikant, Eq. (22.23), p. 581][OzdaglarSrikant2007]). -/
@[expose] def IsSocialOptimum (d R : ℝ) (latency : Link → ℝ → ℝ) (xS : Link → ℝ) : Prop :=
  IsFeasiblePricedFlow d xS ∧
    ∀ y, IsFeasiblePricedFlow d y → socialSurplus R latency y ≤ socialSurplus R latency xS

/-- **Pigovian marginal-congestion price** `x i * latencyDeriv i (x i)` ([Ozdaglar and Srikant,
Section 22.2.2, Eq. (22.24), p. 581][OzdaglarSrikant2007]). -/
@[expose] def pigovianPrice (latencyDeriv : Link → ℝ → ℝ) (x : Link → ℝ) (i : Link) : ℝ :=
  x i * latencyDeriv i (x i)

/-- A **Monopoly Equilibrium** `(p, x)` of the two-stage dynamic pricing-congestion game ([Ozdaglar
and Srikant, Section 22.2.3, p. 582][OzdaglarSrikant2007]; [Acemoglu and Ozdaglar, Definition 3.1,
p. 7][AcemogluOzdaglar2007MOR]): prices and flows are nonnegative, `x` is a priced Wardrop
equilibrium at `p`, and no nonnegative price vector `p'` and equilibrium flow `x'` at `p'` yields
strictly higher monopoly profit. -/
@[expose] def IsMonopolyEquilibrium (d R : ℝ) (latency : Link → ℝ → ℝ) (p x : Link → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧
    IsPricedWardrop d R latency p x ∧
    ∀ p' x', (∀ i, 0 ≤ p' i) → IsPricedWardrop d R latency p' x' →
      monopolyProfit p' x' ≤ monopolyProfit p x

/-- Standard smoothness, monotonicity, convexity, and zero-base-delay assumptions on link latency
functions ([Ozdaglar and Srikant, Section 22.2.2, p. 581][OzdaglarSrikant2007]). -/
structure SmoothConvexLatencies {Link : Type*} (latency latencyDeriv : Link → ℝ → ℝ) : Prop where
  zero_at_zero : ∀ i, latency i 0 = 0
  monotoneOn : ∀ i, MonotoneOn (latency i) (Set.Ici 0)
  convexOn : ∀ i, ConvexOn ℝ (Set.Ici 0) (latency i)
  hasDerivAt : ∀ i x, 0 ≤ x → HasDerivAt (latency i) (latencyDeriv i x) x

end Definitions

section BasicProperties

variable {Link : Type*} [Fintype Link]

/-- Splitting off an updated coordinate `k ∈ s` from `∑ m ∈ s, f m (Function.update y k v m)`. -/
private theorem sum_apply_update_of_mem {ι : Type*} [DecidableEq ι] (f : ι → ℝ → ℝ)
    {s : Finset ι} (y : ι → ℝ) {k : ι} (v : ℝ) (hk : k ∈ s) :
    ∑ m ∈ s, f m (Function.update y k v m) = f k v + ∑ m ∈ s.erase k, f m (y m) := by
  rw [← Finset.add_sum_erase _ _ hk, Function.update_self]
  exact congrArg _ (Finset.sum_congr rfl fun m hm => by
    rw [Function.update_of_ne (Finset.mem_erase.mp hm).1])

/-- Adding `t` units of flow to link `i` increases total flow by `t`. -/
theorem sum_update_add_eq [DecidableEq Link] (x : Link → ℝ) (i : Link) (t : ℝ) :
    ∑ k, Function.update x i (x i + t) k = (∑ k, x k) + t := by
  rw [sum_apply_update_of_mem (fun _ u => u) x _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  ring

/-- Adding `t ≥ 0` units of flow to link `j` preserves feasibility when `(∑ k, x k) + t ≤ d`. -/
theorem isFeasiblePricedFlow_update_add [DecidableEq Link] {d : ℝ} {x : Link → ℝ}
    (hx : IsFeasiblePricedFlow d x) {j : Link} {t : ℝ} (ht0 : 0 ≤ t)
    (htd : (∑ k, x k) + t ≤ d) :
    IsFeasiblePricedFlow d (Function.update x j (x j + t)) := by
  refine ⟨fun k => ?_, (sum_update_add_eq x j t).trans_le htd⟩
  by_cases hkj : k = j
  · subst hkj; simp only [Function.update_self]; linarith [hx.1 k]
  · simp only [Function.update_of_ne hkj]; exact hx.1 k

/-- Splitting a filtered sum at `i` when `f` and `g` agree on all other elements satisfying
`own`. -/
theorem sum_filter_eq_add_erase [DecidableEq Link] (own : Link → Prop) [DecidablePred own]
    {i : Link} (hi : own i) (f g : Link → ℝ) (hfg : ∀ m, own m → m ≠ i → f m = g m) :
    ∑ m with own m, f m = f i + ∑ m ∈ (Finset.univ.filter own).erase i, g m := by
  have hmem : i ∈ Finset.univ.filter own := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  rw [← Finset.add_sum_erase _ _ hmem]
  congr 1
  exact Finset.sum_congr rfl fun m hm =>
    hfg m (Finset.mem_filter.mp (Finset.mem_erase.mp hm).2).2 (Finset.mem_erase.mp hm).1

/-- Redistributing signed steps `step q` across `q ∈ S` (`i ∉ S`) balanced by `-∑ q ∈ S, step q` on
link `i`. -/
@[expose] def flowShift {ι : Type*} [DecidableEq ι] (i : ι) (S : Finset ι) (step x : ι → ℝ)
    (k : ι) : ℝ :=
  if k = i then x i - ∑ q ∈ S, step q else if k ∈ S then x k + step k else x k

/-- `flowShift` preserves total network flow whenever `i ∉ S`. -/
theorem sum_flowShift_eq [DecidableEq Link] {i : Link} {S : Finset Link} (hi : i ∉ S)
    (step x : Link → ℝ) :
    ∑ k, flowShift i S step x k = ∑ k, x k := by
  have h1 : ∀ k, flowShift i S step x k =
      x k + (if k = i then -∑ q ∈ S, step q else if k ∈ S then step k else 0) := fun k => by
    by_cases hki : k = i
    · subst hki; simp only [flowShift, ↓reduceIte]; ring
    · by_cases hkS : k ∈ S <;> simp [flowShift, hki, hkS]
  have hzero : ∑ k : Link, (if k = i then -∑ q ∈ S, step q else if k ∈ S then step k else 0) =
      0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [↓reduceIte]
    have hrest : ∑ k ∈ Finset.univ.erase i,
        (if k = i then -∑ q ∈ S, step q else if k ∈ S then step k else 0) =
        ∑ q ∈ S, step q := by
      rw [← Finset.sum_subset (fun q hq => Finset.mem_erase.mpr
        ⟨fun (h : q = i) => hi (h ▸ hq), Finset.mem_univ q⟩)]
      · exact Finset.sum_congr rfl fun q hq => by
          have hne : q ≠ i := fun h => hi (h ▸ hq)
          simp [hne, hq]
      · intro k hk hkS
        simp [(Finset.mem_erase.mp hk).1, hkS]
    rw [hrest]
    ring
  simp [h1, Finset.sum_add_distrib, hzero]

/-- `flowShift` preserves coordinatewise nonnegativity when `∑ q ∈ S, step q ≤ x i` and
`0 ≤ x q + step q` on `S`. -/
theorem nonneg_flowShift {ι : Type*} [DecidableEq ι] {i : ι} {S : Finset ι} {step x : ι → ℝ}
    (hx : ∀ k, 0 ≤ x k) (hi : ∑ q ∈ S, step q ≤ x i) (hS : ∀ q ∈ S, 0 ≤ x q + step q)
    (k : ι) :
    0 ≤ flowShift i S step x k := by
  simp only [flowShift]
  split_ifs with hki hkS
  · linarith
  · exact hS k hkS
  · exact hx k

/-- Shifting `t` units of flow from link `i` to a distinct link `j` preserves total flow. -/
theorem sum_update_sub_add_eq [DecidableEq Link] (x : Link → ℝ) {i j : Link} (hij : i ≠ j)
    (t : ℝ) :
    ∑ k, Function.update (Function.update x i (x i - t)) j (x j + t) k = ∑ k, x k := by
  have hi : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
  rw [sum_apply_update_of_mem (fun _ u => u) _ _ (Finset.mem_univ j),
    sum_apply_update_of_mem (fun _ u => u) x _ hi, ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ _ hi]
  ring

/-- Shifting `t ∈ [0, x i]` units of flow from link `i` to `j` preserves coordinatewise
nonnegativity. -/
theorem nonneg_update_sub_add {ι : Type*} [DecidableEq ι] {x : ι → ℝ} (hx : ∀ k, 0 ≤ x k)
    {i j : ι} {t : ℝ} (ht0 : 0 ≤ t) (hti : t ≤ x i) (k : ι) :
    0 ≤ Function.update (Function.update x i (x i - t)) j (x j + t) k := by
  simp only [Function.update_apply]
  split_ifs <;> linarith [hx k, hx j]

/-- Social surplus decomposes into consumer surplus plus monopoly profit. -/
theorem socialSurplus_eq_consumerSurplus_add_monopolyProfit (R : ℝ) (latency : Link → ℝ → ℝ)
    (p x : Link → ℝ) :
    socialSurplus R latency x = consumerSurplus R latency p x + monopolyProfit p x := by
  simp only [socialSurplus, consumerSurplus, monopolyProfit, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- When full demand `d` is routed and active links satisfy the reservation ceiling `R`, priced
Wardrop equilibrium coincides with `NonatomicCongestionGame.IsWardrop` under effective latencies
`latency i u + p i`. -/
theorem isPricedWardrop_iff_isWardrop_of_sum_eq [DecidableEq Link] {d R : ℝ}
    {latency : Link → ℝ → ℝ} {p x : Link → ℝ} (hsum : ∑ i, x i = d)
    (hR : ∀ i, 0 < x i → latency i (x i) + p i ≤ R) :
    IsPricedWardrop d R latency p x ↔
      (pricedParallelCongestionGame d latency p).IsWardrop x := by
  constructor
  · intro hw
    refine ⟨⟨hw.1.1, fun k => ?_⟩, fun i j _ hi => ?_⟩
    · cases k
      simpa [pricedParallelCongestionGame] using hsum
    · simpa using hw.2.1 i j hi
  · intro hw
    refine ⟨⟨hw.1.1, hsum.le⟩, fun i j hi => ?_, hR, fun _ => hsum⟩
    simpa using hw.2 i j rfl hi

/-- Any two links carrying positive flow at a priced Wardrop equilibrium have equal effective
cost. -/
theorem IsPricedWardrop.effectiveCost_eq_of_pos {d R : ℝ} {latency : Link → ℝ → ℝ}
    {p x : Link → ℝ} (hw : IsPricedWardrop d R latency p x) {i j : Link}
    (hi : 0 < x i) (hj : 0 < x j) :
    latency i (x i) + p i = latency j (x j) + p j :=
  le_antisymm (hw.2.1 i j hi) (hw.2.1 j i hj)

/-- If total routed flow is strictly less than demand `d`, every link's effective cost at a priced
Wardrop equilibrium is at least `R`. -/
theorem IsPricedWardrop.le_effectiveCost_of_sum_lt {d R : ℝ} {latency : Link → ℝ → ℝ}
    {p x : Link → ℝ} (hw : IsPricedWardrop d R latency p x) (hlt : ∑ i, x i < d) (j : Link) :
    R ≤ latency j (x j) + p j := by
  by_contra h
  exact hlt.ne (hw.2.2.2 ⟨j, lt_of_not_ge h⟩)

/-- If total routed flow is strictly less than demand `d`, every active link at a priced Wardrop
equilibrium has effective cost equal to `R`. -/
theorem IsPricedWardrop.effectiveCost_eq_R_of_sum_lt {d R : ℝ} {latency : Link → ℝ → ℝ}
    {p x : Link → ℝ} (hw : IsPricedWardrop d R latency p x) (hlt : ∑ i, x i < d) {i : Link}
    (hi : 0 < x i) :
    latency i (x i) + p i = R :=
  le_antisymm (hw.2.2.1 i hi) (hw.le_effectiveCost_of_sum_lt hlt i)

/-- Consumer surplus is nonnegative at any priced Wardrop equilibrium. -/
theorem IsPricedWardrop.consumerSurplus_nonneg {d R : ℝ} {latency : Link → ℝ → ℝ} {p x : Link → ℝ}
    (hw : IsPricedWardrop d R latency p x) :
    0 ≤ consumerSurplus R latency p x := by
  refine Finset.sum_nonneg fun i _ => ?_
  rcases (hw.1.1 i).eq_or_lt with hxi | hxi
  · simp [← hxi]
  · have hsub : 0 ≤ R - latency i (x i) - p i := by linarith [hw.2.2.1 i hxi]
    exact mul_nonneg hsub hxi.le

/-- Social surplus is nonnegative at any priced Wardrop equilibrium with nonnegative prices. -/
theorem IsPricedWardrop.socialSurplus_nonneg {d R : ℝ} {latency : Link → ℝ → ℝ} {p x : Link → ℝ}
    (hw : IsPricedWardrop d R latency p x) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ socialSurplus R latency x := by
  rw [socialSurplus_eq_consumerSurplus_add_monopolyProfit R latency p x]
  exact add_nonneg hw.consumerSurplus_nonneg
    (Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hw.1.1 i))

end BasicProperties

namespace SmoothConvexLatencies

variable {Link : Type*} {latency latencyDeriv : Link → ℝ → ℝ}

theorem latency_nonneg (h : SmoothConvexLatencies latency latencyDeriv) (i : Link) {x : ℝ}
    (hx : 0 ≤ x) : 0 ≤ latency i x := by
  rw [← h.zero_at_zero i]
  exact h.monotoneOn i (le_rfl : (0 : ℝ) ∈ Set.Ici 0) hx hx

theorem continuousOn (h : SmoothConvexLatencies latency latencyDeriv) (i : Link) :
    ContinuousOn (latency i) (Set.Ici 0) :=
  fun x hx => (h.hasDerivAt i x hx).continuousAt.continuousWithinAt

theorem latencyDeriv_nonneg (h : SmoothConvexLatencies latency latencyDeriv) (i : Link) {x : ℝ}
    (hx : 0 ≤ x) : 0 ≤ latencyDeriv i x := by
  have hnotMem : x ∉ Set.Ioi x := lt_irrefl x
  have hslope : Filter.Tendsto (slope (latency i) x) (nhdsWithin x (Set.Ioi x))
      (nhds (latencyDeriv i x)) :=
    (hasDerivWithinAt_iff_tendsto_slope' hnotMem).mp (h.hasDerivAt i x hx).hasDerivWithinAt
  refine ge_of_tendsto hslope ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards with t ht
  rw [Set.mem_Ioi] at ht
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr (h.monotoneOn i hx (hx.trans ht.le) ht.le)) (sub_pos.mpr ht).le

/-- First-order supporting-hyperplane inequality for a smooth convex latency function on
`[0, ∞)`. -/
theorem add_deriv_mul_le (h : SmoothConvexLatencies latency latencyDeriv) (i : Link) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    latency i x + latencyDeriv i x * (y - x) ≤ latency i y := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hslope := (h.convexOn i).le_slope_of_hasDerivAt hx hy hxy (h.hasDerivAt i x hx)
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at hslope
    linarith
  · simp
  · have hslope := (h.convexOn i).slope_le_of_hasDerivAt hy hx hyx (h.hasDerivAt i x hx)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hyx)] at hslope
    linarith

/-- Convexity and `latency i 0 = 0` imply `latency i x ≤ x * latencyDeriv i x` for `x ≥ 0`. -/
theorem latency_le_mul_deriv (h : SmoothConvexLatencies latency latencyDeriv) (i : Link) {x : ℝ}
    (hx : 0 ≤ x) :
    latency i x ≤ x * latencyDeriv i x := by
  have h0 := h.add_deriv_mul_le i hx le_rfl
  rw [h.zero_at_zero i] at h0
  linarith

/-- If `latency i x > 0` for `x ≥ 0`, then both `x > 0` and `latencyDeriv i x > 0`. -/
theorem deriv_pos_of_latency_pos (h : SmoothConvexLatencies latency latencyDeriv) (i : Link)
    {x : ℝ} (hx : 0 ≤ x) (hpos : 0 < latency i x) :
    0 < x ∧ 0 < latencyDeriv i x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    linarith [h.zero_at_zero i]
  have hxpos : 0 < x := lt_of_le_of_ne hx hx0.symm
  have hle := h.latency_le_mul_deriv i hx
  exact ⟨hxpos, pos_of_mul_pos_right (lt_of_lt_of_le hpos hle) hx⟩

/-- Concavity inequality for single-link social surplus `(R - latency i y) * y`. -/
theorem term_surplus_le_add_marginal (h : SmoothConvexLatencies latency latencyDeriv) (R : ℝ)
    (i : Link) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (R - latency i y) * y ≤
      (R - latency i x) * x + (R - latency i x - x * latencyDeriv i x) * (y - x) := by
  have htan := h.add_deriv_mul_le i hx hy
  have hd := h.latencyDeriv_nonneg i hx
  have hmul : y * (latency i x + latencyDeriv i x * (y - x)) ≤ y * latency i y :=
    mul_le_mul_of_nonneg_left htan hy
  have hsq : 0 ≤ latencyDeriv i x * (y - x) ^ 2 := mul_nonneg hd (sq_nonneg _)
  nlinarith

end SmoothConvexLatencies

section ExistenceAndPigou

variable {Link : Type*} [Fintype Link]

/-- The set `{x : Link → ℝ | IsFeasiblePricedFlow d x}` of feasible priced flows is compact. -/
theorem isCompact_feasiblePricedFlows {d : ℝ} :
    IsCompact {x : Link → ℝ | IsFeasiblePricedFlow d x} := by
  classical
  by_cases hd : 0 ≤ d
  · have hsub : {x : Link → ℝ | IsFeasiblePricedFlow d x} ⊆
        Set.pi Set.univ fun _ => Set.Icc 0 d := fun x hx i _ =>
      ⟨hx.1 i, (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2⟩
    have hclosed : IsClosed {x : Link → ℝ | IsFeasiblePricedFlow d x} :=
      (isClosed_Ici (a := (0 : Link → ℝ))).inter
        (isClosed_le (continuous_finsetSum Finset.univ fun i _ => continuous_apply i)
          continuous_const)
    exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hclosed hsub
  · rw [Set.eq_empty_of_forall_notMem (s := {x : Link → ℝ | IsFeasiblePricedFlow d x})
      fun x hx => hd ((Finset.sum_nonneg fun i _ => hx.1 i).trans hx.2)]
    exact isCompact_empty

/-- A one-sided derivative inequality along `t ∈ (0, δ)` implies `0 ≤ g'`. -/
theorem nonneg_of_hasDerivAt_of_forall_pos {g : ℝ → ℝ} {g' δ : ℝ} (hδ : 0 < δ)
    (hd : HasDerivAt g g' 0) (hle : ∀ t, 0 < t → t < δ → g 0 ≤ g t) :
    0 ≤ g' := by
  have hnotMem : (0 : ℝ) ∉ Set.Ioi (0 : ℝ) := lt_irrefl 0
  have hslope : Filter.Tendsto (slope g 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds g') :=
    (hasDerivWithinAt_iff_tendsto_slope' hnotMem).mp hd.hasDerivWithinAt
  refine ge_of_tendsto hslope ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [eventually_lt_nhds hδ] with t ht1 ht2
  rw [Set.mem_Ioi] at ht2
  rw [slope_def_field, sub_zero]
  exact div_nonneg (sub_nonneg.mpr (hle t ht2 ht1)) ht2.le

/-- **Existence of a priced Wardrop equilibrium** via Beckmann's convex potential: for any `0 ≤ d`,
reservation utility `R`, price vector `p`, and latencies continuous on `[0, ∞)`, there exists a
priced Wardrop equilibrium `x`. -/
theorem exists_isPricedWardrop {d R : ℝ} {latency : Link → ℝ → ℝ}
    (hl : ∀ i, ContinuousOn (latency i) (Set.Ici 0)) (hd : 0 ≤ d) (p : Link → ℝ) :
    ∃ x, IsPricedWardrop d R latency p x := by
  classical
  let extLat : Link → ℝ → ℝ := fun i u => latency i (max 0 u)
  have hextCont : ∀ i, Continuous (extLat i) := fun i =>
    (hl i).comp_continuous (continuous_const.max continuous_id) fun u => le_max_left 0 u
  let potTerm : Link → ℝ → ℝ := fun i u =>
    (∫ t in (0 : ℝ)..u, extLat i t) + (p i - R) * u
  have hpotDeriv : ∀ i u, HasDerivAt (potTerm i) (extLat i u + (p i - R)) u := fun i u => by
    have hint : HasDerivAt (fun w => ∫ t in (0 : ℝ)..w, extLat i t) (extLat i u) u :=
      intervalIntegral.integral_hasDerivAt_right ((hextCont i).intervalIntegrable _ _)
        (hextCont i).aestronglyMeasurable.stronglyMeasurableAtFilter (hextCont i).continuousAt
    have hlin : HasDerivAt (fun w => (p i - R) * w) (p i - R) u := by
      simpa only [mul_one] using (hasDerivAt_id' u).const_mul (p i - R)
    exact hint.add hlin
  have hpotTermCont : ∀ i, Continuous (potTerm i) := fun i =>
    continuous_iff_continuousAt.mpr fun u => (hpotDeriv i u).continuousAt
  let pot : (Link → ℝ) → ℝ := fun x => ∑ i, potTerm i (x i)
  have hpotCont : Continuous pot :=
    continuous_finsetSum Finset.univ fun i _ => (hpotTermCont i).comp (continuous_apply i)
  have hne : ({x : Link → ℝ | IsFeasiblePricedFlow d x}).Nonempty :=
    ⟨0, fun _ => le_rfl, by simp [hd]⟩
  obtain ⟨x, hxFeas, hxMin⟩ :=
    isCompact_feasiblePricedFlows.exists_isMinOn hne hpotCont.continuousOn
  have hext : ∀ k, extLat k (x k) = latency k (x k) := fun k => by
    simp only [extLat, max_eq_right (hxFeas.1 k)]
  have hsub : ∀ k, HasDerivAt (fun t => potTerm k (x k - t)) (-(latency k (x k) + (p k - R))) 0 :=
    fun k => by simpa only [sub_zero, hext, mul_neg, mul_one, Function.comp_def] using
      (hpotDeriv k (x k - 0)).comp 0 ((hasDerivAt_id' (0 : ℝ)).const_sub (x k))
  have hadd : ∀ k, HasDerivAt (fun t => potTerm k (x k + t)) (latency k (x k) + (p k - R)) 0 :=
    fun k => by simpa only [add_zero, hext, mul_one, Function.comp_def] using
      (hpotDeriv k (x k + 0)).comp 0 ((hasDerivAt_id' (0 : ℝ)).const_add (x k))
  refine ⟨x, hxFeas, ?_, ?_, ?_⟩
  · intro i j hi
    by_cases hij : i = j
    · subst hij; exact le_rfl
    have hcurve : HasDerivAt (fun t => pot (Function.update (Function.update x i (x i - t)) j
        (x j + t))) ((latency j (x j) + p j) - (latency i (x i) + p i)) 0 := by
      simp only [pot, sum_apply_update_of_mem potTerm _ _ (Finset.mem_univ j),
        sum_apply_update_of_mem potTerm x _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)]
      convert (hadd j).add ((hsub i).add_const
        (∑ k ∈ (Finset.univ.erase j).erase i, potTerm k (x k))) using 1
      ring
    have hnonneg := nonneg_of_hasDerivAt_of_forall_pos hi hcurve fun t ht0 hti => by
      simp only [sub_zero, add_zero, Function.update_eq_self]
      exact hxMin ⟨fun k => nonneg_update_sub_add hxFeas.1 ht0.le hti.le k,
        (sum_update_sub_add_eq x hij t).trans_le hxFeas.2⟩
    linarith
  · intro i hi
    have hcurve : HasDerivAt (fun t => pot (Function.update x i (x i - t)))
        (-(latency i (x i) + (p i - R))) 0 := by
      simp only [pot, sum_apply_update_of_mem potTerm x _ (Finset.mem_univ i)]
      exact (hsub i).add_const _
    have hnonneg := nonneg_of_hasDerivAt_of_forall_pos hi hcurve fun t ht0 hti => by
      simp only [sub_zero, Function.update_eq_self]
      have hsum := sum_update_add_eq x i (-t)
      simp only [← sub_eq_add_neg] at hsum
      exact hxMin ⟨fun k => by
        simp only [Function.update_apply]; split_ifs <;> linarith [hxFeas.1 k],
        by linarith [hxFeas.2]⟩
    linarith
  · rintro ⟨j, hj⟩
    by_contra hne_d
    have hcurve : HasDerivAt (fun t => pot (Function.update x j (x j + t)))
        (latency j (x j) + (p j - R)) 0 := by
      simp only [pot, sum_apply_update_of_mem potTerm x _ (Finset.mem_univ j)]
      exact (hadd j).add_const _
    have hnonneg := nonneg_of_hasDerivAt_of_forall_pos
      (sub_pos.mpr (lt_of_le_of_ne hxFeas.2 hne_d)) hcurve fun t ht0 htd => by
        simp only [add_zero, Function.update_eq_self]
        exact hxMin (isFeasiblePricedFlow_update_add hxFeas ht0.le (by linarith))
    linarith

/-- **Existence of a social optimum** for continuous latency functions on `[0, ∞)` and `0 ≤ d`. -/
theorem exists_isSocialOptimum {d R : ℝ} {latency : Link → ℝ → ℝ}
    (hl : ∀ i, ContinuousOn (latency i) (Set.Ici 0)) (hd : 0 ≤ d) :
    ∃ xS, IsSocialOptimum d R latency xS := by
  have hcont :
      ContinuousOn (socialSurplus R latency) {x : Link → ℝ | IsFeasiblePricedFlow d x} := by
    refine continuousOn_finsetSum Finset.univ fun i _ => ?_
    have hi : ContinuousOn (fun x : Link → ℝ => latency i (x i))
        {x : Link → ℝ | IsFeasiblePricedFlow d x} :=
      (hl i).comp (continuous_apply i).continuousOn fun x hx => hx.1 i
    exact (continuousOn_const.sub hi).mul (continuous_apply i).continuousOn
  have hne : ({x : Link → ℝ | IsFeasiblePricedFlow d x}).Nonempty :=
    ⟨0, fun _ => le_rfl, by simp [hd]⟩
  obtain ⟨xS, hxS, hmax⟩ := isCompact_feasiblePricedFlows.exists_isMaxOn hne hcont
  exact ⟨xS, hxS, fun y hy => hmax hy⟩

private theorem hasDerivAt_surplusTerm {Link : Type*} {latency latencyDeriv : Link → ℝ → ℝ}
    (h : SmoothConvexLatencies latency latencyDeriv) (R : ℝ) (k : Link) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun w => (R - latency k w) * w)
      (R - latency k u - u * latencyDeriv k u) u := by
  have hd : HasDerivAt (fun w => R - latency k w) (0 - latencyDeriv k u) u :=
    (hasDerivAt_const u R).sub (h.hasDerivAt k u hu)
  have hm : HasDerivAt (fun w => (R - latency k w) * w)
      ((0 - latencyDeriv k u) * u + (R - latency k u) * 1) u :=
    hd.mul (hasDerivAt_id' u)
  convert hm using 1
  ring

/-- **First-order KKT characterization of social optima** ([Acemoglu and Ozdaglar, Eq. (7),
p. 7][AcemogluOzdaglar2007MOR]): for smooth convex latencies, a feasible flow `xS` maximizes social
surplus if and only if there exists a multiplier `μ ≥ 0` with `μ * (d - ∑ i, xS i) = 0` such that
marginal social benefit `R - latency i (xS i) - xS i * latencyDeriv i (xS i)` equals `μ` on active
links and is at most `μ` on all links. -/
theorem SmoothConvexLatencies.isSocialOptimum_iff_kkt {d R : ℝ}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    {xS : Link → ℝ} :
    IsSocialOptimum d R latency xS ↔
      IsFeasiblePricedFlow d xS ∧
        ∃ μ : ℝ, 0 ≤ μ ∧ μ * (d - ∑ i, xS i) = 0 ∧
          (∀ i, R - latency i (xS i) - xS i * latencyDeriv i (xS i) ≤ μ) ∧
          (∀ i, 0 < xS i → R - latency i (xS i) - xS i * latencyDeriv i (xS i) = μ) := by
  classical
  constructor
  · intro hopt
    refine ⟨hopt.1, ?_⟩
    have hS : ∀ (s : Finset Link) y k v, k ∈ s →
        ∑ m ∈ s, (R - latency m (Function.update y k v m)) * Function.update y k v m =
          (R - latency k v) * v + ∑ m ∈ s.erase k, (R - latency m (y m)) * y m :=
      fun _ y _ v hk => sum_apply_update_of_mem (fun m u => (R - latency m u) * u) y v hk
    have hsub : ∀ k, HasDerivAt (fun t => (R - latency k (xS k - t)) * (xS k - t))
        (-(R - latency k (xS k) - xS k * latencyDeriv k (xS k))) 0 := fun k => by
      simpa only [sub_zero, mul_neg, mul_one, Function.comp_def] using
        (hasDerivAt_surplusTerm h R k (u := xS k - 0) (by simpa using hopt.1.1 k)).comp 0
          ((hasDerivAt_id' (0 : ℝ)).const_sub (xS k))
    have hadd : ∀ k, HasDerivAt (fun t => (R - latency k (xS k + t)) * (xS k + t))
        (R - latency k (xS k) - xS k * latencyDeriv k (xS k)) 0 := fun k => by
      simpa only [add_zero, mul_one, Function.comp_def] using
        (hasDerivAt_surplusTerm h R k (u := xS k + 0) (by simpa using hopt.1.1 k)).comp 0
          ((hasDerivAt_id' (0 : ℝ)).const_add (xS k))
    have hswap : ∀ i j, 0 < xS i →
        R - latency j (xS j) - xS j * latencyDeriv j (xS j) ≤
          R - latency i (xS i) - xS i * latencyDeriv i (xS i) := by
      intro i j hi
      by_cases hij : i = j
      · subst hij; exact le_rfl
      let g : ℝ → ℝ := fun t =>
        -socialSurplus R latency (Function.update (Function.update xS i (xS i - t)) j (xS j + t))
      have hg_deriv : HasDerivAt g
          ((R - latency i (xS i) - xS i * latencyDeriv i (xS i)) -
            (R - latency j (xS j) - xS j * latencyDeriv j (xS j))) 0 := by
        simp only [g, socialSurplus, hS _ _ _ _ (Finset.mem_univ j),
          hS _ xS _ _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)]
        convert ((hadd j).add ((hsub i).add_const
          (∑ k ∈ (Finset.univ.erase j).erase i, (R - latency k (xS k)) * xS k))).neg using 1
        ring
      have h0 := nonneg_of_hasDerivAt_of_forall_pos hi hg_deriv fun t ht0 hti => by
        simp only [g, sub_zero, add_zero, Function.update_eq_self, neg_le_neg_iff]
        exact hopt.2 _ ⟨fun k => nonneg_update_sub_add hopt.1.1 ht0.le hti.le k,
          (sum_update_sub_add_eq xS hij t).trans_le hopt.1.2⟩
      linarith
    have hdec : ∀ i, 0 < xS i → 0 ≤ R - latency i (xS i) - xS i * latencyDeriv i (xS i) := by
      intro i hi
      let g : ℝ → ℝ := fun t => -socialSurplus R latency (Function.update xS i (xS i - t))
      have hg_deriv : HasDerivAt g (R - latency i (xS i) - xS i * latencyDeriv i (xS i)) 0 := by
        simp only [g, socialSurplus, hS _ xS _ _ (Finset.mem_univ i)]
        convert ((hsub i).add_const
          (∑ k ∈ Finset.univ.erase i, (R - latency k (xS k)) * xS k)).neg using 1
        ring
      refine nonneg_of_hasDerivAt_of_forall_pos hi hg_deriv fun t ht0 hti => ?_
      simp only [g, sub_zero, Function.update_eq_self, neg_le_neg_iff]
      have hsum := sum_update_add_eq xS i (-t)
      simp only [← sub_eq_add_neg] at hsum
      exact hopt.2 _ ⟨fun k => by
        simp only [Function.update_apply]; split_ifs <;> linarith [hopt.1.1 k],
        by linarith [hopt.1.2]⟩
    have hinc : ∑ k, xS k < d → ∀ j,
        R - latency j (xS j) - xS j * latencyDeriv j (xS j) ≤ 0 := by
      intro hlt j
      let g : ℝ → ℝ := fun t => -socialSurplus R latency (Function.update xS j (xS j + t))
      have hg_deriv : HasDerivAt g
          (-(R - latency j (xS j) - xS j * latencyDeriv j (xS j))) 0 := by
        simp only [g, socialSurplus, hS _ xS _ _ (Finset.mem_univ j)]
        exact ((hadd j).add_const (∑ k ∈ Finset.univ.erase j, (R - latency k (xS k)) * xS k)).neg
      have h0 := nonneg_of_hasDerivAt_of_forall_pos (sub_pos.mpr hlt) hg_deriv fun t ht0 htd => by
        simp only [g, add_zero, Function.update_eq_self, neg_le_neg_iff]
        exact hopt.2 _ (isFeasiblePricedFlow_update_add hopt.1 ht0.le (by linarith))
      linarith
    rcases hopt.1.2.lt_or_eq with hlt | hsum_eq
    · refine ⟨0, le_rfl, by ring, hinc hlt, fun i hi => le_antisymm (hinc hlt i) (hdec i hi)⟩
    · by_cases hpos : ∃ i₀, 0 < xS i₀
      · obtain ⟨i₀, hi₀⟩ := hpos
        refine ⟨R - latency i₀ (xS i₀) - xS i₀ * latencyDeriv i₀ (xS i₀), hdec i₀ hi₀,
          by simp [hsum_eq], fun j => hswap i₀ j hi₀, fun i hi =>
          le_antisymm (hswap i₀ i hi₀) (hswap i i₀ hi)⟩
      · push Not at hpos
        have hx0 : ∀ i, xS i = 0 := fun i => le_antisymm (hpos i) (hopt.1.1 i)
        refine ⟨max 0 R, le_max_left 0 R, by simp [hsum_eq], fun i => ?_, fun i hi => ?_⟩
        · simp [hx0 i, h.zero_at_zero i, le_max_right 0 R]
        · linarith [hx0 i]
  · rintro ⟨hfeas, μ, hμ0, hcomp, hle, heq⟩
    refine ⟨hfeas, fun y hy => ?_⟩
    have hsum_term : socialSurplus R latency y ≤
        socialSurplus R latency xS +
          ∑ i, (R - latency i (xS i) - xS i * latencyDeriv i (xS i)) * (y i - xS i) := by
      simp only [socialSurplus, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => h.term_surplus_le_add_marginal R i (hfeas.1 i) (hy.1 i)
    have hsum_μ : ∑ i, (R - latency i (xS i) - xS i * latencyDeriv i (xS i)) * (y i - xS i) ≤
        μ * ((∑ i, y i) - ∑ i, xS i) := by
      have hrhs : μ * ((∑ i, y i) - ∑ i, xS i) = ∑ i, μ * (y i - xS i) := by
        rw [← Finset.mul_sum]
        simp [Finset.sum_sub_distrib]
      rw [hrhs]
      refine Finset.sum_le_sum fun i _ => ?_
      rcases (hfeas.1 i).eq_or_lt with hxi | hxi
      · have hxi0 : xS i = 0 := hxi.symm
        have hle_i : R - latency i 0 - 0 * latencyDeriv i 0 ≤ μ := hxi0 ▸ hle i
        rw [hxi0, sub_zero]
        exact mul_le_mul_of_nonneg_right hle_i (hy.1 i)
      · rw [heq i hxi]
    linarith [mul_nonpos_of_nonneg_of_nonpos hμ0 (sub_nonpos.mpr hy.2)]

/-- **Pigovian marginal-congestion decentralization** ([Ozdaglar and Srikant, Section 22.2.2,
Eq. (22.24), p. 581][OzdaglarSrikant2007]): for smooth convex latencies, any social optimum `xS`
routing full demand `d` is a priced Wardrop equilibrium under `pigovianPrice latencyDeriv xS`. -/
theorem SmoothConvexLatencies.isPricedWardrop_pigovianPrice_of_sum_eq {d R : ℝ}
    {latency latencyDeriv : Link → ℝ → ℝ} (h : SmoothConvexLatencies latency latencyDeriv)
    {xS : Link → ℝ} (hopt : IsSocialOptimum d R latency xS) (hsum : ∑ i, xS i = d) :
    IsPricedWardrop d R latency (pigovianPrice latencyDeriv xS) xS := by
  obtain ⟨hfeas, μ, hμ0, _, hle, heq⟩ := h.isSocialOptimum_iff_kkt.mp hopt
  refine ⟨hfeas, fun i j hi => ?_, fun i hi => ?_, fun _ => hsum⟩
  · simp only [pigovianPrice]; linarith [heq i hi, hle j]
  · simp only [pigovianPrice]; linarith [heq i hi]

end ExistenceAndPigou

section MonopolyEfficiency

variable {Link : Type*} [Fintype Link]

/-- At any Monopoly Equilibrium `(p, x)` under nonnegative zero-flow latencies `0 ≤ latency k 0`,
every link carrying positive flow sets effective cost equal to the reservation utility `R`, i.e.
`p i = R - latency i (x i)` ([Acemoglu and Ozdaglar, Proposition 3.2,
p. 7][AcemogluOzdaglar2007MOR]). -/
theorem IsMonopolyEquilibrium.price_eq_sub_latency {d R : ℝ} {latency : Link → ℝ → ℝ}
    {p x : Link → ℝ} (hme : IsMonopolyEquilibrium d R latency p x)
    (hlat0 : ∀ k, 0 ≤ latency k 0) {i : Link} (hi : 0 < x i) :
    p i = R - latency i (x i) := by
  classical
  obtain ⟨hp, hw, hmax⟩ := hme
  have hle : latency i (x i) + p i ≤ R := hw.2.2.1 i hi
  by_contra hne
  have hlt : latency i (x i) + p i < R := lt_of_le_of_ne hle (by
    intro heq; apply hne; linarith)
  let p' : Link → ℝ := fun k => if 0 < x k then R - latency k (x k) else max (p k) R
  have hp'0 : ∀ k, 0 ≤ p' k := by
    intro k
    simp only [p']
    split_ifs with hxk
    · have hk := hw.2.2.1 k hxk
      linarith [hp k]
    · exact (hp k).trans (le_max_left _ _)
  have hp'Pos : ∀ k, 0 < x k → p' k = R - latency k (x k) := fun k hxk => by
    simp only [p', hxk, ↓reduceIte]
  have hw' : IsPricedWardrop d R latency p' x := by
    refine ⟨hw.1, fun a b ha => ?_, fun a ha => ?_, fun ⟨j, hj⟩ => ?_⟩
    · rw [hp'Pos a ha]
      simp only [p']
      split_ifs with hb
      · linarith
      · have hx0 : x b = 0 := le_antisymm (not_lt.mp hb) (hw.1.1 b)
        rw [hx0]
        linarith [hlat0 b, le_max_right (p b) R]
    · rw [hp'Pos a ha]
      linarith
    · exfalso
      simp only [p'] at hj
      split_ifs at hj with hjx
      · linarith
      · have hx0 : x j = 0 := le_antisymm (not_lt.mp hjx) (hw.1.1 j)
        rw [hx0] at hj
        linarith [hlat0 j, le_max_right (p j) R]
  have hprof_lt : monopolyProfit p x < monopolyProfit p' x := by
    refine Finset.sum_lt_sum (fun k _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
    · rcases (hw.1.1 k).eq_or_lt with hxk | hxk
      · simp [← hxk]
      · rw [hp'Pos k hxk]
        have hk := hw.2.2.1 k hxk
        nlinarith
    · rw [hp'Pos i hi]
      nlinarith
  linarith [hmax p' x hp'0 hw']

/-- At any Monopoly Equilibrium under `0 ≤ latency k 0`, consumer surplus is zero: the monopolist
extracts the entire social surplus ([Acemoglu and Ozdaglar, Section 3,
p. 8][AcemogluOzdaglar2007MOR]). -/
theorem IsMonopolyEquilibrium.consumerSurplus_eq_zero {d R : ℝ} {latency : Link → ℝ → ℝ}
    {p x : Link → ℝ} (hme : IsMonopolyEquilibrium d R latency p x)
    (hlat0 : ∀ k, 0 ≤ latency k 0) :
    consumerSurplus R latency p x = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases (hme.2.1.1.1 i).eq_or_lt with hxi | hxi
  · simp [← hxi]
  · rw [hme.price_eq_sub_latency hlat0 hxi]
    ring

/-- At any Monopoly Equilibrium under `0 ≤ latency k 0`, monopoly profit equals social surplus. -/
theorem IsMonopolyEquilibrium.monopolyProfit_eq_socialSurplus {d R : ℝ} {latency : Link → ℝ → ℝ}
    {p x : Link → ℝ} (hme : IsMonopolyEquilibrium d R latency p x)
    (hlat0 : ∀ k, 0 ≤ latency k 0) :
    monopolyProfit p x = socialSurplus R latency x := by
  rw [socialSurplus_eq_consumerSurplus_add_monopolyProfit R latency p x,
    hme.consumerSurplus_eq_zero hlat0, zero_add]

/-- **Monopoly Equilibrium Efficiency** ([Ozdaglar and Srikant, Section 22.2.3,
p. 582][OzdaglarSrikant2007]; [Acemoglu and Ozdaglar, Proposition 3.2,
p. 7][AcemogluOzdaglar2007MOR]): for nonnegative reservation utility `0 ≤ R` and latencies with
`latency i 0 = 0`, a flow vector `x` is the flow at some Monopoly Equilibrium `(p, x)` if and only
if `x` is a social optimum. -/
theorem exists_isMonopolyEquilibrium_iff_isSocialOptimum {d R : ℝ} {latency : Link → ℝ → ℝ}
    (hR : 0 ≤ R) (hzero : ∀ i, latency i 0 = 0) {x : Link → ℝ} :
    (∃ p, IsMonopolyEquilibrium d R latency p x) ↔ IsSocialOptimum d R latency x := by
  classical
  have hlat0 : ∀ k, 0 ≤ latency k 0 := fun k => by rw [hzero k]
  constructor
  · rintro ⟨p, hme⟩
    refine ⟨hme.2.1.1, fun y hy => ?_⟩
    let yPos : Link → ℝ := fun i => if latency i (y i) ≤ R then y i else 0
    have hyPosFeas : IsFeasiblePricedFlow d yPos := by
      refine ⟨fun i => ?_, ?_⟩
      · simp only [yPos]
        split_ifs <;> [exact hy.1 i; exact le_rfl]
      · refine (Finset.sum_le_sum fun i _ => ?_).trans hy.2
        simp only [yPos]
        split_ifs <;> [exact le_rfl; exact hy.1 i]
    let p' : Link → ℝ := fun i => R - latency i (yPos i)
    have hp'0 : ∀ i, 0 ≤ p' i := by
      intro i
      simp only [p', yPos]
      split_ifs with hle
      · linarith
      · simp [hzero i, hR]
    have hw' : IsPricedWardrop d R latency p' yPos := by
      refine ⟨hyPosFeas, fun i j _ => ?_, fun i _ => ?_, fun ⟨j, hj⟩ => ?_⟩
      · simp [p']
      · simp [p']
      · simp [p'] at hj
    have hsurp_le : socialSurplus R latency y ≤ monopolyProfit p' yPos := by
      simp only [socialSurplus, monopolyProfit, p']
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [yPos]
      split_ifs with hle
      · exact le_rfl
      · push Not at hle
        have hyi := hy.1 i
        nlinarith
    have hprof := hme.2.2 p' yPos hp'0 hw'
    rw [hme.monopolyProfit_eq_socialSurplus hlat0] at hprof
    exact hsurp_le.trans hprof
  · intro hopt
    have hlat_le : ∀ i, 0 < x i → latency i (x i) ≤ R := by
      intro i hi
      by_contra hgt
      push Not at hgt
      let y : Link → ℝ := Function.update x i 0
      have hyFeas : IsFeasiblePricedFlow d y := by
        refine ⟨fun k => ?_, ?_⟩
        · by_cases hki : k = i
          · subst hki; simp [y]
          · simp [y, hki, hopt.1.1 k]
        · refine (Finset.sum_le_sum fun k _ => ?_).trans hopt.1.2
          by_cases hki : k = i
          · subst hki; simp [y, hi.le]
          · simp [y, hki]
      have hstrict : socialSurplus R latency x < socialSurplus R latency y := by
        refine Finset.sum_lt_sum (fun k _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
        · by_cases hki : k = i
          · subst hki; simp [y]; nlinarith
          · simp [y, hki]
        · simp [y]; nlinarith
      linarith [hopt.2 y hyFeas]
    let p : Link → ℝ := fun i => R - latency i (x i)
    have hp0 : ∀ i, 0 ≤ p i := by
      intro i
      rcases (hopt.1.1 i).eq_or_lt with hxi | hxi
      · simp [p, ← hxi, hzero i, hR]
      · linarith [hlat_le i hxi]
    have hw : IsPricedWardrop d R latency p x :=
      ⟨hopt.1, fun i j _ => by simp [p], fun i _ => by simp [p], fun ⟨j, hj⟩ => by simp [p] at hj⟩
    refine ⟨p, hp0, hw, fun p' x' _ hw' => ?_⟩
    have hprof_le : monopolyProfit p' x' ≤ socialSurplus R latency x' := by
      rw [socialSurplus_eq_consumerSurplus_add_monopolyProfit R latency p' x']
      linarith [hw'.consumerSurplus_nonneg]
    have hprof_eq : monopolyProfit p x = socialSurplus R latency x := by
      simp [monopolyProfit, socialSurplus, p]
    linarith [hopt.2 x' hw'.1]

end MonopolyEfficiency

section MarkupPerturbation

/-- Rightward inverse-step lemma on `[0, ∞)`: if `f` is monotone and continuous on `[0, ∞)`, then
for `x ≥ 0` and `0 < μ ≤ f (x + 1) - f x` there exists `t ∈ (0, 1]` with `f (x + t) - f x = μ`;
moreover `t < ε` whenever `μ < f (x + ε) - f x`. -/
theorem exists_pos_step_add_eq {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Ici 0))
    (hcont : ContinuousOn f (Set.Ici 0)) {x μ : ℝ} (hx : 0 ≤ x) (hμ0 : 0 < μ)
    (hμ1 : μ ≤ f (x + 1) - f x) :
    ∃ t, 0 < t ∧ t ≤ 1 ∧ f (x + t) - f x = μ ∧
      ∀ ε, 0 < ε → μ < f (x + ε) - f x → t < ε := by
  have hg_cont : ContinuousOn (fun t => f (x + t) - f x) (Set.Icc 0 1) := by
    have hf_comp : ContinuousOn (fun t => f (x + t)) (Set.Icc 0 1) :=
      hcont.comp (continuous_const.add continuous_id).continuousOn fun t ht => by
        rw [Set.mem_Icc] at ht
        exact Set.mem_Ici.mpr (by linarith [ht.1])
    exact hf_comp.sub continuousOn_const
  obtain ⟨t, htIcc, hteq⟩ := isPreconnected_Icc.intermediate_value₂ (g := fun _ => μ)
    ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ hg_cont continuousOn_const
    (by rw [add_zero, sub_self]; exact hμ0.le) hμ1
  have ht0 : 0 < t := by
    refine lt_of_le_of_ne htIcc.1 fun h0 => ?_
    subst h0
    simp at hteq
    linarith
  refine ⟨t, ht0, htIcc.2, hteq, fun ε hε hμε => ?_⟩
  by_contra hge
  push Not at hge
  have hle := hmono (Set.mem_Ici.mpr (show 0 ≤ x + ε by linarith))
    (Set.mem_Ici.mpr (show 0 ≤ x + t by linarith)) (show x + ε ≤ x + t by linarith)
  linarith

/-- Leftward inverse-step lemma on `[0, x]`: if `f` is monotone and continuous on `[0, ∞)` with
`f 0 = 0 < f x`, then for `0 < μ < f x` there exists `t ∈ (0, x)` with `f x - f (x - t) = μ`;
moreover `t < ε` whenever `0 < ε ≤ x` and `μ < f x - f (x - ε)`. -/
theorem exists_pos_step_sub_eq {f : ℝ → ℝ} (hzero : f 0 = 0) (hmono : MonotoneOn f (Set.Ici 0))
    (hcont : ContinuousOn f (Set.Ici 0)) {x μ : ℝ} (hx : 0 < x) (hμ0 : 0 < μ)
    (hμx : μ < f x) :
    ∃ t, 0 < t ∧ t < x ∧ f x - f (x - t) = μ ∧
      ∀ ε, 0 < ε → ε ≤ x → μ < f x - f (x - ε) → t < ε := by
  have hg_cont : ContinuousOn (fun t => f x - f (x - t)) (Set.Icc 0 x) := by
    have hf_comp : ContinuousOn (fun t => f (x - t)) (Set.Icc 0 x) :=
      hcont.comp (continuous_const.sub continuous_id).continuousOn fun t ht => by
        rw [Set.mem_Icc] at ht
        exact Set.mem_Ici.mpr (by linarith [ht.2])
    exact continuousOn_const.sub hf_comp
  obtain ⟨t, htIcc, hteq⟩ := isPreconnected_Icc.intermediate_value₂ (g := fun _ => μ)
    ⟨le_rfl, hx.le⟩ ⟨hx.le, le_rfl⟩ hg_cont continuousOn_const
    (by rw [sub_zero, sub_self]; exact hμ0.le) (by rw [sub_self, hzero, sub_zero]; exact hμx.le)
  have ht0 : 0 < t := by
    refine lt_of_le_of_ne htIcc.1 fun h0 => ?_
    subst h0
    simp at hteq
    linarith
  have htx : t < x := by
    refine lt_of_le_of_ne htIcc.2 fun htx_eq => ?_
    subst htx_eq
    simp [hzero] at hteq
    linarith
  refine ⟨t, ht0, htx, hteq, fun ε hε hεx hμε => ?_⟩
  by_contra hge
  push Not at hge
  have hle := hmono (Set.mem_Ici.mpr (show 0 ≤ x - t by linarith [htx]))
    (Set.mem_Ici.mpr (show 0 ≤ x - ε by linarith)) (show x - t ≤ x - ε by linarith)
  linarith

/-- Left-difference quotient inequality: if `g` has derivative `g'` at `x > 0` and along every
tolerance `η > 0` there is a positive step `0 < δ < η` with `δ < x` satisfying
`((g x - g (x - δ)) / δ) * (x - δ) ≤ B`, then `x * g' ≤ B`. -/
theorem mul_deriv_le_of_forall_pos_sub {g : ℝ → ℝ} {x g' B : ℝ} (_hx : 0 < x)
    (hd : HasDerivAt g g' x)
    (hstep : ∀ η, 0 < η → ∃ δ, 0 < δ ∧ δ < η ∧ δ < x ∧
      ((g x - g (x - δ)) / δ) * (x - δ) ≤ B) :
    x * g' ≤ B := by
  by_contra hgt
  push Not at hgt
  have hlim := (hd.tendsto_slope_zero_left.comp
    (by simpa using tendsto_neg_nhdsGT (a := (0 : ℝ)))).mul
    (((continuous_sub_left x).tendsto' 0 x (sub_zero x)).mono_left nhdsWithin_le_nhds)
  obtain ⟨η, hη, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hlim.eventually (eventually_gt_nhds (by linarith : B < g' * x)))
  obtain ⟨δ, hδ0, hδη, _, hle⟩ := hstep η hη
  have hlt : B < (-δ)⁻¹ • (g (x + -δ) - g x) * (x - δ) := hsub ⟨hδ0, hδη⟩
  rw [smul_eq_mul, ← sub_eq_add_neg, inv_neg, neg_mul, ← mul_neg, neg_sub, inv_mul_eq_div] at hlt
  linarith

/-- Right-difference quotient inequality: if `g` has derivative `g'` at `x ≥ 0` and for every
`ε > 0` and `η > 0` there is `0 < δ < η` satisfying
`B ≤ ((g (x + δ) - g x) / δ) * (x + δ) + (C + ε)`, then `B ≤ x * g' + C`. -/
theorem le_mul_deriv_add_of_forall_pos_add {g : ℝ → ℝ} {x g' B C : ℝ}
    (hd : HasDerivAt g g' x)
    (hstep : ∀ ε η, 0 < ε → 0 < η → ∃ δ, 0 < δ ∧ δ < η ∧
      B ≤ ((g (x + δ) - g x) / δ) * (x + δ) + (C + ε)) :
    B ≤ x * g' + C := by
  by_contra hlt
  push Not at hlt
  have hlim := hd.tendsto_slope_zero_right.mul
    (((continuous_const.add continuous_id).tendsto' 0 x (add_zero x)).mono_left nhdsWithin_le_nhds)
  obtain ⟨η, hη, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hlim.eventually
    (eventually_lt_nhds (by linarith : g' * x < x * g' + (B - (x * g' + C)) / 2)))
  obtain ⟨δ, hδ0, hδη, hge⟩ := hstep ((B - (x * g' + C)) / 2) η (by linarith) hη
  have hlt_δ : δ⁻¹ • (g (x + δ) - g x) * (x + δ) < x * g' + (B - (x * g' + C)) / 2 :=
    hsub ⟨hδ0, hδη⟩
  rw [smul_eq_mul, inv_mul_eq_div] at hlt_δ
  linarith

/-- Finitely many strict lower bounds `c < a q` (for `q` with `P q`), together with `c < R`, leave
a common positive margin `ε`. -/
private theorem exists_pos_margin {ι : Type*} [Finite ι] {P : ι → Prop} {a : ι → ℝ} {c R : ℝ}
    (hR : c < R) (ha : ∀ q, P q → c < a q) :
    ∃ ε > 0, c + ε < R ∧ ∀ q, P q → c + ε ≤ a q := by
  classical
  have := Fintype.ofFinite ι
  let s : Finset ℝ := insert R ((Finset.univ.filter P).image a)
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  have hc : c < s.min' hs := (Finset.lt_min'_iff s hs).2 fun y hy => by
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hR
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      exact ha q (Finset.mem_filter.1 hq).2
  refine ⟨(s.min' hs - c) / 2, by linarith, ?_, fun q hq => ?_⟩
  · linarith [s.min'_le R (Finset.mem_insert_self _ _)]
  · linarith [s.min'_le (a q) (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem a (Finset.mem_filter.2 ⟨Finset.mem_univ q, hq⟩)))]

/-- **General downward-flow markup bound** shared across parallel and parallel-serial oligopolies:
if a portfolio `own : Link → Prop` owns link `i` (`own i`) and cannot increase its portfolio profit
`∑ m with own m, p' m * x' m` by adjusting prices on `own`, then `x i * d_i ≤ p i`. -/
theorem markup_ge_mul_deriv_of_wardrop_bestResponse {Link : Type*} [Fintype Link]
    {d R : ℝ} {latency : Link → ℝ → ℝ} {p x : Link → ℝ}
    (own : Link → Prop) [DecidablePred own] {i : Link} {di : ℝ}
    (hown_i : own i) (hp : ∀ k, 0 ≤ p k) (hw : IsPricedWardrop d R latency p x)
    (hmono_i : MonotoneOn (latency i) (Set.Ici 0))
    (hderiv_i : HasDerivAt (latency i) di (x i))
    (hcomp_mono : ∀ q, ¬ own q → MonotoneOn (latency q) (Set.Ici 0))
    (hcomp_cont : ∀ q, ¬ own q → ContinuousOn (latency q) (Set.Ici 0))
    (hlat0 : ∀ m, own m → 0 ≤ latency m 0)
    (hbest : ∀ p' x', (∀ k, 0 ≤ p' k) → (∀ q, ¬ own q → p' q = p q) →
      ((∃ m, own m ∧ p' m ≠ p m) ∨ x' i ≤ x i) →
      IsPricedWardrop d R latency p' x' →
      (∑ m with own m, p' m * x' m) ≤ ∑ m with own m, p m * x m) :
    x i * di ≤ p i := by
  classical
  rcases (hw.1.1 i).eq_or_lt with hxi0 | hxi
  · rw [← hxi0, zero_mul]
    exact hp i
  let cStar : ℝ := latency i (x i) + p i
  have hcR : cStar ≤ R := hw.2.2.1 i hxi
  have hupd_comp : ∀ v q, ¬ own q → Function.update p i v q = p q := fun _ q hq =>
    Function.update_of_ne (fun h : q = i => hq (h ▸ hown_i)) _ _
  rcases hcR.eq_or_lt with hc_eq_R | hc_lt_R
  · -- Case 1: cStar = R. Reduce x_i directly against the reservation ceiling R.
    refine mul_deriv_le_of_forall_pos_sub hxi hderiv_i fun η hη => ?_
    let δ : ℝ := min (η / 2) (x i / 2)
    have hδ0 : 0 < δ := lt_min (half_pos hη) (half_pos hxi)
    have hδx : δ < x i := (min_le_right _ _).trans_lt (half_lt_self hxi)
    let x' : Link → ℝ := Function.update x i (x i - δ)
    let p' : Link → ℝ := Function.update p i (R - latency i (x i - δ))
    have hlat_le : latency i (x i - δ) ≤ latency i (x i) :=
      hmono_i (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr hxi.le) (by linarith)
    have hp'0 : ∀ k, 0 ≤ p' k := fun k => by
      simp only [p', Function.update_apply]; split_ifs <;> linarith [hp k, hp i]
    have hx'sum : ∑ k, x' k = ∑ k, x k - δ := by
      simpa only [← sub_eq_add_neg] using sum_update_add_eq x i (-δ)
    have hcost : ∀ k, R ≤ latency k (x' k) + p' k ∧
        (0 < x' k → latency k (x' k) + p' k = R) := fun k => by
      by_cases hki : k = i
      · subst hki; simp [x', p']
      · simp only [x', p', Function.update_of_ne hki]
        have hge := hw.2.1 i k hxi
        exact ⟨by linarith, fun hk => le_antisymm (hw.2.2.1 k hk) (by linarith)⟩
    have hw' : IsPricedWardrop d R latency p' x' :=
      ⟨⟨fun k => by simp only [x', Function.update_apply]; split_ifs <;> linarith [hw.1.1 k],
          by linarith [hw.1.2]⟩,
        fun a b ha => ((hcost a).2 ha).trans_le (hcost b).1, fun a ha => ((hcost a).2 ha).le,
        fun ⟨j, hj⟩ => absurd hj (not_lt.mpr (hcost j).1)⟩
    have hprof := hbest p' x' hp'0 (hupd_comp _) (Or.inr (by simp [x', hδ0.le])) hw'
    rw [sum_filter_eq_add_erase own hown_i (fun m => p' m * x' m) (fun m => p m * x m)
        (fun m _ hmi => by simp [p', x', hmi]),
      sum_filter_eq_add_erase own hown_i (fun m => p m * x m) (fun m => p m * x m)
        (fun _ _ _ => rfl)] at hprof
    simp only [p', x', Function.update_self] at hprof
    have hpi_eq : R = latency i (x i) + p i := hc_eq_R.symm
    exact ⟨δ, hδ0, (min_le_left _ _).trans_lt (half_lt_self hη), hδx,
      by rw [div_mul_eq_mul_div, div_le_iff₀ hδ0]; nlinarith⟩
  · -- Case 2: cStar < R, so ∑ k, x k = d.
    have hsum_d : ∑ k, x k = d := hw.2.2.2 ⟨i, hc_lt_R⟩
    let Q0 : Finset Link :=
      Finset.univ.filter fun q => ¬ own q ∧ latency q (x q) + p q = cStar
    have hQ0_nonempty : Q0.Nonempty := by
      by_contra hemp
      have hcomp_gt : ∀ q, ¬ own q → cStar < latency q (x q) + p q := fun q hq =>
        lt_of_le_of_ne (hw.2.1 i q hxi) fun heq =>
          hemp ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq, heq.symm⟩⟩
      obtain ⟨ε, hε0, hcεR, hcomp_ge⟩ := exists_pos_margin hc_lt_R hcomp_gt
      let p' : Link → ℝ := fun k =>
        if own k then (if 0 < x k then p k + ε else max (p k) (cStar + ε)) else p k
      have hp'0 : ∀ k, 0 ≤ p' k := fun k => by
        simp only [p']
        split_ifs
        · linarith [hp k]
        · exact (hp k).trans (le_max_left _ _)
        · exact hp k
      have hcost_a : ∀ a, 0 < x a → latency a (x a) + p' a = cStar + ε := fun a ha => by
        have ha_own : own a := by by_contra hna; linarith [hw.2.1 a i ha, hcomp_gt a hna]
        simp only [p', ha_own, ha, ↓reduceIte]
        linarith [hw.effectiveCost_eq_of_pos ha hxi]
      have hw' : IsPricedWardrop d R latency p' x := by
        refine ⟨hw.1, fun a b ha => ?_, fun a ha => (hcost_a a ha).trans_le hcεR.le,
          fun _ => hsum_d⟩
        rw [hcost_a a ha]
        by_cases hb_own : own b
        · simp only [p', hb_own, ↓reduceIte]
          split_ifs with hxb
          · linarith [hw.effectiveCost_eq_of_pos hxb hxi]
          · rw [le_antisymm (not_lt.mp hxb) (hw.1.1 b)]
            linarith [hlat0 b hb_own, le_max_right (p b) (cStar + ε)]
        · simp only [p', hb_own, ↓reduceIte]
          exact hcomp_ge b hb_own
      have hstrict : (∑ m with own m, p m * x m) < ∑ m with own m, p' m * x m := by
        refine Finset.sum_lt_sum (fun m hm => ?_)
          ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hown_i⟩, ?_⟩
        · rcases (hw.1.1 m).eq_or_lt with hxm | hxm
          · simp [← hxm]
          · simp only [p', (Finset.mem_filter.mp hm).2, hxm, ↓reduceIte]
            nlinarith
        · simp only [p', hown_i, hxi, ↓reduceIte]
          nlinarith
      linarith [hbest p' x hp'0 (fun q hq => by simp [p', hq])
        (Or.inl ⟨i, hown_i, by simp [p', hown_i, hxi, hε0.ne']⟩) hw']
    by_cases hflat : ∃ q ∈ Q0, ∃ δ₀ > 0, latency q (x q + δ₀) = latency q (x q)
    · -- Subcase 2a: some competitor q ∈ Q0 is locally flat above x q.
      obtain ⟨q, hqQ0, δ₀, hδ₀, hlat_flat⟩ := hflat
      obtain ⟨-, hq_not_own, hq_cost⟩ := Finset.mem_filter.mp hqQ0
      have hqi : i ≠ q := fun h => hq_not_own (h ▸ hown_i)
      refine mul_deriv_le_of_forall_pos_sub hxi hderiv_i fun η hη => ?_
      let δ : ℝ := min (min (η / 2) (x i / 2)) (δ₀ / 2)
      have hδ0 : 0 < δ := lt_min (lt_min (half_pos hη) (half_pos hxi)) (half_pos hδ₀)
      have hδx : δ < x i :=
        ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hxi)
      have hδ_le_δ₀ : δ ≤ δ₀ := (min_le_right _ _).trans (half_le_self hδ₀.le)
      have hxq := hw.1.1 q
      have hlat_q_eq : latency q (x q + δ) = latency q (x q) := le_antisymm
        ((hcomp_mono q hq_not_own (Set.mem_Ici.mpr (show 0 ≤ x q + δ by linarith))
          (Set.mem_Ici.mpr (show 0 ≤ x q + δ₀ by linarith)) (by linarith)).trans_eq hlat_flat)
        (hcomp_mono q hq_not_own (Set.mem_Ici.mpr hxq) (Set.mem_Ici.mpr (by linarith))
          (by linarith))
      let x' : Link → ℝ := Function.update (Function.update x i (x i - δ)) q (x q + δ)
      let p' : Link → ℝ := Function.update p i (cStar - latency i (x i - δ))
      have hlat_i_le : latency i (x i - δ) ≤ latency i (x i) :=
        hmono_i (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr hxi.le) (by linarith)
      have hp'0 : ∀ k, 0 ≤ p' k := fun k => by
        simp only [p', cStar, Function.update_apply]; split_ifs <;> linarith [hp k, hp i]
      have hx'sum : ∑ k, x' k = d := (sum_update_sub_add_eq x hqi δ).trans hsum_d
      have hcost : ∀ k, cStar ≤ latency k (x' k) + p' k ∧
          (0 < x' k → latency k (x' k) + p' k = cStar) := fun k => by
        by_cases hkq : k = q
        · subst hkq
          simp only [x', p', Function.update_self, Function.update_of_ne hqi.symm, hlat_q_eq]
          exact ⟨hq_cost.ge, fun _ => hq_cost⟩
        by_cases hki : k = i
        · subst hki
          simp [x', p', hkq]
        simp only [x', p', Function.update_of_ne hkq, Function.update_of_ne hki]
        exact ⟨hw.2.1 i k hxi, fun hxk => hw.effectiveCost_eq_of_pos hxk hxi⟩
      have hw' : IsPricedWardrop d R latency p' x' :=
        ⟨⟨fun k => nonneg_update_sub_add hw.1.1 hδ0.le hδx.le k, hx'sum.le⟩,
          fun a b ha => ((hcost a).2 ha).trans_le (hcost b).1,
          fun a ha => ((hcost a).2 ha).trans_le hc_lt_R.le, fun _ => hx'sum⟩
      have hprof := hbest p' x' hp'0 (hupd_comp _) (Or.inr (by simp [x', hqi, hδ0.le])) hw'
      rw [sum_filter_eq_add_erase own hown_i (fun m => p' m * x' m) (fun m => p m * x m)
          (fun m hm_own hmi => by
            have hmq : m ≠ q := fun h => hq_not_own (h ▸ hm_own)
            simp [p', x', hmi, hmq]),
        sum_filter_eq_add_erase own hown_i (fun m => p m * x m) (fun m => p m * x m)
          (fun _ _ _ => rfl)] at hprof
      simp only [p', x', Function.update_of_ne hqi, Function.update_self, cStar] at hprof
      exact ⟨δ, hδ0, ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hη),
        hδx, by rw [div_mul_eq_mul_div, div_le_iff₀ hδ0]; nlinarith⟩
    · -- Subcase 2b: every q ∈ Q0 strictly increases above x q.
      push Not at hflat
      refine mul_deriv_le_of_forall_pos_sub hxi hderiv_i fun η hη => ?_
      have hcard_pos : 0 < (Q0.card : ℝ) := Nat.cast_pos.mpr hQ0_nonempty.card_pos
      let εStep : ℝ := min 1 (min η (x i) / Q0.card)
      have hεStep_pos : 0 < εStep := lt_min zero_lt_one (div_pos (lt_min hη hxi) hcard_pos)
      have hε_le_1 : εStep ≤ 1 := min_le_left _ _
      have hrem_gt : ∀ r, ¬ own r ∧ r ∉ Q0 → cStar < latency r (x r) + p r := fun r hr =>
        lt_of_le_of_ne (hw.2.1 i r hxi) fun heq =>
          hr.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr.1, heq.symm⟩)
      let boundQ : ℝ := Q0.inf' hQ0_nonempty fun q => latency q (x q + εStep) - latency q (x q)
      have hboundQ_pos : 0 < boundQ := by
        rw [Finset.lt_inf'_iff]
        intro q hq
        have hle := hcomp_mono q (Finset.mem_filter.mp hq).2.1 (Set.mem_Ici.mpr (hw.1.1 q))
          (Set.mem_Ici.mpr (show 0 ≤ x q + εStep by linarith [hw.1.1 q]))
          (show x q ≤ x q + εStep by linarith)
        exact sub_pos.2 (hle.lt_of_ne (hflat q hq εStep hεStep_pos).symm)
      obtain ⟨μ, hμ0, hcμ, hrem_ge⟩ :=
        exists_pos_margin (lt_min hc_lt_R (lt_add_of_pos_right cStar hboundQ_pos)) hrem_gt
      have hcμR : cStar + μ < R := hcμ.trans_le (min_le_left _ _)
      have hμ_lt_boundQ : μ < boundQ := by
        linarith [hcμ.trans_le (min_le_right R (cStar + boundQ))]
      have hex_dq :
          ∀ q ∈ Q0, ∃ t, 0 < t ∧ t < εStep ∧ latency q (x q + t) - latency q (x q) = μ := by
        intro q hq
        have hq_not_own : ¬ own q := (Finset.mem_filter.mp hq).2.1
        have hμ_lt_ε : μ < latency q (x q + εStep) - latency q (x q) :=
          hμ_lt_boundQ.trans_le (Finset.inf'_le _ hq)
        have hle_1 : latency q (x q + εStep) ≤ latency q (x q + 1) :=
          hcomp_mono q hq_not_own (Set.mem_Ici.mpr (by linarith [hw.1.1 q]))
            (Set.mem_Ici.mpr (by linarith [hw.1.1 q])) (by linarith)
        obtain ⟨t, ht0, _, hteq, htsmall⟩ := exists_pos_step_add_eq
          (hcomp_mono q hq_not_own) (hcomp_cont q hq_not_own) (hw.1.1 q) hμ0 (by linarith)
        exact ⟨t, ht0, htsmall εStep hεStep_pos hμ_lt_ε, hteq⟩
      choose! step hstep_pos hstep_lt hdq using hex_dq
      let Δ : ℝ := ∑ q ∈ Q0, step q
      have hΔ0 : 0 < Δ := Finset.sum_pos hstep_pos hQ0_nonempty
      have hΔ_lt : Δ < min η (x i) := by
        have h1 : Δ < ∑ _q ∈ Q0, εStep := Finset.sum_lt_sum_of_nonempty hQ0_nonempty hstep_lt
        have h2 : εStep * Q0.card ≤ min η (x i) := (le_div_iff₀ hcard_pos).mp (min_le_right _ _)
        rw [Finset.sum_const, nsmul_eq_mul] at h1
        linarith
      have hΔη : Δ < η := hΔ_lt.trans_le (min_le_left _ _)
      have hΔx : Δ < x i := hΔ_lt.trans_le (min_le_right _ _)
      let x' : Link → ℝ := flowShift i Q0 step x
      let p' : Link → ℝ := fun k =>
        if k = i then cStar + μ - latency i (x i - Δ)
        else if own k then (if 0 < x k then p k + μ else max (p k) (cStar + μ))
        else p k
      have hi_not_Q0 : i ∉ Q0 := fun hiQ => (Finset.mem_filter.mp hiQ).2.1 hown_i
      have hlat_i_le : latency i (x i - Δ) ≤ latency i (x i) :=
        hmono_i (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr hxi.le) (by linarith)
      have hp'0 : ∀ k, 0 ≤ p' k := fun k => by
        simp only [p']
        split_ifs with hk1 hk2 hk3
        · simp only [cStar]; linarith [hp i]
        · linarith [hp k]
        · exact (hp k).trans (le_max_left _ _)
        · exact hp k
      have hp'comp : ∀ r, ¬ own r → p' r = p r := fun r hr => by
        have hri : r ≠ i := fun h => hr (h ▸ hown_i)
        simp [p', hri, hr]
      have hx'sum : ∑ k, x' k = d := (sum_flowShift_eq hi_not_Q0 step x).trans hsum_d
      have hcost : ∀ k, cStar + μ ≤ latency k (x' k) + p' k ∧
          (0 < x' k → latency k (x' k) + p' k = cStar + μ) := fun k => by
        by_cases hki : k = i
        · subst hki; simp [x', flowShift, Δ, p']
        by_cases hkQ : k ∈ Q0
        · obtain ⟨-, hk_not_own, hk_cost⟩ := Finset.mem_filter.mp hkQ
          have hdq_eq := hdq k hkQ
          simp only [x', flowShift, p', hki, hkQ, hk_not_own, ↓reduceIte]
          exact ⟨by linarith, fun _ => by linarith⟩
        by_cases hk_own : own k
        · simp only [x', flowShift, p', hki, hkQ, hk_own, ↓reduceIte]
          split_ifs with hxk
          · have heq := hw.effectiveCost_eq_of_pos hxk hxi
            exact ⟨by linarith, fun _ => by linarith⟩
          · rw [le_antisymm (not_lt.mp hxk) (hw.1.1 k)]
            exact ⟨by linarith [hlat0 k hk_own, le_max_right (p k) (cStar + μ)],
              fun h => absurd h (lt_irrefl 0)⟩
        · simp only [x', flowShift, p', hki, hkQ, hk_own, ↓reduceIte]
          exact ⟨hrem_ge k ⟨hk_own, hkQ⟩, fun hxk => absurd (Finset.mem_filter.mpr
            ⟨Finset.mem_univ k, hk_own, hw.effectiveCost_eq_of_pos hxk hxi⟩) hkQ⟩
      have hw' : IsPricedWardrop d R latency p' x' :=
        ⟨⟨nonneg_flowShift hw.1.1 hΔx.le (fun q hq => by linarith [hw.1.1 q, hstep_pos q hq]),
            hx'sum.le⟩,
          fun a b ha => ((hcost a).2 ha).trans_le (hcost b).1,
          fun a ha => ((hcost a).2 ha).trans_le hcμR.le, fun _ => hx'sum⟩
      have hprof := hbest p' x' hp'0 hp'comp
        (Or.inr (by simp [x', flowShift, Δ, hΔ0.le])) hw'
      have hmem_i : i ∈ Finset.univ.filter own := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hown_i⟩
      rw [← Finset.add_sum_erase _ _ hmem_i] at hprof
      conv_rhs at hprof => rw [← Finset.add_sum_erase _ _ hmem_i]
      have hrest_ge : ∑ m ∈ (Finset.univ.filter own).erase i, p m * x m ≤
          ∑ m ∈ (Finset.univ.filter own).erase i, p' m * x' m := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hmi : m ≠ i := (Finset.mem_erase.mp hm).1
        have hm_own : own m := (Finset.mem_filter.mp (Finset.mem_erase.mp hm).2).2
        have hm_not_Q0 : m ∉ Q0 := fun h => (Finset.mem_filter.mp h).2.1 hm_own
        rcases (hw.1.1 m).eq_or_lt with hxm | hxm
        · simp [x', flowShift, hmi, hm_not_Q0, ← hxm]
        · simp only [p', x', flowShift, hmi, hm_own, hm_not_Q0, hxm, ↓reduceIte]
          nlinarith
      have hi_term : p' i * x' i =
          (p i + μ + (latency i (x i) - latency i (x i - Δ))) * (x i - Δ) := by
        simp only [p', x', flowShift, Δ, ↓reduceIte, cStar]
        ring
      rw [hi_term] at hprof
      exact ⟨Δ, hΔ0, hΔη, hΔx, by
        rw [div_mul_eq_mul_div, div_le_iff₀ hΔ0]
        nlinarith [mul_nonneg hμ0.le (sub_nonneg.2 hΔx.le)]⟩

end MarkupPerturbation

end Cslib.GameTheory
