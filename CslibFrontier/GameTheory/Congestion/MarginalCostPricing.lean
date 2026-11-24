/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Congestion.BeckmannPotential
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Marginal cost pricing and Pigouvian taxes in nonatomic routing

In a nonatomic congestion game `G`, a socially optimal flow `f*` (`G.IsOptimal f*`) minimizes the
total latency `G.cost f = ∑ e, edgeFlow f e * latency e (edgeFlow f e)` over all feasible flows.
Whereas selfish agents evaluate each resource `e` by its latency `c_e(x)`, a social planner
evaluates `e` by the marginal edge cost `c*_e(x) = (x * c_e(x))' = c_e(x) + x * c'_e(x)`
(`Cslib.GameTheory.marginalCost`), where the extra term `x * c'_e(x)` measures the congestion
externality imposed on the `x` units of traffic already using `e`.

Following Roughgarden [Roughgarden2007Routing], Sections 18.3.1 and 18.5.1 (originally due to
Pigou, 1920, and Beckmann, McGuire and Winsten, 1956), this module proves:

* **Derivative identity** (`hasDerivWithinAt_mul_marginalCost`):
  `x ↦ x * c(x)` has derivative `marginalCost c c' x = c x + x * c' x`.
* **Optimality characterization and equivalence with marginal-cost Wardrop equilibria**
  (`IsOptimal.isWardrop_withMarginalCost_within`, `isOptimal_iff_isWardrop_withMarginalCost`,
  [Roughgarden2007Routing], Proposition 18.9 and Corollary 18.10): when `x ↦ x * latency e x` is
  convex on `[0, ∞)` and `latency e` has derivative `c' e` within `[0, ∞)`, a feasible flow `f*` is
  socially optimal for `G` if and only if every flow-carrying path of `f*` minimizes marginal path
  cost `∑ e ∈ resources p, marginalCost (latency e) (c' e) (edgeFlow f* e)` within its commodity,
  that is, if and only if `f*` is a Wardrop equilibrium of `G.withMarginalCost c'`.
* **Pigouvian marginal-cost taxes** (`IsOptimal.isWardrop_withTaxes_pigouvianTax`,
  `pigouvianTax_nonneg`, `IsOptimal.cost_eq_of_isWardrop_withTaxes`,
  [Roughgarden2007Routing], Theorem 18.27): levying the constant per-unit tax
  `τ_e = edgeFlow f* e * c'_e(edgeFlow f* e)` on each edge `e` makes any optimal flow `f*` a
  Wardrop equilibrium of the taxed network `G.withTaxes τ` (`(G, r, c + τ)`), without even
  requiring convexity of `x ↦ x * c_e(x)` (as noted after Theorem 18.27 in
  [Roughgarden2007Routing], p. 478). Moreover, when `c_e` is nondecreasing on `[0, ∞)`, the taxes
  are nonnegative (`τ_e ≥ 0`), and *every* Wardrop equilibrium of the taxed network has the exact
  same total cost as `f*` on `G` and is therefore socially optimal for `G` (since `c_e` is flat
  between any two distinct equilibrium edge flows, forcing `c'_e(edgeFlow f* e) = 0` and hence
  `τ_e = 0` there).

## Main definitions

* `Cslib.GameTheory.marginalCost`: marginal edge cost `c(x) + x * c'(x)`.
* `Cslib.GameTheory.NonatomicCongestionGame.IsOptimal`: socially optimal feasible flow.
* `Cslib.GameTheory.NonatomicCongestionGame.withMarginalCost`: the game `(G, r, c*)` with edge
  latencies replaced by `marginalCost`.
* `Cslib.GameTheory.NonatomicCongestionGame.withTaxes`: the taxed game `(G, r, c + τ)` with
  constant per-unit edge taxes `τ`.
* `Cslib.GameTheory.NonatomicCongestionGame.pigouvianTax`: the marginal-cost tax
  `τ_e = edgeFlow f* e * c' e (edgeFlow f* e)`.

## Main results

* `Cslib.GameTheory.hasDerivWithinAt_mul_marginalCost`: derivative of `x ↦ x * c(x)`.
* `Cslib.GameTheory.NonatomicCongestionGame.exists_isOptimal`: existence of optimal flows on
  compact feasible polytopes under continuous latencies.
* `Cslib.GameTheory.NonatomicCongestionGame.IsOptimal.isWardrop_withMarginalCost_within` and
  `Cslib.GameTheory.NonatomicCongestionGame.isOptimal_iff_isWardrop_withMarginalCost`
  ([Roughgarden2007Routing], Proposition 18.9 and Corollary 18.10): marginal-cost characterization
  of socially optimal flows.
* `Cslib.GameTheory.NonatomicCongestionGame.pigouvianTax_nonneg`,
  `Cslib.GameTheory.NonatomicCongestionGame.IsOptimal.isWardrop_withTaxes_pigouvianTax` and
  `Cslib.GameTheory.NonatomicCongestionGame.IsOptimal.cost_eq_of_isWardrop_withTaxes`
  ([Roughgarden2007Routing], Theorem 18.27): Pigouvian taxes induce optimal flows as Wardrop
  equilibria.

## References

* [Roughgarden2007Routing]
* [RoughgardenTardos2002]
-/

public section

namespace Cslib.GameTheory

open Set Filter
open scoped Topology

/-- The **marginal cost** `c*(x) = c(x) + x * c'(x)` of an edge with latency `c` and derivative
`c'` ([Roughgarden2007Routing], Section 18.3.1, p. 468). -/
@[expose] def marginalCost (c c' : ℝ → ℝ) (x : ℝ) : ℝ :=
  c x + x * c' x

/-- Product-rule derivative of `y ↦ y * c y` within a set `s`. -/
theorem hasDerivWithinAt_mul_marginalCost {c c' : ℝ → ℝ} {s : Set ℝ} {x : ℝ}
    (hc : HasDerivWithinAt c (c' x) s x) :
    HasDerivWithinAt (fun y : ℝ => y * c y) (marginalCost c c' x) s x := by
  have h := (hasDerivWithinAt_id x s).fun_smul hc
  simpa only [id_eq, smul_eq_mul, one_mul, add_comm, marginalCost] using h

namespace NonatomicCongestionGame

variable {K P E : Type*} [Fintype P] [DecidableEq E] (G : NonatomicCongestionGame K P E)

/-- A flow `f` is **socially optimal** for `G` if it is feasible and minimizes `G.cost` over all
feasible flows ([Roughgarden2007Routing], Section 18.2.1, p. 463). -/
@[expose] def IsOptimal [DecidableEq K] (f : P → ℝ) : Prop :=
  G.IsFeasible f ∧ ∀ g, G.IsFeasible g → G.cost f ≤ G.cost g

/-- If resource latencies are continuous on `[0, ∞)` and a feasible flow exists, then `G` admits a
socially optimal flow. -/
theorem exists_isOptimal [DecidableEq K] [Finite E]
    (hne : {f : P → ℝ | G.IsFeasible f}.Nonempty)
    (hc : ∀ e, ContinuousOn (G.latency e) (Ici 0)) :
    ∃ f, G.IsOptimal f := by
  have := Fintype.ofFinite E
  have hcont : ContinuousOn G.cost {f : P → ℝ | G.IsFeasible f} := by
    have heq : G.cost = fun f => ∑ e, G.edgeFlow f e * G.latency e (G.edgeFlow f e) :=
      funext G.cost_eq_sum_edgeFlow
    rw [heq]
    refine continuousOn_finsetSum _ fun e _ => ?_
    have hef : Continuous (fun f : P → ℝ => G.edgeFlow f e) :=
      continuous_finsetSum _ fun p _ => continuous_apply p
    exact hef.continuousOn.mul ((hc e).comp hef.continuousOn fun f hf => G.edgeFlow_nonneg hf.1 e)
  obtain ⟨f, hf, hmin⟩ := G.isCompact_setOf_isFeasible.exists_isMinOn hne hcont
  exact ⟨f, hf, hmin⟩

/-- The nonatomic congestion game `(G, r, c*)` obtained by replacing each edge latency `latency e`
by its marginal cost `marginalCost (latency e) (c' e)`
([Roughgarden2007Routing], Section 18.3.1). -/
def withMarginalCost (c' : E → ℝ → ℝ) : NonatomicCongestionGame K P E :=
  { G with latency := fun e => marginalCost (G.latency e) (c' e) }

/-- The taxed nonatomic congestion game `(G, r, c + τ)` obtained by adding a per-unit edge tax
`τ e` to each resource `e` ([Roughgarden2007Routing], Section 18.5.1). -/
def withTaxes (τ : E → ℝ) : NonatomicCongestionGame K P E :=
  { G with latency := fun e x => G.latency e x + τ e }

/-- The **Pigouvian marginal-cost tax** `τ_e = edgeFlow f e * c' e (edgeFlow f e)` associated with
a flow `f` and latency derivatives `c'`
([Roughgarden2007Routing], Section 18.5.1, Theorem 18.27). -/
@[expose] def pigouvianTax (c' : E → ℝ → ℝ) (f : P → ℝ) (e : E) : ℝ :=
  G.edgeFlow f e * c' e (G.edgeFlow f e)

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem withMarginalCost_commodity (c' : E → ℝ → ℝ) :
    (G.withMarginalCost c').commodity = G.commodity := by
  rfl

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem withMarginalCost_resources (c' : E → ℝ → ℝ) :
    (G.withMarginalCost c').resources = G.resources := by
  rfl

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem withMarginalCost_rate (c' : E → ℝ → ℝ) :
    (G.withMarginalCost c').rate = G.rate := by
  rfl

omit [DecidableEq E] in
@[simp]
theorem withMarginalCost_isFeasible [DecidableEq K] (c' : E → ℝ → ℝ) (f : P → ℝ) :
    (G.withMarginalCost c').IsFeasible f ↔ G.IsFeasible f := by
  rfl

@[simp]
theorem withMarginalCost_edgeFlow (c' : E → ℝ → ℝ) (f : P → ℝ) (e : E) :
    (G.withMarginalCost c').edgeFlow f e = G.edgeFlow f e := by
  rfl

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem withMarginalCost_latency (c' : E → ℝ → ℝ) (e : E) :
    (G.withMarginalCost c').latency e = marginalCost (G.latency e) (c' e) := by
  rfl

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem withTaxes_commodity (τ : E → ℝ) :
    (G.withTaxes τ).commodity = G.commodity := by
  rfl

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem withTaxes_resources (τ : E → ℝ) :
    (G.withTaxes τ).resources = G.resources := by
  rfl

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem withTaxes_rate (τ : E → ℝ) :
    (G.withTaxes τ).rate = G.rate := by
  rfl

omit [DecidableEq E] in
@[simp]
theorem withTaxes_isFeasible [DecidableEq K] (τ : E → ℝ) (f : P → ℝ) :
    (G.withTaxes τ).IsFeasible f ↔ G.IsFeasible f := by
  rfl

@[simp]
theorem withTaxes_edgeFlow (τ : E → ℝ) (f : P → ℝ) (e : E) :
    (G.withTaxes τ).edgeFlow f e = G.edgeFlow f e := by
  rfl

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem withTaxes_latency (τ : E → ℝ) (e : E) (x : ℝ) :
    (G.withTaxes τ).latency e x = G.latency e x + τ e := by
  rfl

/-- At the flow `f` that defines the Pigouvian taxes, the taxed network
`G.withTaxes (G.pigouvianTax c' f)` and the marginal-cost network `G.withMarginalCost c'` assign
identical path latencies to every path. -/
theorem withTaxes_pigouvianTax_pathLatency (c' : E → ℝ → ℝ) (f : P → ℝ) (p : P) :
    (G.withTaxes (G.pigouvianTax c' f)).pathLatency f p =
      (G.withMarginalCost c').pathLatency f p := by
  rfl

/-- A flow `f` is a Wardrop equilibrium of `G.withTaxes (G.pigouvianTax c' f)` if and only if it is
a Wardrop equilibrium of `G.withMarginalCost c'`. -/
theorem isWardrop_withTaxes_pigouvianTax_iff [DecidableEq K] (c' : E → ℝ → ℝ) (f : P → ℝ) :
    (G.withTaxes (G.pigouvianTax c' f)).IsWardrop f ↔ (G.withMarginalCost c').IsWardrop f := by
  rfl

section FirstOrderConditions

variable {G}

/-- Tangent-line lower bound on `[0, ∞)` for a convex function differentiable within `[0, ∞)`. -/
private theorem convexOn_mul_sub_le {h : ℝ → ℝ} (hconv : ConvexOn ℝ (Ici 0) h)
    {x y d : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hd : HasDerivWithinAt h d (Ici 0) x) :
    d * (y - x) ≤ h y - h x := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hsl := hconv.le_slope_of_hasDerivWithinAt hx hy hxy hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 hxy)] at hsl
    exact hsl
  · simp only [sub_self, mul_zero, le_rfl]
  · have hsl := hconv.slope_le_of_hasDerivWithinAt hy hx hyx hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hyx)] at hsl
    linarith

/-- First-order necessary condition: if `f` is optimal for `G` and `G.latency e` has derivative
`c' e (edgeFlow f e)` within `[0, ∞)` at `edgeFlow f e`, then `f` is a Wardrop equilibrium of
`G.withMarginalCost c'`. Notably, no convexity hypothesis is required for this direction. -/
theorem IsOptimal.isWardrop_withMarginalCost_within [DecidableEq K] [Finite E] {c' : E → ℝ → ℝ}
    {f : P → ℝ} (hf : G.IsOptimal f)
    (hderiv : ∀ e, HasDerivWithinAt (G.latency e) (c' e (G.edgeFlow f e))
      (Ici 0) (G.edgeFlow f e)) :
    (G.withMarginalCost c').IsWardrop f := by
  have := Fintype.ofFinite E
  rw [isWardrop_iff_variationalInequality]
  refine ⟨hf.1, fun g hg => ?_⟩
  have hmin : IsMinOn (fun h => ∑ e, G.edgeFlow h e * G.latency e (G.edgeFlow h e))
      {h | G.IsFeasible h} f := fun h hh => by
    change ∑ e, G.edgeFlow f e * G.latency e (G.edgeFlow f e) ≤
      ∑ e, G.edgeFlow h e * G.latency e (G.edgeFlow h e)
    rw [← G.cost_eq_sum_edgeFlow, ← G.cost_eq_sum_edgeFlow]
    exact hf.2 h hh
  simpa only [withMarginalCost_edgeFlow, withMarginalCost_latency] using
    hf.1.sum_mul_edgeFlow_le_of_isMinOn (H := fun e u => u * G.latency e u) hmin
      (fun e => hasDerivWithinAt_mul_marginalCost (hderiv e)) hg

/-- Sufficient condition under convexity: if `x ↦ x * latency e x` is convex on `[0, ∞)` and `f`
is a Wardrop equilibrium of `G.withMarginalCost c'`, then `f` is socially optimal for `G`. -/
theorem isOptimal_of_isWardrop_withMarginalCost_within [DecidableEq K] [Finite E] {c' : E → ℝ → ℝ}
    (hconv : ∀ e, ConvexOn ℝ (Ici 0) (fun x => x * G.latency e x))
    (hderiv : ∀ e x, 0 ≤ x → HasDerivWithinAt (G.latency e) (c' e x) (Ici 0) x)
    {f : P → ℝ} (hf : (G.withMarginalCost c').IsWardrop f) :
    G.IsOptimal f := by
  have := Fintype.ofFinite E
  obtain ⟨hfeas, hvi⟩ := isWardrop_iff_variationalInequality.1 hf
  rw [withMarginalCost_isFeasible] at hfeas
  refine ⟨hfeas, fun g hg => ?_⟩
  have hvi_g := hvi g hg
  simp only [withMarginalCost_edgeFlow, withMarginalCost_latency] at hvi_g
  rw [G.cost_eq_sum_edgeFlow, G.cost_eq_sum_edgeFlow]
  have htan : ∀ e ∈ (Finset.univ : Finset E),
      marginalCost (G.latency e) (c' e) (G.edgeFlow f e) *
        (G.edgeFlow g e - G.edgeFlow f e) ≤
        G.edgeFlow g e * G.latency e (G.edgeFlow g e) -
          G.edgeFlow f e * G.latency e (G.edgeFlow f e) := by
    intro e _
    exact convexOn_mul_sub_le (hconv e) (G.edgeFlow_nonneg hfeas.1 e)
      (G.edgeFlow_nonneg hg.1 e)
      (hasDerivWithinAt_mul_marginalCost (hderiv e _ (G.edgeFlow_nonneg hfeas.1 e)))
  have hsum := Finset.sum_le_sum htan
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum
  linarith

/-- **Characterization of optimal flows and equivalence with marginal-cost Wardrop equilibria**
([Roughgarden2007Routing], Proposition 18.9 and Corollary 18.10, pp. 468–469): when
`x ↦ x * latency e x` is convex on `[0, ∞)` and `latency e` has derivative `c' e` within `[0, ∞)`,
a flow `f` is socially optimal for `G` if and only if `f` is a Wardrop equilibrium of
`G.withMarginalCost c'`.

*Precision note relative to [Roughgarden2007Routing], Proposition 18.9:* the source assumes that
`x ↦ x * c_e(x)` is convex and continuously differentiable (`C¹`) on `[0, ∞)`, which admits
latencies such as `c_e(x) = √x` where `x * √x = x ^ (3 / 2)` is `C¹` at `0` even though `c_e` is
not differentiable at `0`. To write the marginal cost explicitly as `c_e(x) + x * c'_e(x)`, the
hypothesis `hderiv` here requires right-differentiability of `G.latency e` itself within `[0, ∞)`
at every `x ≥ 0` (including `x = 0`). -/
theorem isOptimal_iff_isWardrop_withMarginalCost [DecidableEq K] [Finite E] {c' : E → ℝ → ℝ}
    (hconv : ∀ e, ConvexOn ℝ (Ici 0) (fun x => x * G.latency e x))
    (hderiv : ∀ e x, 0 ≤ x → HasDerivWithinAt (G.latency e) (c' e x) (Ici 0) x)
    {f : P → ℝ} :
    G.IsOptimal f ↔ (G.withMarginalCost c').IsWardrop f :=
  ⟨fun hf => hf.isWardrop_withMarginalCost_within fun e =>
      hderiv e _ (G.edgeFlow_nonneg hf.1.1 e),
    isOptimal_of_isWardrop_withMarginalCost_within hconv hderiv⟩

/-! ### Theorem 18.27: Pigouvian marginal-cost taxes -/

/-- When resource latencies are nondecreasing on `[0, ∞)`, the Pigouvian marginal-cost tax
`τ_e = edgeFlow f e * c' e (edgeFlow f e)` of any nonnegative flow `f` is nonnegative. -/
theorem pigouvianTax_nonneg {c' : E → ℝ → ℝ} {f : P → ℝ}
    (hf : ∀ p, 0 ≤ f p)
    (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0))
    (hderiv : ∀ e, HasDerivWithinAt (G.latency e) (c' e (G.edgeFlow f e))
      (Ici 0) (G.edgeFlow f e))
    (e : E) :
    0 ≤ G.pigouvianTax c' f e := by
  have hx : 0 ≤ G.edgeFlow f e := G.edgeFlow_nonneg hf e
  refine mul_nonneg hx ?_
  have hd_ioi : HasDerivWithinAt (G.latency e) (c' e (G.edgeFlow f e))
      (Ioi (G.edgeFlow f e)) (G.edgeFlow f e) :=
    (hderiv e).mono fun y hy => le_trans hx (le_of_lt hy)
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).1 hd_ioi
  have hnonneg : ∀ᶠ y in 𝓝[>] (G.edgeFlow f e), 0 ≤ slope (G.latency e) (G.edgeFlow f e) y := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.2 (hm e hx (le_trans hx (le_of_lt hy)) (le_of_lt hy)))
      (sub_nonneg.2 (le_of_lt hy))
  exact ge_of_tendsto hslope hnonneg

/-- **Pigouvian marginal-cost taxes induce optimal flows as Wardrop equilibria**
([Roughgarden2007Routing], Theorem 18.27 and subsequent remark, p. 478): if `f*` is socially
optimal for `G` and `G.latency e` has derivative `c' e (edgeFlow f* e)` within `[0, ∞)` at
`edgeFlow f* e`, then `f*` is a Wardrop equilibrium of the taxed network
`G.withTaxes (G.pigouvianTax c' f*)`. No convexity assumption on `x ↦ x * latency e x` is needed. -/
theorem IsOptimal.isWardrop_withTaxes_pigouvianTax [DecidableEq K] [Finite E] {c' : E → ℝ → ℝ}
    {f : P → ℝ} (hf : G.IsOptimal f)
    (hderiv : ∀ e, HasDerivWithinAt (G.latency e) (c' e (G.edgeFlow f e))
      (Ici 0) (G.edgeFlow f e)) :
    (G.withTaxes (G.pigouvianTax c' f)).IsWardrop f :=
  hf.isWardrop_withMarginalCost_within hderiv

/-- If `c` is nondecreasing on `[0, ∞)` and achieves the same value at two distinct points
`x, y ≥ 0`, then its derivative within `[0, ∞)` at `x` (when it exists) is `0`. -/
private theorem deriv_eq_zero_of_monotoneOn_eq {c : ℝ → ℝ} {d x y : ℝ}
    (hm : MonotoneOn c (Ici 0)) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : y ≠ x) (hc : c y = c x)
    (hd : HasDerivWithinAt c d (Ici 0) x) : d = 0 := by
  set s := Ioo (min x y) (max x y)
  have hlt : min x y < max x y := by rcases hxy.lt_or_gt with h | h <;> simp [h.le, h]
  have hsub : s ⊆ Ici 0 := fun z hz => (le_min hx hy).trans hz.1.le
  have hnot : x ∉ s := fun h => by rcases le_total x y with hle | hle <;> simp_all [s]
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' hnot).1 (hd.mono hsub)
  have hzero : Tendsto (slope c x) (𝓝[s] x) (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hmin_eq : c (min x y) = c x := by
        rcases min_cases x y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h, hc]
      have hmax_eq : c (max x y) = c x := by
        rcases max_cases x y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h, hc]
      have hcz : c z = c x := le_antisymm
        (hmax_eq ▸ hm (hsub hz) (le_max_of_le_left hx) hz.2.le)
        (hmin_eq ▸ hm (le_min hx hy) (hsub hz) hz.1.le)
      rw [slope_def_field, hcz, sub_self, zero_div])
  have : (𝓝[s] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 <| by
    rw [closure_Ioo hlt.ne]
    exact ⟨min_le_left x y, le_max_left x y⟩
  exact tendsto_nhds_unique hslope hzero

/-- When resource latencies are nondecreasing on `[0, ∞)` and differentiable at `edgeFlow f* e`,
*every* Wardrop equilibrium `g` of the Pigouvian-taxed network
`G.withTaxes (G.pigouvianTax c' f*)` has the same total social cost on `G` as the optimal flow `f*`
and is therefore socially optimal for `G` (so Pigouvian taxes reduce the price of anarchy on `G` to
`1`, including on networks with constant edges such as Pigou's and Braess's examples). -/
theorem IsOptimal.cost_eq_of_isWardrop_withTaxes [DecidableEq K] [Finite E] {c' : E → ℝ → ℝ}
    {f g : P → ℝ} (hf : G.IsOptimal f)
    (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0))
    (hderiv : ∀ e, HasDerivWithinAt (G.latency e) (c' e (G.edgeFlow f e))
      (Ici 0) (G.edgeFlow f e))
    (hg : (G.withTaxes (G.pigouvianTax c' f)).IsWardrop g) :
    G.cost g = G.cost f ∧ G.IsOptimal g := by
  have := Fintype.ofFinite E
  set τ := G.pigouvianTax c' f
  have hm_tax : ∀ e, MonotoneOn ((G.withTaxes τ).latency e) (Ici 0) :=
    fun e x hx y hy hxy => add_le_add_left (hm e hx hy hxy) (τ e)
  have hf_tax : (G.withTaxes τ).IsWardrop f := hf.isWardrop_withTaxes_pigouvianTax hderiv
  have htax_cost : ∀ h : P → ℝ, (G.withTaxes τ).cost h = G.cost h + ∑ e, G.edgeFlow h e * τ e := by
    intro h
    rw [(G.withTaxes τ).cost_eq_sum_edgeFlow, G.cost_eq_sum_edgeFlow, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [withTaxes_edgeFlow, withTaxes_latency]
    ring
  have htax_eq : ∑ e, G.edgeFlow g e * τ e = ∑ e, G.edgeFlow f e * τ e := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rcases eq_or_ne (G.edgeFlow g e) (G.edgeFlow f e) with heq | hne
    · rw [heq]
    · have hlat := isWardrop_latency_eq hm_tax hg hf_tax e
      simp only [withTaxes_edgeFlow, withTaxes_latency, add_left_inj] at hlat
      have hc'0 : c' e (G.edgeFlow f e) = 0 :=
        deriv_eq_zero_of_monotoneOn_eq (hm e) (G.edgeFlow_nonneg hf.1.1 e)
          (G.edgeFlow_nonneg hg.1.1 e) hne hlat (hderiv e)
      simp only [τ, pigouvianTax, hc'0, mul_zero]
  have hcost_tax := isWardrop_cost_eq hm_tax hg hf_tax
  rw [htax_cost g, htax_cost f, htax_eq] at hcost_tax
  have hcost : G.cost g = G.cost f := add_right_cancel hcost_tax
  exact ⟨hcost, hg.1, fun q hq => hcost ▸ hf.2 q hq⟩

end FirstOrderConditions

end NonatomicCongestionGame

end Cslib.GameTheory
