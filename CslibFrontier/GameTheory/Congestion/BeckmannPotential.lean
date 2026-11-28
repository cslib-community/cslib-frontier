/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Congestion.PigouBound
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Beckmann's potential and existence and uniqueness of Wardrop equilibria

In a nonatomic congestion game `G`, a flow `f` is a Wardrop equilibrium (`G.IsWardrop f`) when it
is feasible and routes flow only along minimum-latency paths of each commodity. Following
Roughgarden [Roughgarden2007Routing], Sections 18.3.1 and 18.4.1 (originally due to Beckmann,
McGuire and Winsten, 1956, and Smith, 1979), this module establishes:

* **Variational inequality characterization** (`isWardrop_iff_forall_cost_le_sum_mul_pathLatency`,
  `isWardrop_iff_variationalInequality`, [Roughgarden2007Routing], Proposition 18.20): a feasible
  flow `f` is a Wardrop equilibrium if and only if `∑ e, latency e (edgeFlow f e) * edgeFlow f e ≤
  ∑ e, latency e (edgeFlow f e) * edgeFlow g e` for every feasible flow `g`.
* **Beckmann's potential** (`beckmannPotential`, `isWardrop_iff_isMinOn_beckmannPotential`,
  [Roughgarden2007Routing], Equation (18.3) and Proposition 18.11): for continuous nondecreasing
  latencies on `[0, ∞)`, a feasible flow is a Wardrop equilibrium if and only if it globally
  minimizes `Φ(f) = ∑ e, ∫ x in 0..edgeFlow f e, latency e x` over all feasible flows.
* **Existence and essential uniqueness** (`exists_isWardrop_of_nonempty`, `exists_isWardrop`,
  `isWardrop_latency_eq`, `isWardrop_cost_eq`, [Roughgarden2007Routing], Theorem 18.8(a–b)):
  because the feasible flow polytope is compact (`isCompact_setOf_isFeasible`) and `Φ` is
  continuous on nonnegative flows (`continuousOn_beckmannPotential`), a Wardrop equilibrium exists
  whenever a feasible flow exists; and for nondecreasing latencies, any two Wardrop equilibria
  induce identical resource latencies on every edge and therefore have identical total cost, so the
  price of stability equals the price of anarchy. In particular, Pigou's linear network has the
  unique Wardrop equilibrium `![1, 0]` (`pigouNetwork_id_isWardrop_iff`,
  [RoughgardenTardos2007], Example 17.1), giving price of stability `4/3`.
* **Potential-function price-of-anarchy bounds** (`IsWardrop.cost_le_mul_of_le_mul_integral`,
  `IsWardrop.cost_le_succ_mul_of_mem_polynomialLatencies`, [Roughgarden2007Routing], Theorem 18.16
  and Corollary 18.17): if `x * c_e(x) ≤ γ * ∫_0^x c_e(y) dy` on `[0, ∞)`, the price of anarchy is
  at most `γ`, giving `d + 1` for degree-`d` polynomial latencies.

## Main definitions

* `Cslib.GameTheory.NonatomicCongestionGame.beckmannPotential`: Beckmann's potential
  `∑ e, ∫ x in 0..edgeFlow f e, latency e x`.

## Main results

* `Cslib.GameTheory.NonatomicCongestionGame.isWardrop_iff_forall_cost_le_sum_mul_pathLatency` and
  `Cslib.GameTheory.NonatomicCongestionGame.isWardrop_iff_variationalInequality`
  ([Roughgarden2007Routing], Proposition 18.20): both forms of the variational inequality
  characterization of Wardrop equilibria.
* `Cslib.GameTheory.NonatomicCongestionGame.convex_setOf_isFeasible` and
  `Cslib.GameTheory.NonatomicCongestionGame.isCompact_setOf_isFeasible`: convexity and compactness
  of the feasible flow polytope.
* `Cslib.GameTheory.NonatomicCongestionGame.convexOn_beckmannPotential` and
  `Cslib.GameTheory.NonatomicCongestionGame.continuousOn_beckmannPotential`: convexity and
  continuity of Beckmann's potential.
* `Cslib.GameTheory.NonatomicCongestionGame.isWardrop_iff_isMinOn_beckmannPotential`
  ([Roughgarden2007Routing], Proposition 18.11): Wardrop equilibria are the global minimizers of
  Beckmann's potential over feasible flows.
* `Cslib.GameTheory.NonatomicCongestionGame.exists_isWardrop_of_nonempty` and
  `Cslib.GameTheory.NonatomicCongestionGame.exists_isWardrop` ([Roughgarden2007Routing],
  Theorem 18.8(a)): existence of Wardrop equilibria.
* `Cslib.GameTheory.NonatomicCongestionGame.isWardrop_latency_eq`,
  `Cslib.GameTheory.NonatomicCongestionGame.isWardrop_pathLatency_eq` and
  `Cslib.GameTheory.NonatomicCongestionGame.isWardrop_cost_eq` ([Roughgarden2007Routing],
  Theorem 18.8(b)): essential uniqueness of Wardrop equilibria.
* `Cslib.GameTheory.NonatomicCongestionGame.pigouNetwork_id_isWardrop_iff` and
  `Cslib.GameTheory.NonatomicCongestionGame.pigouNetwork_id_priceOfStability`
  ([RoughgardenTardos2007], Example 17.1): uniqueness of the Wardrop equilibrium on Pigou's linear
  network and its `4/3` price of stability.
* `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.cost_le_mul_of_le_mul_integral` and
  `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.cost_le_succ_mul_of_mem_polynomialLatencies`
  ([Roughgarden2007Routing], Theorem 18.16 and Corollary 18.17): potential-function bounds on the
  price of anarchy.

## References

* [Roughgarden2007Routing]
* [RoughgardenTardos2002]
* [RoughgardenTardos2007]
-/

public section

namespace Cslib.GameTheory.NonatomicCongestionGame

open Set Filter intervalIntegral
open scoped Topology

section Feasibility

variable {K P E : Type*} [Fintype P] (G : NonatomicCongestionGame K P E)

/-- Nonnegative flows induce nonnegative edge flows. -/
theorem edgeFlow_nonneg [DecidableEq E] {f : P → ℝ} (hf : ∀ p, 0 ≤ f p) (e : E) :
    0 ≤ G.edgeFlow f e :=
  Finset.sum_nonneg fun p _ => hf p

/-- `edgeFlow` is additive in the path flow. -/
theorem edgeFlow_add [DecidableEq E] (f g : P → ℝ) (e : E) :
    G.edgeFlow (f + g) e = G.edgeFlow f e + G.edgeFlow g e := by
  simp only [edgeFlow, Pi.add_apply, Finset.sum_add_distrib]

/-- `edgeFlow` commutes with scalar multiplication. -/
theorem edgeFlow_smul [DecidableEq E] (c : ℝ) (f : P → ℝ) (e : E) :
    G.edgeFlow (c • f) e = c * G.edgeFlow f e := by
  simp only [edgeFlow, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- Every coordinate of a feasible flow is bounded by its commodity's demand rate. -/
theorem IsFeasible.le_rate [DecidableEq K] {f : P → ℝ} (hf : G.IsFeasible f) (p : P) :
    f p ≤ G.rate (G.commodity p) := by
  rw [← hf.2 (G.commodity p)]
  exact Finset.single_le_sum (fun q _ => hf.1 q)
    (Finset.mem_filter.2 ⟨Finset.mem_univ p, rfl⟩)

/-- Convex combinations of feasible flows are feasible. -/
theorem IsFeasible.convex_combo [DecidableEq K] {f g : P → ℝ} (hf : G.IsFeasible f)
    (hg : G.IsFeasible g) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    G.IsFeasible (a • f + b • g) := by
  refine ⟨fun p => add_nonneg (mul_nonneg ha (hf.1 p)) (mul_nonneg hb (hg.1 p)), fun k => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    hf.2 k, hg.2 k]
  linear_combination G.rate k * hab

/-- The set of feasible flows is convex. -/
theorem convex_setOf_isFeasible [DecidableEq K] : Convex ℝ {f : P → ℝ | G.IsFeasible f} :=
  fun _ hf _ hg _ _ ha hb hab => hf.convex_combo G hg ha hb hab

/-- The feasible flow polytope `{f : P → ℝ | G.IsFeasible f}` is compact. -/
theorem isCompact_setOf_isFeasible [DecidableEq K] :
    IsCompact {f : P → ℝ | G.IsFeasible f} := by
  have hbox : IsCompact (Set.pi Set.univ fun p : P => Icc 0 (G.rate (G.commodity p))) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ fun f hf p _ => ⟨hf.1 p, hf.le_rate G p⟩
  have h1 : IsClosed {f : P → ℝ | ∀ p, 0 ≤ f p} := by
    simpa only [ofPred_forall] using
      isClosed_iInter fun p => isClosed_le continuous_const (continuous_apply p)
  have h2 : IsClosed {f : P → ℝ | ∀ k, ∑ p with G.commodity p = k, f p = G.rate k} := by
    simpa only [ofPred_forall] using isClosed_iInter fun k =>
      isClosed_eq (continuous_finsetSum _ fun p _ => continuous_apply p) continuous_const
  exact h1.inter h2

/-- If every commodity has nonnegative demand rate and every commodity with positive demand has at
least one path, then a feasible flow exists. -/
theorem nonempty_setOf_isFeasible [DecidableEq K] (hr : ∀ k, 0 ≤ G.rate k)
    (hpath : ∀ k, G.rate k ≠ 0 → ∃ p, G.commodity p = k) :
    {f : P → ℝ | G.IsFeasible f}.Nonempty := by
  let f : P → ℝ := fun p =>
    G.rate (G.commodity p) /
      ((Finset.univ.filter (G.commodity · = G.commodity p)).card : ℝ)
  refine ⟨f, ⟨fun p => div_nonneg (hr _) (Nat.cast_nonneg _), fun k => ?_⟩⟩
  set S := Finset.univ.filter (G.commodity · = k)
  have hcongr : ∑ p ∈ S, f p = ∑ _p ∈ S, G.rate k / (S.card : ℝ) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpk : G.commodity p = k := (Finset.mem_filter.1 hp).2
    simp only [f, hpk, S]
  rw [hcongr, Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [h0, Nat.cast_zero, zero_mul]
    by_contra hne
    obtain ⟨p, hp⟩ := hpath k (Ne.symm hne)
    exact Finset.notMem_empty p
      ((Finset.card_eq_zero.1 h0).subset (Finset.mem_filter.2 ⟨Finset.mem_univ p, hp⟩))
  · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hpos.ne')

end Feasibility

/-! ### Proposition 18.20: variational inequality characterization -/

section VariationalInequality

variable {K P E : Type*} [Fintype P] [DecidableEq E] {G : NonatomicCongestionGame K P E}

/-- **Variational inequality characterization, path form** ([Roughgarden2007Routing],
Proposition 18.20): a flow `f` is a Wardrop equilibrium if and only if `f` is feasible and
`cost f ≤ ∑ p, g p * pathLatency f p` for every feasible flow `g`. -/
theorem isWardrop_iff_forall_cost_le_sum_mul_pathLatency [DecidableEq K] {f : P → ℝ} :
    G.IsWardrop f ↔
      G.IsFeasible f ∧ ∀ g, G.IsFeasible g → G.cost f ≤ ∑ p, g p * G.pathLatency f p := by
  refine ⟨fun hf => ⟨hf.1, fun g hg => hf.cost_le_sum_mul_pathLatency hg⟩, ?_⟩
  rintro ⟨hf, hvi⟩
  refine ⟨hf, fun p q hpq hfp => ?_⟩
  classical
  by_cases hpne : p = q
  · subst hpne; exact le_rfl
  · let g : P → ℝ := fun r => if r = p then 0 else if r = q then f q + f p else f r
    have hg_nonneg : ∀ r, 0 ≤ g r := fun r => by
      dsimp only [g]
      split_ifs
      · exact le_rfl
      · exact add_nonneg (hf.1 q) (hf.1 p)
      · exact hf.1 r
    have hg_sum : ∀ (S : Finset P) (w : P → ℝ), (p ∈ S ↔ q ∈ S) →
        ∑ r ∈ S, g r * w r - ∑ r ∈ S, f r * w r =
          if p ∈ S then f p * (w q - w p) else 0 := by
      intro S w hpqS
      rw [← Finset.sum_sub_distrib]
      by_cases hpS : p ∈ S
      · have hqS : q ∈ S := hpqS.1 hpS
        simp only [hpS, ↓reduceIte]
        rw [← Finset.add_sum_erase _ _ hpS]
        have hqS' : q ∈ S.erase p := Finset.mem_erase.2 ⟨Ne.symm hpne, hqS⟩
        rw [← Finset.add_sum_erase _ _ hqS']
        have hrest : ∑ x ∈ (S.erase p).erase q, (g x * w x - f x * w x) = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hxq : x ≠ q := (Finset.mem_erase.1 hx).1
          have hxp : x ≠ p := (Finset.mem_erase.1 (Finset.mem_erase.1 hx).2).1
          simp only [g, hxp, hxq, ↓reduceIte, sub_self]
        rw [hrest, add_zero]
        have hqp : q ≠ p := Ne.symm hpne
        simp only [g, hqp, ↓reduceIte]
        ring
      · have hqS : q ∉ S := fun hq => hpS (hpqS.2 hq)
        simp only [hpS, ↓reduceIte]
        refine Finset.sum_eq_zero fun x hx => ?_
        have hxp : x ≠ p := fun h => hpS (h ▸ hx)
        have hxq : x ≠ q := fun h => hqS (h ▸ hx)
        simp only [g, hxp, hxq, ↓reduceIte, sub_self]
    have hg : G.IsFeasible g := by
      refine ⟨hg_nonneg, fun k => ?_⟩
      have hdiff := hg_sum (Finset.univ.filter (G.commodity · = k)) (fun _ => 1)
        (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpq])
      simp only [mul_one, sub_self, mul_zero, ite_self] at hdiff
      linarith [hf.2 k]
    have hcost := hvi g hg
    unfold cost at hcost
    have hdiff := hg_sum Finset.univ (G.pathLatency f) (by simp only [Finset.mem_univ])
    simp only [Finset.mem_univ, ↓reduceIte] at hdiff
    have h0 : 0 ≤ f p * (G.pathLatency f q - G.pathLatency f p) := by linarith
    have hsub : 0 ≤ G.pathLatency f q - G.pathLatency f p :=
      nonneg_of_mul_nonneg_right h0 hfp
    linarith

/-- **Variational inequality characterization, edge form** ([Roughgarden2007Routing],
Proposition 18.20): a flow `f` is a Wardrop equilibrium if and only if `f` is feasible and
`∑ e, latency e (edgeFlow f e) * edgeFlow f e ≤ ∑ e, latency e (edgeFlow f e) * edgeFlow g e`
for every feasible flow `g`. -/
theorem isWardrop_iff_variationalInequality [DecidableEq K] [Fintype E] {f : P → ℝ} :
    G.IsWardrop f ↔
      G.IsFeasible f ∧ ∀ g, G.IsFeasible g →
        ∑ e, G.latency e (G.edgeFlow f e) * G.edgeFlow f e ≤
          ∑ e, G.latency e (G.edgeFlow f e) * G.edgeFlow g e := by
  rw [isWardrop_iff_forall_cost_le_sum_mul_pathLatency]
  refine and_congr_right fun _ => forall_congr' fun g => imp_congr_right fun _ => ?_
  have h1 : G.cost f = ∑ e, G.latency e (G.edgeFlow f e) * G.edgeFlow f e := by
    rw [G.cost_eq_sum_edgeFlow]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  have h2 : ∑ p, g p * G.pathLatency f p =
      ∑ e, G.latency e (G.edgeFlow f e) * G.edgeFlow g e := by
    simp only [pathLatency]
    rw [G.sum_mul_sum_resources]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  rw [h1, h2]

end VariationalInequality

/-! ### Proposition 18.11: Beckmann's potential -/

section BeckmannPotential

variable {K P E : Type*} [Fintype P] [DecidableEq E] [Fintype E]
  (G : NonatomicCongestionGame K P E)

/-- **Beckmann's potential** ([Roughgarden2007Routing], Equation (18.3), originally due to
Beckmann, McGuire and Winsten, 1956): `Φ(f) = ∑ e, ∫ x in 0..edgeFlow f e, latency e x`. -/
noncomputable def beckmannPotential (f : P → ℝ) : ℝ :=
  ∑ e, ∫ x in (0 : ℝ)..G.edgeFlow f e, G.latency e x

/-- Unfolding equation for `beckmannPotential`. -/
theorem beckmannPotential_def (f : P → ℝ) :
    G.beckmannPotential f = ∑ e, ∫ x in (0 : ℝ)..G.edgeFlow f e, G.latency e x := by
  rfl

/-- A function continuous on `[0, ∞)` is interval-integrable between any two nonnegative reals. -/
private theorem intervalIntegrable_of_continuousOn_Ici {c : ℝ → ℝ} (hc : ContinuousOn c (Ici 0))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable c MeasureTheory.volume a b :=
  (hc.mono (fun _ hx => le_trans (le_min ha hb) (mem_Icc.1 hx).1)).intervalIntegrable

/-- Adjacent-interval difference formula for the primitive `u ↦ ∫ x in 0..u, c x` on `[0, ∞)`. -/
private theorem integral_sub_zero_eq {c : ℝ → ℝ} (hc : ContinuousOn c (Ici 0))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ x in (0 : ℝ)..b, c x) - (∫ x in (0 : ℝ)..a, c x) = ∫ x in a..b, c x :=
  sub_eq_of_eq_add' (integral_add_adjacent_intervals
    (intervalIntegrable_of_continuousOn_Ici hc le_rfl ha)
    (intervalIntegrable_of_continuousOn_Ici hc ha hb)).symm

/-- Two-sided subgradient inequality for the primitive `u ↦ ∫ x in 0..u, c x` of a continuous
nondecreasing function on `[0, ∞)`. -/
private theorem mul_sub_le_integral_sub_and_le {c : ℝ → ℝ} (hc : ContinuousOn c (Ici 0))
    (hm : MonotoneOn c (Ici 0)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    c a * (b - a) ≤ (∫ x in (0 : ℝ)..b, c x) - (∫ x in (0 : ℝ)..a, c x) ∧
      (∫ x in (0 : ℝ)..b, c x) - (∫ x in (0 : ℝ)..a, c x) ≤ c b * (b - a) := by
  rw [integral_sub_zero_eq hc ha hb]
  have hint_ab := intervalIntegrable_of_continuousOn_Ici hc ha hb
  rcases le_total a b with hab | hba
  · constructor
    · have hle : ∫ _ in a..b, c a ≤ ∫ x in a..b, c x :=
        integral_mono_on hab intervalIntegrable_const hint_ab
          fun x hx => hm ha (le_trans ha hx.1) hx.1
      rw [integral_const, smul_eq_mul, mul_comm] at hle
      exact hle
    · have hle : ∫ x in a..b, c x ≤ ∫ _ in a..b, c b :=
        integral_mono_on hab hint_ab intervalIntegrable_const
          fun x hx => hm (le_trans ha hx.1) hb hx.2
      rw [integral_const, smul_eq_mul, mul_comm] at hle
      exact hle
  · rw [integral_symm b a]
    have hint_ba := intervalIntegrable_of_continuousOn_Ici hc hb ha
    have hlo : ∫ _ in b..a, c b ≤ ∫ x in b..a, c x :=
      integral_mono_on hba intervalIntegrable_const hint_ba
        fun x hx => hm hb (le_trans hb hx.1) hx.1
    have hhi : ∫ x in b..a, c x ≤ ∫ _ in b..a, c a :=
      integral_mono_on hba hint_ba intervalIntegrable_const
        fun x hx => hm (le_trans hb hx.1) ha hx.2
    rw [integral_const, smul_eq_mul] at hlo hhi
    constructor <;> linarith

/-- By the Fundamental Theorem of Calculus, `u ↦ ∫ x in 0..u, c x` has derivative `c a` within
`[0, ∞)` at every `a ≥ 0` when `c` is continuous on `[0, ∞)`. -/
private theorem hasDerivWithinAt_primitive_Ici {c : ℝ → ℝ} (hc : ContinuousOn c (Ici 0))
    {a : ℝ} (ha : 0 ≤ a) :
    HasDerivWithinAt (fun u => ∫ x in (0 : ℝ)..u, c x) (c a) (Ici 0) a := by
  have : Fact (a ∈ Icc 0 (a + 1)) := ⟨⟨ha, by linarith⟩⟩
  have hcont : ContinuousOn c (Icc 0 (a + 1)) := hc.mono Icc_subset_Ici_self
  have hd : HasDerivWithinAt (fun u => ∫ x in (0 : ℝ)..u, c x) (c a) (Icc 0 (a + 1)) a :=
    integral_hasDerivWithinAt_right (intervalIntegrable_of_continuousOn_Ici hc le_rfl ha)
      (hcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc a)
      (hcont a ⟨ha, by linarith⟩)
  exact hd.mono_of_mem_nhdsWithin <|
    Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith)))

/-- First-order variational inequality for a separable edge-flow objective: if `f` is feasible and
minimizes `g ↦ ∑ e, H e (G.edgeFlow g e)` over `{g | G.IsFeasible g}`, and each `H e` has
derivative `d e` within `[0, ∞)` at `G.edgeFlow f e`, then
`∑ e, d e * G.edgeFlow f e ≤ ∑ e, d e * G.edgeFlow g e` for every feasible flow `g`. -/
theorem IsFeasible.sum_mul_edgeFlow_le_of_isMinOn [DecidableEq K]
    {G : NonatomicCongestionGame K P E} {H : E → ℝ → ℝ} {d : E → ℝ} {f : P → ℝ}
    (hf : G.IsFeasible f)
    (hmin : IsMinOn (fun g => ∑ e, H e (G.edgeFlow g e)) {g | G.IsFeasible g} f)
    (hderiv : ∀ e, HasDerivWithinAt (H e) (d e) (Ici 0) (G.edgeFlow f e))
    {g : P → ℝ} (hg : G.IsFeasible g) :
    ∑ e, d e * G.edgeFlow f e ≤ ∑ e, d e * G.edgeFlow g e := by
  have hterm : ∀ e, HasDerivWithinAt
      (fun t : ℝ => H e ((1 - t) * G.edgeFlow f e + t * G.edgeFlow g e))
      (d e * (G.edgeFlow g e - G.edgeFlow f e)) (Icc 0 1) 0 := by
    intro e
    have hlin : HasDerivAt (fun t : ℝ => (1 - t) * G.edgeFlow f e + t * G.edgeFlow g e)
        (G.edgeFlow g e - G.edgeFlow f e) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (1 - t) * G.edgeFlow f e) (-G.edgeFlow f e) 0 := by
        simpa only [id_eq, smul_eq_mul, neg_one_mul] using
          ((hasDerivAt_id (0 : ℝ)).const_sub (1 : ℝ)).smul_const (G.edgeFlow f e)
      have h2 : HasDerivAt (fun t : ℝ => t * G.edgeFlow g e) (G.edgeFlow g e) 0 := by
        simpa only [id_eq, smul_eq_mul, one_mul] using
          (hasDerivAt_id (0 : ℝ)).smul_const (G.edgeFlow g e)
      simpa only [sub_eq_neg_add] using h1.fun_add h2
    have h0 : (1 - (0 : ℝ)) * G.edgeFlow f e + (0 : ℝ) * G.edgeFlow g e = G.edgeFlow f e := by
      ring
    have hH : HasDerivWithinAt (H e) (d e) (Ici 0)
        ((1 - (0 : ℝ)) * G.edgeFlow f e + (0 : ℝ) * G.edgeFlow g e) := by
      rw [h0]
      exact hderiv e
    have hmaps : MapsTo (fun t : ℝ => (1 - t) * G.edgeFlow f e + t * G.edgeFlow g e)
        (Icc 0 1) (Ici 0) := fun t ⟨ht0, ht1⟩ =>
      add_nonneg (mul_nonneg (sub_nonneg.2 ht1) (G.edgeFlow_nonneg hf.1 e))
        (mul_nonneg ht0 (G.edgeFlow_nonneg hg.1 e))
    simpa only [Function.comp_def, smul_eq_mul,
      mul_comm (G.edgeFlow g e - G.edgeFlow f e)] using
      hH.scomp (0 : ℝ) hlin.hasDerivWithinAt hmaps
  have hsum : HasDerivWithinAt
      (fun t : ℝ => ∑ e, H e ((1 - t) * G.edgeFlow f e + t * G.edgeFlow g e))
      (∑ e, d e * (G.edgeFlow g e - G.edgeFlow f e)) (Ioc 0 1) 0 :=
    (HasDerivWithinAt.fun_sum fun e _ => hterm e).mono Ioc_subset_Icc_self
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1 hsum
  have hnonneg : ∀ᶠ t in 𝓝[Ioc 0 1] (0 : ℝ),
      0 ≤ slope (fun t : ℝ => ∑ e, H e ((1 - t) * G.edgeFlow f e + t * G.edgeFlow g e)) 0 t := by
    filter_upwards [self_mem_nhdsWithin] with t ⟨ht0, ht1⟩
    rw [slope_def_field]
    have hfeas : G.IsFeasible ((1 - t) • f + t • g) :=
      hf.convex_combo G hg (sub_nonneg.2 ht1) ht0.le (sub_add_cancel 1 t)
    have hval_t : ∑ e, H e ((1 - t) * G.edgeFlow f e + t * G.edgeFlow g e) =
        ∑ e, H e (G.edgeFlow ((1 - t) • f + t • g) e) :=
      Finset.sum_congr rfl fun e _ => by simp only [G.edgeFlow_add, G.edgeFlow_smul]
    have hval_0 : ∑ e, H e (1 * G.edgeFlow f e + 0 * G.edgeFlow g e) =
        ∑ e, H e (G.edgeFlow f e) :=
      Finset.sum_congr rfl fun e _ => by ring_nf
    simp only [sub_zero]
    rw [hval_t, hval_0]
    exact div_nonneg (sub_nonneg.2 (hmin hfeas)) ht0.le
  have hnt : (𝓝[Ioc (0 : ℝ) 1] 0).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1
      (by rw [closure_Ioc zero_ne_one]; exact left_mem_Icc.2 zero_le_one)
  have hlim := ge_of_tendsto hslope hnonneg
  simp only [mul_sub, Finset.sum_sub_distrib] at hlim
  linarith

/-- `beckmannPotential` is continuous on the set of nonnegative path flows when resource latencies
are continuous on `[0, ∞)`. -/
theorem continuousOn_beckmannPotential (hc : ∀ e, ContinuousOn (G.latency e) (Ici 0)) :
    ContinuousOn G.beckmannPotential {f : P → ℝ | ∀ p, 0 ≤ f p} := by
  unfold beckmannPotential
  refine continuousOn_finsetSum _ fun e _ => ?_
  have hef : Continuous (fun f : P → ℝ => G.edgeFlow f e) :=
    continuous_finsetSum _ fun p _ => continuous_apply p
  have hprim : ContinuousOn (fun u => ∫ x in (0 : ℝ)..u, G.latency e x) (Ici 0) :=
    fun _ hu => (hasDerivWithinAt_primitive_Ici (hc e) hu).continuousWithinAt
  exact hprim.comp hef.continuousOn fun f hf => G.edgeFlow_nonneg hf e

/-- `beckmannPotential` is convex on the feasible flow polytope when resource latencies are
continuous and nondecreasing on `[0, ∞)`. -/
theorem convexOn_beckmannPotential [DecidableEq K]
    (hc : ∀ e, ContinuousOn (G.latency e) (Ici 0))
    (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0)) :
    ConvexOn ℝ {f : P → ℝ | G.IsFeasible f} G.beckmannPotential := by
  refine ⟨G.convex_setOf_isFeasible, fun f hf g hg a b ha hb hab => ?_⟩
  simp only [beckmannPotential_def, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  set xf := G.edgeFlow f e
  set xg := G.edgeFlow g e
  set xz := G.edgeFlow (a • f + b • g) e
  have hxf : 0 ≤ xf := G.edgeFlow_nonneg hf.1 e
  have hxg : 0 ≤ xg := G.edgeFlow_nonneg hg.1 e
  have hxz_eq : xz = a * xf + b * xg := by
    simp only [xz, xf, xg, G.edgeFlow_add, G.edgeFlow_smul]
  have hxz : 0 ≤ xz := by rw [hxz_eq]; positivity
  have h1 := (mul_sub_le_integral_sub_and_le (hc e) (hm e) hxz hxf).1
  have h2 := (mul_sub_le_integral_sub_and_le (hc e) (hm e) hxz hxg).1
  have hcomb : a * (G.latency e xz * (xf - xz)) + b * (G.latency e xz * (xg - xz)) = 0 := by
    rw [hxz_eq]
    linear_combination -G.latency e (a * xf + b * xg) * (a * xf + b * xg) * hab
  have hsum := add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
  have hint_eq : (a + b) * ∫ x in (0 : ℝ)..xz, G.latency e x =
      ∫ x in (0 : ℝ)..xz, G.latency e x := by rw [hab, one_mul]
  linarith

/-- With continuous nondecreasing latencies, every Wardrop equilibrium globally minimizes Beckmann's
potential over feasible flows. -/
theorem IsWardrop.isMinOn_beckmannPotential [DecidableEq K] {G : NonatomicCongestionGame K P E}
    (hc : ∀ e, ContinuousOn (G.latency e) (Ici 0))
    (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0))
    {f : P → ℝ} (hf : G.IsWardrop f) :
    IsMinOn G.beckmannPotential {g | G.IsFeasible g} f := by
  intro g hg
  have hvi := (isWardrop_iff_variationalInequality.1 hf).2 g hg
  have hsub : ∑ e, G.latency e (G.edgeFlow f e) * (G.edgeFlow g e - G.edgeFlow f e) ≤
      G.beckmannPotential g - G.beckmannPotential f := by
    simp only [beckmannPotential_def, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun e _ =>
      (mul_sub_le_integral_sub_and_le (hc e) (hm e)
        (G.edgeFlow_nonneg hf.1.1 e) (G.edgeFlow_nonneg hg.1 e)).1
  have h0 : 0 ≤ ∑ e, G.latency e (G.edgeFlow f e) * (G.edgeFlow g e - G.edgeFlow f e) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith
  change G.beckmannPotential f ≤ G.beckmannPotential g
  linarith

/-- With continuous latencies on `[0, ∞)`, every global minimizer of Beckmann's potential over
feasible flows is a Wardrop equilibrium. -/
theorem IsFeasible.isWardrop_of_isMinOn_beckmannPotential [DecidableEq K]
    {G : NonatomicCongestionGame K P E}
    (hc : ∀ e, ContinuousOn (G.latency e) (Ici 0)) {f : P → ℝ} (hf : G.IsFeasible f)
    (hmin : IsMinOn G.beckmannPotential {g | G.IsFeasible g} f) :
    G.IsWardrop f :=
  isWardrop_iff_variationalInequality.2 ⟨hf, fun _ hg =>
    hf.sum_mul_edgeFlow_le_of_isMinOn (H := fun e u => ∫ x in (0 : ℝ)..u, G.latency e x)
      hmin (fun e => hasDerivWithinAt_primitive_Ici (hc e) (G.edgeFlow_nonneg hf.1 e)) hg⟩

/-- **Beckmann's potential characterization** ([Roughgarden2007Routing], Proposition 18.11): for
continuous nondecreasing latencies on `[0, ∞)`, a feasible flow is a Wardrop equilibrium if and
only if it globally minimizes Beckmann's potential over all feasible flows. -/
theorem isWardrop_iff_isMinOn_beckmannPotential [DecidableEq K]
    {G : NonatomicCongestionGame K P E}
    (hc : ∀ e, ContinuousOn (G.latency e) (Ici 0))
    (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0))
    {f : P → ℝ} (hf : G.IsFeasible f) :
    G.IsWardrop f ↔ IsMinOn G.beckmannPotential {g | G.IsFeasible g} f :=
  ⟨fun h => h.isMinOn_beckmannPotential hc hm, hf.isWardrop_of_isMinOn_beckmannPotential hc⟩

end BeckmannPotential

/-! ### Theorem 18.8: existence and essential uniqueness of Wardrop equilibria -/

section Existence

variable {K P E : Type*} [Fintype P] [DecidableEq E] [Finite E]
  (G : NonatomicCongestionGame K P E)

/-- **Existence of Wardrop equilibria from nonempty feasibility** ([Roughgarden2007Routing],
Theorem 18.8(a)): if a nonatomic congestion game has continuous latencies on `[0, ∞)` and at least
one feasible flow, then it admits a Wardrop equilibrium. -/
theorem exists_isWardrop_of_nonempty [DecidableEq K]
    (hne : {f : P → ℝ | G.IsFeasible f}.Nonempty)
    (hc : ∀ e, ContinuousOn (G.latency e) (Ici 0)) :
    ∃ f, G.IsWardrop f := by
  have := Fintype.ofFinite E
  have hcont : ContinuousOn G.beckmannPotential {f : P → ℝ | G.IsFeasible f} :=
    (G.continuousOn_beckmannPotential hc).mono fun _ hf => hf.1
  obtain ⟨f, hf, hmin⟩ := G.isCompact_setOf_isFeasible.exists_isMinOn hne hcont
  exact ⟨f, hf.isWardrop_of_isMinOn_beckmannPotential hc hmin⟩

/-- **Existence of Wardrop equilibria** ([Roughgarden2007Routing], Theorem 18.8(a)): if demand
rates are nonnegative, every commodity with nonzero demand has at least one path, and resource
latencies are continuous on `[0, ∞)`, then a Wardrop equilibrium exists. -/
theorem exists_isWardrop [DecidableEq K] (hr : ∀ k, 0 ≤ G.rate k)
    (hpath : ∀ k, G.rate k ≠ 0 → ∃ p, G.commodity p = k)
    (hc : ∀ e, ContinuousOn (G.latency e) (Ici 0)) :
    ∃ f, G.IsWardrop f :=
  G.exists_isWardrop_of_nonempty (G.nonempty_setOf_isFeasible hr hpath) hc

end Existence

section Uniqueness

variable {K P E : Type*} [Fintype P] [DecidableEq E] {G : NonatomicCongestionGame K P E}

/-- **Essential uniqueness of Wardrop edge latencies** ([Roughgarden2007Routing],
Theorem 18.8(b)): if resource latencies are nondecreasing on `[0, ∞)`, any two Wardrop equilibria
`f` and `g` induce the same latency on every resource `e`. -/
theorem isWardrop_latency_eq [DecidableEq K] [Finite E]
    (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0))
    {f g : P → ℝ} (hf : G.IsWardrop f) (hg : G.IsWardrop g) (e : E) :
    G.latency e (G.edgeFlow f e) = G.latency e (G.edgeFlow g e) := by
  have := Fintype.ofFinite E
  have h1 := (isWardrop_iff_variationalInequality.1 hf).2 g hg.1
  have h2 := (isWardrop_iff_variationalInequality.1 hg).2 f hf.1
  have hterm : ∀ e' ∈ (Finset.univ : Finset E),
      0 ≤ (G.latency e' (G.edgeFlow f e') - G.latency e' (G.edgeFlow g e')) *
        (G.edgeFlow f e' - G.edgeFlow g e') := by
    intro e' _
    have hfe : 0 ≤ G.edgeFlow f e' := G.edgeFlow_nonneg hf.1.1 e'
    have hge : 0 ≤ G.edgeFlow g e' := G.edgeFlow_nonneg hg.1.1 e'
    rcases le_total (G.edgeFlow g e') (G.edgeFlow f e') with hle | hle
    · exact mul_nonneg (sub_nonneg.2 (hm e' hge hfe hle)) (sub_nonneg.2 hle)
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.2 (hm e' hfe hge hle)) (sub_nonpos.2 hle)
  have hsum : ∑ e', (G.latency e' (G.edgeFlow f e') - G.latency e' (G.edgeFlow g e')) *
      (G.edgeFlow f e' - G.edgeFlow g e') ≤ 0 := by
    have hexpand : ∀ e',
        (G.latency e' (G.edgeFlow f e') - G.latency e' (G.edgeFlow g e')) *
          (G.edgeFlow f e' - G.edgeFlow g e') =
        (G.latency e' (G.edgeFlow f e') * G.edgeFlow f e' -
          G.latency e' (G.edgeFlow f e') * G.edgeFlow g e') +
        (G.latency e' (G.edgeFlow g e') * G.edgeFlow g e' -
          G.latency e' (G.edgeFlow g e') * G.edgeFlow f e') := fun _ => by ring
    simp only [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).1
    (le_antisymm hsum (Finset.sum_nonneg hterm)) e (Finset.mem_univ e)
  rcases mul_eq_zero.1 hzero with hlat | hflow
  · exact sub_eq_zero.1 hlat
  · rw [sub_eq_zero.1 hflow]

/-- Any two Wardrop equilibria induce the same path latencies under nondecreasing resource
latencies. -/
theorem isWardrop_pathLatency_eq [DecidableEq K] [Finite E]
    (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0))
    {f g : P → ℝ} (hf : G.IsWardrop f) (hg : G.IsWardrop g) (p : P) :
    G.pathLatency f p = G.pathLatency g p :=
  Finset.sum_congr rfl fun e _ => isWardrop_latency_eq hm hf hg e

/-- **All Wardrop equilibria have equal total cost** ([Roughgarden2007Routing], Theorem 18.8(b)):
in particular, the price of stability equals the price of anarchy in every nonatomic congestion
game with nondecreasing latencies. -/
theorem isWardrop_cost_eq [DecidableEq K] [Finite E]
    (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0))
    {f g : P → ℝ} (hf : G.IsWardrop f) (hg : G.IsWardrop g) :
    G.cost f = G.cost g := by
  have := Fintype.ofFinite E
  have h1 := hf.cost_le_sum_mul_pathLatency hg.1
  have h2 := hg.cost_le_sum_mul_pathLatency hf.1
  have heq1 : ∑ p, g p * G.pathLatency f p = G.cost g :=
    Finset.sum_congr rfl fun p _ => by rw [isWardrop_pathLatency_eq hm hf hg p]
  have heq2 : ∑ p, f p * G.pathLatency g p = G.cost f :=
    Finset.sum_congr rfl fun p _ => by rw [isWardrop_pathLatency_eq hm hg hf p]
  linarith

/-- **Uniqueness of the Wardrop equilibrium in Pigou's linear example**
([RoughgardenTardos2007], Example 17.1): on `pigouNetwork id 1`, `![1, 0]` is the unique Wardrop
equilibrium. -/
theorem pigouNetwork_id_isWardrop_iff {f : Fin 2 → ℝ} :
    (pigouNetwork (fun x => x) 1).IsWardrop f ↔ f = ![1, 0] := by
  refine ⟨fun hf => ?_, fun h => h ▸ pigouNetwork_isWardrop _ zero_le_one⟩
  have hm : ∀ e, MonotoneOn ((pigouNetwork (fun x => x) 1).latency e) (Ici 0) := by
    intro e x _ y _ hxy
    fin_cases e
    · exact hxy
    · exact le_rfl
  have hlat := isWardrop_latency_eq hm hf (pigouNetwork_isWardrop _ zero_le_one) 0
  simp only [pigouNetwork_edgeFlow, pigouNetwork_latency_zero, Matrix.cons_val_zero] at hlat
  have hsum : f 0 + f 1 = 1 := by
    have h := hf.1.2 ()
    simpa [pigouNetwork, Fin.sum_univ_two] using h
  ext i
  fin_cases i
  · exact hlat
  · change f 1 = 0
    linarith

/-- **Price of stability of Pigou's linear example is `4/3`** ([RoughgardenTardos2007],
Example 17.1): `![1/2, 1/2]` minimizes total cost (`3/4`) over all feasible flows, and *every*
Wardrop equilibrium `f` of `pigouNetwork id 1` has cost `(4/3) * cost ![1/2, 1/2] = 1`. -/
theorem pigouNetwork_id_priceOfStability :
    (pigouNetwork (fun x => x) 1).IsFeasible ![1 / 2, 1 / 2] ∧
      (∀ g, (pigouNetwork (fun x => x) 1).IsFeasible g →
        (pigouNetwork (fun x => x) 1).cost ![1 / 2, 1 / 2] ≤
          (pigouNetwork (fun x => x) 1).cost g) ∧
      ∀ f, (pigouNetwork (fun x => x) 1).IsWardrop f →
        (pigouNetwork (fun x => x) 1).cost f =
          4 / 3 * (pigouNetwork (fun x => x) 1).cost ![1 / 2, 1 / 2] := by
  refine ⟨?_, fun g hg => ?_, fun f hf => ?_⟩
  · convert pigouNetwork_isFeasible (fun x => x) (r := 1) (x := 1 / 2) (by norm_num) (by norm_num)
    norm_num
  · rw [pigouNetwork_cost, pigouNetwork_cost]
    have hsum : g 0 + g 1 = 1 := by
      have h := hg.2 ()
      simpa [pigouNetwork, Fin.sum_univ_two] using h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [sq_nonneg (g 0 - 1 / 2)]
  · rw [pigouNetwork_id_isWardrop_iff.1 hf, pigouNetwork_cost, pigouNetwork_cost]
    norm_num

end Uniqueness

/-! ### Theorem 18.16 and Corollary 18.17: potential-function price-of-anarchy bounds -/

section PotentialPoA

variable {K P E : Type*} [Fintype P] [DecidableEq E] {G : NonatomicCongestionGame K P E}

/-- With continuous nondecreasing latencies on `[0, ∞)`, Beckmann's potential is at most the flow
cost for every nonnegative flow. -/
theorem beckmannPotential_le_cost [Fintype E]
    (hc : ∀ e, ContinuousOn (G.latency e) (Ici 0))
    (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0))
    {f : P → ℝ} (hf : ∀ p, 0 ≤ f p) :
    G.beckmannPotential f ≤ G.cost f := by
  rw [beckmannPotential_def, G.cost_eq_sum_edgeFlow]
  refine Finset.sum_le_sum fun e _ => ?_
  have h := (mul_sub_le_integral_sub_and_le (hc e) (hm e) le_rfl (G.edgeFlow_nonneg hf e)).2
  simp only [integral_same, sub_zero] at h
  linarith

/-- **Potential-function price-of-anarchy upper bound** ([Roughgarden2007Routing], Theorem 18.16;
[RoughgardenTardos2002]): if resource latencies are continuous and nondecreasing on `[0, ∞)` and
`x * latency e x ≤ γ * ∫ y in 0..x, latency e y` for all `x ≥ 0` with `γ ≥ 0`, then every Wardrop
equilibrium costs at most `γ` times every feasible flow. -/
theorem IsWardrop.cost_le_mul_of_le_mul_integral [DecidableEq K] [Finite E] {γ : ℝ} (hγ : 0 ≤ γ)
    (hc : ∀ e, ContinuousOn (G.latency e) (Ici 0))
    (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0))
    (hub : ∀ e x, 0 ≤ x → x * G.latency e x ≤ γ * ∫ y in (0 : ℝ)..x, G.latency e y)
    {f g : P → ℝ} (hf : G.IsWardrop f) (hg : G.IsFeasible g) :
    G.cost f ≤ γ * G.cost g := by
  have := Fintype.ofFinite E
  calc G.cost f
      = ∑ e, G.edgeFlow f e * G.latency e (G.edgeFlow f e) := G.cost_eq_sum_edgeFlow f
    _ ≤ ∑ e, γ * ∫ y in (0 : ℝ)..G.edgeFlow f e, G.latency e y :=
        Finset.sum_le_sum fun e _ => hub e _ (G.edgeFlow_nonneg hf.1.1 e)
    _ = γ * G.beckmannPotential f := by rw [beckmannPotential_def, Finset.mul_sum]
    _ ≤ γ * G.beckmannPotential g :=
        mul_le_mul_of_nonneg_left (hf.isMinOn_beckmannPotential hc hm hg) hγ
    _ ≤ γ * G.cost g :=
        mul_le_mul_of_nonneg_left (beckmannPotential_le_cost hc hm hg.1) hγ

/-- **Potential-function bound for polynomial latencies** ([Roughgarden2007Routing],
Corollary 18.17): if every resource latency is a polynomial of degree at most `d` with nonnegative
coefficients, then every Wardrop equilibrium costs at most `(d + 1)` times every feasible flow. -/
theorem IsWardrop.cost_le_succ_mul_of_mem_polynomialLatencies [DecidableEq K] [Finite E] {d : ℕ}
    (hG : ∀ e, G.latency e ∈ polynomialLatencies d)
    {f g : P → ℝ} (hf : G.IsWardrop f) (hg : G.IsFeasible g) :
    G.cost f ≤ ((d : ℝ) + 1) * G.cost g := by
  have hc : ∀ e, ContinuousOn (G.latency e) (Ici 0) := by
    intro e
    obtain ⟨a, _, heq⟩ := mem_polynomialLatencies.1 (hG e)
    have hcont : Continuous (G.latency e) := by
      rw [funext heq]
      exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow _)
    exact hcont.continuousOn
  refine hf.cost_le_mul_of_le_mul_integral (by positivity) hc
    (fun e => monotoneOn_of_mem_polynomialLatencies (hG e)) (fun e x hx => ?_) hg
  obtain ⟨a, ha, heq⟩ := mem_polynomialLatencies.1 (hG e)
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin (d + 1))),
      IntervalIntegrable (fun y : ℝ => a i * y ^ (i : ℕ)) MeasureTheory.volume 0 x :=
    fun i _ => (continuous_const.mul (continuous_pow (i : ℕ))).intervalIntegrable 0 x
  have hcalc : ∫ y in (0 : ℝ)..x, G.latency e y =
      ∑ i : Fin (d + 1), a i * (x ^ ((i : ℕ) + 1) / ((i : ℕ) + 1)) := by
    simp only [heq]
    rw [integral_finsetSum hint]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
  rw [hcalc, heq, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hi_le : ((i : ℕ) : ℝ) + 1 ≤ (d : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.lt_succ_iff.1 i.isLt)
  have hi_pos : (0 : ℝ) < (i : ℕ) + 1 := by positivity
  have hd_pos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  calc x * (a i * x ^ (i : ℕ))
      = a i * x ^ ((i : ℕ) + 1) := by rw [pow_succ]; ring
    _ = ((d : ℝ) + 1) * (a i * (x ^ ((i : ℕ) + 1) / ((d : ℝ) + 1))) := by field_simp [hd_pos.ne']
    _ ≤ ((d : ℝ) + 1) * (a i * (x ^ ((i : ℕ) + 1) / ((i : ℕ) + 1))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (ha i)) hd_pos.le
        exact div_le_div_of_nonneg_left (pow_nonneg hx _) hi_pos hi_le

end PotentialPoA

end Cslib.GameTheory.NonatomicCongestionGame
