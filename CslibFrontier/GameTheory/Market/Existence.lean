/-
Copyright (c) 2026 Matthew Doty, Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Nick L. Leppelmeier
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Berge
public import CslibFrontier.GameTheory.Market.GaleNikaidoDebreu
public import CslibFrontier.GameTheory.Market.Welfare
public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Existence of competitive equilibria in exchange economies

This module proves the **Arrow–Debreu competitive equilibrium existence theorem**
([ArrowDebreu1954]; [Gale1955]; [Nikaido1956]; [Debreu1956]) for finite exchange economies
`ExchangeMarket I G` via McKenzie's bounded-box truncation, Berge's maximum theorem
(`Cslib.Berge`), and the Gale–Nikaido–Debreu lemma (`Cslib.GameTheory.Market.GaleNikaidoDebreu`).

## Main definitions

* `Cslib.GameTheory.Market.truncationBox`: McKenzie's bounded hypercube
  `{x | ∀ g, 0 ≤ x g ∧ x g ≤ B}`.
* `Cslib.GameTheory.Market.truncatedBudget`, `Cslib.GameTheory.Market.truncatedDemand`: trader `i`'s
  truncated budget set and compact-box demand correspondence.

## Main results

* `Cslib.GameTheory.Market.HasConvexPreferences.quasiconcaveOn`: convex strictly-preferred upper
  contour sets imply quasiconcavity on `ℝ_+^G`.
* `Cslib.GameTheory.Market.mem_demandSet_of_mem_truncatedDemand`: McKenzie truncation removal when
  clearing bundles lie strictly inside the truncation box under positive income, continuous
  utilities, convex preferences, and local nonsatiation.
* `Cslib.GameTheory.Market.ExchangeMarket.exists_isCompetitiveEquilibrium`: any `ExchangeMarket I G`
  over nonempty finite goods `G` with strictly positive endowments (`∀ i g, 0 < E.endowment i g`),
  continuous utilities on `ℝ_+^G`, convex preferences (`HasConvexPreferences`), and local
  nonsatiation (`IsLocallyNonsatiated`) admits a price vector `p ∈ priceSimplex G` and allocation
  `x` forming a competitive equilibrium (`E.IsCompetitiveEquilibrium x p`).
* `Cslib.GameTheory.Market.ExchangeMarket.exists_isCompetitiveEquilibrium_of_strictQuasiconcaveOn`:
  single-valued continuous-demand specialization under strict quasiconcavity on `ℝ_+^G`, routed
  through `Cslib.Berge.exists_unique_continuousOn_argmaxSet` and the single-valued
  Gale–Nikaido–Debreu lemma `exists_excessDemand_le_zero_of_continuousOn`.

## References

* [K. J. Arrow and G. Debreu,
  *Existence of an Equilibrium for a Competitive Economy*][ArrowDebreu1954]
* [D. Gale, *The Law of Supply and Demand*][Gale1955] (primary PDF unverified)
* [H. Nikaido, *On the Classical Multilateral Exchange Problem*][Nikaido1956]
  (primary PDF unverified)
* [G. Debreu, *Market Equilibrium*][Debreu1956] (primary PDF unverified)
-/

public section

namespace Cslib.GameTheory.Market

open Finset Set Filter Topology

section Convexity

variable {G : Type*}

/-- Convex strictly-preferred upper contour sets imply quasiconcavity on `ℝ_+^G`. -/
theorem HasConvexPreferences.quasiconcaveOn {u : (G → ℝ) → ℝ}
    (hconv : HasConvexPreferences u) :
    QuasiconcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} u := by
  intro c x hx y hy a b ha hb hab
  refine ⟨fun g => add_nonneg (mul_nonneg ha (hx.1 g)) (mul_nonneg hb (hy.1 g)), ?_⟩
  by_contra! hlt
  let z := a • x + b • y
  have hz_nn : ∀ g, 0 ≤ z g := fun g => add_nonneg (mul_nonneg ha (hx.1 g)) (mul_nonneg hb (hy.1 g))
  have hx' : x ∈ {w : G → ℝ | (∀ g, 0 ≤ w g) ∧ u z < u w} :=
    ⟨hx.1, lt_of_lt_of_le hlt hx.2⟩
  have hy' : y ∈ {w : G → ℝ | (∀ g, 0 ≤ w g) ∧ u z < u w} :=
    ⟨hy.1, lt_of_lt_of_le hlt hy.2⟩
  exact lt_irrefl (u z) ((hconv hz_nn) hx' hy' ha hb hab).2

end Convexity

section TruncationBox

variable {G : Type*}

/-- McKenzie's bounded consumption hypercube `{x : G → ℝ | ∀ g, 0 ≤ x g ∧ x g ≤ B}`. -/
@[expose] def truncationBox (B : ℝ) : Set (G → ℝ) :=
  {x | ∀ g, 0 ≤ x g ∧ x g ≤ B}

theorem truncationBox_isCompact (B : ℝ) : IsCompact (truncationBox (G := G) B) := by
  have hEq : truncationBox (G := G) B = univ.pi fun _ : G => Icc (0 : ℝ) B := by
    ext x
    simp only [truncationBox, mem_ofPred_eq, mem_univ_pi, Set.mem_Icc]
  rw [hEq]
  exact isCompact_univ_pi fun _ => isCompact_Icc

theorem truncationBox_convex (B : ℝ) : Convex ℝ (truncationBox (G := G) B) := by
  have hEq : truncationBox (G := G) B = univ.pi fun _ : G => Icc (0 : ℝ) B := by
    ext x
    simp only [truncationBox, mem_ofPred_eq, mem_univ_pi, Set.mem_Icc]
  rw [hEq]
  exact convex_pi fun _ _ => convex_Icc (0 : ℝ) B

end TruncationBox

section TruncatedMarket

variable {I G : Type*} [Fintype G]

/-- The truncated budget set of trader `i` at prices `p` inside `truncationBox B`. -/
@[expose] def truncatedBudget (E : ExchangeMarket I G) (B : ℝ) (p : G → ℝ) (i : I) :
    Set (G → ℝ) :=
  {x ∈ truncationBox B | expenditure p x ≤ E.income p i}

private lemma continuous_expenditure_left (x : G → ℝ) :
    Continuous fun p : G → ℝ => expenditure p x := by
  simp_rw [expenditure_eq_sum]
  exact continuous_finsetSum Finset.univ fun g _ => (continuous_apply g).mul continuous_const

private lemma continuous_income (E : ExchangeMarket I G) (i : I) :
    Continuous fun p : G → ℝ => E.income p i := by
  simp_rw [E.income_eq]
  exact continuous_expenditure_left (E.endowment i)

private lemma continuous_expenditure_pair' :
    Continuous fun pq : (G → ℝ) × (G → ℝ) => expenditure pq.1 pq.2 := by
  simp_rw [expenditure_eq_sum]
  exact continuous_finsetSum Finset.univ fun g _ =>
    ((continuous_apply g).comp continuous_fst).mul ((continuous_apply g).comp continuous_snd)

private lemma income_pos_of_endowment_pos (E : ExchangeMarket I G)
    (hend : ∀ i g, 0 < E.endowment i g) {p : G → ℝ} (hp : p ∈ priceSimplex G) (i : I) :
    0 < E.income p i := by
  have hex : ∃ g : G, 0 < p g := by
    by_contra! hall
    have hp0 : ∑ g : G, p g = 0 := Finset.sum_eq_zero fun g _ => le_antisymm (hall g) (hp.1 g)
    linarith [hp.2]
  obtain ⟨g₀, hpg₀⟩ := hex
  rw [E.income_eq, expenditure_eq_sum]
  exact Finset.sum_pos' (fun g _ => mul_nonneg (hp.1 g) (E.endowment_nonneg i g))
    ⟨g₀, Finset.mem_univ g₀, mul_pos hpg₀ (hend i g₀)⟩

private lemma truncatedBudget_nonempty (E : ExchangeMarket I G) {B : ℝ} (hB : 0 ≤ B)
    {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (i : I) :
    (truncatedBudget E B p i).Nonempty := by
  refine ⟨0, fun _ => ⟨le_rfl, hB⟩, ?_⟩
  rw [expenditure_zero_right]
  exact E.income_nonneg hp i

private lemma truncatedBudget_isCompact (E : ExchangeMarket I G) (B : ℝ) (p : G → ℝ) (i : I) :
    IsCompact (truncatedBudget E B p i) := by
  have hEq : truncatedBudget E B p i =
      truncationBox B ∩ {x : G → ℝ | expenditure p x ≤ E.income p i} := rfl
  rw [hEq]
  refine (truncationBox_isCompact (G := G) B).inter_right ?_
  have hexp : Continuous fun x : G → ℝ => expenditure p x := by
    simp_rw [expenditure_eq_sum]
    exact continuous_finsetSum Finset.univ fun g _ => continuous_const.mul (continuous_apply g)
  exact isClosed_Iic.preimage hexp

private lemma truncatedBudget_convex (E : ExchangeMarket I G) (B : ℝ) (p : G → ℝ) (i : I) :
    Convex ℝ (truncatedBudget E B p i) := by
  intro x hx y hy a b ha hb hab
  refine ⟨truncationBox_convex (G := G) B hx.1 hy.1 ha hb hab, ?_⟩
  rw [expenditure_add, expenditure_smul_right, expenditure_smul_right]
  calc
    a * expenditure p x + b * expenditure p y
        ≤ a * E.income p i + b * E.income p i := by
            gcongr
            · exact hx.2
            · exact hy.2
    _ = E.income p i := by rw [← add_mul, hab, one_mul]

private lemma truncatedBudget_uhc (E : ExchangeMarket I G) (B : ℝ) (i : I) :
    UpperHemicontinuousOn (fun p => truncatedBudget E B p i) (priceSimplex G) := by
  refine Cslib.Berge.upperHemicontinuousOn_of_isClosed_graph
    (truncationBox_isCompact B).isSeqCompact (fun _ _ _ hx => hx.1) ?_
  have hEq :
      {pq : (G → ℝ) × (G → ℝ) | pq.1 ∈ priceSimplex G ∧ pq.2 ∈ truncatedBudget E B pq.1 i} =
      {pq | pq.1 ∈ priceSimplex G} ∩ {pq | pq.2 ∈ truncationBox B} ∩
      {pq | expenditure pq.1 pq.2 ≤ E.income pq.1 i} := by
    ext ⟨p, x⟩
    simp [truncatedBudget]
    tauto
  rw [hEq]
  refine ((priceSimplex_isCompact.isClosed.preimage continuous_fst).inter
    ((truncationBox_isCompact B).isClosed.preimage continuous_snd)).inter ?_
  exact isClosed_le continuous_expenditure_pair' ((continuous_income E i).comp continuous_fst)

private lemma truncatedBudget_lhc (E : ExchangeMarket I G)
    (hend : ∀ i g, 0 < E.endowment i g) (B : ℝ) (i : I) :
    LowerHemicontinuousOn (fun p => truncatedBudget E B p i) (priceSimplex G) := by
  rw [lowerHemicontinuousOn_iff]
  intro p₀ hp₀
  rw [lowerHemicontinuousWithinAt_iff]
  rintro U hU ⟨x₀, ⟨hx₀_box, hx₀_exp⟩, hx₀U⟩
  have hlim_smul : Tendsto (fun t : ℝ => t • x₀) (𝓝 1) (𝓝 x₀) := by
    have hcont : Continuous fun t : ℝ => t • x₀ := continuous_id.smul continuous_const
    simpa using (hcont.continuousAt (x := (1 : ℝ))).tendsto
  have ht_nhds : {t : ℝ | t • x₀ ∈ U} ∈ 𝓝 (1 : ℝ) := hlim_smul (hU.mem_nhds hx₀U)
  obtain ⟨δ, hδ, hδ_sub⟩ := Metric.mem_nhds_iff.mp ht_nhds
  let t : ℝ := max (1 / 2) (1 - δ / 2)
  have ht_pos : 0 < t := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have ht_lt : t < 1 := max_lt (by norm_num) (by linarith)
  have ht_ball : t ∈ Metric.ball (1 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · have : 1 - δ / 2 ≤ t := le_max_right _ _
      linarith
    · linarith
  let y : G → ℝ := t • x₀
  have hyU : y ∈ U := hδ_sub ht_ball
  have hy_box : y ∈ truncationBox B := fun g =>
    ⟨mul_nonneg ht_pos.le (hx₀_box g).1, by
      calc
        t * x₀ g ≤ 1 * x₀ g := mul_le_mul_of_nonneg_right ht_lt.le (hx₀_box g).1
        _ = x₀ g := one_mul _
        _ ≤ B := (hx₀_box g).2⟩
  have hinc_pos : 0 < E.income p₀ i := income_pos_of_endowment_pos E hend hp₀ i
  have hy_strict : expenditure p₀ y < E.income p₀ i := by
    rw [show y = t • x₀ from rfl, expenditure_smul_right]
    calc
      t * expenditure p₀ x₀ ≤ t * E.income p₀ i := mul_le_mul_of_nonneg_left hx₀_exp ht_pos.le
      _ < 1 * E.income p₀ i := mul_lt_mul_of_pos_right ht_lt hinc_pos
      _ = E.income p₀ i := one_mul _
  have hcont_slack : Continuous fun p : G → ℝ => E.income p i - expenditure p y :=
    (continuous_income E i).sub (continuous_expenditure_left y)
  have h_open_p : IsOpen {p : G → ℝ | expenditure p y < E.income p i} := by
    have hEq : {p : G → ℝ | expenditure p y < E.income p i} =
        (fun p => E.income p i - expenditure p y) ⁻¹' Ioi 0 := by
      ext p
      simp [sub_pos]
    rw [hEq]
    exact isOpen_Ioi.preimage hcont_slack
  have hp_ev : ∀ᶠ p in 𝓝[priceSimplex G] p₀, expenditure p y < E.income p i :=
    nhdsWithin_le_nhds (h_open_p.mem_nhds hy_strict)
  filter_upwards [hp_ev] with p hp_lt
  exact ⟨y, ⟨hy_box, hp_lt.le⟩, hyU⟩

/-- Truncated demand correspondence of trader `i` at prices `p` inside `truncationBox B`. -/
@[expose] noncomputable def truncatedDemand (E : ExchangeMarket I G) (B : ℝ) (i : I)
    (p : G → ℝ) : Set (G → ℝ) :=
  Cslib.Berge.argmaxSet (fun q => truncatedBudget E B q i) (fun _ => E.utility i) p

private lemma truncatedDemand_nonempty (E : ExchangeMarket I G) {B : ℝ} (hB : 0 ≤ B) (i : I)
    (hcont : ContinuousOn (E.utility i) {x | ∀ g, 0 ≤ x g})
    {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) :
    (truncatedDemand E B i p).Nonempty :=
  Cslib.Berge.argmaxSet_nonempty (truncatedBudget_nonempty E hB hp i)
    (truncatedBudget_isCompact E B p i)
    (hcont.mono fun _ hx => fun g => (hx.1 g).1)

private lemma truncatedDemand_isCompact (E : ExchangeMarket I G) (B : ℝ) (i : I)
    (hcont : ContinuousOn (E.utility i) {x | ∀ g, 0 ≤ x g}) (p : G → ℝ) :
    IsCompact (truncatedDemand E B i p) :=
  Cslib.Berge.argmaxSet_isCompact (truncatedBudget_isCompact E B p i)
    (hcont.mono fun _ hx => fun g => (hx.1 g).1)

private lemma truncatedDemand_convex (E : ExchangeMarket I G) (B : ℝ) (i : I)
    (hconv : HasConvexPreferences (E.utility i)) (p : G → ℝ) :
    Convex ℝ (truncatedDemand E B i p) := by
  refine Cslib.Berge.convex_argmaxSet (truncatedBudget_convex E B p i) ?_
  intro c x hx y hy a b ha hb hab
  exact ⟨truncatedBudget_convex E B p i hx.1 hy.1 ha hb hab,
    (hconv.quasiconcaveOn c ⟨fun g => (hx.1.1 g).1, hx.2⟩
      ⟨fun g => (hy.1.1 g).1, hy.2⟩ ha hb hab).2⟩

private lemma truncatedDemand_uhc (E : ExchangeMarket I G)
    (hend : ∀ i g, 0 < E.endowment i g) {B : ℝ} (hB : 0 ≤ B)
    (hcont : ∀ i, ContinuousOn (E.utility i) {x | ∀ g, 0 ≤ x g}) (i : I) :
    UpperHemicontinuousOn (truncatedDemand E B i) (priceSimplex G) := by
  refine Cslib.Berge.upperHemicontinuousOn_argmaxSet
    (fun p hp => truncatedBudget_nonempty E hB hp.1 i)
    (fun p _ => truncatedBudget_isCompact E B p i)
    (truncatedBudget_uhc E B i)
    (truncatedBudget_lhc E hend B i) ?_
  exact (hcont i).comp continuousOn_snd fun _ hp g => (hp.2.1 g).1

end TruncatedMarket

section TruncationRemoval

variable {I G : Type*} [Fintype I] [Fintype G]

omit [Fintype G] in
private lemma continuous_excessDemand (E : ExchangeMarket I G) :
    Continuous (E.excessDemand) := by
  refine continuous_pi fun g => ?_
  have hsum : Continuous fun x : I → G → ℝ => ∑ i, x i g :=
    continuous_finsetSum Finset.univ fun i _ => (continuous_apply g).comp (continuous_apply i)
  simp_rw [E.excessDemand_eq]
  exact hsum.sub continuous_const

/-- Truncation removal: if an allocation `x` is coordinatewise in `truncatedDemand E B i p` where
every good clears (`E.excessDemand x g ≤ 0`) and `E.totalSupply g < B`, then under positive
income, continuous utilities, convex preferences, and local nonsatiation, every trader maximizes on
the full budget set. -/
theorem mem_demandSet_of_mem_truncatedDemand (E : ExchangeMarket I G) [Nonempty G]
    {B : ℝ} (hB : ∀ g, E.totalSupply g < B)
    {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hinc : ∀ i, 0 < E.income p i)
    (hcont : ∀ i, ContinuousOn (E.utility i) {y | ∀ g, 0 ≤ y g})
    (hconv : ∀ i, HasConvexPreferences (E.utility i))
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i))
    {x : I → G → ℝ} (hdem : ∀ i, x i ∈ truncatedDemand E B i p)
    (hclear : ∀ g, E.excessDemand x g ≤ 0) (i : I) :
    x i ∈ E.demandSet p i := by
  have hx_feas : E.IsBudgetFeasible p i (x i) :=
    ⟨fun g => ((hdem i).1.1 g).1, (hdem i).1.2⟩
  refine E.mem_demandSet.mpr (Market.mem_demandSet.mpr ⟨hx_feas, fun y hy => ?_⟩)
  by_contra! hlt
  -- Step 1: Shrink `y` slightly to `y'` with strictly slack budget and `u (x i) < u y'`.
  have hlim_eps : Tendsto (fun ε : ℝ => (1 - ε) • y) (𝓝 0) (𝓝 y) := by
    have hcont_smul : Continuous fun ε : ℝ => (1 - ε) • y :=
      (continuous_const.sub continuous_id).smul continuous_const
    simpa using (hcont_smul.continuousAt (x := (0 : ℝ))).tendsto
  have hcont_y : ContinuousWithinAt (E.utility i) {z | ∀ g, 0 ≤ z g} y :=
    hcont i y hy.1
  have hy_open_nhds : {z | E.utility i (x i) < E.utility i z} ∈ 𝓝[{z | ∀ g, 0 ≤ z g}] y :=
    hcont_y (isOpen_Ioi.mem_nhds hlt)
  obtain ⟨U, hU_open, hyU, hU_sub⟩ := mem_nhdsWithin.mp hy_open_nhds
  obtain ⟨δ₁, hδ₁, hδ₁_sub⟩ := Metric.mem_nhds_iff.mp (hlim_eps (hU_open.mem_nhds hyU))
  let ε : ℝ := min (1 / 2) (δ₁ / 2)
  have hε_pos : 0 < ε := lt_min (by norm_num) (half_pos hδ₁)
  have hε_lt : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  let y' : G → ℝ := (1 - ε) • y
  have hy'_nn : ∀ g, 0 ≤ y' g := fun g => mul_nonneg (by linarith) (hy.1 g)
  have hε_ball : ε ∈ Metric.ball (0 : ℝ) δ₁ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε_pos]
    exact (min_le_right _ _).trans_lt (half_lt_self hδ₁)
  have hy'_lt : E.utility i (x i) < E.utility i y' := hU_sub ⟨hδ₁_sub hε_ball, hy'_nn⟩
  have hy'_exp : expenditure p y' < E.income p i := by
    dsimp [y']
    rw [expenditure_smul_right]
    calc
      (1 - ε) * expenditure p y ≤ (1 - ε) * E.income p i :=
        mul_le_mul_of_nonneg_left hy.2 (by linarith)
      _ < 1 * E.income p i := mul_lt_mul_of_pos_right (by linarith) (hinc i)
      _ = E.income p i := one_mul _
  -- Step 2: Move strictly inside `truncationBox B` along the segment `[x i, y']`.
  have hxi_ltB : ∀ g, x i g < B := fun g => by
    have hle_sum : x i g ≤ ∑ j : I, x j g :=
      Finset.single_le_sum (fun j _ => ((hdem j).1.1 g).1) (Finset.mem_univ i)
    have hsum_le : ∑ j : I, x j g ≤ E.totalSupply g :=
      sub_nonpos.mp (E.excessDemand_eq x g ▸ hclear g)
    exact (hle_sum.trans hsum_le).trans_lt (hB g)
  let t : ℝ := min (1 / 2)
    (Finset.univ.inf' Finset.univ_nonempty
      (fun g => (B - x i g) / (2 * (|y' g - x i g| + 1))))
  have ht_pos : 0 < t := by
    refine lt_min (by norm_num) ?_
    rw [Finset.lt_inf'_iff]
    intro g _
    exact div_pos (sub_pos.mpr (hxi_ltB g)) (by positivity)
  have ht_lt : t < 1 := (min_le_left _ _).trans_lt (by norm_num)
  let z : G → ℝ := (1 - t) • x i + t • y'
  have hz_nn : ∀ g, 0 ≤ z g := fun g =>
    add_nonneg (mul_nonneg (by linarith) ((hdem i).1.1 g).1) (mul_nonneg ht_pos.le (hy'_nn g))
  have hz_ltB : ∀ g, z g < B := fun g => by
    have ht_le_g : t ≤ (B - x i g) / (2 * (|y' g - x i g| + 1)) :=
      (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ g))
    have hpos_den : 0 < 2 * (|y' g - x i g| + 1) := by positivity
    have hprod : t * (2 * (|y' g - x i g| + 1)) ≤ B - x i g :=
      (le_div_iff₀ hpos_den).mp ht_le_g
    have hdiff_le : t * (y' g - x i g) ≤ t * |y' g - x i g| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) ht_pos.le
    have hlt_step : t * |y' g - x i g| < t * (2 * (|y' g - x i g| + 1)) :=
      mul_lt_mul_of_pos_left (by linarith [abs_nonneg (y' g - x i g)]) ht_pos
    calc
      z g = x i g + t * (y' g - x i g) := by simp [z]; ring
      _ ≤ x i g + t * |y' g - x i g| := by linarith
      _ < x i g + t * (2 * (|y' g - x i g| + 1)) := by linarith
      _ ≤ B := by linarith
  have hz_exp : expenditure p z < E.income p i := by
    dsimp [z]
    rw [expenditure_add, expenditure_smul_right, expenditure_smul_right]
    calc
      (1 - t) * expenditure p (x i) + t * expenditure p y'
          < (1 - t) * E.income p i + t * E.income p i := by
              have h1 : (1 - t) * expenditure p (x i) ≤ (1 - t) * E.income p i :=
                mul_le_mul_of_nonneg_left hx_feas.2 (by linarith)
              have h2 : t * expenditure p y' < t * E.income p i :=
                mul_lt_mul_of_pos_left hy'_exp ht_pos
              linarith
      _ = E.income p i := by ring
  have hz_util : E.utility i (x i) ≤ E.utility i z := by
    have hqc := (hconv i).quasiconcaveOn
    exact (le_min le_rfl hy'_lt.le).trans
      (hqc _ ⟨hx_feas.1, min_le_left _ _⟩ ⟨hy'_nn, min_le_right _ _⟩
        (by linarith) ht_pos.le (by ring)).2
  -- Step 3: Local nonsatiation around `z` produces a strictly better truncated-budget bundle.
  let Psum : ℝ := ∑ g : G, p g
  have hPsum_nn : 0 ≤ Psum := Finset.sum_nonneg fun g _ => hp g
  let rBox : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun g => B - z g)
  have hrBox_pos : 0 < rBox := by
    dsimp [rBox]
    rw [Finset.lt_inf'_iff]
    intro g _
    exact sub_pos.mpr (hz_ltB g)
  let r : ℝ := min rBox ((E.income p i - expenditure p z) / (Psum + 1))
  have hr_pos : 0 < r := lt_min hrBox_pos (div_pos (sub_pos.mpr hz_exp) (by linarith))
  obtain ⟨w, hw_nn, hw_dist, hw_lt⟩ := hlns i z hz_nn r hr_pos
  have hw_box : w ∈ truncationBox B := fun g => ⟨hw_nn g, by
    have hr_le : r ≤ B - z g := (min_le_left _ _).trans (Finset.inf'_le _ (Finset.mem_univ g))
    have hwg : w g - z g < r := (abs_lt.mp (hw_dist g)).2
    linarith⟩
  have hw_exp : expenditure p w ≤ E.income p i := by
    have hdiff : expenditure p w - expenditure p z ≤ Psum * r := by
      rw [← expenditure_sub, expenditure_eq_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left ?_ (hp g)
      exact (le_abs_self (w g - z g)).trans (hw_dist g).le
    have hr_le : r ≤ (E.income p i - expenditure p z) / (Psum + 1) := min_le_right _ _
    have hprod : r * (Psum + 1) ≤ E.income p i - expenditure p z :=
      (le_div_iff₀ (by linarith)).mp hr_le
    linarith [mul_le_mul_of_nonneg_right (show Psum ≤ Psum + 1 by linarith) hr_pos.le]
  have hw_util : E.utility i w ≤ E.utility i (x i) := (hdem i).2 w ⟨hw_box, hw_exp⟩
  linarith

end TruncationRemoval

section EquilibriumExistence

variable {I G : Type*} [Fintype I] [Fintype G] [Nonempty G]

omit [Nonempty G] in
private lemma nonempty_box_of_endowment (E : ExchangeMarket I G) :
    0 ≤ (1 : ℝ) + ∑ g : G, E.totalSupply g := by
  have hs : ∀ g : G, 0 ≤ E.totalSupply g := E.totalSupply_nonneg
  linarith [Finset.sum_nonneg (s := Finset.univ) fun g _ => hs g]

omit [Nonempty G] in
private lemma totalSupply_lt_box (E : ExchangeMarket I G) (g : G) :
    E.totalSupply g < 1 + ∑ k : G, E.totalSupply k := by
  have hle : E.totalSupply g ≤ ∑ k : G, E.totalSupply k :=
    Finset.single_le_sum (fun k _ => E.totalSupply_nonneg k) (Finset.mem_univ g)
  linarith

/-- **Arrow–Debreu competitive equilibrium existence theorem** ([ArrowDebreu1954]; [Gale1955];
[Nikaido1956]; [Debreu1956]): in a finite exchange economy over nonempty goods `G`, if every trader
has strictly positive endowments (`∀ i g, 0 < E.endowment i g`), continuous utility on `ℝ_+^G`,
convex preferences (`HasConvexPreferences`), and local nonsatiation (`IsLocallyNonsatiated`), then
there exist simplex prices `p ∈ priceSimplex G` and an allocation `x` forming a competitive
equilibrium `E.IsCompetitiveEquilibrium x p`. -/
theorem ExchangeMarket.exists_isCompetitiveEquilibrium (E : ExchangeMarket I G)
    (hend : ∀ i g, 0 < E.endowment i g)
    (hcont : ∀ i, ContinuousOn (E.utility i) {x | ∀ g, 0 ≤ x g})
    (hconv : ∀ i, HasConvexPreferences (E.utility i))
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i)) :
    ∃ x : I → G → ℝ, ∃ p ∈ priceSimplex G, E.IsCompetitiveEquilibrium x p := by
  let B : ℝ := 1 + ∑ g : G, E.totalSupply g
  have hB_nn : 0 ≤ B := nonempty_box_of_endowment E
  have hB_gt : ∀ g : G, E.totalSupply g < B := totalSupply_lt_box E
  let D := truncatedDemand E B
  let Z : (G → ℝ) → Set (G → ℝ) := fun p =>
    {z | ∃ x : I → G → ℝ, (∀ i, x i ∈ D i p) ∧ z = E.excessDemand x}
  have hZ_ne : ∀ p ∈ priceSimplex G, (Z p).Nonempty := by
    intro p hp
    choose x hx using fun i => truncatedDemand_nonempty E hB_nn i (hcont i) hp.1
    exact ⟨E.excessDemand x, x, hx, rfl⟩
  have hZ_comp : ∀ p ∈ priceSimplex G, IsCompact (Z p) := by
    intro p _
    have hEq : Z p = E.excessDemand '' (univ.pi fun i => D i p) := by
      ext z
      simp [Z]
      tauto
    rw [hEq]
    exact (isCompact_univ_pi fun i => truncatedDemand_isCompact E B i (hcont i) p).image
      (continuous_excessDemand E)
  have hZ_conv : ∀ p ∈ priceSimplex G, Convex ℝ (Z p) := by
    intro p _ z₁ hz₁ z₂ hz₂ a b ha hb hab
    obtain ⟨x₁, hx₁, rfl⟩ := hz₁
    obtain ⟨x₂, hx₂, rfl⟩ := hz₂
    refine ⟨a • x₁ + b • x₂, fun i =>
      truncatedDemand_convex E B i (hconv i) p (hx₁ i) (hx₂ i) ha hb hab, ?_⟩
    ext g
    simp only [E.excessDemand_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    calc
      a * (∑ i, x₁ i g - E.totalSupply g) + b * (∑ i, x₂ i g - E.totalSupply g)
          = (a * ∑ i, x₁ i g + b * ∑ i, x₂ i g) - (a + b) * E.totalSupply g := by ring
      _ = (a * ∑ i, x₁ i g + b * ∑ i, x₂ i g) - E.totalSupply g := by rw [hab, one_mul]
  let BoxI : Set (I → G → ℝ) := univ.pi fun _ : I => truncationBox B
  have hBoxI_comp : IsCompact BoxI := isCompact_univ_pi fun _ => truncationBox_isCompact B
  have hKZ_comp : IsCompact (E.excessDemand '' BoxI) :=
    hBoxI_comp.image (continuous_excessDemand E)
  have hZ_sub_KZ : ∀ p ∈ priceSimplex G, Z p ⊆ E.excessDemand '' BoxI := by
    rintro p _ z ⟨x, hx, rfl⟩
    exact ⟨x, fun i _ => (hx i).1.1, rfl⟩
  have hD_graph : ∀ i : I,
      IsClosed {pq : (G → ℝ) × (G → ℝ) | pq.1 ∈ priceSimplex G ∧ pq.2 ∈ D i pq.1} := fun i =>
    Cslib.Berge.isClosed_graph_of_upperHemicontinuousOn priceSimplex_isCompact.isClosed
      (fun p _ => (truncatedDemand_isCompact E B i (hcont i) p).isClosed)
      (truncatedDemand_uhc E hend hB_nn hcont i)
  have hZ_graph : IsClosed {pz : (G → ℝ) × (G → ℝ) | pz.1 ∈ priceSimplex G ∧ pz.2 ∈ Z pz.1} := by
    rw [← isSeqClosed_iff_isClosed]
    intro pz_seq ⟨p₀, z₀⟩ hmem hlim
    have hp_mem : ∀ n, (pz_seq n).1 ∈ priceSimplex G := fun n => (hmem n).1
    have hp₀_lim : Tendsto (fun n => (pz_seq n).1) atTop (𝓝 p₀) :=
      continuous_fst.continuousAt.tendsto.comp hlim
    have hz₀_lim : Tendsto (fun n => (pz_seq n).2) atTop (𝓝 z₀) :=
      continuous_snd.continuousAt.tendsto.comp hlim
    have hp₀ : p₀ ∈ priceSimplex G := priceSimplex_isCompact.isClosed.mem_of_tendsto hp₀_lim
      (Eventually.of_forall hp_mem)
    choose x_seq hx_dem hx_eq using fun n => (hmem n).2
    have hx_box : ∀ n, x_seq n ∈ BoxI := fun n i _ => (hx_dem n i).1.1
    obtain ⟨x₀, _, φ, hφ, hlim_x⟩ := hBoxI_comp.isSeqCompact hx_box
    have hx₀_dem : ∀ i, x₀ i ∈ D i p₀ := by
      intro i
      have hlim_pair :
          Tendsto (fun k => ((pz_seq (φ k)).1, x_seq (φ k) i)) atTop (𝓝 (p₀, x₀ i)) :=
        (hp₀_lim.comp hφ.tendsto_atTop).prodMk_nhds
          ((continuous_apply i).continuousAt.tendsto.comp hlim_x)
      exact ((hD_graph i).mem_of_tendsto hlim_pair
        (Eventually.of_forall fun k => ⟨hp_mem (φ k), hx_dem (φ k) i⟩)).2
    have hz_eq_x : Tendsto (fun k => (pz_seq (φ k)).2) atTop (𝓝 (E.excessDemand x₀)) := by
      have heq : (fun k => (pz_seq (φ k)).2) = fun k => E.excessDemand (x_seq (φ k)) :=
        funext fun k => hx_eq (φ k)
      rw [heq]
      exact (continuous_excessDemand E).continuousAt.tendsto.comp hlim_x
    have hz₀_eq : z₀ = E.excessDemand x₀ :=
      tendsto_nhds_unique (hz₀_lim.comp hφ.tendsto_atTop) hz_eq_x
    exact ⟨hp₀, x₀, hx₀_dem, hz₀_eq⟩
  have hZ_uhc : UpperHemicontinuousOn Z (priceSimplex G) :=
    Cslib.Berge.upperHemicontinuousOn_of_isClosed_graph hKZ_comp.isSeqCompact hZ_sub_KZ hZ_graph
  have hZ_walras : ∀ p ∈ priceSimplex G, ∀ z ∈ Z p, expenditure p z ≤ 0 := by
    rintro p _ z ⟨x, hx, rfl⟩
    exact E.expenditure_excessDemand_le_zero fun i => ⟨fun g => ((hx i).1.1 g).1, (hx i).1.2⟩
  obtain ⟨p, hp, z, ⟨x, hx_dem, rfl⟩, hclear⟩ :=
    exists_excessDemand_le_zero_of_upperHemicontinuousOn hZ_ne hZ_comp hZ_conv hZ_uhc hZ_walras
  have hdem_full : ∀ i, x i ∈ E.demandSet p i :=
    mem_demandSet_of_mem_truncatedDemand E hB_gt hp.1
      (fun i => income_pos_of_endowment_pos E hend hp i) hcont hconv hlns hx_dem hclear
  exact ⟨x, p, hp,
    ExchangeMarket.IsCompetitiveEquilibrium.of_locallyNonsatiated hlns hp.1 hdem_full hclear⟩

/-- Strictly quasiconcave specialization of Arrow–Debreu existence routed directly through
`Cslib.Berge.exists_unique_continuousOn_argmaxSet` and the single-valued Gale–Nikaido–Debreu
lemma `exists_excessDemand_le_zero_of_continuousOn`. -/
theorem ExchangeMarket.exists_isCompetitiveEquilibrium_of_strictQuasiconcaveOn
    (E : ExchangeMarket I G)
    (hend : ∀ i g, 0 < E.endowment i g)
    (hcont : ∀ i, ContinuousOn (E.utility i) {x | ∀ g, 0 ≤ x g})
    (hsqc : ∀ i, ∀ ⦃x y : G → ℝ⦄, (∀ g, 0 ≤ x g) → (∀ g, 0 ≤ y g) → x ≠ y →
      ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
        min (E.utility i x) (E.utility i y) < E.utility i (a • x + b • y))
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i)) :
    ∃ x : I → G → ℝ, ∃ p ∈ priceSimplex G, E.IsCompetitiveEquilibrium x p := by
  let B : ℝ := 1 + ∑ g : G, E.totalSupply g
  have hB_nn : 0 ≤ B := nonempty_box_of_endowment E
  have hB_gt : ∀ g : G, E.totalSupply g < B := totalSupply_lt_box E
  have hconv : ∀ i, HasConvexPreferences (E.utility i) := by
    intro i x _ y₁ hy₁ y₂ hy₂ a b ha hb hab
    refine ⟨fun g => add_nonneg (mul_nonneg ha (hy₁.1 g)) (mul_nonneg hb (hy₂.1 g)), ?_⟩
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · obtain rfl : b = 1 := by linarith
      simpa using hy₂.2
    · rcases eq_or_lt_of_le hb with rfl | hb_pos
      · obtain rfl : a = 1 := by linarith
        simpa using hy₁.2
      · by_cases heq : y₁ = y₂
        · subst heq
          have : a • y₁ + b • y₁ = y₁ := by rw [← add_smul, hab, one_smul]
          simpa [this] using hy₁.2
        · exact (lt_min hy₁.2 hy₂.2).trans (hsqc i hy₁.1 hy₂.1 heq ha_pos hb_pos hab)
  let D := truncatedDemand E B
  have hd_ex : ∀ i : I, ∃ d : (G → ℝ) → (G → ℝ),
      ContinuousOn d (priceSimplex G) ∧ ∀ p ∈ priceSimplex G, D i p = {d p} := by
    intro i
    refine Cslib.Berge.exists_unique_continuousOn_argmaxSet
      (fun p (hp : p ∈ priceSimplex G) => truncatedBudget_nonempty E hB_nn hp.1 i)
      (fun p _ => truncatedBudget_isCompact E B p i)
      (fun p _ => truncatedBudget_convex E B p i)
      (truncatedBudget_uhc E B i)
      (truncatedBudget_lhc E hend B i)
      ((hcont i).comp continuousOn_snd fun _ hp g => (hp.2.1 g).1)
      fun _ _ _ _ hx hy hne _ _ ha hb hab =>
        hsqc i (fun g => (hx.1 g).1) (fun g => (hy.1 g).1) hne ha hb hab
  choose d hd_cont hd_sing using hd_ex
  have hd_mem : ∀ i, ∀ p ∈ priceSimplex G, d i p ∈ D i p := fun i p hp => by
    rw [hd_sing i p hp]
    exact rfl
  let z : (G → ℝ) → (G → ℝ) := fun p => E.excessDemand (fun i => d i p)
  have hz_cont : ContinuousOn z (priceSimplex G) :=
    (continuous_excessDemand E).continuousOn.comp (continuousOn_pi.mpr hd_cont)
      (fun _ _ => mem_univ _)
  have hz_walras : ∀ p ∈ priceSimplex G, expenditure p (z p) ≤ 0 := fun p hp =>
    E.expenditure_excessDemand_le_zero fun i =>
      ⟨fun g => ((hd_mem i p hp).1.1 g).1, (hd_mem i p hp).1.2⟩
  obtain ⟨p, hp, hclear⟩ := exists_excessDemand_le_zero_of_continuousOn hz_cont hz_walras
  have hdem_full : ∀ i, d i p ∈ E.demandSet p i :=
    mem_demandSet_of_mem_truncatedDemand E hB_gt hp.1
      (fun i => income_pos_of_endowment_pos E hend hp i) hcont hconv hlns
      (fun i => hd_mem i p hp) hclear
  exact ⟨fun i => d i p, p, hp,
    ExchangeMarket.IsCompetitiveEquilibrium.of_locallyNonsatiated hlns hp.1 hdem_full hclear⟩

end EquilibriumExistence

end Cslib.GameTheory.Market
