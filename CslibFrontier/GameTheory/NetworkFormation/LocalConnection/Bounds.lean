/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.NetworkFormation.LocalConnection
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Acyclic
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.EdgeSide
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tighter optima characterizations, small-`α`, tree, and `3d - 1` bounds for local connection games

Complements `CslibFrontier.GameTheory.NetworkFormation.LocalConnection` ([TardosWexler2007],
Section 19.2; [FabrikantLuthraManevaPapadimitriouShenker2003]; all newly cited locators in this
file unverified against primary PDFs) with:

* **Exact social-optimum characterizations** ([TardosWexler2007], Exercises 19.1–19.2):
  equality in `le_networkCost_of_preconnected` holds iff every pair of vertices has distance at most
  `2` (`networkCost_eq_iff_diam_le_two`), giving strict uniqueness of `⊤` for `0 ≤ α < 2`
  (`isOptimalNetwork_iff_eq_top_of_lt_two`), strict uniqueness of stars `SimpleGraph.starGraph r`
  for `α > 2` (`isOptimalNetwork_iff_exists_starGraph_of_two_lt`), and characterization of optimal
  networks at `α = 2` as connected diameter-`≤ 2` graphs (`isOptimalNetwork_two_iff`).
* **Small-`α` Price of Anarchy** ([TardosWexler2007], Exercise 19.3): for `0 ≤ α < 1`, every pure
  Nash equilibrium forms the complete graph `⊤` and has `PoA = 1`
  (`IsPureNash.formedGraph_eq_top_of_lt_one`, `IsPureNash.isSocialOptimum_of_lt_one`); for
  `0 ≤ α < 2`, every pure Nash equilibrium has diameter at most `2` and social cost at most
  `(4 / 3)` times optimal (`IsPureNash.socialECost_le_four_thirds_mul_of_lt_two`).
* **Tree equilibria Price of Anarchy ≤ 5** ([FabrikantLuthraManevaPapadimitriouShenker2003],
  Theorem 2): via a tree centroid and `SimpleGraph.edgeSide` cuts, every pure Nash equilibrium
  whose formed graph is a tree satisfies `SC(s) ≤ 5 · OPT`
  (`IsPureNash.socialCost_le_five_mul_of_isTree`, `IsPureNash.socialECost_le_five_mul_of_isTree`).
* **Tighter `3d - 1` Lemma 19.4 factor and Theorem 19.5 corollaries**: using a shortest-path
  spanning subgraph (`SimpleGraph.parentGraph`), strengthens `[TardosWexler2007]` Lemma 19.4's
  `3d` factor to `3d - 1` for diameter `d ≥ 1` (`IsPureNash.socialCost_le_three_diam_sub_one_mul`,
  `IsPureNash.socialECost_le_three_diam_sub_one_mul`). Combining with `LocalConnection`'s sharp
  diameter bound `d ≤ √(4α + 1) ≤ 2√α + 1` (accounting for the odd-diameter `+ 1` parity gap
  omitted by `[TardosWexler2007]`, Theorem 19.5) yields `PoA ≤ 3√(4α + 1) - 1 ≤ 6√α + 2`
  (`IsPureNash.socialECost_le_three_mul_sqrt_four_add_one_sub_one_mul`,
  `IsPureNash.socialECost_le_six_mul_sqrt_add_two_mul`).

## References

* [FabrikantLuthraManevaPapadimitriouShenker2003]
* [TardosWexler2007]
-/

public section

namespace Cslib.GameTheory.LocalConnection

open Finset SimpleGraph
open scoped BigOperators ENNReal

section OptimalNetworks

variable {V : Type*} [Fintype V]

omit [Fintype V] in
private noncomputable def diamLowerTerm [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : ℝ :=
  (if u = v then 0 else 2) - if G.Adj u v then 1 else 0

omit [Fintype V] in
private theorem diamLowerTerm_le_dist [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hc : G.Preconnected) (u v : V) : diamLowerTerm G u v ≤ (G.dist u v : ℝ) := by
  unfold diamLowerTerm
  by_cases huv : u = v
  · subst huv; simp
  · by_cases hadj : G.Adj u v
    · simp only [huv, ↓reduceIte, hadj, dist_eq_one_iff_adj.mpr hadj, Nat.cast_one]
      norm_num
    · simp only [huv, ↓reduceIte, hadj, sub_zero]
      exact_mod_cast (hc u v).one_lt_dist_of_ne_of_not_adj huv hadj

private theorem sum_sum_diamLowerTerm [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ u : V, ∑ v : V, diamLowerTerm G u v) =
      2 * (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) - 2 * (G.edgeSet.ncard : ℝ) := by
  unfold diamLowerTerm
  simp only [sum_sub_distrib]
  have hne2 : (∑ u : V, ∑ v : V, if u = v then (0 : ℝ) else 2) =
      2 * (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) := by
    have hinner : ∀ u : V, (∑ v : V, if u = v then (0 : ℝ) else 2) =
        2 * ((Fintype.card V - 1 : ℕ) : ℝ) := fun u => by
      rw [← sum_erase_add _ _ (mem_univ u)]
      simp only [↓reduceIte, add_zero]
      have h1 : ∀ v ∈ univ.erase u, (if u = v then (0 : ℝ) else 2) = 2 := fun v hv => by
        simp only [(ne_of_mem_erase hv).symm, ↓reduceIte]
      rw [sum_congr rfl h1, sum_const, card_erase_of_mem (mem_univ u), card_univ, nsmul_eq_mul,
        mul_comm]
    simp only [hinner, sum_const, card_univ, nsmul_eq_mul]
    ring
  have hadj1 : (∑ u : V, ∑ v : V, if G.Adj u v then (1 : ℝ) else 0) =
      2 * (G.edgeSet.ncard : ℝ) := by
    have hinner : ∀ u : V, (∑ v : V, if G.Adj u v then (1 : ℝ) else 0) = (G.degree u : ℝ) :=
      fun u => by
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, ← G.neighborFinset_eq_filter,
          G.card_neighborFinset_eq_degree]
    simp only [hinner, ncard_edgeSet_eq_card_edgeFinset]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hne2, hadj1]

/-- Equality holds in `le_networkCost_of_preconnected` iff every pair of vertices has distance at
most `2` ([TardosWexler2007], Exercises 19.1–19.2, locator not re-verified against primary PDF). -/
theorem networkCost_eq_iff_diam_le_two {α : ℝ} {G : SimpleGraph V} (hc : G.Preconnected) :
    networkCost α G =
      (α - 2) * (G.edgeSet.ncard : ℝ) +
        2 * (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) ↔
      ∀ u v : V, G.dist u v ≤ 2 := by
  classical
  have heq_iff : networkCost α G =
      (α - 2) * (G.edgeSet.ncard : ℝ) +
        2 * (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) ↔
      ∑ u : V, ∑ v : V, diamLowerTerm G u v = ∑ u : V, ∑ v : V, (G.dist u v : ℝ) := by
    rw [networkCost_def, sum_sum_diamLowerTerm]
    constructor <;> intro h <;> linarith
  rw [heq_iff, sum_eq_sum_iff_of_le
    fun u _ => sum_le_sum fun v _ => diamLowerTerm_le_dist hc u v]
  simp only [mem_univ, forall_true_left]
  refine ⟨fun h u v => ?_, fun h u => sum_congr rfl fun v _ => ?_⟩
  · have huv := (sum_eq_sum_iff_of_le fun w _ => diamLowerTerm_le_dist hc u w).mp (h u) v
      (mem_univ v)
    unfold diamLowerTerm at huv
    by_cases heq : u = v
    · subst heq; simp
    · by_cases hadj : G.Adj u v
      · rw [dist_eq_one_iff_adj.mpr hadj]; omega
      · simp only [heq, ↓reduceIte, hadj, sub_zero] at huv
        exact_mod_cast huv.symm.le
  · apply le_antisymm (diamLowerTerm_le_dist hc u v)
    unfold diamLowerTerm
    by_cases heq : u = v
    · subst heq; simp
    · by_cases hadj : G.Adj u v
      · simp only [heq, ↓reduceIte, hadj, dist_eq_one_iff_adj.mpr hadj, Nat.cast_one]
        norm_num
      · simp only [heq, ↓reduceIte, hadj, sub_zero]
        exact_mod_cast h u v

private theorem networkCost_top_eq_diam_form (α : ℝ) :
    networkCost α (⊤ : SimpleGraph V) =
      (α - 2) * ((⊤ : SimpleGraph V).edgeSet.ncard : ℝ) +
        2 * (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) := by
  classical
  refine (networkCost_eq_iff_diam_le_two (α := α) preconnected_top).mpr fun u v => ?_
  by_cases huv : u = v
  · subst huv; simp
  · rw [dist_eq_one_iff_adj.mpr (by simp [huv])]; omega

private theorem networkCost_starGraph_eq_diam_form [Nonempty V] (α : ℝ) (r : V) :
    networkCost α (starGraph r) =
      (α - 2) * ((Fintype.card V - 1 : ℕ) : ℝ) +
        2 * (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) := by
  have hcast : (Fintype.card V : ℝ) = ((Fintype.card V - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel (Fintype.card_pos (α := V))).symm
  rw [networkCost_starGraph, hcast]
  ring

/-- **Strict uniqueness of `K_n` for `0 ≤ α < 2`** ([TardosWexler2007], Exercise 19.1, locator not
re-verified against primary PDF): a network minimizes `networkECost α` iff it is the complete
graph `⊤`. -/
theorem isOptimalNetwork_iff_eq_top_of_lt_two {α : ℝ} (hα₀ : 0 ≤ α) (hα : α < 2)
    {G : SimpleGraph V} :
    IsOptimalNetwork α G ↔ G = ⊤ := by
  classical
  refine ⟨fun hopt => ?_, fun htop => htop ▸ isOptimalNetwork_top hα₀ hα.le⟩
  rcases isEmpty_or_nonempty V with hE | hNE
  · have := hE
    exact Subsingleton.elim G ⊤
  · have : Nonempty V := hNE
    have hleE := hopt ⊤
    have hconn : G.Connected := by
      by_contra hnc
      rw [networkECost_eq_top_iff.mpr hnc,
        networkECost_eq_ofReal_of_preconnected hα₀ preconnected_top] at hleE
      exact absurd hleE (by simp)
    rw [networkECost_eq_ofReal_of_connected hα₀ hconn,
      networkECost_eq_ofReal_of_preconnected hα₀ preconnected_top,
      ENNReal.ofReal_le_ofReal_iff (networkCost_nonneg hα₀ ⊤)] at hleE
    have hlow := le_networkCost_of_preconnected (α := α) hconn.preconnected
    have hle_m : G.edgeSet.ncard ≤ (⊤ : SimpleGraph V).edgeSet.ncard := by
      simp only [ncard_edgeSet_eq_card_edgeFinset]
      exact card_le_card (edgeFinset_mono le_top)
    have hle_mR : (G.edgeSet.ncard : ℝ) ≤ ((⊤ : SimpleGraph V).edgeSet.ncard : ℝ) := by
      exact_mod_cast hle_m
    have hcost_top := networkCost_top_eq_diam_form (V := V) α
    have heq_mR : (G.edgeSet.ncard : ℝ) = ((⊤ : SimpleGraph V).edgeSet.ncard : ℝ) := by
      nlinarith
    have heq_card : G.edgeFinset.card = (⊤ : SimpleGraph V).edgeFinset.card := by
      simp only [ncard_edgeSet_eq_card_edgeFinset] at heq_mR
      exact_mod_cast heq_mR
    rw [← edgeFinset_inj]
    exact eq_of_subset_of_card_le (edgeFinset_mono le_top) heq_card.ge

omit [Fintype V] in
/-- Every finite tree of diameter at most `2` is `SimpleGraph.starGraph r` for some center `r`. -/
private theorem exists_eq_starGraph_of_isTree_of_diam_le_two [Finite V] {G : SimpleGraph V}
    (hT : G.IsTree) (hdiam : ∀ u v : V, G.dist u v ≤ 2) :
    ∃ r : V, G = starGraph r := by
  have := Fintype.ofFinite V
  classical
  have := hT.connected.nonempty
  by_cases hsub : Subsingleton V
  · refine ⟨Classical.arbitrary V, ?_⟩
    ext u v
    have huv : u = v := Subsingleton.elim u v
    subst huv
    simp
  · rw [not_subsingleton_iff_nontrivial] at hsub
    obtain ⟨l, hl⟩ := hT.exists_vert_degree_one_of_nontrivial
    obtain ⟨c, hlc, hc_uniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hl
    refine ⟨c, eq_starGraph_of_isUniversal_of_cliqueFree_three ?_ hT.isAcyclic.cliqueFree_three⟩
    intro v hvc
    by_cases hvl : v = l
    · subst hvl; exact hlc.symm
    · have hnot_lv : ¬ G.Adj l v := fun h => hvc.symm (hc_uniq v h)
      have hge2 : 2 ≤ G.dist l v :=
        hT.connected.one_lt_dist_of_ne_of_not_adj (Ne.symm hvl) hnot_lv
      have hd2 : G.dist l v = 2 := le_antisymm (hdiam l v) hge2
      have hed2 : G.edist l v = 2 := by
        rw [← (hT.connected l v).coe_dist_eq_edist, hd2]
        rfl
      obtain ⟨_, -, ⟨x, hx⟩⟩ := edist_eq_two_iff.mp hed2
      rw [mem_commonNeighbors] at hx
      have hxc : x = c := hc_uniq x hx.1
      subst hxc
      exact hx.2.symm

/-- **Strict uniqueness of star graphs for `α > 2`** ([TardosWexler2007], Exercise 19.1, locator not
re-verified against primary PDF): on a nonempty vertex set, a network minimizes `networkECost α`
iff it is `SimpleGraph.starGraph r` for some center `r : V`. -/
theorem isOptimalNetwork_iff_exists_starGraph_of_two_lt [Nonempty V] {α : ℝ} (hα : 2 < α)
    {G : SimpleGraph V} :
    IsOptimalNetwork α G ↔ ∃ r : V, G = starGraph r := by
  classical
  have hα₀ : 0 ≤ α := by linarith
  refine ⟨fun hopt => ?_, ?_⟩
  · obtain ⟨r₀⟩ := ‹Nonempty V›
    have hleE := hopt (starGraph r₀)
    have hconn : G.Connected := by
      by_contra hnc
      rw [networkECost_eq_top_iff.mpr hnc,
        networkECost_eq_ofReal_of_connected hα₀ (connected_starGraph r₀)] at hleE
      exact absurd hleE (by simp)
    rw [networkECost_eq_ofReal_of_connected hα₀ hconn,
      networkECost_eq_ofReal_of_connected hα₀ (connected_starGraph r₀),
      ENNReal.ofReal_le_ofReal_iff (networkCost_nonneg hα₀ _)] at hleE
    have hlow := le_networkCost_of_preconnected (α := α) hconn.preconnected
    have hconn_card := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hconn_card
    have hm_ge : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ (G.edgeSet.ncard : ℝ) := by
      exact_mod_cast (show Fintype.card V - 1 ≤ G.edgeSet.ncard by omega)
    rw [networkCost_starGraph_eq_diam_form] at hleE
    have hm_eqR : (G.edgeSet.ncard : ℝ) = ((Fintype.card V - 1 : ℕ) : ℝ) := by
      nlinarith
    have hm_eq : G.edgeFinset.card + 1 = Fintype.card V := by
      have hcard : 1 ≤ Fintype.card V := Fintype.card_pos
      rw [← ncard_edgeSet_eq_card_edgeFinset]
      have h1 : G.edgeSet.ncard = Fintype.card V - 1 := by exact_mod_cast hm_eqR
      omega
    have hT : G.IsTree := by
      rw [isTree_iff_connected_and_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        ← edgeFinset_card]
      exact ⟨hconn, hm_eq⟩
    have hdiam : ∀ u v : V, G.dist u v ≤ 2 := by
      refine (networkCost_eq_iff_diam_le_two (α := α) hconn.preconnected).mp ?_
      nlinarith
    exact exists_eq_starGraph_of_isTree_of_diam_le_two hT hdiam
  · rintro ⟨r, rfl⟩
    exact isOptimalNetwork_starGraph hα.le r

/-- **Diameter-`≤ 2` characterization of optimal networks at `α = 2`** ([TardosWexler2007],
Exercise 19.2, locator not re-verified against primary PDF): on a nonempty vertex set, a network
minimizes `networkECost 2` iff it is connected and every pair of vertices has distance at most
`2`. -/
theorem isOptimalNetwork_two_iff [Nonempty V] {G : SimpleGraph V} :
    IsOptimalNetwork 2 G ↔ G.Connected ∧ ∀ u v : V, G.dist u v ≤ 2 := by
  classical
  have hcost_top2 : networkCost 2 (⊤ : SimpleGraph V) =
      2 * (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) := by
    rw [networkCost_top_eq_diam_form]
    ring
  refine ⟨fun hopt => ?_, fun ⟨hc, hdiam⟩ G' => ?_⟩
  · have hleE := hopt ⊤
    have hconn : G.Connected := by
      by_contra hnc
      rw [networkECost_eq_top_iff.mpr hnc,
        networkECost_eq_ofReal_of_preconnected (by norm_num) preconnected_top] at hleE
      exact absurd hleE (by simp)
    rw [networkECost_eq_ofReal_of_connected (by norm_num) hconn,
      networkECost_eq_ofReal_of_preconnected (by norm_num) preconnected_top,
      ENNReal.ofReal_le_ofReal_iff (networkCost_nonneg (by norm_num) _), hcost_top2] at hleE
    have hlow := le_networkCost_of_preconnected (α := 2) hconn.preconnected
    have heq : networkCost 2 G =
        (2 - 2) * (G.edgeSet.ncard : ℝ) +
          2 * (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) := by
      linarith
    exact ⟨hconn, (networkCost_eq_iff_diam_le_two hconn.preconnected).mp heq⟩
  · have heq := (networkCost_eq_iff_diam_le_two (α := 2) hc.preconnected).mpr hdiam
    by_cases hc' : G'.Connected
    · rw [networkECost_eq_ofReal_of_connected (by norm_num) hc,
        networkECost_eq_ofReal_of_connected (by norm_num) hc',
        ENNReal.ofReal_le_ofReal_iff (networkCost_nonneg (by norm_num) G')]
      have hlow' := le_networkCost_of_preconnected (α := 2) hc'.preconnected
      linarith
    · rw [networkECost_eq_top_iff.mpr hc']
      exact le_top

end OptimalNetworks

section PriceOfAnarchySmallAlpha

variable {V : Type*} [Fintype V] [DecidableEq V]

private def addLink (s : Profile V) (u v : V) : Profile V :=
  Function.update s u (LinkSet.ofFinset u (insert v (s u).neighbors))

omit [Fintype V] in
private theorem formedGraph_le_addLink (s : Profile V) (u v : V) :
    formedGraph s ≤ formedGraph (addLink s u v) := by
  intro a b hab
  have hab_ne : a ≠ b := hab.ne
  rw [formedGraph_adj] at hab ⊢
  simp only [addLink]
  by_cases hau : a = u
  · subst hau
    rw [Function.update_self, Function.update_of_ne hab_ne.symm]
    exact hab.elim
      (fun h => Or.inl (LinkSet.mem_ofFinset.mpr ⟨hab_ne.symm, mem_insert_of_mem h⟩)) Or.inr
  · by_cases hbu : b = u
    · subst hbu
      rw [Function.update_of_ne hau, Function.update_self]
      exact hab.elim Or.inl
        (fun h => Or.inr (LinkSet.mem_ofFinset.mpr ⟨hau, mem_insert_of_mem h⟩))
    · rw [Function.update_of_ne hau, Function.update_of_ne hbu]
      exact hab

omit [Fintype V] in
private theorem adj_addLink {s : Profile V} {u v : V} (huv : u ≠ v) :
    (formedGraph (addLink s u v)).Adj u v := by
  rw [formedGraph_adj]
  left
  rw [addLink, Function.update_self, LinkSet.mem_ofFinset]
  exact ⟨huv.symm, mem_insert_self v _⟩

/-- At any pure Nash equilibrium (`0 ≤ α`), adding a single link `(u, v)` decreases player `u`'s
total distance sum over any subset `S : Finset V` by at most `α`. -/
private theorem sum_dist_sub_addLink_le {α : ℝ} (hα₀ : 0 ≤ α) {s : Profile V}
    (hs : IsPureNash α s) (u v : V) (S : Finset V) :
    ∑ x ∈ S, (((formedGraph s).dist u x : ℝ) -
      ((formedGraph (addLink s u v)).dist u x : ℝ)) ≤ α := by
  let s' := addLink s u v
  have hmono : formedGraph s ≤ formedGraph s' := formedGraph_le_addLink s u v
  have hreach' : ∀ x, (formedGraph s').Reachable u x :=
    fun x => (hs.preconnected u x).mono hmono
  have hdist_le : ∀ x, (formedGraph s').dist u x ≤ (formedGraph s).dist u x := fun x =>
    (hs.preconnected u x).dist_anti hmono
  have hnonneg : ∀ x : V,
      0 ≤ ((formedGraph s).dist u x : ℝ) - ((formedGraph s').dist u x : ℝ) :=
    fun x => sub_nonneg.mpr (by exact_mod_cast hdist_le x)
  have hsub : ∑ x ∈ S, (((formedGraph s).dist u x : ℝ) - ((formedGraph s').dist u x : ℝ)) ≤
      (∑ x : V, ((formedGraph s).dist u x : ℝ)) -
        ∑ x : V, ((formedGraph s').dist u x : ℝ) := by
    rw [← sum_sub_distrib]
    exact sum_le_univ_sum_of_nonneg hnonneg
  have hne_cost := hs.playerCost_le hα₀ hreach'
  rw [playerCost_def, playerCost_def] at hne_cost
  have hcard : ((s' u).neighbors.card : ℝ) ≤ ((s u).neighbors.card : ℝ) + 1 := by
    simp only [s', addLink, Function.update_self, LinkSet.neighbors_ofFinset]
    have h1 := card_erase_le (a := u) (s := insert v (s u).neighbors)
    have h2 := card_insert_le v (s u).neighbors
    exact_mod_cast h1.trans h2
  dsimp only [s', addLink] at hsub hcard
  dsimp only [addLink]
  nlinarith

/-- At any pure Nash equilibrium (`0 ≤ α`), all vertices `u, v` satisfy `dist u v ≤ α + 1`. -/
theorem IsPureNash.dist_le_alpha_add_one {α : ℝ} (hα₀ : 0 ≤ α) {s : Profile V}
    (hs : IsPureNash α s) (u v : V) :
    ((formedGraph s).dist u v : ℝ) ≤ α + 1 := by
  by_cases huv : u = v
  · subst huv
    simp only [SimpleGraph.dist_self, Nat.cast_zero]
    linarith
  · have h := sum_dist_sub_addLink_le hα₀ hs u v {v}
    rw [sum_singleton, dist_eq_one_iff_adj.mpr (adj_addLink huv), Nat.cast_one] at h
    linarith

/-- **Uniqueness of `K_n` for `0 ≤ α < 1`** ([TardosWexler2007], Exercise 19.3, locator not
re-verified against primary PDF): when `0 ≤ α < 1`, every pure Nash equilibrium forms the complete
graph `⊤`. -/
theorem IsPureNash.formedGraph_eq_top_of_lt_one {α : ℝ} (hα₀ : 0 ≤ α) (hα : α < 1)
    {s : Profile V} (hs : IsPureNash α s) : formedGraph s = ⊤ := by
  ext u v
  simp only [top_adj]
  refine ⟨fun h => h.ne, fun huv => ?_⟩
  have hd : ((formedGraph s).dist u v : ℝ) < 2 := by
    linarith [hs.dist_le_alpha_add_one hα₀ u v]
  have hd_nat : (formedGraph s).dist u v < 2 := by exact_mod_cast hd
  have hd_pos : 0 < (formedGraph s).dist u v := (hs.preconnected u v).pos_dist_of_ne huv
  exact dist_eq_one_iff_adj.mp (by omega)

/-- **`PoA = 1` for `0 ≤ α < 1`** ([TardosWexler2007], Exercise 19.3, locator not re-verified
against primary PDF): every pure Nash equilibrium for `0 ≤ α < 1` is socially optimal. -/
theorem IsPureNash.isSocialOptimum_of_lt_one {α : ℝ} (hα₀ : 0 ≤ α) (hα : α < 1)
    {s : Profile V} (hs : IsPureNash α s) : IsSocialOptimum α s := fun s' => by
  rw [hs.socialECost_eq_networkECost hα₀, hs.formedGraph_eq_top_of_lt_one hα₀ hα]
  exact isOptimalNetwork_iff_forall_profile.mp (isOptimalNetwork_top hα₀ (by linarith)) s'

/-- When `0 ≤ α < 2`, every pure Nash equilibrium has diameter at most `2`. -/
theorem IsPureNash.dist_le_two_of_lt_two {α : ℝ} (hα₀ : 0 ≤ α) (hα : α < 2)
    {s : Profile V} (hs : IsPureNash α s) (u v : V) : (formedGraph s).dist u v ≤ 2 := by
  have hd : ((formedGraph s).dist u v : ℝ) < 3 := by
    linarith [hs.dist_le_alpha_add_one hα₀ u v]
  have hd_nat : (formedGraph s).dist u v < 3 := by exact_mod_cast hd
  omega

private theorem IsPureNash.socialCost_eq_zero_of_subsingleton [Subsingleton V] {α : ℝ} (hα₀ : 0 ≤ α)
    {s : Profile V} (hs : IsPureNash α s) : socialCost α s = 0 := by
  rw [hs.socialCost_eq_networkCost hα₀, networkCost_def]
  have he0 : (formedGraph s).edgeSet = ∅ := by
    ext ⟨a, b⟩
    simp only [mem_edgeSet, Set.mem_empty_iff_false, iff_false]
    rw [Subsingleton.elim a b]
    exact (formedGraph s).loopless.irrefl b
  have hd0 : (∑ u : V, ∑ v : V, ((formedGraph s).dist u v : ℝ)) = 0 :=
    sum_eq_zero fun u _ => sum_eq_zero fun v _ => by
      rw [Subsingleton.elim u v, SimpleGraph.dist_self, Nat.cast_zero]
  rw [he0, Set.ncard_empty, Nat.cast_zero, mul_zero, hd0, add_zero]

/-- **`PoA ≤ 4 / 3` for `0 ≤ α < 2`** (real-valued, against connected profiles): every pure Nash
equilibrium has diameter at most `2`, hence social cost at most `(4 / 3)` times any connected
profile's cost. -/
theorem IsPureNash.socialCost_le_four_thirds_mul_of_lt_two {α : ℝ} (hα₀ : 0 ≤ α) (hα : α < 2)
    {s : Profile V} (hs : IsPureNash α s) {s' : Profile V} (hc' : (formedGraph s').Connected) :
    socialCost α s ≤ (4 / 3) * socialCost α s' := by
  have : Nonempty V := hc'.nonempty
  rcases lt_or_ge α 1 with hα1 | hα1
  · have hopt := hs.isSocialOptimum_of_lt_one hα₀ hα1 s'
    rw [socialECost_eq_ofReal_of_connected hα₀ hs.connected,
      socialECost_eq_ofReal_of_connected hα₀ hc',
      ENNReal.ofReal_le_ofReal_iff (socialCost_nonneg hα₀ s')] at hopt
    have hnn := socialCost_nonneg hα₀ s'
    linarith
  · rcases le_or_gt (Fintype.card V) 1 with hV | hV
    · have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hV
      have hsc0 := hs.socialCost_eq_zero_of_subsingleton hα₀
      have hnn := socialCost_nonneg hα₀ s'
      rw [hsc0]
      linarith
    · obtain ⟨r⟩ := hc'.nonempty
      have hc := hs.connected
      have heq := (networkCost_eq_iff_diam_le_two (α := α) hc.preconnected).mpr
        (hs.dist_le_two_of_lt_two hα₀ hα)
      have hconn_card := hc.card_vert_le_card_edgeSet_add_one
      rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hconn_card
      have hm_ge : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ ((formedGraph s).edgeSet.ncard : ℝ) := by
        exact_mod_cast (show Fintype.card V - 1 ≤ (formedGraph s).edgeSet.ncard by omega)
      have hle_star : socialCost α s ≤ socialCost α (starCenterProfile r) := by
        rw [hs.socialCost_eq_networkCost hα₀, heq,
          (noDoubleEdges_starCenterProfile r).socialCost_eq_networkCost,
          formedGraph_starCenterProfile, networkCost_starGraph_eq_diam_form]
        nlinarith
      exact hle_star.trans (socialCost_starCenterProfile_lt_four_thirds_mul hα1 hα.le hV r hc').le

/-- **`PoA ≤ 4 / 3` for `0 ≤ α < 2`** (extended, for all strategy profiles `s'`). -/
theorem IsPureNash.socialECost_le_four_thirds_mul_of_lt_two {α : ℝ} (hα₀ : 0 ≤ α) (hα : α < 2)
    {s : Profile V} (hs : IsPureNash α s) (s' : Profile V) :
    socialECost α s ≤ ENNReal.ofReal (4 / 3) * socialECost α s' := by
  rcases isEmpty_or_nonempty V with hE | hNE
  · have := hE
    simp only [socialECost_def, univ_eq_empty, sum_empty, zero_le]
  · have : Nonempty V := hNE
    by_cases hc' : (formedGraph s').Connected
    · rw [socialECost_eq_ofReal_of_connected hα₀ hs.connected,
        socialECost_eq_ofReal_of_connected hα₀ hc',
        ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (hs.socialCost_le_four_thirds_mul_of_lt_two hα₀ hα hc')
    · rw [socialECost_eq_top_iff.mpr hc', ENNReal.mul_top (by positivity)]
      exact le_top

end PriceOfAnarchySmallAlpha

section TreeEquilibria

variable {V : Type*} [Fintype V]

/-- A sum over `V` vanishing at `u` and bounded by `c` elsewhere is at most `(|V| - 1) * c`. -/
private theorem sum_le_card_sub_one_mul {f : V → ℝ} {u : V} {c : ℝ}
    (hu : f u = 0) (hf : ∀ x, x ≠ u → f x ≤ c) :
    ∑ x, f x ≤ ((Fintype.card V - 1 : ℕ) : ℝ) * c := by
  classical
  rw [← sum_erase_add _ _ (mem_univ u), hu, add_zero, ← card_univ,
    ← card_erase_of_mem (mem_univ u), ← nsmul_eq_mul, ← sum_const]
  exact sum_le_sum fun x hx => hf x (ne_of_mem_erase hx)

/-- In a tree `T`, if `u ∈ edgeSide T a b` and `v ∉ edgeSide T a b`, every walk from `u` to `v`
crosses `s(a, b)` and `T.dist u v = T.dist u b + T.dist b v`. -/
private theorem dist_eq_add_of_edgeSide {T : SimpleGraph V} (hT : T.IsTree) {a b u v : V}
    (hu : u ∈ edgeSide T a b) (hv : v ∉ edgeSide T a b) :
    T.dist u v = T.dist u b + T.dist b v := by
  classical
  obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist u v
  have he : s(a, b) ∈ p.edges := by
    by_contra hnot
    have hr : (T.deleteEdges {s(a, b)}).Reachable u v :=
      reachable_deleteEdges_iff_exists_walk.mpr ⟨p, hnot⟩
    exact hv (mem_edgeSide.mpr ((mem_edgeSide.mp hu).trans hr))
  have hb : b ∈ p.support := p.fst_mem_support_of_mem_edges (Sym2.eq_swap ▸ he)
  have hlen : (p.takeUntil b hb).length + (p.dropUntil b hb).length = T.dist u v := by
    rw [← Walk.length_append, Walk.take_spec p hb, hp]
  have h1 : T.dist u b ≤ (p.takeUntil b hb).length := T.dist_le _
  have h2 : T.dist b v ≤ (p.dropUntil b hb).length := T.dist_le _
  have htri : T.dist u v ≤ T.dist u b + T.dist b v := hT.connected.dist_triangle
  omega

/-- **Centroid of a finite tree**: a vertex `c` minimizing `∑ x, T.dist c x` satisfies
`2 · |edgeSide T w c| ≤ |V|` for every neighbor `w` of `c`. -/
private theorem exists_tree_centroid {T : SimpleGraph V} (hT : T.IsTree) :
    ∃ c : V, ∀ w : V, T.Adj c w → 2 * (edgeSide T w c).card ≤ Fintype.card V := by
  classical
  have := hT.connected.nonempty
  obtain ⟨c, hc⟩ := Finite.exists_min fun u : V => ∑ x : V, (T.dist u x : ℤ)
  refine ⟨c, fun w hcw => ?_⟩
  let S := edgeSide T w c
  have hpt : ∀ x : V, (T.dist w x : ℤ) - (T.dist c x : ℤ) = if x ∈ S then -1 else 1 := fun x => by
    by_cases hx : x ∈ S
    · simp only [hx, ↓reduceIte]
      have hcx : x ∉ edgeSide T c w := (mem_edgeSide_swap hT hcw x).mp hx
      have hd := dist_eq_add_of_edgeSide hT (mem_edgeSide_self c w) hcx
      have hcw1 : T.dist c w = 1 := dist_eq_one_iff_adj.mpr hcw
      omega
    · simp only [hx, ↓reduceIte]
      have hd := dist_eq_add_of_edgeSide hT (mem_edgeSide_self w c) hx
      have hwc1 : T.dist w c = 1 := dist_eq_one_iff_adj.mpr hcw.symm
      omega
  have hmin : (0 : ℤ) ≤ (∑ x : V, (T.dist w x : ℤ)) - ∑ x : V, (T.dist c x : ℤ) :=
    sub_nonneg.mpr (hc w)
  rw [← sum_sub_distrib] at hmin
  simp only [hpt] at hmin
  have hsum : (∑ x : V, if x ∈ S then (-1 : ℤ) else 1) =
      (Fintype.card V : ℤ) - 2 * (S.card : ℤ) := by
    have heq : ∀ x : V, (if x ∈ S then (-1 : ℤ) else 1) = 1 - if x ∈ S then 2 else 0 := fun x => by
      split_ifs <;> rfl
    simp only [heq, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, ← sum_filter,
      filter_mem_eq_inter, univ_inter]
    ring
  rw [hsum] at hmin
  change 2 * S.card ≤ Fintype.card V
  omega

/-- **Tree equilibria Price of Anarchy ≤ 5** (real-valued, against connected profiles;
[FabrikantLuthraManevaPapadimitriouShenker2003], Theorem 2, locator not re-verified against primary
PDF): every pure Nash equilibrium (`0 ≤ α`) whose formed graph is a tree satisfies
`socialCost α s ≤ 5 * socialCost α s'`. -/
theorem IsPureNash.socialCost_le_five_mul_of_isTree [DecidableEq V] {α : ℝ} (hα₀ : 0 ≤ α)
    {s : Profile V} (hs : IsPureNash α s) (hT : (formedGraph s).IsTree) {s' : Profile V}
    (hc' : (formedGraph s').Connected) :
    socialCost α s ≤ 5 * socialCost α s' := by
  have : Nonempty V := hT.connected.nonempty
  rcases lt_or_ge α 2 with hα2 | hα2
  · have h43 := hs.socialCost_le_four_thirds_mul_of_lt_two hα₀ hα2 hc'
    have hnn := socialCost_nonneg hα₀ s'
    linarith
  · rcases le_or_gt (Fintype.card V) 1 with hn | hn
    · have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hn
      have hsc0 := hs.socialCost_eq_zero_of_subsingleton hα₀
      have hnn := socialCost_nonneg hα₀ s'
      rw [hsc0]
      linarith
    · obtain ⟨c, hc⟩ := exists_tree_centroid hT
      have hn_pos : (0 : ℝ) < (Fintype.card V : ℝ) := by
        exact_mod_cast (by omega : 0 < Fintype.card V)
      have hdist_c : ∀ u : V, u ≠ c →
          ((formedGraph s).dist u c : ℝ) ≤ 1 + 2 * α / (Fintype.card V : ℝ) := by
        intro u huc
        obtain ⟨q, hq_path, _⟩ := hT.connected.exists_path_of_dist c u
        cases q with
        | nil => exact absurd rfl huc.symm
        | @cons _ w _ hcw q' =>
          have hd_mem : (⟨(c, w), hcw⟩ : (formedGraph s).Dart) ∈ (Walk.cons hcw q').darts := by
            simp
          have hside := mem_edgeSide_of_mem_darts hT.isAcyclic hq_path hd_mem
          have hu_side : u ∈ edgeSide (formedGraph s) w c :=
            (mem_edgeSide_swap hT hcw u).mpr hside.2
          let S := edgeSide (formedGraph s) c w
          have hS_card : (Fintype.card V : ℝ) ≤ 2 * (S.card : ℝ) := by
            have hcompl : S = (edgeSide (formedGraph s) w c)ᶜ := edgeSide_swap hT hcw.symm
            have hadd : S.card + (edgeSide (formedGraph s) w c).card = Fintype.card V := by
              rw [hcompl, card_compl_add_card]
            have hcw_le := hc w hcw
            exact_mod_cast (by omega : Fintype.card V ≤ 2 * S.card)
          let s_dev := addLink s u c
          have hadj_uc : (formedGraph s_dev).Adj u c := adj_addLink huc
          have hmono : formedGraph s ≤ formedGraph s_dev := formedGraph_le_addLink s u c
          have hreach_dev : ∀ x, (formedGraph s_dev).Reachable u x :=
            fun x => (hT.connected u x).mono hmono
          have hpt : ∀ x ∈ S,
              (((formedGraph s).dist u c : ℝ) - 1) ≤
                ((formedGraph s).dist u x : ℝ) - ((formedGraph s_dev).dist u x : ℝ) := by
            intro x hx
            have hx_not : x ∉ edgeSide (formedGraph s) w c :=
              (mem_edgeSide_swap hT hcw.symm x).mp hx
            have hux_eq : (formedGraph s).dist u x =
                (formedGraph s).dist u c + (formedGraph s).dist c x :=
              dist_eq_add_of_edgeSide hT hu_side hx_not
            have hcx_le : (formedGraph s_dev).dist c x ≤ (formedGraph s).dist c x := by
              have he := edist_anti hmono (u := c) (v := x)
              rw [← ((hreach_dev c).symm.trans (hreach_dev x)).coe_dist_eq_edist,
                ← (hT.connected c x).coe_dist_eq_edist] at he
              exact_mod_cast he
            have hux'_le : (formedGraph s_dev).dist u x ≤ 1 + (formedGraph s).dist c x := by
              have htri := (hreach_dev c).dist_triangle_left x
              have huc1 : (formedGraph s_dev).dist u c = 1 := dist_eq_one_iff_adj.mpr hadj_uc
              omega
            have hux_eqR : ((formedGraph s).dist u x : ℝ) =
                ((formedGraph s).dist u c : ℝ) + ((formedGraph s).dist c x : ℝ) := by
              exact_mod_cast hux_eq
            have hux'_leR : ((formedGraph s_dev).dist u x : ℝ) ≤
                1 + ((formedGraph s).dist c x : ℝ) := by
              exact_mod_cast hux'_le
            linarith
          have hsum_ge : (S.card : ℝ) * (((formedGraph s).dist u c : ℝ) - 1) ≤
              ∑ x ∈ S, (((formedGraph s).dist u x : ℝ) - ((formedGraph s_dev).dist u x : ℝ)) := by
            calc (S.card : ℝ) * (((formedGraph s).dist u c : ℝ) - 1)
              _ = ∑ _x ∈ S, (((formedGraph s).dist u c : ℝ) - 1) := by
                  rw [sum_const, nsmul_eq_mul]
              _ ≤ ∑ x ∈ S, (((formedGraph s).dist u x : ℝ) - ((formedGraph s_dev).dist u x : ℝ)) :=
                  sum_le_sum hpt
          have hmul : (S.card : ℝ) * (((formedGraph s).dist u c : ℝ) - 1) ≤ α :=
            hsum_ge.trans (sum_dist_sub_addLink_le hα₀ hs u c S)
          rcases le_or_gt (((formedGraph s).dist u c : ℝ) - 1) 0 with hnonpos | hpos
          · have hdiv_nn : 0 ≤ 2 * α / (Fintype.card V : ℝ) := by positivity
            linarith
          · have hn_mul : (Fintype.card V : ℝ) * (((formedGraph s).dist u c : ℝ) - 1) ≤ 2 * α := by
              nlinarith
            have hdiv : ((formedGraph s).dist u c : ℝ) - 1 ≤ 2 * α / (Fintype.card V : ℝ) :=
              (le_div_iff₀ hn_pos).mpr (by linarith)
            linarith
      have hsum_uc : ∑ u : V, ((formedGraph s).dist u c : ℝ) ≤
          ((Fintype.card V - 1 : ℕ) : ℝ) * (1 + 2 * α / (Fintype.card V : ℝ)) :=
        sum_le_card_sub_one_mul (by simp) hdist_c
      have hpair_sum : ∑ u : V, ∑ v : V, ((formedGraph s).dist u v : ℝ) ≤
          2 * ((Fintype.card V - 1 : ℕ) : ℝ) * ∑ u : V, ((formedGraph s).dist u c : ℝ) := by
        have hinner : ∀ u : V, ∑ v : V, ((formedGraph s).dist u v : ℝ) ≤
            ((Fintype.card V - 1 : ℕ) : ℝ) * ((formedGraph s).dist u c : ℝ) +
              ∑ v ∈ univ.erase u, ((formedGraph s).dist v c : ℝ) := fun u => by
          rw [← sum_erase_add _ _ (mem_univ u)]
          simp only [SimpleGraph.dist_self, Nat.cast_zero, add_zero]
          calc ∑ v ∈ univ.erase u, ((formedGraph s).dist u v : ℝ)
            _ ≤ ∑ v ∈ univ.erase u,
                (((formedGraph s).dist u c : ℝ) + ((formedGraph s).dist v c : ℝ)) :=
                sum_le_sum fun v _ => by
                  have htri := hT.connected.dist_triangle (u := u) (v := c) (w := v)
                  rw [dist_comm (u := c) (v := v)] at htri
                  exact_mod_cast htri
            _ = ((Fintype.card V - 1 : ℕ) : ℝ) * ((formedGraph s).dist u c : ℝ) +
                ∑ v ∈ univ.erase u, ((formedGraph s).dist v c : ℝ) := by
                rw [sum_add_distrib, sum_const, card_erase_of_mem (mem_univ u), card_univ,
                  nsmul_eq_mul]
        have h1 := sum_le_sum fun u (_ : u ∈ univ) => hinner u
        rw [sum_add_distrib, ← mul_sum] at h1
        have h2 : (∑ u : V, ∑ v ∈ univ.erase u, ((formedGraph s).dist v c : ℝ)) =
            ((Fintype.card V - 1 : ℕ) : ℝ) * ∑ v : V, ((formedGraph s).dist v c : ℝ) := by
          simp only [sum_erase_eq_sub (mem_univ _), sum_sub_distrib, sum_const, card_univ,
            nsmul_eq_mul]
          rw [Nat.cast_sub hn.le, Nat.cast_one]
          ring
        linarith
      have hm : (formedGraph s).edgeSet.ncard = Fintype.card V - 1 := by
        have hc_edge := hT.card_edgeFinset
        rw [ncard_edgeSet_eq_card_edgeFinset]
        omega
      have hn1_le : ((Fintype.card V - 1 : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by
        exact_mod_cast Nat.sub_le (Fintype.card V) 1
      have hdiv_le : ((Fintype.card V - 1 : ℕ) : ℝ) * (2 * α / (Fintype.card V : ℝ)) ≤
          2 * α := by
        rw [mul_div_assoc', div_le_iff₀ hn_pos]
        nlinarith
      have hstar_le : networkCost α (starGraph c) ≤ socialCost α s' := by
        have hle := isOptimalNetwork_iff_forall_profile.mp (isOptimalNetwork_starGraph hα2 c) s'
        rw [networkECost_eq_ofReal_of_connected hα₀ (connected_starGraph c),
          socialECost_eq_ofReal_of_connected hα₀ hc',
          ENNReal.ofReal_le_ofReal_iff (socialCost_nonneg hα₀ s')] at hle
        exact hle
      rw [networkCost_starGraph] at hstar_le
      rw [hs.socialCost_eq_networkCost hα₀, networkCost_def, hm]
      have hn1_nn : (0 : ℝ) ≤ ((Fintype.card V - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hsum_uc2 : ((Fintype.card V - 1 : ℕ) : ℝ) * ∑ u : V, ((formedGraph s).dist u c : ℝ) ≤
          ((Fintype.card V - 1 : ℕ) : ℝ) * (((Fintype.card V - 1 : ℕ) : ℝ) + 2 * α) :=
        mul_le_mul_of_nonneg_left (by linarith) hn1_nn
      nlinarith

/-- **Tree equilibria Price of Anarchy ≤ 5** (extended, for all strategy profiles `s'`;
[FabrikantLuthraManevaPapadimitriouShenker2003], Theorem 2, locator not re-verified against primary
PDF). -/
theorem IsPureNash.socialECost_le_five_mul_of_isTree [DecidableEq V] {α : ℝ} (hα₀ : 0 ≤ α)
    {s : Profile V} (hs : IsPureNash α s) (hT : (formedGraph s).IsTree) (s' : Profile V) :
    socialECost α s ≤ 5 * socialECost α s' := by
  have : Nonempty V := hT.connected.nonempty
  by_cases hc' : (formedGraph s').Connected
  · rw [socialECost_eq_ofReal_of_connected hα₀ hT.connected,
      socialECost_eq_ofReal_of_connected hα₀ hc']
    have h5 : (5 : ℝ≥0∞) = ENNReal.ofReal 5 := by norm_num
    rw [h5, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (hs.socialCost_le_five_mul_of_isTree hα₀ hT hc')
  · rw [socialECost_eq_top_iff.mpr hc', ENNReal.mul_top (by norm_num)]
    exact le_top

end TreeEquilibria

section DiameterStrengthening

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Diameter-`d` pure Nash equilibrium social-cost bound (`3d - 1`)** ([TardosWexler2007],
Lemma 19.4, p. 491, locator not re-verified against primary PDF): strengthens `[TardosWexler2007]`
Lemma 19.4's `3d` factor to `3d - 1` (for any distance upper bound `d ≥ 1`) via a shortest-path
spanning subgraph built with `SimpleGraph.parentGraph`. -/
theorem IsPureNash.socialCost_le_three_mul_sub_one_of_dist_le {α : ℝ} (hα₀ : 0 ≤ α)
    {s : Profile V} (hs : IsPureNash α s) {d : ℝ} (hd1 : 1 ≤ d)
    (hd : ∀ u v : V, ((formedGraph s).dist u v : ℝ) ≤ d) {s' : Profile V}
    (hc' : (formedGraph s').Connected) :
    socialCost α s ≤ (3 * d - 1) * socialCost α s' := by
  have h3d : 0 ≤ 3 * d - 1 := by linarith
  rcases le_or_gt (Fintype.card V) 1 with hn | hn
  · have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hn
    have hsc0 := hs.socialCost_eq_zero_of_subsingleton hα₀
    have hnn := socialCost_nonneg hα₀ s'
    rw [hsc0]
    exact mul_nonneg h3d hnn
  · have : Nonempty V := hc'.nonempty
    let H := formedGraph s
    have hconn : H.Connected := hs.connected
    have hdist_total : ∑ u : V, ∑ v : V, (H.dist u v : ℝ) ≤
        d * ((Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ)) := by
      have hinner : ∀ u : V, ∑ v : V, (H.dist u v : ℝ) ≤ d * (Fintype.card V - 1 : ℕ) := fun u =>
        calc ∑ v : V, (H.dist u v : ℝ)
          _ ≤ ((Fintype.card V - 1 : ℕ) : ℝ) * d :=
              sum_le_card_sub_one_mul (u := u) (by simp) fun v _ => hd u v
          _ = d * (Fintype.card V - 1 : ℕ) := mul_comm _ _
      calc ∑ u : V, ∑ v : V, (H.dist u v : ℝ)
        _ ≤ ∑ _u : V, d * (Fintype.card V - 1 : ℕ) := sum_le_sum fun u _ => hinner u
        _ = d * ((Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ)) := by
            rw [sum_const, card_univ, nsmul_eq_mul]
            ring
    have hlow_s' : α * (Fintype.card V - 1 : ℕ) +
        (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) ≤ socialCost α s' := by
      have hnet : networkCost α (formedGraph s') ≤ socialCost α s' := by
        have hle := networkECost_formedGraph_le α s'
        rw [networkECost_eq_ofReal_of_connected hα₀ hc',
          socialECost_eq_ofReal_of_connected hα₀ hc',
          ENNReal.ofReal_le_ofReal_iff (socialCost_nonneg hα₀ s')] at hle
        exact hle
      exact (edge_add_dist_le_networkCost_of_connected hα₀ hc').trans hnet
    rcases eq_or_lt_of_le hα₀ with rfl | hα_pos
    · rw [hs.socialCost_eq_networkCost le_rfl, networkCost_def, zero_mul, zero_add]
      have hd_le_3d : d ≤ 3 * d - 1 := by linarith
      have hnn_card : 0 ≤ (Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ) := by positivity
      calc ∑ u : V, ∑ v : V, (H.dist u v : ℝ)
        _ ≤ d * ((Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ)) := hdist_total
        _ ≤ (3 * d - 1) * ((Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ)) :=
            mul_le_mul_of_nonneg_right hd_le_3d hnn_card
        _ ≤ (3 * d - 1) * socialCost 0 s' := by
            rw [zero_mul, zero_add] at hlow_s'
            exact mul_le_mul_of_nonneg_left hlow_s' h3d
    · have hnd : NoDoubleEdges s := hs.noDoubleEdges hα_pos
      have v₀ : V := Classical.arbitrary V
      have hex_par : ∀ w : V, w ≠ v₀ → ∃ p : V, H.Adj p w ∧ H.dist v₀ p + 1 = H.dist v₀ w := by
        intro w hw
        have hpos : 0 < H.dist v₀ w := hconn.pos_dist_of_ne (Ne.symm hw)
        have hed : H.edist v₀ w = ((H.dist v₀ w - 1 : ℕ) : ℕ∞) + 1 := by
          rw [← (hconn v₀ w).coe_dist_eq_edist]
          exact_mod_cast (by omega : H.dist v₀ w = (H.dist v₀ w - 1) + 1)
        obtain ⟨p, hpw, hp_ed⟩ := exists_adj_edist_eq_of_edist_eq_add_one hed
        rw [← (hconn v₀ p).coe_dist_eq_edist] at hp_ed
        have hp_d : H.dist v₀ p = H.dist v₀ w - 1 := Nat.cast_injective hp_ed
        exact ⟨p, hpw, by omega⟩
      let par : V → V := fun w => if hw : w ≠ v₀ then (hex_par w hw).choose else v₀
      let H₀ : SimpleGraph V := parentGraph par
      have hpar0 : par v₀ = v₀ := by simp [par]
      have hpar_adj : ∀ x, par x ≠ x → H.Adj (par x) x := fun x hx => by
        by_cases hx0 : x ≠ v₀
        · simpa [par, hx0] using (hex_par x hx0).choose_spec.1
        · rw [not_not.1 hx0] at hx
          exact absurd hpar0 hx
      have hH₀_le : H₀ ≤ H := by
        intro x y hxy
        rw [parentGraph_adj] at hxy
        rcases hxy.2 with hp | hp
        · rw [← hp]
          exact (hpar_adj x (hp ▸ hxy.1.symm)).symm
        · rw [← hp]
          exact hpar_adj y (hp ▸ hxy.1)
      have hH₀_dist_root : ∀ k : ℕ, ∀ x : V, H.dist v₀ x = k →
          H₀.Reachable v₀ x ∧ H₀.dist v₀ x ≤ k := by
        intro k
        induction k with
        | zero =>
          intro x hx
          have hxv : v₀ = x := hconn.dist_eq_zero_iff.mp hx
          subst x
          exact ⟨Reachable.refl v₀, by simp⟩
        | succ k ih =>
          intro x hx
          have hxv : x ≠ v₀ := fun h => by subst x; simp at hx
          have hspec := (hex_par x hxv).choose_spec
          have hpar_eq : par x = (hex_par x hxv).choose := by simp [par, hxv]
          obtain ⟨hr_p, hd_p⟩ := ih (par x) (by rw [hpar_eq]; omega)
          have hadj₀ : H₀.Adj (par x) x := by
            rw [parentGraph_adj]
            exact ⟨by rw [hpar_eq]; exact hspec.1.ne, Or.inr rfl⟩
          refine ⟨hr_p.trans hadj₀.reachable, ?_⟩
          have htri := hr_p.dist_triangle_left x
          have h1 : H₀.dist (par x) x = 1 := dist_eq_one_iff_adj.mpr hadj₀
          omega
      have hH₀_conn : H₀.Connected :=
        ⟨fun x y => (hH₀_dist_root _ x rfl).1.symm.trans (hH₀_dist_root _ y rfl).1⟩
      have hH₀_diam : ∀ x y : V, (H₀.dist x y : ℝ) ≤ 2 * d := fun x y => by
        have htri := hH₀_conn.dist_triangle (u := x) (v := v₀) (w := y)
        rw [dist_comm (u := x) (v := v₀)] at htri
        have hx_le : (H₀.dist v₀ x : ℝ) ≤ d :=
          (Nat.cast_le.mpr (hH₀_dist_root _ x rfl).2).trans (hd v₀ x)
        have hy_le : (H₀.dist v₀ y : ℝ) ≤ d :=
          (Nat.cast_le.mpr (hH₀_dist_root _ y rfl).2).trans (hd v₀ y)
        have htriR : (H₀.dist x y : ℝ) ≤ (H₀.dist v₀ x : ℝ) + (H₀.dist v₀ y : ℝ) := by
          exact_mod_cast htri
        linarith
      classical
      have hH₀_edges : H₀.edgeFinset.card ≤ Fintype.card V - 1 := by
        have hsub : H₀.edgeFinset ⊆ (univ.erase v₀).image fun x => s(x, par x) := by
          intro e he
          induction e using Sym2.ind with
          | h x y =>
            rw [mem_edgeFinset, mem_edgeSet, parentGraph_adj] at he
            rw [mem_image]
            rcases he.2 with hp | hp
            · have hx : x ≠ v₀ := fun h => he.1 <| by
                rw [h] at hp ⊢
                exact hpar0.symm.trans hp
              exact ⟨x, mem_erase.mpr ⟨hx, mem_univ x⟩, by rw [hp]⟩
            · have hy : y ≠ v₀ := fun h => he.1 <| by
                rw [h] at hp ⊢
                exact hp.symm.trans hpar0
              exact ⟨y, mem_erase.mpr ⟨hy, mem_univ y⟩, by rw [hp, Sym2.eq_swap]⟩
        calc H₀.edgeFinset.card
          _ ≤ ((univ.erase v₀).image fun x => s(x, par x)).card := card_le_card hsub
          _ ≤ (univ.erase v₀).card := card_image_le
          _ = Fintype.card V - 1 := by rw [card_erase_of_mem (mem_univ v₀), card_univ]
      let keep : ∀ u : V, LinkSet V u := fun u =>
        LinkSet.ofFinset u ((s u).neighbors.filter fun w => H₀.Adj u w)
      have hdev_bound : ∀ u : V,
          α * (((s u).neighbors.card : ℝ) - ((keep u).neighbors.card : ℝ)) ≤
            (2 * d - 1) * (Fintype.card V - 1 : ℕ) := by
        intro u
        let s_dev := Function.update s u (keep u)
        have hle_dev : H₀ ≤ formedGraph s_dev := by
          intro a b hab
          have habH : H.Adj a b := hH₀_le hab
          have hab_ne : a ≠ b := habH.ne
          rw [formedGraph_adj] at habH ⊢
          rcases habH with hb | ha
          · left
            by_cases hau : a = u
            · subst hau
              simp only [s_dev, Function.update_self, keep, LinkSet.mem_ofFinset, mem_filter]
              exact ⟨hab_ne.symm, hb, hab⟩
            · simp only [s_dev, Function.update_of_ne hau]
              exact hb
          · right
            by_cases hbu : b = u
            · subst hbu
              simp only [s_dev, Function.update_self, keep, LinkSet.mem_ofFinset, mem_filter]
              exact ⟨hab_ne, ha, hab.symm⟩
            · simp only [s_dev, Function.update_of_ne hbu]
              exact ha
        have hconn_dev : (formedGraph s_dev).Connected := hH₀_conn.mono hle_dev
        have hne_u := hs.playerCost_le hα₀ fun x => hconn_dev u x
        rw [playerCost_def, playerCost_def, Function.update_self] at hne_u
        have hdist_diff : ∑ x : V, (((formedGraph s_dev).dist u x : ℝ) - (H.dist u x : ℝ)) ≤
            (2 * d - 1) * (Fintype.card V - 1 : ℕ) :=
          calc ∑ x : V, (((formedGraph s_dev).dist u x : ℝ) - (H.dist u x : ℝ))
            _ ≤ ((Fintype.card V - 1 : ℕ) : ℝ) * (2 * d - 1) :=
                sum_le_card_sub_one_mul (u := u) (by simp)
                  fun x hx => by
                    have h1 : (1 : ℝ) ≤ (H.dist u x : ℝ) := by
                      exact_mod_cast hconn.pos_dist_of_ne hx.symm
                    have h2 : ((formedGraph s_dev).dist u x : ℝ) ≤ 2 * d := by
                      have he := edist_anti hle_dev (u := u) (v := x)
                      rw [← (hconn_dev u x).coe_dist_eq_edist, ← (hH₀_conn u x).coe_dist_eq_edist]
                        at he
                      have hle0 : ((formedGraph s_dev).dist u x : ℝ) ≤ (H₀.dist u x : ℝ) := by
                        exact_mod_cast he
                      exact hle0.trans (hH₀_diam u x)
                    linarith
            _ = (2 * d - 1) * (Fintype.card V - 1 : ℕ) := mul_comm _ _
        rw [sum_sub_distrib] at hdist_diff
        dsimp only [s_dev, H] at hdist_diff
        linarith
      have hsum_keep : ∑ u : V, (keep u).neighbors.card ≤ Fintype.card V - 1 := by
        rw [← card_sigma (s := univ)]
        refine (card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_).trans hH₀_edges
        · rintro ⟨u, w⟩ hp
          rw [mem_coe, mem_sigma] at hp
          have hmem : w ∈ (keep u).neighbors := hp.2
          rw [LinkSet.neighbors_ofFinset, mem_erase, mem_filter] at hmem
          exact mem_edgeFinset.mpr hmem.2.2
        · rintro ⟨u₁, w₁⟩ hp₁ ⟨u₂, w₂⟩ hp₂ heq
          rw [mem_coe, mem_sigma] at hp₁ hp₂
          have h1 : w₁ ∈ (keep u₁).neighbors := hp₁.2
          have h2 : w₂ ∈ (keep u₂).neighbors := hp₂.2
          rw [LinkSet.neighbors_ofFinset, mem_erase, mem_filter] at h1 h2
          rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact absurd h2.2.1 (hnd h1.2.1)
      have hsum_dev := sum_le_sum fun u (_ : u ∈ univ) => hdev_bound u
      simp only [← mul_sum, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] at hsum_dev
      have hkeepR : ∑ u : V, ((keep u).neighbors.card : ℝ) ≤ (Fintype.card V - 1 : ℕ) := by
        exact_mod_cast hsum_keep
      have hsum_dev' : α * ∑ u : V, ((s u).neighbors.card : ℝ) ≤
          α * (Fintype.card V - 1 : ℕ) +
            (2 * d - 1) * ((Fintype.card V : ℝ) * (Fintype.card V - 1 : ℕ)) := by
        nlinarith
      have halpha_term : α * ((Fintype.card V - 1 : ℕ) : ℝ) ≤
          (3 * d - 1) * (α * ((Fintype.card V - 1 : ℕ) : ℝ)) := by
        have hprod_nn : 0 ≤ α * ((Fintype.card V - 1 : ℕ) : ℝ) := by positivity
        nlinarith
      have hmul_low := mul_le_mul_of_nonneg_left hlow_s' h3d
      rw [socialCost_def]
      simp_rw [playerCost_def, sum_add_distrib, ← mul_sum]
      dsimp only [H] at hdist_total
      nlinarith

/-- **Tightened Lemma 19.4 (real-valued, diameter `d ≥ 1`)** ([TardosWexler2007], Lemma 19.4,
p. 491, locator not re-verified against primary PDF): strengthens `[TardosWexler2007]` Lemma 19.4's
`3d` factor to `3d - 1` whenever `V` is nontrivial (so `(formedGraph s).diam ≥ 1`). -/
theorem IsPureNash.socialCost_le_three_diam_sub_one_mul [Nontrivial V] {α : ℝ} (hα₀ : 0 ≤ α)
    {s : Profile V} (hs : IsPureNash α s) {s' : Profile V} (hc' : (formedGraph s').Connected) :
    socialCost α s ≤ (3 * ((formedGraph s).diam : ℝ) - 1) * socialCost α s' := by
  have hed : (formedGraph s).ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hs.connected
  have hd1 : (1 : ℝ) ≤ ((formedGraph s).diam : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (diam_ne_zero_of_ediam_ne_top hed)
  exact hs.socialCost_le_three_mul_sub_one_of_dist_le hα₀ hd1
    (fun u v => by exact_mod_cast dist_le_diam hed (u := u) (v := v)) hc'

/-- **Tightened Lemma 19.4 (extended, diameter `d ≥ 1`)** ([TardosWexler2007], Lemma 19.4, p. 491,
locator not re-verified against primary PDF): strengthens `3d` to `3d - 1` whenever `V` is
nontrivial. -/
theorem IsPureNash.socialECost_le_three_diam_sub_one_mul [Nontrivial V] {α : ℝ} (hα₀ : 0 ≤ α)
    {s : Profile V} (hs : IsPureNash α s) (s' : Profile V) :
    socialECost α s ≤
      ENNReal.ofReal (3 * ((formedGraph s).diam : ℝ) - 1) * socialECost α s' := by
  have hed : (formedGraph s).ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hs.connected
  have hd1 : (1 : ℝ) ≤ ((formedGraph s).diam : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (diam_ne_zero_of_ediam_ne_top hed)
  have hpos : 0 < 3 * ((formedGraph s).diam : ℝ) - 1 := by linarith
  by_cases hc' : (formedGraph s').Connected
  · rw [socialECost_eq_ofReal_of_connected hα₀ hs.connected,
      socialECost_eq_ofReal_of_connected hα₀ hc', ← ENNReal.ofReal_mul hpos.le]
    exact ENNReal.ofReal_le_ofReal (hs.socialCost_le_three_diam_sub_one_mul hα₀ hc')
  · rw [socialECost_eq_top_iff.mpr hc', ENNReal.mul_top (by positivity)]
    exact le_top

/-- **Sharp `O(√α)` Price of Anarchy `(3√(4α + 1) - 1)`**
([FabrikantLuthraManevaPapadimitriouShenker2003]; [TardosWexler2007], Theorem 19.5, p. 492,
locator not re-verified against primary PDF): combines `LocalConnection`'s sharp diameter bound
`d ≤ √(4α + 1)` with the `3d - 1` Lemma 19.4 tightening. This explicitly incorporates the
odd-diameter `+ 1` parity term (`d = 2k + 1` satisfies `k(k + 1) ≤ α`, i.e., `d ≤ √(4α + 1)`)
omitted when `[TardosWexler2007]` Theorem 19.5 writes `6√α`. -/
theorem IsPureNash.socialECost_le_three_mul_sqrt_four_add_one_sub_one_mul {α : ℝ} (hα₀ : 0 ≤ α)
    {s : Profile V} (hs : IsPureNash α s) (s' : Profile V) :
    socialECost α s ≤ ENNReal.ofReal (3 * Real.sqrt (4 * α + 1) - 1) * socialECost α s' := by
  have hsq1 : 1 ≤ Real.sqrt (4 * α + 1) :=
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (4 * α + 1) := Real.sqrt_le_sqrt (by linarith)
  have hpos : 0 < 3 * Real.sqrt (4 * α + 1) - 1 := by linarith
  rcases isEmpty_or_nonempty V with hE | hNE
  · have := hE
    simp only [socialECost_def, univ_eq_empty, sum_empty, zero_le]
  · have : Nonempty V := hNE
    by_cases hc' : (formedGraph s').Connected
    · have hed : (formedGraph s).ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hs.connected
      have hdist : ∀ u v : V, ((formedGraph s).dist u v : ℝ) ≤ Real.sqrt (4 * α + 1) :=
        fun u v =>
          (Nat.cast_le.mpr (dist_le_diam hed (u := u) (v := v))).trans
            (hs.diam_le_sqrt_four_mul_add_one hα₀)
      rw [socialECost_eq_ofReal_of_connected hα₀ hs.connected,
        socialECost_eq_ofReal_of_connected hα₀ hc', ← ENNReal.ofReal_mul hpos.le]
      exact ENNReal.ofReal_le_ofReal
        (hs.socialCost_le_three_mul_sub_one_of_dist_le hα₀ hsq1 hdist hc')
    · rw [socialECost_eq_top_iff.mpr hc', ENNReal.mul_top (by positivity)]
      exact le_top

/-- **`O(√α)` Price of Anarchy `(6√α + 2)`**
([FabrikantLuthraManevaPapadimitriouShenker2003]; [TardosWexler2007], Theorem 19.5, p. 492,
locator not re-verified against primary PDF): tightens
`IsPureNash.socialECost_le_six_mul_sqrt_add_three_mul` from `6√α + 3` to `6√α + 2` via
`√(4α + 1) ≤ 2√α + 1` and the `3d - 1` bound. The additive `+ 2` constant reflects the
odd-diameter `+ 1` parity term (`d ≤ 2√α + 1`, witnessed on `P₄` at `α = 2` with `d = 3 > 2√2`)
omitted in `[TardosWexler2007]`'s informal `6√α` statement. -/
theorem IsPureNash.socialECost_le_six_mul_sqrt_add_two_mul {α : ℝ} (hα₀ : 0 ≤ α)
    {s : Profile V} (hs : IsPureNash α s) (s' : Profile V) :
    socialECost α s ≤ ENNReal.ofReal (6 * Real.sqrt α + 2) * socialECost α s' := by
  have hle : ENNReal.ofReal (3 * Real.sqrt (4 * α + 1) - 1) ≤
      ENNReal.ofReal (6 * Real.sqrt α + 2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hsq : Real.sqrt (4 * α + 1) ≤ 2 * Real.sqrt α + 1 := by
      calc Real.sqrt (4 * α + 1)
        _ ≤ Real.sqrt ((2 * Real.sqrt α + 1) ^ 2) := by
            refine Real.sqrt_le_sqrt ?_
            have h1 : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα₀
            have h2 : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
            nlinarith
        _ = 2 * Real.sqrt α + 1 := Real.sqrt_sq (by positivity)
    linarith
  calc socialECost α s
    _ ≤ ENNReal.ofReal (3 * Real.sqrt (4 * α + 1) - 1) * socialECost α s' :=
        hs.socialECost_le_three_mul_sqrt_four_add_one_sub_one_mul hα₀ s'
    _ ≤ ENNReal.ofReal (6 * Real.sqrt α + 2) * socialECost α s' := by gcongr

end DiameterStrengthening

end Cslib.GameTheory.LocalConnection
