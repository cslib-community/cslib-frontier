/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Functions
public import CslibFrontier.GameTheory.Cooperative.MoulinCostSharing
public import CslibFrontier.GameTheory.Cooperative.ShapleyValue
public import Mathlib.NumberTheory.Harmonic.Defs
import CslibFrontier.Foundations.Data.Nat.Radix.Unique
import CslibFrontier.Foundations.NumberTheory.Harmonic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multicast Cost Sharing: Shapley (`SH`) vs. Marginal Cost (`MC`), Welfare Loss, and Communication

In the **multicast cost-sharing problem** ([MoulinShenker2001];
[FeigenbaumPapadimitriouShenker2001]; [FeigenbaumSchapiraShenker2007]), a source at the root of a
tree `T` with nonnegative link costs transmits to a
selected coalition `R` of strategic receivers located at nodes of `T`. Serving `R` incurs total
routing cost `cost R` equal to the sum of link costs along the union of root-to-receiver paths.

Two canonical incentive-compatible mechanisms arise from opposing economic priorities:

1. **Shapley (`SH`) multicast cost sharing** ([MoulinShenker2001];
   [FeigenbaumPapadimitriouShenker2001]; [JainMahdian2007], Section 15.6.1 and Exercise 15.2):
   - Multicast tree cost `MulticastInstance.toCostSharingGame` is monotone, nonnegative, and
     submodular (`toCostSharingGame_isSubmodular`).
   - On every serviced coalition `R`, the coalition-restricted Shapley share
     `toCostSharingGame.shapleyScheme.share R i` equals the closed-form equal per-link split
     `shShare`: each active link's cost is divided equally among the serviced receivers downstream
     of that link (`shapleyScheme_share_eq_shShare`).
   - The resulting Moulin mechanism `shMechanism` is **group-strategyproof**
     (`shMechanism_isGroupStrategyproof`), `1`-budget-balanced (`shMechanism_isBudgetBalanced`),
     and satisfies No Positive Transfers, Voluntary Participation, and Consumer Sovereignty.
2. **Marginal Cost (`MC` / Clarke VCG) multicast mechanism and the `2`-pass distributed algorithm**
   ([FeigenbaumPapadimitriouShenker2001]; [FeigenbaumSchapiraShenker2007]):
   - Because `toCostSharingGame` is submodular, net social welfare `netWelfare` is supermodular
     (`netWelfare_supermodular`), so the family of welfare-maximizing receiver coalitions has a
     **unique largest element `mcReceivers`** (`isGreatest_isWelfareMaximizingSet_mcReceivers`).
   - The Clarke VCG mechanism `mcMechanism` serving `mcReceivers` is DSIC across all real bid
     profiles (`mcMechanism_utility_le_truthful`, `mcMechanism_isDSIC`), satisfies Voluntary
     Participation and No Positive Transfers, maximizes net social welfare, and never runs a budget
     surplus (`mcMechanism_payment_sum_le_cost`), **but fails group-strategyproofness** even on a
     single shared link with two receivers (`not_mcMechanism_isGroupStrategyproof_singleLink`).
   - **Distributed `2`-pass tree algorithm (`twoPassReceivers`, `twoPassPayment`)**: a single
     bottom-up pass (`1` real surplus message per link) followed by a single top-down pass (`1`
     `(Bool, Option ℝ)` message per link, `2 * (|V| - 1)` messages total across the `|V| - 1` tree
     links) computes both `mcReceivers` (`twoPassReceivers_eq_mcReceivers`) and the exact VCG
     payments (`twoPassPayment_eq_mcMechanism_payment`) on all nonnegative bid profiles.
3. **Efficiency vs. budget balance and Moulin–Shenker `(H_n - 1) C` minimax welfare loss**
   ([MoulinShenker2001]):
   - On a single excludable link of positive cost `C > 0` with `|A| ≥ 2` receivers
     (`singleLinkMulticast`), **no mechanism can simultaneously satisfy `IsDSIC`, Voluntary
     Participation, No Positive Transfers, `1`-budget balance, and net-welfare maximization**
     (`not_exists_dsic_budgetBalanced_welfareMaximizing_singleLink`).
   - Under `shMechanism` on `singleLinkMulticast`, worst-case additive welfare loss on nonnegative
     profiles is **at most `(H_n - 1) C`** (`netWelfare_sub_shMechanism_le_harmonic_sub_one`), and
     for **every** `1`-budget-balanced cross-monotonic scheme `ξ`, its Moulin mechanism suffers
     welfare loss arbitrarily close to `(H_n - 1) C` (`exists_welfareLoss_gt_harmonic_sub_one`),
     establishing minimax optimality of the Shapley scheme.
4. **Cut communication lower bound for `SH`** ([FeigenbaumPapadimitriouShenker2001]):
   - On the `(k + 2)`-node path multicast instance `pathMulticast k` with fixed link costs, any
     deterministic two-party protocol across the bottom cut link deciding whether the bottom
     receiver is served by `shMechanism` requires **at least `k + 1` bits**
     (`le_ecomplexityFun_pathMulticast_shServiced`), contrasting with `MC`'s `2` messages per link.
     (The randomized bounded-error lower bound of [FeigenbaumPapadimitriouShenker2001] is not
     formalized here.)

## Main definitions

* `Cslib.GameTheory.RootedTree`: finite rooted tree `(root, parent)` with `depth`, `IsAncestor`,
  `subtreeNodes`, and `children`.
* `Cslib.GameTheory.orGame`: excludable-resource OR cost-sharing game `c(S) = w` if `(S ∩ U) ≠ ∅`.
* `Cslib.GameTheory.MulticastInstance`: rooted tree with nonnegative link costs `edgeCost` and
  receiver node placements `loc`, inducing `toCostSharingGame`.
* `Cslib.GameTheory.MulticastInstance.shShare`, `Cslib.GameTheory.MulticastInstance.shScheme`,
  `Cslib.GameTheory.MulticastInstance.shMechanism`: closed-form per-link Shapley shares and Moulin
  multicast mechanism (`SH`).
* `Cslib.GameTheory.MulticastInstance.netWelfare`,
  `Cslib.GameTheory.MulticastInstance.IsWelfareMaximizingSet`,
  `Cslib.GameTheory.MulticastInstance.mcReceivers`,
  `Cslib.GameTheory.MulticastInstance.mcMechanism`: net social welfare, unique largest
  welfare-maximizing receiver set, and Clarke VCG Marginal Cost mechanism (`MC`).
* `Cslib.GameTheory.MulticastInstance.nodeWelfare`,
  `Cslib.GameTheory.MulticastInstance.subtreeSurplus`,
  `Cslib.GameTheory.MulticastInstance.upMsg`,
  `Cslib.GameTheory.MulticastInstance.topDownActive`,
  `Cslib.GameTheory.MulticastInstance.topDownThreshold`,
  `Cslib.GameTheory.MulticastInstance.twoPassReceivers`,
  `Cslib.GameTheory.MulticastInstance.twoPassPayment`: distributed `2`-pass tree algorithm for `MC`.
* `Cslib.GameTheory.singleLinkMulticast`, `Cslib.GameTheory.pathMulticast`: canonical single-link
  excludable public good and `(k + 2)`-node path multicast instances.

## Main results

* `Cslib.GameTheory.shapleyValue_orGame`,
  `Cslib.GameTheory.MulticastInstance.toCostSharingGame_isSubmodular`,
  `Cslib.GameTheory.MulticastInstance.shapleyScheme_share_eq_shShare`,
  `Cslib.GameTheory.MulticastInstance.shMechanism_isGroupStrategyproof`: submodularity of multicast
  cost, exact per-link formula for the Shapley scheme, and group-strategyproofness of `SH`.
* `Cslib.GameTheory.MulticastInstance.netWelfare_supermodular`,
  `Cslib.GameTheory.MulticastInstance.isGreatest_isWelfareMaximizingSet_mcReceivers`:
  supermodularity of net welfare and unique largest welfare-maximizing receiver set.
* `Cslib.GameTheory.MulticastInstance.mcMechanism_isDSIC`,
  `Cslib.GameTheory.MulticastInstance.mcMechanism_payment_sum_le_cost`,
  `Cslib.GameTheory.not_mcMechanism_isGroupStrategyproof_singleLink`: truthfulness, non-surplus
  budget bound, and group-strategyproofness failure of `MC`.
* `Cslib.GameTheory.MulticastInstance.nodeWelfare_root_eq_maxNetWelfare`,
  `Cslib.GameTheory.MulticastInstance.twoPassReceivers_eq_mcReceivers`,
  `Cslib.GameTheory.MulticastInstance.twoPassPayment_eq_mcMechanism_payment`: correctness of the
  `2`-pass distributed tree algorithm for `MC`.
* `Cslib.GameTheory.not_exists_dsic_budgetBalanced_welfareMaximizing_singleLink`,
  `Cslib.GameTheory.netWelfare_sub_shMechanism_le_harmonic_sub_one`,
  `Cslib.GameTheory.exists_welfareLoss_gt_harmonic_sub_one`: impossibility of DSIC + exact budget
  balance + efficiency, and Moulin–Shenker `(H_n - 1) C` minimax welfare-loss bound.
* `Cslib.GameTheory.le_ecomplexityFun_pathMulticast_shServiced`: `(k + 1)`-bit deterministic cut
  communication lower bound for `SH` on `(k + 2)`-node path trees.

## References

* [H. Moulin, S. Shenker, *Strategyproof Sharing of Submodular Costs: Budget Balance versus
  Efficiency*][MoulinShenker2001]
* [J. Feigenbaum, C. H. Papadimitriou, S. Shenker, *Sharing the Cost of Multicast
  Transmissions*][FeigenbaumPapadimitriouShenker2001]
* [K. Jain, M. Mahdian, *Cost Sharing*][JainMahdian2007]
* [J. Feigenbaum, M. Schapira, S. Shenker, *Distributed Algorithmic Mechanism
  Design*][FeigenbaumSchapiraShenker2007]
-/

public section

namespace Cslib.GameTheory

open Finset

/-! ## 1. Rooted multicast trees -/

/-- A rooted tree on vertex type `V`, represented by a distinguished `root` and `parent` pointer
map with `parent root = root` such that iterating `parent` from every vertex reaches `root`. -/
structure RootedTree (V : Type*) where
  /-- The source / root vertex of the multicast tree. -/
  root : V
  /-- Parent pointer (`parent root = root`). -/
  parent : V → V
  /-- The root is a fixed point of `parent`. -/
  parent_root : parent root = root
  /-- Every vertex reaches `root` in finitely many `parent` steps. -/
  reaches_root : ∀ v, ∃ k, parent^[k] v = root

namespace RootedTree

/-- `u` is an **ancestor** of `w` in `T` (reflexively: `u` lies on the path from `w` to `root`). -/
@[expose] def IsAncestor {V : Type*} (T : RootedTree V) (u w : V) : Prop :=
  ∃ k, T.parent^[k] w = u

theorem isAncestor_refl {V : Type*} (T : RootedTree V) (u : V) : T.IsAncestor u u :=
  ⟨0, rfl⟩

theorem isAncestor_root {V : Type*} (T : RootedTree V) (w : V) : T.IsAncestor T.root w :=
  T.reaches_root w

theorem IsAncestor.trans {V : Type*} {T : RootedTree V} {u v w : V}
    (huv : T.IsAncestor u v) (hvw : T.IsAncestor v w) : T.IsAncestor u w := by
  obtain ⟨k₁, rfl⟩ := huv
  obtain ⟨k₂, rfl⟩ := hvw
  exact ⟨k₁ + k₂, Function.iterate_add_apply T.parent k₁ k₂ w⟩

theorem isAncestor_parent_self {V : Type*} (T : RootedTree V) (w : V) :
    T.IsAncestor (T.parent w) w :=
  ⟨1, rfl⟩

section Decidable

variable {V : Type*} [DecidableEq V] (T : RootedTree V)

/-- Distance (number of links) from `v` up to `T.root`. -/
def depth (v : V) : ℕ :=
  Nat.find (T.reaches_root v)

theorem parent_iter_depth (v : V) : T.parent^[T.depth v] v = T.root :=
  Nat.find_spec (T.reaches_root v)

@[simp]
theorem depth_eq_zero_iff {v : V} : T.depth v = 0 ↔ v = T.root :=
  Nat.find_eq_zero (T.reaches_root v)

@[simp]
theorem depth_root : T.depth T.root = 0 :=
  T.depth_eq_zero_iff.mpr rfl

theorem depth_parent (v : V) : T.depth (T.parent v) = T.depth v - 1 := by
  by_cases hv : v = T.root
  · simp [hv, T.parent_root]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (mt T.depth_eq_zero_iff.mp hv)
    have hle : T.depth (T.parent v) ≤ m := Nat.find_min' _ <| by
      have h := T.parent_iter_depth v
      rwa [hm, Function.iterate_succ_apply] at h
    have hge : T.depth v ≤ T.depth (T.parent v) + 1 := Nat.find_min' _ <| by
      rw [Function.iterate_succ_apply]
      exact T.parent_iter_depth (T.parent v)
    omega

theorem depth_parent_lt {v : V} (hv : v ≠ T.root) : T.depth (T.parent v) < T.depth v := by
  have := mt T.depth_eq_zero_iff.mp hv
  rw [T.depth_parent]; omega

theorem depth_iterate_parent (k : ℕ) (v : V) :
    T.depth (T.parent^[k] v) = T.depth v - k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', T.depth_parent, ih]; omega

theorem isAncestor_iff_iterate {u w : V} :
    T.IsAncestor u w ↔ T.parent^[T.depth w - T.depth u] w = u ∧ T.depth u ≤ T.depth w := by
  constructor
  · rintro ⟨k, rfl⟩
    by_cases hroot : T.parent^[k] w = T.root
    · rw [hroot, T.depth_root, Nat.sub_zero]
      exact ⟨T.parent_iter_depth w, Nat.zero_le _⟩
    · have hpos := Nat.pos_of_ne_zero (mt T.depth_eq_zero_iff.mp hroot)
      rw [T.depth_iterate_parent] at hpos ⊢
      exact ⟨by rw [show T.depth w - (T.depth w - k) = k by omega], by omega⟩
  · exact fun ⟨hiter, _⟩ => ⟨T.depth w - T.depth u, hiter⟩

instance instDecidableRelIsAncestor : DecidableRel T.IsAncestor :=
  fun _ _ => decidable_of_iff' _ T.isAncestor_iff_iterate

theorem IsAncestor.depth_le {T : RootedTree V} {u w : V} (h : T.IsAncestor u w) :
    T.depth u ≤ T.depth w :=
  (T.isAncestor_iff_iterate.mp h).2

omit [DecidableEq V] in
theorem IsAncestor.antisymm {T : RootedTree V} {u w : V}
    (huw : T.IsAncestor u w) (hwu : T.IsAncestor w u) : u = w := by
  classical
  obtain ⟨hiter, _⟩ := T.isAncestor_iff_iterate.mp huw
  have := hwu.depth_le
  simpa [show T.depth w - T.depth u = 0 by omega] using hiter.symm

/-- Two ancestors of the same vertex `w` are comparable by depth along the unique root path. -/
theorem IsAncestor.of_ancestors_of_depth_le {T : RootedTree V} {u₁ u₂ w : V}
    (h₁ : T.IsAncestor u₁ w) (h₂ : T.IsAncestor u₂ w) (hd : T.depth u₁ ≤ T.depth u₂) :
    T.IsAncestor u₁ u₂ := by
  obtain ⟨hit₁, _⟩ := T.isAncestor_iff_iterate.mp h₁
  obtain ⟨hit₂, hd₂⟩ := T.isAncestor_iff_iterate.mp h₂
  refine ⟨T.depth u₂ - T.depth u₁, ?_⟩
  calc
    T.parent^[T.depth u₂ - T.depth u₁] u₂
      = T.parent^[T.depth u₂ - T.depth u₁] (T.parent^[T.depth w - T.depth u₂] w) :=
        congrArg _ hit₂.symm
    _ = T.parent^[T.depth w - T.depth u₁] w := by
        rw [← Function.iterate_add_apply]
        exact congrArg (fun k => T.parent^[k] w) (by omega)
    _ = u₁ := hit₁

omit [DecidableEq V] in
theorem IsAncestor.eq_or_isAncestor_parent {T : RootedTree V} {u w : V}
    (huw : T.IsAncestor u w) : w = u ∨ (w ≠ T.root ∧ T.IsAncestor u (T.parent w)) := by
  obtain ⟨k, rfl⟩ := huw
  cases k with
  | zero => exact Or.inl rfl
  | succ m =>
    by_cases hw : w = T.root
    · exact Or.inl (by rw [hw, Function.iterate_fixed T.parent_root])
    · exact Or.inr ⟨hw, m, (Function.iterate_succ_apply T.parent m w).symm⟩

section Finite

variable [Fintype V]

/-- Direct children `{c ≠ root | parent c = u}` of vertex `u`. -/
def children (u : V) : Finset V :=
  Finset.univ.filter fun c => c ≠ T.root ∧ T.parent c = u

@[simp]
theorem mem_children {u c : V} :
    c ∈ T.children u ↔ c ≠ T.root ∧ T.parent c = u :=
  Finset.mem_filter.trans (and_iff_right (Finset.mem_univ c))

theorem depth_of_mem_children {u c : V} (hc : c ∈ T.children u) :
    T.depth c = T.depth u + 1 := by
  obtain ⟨hne, rfl⟩ := (T.mem_children).mp hc
  have hpos : 0 < T.depth c := Nat.pos_of_ne_zero (mt T.depth_eq_zero_iff.mp hne)
  have hdp := T.depth_parent c
  omega

/-- Subtree of descendants `{w | IsAncestor u w}` rooted at `u`. -/
def subtreeNodes (u : V) : Finset V :=
  Finset.univ.filter (T.IsAncestor u)

@[simp]
theorem mem_subtreeNodes {u w : V} : w ∈ T.subtreeNodes u ↔ T.IsAncestor u w :=
  Finset.mem_filter.trans (and_iff_right (Finset.mem_univ w))

@[simp]
theorem subtreeNodes_root : T.subtreeNodes T.root = Finset.univ := by
  ext w
  simp [T.isAncestor_root w]

theorem notMem_biUnion_children_subtreeNodes (u : V) :
    u ∉ (T.children u).biUnion T.subtreeNodes := by
  simp only [Finset.mem_biUnion, mem_subtreeNodes]
  rintro ⟨c, hc, hcu⟩
  have hdc := T.depth_of_mem_children hc
  have hle := hcu.depth_le
  omega

theorem pairwiseDisjoint_children_subtreeNodes (u : V) :
    (T.children u : Set V).PairwiseDisjoint T.subtreeNodes := by
  intro c₁ hc₁ c₂ hc₂ hne
  refine Finset.disjoint_left.mpr fun w hw₁ hw₂ => hne ?_
  rw [mem_subtreeNodes] at hw₁ hw₂
  have hd₁ := T.depth_of_mem_children hc₁
  have hd₂ := T.depth_of_mem_children hc₂
  have h12 := hw₁.of_ancestors_of_depth_le hw₂ (by omega)
  have h21 := hw₂.of_ancestors_of_depth_le hw₁ (by omega)
  exact h12.antisymm h21

/-- Rooted-subtree decomposition: `subtreeNodes u` is the disjoint union of `{u}` and the subtrees
of `u`'s children. -/
theorem subtreeNodes_eq_insert_biUnion (u : V) :
    T.subtreeNodes u = insert u ((T.children u).biUnion T.subtreeNodes) := by
  ext w
  simp only [mem_subtreeNodes, Finset.mem_insert, Finset.mem_biUnion, mem_children]
  constructor
  · intro huw
    by_cases hwu : w = u
    · exact Or.inl hwu
    · obtain ⟨hit, hle⟩ := T.isAncestor_iff_iterate.mp huw
      have hlt : T.depth u < T.depth w := lt_of_le_of_ne hle fun h => hwu (by simpa [h] using hit)
      let k := T.depth w - (T.depth u + 1)
      have hdc : T.depth (T.parent^[k] w) = T.depth u + 1 := by rw [T.depth_iterate_parent]; omega
      refine Or.inr ⟨T.parent^[k] w, ⟨fun hr => by rw [hr, T.depth_root] at hdc; omega, ?_⟩, k, rfl⟩
      rwa [show T.depth w - T.depth u = k + 1 by omega, Function.iterate_succ_apply'] at hit
  · rintro (rfl | ⟨c, ⟨_, rfl⟩, hcw⟩)
    · exact T.isAncestor_refl w
    · exact (T.isAncestor_parent_self c).trans hcw

/-- Maximum depth across `V`, used for well-founded bottom-up recursion on `T`. -/
def maxDepth : ℕ :=
  Finset.univ.sup T.depth

theorem depth_le_maxDepth (v : V) : T.depth v ≤ T.maxDepth :=
  Finset.le_sup (f := T.depth) (Finset.mem_univ v)

end Finite

end Decidable

end RootedTree

/-! ## 2. Excludable-link OR game, multicast cost sharing, and Shapley (`SH`) -/

open Classical in
/-- **Excludable-resource OR game** `orGame U w`: coalition `S` incurs fixed cost `w` if at least
one member of `S` belongs to the user set `U`, and `0` otherwise. -/
noncomputable def orGame {B : Type*} (U : Finset B) (w : ℝ) : CostSharingGame B where
  cost S := if ∃ i ∈ S, i ∈ U then w else 0
  cost_empty := by simp

open Classical in
@[simp]
theorem orGame_cost {B : Type*} (U : Finset B) (w : ℝ) (S : Finset B) :
    (orGame U w).cost S = if ∃ i ∈ S, i ∈ U then w else 0 := by
  rfl

theorem orGame_isSubmodular {B : Type*} [DecidableEq B] (U : Finset B) {w : ℝ} (hw : 0 ≤ w) :
    (orGame U w).IsSubmodular := by
  classical
  intro S T
  simp only [orGame_cost]
  have h1 : (∃ i ∈ S ∪ T, i ∈ U) ↔ (∃ i ∈ S, i ∈ U) ∨ (∃ i ∈ T, i ∈ U) := by
    simp [Finset.mem_union, or_and_right, exists_or]
  have h2 : (∃ i ∈ S ∩ T, i ∈ U) → (∃ i ∈ S, i ∈ U) ∧ (∃ i ∈ T, i ∈ U) :=
    fun ⟨i, hi, hiU⟩ => ⟨⟨i, (Finset.mem_inter.mp hi).1, hiU⟩, ⟨i, (Finset.mem_inter.mp hi).2, hiU⟩⟩
  by_cases hS : ∃ i ∈ S, i ∈ U <;> by_cases hT : ∃ i ∈ T, i ∈ U
  · simp only [h1, hS, hT, or_self, ↓reduceIte]
    split_ifs <;> linarith
  · simp only [h1, hS, hT, or_false, ↓reduceIte,
      show ¬ ∃ i ∈ S ∩ T, i ∈ U from fun h => hT (h2 h).2, add_zero, le_rfl]
  · simp only [h1, hS, hT, false_or, ↓reduceIte,
      show ¬ ∃ i ∈ S ∩ T, i ∈ U from fun h => hS (h2 h).1, zero_add, add_zero, le_rfl]
  · simp only [h1, hS, hT, or_self, ↓reduceIte,
      show ¬ ∃ i ∈ S ∩ T, i ∈ U from fun h => hS (h2 h).1, add_zero, le_rfl]

/-- The Shapley value of `orGame U w` splits `w` equally among `U` (`w / |U|`) and assigns `0`
outside `U`. -/
theorem shapleyValue_orGame {B : Type*} [Fintype B] [DecidableEq B]
    (U : Finset B) (w : ℝ) (i : B) :
    shapleyValue (orGame U w) i = if i ∈ U then w / (U.card : ℝ) else 0 := by
  have hdum_out : ∀ j ∉ U, shapleyValue (orGame U w) j = 0 := fun j hjU =>
    shapleyValue_satisfiesDummy (orGame U w) j fun S _ => by
      have hiff : (∃ x ∈ insert j S, x ∈ U) ↔ ∃ x ∈ S, x ∈ U :=
        ⟨fun ⟨x, hx, hxU⟩ => ⟨x, (Finset.mem_insert.mp hx).resolve_left fun h => hjU (h ▸ hxU),
          hxU⟩, fun ⟨x, hx, hxU⟩ => ⟨x, Finset.mem_insert_of_mem hx, hxU⟩⟩
      simp only [orGame_cost, hiff]
      split_ifs <;> rfl
  have hsym_in : ∀ j ∈ U, ∀ k ∈ U,
      shapleyValue (orGame U w) j = shapleyValue (orGame U w) k := fun j hjU k hkU =>
    shapleyValue_isSymmetric (orGame U w) j k fun S _ _ => by
      simp only [orGame_cost,
        show ∃ x ∈ insert j S, x ∈ U from ⟨j, Finset.mem_insert_self j S, hjU⟩,
        show ∃ x ∈ insert k S, x ∈ U from ⟨k, Finset.mem_insert_self k S, hkU⟩, ↓reduceIte]
  split_ifs with hiU
  · have htot := shapleyValue_isEfficient (orGame U w)
    have hex_univ : ∃ x ∈ (Finset.univ : Finset B), x ∈ U := ⟨i, Finset.mem_univ i, hiU⟩
    have huniv : (orGame U w).cost Finset.univ = w := by
      simp only [orGame_cost, hex_univ, ↓reduceIte]
    have hsplit : (∑ j : B, shapleyValue (orGame U w) j) =
        shapleyValue (orGame U w) i * (U.card : ℝ) :=
      calc (∑ j : B, shapleyValue (orGame U w) j)
          = ∑ j ∈ U, shapleyValue (orGame U w) j :=
            (Finset.sum_subset (Finset.subset_univ U) fun j _ hjU => hdum_out j hjU).symm
        _ = ∑ _j ∈ U, shapleyValue (orGame U w) i :=
            Finset.sum_congr rfl fun j hj => hsym_in j hj i hiU
        _ = shapleyValue (orGame U w) i * (U.card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [huniv, hsplit] at htot
    exact eq_div_of_mul_eq (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨i, hiU⟩)).ne' htot
  · exact hdum_out i hiU

/-- A **multicast routing cost-sharing instance** ([FeigenbaumPapadimitriouShenker2001];
[MoulinShenker2001]) on a rooted tree `tree : RootedTree V` with nonnegative link costs `edgeCost`
(`edgeCost tree.root = 0`) and receiver node placements `loc : A → V`. -/
structure MulticastInstance (V A : Type*) where
  /-- Underlying rooted multicast routing tree. -/
  tree : RootedTree V
  /-- Nonnegative cost of the link `(tree.parent v, v)` entering `v` (`0` at `tree.root`). -/
  edgeCost : V → ℝ
  /-- The root carries no incoming link cost. -/
  edgeCost_root : edgeCost tree.root = 0
  /-- Link costs are nonnegative. -/
  edgeCost_nonneg : ∀ v, 0 ≤ edgeCost v
  /-- Node of `tree` at which each receiver `i : A` resides. -/
  loc : A → V

namespace MulticastInstance

section CostAndShapley

variable {V A : Type*} [Fintype V] [DecidableEq V] (M : MulticastInstance V A)

/-- Non-root tree links traversed by the minimal multicast subtree serving coalition `R`. -/
def activeLinks (R : Finset A) : Finset V :=
  Finset.univ.filter fun v => v ≠ M.tree.root ∧ ∃ i ∈ R, M.tree.IsAncestor v (M.loc i)

@[simp]
theorem mem_activeLinks {R : Finset A} {v : V} :
    v ∈ M.activeLinks R ↔ v ≠ M.tree.root ∧ ∃ i ∈ R, M.tree.IsAncestor v (M.loc i) :=
  Finset.mem_filter.trans (and_iff_right (Finset.mem_univ v))

/-- Cooperative TU cost-sharing game induced by `M`: serving `R` costs the sum of `edgeCost` over
`M.activeLinks R`. -/
def toCostSharingGame : CostSharingGame A where
  cost R := ∑ v ∈ M.activeLinks R, M.edgeCost v
  cost_empty := by simp [activeLinks]

theorem toCostSharingGame_cost (R : Finset A) :
    M.toCostSharingGame.cost R = ∑ v ∈ M.activeLinks R, M.edgeCost v := by
  rfl

/-- Equivalent sum over all `v : V` (since `edgeCost tree.root = 0`). -/
theorem toCostSharingGame_cost_eq_sum (R : Finset A) :
    M.toCostSharingGame.cost R =
      ∑ v : V, if ∃ i ∈ R, M.tree.IsAncestor v (M.loc i) then M.edgeCost v else 0 := by
  rw [toCostSharingGame_cost, activeLinks, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : v = M.tree.root <;> simp [hv, M.edgeCost_root]

theorem toCostSharingGame_eq_sum_orGame [Fintype A] :
    M.toCostSharingGame =
      ∑ v : V, orGame (Finset.univ.filter fun i : A => M.tree.IsAncestor v (M.loc i))
        (M.edgeCost v) := by
  classical
  ext R
  rw [CostSharingGame.sum_cost, toCostSharingGame_cost_eq_sum]
  exact Finset.sum_congr rfl fun v _ => by simp [orGame_cost]

theorem restrict_toCostSharingGame_eq_sum_orGame (R : Finset A) :
    M.toCostSharingGame.restrict R =
      ∑ v : V, orGame (Finset.univ.filter fun x : R => M.tree.IsAncestor v (M.loc x.val))
        (M.edgeCost v) := by
  classical
  ext S
  rw [CostSharingGame.sum_cost, CostSharingGame.restrict_cost, toCostSharingGame_cost_eq_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [orGame_cost]

theorem toCostSharingGame_mono : Monotone M.toCostSharingGame.cost := by
  intro R S hRS
  simp only [toCostSharingGame_cost_eq_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  split_ifs with hR hS
  · exact le_rfl
  · obtain ⟨i, hi, h⟩ := hR
    exact absurd ⟨i, hRS hi, h⟩ hS
  · exact M.edgeCost_nonneg v
  · exact le_rfl

/-- Multicast tree cost `M.toCostSharingGame` is submodular ([MoulinShenker2001];
[FeigenbaumPapadimitriouShenker2001]). -/
theorem toCostSharingGame_isSubmodular [DecidableEq A] : M.toCostSharingGame.IsSubmodular := by
  intro R S
  simp only [toCostSharingGame_cost_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  let U : Finset A := (R ∪ S).filter fun i => M.tree.IsAncestor v (M.loc i)
  have heq : ∀ T : Finset A, T ⊆ R ∪ S →
      (if ∃ i ∈ T, M.tree.IsAncestor v (M.loc i) then M.edgeCost v else 0) =
        (orGame U (M.edgeCost v)).cost T := fun T hT => by
    have hiff : (∃ i ∈ T, M.tree.IsAncestor v (M.loc i)) ↔ ∃ i ∈ T, i ∈ U :=
      ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, Finset.mem_filter.mpr ⟨hT hi, h⟩⟩,
       fun ⟨i, hi, h⟩ => ⟨i, hi, (Finset.mem_filter.mp h).2⟩⟩
    simp only [orGame_cost, hiff]
    split_ifs <;> rfl
  rw [heq (R ∪ S) Subset.rfl,
    heq (R ∩ S) (Finset.inter_subset_left.trans Finset.subset_union_left),
    heq R Finset.subset_union_left,
    heq S Finset.subset_union_right]
  exact orGame_isSubmodular U (M.edgeCost_nonneg v) R S

theorem toCostSharingGame_isNonneg : M.toCostSharingGame.IsNonneg :=
  fun _ => Finset.sum_nonneg fun v _ => M.edgeCost_nonneg v

section ShapleyMulticast

variable [DecidableEq A]

/-- Closed-form **Shapley multicast cost share (`SH`)** ([MoulinShenker2001];
[FeigenbaumPapadimitriouShenker2001]): each active link `v` on the path from `root` to `M.loc i`
divides `M.edgeCost v` equally among the serviced receivers in `R` downstream of `v`. -/
noncomputable def shShare (R : Finset A) (i : A) : ℝ :=
  if i ∈ R then
    ∑ v : V with M.tree.IsAncestor v (M.loc i),
      M.edgeCost v / ((R.filter fun j => M.tree.IsAncestor v (M.loc j)).card : ℝ)
  else 0

theorem shShare_apply (R : Finset A) (i : A) :
    M.shShare R i =
      if i ∈ R then
        ∑ v : V with M.tree.IsAncestor v (M.loc i),
          M.edgeCost v / ((R.filter fun j => M.tree.IsAncestor v (M.loc j)).card : ℝ)
      else 0 := by
  rfl

private theorem shapleyValue_sum {B ι : Type*} [Fintype B] [DecidableEq B]
    (s : Finset ι) (f : ι → CostSharingGame B) (x : B) :
    shapleyValue (∑ k ∈ s, f k) x = ∑ k ∈ s, shapleyValue (f k) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact shapleyValue_satisfiesDummy 0 x fun _ _ => rfl
  | insert k s hks ih =>
    rw [Finset.sum_insert hks,
      congrFun (shapleyValue_isAdditive (f k) (∑ l ∈ s, f l)) x,
      Pi.add_apply, ih, Finset.sum_insert hks]

/-- **Per-link decomposition of the Shapley multicast scheme** ([MoulinShenker2001];
[FeigenbaumPapadimitriouShenker2001]): the coalition-restricted Shapley share
`M.toCostSharingGame.shapleyScheme.share R i` equals `M.shShare R i`. -/
theorem shapleyScheme_share_eq_shShare (R : Finset A) (i : A) :
    M.toCostSharingGame.shapleyScheme.share R i = M.shShare R i := by
  by_cases hi : i ∈ R
  · rw [CostSharingGame.shapleyScheme_eq_restrict M.toCostSharingGame hi,
      M.restrict_toCostSharingGame_eq_sum_orGame R, shapleyValue_sum]
    simp only [shShare, hi, ↓reduceIte, Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [shapleyValue_orGame]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with hanc
    · congr 2
      rw [Finset.univ_eq_attach, ← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
      congr 1
      ext a
      simp [and_comm]
    · rfl
  · simp [shShare, hi]

/-- The **Shapley multicast cost-sharing scheme (`SH`)**, defined by the closed-form equal
per-link split `M.shShare`. -/
noncomputable def shScheme : CostSharingScheme A where
  share := M.shShare
  share_eq_zero_of_not_mem {_ _} hi := by simp [shShare, hi]

@[simp]
theorem shScheme_share (R : Finset A) (i : A) :
    M.shScheme.share R i = M.shShare R i := by
  rfl

theorem shScheme_eq_shapleyScheme : M.shScheme = M.toCostSharingGame.shapleyScheme := by
  ext R i
  exact (M.shapleyScheme_share_eq_shShare R i).symm

theorem shScheme_isNonneg : M.shScheme.IsNonneg := by
  intro R i
  rw [shScheme_share, shShare_apply]
  split_ifs
  · exact Finset.sum_nonneg fun v _ => div_nonneg (M.edgeCost_nonneg v) (Nat.cast_nonneg _)
  · exact le_rfl

theorem shScheme_isBudgetBalanced : M.shScheme.IsBudgetBalanced M.toCostSharingGame 1 := by
  rw [M.shScheme_eq_shapleyScheme]
  exact M.toCostSharingGame.shapleyScheme_isBudgetBalanced

theorem shScheme_isCrossMonotone : M.shScheme.IsCrossMonotone := by
  rw [M.shScheme_eq_shapleyScheme]
  exact M.toCostSharingGame_isSubmodular.shapleyScheme_isCrossMonotone

theorem shScheme_inCore_univ [Fintype A] :
    M.toCostSharingGame.InCore (M.shScheme.share Finset.univ) :=
  M.shScheme.inCore_univ M.shScheme_isBudgetBalanced M.shScheme_isCrossMonotone

/-- The **Shapley (`SH`) multicast mechanism** `M.shScheme.moulinMechanism`
([MoulinShenker2001]; [FeigenbaumPapadimitriouShenker2001]). -/
noncomputable def shMechanism [Fintype A] : CostSharingMechanism A :=
  M.shScheme.moulinMechanism

@[simp]
theorem shMechanism_serviced [Fintype A] (b : A → ℝ) :
    M.shMechanism.serviced b = M.shScheme.moulinServiced b := by
  unfold shMechanism
  exact M.shScheme.moulinMechanism_serviced b

@[simp]
theorem shMechanism_payment [Fintype A] (b : A → ℝ) (i : A) :
    M.shMechanism.payment b i = M.shShare (M.shScheme.moulinServiced b) i := by
  unfold shMechanism
  rw [M.shScheme.moulinMechanism_payment, M.shScheme_share]

/-- **`SH` is group-strategyproof** ([MoulinShenker2001];
[FeigenbaumSchapiraShenker2007]). -/
theorem shMechanism_isGroupStrategyproof [Fintype A] : M.shMechanism.IsGroupStrategyproof :=
  M.shScheme.moulinMechanism_isGroupStrategyproof M.shScheme_isCrossMonotone

theorem shMechanism_isBudgetBalanced [Fintype A] :
    M.shMechanism.IsBudgetBalanced M.toCostSharingGame 1 :=
  M.shScheme.moulinMechanism_isBudgetBalanced M.shScheme_isBudgetBalanced

theorem shMechanism_noPositiveTransfers [Fintype A] : M.shMechanism.NoPositiveTransfers :=
  M.shScheme.moulinMechanism_noPositiveTransfers M.shScheme_isNonneg

theorem shMechanism_voluntaryParticipation [Fintype A] : M.shMechanism.VoluntaryParticipation :=
  M.shScheme.moulinMechanism_voluntaryParticipation

theorem shMechanism_consumerSovereignty [Fintype A] : M.shMechanism.ConsumerSovereignty :=
  M.shScheme.moulinMechanism_consumerSovereignty

end ShapleyMulticast

end CostAndShapley

/-! ## 3. Marginal Cost (`MC` / VCG) multicast mechanism and `2`-pass tree algorithm -/

section MarginalCost

variable {V A : Type*} [Fintype V] [DecidableEq V] (M : MulticastInstance V A)

/-- Net social welfare `(∑ i ∈ R, b i) - cost R` of serving coalition `R` under reported bids `b`
([FeigenbaumPapadimitriouShenker2001]). -/
def netWelfare (b : A → ℝ) (R : Finset A) : ℝ :=
  (∑ i ∈ R, b i) - M.toCostSharingGame.cost R

@[simp]
theorem netWelfare_empty (b : A → ℝ) : M.netWelfare b ∅ = 0 := by
  simp [netWelfare]

theorem netWelfare_apply (b : A → ℝ) (R : Finset A) :
    M.netWelfare b R = (∑ i ∈ R, b i) - M.toCostSharingGame.cost R := by
  rfl

/-- **Supermodularity of net welfare** on multicast trees ([FeigenbaumPapadimitriouShenker2001];
[FeigenbaumSchapiraShenker2007]). -/
theorem netWelfare_supermodular [DecidableEq A] (b : A → ℝ) (R S : Finset A) :
    M.netWelfare b R + M.netWelfare b S ≤
      M.netWelfare b (R ∪ S) + M.netWelfare b (R ∩ S) := by
  simp only [netWelfare]
  have hsum := Finset.sum_union_inter (s₁ := R) (s₂ := S) (f := b)
  have hsub := M.toCostSharingGame_isSubmodular R S
  linarith

/-- Coalition `R` maximizes reported net social welfare `M.netWelfare b`. -/
@[expose] def IsWelfareMaximizingSet (b : A → ℝ) (R : Finset A) : Prop :=
  ∀ S : Finset A, M.netWelfare b S ≤ M.netWelfare b R

theorem IsWelfareMaximizingSet.union [DecidableEq A] {M : MulticastInstance V A}
    {b : A → ℝ} {R S : Finset A}
    (hR : M.IsWelfareMaximizingSet b R) (hS : M.IsWelfareMaximizingSet b S) :
    M.IsWelfareMaximizingSet b (R ∪ S) := by
  intro T
  exact (hR T).trans (by linarith [M.netWelfare_supermodular b R S, hS (R ∩ S)])

/-- Local subtree net welfare of `R` inside `M.tree.subtreeNodes u` (charging `M.edgeCost u` when
at least one receiver of `R` resides in `M.tree.subtreeNodes u`). -/
private def localNetWelfare (b : A → ℝ) (u : V) (R : Finset A) : ℝ :=
  let Ru := R.filter fun i => M.loc i ∈ M.tree.subtreeNodes u
  (∑ i ∈ Ru, b i) -
    ∑ v ∈ M.tree.subtreeNodes u,
      if ∃ i ∈ Ru, M.tree.IsAncestor v (M.loc i) then M.edgeCost v else 0

private theorem localNetWelfare_root (b : A → ℝ) (R : Finset A) :
    M.localNetWelfare b M.tree.root R = M.netWelfare b R := by
  simp [localNetWelfare, M.tree.subtreeNodes_root, netWelfare, M.toCostSharingGame_cost_eq_sum]

private theorem localNetWelfare_eq_zero_of_empty {b : A → ℝ} {u : V} {R : Finset A}
    (h : (R.filter fun i => M.loc i ∈ M.tree.subtreeNodes u) = ∅) :
    M.localNetWelfare b u R = 0 := by
  dsimp only [localNetWelfare]
  rw [h]
  simp

private theorem localNetWelfare_decomp {b : A → ℝ} {u : V} {R : Finset A}
    (hne : (R.filter fun i => M.loc i ∈ M.tree.subtreeNodes u).Nonempty) :
    M.localNetWelfare b u R =
      (∑ i ∈ R with M.loc i = u, b i) +
        (∑ c ∈ M.tree.children u, M.localNetWelfare b c R) - M.edgeCost u := by
  classical
  set Ru := R.filter fun i => M.loc i ∈ M.tree.subtreeNodes u
  have hpart := M.tree.subtreeNodes_eq_insert_biUnion u
  have hnot_u := M.tree.notMem_biUnion_children_subtreeNodes u
  have hpwd := M.tree.pairwiseDisjoint_children_subtreeNodes u
  have hRu_eq : Ru = (R.filter fun i => M.loc i = u) ∪
      (M.tree.children u).biUnion
        (fun c => R.filter fun i => M.loc i ∈ M.tree.subtreeNodes c) := by
    ext i
    simp only [Ru, Finset.mem_filter, hpart, Finset.mem_insert, Finset.mem_biUnion,
      Finset.mem_union]
    tauto
  have hdisj_head : Disjoint (R.filter fun i => M.loc i = u)
      ((M.tree.children u).biUnion
        fun c => R.filter fun i => M.loc i ∈ M.tree.subtreeNodes c) := by
    refine Finset.disjoint_left.mpr fun i hi₁ hi₂ => ?_
    obtain ⟨c, hc, hj⟩ := Finset.mem_biUnion.mp hi₂
    exact hnot_u (Finset.mem_biUnion.mpr
      ⟨c, hc, (Finset.mem_filter.mp hi₁).2 ▸ (Finset.mem_filter.mp hj).2⟩)
  have hpwd_agents : (M.tree.children u : Set V).PairwiseDisjoint
      (fun c => R.filter fun i => M.loc i ∈ M.tree.subtreeNodes c) := fun c₁ hc₁ c₂ hc₂ hne_c =>
    Finset.disjoint_left.mpr fun i hi₁ hi₂ =>
      Finset.disjoint_left.mp (hpwd hc₁ hc₂ hne_c)
        (Finset.mem_filter.mp hi₁).2 (Finset.mem_filter.mp hi₂).2
  have hu_active : ∃ i ∈ Ru, M.tree.IsAncestor u (M.loc i) :=
    let ⟨i, hi⟩ := hne
    ⟨i, hi, M.tree.mem_subtreeNodes.mp (Finset.mem_filter.mp hi).2⟩
  have hchild_iff : ∀ c ∈ M.tree.children u, ∀ v ∈ M.tree.subtreeNodes c,
      ((∃ i ∈ Ru, M.tree.IsAncestor v (M.loc i)) ↔
        ∃ i ∈ R.filter (fun j => M.loc j ∈ M.tree.subtreeNodes c),
          M.tree.IsAncestor v (M.loc i)) := fun c hc v hv => by
    have hcv := M.tree.mem_subtreeNodes.mp hv
    have huc : M.tree.IsAncestor u c :=
      (M.tree.mem_children.mp hc).2 ▸ M.tree.isAncestor_parent_self c
    exact ⟨fun ⟨i, hi, hvi⟩ => ⟨i, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hi).1, M.tree.mem_subtreeNodes.mpr (hcv.trans hvi)⟩, hvi⟩,
      fun ⟨i, hi, hvi⟩ => ⟨i, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hi).1,
          M.tree.mem_subtreeNodes.mpr (huc.trans (hcv.trans hvi))⟩, hvi⟩⟩
  have hsum_cost :
      (∑ v ∈ M.tree.subtreeNodes u,
          if ∃ i ∈ Ru, M.tree.IsAncestor v (M.loc i) then M.edgeCost v else 0) =
        M.edgeCost u +
          ∑ c ∈ M.tree.children u, ∑ v ∈ M.tree.subtreeNodes c,
            if ∃ i ∈ R.filter (fun j => M.loc j ∈ M.tree.subtreeNodes c),
                M.tree.IsAncestor v (M.loc i)
            then M.edgeCost v else 0 := by
    conv_lhs => rw [hpart]
    rw [Finset.sum_insert hnot_u, Finset.sum_biUnion hpwd]
    simp only [hu_active, ↓reduceIte]
    congr 1
    exact Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun v hv => by
      simp only [hchild_iff c hc v hv]
  have hsum_b : ∑ i ∈ Ru, b i = (∑ i ∈ R with M.loc i = u, b i) +
      ∑ c ∈ M.tree.children u, ∑ i ∈ R with M.loc i ∈ M.tree.subtreeNodes c, b i := by
    rw [hRu_eq, Finset.sum_union hdisj_head, Finset.sum_biUnion hpwd_agents]
  dsimp only [localNetWelfare]
  rw [hsum_b, hsum_cost, Finset.sum_sub_distrib]
  ring

section FintypeAgentsOnly

variable [Fintype A]

/-- Maximum reported net social welfare `max_R netWelfare b R` (`≥ 0`). -/
noncomputable def maxNetWelfare (b : A → ℝ) : ℝ :=
  letI := Classical.decEq A
  Finset.univ.sup' Finset.univ_nonempty (M.netWelfare b)

theorem netWelfare_le_maxNetWelfare (b : A → ℝ) (R : Finset A) :
    M.netWelfare b R ≤ M.maxNetWelfare b := by
  classical
  unfold maxNetWelfare
  exact Finset.le_sup' (M.netWelfare b) (Finset.mem_univ R)

theorem maxNetWelfare_nonneg (b : A → ℝ) : 0 ≤ M.maxNetWelfare b := by
  simpa using M.netWelfare_le_maxNetWelfare b ∅

theorem isWelfareMaximizingSet_iff_eq_maxNetWelfare {b : A → ℝ} {R : Finset A} :
    M.IsWelfareMaximizingSet b R ↔ M.netWelfare b R = M.maxNetWelfare b := by
  classical
  refine ⟨fun h => le_antisymm (M.netWelfare_le_maxNetWelfare b R) ?_,
    fun h S => (M.netWelfare_le_maxNetWelfare b S).trans_eq h.symm⟩
  unfold maxNetWelfare
  exact Finset.sup'_le _ _ fun S _ => h S

/-- **Pass 1 (bottom-up) node welfare** `nodeWelfare b u`: sum of nonnegative resident bids at `u`
plus incoming nonnegative child surplus messages `max 0 (nodeWelfare b c - edgeCost c)`
([FeigenbaumPapadimitriouShenker2001]; [FeigenbaumSchapiraShenker2007]). -/
noncomputable def nodeWelfare (b : A → ℝ) (u : V) : ℝ :=
  (∑ i : A with M.loc i = u, max (b i) 0) +
    ∑ c ∈ (M.tree.children u).attach, max 0 (nodeWelfare b c.val - M.edgeCost c.val)
termination_by M.tree.maxDepth + 1 - M.tree.depth u
decreasing_by
  have hdc := M.tree.depth_of_mem_children c.property
  have hle := M.tree.depth_le_maxDepth c.val
  omega

/-- Net surplus `nodeWelfare b u - edgeCost u` of the subtree rooted at `u` (including link `u`). -/
noncomputable def subtreeSurplus (b : A → ℝ) (u : V) : ℝ :=
  M.nodeWelfare b u - M.edgeCost u

theorem subtreeSurplus_eq (b : A → ℝ) (u : V) :
    M.subtreeSurplus b u = M.nodeWelfare b u - M.edgeCost u := by
  rfl

/-- **Pass 1 upward message** `max 0 (subtreeSurplus b u)` sent along link `(parent u ← u)`. -/
noncomputable def upMsg (b : A → ℝ) (u : V) : ℝ :=
  max 0 (M.subtreeSurplus b u)

theorem upMsg_eq (b : A → ℝ) (u : V) :
    M.upMsg b u = max 0 (M.subtreeSurplus b u) := by
  rfl

theorem nodeWelfare_eq (b : A → ℝ) (u : V) :
    M.nodeWelfare b u =
      (∑ i : A with M.loc i = u, max (b i) 0) + ∑ c ∈ M.tree.children u, M.upMsg b c := by
  conv_lhs => unfold nodeWelfare
  rw [Finset.sum_attach _ (fun c => max 0 (M.nodeWelfare b c - M.edgeCost c))]
  rfl

theorem nodeWelfare_nonneg (b : A → ℝ) (u : V) : 0 ≤ M.nodeWelfare b u := by
  rw [M.nodeWelfare_eq]
  exact add_nonneg (Finset.sum_nonneg fun _ _ => le_max_right _ _)
    (Finset.sum_nonneg fun _ _ => le_max_left _ _)

theorem subtreeSurplus_root (b : A → ℝ) :
    M.subtreeSurplus b M.tree.root = M.nodeWelfare b M.tree.root := by
  simp [subtreeSurplus, M.edgeCost_root]

theorem upMsg_root (b : A → ℝ) :
    M.upMsg b M.tree.root = M.nodeWelfare b M.tree.root := by
  rw [upMsg, M.subtreeSurplus_root, max_eq_right (M.nodeWelfare_nonneg b M.tree.root)]

private theorem localNetWelfare_le_subtreeSurplus_and_upMsg {b : A → ℝ} (hb : ∀ i, 0 ≤ b i)
    (u : V) (R : Finset A) :
    ((R.filter fun i => M.loc i ∈ M.tree.subtreeNodes u).Nonempty →
        M.localNetWelfare b u R ≤ M.subtreeSurplus b u) ∧
      M.localNetWelfare b u R ≤ M.upMsg b u := by
  suffices hrec : ∀ rem v, M.tree.maxDepth + 1 - M.tree.depth v ≤ rem →
      (((R.filter fun i => M.loc i ∈ M.tree.subtreeNodes v).Nonempty →
          M.localNetWelfare b v R ≤ M.subtreeSurplus b v) ∧
        M.localNetWelfare b v R ≤ M.upMsg b v) from hrec _ u le_rfl
  intro rem
  induction rem with
  | zero =>
    intro v hrem
    have := M.tree.depth_le_maxDepth v
    omega
  | succ rem ih =>
    intro v hrem
    have hne_case : (R.filter fun i => M.loc i ∈ M.tree.subtreeNodes v).Nonempty →
        M.localNetWelfare b v R ≤ M.subtreeSurplus b v := fun hne => by
      classical
      rw [M.localNetWelfare_decomp hne, subtreeSurplus, M.nodeWelfare_eq]
      have hres : (∑ i ∈ R with M.loc i = v, b i) ≤ ∑ i : A with M.loc i = v, max (b i) 0 :=
        calc (∑ i ∈ R with M.loc i = v, b i)
            ≤ ∑ i : A with M.loc i = v, b i :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.filter_subset_filter _ (Finset.subset_univ _)) fun i _ _ => hb i
          _ ≤ ∑ i : A with M.loc i = v, max (b i) 0 :=
              Finset.sum_le_sum fun _ _ => le_max_left _ _
      have hch : (∑ c ∈ M.tree.children v, M.localNetWelfare b c R) ≤
          ∑ c ∈ M.tree.children v, M.upMsg b c := Finset.sum_le_sum fun c hc => by
        have := M.tree.depth_of_mem_children hc
        have := M.tree.depth_le_maxDepth c
        exact (ih c (by omega)).2
      linarith
    refine ⟨hne_case, ?_⟩
    rcases (R.filter fun i => M.loc i ∈ M.tree.subtreeNodes v).eq_empty_or_nonempty with h | h
    · rw [M.localNetWelfare_eq_zero_of_empty h]
      exact le_max_left 0 _
    · exact (hne_case h).trans (le_max_right 0 _)

/-- **Pass 2 (top-down) activation bit** `topDownActive b u`: `true` at `root`, and propagated from
`parent u` to `u` iff `0 ≤ subtreeSurplus b u`. -/
noncomputable def topDownActive (b : A → ℝ) (u : V) : Bool :=
  if _h : u = M.tree.root then true
  else topDownActive b (M.tree.parent u) && decide (0 ≤ M.subtreeSurplus b u)
termination_by M.tree.depth u
decreasing_by exact M.tree.depth_parent_lt _h

/-- **Pass 2 (top-down) bottleneck surplus** `topDownThreshold b u : Option ℝ`: `none` at `root`,
and `min` of `subtreeSurplus` over all non-root ancestors along `(root → u)`. -/
noncomputable def topDownThreshold (b : A → ℝ) (u : V) : Option ℝ :=
  if _h : u = M.tree.root then none
  else
    match topDownThreshold b (M.tree.parent u) with
    | none => some (M.subtreeSurplus b u)
    | some m => some (min m (M.subtreeSurplus b u))
termination_by M.tree.depth u
decreasing_by exact M.tree.depth_parent_lt _h

@[simp]
theorem topDownActive_root (b : A → ℝ) : M.topDownActive b M.tree.root = true := by
  unfold topDownActive
  simp

theorem topDownActive_of_ne_root (b : A → ℝ) {u : V} (hu : u ≠ M.tree.root) :
    M.topDownActive b u =
      (M.topDownActive b (M.tree.parent u) && decide (0 ≤ M.subtreeSurplus b u)) := by
  conv_lhs => unfold topDownActive
  simp only [hu, ↓reduceDIte]

@[simp]
theorem topDownThreshold_root (b : A → ℝ) : M.topDownThreshold b M.tree.root = none := by
  unfold topDownThreshold
  simp

theorem topDownThreshold_of_ne_root (b : A → ℝ) {u : V} (hu : u ≠ M.tree.root) :
    M.topDownThreshold b u =
      match M.topDownThreshold b (M.tree.parent u) with
      | none => some (M.subtreeSurplus b u)
      | some m => some (min m (M.subtreeSurplus b u)) := by
  conv_lhs => unfold topDownThreshold
  simp only [hu, ↓reduceDIte]
  rfl

theorem topDownActive_eq_true_iff (b : A → ℝ) (u : V) :
    M.topDownActive b u = true ↔
      ∀ w, M.tree.IsAncestor w u → w ≠ M.tree.root → 0 ≤ M.subtreeSurplus b w := by
  suffices hrec : ∀ d v, M.tree.depth v = d →
      (M.topDownActive b v = true ↔
        ∀ w, M.tree.IsAncestor w v → w ≠ M.tree.root → 0 ≤ M.subtreeSurplus b w) from
    hrec _ u rfl
  intro d
  induction d with
  | zero =>
    intro v hd
    rw [M.tree.depth_eq_zero_iff.mp hd, M.topDownActive_root]
    exact ⟨fun _ w hw hne => absurd (hw.antisymm (M.tree.isAncestor_root w)) hne, fun _ => rfl⟩
  | succ d ih =>
    intro v hd
    have hv : v ≠ M.tree.root := fun h => by rw [h, M.tree.depth_root] at hd; omega
    rw [M.topDownActive_of_ne_root b hv, Bool.and_eq_true, decide_eq_true_eq,
      ih (M.tree.parent v) (by have := M.tree.depth_parent v; omega)]
    exact ⟨fun ⟨hp, hs⟩ w hw hne => hw.eq_or_isAncestor_parent.elim (fun h => h ▸ hs)
        fun ⟨_, hwp⟩ => hp w hwp hne,
      fun hall => ⟨fun w hwp => hall w (hwp.trans (M.tree.isAncestor_parent_self v)),
        hall v (M.tree.isAncestor_refl v) hv⟩⟩

/-- Receiver set selected locally at each node by the `2`-pass algorithm. -/
noncomputable def twoPassReceivers (b : A → ℝ) : Finset A :=
  Finset.univ.filter fun i => M.topDownActive b (M.loc i) = true

@[simp]
theorem mem_twoPassReceivers {b : A → ℝ} {i : A} :
    i ∈ M.twoPassReceivers b ↔ M.topDownActive b (M.loc i) = true :=
  Finset.mem_filter.trans (and_iff_right (Finset.mem_univ i))

/-- Payment computed locally at each node by the `2`-pass algorithm. -/
noncomputable def twoPassPayment (b : A → ℝ) (i : A) : ℝ :=
  if M.topDownActive b (M.loc i) = true then
    match M.topDownThreshold b (M.loc i) with
    | none => 0
    | some m => max 0 (b i - m)
  else 0

theorem twoPassPayment_eq (b : A → ℝ) (i : A) :
    M.twoPassPayment b i =
      if M.topDownActive b (M.loc i) = true then
        match M.topDownThreshold b (M.loc i) with
        | none => 0
        | some m => max 0 (b i - m)
      else 0 := by
  rfl

private theorem localNetWelfare_twoPassReceivers_eq_subtreeSurplus
    {b : A → ℝ} (hb : ∀ i, 0 ≤ b i) :
    ∀ u : V, M.topDownActive b u = true →
      M.localNetWelfare b u (M.twoPassReceivers b) = M.subtreeSurplus b u := by
  set R₂ := M.twoPassReceivers b
  suffices hrec : ∀ rem v, M.tree.maxDepth + 1 - M.tree.depth v ≤ rem →
      M.topDownActive b v = true → M.localNetWelfare b v R₂ = M.subtreeSurplus b v from
    fun u => hrec _ u le_rfl
  intro rem
  induction rem with
  | zero =>
    intro v hrem
    have := M.tree.depth_le_maxDepth v
    omega
  | succ rem ih =>
    intro v hrem hact_v
    have hsurp_nonneg : 0 ≤ M.subtreeSurplus b v := by
      by_cases hv : v = M.tree.root
      · rw [hv, M.subtreeSurplus_root]
        exact M.nodeWelfare_nonneg b _
      · exact ((M.topDownActive_eq_true_iff b v).mp hact_v) v (M.tree.isAncestor_refl v) hv
    have hch_eq : ∀ c ∈ M.tree.children v, M.localNetWelfare b c R₂ = M.upMsg b c := fun c hc => by
      obtain ⟨hc_ne, hpc⟩ := M.tree.mem_children.mp hc
      have := M.tree.depth_of_mem_children hc
      have := M.tree.depth_le_maxDepth c
      by_cases hsc : 0 ≤ M.subtreeSurplus b c
      · have hact_c : M.topDownActive b c = true := by
          rw [M.topDownActive_of_ne_root b hc_ne, hpc, hact_v, Bool.true_and, decide_eq_true_eq]
          exact hsc
        rw [ih c (by omega) hact_c, upMsg, max_eq_right hsc]
      · have hemp : (R₂.filter fun i => M.loc i ∈ M.tree.subtreeNodes c) = ∅ :=
          Finset.eq_empty_of_forall_notMem fun i hi => by
            obtain ⟨hiR, hmem⟩ := Finset.mem_filter.mp hi
            exact hsc (((M.topDownActive_eq_true_iff b _).mp (M.mem_twoPassReceivers.mp hiR)) c
              (M.tree.mem_subtreeNodes.mp hmem) hc_ne)
        rw [M.localNetWelfare_eq_zero_of_empty hemp, upMsg, max_eq_left (not_le.mp hsc).le]
    rcases (R₂.filter fun i => M.loc i ∈ M.tree.subtreeNodes v).eq_empty_or_nonempty with
      hemp | hne
    · have hno_res : (Finset.univ.filter fun i : A => M.loc i = v) = ∅ :=
        Finset.eq_empty_of_forall_notMem fun i hi => by
          have hloc := (Finset.mem_filter.mp hi).2
          have hmem : i ∈ R₂.filter fun j => M.loc j ∈ M.tree.subtreeNodes v :=
            Finset.mem_filter.mpr ⟨M.mem_twoPassReceivers.mpr (hloc.symm ▸ hact_v),
              M.tree.mem_subtreeNodes.mpr (hloc.symm ▸ M.tree.isAncestor_refl v)⟩
          exact Finset.notMem_empty i (hemp ▸ hmem)
      have hch_zero : ∀ c ∈ M.tree.children v, M.upMsg b c = 0 := fun c hc => by
        have huc : M.tree.IsAncestor v c :=
          (M.tree.mem_children.mp hc).2 ▸ M.tree.isAncestor_parent_self c
        have hsub_c : (R₂.filter fun i => M.loc i ∈ M.tree.subtreeNodes c) = ∅ :=
          Finset.eq_empty_of_forall_notMem fun i hi => by
            obtain ⟨hiR, hic⟩ := Finset.mem_filter.mp hi
            exact Finset.notMem_empty i (hemp ▸ Finset.mem_filter.mpr ⟨hiR,
              M.tree.mem_subtreeNodes.mpr (huc.trans (M.tree.mem_subtreeNodes.mp hic))⟩)
        rw [← hch_eq c hc, M.localNetWelfare_eq_zero_of_empty hsub_c]
      rw [M.localNetWelfare_eq_zero_of_empty hemp]
      have : M.nodeWelfare b v = 0 := by
        rw [M.nodeWelfare_eq, hno_res, Finset.sum_empty, Finset.sum_eq_zero hch_zero, add_zero]
      have := M.edgeCost_nonneg v
      unfold subtreeSurplus at hsurp_nonneg ⊢
      linarith
    · have hflt_eq : (R₂.filter fun i => M.loc i = v) =
          Finset.univ.filter fun i : A => M.loc i = v := by
        ext i
        simp only [R₂, twoPassReceivers, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨And.right, fun hl => ⟨hl.symm ▸ hact_v, hl⟩⟩
      rw [M.localNetWelfare_decomp hne, subtreeSurplus, M.nodeWelfare_eq, hflt_eq,
        Finset.sum_congr rfl fun i _ => (max_eq_left (hb i)).symm, Finset.sum_congr rfl hch_eq]

/-- **Pass 1 root correctness**: on nonnegative bid profiles, `nodeWelfare b tree.root` equals the
global maximum net social welfare `maxNetWelfare b`. -/
theorem nodeWelfare_root_eq_maxNetWelfare {b : A → ℝ} (hb : ∀ i, 0 ≤ b i) :
    M.nodeWelfare b M.tree.root = M.maxNetWelfare b := by
  classical
  refine le_antisymm ?_ ?_
  · rw [← M.subtreeSurplus_root, ← M.localNetWelfare_twoPassReceivers_eq_subtreeSurplus hb
      M.tree.root (M.topDownActive_root b), M.localNetWelfare_root]
    exact M.netWelfare_le_maxNetWelfare b _
  · unfold maxNetWelfare
    refine Finset.sup'_le _ _ fun R _ => ?_
    simpa only [M.localNetWelfare_root, M.upMsg_root] using
      (M.localNetWelfare_le_subtreeSurplus_and_upMsg hb M.tree.root R).2

end FintypeAgentsOnly

section FiniteAgents

variable [Fintype A] [DecidableEq A]

open Classical in
/-- The **unique largest welfare-maximizing receiver coalition** `mcReceivers b`: the union of all
coalitions maximizing `M.netWelfare b` ([FeigenbaumPapadimitriouShenker2001];
[FeigenbaumSchapiraShenker2007]). -/
noncomputable def mcReceivers (b : A → ℝ) : Finset A :=
  ((Finset.univ : Finset (Finset A)).filter (M.IsWelfareMaximizingSet b)).biUnion id

/-- **Unique largest welfare-maximizing coalition** ([FeigenbaumPapadimitriouShenker2001];
[FeigenbaumSchapiraShenker2007]): `mcReceivers b` is itself welfare-maximizing and contains every
welfare-maximizing coalition (`IsGreatest {R | IsWelfareMaximizingSet b R} (mcReceivers b)`). -/
theorem isGreatest_isWelfareMaximizingSet_mcReceivers (b : A → ℝ) :
    IsGreatest {R : Finset A | M.IsWelfareMaximizingSet b R} (M.mcReceivers b) := by
  classical
  let W := (Finset.univ : Finset (Finset A)).filter (M.IsWelfareMaximizingSet b)
  obtain ⟨R₀, _, hR₀⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Finset A)) (M.netWelfare b) Finset.univ_nonempty
  have hW_ne : W.Nonempty :=
    ⟨R₀, Finset.mem_filter.mpr ⟨Finset.mem_univ R₀, fun S => hR₀ S (Finset.mem_univ S)⟩⟩
  have hbi_max : ∀ {U : Finset (Finset A)}, U.Nonempty →
      (∀ R ∈ U, M.IsWelfareMaximizingSet b R) →
      M.IsWelfareMaximizingSet b (U.biUnion id) := by
    intro U hU
    induction hU using Finset.Nonempty.cons_induction with
    | singleton R => simp
    | cons R U hRU _ ih =>
      intro hall
      rw [Finset.cons_eq_insert, Finset.biUnion_insert]
      exact (hall R (Finset.mem_cons_self R U)).union
        (ih fun S hS => hall S (Finset.mem_cons.mpr (Or.inr hS)))
  change IsGreatest _ (W.biUnion id)
  exact ⟨hbi_max hW_ne fun R hR => (Finset.mem_filter.mp hR).2,
    fun R hR => Finset.subset_biUnion_of_mem id (Finset.mem_filter.mpr ⟨Finset.mem_univ R, hR⟩)⟩

theorem netWelfare_mcReceivers (b : A → ℝ) :
    M.netWelfare b (M.mcReceivers b) = M.maxNetWelfare b :=
  M.isWelfareMaximizingSet_iff_eq_maxNetWelfare.mp
    (M.isGreatest_isWelfareMaximizingSet_mcReceivers b).1

/-- Maximum reported net social welfare achievable by coalitions excluding receiver `i`. -/
noncomputable def maxNetWelfareWithout (b : A → ℝ) (i : A) : ℝ :=
  ((Finset.univ : Finset (Finset A)).filter fun R => i ∉ R).sup'
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ ∅, Finset.notMem_empty i⟩⟩
    (M.netWelfare b)

theorem netWelfare_le_maxNetWelfareWithout {b : A → ℝ} {i : A} {R : Finset A} (hi : i ∉ R) :
    M.netWelfare b R ≤ M.maxNetWelfareWithout b i :=
  Finset.le_sup' (M.netWelfare b) (Finset.mem_filter.mpr ⟨Finset.mem_univ R, hi⟩)

theorem maxNetWelfareWithout_le_maxNetWelfare (b : A → ℝ) (i : A) :
    M.maxNetWelfareWithout b i ≤ M.maxNetWelfare b :=
  Finset.sup'_le _ _ fun R _ => M.netWelfare_le_maxNetWelfare b R

theorem maxNetWelfareWithout_update (b : A → ℝ) (i : A) (x : ℝ) :
    M.maxNetWelfareWithout (Function.update b i x) i = M.maxNetWelfareWithout b i := by
  unfold maxNetWelfareWithout
  refine Finset.sup'_congr _ rfl fun R hR => congrArg (· - _) <| Finset.sum_congr rfl fun j hj =>
    Function.update_of_ne (fun h : j = i => (Finset.mem_filter.mp hR).2 (h ▸ hj)) x b

/-- The **Marginal Cost (`MC` / Clarke VCG) multicast mechanism**
([FeigenbaumPapadimitriouShenker2001]; [FeigenbaumSchapiraShenker2007]):
serves `mcReceivers b` and charges each served receiver `i` its Clarke pivot payment
`maxNetWelfareWithout b i - (netWelfare b (mcReceivers b) - b i)`. -/
noncomputable def mcMechanism : CostSharingMechanism A where
  serviced := M.mcReceivers
  payment b i :=
    if i ∈ M.mcReceivers b then
      M.maxNetWelfareWithout b i - (M.netWelfare b (M.mcReceivers b) - b i)
    else 0

@[simp]
theorem mcMechanism_serviced (b : A → ℝ) :
    M.mcMechanism.serviced b = M.mcReceivers b := by
  rfl

theorem mcMechanism_payment_of_mem {b : A → ℝ} {i : A} (hi : i ∈ M.mcReceivers b) :
    M.mcMechanism.payment b i =
      M.maxNetWelfareWithout b i - (M.netWelfare b (M.mcReceivers b) - b i) := by
  simp [mcMechanism, hi]

theorem mcMechanism_payment_of_notMem {b : A → ℝ} {i : A} (hi : i ∉ M.mcReceivers b) :
    M.mcMechanism.payment b i = 0 := by
  simp [mcMechanism, hi]

theorem mcMechanism_utility_eq (u b : A → ℝ) (i : A) :
    M.mcMechanism.utility u b i =
      M.netWelfare (Function.update b i (u i)) (M.mcReceivers b) -
        M.maxNetWelfareWithout b i := by
  rw [CostSharingMechanism.utility_eq]
  simp only [mcMechanism, netWelfare]
  by_cases hi : i ∈ M.mcReceivers b
  · have hsum : ∑ j ∈ M.mcReceivers b, Function.update b i (u i) j =
        (∑ j ∈ M.mcReceivers b, b j) - b i + u i := by
      rw [← Finset.sum_erase_add _ _ hi, ← Finset.sum_erase_add _ b hi, Function.update_self,
        Finset.sum_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ b]
      ring
    simp only [hi, ↓reduceIte, hsum]; ring
  · have hsum : ∑ j ∈ M.mcReceivers b, Function.update b i (u i) j = ∑ j ∈ M.mcReceivers b, b j :=
      Finset.sum_congr rfl fun j hj => Function.update_of_ne (fun h : j = i => hi (h ▸ hj)) _ b
    have heq_w : M.maxNetWelfareWithout b i =
        (∑ j ∈ M.mcReceivers b, b j) - M.toCostSharingGame.cost (M.mcReceivers b) := by
      rw [← M.netWelfare_apply, M.netWelfare_mcReceivers]
      exact le_antisymm (M.maxNetWelfareWithout_le_maxNetWelfare b i)
        (M.netWelfare_mcReceivers b ▸ M.netWelfare_le_maxNetWelfareWithout hi)
    simp only [hi, ↓reduceIte, hsum, heq_w]; ring

/-- **Dominant-strategy truthfulness of `mcMechanism` on all real profiles**: reporting `u i`
weakly dominates any misreport `b i`. -/
theorem mcMechanism_utility_le_truthful (u b : A → ℝ) (i : A) :
    M.mcMechanism.utility u b i ≤ M.mcMechanism.utility u (Function.update b i (u i)) i := by
  rw [M.mcMechanism_utility_eq, M.mcMechanism_utility_eq, Function.update_idem,
    M.maxNetWelfareWithout_update]
  have hmax := (M.isGreatest_isWelfareMaximizingSet_mcReceivers (Function.update b i (u i))).1
    (M.mcReceivers b)
  linarith

theorem mcMechanism_isDSIC : M.mcMechanism.toSingleParameterMechanism.IsDSIC := by
  intro i b v _ _
  let u := Function.update b i v
  have hv : v = u i := (Function.update_self i v b).symm
  rw [hv, CostSharingMechanism.toSingleParameterMechanism_utility,
    CostSharingMechanism.toSingleParameterMechanism_utility]
  simpa [u, Function.update_idem] using M.mcMechanism_utility_le_truthful u b i

theorem mcMechanism_voluntaryParticipation : M.mcMechanism.VoluntaryParticipation := by
  refine ⟨fun b i hi => M.mcMechanism_payment_of_notMem hi, fun b i hi => ?_⟩
  rw [M.mcMechanism_payment_of_mem hi, M.netWelfare_mcReceivers]
  have hle := M.maxNetWelfareWithout_le_maxNetWelfare b i
  linarith

/-- Each served receiver under `mcMechanism` pays at least its marginal cost
`cost (mcReceivers b) - cost (mcReceivers b \ {i}) ≥ 0`. -/
theorem cost_sub_erase_le_mcMechanism_payment {b : A → ℝ} {i : A} (hi : i ∈ M.mcReceivers b) :
    M.toCostSharingGame.cost (M.mcReceivers b) -
        M.toCostSharingGame.cost ((M.mcReceivers b).erase i) ≤
      M.mcMechanism.payment b i := by
  rw [M.mcMechanism_payment_of_mem hi]
  have her :=
    M.netWelfare_le_maxNetWelfareWithout (b := b) (Finset.notMem_erase i (M.mcReceivers b))
  simp only [netWelfare, ← Finset.sum_erase_add _ b hi] at her ⊢
  linarith

theorem mcMechanism_noPositiveTransfers : M.mcMechanism.NoPositiveTransfers := by
  intro b i
  by_cases hi : i ∈ M.mcReceivers b
  · linarith [M.toCostSharingGame_mono (Finset.erase_subset i (M.mcReceivers b)),
      M.cost_sub_erase_le_mcMechanism_payment hi]
  · rw [M.mcMechanism_payment_of_notMem hi]

/-- **`mcMechanism` never runs a budget surplus** ([MoulinShenker2001];
[FeigenbaumPapadimitriouShenker2001]): for every real bid profile `b`, total VCG payments are at
most `cost (mcReceivers b)` (so `MC` either breaks even or incurs a budget deficit). -/
theorem mcMechanism_payment_sum_le_cost (b : A → ℝ) :
    ∑ i ∈ M.mcMechanism.serviced b, M.mcMechanism.payment b i ≤
      M.toCostSharingGame.cost (M.mcMechanism.serviced b) := by
  set R := M.mcReceivers b
  have hex : ∀ i : A, ∃ T : Finset A, i ∉ T ∧ T ⊆ R ∧
      M.netWelfare b T = M.maxNetWelfareWithout b i := fun i => by
    obtain ⟨W, hW_mem, hW_eq⟩ := Finset.exists_mem_eq_sup'
      (s := Finset.univ.filter fun S : Finset A => i ∉ S) ⟨∅, by simp⟩ (M.netWelfare b)
    have hiRW : i ∉ R ∩ W := fun h => (Finset.mem_filter.mp hW_mem).2 (Finset.mem_inter.mp h).2
    have hsup := M.netWelfare_supermodular b R W
    have hRU := (M.isGreatest_isWelfareMaximizingSet_mcReceivers b).1 (R ∪ W)
    refine ⟨R ∩ W, hiRW, Finset.inter_subset_left,
      le_antisymm (M.netWelfare_le_maxNetWelfareWithout hiRW) ?_⟩
    unfold maxNetWelfareWithout
    linarith [hW_eq]
  choose T hTi hTR hTeq using hex
  have hgap : ∀ S : Finset A,
      M.netWelfare b R - M.netWelfare b (R.filter fun x => ∀ i ∈ S, x ∈ T i) ≤
        ∑ i ∈ S, (M.netWelfare b R - M.netWelfare b (T i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hjS ih =>
      let IS := R.filter fun x => ∀ i ∈ S, x ∈ T i
      have hflt : (R.filter fun x => ∀ i ∈ insert j S, x ∈ T i) = T j ∩ IS := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp, Finset.mem_inter, IS]
        exact ⟨fun ⟨_, hTj, hall⟩ => ⟨hTj, hTR j hTj, hall⟩,
          fun ⟨hTj, hxR, hall⟩ => ⟨hxR, hTj, hall⟩⟩
      rw [hflt, Finset.sum_insert hjS]
      have := M.netWelfare_supermodular b (T j) IS
      have := (M.isGreatest_isWelfareMaximizingSet_mcReceivers b).1 (T j ∪ IS)
      linarith
  have hempty : (R.filter fun x => ∀ i ∈ R, x ∈ T i) = ∅ :=
    Finset.eq_empty_of_forall_notMem fun x hx =>
      let ⟨hxR, hall⟩ := Finset.mem_filter.mp hx
      hTi x (hall x hxR)
  have hmain := hgap R
  rw [hempty, M.netWelfare_empty, sub_zero] at hmain
  have hpay_sum : ∑ i ∈ R, M.mcMechanism.payment b i =
      (∑ i ∈ R, b i) - ∑ i ∈ R, (M.netWelfare b R - M.netWelfare b (T i)) :=
    calc ∑ i ∈ R, M.mcMechanism.payment b i
        = ∑ i ∈ R, (b i - (M.netWelfare b R - M.netWelfare b (T i))) :=
          Finset.sum_congr rfl fun i hi => by rw [M.mcMechanism_payment_of_mem hi, ← hTeq i]; ring
      _ = (∑ i ∈ R, b i) - ∑ i ∈ R, (M.netWelfare b R - M.netWelfare b (T i)) :=
          Finset.sum_sub_distrib _ _
  change ∑ i ∈ R, M.mcMechanism.payment b i ≤ M.toCostSharingGame.cost R
  have hnwR : M.netWelfare b R = (∑ i ∈ R, b i) - M.toCostSharingGame.cost R := rfl
  linarith

/-- **Pass 2 allocation correctness** ([FeigenbaumPapadimitriouShenker2001];
[FeigenbaumSchapiraShenker2007]): on nonnegative bid
profiles, `twoPassReceivers b` equals the unique largest welfare-maximizing receiver set
`mcReceivers b`. -/
theorem twoPassReceivers_eq_mcReceivers {b : A → ℝ} (hb : ∀ i, 0 ≤ b i) :
    M.twoPassReceivers b = M.mcReceivers b := by
  have hmax_twoPass : M.IsWelfareMaximizingSet b (M.twoPassReceivers b) := by
    rw [M.isWelfareMaximizingSet_iff_eq_maxNetWelfare, ← M.nodeWelfare_root_eq_maxNetWelfare hb,
      ← M.localNetWelfare_root, ← M.subtreeSurplus_root]
    exact M.localNetWelfare_twoPassReceivers_eq_subtreeSurplus hb
      M.tree.root (M.topDownActive_root b)
  refine le_antisymm ((M.isGreatest_isWelfareMaximizingSet_mcReceivers b).2 hmax_twoPass)
    fun i hi => ?_
  by_contra hnot
  have hnot_all : ¬ ∀ w, M.tree.IsAncestor w (M.loc i) → w ≠ M.tree.root →
      0 ≤ M.subtreeSurplus b w :=
    mt (M.topDownActive_eq_true_iff b (M.loc i)).mpr (by simpa [twoPassReceivers] using hnot)
  push Not at hnot_all
  obtain ⟨w, hwi, _, hsurp_neg⟩ := hnot_all
  set R := M.mcReceivers b
  let R' := R.filter fun j => M.loc j ∉ M.tree.subtreeNodes w
  let R_in := R.filter fun j => M.loc j ∈ M.tree.subtreeNodes w
  have hi_in : i ∈ R_in := Finset.mem_filter.mpr ⟨hi, M.tree.mem_subtreeNodes.mpr hwi⟩
  have hsum_R : ∑ j ∈ R, b j = (∑ j ∈ R_in, b j) + ∑ j ∈ R', b j :=
    (Finset.sum_filter_add_sum_filter_not R _ b).symm
  have hcost_diff :
      (∑ v ∈ M.tree.subtreeNodes w,
          if ∃ j ∈ R_in, M.tree.IsAncestor v (M.loc j) then M.edgeCost v else 0) ≤
        M.toCostSharingGame.cost R - M.toCostSharingGame.cost R' := by
    rw [M.toCostSharingGame_cost_eq_sum R, M.toCostSharingGame_cost_eq_sum R',
      ← Finset.sum_sub_distrib, ← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun v => v ∈ M.tree.subtreeNodes w), Finset.filter_univ_mem]
    have hin_eq : ∀ v ∈ M.tree.subtreeNodes w,
        (if ∃ j ∈ R, M.tree.IsAncestor v (M.loc j) then M.edgeCost v else 0) -
          (if ∃ j ∈ R', M.tree.IsAncestor v (M.loc j) then M.edgeCost v else 0) =
        if ∃ j ∈ R_in, M.tree.IsAncestor v (M.loc j) then M.edgeCost v else 0 := fun v hv => by
      have hvw := M.tree.mem_subtreeNodes.mp hv
      have hno_R' : ¬ ∃ j ∈ R', M.tree.IsAncestor v (M.loc j) := fun ⟨j, hj, hvj⟩ =>
        (Finset.mem_filter.mp hj).2 (M.tree.mem_subtreeNodes.mpr (hvw.trans hvj))
      have hiff : (∃ j ∈ R, M.tree.IsAncestor v (M.loc j)) ↔
          ∃ j ∈ R_in, M.tree.IsAncestor v (M.loc j) :=
        ⟨fun ⟨j, hj, hvj⟩ => ⟨j, Finset.mem_filter.mpr
            ⟨hj, M.tree.mem_subtreeNodes.mpr (hvw.trans hvj)⟩, hvj⟩,
         fun ⟨j, hj, hvj⟩ => ⟨j, (Finset.mem_filter.mp hj).1, hvj⟩⟩
      simp [hno_R', hiff]
    have hout_nn : 0 ≤ ∑ v ∈ Finset.univ.filter (fun v => v ∉ M.tree.subtreeNodes w),
        ((if ∃ j ∈ R, M.tree.IsAncestor v (M.loc j) then M.edgeCost v else 0) -
          (if ∃ j ∈ R', M.tree.IsAncestor v (M.loc j) then M.edgeCost v else 0)) :=
      Finset.sum_nonneg fun v _ => by
        by_cases hR' : ∃ j ∈ R', M.tree.IsAncestor v (M.loc j)
        · let ⟨j, hj, hvj⟩ := hR'
          have hR : ∃ k ∈ R, M.tree.IsAncestor v (M.loc k) := ⟨j, (Finset.mem_filter.mp hj).1, hvj⟩
          simp [hR, hR']
        · simp only [hR', ↓reduceIte, sub_zero]
          split_ifs
          · exact M.edgeCost_nonneg v
          · exact le_rfl
    rw [Finset.sum_congr rfl hin_eq]; linarith
  have hloc_le := (M.localNetWelfare_le_subtreeSurplus_and_upMsg hb w R).1 ⟨i, hi_in⟩
  have hmax_R := (M.isGreatest_isWelfareMaximizingSet_mcReceivers b).1 R'
  simp only [netWelfare, localNetWelfare, R_in] at hcost_diff hsum_R hloc_le hmax_R
  linarith

/-- **Pass 2 payment correctness** ([FeigenbaumPapadimitriouShenker2001];
[FeigenbaumSchapiraShenker2007]): on nonnegative bid
profiles, `twoPassPayment b` equals `mcMechanism.payment b`. -/
theorem twoPassPayment_eq_mcMechanism_payment {b : A → ℝ} (hb : ∀ j, 0 ≤ b j) (i : A) :
    M.twoPassPayment b i = M.mcMechanism.payment b i := by
  have hserv := M.twoPassReceivers_eq_mcReceivers hb
  by_cases hact : M.topDownActive b (M.loc i) = true
  · have hi_mc : i ∈ M.mcReceivers b := hserv ▸ M.mem_twoPassReceivers.mpr hact
    let b' := Function.update b i 0
    have hb' : ∀ j, 0 ≤ b' j := fun j => by
      by_cases h : j = i <;> simp [b', h, hb j]
    have hnw_eq : ∀ R, i ∉ R → M.netWelfare b' R = M.netWelfare b R := fun R hiR => by
      simp only [netWelfare]
      congr 1
      exact Finset.sum_congr rfl fun j hj =>
        Function.update_of_ne (fun h : j = i => hiR (h ▸ hj)) 0 b
    have hwithout : M.maxNetWelfareWithout b i = M.maxNetWelfare b' := by
      classical
      refine le_antisymm (Finset.sup'_le _ _ fun R hR =>
          (hnw_eq R (Finset.mem_filter.mp hR).2) ▸ M.netWelfare_le_maxNetWelfare b' R)
        (Finset.sup'_le _ _ fun R _ => ?_)
      by_cases hiR : i ∈ R
      · refine le_trans ?_ (M.netWelfare_le_maxNetWelfareWithout (Finset.notMem_erase i R))
        have hsum : ∑ j ∈ R, b' j = ∑ j ∈ R.erase i, b j := by
          rw [← Finset.sum_erase_add _ _ hiR]
          simp only [b', Function.update_self, add_zero]
          exact Finset.sum_congr rfl fun j hj =>
            Function.update_of_ne (Finset.ne_of_mem_erase hj) 0 b
        have := M.toCostSharingGame_mono (Finset.erase_subset i R)
        simp only [netWelfare]; linarith
      · exact (hnw_eq R hiR) ▸ M.netWelfare_le_maxNetWelfareWithout hiR
    have hoff : ∀ v : V, ¬ M.tree.IsAncestor v (M.loc i) → M.upMsg b' v = M.upMsg b v := by
      suffices hrec : ∀ rem v, M.tree.maxDepth + 1 - M.tree.depth v ≤ rem →
          ¬ M.tree.IsAncestor v (M.loc i) → M.upMsg b' v = M.upMsg b v from fun v => hrec _ v le_rfl
      intro rem
      induction rem with
      | zero =>
        intro v hrem
        have := M.tree.depth_le_maxDepth v
        omega
      | succ rem ih =>
        intro v hrem hnot_anc
        have hres : (∑ j : A with M.loc j = v, max (b' j) 0) =
            ∑ j : A with M.loc j = v, max (b j) 0 :=
          Finset.sum_congr rfl fun j hj => by
            have hji : j ≠ i := fun h =>
              hnot_anc ((h ▸ (Finset.mem_filter.mp hj).2) ▸ M.tree.isAncestor_refl _)
            simp [b', Function.update_of_ne hji]
        have hch : ∑ c ∈ M.tree.children v, M.upMsg b' c = ∑ c ∈ M.tree.children v, M.upMsg b c :=
          Finset.sum_congr rfl fun c hc => by
            have := M.tree.depth_of_mem_children hc
            have := M.tree.depth_le_maxDepth c
            have huc : M.tree.IsAncestor v c :=
              (M.tree.mem_children.mp hc).2 ▸ M.tree.isAncestor_parent_self c
            exact ih c (by omega) fun hci => hnot_anc (huc.trans hci)
        rw [upMsg, upMsg, subtreeSurplus, subtreeSurplus,
          M.nodeWelfare_eq b' v, M.nodeWelfare_eq b v, hres, hch]
    have hclamp : ∀ s δ : ℝ, 0 ≤ s → max 0 (s - δ) = s - min δ s := fun s δ hs => by
      rcases le_total δ s with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]
      · rw [min_eq_right h, max_eq_left (by linarith), sub_self]
    let upDrop : ℕ → ℝ := fun k =>
      Nat.rec (b i) (fun r acc => min acc (M.subtreeSurplus b (M.tree.parent^[r] (M.loc i)))) k
    have hup_nw : ∀ k : ℕ, k ≤ M.tree.depth (M.loc i) →
        M.nodeWelfare b' (M.tree.parent^[k] (M.loc i)) =
          M.nodeWelfare b (M.tree.parent^[k] (M.loc i)) - upDrop k := by
      intro k
      induction k with
      | zero =>
        intro _
        simp only [Function.iterate_zero_apply, M.nodeWelfare_eq]
        have hch : ∑ c ∈ M.tree.children (M.loc i), M.upMsg b' c =
            ∑ c ∈ M.tree.children (M.loc i), M.upMsg b c :=
          Finset.sum_congr rfl fun c hc => hoff c fun hci => by
            have := M.tree.depth_of_mem_children hc
            have := hci.depth_le
            omega
        let Floc := Finset.univ.filter fun j : A => M.loc j = M.loc i
        have hi_mem : i ∈ Floc := by simp [Floc]
        have hsum_b' : ∑ j ∈ Floc, max (b' j) 0 = (∑ j ∈ Floc, max (b j) 0) - b i := by
          rw [← Finset.sum_erase_add _ _ hi_mem,
            ← Finset.sum_erase_add _ (fun j => max (b j) 0) hi_mem, max_eq_left (hb i)]
          have hcongr : ∑ j ∈ Floc.erase i, max (b' j) 0 = ∑ j ∈ Floc.erase i, max (b j) 0 :=
            Finset.sum_congr rfl fun j hj => by
              simp [b', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
          rw [hcongr]
          simp [b']
        change (∑ j ∈ Floc, max (b' j) 0) + _ = ((∑ j ∈ Floc, max (b j) 0) + _) - b i
        rw [hch, hsum_b']; ring
      | succ k ih =>
        intro hk
        set w := M.tree.parent^[k] (M.loc i)
        have hdw : M.tree.depth w = M.tree.depth (M.loc i) - k := M.tree.depth_iterate_parent k _
        have hw_ne : w ≠ M.tree.root := fun hr => by rw [hr, M.tree.depth_root] at hdw; omega
        have hwi : M.tree.IsAncestor w (M.loc i) := ⟨k, rfl⟩
        have hsw_nn : 0 ≤ M.subtreeSurplus b w :=
          ((M.topDownActive_eq_true_iff b (M.loc i)).mp hact) w hwi hw_ne
        have hw_child : w ∈ M.tree.children (M.tree.parent w) :=
          M.tree.mem_children.mpr ⟨hw_ne, rfl⟩
        have hup_w : M.upMsg b' w = M.upMsg b w - min (upDrop k) (M.subtreeSurplus b w) := by
          have hsurp' : M.subtreeSurplus b' w = M.subtreeSurplus b w - upDrop k := by
            simp only [subtreeSurplus, ih (by omega)]; ring
          rw [upMsg, hsurp', hclamp _ _ hsw_nn, upMsg, max_eq_right hsw_nn]
        rw [Function.iterate_succ_apply', M.nodeWelfare_eq b' (M.tree.parent w),
          M.nodeWelfare_eq b (M.tree.parent w)]
        have hres : (∑ j : A with M.loc j = M.tree.parent w, max (b' j) 0) =
            ∑ j : A with M.loc j = M.tree.parent w, max (b j) 0 :=
          Finset.sum_congr rfl fun j hj => by
            have hji : j ≠ i := fun h => by
              have := M.tree.depth_parent_lt hw_ne
              have hle := hwi.depth_le
              rw [← h, (Finset.mem_filter.mp hj).2] at hle; omega
            simp [b', Function.update_of_ne hji]
        have hch_other : ∑ c ∈ (M.tree.children (M.tree.parent w)).erase w, M.upMsg b' c =
            ∑ c ∈ (M.tree.children (M.tree.parent w)).erase w, M.upMsg b c :=
          Finset.sum_congr rfl fun c hc => hoff c fun hci => by
            obtain ⟨hcw, hc_ch⟩ := Finset.mem_erase.mp hc
            exact Finset.disjoint_left.mp
              (M.tree.pairwiseDisjoint_children_subtreeNodes _ hc_ch hw_child hcw)
              (M.tree.mem_subtreeNodes.mpr hci) (M.tree.mem_subtreeNodes.mpr hwi)
        rw [hres, ← Finset.sum_erase_add _ (M.upMsg b') hw_child,
          ← Finset.sum_erase_add _ (M.upMsg b) hw_child, hch_other, hup_w]
        change _ = _ - min (upDrop k) (M.subtreeSurplus b w)
        ring
    have hshift : ∀ (m : ℕ) (u : V) (x : ℝ),
        min (Nat.rec x (fun r acc =>
            min acc (M.subtreeSurplus b (M.tree.parent^[r] (M.tree.parent u)))) m)
          (M.subtreeSurplus b u) =
        Nat.rec x (fun r acc => min acc (M.subtreeSurplus b (M.tree.parent^[r] u))) (m + 1) := by
      intro m
      induction m with
      | zero =>
        intro _ _
        rfl
      | succ m ihm =>
        intro u x
        change min (min _ _) _ = min _ (M.subtreeSurplus b (M.tree.parent^[m + 1] u))
        rw [Function.iterate_succ_apply M.tree.parent m u, ← ihm u x, min_assoc,
          min_comm (M.subtreeSurplus b _), ← min_assoc]
    have hthresh_eq : ∀ d : ℕ, ∀ u : V, M.tree.depth u = d →
        (match M.topDownThreshold b u with | none => b i | some m => min (b i) m) =
          Nat.rec (b i) (fun r acc => min acc (M.subtreeSurplus b (M.tree.parent^[r] u))) d := by
      intro d
      induction d with
      | zero =>
        intro u hd
        rw [M.tree.depth_eq_zero_iff.mp hd, M.topDownThreshold_root]; rfl
      | succ d ih =>
        intro u hd
        have hu_ne : u ≠ M.tree.root := fun hr => by rw [hr, M.tree.depth_root] at hd; omega
        rw [M.topDownThreshold_of_ne_root b hu_ne]
        have ihp := ih (M.tree.parent u) (by have := M.tree.depth_parent u; omega)
        rw [← hshift d u (b i), ← ihp]
        cases M.topDownThreshold b (M.tree.parent u)
        · rfl
        · exact (min_assoc _ _ _).symm
    have hroot_nw := hup_nw (M.tree.depth (M.loc i)) le_rfl
    rw [M.tree.parent_iter_depth] at hroot_nw
    have hdrop_match := hthresh_eq (M.tree.depth (M.loc i)) (M.loc i) rfl
    rw [M.mcMechanism_payment_of_mem hi_mc, hwithout,
      ← M.nodeWelfare_root_eq_maxNetWelfare hb', M.netWelfare_mcReceivers,
      ← M.nodeWelfare_root_eq_maxNetWelfare hb, hroot_nw]
    simp only [twoPassPayment, hact, ↓reduceIte]
    dsimp only [upDrop] at hdrop_match ⊢
    rw [← hdrop_match]
    cases M.topDownThreshold b (M.loc i) with
    | none => ring
    | some m =>
      dsimp only
      rw [hclamp (b i) m (hb i), min_comm]
      ring
  · have hi_not : i ∉ M.mcReceivers b := by simpa [← hserv] using hact
    simp [twoPassPayment, hact, M.mcMechanism_payment_of_notMem hi_not]

end FiniteAgents

end MarginalCost

end MulticastInstance

/-! ## 4. Single-link public good: GSP failure of `MC`, impossibility, and `(H_n - 1) C` bound -/

/-- Canonical **single-link multicast instance** (an excludable public good of cost `C ≥ 0`): root
`false`, link `(false, true)` of cost `C`, with all receivers `A` located at `true`. -/
def singleLinkMulticast (A : Type*) (C : ℝ) (hC : 0 ≤ C) : MulticastInstance Bool A where
  tree :=
    { root := false
      parent := fun _ => false
      parent_root := rfl
      reaches_root := fun _ => ⟨1, rfl⟩ }
  edgeCost b := if b then C else 0
  edgeCost_root := rfl
  edgeCost_nonneg b := by cases b <;> [exact le_rfl; exact hC]
  loc _ := true

@[simp]
theorem singleLinkMulticast_cost {A : Type*} (C : ℝ) (hC : 0 ≤ C) (R : Finset A) :
    (singleLinkMulticast A C hC).toCostSharingGame.cost R = if R.Nonempty then C else 0 := by
  rw [MulticastInstance.toCostSharingGame_cost]
  rcases R.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp [MulticastInstance.activeLinks, singleLinkMulticast]
  · have hne : R.Nonempty := ⟨i, hi⟩
    have hact : (singleLinkMulticast A C hC).activeLinks R = {true} := by
      ext b
      cases b
      · simp [MulticastInstance.mem_activeLinks, singleLinkMulticast]
      · simp only [MulticastInstance.mem_activeLinks, Finset.mem_singleton, iff_true]
        exact ⟨fun h => Bool.noConfusion h, i, hi, 0, rfl⟩
    rw [hact, Finset.sum_singleton]
    simp [hne, singleLinkMulticast]

theorem singleLinkMulticast_shShare {A : Type*} [DecidableEq A] (C : ℝ) (hC : 0 ≤ C)
    (R : Finset A) (i : A) :
    (singleLinkMulticast A C hC).shShare R i = if i ∈ R then C / (R.card : ℝ) else 0 := by
  rw [MulticastInstance.shShare_apply]
  by_cases hi : i ∈ R
  · have hanc (j : A) : (singleLinkMulticast A C hC).tree.IsAncestor true
        ((singleLinkMulticast A C hC).loc j) := ⟨0, rfl⟩
    simp only [hi, ↓reduceIte, Finset.sum_filter, Fintype.sum_bool]
    rw [ite_eq_left (hanc i), Finset.filter_true_of_mem fun j _ => hanc j]
    simp [singleLinkMulticast]
  · simp [hi]

private theorem sum_le_of_eq_zero_outside {α : Type*} {S T : Finset α}
    {f : α → ℝ} (h0 : ∀ x ∈ S, x ∉ T → f x = 0) (hnn : ∀ x ∈ T, 0 ≤ f x) :
    ∑ x ∈ S, f x ≤ ∑ x ∈ T, f x := by
  classical
  calc ∑ x ∈ S, f x = ∑ x ∈ S ∩ T, f x :=
        (Finset.sum_subset Finset.inter_subset_left fun x hx h =>
          h0 x hx fun hxT => h (Finset.mem_inter.mpr ⟨hx, hxT⟩)).symm
    _ ≤ ∑ x ∈ T, f x :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun x hx _ => hnn x hx

/-- **`mcMechanism` is NOT group-strategyproof** ([FeigenbaumPapadimitriouShenker2001];
[FeigenbaumSchapiraShenker2007]): on a single link of positive cost
`C > 0` with at least two receivers, two receivers with true valuations `C / 3` each get utility `0`
under truthful reporting (`2C / 3 < C`), whereas jointly bidding `2C` causes both to be served at
VCG payment `0` (strictly positive utility `C / 3 > 0` each). -/
theorem not_mcMechanism_isGroupStrategyproof_singleLink {A : Type*} [Fintype A] [DecidableEq A]
    (hcard : 2 ≤ Fintype.card A) {C : ℝ} (hC : 0 < C) :
    ¬ (singleLinkMulticast A C hC.le).mcMechanism.IsGroupStrategyproof := by
  rw [CostSharingMechanism.isGroupStrategyproof_iff_not_beneficial]
  push Not
  obtain ⟨i₀, i₁, hne⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card A)
  let I := singleLinkMulticast A C hC.le
  let u : A → ℝ := fun k => if k = i₀ ∨ k = i₁ then C / 3 else 0
  let z : A → ℝ := fun _ => 2 * C
  let pair : Finset A := {i₀, i₁}
  have hpair_ne : pair.Nonempty := ⟨i₀, by simp [pair]⟩
  have hserv_u : I.mcReceivers u = ∅ := by
    rcases (I.mcReceivers u).eq_empty_or_nonempty with hemp | hRne
    · exact hemp
    · have hle : ∑ k ∈ I.mcReceivers u, u k ≤ 2 * C / 3 :=
        calc ∑ k ∈ I.mcReceivers u, u k
            ≤ ∑ k ∈ pair, u k :=
              sum_le_of_eq_zero_outside
                (fun k _ hk => by
                  simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hk
                  simp [u, hk])
                (fun k _ => by
                  dsimp [u]
                  split_ifs <;> linarith)
          _ = 2 * C / 3 := by
              rw [Finset.sum_pair hne]
              simp only [u, true_or, or_true, ↓reduceIte]
              ring
      have hge := I.maxNetWelfare_nonneg u
      rw [← I.netWelfare_mcReceivers u, MulticastInstance.netWelfare_apply,
        singleLinkMulticast_cost] at hge
      simp only [hRne, ↓reduceIte] at hge; linarith
  let b' := pair.piecewise z u
  have hb'_in : ∀ k ∈ pair, b' k = 2 * C := fun k hk => by
    simp [b', Finset.piecewise_eq_of_mem _ _ _ hk, z]
  have hb'_out : ∀ k ∉ pair, b' k = 0 := fun k hk => by
    have hk_ne : ¬ (k = i₀ ∨ k = i₁) := by simpa [pair] using hk
    simp [b', Finset.piecewise_eq_of_notMem _ _ _ hk, u, hk_ne]
  have hb'_nn : ∀ k, 0 ≤ b' k := fun k => by
    by_cases hp : k ∈ pair
    · rw [hb'_in k hp]; linarith
    · rw [hb'_out k hp]
  have hnw_pair : I.netWelfare b' pair = 3 * C := by
    rw [MulticastInstance.netWelfare_apply, singleLinkMulticast_cost,
      Finset.sum_pair hne, hb'_in i₀ (by simp [pair]), hb'_in i₁ (by simp [pair])]
    simp only [hpair_ne, ↓reduceIte]; ring
  have hpair_max : I.IsWelfareMaximizingSet b' pair := fun S => by
    rw [hnw_pair, MulticastInstance.netWelfare_apply, singleLinkMulticast_cost]
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · simp; linarith
    · simp only [hSne, ↓reduceIte]
      have hle : ∑ k ∈ S, b' k ≤ 4 * C :=
        calc ∑ k ∈ S, b' k
            ≤ ∑ k ∈ pair, b' k :=
              sum_le_of_eq_zero_outside (fun k _ hk => hb'_out k hk) fun k _ => hb'_nn k
          _ = 4 * C := by
              rw [Finset.sum_pair hne, hb'_in i₀ (by simp [pair]), hb'_in i₁ (by simp [pair])]
              ring
      linarith
  have hpair_sub : pair ⊆ I.mcReceivers b' :=
    (I.isGreatest_isWelfareMaximizingSet_mcReceivers b').2 hpair_max
  have hpay_zero : ∀ k ∈ pair, I.mcMechanism.payment b' k = 0 := fun k hk => by
    rw [I.mcMechanism_payment_of_mem (hpair_sub hk)]
    obtain ⟨other, hother_pair, hother_ne⟩ : ∃ m ∈ pair, m ≠ k := by
      rcases Finset.mem_insert.mp hk with rfl | hk1
      · exact ⟨i₁, by simp [pair], hne.symm⟩
      · exact ⟨i₀, by simp [pair], (Finset.mem_singleton.mp hk1) ▸ hne⟩
    have hnw_b' : I.netWelfare b' (I.mcReceivers b') = 3 * C := by
      rw [I.netWelfare_mcReceivers, ← I.isWelfareMaximizingSet_iff_eq_maxNetWelfare.mp hpair_max,
        hnw_pair]
    have hge_without : C ≤ I.maxNetWelfareWithout b' k := by
      refine le_trans ?_ (I.netWelfare_le_maxNetWelfareWithout
        (R := {other}) (Finset.notMem_singleton.mpr hother_ne.symm))
      rw [MulticastInstance.netWelfare_apply, singleLinkMulticast_cost,
        Finset.sum_singleton, hb'_in other hother_pair]
      simp only [Finset.singleton_nonempty, ↓reduceIte]; linarith
    have hle_without : I.maxNetWelfareWithout b' k ≤ C := Finset.sup'_le _ _ fun R hR => by
      have hkR : k ∉ R := (Finset.mem_filter.mp hR).2
      rw [MulticastInstance.netWelfare_apply, singleLinkMulticast_cost]
      rcases R.eq_empty_or_nonempty with rfl | hRne
      · simp [hC.le]
      · simp only [hRne, ↓reduceIte]
        have hsum_le : ∑ x ∈ R, b' x ≤ 2 * C :=
          calc ∑ x ∈ R, b' x
              ≤ ∑ x ∈ ({other} : Finset A), b' x :=
                sum_le_of_eq_zero_outside (fun x hxR hxo => hb'_out x fun hxp => by
                  simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hxp hother_pair hk
                  simp only [Finset.mem_singleton] at hxo
                  rcases hxp with rfl | rfl <;> rcases hother_pair with rfl | rfl <;>
                    rcases hk with rfl | rfl <;>
                      first | exact hxo rfl | exact hkR hxR | exact hother_ne rfl)
                  fun x _ => hb'_nn x
            _ = 2 * C := by rw [Finset.sum_singleton, hb'_in other hother_pair]
        linarith
    rw [le_antisymm hle_without hge_without, hnw_b', hb'_in k hk]; ring
  have hutil_u : ∀ k ∈ pair, I.mcMechanism.utility u u k = 0 := fun k _ => by
    have hk_not : k ∉ I.mcReceivers u := by simp [hserv_u]
    rw [CostSharingMechanism.utility_eq]
    simp [hserv_u, I.mcMechanism_payment_of_notMem hk_not]
  have hutil_b' : ∀ k ∈ pair, I.mcMechanism.utility u b' k = C / 3 := fun k hk => by
    have huk : u k = C / 3 := by
      simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hk
      simp [u, hk]
    rw [CostSharingMechanism.utility_eq]
    simp [hpair_sub hk, hpay_zero k hk, huk]
  refine ⟨u, z, pair, fun k hk => by rw [hutil_u k hk, hutil_b' k hk]; linarith,
    i₀, by simp [pair], by rw [hutil_u i₀ (by simp [pair]), hutil_b' i₀ (by simp [pair])]; linarith⟩

/-- **Impossibility of DSIC + exact budget balance + welfare maximization** ([MoulinShenker2001];
Green–Laffont): on `singleLinkMulticast` with `|A| ≥ 2` receivers and link cost `C > 0`, no
mechanism `M` satisfies `IsDSIC`, `VoluntaryParticipation`, `NoPositiveTransfers`,
`1`-budget balance, and net-welfare maximization on nonnegative bid profiles. -/
theorem not_exists_dsic_budgetBalanced_welfareMaximizing_singleLink
    {A : Type*} [Fintype A] [DecidableEq A] (hcard : 2 ≤ Fintype.card A) {C : ℝ} (hC : 0 < C) :
    ¬ ∃ M : CostSharingMechanism A,
      M.toSingleParameterMechanism.IsDSIC ∧
      M.VoluntaryParticipation ∧
      M.NoPositiveTransfers ∧
      M.IsBudgetBalanced (singleLinkMulticast A C hC.le).toCostSharingGame 1 ∧
      ∀ b : A → ℝ, (∀ k, 0 ≤ b k) →
        (singleLinkMulticast A C hC.le).IsWelfareMaximizingSet b (M.serviced b) := by
  rintro ⟨M, hdsic, hvp, hnpt, hbb, heff⟩
  obtain ⟨i₀, i₁, hne⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card A)
  let I := singleLinkMulticast A C hC.le
  let bHigh : A → ℝ := fun k => if k = i₀ ∨ k = i₁ then 3 * C / 4 else 0
  have hbHigh_nn : 0 ≤ bHigh := fun k => by dsimp [bHigh]; split_ifs <;> linarith
  have hserv_ne : (M.serviced bHigh).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h := heff bHigh hbHigh_nn {i₀, i₁}
    rw [hemp, I.netWelfare_empty, MulticastInstance.netWelfare_apply, singleLinkMulticast_cost,
      Finset.sum_pair hne] at h
    simp only [show ({i₀, i₁} : Finset A).Nonempty from ⟨i₀, by simp⟩,
      bHigh, true_or, or_true, ↓reduceIte] at h
    linarith
  have hpay_zero_out : ∀ k, k ≠ i₀ → k ≠ i₁ → M.payment bHigh k = 0 := fun k hk0 hk1 => by
    by_cases hk : k ∈ M.serviced bHigh
    · exact le_antisymm ((hvp.2 bHigh k hk).trans_eq (by simp [bHigh, hk0, hk1])) (hnpt bHigh k)
    · exact hvp.1 bHigh k hk
  have hpay_le_third : ∀ m o : A, m ≠ o → (m = i₀ ∧ o = i₁ ∨ m = i₁ ∧ o = i₀) →
      M.payment bHigh m ≤ C / 3 := fun m o hmo hpair => by
    let bLow : A → ℝ := Function.update bHigh m (C / 3)
    have hbLow_nn : 0 ≤ bLow := fun k => by
      rcases eq_or_ne k m with rfl | hkm
      · simp [bLow]; linarith
      · simpa [bLow, Function.update_of_ne hkm] using hbHigh_nn k
    have hm_bLow : bLow m = C / 3 := Function.update_self m (C / 3) bHigh
    have ho_bLow : bLow o = 3 * C / 4 := by
      dsimp only [bLow]
      rw [Function.update_of_ne hmo.symm]
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [bHigh]
    have hm_in_low : m ∈ M.serviced bLow := by
      by_contra hm_not
      have hmax_low := heff bLow hbLow_nn {m, o}
      rw [MulticastInstance.netWelfare_apply, singleLinkMulticast_cost, Finset.sum_pair hmo,
        hm_bLow, ho_bLow, MulticastInstance.netWelfare_apply, singleLinkMulticast_cost] at hmax_low
      simp only [show ({m, o} : Finset A).Nonempty from ⟨m, by simp⟩, ↓reduceIte] at hmax_low
      rcases (M.serviced bLow).eq_empty_or_nonempty with hemp | hSne
      · simp [hemp] at hmax_low; linarith
      · simp only [hSne, ↓reduceIte] at hmax_low
        have hsum_le : ∑ k ∈ M.serviced bLow, bLow k ≤ 3 * C / 4 :=
          calc ∑ k ∈ M.serviced bLow, bLow k
              ≤ ∑ k ∈ ({o} : Finset A), bLow k :=
                sum_le_of_eq_zero_outside (fun k hkS hko => by
                  have hkm : k ≠ m := fun h => hm_not (h ▸ hkS)
                  dsimp only [bLow]
                  rw [Function.update_of_ne hkm]
                  have hko' : k ≠ o := Finset.notMem_singleton.mp hko
                  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [bHigh, hkm, hko'])
                  fun k _ => hbLow_nn k
            _ = 3 * C / 4 := by rw [Finset.sum_singleton, ho_bLow]
        linarith
    have hpay_low : M.payment bLow m ≤ C / 3 := (hvp.2 bLow m hm_in_low).trans_eq hm_bLow
    have hupd_high : Function.update bLow m (3 * C / 4) = bHigh := by
      ext k
      rcases eq_or_ne k m with rfl | hkm
      · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [bLow, bHigh]
      · simp [bLow, Function.update_of_ne hkm]
    by_cases hm_in_high : m ∈ M.serviced bHigh
    · have hdsic_step := hdsic m bLow (3 * C / 4) hbLow_nn (by positivity)
      rw [hupd_high] at hdsic_step
      simp [SingleParameter.Mechanism.utility, hm_in_low, hm_in_high] at hdsic_step
      linarith
    · rw [hvp.1 bHigh m hm_in_high]; positivity
  have hp0 := hpay_le_third i₀ i₁ hne (Or.inl ⟨rfl, rfl⟩)
  have hp1 := hpay_le_third i₁ i₀ hne.symm (Or.inr ⟨rfl, rfl⟩)
  have hbb_eq : ∑ k ∈ M.serviced bHigh, M.payment bHigh k = C := by
    obtain ⟨h1, h2⟩ := hbb bHigh
    rw [singleLinkMulticast_cost] at h1 h2
    simp only [hserv_ne, ↓reduceIte, one_mul] at h1 h2; linarith
  have hsum_le : ∑ k ∈ M.serviced bHigh, M.payment bHigh k ≤
      M.payment bHigh i₀ + M.payment bHigh i₁ :=
    calc ∑ k ∈ M.serviced bHigh, M.payment bHigh k
        ≤ ∑ k ∈ ({i₀, i₁} : Finset A), M.payment bHigh k :=
          sum_le_of_eq_zero_outside
            (fun k _ hk => by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
              exact hpay_zero_out k hk.1 hk.2)
            fun k _ => hnpt bHigh k
      _ = M.payment bHigh i₀ + M.payment bHigh i₁ := Finset.sum_pair hne
  linarith

private theorem sum_le_harmonic_sub_mul {A : Type*}
    {b : A → ℝ} {C : ℝ} (s : ℕ) :
    ∀ T : Finset A,
      (∀ U : Finset A, U.Nonempty → U ⊆ T → ∃ x ∈ U, b x ≤ C / ((s + U.card : ℕ) : ℝ)) →
      ∑ x ∈ T, b x ≤ ((harmonic (s + T.card) : ℝ) - (harmonic s : ℝ)) * C := by
  classical
  suffices hrec : ∀ m (T : Finset A), T.card = m →
      (∀ U : Finset A, U.Nonempty → U ⊆ T → ∃ x ∈ U, b x ≤ C / ((s + U.card : ℕ) : ℝ)) →
      ∑ x ∈ T, b x ≤ ((harmonic (s + m) : ℝ) - (harmonic s : ℝ)) * C from fun T => hrec _ T rfl
  intro m
  induction m with
  | zero =>
    intro T hc _
    rw [Finset.card_eq_zero.mp hc]
    simp
  | succ m ih =>
    intro T hc hpeel
    obtain ⟨x, hxT, hbx⟩ := hpeel T (Finset.card_pos.mp (by omega)) Subset.rfl
    have ih_er := ih (T.erase x) (by rw [Finset.card_erase_of_mem hxT, hc]; omega) fun U hU hUT =>
      hpeel U hU (hUT.trans (Finset.erase_subset x T))
    have hh : (harmonic (s + (m + 1)) : ℝ) = (harmonic (s + m) : ℝ) + ((s + m + 1 : ℕ) : ℝ)⁻¹ := by
      rw [show s + (m + 1) = (s + m) + 1 by omega, harmonic_succ]
      push_cast
      ring
    rw [hc, show s + (m + 1) = s + m + 1 by omega, div_eq_mul_inv, mul_comm] at hbx
    rw [← Finset.sum_erase_add _ _ hxT, hh]; linarith

/-- **Moulin–Shenker `(H_n - 1) C` welfare-loss upper bound** ([MoulinShenker2001]): on a single
excludable link of cost `C ≥ 0` with `n = Fintype.card A ≥ 1` receivers, `shMechanism` incurs
additive net-welfare loss at most `(H_n - 1) * C` relative to any coalition `R` on every
nonnegative bid profile `b`. -/
theorem netWelfare_sub_shMechanism_le_harmonic_sub_one
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    {C : ℝ} (hC : 0 ≤ C) {b : A → ℝ} (hb : ∀ i, 0 ≤ b i) (R : Finset A) :
    let I := singleLinkMulticast A C hC
    I.netWelfare b R - I.netWelfare b (I.shMechanism.serviced b) ≤
      ((harmonic (Fintype.card A) : ℝ) - 1) * C := by
  dsimp only
  set I := singleLinkMulticast A C hC
  rw [I.shMechanism_serviced]
  set S := I.shScheme.moulinServiced b
  have h1_le_hn : (1 : ℝ) ≤ (harmonic (Fintype.card A) : ℝ) := by
    exact_mod_cast one_le_harmonic Fintype.card_ne_zero
  have hgreat := I.shScheme.isGreatest_isWilling_moulinServiced I.shScheme_isCrossMonotone b
  have hS_willing : I.shScheme.IsWilling b S := hgreat.1
  rcases R.eq_empty_or_nonempty with rfl | hRne
  · have hnw_S_nn : 0 ≤ I.netWelfare b S := by
      rw [MulticastInstance.netWelfare_apply, singleLinkMulticast_cost]
      rcases S.eq_empty_or_nonempty with hemp | hSne
      · simp [hemp]
      · simp only [hSne, ↓reduceIte]
        have hsum : C ≤ ∑ i ∈ S, b i := by
          have hpos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hSne)
          calc C = ∑ _i ∈ S, (C / (S.card : ℝ)) := by
                rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hpos.ne']
            _ ≤ ∑ i ∈ S, b i := Finset.sum_le_sum fun i hi => by
                have hw := hS_willing i hi
                rw [MulticastInstance.shScheme_share, singleLinkMulticast_shShare] at hw
                simpa [hi] using hw
        linarith
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ (harmonic (Fintype.card A) : ℝ) - 1) hC
    rw [I.netWelfare_empty]; linarith
  · have hpeel : ∀ U : Finset A, U.Nonempty → U ⊆ R \ S →
        ∃ x ∈ U, b x ≤ C / ((S.card + U.card : ℕ) : ℝ) := fun U hUne hU_sub => by
      have hdisj : Disjoint S U :=
        Finset.disjoint_left.mpr fun x hxS hxU => (Finset.mem_sdiff.mp (hU_sub hxU)).2 hxS
      by_contra hall
      push Not at hall
      have hwSU : I.shScheme.IsWilling b (S ∪ U) := fun x hx => by
        rcases Finset.mem_union.mp hx with hxS | hxU
        · exact (I.shScheme_isCrossMonotone Finset.subset_union_left hxS).trans (hS_willing x hxS)
        · rw [MulticastInstance.shScheme_share, singleLinkMulticast_shShare]
          simp only [hx, ↓reduceIte, Finset.card_union_of_disjoint hdisj]
          exact (hall x hxU).le
      obtain ⟨u, huU⟩ := hUne
      exact (Finset.mem_sdiff.mp (hU_sub huU)).2 (hgreat.2 hwSU (Finset.mem_union_right S huU))
    have hsum_diff := sum_le_harmonic_sub_mul (b := b) (C := C) S.card (R \ S) hpeel
    have hcard_SR : S.card + (R \ S).card ≤ Fintype.card A := by
      rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff]
      exact Finset.card_le_univ _
    have hmono_SR : (harmonic (S.card + (R \ S).card) : ℝ) ≤ (harmonic (Fintype.card A) : ℝ) := by
      exact_mod_cast harmonic_mono hcard_SR
    rcases S.eq_empty_or_nonempty with hSemp | hSne
    · simp only [hSemp, Finset.sdiff_empty, Finset.card_empty, zero_add, harmonic_zero,
        Rat.cast_zero, sub_zero] at hsum_diff hmono_SR
      have := mul_le_mul_of_nonneg_right hmono_SR hC
      rw [hSemp, I.netWelfare_empty, sub_zero, MulticastInstance.netWelfare_apply,
        singleLinkMulticast_cost]
      simp only [hRne, ↓reduceIte]; linarith
    · have h1_le_hS : (1 : ℝ) ≤ (harmonic S.card : ℝ) := by
        exact_mod_cast one_le_harmonic (Finset.card_pos.mpr hSne).ne'
      have hdiff_nw : I.netWelfare b R - I.netWelfare b S ≤ ∑ x ∈ R \ S, b x := by
        rw [MulticastInstance.netWelfare_apply, MulticastInstance.netWelfare_apply,
          singleLinkMulticast_cost, singleLinkMulticast_cost]
        simp only [hRne, hSne, ↓reduceIte]
        have hR_split : ∑ x ∈ R, b x = (∑ x ∈ R \ S, b x) + ∑ x ∈ R ∩ S, b x := by
          rw [← Finset.sum_union (Finset.disjoint_sdiff_inter R S), Finset.sdiff_union_inter]
        have hS_ge : ∑ x ∈ R ∩ S, b x ≤ ∑ x ∈ S, b x :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun x _ _ => hb x
        linarith
      have := mul_le_mul_of_nonneg_right (by linarith :
        (harmonic (S.card + (R \ S).card) : ℝ) - (harmonic S.card : ℝ) ≤
          (harmonic (Fintype.card A) : ℝ) - 1) hC
      linarith

/-- **Moulin–Shenker minimax welfare-loss lower bound** ([MoulinShenker2001]): for **every**
`1`-budget-balanced cross-monotonic cost-sharing scheme `ξ` on `singleLinkMulticast` (`C > 0`,
`n = Fintype.card A ≥ 1`) and every `ε > 0`, there exists a nonnegative bid profile `b` on which
`ξ.moulinMechanism` suffers additive welfare loss strictly greater than `(H_n - 1) * C - ε`
(in fact returning `serviced b = ∅` while `netWelfare b univ > (H_n - 1) * C - ε`). -/
theorem exists_welfareLoss_gt_harmonic_sub_one
    {A : Type*} [Fintype A] [Nonempty A]
    {C : ℝ} (hC : 0 < C) {ξ : CostSharingScheme A}
    (hbb : ξ.IsBudgetBalanced (singleLinkMulticast A C hC.le).toCostSharingGame 1)
    (hcm : ξ.IsCrossMonotone) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : A → ℝ, (∀ i, 0 ≤ b i) ∧
      ((harmonic (Fintype.card A) : ℝ) - 1) * C - ε <
        (singleLinkMulticast A C hC.le).netWelfare b Finset.univ -
          (singleLinkMulticast A C hC.le).netWelfare b (ξ.moulinMechanism.serviced b) := by
  classical
  set n := Fintype.card A
  have hn_pos : 0 < n := Fintype.card_pos
  have hbb_eq := (ξ.isBudgetBalanced_one_iff _).mp hbb
  have hchain : ∀ r : ℕ, r ≤ n →
      ∃ (W : Finset A) (seq : Fin r → A),
        W.card = n - r ∧
        Function.Injective seq ∧
        (∀ t : Fin r, seq t ∉ W) ∧
        (∀ t : Fin r,
          C / ((n - t.val : ℕ) : ℝ) ≤
            ξ.share (W ∪ (Finset.univ.filter fun s : Fin r => t ≤ s).image seq) (seq t)) := by
    intro r
    induction r with
    | zero => exact fun _ => ⟨Finset.univ, Fin.elim0, by simp [n], fun x => Fin.elim0 x,
        fun x => Fin.elim0 x, fun x => Fin.elim0 x⟩
    | succ r ih =>
      intro hr
      obtain ⟨W₀, seq₀, hW₀_card, hinj₀, hnotW₀, hshare₀⟩ := ih (by omega)
      have hW₀_ne : W₀.Nonempty := Finset.card_pos.mp (by omega)
      have hsum_W₀ : ∑ x ∈ W₀, ξ.share W₀ x = C := by
        simpa [singleLinkMulticast_cost, hW₀_ne] using hbb_eq W₀
      obtain ⟨a, haW₀, ha_ge⟩ : ∃ a ∈ W₀, C / (W₀.card : ℝ) ≤ ξ.share W₀ a := by
        by_contra hall
        push Not at hall
        have hlt := Finset.sum_lt_sum_of_nonempty hW₀_ne hall
        have hcpos : (0 : ℝ) < W₀.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hW₀_ne)
        rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hcpos.ne'] at hlt; linarith
      let W₁ := W₀.erase a
      let seq₁ : Fin (r + 1) → A := Fin.snoc seq₀ a
      refine ⟨W₁, seq₁, by rw [Finset.card_erase_of_mem haW₀, hW₀_card]; omega, ?_, ?_, ?_⟩
      · intro x y hxy
        rcases Fin.eq_castSucc_or_eq_last x with ⟨x', rfl⟩ | rfl <;>
          rcases Fin.eq_castSucc_or_eq_last y with ⟨y', rfl⟩ | rfl
        · exact congrArg Fin.castSucc (hinj₀ (by simpa [seq₁] using hxy))
        · simp only [seq₁, Fin.snoc_castSucc, Fin.snoc_last] at hxy
          exact absurd (hxy ▸ haW₀) (hnotW₀ x')
        · simp only [seq₁, Fin.snoc_castSucc, Fin.snoc_last] at hxy
          exact absurd (hxy.symm ▸ haW₀) (hnotW₀ y')
        · rfl
      · intro t
        rcases Fin.eq_castSucc_or_eq_last t with ⟨t', rfl⟩ | rfl
        · simp only [seq₁, Fin.snoc_castSucc]
          exact fun h => hnotW₀ t' (Finset.erase_subset a W₀ h)
        · simp [seq₁, W₁]
      · intro t
        rcases Fin.eq_castSucc_or_eq_last t with ⟨t', rfl⟩ | rfl
        · simp only [seq₁, Fin.snoc_castSucc, Fin.val_castSucc]
          have hset_eq :
              W₁ ∪ (Finset.univ.filter fun s : Fin (r + 1) => t'.castSucc ≤ s).image seq₁ =
                W₀ ∪ (Finset.univ.filter fun s : Fin r => t' ≤ s).image seq₀ := by
            ext x
            simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
              true_and, W₁]
            refine ⟨?_, ?_⟩
            · rintro (hx | ⟨s, hts, rfl⟩)
              · exact Or.inl (Finset.erase_subset a W₀ hx)
              · rcases Fin.eq_castSucc_or_eq_last s with ⟨s', rfl⟩ | rfl
                · exact Or.inr ⟨s', Fin.castSucc_le_castSucc_iff.mp hts, by simp [seq₁]⟩
                · simpa [seq₁] using Or.inl haW₀
            · rintro (hx | ⟨s', hts', rfl⟩)
              · rcases eq_or_ne x a with rfl | hxa
                · exact Or.inr ⟨Fin.last r, Fin.le_last _, by simp [seq₁]⟩
                · exact Or.inl (Finset.mem_erase.mpr ⟨hxa, hx⟩)
              · exact Or.inr ⟨s'.castSucc, Fin.castSucc_le_castSucc_iff.mpr hts', by simp [seq₁]⟩
          rw [hset_eq]
          exact hshare₀ t'
        · simp only [seq₁, Fin.snoc_last, Fin.val_last]
          have hflt : (Finset.univ.filter fun s : Fin (r + 1) => Fin.last r ≤ s) =
              {Fin.last r} :=
            Finset.eq_singleton_iff_unique_mem.mpr
              ⟨by simp, fun s hs => le_antisymm (Fin.le_last s) (Finset.mem_filter.mp hs).2⟩
          have hset_W₀ : W₁ ∪ ({Fin.last r} : Finset (Fin (r + 1))).image seq₁ = W₀ := by
            simp [Finset.image_singleton, seq₁, W₁, Finset.insert_erase haW₀]
          rw [hflt, hset_W₀, ← hW₀_card]
          exact ha_ge
  obtain ⟨W, seq, hW_card, hinj, _, hshare⟩ := hchain n le_rfl
  have hW_emp : W = ∅ := Finset.card_eq_zero.mp (by omega)
  let eqv : Fin n ≃ A := Equiv.ofBijective seq
    ((Fintype.bijective_iff_injective_and_card seq).mpr ⟨hinj, Fintype.card_fin n⟩)
  let δ : ℝ := min (C / (2 * (n : ℝ))) (ε / (2 * (n : ℝ)))
  have hn_rpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hδ_pos : 0 < δ := lt_min (div_pos hC (by positivity)) (div_pos hε (by positivity))
  have hδ_le_C : δ ≤ C / (2 * (n : ℝ)) := min_le_left _ _
  have hnδ_lt_ε : (n : ℝ) * δ < ε := by
    have hmul := mul_le_mul_of_nonneg_left (min_le_right _ _ : δ ≤ ε / (2 * (n : ℝ))) hn_rpos.le
    have : (n : ℝ) * (ε / (2 * (n : ℝ))) = ε / 2 := by field_simp
    linarith
  let b : A → ℝ := fun x => C / ((n - (eqv.symm x).val : ℕ) : ℝ) - δ
  have hb_nn : ∀ x : A, 0 ≤ b x := fun x => by
    have hk_le : ((n - (eqv.symm x).val : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n _
    have hk_pos : (0 : ℝ) < ((n - (eqv.symm x).val : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (by omega)
    have := div_le_div_of_nonneg_left hC.le hk_pos
      (by linarith : ((n - (eqv.symm x).val : ℕ) : ℝ) ≤ 2 * n)
    dsimp only [b]; linarith
  have hserv_emp : ξ.moulinServiced b = ∅ := by
    rcases (ξ.moulinServiced b).eq_empty_or_nonempty with hemp | hSne
    · exact hemp
    · exfalso
      set S := ξ.moulinServiced b
      let idxSet := S.image eqv.symm
      let t₀ := idxSet.min' (hSne.image _)
      have ha_in_S : seq t₀ ∈ S := by
        obtain ⟨x, hxS, hxt⟩ := Finset.mem_image.mp (Finset.min'_mem idxSet (hSne.image _))
        exact (show seq t₀ = x from (eqv.symm_apply_eq.mp hxt).symm).symm ▸ hxS
      have hS_sub : S ⊆ W ∪ (Finset.univ.filter fun s : Fin n => t₀ ≤ s).image seq :=
        fun x hxS => by
        rw [hW_emp, Finset.empty_union, Finset.mem_image]
        exact ⟨eqv.symm x, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Finset.min'_le idxSet _ (Finset.mem_image_of_mem _ hxS)⟩,
          eqv.apply_symm_apply x⟩
      have hcm_le := hcm hS_sub ha_in_S
      have hpeel_ge := hshare t₀
      have hwill_t₀ := (ξ.isGreatest_isWilling_moulinServiced hcm b).1 (seq t₀) ha_in_S
      have hb_t₀ : b (seq t₀) = C / ((n - t₀.val : ℕ) : ℝ) - δ := by
        have hsymm : eqv.symm (seq t₀) = t₀ := eqv.symm_apply_apply t₀
        simp [b, hsymm]
      linarith
  have hsum_b : ∑ x : A, b x = (harmonic n : ℝ) * C - (n : ℝ) * δ := by
    rw [← Equiv.sum_comp eqv]
    simp only [b, Equiv.symm_apply_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun r => C / ((n - r : ℕ) : ℝ)), ← Finset.sum_range_reflect]
    conv_rhs => rw [cast_harmonic, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hlt := Finset.mem_range.mp hm
    rw [show n - (n - 1 - m) = m + 1 by omega, div_eq_mul_inv, mul_comm]
    push_cast
    rfl
  refine ⟨b, hb_nn, ?_⟩
  rw [ξ.moulinMechanism_serviced, hserv_emp, (singleLinkMulticast A C hC.le).netWelfare_empty,
    sub_zero, MulticastInstance.netWelfare_apply, singleLinkMulticast_cost, hsum_b]
  simp only [Finset.univ_nonempty, ↓reduceIte]; linarith

/-! ## 5. `(k + 1)`-bit cut communication lower bound for `SH` on path trees -/

section PathLowerBound

/-- Rooted path tree `0 — 1 — 2 — … — k — (k + 1)` on `Fin (k + 2)` with root `0`. -/
def pathRootedTree (k : ℕ) : RootedTree (Fin (k + 2)) where
  root := ⟨0, by omega⟩
  parent v := ⟨v.val - 1, by omega⟩
  parent_root := rfl
  reaches_root v := ⟨v.val, by
    have hiter : ∀ m : ℕ, ∀ w : Fin (k + 2),
        ((fun u : Fin (k + 2) => (⟨u.val - 1, by omega⟩ : Fin (k + 2)))^[m] w) =
          ⟨w.val - m, by omega⟩ := by
      intro m
      induction m with
      | zero => intro w; rfl
      | succ m ih =>
        intro w
        rw [Function.iterate_succ_apply', ih]
        ext; dsimp; omega
    rw [hiter]
    ext; simp⟩

private theorem pathRootedTree_iterate_parent (k m : ℕ) (w : Fin (k + 2)) :
    (pathRootedTree k).parent^[m] w = ⟨w.val - m, by omega⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    ext; simp [pathRootedTree]; omega

private theorem pathRootedTree_isAncestor_iff (k : ℕ) (u w : Fin (k + 2)) :
    (pathRootedTree k).IsAncestor u w ↔ u.val ≤ w.val := by
  refine ⟨?_, fun hle => ⟨w.val - u.val,
    (pathRootedTree_iterate_parent k _ w).trans (Fin.ext (Nat.sub_sub_self hle))⟩⟩
  rintro ⟨m, rfl⟩
  simp [pathRootedTree_iterate_parent]

/-- Fixed `(k + 2)`-node **path multicast instance** `pathMulticast k`:
- `k` spine nodes `1 .. k` on Alice's side, with link cost `((k + 1)!) * ((k + 1)! + 1) ^ (v - 1)`
  and one Alice receiver `Sum.inl t` at `t + 1`;
- bottom node `k + 1` on Bob's side (link cost `0`), housing Bob's receiver `Sum.inr ()`. -/
def pathMulticast (k : ℕ) : MulticastInstance (Fin (k + 2)) (Fin k ⊕ Unit) where
  tree := pathRootedTree k
  edgeCost v :=
    if v.val = 0 ∨ v.val = k + 1 then 0
    else (((k + 1).factorial : ℕ) : ℝ) * ((((k + 1).factorial + 1 : ℕ) : ℝ) ^ (v.val - 1))
  edgeCost_root := by simp [pathRootedTree]
  edgeCost_nonneg v := by
    split_ifs
    · exact le_rfl
    · positivity
  loc
    | Sum.inl t => ⟨t.val + 1, by omega⟩
    | Sum.inr () => ⟨k + 1, by omega⟩

/-- Exact `shShare` of Bob's bottom receiver `Sum.inr ()` when Alice's active spine receivers are
`{t : Fin k | x t = true}`. -/
noncomputable def pathBottomShare (k : ℕ) (x : Cslib.BitString k) : ℝ :=
  (pathMulticast k).shShare
    (((Finset.univ.filter fun t : Fin k => x t = true).map ⟨Sum.inl, Sum.inl_injective⟩) ∪
      {Sum.inr ()})
    (Sum.inr ())

/-- Two-party bid profile on `pathMulticast k` induced by Alice's `x : BitString k` and Bob's
`y : BitString k`: Alice's active receivers bid `1 + ∑ edgeCost`, Alice's inactive receivers bid
`0`, and Bob's bottom receiver bids `pathBottomShare k y`. -/
noncomputable def pathBidProfile (k : ℕ) (x y : Cslib.BitString k) : Fin k ⊕ Unit → ℝ
  | Sum.inl t =>
    if x t = true then 1 + ∑ v : Fin (k + 2), (pathMulticast k).edgeCost v else 0
  | Sum.inr () => pathBottomShare k y

/-- `pathBottomShare k` is injective on `BitString k`: distinct active receiver subsets along the
spine induce distinct Shapley shares at the bottom node. -/
theorem pathBottomShare_injective (k : ℕ) : Function.Injective (pathBottomShare k) := by
  intro x x' heq
  set L : ℕ := (k + 1).factorial
  let cnt (z : Cslib.BitString k) (t : Fin k) : ℕ :=
    1 + (Finset.univ.filter fun r : Fin k => t ≤ r ∧ z r = true).card
  let dig (z : Cslib.BitString k) (n : ℕ) : ℕ :=
    if h : n < k then L / cnt z ⟨n, h⟩ else 0
  have hcnt_bounds : ∀ z t, 1 ≤ cnt z t ∧ cnt z t ≤ k + 1 := fun z t => by
    have := Finset.card_le_univ (Finset.univ.filter fun r : Fin k => t ≤ r ∧ z r = true)
    rw [Fintype.card_fin] at this
    dsimp only [cnt]
    exact ⟨Nat.le_add_right 1 _, by omega⟩
  have hcnt_dvd : ∀ z t, cnt z t ∣ L := fun z t =>
    Nat.dvd_factorial (hcnt_bounds z t).1 (hcnt_bounds z t).2
  have hdig_lt : ∀ z n, n < k → dig z n < L + 1 := fun z n hn => by
    simp only [dig, hn, ↓reduceDIte]
    have := Nat.div_le_self L (cnt z ⟨n, hn⟩)
    omega
  have heval : ∀ z : Cslib.BitString k,
      pathBottomShare k z = ((∑ n ∈ Finset.range k, dig z n * (L + 1) ^ n : ℕ) : ℝ) := fun z => by
    let Sz : Finset (Fin k ⊕ Unit) :=
      ((Finset.univ.filter fun t : Fin k => z t = true).map ⟨Sum.inl, Sum.inl_injective⟩) ∪
        {Sum.inr ()}
    unfold pathBottomShare
    rw [MulticastInstance.shShare_apply]
    simp only [Sz, show Sum.inr () ∈ Sz by simp [Sz], ↓reduceIte, Finset.sum_filter]
    let termNat (v : ℕ) : ℝ :=
      if hv : v < k + 2 then
        if (pathMulticast k).tree.IsAncestor ⟨v, hv⟩ ((pathMulticast k).loc (Sum.inr ())) then
          (pathMulticast k).edgeCost ⟨v, hv⟩ /
            ((Sz.filter fun j =>
              (pathMulticast k).tree.IsAncestor ⟨v, hv⟩ ((pathMulticast k).loc j)).card : ℝ)
        else 0
      else 0
    have hsum_fin : (∑ v : Fin (k + 2),
        if (pathMulticast k).tree.IsAncestor v ((pathMulticast k).loc (Sum.inr ())) then
          (pathMulticast k).edgeCost v /
            ((Sz.filter fun j =>
              (pathMulticast k).tree.IsAncestor v ((pathMulticast k).loc j)).card : ℝ)
        else 0) = ∑ v ∈ Finset.range (k + 2), termNat v := by
      rw [← Fin.sum_univ_eq_sum_range termNat]
      exact Finset.sum_congr rfl fun v _ => by simp only [termNat, v.isLt, ↓reduceDIte]
    rw [hsum_fin, Finset.sum_range_succ,
      show termNat (k + 1) = 0 by simp [termNat, pathMulticast], add_zero, Finset.sum_range_succ',
      show termNat 0 = 0 by simp [termNat, pathMulticast], add_zero]
    simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnk := Finset.mem_range.mp hn
    have hn_lt : n + 1 < k + 2 := by omega
    have hanc_bot : (pathMulticast k).tree.IsAncestor ⟨n + 1, hn_lt⟩
        ((pathMulticast k).loc (Sum.inr ())) := by
      change (pathRootedTree k).IsAncestor ⟨n + 1, hn_lt⟩ ⟨k + 1, by omega⟩
      rw [pathRootedTree_isAncestor_iff]
      dsimp
      omega
    have hedge : (pathMulticast k).edgeCost ⟨n + 1, hn_lt⟩ = (L : ℝ) * ((L + 1 : ℝ) ^ n) := by
      simp only [pathMulticast, show ¬ (n + 1 = 0 ∨ n + 1 = k + 1) by omega, ↓reduceIte]
      push_cast [L]; rfl
    have hcard_Sz : (Sz.filter fun j =>
        (pathMulticast k).tree.IsAncestor ⟨n + 1, hn_lt⟩ ((pathMulticast k).loc j)).card =
        cnt z ⟨n, hnk⟩ := by
      let A_n : Finset (Fin k ⊕ Unit) :=
        ((Finset.univ.filter fun r : Fin k => (⟨n, hnk⟩ : Fin k) ≤ r ∧ z r = true).map
          ⟨Sum.inl, Sum.inl_injective⟩)
      have hflt_eq : (Sz.filter fun j =>
          (pathMulticast k).tree.IsAncestor ⟨n + 1, hn_lt⟩ ((pathMulticast k).loc j)) =
          insert (Sum.inr ()) A_n := by
        ext j
        cases j with
        | inl r =>
          simp only [Finset.mem_filter, Sz, Finset.mem_union, Finset.mem_map,
            Function.Embedding.coeFn_mk, Sum.inl.injEq, exists_eq_right, Finset.mem_univ,
            true_and, Finset.mem_singleton, reduceCtorEq, or_false, Finset.mem_insert,
            false_or, A_n]
          change (z r = true ∧
              (pathRootedTree k).IsAncestor ⟨n + 1, hn_lt⟩ ⟨r.val + 1, by omega⟩) ↔
            (⟨n, hnk⟩ : Fin k) ≤ r ∧ z r = true
          rw [pathRootedTree_isAncestor_iff, Fin.le_def]
          dsimp
          exact ⟨fun ⟨hz, hle⟩ => ⟨by omega, hz⟩, fun ⟨hle, hz⟩ => ⟨hz, by omega⟩⟩
        | inr u =>
          cases u
          simp [Sz, hanc_bot, A_n]
      rw [hflt_eq, Finset.card_insert_of_notMem (by simp [A_n]), Finset.card_map]
      dsimp [cnt]; omega
    simp only [termNat, hn_lt, ↓reduceDIte, hanc_bot, ↓reduceIte, hedge, hcard_Sz, dig, hnk]
    have hc_pos : (0 : ℝ) < (cnt z ⟨n, hnk⟩ : ℝ) :=
      Nat.cast_pos.mpr (by have := (hcnt_bounds z ⟨n, hnk⟩).1; omega)
    rw [div_eq_iff hc_pos.ne']
    have hcast : ((L / cnt z ⟨n, hnk⟩ : ℕ) : ℝ) * (cnt z ⟨n, hnk⟩ : ℝ) = (L : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel (hcnt_dvd z ⟨n, hnk⟩)
    rw [← hcast]; ring
  rw [heval x, heval x'] at heq
  have hdig_eq : ∀ i ∈ Finset.range k, dig x i = dig x' i :=
    Nat.eq_of_sum_mul_pow_eq (e := id) Function.injective_id.injOn
      (fun i hi => hdig_lt x i (Finset.mem_range.mp hi))
      (fun i hi => hdig_lt x' i (Finset.mem_range.mp hi)) (Nat.cast_injective heq)
  have hcnt_eq : ∀ t : Fin k, cnt x t = cnt x' t := fun t => by
    have hd := hdig_eq t.val (Finset.mem_range.mpr t.isLt)
    simp only [dig, t.isLt, ↓reduceDIte] at hd
    have h1 := Nat.div_mul_cancel (hcnt_dvd x t)
    rw [hd] at h1
    have hdiv_pos : 0 < L / cnt x' t :=
      Nat.div_pos ((hcnt_bounds x' t).2.trans (Nat.self_le_factorial (k + 1))) (hcnt_bounds x' t).1
    exact Nat.eq_of_mul_eq_mul_left hdiv_pos (h1.trans (Nat.div_mul_cancel (hcnt_dvd x' t)).symm)
  suffices htail : ∀ m (t : Fin k), k - t.val ≤ m → x t = x' t from funext fun t => htail _ t le_rfl
  intro m
  induction m with
  | zero =>
    intro t hm
    have := t.isLt
    omega
  | succ m ih =>
    intro t hm
    have hstrict : (Finset.univ.filter fun r : Fin k => t < r ∧ x r = true) =
        Finset.univ.filter fun r : Fin k => t < r ∧ x' r = true := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_congr_right fun htr => by
        have : t.val < r.val := htr
        have := r.isLt
        rw [ih r (by omega)]
    have hflt_z (z : Cslib.BitString k) :
        (Finset.univ.filter fun r : Fin k => t ≤ r ∧ z r = true) =
          if z t = true then insert t (Finset.univ.filter fun r : Fin k => t < r ∧ z r = true)
          else Finset.univ.filter fun r : Fin k => t < r ∧ z r = true := by
      ext r
      by_cases hrt : r = t
      · subst hrt
        by_cases hzt : z r = true <;> simp [hzt]
      · by_cases hzt : z t = true <;> simp [hzt, hrt, Ne.symm hrt, lt_iff_le_and_ne]
    have hc := hcnt_eq t
    dsimp only [cnt] at hc
    rw [hflt_z x, hflt_z x', hstrict] at hc
    cases hx : x t <;> cases hx' : x' t <;>
      simp [hx, hx', Finset.card_insert_of_notMem] at hc ⊢

/-- On `pathBidProfile k x y`, Bob's bottom receiver `Sum.inr ()` is served by `shMechanism` iff
`pathBottomShare k x ≤ pathBottomShare k y`. -/
theorem mem_pathMulticast_shMechanism_serviced_iff (k : ℕ) (x y : Cslib.BitString k) :
    Sum.inr () ∈ (pathMulticast k).shMechanism.serviced (pathBidProfile k x y) ↔
      pathBottomShare k x ≤ pathBottomShare k y := by
  set I := pathMulticast k
  set b := pathBidProfile k x y
  rw [I.shMechanism_serviced]
  let Sx : Finset (Fin k ⊕ Unit) :=
    (Finset.univ.filter fun t : Fin k => x t = true).map ⟨Sum.inl, Sum.inl_injective⟩
  have hgreat := I.shScheme.isGreatest_isWilling_moulinServiced I.shScheme_isCrossMonotone b
  have hshare_le_tot : ∀ (S : Finset (Fin k ⊕ Unit)) (j : Fin k ⊕ Unit),
      I.shShare S j ≤ ∑ v : Fin (k + 2), I.edgeCost v := fun S j => by
    rw [MulticastInstance.shShare_apply]
    split_ifs with hjS
    · rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun v _ => ?_
      split_ifs with hanc
      · exact div_le_self (I.edgeCost_nonneg v) (by
          exact_mod_cast Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hjS, hanc⟩⟩)
      · exact I.edgeCost_nonneg v
    · exact Finset.sum_nonneg fun v _ => I.edgeCost_nonneg v
  have hSx_will_any : ∀ S : Finset (Fin k ⊕ Unit), ∀ j ∈ Sx, I.shScheme.share S j ≤ b j :=
    fun S j hj => by
      obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hj
      simp only [MulticastInstance.shScheme_share, Function.Embedding.coeFn_mk, b, pathBidProfile,
        (Finset.mem_filter.mp ht).2, ↓reduceIte]
      linarith [hshare_le_tot S (Sum.inl t)]
  have hinact_out : ∀ S : Finset (Fin k ⊕ Unit), I.shScheme.IsWilling b S →
      ∀ t : Fin k, x t = false → Sum.inl t ∉ S := fun S hw t hxt hmem => by
    have hw_t := hw (Sum.inl t) hmem
    simp only [MulticastInstance.shScheme_share, MulticastInstance.shShare_apply, hmem, ↓reduceIte,
      b, pathBidProfile, hxt, Bool.false_eq_true] at hw_t
    let vt : Fin (k + 2) := ⟨t.val + 1, by omega⟩
    have hvt_cost_pos : 0 < I.edgeCost vt := by
      simp only [I, pathMulticast, vt,
        show ¬ (t.val + 1 = 0 ∨ t.val + 1 = k + 1) by omega, ↓reduceIte]
      have := Nat.factorial_pos (k + 1)
      positivity
    have hcard_pos : (0 : ℝ) < ((S.filter fun j => I.tree.IsAncestor vt (I.loc j)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr
        ⟨Sum.inl t, Finset.mem_filter.mpr ⟨hmem, I.tree.isAncestor_refl vt⟩⟩
    have hvt_mem : vt ∈ Finset.univ.filter fun v => I.tree.IsAncestor v (I.loc (Sum.inl t)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ vt, I.tree.isAncestor_refl vt⟩
    have hsum_pos := lt_of_lt_of_le (div_pos hvt_cost_pos hcard_pos) (Finset.single_le_sum
      (f := fun v => I.edgeCost v / ((S.filter fun j => I.tree.IsAncestor v (I.loc j)).card : ℝ))
      (fun v _ => div_nonneg (I.edgeCost_nonneg v) (Nat.cast_nonneg _)) hvt_mem)
    linarith
  refine ⟨fun hinr_serv => ?_, fun hle => ?_⟩
  · have hsub : I.shScheme.moulinServiced b ⊆ Sx ∪ {Sum.inr ()} := fun j hj => by
      cases j with
      | inl t =>
        cases hxt : x t
        · exact absurd hj (hinact_out _ hgreat.1 t hxt)
        · exact Finset.mem_union_left _
            (Finset.mem_map.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, hxt⟩, rfl⟩)
      | inr u =>
        cases u
        exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have heq_serv : I.shScheme.moulinServiced b = Sx ∪ {Sum.inr ()} :=
      le_antisymm hsub (Finset.union_subset (hgreat.2 (hSx_will_any Sx))
        (Finset.singleton_subset_iff.mpr hinr_serv))
    have hw_bot := hgreat.1 (Sum.inr ()) hinr_serv
    rwa [heq_serv, MulticastInstance.shScheme_share] at hw_bot
  · have hw_both : I.shScheme.IsWilling b (Sx ∪ {Sum.inr ()}) := fun j hj =>
      (Finset.mem_union.mp hj).elim (hSx_will_any _ j) fun h => by
        rw [Finset.mem_singleton.mp h, MulticastInstance.shScheme_share]
        exact hle
    exact hgreat.2 hw_both (Finset.mem_union_right Sx (Finset.mem_singleton_self _))

/-- **`(k + 1)`-bit deterministic cut communication lower bound for `SH` on path trees**
([FeigenbaumPapadimitriouShenker2001]; [FeigenbaumSchapiraShenker2007]): for `0 < k`, any
deterministic two-party protocol across the bottom cut link of `pathMulticast k` deciding whether
Bob's receiver `Sum.inr ()` is served by `shMechanism` exchanges at least `k + 1` bits. -/
theorem le_ecomplexityFun_pathMulticast_shServiced {k : ℕ} (hk : 0 < k) :
    (k + 1 : ℕ∞) ≤ Cslib.Communication.Protocol.ecomplexityFun
      (fun x y : Cslib.BitString k =>
        decide (Sum.inr () ∈ (pathMulticast k).shMechanism.serviced (pathBidProfile k x y))) := by
  have hfun :
      (fun x y : Cslib.BitString k =>
        decide (Sum.inr () ∈ (pathMulticast k).shMechanism.serviced (pathBidProfile k x y))) =
      fun x y : Cslib.BitString k => decide (pathBottomShare k x ≤ pathBottomShare k y) :=
    funext fun x => funext fun y => by simp only [mem_pathMulticast_shMechanism_serviced_iff]
  rw [hfun]
  let S : Finset (Cslib.BitString k × Cslib.BitString k) :=
    (Finset.univ : Finset (Cslib.BitString k)).image fun x => (x, x)
  have hfool : Cslib.Communication.IsFoolingSet
      (fun x y : Cslib.BitString k => decide (pathBottomShare k x ≤ pathBottomShare k y)) true S :=
    ⟨fun _ hp => by
       obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
       simp,
     fun _ hp _ hq h₁ h₂ => by
       obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
       obtain ⟨x', -, rfl⟩ := Finset.mem_image.mp hq
       simp only [decide_eq_true_eq] at h₁ h₂
       rw [pathBottomShare_injective k (le_antisymm h₁ h₂)]⟩
  have hz : ∃ x y : Cslib.BitString k,
      decide (pathBottomShare k x ≤ pathBottomShare k y) ≠ true := by
    let x₀ : Cslib.BitString k := fun _ => false
    let x₁ : Cslib.BitString k := fun _ => true
    have hne : pathBottomShare k x₀ ≠ pathBottomShare k x₁ := fun h => by
      have := congrFun (pathBottomShare_injective k h) ⟨0, hk⟩
      simp [x₀, x₁] at this
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨x₁, x₀, by simp [not_le.mpr h]⟩
    · exact ⟨x₀, x₁, by simp [not_le.mpr h]⟩
  exact hfool.succ_le_ecomplexity hz (by
    rw [Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.fst h,
      Finset.card_univ, Cslib.BitString.card])

end PathLowerBound

end Cslib.GameTheory


