/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Submodular.Basic
public import CslibFrontier.Algorithms.Lean.Submodular.Greedy
public import CslibFrontier.GameTheory.Network.InfluenceModels
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Influence Submodularity and Greedy Influence Maximization

This module formalizes Section 24.4 of [Kleinberg2007] (pp. 622–627), establishing the
local-to-global submodularity theorems for network influence functions and their `(1 - 1/e)` greedy
approximation corollaries:

1. **Independent Cascade Submodularity via Live-Edge Graphs** ([KempeKleinbergTardos2003];
   [Kleinberg2007], Theorem 24.5, pp. 625–626): flipping all edge coins upfront decomposes
   `IndependentCascadeModel.influence` into a convex combination of directed reachability coverage
   sizes `|liveReachable H S|` (`IndependentCascadeModel.influence_eq_sum_liveGraphWeight`), each
   of which is monotone and submodular (`IndependentCascadeModel.isSubmodular_influence`).
2. **Mossel–Roch General Threshold Submodularity** ([MosselRoch2007]; [Kleinberg2007],
   Theorem 24.6, p. 626): whenever every local threshold function `M.thresholdFn v` is submodular,
   the global expectation `S ↦ ∫ θ, φ (M.thresholdFinal θ S) ∂thresholdMeasure V` is monotone and
   submodular for every monotone submodular objective `φ : Finset V → ℝ`
   (`GeneralThresholdModel.isSubmodular_integral_thresholdFinal`), and in particular `M.influence`
   is submodular (`GeneralThresholdModel.isSubmodular_influence`). Specializations yield
   submodularity for `LinearThresholdModel` and for `T`-step nonprogressive threshold processes via
   `timeLayeredDigraph` (`GeneralThresholdModel.isSubmodular_nonprogStepInfluence`).
3. **Diminishing-Returns Cascade Submodularity** ([KempeKleinbergTardos2003];
   [KempeKleinbergTardos2005]; [Kleinberg2007], Theorem 24.4, pp. 624, 626): under
   `CascadeModel.HasDiminishingReturns`, every translated threshold function
   `C.toGeneralThresholdModel.thresholdFn v` is submodular
   (`CascadeModel.isSubmodular_toGeneralThresholdModel_thresholdFn`), so `C.influence` is
   submodular (`CascadeModel.isSubmodular_influence_of_diminishingReturns`).
4. **Greedy `(1 - 1/e)` Influence Maximization** ([NemhauserWolseyFisher1978];
   [KempeKleinbergTardos2003]; [Kleinberg2007], Theorem 24.3 and Section 24.4, pp. 623–626):
   combining monotone submodularity with `one_sub_exp_neg_one_mul_le_submodularGreedy` gives the
   `(1 - Real.exp (-1))` cardinality-constrained greedy guarantee across all three models.

## Main definitions

* `Cslib.GameTheory.Network.liveReachableFrom`, `Cslib.GameTheory.Network.liveReachable`:
  vertices reachable from a seed or seed set in a realized live-edge digraph `H : Digraph V`.
* `Cslib.GameTheory.Network.liveGraphWeight`: product Bernoulli weight of a live-edge digraph `H`
  under `IC : IndependentCascadeModel G`.
* `Cslib.GameTheory.Network.IndependentCascadeModel.influence`: expected final active-set size in
  the Independent Cascade Model.

## Main results

* `Cslib.GameTheory.Network.IndependentCascadeModel.influence_eq_sum_liveGraphWeight`: live-edge
  graph decomposition of Independent Cascade influence ([Kleinberg2007], Section 24.4, pp. 625–626).
* `Cslib.GameTheory.Network.IndependentCascadeModel.isSubmodular_influence`:
  **Theorem 24.5** of [Kleinberg2007] ([KempeKleinbergTardos2003]).
* `Cslib.GameTheory.Network.GeneralThresholdModel.isSubmodular_integral_thresholdFinal`,
  `Cslib.GameTheory.Network.GeneralThresholdModel.isSubmodular_influence`:
  **Theorem 24.6** of [Kleinberg2007] ([MosselRoch2007]).
* `Cslib.GameTheory.Network.CascadeModel.isSubmodular_influence_of_diminishingReturns`:
  **Theorem 24.4** of [Kleinberg2007] ([KempeKleinbergTardos2003]; [KempeKleinbergTardos2005]).
* `Cslib.GameTheory.Network.GeneralThresholdModel.one_sub_exp_neg_one_mul_le_greedy_influence`,
  `Cslib.GameTheory.Network.CascadeModel.one_sub_exp_neg_one_mul_le_greedy_influence`,
  `Cslib.GameTheory.Network.IndependentCascadeModel.one_sub_exp_neg_one_mul_le_greedy_influence`:
  `(1 - 1/e)` greedy influence maximization guarantees.

## References

* [KempeKleinbergTardos2003]
* [KempeKleinbergTardos2005]
* [Kleinberg2007]
* [MosselRoch2007]
* [NemhauserWolseyFisher1978]
-/

public section

open Cslib.Algorithms.Lean.Submodular MeasureTheory Set

namespace Cslib.GameTheory.Network

/-! ## Theorem 24.5: Independent Cascade Live-Edge Decomposition and Submodularity -/

section LiveEdge

/-- Vertices reachable from `s : V` along directed paths in a realized live-edge graph
`H : Digraph V` ([Kleinberg2007], Section 24.4, pp. 625–626). -/
noncomputable def liveReachableFrom {V : Type*} [Fintype V] (H : Digraph V) (s : V) : Finset V :=
  open scoped Classical in
  Finset.univ.filter (Relation.ReflTransGen H.Adj s ·)

@[simp]
theorem mem_liveReachableFrom {V : Type*} [Fintype V] {H : Digraph V} {s v : V} :
    v ∈ liveReachableFrom H s ↔ Relation.ReflTransGen H.Adj s v := by
  unfold liveReachableFrom
  simp

/-- Vertices reachable from at least one seed in `S` along directed paths in `H : Digraph V`
([Kleinberg2007], Section 24.4, p. 625). -/
noncomputable def liveReachable {V : Type*} [DecidableEq V] [Fintype V] (H : Digraph V)
    (S : Finset V) : Finset V :=
  S.biUnion (liveReachableFrom H)

@[simp]
theorem mem_liveReachable {V : Type*} [DecidableEq V] [Fintype V] {H : Digraph V}
    {S : Finset V} {v : V} :
    v ∈ liveReachable H S ↔ ∃ s ∈ S, Relation.ReflTransGen H.Adj s v := by
  simp [liveReachable]

@[simp]
theorem liveReachable_empty {V : Type*} [DecidableEq V] [Fintype V] (H : Digraph V) :
    liveReachable H ∅ = ∅ := by
  simp [liveReachable]

theorem subset_liveReachable {V : Type*} [DecidableEq V] [Fintype V] (H : Digraph V)
    (S : Finset V) : S ⊆ liveReachable H S :=
  fun s hs => mem_liveReachable.mpr ⟨s, hs, Relation.ReflTransGen.refl⟩

theorem monotone_liveReachable {V : Type*} [DecidableEq V] [Fintype V] (H : Digraph V) :
    Monotone (liveReachable H) :=
  fun _ _ hAB _ hv =>
    let ⟨s, hs, hp⟩ := mem_liveReachable.mp hv
    mem_liveReachable.mpr ⟨s, hAB hs, hp⟩

/-- Realized live-edge graph probability
`∏_{(u, v)} p_{uv}^{[H.Adj u v]} (1 - p_{uv})^{[¬ H.Adj u v]}` under independent edge coin flips
([Kleinberg2007], Section 24.4, p. 625). -/
noncomputable def liveGraphWeight {V : Type*} [Fintype V] {G : Digraph V}
    (IC : IndependentCascadeModel G) (H : Digraph V) : ℝ :=
  open scoped Classical in
  ∏ e : V × V, if H.Adj e.1 e.2 then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2

theorem liveGraphWeight_nonneg {V : Type*} [Fintype V] {G : Digraph V}
    (IC : IndependentCascadeModel G) (H : Digraph V) :
    0 ≤ liveGraphWeight IC H := by
  classical
  refine Finset.prod_nonneg fun e _ => ?_
  split_ifs
  · exact IC.edgeProb_nonneg e.1 e.2
  · exact sub_nonneg.mpr (IC.edgeProb_le_one e.1 e.2)

private theorem liveGraphWeight_eq_zero_of_not_le {V : Type*} [Fintype V] {G : Digraph V}
    (IC : IndependentCascadeModel G) {H : Digraph V} (hnot : ¬ H ≤ G) :
    liveGraphWeight IC H = 0 := by
  classical
  have hex : ∃ e : V × V, H.Adj e.1 e.2 ∧ ¬ G.Adj e.1 e.2 := by
    by_contra hall
    push Not at hall
    exact hnot fun u v huv => hall (u, v) huv
  rcases hex with ⟨e, heH, heG⟩
  unfold liveGraphWeight
  refine Finset.prod_eq_zero (Finset.mem_univ e) ?_
  simp [heH, IC.edgeProb_eq_zero_of_not_adj e.1 e.2 heG]

/-- Sum of independent Bernoulli product weights over subsets `E ⊆ U` containing `inSet` and
disjoint from `outSet`. -/
private theorem sum_powerset_bernWeight {α : Type*} [DecidableEq α] (p : α → ℝ)
    (U inSet outSet : Finset α) (hin : inSet ⊆ U) (hout : outSet ⊆ U)
    (hdisj : Disjoint inSet outSet) :
    (∑ E ∈ U.powerset with inSet ⊆ E ∧ Disjoint E outSet,
        ∏ a ∈ U, (if a ∈ E then p a else 1 - p a)) =
      (∏ a ∈ inSet, p a) * (∏ a ∈ outSet, (1 - p a)) := by
  let free := U \ (inSet ∪ outSet)
  have hbij : (∑ E ∈ U.powerset with inSet ⊆ E ∧ Disjoint E outSet,
        ∏ a ∈ U, (if a ∈ E then p a else 1 - p a)) =
      ∑ S ∈ free.powerset, ∏ a ∈ U, (if a ∈ inSet ∪ S then p a else 1 - p a) := by
    refine Finset.sum_bij' (fun E _ => E \ inSet) (fun S _ => inSet ∪ S) ?_ ?_ ?_ ?_ ?_
    · intro E hE
      rcases Finset.mem_filter.mp hE with ⟨hEU, _, hEout⟩
      rw [Finset.mem_powerset] at hEU ⊢
      intro a ha
      rcases Finset.mem_sdiff.mp ha with ⟨haE, hain⟩
      exact Finset.mem_sdiff.mpr ⟨hEU haE, Finset.notMem_union.mpr
        ⟨hain, Finset.disjoint_left.mp hEout haE⟩⟩
    · intro S hS
      have hSfree : S ⊆ free := Finset.mem_powerset.mp hS
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (Finset.union_subset hin (hSfree.trans Finset.sdiff_subset)),
        Finset.subset_union_left, Finset.disjoint_union_left.mpr ⟨hdisj, ?_⟩⟩
      rw [Finset.disjoint_left]
      intro a haS haout
      exact (Finset.mem_sdiff.mp (hSfree haS)).2 (Finset.mem_union_right _ haout)
    · intro E hE
      exact Finset.union_sdiff_of_subset (Finset.mem_filter.mp hE).2.1
    · intro S hS
      have hSin : Disjoint inSet S := by
        rw [Finset.disjoint_right]
        intro a haS hain
        exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hS haS)).2
          (Finset.mem_union_left _ hain)
      exact Finset.union_sdiff_cancel_left hSin
    · intro E hE
      rw [Finset.union_sdiff_of_subset (Finset.mem_filter.mp hE).2.1]
  have hterm : ∀ S ∈ free.powerset,
      (∏ a ∈ U, (if a ∈ inSet ∪ S then p a else 1 - p a)) =
        ((∏ a ∈ inSet, p a) * (∏ a ∈ outSet, (1 - p a))) *
          ((∏ a ∈ S, p a) * (∏ a ∈ free \ S, (1 - p a))) := by
    intro S hS
    have hSfree : S ⊆ free := Finset.mem_powerset.mp hS
    rw [← Finset.prod_sdiff (Finset.union_subset hin hout), Finset.prod_union hdisj,
      ← Finset.prod_sdiff hSfree]
    have hin_prod : (∏ a ∈ inSet, if a ∈ inSet ∪ S then p a else 1 - p a) = ∏ a ∈ inSet, p a :=
      Finset.prod_congr rfl fun a ha => ite_eq_left (Finset.mem_union_left _ ha)
    have hout_prod :
        (∏ a ∈ outSet, if a ∈ inSet ∪ S then p a else 1 - p a) = ∏ a ∈ outSet, (1 - p a) :=
      Finset.prod_congr rfl fun a ha => ite_eq_right fun hmem =>
        (Finset.mem_union.mp hmem).elim (fun hain => Finset.disjoint_left.mp hdisj hain ha)
          fun haS => (Finset.mem_sdiff.mp (hSfree haS)).2 (Finset.mem_union_right _ ha)
    have hS_prod : (∏ a ∈ S, if a ∈ inSet ∪ S then p a else 1 - p a) = ∏ a ∈ S, p a :=
      Finset.prod_congr rfl fun a ha => ite_eq_left (Finset.mem_union_right _ ha)
    have hcomp_prod :
        (∏ a ∈ free \ S, if a ∈ inSet ∪ S then p a else 1 - p a) = ∏ a ∈ free \ S, (1 - p a) :=
      Finset.prod_congr rfl fun a ha => ite_eq_right fun hmem =>
        (Finset.mem_union.mp hmem).elim
          (fun hain => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ha).1).2
            (Finset.mem_union_left _ hain))
          (Finset.mem_sdiff.mp ha).2
    rw [hin_prod, hout_prod, hS_prod, hcomp_prod]
    ring
  have hfree1 :
      (∑ S ∈ free.powerset, (∏ a ∈ S, p a) * (∏ a ∈ free \ S, (1 - p a))) = 1 := by
    rw [← Finset.prod_add p (fun a => 1 - p a) free]
    exact Finset.prod_eq_one fun a _ => by ring
  rw [hbij, Finset.sum_congr rfl hterm, ← Finset.mul_sum, hfree1, mul_one]

/-- Equivalence between `Digraph V` and edge sets `Finset (V × V)`. -/
private noncomputable def digraphEquivEdgeFinset (V : Type*) [DecidableEq V] [Fintype V] :
    Digraph V ≃ Finset (V × V) where
  toFun H := open scoped Classical in Finset.univ.filter fun e : V × V => H.Adj e.1 e.2
  invFun E := ⟨fun u v => (u, v) ∈ E⟩
  left_inv H := by
    ext u v
    simp
  right_inv E := by
    ext ⟨u, v⟩
    simp

/-- Modifying incoming edges into a vertex `v ∈ B` already in the seed set `B` leaves
`liveReachable · B` unchanged. -/
private theorem liveReachable_congr_inEdges {V : Type*} [DecidableEq V] [Fintype V]
    {H₁ H₂ : Digraph V} {v : V} {B : Finset V} (hv : v ∈ B)
    (hother : ∀ x y, y ≠ v → (H₁.Adj x y ↔ H₂.Adj x y)) :
    liveReachable H₁ B = liveReachable H₂ B := by
  have dir : ∀ {G₁ G₂ : Digraph V}, (∀ x y, y ≠ v → G₁.Adj x y → G₂.Adj x y) →
      liveReachable G₁ B ⊆ liveReachable G₂ B := by
    intro G₁ G₂ hG z hz
    rcases mem_liveReachable.mp hz with ⟨s, hsB, hp⟩
    clear hz
    induction hp with
    | refl => exact subset_liveReachable G₂ B hsB
    | @tail a b _ hab ih =>
      rcases mem_liveReachable.mp ih with ⟨s', hs'B, hp'⟩
      rcases eq_or_ne b v with rfl | hbv
      · exact subset_liveReachable G₂ B hv
      · exact mem_liveReachable.mpr ⟨s', hs'B, hp'.tail (hG a b hbv hab)⟩
  exact Finset.Subset.antisymm
    (dir fun x y hy => (hother x y hy).mp)
    (dir fun x y hy => (hother x y hy).mpr)

namespace IndependentCascadeModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (IC : IndependentCascadeModel G)

/-- Expected number of active vertices at the end of the Independent Cascade process starting from
seed set `S` ([Kleinberg2007], Section 24.4, p. 623). -/
@[expose] noncomputable def influence (S : Finset V) : ℝ :=
  IC.toCascadeModel.influence S

private theorem survivalProb_toCascadeModel (w : V) (X : Finset V) :
    IC.toCascadeModel.survivalProb w X = ∏ u ∈ X, (1 - IC.edgeProb u w) := by
  induction X using Finset.induction with
  | empty => simp
  | insert u X hu ih =>
    rw [IC.toCascadeModel.survivalProb_insert w hu, ih, Finset.prod_insert hu, mul_comm,
      IC.toCascadeModel_prob]

/-- **Live-Edge Distribution Equivalence** ([KempeKleinbergTardos2003]; [Kleinberg2007],
Section 24.4, pp. 625–626): under any valid attempt schedule `nextEdge`, the Independent Cascade
probability of terminating at active set `A` equals the total weight of realized live-edge graphs
`H` in which `liveReachable H S = A`. -/
theorem activeSetProb_eq_sum_liveGraphWeight
    {nextEdge : Finset V → (V → Finset V) → Option (V × V)}
    (hvalid : CascadeModel.ValidNextEdge G nextEdge) (S A : Finset V) :
    open scoped Classical in
    IC.toCascadeModel.activeSetProb nextEdge S A =
      ∑ H : Digraph V with liveReachable H S = A, liveGraphWeight IC H := by
  classical
  have h0 := IC.toCascadeModel.activeSetProb_eq_of_step hvalid S A
    (fun active tried =>
      ∑ H : Digraph V with
          (∀ w ∉ active, ∀ u ∈ tried w, ¬ H.Adj u w) ∧ liveReachable H active = A,
        liveGraphWeight IC H)
    (fun active tried htr_eq => by
      have hreach_closed : ∀ H : Digraph V, H ≤ G →
          (∀ w ∉ active, ∀ u ∈ tried w, ¬ H.Adj u w) →
          liveReachable H active = active := by
        intro H hHG hno
        refine Finset.Subset.antisymm (fun z hz => ?_) (subset_liveReachable H active)
        rcases mem_liveReachable.mp hz with ⟨s, hs, hp⟩
        clear hz
        induction hp with
        | refl => exact hs
        | @tail x y _ hxy ih_p =>
          by_contra hy_not
          have hGxy : G.Adj x y := hHG hxy
          have hx_tr : x ∈ tried y := by
            rw [htr_eq y hy_not]
            exact Finset.mem_inter.mpr ⟨ih_p, mem_inNeighbors.mpr hGxy⟩
          exact hno y hy_not x hx_tr hxy
      by_cases hA : active = A
      · subst hA
        simp only [↓reduceIte]
        have hsum_drop_reach :
            (∑ H : Digraph V with
                (∀ w ∉ active, ∀ u ∈ tried w, ¬ H.Adj u w) ∧ liveReachable H active = active,
              liveGraphWeight IC H) =
            ∑ H : Digraph V with (∀ w ∉ active, ∀ u ∈ tried w, ¬ H.Adj u w),
              liveGraphWeight IC H := by
          refine Finset.sum_subset (fun H hH => ?_) fun H hH hnot => ?_
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH ⊢
            exact hH.1
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH hnot
            by_cases hHG : H ≤ G
            · exact absurd ⟨hH, hreach_closed H hHG hH⟩ hnot
            · exact liveGraphWeight_eq_zero_of_not_le IC hHG
        rw [hsum_drop_reach]
        let outEdges : Finset (V × V) :=
          Finset.univ.filter fun e : V × V => e.2 ∉ active ∧ e.1 ∈ tried e.2
        have hbij :
            (∑ H : Digraph V with (∀ w ∉ active, ∀ u ∈ tried w, ¬ H.Adj u w),
              liveGraphWeight IC H) =
            ∑ E ∈ (Finset.univ : Finset (V × V)).powerset with
                (∅ : Finset (V × V)) ⊆ E ∧ Disjoint E outEdges,
              ∏ e ∈ (Finset.univ : Finset (V × V)),
                (if e ∈ E then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2) := by
          refine Finset.sum_bij (fun H _ => digraphEquivEdgeFinset V H) ?_ ?_ ?_ ?_
          · intro H hH
            have hno := (Finset.mem_filter.mp hH).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
              Finset.empty_subset _, ?_⟩
            rw [Finset.disjoint_left]
            intro ⟨x, y⟩ hxE hxo
            rcases (Finset.mem_filter.mp hxo).2 with ⟨hy, hxt⟩
            have hadjH : H.Adj x y := by
              simpa [digraphEquivEdgeFinset] using hxE
            exact hno y hy x hxt hadjH
          · intro H₁ _ H₂ _ heq
            exact (digraphEquivEdgeFinset V).injective heq
          · intro E hE
            rcases (Finset.mem_filter.mp hE).2 with ⟨_, hdisjE⟩
            let H := (digraphEquivEdgeFinset V).symm E
            refine ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
              (digraphEquivEdgeFinset V).apply_symm_apply E⟩
            intro w hw u hu hadjH
            have hmemE : (u, w) ∈ E := hadjH
            have hmemOut : (u, w) ∈ outEdges :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hu⟩
            exact Finset.disjoint_left.mp hdisjE hmemE hmemOut
          · intro H _
            unfold liveGraphWeight
            refine Finset.prod_congr rfl fun ⟨x, y⟩ _ => ?_
            simp [digraphEquivEdgeFinset]
        rw [hbij, sum_powerset_bernWeight _ _ _ _ (Finset.empty_subset _)
          (Finset.subset_univ _) (Finset.disjoint_empty_left _), Finset.prod_empty, one_mul]
        have hout_eq : outEdges =
            activeᶜ.biUnion fun w =>
              (tried w).map ⟨fun x => (x, w), fun _ _ h => congrArg Prod.fst h⟩ := by
          ext ⟨u, w⟩
          rw [Finset.mem_filter, Finset.mem_biUnion]
          simp only [Finset.mem_univ, true_and, Finset.mem_compl, Finset.mem_map]
          constructor
          · rintro ⟨hw, hu⟩
            exact ⟨w, hw, u, hu, rfl⟩
          · rintro ⟨w', hw', u', hu', hpair⟩
            change (u', w') = (u, w) at hpair
            cases hpair
            exact ⟨hw', hu'⟩
        rw [hout_eq, Finset.prod_biUnion]
        · refine Finset.prod_congr rfl fun w _ => ?_
          rw [IC.survivalProb_toCascadeModel w (tried w), Finset.prod_map]
          rfl
        · intro w₁ _ w₂ _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro ⟨x, y⟩ h₁ h₂
          rw [Finset.mem_map] at h₁ h₂
          rcases h₁ with ⟨u₁, _, hp₁⟩
          rcases h₂ with ⟨u₂, _, hp₂⟩
          change (u₁, w₁) = (x, y) at hp₁
          change (u₂, w₂) = (x, y) at hp₂
          cases hp₁
          cases hp₂
          exact hne rfl
      · simp only [hA, ↓reduceIte]
        refine Finset.sum_eq_zero fun H hH => ?_
        rcases (Finset.mem_filter.mp hH).2 with ⟨hno, hreach⟩
        by_cases hHG : H ≤ G
        · exact absurd ((hreach_closed H hHG hno).symm.trans hreach) hA
        · exact liveGraphWeight_eq_zero_of_not_le IC hHG)
    (fun active tried _ u v hu_act hv_inact _ hu_untried => by
      let tried' := Function.update tried v (insert u (tried v))
      let S_all := Finset.univ.filter fun H : Digraph V =>
        (∀ w ∉ active, ∀ x ∈ tried w, ¬ H.Adj x w) ∧ liveReachable H active = A
      have hpart : ∑ H ∈ S_all, liveGraphWeight IC H =
          (∑ H ∈ S_all with H.Adj u v, liveGraphWeight IC H) +
            (∑ H ∈ S_all with ¬ H.Adj u v, liveGraphWeight IC H) :=
        (Finset.sum_filter_add_sum_filter_not S_all (fun H : Digraph V => H.Adj u v) _).symm
      change ∑ H ∈ S_all, liveGraphWeight IC H =
        IC.toCascadeModel.prob v u (tried v) * IC.toCascadeModel.survivalProb v (tried v) *
          (∑ H : Digraph V with
              (∀ w ∉ insert v active, ∀ x ∈ tried' w, ¬ H.Adj x w) ∧
                liveReachable H (insert v active) = A,
            liveGraphWeight IC H) +
          (∑ H : Digraph V with
              (∀ w ∉ active, ∀ x ∈ tried' w, ¬ H.Adj x w) ∧ liveReachable H active = A,
            liveGraphWeight IC H)
      rw [hpart, IC.toCascadeModel_prob]
      congr 1
      · -- `H.Adj u v` branch: factor out incoming edges to `v`.
        let Base := Finset.univ.filter fun H₀ : Digraph V =>
          (∀ x, ¬ H₀.Adj x v) ∧
            (∀ w ∉ insert v active, ∀ x ∈ tried' w, ¬ H₀.Adj x w) ∧
            liveReachable H₀ (insert v active) = A
        let decompV : Digraph V → Digraph V × Finset V := fun H =>
          (⟨fun x y => y ≠ v ∧ H.Adj x y⟩, Finset.univ.filter fun x => H.Adj x v)
        let mkH : Digraph V → Finset V → Digraph V := fun H₀ X =>
          ⟨fun x y => if y = v then x ∈ X else H₀.Adj x y⟩
        have hdecomp_inj : Function.Injective decompV := by
          intro H₁ H₂ heq
          rcases Prod.mk.inj heq with ⟨h₀, hX⟩
          ext x y
          rcases eq_or_ne y v with rfl | hyv
          · simpa [decompV] using congrArg (x ∈ ·) hX
          · have h := congrFun (congrFun (congrArg Digraph.Adj h₀) x) y
            simpa [decompV, hyv] using h
        have hdecomp_mkH : ∀ {H₀ : Digraph V} (X : Finset V), (∀ x, ¬ H₀.Adj x v) →
            decompV (mkH H₀ X) = (H₀, X) := by
          intro H₀ X hnov
          refine Prod.ext ?_ ?_
          · ext x y
            rcases eq_or_ne y v with rfl | hyv
            · simp only [decompV, mkH, ↓reduceIte, ne_eq, not_true_eq_false, false_and, false_iff]
              exact hnov x
            · simp [decompV, mkH, hyv]
          · ext x
            simp [decompV, mkH]
        have hmkH_decomp : ∀ H : Digraph V, mkH (decompV H).1 (decompV H).2 = H := by
          intro H
          ext x y
          rcases eq_or_ne y v with rfl | hyv <;> simp [decompV, mkH, *]
        have hweight_mkH : ∀ H₀ ∈ Base, ∀ X : Finset V,
            liveGraphWeight IC (mkH H₀ X) =
              (∏ e ∈ Finset.univ.filter (fun e : V × V => e.2 ≠ v),
                if H₀.Adj e.1 e.2 then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2) *
              (∏ x : V, if x ∈ X then IC.edgeProb x v else 1 - IC.edgeProb x v) := by
          intro H₀ _ X
          unfold liveGraphWeight
          rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e : V × V => e.2 ≠ v)]
          congr 1
          · refine Finset.prod_congr rfl fun e he => ?_
            have hne_v : e.2 ≠ v := (Finset.mem_filter.mp he).2
            simp [mkH, hne_v]
          · have hbij : (∏ e ∈ Finset.univ.filter (fun e : V × V => ¬ e.2 ≠ v),
                if (mkH H₀ X).Adj e.1 e.2 then IC.edgeProb e.1 e.2
                else 1 - IC.edgeProb e.1 e.2) =
                ∏ x : V, if x ∈ X then IC.edgeProb x v else 1 - IC.edgeProb x v := by
              refine Finset.prod_bij (fun e _ => e.1) ?_ ?_ ?_ ?_
              · intro _ _; exact Finset.mem_univ _
              · intro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ hx
                have hy₁ : y₁ = v := not_not.mp (Finset.mem_filter.mp h₁).2
                have hy₂ : y₂ = v := not_not.mp (Finset.mem_filter.mp h₂).2
                subst hx hy₁ hy₂
                rfl
              · intro x _
                exact ⟨(x, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_not.mpr rfl⟩, rfl⟩
              · intro ⟨x, y⟩ hy
                have hyv : y = v := not_not.mp (Finset.mem_filter.mp hy).2
                subst hyv
                simp [mkH]
            convert hbij
        have hdecomp_sum : ∀ (Dom : Finset (Digraph V)) (inX outX : Finset V),
            Disjoint inX outX →
            (∀ H : Digraph V,
              H ∈ Dom ↔ decompV H ∈ Base ×ˢ
                (Finset.univ.powerset.filter fun X => inX ⊆ X ∧ Disjoint X outX)) →
            (∑ H ∈ Dom, liveGraphWeight IC H) =
              ((∏ x ∈ inX, IC.edgeProb x v) * (∏ x ∈ outX, (1 - IC.edgeProb x v))) *
              ∑ H₀ ∈ Base,
                ∏ e ∈ Finset.univ.filter (fun e : V × V => e.2 ≠ v),
                  if H₀.Adj e.1 e.2 then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2 := by
          intro Dom inX outX hdisj hDom
          let XValid := (Finset.univ : Finset V).powerset.filter
            fun X => inX ⊆ X ∧ Disjoint X outX
          have hbij : (∑ H ∈ Dom, liveGraphWeight IC H) =
              ∑ p ∈ Base ×ˢ XValid, liveGraphWeight IC (mkH p.1 p.2) := by
            refine Finset.sum_bij (fun H _ => decompV H) (fun H hH => (hDom H).mp hH)
              (fun _ _ _ _ h => hdecomp_inj h) ?_
              (fun H _ => congrArg (liveGraphWeight IC) (hmkH_decomp H).symm)
            rintro ⟨H₀, X⟩ hp
            have hnov : ∀ x, ¬ H₀.Adj x v := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2.1
            have hdec : decompV (mkH H₀ X) = (H₀, X) := hdecomp_mkH X hnov
            exact ⟨mkH H₀ X, (hDom (mkH H₀ X)).mpr (hdec.symm ▸ hp), hdec⟩
          rw [hbij, Finset.sum_product, Finset.mul_sum]
          refine Finset.sum_congr rfl fun H₀ hH₀ => ?_
          have hrow : (∑ X ∈ XValid, liveGraphWeight IC (mkH H₀ X)) =
              (∏ e ∈ Finset.univ.filter (fun e : V × V => e.2 ≠ v),
                if H₀.Adj e.1 e.2 then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2) *
              ∑ X ∈ XValid,
                ∏ x ∈ (Finset.univ : Finset V),
                  (if x ∈ X then IC.edgeProb x v else 1 - IC.edgeProb x v) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun X _ => hweight_mkH H₀ hH₀ X
          rw [hrow, sum_powerset_bernWeight (fun x => IC.edgeProb x v) Finset.univ inX outX
            (Finset.subset_univ _) (Finset.subset_univ _) hdisj, mul_comm]
        have hsum_succ :
            (∑ H : Digraph V with
                (∀ w ∉ insert v active, ∀ x ∈ tried' w, ¬ H.Adj x w) ∧
                  liveReachable H (insert v active) = A,
              liveGraphWeight IC H) =
            ∑ H₀ ∈ Base,
              ∏ e ∈ Finset.univ.filter (fun e : V × V => e.2 ≠ v),
                if H₀.Adj e.1 e.2 then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2 := by
          rw [hdecomp_sum _ ∅ ∅ (Finset.disjoint_empty_left _) ?_]
          · simp
          · intro H
            have hreach_eq :
                liveReachable (decompV H).1 (insert v active) =
                  liveReachable H (insert v active) :=
              liveReachable_congr_inEdges (Finset.mem_insert_self v active)
                fun x y hy => by simp [decompV, hy]
            simp only [Base, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
              Finset.mem_powerset, Finset.subset_univ, Finset.empty_subset,
              Finset.disjoint_empty_right, and_self, and_true, true_and, hreach_eq]
            refine ⟨fun ⟨hno, hr⟩ => ⟨fun x => by simp [decompV],
                fun w hw x hx hadj => hno w hw x hx hadj.2, hr⟩,
              fun ⟨_, hno, hr⟩ => ⟨fun w hw x hx hadj => ?_, hr⟩⟩
            have hwv : w ≠ v := fun heq => hw (heq ▸ Finset.mem_insert_self v active)
            exact hno w hw x hx ⟨hwv, hadj⟩
        have hsum_act :
            (∑ H ∈ S_all with H.Adj u v, liveGraphWeight IC H) =
            IC.edgeProb u v * IC.toCascadeModel.survivalProb v (tried v) *
            ∑ H₀ ∈ Base,
              ∏ e ∈ Finset.univ.filter (fun e : V × V => e.2 ≠ v),
                if H₀.Adj e.1 e.2 then IC.edgeProb e.1 e.2 else 1 - IC.edgeProb e.1 e.2 := by
          have hreach_ins : ∀ H : Digraph V, H.Adj u v →
              liveReachable H active = liveReachable H (insert v active) := by
            intro H huvH
            refine Finset.Subset.antisymm
              (monotone_liveReachable H (Finset.subset_insert v active)) fun z hz => ?_
            rcases mem_liveReachable.mp hz with ⟨s, hs, hp⟩
            rcases Finset.mem_insert.mp hs with rfl | hs_act
            · exact mem_liveReachable.mpr
                ⟨u, hu_act, (Relation.ReflTransGen.single huvH).trans hp⟩
            · exact mem_liveReachable.mpr ⟨s, hs_act, hp⟩
          rw [hdecomp_sum _ {u} (tried v) (Finset.disjoint_singleton_left.mpr hu_untried) ?_,
            Finset.prod_singleton, ← IC.survivalProb_toCascadeModel v (tried v)]
          intro H
          have hreach_eq :
              liveReachable (decompV H).1 (insert v active) =
                liveReachable H (insert v active) :=
            liveReachable_congr_inEdges (Finset.mem_insert_self v active)
              fun x y hy => by simp [decompV, hy]
          simp only [S_all, Base, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
            Finset.mem_powerset, Finset.subset_univ, Finset.singleton_subset_iff, true_and,
            hreach_eq]
          constructor
          · rintro ⟨⟨hno, hr⟩, huvH⟩
            refine ⟨⟨fun x => by simp [decompV], fun w hw x hx hadj => ?_,
                (hreach_ins H huvH).symm.trans hr⟩,
              by simp [decompV, huvH], Finset.disjoint_left.mpr fun x hx hxt =>
                hno v hv_inact x hxt (Finset.mem_filter.mp hx).2⟩
            have hwv : w ≠ v := fun heq => hw (heq ▸ Finset.mem_insert_self v active)
            have hwin : w ∉ active := fun ha => hw (Finset.mem_insert_of_mem ha)
            dsimp only [tried'] at hx
            rw [Function.update_of_ne hwv] at hx
            exact hno w hwin x hx hadj.2
          · rintro ⟨⟨_, hno, hr⟩, huX, hdisjX⟩
            have huvH : H.Adj u v := by simpa [decompV] using huX
            refine ⟨⟨fun w hw x hx hadj => ?_, (hreach_ins H huvH).trans hr⟩, huvH⟩
            rcases eq_or_ne w v with rfl | hwv
            · exact Finset.disjoint_left.mp hdisjX (by simp [decompV, hadj]) hx
            · have hw' : w ∉ insert v active := by simp [hwv, hw]
              have hx' : x ∈ tried' w := by simpa [tried', Function.update_of_ne hwv] using hx
              exact hno w hw' x hx' ⟨hwv, hadj⟩
        rw [hsum_succ, hsum_act]
      · -- `¬ H.Adj u v` branch: identical filter to `tried'`.
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext H
        simp only [S_all, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨hno, hreach⟩, hnotuv⟩
          refine ⟨fun w hw x hx => ?_, hreach⟩
          dsimp only [tried'] at hx
          rcases eq_or_ne w v with rfl | hwv
          · rw [Function.update_self] at hx
            rcases Finset.mem_insert.mp hx with rfl | hxt
            · exact hnotuv
            · exact hno w hv_inact x hxt
          · rw [Function.update_of_ne hwv] at hx
            exact hno w hw x hx
        · rintro ⟨hno', hreach⟩
          refine ⟨⟨fun w hw x hx => ?_, hreach⟩, ?_⟩
          · rcases eq_or_ne w v with rfl | hwv
            · exact hno' w hv_inact x (by simp [tried', Finset.mem_insert_of_mem hx])
            · exact hno' w hw x (by simp [tried', Function.update_of_ne hwv, hx])
          · exact hno' v hv_inact u (by simp [tried']))
  rw [h0]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext H
  simp

/-- **Live-Edge Expectation Formula** ([KempeKleinbergTardos2003]; [Kleinberg2007], Section 24.4,
p. 625): expected influence in the Independent Cascade Model equals the weighted sum of reachable
set sizes `|liveReachable H S|` across all realized live-edge graphs `H : Digraph V`. -/
theorem influence_eq_sum_liveGraphWeight (S : Finset V) :
    IC.influence S = ∑ H : Digraph V, liveGraphWeight IC H * ((liveReachable H S).card : ℝ) := by
  classical
  rw [influence, IC.toCascadeModel.influence_def]
  simp_rw [IC.activeSetProb_eq_sum_liveGraphWeight CascadeModel.validNextEdge_defaultNextEdge,
    Finset.sum_mul]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ => p.2) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · rintro ⟨A₁, H₁⟩ h₁ ⟨A₂, H₂⟩ h₂ hH
    dsimp only at hH
    subst hH
    have hA₁ : liveReachable H₁ S = A₁ := (Finset.mem_filter.mp (Finset.mem_sigma.mp h₁).2).2
    have hA₂ : liveReachable H₁ S = A₂ := (Finset.mem_filter.mp (Finset.mem_sigma.mp h₂).2).2
    exact Sigma.ext (hA₁.symm.trans hA₂) HEq.rfl
  · intro H _
    exact ⟨⟨liveReachable H S, H⟩,
      Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩,
      rfl⟩
  · rintro ⟨A, H⟩ h
    have hA : liveReachable H S = A := (Finset.mem_filter.mp (Finset.mem_sigma.mp h).2).2
    rw [hA]

@[simp]
theorem influence_empty : IC.influence ∅ = 0 :=
  IC.toCascadeModel.influence_empty

theorem monotone_influence : Monotone IC.influence :=
  IC.toCascadeModel.monotone_influence

/-- **Kempe–Kleinberg–Tardos Independent Cascade Submodularity Theorem**
([KempeKleinbergTardos2003]; [Kleinberg2007], Theorem 24.5, pp. 625–626): for every instance of
the Independent Cascade Model, the expected influence function `IC.influence` is submodular. -/
theorem isSubmodular_influence : IsSubmodular IC.influence := by
  have hcov : ∀ H : Digraph V,
      (fun S : Finset V => liveGraphWeight IC H * ((liveReachable H S).card : ℝ)) =
        weightedCoverage (liveReachableFrom H) (fun _ => liveGraphWeight IC H) := by
    intro H
    ext S
    simp [weightedCoverage, liveReachable, mul_comm]
  have heq : IC.influence =
      fun S => ∑ H : Digraph V,
        weightedCoverage (liveReachableFrom H) (fun _ => liveGraphWeight IC H) S := by
    ext S
    rw [IC.influence_eq_sum_liveGraphWeight]
    exact Finset.sum_congr rfl fun H _ => congrFun (hcov H) S
  rw [heq]
  exact isSubmodular_sum Finset.univ fun H _ =>
    isSubmodular_weightedCoverage (liveReachableFrom H) fun _ => liveGraphWeight_nonneg IC H

end IndependentCascadeModel

end LiveEdge

/-! ## Theorem 24.6: Mossel–Roch General Threshold Submodularity -/

section MosselRoch

/-- Order-reversing involution on `Ioo c 1` fixing all points outside `Ioo c 1`. -/
private noncomputable def reflectUnit (c z : ℝ) : ℝ :=
  if z ∈ Ioo c 1 then 1 + c - z else z

private theorem reflectUnit_involutive (c : ℝ) : Function.Involutive (reflectUnit c) := by
  intro z
  unfold reflectUnit
  by_cases hz : z ∈ Ioo c 1
  · have hz' : 1 + c - z ∈ Ioo c 1 := by
      rcases hz with ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    simp only [hz, ↓reduceIte, hz']
    ring
  · simp [hz]

private theorem measurable_reflectUnit (c : ℝ) : Measurable (reflectUnit c) :=
  Measurable.ite measurableSet_Ioo (measurable_const.sub measurable_id) measurable_id

private theorem measurePreserving_reflectUnit {c : ℝ} (hc0 : 0 ≤ c) :
    MeasurePreserving (reflectUnit c) unitMeasure unitMeasure where
  measurable := measurable_reflectUnit c
  map_eq := by
    ext s hs
    rw [Measure.map_apply (measurable_reflectUnit c) hs]
    let J := Ioo c 1
    have hJ_sub : J ⊆ Icc 0 1 := fun z hz => ⟨hc0.trans hz.1.le, hz.2.le⟩
    have hpre_split : reflectUnit c ⁻¹' s =
        ((fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J) ∩ J) ∪ (s \ J) := by
      ext z
      simp only [mem_preimage, reflectUnit, J, mem_union, mem_inter_iff, mem_sdiff]
      by_cases hz : z ∈ Ioo c 1
      · have hz' : (1 + c) - z ∈ Ioo c 1 := ⟨by linarith [hz.2], by linarith [hz.1]⟩
        simp [hz, hz']
      · simp [hz]
    have hpre_inJ : (fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J) ⊆ J := by
      intro z hz
      rcases hz.2 with ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    have hpre_inter : (fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J) ∩ J =
        (fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J) :=
      inter_eq_left.mpr hpre_inJ
    rw [hpre_split, hpre_inter]
    have hdisj1 : Disjoint ((fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J)) (s \ J) :=
      Disjoint.mono_left hpre_inJ disjoint_sdiff_right
    have hm_sJ : MeasurableSet (s ∩ J) := hs.inter measurableSet_Ioo
    have hm_diff : MeasurableSet (s \ J) := hs.diff measurableSet_Ioo
    have hm_pre : MeasurableSet ((fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J)) :=
      hm_sJ.preimage (measurable_const.sub measurable_id)
    rw [measure_union hdisj1 hm_diff]
    have hvol_eq : unitMeasure ((fun z : ℝ => (1 + c) - z) ⁻¹' (s ∩ J)) = unitMeasure (s ∩ J) := by
      rw [unitMeasure_def, Measure.restrict_apply hm_pre, Measure.restrict_apply hm_sJ,
        inter_eq_left.mpr (hpre_inJ.trans hJ_sub),
        inter_eq_left.mpr (inter_subset_right.trans hJ_sub)]
      exact (volume.measurePreserving_sub_left (1 + c)).measure_preimage hm_sJ.nullMeasurableSet
    have hdisj2 : Disjoint (s ∩ J) (s \ J) :=
      Disjoint.mono_left inter_subset_right disjoint_sdiff_right
    rw [hvol_eq, ← measure_union hdisj2 hm_diff, inter_union_sdiff]

namespace GeneralThresholdModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (M : GeneralThresholdModel G)

/-- Coordinatewise threshold reflection outside `K`: preserves `U v` for `v ∈ K` and reflects
`U v ∈ (g_v(K), 1)` to `1 + g_v(K) - U v` for `v ∉ K`. -/
private noncomputable def reflectMap (K : Finset V) (U : V → ℝ) : V → ℝ :=
  fun v => if v ∈ K then U v else reflectUnit (M.thresholdFn v K) (U v)

private theorem reflectMap_involutive (K : Finset V) :
    Function.Involutive (M.reflectMap K) := by
  intro U
  ext v
  unfold reflectMap
  by_cases hv : v ∈ K
  · simp [hv]
  · simp only [hv, ↓reduceIte]
    exact reflectUnit_involutive (M.thresholdFn v K) (U v)

private theorem measurePreserving_reflectMap (K : Finset V) :
    MeasurePreserving (M.reflectMap K) (thresholdMeasure V) (thresholdMeasure V) := by
  rw [thresholdMeasure_def V]
  exact measurePreserving_pi (fun _ : V => unitMeasure) (fun _ : V => unitMeasure)
    (f := fun v z => if v ∈ K then z else reflectUnit (M.thresholdFn v K) z) fun v => by
    by_cases hv : v ∈ K
    · simp only [hv, ↓reduceIte]
      exact MeasurePreserving.id unitMeasure
    · simp only [hv, ↓reduceIte]
      exact measurePreserving_reflectUnit (M.thresholdFn_nonneg v K)

/-- Conditional reflection coupling from seed `X` to superset `Y`: runs `X` under `U` to obtain
`K = M.thresholdFinal U X`, reflects surviving thresholds on `Kᶜ`, and continues from `K ∪ Y`. -/
private noncomputable def reflectCouple (X Y : Finset V) (U : V → ℝ) : Finset V :=
  let K := M.thresholdFinal U X
  M.thresholdFinal (M.reflectMap K U) (K ∪ Y)

/-- **Reflection Marginal-Law Identity** ([MosselRoch2007]): whenever `X ⊆ Y`, `M.reflectCouple X Y`
has the exact same expectation under `thresholdMeasure V` as `U ↦ M.thresholdFinal U Y`. -/
private theorem integral_reflectCouple {X Y : Finset V} (hXY : X ⊆ Y) (φ : Finset V → ℝ) :
    (∫ U, φ (M.reflectCouple X Y U) ∂thresholdMeasure V) =
      ∫ U, φ (M.thresholdFinal U Y) ∂thresholdMeasure V := by
  let E : Finset V → Set (V → ℝ) := fun K =>
    {U : V → ℝ | M.thresholdFinal U X = K ∧ ∀ v : V, U v < 1}
  have hmE : ∀ K : Finset V, MeasurableSet (E K) := by
    intro K
    have heqE : E K = {U | M.thresholdFinal U X = K} ∩
        ⋂ v : V, (fun U : V → ℝ => U v) ⁻¹' Iio 1 := by
      ext U
      simp [E]
    rw [heqE]
    exact (M.measurableSet_thresholdFinal_eq X K).inter
      (MeasurableSet.iInter fun v => measurableSet_Iio.preimage (measurable_pi_apply v))
  have hmem_reflect : ∀ (K : Finset V) (U : V → ℝ), U ∈ E K ↔ M.reflectMap K U ∈ E K := by
    suffices dir : ∀ (K : Finset V) (U : V → ℝ), U ∈ E K → M.reflectMap K U ∈ E K from
      fun K U => ⟨dir K U, fun h => M.reflectMap_involutive K U ▸ dir K _ h⟩
    intro K U ⟨hfin, hlt1⟩
    rw [M.thresholdFinal_eq_iff_piecewise] at hfin
    rcases hfin with ⟨hpiece, hsurv⟩
    have hpiece_eq : K.piecewise (M.reflectMap K U) (fun _ => (2 : ℝ)) =
        K.piecewise U (fun _ => (2 : ℝ)) := by
      ext v
      by_cases hv : v ∈ K
      · simp [reflectMap, hv]
      · simp [Finset.piecewise_eq_of_notMem _ _ _ hv]
    refine ⟨(M.thresholdFinal_eq_iff_piecewise _ X K).mpr ⟨hpiece_eq ▸ hpiece, fun v hvK => ?_⟩,
      fun v => ?_⟩
    · have hmem : U v ∈ Ioo (M.thresholdFn v K) 1 := ⟨hsurv v hvK, hlt1 v⟩
      simp only [reflectMap, hvK, ↓reduceIte, reflectUnit, hmem]
      linarith [hmem.2]
    · by_cases hvK : v ∈ K
      · simp [reflectMap, hvK, hlt1 v]
      · have hmem : U v ∈ Ioo (M.thresholdFn v K) 1 := ⟨hsurv v hvK, hlt1 v⟩
        simp only [reflectMap, hvK, ↓reduceIte, reflectUnit, hmem]
        linarith [hmem.1]
  have hsum_ae : ∀ ψ : (V → ℝ) → ℝ, ∀ᵐ U ∂thresholdMeasure V,
      ψ U = ∑ K : Finset V, (E K).indicator ψ U := by
    intro ψ
    filter_upwards [ae_mem_Ioo_thresholdMeasure V] with U hU
    rw [Finset.sum_eq_single (M.thresholdFinal U X)]
    · have hmem : U ∈ E (M.thresholdFinal U X) := ⟨rfl, fun v => (hU v).2⟩
      rw [indicator_of_mem hmem]
    · intro K _ hne
      have hnot : U ∉ E K := fun h => hne h.1.symm
      rw [indicator_of_notMem hnot]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  have hsum_lhs := hsum_ae fun U' => φ (M.reflectCouple X Y U')
  have hsum_rhs := hsum_ae fun U' => φ (M.thresholdFinal U' Y)
  have hint_piece_rhs : ∀ K : Finset V,
      Integrable ((E K).indicator fun U => φ (M.thresholdFinal U Y)) (thresholdMeasure V) :=
    fun K => (M.integrable_of_finset Y φ).indicator (hmE K)
  have hterm_eq : ∀ (K : Finset V) (U : V → ℝ),
      (E K).indicator (fun U' => φ (M.reflectCouple X Y U')) U =
        (E K).indicator (fun U' => φ (M.thresholdFinal U' Y)) (M.reflectMap K U) := by
    intro K U
    by_cases hU : U ∈ E K
    · have hRU : M.reflectMap K U ∈ E K := (hmem_reflect K U).mp hU
      rw [indicator_of_mem hU, indicator_of_mem hRU]
      dsimp only [reflectCouple]
      rw [hU.1]
      have hYK : K ∪ Y = M.thresholdFinal (M.reflectMap K U) X ∪ Y := by rw [hRU.1]
      rw [hYK, M.thresholdFinal_union_eq, Finset.union_eq_right.mpr hXY]
    · have hRU : M.reflectMap K U ∉ E K := mt (hmem_reflect K U).mpr hU
      rw [indicator_of_notMem hU, indicator_of_notMem hRU]
  have hint_piece_lhs : ∀ K : Finset V,
      Integrable ((E K).indicator fun U => φ (M.reflectCouple X Y U)) (thresholdMeasure V) := by
    intro K
    have hfn : ((E K).indicator fun U => φ (M.reflectCouple X Y U)) =
        fun U => (E K).indicator (fun U' => φ (M.thresholdFinal U' Y)) (M.reflectMap K U) :=
      funext (hterm_eq K)
    rw [hfn]
    exact (M.measurePreserving_reflectMap K).integrable_comp_of_integrable (hint_piece_rhs K)
  rw [integral_congr_ae hsum_lhs, integral_congr_ae hsum_rhs,
    integral_finsetSum _ (fun K _ => hint_piece_lhs K),
    integral_finsetSum _ (fun K _ => hint_piece_rhs K)]
  refine Finset.sum_congr rfl fun K _ => ?_
  have hfn : ((E K).indicator fun U => φ (M.reflectCouple X Y U)) =
      fun U => (E K).indicator (fun U' => φ (M.thresholdFinal U' Y)) (M.reflectMap K U) :=
    funext (hterm_eq K)
  rw [hfn]
  have hp := M.measurePreserving_reflectMap K
  conv_rhs => rw [← hp.map_eq]
  rw [integral_map hp.measurable.aemeasurable
    (by rw [hp.map_eq]; exact (hint_piece_rhs K).aestronglyMeasurable)]

private theorem integrable_reflectCouple (X Y : Finset V) (φ : Finset V → ℝ) :
    Integrable (fun U => φ (M.reflectCouple X Y U)) (thresholdMeasure V) := by
  have heq : (fun U : V → ℝ => φ (M.reflectCouple X Y U)) =
      fun U => ∑ K : Finset V, ∑ L : Finset V,
        ({U' : V → ℝ | M.thresholdFinal U' X = K} ∩
          {U' : V → ℝ | M.thresholdFinal (M.reflectMap K U') (K ∪ Y) = L}).indicator
          (fun _ => φ L) U := by
    ext U
    rw [Finset.sum_eq_single (M.thresholdFinal U X)]
    · rw [Finset.sum_eq_single (M.reflectCouple X Y U)]
      · simp [reflectCouple]
      · intro L _ hne
        have hnot : U ∉ {U' : V → ℝ | M.thresholdFinal U' X = M.thresholdFinal U X} ∩
            {U' : V → ℝ |
              M.thresholdFinal (M.reflectMap (M.thresholdFinal U X) U')
                (M.thresholdFinal U X ∪ Y) = L} :=
          fun h => hne h.2.symm
        exact indicator_of_notMem hnot _
      · intro habs; exact absurd (Finset.mem_univ _) habs
    · intro K _ hne
      refine Finset.sum_eq_zero fun L _ => ?_
      have hnot : U ∉ {U' : V → ℝ | M.thresholdFinal U' X = K} ∩
          {U' : V → ℝ | M.thresholdFinal (M.reflectMap K U') (K ∪ Y) = L} :=
        fun h => hne h.1.symm
      exact indicator_of_notMem hnot _
    · intro habs; exact absurd (Finset.mem_univ _) habs
  rw [heq]
  refine integrable_finsetSum _ fun K _ => integrable_finsetSum _ fun L _ => ?_
  refine (integrable_const (φ L)).indicator ((M.measurableSet_thresholdFinal_eq X K).inter ?_)
  exact (M.measurableSet_thresholdFinal_eq (K ∪ Y) L).preimage
    (M.measurePreserving_reflectMap K).measurable

/-- Monotonicity of general threshold expectations for any monotone objective `φ`. -/
theorem monotone_integral_thresholdFinal {φ : Finset V → ℝ} (hmono : Monotone φ) :
    Monotone (fun S : Finset V => ∫ θ, φ (M.thresholdFinal θ S) ∂thresholdMeasure V) := by
  intro A B hAB
  exact integral_mono (M.integrable_of_finset A φ) (M.integrable_of_finset B φ) fun θ =>
    hmono (M.thresholdFinal_mono_seed θ hAB)

/-- **Mossel–Roch Functional Submodularity Theorem** ([MosselRoch2007]; generalizing
[Kleinberg2007], Theorem 24.6, p. 626): if every local threshold function `M.thresholdFn v` is
submodular, then for every monotone submodular objective `φ : Finset V → ℝ`, the expected value
`S ↦ ∫ θ, φ (M.thresholdFinal θ S) ∂thresholdMeasure V` is submodular. -/
theorem isSubmodular_integral_thresholdFinal
    (hlocal : ∀ v, IsSubmodular (M.thresholdFn v))
    {φ : Finset V → ℝ} (hφ_mono : Monotone φ) (hφ_sub : IsSubmodular φ) :
    IsSubmodular (fun S : Finset V => ∫ θ, φ (M.thresholdFinal θ S) ∂thresholdMeasure V) := by
  intro A B
  dsimp only
  rw [← M.integral_reflectCouple (Finset.subset_union_left (s₁ := A) (s₂ := B)) φ,
    ← M.integral_reflectCouple (Finset.inter_subset_right (s₁ := A) (s₂ := B)) φ]
  have hintD := M.integrable_reflectCouple A (A ∪ B) φ
  have hintB := M.integrable_reflectCouple (A ∩ B) B φ
  rw [← integral_add hintD (M.integrable_of_finset (A ∩ B) φ),
    ← integral_add (M.integrable_of_finset A φ) hintB]
  refine integral_mono_ae (hintD.add (M.integrable_of_finset (A ∩ B) φ))
    ((M.integrable_of_finset A φ).add hintB) ?_
  filter_upwards [ae_mem_Ioo_thresholdMeasure V] with U hU
  have hlt1 : ∀ v : V, U v < 1 := fun v => (hU v).2
  set Cstar := M.thresholdFinal U (A ∩ B)
  set Astar := M.thresholdFinal U A
  set Bstar := M.reflectCouple (A ∩ B) B U
  set Dstar := M.reflectCouple A (A ∪ B) U
  have hCA : Cstar ⊆ Astar := M.thresholdFinal_mono_seed U Finset.inter_subset_left
  have hCB : Cstar ⊆ Bstar :=
    Finset.subset_union_left.trans (M.subset_thresholdFinal (M.reflectMap Cstar U) (Cstar ∪ B))
  have hC_inter : Cstar ⊆ Astar ∩ Bstar := Finset.subset_inter hCA hCB
  -- Show `Dstar ⊆ Astar ∪ Bstar` via the least post-fixed point property of `thresholdFinal`.
  have hD_union : Dstar ⊆ Astar ∪ Bstar := by
    have hD_eq : Dstar = M.thresholdFinal (M.reflectMap Astar U) (Astar ∪ B) := by
      have hunion : Astar ∪ (A ∪ B) = Astar ∪ B := by
        have hAsub : A ⊆ Astar := M.subset_thresholdFinal U A
        ext v
        simp only [Finset.mem_union]
        exact ⟨fun h => h.elim Or.inl fun h' => h'.elim (fun hvA => Or.inl (hAsub hvA)) Or.inr,
          fun h => h.elim Or.inl (Or.inr ∘ Or.inr)⟩
      change M.thresholdFinal (M.reflectMap Astar U) (Astar ∪ (A ∪ B)) = _
      rw [hunion]
    rw [hD_eq]
    have hB_sub : B ⊆ Bstar :=
      Finset.subset_union_right.trans (M.subset_thresholdFinal (M.reflectMap Cstar U) (Cstar ∪ B))
    refine M.thresholdFinal_subset_of_lt (Finset.union_subset_union_right hB_sub) fun v hvAB => ?_
    have hvA : v ∉ Astar := fun h => hvAB (Finset.mem_union_left _ h)
    have hvB : v ∉ Bstar := fun h => hvAB (Finset.mem_union_right _ h)
    have hvC : v ∉ Cstar := fun h => hvA (hCA h)
    have hA_lt : M.thresholdFn v Astar < U v := M.thresholdFn_lt_of_notMem_thresholdFinal hvA
    have hC_lt : M.thresholdFn v Cstar < U v := M.thresholdFn_lt_of_notMem_thresholdFinal hvC
    have hB_lt : M.thresholdFn v Bstar < M.reflectMap Cstar U v :=
      M.thresholdFn_lt_of_notMem_thresholdFinal hvB
    have hRA : M.reflectMap Astar U v = 1 + M.thresholdFn v Astar - U v := by
      have hmem : U v ∈ Ioo (M.thresholdFn v Astar) 1 := ⟨hA_lt, hlt1 v⟩
      simp [reflectMap, hvA, reflectUnit, hmem]
    have hRC : M.reflectMap Cstar U v = 1 + M.thresholdFn v Cstar - U v := by
      have hmem : U v ∈ Ioo (M.thresholdFn v Cstar) 1 := ⟨hC_lt, hlt1 v⟩
      simp [reflectMap, hvC, reflectUnit, hmem]
    have hsub_v := hlocal v Astar Bstar
    have hC_le_inter : M.thresholdFn v Cstar ≤ M.thresholdFn v (Astar ∩ Bstar) :=
      M.monotone v hC_inter
    rw [hRA]
    rw [hRC] at hB_lt
    linarith
  calc φ Dstar + φ Cstar
      ≤ φ (Astar ∪ Bstar) + φ (Astar ∩ Bstar) :=
        add_le_add (hφ_mono hD_union) (hφ_mono hC_inter)
    _ ≤ φ Astar + φ Bstar := hφ_sub Astar Bstar

/-- **Mossel–Roch General Threshold Submodularity Theorem** ([MosselRoch2007]; [Kleinberg2007],
Theorem 24.6, p. 626): for any instance of the General Threshold Model in which all local threshold
functions `M.thresholdFn v` are submodular, the global expected influence function `M.influence` is
submodular. -/
theorem isSubmodular_influence (hlocal : ∀ v, IsSubmodular (M.thresholdFn v)) :
    IsSubmodular M.influence := by
  have heq : M.influence = fun S => ∫ θ, ((M.thresholdFinal θ S).card : ℝ) ∂thresholdMeasure V :=
    funext M.influence_def
  rw [heq]
  have hcard_mono : Monotone (fun X : Finset V => (X.card : ℝ)) :=
    fun _ _ h => Nat.cast_le.mpr (Finset.card_le_card h)
  have hcard_sub : IsSubmodular (fun X : Finset V => (X.card : ℝ)) := by
    intro A B
    dsimp only
    exact_mod_cast (Finset.card_union_add_card_inter A B).le
  exact M.isSubmodular_integral_thresholdFinal hlocal hcard_mono hcard_sub

/-- Lifting a locally submodular `GeneralThresholdModel` to `timeLayeredDigraph G T` preserves
submodularity of all local threshold functions. -/
theorem isSubmodular_toTimeLayered_thresholdFn
    (hlocal : ∀ v, IsSubmodular (M.thresholdFn v)) (T : ℕ)
    (vt : V × Fin (T + 1)) :
    IsSubmodular ((M.toTimeLayered T).thresholdFn vt) := by
  intro A B
  simp only [M.toTimeLayered_thresholdFn]
  split_ifs with h0
  · simp
  · set prev : Fin (T + 1) := ⟨(vt.2 : ℕ) - 1, by omega⟩
    let slice : Finset (V × Fin (T + 1)) → Finset V :=
      fun X => Finset.univ.filter fun u => (u, prev) ∈ X
    have hU : slice (A ∪ B) = slice A ∪ slice B := by
      ext u
      simp [slice]
    have hI : slice (A ∩ B) = slice A ∩ slice B := by
      ext u
      simp [slice]
    change M.thresholdFn vt.1 (slice (A ∪ B)) + M.thresholdFn vt.1 (slice (A ∩ B)) ≤
      M.thresholdFn vt.1 (slice A) + M.thresholdFn vt.1 (slice B)
    rw [hU, hI]
    exact hlocal vt.1 (slice A) (slice B)

/-- Monotonicity of expected step-`t` active count in the `T`-step nonprogressive threshold
process ([Kleinberg2007], Section 24.3, p. 622). -/
theorem monotone_nonprogStepInfluence (T : ℕ) (t : Fin (T + 1)) :
    Monotone (M.nonprogStepInfluence T t) := by
  intro A B hAB
  rw [M.nonprogStepInfluence_eq_toTimeLayered, M.nonprogStepInfluence_eq_toTimeLayered]
  have hφ_mono : Monotone (fun X : Finset (V × Fin (T + 1)) =>
      ((X.filter (·.2 = t)).card : ℝ)) :=
    fun _ _ h => Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ h))
  exact (M.toTimeLayered T).monotone_integral_thresholdFinal hφ_mono
    (by
      intro x hx
      rcases mem_seedLayer0.mp hx with ⟨h0, hxA⟩
      exact mem_seedLayer0.mpr ⟨h0, hAB hxA⟩)

/-- Submodularity of expected step-`t` active count in the `T`-step nonprogressive threshold
process via `timeLayeredDigraph G T` and Theorem 24.6 ([KempeKleinbergTardos2003];
[MosselRoch2007]; [Kleinberg2007], Sections 24.3–24.4, pp. 622, 626). -/
theorem isSubmodular_nonprogStepInfluence
    (hlocal : ∀ v, IsSubmodular (M.thresholdFn v)) (T : ℕ) (t : Fin (T + 1)) :
    IsSubmodular (M.nonprogStepInfluence T t) := by
  intro A B
  simp only [M.nonprogStepInfluence_eq_toTimeLayered, seedLayer0_union, seedLayer0_inter]
  let φ : Finset (V × Fin (T + 1)) → ℝ := fun X => ((X.filter (·.2 = t)).card : ℝ)
  have hφ_mono : Monotone φ :=
    fun _ _ h => Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ h))
  have hφ_sub : IsSubmodular φ := by
    intro X Y
    dsimp only [φ]
    have hfU : (X ∪ Y).filter (·.2 = t) = X.filter (·.2 = t) ∪ Y.filter (·.2 = t) :=
      Finset.filter_union _ _ _
    have hfI : (X ∩ Y).filter (·.2 = t) = X.filter (·.2 = t) ∩ Y.filter (·.2 = t) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_inter]
      tauto
    rw [hfU, hfI]
    exact_mod_cast (Finset.card_union_add_card_inter _ _).le
  exact (M.toTimeLayered T).isSubmodular_integral_thresholdFinal
    (M.isSubmodular_toTimeLayered_thresholdFn hlocal T) hφ_mono hφ_sub
    (seedLayer0 T A) (seedLayer0 T B)

end GeneralThresholdModel

/-! ### Linear Threshold Model Specialization -/

namespace LinearThresholdModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (L : LinearThresholdModel G)

/-- Every local threshold function of a `LinearThresholdModel` is modular, hence submodular
([Kleinberg2007], Section 24.4, p. 626). -/
theorem isSubmodular_toGeneralThresholdModel_thresholdFn (v : V) :
    IsSubmodular (L.toGeneralThresholdModel.thresholdFn v) := by
  have heq : L.toGeneralThresholdModel.thresholdFn v = modularSum (fun u => L.weight u v) := by
    ext X
    simp [modularSum]
  rw [heq]
  exact isSubmodular_modularSum _

/-- Expected influence in any `LinearThresholdModel` is submodular
([KempeKleinbergTardos2003]; [Kleinberg2007], Section 24.4, p. 626). -/
theorem isSubmodular_influence : IsSubmodular L.toGeneralThresholdModel.influence :=
  L.toGeneralThresholdModel.isSubmodular_influence
    L.isSubmodular_toGeneralThresholdModel_thresholdFn

end LinearThresholdModel

end MosselRoch

/-! ## Theorem 24.4: Diminishing-Returns Cascade Submodularity -/

namespace CascadeModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (C : CascadeModel G)

/-- If a `CascadeModel` has diminishing-returns incremental probabilities (`HasDiminishingReturns`),
every local threshold function of `C.toGeneralThresholdModel` is submodular
([KempeKleinbergTardos2005]; [Kleinberg2007], Section 24.4, p. 626). -/
theorem isSubmodular_toGeneralThresholdModel_thresholdFn (hdim : C.HasDiminishingReturns)
    (v : V) : IsSubmodular (C.toGeneralThresholdModel.thresholdFn v) := by
  rw [isSubmodular_iff_marginalGain_le]
  intro X Y u hXY huY
  have huX : u ∉ X := fun h => huY (hXY h)
  have hgain : ∀ {Z : Finset V}, u ∉ Z →
      marginalGain (C.toGeneralThresholdModel.thresholdFn v) Z u =
        C.survivalProb v Z * C.prob v u Z := by
    intro Z huZ
    simp only [marginalGain, toGeneralThresholdModel_thresholdFn, C.survivalProb_insert v huZ]
    ring
  rw [hgain huY, hgain huX]
  exact mul_le_mul (C.survivalProb_anti v hXY) (hdim v u hXY huY)
    (C.prob_nonneg v u Y) (C.survivalProb_nonneg v X)

/-- **Kempe–Kleinberg–Tardos Diminishing-Returns Cascade Submodularity Theorem**
([KempeKleinbergTardos2003]; [KempeKleinbergTardos2005]; [Kleinberg2007], Theorem 24.4,
pp. 624, 626): for any instance of the Cascade Model whose incremental functions satisfy
`HasDiminishingReturns`, the resulting expected influence function `C.influence` is submodular. -/
theorem isSubmodular_influence_of_diminishingReturns (hdim : C.HasDiminishingReturns) :
    IsSubmodular C.influence := by
  have heq : C.influence = C.toGeneralThresholdModel.influence :=
    funext C.influence_eq_toGeneralThresholdModel
  rw [heq]
  exact C.toGeneralThresholdModel.isSubmodular_influence
    (C.isSubmodular_toGeneralThresholdModel_thresholdFn hdim)

end CascadeModel

/-! ## Greedy `(1 - 1/e)` Influence Maximization Guarantees (Theorem 24.3 + Theorems 24.4–24.6) -/

section GreedyGuarantees

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]

/-- **`(1 - 1/e)` Greedy Influence Maximization for Locally Submodular Threshold Models**
([NemhauserWolseyFisher1978]; [KempeKleinbergTardos2003]; [MosselRoch2007]; [Kleinberg2007],
Theorems 24.3 and 24.6, pp. 623–626): `k`-step `submodularGreedy` achieves at least
`(1 - Real.exp (-1)) * M.influence OPT` against every `OPT ⊆ xs.toFinset` with `OPT.card ≤ k`. -/
theorem GeneralThresholdModel.one_sub_exp_neg_one_mul_le_greedy_influence
    (M : GeneralThresholdModel G) (hlocal : ∀ v, IsSubmodular (M.thresholdFn v))
    (xs : List V) (k : ℕ) {OPT : Finset V}
    (hOPT_sub : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ k) :
    (1 - Real.exp (-1)) * M.influence OPT ≤
      M.influence (submodularGreedy M.influence xs k) :=
  one_sub_exp_neg_one_mul_le_submodularGreedy (M.isSubmodular_influence hlocal)
    M.monotone_influence M.influence_empty.ge xs k hOPT_sub hOPT_card

/-- **`(1 - 1/e)` Greedy Influence Maximization for Diminishing-Returns Cascade Models**
([NemhauserWolseyFisher1978]; [KempeKleinbergTardos2003]; [KempeKleinbergTardos2005];
[Kleinberg2007], Theorems 24.3 and 24.4, pp. 623–626). -/
theorem CascadeModel.one_sub_exp_neg_one_mul_le_greedy_influence
    (C : CascadeModel G) (hdim : C.HasDiminishingReturns)
    (xs : List V) (k : ℕ) {OPT : Finset V}
    (hOPT_sub : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ k) :
    (1 - Real.exp (-1)) * C.influence OPT ≤
      C.influence (submodularGreedy C.influence xs k) :=
  one_sub_exp_neg_one_mul_le_submodularGreedy
    (C.isSubmodular_influence_of_diminishingReturns hdim)
    C.monotone_influence C.influence_empty.ge xs k hOPT_sub hOPT_card

/-- **`(1 - 1/e)` Greedy Influence Maximization for Independent Cascade Models**
([NemhauserWolseyFisher1978]; [KempeKleinbergTardos2003]; [Kleinberg2007], Theorems 24.3 and 24.5,
pp. 623–626). -/
theorem IndependentCascadeModel.one_sub_exp_neg_one_mul_le_greedy_influence
    (IC : IndependentCascadeModel G)
    (xs : List V) (k : ℕ) {OPT : Finset V}
    (hOPT_sub : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ k) :
    (1 - Real.exp (-1)) * IC.influence OPT ≤
      IC.influence (submodularGreedy IC.influence xs k) :=
  one_sub_exp_neg_one_mul_le_submodularGreedy IC.isSubmodular_influence
    IC.monotone_influence IC.influence_empty.ge xs k hOPT_sub hOPT_card

end GreedyGuarantees

end Cslib.GameTheory.Network
