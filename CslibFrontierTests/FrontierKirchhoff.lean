/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Frontier.Dual.Kirchhoff
import Mathlib.Algebra.Field.ZMod

/-!
# Checked tests for Kirchhoff `1`-symbol additive-component frontier deduplication

Exercises across the `module` boundary:
1. **Cyclic `coker = A` solvability over `ZMod 7`:** On the cyclic `3`-vertex triangle
   `0 → 1 → 2 → 0`, `Multigraph.sum_netFlow_eq_cutFlow` and `Multigraph.exists_netFlow_eq_iff`
   characterize solvable demands as zero-sum (`![2, 3, 2]` is solvable over `ZMod 7`; `![1, 0, 0]`
   is unsolvable).
2. **Acyclic forest bridge uniqueness (`Multigraph.eq_of_netFlow_eq_of_isForest`):** On the `2`-edge
   path `0 → 1 → 2`, `IsForest` forces unique wire assignments over any abelian group `A`.
3. **Simultaneous zero-overlap `COPY` + Kirchhoff `XOR` (`ZMod 2`) deduplication:** On an
   `8`-vertex, `6`-edge network with a `3`-wire `COPY` star on `{0, 1, 2, 3}` and a vertex-disjoint
   `3`-wire `XOR` (`ZMod 2`) star on `{4, 5, 6, 7}`, the cut `P = {0, 4}` has `|δ(P)| = 6` raw cut
   edges (`2^6 = 64` naive frontier states), compressed width `6 - 2 - 2 = 2`, at most `2^2 = 4`
   compressed states (`ncard_state_le`, `logb_ncard_state_le`), exact acceptance
   (`accepted_branchingProgram`), and provable unambiguity (`unambiguous_branchingProgram`).
-/

set_option linter.privateModule false

open Set Cslib.Circuits.Frontier Cslib.Circuits.Frontier.Dual

namespace CslibFrontierTests.FrontierKirchhoff

/-! ### 1. Cyclic triangle over `ZMod 7`: `coker = ZMod 7` solvability iff -/

/-- Oriented `3`-cycle `0 → 1 → 2 → 0` on `Fin 3`. -/
private def triangleGraph : Multigraph (Fin 3) (Fin 3) where
  src i := i
  tgt i := i + 1

private theorem triangleGraph_connected :
    (triangleGraph.subgraph univ univ
      (fun _ _ => ⟨trivial, trivial⟩)).toSimpleGraph.Connected := by
  let H := triangleGraph.subgraph univ univ (fun _ _ => ⟨trivial, trivial⟩)
  refine (Cslib.Multigraph.connected_toSimpleGraph_iff H.ends).mpr ⟨⟨⟨0, trivial⟩⟩, ?_⟩
  intro S ⟨u, hu⟩ hS
  have hex : ∃ v : {x : Fin 3 // x ∈ (univ : Set (Fin 3))}, v ∉ S := by
    by_contra! hall
    exact hS (Finset.eq_univ_of_forall hall)
  obtain ⟨v, hv⟩ := hex
  have hadj : H.toSimpleGraph.Adj u v := by
    have hne : u ≠ v := fun h => hv (h ▸ hu)
    refine Multigraph.toSimpleGraph_adj.mpr ⟨hne, ?_⟩
    obtain ⟨uval, _⟩ := u
    obtain ⟨vval, _⟩ := v
    have hval : uval ≠ vval := fun h => hne (Subtype.ext h)
    fin_cases uval <;> fin_cases vval
    · contradiction
    · exact ⟨⟨0, trivial⟩, rfl⟩
    · exact ⟨⟨2, trivial⟩, Sym2.eq_swap⟩
    · exact ⟨⟨0, trivial⟩, Sym2.eq_swap⟩
    · contradiction
    · exact ⟨⟨1, trivial⟩, rfl⟩
    · exact ⟨⟨2, trivial⟩, rfl⟩
    · exact ⟨⟨1, trivial⟩, Sym2.eq_swap⟩
    · contradiction
  obtain ⟨_, e, he⟩ := Multigraph.toSimpleGraph_adj.mp hadj
  exact ⟨e, Cslib.Multigraph.mem_edgeCut.mpr ⟨u, hu, v, Finset.mem_compl.mpr hv, he⟩⟩

/-- On the cyclic triangle over `ZMod 7`, demand `![2, 3, 2]` sums to `0` (`2 + 3 + 2 = 7 = 0`), so
a satisfying internal flow exists. -/
example : ∃ w : Fin 3 → ZMod 7,
    ∀ v : Fin 3, triangleGraph.netFlow univ w v = (![2, 3, 2] : Fin 3 → ZMod 7) v := by
  have hiff := triangleGraph.exists_netFlow_eq_iff (K := univ) (F := univ)
    (fun _ _ => ⟨trivial, trivial⟩) triangleGraph_connected (0 : Fin 3 → ZMod 7) ![2, 3, 2]
  have hsum :
      ∑ v ∈ (toFinite (univ : Set (Fin 3))).toFinset, (![2, 3, 2] : Fin 3 → ZMod 7) v = 0 := by
    have hfin : (toFinite (univ : Set (Fin 3))).toFinset = Finset.univ := by ext; simp
    rw [hfin]
    decide
  obtain ⟨w, -, hw⟩ := hiff.mpr hsum
  exact ⟨w, fun v => hw v trivial⟩

/-- Conversely, demand `![1, 0, 0]` has nonzero sum `1 ≠ 0` in `ZMod 7`, so no flow realizes it. -/
example : ¬∃ w : Fin 3 → ZMod 7,
    ∀ v : Fin 3, triangleGraph.netFlow univ w v = (![1, 0, 0] : Fin 3 → ZMod 7) v := by
  rintro ⟨w, hw⟩
  have hiff := triangleGraph.exists_netFlow_eq_iff (K := univ) (F := univ)
    (fun _ _ => ⟨trivial, trivial⟩) triangleGraph_connected w ![1, 0, 0]
  have hsum := hiff.mp ⟨w, eqOn_refl _ _, fun v _ => hw v⟩
  have hfin : (toFinite (univ : Set (Fin 3))).toFinset = Finset.univ := by ext; simp
  rw [hfin] at hsum
  exact absurd hsum (by decide)

/-! ### 2. Acyclic forest uniqueness on `0 → 1 → 2` over any `AddCommGroup A` -/

/-- Oriented `2`-edge path `0 → 1 → 2` on `Fin 3`. -/
private def pathGraph : Multigraph (Fin 3) (Fin 2) where
  src i := ⟨i.val, by omega⟩
  tgt i := ⟨i.val + 1, by omega⟩

private theorem pathGraph_isForest :
    pathGraph.IsForest univ univ (fun _ _ => ⟨trivial, trivial⟩) where
  loopless e := by
    obtain ⟨⟨i, hi⟩, _⟩ := e
    intro h
    have := congrArg (fun x : {v : Fin 3 // v ∈ (univ : Set (Fin 3))} => x.val.val) h
    dsimp [Multigraph.subgraph, pathGraph] at this
    omega
  ends_injOn e₁ _ e₂ _ h := by
    fin_cases e₁ <;> fin_cases e₂ <;> simp_all [Multigraph.ends, pathGraph]
  isAcyclic := by
    let H := pathGraph.subgraph univ univ (fun _ _ => ⟨trivial, trivial⟩)
    intro u c hc
    have hlen := hc.three_le_length
    have hnodup := hc.edges_nodup
    have hsub : ∀ s ∈ c.edges, s ∈ H.toSimpleGraph.edgeSet := fun _ hs => c.edges_subset_edgeSet hs
    have hcard : c.edges.toFinset.card ≤ (toFinite H.toSimpleGraph.edgeSet).toFinset.card := by
      refine Finset.card_le_card fun s hs => ?_
      exact (toFinite _).mem_toFinset.mpr (hsub s (List.mem_toFinset.mp hs))
    rw [List.toFinset_card_of_nodup hnodup, SimpleGraph.Walk.length_edges] at hcard
    have hedge_le : (toFinite H.toSimpleGraph.edgeSet).toFinset.card ≤ 2 := by
      have : H.toSimpleGraph.edgeSet.ncard ≤ Nat.card {e : Fin 2 // e ∈ (univ : Set (Fin 2))} := by
        rw [Multigraph.toSimpleGraph_eq, Cslib.Multigraph.edgeSet_toSimpleGraph]
        exact (ncard_le_ncard sdiff_subset (finite_range _)).trans
          ((Nat.card_coe_set_eq _).symm.trans_le (Finite.card_range_le _))
      rw [← ncard_coe_finset, (toFinite _).coe_toFinset]
      exact this.trans_eq (by simp)
    omega

example {A : Type*} [AddCommGroup A] (w₁ w₂ : Fin 2 → A)
    (hflow : ∀ v : Fin 3, pathGraph.netFlow univ w₁ v = pathGraph.netFlow univ w₂ v) :
    w₁ = w₂ :=
  pathGraph.eq_of_netFlow_eq_of_isForest pathGraph_isForest (by simp) (fun v _ => hflow v)

/-! ### 3. Simultaneous zero-overlap `COPY` + Kirchhoff `XOR` (`ZMod 2`) `6 → 2` compression -/

/-- `8`-vertex, `6`-edge network over `ZMod 2`:
- Edges `0, 1, 2` form a `3`-wire `COPY` star rooted at vertex `0` (`0 → 1`, `0 → 2`, `0 → 3`).
- Edges `3, 4, 5` form a vertex-disjoint `3`-wire `XOR`/`+` star rooted at vertex `4` (`4 → 5`,
  `4 → 6`, `4 → 7`).
Across `P = {0, 4}`, all `6` edges cross `δ(P)` (`|δ(P)| = 6`), while simultaneous `COPY` +
Kirchhoff deduplication compresses the cut to `6 - 2 - 2 = 2` bits (`≤ 4` states). -/
private def dualGraph : Multigraph (Fin 8) (Fin 6) where
  src e := if e.val < 3 then 0 else 4
  tgt e := if e.val < 3 then ⟨e.val + 1, by omega⟩ else ⟨e.val + 2, by omega⟩

private def copySet : Set (Fin 6) := {e | e.val < 3}
private def addVertSet : Set (Fin 8) := {v | 4 ≤ v.val}
private def addEdgeSet : Set (Fin 6) := {e | 3 ≤ e.val}

private noncomputable def dualNetwork : Network (ZMod 2) (Fin 8) (Fin 8) (Fin 6) where
  toMultigraph := dualGraph
  site i := some i
  Constraint v x α :=
    if v.val < 4 then
      (v = 0 → α 0 = x 0 ∧ α 1 = x 0 ∧ α 2 = x 0) ∧
      (v = 1 → α 0 = x 1) ∧ (v = 2 → α 1 = x 2) ∧ (v = 3 → α 2 = x 3)
    else
      dualGraph.netFlow addEdgeSet α v = x v
  constraint_congr v x x' α α' hx hα hcon := by
    have hxv : x v = x' v := hx v rfl
    split_ifs at hcon ⊢ with hv
    · fin_cases v
      · have h0 : α 0 = α' 0 := hα 0 (Or.inl rfl)
        have h1 : α 1 = α' 1 := hα 1 (Or.inl rfl)
        have h2 : α 2 = α' 2 := hα 2 (Or.inl rfl)
        simp_all
      · have h0 : α 0 = α' 0 := hα 0 (Or.inr rfl)
        simp_all
      · have h1 : α 1 = α' 1 := hα 1 (Or.inr rfl)
        simp_all
      · have h2 : α 2 = α' 2 := hα 2 (Or.inr rfl)
        simp_all
      all_goals (dsimp at hv; omega)
    · rw [← hxv, ← hcon]
      exact dualGraph.netFlow_congr fun e _ heinc => (hα e heinc).symm

private theorem addEdgeSet_endpoints :
    ∀ ⦃e : Fin 6⦄, e ∈ addEdgeSet →
      dualNetwork.src e ∈ addVertSet ∧ dualNetwork.tgt e ∈ addVertSet := by
  intro e he
  have he3 : ¬e.val < 3 := by simp only [addEdgeSet, mem_ofPred_eq] at he; omega
  simp only [dualNetwork, dualGraph, addVertSet, he3, ↓reduceIte, mem_ofPred_eq]
  omega

private theorem addSubgraph_connected :
    (dualNetwork.subgraph addVertSet addEdgeSet addEdgeSet_endpoints).toSimpleGraph.Connected := by
  let r : {v : Fin 8 // v ∈ addVertSet} := ⟨4, by simp [addVertSet]⟩
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨r, fun u => ?_⟩
  obtain ⟨uval, hu⟩ := u
  have hu4 : 4 ≤ uval.val := hu
  fin_cases uval
  any_goals (dsimp at hu4; omega)
  · exact SimpleGraph.Reachable.refl r
  · exact (Multigraph.toSimpleGraph_adj.mpr
      ⟨(fun h => by cases h), (⟨3, by simp [addEdgeSet]⟩ : {e : Fin 6 // e ∈ addEdgeSet}),
        rfl⟩).reachable
  · exact (Multigraph.toSimpleGraph_adj.mpr
      ⟨(fun h => by cases h), (⟨4, by simp [addEdgeSet]⟩ : {e : Fin 6 // e ∈ addEdgeSet}),
        rfl⟩).reachable
  · exact (Multigraph.toSimpleGraph_adj.mpr
      ⟨(fun h => by cases h), (⟨5, by simp [addEdgeSet]⟩ : {e : Fin 6 // e ∈ addEdgeSet}),
        rfl⟩).reachable

private theorem addSubgraph_isForest :
    dualNetwork.IsForest addVertSet addEdgeSet addEdgeSet_endpoints where
  loopless e := by
    obtain ⟨e, he⟩ := e
    fin_cases e <;> simp_all [addEdgeSet, Multigraph.subgraph, dualNetwork, dualGraph]
  ends_injOn e₁ h₁ e₂ h₂ h := by
    fin_cases e₁ <;> fin_cases e₂ <;>
      simp_all [addEdgeSet, Multigraph.ends, dualNetwork, dualGraph]
  isAcyclic := by
    let H := dualNetwork.subgraph addVertSet addEdgeSet addEdgeSet_endpoints
    let r : {v : Fin 8 // v ∈ addVertSet} := ⟨4, by simp [addVertSet]⟩
    have hstar :
        ∀ ⦃a b : {v : Fin 8 // v ∈ addVertSet}⦄, H.toSimpleGraph.Adj a b → a = r ∨ b = r := by
      intro a b hadj
      obtain ⟨_, ⟨e, he⟩, hends⟩ := Multigraph.toSimpleGraph_adj.mp hadj
      have he3 : 3 ≤ e.val := he
      have hsrc : H.src ⟨e, he⟩ = r := by
        fin_cases e <;> first | (dsimp at he3; omega) | rfl
      rcases Sym2.eq_iff.mp hends with ⟨ha, _⟩ | ⟨ha, _⟩
      · exact Or.inl (ha.symm.trans hsrc)
      · exact Or.inr (ha.symm.trans hsrc)
    intro v c hc
    have hlen := hc.three_le_length
    rcases c with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, p⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · simp at hlen
    · have hnodup := hc.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.tail_cons, List.nodup_cons] at hnodup
      obtain ⟨hw₁, hw₂, _⟩ := hnodup
      simp only [List.mem_cons, not_or] at hw₁
      rcases hstar h₁ with rfl | rfl
      · rcases hstar h₂ with h | rfl
        · exact h₁.ne h.symm
        · exact hw₂ (SimpleGraph.Walk.end_mem_support p)
      · rcases hstar h₃ with h | rfl
        · exact h₂.ne h.symm
        · exact hw₁.2 (SimpleGraph.Walk.start_mem_support p)

private noncomputable def dualDecomp : KirchhoffDecomposition dualNetwork Unit Unit where
  copyEdges _ := copySet
  copyEdges_pairwiseDisjoint _ _ h := (h rfl).elim
  copy_const x α hsat _ e₁ h₁ e₂ h₂ := by
    have h0 := (hsat 0).1 rfl
    have he₁ : α e₁ = x 0 := by
      fin_cases e₁ <;> simp_all [copySet]
    have he₂ : α e₂ = x 0 := by
      fin_cases e₂ <;> simp_all [copySet]
    exact he₁.trans he₂.symm
  addVerts _ := addVertSet
  addVerts_pairwiseDisjoint _ _ h := (h rfl).elim
  addEdges _ := addEdgeSet
  addEdges_endpoints _ := addEdgeSet_endpoints
  disjoint_copy_add _ _ := by
    rw [disjoint_left]
    intro e h₁ h₂
    simp only [copySet, addEdgeSet, mem_ofPred_eq] at h₁ h₂
    omega
  add_connected _ := addSubgraph_connected
  demand v x _ := x v
  demand_congr _ v _ _ _ _ _ hx _ := hx v rfl
  constraint_add_iff _ v hv x α := by
    have hv4 : ¬v.val < 4 := by simp only [addVertSet, mem_ofPred_eq] at hv; omega
    simp [dualNetwork, hv4]

/-- Across `P = {0, 4}`, all `6` edges cross `δ(P)`, while `dualDecomp.compressedWidth P = 2`,
bounding the compressed state space by `2^2 = 4` (`log₂ ≤ 2`) with an exact, unambiguous
`ReadOnceNBP`. -/
example :
    let P : Set (Fin 8) := {0, 4}
    (dualNetwork.edgeCut P).ncard = 6 ∧
    dualDecomp.compressedWidth P = 2 ∧
    (dualDecomp.state P '' (univ : Set (Fin 6 → ZMod 2))).ncard ≤ 4 ∧
    Real.logb 2 ((dualDecomp.state P '' (univ : Set (Fin 6 → ZMod 2))).ncard : ℝ) ≤ 2 ∧
    ∀ π : Layout (Fin 8),
      (dualDecomp.branchingProgram π).accepted = dualNetwork.accepted ∧
      (dualDecomp.branchingProgram π).Unambiguous := by
  intro P
  have hcut_univ : dualNetwork.edgeCut P = univ := by
    ext e
    fin_cases e <;> simp [P, dualNetwork, dualGraph, Multigraph.mem_edgeCut]
  have hcut6 : (dualNetwork.edgeCut P).ncard = 6 := by
    rw [hcut_univ, ncard_univ, Nat.card_fin]
  have hcopy3 : (copySet ∩ dualNetwork.edgeCut P).ncard = 3 := by
    rw [hcut_univ, inter_univ]
    have : copySet = ({0, 1, 2} : Finset (Fin 6)) := by ext e; fin_cases e <;> simp [copySet]
    rw [this, ncard_coe_finset]
    decide
  have hadd3 : (addEdgeSet ∩ dualNetwork.edgeCut P).ncard = 3 := by
    rw [hcut_univ, inter_univ]
    have : addEdgeSet = ({3, 4, 5} : Finset (Fin 6)) := by ext e; fin_cases e <;> simp [addEdgeSet]
    rw [this, ncard_coe_finset]
    decide
  have hcomp2 : dualDecomp.compressedWidth P = 2 := by
    have hu : (toFinite (univ : Set Unit)).toFinset = {()} := by ext u; cases u; simp
    simp only [KirchhoffDecomposition.compressedWidth, dualDecomp, hu, Finset.sum_singleton,
      hcut6, hcopy3, hadd3]
  have hcardA : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hstate4 : (dualDecomp.state P '' (univ : Set (Fin 6 → ZMod 2))).ncard ≤ 4 := by
    simpa [hcardA, hcomp2] using dualDecomp.ncard_state_le P univ
  have hlog2 :
      Real.logb 2 ((dualDecomp.state P '' (univ : Set (Fin 6 → ZMod 2))).ncard : ℝ) ≤ 2 := by
    have h := dualDecomp.logb_ncard_state_le (by rw [hcardA]; omega) P univ
    have hu : (toFinite (univ : Set Unit)).toFinset = {()} := by ext u; cases u; simp
    have hcE : dualDecomp.copyEdges () = copySet := rfl
    have haE : dualDecomp.addEdges () = addEdgeSet := rfl
    rw [hcardA, Nat.cast_ofNat, hu, Finset.sum_singleton, Finset.sum_singleton, hcE, haE, hcut6,
      hcopy3, hadd3] at h
    norm_num at h
    rw [image_univ]
    exact h
  refine ⟨hcut6, hcomp2, hstate4, hlog2, fun π => ⟨dualDecomp.accepted_branchingProgram π, ?_⟩⟩
  refine dualDecomp.unambiguous_branchingProgram π (fun _ => addSubgraph_isForest) ?_
  intro x α₁ α₂ h₁ h₂ e henot
  have hlt3 : e.val < 3 := by
    by_contra hge
    exact henot (mem_iUnion.mpr ⟨(), by simp only [dualDecomp, addEdgeSet, mem_ofPred_eq]; omega⟩)
  have c₁ := (h₁ 0).1 rfl
  have c₂ := (h₂ 0).1 rfl
  fin_cases e <;> simp_all

end CslibFrontierTests.FrontierKirchhoff
