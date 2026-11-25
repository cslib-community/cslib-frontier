/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Powerset

/-!
# Cut Property (Blue Rule) and Minimum Spanning Tree Uniqueness on `SimpleGraph`

This module formalizes minimum-weight spanning trees (`SimpleGraph.IsMST`), outgoing cut edges
(`SimpleGraph.IsOutgoingEdge`, `SimpleGraph.outgoingEdges`), minimum-weight outgoing edges
(`SimpleGraph.IsMOE`), the cycle-exchange cut property, and distinct-weight MST uniqueness on
Mathlib's `SimpleGraph V`, following Section 2 (Properties 1 and 2, p. 68) of
[GallagerHumbletSpira1983] and bridging both sequential Kruskal
(`CslibFrontier.Algorithms.Lean.Kruskal.SimpleGraph`) and the distributed GHS protocol
(`CslibFrontier.Computability.Distributed.MinimumSpanningTree.GHS`).

## Main definitions

* `SimpleGraph.IsSpanningTree`: spanning tree `T ≤ G ∧ T.IsTree` of a simple graph `G`.
* `SimpleGraph.edgeWeightSum`: total edge weight `∑ᶠ e ∈ H.edgeSet, w e` of a simple graph `H`.
* `SimpleGraph.IsMST`: minimum-weight spanning tree of `(G, w)`.
* `SimpleGraph.IsOutgoingEdge`: undirected edge of `G` with one endpoint in `S : Finset V` and one
  outside `S`.
* `SimpleGraph.crossesCut`, `SimpleGraph.outgoingEdges`: computable Boolean cut test and outgoing
  edge `Finset` for finite decidable graphs.
* `SimpleGraph.IsMOE`: minimum-weight outgoing edge of a vertex subset `S : Finset V` in `(G, w)`.

## Main results

* `SimpleGraph.IsSpanningTree.swap_edge`: adding a non-tree edge `s(u, v)` (`u ∈ S`, `v ∉ S`) to a
  spanning tree `T` and deleting a boundary edge `e'` on the `u`–`v` tree path yields another
  spanning tree preserving any subgraph internal to `S`.
* `SimpleGraph.IsMST.exists_sup_edge_of_isMOE`: **GHS Property 1** ([GallagerHumbletSpira1983], §2,
  p. 68) — extending a fragment `H ≤ T` of an MST `T` by any minimum-weight outgoing edge of its
  vertex set yields a subgraph of an MST `T'`.
* `SimpleGraph.IsMOE.mem_edgeSet_of_isMST_of_injOn`: **Distinct-weight cut / blue-rule theorem** —
  when `w` is injective on `G.edgeSet`, every minimum-weight outgoing edge across any cut belongs to
  every MST of `G`.
* `SimpleGraph.exists_isMOE`, `SimpleGraph.existsUnique_isMOE_of_injOn`: existence (and uniqueness
  under injective edge weights) of the minimum-weight outgoing edge of any nonempty proper vertex
  subset `S` in a finite connected graph.
* `SimpleGraph.exists_isMST`: every finite connected graph admits a minimum-weight spanning tree.
* `SimpleGraph.IsMST.eq_of_injOn`, `SimpleGraph.existsUnique_isMST_of_injOn`: **GHS Property 2**
  ([GallagerHumbletSpira1983], §2, p. 68) — when `w` is injective on `G.edgeSet`, the minimum
  spanning tree of a finite connected graph is unique.
* `SimpleGraph.le_of_forall_isMOE_of_isMST_of_injOn`,
  `SimpleGraph.isAcyclic_of_forall_isMOE_of_injOn`,
  `SimpleGraph.isMST_of_forall_isMOE_of_connected_of_injOn`: any subgraph whose edges are all
  cut-MOEs is contained in the unique MST, hence acyclic, and equals the unique MST once connected.

## References

* [R. G. Gallager, P. A. Humblet, and P. M. Spira, *A Distributed Algorithm for Minimum-Weight
  Spanning Trees*][GallagerHumbletSpira1983], Section 2 (Properties 1–2, p. 68).
-/

public section

namespace SimpleGraph

/-! ### Spanning trees, edge-weight sums, and minimum spanning trees -/

/-- `T` is a spanning tree of `G` when `T` is a spanning subgraph (`T ≤ G`) that is a tree
(`T.IsTree`). -/
@[expose] def IsSpanningTree {V : Type*} (G T : SimpleGraph V) : Prop :=
  T ≤ G ∧ T.IsTree

/-- Total weight `∑ᶠ e ∈ H.edgeSet, w e` of the undirected edges of `H : SimpleGraph V`.
Using `finsum` avoids carrying `[DecidableRel H.Adj]` or `[Fintype H.edgeSet]` in quantified
optimality statements while simplifying to `∑ e ∈ H.edgeFinset, w e` whenever `[Fintype H.edgeSet]`
is available. -/
noncomputable def edgeWeightSum {V W : Type*} [AddCommMonoid W]
    (H : SimpleGraph V) (w : Sym2 V → W) : W :=
  ∑ᶠ e ∈ H.edgeSet, w e

@[simp]
theorem edgeWeightSum_eq_sum_edgeFinset {V W : Type*} [AddCommMonoid W]
    (H : SimpleGraph V) [Fintype H.edgeSet] (w : Sym2 V → W) :
    edgeWeightSum H w = ∑ e ∈ H.edgeFinset, w e := by
  unfold edgeWeightSum
  rw [← H.coe_edgeFinset, finsum_mem_coe_finset]

/-- `T` is a minimum-weight spanning tree (MST) of `G` with respect to edge weights `w` if `T` is a
spanning tree of `G` whose total edge weight is less than or equal to that of every spanning tree
of `G`. -/
@[expose] def IsMST {V W : Type*} [AddCommMonoid W] [LE W]
    (G : SimpleGraph V) (w : Sym2 V → W) (T : SimpleGraph V) : Prop :=
  IsSpanningTree G T ∧ ∀ T', IsSpanningTree G T' → edgeWeightSum T w ≤ edgeWeightSum T' w

/-! ### Outgoing cut edges and minimum-weight outgoing edges (MOEs) -/

/-- `e` is an outgoing edge of `S : Finset V` in `G` ([GallagerHumbletSpira1983], §2, p. 68) when
`e ∈ G.edgeSet` has one endpoint in `S` and the other outside `S`. -/
@[expose] def IsOutgoingEdge {V : Type*} (G : SimpleGraph V) (S : Finset V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ ∃ u ∈ S, ∃ v ∉ S, e = s(u, v)

theorem IsOutgoingEdge.mem_edgeSet {V : Type*} {G : SimpleGraph V} {S : Finset V} {e : Sym2 V}
    (h : IsOutgoingEdge G S e) : e ∈ G.edgeSet :=
  h.1

theorem IsOutgoingEdge.mono {V : Type*} {H G : SimpleGraph V} (hle : H ≤ G) {S : Finset V}
    {e : Sym2 V} (h : IsOutgoingEdge H S e) : IsOutgoingEdge G S e :=
  ⟨edgeSet_mono hle h.1, h.2⟩

theorem isOutgoingEdge_mk {V : Type*} {G : SimpleGraph V} {S : Finset V} {u v : V} :
    IsOutgoingEdge G S s(u, v) ↔ G.Adj u v ∧ ((u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S)) := by
  constructor
  · rintro ⟨hadj, a, ha, b, hb, heq⟩
    rw [G.mem_edgeSet] at hadj
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hadj, .inl ⟨ha, hb⟩⟩
    · exact ⟨hadj, .inr ⟨hb, ha⟩⟩
  · rintro ⟨hadj, ⟨hu, hv⟩ | ⟨hu, hv⟩⟩
    · exact ⟨G.mem_edgeSet.mpr hadj, u, hu, v, hv, rfl⟩
    · exact ⟨G.mem_edgeSet.mpr hadj, v, hv, u, hu, Sym2.eq_swap⟩

/-- Symmetry-preserving computable Boolean check testing whether `e : Sym2 V` has one endpoint in
`S` and one outside `S`. -/
@[expose] def crossesCut {V : Type*} [DecidableEq V] (S : Finset V) (e : Sym2 V) : Bool :=
  Sym2.lift
    ⟨fun u v => decide (u ∈ S) != decide (v ∈ S),
      fun u v => by dsimp only; cases decide (u ∈ S) <;> cases decide (v ∈ S) <;> rfl⟩
    e

@[simp]
private theorem crossesCut_mk {V : Type*} [DecidableEq V] (S : Finset V) (u v : V) :
    crossesCut S s(u, v) = (decide (u ∈ S) != decide (v ∈ S)) :=
  rfl

private theorem crossesCut_eq_true_iff {V : Type*} [DecidableEq V] (S : Finset V) (e : Sym2 V) :
    crossesCut S e = true ↔ ∃ u ∈ S, ∃ v ∉ S, e = s(u, v) := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [crossesCut_mk, bne_iff_ne, ne_eq, decide_eq_decide]
    constructor
    · intro hiff
      by_cases hx : x ∈ S
      · exact ⟨x, hx, y, fun hy => hiff ⟨fun _ => hy, fun _ => hx⟩, rfl⟩
      · have hy : y ∈ S := by
          by_contra hy
          exact hiff ⟨fun h => absurd h hx, fun h => absurd h hy⟩
        exact ⟨y, hy, x, hx, Sym2.eq_swap⟩
    · rintro ⟨u, hu, v, hv, heq⟩
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact fun h => hv (h.mp hu)
      · exact fun h => hv (h.mpr hu)

/-- Computable `Finset` of outgoing edges of `S` in `G`. -/
@[expose] def outgoingEdges {V : Type*} [DecidableEq V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => crossesCut S e)

@[simp]
theorem mem_outgoingEdges {V : Type*} [DecidableEq V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (S : Finset V) (e : Sym2 V) :
    e ∈ outgoingEdges G S ↔ IsOutgoingEdge G S e := by
  rw [outgoingEdges, Finset.mem_filter, mem_edgeFinset, crossesCut_eq_true_iff, IsOutgoingEdge]

/-- `e` is a minimum-weight outgoing edge (`MOE`) of `S` in `(G, w)` if `e` is an outgoing edge of
`S` and its weight is at most that of every outgoing edge of `S`. -/
@[expose] def IsMOE {V W : Type*} [LE W] (G : SimpleGraph V) (w : Sym2 V → W) (S : Finset V)
    (e : Sym2 V) : Prop :=
  IsOutgoingEdge G S e ∧ ∀ e', IsOutgoingEdge G S e' → w e ≤ w e'

/-- Computable check for `IsMOE` on a finite decidable graph. -/
instance instDecidableIsMOE {V W : Type*} [DecidableEq V] (G : SimpleGraph V) [Fintype G.edgeSet]
    [LE W] [DecidableLE W] (w : Sym2 V → W) (S : Finset V) (e : Sym2 V) :
    Decidable (IsMOE G w S e) :=
  decidable_of_iff
    (e ∈ outgoingEdges G S ∧ ∀ e' ∈ outgoingEdges G S, w e ≤ w e')
    (by simp [IsMOE])

theorem IsMOE.unique_of_injOn {V W : Type*} [LinearOrder W] {G : SimpleGraph V}
    {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet) {S : Finset V} {e₁ e₂ : Sym2 V}
    (h₁ : IsMOE G w S e₁) (h₂ : IsMOE G w S e₂) : e₁ = e₂ :=
  hinj h₁.1.1 h₂.1.1 (le_antisymm (h₁.2 e₂ h₂.1) (h₂.2 e₁ h₁.1))

/-- Every nonempty proper subset `S` of a finite connected graph has at least one outgoing edge. -/
theorem exists_isOutgoingEdge {V : Type*} [Fintype V] {G : SimpleGraph V} (hconn : G.Connected)
    {S : Finset V} (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ∃ e, IsOutgoingEdge G S e := by
  classical
  obtain ⟨u, hu⟩ := hne
  obtain ⟨v, -, hv⟩ : ∃ v ∈ (Finset.univ : Finset V), v ∉ S :=
    Finset.not_subset.mp fun hsub => hproper (Finset.eq_univ_of_forall fun x => hsub (by simp))
  obtain ⟨p⟩ := hconn u v
  obtain ⟨d, -, hdfst, hdsnd⟩ :=
    p.exists_boundary_dart (S : Set V) (Finset.mem_coe.mpr hu) (Finset.mem_coe.not.mpr hv)
  exact ⟨d.edge, G.mem_edgeSet.mpr d.adj, d.fst, Finset.mem_coe.mp hdfst, d.snd,
    Finset.mem_coe.not.mp hdsnd, rfl⟩

/-- Every nonempty proper subset `S` of a finite connected graph has a minimum-weight outgoing
edge. -/
theorem exists_isMOE {V W : Type*} [Fintype V] [LinearOrder W] {G : SimpleGraph V}
    (hconn : G.Connected) (w : Sym2 V → W) {S : Finset V} (hne : S.Nonempty)
    (hproper : S ≠ Finset.univ) :
    ∃ e, IsMOE G w S e := by
  classical
  obtain ⟨e₀, he₀⟩ := exists_isOutgoingEdge hconn hne hproper
  have hfin : (outgoingEdges G S).Nonempty := ⟨e₀, (mem_outgoingEdges G S e₀).mpr he₀⟩
  obtain ⟨e, he, hmin⟩ := Finset.exists_min_image (outgoingEdges G S) w hfin
  exact ⟨e, (mem_outgoingEdges G S e).mp he,
    fun e' he' => hmin e' ((mem_outgoingEdges G S e').mpr he')⟩

/-- Under injective edge weights on `G.edgeSet`, every nonempty proper subset `S` of a finite
connected graph has a unique minimum-weight outgoing edge. -/
theorem existsUnique_isMOE_of_injOn {V W : Type*} [Fintype V] [LinearOrder W] {G : SimpleGraph V}
    (hconn : G.Connected) {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet)
    {S : Finset V} (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ∃! e, IsMOE G w S e := by
  obtain ⟨e, he⟩ := exists_isMOE hconn w hne hproper
  exact ⟨e, he, fun e' he' => he'.unique_of_injOn hinj he⟩

/-! ### Fundamental cycle-exchange lemma on spanning trees -/

/-- Adding an edge `s(u, v) ∉ T.edgeSet` (`u ≠ v`) to a finite tree `T` and deleting an edge
`e' ∈ p.edges` along the unique `u`–`v` path `p` in `T` yields another tree on `V`, with edge-weight
sum satisfying `edgeWeightSum T' w + w e' = edgeWeightSum T w + w s(u, v)`. -/
private theorem isTree_sup_edge_deleteEdges_of_mem_path {V W : Type*} [Finite V]
    [AddCommMonoid W] {T : SimpleGraph V} (hT : T.IsTree) {u v : V} (huv : u ≠ v)
    (hnotMem : s(u, v) ∉ T.edgeSet) {p : T.Walk u v} (hp : p.IsPath)
    {e' : Sym2 V} (he' : e' ∈ p.edges) (w : Sym2 V → W) :
    let T' := (T ⊔ SimpleGraph.edge u v).deleteEdges {e'}
    T'.IsTree ∧ e' ∈ T.edgeSet ∧ e' ≠ s(u, v) ∧
      edgeWeightSum T' w + w e' = edgeWeightSum T w + w s(u, v) := by
  have := Fintype.ofFinite V
  classical
  intro T'
  have he'T : e' ∈ T.edgeSet := p.edges_subset_edgeSet he'
  have hne_e : e' ≠ s(u, v) := fun h => hnotMem (h ▸ he'T)
  have hadj_vu : (T ⊔ SimpleGraph.edge u v).Adj v u :=
    (sup_adj T (SimpleGraph.edge u v) v u).mpr
      (.inr ((edge_adj u v v u).mpr ⟨.inr ⟨rfl, rfl⟩, huv.symm⟩))
  let p_sup : (T ⊔ SimpleGraph.edge u v).Walk u v := p.mapLe le_sup_left
  have hp_sup : p_sup.IsPath := hp.mapLe le_sup_left
  have hnot_p : s(v, u) ∉ p_sup.edges := by
    rw [Walk.edges_map, Hom.coe_ofLE, Sym2.map_id, List.map_id_fun, id_eq, Sym2.eq_swap]
    exact fun hm => hnotMem (p.edges_subset_edgeSet hm)
  have hcyc : (Walk.cons hadj_vu p_sup).IsCycle := Path.cons_isCycle ⟨p_sup, hp_sup⟩ hadj_vu hnot_p
  have he'_cyc : e' ∈ (Walk.cons hadj_vu p_sup).edges := by
    rw [Walk.edges_cons]; exact List.mem_cons_of_mem _ (by simpa [p_sup] using he')
  have hnot_bridge : ¬ (T ⊔ SimpleGraph.edge u v).IsBridge e' := fun hb =>
    hb.notMem_edges_of_isCycle hcyc he'_cyc
  have hconn_sup : (T ⊔ SimpleGraph.edge u v).Connected := hT.connected.mono le_sup_left
  have hconn' : T'.Connected :=
    hconn_sup.preconnected.connected_deleteEdges_of_not_isBridge hnot_bridge
  have hedge_fin : T'.edgeFinset = (insert s(u, v) T.edgeFinset).erase e' := by
    ext z
    have : z = s(u, v) → z ∉ Sym2.diagSet := by rintro rfl; simpa using huv
    simp only [T', mem_edgeFinset, edgeSet_deleteEdges, edgeSet_sup, edgeSet_edge, Set.mem_sdiff,
      Set.mem_union, Set.mem_singleton_iff, Finset.mem_erase, Finset.mem_insert]
    tauto
  have he'_ins : e' ∈ insert s(u, v) T.edgeFinset :=
    Finset.mem_insert_of_mem (mem_edgeFinset.mpr he'T)
  have hnot_fin : s(u, v) ∉ T.edgeFinset := mem_edgeFinset.not.mpr hnotMem
  have hcard' : T'.edgeFinset.card + 1 = Fintype.card V := by
    rw [hedge_fin, Finset.card_erase_of_mem he'_ins, Finset.card_insert_of_notMem hnot_fin,
      Nat.add_sub_cancel, hT.card_edgeFinset]
  have htree' : T'.IsTree := by
    rw [isTree_iff_connected_and_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      ← edgeFinset_card]
    exact ⟨hconn', hcard'⟩
  have hsum : edgeWeightSum T' w + w e' = edgeWeightSum T w + w s(u, v) := by
    rw [edgeWeightSum_eq_sum_edgeFinset, edgeWeightSum_eq_sum_edgeFinset, hedge_fin,
      Finset.sum_erase_add _ _ he'_ins, Finset.sum_insert hnot_fin, add_comm (w s(u, v))]
  exact ⟨htree', he'T, hne_e, hsum⟩

/-- **Cycle-exchange lemma across a cut**: if `T` is a spanning tree of `G` on `[Finite V]` and
`G.Adj u v` crosses `(S, Sᶜ)` (`u ∈ S`, `v ∉ S`) with `s(u, v) ∉ T.edgeSet`, there is an edge
`e' ∈ T.edgeSet` crossing `(S, Sᶜ)` in `T` such that `(T ⊔ edge u v).deleteEdges {e'}` is a
spanning tree of `G` with the exact swapped weight sum. -/
theorem IsSpanningTree.swap_edge {V W : Type*} [Finite V] [AddCommMonoid W]
    {G T : SimpleGraph V} (hT : IsSpanningTree G T) {S : Finset V} {u v : V}
    (hu : u ∈ S) (hv : v ∉ S) (hadj : G.Adj u v) (hnotMem : s(u, v) ∉ T.edgeSet)
    (w : Sym2 V → W) :
    ∃ e', IsOutgoingEdge T S e' ∧ e' ≠ s(u, v) ∧
      IsSpanningTree G ((T ⊔ SimpleGraph.edge u v).deleteEdges {e'}) ∧
      edgeWeightSum ((T ⊔ SimpleGraph.edge u v).deleteEdges {e'}) w + w e' =
        edgeWeightSum T w + w s(u, v) := by
  classical
  obtain ⟨hTG, hTree⟩ := hT
  obtain ⟨p, hp⟩ := hTree.connected.exists_isPath u v
  obtain ⟨d, hd, hdfst, hdsnd⟩ :=
    p.exists_boundary_dart (S : Set V) (Finset.mem_coe.mpr hu) (Finset.mem_coe.not.mpr hv)
  have hd_edges : d.edge ∈ p.edges := List.mem_map_of_mem hd
  obtain ⟨htree', he'T, hne_e, hsum⟩ :=
    isTree_sup_edge_deleteEdges_of_mem_path hTree hadj.ne hnotMem hp hd_edges w
  have hout : IsOutgoingEdge T S d.edge :=
    ⟨he'T, d.fst, Finset.mem_coe.mp hdfst, d.snd, Finset.mem_coe.not.mp hdsnd, rfl⟩
  have hle' : (T ⊔ SimpleGraph.edge u v).deleteEdges {d.edge} ≤ G :=
    (deleteEdges_le _).trans (sup_le hTG ((edge_le_iff _).2 (.inr hadj)))
  exact ⟨d.edge, hout, hne_e, ⟨hle', htree'⟩, hsum⟩

/-! ### Cut optimality (GHS Property 1) and distinct-weight blue rule -/

/-- **GHS Property 1** ([GallagerHumbletSpira1983], §2, p. 68): given a minimum-weight spanning
tree `T` of `G`, any subgraph `H ≤ T` whose edges lie inside `S : Finset V` (in particular, a
connected fragment of `T` on vertex set `S`), and any minimum-weight outgoing edge `s(u, v)` of `S`,
there exists a minimum-weight spanning tree `T'` of `G` containing both `H` and `s(u, v)`. -/
theorem IsMST.exists_sup_edge_of_isMOE {V W : Type*} [Finite V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G T H : SimpleGraph V} {w : Sym2 V → W} (hMST : IsMST G w T)
    {S : Finset V} (hHT : H ≤ T) (hHS : ∀ ⦃x y : V⦄, H.Adj x y → x ∈ S ∧ y ∈ S)
    {u v : V} (hmoe : IsMOE G w S s(u, v)) :
    ∃ T', IsMST G w T' ∧ H ⊔ SimpleGraph.edge u v ≤ T' := by
  by_cases hmem : s(u, v) ∈ T.edgeSet
  · exact ⟨T, hMST, sup_le hHT ((edge_le_iff _).2 (.inr (T.mem_edgeSet.mp hmem)))⟩
  · obtain ⟨hadj, hcut⟩ := isOutgoingEdge_mk.mp hmoe.1
    have swap_case : ∀ a b : V, a ∈ S → b ∉ S → G.Adj a b → s(a, b) = s(u, v) →
        ∃ T', IsMST G w T' ∧ H ⊔ SimpleGraph.edge u v ≤ T' := by
      intro a b ha hb hadj_ab heq_ab
      have hnot_ab : s(a, b) ∉ T.edgeSet := heq_ab ▸ hmem
      obtain ⟨e', houtT, hne_e, hST', hsum⟩ :=
        hMST.1.swap_edge ha hb hadj_ab hnot_ab w
      have hw_le : w s(a, b) ≤ w e' := by
        rw [heq_ab]
        exact hmoe.2 e' (houtT.mono hMST.1.1)
      let T' := (T ⊔ SimpleGraph.edge a b).deleteEdges {e'}
      have hT'_le_T : edgeWeightSum T' w ≤ edgeWeightSum T w :=
        le_of_add_le_add_right (hsum.trans_le (add_le_add_right hw_le _))
      have hMST' : IsMST G w T' :=
        ⟨hST', fun T'' hT'' => hT'_le_T.trans (hMST.2 T'' hT'')⟩
      have he'_not_H : e' ∉ H.edgeSet := by
        rintro he'H
        obtain ⟨_, x, hx, y, hy, rfl⟩ := houtT
        exact hy (hHS (H.mem_edgeSet.mp he'H)).2
      have hH_le : H ≤ T' := by
        intro x y hxy
        rw [deleteEdges_adj]
        exact ⟨(le_sup_left : T ≤ T ⊔ SimpleGraph.edge a b) (hHT hxy),
          fun heq => he'_not_H (heq ▸ H.mem_edgeSet.mpr hxy)⟩
      have hadj_T' : T'.Adj u v := by
        rw [← T'.mem_edgeSet, ← heq_ab, T'.mem_edgeSet, deleteEdges_adj]
        exact ⟨(sup_adj T (SimpleGraph.edge a b) a b).mpr
          (.inr ((edge_adj a b a b).mpr ⟨.inl ⟨rfl, rfl⟩, hadj_ab.ne⟩)), hne_e.symm⟩
      exact ⟨T', hMST', sup_le hH_le ((edge_le_iff _).2 (.inr hadj_T'))⟩
    rcases hcut with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact swap_case u v hu hv hadj rfl
    · exact swap_case v u hv hu hadj.symm Sym2.eq_swap

/-- **Distinct-weight cut / blue-rule theorem**: when `w` is injective on `G.edgeSet`, the
minimum-weight outgoing edge across any cut `S : Finset V` belongs to **every** minimum-weight
spanning tree of `G`. -/
theorem IsMOE.mem_edgeSet_of_isMST_of_injOn {V W : Type*} [Finite V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G T : SimpleGraph V} {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet)
    {S : Finset V} {e : Sym2 V} (hmoe : IsMOE G w S e) (hMST : IsMST G w T) :
    e ∈ T.edgeSet := by
  by_contra hnotMem
  obtain ⟨_, u, hu, v, hv, rfl⟩ := hmoe.1
  have hadj : G.Adj u v := G.mem_edgeSet.mp hmoe.1.1
  obtain ⟨e', houtT, hne_e, hST', hsum⟩ := hMST.1.swap_edge hu hv hadj hnotMem w
  have houtG : IsOutgoingEdge G S e' := houtT.mono hMST.1.1
  have hw_le : w s(u, v) ≤ w e' := hmoe.2 e' houtG
  have hw_ne : w s(u, v) ≠ w e' := fun heq => hne_e.symm (hinj hmoe.1.1 houtG.1 heq)
  exact not_le_of_gt (lt_of_add_lt_add_right (hsum.trans_lt (add_lt_add_right
    (lt_of_le_of_ne hw_le hw_ne) _))) (hMST.2 _ hST')

/-! ### Existence and distinct-weight uniqueness of the MST (GHS Property 2) -/

/-- Every finite connected graph admits a minimum-weight spanning tree. -/
theorem exists_isMST {V W : Type*} [Finite V] [AddCommMonoid W] [LinearOrder W]
    {G : SimpleGraph V} (hconn : G.Connected) (w : Sym2 V → W) :
    ∃ T, IsMST G w T := by
  have := Fintype.ofFinite V
  classical
  obtain ⟨T₀, hle₀, hT₀⟩ := hconn.exists_isTree_le
  let trees : Finset (SimpleGraph V) := Finset.univ.filter (IsSpanningTree G)
  have hne : trees.Nonempty := ⟨T₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle₀, hT₀⟩⟩
  obtain ⟨T, hTmem, hmin⟩ := Finset.exists_min_image trees (fun H => edgeWeightSum H w) hne
  exact ⟨T, (Finset.mem_filter.mp hTmem).2,
    fun T' hT' => hmin T' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩)⟩

/-- **GHS Property 2** ([GallagerHumbletSpira1983], §2, p. 68): when `w` is injective on
`G.edgeSet`, any two minimum-weight spanning trees of `G` are equal. -/
theorem IsMST.eq_of_injOn {V W : Type*} [Finite V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G T₁ T₂ : SimpleGraph V} {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet)
    (h₁ : IsMST G w T₁) (h₂ : IsMST G w T₂) : T₁ = T₂ := by
  have := Fintype.ofFinite V
  classical
  by_contra hne
  have hdiff_ne : (symmDiff T₁.edgeFinset T₂.edgeFinset).Nonempty :=
    Finset.symmDiff_nonempty.2 (mt edgeFinset_inj.1 hne)
  obtain ⟨e, he_mem, he_min⟩ := Finset.exists_min_image _ w hdiff_ne
  have symm_step : ∀ A B : SimpleGraph V, IsMST G w A → IsMST G w B →
      (∀ z ∈ symmDiff A.edgeFinset B.edgeFinset, w e ≤ w z) →
      e ∈ A.edgeSet → e ∉ B.edgeSet → False := by
    intro A B hA hB hmin_AB heA heB
    induction e using Sym2.ind with
    | _ u v =>
      have hadjA : A.Adj u v := A.mem_edgeSet.mp heA
      obtain ⟨p, hp⟩ := hB.1.2.connected.exists_isPath u v
      have hexists_notA : ∃ e' ∈ p.edges, e' ∉ A.edgeSet := by
        by_contra! hallA
        let pA : A.Walk u v := p.transfer A hallA
        have he_not_pA : s(u, v) ∉ pA.edges := by
          rw [Walk.edges_transfer]
          exact fun hm => heB (p.edges_subset_edgeSet hm)
        have hbridge : A.IsBridge s(u, v) := isAcyclic_iff_forall_isBridge.mp hA.1.2.isAcyclic heA
        exact he_not_pA (isBridge_iff_forall_walk_mem_edges.mp hbridge pA)
      obtain ⟨e', he'_edges, he'_notA⟩ := hexists_notA
      have he'B : e' ∈ B.edgeSet := p.edges_subset_edgeSet he'_edges
      obtain ⟨htreeB', _, hne_e', hsum⟩ :=
        isTree_sup_edge_deleteEdges_of_mem_path hB.1.2 hadjA.ne heB hp he'_edges w
      have hleB' : (B ⊔ SimpleGraph.edge u v).deleteEdges {e'} ≤ G :=
        (deleteEdges_le _).trans (sup_le hB.1.1 ((edge_le_iff _).2 (.inr (hA.1.1 hadjA))))
      have he'_diff : e' ∈ symmDiff A.edgeFinset B.edgeFinset := by
        rw [Finset.mem_symmDiff, mem_edgeFinset, mem_edgeFinset]
        exact .inr ⟨he'B, he'_notA⟩
      have hw_le : w s(u, v) ≤ w e' := hmin_AB e' he'_diff
      have hw_ne : w s(u, v) ≠ w e' := fun heq =>
        hne_e'.symm (hinj (edgeSet_mono hA.1.1 heA) (edgeSet_mono hB.1.1 he'B) heq)
      exact not_le_of_gt (lt_of_add_lt_add_right (hsum.trans_lt (add_lt_add_right
        (lt_of_le_of_ne hw_le hw_ne) _))) (hB.2 _ ⟨hleB', htreeB'⟩)
  rw [Finset.mem_symmDiff, mem_edgeFinset, mem_edgeFinset] at he_mem
  rcases he_mem with ⟨he₁, he₂⟩ | ⟨he₂, he₁⟩
  · exact symm_step T₁ T₂ h₁ h₂ he_min he₁ he₂
  · exact symm_step T₂ T₁ h₂ h₁ (by simpa only [symmDiff_comm] using he_min) he₂ he₁

/-- On a finite connected graph with edge weights injective on `G.edgeSet`, there exists a unique
minimum-weight spanning tree. -/
theorem existsUnique_isMST_of_injOn {V W : Type*} [Finite V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G : SimpleGraph V} (hconn : G.Connected) {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet) :
    ∃! T, IsMST G w T := by
  obtain ⟨T, hT⟩ := exists_isMST hconn w
  exact ⟨T, hT, fun T' hT' => hT'.eq_of_injOn hinj hT⟩

/-! ### Cut-MOE subgraphs and acyclicity -/

/-- Any subgraph `H` whose edges are all cut-MOEs of `(G, w)` is contained in every MST of `(G, w)`
when `w` is injective on `G.edgeSet`. -/
theorem le_of_forall_isMOE_of_isMST_of_injOn {V W : Type*} [Finite V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G H T : SimpleGraph V} {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet)
    (hMOE : ∀ e ∈ H.edgeSet, ∃ S : Finset V, IsMOE G w S e) (hMST : IsMST G w T) :
    H ≤ T := by
  rw [← edgeSet_subset_edgeSet]
  intro e he
  obtain ⟨S, hS⟩ := hMOE e he
  exact hS.mem_edgeSet_of_isMST_of_injOn hinj hMST

/-- On a finite connected graph with injective edge weights, any subgraph whose edges are all
cut-MOEs is acyclic (since it is a subgraph of the unique MST). -/
theorem isAcyclic_of_forall_isMOE_of_injOn {V W : Type*} [Finite V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G H : SimpleGraph V} (hconn : G.Connected) {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet)
    (hMOE : ∀ e ∈ H.edgeSet, ∃ S : Finset V, IsMOE G w S e) :
    H.IsAcyclic := by
  obtain ⟨T, hMST⟩ := exists_isMST hconn w
  exact hMST.1.2.isAcyclic.anti (le_of_forall_isMOE_of_isMST_of_injOn hinj hMOE hMST)

/-- On a finite connected graph with injective edge weights, any connected graph `H` whose edges are
all cut-MOEs of `(G, w)` is the unique minimum-weight spanning tree of `(G, w)`. -/
theorem isMST_of_forall_isMOE_of_connected_of_injOn {V W : Type*} [Finite V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G H : SimpleGraph V} (hconn : G.Connected) {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet)
    (hHconn : H.Connected) (hMOE : ∀ e ∈ H.edgeSet, ∃ S : Finset V, IsMOE G w S e) :
    IsMST G w H := by
  have := Fintype.ofFinite V
  obtain ⟨T, hMST⟩ := exists_isMST hconn w
  have hHT : H ≤ T := le_of_forall_isMOE_of_isMST_of_injOn hinj hMOE hMST
  have htreeH : H.IsTree := ⟨hHconn, hMST.1.2.isAcyclic.anti hHT⟩
  have heq : H = T := by
    classical
    have hsub : H.edgeFinset ⊆ T.edgeFinset := edgeFinset_mono hHT
    have hcard : H.edgeFinset.card = T.edgeFinset.card := by
      have h1 := htreeH.card_edgeFinset
      have h2 := hMST.1.2.card_edgeFinset
      omega
    have hfin_eq : H.edgeFinset = T.edgeFinset := Finset.eq_of_subset_of_card_le hsub hcard.ge
    rw [← SimpleGraph.edgeSet_inj, ← H.coe_edgeFinset, ← T.coe_edgeFinset, hfin_eq]
  exact heq ▸ hMST

end SimpleGraph
