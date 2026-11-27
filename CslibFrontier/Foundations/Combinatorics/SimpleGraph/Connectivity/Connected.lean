/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Empty cuts of disconnected graphs

A graph on a nonempty finite vertex set that is not connected has a vertex set `S` with
`1 ≤ |S|`, `2 |S| ≤ |V|` and no edge between `S` and its complement
(`SimpleGraph.exists_forall_not_adj_of_not_connected`): take the reachability class of a vertex
or its complement, whichever is smaller. This is the combinatorial step of the union bound over
cuts for the connectivity of random graphs. A graph homomorphism also carries reachability
within a component to the induced graph on its image.
-/

public section

open Finset
open scoped Finset

namespace SimpleGraph

variable {V : Type*}

/-- Any two vertices in the image of a connected component are reachable within that
image, even if the homomorphism identifies vertices. -/
theorem ConnectedComponent.reachable_induce_image {W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (C : G.ConnectedComponent) (f : G →g H)
    {x y : W} (hx : x ∈ f '' C.supp) (hy : y ∈ f '' C.supp) :
    (H.induce (f '' C.supp)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact (C.reachable_toSimpleGraph ha hb).map
    (SimpleGraph.induceHom f (fun _ hu => ⟨_, hu, rfl⟩) :
      C.toSimpleGraph →g H.induce (f '' C.supp))

/-- A graph on a nonempty finite vertex set that is not connected has a nonempty vertex set `S`
with at most half of the vertices and no edge between `S` and its complement. -/
theorem exists_forall_not_adj_of_not_connected [Fintype V] [Nonempty V]
    {G : SimpleGraph V} (hG : ¬G.Connected) :
    ∃ S : Finset V, 1 ≤ #S ∧ 2 * #S ≤ Fintype.card V ∧ ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v := by
  classical
  rw [connected_iff] at hG
  simp only [‹Nonempty V›, and_true, Preconnected, not_forall] at hG
  obtain ⟨u, v, huv⟩ := hG
  set C : Finset V := {w | G.Reachable u w} with hC
  have hclosed (a b : V) (hab : G.Adj a b) : a ∈ C ↔ b ∈ C := by
    simp only [hC, mem_filter, mem_univ, true_and]
    exact ⟨(·.trans hab.reachable), (·.trans hab.symm.reachable)⟩
  have hsum : #C + #Cᶜ = Fintype.card V := card_add_card_compl C
  by_cases h : 2 * #C ≤ Fintype.card V
  · exact ⟨C, card_pos.2 ⟨u, by simp [hC]⟩, h, fun a ha b hb hab => hb ((hclosed a b hab).1 ha)⟩
  · refine ⟨Cᶜ, card_pos.2 ⟨v, mem_compl.2 (by simpa [hC] using huv)⟩, by omega,
      fun a ha b hb hab => ?_⟩
    rw [mem_compl] at ha hb
    exact ha ((hclosed a b hab).2 (not_not.1 hb))

/-- Every disconnected finite nonempty graph without isolated vertices contains a connected induced
subgraph on a vertex subset `S` with `2 ≤ #S ≤ |V| / 2` and no edges leaving `S`. -/
theorem exists_connected_induce_forall_not_adj_of_not_connected {V : Type*} [Fintype V]
    [Nonempty V] {G : SimpleGraph V} (hnc : ¬G.Connected)
    (hni : ∀ v, ¬G.IsIsolated v) :
    ∃ S : Finset V, 2 ≤ #S ∧ 2 * #S ≤ Fintype.card V ∧ (G.induce (S : Set V)).Connected ∧
      ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v := by
  classical
  let K (u : V) : Finset V := Finset.univ.filter fun w => G.Reachable u w
  have hK_mem (u w : V) : w ∈ K u ↔ G.Reachable u w := by simp [K]
  obtain ⟨u₀, _, hu₀min⟩ :=
    Finset.exists_min_image Finset.univ (fun u => #(K u)) Finset.univ_nonempty
  have ⟨v₀, hv₀⟩ : ∃ v₀ : V, v₀ ∉ K u₀ := by
    by_contra! hall
    exact hnc ⟨fun a b => ((hK_mem u₀ a).mp (hall a)).symm.trans ((hK_mem u₀ b).mp (hall b))⟩
  have hdisj : Disjoint (K u₀) (K v₀) := Finset.disjoint_left.mpr fun w hwu hwv =>
    hv₀ ((hK_mem u₀ v₀).mpr (((hK_mem u₀ w).mp hwu).trans ((hK_mem v₀ w).mp hwv).symm))
  have hsum_card : #(K u₀) + #(K v₀) ≤ Fintype.card V :=
    Finset.card_union_of_disjoint hdisj ▸ Finset.card_le_univ _
  have hle_half : 2 * #(K u₀) ≤ Fintype.card V := by
    have := hu₀min v₀ (Finset.mem_univ v₀)
    omega
  have hcard_ge_two : 2 ≤ #(K u₀) := by
    by_contra! hlt
    have hK_eq : K u₀ = {u₀} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨(hK_mem u₀ u₀).mpr Reachable.rfl, fun w hw => by
        by_contra hne
        have h2 := Finset.card_le_card (s := {u₀, w}) (t := K u₀) fun x hx => by
          rcases Finset.mem_insert.mp hx with hx | hx
          · exact hx ▸ (hK_mem u₀ u₀).mpr Reachable.rfl
          · exact Finset.mem_singleton.mp hx ▸ hw
        rw [Finset.card_pair (Ne.symm hne)] at h2; omega⟩
    exact hni u₀ fun w hadj => hadj.ne <| by
      have hw := (hK_mem u₀ w).mpr hadj.reachable
      rwa [hK_eq, Finset.mem_singleton, eq_comm] at hw
  have hind_conn : (G.induce (K u₀ : Set V)).Connected := by
    have hsupp : (K u₀ : Set V) = (G.connectedComponentMk u₀).supp := by
      ext
      simp [K, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, reachable_comm]
    rw [hsupp]
    exact (G.connectedComponentMk u₀).connected_toSimpleGraph
  exact ⟨K u₀, hcard_ge_two, hle_half, hind_conn, fun x hx y hy hadj =>
    hy ((hK_mem u₀ y).mpr (((hK_mem u₀ x).mp hx).trans hadj.reachable))⟩

/-- Every connected finite graph contains a spanning tree edge subset of cardinality
`|V| - 1`. All elements of this subset are non-diagonal edges of `G`. -/
theorem exists_card_sub_one_subset_edgeSet_of_connected {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hc : G.Connected) :
    ∃ t : Finset (Sym2 V), #t = Fintype.card V - 1 ∧ ∀ e ∈ t, e ∈ G.edgeSet ∧ ¬e.IsDiag := by
  classical
  obtain ⟨T, hTG, hT⟩ := hc.exists_isTree_le
  refine ⟨T.edgeFinset, by have := hT.card_edgeFinset; omega, fun e he => ?_⟩
  have heG : e ∈ G.edgeSet := edgeSet_mono hTG (mem_edgeFinset.mp he)
  exact ⟨heG, G.not_isDiag_of_mem_edgeSet heG⟩

end SimpleGraph
