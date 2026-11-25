/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Clique
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Graphs from an adjacency test

`Graph.ofAdj vs adj` is the graph whose vertices are the positions of the list `vs`, with an edge
from `i` to `j` when `adj vs[i] vs[j]` holds. Its cliques are the sets of positions whose entries
are pairwise adjacent in some direction (`Graph.mem_Clique_ofAdj_iff`). For an irreflexive test
they are the sets of entries of `vs` that are pairwise adjacent
(`Graph.mem_Clique_ofAdj_iff_entries`). The graph is polynomial-time when the list and the test
are (`Graph.computableInPolyTime_ofAdj`).

## Main definitions

* `Cslib.Complexity.Graph.ofAdj`: the graph on the positions of a list with a Boolean adjacency
  test.

## Main results

* `Cslib.Complexity.Graph.ofAdj_adj`: adjacency in `Graph.ofAdj vs adj`.
* `Cslib.Complexity.Graph.mem_Clique_ofAdj_iff`,
  `Cslib.Complexity.Graph.mem_Clique_ofAdj_iff_entries`: the cliques of `Graph.ofAdj vs adj`.
* `Cslib.Complexity.Graph.computableInPolyTime_ofAdj`: building the graph is polynomial-time.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

namespace Graph

variable {V : Type}

/-- The graph on the positions of `vs`, with an edge from `i` to `j` when `adj` holds of the
entries at `i` and `j`. -/
def ofAdj (vs : List V) (adj : V → V → Bool) : Graph :=
  ⟨List.range vs.length,
    vs.zipIdx.flatMap fun a => (vs.zipIdx.filter fun b => adj a.1 b.1).map fun b => (a.2, b.2)⟩

/-- The edges of `ofAdj vs adj`. -/
theorem mem_ofAdj_edges {vs : List V} {adj : V → V → Bool} {i j : ℕ} :
    (i, j) ∈ (ofAdj vs adj).edges ↔
      ∃ (hi : i < vs.length) (hj : j < vs.length), adj vs[i] vs[j] = true := by
  simp only [ofAdj, List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq,
    List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨a, i'⟩, ha, ⟨b, j'⟩, ⟨hb, hadj⟩, rfl, rfl⟩
    simp only [List.getElem?_eq_some_iff] at ha hb
    obtain ⟨hi, rfl⟩ := ha
    obtain ⟨hj, rfl⟩ := hb
    exact ⟨hi, hj, hadj⟩
  · rintro ⟨hi, hj, hadj⟩
    exact ⟨⟨vs[i], i⟩, by simp [hi], ⟨vs[j], j⟩, ⟨by simp [hj], hadj⟩, rfl, rfl⟩

/-- Adjacency in `ofAdj vs adj`: distinct positions whose entries are adjacent in some
direction. -/
theorem ofAdj_adj {vs : List V} {adj : V → V → Bool} {i j : ℕ} :
    (ofAdj vs adj).toSimpleGraph.Adj i j ↔
      i ≠ j ∧ ∃ (hi : i < vs.length) (hj : j < vs.length),
        (adj vs[i] vs[j] || adj vs[j] vs[i]) = true := by
  rw [Graph.toSimpleGraph_adj, mem_ofAdj_edges, mem_ofAdj_edges]
  refine ⟨?_,
    fun ⟨hne, hi, hj, h⟩ => ⟨hne, (Bool.or_eq_true_iff.1 h).imp (⟨hi, hj, ·⟩) (⟨hj, hi, ·⟩)⟩⟩
  rintro ⟨hne, ⟨hi, hj, h⟩ | ⟨hj, hi, h⟩⟩ <;> exact ⟨hne, hi, hj, by simp [h]⟩

/-- The cliques of `ofAdj vs adj`: sets of positions whose entries are pairwise adjacent in some
direction. -/
theorem mem_Clique_ofAdj_iff {vs : List V} {adj : V → V → Bool} {m : ℕ} :
    (⟨ofAdj vs adj, m⟩ : CliqueInstance) ∈ Clique ↔
      ∃ S : Finset ℕ, S.card = m ∧ (∀ i ∈ S, i < vs.length) ∧
        ∀ i ∈ S, ∀ j ∈ S, ∀ (hi : i < vs.length) (hj : j < vs.length), i ≠ j →
          (adj vs[i] vs[j] || adj vs[j] vs[i]) = true := by
  rw [mem_Clique_iff]
  exact ⟨fun ⟨S, hS, hc⟩ => ⟨S, hc.card_eq, fun i hi => by simpa [ofAdj] using hS i hi,
    fun _ hi _ hj _ _ hne => (ofAdj_adj.1 (hc.isClique hi hj hne)).2.choose_spec.choose_spec⟩,
    fun ⟨S, hc, hlt, hadj⟩ => ⟨S, fun i hi => by simpa [ofAdj] using hlt i hi,
      ⟨fun i hi j hj hne => ofAdj_adj.2 ⟨hne, hlt i hi, hlt j hj, hadj i hi j hj _ _ hne⟩, hc⟩⟩⟩

/-- The cliques of `ofAdj vs adj` for an irreflexive test: sets of entries of `vs` that are
pairwise adjacent in some direction. -/
theorem mem_Clique_ofAdj_iff_entries {vs : List V} {adj : V → V → Bool}
    (hirr : ∀ v, adj v v = false) {m : ℕ} :
    (⟨ofAdj vs adj, m⟩ : CliqueInstance) ∈ Clique ↔
      ∃ T : Finset V, T.card = m ∧ (∀ v ∈ T, v ∈ vs) ∧
        ∀ v ∈ T, ∀ w ∈ T, v ≠ w → (adj v w || adj w v) = true := by
  classical
  rw [mem_Clique_ofAdj_iff]
  refine ⟨fun ⟨S, hcard, hlt, hadj⟩ => ⟨S.attach.image fun i => vs[i.1]'(hlt _ i.2), ?_, ?_, ?_⟩,
    fun ⟨T, hcard, hmem, hadj⟩ => ?_⟩
  · rw [Finset.card_image_of_injective, Finset.card_attach, hcard]
    intro i j hij
    by_contra hne
    have h := hadj i.1 i.2 j.1 j.2 (hlt _ i.2) (hlt _ j.2) fun e => hne (Subtype.ext e)
    simp only at hij
    simp [hij, hirr] at h
  · intro _ hv
    obtain ⟨_, -, rfl⟩ := Finset.mem_image.1 hv
    exact List.getElem_mem _
  · intro v hv w hw hvw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
    exact hadj i.1 i.2 j.1 j.2 _ _ fun h => hvw (by simp [h])
  · refine ⟨T.image vs.idxOf, by rw [Finset.card_image_of_injOn
      (fun v hv _ _ h => (List.idxOf_inj (hmem v hv)).1 h), hcard], ?_, ?_⟩
    · intro _ hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi
      exact List.idxOf_lt_length_of_mem (hmem v hv)
    · intro _ hi _ hj _ _ hij
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hj
      rw [List.getElem_idxOf, List.getElem_idxOf]
      exact hadj v hv w hw fun h => hij (h ▸ rfl)

variable {γ : Type} {encIn : γ ↪ List Bool} {encV : V ↪ List Bool}

/-- **Building a graph from an adjacency test is polynomial-time**, for a list and a test
computed in polynomial time. -/
theorem computableInPolyTime_ofAdj {vs : γ → List V} {adj : γ → V → V → Bool}
    (hvs : ComputableInPolyTime vs encIn (encList encV))
    (hadj : ComputableInPolyTime (fun p : γ × (V × V) => adj p.1 p.2.1 p.2.2)
      (encPair encIn (encPair encV encV)) encBool) :
    ComputableInPolyTime (fun a => ofAdj (vs a) (adj a)) encIn encGraph := by
  have hz : ComputableInPolyTime (fun a => (vs a).zipIdx) encIn (encList (encPair encV encUnary)) :=
    (ComputableInPolyTime.zipIdx encV).comp hvs
  have hb := ComputableInPolyTime.unary_to_binary
  have hlen : ComputableInPolyTime (fun a => (vs a).length) encIn encUnary := by fun_prop
  unfold ofAdj
  exact encGraph_mk_polyTime
    (by simpa using (show ComputableInPolyTime (fun a => (List.range (vs a).length).map id)
      encIn (encList encNat) by fun_prop))
    (by fun_prop)

end Graph

end Cslib.Complexity
