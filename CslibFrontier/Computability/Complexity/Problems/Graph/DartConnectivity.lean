/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Certificate
import Mathlib.Data.List.GetD

/-!
# Dart invariants and existing graph components

Adjacency and trails in induced simple graphs lift to oriented occurrences in the edge list.
Vertex and edge-reversal invariants are constant on existing declared-vertex components.
Point components have no darts.
-/

public section

namespace Cslib.Complexity.Graph

namespace Dart

/-- A simple-graph adjacency is witnessed by an oriented listed edge occurrence. -/
theorem exists_of_adj {G : Graph} {u v : ℕ} (h : G.toSimpleGraph.Adj u v) :
    ∃ d : Dart G, d.vertex = u ∧ d.reverse.vertex = v := by
  obtain ⟨-, h | h⟩ := toSimpleGraph_adj.mp h
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
    change G.edges[i.val] = (u, v) at hi
    refine ⟨(i, false), ?_, ?_⟩ <;>
      simp [vertex, reverse, edgeEndpoint, hi]
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
    change G.edges[i.val] = (v, u) at hi
    refine ⟨(i, true), ?_, ?_⟩ <;>
      simp [vertex, reverse, edgeEndpoint, hi]

/-- Either orientation of a dart gives the same unordered pair of listed endpoints. -/
theorem sym2_vertex_reverse {G : Graph} (d : Dart G) :
    (s(d.vertex, d.reverse.vertex) : Sym2 ℕ) = s(G.edges[d.1].1, G.edges[d.1].2) := by
  rcases d with ⟨i, b⟩
  rw [edge_eq_vertices i]
  cases b
  · rfl
  · exact Sym2.eq_swap

/-- Each step of a trail in an induced simple graph lifts to an oriented listed edge.
The chosen occurrences have distinct indices, and preserve the order of the trail's vertices. -/
theorem exists_darts_of_induced_trail {G : Graph} {S : Set ℕ} {u v : S}
    (p : (G.toSimpleGraph.induce S).Walk u v) (hp : p.IsTrail) :
    ∃ d : Fin p.length → Dart G, Function.Injective (fun i => (d i).1) ∧
      ∀ i, (d i).vertex = (p.getVert i).val ∧
        (d i).reverse.vertex = (p.getVert (i.val + 1)).val := by
  classical
  have hlift (i : Fin p.length) : ∃ d : Dart G,
      d.vertex = (p.getVert i).val ∧ d.reverse.vertex = (p.getVert (i.val + 1)).val :=
    exists_of_adj (p.adj_getVert_succ i.isLt)
  choose d hd using hlift
  refine ⟨d, ?_, hd⟩
  intro i j hij
  have hi : i.val < p.edges.length := p.length_edges.symm ▸ i.isLt
  have hj : j.val < p.edges.length := p.length_edges.symm ▸ j.isLt
  apply Fin.ext ((hp.edges_nodup.getElem_inj_iff (hi := hi) (hj := hj)).mp ?_)
  apply Sym2.map.injective (f := Subtype.val) Subtype.val_injective
  simp only [SimpleGraph.Walk.getElem_edges, Sym2.map_mk, ← (hd i).1, ← (hd i).2,
    ← (hd j).1, ← (hd j).2, sym2_vertex_reverse, hij]

/-- Vertex invariance and reversal invariance imply constancy on existing edge components.
Only finite listed edge witnesses are used; the ambient natural-number universe need not be
finite. The component hypothesis already includes endpoint declarations. -/
theorem eq_of_sameComponent {G : Graph} {β : Sort*} (f : Dart G → β)
    (hv : ∀ d e, d.vertex = e.vertex → f d = f e)
    (ha : ∀ d, f d = f d.reverse) {d e : Dart G}
    (h : RotationCertificate.SameComponent G d.vertex e.vertex) : f d = f e := by
  obtain ⟨hd, he, ⟨p⟩⟩ := h
  have hw {u v : {v // v ∈ G.vertices}} (p : G.induced.Walk u v) :
      ∀ d e : Dart G, d.vertex = u.val → e.vertex = v.val → f d = f e := by
    induction p with
    | nil =>
      intro d e hd he
      exact hv d e (hd.trans he.symm)
    | @cons u v w hadj p ih =>
      intro d e hd he
      obtain ⟨a, hau, hav⟩ := exists_of_adj hadj
      exact (hv d a (hd.trans hau.symm)).trans ((ha a).trans (ih a.reverse e hav he))
  exact hw p d e rfl rfl

/-- Every vertex in an edge component has an incident dart. This does not invent a dart for
a declared isolated point. -/
theorem exists_of_sameComponent {G : Graph} (d : Dart G) (v : ℕ)
    (h : RotationCertificate.SameComponent G d.vertex v) : ∃ e : Dart G, e.vertex = v := by
  by_cases hv : d.vertex = v
  · exact ⟨d, hv⟩
  obtain ⟨hd, hv', hc⟩ := h
  obtain ⟨w, hw⟩ := hc.nonempty_neighborSet_right (by
    intro he
    exact hv (congrArg Subtype.val he))
  obtain ⟨e, he, -⟩ := exists_of_adj hw
  exact ⟨e, he⟩

end Dart

end Cslib.Complexity.Graph
