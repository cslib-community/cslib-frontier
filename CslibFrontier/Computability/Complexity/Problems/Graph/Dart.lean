/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.Ports
import Mathlib.Data.List.GetD

/-!
# Indexed ends of a listed multigraph

Darts retain edge positions and end tags. Both ends of a loop remain distinct.
-/

public section

namespace Cslib.Complexity.Graph

/-- A listed edge occurrence together with a choice of endpoint. -/
abbrev Dart (G : Graph) := Fin G.edges.length × Bool

namespace Dart

/-- The endpoint of an indexed edge end; `false` selects the first endpoint. -/
@[expose] def vertex {G : Graph} (d : Dart G) : ℕ := G.edgeEndpoint d.1 d.2

/-- The stored endpoints of a listed edge occurrence are its two indexed dart vertices.
This retains occurrence and end tags, including loops and parallel edge records. -/
theorem edge_eq_vertices {G : Graph} (e : Fin G.edges.length) :
    G.edges[e] = (Dart.vertex (G := G) (e, false), Dart.vertex (G := G) (e, true)) := by
  simp [Dart.vertex, Graph.edgeEndpoint]

/-- Reverse an edge while retaining its edge-list occurrence. -/
@[expose] def reverse {G : Graph} (d : Dart G) : Dart G := (d.1, !d.2)

/-- Reversing twice returns the same indexed end. -/
@[simp] theorem reverse_reverse {G : Graph} (d : Dart G) : d.reverse.reverse = d := by
  rcases d with ⟨i, b⟩
  simp [reverse]

/-- Even a loop has two distinct indexed ends. -/
theorem reverse_ne {G : Graph} (d : Dart G) : d.reverse ≠ d := by
  intro h
  have hb := congrArg Prod.snd h
  exact Bool.not_ne_self _ hb

/-- Edge reversal as a permutation of all indexed ends. -/
@[expose] def reversal (G : Graph) : Equiv.Perm (Dart G) where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_reverse
  right_inv := reverse_reverse

/-- There are two darts per listed edge, counting loops and parallel occurrences. -/
theorem card (G : Graph) : Fintype.card (Dart G) = 2 * G.edges.length := by
  simp [Dart, Nat.mul_comm]

/-- Distinct endpoints of a dart are adjacent in the simple graph of the edge list. -/
theorem adj_vertex_reverse {G : Graph} (d : Dart G) (hne : d.vertex ≠ d.reverse.vertex) :
    G.toSimpleGraph.Adj d.vertex d.reverse.vertex := by
  rcases d with ⟨i, side⟩
  have hm : G.edges[i] ∈ G.edges := List.getElem_mem _
  rw [edge_eq_vertices] at hm
  rw [toSimpleGraph_adj]
  cases side
  · exact ⟨hne, Or.inl hm⟩
  · exact ⟨hne, Or.inr hm⟩

end Dart

open Equiv in
/-- Redirect the selected indexed ends to one new label, prepending the label to the vertex
list and keeping all edge positions. This construction depends only on the choice of ends. -/
theorem exists_split_darts (G : Graph) (selected : Dart G → Prop) [DecidablePred selected]
    (w : ℕ) : ∃ (H : Graph) (E : Fin G.edges.length ≃ Fin H.edges.length),
      H.vertices = w :: G.vertices ∧
      ∀ d : Dart G, Dart.vertex (G := H) (E d.1, d.2) = if selected d then w else d.vertex := by
  let endpoint (d : Dart G) := if selected d then w else d.vertex
  let H : Graph := ⟨w :: G.vertices,
    List.ofFn fun i : Fin G.edges.length => (endpoint (i, false), endpoint (i, true))⟩
  have hlen : H.edges.length = G.edges.length := List.length_ofFn
  refine ⟨H, finCongr hlen.symm, rfl, fun ⟨i, b⟩ => ?_⟩
  have hi : i.val < H.edges.length := hlen.symm ▸ i.isLt
  simp only [Dart.vertex, Graph.edgeEndpoint, finCongr_apply, Fin.val_cast,
    List.getD_eq_getElem _ _ hi]
  simp only [H, List.getElem_ofFn]
  cases b <;> rfl

end Cslib.Complexity.Graph
