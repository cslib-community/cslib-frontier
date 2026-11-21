/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Parity
public import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Indexed edges of the twice subdivision

The stored subdivision retains three indexed segments for each original edge occurrence.
Their unordered endpoint pairs distinguish all occurrences under valid endpoint bounds,
even for original loops, repeated edges and reversed edges. The vertex range is unchanged.

## Main results

* `Cslib.Complexity.Graph.RotationRecognition.subdivide_getElem?`: the exact indexed
  three-case subdivision specification, including the stored frozen flags.
* `Cslib.Complexity.Graph.RotationRecognition.subdivisionGraph_edge_injective`: unordered
  endpoints identify an actual indexed subdivision edge.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

/-- The three stored segments of an original occurrence, with their literal endpoints and
frozen flags. This indexed specification applies to raw inputs without a validity premise. -/
theorem subdivide_getElem? (I : FixedRotationInput)
    (i : Fin I.graph.edges.length) (k : Fin 3) :
    (subdivide I)[3 * i.val + k.val]? = some
      ([((I.graph.edges[i].1, I.graph.vertices.length + 2 * i.val),
          (I.orders.getD I.graph.edges[i].1 none).isSome),
        ((I.graph.vertices.length + 2 * i.val, I.graph.vertices.length + 2 * i.val + 1), false),
        ((I.graph.vertices.length + 2 * i.val + 1, I.graph.edges[i].2),
          (I.orders.getD I.graph.edges[i].2 none).isSome)] : List Segment)[k] := by
  let entries := I.graph.edges.zipIdx
  let emit : (ℕ × ℕ) × ℕ → List Segment := fun ((u, v), j) =>
    [((u, I.graph.vertices.length + 2 * j), (I.orders.getD u none).isSome),
      ((I.graph.vertices.length + 2 * j, I.graph.vertices.length + 2 * j + 1), false),
      ((I.graph.vertices.length + 2 * j + 1, v), (I.orders.getD v none).isSome)]
  have hi : i.val < entries.length := by simp [entries]
  have hsplit : entries = entries.take i.val ++ entries[i.val] :: entries.drop (i.val + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hprefix : ((entries.take i.val).flatMap emit).length = 3 * i.val := by
    simp [emit, List.length_flatMap, Nat.min_eq_left hi.le, Nat.mul_comm]
  change (entries.flatMap emit)[3 * i.val + k.val]? = _
  rw [hsplit, List.flatMap_append, List.flatMap_cons,
    List.getElem?_append_right (by omega), hprefix]
  have hsub : 3 * i.val + k.val - 3 * i.val = k.val := by omega
  rw [hsub, List.getElem?_append_left (by simp [emit])]
  simp [emit, entries, List.getElem_zipIdx]

/-- The original occurrence and the position of a stored subdivision edge within it. -/
structure SubdivisionEdgeIndex (I : FixedRotationInput) where
  /-- The original indexed edge occurrence. -/
  original : Fin I.graph.edges.length
  /-- The first, middle or last piece, in traversal order. -/
  piece : Fin 3

private theorem subdivision_edge_lt (I : FixedRotationInput)
    (e : Fin (subdivisionGraph I).edges.length) :
    e.val < (subdivide I).length := by
  simpa only [subdivisionGraph, List.length_map] using e.isLt

/-- Decode a stored subdivision edge in the same order as the three-piece blocks. -/
def subdivisionEdgeIndex (I : FixedRotationInput) (e : Fin (subdivisionGraph I).edges.length) :
    SubdivisionEdgeIndex I :=
  let packed : Fin (I.graph.edges.length * 3) := ⟨e.val, by
    simpa only [length_subdivide, Nat.mul_comm] using subdivision_edge_lt I e⟩
  let parts := finProdFinEquiv.symm packed
  ⟨parts.1, parts.2⟩

/-- The decoded original occurrence and piece reconstruct the stored index. -/
theorem subdivisionEdgeIndex_val (I : FixedRotationInput)
    (e : Fin (subdivisionGraph I).edges.length) :
    e.val = 3 * (subdivisionEdgeIndex I e).original.val + (subdivisionEdgeIndex I e).piece.val := by
  change e.val = 3 * (e.val / 3) + e.val % 3
  rw [Nat.add_comm, Nat.mod_add_div]

/-- The ordered source or fresh vertex names at the ends of the decoded piece. -/
@[expose] def SubdivisionEdgeIndex.endpoints {I : FixedRotationInput} (d : SubdivisionEdgeIndex I) :
    ℕ × ℕ :=
  let i := d.original
  ([(I.graph.edges[i].1, I.graph.vertices.length + 2 * i.val),
    (I.graph.vertices.length + 2 * i.val, I.graph.vertices.length + 2 * i.val + 1),
    (I.graph.vertices.length + 2 * i.val + 1, I.graph.edges[i].2)] :
      List (ℕ × ℕ))[d.piece]

/-- The ordered endpoints of a stored subdivision edge are its decoded endpoints. -/
theorem subdivision_edge_endpoints (I : FixedRotationInput)
    (e : Fin (subdivisionGraph I).edges.length) :
    (subdivisionGraph I).edges[e] = (subdivisionEdgeIndex I e).endpoints := by
  have he := subdivisionEdgeIndex_val I e
  generalize subdivisionEdgeIndex I e = d at he ⊢
  obtain ⟨i, k⟩ := d
  have hlookup := subdivide_getElem? I i k
  change e.val = 3 * i.val + k.val at he
  rw [← he] at hlookup
  have hget :=
    Option.some.inj ((List.getElem?_eq_getElem (subdivision_edge_lt I e)).symm.trans hlookup)
  change ((subdivide I).map Segment.endpoints)[e.val] = _
  rw [List.getElem_map, hget]
  generalize k = k'
  fin_cases k' <;> rfl

/-- Unordered endpoints identify the actual indexed subdivision occurrence. Original loops,
parallel edges and reversed occurrences retain their distinct fresh vertices. -/
theorem subdivisionGraph_edge_injective {I : FixedRotationInput} (hI : Valid I) :
    Function.Injective (fun e : Fin (subdivisionGraph I).edges.length =>
      (s(((subdivisionGraph I).edges[e]).1, ((subdivisionGraph I).edges[e]).2) : Sym2 ℕ)) := by
  intro e f h
  generalize hIe : subdivisionEdgeIndex I e = de
  generalize hIf : subdivisionEdgeIndex I f = df
  obtain ⟨i, k⟩ := de
  obtain ⟨j, l⟩ := df
  have he : e.val = 3 * i.val + k.val := by
    simpa only [hIe] using subdivisionEdgeIndex_val I e
  have hf : f.val = 3 * j.val + l.val := by
    simpa only [hIf] using subdivisionEdgeIndex_val I f
  have hep := subdivision_edge_endpoints I e
  have hfp := subdivision_edge_endpoints I f
  rw [hIe] at hep
  rw [hIf] at hfp
  have hi := hI.edge_endpoints_lt (List.getElem_mem i.isLt)
  have hj := hI.edge_endpoints_lt (List.getElem_mem j.isLt)
  have hp := Sym2.eq_iff.mp h
  rw [hep, hfp] at hp
  fin_cases k <;> fin_cases l <;>
    simp only [SubdivisionEdgeIndex.endpoints, Fin.getElem_fin, List.getElem_cons_zero,
      List.getElem_cons_succ] at hp
  all_goals rcases hp with hp | hp <;> apply Fin.ext <;> omega

end Cslib.Complexity.Graph.RotationRecognition
