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

private theorem subdivision_edge_cases (I : FixedRotationInput)
    (e : Fin (subdivisionGraph I).edges.length) :
    ∃ (i : Fin I.graph.edges.length) (k : Fin 3), e.val = 3 * i.val + k.val ∧
      (subdivisionGraph I).edges[e] =
        ([(I.graph.edges[i].1, I.graph.vertices.length + 2 * i.val),
          (I.graph.vertices.length + 2 * i.val, I.graph.vertices.length + 2 * i.val + 1),
          (I.graph.vertices.length + 2 * i.val + 1, I.graph.edges[i].2)] :
            List (ℕ × ℕ))[k] := by
  have he : e.val < (subdivide I).length := by
    simpa only [subdivisionGraph, List.length_map] using e.isLt
  have hsize : e.val < 3 * I.graph.edges.length := by
    simpa only [length_subdivide] using he
  let i : Fin I.graph.edges.length := ⟨e.val / 3, by omega⟩
  let k : Fin 3 := ⟨e.val % 3, Nat.mod_lt _ (by decide)⟩
  have hindex : 3 * i.val + k.val = e.val := by dsimp [i, k]; omega
  have hlookup := subdivide_getElem? I i k
  rw [hindex] at hlookup
  have hget := Option.some.inj ((List.getElem?_eq_getElem he).symm.trans hlookup)
  refine ⟨i, k, hindex.symm, ?_⟩
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
  obtain ⟨i, k, he, hep⟩ := subdivision_edge_cases I e
  obtain ⟨j, l, hf, hfp⟩ := subdivision_edge_cases I f
  have hi := hI.edge_endpoints_lt (List.getElem_mem i.isLt)
  have hj := hI.edge_endpoints_lt (List.getElem_mem j.isLt)
  have hp := Sym2.eq_iff.mp h
  rw [hep, hfp] at hp
  fin_cases k <;> fin_cases l <;>
    simp only [Fin.getElem_fin, List.getElem_cons_zero, List.getElem_cons_succ] at hp
  all_goals rcases hp with hp | hp <;> apply Fin.ext <;> omega

end Cslib.Complexity.Graph.RotationRecognition
