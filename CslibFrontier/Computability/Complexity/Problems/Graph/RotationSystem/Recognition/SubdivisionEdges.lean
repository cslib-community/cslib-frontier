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

/-- Retain the original occurrence and end tag while selecting its incident first or last
subdivision segment. In particular, the two original loop ends select different segments. -/
@[expose] def subdivisionDart (I : FixedRotationInput) (d : Dart I.graph) :
    Dart (subdivisionGraph I) :=
  (⟨3 * d.1.val + if d.2 then 2 else 0, by
    have hi := d.1.isLt
    simp only [subdivisionGraph, List.length_map, length_subdivide]
    cases d.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩, d.2)

/-- An original dart selects its own occurrence's first or last piece. -/
theorem subdivisionEdgeIndex_subdivisionDart (I : FixedRotationInput) (d : Dart I.graph) :
    subdivisionEdgeIndex I (subdivisionDart I d).1 =
      ⟨d.1, if d.2 then 2 else 0⟩ := by
  have ha := subdivisionEdgeIndex_val I (subdivisionDart I d).1
  generalize subdivisionEdgeIndex I (subdivisionDart I d).1 = a at ha ⊢
  obtain ⟨i, k⟩ := a
  let j : Fin 3 := if d.2 then 2 else 0
  have hjval : j.val = (if d.2 then 2 else 0) := by
    dsimp only [j]
    cases d.2 <;> rfl
  change 3 * d.1.val + (if d.2 then 2 else 0) = 3 * i.val + k.val at ha
  rw [← hjval] at ha
  have hj := j.isLt
  have hk := k.isLt
  exact congrArg₂ SubdivisionEdgeIndex.mk (Fin.ext (by omega)) (Fin.ext (by omega))

/-- The selected outgoing end has its original center and its own fresh occurrence leaf. -/
theorem subdivisionDart_endpoints (I : FixedRotationInput) (d : Dart I.graph) :
    (subdivisionDart I d).vertex = d.vertex ∧
      (subdivisionDart I d).reverse.vertex = I.graph.vertices.length + d.index := by
  rcases d with ⟨i, b⟩
  let e := (subdivisionDart I (i, b)).1
  have h := subdivision_edge_endpoints I e
  rw [Dart.edge_eq_vertices e] at h
  change (Dart.vertex (e, false), Dart.vertex (e, true)) =
    (subdivisionEdgeIndex I (subdivisionDart I (i, b)).1).endpoints at h
  rw [subdivisionEdgeIndex_subdivisionDart] at h
  have hleft := congrArg Prod.fst h
  have hright := congrArg Prod.snd h
  have holdLeft := congrArg Prod.fst (Dart.edge_eq_vertices i)
  have holdRight := congrArg Prod.snd (Dart.edge_eq_vertices i)
  cases b
  · exact ⟨hleft.trans holdLeft, hright⟩
  · refine ⟨hright.trans holdRight, ?_⟩
    change Dart.vertex (e, false) = I.graph.vertices.length + (2 * i.val + 1)
    change Dart.vertex (e, false) = I.graph.vertices.length + 2 * i.val + 1 at hleft
    simpa only [Nat.add_assoc] using hleft

private theorem subdivisionDart_of_original_vertex (I : FixedRotationInput)
    (d : Dart (subdivisionGraph I)) (hd : d.vertex < I.graph.vertices.length) :
    subdivisionDart I ((subdivisionEdgeIndex I d.1).original, d.2) = d := by
  obtain ⟨e, b⟩ := d
  have he := subdivisionEdgeIndex_val I e
  have hends := subdivision_edge_endpoints I e
  generalize subdivisionEdgeIndex I e = a at he hends ⊢
  obtain ⟨i, k⟩ := a
  change e.val = 3 * i.val + k.val at he
  rw [Dart.edge_eq_vertices e] at hends
  have hleft := congrArg Prod.fst hends
  have hright := congrArg Prod.snd hends
  apply Prod.ext
  · apply Fin.ext
    change 3 * i.val + (if b then 2 else 0) = e.val
    fin_cases k <;> cases b
    · exact he.symm
    · change Dart.vertex (e, true) = I.graph.vertices.length + 2 * i.val at hright
      change Dart.vertex (e, true) < I.graph.vertices.length at hd
      omega
    · change Dart.vertex (e, false) = I.graph.vertices.length + 2 * i.val at hleft
      change Dart.vertex (e, false) < I.graph.vertices.length at hd
      omega
    · change Dart.vertex (e, true) = I.graph.vertices.length + 2 * i.val + 1 at hright
      change Dart.vertex (e, true) < I.graph.vertices.length at hd
      omega
    · change Dart.vertex (e, false) = I.graph.vertices.length + 2 * i.val + 1 at hleft
      change Dart.vertex (e, false) < I.graph.vertices.length at hd
      omega
    · exact he.symm
  · rfl

/-- At an original vertex, the subdivision darts are exactly the original incident darts,
with their distinct occurrence indices and end tags retained. -/
def subdivisionDartEquiv (I : FixedRotationInput) (v : ℕ) (hv : v < I.graph.vertices.length) :
    {d : Dart I.graph // d.vertex = v} ≃ {d : Dart (subdivisionGraph I) // d.vertex = v} where
  toFun d := ⟨subdivisionDart I d.val, (subdivisionDart_endpoints I d.val).1.trans d.property⟩
  invFun d :=
    let a : Dart I.graph := ((subdivisionEdgeIndex I d.val.1).original, d.val.2)
    have hd : d.val.vertex < I.graph.vertices.length := lt_of_eq_of_lt d.property hv
    have he : subdivisionDart I a = d.val := subdivisionDart_of_original_vertex I d.val hd
    ⟨a, (subdivisionDart_endpoints I a).1.symm.trans
      ((congrArg Dart.vertex he).trans d.property)⟩
  left_inv d := by
    apply Subtype.ext
    exact Prod.ext
      (congrArg SubdivisionEdgeIndex.original (subdivisionEdgeIndex_subdivisionDart I d.val)) rfl
  right_inv d := by
    apply Subtype.ext
    apply subdivisionDart_of_original_vertex
    rw [d.property]
    exact hv

/-- The forward map on an original vertex's incident darts selects the first or last piece. -/
@[simp] theorem subdivisionDartEquiv_apply_val (I : FixedRotationInput) (v : ℕ)
    (hv : v < I.graph.vertices.length) (d : {d : Dart I.graph // d.vertex = v}) :
    (subdivisionDartEquiv I v hv d).val = subdivisionDart I d.val := by
  rw [subdivisionDartEquiv]
  rfl

/-- Mapping the inverse image of a subdivision dart recovers the actual indexed dart. -/
@[simp] theorem subdivisionDart_subdivisionDartEquiv_symm (I : FixedRotationInput) (v : ℕ)
    (hv : v < I.graph.vertices.length)
    (d : {d : Dart (subdivisionGraph I) // d.vertex = v}) :
    subdivisionDart I ((subdivisionDartEquiv I v hv).symm d).val = d.val := by
  simpa only [subdivisionDartEquiv_apply_val] using
    congrArg Subtype.val ((subdivisionDartEquiv I v hv).apply_symm_apply d)

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
