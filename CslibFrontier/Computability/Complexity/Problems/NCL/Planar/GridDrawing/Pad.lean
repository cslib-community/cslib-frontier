/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Cell
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Reindex
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Prim

/-!
# Exact diagram semantics of a cell layer

The padded single-vertex diagram has precisely the strands drawn by a grid layer. The edge and
vertex equivalences preserve every weighted port and both ordered boundary interfaces.

## Main definitions

* `Cslib.Complexity.NCL.GridDrawing.Pad.diagram`: the exact diagram of a cell layer.

## Main results

* `Cslib.Complexity.NCL.GridDrawing.Pad.drawing`: draw the exact padded diagram graph.
-/

public section

namespace Cslib.Complexity.NCL.GridDrawing.Pad

open Diagram GridRouting GridLayout

variable (left as bs right : List Color) (v : Vertex (Fin as.length ⊕ Fin bs.length))

/-- The primitive cell before adding its bypass wires. -/
abbrev cell : Diagram Prim as bs := gen (show Prim as bs from [v])

/-- The single-vertex diagram beside its two sets of bypass wires. -/
abbrev diagram : Diagram Prim (left ++ (as ++ right)) (left ++ (bs ++ right)) :=
  pad left (cell as bs v) right

/-- A padded boundary has prefix, cell and suffix widths. -/
theorem boundary_length (left middle right : List Color) :
    (left ++ (middle ++ right)).length = left.length + middle.length + right.length := by
  simp only [List.length_append]; omega

/-- Read a diagram edge as its full-layer strand. -/
@[expose] def toStrand : (diagram left as bs right v).Edge →
    Strand left.length as.length bs.length right.length
  | .inl i => inputStrand (i.cast (boundary_length left as right))
  | .inr (.inl e) => e.elim
  | .inr (.inr (.inl j)) => .inr (.inl (.inr j))
  | .inr (.inr (.inr e)) => e.elim

/-- The edge represented by a full-layer strand. -/
@[expose] def fromStrand : Strand left.length as.length bs.length right.length →
    (diagram left as bs right v).Edge
  | .inl i => .inl ⟨i, by simp only [List.length_append]; have := i.isLt; omega⟩
  | .inr (.inl (.inl i)) => .inl ⟨left.length + i, by
      simp only [List.length_append]; have := i.isLt; omega⟩
  | .inr (.inl (.inr j)) => .inr (.inr (.inl j))
  | .inr (.inr j) => .inl ⟨left.length + as.length + j, by
      simp only [List.length_append]; have := j.isLt; omega⟩

/-- Every input strand reads back the corresponding diagram input edge. -/
private theorem fromStrand_of_input (e : Strand left.length as.length bs.length right.length)
    (i : Fin (left.length + as.length + right.length)) (hi : inputIndex e = some i) :
    fromStrand left as bs right v e = .inl (i.cast (boundary_length left as right).symm) := by
  rcases e with j | ((j | j) | j) <;> simp only [inputIndex, Option.some.injEq] at hi
  all_goals cases hi
  all_goals rfl

/-- Diagram edge names and geometric strand names are exactly equivalent. -/
@[expose] def edgeEquiv : (diagram left as bs right v).Edge ≃
    Strand left.length as.length bs.length right.length where
  toFun := toStrand left as bs right v
  invFun := fromStrand left as bs right v
  left_inv e := by
    rcases e with i | (e | (j | e))
    · have hh := fromStrand_of_input left as bs right v _ _
        (inputIndex_inputStrand (b := bs.length) (i.cast (boundary_length left as right)))
      simpa only [toStrand, Fin.cast_cast, Fin.cast_eq_self] using hh
    · exact e.elim
    · rfl
    · exact e.elim
  right_inv e := by
    rcases e with i | ((i | j) | j)
    · exact inputStrand_of_index _ _ rfl
    · exact inputStrand_of_index _ _ rfl
    · rfl
    · exact inputStrand_of_index _ _ rfl

/-- The sole diagram vertex is the sole geometric cell vertex. -/
@[expose] def vertexEquiv : (diagram left as bs right v).Vtx Prim.interp ≃ Unit where
  toFun _ := ()
  invFun _ := .inr (.inl (show Fin 1 from 0))
  left_inv x := by
    rcases x with e | (i | e)
    · exact e.elim
    · have hi : i = (show Fin 1 from 0) := Fin.eq_zero i
      subst i
      rfl
    · exact e.elim
  right_inv _ := rfl

/-- Local vertex edges inside the padded diagram. -/
private def embed : Fin as.length ⊕ Fin bs.length → (diagram left as bs right v).Edge :=
  tensorRight (Diagram.id left) ((cell as bs v).tensor (Diagram.id right)) ∘
    tensorLeft (cell as bs v) (Diagram.id right)

/-- The diagram and the layout use the same local port edge. -/
private theorem toStrand_embed (q : Fin as.length ⊕ Fin bs.length) :
    toStrand left as bs right v (embed left as bs right v q) =
      Cell.embed (k := left.length) (r := right.length) q := by
  cases q with
  | inl i =>
    simp only [embed, tensorLeft, tensorRight, toStrand]
    exact inputStrand_of_index _ _
      (by simp [Cell.embed, inputIndex, Fin.ext_iff, List.appendIndexEquiv])
  | inr j => rfl

/-- The padded graph is exactly the declared vertex with its local edges embedded. -/
private theorem graph_vertex (x : (diagram left as bs right v).Vtx Prim.interp) :
    (diagram left as bs right v).graph Prim.interp x = v.map (embed left as bs right v) := by
  rcases x with e | (i | e)
  · exact e.elim
  · obtain rfl : i = (show Fin 1 from 0) := Fin.eq_zero i
    change (v.map (tensorLeft (cell as bs v) (Diagram.id right))).map
      (tensorRight (Diagram.id left) ((cell as bs v).tensor (Diagram.id right))) =
        v.map (embed left as bs right v)
    exact Vertex.map_map _ _ _
  · exact e.elim

/-- The port equivalence preserves each reference direction. -/
theorem hasPort_iff (x : (diagram left as bs right v).Vtx Prim.interp)
    (e : (diagram left as bs right v).Edge) (d : Bool) :
    HasPort ((diagram left as bs right v).graph Prim.interp) x e d ↔
      HasPort (Cell.graph v) () (edgeEquiv left as bs right v e) d := by
  rw [HasPort, graph_vertex]
  change HasPort (ConstraintGraph.map (fun _ : Unit => v) (embed left as bs right v)) () e d ↔
    HasPort (ConstraintGraph.map (fun _ : Unit => v)
      (Cell.embed (k := left.length) (r := right.length))) ()
      (edgeEquiv left as bs right v e) d
  rw [hasPort_map_iff, hasPort_map_iff]
  exact ⟨fun ⟨q, hq, he⟩ => ⟨q, hq, he ▸ (toStrand_embed left as bs right v q).symm⟩,
    fun ⟨q, hq, he⟩ => ⟨q, hq, (edgeEquiv left as bs right v).injective
      ((toStrand_embed left as bs right v q).trans he)⟩⟩

/-- The padded diagram's bottom interface is the layout's ordered bottom interface. -/
theorem toStrand_bottom (j : Fin (left ++ (bs ++ right)).length) :
    toStrand left as bs right v ((diagram left as bs right v).bottom j) =
      outputStrand (a := as.length) (j.cast (boundary_length left bs right)) := by
  obtain ⟨i | j, rfl⟩ := (List.appendIndexEquiv left (bs ++ right)).surjective j
  · rw [show (diagram left as bs right v).bottom _ = _ from bottom_tensor_left ..]
    simp (disch := omega) [tensorLeft, toStrand, bottom, inputStrand, outputStrand,
      List.appendIndexEquiv, Sum.map]
  obtain ⟨j | t, rfl⟩ := (List.appendIndexEquiv bs right).surjective j
  · simp only [diagram, pad, bottom_tensor_right, bottom, tensorLeft, tensorRight,
      toStrand, Sum.elim_inl, Equiv.symm_apply_apply]
    exact (outputStrand_of_index (.inr (.inl (.inr j))) _
      (by simp [outputIndex, Fin.ext_iff, List.appendIndexEquiv])).symm
  · simp only [diagram, pad, bottom_tensor_right, bottom, tensorRight,
      Sum.elim_inr, Equiv.symm_apply_apply, toStrand]
    exact (inputStrand_of_index (.inr (.inr t)) _
      (by simp [inputIndex, Fin.ext_iff, List.appendIndexEquiv, Nat.add_assoc])).trans
      (outputStrand_of_index (.inr (.inr t)) _
        (by simp [outputIndex, Fin.ext_iff, List.appendIndexEquiv, Nat.add_assoc])).symm

/-- A grid layer draws the exact padded single-vertex diagram, including all bypasses. -/
noncomputable def drawing (hp : v.ports.Perm (genVertex as bs 0).ports)
    (L : Layer left.length as.length bs.length right.length) :
    DiagramDrawing Prim.interp (diagram left as bs right v) :=
  ((Cell.drawing v hp L).castBoundary
    (boundary_length left as right) (boundary_length left bs right)).reindex
    (vertexEquiv left as bs right v) (edgeEquiv left as bs right v)
    (hasPort_iff left as bs right v) Sum.inl (diagram left as bs right v).bottom
    (fun _ => rfl) (toStrand_bottom left as bs right v)

end Cslib.Complexity.NCL.GridDrawing.Pad
