/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Orthogonal
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Pad
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Composition
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Identity
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Compile
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Finite

/-!
# Orthogonal drawings of the exact compiled graph

Realize each layered word drawing by complete paths for its diagram edges. Shared interfaces
join paths on the same edge, and compilation changes only the vertex and edge names.

## Main definitions

* `Cslib.Complexity.NCL.Slice.OrthogonalDrawing.diagram`: the exact padded cell diagram.
* `Cslib.Complexity.NCL.Word.OrthogonalDrawing.diagram`: the whole interpreted diagram.

## Main results

* `Cslib.Complexity.NCL.Word.orthogonalDrawing_compile`: every closed well-typed plane word
  admits a complete orthogonal drawing of its compiled constraint graph.
-/

public section

namespace Cslib.Complexity.NCL

open Diagram

/-- The exact padded primitive diagram represented by one drawn word layer. -/
@[expose] def Slice.OrthogonalDrawing.diagram {sl : Slice} {source target : List Color}
    (L : sl.OrthogonalDrawing source target) : Diagram Prim source target :=
  Eq.mp (congrArg₂ (Diagram Prim)
    (L.source_eq.trans (List.append_assoc _ _ _)).symm
    (L.target_eq.trans (List.append_assoc _ _ _)).symm)
    (GridDrawing.Pad.diagram L.left L.inputs L.outputs L.right L.vertex)

/-- Flattening the layer diagram recovers the original slice, including its vertex data. -/
theorem Slice.OrthogonalDrawing.toWord_diagram {sl : Slice} {source target : List Color}
    (L : sl.OrthogonalDrawing source target) : L.diagram.toWord Prim.interp 0 = [sl] := by
  rcases L with ⟨left, as, bs, right, v, hsl, hs, ht, hp, layout⟩
  have hs' := hs.trans (List.append_assoc left as right)
  have ht' := ht.trans (List.append_assoc left bs right)
  cases hs'
  cases ht'
  change (pad left (Diagram.gen (show Prim as bs from [v])) right).toWord Prim.interp 0 = [sl]
  simpa only [pad, toWord, List.nil_append, List.append_nil, Nat.zero_add, Prim.interp] using
    congrArg (fun sl => [sl]) hsl.symm

/-- The complete edge paths of one word layer draw its exact diagram graph. -/
private noncomputable def Slice.OrthogonalDrawing.geometric {sl : Slice}
    {source target : List Color}
    (L : sl.OrthogonalDrawing source target) :
    GridDrawing.DiagramDrawing Prim.interp L.diagram := by
  rcases L with ⟨left, as, bs, right, v, hsl, hs, ht, hp, layout⟩
  have hs' := hs.trans (List.append_assoc left as right)
  have ht' := ht.trans (List.append_assoc left bs right)
  cases hs'
  cases ht'
  exact GridDrawing.Pad.drawing left as bs right v hp layout

/-- Recover the typed primitive diagram represented by a layered word drawing. -/
@[expose] def Word.OrthogonalDrawing.diagram {w : Word} {a b : List Color} :
    w.OrthogonalDrawing a b → Diagram Prim a b
  | .nil a => Diagram.id a
  | .cons layer rest => layer.diagram.comp rest.diagram

/-- Flattening the recovered diagram returns the original word exactly. -/
theorem Word.OrthogonalDrawing.toWord_diagram {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) : D.diagram.toWord Prim.interp 0 = w := by
  induction D with
  | nil _ => rfl
  | cons layer rest ih =>
    rw [diagram, Diagram.toWord, layer.toWord_diagram, ih]
    rfl

/-- Replace the layered construction by full finite paths for all its diagram edges. -/
private noncomputable def Word.OrthogonalDrawing.geometric {w : Word} {a b : List Color} :
    (D : w.OrthogonalDrawing a b) → GridDrawing.DiagramDrawing Prim.interp D.diagram
  | .nil a => GridDrawing.identity Prim.interp a
  | .cons layer rest => GridDrawing.comp layer.geometric rest.geometric

/-- The exact compiled graph of every closed well-typed plane word has an orthogonal drawing.
Each edge is a complete finite path, its endpoints are the corresponding port vertices, paths
avoid nonincident vertices, and distinct edge paths meet only at common incident vertices. -/
theorem Word.orthogonalDrawing_compile {w : Word} (hP : w.checkPlane = true)
    (hT : w.WellTyped [] []) : Nonempty (GridDrawing.Closed w.compile.graph) := by
  obtain ⟨D⟩ := Word.orthogonalDrawing hP hT
  rw [← D.toWord_diagram, compile_toWord]
  exact ⟨(GridDrawing.Closed.finite D.diagram D.geometric.close).ofFinite⟩

end Cslib.Complexity.NCL
