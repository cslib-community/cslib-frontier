/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Planarize

/-!
# Polynomial size of canonical planarization

At most `(2m)²` swaps route the `2m` incidence labels. Source cells contribute one vertex each,
wire caps at most sixteen vertices and twenty-three new edges each, and crossovers contribute the
uniform bounds from the planarization engine.

## Main results

* `Planar.Embedding.plane_vertexCount_le`: at most `n + 16m + 286(2m)²` vertices.
* `Planar.Embedding.plane_innerCount_le`: at most `25m + 429(2m)²` edges in the closed result.
* `Planar.Embedding.compiled_vertices_le`, `Planar.Embedding.compiled_edges_le`: the same bounds
  on the serialized finite graph.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding

open Diagram

variable {m : ℕ}

private theorem source_swaps {E : Type*} (vs : List (Vertex E)) (c : Port E → Color) :
    swapCount (Sources.vertices c vs).diagram = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [Sources.vertices, Sources.tensor, Sources.one, swapCount, ih, Nat.add_zero]

private theorem cap_swaps {E : Type*} (es : List E) (c : E → Color) :
    swapCount (Sinks.caps c es).diagram = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [Sinks.caps, Sinks.tensor, Sinks.cap, swapCount, ih, Nat.add_zero]

/-- Canonical reordering has at most quadratically many crossings in the number of incidences. -/
theorem routing_swapCount_le (vs : List (Vertex (Fin m))) (c : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    swapCount (routing vs c hw).diagram ≤ (2 * m) ^ 2 := by
  unfold routing
  rw [Wiring.swapCount_cast]
  simpa only [length_pairLabels, List.length_finRange] using
    swapCount_reorder_le (Γ := Cell) (fun p => c p.edge) (Sinks.pairLabels (List.finRange m))
      (Sources.vertexLabels vs) (incidencePerm vs hw)

/-- All crossings of the canonical drawing occur in its incidence permutation. -/
theorem diagram_swapCount_le (vs : List (Vertex (Fin m))) (c : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    swapCount (diagram vs c hw) ≤ (2 * m) ^ 2 := by
  change swapCount (sourceBundle vs c).diagram +
    (swapCount (routing vs c hw).diagram + swapCount (sinkBundle c).diagram) ≤ _
  dsimp only [sourceBundle, sinkBundle]
  rw [source_swaps, cap_swaps, Nat.zero_add, Nat.add_zero]
  exact routing_swapCount_le vs c hw

private theorem empty_vertices {Γ : List Color → List Color → Type} (I : Interp Γ) :
    ∀ {a b : List Color} (D : Diagram Γ a b), D.checkGens (fun _ => false) = true →
      vertexList I D = []
  | _, _, .gen _, h => by cases h
  | _, _, .id _, _ => rfl
  | _, _, .swap .., _ => rfl
  | _, _, .comp D₁ D₂, h | _, _, .tensor D₁ D₂, h => by
    simp only [vertexList, empty_vertices I D₁ (Bool.and_eq_true_iff.1 h).1,
      empty_vertices I D₂ (Bool.and_eq_true_iff.1 h).2, List.map_nil, List.nil_append]

private theorem empty_inner {Γ : List Color → List Color → Type} :
    ∀ {a b : List Color} (D : Diagram Γ a b), D.checkGens (fun _ => false) = true →
      D.innerCount = 0
  | _, _, .gen _, h => by cases h
  | _, _, .id _, _ => rfl
  | _, _, .swap .., _ => rfl
  | _, _, .comp D₁ D₂, h | _, _, .tensor D₁ D₂, h => by
    simp only [innerCount, empty_inner D₁ (Bool.and_eq_true_iff.1 h).1,
      empty_inner D₂ (Bool.and_eq_true_iff.1 h).2, Nat.add_zero]

private theorem source_vertices {E : Type*} (vs : List (Vertex E)) (c : Port E → Color) :
    (vertexList Prim.interp ((Sources.vertices c vs).diagram.subst Cell.expand)).length =
      vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change (vertexList Prim.interp
      (((Sources.one c (v.ports.map WeightedPort.port)
          v.minInflow).diagram.subst Cell.expand).tensor
        ((Sources.vertices c vs).diagram.subst Cell.expand))).length = _
    rw [length_vertexList_tensor]
    change 1 + (vertexList Prim.interp
      ((Sources.vertices c vs).diagram.subst Cell.expand)).length = vs.length + 1
    rw [ih]
    omega

private theorem source_inner {E : Type*} (vs : List (Vertex E)) (c : Port E → Color) :
    ((Sources.vertices c vs).diagram.subst Cell.expand).innerCount =
      (Sources.vertexLabels vs).length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [Sources.vertices, Sources.tensor, Sources.one, subst, Cell.expand, innerCount,
      Sources.vertexLabels, List.flatMap_cons, List.length_append, List.length_map, ih]

private theorem cap_vertices {E : Type*} (es : List E) (c : E → Color) :
    (vertexList Prim.interp ((Sinks.caps c es).diagram.subst Cell.expand)).length ≤
      16 * es.length := by
  induction es with
  | nil => exact Nat.zero_le _
  | cons e es ih =>
    change (vertexList Prim.interp ((Gadgets.Wire.cap (c e)).tensor
      ((Sinks.caps c es).diagram.subst Cell.expand))).length ≤ 16 * (es.length + 1)
    rw [length_vertexList_tensor]
    have hc := Gadgets.Wire.cap_length_vertexList_le (c e)
    omega

private theorem cap_inner {E : Type*} (es : List E) (c : E → Color) :
    ((Sinks.caps c es).diagram.subst Cell.expand).innerCount ≤ 23 * es.length := by
  induction es with
  | nil => exact Nat.zero_le _
  | cons e es ih =>
    simp only [Sinks.caps, Sinks.tensor, Sinks.cap, subst, Cell.expand,
      innerCount, List.length_cons]
    have hc := Gadgets.Wire.cap_innerCount_le (c e)
    omega

private theorem routing_empty {a b : List Color} {xs ys : List (Port (Fin m))}
    (W : Wiring Cell a b xs ys) :
    (W.diagram.subst Cell.expand).checkGens (fun _ => false) = true :=
  (checkGens_subst _ _ _).trans (W.all_checks _)

private theorem expanded_vertices (vs : List (Vertex (Fin m))) (c : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (vertexList Prim.interp ((diagram vs c hw).subst Cell.expand)).length ≤ vs.length + 16 * m := by
  have hs := source_vertices vs (fun p => c p.edge)
  have ht := cap_vertices (List.finRange m) c
  have hr := empty_vertices Prim.interp _ (routing_empty (routing vs c hw))
  change (vertexList Prim.interp (((sourceBundle vs c).diagram.subst Cell.expand).comp
    (((routing vs c hw).diagram.subst Cell.expand).comp
      ((sinkBundle c).diagram.subst Cell.expand)))).length ≤ _
  rw [length_vertexList_comp, length_vertexList_comp]
  dsimp only [sourceBundle, sinkBundle]
  rw [hr, List.length_nil, Nat.zero_add, hs]
  simpa only [List.length_finRange] using Nat.add_le_add_left ht vs.length

private theorem expanded_inner (vs : List (Vertex (Fin m))) (c : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    ((diagram vs c hw).subst Cell.expand).innerCount ≤ 25 * m := by
  have hs := source_inner vs (fun p => c p.edge)
  have ht := cap_inner (List.finRange m) c
  have hr := empty_inner _ (routing_empty (routing vs c hw))
  have hl : (Sources.vertexLabels vs).length = 2 * m := by
    rw [(incidencePerm vs hw).length_eq, length_pairLabels, List.length_finRange]
  change ((sourceBundle vs c).diagram.subst Cell.expand).innerCount +
    (((routing vs c hw).diagram.subst Cell.expand).innerCount +
      ((sinkBundle c).diagram.subst Cell.expand).innerCount) ≤ _
  dsimp only [sourceBundle, sinkBundle]
  rw [hr, Nat.zero_add, hs, hl]
  simp only [List.length_finRange] at ht
  omega

/-- Polynomial vertex bound for the canonical planarization. -/
theorem plane_vertexCount_le (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (vertexList Prim.interp (planeDiagram vs hw)).length ≤
      vs.length + 16 * m + 286 * (2 * m) ^ 2 :=
  (length_vertexList_planarizeAlong_le Cell.expand (diagram vs (color vs) hw)).trans
    (Nat.add_le_add (expanded_vertices vs (color vs) hw)
      (Nat.mul_le_mul_left 286 (diagram_swapCount_le vs (color vs) hw)))

/-- Polynomial edge bound for the closed canonical planarization. -/
theorem plane_innerCount_le (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (planeDiagram vs hw).innerCount ≤ 25 * m + 429 * (2 * m) ^ 2 :=
  (innerCount_planarizeAlong_le Cell.expand (diagram vs (color vs) hw)).trans
    (Nat.add_le_add (expanded_inner vs (color vs) hw)
      (Nat.mul_le_mul_left 429 (diagram_swapCount_le vs (color vs) hw)))

/-- The compiled finite graph satisfies the polynomial vertex bound. -/
theorem compiled_vertices_le (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (Word.compile (word vs hw)).vertices.length ≤ vs.length + 16 * m + 286 * (2 * m) ^ 2 := by
  rw [word, compile_toWord]
  simpa only [AndOrGraph.ofFinite, List.length_ofFn] using plane_vertexCount_le vs hw

/-- The compiled finite graph satisfies the polynomial edge bound. -/
theorem compiled_edges_le (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (Word.compile (word vs hw)).edgeCount ≤ 25 * m + 429 * (2 * m) ^ 2 := by
  rw [word, compile_toWord]
  simpa only [AndOrGraph.ofFinite, List.length_nil, Nat.zero_add] using plane_innerCount_le vs hw

end Cslib.Complexity.NCL.Planar.Embedding
