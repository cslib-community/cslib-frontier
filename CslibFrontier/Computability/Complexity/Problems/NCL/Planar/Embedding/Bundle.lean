/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Cells
import Mathlib.Data.List.OfFn

/-!
# Labeled source and sink bundles

A source bundle presents all its edges at the lower boundary; a sink bundle creates no edges.
Their labels identify the threshold constraints after a wire permutation is inserted between
them. The records retain the local legality calculation through juxtaposition.

## Main definitions

* `Planar.Embedding.Sources`, `Planar.Embedding.Sinks`: labeled source and sink drawings.
* `Planar.Embedding.Sources.one`: one threshold vertex with all its ports below it.
* `Planar.Embedding.Sinks.cap`: a wire cap with its two incidence labels above it.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding

open Diagram

variable {Label : Type*} {a b : List Color} {xs ys : List Label}
  {specs specs' : List (Vertex Label)}

/-- A source drawing, whose edges are all exposed below it. -/
structure Sources (a : List Color) (tags : List Label) (specs : List (Vertex Label)) where
  /-- The source drawing. -/
  diagram : Diagram Cell [] a
  /-- The labels read below the drawing. -/
  labeling : Labeling diagram [] tags
  /-- Every edge appears at the lower boundary. -/
  bottom_surjective : Function.Surjective diagram.bottom
  /-- Its labeled configurations are exactly the listed source constraints. -/
  legal_iff (u : Label → Bool) : (diagram.graph Cell.interp).Legal (u ∘ labeling.label) ↔
    ∀ v ∈ specs, v.Sat u

/-- A sink drawing, which creates no edges. -/
structure Sinks (a : List Color) (tags : List Label) (specs : List (Vertex Label)) where
  /-- The sink drawing. -/
  diagram : Diagram Cell a []
  /-- The labels read above the drawing. -/
  labeling : Labeling diagram tags []
  /-- Sinks introduce no additional edges. -/
  no_inner : IsEmpty diagram.Inner
  /-- Its labeled configurations are exactly the listed sink constraints. -/
  legal_iff (u : Label → Bool) : (diagram.graph Cell.interp).Legal (u ∘ labeling.label) ↔
    ∀ v ∈ specs, v.Sat u

private theorem bottom_surjective_tensor {Γ : List Color → List Color → Type}
    {a b c d : List Color} {D : Diagram Γ a b} {D' : Diagram Γ c d}
    (h : Function.Surjective D.bottom) (h' : Function.Surjective D'.bottom) :
    Function.Surjective (D.tensor D').bottom := by
  intro e
  rcases tensor_cases e with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · obtain ⟨j, rfl⟩ := h e
    exact ⟨(List.appendIndexEquiv b d) (.inl j), bottom_tensor_left ..⟩
  · obtain ⟨j, rfl⟩ := h' e
    exact ⟨(List.appendIndexEquiv b d) (.inr j), bottom_tensor_right ..⟩

namespace Sources

/-- Juxtapose source bundles and concatenate their constraints. -/
@[expose] def tensor (D : Sources a xs specs) (D' : Sources b ys specs') :
    Sources (a ++ b) (xs ++ ys) (specs ++ specs') where
  diagram := D.diagram.tensor D'.diagram
  labeling := D.labeling.tensor D'.labeling
  bottom_surjective := by
    exact bottom_surjective_tensor D.bottom_surjective D'.bottom_surjective
  legal_iff u := by
    rw [Labeling.legal_tensor, D.legal_iff, D'.legal_iff]
    simp only [List.forall_mem_append]

/-- The empty source bundle. -/
@[expose] def nil : Sources [] ([] : List Label) [] where
  diagram := .id []
  labeling := .id [] [] rfl
  bottom_surjective e := e.elim Fin.elim0 Empty.elim
  legal_iff _ := by
    constructor
    · intro _ v hv
      exact (List.not_mem_nil hv).elim
    · intro _ v
      exact v.elim

/-- A source vertex with the listed wire labels, colors, and threshold. -/
@[expose] def spec (color : Label → Color) (tags : List Label) (need : ℕ) : Vertex Label :=
  ⟨tags.map (fun p => ⟨⟨p, false⟩, (color p).weight⟩), need⟩

/-- The label at a source generator's boundary position. -/
@[expose] def sourceLabel (color : Label → Color) (tags : List Label) :
    Fin 0 ⊕ Fin (tags.map color).length → Label :=
  Sum.elim Fin.elim0 (fun i => tags.get (i.cast (List.length_map ..)))

/-- The labels of a source generator follow its output wire order. -/
@[expose] def labels (color : Label → Color) (tags : List Label) (need : ℕ) :
    Labeling (.gen (Cell.source (tags.map color) need)) [] tags where
  label := sourceLabel color tags
  top_eq := rfl
  bot_eq := by
    change List.ofFn (fun i : Fin (tags.map color).length =>
      tags.get (i.cast (List.length_map ..))) = tags
    rw [List.ofFn_congr (List.length_map ..)]
    simp

/-- Reading the source generator through its labels gives its threshold constraint. -/
theorem map_source (color : Label → Color) (tags : List Label) (need : ℕ) :
    (genVertex [] (tags.map color) need).map (sourceLabel color tags) = spec color tags need := by
  simp only [Vertex.map, genVertex, List.length_nil, List.finRange_zero, List.map_nil,
    List.nil_append, List.map_map, Function.comp_def, WeightedPort.map, Port.map, sourceLabel, spec]
  congr 1
  rw [← List.ofFn_eq_map, List.ofFn_congr (List.length_map ..)]
  simpa using List.ofFn_getElem_eq_map tags
    (fun p : Label => (⟨⟨p, false⟩, (color p).weight⟩ : WeightedPort Label))

/-- Draw one threshold vertex with all ports below it. -/
@[expose] def one (color : Label → Color) (tags : List Label) (need : ℕ) :
    Sources (tags.map color) tags [spec color tags need] where
  diagram := .gen (.source (tags.map color) need)
  labeling := labels color tags need
  bottom_surjective e := by
    rcases e with i | j
    · exact i.elim0
    · exact ⟨j, rfl⟩
  legal_iff u := by
    refine (genLegal_iff (I := Cell.interp) (Cell.source (tags.map color) need)
      (u ∘ sourceLabel color tags)).symm.trans ?_
    change (∀ v ∈ [genVertex [] (tags.map color) need], v.Sat (u ∘ sourceLabel color tags)) ↔ _
    simp only [List.forall_mem_singleton]
    exact (Vertex.sat_map (sourceLabel color tags)
      (genVertex [] (tags.map color) need) u).symm.trans
      (by rw [map_source])

/-- The original incidence labels, ordered by vertices and then by ports. -/
@[expose] def vertexLabels {E : Type*} (vs : List (Vertex E)) : List (Port E) :=
  vs.flatMap (fun v => v.ports.map WeightedPort.port)

/-- The original vertices with all reference directions pointing into source cells. -/
@[expose] def vertexSpecs {E : Type*} (color : Port E → Color) (vs : List (Vertex E)) :
    List (Vertex (Port E)) :=
  vs.map (fun v => spec color (v.ports.map WeightedPort.port) v.minInflow)

/-- The source boundary colors in vertex and port order. -/
@[expose] def vertexColors {E : Type*} (color : Port E → Color) : List (Vertex E) → List Color
  | [] => []
  | v :: vs => (v.ports.map WeightedPort.port).map color ++ vertexColors color vs

/-- Source boundary colors are the colors of the ordered incidence labels. -/
theorem vertexColors_eq {E : Type*} (color : Port E → Color) (vs : List (Vertex E)) :
    vertexColors color vs = (vertexLabels vs).map color := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [vertexColors, vertexLabels, List.flatMap_cons, List.map_append, ih]

/-- Draw all vertices as sources, preserving their port order. -/
@[expose] def vertices {E : Type*} (color : Port E → Color) : (vs : List (Vertex E)) →
    Sources (vertexColors color vs) (vertexLabels vs) (vertexSpecs color vs)
  | [] => nil
  | v :: vs => (one color (v.ports.map WeightedPort.port) v.minInflow).tensor (vertices color vs)

end Sources

namespace Sinks

/-- Juxtapose sink bundles and concatenate their constraints. -/
@[expose] def tensor (D : Sinks a xs specs) (D' : Sinks b ys specs') :
    Sinks (a ++ b) (xs ++ ys) (specs ++ specs') where
  diagram := D.diagram.tensor D'.diagram
  labeling := D.labeling.tensor D'.labeling
  no_inner := by
    let := D.no_inner
    let := D'.no_inner
    change IsEmpty (D.diagram.Inner ⊕ D'.diagram.Inner)
    infer_instance
  legal_iff u := by
    rw [Labeling.legal_tensor, D.legal_iff, D'.legal_iff]
    simp only [List.forall_mem_append]

/-- The empty sink bundle. -/
@[expose] def nil : Sinks [] ([] : List Label) [] where
  diagram := .id []
  labeling := .id [] [] rfl
  no_inner := ⟨Empty.elim⟩
  legal_iff _ := by
    constructor
    · intro _ v hv
      exact (List.not_mem_nil hv).elim
    · intro _ v
      exact v.elim

/-- A cap requires at least one of its two incidences to point upward. -/
@[expose] def capSpec (c : Color) (p q : Label) : Vertex Label :=
  ⟨[⟨⟨p, true⟩, c.weight⟩, ⟨⟨q, true⟩, c.weight⟩], c.weight⟩

/-- The two labels on a cap. -/
@[expose] def capLabels (c : Color) (p q : Label) : Labeling (gen (Cell.cap c)) [p, q] [] where
  label := Sum.elim (fun i => if i.val = 0 then p else q) Fin.elim0
  top_eq := rfl
  bot_eq := rfl

/-- Draw the cap joining two equally colored incidence labels. -/
@[expose] def cap (c : Color) (p q : Label) : Sinks [c, c] [p, q] [capSpec c p q] where
  diagram := gen (Cell.cap c)
  labeling := capLabels c p q
  no_inner := ⟨Fin.elim0⟩
  legal_iff u := by
    let f : Fin 2 ⊕ Fin 0 → Label :=
      Sum.elim (fun i => if i.val = 0 then p else q) Fin.elim0
    refine (genLegal_iff (I := Cell.interp) (Cell.cap c) (u ∘ f)).symm.trans ?_
    change (∀ v ∈ [genVertex [c, c] [] c.weight], v.Sat (u ∘ f)) ↔ _
    simp only [List.forall_mem_singleton]
    exact (Vertex.sat_map f (genVertex [c, c] [] c.weight) u).symm.trans Iff.rfl

/-- Pair the two endpoint labels of every edge in the listed order. -/
@[expose] def pairLabels {E : Type*} (es : List E) : List (Port E) :=
  es.flatMap (fun e => [⟨e, false⟩, ⟨e, true⟩])

/-- The cap constraints, in edge order. -/
@[expose] def capSpecs {E : Type*} (color : E → Color) (es : List E) : List (Vertex (Port E)) :=
  es.map (fun e => capSpec (color e) ⟨e, false⟩ ⟨e, true⟩)

/-- The sink boundary colors in edge-pair order. -/
@[expose] def pairColors {E : Type*} (color : E → Color) : List E → List Color
  | [] => []
  | e :: es => [color e, color e] ++ pairColors color es

/-- Sink boundary colors are the colors of the ordered endpoint pairs. -/
theorem pairColors_eq {E : Type*} (color : E → Color) (es : List E) :
    pairColors color es = (pairLabels es).map (fun p => color p.edge) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [pairColors, pairLabels, List.flatMap_cons, List.map_append,
      List.map_cons, List.map_nil, ih]

/-- Cap all pairs of edge incidences. -/
@[expose] def caps {E : Type*} (color : E → Color) : (es : List E) →
    Sinks (pairColors color es) (pairLabels es) (capSpecs color es)
  | [] => nil
  | e :: es => (cap (color e) (Port.mk e false) (Port.mk e true)).tensor (caps color es)

end Sinks

end Cslib.Complexity.NCL.Planar.Embedding
