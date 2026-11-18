/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Frame
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import CslibFrontier.Foundations.Geometry.Polygonal.Segment
public import CslibFrontier.Foundations.Geometry.Polygonal.ParabolaChord
import CslibFrontier.Foundations.Geometry.Polygonal.LineEnds
import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Actual parabolic reference drawings for frozen parity queries

Every vertex of the twice-subdivided graph is placed at its reference rank on `(x,x²)`.
Every indexed segment occurrence is its own one-segment polygonal route. Valid input gives
simple routes, distinct declared points and no visits to unrelated declared vertices.
For independent pairs the existing `crossing` bit is true precisely when their actual open
segments have a unique common point. Membership in the enumerated reference order is used
before every rank-injectivity argument; no absent-name fallback is used.

Crossings between independent segments are intentional, so this construction is not an
`IsEmbedding`. The coordinate proof is original reference geometry, not Hanani–Tutte.
Clockwise frozen-star order, triple-crossing perturbations, frozen placement, move realization
and the parity-query feasibility criterion remain separate obligations.

## Main definitions

* `Cslib.Complexity.Graph.RotationRecognition.referencePoint`: the actual ranked vertex point.
* `Cslib.Complexity.Graph.RotationRecognition.referenceDrawing`: indexed straight-line routes.

## Main results

* `Cslib.Complexity.Graph.RotationRecognition.subdivision_endpoint_spec`: actual endpoint
  membership and nonloop certificate for every indexed subdivision edge.
* `Cslib.Complexity.Graph.RotationRecognition.subdivide_source_ne_target`: all three segments
  of each original occurrence are nonloops, including when the original occurrence is a loop.
* `Cslib.Complexity.Graph.RotationRecognition.referenceDrawing_simple`: each actual route is simple.
* `Cslib.Complexity.Graph.RotationRecognition.referenceDrawing_vertex_contacts`: every declared
  point on a route occurs at its corresponding endpoint parameter.
* `Cslib.Complexity.Graph.RotationRecognition.referenceDrawing_crossing_iff`: exact pairwise
  geometric meaning of the existing rank crossing bit.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Polygonal

/-- Place a raw vertex name at its reference-order rank on the real parabola. Geometric
properties below use valid inputs, hence membership in the reference order, before reading ranks. -/
@[expose] def referencePoint (I : FixedRotationInput) (v : ℕ) : ℂ :=
  parabolaPoint ((referenceOrder I).idxOf v : ℝ)

/-- One straight route per actual subdivision edge occurrence, preserving its end orientation. -/
@[expose] def referenceDrawing (I : FixedRotationInput) :
    PolygonalDrawing (subdivisionGraph I) where
  vertex := referencePoint I
  route := fun e => Route.line
    (referencePoint I (Dart.vertex (e, false))) (referencePoint I (Dart.vertex (e, true)))
  endpoint_eq := by intro e b; cases b <;> rfl

private theorem rankPoint_inj {order : List ℕ} {u v : ℕ} (hu : u ∈ order)
    (h : parabolaPoint (order.idxOf u : ℝ) = parabolaPoint (order.idxOf v : ℝ)) : u = v :=
  (List.idxOf_inj hu).mp (Nat.cast_injective (parabolaPoint_injective h))

/-- Twice subdivision removes original loops by giving every occurrence two fresh points. -/
theorem subdivide_source_ne_target {I : FixedRotationInput} (hI : Valid I)
    {s : Segment} (hs : s ∈ subdivide I) : s.source ≠ s.target := by
  obtain ⟨entry, he, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp he)
  have hb := hI.edge_endpoints_lt (hv ▸ List.getElem_mem hi)
  change s ∈ [((entry.1.1, I.graph.vertices.length + 2 * entry.2), _),
    ((I.graph.vertices.length + 2 * entry.2, I.graph.vertices.length + 2 * entry.2 + 1), false),
    ((I.graph.vertices.length + 2 * entry.2 + 1, entry.1.2), _)] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;>
    dsimp only [Segment.source, Segment.target, Segment.endpoints] <;> omega

/-- Both ends of an actual indexed subdivision edge occur in the reference order and
are distinct. The certificate includes original loops after twice subdivision. -/
theorem subdivision_endpoint_spec {I : FixedRotationInput} (hI : Valid I)
    (e : Fin (subdivisionGraph I).edges.length) :
    (∀ b, Dart.vertex (e, b) ∈ referenceOrder I) ∧
      Dart.vertex (e, false) ≠ Dart.vertex (e, true) := by
  have hclosed : ∀ edge ∈ (subdivisionGraph I).edges,
      edge.1 ∈ (subdivisionGraph I).vertices ∧ edge.2 ∈ (subdivisionGraph I).vertices := by
    intro edge he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
    have hb := boundedEndpoints_frame hI s hs
    exact ⟨List.mem_range.mpr hb.1, List.mem_range.mpr hb.2⟩
  refine ⟨fun b => ((referenceOrder_enumerates hI).2 _).mpr
    ((subdivisionGraph I).edgeEndpoint_mem hclosed e.isLt b), ?_⟩
  have he : (subdivisionGraph I).edges[e] ∈ (subdivisionGraph I).edges :=
    List.getElem_mem e.isLt
  obtain ⟨s, hs, hse⟩ := List.mem_map.mp he
  have hne := subdivide_source_ne_target hI hs
  simp only [Fin.getElem_fin] at hse
  change ((subdivisionGraph I).edges.getD e.val (0, 0)).1 ≠
    ((subdivisionGraph I).edges.getD e.val (0, 0)).2
  rw [List.getD_eq_getElem _ _ e.isLt, ← hse]
  exact hne

/-- All declared subdivision points, including isolated points, have distinct coordinates. -/
theorem referenceDrawing_vertices_injective {I : FixedRotationInput} (hI : Valid I) :
    Set.InjOn (referenceDrawing I).vertex {v | v ∈ (subdivisionGraph I).vertices} := by
  intro u hu v _ h
  exact rankPoint_inj (((referenceOrder_enumerates hI).2 u).mpr hu) h

/-- Each indexed subdivision occurrence has a nondegenerate, simple one-segment route. -/
theorem referenceDrawing_simple {I : FixedRotationInput} (hI : Valid I)
    (e : Fin (subdivisionGraph I).edges.length) : ((referenceDrawing I).route e).IsSimple := by
  apply Route.isSimple_line
  intro h
  have hs := subdivision_endpoint_spec hI e
  exact hs.2 (rankPoint_inj (hs.1 false) h)

/-- An actual reference route meets a declared vertex only at that vertex's corresponding
original end parameter. This is the vertex-contact field, without claiming `IsEmbedding`. -/
theorem referenceDrawing_vertex_contacts {I : FixedRotationInput} (hI : Valid I)
    (e : Fin (subdivisionGraph I).edges.length)
    (i : Fin ((referenceDrawing I).route e).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    {v : ℕ} (hv : v ∈ (subdivisionGraph I).vertices)
    (heq : ((referenceDrawing I).route e).eval i t = (referenceDrawing I).vertex v) :
    ∃ b, ((referenceDrawing I).route e).AtEnd i t b ∧ Dart.vertex (e, b) = v := by
  let a := Dart.vertex (e, false)
  let b := Dart.vertex (e, true)
  let p := referencePoint I
  have hs := subdivision_endpoint_spec hI e
  have hp : p a ≠ p b := fun h => hs.2 (rankPoint_inj (hs.1 false) h)
  have hline : AffineMap.lineMap (p a) (p b) t = p v := by
    change (Route.line (p a) (p b)).eval i t = p v at heq
    exact (Route.eval_line (p a) (p b) i t).symm.trans heq
  have hm : p v ∈ segment ℝ (p a) (p b) :=
    hline ▸ lineMap_mem_segment ℝ (p a) (p b) ht
  have hmem := ((referenceOrder_enumerates hI).2 v).mpr hv
  have hends : v = a ∨ v = b := by
    obtain h | h := (parabolaPoint_mem_segment_iff
      ((referenceOrder I).idxOf a : ℝ) ((referenceOrder I).idxOf b : ℝ)
      ((referenceOrder I).idxOf v : ℝ)).mp hm
    · exact Or.inl (rankPoint_inj hmem (congrArg parabolaPoint h))
    · exact Or.inr (rankPoint_inj hmem (congrArg parabolaPoint h))
  rcases hends with h | h
  · have htime : t = 0 :=
      (AffineMap.lineMap_eq_left_iff.mp (by simpa only [h] using hline)).resolve_left hp
    exact ⟨false, (Route.atEnd_line_iff _ _ i t false).mpr htime, h.symm⟩
  · have htime : t = 1 :=
      (AffineMap.lineMap_eq_right_iff.mp (by simpa only [h] using hline)).resolve_left hp
    exact ⟨true, (Route.atEnd_line_iff _ _ i t true).mpr htime, h.symm⟩

private theorem crossing_rankChord_iff {order : List ℕ} {e f : ℕ × ℕ}
    (he : e.1 ∈ order ∧ e.2 ∈ order) (hf : f.1 ∈ order ∧ f.2 ∈ order)
    (he0 : e.1 ≠ e.2) (hf0 : f.1 ≠ f.2) (hind : independent e f = true) :
    crossing order e f = true ↔
      ∃! z : ℂ,
        z ∈ openSegment ℝ (parabolaPoint (order.idxOf e.1 : ℝ))
          (parabolaPoint (order.idxOf e.2 : ℝ)) ∧
        z ∈ openSegment ℝ (parabolaPoint (order.idxOf f.1 : ℝ))
          (parabolaPoint (order.idxOf f.2 : ℝ)) := by
  have rank_ne {u v : ℕ} (hu : u ∈ order) (hne : u ≠ v) :
      (order.idxOf u : ℝ) ≠ (order.idxOf v : ℝ) := by
    intro h
    exact hne ((List.idxOf_inj hu).mp (Nat.cast_injective h))
  have hfour : e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
    simpa only [independent, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hind
  have hbetween (p : ℕ × ℕ) (v : ℕ) : between order p v = true ↔
      (order.idxOf v : ℝ) ∈ Set.Ioo
        (min (order.idxOf p.1 : ℝ) (order.idxOf p.2 : ℝ))
        (max (order.idxOf p.1 : ℝ) (order.idxOf p.2 : ℝ)) := by
    simp only [between, Bool.and_eq_true, decide_eq_true_eq, Set.mem_Ioo,
      ← Nat.cast_min, ← Nat.cast_max, Nat.cast_lt]
  rw [existsUnique_parabolaChord_inter_iff (rank_ne he.1 he0) (rank_ne hf.1 hf0)
    (rank_ne he.1 hfour.1) (rank_ne he.1 hfour.2.1)
    (rank_ne he.2 hfour.2.2.1) (rank_ne he.2 hfour.2.2.2)]
  change ((between order e f.1 ^^ between order e f.2) : Prop) ↔ _
  rw [Bool.coe_xor_iff, hbetween, hbetween]

private theorem subdivision_edge_ends (I : FixedRotationInput)
    (e : Fin (subdivisionGraph I).edges.length) :
    (subdivisionGraph I).edges[e] = (Dart.vertex (e, false), Dart.vertex (e, true)) := by
  simp [Dart.vertex, Graph.edgeEndpoint]

/-- The existing rank-interleaving bit is exactly a unique actual common interior point
of the two indexed straight reference routes. Independence supplies all four cross-endpoint
inequalities; validity supplies nondegenerate segments and actual reference-order membership. -/
theorem referenceDrawing_crossing_iff {I : FixedRotationInput} (hI : Valid I)
    (e f : Fin (subdivisionGraph I).edges.length)
    (hind : independent ((subdivisionGraph I).edges[e])
      ((subdivisionGraph I).edges[f]) = true) :
    crossing (referenceOrder I) ((subdivisionGraph I).edges[e])
      ((subdivisionGraph I).edges[f]) = true ↔
        ∃! z : ℂ,
          z ∈ openSegment ℝ ((referenceDrawing I).route e).start
            ((referenceDrawing I).route e).finish ∧
          z ∈ openSegment ℝ ((referenceDrawing I).route f).start
            ((referenceDrawing I).route f).finish := by
  rw [subdivision_edge_ends I e, subdivision_edge_ends I f] at hind ⊢
  have he := subdivision_endpoint_spec hI e
  have hf := subdivision_endpoint_spec hI f
  exact crossing_rankChord_iff ⟨he.1 false, he.1 true⟩ ⟨hf.1 false, hf.1 true⟩ he.2 hf.2 hind

end Cslib.Complexity.Graph.RotationRecognition
