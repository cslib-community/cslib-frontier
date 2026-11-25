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
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Certificate
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

/-- Every incidence of a valid input's twice subdivision has a declared vertex. -/
theorem subdivisionGraph_endpoints_declared {I : FixedRotationInput} (hI : Valid I) :
    ∀ v ∈ (subdivisionGraph I).incidenceVertices, v ∈ (subdivisionGraph I).vertices := by
  intro v hv
  obtain ⟨_, he, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
  rcases List.mem_cons.mp hv with rfl | hv
  · exact List.mem_range.mpr (boundedEndpoints_frame hI s hs).1
  · exact List.mem_singleton.mp hv ▸ List.mem_range.mpr (boundedEndpoints_frame hI s hs).2

/-- Both ends of an actual indexed subdivision edge occur in the reference order and
are distinct. The certificate includes original loops after twice subdivision. -/
theorem subdivision_endpoint_spec {I : FixedRotationInput} (hI : Valid I)
    (e : Fin (subdivisionGraph I).edges.length) :
    (∀ b, Dart.vertex (e, b) ∈ referenceOrder I) ∧
      Dart.vertex (e, false) ≠ Dart.vertex (e, true) := by
  refine ⟨fun b => ((referenceOrder_enumerates hI).2 _).mpr
    (RotationSystem.vertex_mem (subdivisionGraph_endpoints_declared hI) (e, b)), ?_⟩
  obtain ⟨s, hs, hse⟩ := List.mem_map.mp (List.getElem_mem e.isLt)
  change ((subdivisionGraph I).edges.getD e.val (0, 0)).1 ≠
    ((subdivisionGraph I).edges.getD e.val (0, 0)).2
  rw [List.getD_eq_getElem _ _ e.isLt, ← hse]
  exact subdivide_source_ne_target hI hs

/-- All declared subdivision points, including isolated points, have distinct coordinates. -/
theorem referenceDrawing_vertices_injective {I : FixedRotationInput} (hI : Valid I) :
    Set.InjOn (referenceDrawing I).vertex {v | v ∈ (subdivisionGraph I).vertices} :=
  fun u hu _ _ h => rankPoint_inj (((referenceOrder_enumerates hI).2 u).mpr hu) h

/-- Each indexed subdivision occurrence has a nondegenerate, simple one-segment route. -/
theorem referenceDrawing_simple {I : FixedRotationInput} (hI : Valid I)
    (e : Fin (subdivisionGraph I).edges.length) : ((referenceDrawing I).route e).IsSimple :=
  Route.isSimple_line fun h =>
    (subdivision_endpoint_spec hI e).2 (rankPoint_inj ((subdivision_endpoint_spec hI e).1 false) h)

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
  have hline : AffineMap.lineMap (p a) (p b) t = p v :=
    (Route.eval_line (p a) (p b) i t).symm.trans heq
  have hm : p v ∈ segment ℝ (p a) (p b) := hline ▸ lineMap_mem_segment ℝ (p a) (p b) ht
  have hmem := ((referenceOrder_enumerates hI).2 v).mpr hv
  rcases (parabolaPoint_mem_segment_iff ((referenceOrder I).idxOf a : ℝ)
    ((referenceOrder I).idxOf b : ℝ) ((referenceOrder I).idxOf v : ℝ)).mp hm with h | h
  · have hv' := rankPoint_inj hmem (congrArg parabolaPoint h)
    exact ⟨false, (Route.atEnd_line_iff _ _ i t false).mpr
      ((AffineMap.lineMap_eq_left_iff.mp (hv' ▸ hline)).resolve_left hp), hv'.symm⟩
  · have hv' := rankPoint_inj hmem (congrArg parabolaPoint h)
    exact ⟨true, (Route.atEnd_line_iff _ _ i t true).mpr
      ((AffineMap.lineMap_eq_right_iff.mp (hv' ▸ hline)).resolve_left hp), hv'.symm⟩

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
      (order.idxOf u : ℝ) ≠ (order.idxOf v : ℝ) :=
    fun h => hne ((List.idxOf_inj hu).mp (Nat.cast_injective h))
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
  rw [Dart.edge_eq_vertices e, Dart.edge_eq_vertices f] at hind ⊢
  have he := subdivision_endpoint_spec hI e
  have hf := subdivision_endpoint_spec hI f
  exact crossing_rankChord_iff ⟨he.1 false, he.1 true⟩ ⟨hf.1 false, hf.1 true⟩ he.2 hf.2 hind

end Cslib.Complexity.Graph.RotationRecognition
