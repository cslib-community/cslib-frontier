/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceCrossings
public import CslibFrontier.Foundations.Geometry.Polygonal.Neighborhood
import CslibFrontier.Foundations.Geometry.Polygonal.RouteInterior
import Mathlib.Data.Set.Finite.Lattice

/-!
# Disjoint neighborhoods of actual reference crossings

The actual common strict-interior points of distinct indexed reference routes form a
finite set. They admit positive radii whose closed balls are pairwise disjoint and avoid
every declared vertex, including isolates, and every route support not containing the
center. All stored edge occurrences are retained. Vertices enter the existing finite
segment-separation argument as degenerate segments.

## Main definitions

* `referenceCrossingPoints`: all actual common strict-interior points of distinct indexed routes.

## Main results

* `Cslib.Complexity.Graph.RotationRecognition.exists_reference_crossing_neighborhoods`:
  finite actual crossing set and internally chosen disjoint closed neighborhoods with
  full vertex and nonincident-support exclusion.

These neighborhoods are prerequisites for local detour insertion. Coordinate placement,
ordered route gluing, contact/parity preservation, placement and the Hanani–Tutte/query
criterion remain open under [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).
No regularization or placement provider is assumed.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Polygonal

/-- Actual common strict-interior points of distinct indexed reference routes. -/
@[expose] def referenceCrossingPoints (I : FixedRotationInput) : Set ℂ :=
  openSegmentCrossings (fun e => ((referenceDrawing I).route e).start)
    (fun e => ((referenceDrawing I).route e).finish)

/-- A strict-interior crossing of actual reference routes avoids every declared vertex. -/
theorem referenceDrawing_crossing_ne_vertex {I : FixedRotationInput} (hI : Valid I)
    {z : ℂ} (hz : ∃ e f : Fin (subdivisionGraph I).edges.length, e ≠ f ∧
      z ∈ openSegment ℝ ((referenceDrawing I).route e).start
        ((referenceDrawing I).route e).finish ∧
      z ∈ openSegment ℝ ((referenceDrawing I).route f).start
        ((referenceDrawing I).route f).finish) {v : ℕ}
    (hv : v ∈ (subdivisionGraph I).vertices) : z ≠ (referenceDrawing I).vertex v := by
  intro hzv
  obtain ⟨e, _, _, he, _⟩ := hz
  rw [openSegment_eq_image_lineMap] at he
  obtain ⟨t, ht, htz⟩ := he
  have heq : ((referenceDrawing I).route e).eval 0 t =
      (referenceDrawing I).vertex v := by
    change (Route.line _ _).eval 0 t = _
    rw [Route.eval_line]
    exact htz.trans hzv
  obtain ⟨b, hb, _⟩ := referenceDrawing_vertex_contacts hI e 0
    ⟨ht.1.le, ht.2.le⟩ hv heq
  exact (Route.not_atEnd_of_mem_Ioo _ 0 ht b) hb

/-- The actual crossing set is finite and has internally chosen pairwise-disjoint closed
neighborhoods excluding every declared vertex and every nonincident route support. -/
theorem exists_reference_crossing_neighborhoods {I : FixedRotationInput} (hI : Valid I) :
    let C : Set ℂ := {z | ∃ e f : Fin (subdivisionGraph I).edges.length, e ≠ f ∧
      z ∈ openSegment ℝ ((referenceDrawing I).route e).start
        ((referenceDrawing I).route e).finish ∧
      z ∈ openSegment ℝ ((referenceDrawing I).route f).start
        ((referenceDrawing I).route f).finish}
    C.Finite ∧ ∃ ρ : ℂ → ℝ,
      (∀ z ∈ C, 0 < ρ z) ∧
      C.PairwiseDisjoint (fun z => Metric.closedBall z (ρ z)) ∧
      (∀ z ∈ C,
        (∀ v ∈ (subdivisionGraph I).vertices,
          (referenceDrawing I).vertex v ∉ Metric.closedBall z (ρ z)) ∧
        (∀ e : Fin (subdivisionGraph I).edges.length,
          z ∉ ((referenceDrawing I).route e).support →
          Disjoint (Metric.closedBall z (ρ z)) ((referenceDrawing I).route e).support)) := by
  let D := referenceDrawing I
  let V := D.vertex '' {v | v ∈ (subdivisionGraph I).vertices}
  have hV : V.Finite := (List.finite_toSet (subdivisionGraph I).vertices).image _
  have havoid : Disjoint (referenceCrossingPoints I) V := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨v, hv, rfl⟩
    exact referenceDrawing_crossing_ne_vertex hI hz hv rfl
  obtain ⟨hC, ρ, hpos, hdisj, hlocal⟩ := exists_openSegment_crossing_neighborhoods
    (fun e => (D.route e).start) (fun e => (D.route e).finish)
    hV havoid (referenceDrawing_open_inter_subsingleton hI)
  refine ⟨hC, ρ, hpos, hdisj, fun z hz => ⟨fun v hv hw => ?_, fun e he => ?_⟩⟩
  · exact Set.disjoint_left.mp (hlocal z hz).1 hw ⟨v, hv, rfl⟩
  · have hline : (D.route e).support = segment ℝ (D.route e).start (D.route e).finish :=
      Route.support_line _ _
    rw [hline] at he ⊢
    exact (hlocal z hz).2 e he

end Cslib.Complexity.Graph.RotationRecognition
