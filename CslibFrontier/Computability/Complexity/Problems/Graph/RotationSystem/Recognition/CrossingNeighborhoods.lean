/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceCrossings
public import CslibFrontier.Foundations.Geometry.Polygonal.Neighborhood
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import CslibFrontier.Foundations.Geometry.Polygonal.RouteInterior
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
# Disjoint neighborhoods of actual reference crossings

The actual common strict-interior points of distinct indexed reference routes form a
finite set. They admit positive radii whose closed balls are pairwise disjoint and avoid
every declared vertex, including isolates, and every route support not containing the
center. All stored edge occurrences are retained. Vertices enter the existing finite
segment-separation argument as degenerate segments.

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

private def crossingPoints (I : FixedRotationInput) : Set ℂ :=
  {z | ∃ e f : Fin (subdivisionGraph I).edges.length, e ≠ f ∧
    z ∈ openSegment ℝ ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish ∧
    z ∈ openSegment ℝ ((referenceDrawing I).route f).start
      ((referenceDrawing I).route f).finish}

private theorem crossingPoints_finite {I : FixedRotationInput} (hI : Valid I) :
    (crossingPoints I).Finite := by
  let E := Fin (subdivisionGraph I).edges.length
  let P := {p : E × E // p.1 ≠ p.2}
  let S := fun p : P =>
    openSegment ℝ ((referenceDrawing I).route p.val.1).start
      ((referenceDrawing I).route p.val.1).finish ∩
    openSegment ℝ ((referenceDrawing I).route p.val.2).start
      ((referenceDrawing I).route p.val.2).finish
  have hS : ∀ p, (S p).Finite := fun p =>
    (referenceDrawing_open_inter_subsingleton hI p.val.1 p.val.2 p.property).finite
  have hC : crossingPoints I = ⋃ p : P, S p := by
    ext z
    constructor
    · rintro ⟨e, f, hef, he, hf⟩
      exact Set.mem_iUnion.mpr ⟨⟨(e, f), hef⟩, he, hf⟩
    · intro hz
      obtain ⟨p, he, hf⟩ := Set.mem_iUnion.mp hz
      exact ⟨p.val.1, p.val.2, p.property, he, hf⟩
  rw [hC]
  exact Set.finite_iUnion hS

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

private theorem exists_crossing_ball {I : FixedRotationInput} (hI : Valid I)
    {z : ℂ} (hz : z ∈ crossingPoints I) :
    ∃ ε > 0,
      (∀ v ∈ (subdivisionGraph I).vertices,
        (referenceDrawing I).vertex v ∉ Metric.ball z ε) ∧
      (∀ e : Fin (subdivisionGraph I).edges.length,
        z ∉ ((referenceDrawing I).route e).support →
        Disjoint (Metric.ball z ε) ((referenceDrawing I).route e).support) := by
  let H := subdivisionGraph I
  let D := referenceDrawing I
  let J := Sum (Fin H.edges.length) (Fin H.vertices.length)
  let a : J → ℂ := Sum.elim (fun e => (D.route e).start) (fun v => D.vertex H.vertices[v])
  let b : J → ℂ := Sum.elim (fun e => (D.route e).finish) (fun v => D.vertex H.vertices[v])
  obtain ⟨ε, hε, hsep⟩ := exists_ball_only_incident_segments a b z
  refine ⟨ε, hε, ?_, ?_⟩
  · intro v hv hw
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hv
    change H.vertices[j.val] = v at hj
    have hseg : D.vertex v ∈ segment ℝ (a (Sum.inr j)) (b (Sum.inr j)) := by
      simp [a, b, hj]
    have hzseg := hsep (Sum.inr j) (D.vertex v) hw hseg
    have hzv : z = D.vertex v := by simpa [a, b, hj] using hzseg
    exact referenceDrawing_crossing_ne_vertex hI hz hv hzv
  · intro e hze
    apply Set.disjoint_left.mpr
    intro w hw hwe
    apply hze
    have hwseg : w ∈ segment ℝ (a (Sum.inl e)) (b (Sum.inl e)) :=
      (Route.support_line (referencePoint I (Dart.vertex (e, false)))
        (referencePoint I (Dart.vertex (e, true)))) ▸ hwe
    have hzseg := hsep (Sum.inl e) w hw hwseg
    exact (Route.support_line (referencePoint I (Dart.vertex (e, false)))
        (referencePoint I (Dart.vertex (e, true)))).symm ▸ hzseg

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
  classical
  change (crossingPoints I).Finite ∧ _
  have hC := crossingPoints_finite hI
  obtain ⟨U, hU, hdisj⟩ := hC.t2_separation
  have hopen : ∀ z : crossingPoints I, ∃ δ > 0, Metric.ball z.val δ ⊆ U z.val := by
    intro z
    exact Metric.isOpen_iff.mp (hU z.val).2 z.val (hU z.val).1
  choose δ hδ hsub using hopen
  have hlocal := fun z : crossingPoints I => exists_crossing_ball hI z.property
  choose η hη hvert hsupp using hlocal
  let ρ : ℂ → ℝ := fun z =>
    if hz : z ∈ crossingPoints I then min (δ ⟨z, hz⟩) (η ⟨z, hz⟩) / 2 else 1
  have hbounds (z : ℂ) (hz : z ∈ crossingPoints I) :
      0 < ρ z ∧ ρ z < δ ⟨z, hz⟩ ∧ ρ z < η ⟨z, hz⟩ := by
    have hρ : ρ z = min (δ ⟨z, hz⟩) (η ⟨z, hz⟩) / 2 := by
      simp only [ρ, dite_eq_left hz]
    rw [hρ]
    have hp := lt_min (hδ ⟨z, hz⟩) (hη ⟨z, hz⟩)
    have hleft := min_le_left (δ ⟨z, hz⟩) (η ⟨z, hz⟩)
    have hright := min_le_right (δ ⟨z, hz⟩) (η ⟨z, hz⟩)
    refine ⟨by linarith, by linarith, by linarith⟩
  have hclosed (z : ℂ) (hz : z ∈ crossingPoints I) :
      Metric.closedBall z (ρ z) ⊆ U z :=
    (Metric.closedBall_subset_ball (hbounds z hz).2.1).trans (hsub ⟨z, hz⟩)
  refine ⟨hC, ρ, fun z hz => (hbounds z hz).1, ?_, ?_⟩
  · exact hdisj.mono_on (fun {z} hz => hclosed z hz)
  · intro z hz
    have hshrink : Metric.closedBall z (ρ z) ⊆ Metric.ball z (η ⟨z, hz⟩) :=
      Metric.closedBall_subset_ball (hbounds z hz).2.2
    exact ⟨fun v hv hw => hvert ⟨z, hz⟩ v hv (hshrink hw),
      fun e hze => (hsupp ⟨z, hz⟩ e hze).mono_left hshrink⟩

end Cslib.Complexity.Graph.RotationRecognition
