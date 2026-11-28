/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary clients of actual rank reference geometry)

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceDrawing
import Mathlib.Tactic.NormNum

/-! Ordinary module clients use actual affine parameters and a loop/parallel/isolate input.
The reference drawing intentionally has independent crossings; no embedding is assumed. -/

public section

namespace Cslib.Tests.RotationReferenceDrawing

open Cslib.Polygonal Cslib.Complexity.Graph Cslib.Complexity.Graph.RotationRecognition

-- The alternating pair meets at the actual point (3/2,3), with interior parameters 3/4 and 1/4.
example : (⟨3 / 2, 3⟩ : ℂ) ∈ openSegment ℝ (parabolaPoint 0) (parabolaPoint 2) ∧
    (⟨3 / 2, 3⟩ : ℂ) ∈ openSegment ℝ (parabolaPoint 1) (parabolaPoint 3) := by
  constructor
  · have h := lineMap_mem_openSegment ℝ (parabolaPoint 0) (parabolaPoint 2)
      (by norm_num : (3 / 4 : ℝ) ∈ Set.Ioo 0 1)
    have heq : AffineMap.lineMap (parabolaPoint 0) (parabolaPoint 2) (3 / 4 : ℝ) =
        (⟨3 / 2, 3⟩ : ℂ) := by
      apply Complex.ext <;>
        norm_num [parabolaPoint, AffineMap.lineMap_apply_module, Complex.real_smul]
    exact heq ▸ h
  · have h := lineMap_mem_openSegment ℝ (parabolaPoint 1) (parabolaPoint 3)
      (by norm_num : (1 / 4 : ℝ) ∈ Set.Ioo 0 1)
    have heq : AffineMap.lineMap (parabolaPoint 1) (parabolaPoint 3) (1 / 4 : ℝ) =
        (⟨3 / 2, 3⟩ : ℂ) := by
      apply Complex.ext <;>
        norm_num [parabolaPoint, AffineMap.lineMap_apply_module, Complex.real_smul]
    exact heq ▸ h

-- Nested endpoint intervals make both strict-membership bits true, rather than alternating.
example : ¬(openSegment ℝ (parabolaPoint 0) (parabolaPoint 3) ∩
    openSegment ℝ (parabolaPoint 1) (parabolaPoint 2)).Nonempty := by
  intro h
  have hnot : ¬ ∃! z : ℂ,
      z ∈ openSegment ℝ (parabolaPoint 0) (parabolaPoint 3) ∧
      z ∈ openSegment ℝ (parabolaPoint 1) (parabolaPoint 2) := by
    rw [existsUnique_parabolaChord_inter_iff (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num [Xor]
  obtain ⟨z, hz⟩ := h
  exact hnot ⟨z, hz, fun w hw =>
    parabolaChord_inter_subsingleton (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hw hz⟩

example : parabolaPoint 1 ∉ segment ℝ (parabolaPoint 0) (parabolaPoint 2) := by
  rw [parabolaPoint_mem_segment_iff]
  norm_num

/-- One original loop, two parallel occurrences and an isolated original vertex. -/
@[expose] def input : FixedRotationInput :=
  ⟨⟨[0, 1, 2], [(0, 0), (0, 1), (0, 1)]⟩, List.replicate 3 none⟩

private theorem valid_input : Valid input := validate_eq_true_iff input |>.mp (by decide +kernel)

private def firstEdge : Fin (subdivisionGraph input).edges.length := ⟨0, by decide⟩
private def crossingEdge : Fin (subdivisionGraph input).edges.length := ⟨5, by decide⟩

-- The loop occurrence becomes three nondegenerate routes, without discarding either loop end.
example : ((referenceDrawing input).route firstEdge).IsSimple :=
  referenceDrawing_simple valid_input firstEdge

-- The native rank bit for two actual independent occurrences produces a unique real crossing.
example :
    ∃! z : ℂ,
      z ∈ openSegment ℝ ((referenceDrawing input).route firstEdge).start
        ((referenceDrawing input).route firstEdge).finish ∧
      z ∈ openSegment ℝ ((referenceDrawing input).route crossingEdge).start
        ((referenceDrawing input).route crossingEdge).finish :=
  (referenceDrawing_crossing_iff valid_input firstEdge crossingEdge (by decide +kernel)).mp
    (by decide +kernel)

-- The original isolated vertex is still a distinct declared point.
example : (referenceDrawing input).vertex 2 ≠ (referenceDrawing input).vertex 0 := by
  intro h
  have he := referenceDrawing_vertices_injective valid_input
    (show 2 ∈ (subdivisionGraph input).vertices by decide)
    (show 0 ∈ (subdivisionGraph input).vertices by decide) h
  omega

-- No interior or endpoint parameter of the first route can visit that unrelated isolate.
example {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ((referenceDrawing input).route firstEdge).eval 0 t ≠ (referenceDrawing input).vertex 2 := by
  intro h
  obtain ⟨b, _, hb⟩ := referenceDrawing_vertex_contacts valid_input firstEdge 0 ht
    (by decide) h
  cases b <;>
    norm_num [firstEdge, Dart.vertex, Cslib.Complexity.Graph.edgeEndpoint,
      subdivisionGraph, subdivide, input] at hb

end Cslib.Tests.RotationReferenceDrawing
