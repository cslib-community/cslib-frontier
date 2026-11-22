/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.FrozenReference
public import Mathlib.Topology.Connected.PathConnected
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Certificate
import CslibFrontier.Foundations.Geometry.SeparatedStarObstacles
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Paths avoiding the frozen reference spokes

The protected set consists of the original centers and the literal supports of all frozen
reference spokes. The existing strip bounds separate the stars horizontally. Compactness
gives common vertical bounds, so the complement is path connected.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Polygonal

private noncomputable def frozenStar (I : FixedRotationInput) (v : ℕ) : Set ℂ :=
  {referencePoint I v} ∪
    ⋃ d : {d : Dart I.graph // d.vertex = v ∧ (I.orders.getD d.vertex none).isSome},
      ((referenceDrawing I).route (subdivisionDart I d.val).1).support

/-- The original centers, including isolated vertices, and the full supports of the
frozen reference spokes. Free subdivision vertices are not added as obstacles. -/
noncomputable def frozenReferenceObstacle (I : FixedRotationInput) : Set ℂ :=
  ⋃ v : Fin I.graph.vertices.length, frozenStar I v.val

private theorem original_mem_iff_lt {I : FixedRotationInput} (hI : Valid I) (v : ℕ) :
    v ∈ I.graph.vertices ↔ v < I.graph.vertices.length :=
  (iff_of_eq (congrArg (fun vs : List ℕ => v ∈ vs) hI.1)).trans List.mem_range

/-- Membership in the frozen obstacle is membership in an original center or in an
indexed frozen spoke. Both orientations use their actual stored route supports. -/
theorem mem_frozenReferenceObstacle_iff {I : FixedRotationInput} (hI : Valid I) {z : ℂ} :
    z ∈ frozenReferenceObstacle I ↔
      (∃ v ∈ I.graph.vertices, z = referencePoint I v) ∨
      ∃ d : Dart I.graph, (I.orders.getD d.vertex none).isSome ∧
        z ∈ ((referenceDrawing I).route (subdivisionDart I d).1).support := by
  rw [frozenReferenceObstacle]
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hz
    rcases hv with hv | hv
    · exact Or.inl ⟨v.val, (original_mem_iff_lt hI v.val).mpr v.isLt, hv⟩
    · obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hv
      exact Or.inr ⟨d.val, d.property.2, hd⟩
  · rintro (⟨v, hv, h⟩ | ⟨d, hd, h⟩)
    · exact Set.mem_iUnion.mpr ⟨⟨v, (original_mem_iff_lt hI v).mp hv⟩, Or.inl h⟩
    · have hv := RotationSystem.vertex_mem
        (fun v hv => (original_mem_iff_lt hI v).mpr (hI.2.1 v hv)) d
      refine Set.mem_iUnion.mpr ⟨⟨d.vertex, (original_mem_iff_lt hI d.vertex).mp hv⟩, Or.inr ?_⟩
      exact Set.mem_iUnion.mpr ⟨⟨d, rfl, hd⟩, h⟩

private theorem spoke_support (I : FixedRotationInput) (d : Dart I.graph) :
    ((referenceDrawing I).route (subdivisionDart I d).1).support =
      segment ℝ (referencePoint I d.vertex)
        (referencePoint I (I.graph.vertices.length + d.index)) := by
  let e := (subdivisionDart I d).1
  have hcenter : Dart.vertex (G := subdivisionGraph I) (e, d.2) = d.vertex :=
    (subdivisionDart_endpoints I d).1
  have hleaf : Dart.vertex (G := subdivisionGraph I) (e, !d.2) =
      I.graph.vertices.length + d.index := (subdivisionDart_endpoints I d).2
  change (Route.line (referencePoint I (Dart.vertex (G := subdivisionGraph I) (e, false)))
    (referencePoint I (Dart.vertex (G := subdivisionGraph I) (e, true)))).support = _
  rw [Route.support_line, ← hcenter, ← hleaf]
  cases hb : d.2
  · rfl
  · exact segment_symm ℝ _ _

/-- The protected reference set is compact, being a finite union of points and closed
segments. -/
theorem frozenReferenceObstacle_isCompact (I : FixedRotationInput) :
    IsCompact (frozenReferenceObstacle I) := by
  unfold frozenReferenceObstacle
  apply isCompact_iUnion
  intro v
  unfold frozenStar
  apply isCompact_singleton.union
  apply isCompact_iUnion
  intro d
  rw [spoke_support, segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

private theorem frozenStar_starConvex (I : FixedRotationInput) (v : ℕ) :
    StarConvex ℝ (referencePoint I v) (frozenStar I v) := by
  unfold frozenStar
  apply (starConvex_singleton _).union
  apply starConvex_iUnion
  intro d
  rw [spoke_support, d.property.1]
  exact (convex_segment _ _).starConvex (left_mem_segment ℝ _ _)

/-- Any two points off the original centers and frozen reference spokes can be joined
by a path avoiding that entire protected set. -/
theorem frozenReferenceObstacle_compl_isPathConnected {I : FixedRotationInput}
    (hI : Valid I) : IsPathConnected (frozenReferenceObstacle I)ᶜ := by
  obtain ⟨right, hright, hsep, hstrip⟩ := exists_frozen_reference_strips hI
  obtain ⟨R, _, hbound⟩ := (frozenReferenceObstacle_isCompact I).isBounded.subset_ball_lt 0 0
  let V := Fin I.graph.vertices.length
  have hmem (v : V) : v.val ∈ I.graph.vertices := (original_mem_iff_lt hI v.val).mpr v.isLt
  have hcenter (v : V) : referencePoint I v.val ∈ frozenStar I v.val := Or.inl rfl
  refine isPathConnected_compl_iUnion_starConvex_of_separated_rectangles
    (fun v : V => frozenStar I v.val) (fun v => referencePoint I v.val)
    (fun v => (referencePoint I v.val).re - 1 / 8) (fun v => right v.val) (-R) R
    (fun v => frozenStar_starConvex I v.val) hcenter ?_ ?_ (x := -1) ?_
  · intro v z hz
    have hOb : z ∈ frozenReferenceObstacle I := by
      unfold frozenReferenceObstacle
      exact Set.mem_iUnion.mpr ⟨v, hz⟩
    have hnorm : ‖z‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hbound hOb
    refine ⟨?_, abs_lt.mp ((Complex.abs_im_le_norm z).trans_lt hnorm)⟩
    rcases hz with hz | hz
    · have he : z = referencePoint I v.val := hz
      rw [he]
      exact ⟨by linarith, hright _ (hmem v)⟩
    · obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hz
      have h := hstrip d.val d.property.2 z hd
      rw [d.property.1] at h
      exact ⟨by linarith only [h.1], h.2⟩
  · intro u v hne
    apply Set.disjoint_left.mpr
    intro x hu hv
    have huve : u.val ≠ v.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne huve with h | h
    · have hs := hsep _ (hmem u) _ (hmem v) h
      linarith only [hs, hu.2, hv.1]
    · have hs := hsep _ (hmem v) _ (hmem u) h
      linarith only [hs, hv.2, hu.1]
  · intro v hv
    have hnonneg : 0 ≤ (referencePoint I v.val).re := by
      change (0 : ℝ) ≤ ((referenceOrder I).idxOf v.val : ℝ)
      exact Nat.cast_nonneg _
    linarith only [hnonneg, hv.1]

end Cslib.Complexity.Graph.RotationRecognition
