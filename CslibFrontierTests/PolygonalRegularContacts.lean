/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: local-only (ordinary-import regular-contact regression)

import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RegularContacts
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star
import CslibFrontier.Foundations.Geometry.Polygonal.RouteInterior
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.privateModule false

/-! The two spokes of an embedded star give a regular contact at an actual shared endpoint. -/

namespace CslibFrontierTests.PolygonalRegularContacts

open Cslib.Complexity.Graph Cslib.Polygonal
open Cslib.Complexity.Graph.PolygonalDrawing Cslib.Complexity.Graph.RotationSystem

private abbrev D : PolygonalDrawing (starGraph 2) := PolygonalDrawing.star 2

private theorem edge_injective : Function.Injective (fun i : D.SegmentIndex => i.1) := by
  rintro ⟨e, i⟩ ⟨f, j⟩ he
  change e = f at he
  subst f
  have hi : i = j := Subsingleton.elim (α := Fin 1) i j
  rw [hi]

private theorem segment_end (i : D.SegmentIndex) (b : Bool) :
    (if b then D.segmentFinish i else D.segmentStart i) = D.vertex (Dart.vertex (i.1, b)) := by
  rcases i with ⟨e, i⟩
  have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  subst i
  cases b
  · exact D.endpoint_eq e false
  · exact D.endpoint_eq e true

private theorem endpoints_declared (e : Fin (starGraph 2).edges.length) (b : Bool) :
    Dart.vertex (G := starGraph 2) (e, b) ∈ (starGraph 2).vertices :=
  vertex_mem (starGraph_endpoints_declared 2) (e, b)

private theorem vertex_avoids (i : D.SegmentIndex) (b : Bool) (j : D.SegmentIndex) :
    (if b then D.segmentFinish i else D.segmentStart i) ∉
      openSegment ℝ (D.segmentStart j) (D.segmentFinish j) := by
  rw [segment_end]
  exact D.vertex_notMem_openSegment_of_vertex_contacts _
    (fun e k t ht => (star_isEmbedding 2).vertex_contacts e k t ht _ (endpoints_declared _ _)) j

private theorem open_disjoint (i j : D.SegmentIndex) (hij : i ≠ j) {z : ℂ}
    (hi : z ∈ openSegment ℝ (D.segmentStart i) (D.segmentFinish i)) :
    z ∉ openSegment ℝ (D.segmentStart j) (D.segmentFinish j) := by
  intro hj
  rw [openSegment_eq_image_lineMap] at hi hj
  obtain ⟨s, hs, hsz⟩ := hi
  obtain ⟨t, ht, htz⟩ := hj
  obtain ⟨b, _, he, _, _⟩ := (star_isEmbedding 2).edge_contacts i.1 j.1 (edge_injective.ne hij)
    i.2 j.2 s t ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩ (hsz.trans htz.symm)
  exact (D.route i.1).not_atEnd_of_mem_Ioo i.2 hs b he

private theorem regular : D.HasRegularContacts where
  points_injective e := by
    intro i j h
    change Fin 2 at i j
    fin_cases i <;> fin_cases j
    · rfl
    · change (⟨(e.val : ℝ) + 1, 1⟩ : ℂ) = 0 at h
      have hi := congrArg Complex.im h
      norm_num at hi
    · change (0 : ℂ) = ⟨(e.val : ℝ) + 1, 1⟩ at h
      have hi := congrArg Complex.im h
      norm_num at hi
    · rfl
  vertex_contacts := (star_isEmbedding 2).vertex_contacts
  endpoints_avoid_interiors i j := ⟨vertex_avoids i false j, vertex_avoids i true j⟩
  lines_ne_at_intersections i j hij _ hi hj := (open_disjoint i j hij hi hj).elim
  no_open_triple f _ h := open_disjoint (f 0) (f 1) (f.injective.ne (by decide)) (h 0) (h 1)
  shared_ends_are_vertices := by
    intro i j hij s t hs ht he
    have htimes : ({0, 1} : Set ℝ) ⊆ Set.Icc 0 1 :=
      Set.pair_subset_iff.mpr ⟨Set.left_mem_Icc.mpr zero_le_one, Set.right_mem_Icc.mpr zero_le_one⟩
    obtain ⟨b, _, hb, _, _⟩ := (star_isEmbedding 2).edge_contacts i.1 j.1 hij
      i.2 j.2 s t (htimes hs) (htimes ht) he
    exact ⟨Dart.vertex (i.1, b), endpoints_declared _ _,
      (((D.route i.1).at_eq_endpoint i.2 (htimes hs) b hb).trans (D.endpoint_eq i.1 b)).symm⟩

private abbrev leftSpoke : D.SegmentIndex := ⟨⟨0, by decide⟩, (0 : Fin 1)⟩
private abbrev rightSpoke : D.SegmentIndex := ⟨⟨1, by decide⟩, (0 : Fin 1)⟩

example : ∃ b c, (D.route leftSpoke.1).AtEnd leftSpoke.2 1 b ∧
    (D.route rightSpoke.1).AtEnd rightSpoke.2 1 c ∧
    Dart.vertex (leftSpoke.1, b) = Dart.vertex (rightSpoke.1, c) := by
  have he : (D.route leftSpoke.1).eval leftSpoke.2 1 =
      (D.route rightSpoke.1).eval rightSpoke.2 1 := by
    change AffineMap.lineMap _ (0 : ℂ) (1 : ℝ) = AffineMap.lineMap _ (0 : ℂ) (1 : ℝ)
    simp only [AffineMap.lineMap_apply_one]
  rcases regular.edge_contact_cases leftSpoke rightSpoke (by decide)
      (by simp) (by simp) he with h | h
  · obtain ⟨hs, _⟩ := h
    exact (lt_irrefl _ hs.2).elim
  · exact h

end CslibFrontierTests.PolygonalRegularContacts
