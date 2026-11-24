/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: local-only (ordinary-import regular-contact regression)

import CslibFrontier.Computability.Complexity.Problems.Graph.ClosedPassages.Polygonal
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Rotation
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Subdrawing
import CslibFrontier.Computability.Complexity.Problems.Graph.CutComponent
import CslibFrontier.Foundations.Geometry.Polygonal.RouteInterior
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.privateModule false

/-! Regular contacts of a two-spoke star and parity of two triangles sharing one vertex. -/

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

private abbrev splitStar : Cslib.Complexity.Graph :=
  ⟨3 :: (starGraph 2).vertices, [(0, 3), (1, 2)]⟩

private abbrev splitLabels := Function.update (id : ℕ → ℕ) 3 2

private theorem star_even : D.EvenCrossings (fun v => v = 2) := by
  intro e f hef _
  classical
  change (Route.line ⟨(e.val : ℝ) + 1, 1⟩ 0).intersectionParity
    (Route.line ⟨(f.val : ℝ) + 1, 1⟩ 0) = false
  rw [Route.intersectionParity_line_line]
  apply decide_eq_false
  rintro ⟨z, hz, hz'⟩
  exact open_disjoint ⟨e, (0 : Fin 1)⟩ ⟨f, (0 : Fin 1)⟩
    (fun h => hef (congrArg Sigma.fst h)) hz hz'

-- Both separated copies of the star center inherit its point while retaining regularity.
example :
    ∃ (A : PolygonalDrawing (splitStar.componentGraph 3))
      (B : PolygonalDrawing (splitStar.componentGraph 2)),
      A.HasRegularContacts ∧ B.HasRegularContacts ∧ A.vertex 3 = B.vertex 2 ∧
        A.EvenCrossings ((fun v => v = 2) ∘ splitLabels) ∧
        B.EvenCrossings ((fun v => v = 2) ∘ splitLabels) := by
  let selected (d : Dart (starGraph 2)) := d = starDartEquiv 2 (0, true)
  let E : Fin (starGraph 2).edges.length ≃ Fin splitStar.edges.length := Equiv.refl _
  have hEnds (d : Dart (starGraph 2)) :
      Dart.vertex (G := splitStar) (E d.1, d.2) =
        if selected d then 3 else d.vertex := by
    exact (by decide : ∀ d : Dart (starGraph 2),
      Dart.vertex (G := splitStar) (E d.1, d.2) =
        if selected d then 3 else d.vertex) d
  have hdecl := split_darts_endpoints_declared (starGraph_endpoints_declared 2)
    3 selected E rfl hEnds
  have hback := vertex_preimage_split_darts (G := starGraph 2) (H := splitStar) 2 3
    (by decide) selected (by decide) E hEnds
  have hsep : ¬RotationCertificate.SameComponent splitStar 3 2 := by
    intro h
    have he := Dart.eq_of_sameComponent (G := splitStar) (fun d => decide (d.1 = 0))
      (by decide) (by decide) (d := (0, true)) (e := (1, true)) h
    cases he
  have restrict (root : ℕ) : ∃ A : PolygonalDrawing (splitStar.componentGraph root),
      A.HasRegularContacts ∧ A.vertex = D.vertex ∘ splitLabels ∧
        A.EvenCrossings ((fun v => v = 2) ∘ splitLabels) := by
    obtain ⟨A, hA, hroutes, hv, _, hinj⟩ := regular.exists_component_subdrawing
      E.symm.toEmbedding 3 2 (by decide) hsep hdecl (fun _ h => List.mem_cons.mp h) hback root
    let edges := (splitStar.componentEdgeEquiv root).toEmbedding.trans
      ((Function.Embedding.subtype _).trans E.symm.toEmbedding)
    have hEnds' (i : Fin (splitStar.componentGraph root).edges.length) (b : Bool) :
        Dart.vertex (G := starGraph 2) (edges i, b) = splitLabels (Dart.vertex (i, b)) := by
      rw [splitStar.vertex_componentEdgeEquiv root i b]
      exact hback _ _
    exact ⟨A, hA, hv, star_even.of_route_restriction edges splitLabels hEnds'
      (splitStar.componentGraph_endpoints_declared root hdecl) hinj hroutes⟩
  obtain ⟨A, hA, hvA, heA⟩ := restrict 3
  obtain ⟨B, hB, hvB, heB⟩ := restrict 2
  exact ⟨A, B, hA, hB, by rw [hvA, hvB]; rfl, heA, heB⟩

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

private def emptyPassages : ClosedPassages (starGraph 2) (fun _ => false) := by
  letI : IsEmpty {d : Dart (starGraph 2) // (false : Bool) = true} :=
    ⟨fun d => Bool.noConfusion d.property⟩
  exact ⟨0, Equiv.equivOfIsEmpty _ _, fun i => Fin.elim0 i⟩

-- The result is usable with empty support even when the drawing itself has two incident edges.
example : (star_isEmbedding 2).rotation.intersectionParity emptyPassages emptyPassages = false := by
  let hD := star_isEmbedding 2
  rw [emptyPassages.intersectionParity_eq_sum_route_intersectionParity emptyPassages
    hD.realizes_rotation regular hD.simple hD.vertices_injective
    (vertex_mem (starGraph_endpoints_declared 2)) (fun _ h _ => Bool.noConfusion h)]
  simp [← Bool.zero_eq_false]

private abbrev bowtie : Cslib.Complexity.Graph :=
  ⟨[0, 1, 2, 3, 4], [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)]⟩

private abbrev leftSupport (e : Fin bowtie.edges.length) : Bool := decide (e.val < 3)
private abbrev rightSupport (e : Fin bowtie.edges.length) : Bool := decide (3 ≤ e.val)

private def leftEdges : Fin 3 ≃ {e : Fin bowtie.edges.length // leftSupport e = true} where
  toFun i := ⟨⟨i.val, i.isLt.trans (by decide)⟩, decide_eq_true i.isLt⟩
  invFun e := ⟨e.val.val, of_decide_eq_true e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def rightEdges : Fin 3 ≃ {e : Fin bowtie.edges.length // rightSupport e = true} where
  toFun i := ⟨⟨i.val + 3, by have := i.isLt; change i.val + 3 < 6; omega⟩,
    decide_eq_true (Nat.le_add_left 3 i.val)⟩
  invFun e := ⟨e.val.val - 3, by have h : e.val.val < 6 := e.val.isLt; omega⟩
  left_inv i := Fin.ext (Nat.add_sub_cancel i.val 3)
  right_inv e := by
    have h : 3 ≤ e.val.val := of_decide_eq_true e.property
    exact Subtype.ext (Fin.ext (Nat.sub_add_cancel h))

private def leftTriangle : ClosedPassages bowtie leftSupport :=
  ClosedPassages.ofCyclicEdges leftEdges (fun _ => false) (by decide)

private def rightTriangle : ClosedPassages bowtie rightSupport :=
  ClosedPassages.ofCyclicEdges rightEdges (fun _ => false) (by decide)

private abbrev leftShared : Fin leftTriangle.count := ⟨0, by decide⟩
private abbrev rightShared : Fin rightTriangle.count := ⟨0, by decide⟩

-- Each triangle gives a nonempty system. Their passages at vertex zero are their only meeting.
example : 0 < leftTriangle.count ∧ 0 < rightTriangle.count ∧
    (leftTriangle.dart leftShared false).vertex = (rightTriangle.dart rightShared false).vertex :=
  by decide

open scoped BigOperators in
example {A : PolygonalDrawing bowtie} {r : RotationSystem bowtie}
    (hr : A.Realizes r) (hregular : A.HasRegularContacts)
    (hsimple : ∀ e, (A.route e).IsSimple)
    (hvertices : Set.InjOn A.vertex {v | v ∈ bowtie.vertices})
    (heven : ∀ e f, leftSupport e = true → rightSupport f = true →
      (A.route e).intersectionParity (A.route f) = false) :
    (r.intersectionParity leftTriangle rightTriangle =
      ∑ f, rightSupport f * ∑ e, leftSupport e * (A.route e).intersectionParity (A.route f)) ∧
    ¬r.Alternates (leftTriangle.dart leftShared false) (leftTriangle.dart leftShared true)
      (rightTriangle.dart rightShared false) (rightTriangle.dart rightShared true) := by
  have hdeclared : ∀ d : Dart bowtie, d.vertex ∈ bowtie.vertices := by decide
  have hdisjoint : ∀ e, leftSupport e = true → rightSupport e = true → False := by decide
  exact ⟨leftTriangle.intersectionParity_eq_sum_route_intersectionParity rightTriangle
      hr hregular hsimple hvertices hdeclared hdisjoint,
    leftTriangle.not_alternates_of_unique_shared_passages rightTriangle
      hr hregular hsimple hvertices hdeclared hdisjoint heven leftShared rightShared (by decide)⟩

end CslibFrontierTests.PolygonalRegularContacts
