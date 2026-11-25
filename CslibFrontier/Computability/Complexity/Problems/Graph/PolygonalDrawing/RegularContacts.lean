/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import CslibFrontier.Foundations.Geometry.Polygonal.Neighborhood
import CslibFrontier.Foundations.Geometry.FiniteLineAvoidance
import CslibFrontier.Foundations.Geometry.Polygonal.RouteInterior
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Finite.Lattice

/-!
# Regular contacts in polygonal graph drawings

Regular contacts permit transverse crossings of two open segments, with no listed
endpoint at a crossing or bend shared by different edges. The contact dichotomy
identifies the remaining intersections as shared graph endpoints.

## Main definitions and results

* `HasRegularContacts` records the local segment and vertex contact conditions.
* `HasRegularContacts.edge_contact_cases` classifies contacts between two distinct edges.
* `HasRegularContacts.open_inter_subsingleton` bounds each indexed open intersection.
* `HasRegularContacts.exists_crossing_neighborhoods` isolates all double crossings.
* `HasRegularContacts.point_notMem_other_support` excludes listed points from independent edges.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

/-- A vertex reached only at original route ends misses every open segment. -/
theorem vertex_notMem_openSegment_of_vertex_contacts {G : Graph} (D : PolygonalDrawing G) (v : ℕ)
    (hcontacts : ∀ e (i : Fin (D.route e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.route e).eval i t = D.vertex v →
        ∃ b, (D.route e).AtEnd i t b ∧ Dart.vertex (e, b) = v)
    (j : D.SegmentIndex) :
    D.vertex v ∉ openSegment ℝ (D.segmentStart j) (D.segmentFinish j) := by
  intro h
  rw [openSegment_eq_image_lineMap] at h
  obtain ⟨t, ht, he⟩ := h
  obtain ⟨b, hb, _⟩ := hcontacts j.1 j.2 t ⟨ht.1.le, ht.2.le⟩ he
  exact Polygonal.Route.not_atEnd_of_mem_Ioo _ _ ht b hb

/-- If endpoints of two segments on different edges coincide, their point is a
declared vertex. This allows the two segments of a single route at a bend. -/
@[expose] def SharedSegmentEndsAreVertices {G : Graph} (D : PolygonalDrawing G) : Prop :=
  ∀ (i j : D.SegmentIndex), i.1 ≠ j.1 → ∀ {s t : ℝ},
    s ∈ ({0, 1} : Set ℝ) → t ∈ ({0, 1} : Set ℝ) →
    (D.route i.1).eval i.2 s = (D.route j.1).eval j.2 t →
    (D.route i.1).eval i.2 s ∈ D.vertex '' {v | v ∈ G.vertices}

/-- Regularity of a polygonal drawing of open routes. Listed points are distinct
along each route. Contacts in open segments avoid all listed endpoints, meet on
distinct supporting lines, and involve at most two segments. Common segment
ends on distinct edges are declared vertices. -/
structure HasRegularContacts {G : Graph} (D : PolygonalDrawing G) : Prop where
  /-- Each route has distinct listed points, including its two outer endpoints. -/
  points_injective : ∀ e, Function.Injective (D.route e).point
  /-- A declared vertex is reached only at its corresponding original ends. -/
  vertex_contacts : ∀ e (i : Fin (D.route e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
    ∀ v ∈ G.vertices, (D.route e).eval i t = D.vertex v →
      ∃ b, (D.route e).AtEnd i t b ∧ Dart.vertex (e, b) = v
  /-- A listed endpoint cannot lie in the open part of any segment. -/
  endpoints_avoid_interiors : ∀ i j : D.SegmentIndex,
    D.segmentStart i ∉ openSegment ℝ (D.segmentStart j) (D.segmentFinish j) ∧
    D.segmentFinish i ∉ openSegment ℝ (D.segmentStart j) (D.segmentFinish j)
  /-- Open intersections of distinct segments are between distinct lines. -/
  lines_ne_at_intersections : ∀ i j : D.SegmentIndex, i ≠ j → ∀ z,
    z ∈ openSegment ℝ (D.segmentStart i) (D.segmentFinish i) →
    z ∈ openSegment ℝ (D.segmentStart j) (D.segmentFinish j) →
    affineSpan ℝ ({D.segmentStart i, D.segmentFinish i} : Set ℂ) ≠
      affineSpan ℝ ({D.segmentStart j, D.segmentFinish j} : Set ℂ)
  /-- No three distinct open segments contain a common point. -/
  no_open_triple : ∀ (f : Fin 3 ↪ D.SegmentIndex) (z : ℂ),
    ¬∀ i, z ∈ openSegment ℝ (D.segmentStart (f i)) (D.segmentFinish (f i))
  /-- Different edges can only share listed endpoints at declared vertices. -/
  shared_ends_are_vertices : D.SharedSegmentEndsAreVertices

/-- The two ends of a route with regular contacts name different vertices. -/
theorem HasRegularContacts.reverse_vertex_ne {G : Graph} {D : PolygonalDrawing G}
    (hD : D.HasRegularContacts) (d : Dart G) : d.reverse.vertex ≠ d.vertex := by
  obtain ⟨e, b⟩ := d
  have hend : (D.route e).start ≠ (D.route e).finish := by
    intro he
    have hval := congrArg Fin.val (hD.points_injective e he)
    exact Nat.succ_ne_zero _ hval.symm
  have hv : Dart.vertex (G := G) (e, false) ≠ Dart.vertex (e, true) := by
    intro he
    apply hend
    change (D.route e).endpoint false = (D.route e).endpoint true
    rw [D.endpoint_eq, D.endpoint_eq, he]
  cases b
  · exact hv.symm
  · exact hv

/-- Distinct segment occurrences in a regular drawing have at most one open point in common. -/
theorem HasRegularContacts.open_inter_subsingleton {G : Graph} {D : PolygonalDrawing G}
    (hD : D.HasRegularContacts) (i j : D.SegmentIndex) (hij : i ≠ j) :
    (openSegment ℝ (D.segmentStart i) (D.segmentFinish i) ∩
      openSegment ℝ (D.segmentStart j) (D.segmentFinish j)).Subsingleton := by
  intro x hx y hy
  have hne := hD.lines_ne_at_intersections i j hij x hx.1 hx.2
  exact (segment_inter_subsingleton_of_affineSpan_ne hne).anti
    (Set.inter_subset_inter (openSegment_subset_segment ℝ _ _)
      (openSegment_subset_segment ℝ _ _)) hx hy

/-- The actual crossings of a regular drawing admit disjoint closed disks avoiding all
vertices and listed segment endpoints. Only the two crossing segments meet each disk. -/
theorem HasRegularContacts.exists_crossing_neighborhoods {G : Graph} {D : PolygonalDrawing G}
    (hD : D.HasRegularContacts) :
    let C := Polygonal.openSegmentCrossings D.segmentStart D.segmentFinish
    C.Finite ∧ ∃ ρ : ℂ → ℝ,
      (∀ z ∈ C, 0 < ρ z) ∧ C.PairwiseDisjoint (fun z => Metric.closedBall z (ρ z)) ∧
      (∀ z ∈ C, ∀ v ∈ G.vertices, D.vertex v ∉ Metric.closedBall z (ρ z)) ∧
      (∀ z ∈ C, ∀ i : D.SegmentIndex,
        D.segmentStart i ∉ Metric.closedBall z (ρ z) ∧
        D.segmentFinish i ∉ Metric.closedBall z (ρ z)) ∧
      ∀ (i j : D.SegmentIndex), i ≠ j → ∀ z,
        z ∈ openSegment ℝ (D.segmentStart i) (D.segmentFinish i) →
        z ∈ openSegment ℝ (D.segmentStart j) (D.segmentFinish j) →
        ∀ k : D.SegmentIndex, k ≠ i → k ≠ j →
          Disjoint (Metric.closedBall z (ρ z))
            (segment ℝ (D.segmentStart k) (D.segmentFinish k)) := by
  let C := Polygonal.openSegmentCrossings D.segmentStart D.segmentFinish
  let V := D.vertex '' {v | v ∈ G.vertices}
  let E := Set.range D.segmentStart ∪ Set.range D.segmentFinish
  have hV : V.Finite := (List.finite_toSet G.vertices).image _
  have havoid : Disjoint C (V ∪ E) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨i, _, _, hi, _⟩ (⟨v, hv, rfl⟩ | (⟨k, rfl⟩ | ⟨k, rfl⟩))
    · exact D.vertex_notMem_openSegment_of_vertex_contacts v
        (fun e l t ht => hD.vertex_contacts e l t ht v hv) i hi
    · exact (hD.endpoints_avoid_interiors k i).1 hi
    · exact (hD.endpoints_avoid_interiors k i).2 hi
  obtain ⟨hC, ρ, hpos, hdisj, hlocal⟩ := Polygonal.exists_openSegment_crossing_neighborhoods
    D.segmentStart D.segmentFinish (hV.union ((Set.finite_range _).union (Set.finite_range _)))
    havoid hD.open_inter_subsingleton
  refine ⟨hC, ρ, hpos, hdisj, ?_, ?_, ?_⟩
  · intro z hz v hv hw
    exact Set.disjoint_left.mp (hlocal z hz).1 hw (Or.inl ⟨v, hv, rfl⟩)
  · intro z hz i
    exact ⟨fun hw => Set.disjoint_left.mp (hlocal z hz).1 hw (Or.inr (Or.inl ⟨i, rfl⟩)),
      fun hw => Set.disjoint_left.mp (hlocal z hz).1 hw (Or.inr (Or.inr ⟨i, rfl⟩))⟩
  · intro i j hij z hi hj k hki hkj
    apply (hlocal z ⟨i, j, hij, hi, hj⟩).2 k
    intro hk
    have hko : z ∈ openSegment ℝ (D.segmentStart k) (D.segmentFinish k) := by
      refine mem_openSegment_of_ne_left_right ?_ ?_ hk
      · intro he
        exact (hD.endpoints_avoid_interiors k i).1 (he.symm ▸ hi)
      · intro he
        exact (hD.endpoints_avoid_interiors k i).2 (he.symm ▸ hi)
    let f : Fin 3 ↪ D.SegmentIndex := ⟨Fin.cons i (Fin.cons j (fun _ : Fin 1 => k)), by
      rw [Fin.cons_injective_iff, Fin.cons_injective_iff]
      have hsingle : Function.Injective (fun _ : Fin 1 => k) :=
        Function.injective_of_subsingleton _
      simp [hij, hki.symm, hkj.symm, hsingle]⟩
    exact hD.no_open_triple f z (Fin.cases hi (Fin.cases hj (fun _ => hko)))

/-- A contact between two different edges is either in both segment interiors
or at matching ends of the two graph routes. -/
theorem HasRegularContacts.edge_contact_cases {G : Graph} {D : PolygonalDrawing G}
    (hD : D.HasRegularContacts) (i j : D.SegmentIndex) (hij : i.1 ≠ j.1) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : (D.route i.1).eval i.2 s = (D.route j.1).eval j.2 t) :
    (s ∈ Set.Ioo 0 1 ∧ t ∈ Set.Ioo 0 1) ∨
      ∃ b c, (D.route i.1).AtEnd i.2 s b ∧ (D.route j.1).AtEnd j.2 t c ∧
        Dart.vertex (i.1, b) = Dart.vertex (j.1, c) := by
  have both_open (a b : D.SegmentIndex) {u v : ℝ}
      (hv : v ∈ Set.Icc 0 1)
      (heval : (D.route a.1).eval a.2 u = (D.route b.1).eval b.2 v)
      (hu : u ∈ Set.Ioo 0 1) : v ∈ Set.Ioo 0 1 := by
    by_contra h
    have hb : v ∈ ({0, 1} : Set ℝ) := by
      rw [← Set.Icc_sdiff_Ioo_same zero_le_one]
      exact ⟨hv, h⟩
    have hopen : (D.route b.1).eval b.2 v ∈
        openSegment ℝ (D.segmentStart a) (D.segmentFinish a) := by
      rw [← heval]
      exact lineMap_mem_openSegment ℝ _ _ hu
    rcases hb with hzero | hone
    · rw [show v = 0 from hzero, Polygonal.Route.eval, AffineMap.lineMap_apply_zero] at hopen
      exact (hD.endpoints_avoid_interiors b a).1 hopen
    · rw [show v = 1 from hone, Polygonal.Route.eval, AffineMap.lineMap_apply_one] at hopen
      exact (hD.endpoints_avoid_interiors b a).2 hopen
  by_cases hso : s ∈ Set.Ioo 0 1
  · exact Or.inl ⟨hso, both_open i j ht he hso⟩
  have hto : t ∉ Set.Ioo 0 1 := hso ∘ both_open j i hs he.symm
  have shared := hD.shared_ends_are_vertices i j hij (s := s) (t := t)
  rw [← Set.Icc_sdiff_Ioo_same zero_le_one] at shared
  obtain ⟨v, hv, heq⟩ := shared ⟨hs, hso⟩ ⟨ht, hto⟩ he
  obtain ⟨b, hb, hbv⟩ := hD.vertex_contacts i.1 i.2 s hs v hv heq.symm
  obtain ⟨c, hc, hcv⟩ := hD.vertex_contacts j.1 j.2 t ht v hv (he.symm.trans heq.symm)
  exact Or.inr ⟨b, c, hb, hc, hbv.trans hcv.symm⟩

/-- Every listed point of an edge misses the support of an edge with disjoint
graph endpoints. Their open segments may still cross. -/
theorem HasRegularContacts.point_notMem_other_support {G : Graph} {D : PolygonalDrawing G}
    (hD : D.HasRegularContacts) (e f : Fin G.edges.length)
    (hind : ∀ b c, Dart.vertex (e, b) ≠ Dart.vertex (f, c))
    (k : Fin ((D.route e).bends + 2)) :
    (D.route e).point k ∉ (D.route f).support := by
  have hef : e ≠ f := fun he => hind false false (congrArg (fun i => Dart.vertex (i, false)) he)
  have hav (i : Fin (D.route e).segments) {s : ℝ} (hs : s ∈ ({0, 1} : Set ℝ)) :
      (D.route e).eval i s ∉ (D.route f).support := by
    intro h
    obtain ⟨j, t, ht, heq⟩ := ((D.route f).mem_support_iff _).mp h
    rw [← Set.Icc_sdiff_Ioo_same zero_le_one] at hs
    obtain ⟨hscl, hsend⟩ := hs
    rcases hD.edge_contact_cases ⟨e, i⟩ ⟨f, j⟩ hef hscl ht heq.symm with
      ⟨hsopen, _⟩ | ⟨b, c, _, _, he⟩
    · exact hsend hsopen
    · exact hind b c he
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simpa only [Polygonal.Route.eval, AffineMap.lineMap_apply_one, Fin.succ_last] using
      hav (Fin.last (D.route e).bends) (Or.inr rfl : (1 : ℝ) ∈ ({0, 1} : Set ℝ))
  · simpa only [Polygonal.Route.eval, AffineMap.lineMap_apply_zero] using
      hav i (Or.inl rfl : (0 : ℝ) ∈ ({0, 1} : Set ℝ))

end Cslib.Complexity.Graph.PolygonalDrawing
