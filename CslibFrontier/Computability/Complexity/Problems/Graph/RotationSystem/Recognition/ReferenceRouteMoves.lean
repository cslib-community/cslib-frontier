/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Moves
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceDrawing
public import CslibFrontier.Foundations.Geometry.Polygonal.RouteParity
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.CrossingNeighborhoods
import CslibFrontier.Foundations.Geometry.Polygonal.LineEnds
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Data.Finset.DenselyOrdered

/-!
# Parity moves on reference routes

Each free subdivision edge receives its prescribed parity excursion at its midpoint.
The resulting routes keep short initial and terminal segments along the reference
edge. The route between those segments avoids every declared vertex. The
construction is original finite polygonal geometry and admits retracing.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Polygonal

/-- All sufficiently short end segments of the reference drawing fit in disjoint
closed balls at their declared vertices. Inside each ball, two distinct reference
edges can meet only at the center. For every allowed cut fraction the ports are
distinct across darts and avoid all declared vertices. The cuts use the same
fraction of each half-edge as the parity-move construction. -/
theorem exists_reference_move_stub_isolation {I : FixedRotationInput} (hI : Valid I) :
    let G := subdivisionGraph I
    let ref := referenceDrawing I
    ∃ ρ > (0 : ℝ), ∃ δ₀ ∈ Set.Ioo (0 : ℝ) 1,
      (∀ v ∈ G.vertices, ∀ w ∈ G.vertices, v ≠ w →
        Disjoint (Metric.closedBall (ref.vertex v) ρ) (Metric.closedBall (ref.vertex w) ρ)) ∧
      (∀ v ∈ G.vertices, ∀ (e f : Fin G.edges.length), e ≠ f → ∀ z,
        z ∈ Metric.closedBall (ref.vertex v) ρ →
        z ∈ (ref.route e).support → z ∈ (ref.route f).support → z = ref.vertex v) ∧
      ∀ δ ∈ Set.Ioc 0 δ₀,
        let port (a : Dart G) :=
          AffineMap.lineMap (ref.vertex a.vertex) ((ref.route a.1).eval 0 (1 / 2)) δ
        (∀ a : Dart G, segment ℝ (ref.vertex a.vertex) (port a) ⊆
          Metric.closedBall (ref.vertex a.vertex) ρ ∩ (ref.route a.1).support) ∧
        Function.Injective port ∧
        ∀ a, port a ∉ ref.vertex '' {v | v ∈ G.vertices} := by
  classical
  let G := subdivisionGraph I
  let ref := referenceDrawing I
  let C := referenceCrossingPoints I
  let V := ref.vertex '' {v | v ∈ G.vertices}
  have hC : C.Finite := (exists_reference_crossing_neighborhoods hI).1
  have hV : V.Finite := (List.finite_toSet G.vertices).image _
  let pts := (hV.union hC).toFinset
  let gaps := ((pts ×ˢ pts).filter fun p => p.1 ≠ p.2).image
    (fun p => dist p.1 p.2 / 2)
  obtain ⟨ρ, hpos, hgap⟩ := Finset.exists_between' ({0} : Finset ℝ) gaps fun x hx y hy => by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_singleton.mp hx).symm ▸ half_pos (dist_pos.mpr (Finset.mem_filter.mp hp).2)
  have hρ := hpos _ (Finset.mem_singleton_self _)
  have hdist {x y : ℂ} (hx : x ∈ V ∪ C) (hy : y ∈ V ∪ C) (hne : x ≠ y) :
      ρ < dist x y / 2 :=
    hgap _ (Finset.mem_image.mpr ⟨(x, y), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨(hV.union hC).mem_toFinset.mpr hx, (hV.union hC).mem_toFinset.mpr hy⟩,
        hne⟩, rfl⟩)
  have hmem (v : ℕ) (hv : v ∈ G.vertices) : ref.vertex v ∈ V ∪ C :=
    Or.inl ⟨v, hv, rfl⟩
  have hvertex (a : Dart G) : a.vertex ∈ G.vertices :=
    RotationSystem.vertex_mem (subdivisionGraph_endpoints_declared hI) a
  have hdisj (v : ℕ) (hv : v ∈ G.vertices) (w : ℕ) (hw : w ∈ G.vertices) (hne : v ≠ w) :
      Disjoint (Metric.closedBall (ref.vertex v) ρ) (Metric.closedBall (ref.vertex w) ρ) := by
    have hne' : ref.vertex v ≠ ref.vertex w :=
      fun h => hne (referenceDrawing_vertices_injective hI hv hw h)
    exact Metric.closedBall_disjoint_closedBall (by linarith [hdist (hmem v hv) (hmem w hw) hne'])
  have hinterior {v : ℕ} (hv : v ∈ G.vertices) {z : ℂ}
      (hz : z ∈ Metric.closedBall (ref.vertex v) ρ) (hne : z ≠ ref.vertex v)
      (e : Fin G.edges.length) (he : z ∈ (ref.route e).support) :
      z ∈ openSegment ℝ (ref.route e).start (ref.route e).finish := by
    let a := ref.vertex (Dart.vertex (e, false))
    let b := ref.vertex (Dart.vertex (e, true))
    change z ∈ (Route.line a b).support at he
    rw [Route.support_line, segment_eq_image_lineMap] at he
    obtain ⟨t, ht, rfl⟩ := he
    have hnot (side : Bool) (h : AffineMap.lineMap a b t = ref.vertex (Dart.vertex (e, side))) :
        False :=
      Set.disjoint_left.mp (hdisj v hv _ (hvertex (e, side))
        fun h' => hne (h.trans (congrArg ref.vertex h'.symm))) hz
        (h.symm ▸ Metric.mem_closedBall_self hρ.le)
    exact lineMap_mem_openSegment ℝ a b
      ⟨lt_of_le_of_ne ht.1 fun h => hnot false (h.symm ▸ AffineMap.lineMap_apply_zero a b),
        lt_of_le_of_ne ht.2 fun h => hnot true (h ▸ AffineMap.lineMap_apply_one a b)⟩
  let length (a : Dart G) :=
    dist (ref.vertex a.vertex) ((ref.route a.1).eval 0 (1 / 2))
  let bounds := insert 1 (Finset.univ.image fun a : Dart G => ρ / (length a + 1))
  obtain ⟨δ₀, hδpos, hbound⟩ := Finset.exists_between' ({0} : Finset ℝ) bounds fun x hx y hy => by
    rw [Finset.mem_singleton.mp hx]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact one_pos
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy
      exact div_pos hρ (add_pos_of_nonneg_of_pos dist_nonneg one_pos)
  have hδ₀ : δ₀ ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hδpos _ (Finset.mem_singleton_self _), hbound _ (Finset.mem_insert_self ..)⟩
  have hcontact (v : ℕ) (hv : v ∈ G.vertices) (e f : Fin G.edges.length) (hef : e ≠ f)
      (z : ℂ) (hz : z ∈ Metric.closedBall (ref.vertex v) ρ)
      (he : z ∈ (ref.route e).support) (hf : z ∈ (ref.route f).support) :
      z = ref.vertex v := by
    by_contra hne
    have hc : z ∈ C := ⟨e, f, hef, hinterior hv hz hne e he, hinterior hv hz hne f hf⟩
    have hd := hdist (Or.inr hc) (hmem v hv) hne
    linarith [Metric.mem_closedBall.mp hz]
  refine ⟨ρ, hρ, δ₀, hδ₀, hdisj, hcontact, ?_⟩
  intro δ hδ
  let port (a : Dart G) :=
    AffineMap.lineMap (ref.vertex a.vertex) ((ref.route a.1).eval 0 (1 / 2)) δ
  have hstub (a : Dart G) :
      segment ℝ (ref.vertex a.vertex) (port a) ⊆
        Metric.closedBall (ref.vertex a.vertex) ρ ∩ (ref.route a.1).support := by
    let c := ref.vertex a.vertex
    let m := (ref.route a.1).eval 0 (1 / 2)
    change segment ℝ c (AffineMap.lineMap c m δ) ⊆
      Metric.closedBall c ρ ∩ (ref.route a.1).support
    apply Set.subset_inter
    · apply (convex_closedBall c ρ).segment_subset (Metric.mem_closedBall_self hρ.le)
      rw [Metric.mem_closedBall, dist_lineMap_left, Real.norm_eq_abs, abs_of_pos hδ.1]
      have ha := hbound _ (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem (fun a : Dart G => ρ / (length a + 1)) (Finset.mem_univ a)))
      have hd := (lt_div_iff₀ (add_pos_of_nonneg_of_pos (dist_nonneg : 0 ≤ length a) one_pos)).mp
        (hδ.2.trans_lt ha)
      change δ * length a ≤ ρ
      nlinarith [hδ.1]
    · have hc : c ∈ (ref.route a.1).support := by
        change ref.vertex a.vertex ∈ (ref.route a.1).support
        rw [← ref.endpoint_eq a.1 a.2]
        cases a.2 <;> exact (ref.route a.1).point_mem_support _
      have hm : m ∈ (ref.route a.1).support :=
        (ref.route a.1).at_mem_support 0 (by constructor <;> norm_num)
      have hs : Convex ℝ (ref.route a.1).support :=
        (Route.support_line _ _).symm ▸ convex_segment _ _
      exact hs.segment_subset hc (hs.segment_subset hc hm
        (lineMap_mem_segment ℝ _ _ ⟨hδ.1.le, hδ.2.trans hδ₀.2.le⟩))
  have hport (a : Dart G) :
      port a ∈ Metric.closedBall (ref.vertex a.vertex) ρ ∩ (ref.route a.1).support :=
    hstub a (right_mem_segment ℝ _ _)
  have hcenter (a : Dart G) : port a ≠ ref.vertex a.vertex := by
    have hmid : (ref.route a.1).eval 0 (1 / 2) ≠ ref.vertex a.vertex := by
      rcases a with ⟨e, side⟩
      let x := ref.vertex (Dart.vertex (e, false))
      let y := ref.vertex (Dart.vertex (e, true))
      have hxy : x ≠ y := fun h => (subdivision_endpoint_spec hI e).2
        (referenceDrawing_vertices_injective hI (hvertex (e, false)) (hvertex (e, true)) h)
      change (Route.line x y).eval 0 (1 / 2) ≠ _
      rw [Route.eval_line]
      cases side <;> intro h
      · exact absurd ((AffineMap.lineMap_eq_left_iff.mp h).resolve_left hxy) (by norm_num)
      · exact absurd ((AffineMap.lineMap_eq_right_iff.mp h).resolve_left hxy) (by norm_num)
    intro h
    exact hmid ((AffineMap.lineMap_eq_left_iff.mp h).resolve_right hδ.1.ne').symm
  refine ⟨hstub, ?_, ?_⟩
  · intro a b heq
    change port a = port b at heq
    have hv : a.vertex = b.vertex := by
      by_contra h
      exact Set.disjoint_left.mp (hdisj _ (hvertex a) _ (hvertex b) h)
        (hport a).1 (heq.symm ▸ (hport b).1)
    have he : a.1 = b.1 := by
      by_contra h
      exact hcenter a (hcontact _ (hvertex a) _ _ h _ (hport a).1 (hport a).2
        (heq.symm ▸ (hport b).2))
    rcases a with ⟨e, s⟩
    rcases b with ⟨f, t⟩
    change e = f at he
    subst f
    cases s <;> cases t
    · rfl
    · exact ((subdivision_endpoint_spec hI e).2 hv).elim
    · exact ((subdivision_endpoint_spec hI e).2 hv.symm).elim
    · rfl
  · rintro a ⟨v, hv, heq⟩
    by_cases he : v = a.vertex
    · exact hcenter a (heq.symm.trans (congrArg ref.vertex he))
    · exact Set.disjoint_left.mp (hdisj _ (hvertex a) _ hv (Ne.symm he)) (hport a).1
        (heq ▸ Metric.mem_closedBall_self hρ.le)

/-- Realize the entire finite move table as ray-parity differences from the reference
routes. Frozen routes remain literal. On free routes the initial and terminal segments
each cover the fraction `δ` of the corresponding half of the reference edge. The
middle route has at least two segments, avoids all declared vertices, and preserves
the outgoing rays through the two protected segments. -/
theorem exists_reference_drawing_with_move_rayParity {I : FixedRotationInput} (hI : Valid I)
    (moves : Moves (frame I)) (hfrozen : FrozenMoves (frame I) moves)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) {u : ℂ} (hu : u ≠ 0) :
    let ref := referenceDrawing I
    ∃ D : PolygonalDrawing (subdivisionGraph I), D.vertex = ref.vertex ∧
      (∀ e, ((frame I).segments.getD e.val ((0, 0), false)).frozen = true →
        D.route e = ref.route e) ∧
      (∀ e side, ∃ k : ℝ, 0 < k ∧ (D.route e).germ side = k • (ref.route e).germ side) ∧
      (∀ e (v : Fin (frame I).vertexCount),
        (∀ side, Dart.vertex (e, side) ≠ v.val) → D.vertex v.val ∉ (D.route e).support) ∧
      (∀ e (v : Fin (frame I).vertexCount),
        (D.route e).rayParity u (D.vertex v.val) =
          (ref.route e).rayParity u (ref.vertex v.val) + readMove (frame I) moves e.val v.val) ∧
      ∀ e, ((frame I).segments.getD e.val ((0, 0), false)).frozen ≠ true →
        let a := D.vertex (Dart.vertex (e, false))
        let b := D.vertex (Dart.vertex (e, true))
        let m := AffineMap.lineMap a b (1 / 2 : ℝ)
        let c := AffineMap.lineMap a m δ
        let d := AffineMap.lineMap m b (1 - δ)
        ∃ middle : Route, middle.start = c ∧ middle.finish = d ∧ 2 ≤ middle.segments ∧
          D.route e = ((Route.line a c).concat middle).concat (Route.line d b) ∧
          ∀ v : Fin (frame I).vertexCount, D.vertex v.val ∉ middle.support := by
  classical
  let F := frame I
  let G := subdivisionGraph I
  let ref := referenceDrawing I
  let V := Fin F.vertexCount
  let E := Fin G.edges.length
  have hvertex (v : V) : v.val ∈ G.vertices := List.mem_range.mpr v.isLt
  let point : V ↪ ℂ := ⟨fun v => ref.vertex v.val, fun a b hab =>
    Fin.ext (referenceDrawing_vertices_injective hI (hvertex a) (hvertex b) hab)⟩
  let points : Finset ℂ := Finset.univ.map point
  have hpoint (v : V) : point v ∈ points := Finset.mem_map_of_mem point (Finset.mem_univ v)
  let frozen (e : E) := (F.segments.getD e.val ((0, 0), false)).frozen = true
  have each (e : E) :
      let a := ref.vertex (Dart.vertex (e, false))
      let b := ref.vertex (Dart.vertex (e, true))
      let m := AffineMap.lineMap a b (1 / 2 : ℝ)
      let c := AffineMap.lineMap a m δ
      let d := AffineMap.lineMap m b (1 - δ)
      ∃ r : Route,
      (∀ side, r.endpoint side = (ref.route e).endpoint side) ∧
      (frozen e → r = ref.route e) ∧
      (∀ side, ∃ k : ℝ, 0 < k ∧ r.germ side = k • (ref.route e).germ side) ∧
      (∀ v : V, (∀ side, Dart.vertex (e, side) ≠ v.val) → point v ∉ r.support) ∧
      (∀ v : V, r.rayParity u (point v) =
        (ref.route e).rayParity u (point v) + readMove F moves e.val v.val) ∧
      (¬ frozen e → ∃ middle : Route, middle.start = c ∧ middle.finish = d ∧ 2 ≤ middle.segments ∧
        r = ((Route.line a c).concat middle).concat (Route.line d b) ∧
        ∀ v : V, point v ∉ middle.support) := by
    have heIdx : e.val < F.segments.length := by
      simpa only [G, F, subdivisionGraph, frame, List.length_map] using e.isLt
    let idx : Fin F.segments.length := ⟨e.val, heIdx⟩
    have hread (v : V) : readMove F moves e.val v.val = moves idx v := by
      simp only [readMove, heIdx, v.isLt, dite_true, idx]
      rfl
    let a := ref.vertex (Dart.vertex (e, false))
    let b := ref.vertex (Dart.vertex (e, true))
    let L := AffineMap.lineMap (k := ℝ) a b
    let m := L (1 / 2)
    let c := AffineMap.lineMap a m δ
    let d := AffineMap.lineMap m b (1 - δ)
    have havoid (v : V) (hne : ∀ side, Dart.vertex (e, side) ≠ v.val) :
        point v ∉ segment ℝ a b := by
      rw [segment_eq_image_lineMap]
      rintro ⟨t, ht, heq⟩
      have hhit : (ref.route e).eval 0 t = ref.vertex v.val :=
        (Route.eval_line a b 0 t).trans heq
      obtain ⟨side, _, hs⟩ := referenceDrawing_vertex_contacts hI e 0 ht (hvertex v) hhit
      exact hne side hs
    by_cases hfixed : frozen e
    · refine ⟨ref.route e, fun _ => rfl, fun _ => rfl,
        fun _ => ⟨1, one_pos, (one_smul ℝ _).symm⟩, ?_, ?_, fun h => (h hfixed).elim⟩
      · intro v hne
        change point v ∉ (Route.line a b).support
        rw [Route.support_line]
        exact havoid v hne
      · intro v
        rw [hread, hfrozen idx v hfixed, ← Bool.zero_eq_false, add_zero]
    let odd := (Finset.univ.filter fun v : V => moves idx v = true).map point
    have hsub : odd ⊆ points := Finset.map_subset_map.mpr (Finset.filter_subset _ _)
    have hbit (v : V) : decide (point v ∈ odd) = readMove F moves e.val v.val := by
      rw [hread]
      have hm : point v ∈ odd ↔ moves idx v = true := by
        simp only [odd, Finset.mem_map' point, Finset.mem_filter, Finset.mem_univ, true_and]
      calc
        _ = decide (moves idx v = true) := Bool.decide_congr hm
        _ = _ := by cases moves idx v <;> rfl
    have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by constructor <;> norm_num
    have hδ' : 1 - δ ∈ Set.Ioo (0 : ℝ) 1 := ⟨sub_pos.mpr hδ.2, sub_lt_self _ hδ.1⟩
    have hc : c = L (δ / 2) := by
      have h := L.apply_lineMap 0 (1 / 2) δ
      rw [AffineMap.lineMap_apply_ring'] at h
      simp only [L, AffineMap.lineMap_apply_zero] at h
      convert h.symm using 2
      ring
    have hd : d = L (1 - δ / 2) := by
      have h := L.apply_lineMap (1 / 2) 1 (1 - δ)
      rw [AffineMap.lineMap_apply_ring'] at h
      simp only [L, AffineMap.lineMap_apply_one] at h
      convert h.symm using 2
      ring
    have hopen (v : V) : point v ∉ openSegment ℝ a b := by
      rw [openSegment_eq_image_lineMap]
      rintro ⟨t, ht, heq⟩
      have hhit : (ref.route e).eval 0 t = ref.vertex v.val :=
        (Route.eval_line a b 0 t).trans heq
      obtain ⟨side, hs, _⟩ :=
        referenceDrawing_vertex_contacts hI e 0 ⟨ht.1.le, ht.2.le⟩ (hvertex v) hhit
      have htEnd := (Route.atEnd_line_iff a b 0 t side).mp hs
      cases side
      · exact ht.1.ne' htEnd
      · exact ht.2.ne htEnd
    have hm : m ∈ openSegment ℝ a b := lineMap_mem_openSegment ℝ a b hhalf
    have hmid : m ∉ points := fun h =>
      let ⟨v, _, hv⟩ := Finset.mem_map.mp h
      hopen v (hv.symm ▸ hm)
    have hcopen : c ∈ openSegment ℝ a b :=
      hc ▸ lineMap_mem_openSegment ℝ a b ⟨half_pos hδ.1, by linarith [hδ.2]⟩
    have hdopen : d ∈ openSegment ℝ a b :=
      hd ▸ lineMap_mem_openSegment ℝ a b ⟨by linarith [hδ.2], sub_lt_self 1 (half_pos hδ.1)⟩
    let p := Route.line c m
    let q := Route.line m d
    obtain ⟨middle, hend, _, _, hsupport, hpar, hsegments⟩ :=
      Route.exists_concat_add_rayParity isOpen_univ isPathConnected_univ points odd hsub
        (fun z _ => Set.mem_univ z) p q rfl (Set.mem_univ _) hmid hu
    have hs : middle.start = c :=
      (hend false).trans (Route.endpoint_concat p q rfl false)
    have hf : middle.finish = d :=
      (hend true).trans (Route.endpoint_concat p q rfl true)
    have hmiddle (v : V) : point v ∉ middle.support := by
      intro hv
      rcases hsupport hv with h | h
      · rw [Route.support_concat p q rfl] at h
        change point v ∈ (Route.line c m).support ∪ (Route.line m d).support at h
        rw [Route.support_line, Route.support_line] at h
        exact hopen v (h.elim
          (fun hcm => (convex_openSegment a b).segment_subset hcopen hm hcm)
          (fun hmd => (convex_openSegment a b).segment_subset hm hdopen hmd))
      · exact h.2 (hpoint v)
    let left := Route.line a c
    let right := Route.line d b
    have hleft : left.finish = middle.start := hs.symm
    have hright : (left.concat middle).finish = right.start :=
      (Route.endpoint_concat left middle hleft true).trans hf
    let r := (left.concat middle).concat right
    refine ⟨r, ?_, fun h => (hfixed h).elim, ?_, ?_, ?_,
      fun _ => ⟨middle, hs, hf, hsegments, rfl, hmiddle⟩⟩
    · intro side
      rw [Route.endpoint_concat _ _ hright, Route.endpoint_concat _ _ hleft]
      cases side <;> rfl
    · intro side
      refine ⟨δ / 2, by linarith [hδ.1], ?_⟩
      rw [Route.germ_concat _ _ hright, Route.germ_concat _ _ hleft]
      cases side
      · change c - a = (δ / 2) • (b - a)
        rw [hc]
        exact AffineMap.lineMap_vsub_left a b _
      · change d - b = (δ / 2) • (a - b)
        rw [hd]
        calc
          _ = (1 - (1 - δ / 2)) • (a - b) := AffineMap.lineMap_vsub_right a b _
          _ = _ := by rw [sub_sub_cancel]
    · intro v hne hv
      change point v ∈ r.support at hv
      rw [Route.support_concat _ _ hright, Route.support_concat _ _ hleft] at hv
      change point v ∈ ((Route.line a c).support ∪ middle.support) ∪
        (Route.line d b).support at hv
      rw [Route.support_line, Route.support_line] at hv
      have hconvex : Convex ℝ (segment ℝ a b) := convex_segment a b
      rcases hv with (h | h) | h
      · exact havoid v hne (hconvex.segment_subset (left_mem_segment ..)
          (openSegment_subset_segment ℝ a b hcopen) h)
      · exact hmiddle v h
      · exact havoid v hne (hconvex.segment_subset
          (openSegment_subset_segment ℝ a b hdopen) (right_mem_segment ..) h)
    · intro v
      let z := point v
      have hp := (Route.rayParity_concat left p rfl u z).symm.trans
        (Route.rayParity_line_split a m u z hδ)
      have hq := (Route.rayParity_concat q right rfl u z).symm.trans
        (Route.rayParity_line_split m b u z hδ')
      have hsplit := (Route.rayParity_concat _ _ rfl u z).symm.trans
        (Route.rayParity_line_split a b u z hhalf)
      change r.rayParity u z = (Route.line a b).rayParity u z + _
      rw [← hbit v, Route.rayParity_concat _ _ hright, Route.rayParity_concat _ _ hleft,
        hpar z (hpoint v), Route.rayParity_concat p q rfl, ← hsplit, ← hp, ← hq]
      ac_rfl
  choose routes hroutes using each
  let D : PolygonalDrawing G :=
    ⟨ref.vertex, routes, fun e side => (hroutes e).1 side |>.trans (ref.endpoint_eq e side)⟩
  exact ⟨D, rfl, fun e => (hroutes e).2.1, fun e => (hroutes e).2.2.1,
    fun e => (hroutes e).2.2.2.1, fun e => (hroutes e).2.2.2.2.1,
    fun e => (hroutes e).2.2.2.2.2⟩

end Cslib.Complexity.Graph.RotationRecognition
