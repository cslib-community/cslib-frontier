/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.FaceColorsRayParity
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Germs
public import CslibFrontier.Foundations.Geometry.Polygonal.RayParityColors
public import CslibFrontier.Foundations.Geometry.Polygonal.RouteInterior
public import CslibFrontier.Foundations.Geometry.Polygonal.SegmentRays
import CslibFrontier.Foundations.Geometry.Polygonal.Join

/-!
# Segment incidences of polygonal drawings

The interior of each actual listed segment is disjoint from every other segment
occurrence. Consecutive bends may coincide only as the shared endpoints allowed by
the route parameter, and the two original ends of a loop remain distinct.
`HasRegularContacts.segment_ends_at_bend` identifies both segment occurrences at
an internal bend of a regular drawing with simple routes, even when the drawing has crossings.
`segment_end_at_vertex_of_contacts` identifies graph darts from the vertex contact condition.
`IsEmbedding.hasRegularContacts` supplies those contact conditions for loopless embeddings.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal

/-- Distinct indexed segments in an embedding cannot meet in the open interior
of either segment. The statement includes different segments on the same loop route. -/
theorem IsEmbedding.segment_interior_disjoint {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (s j : D.SegmentIndex) (hne : j ≠ s)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
    AffineMap.lineMap (D.segmentStart s) (D.segmentFinish s) t ∉
      segment ℝ (D.segmentStart j) (D.segmentFinish j) := by
  rw [segment_eq_image_lineMap]
  rintro ⟨u, hu, heq⟩
  rcases s with ⟨e, i⟩
  rcases j with ⟨f, k⟩
  by_cases hedge : e = f
  · subst f
    exact hne (((hD.simple e).index_time_eq_of_eval_eq_of_mem_Ioo i k ht hu heq.symm).1 ▸ rfl)
  · obtain ⟨tag, _, hs, _, _⟩ :=
      hD.edge_contacts e f hedge i k t u ⟨ht.1.le, ht.2.le⟩ hu heq.symm
    exact Route.not_atEnd_of_mem_Ioo _ _ ht tag hs

/-- At any listed segment endpoint, another segment can contain the point only
as one of its own endpoints. This uses the actual continuum of each segment. -/
theorem IsEmbedding.segment_endpoint_contact {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (k : D.SegmentIndex × Bool) (j : D.SegmentIndex)
    (hp : rayEndpoint D.segmentStart D.segmentFinish k ∈
      segment ℝ (D.segmentStart j) (D.segmentFinish j)) :
    D.segmentStart j = rayEndpoint D.segmentStart D.segmentFinish k ∨
      D.segmentFinish j = rayEndpoint D.segmentStart D.segmentFinish k := by
  classical
  rcases k with ⟨s, tag⟩
  by_cases hj : j = s
  · subst j
    cases tag <;> simp [rayEndpoint]
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨t, ht, heq⟩ := hp
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · exact .inl (by simpa only [← ht0, AffineMap.lineMap_apply_zero] using heq)
  rcases eq_or_lt_of_le ht.2 with ht1 | ht1
  · exact .inr (by simpa only [ht1, AffineMap.lineMap_apply_one] using heq)
  refine (hD.segment_interior_disjoint j s (Ne.symm hj) t ⟨ht0, ht1⟩ ?_).elim
  rw [heq]
  cases tag <;> simp [rayEndpoint, left_mem_segment, right_mem_segment]

/-- The actual point of a segment-end occurrence is its affine endpoint parameter. -/
theorem segment_endpoint_eq_eval {G : Graph} (D : PolygonalDrawing G)
    (s : D.SegmentIndex) (tag : Bool) :
    rayEndpoint D.segmentStart D.segmentFinish (s, tag) =
      (D.route s.1).eval s.2 (if tag then 1 else 0) := by
  rcases s with ⟨e, i⟩
  cases tag <;> simp [rayEndpoint, segmentStart, segmentFinish, Route.eval]

private theorem endpoint_parameters_mem_Icc : ({0, 1} : Set ℝ) ⊆ Set.Icc 0 1 :=
  Set.pair_subset_iff.mpr ⟨by simp, by simp⟩

private theorem segment_ends_at_bend_of_contacts {G : Graph} {D : PolygonalDrawing G}
    (hsimple : ∀ e, (D.route e).IsSimple)
    (hcontact : ∀ (a b : D.SegmentIndex), a.1 ≠ b.1 → ∀ {t u : ℝ},
      t ∈ ({0, 1} : Set ℝ) → u ∈ ({0, 1} : Set ℝ) →
      (D.route a.1).eval a.2 t = (D.route b.1).eval b.2 u →
      ∃ side, (D.route a.1).AtEnd a.2 t side) (e : Fin G.2.length) (i : Fin (D.route e).bends)
    (k : D.SegmentIndex × Bool)
    (hp : rayEndpoint D.segmentStart D.segmentFinish k =
      (D.route e).point i.castSucc.succ) :
    k = (⟨e, i.castSucc⟩, true) ∨ k = (⟨e, i.succ⟩, false) := by
  rcases k with ⟨⟨f, j⟩, tag⟩
  have htime : (if tag then (1 : ℝ) else 0) ∈ ({0, 1} : Set ℝ) := by
    cases tag <;> simp
  have hpoint : (D.route e).eval i.castSucc 1 =
      (D.route f).eval j (if tag then 1 else 0) := by
    rw [← D.segment_endpoint_eq_eval ⟨f, j⟩ tag]
    simpa only [Route.eval, AffineMap.lineMap_apply_one] using hp.symm
  have hnot (b : Bool) : ¬(D.route e).AtEnd i.castSucc 1 b := by
    have hi : (i.val : ℝ) + 1 < (D.route e).segments := by
      exact_mod_cast Nat.add_lt_add_right i.isLt 1
    have hlo : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    cases b <;> simp only [Route.AtEnd, Route.position, Fin.val_castSucc,
      Bool.false_eq_true, ↓reduceIte] <;> linarith
  by_cases hedge : e = f
  · subst f
    obtain hpos | ⟨hstart, -⟩ | ⟨hfinish, -⟩ :=
      hsimple e _ _ _ _ (by simp) (endpoint_parameters_mem_Icc htime) hpoint
    · cases tag
      · dsimp [Route.position] at hpos
        have hj : j = i.succ := Fin.ext (by exact_mod_cast (hpos.trans (add_zero _)).symm)
        exact .inr (hj ▸ rfl)
      · dsimp [Route.position] at hpos
        have hj : j = i.castSucc := Fin.ext (by exact_mod_cast (add_right_cancel hpos).symm)
        exact .inl (hj ▸ rfl)
    · exact (hnot false hstart).elim
    · exact (hnot true hfinish).elim
  · obtain ⟨b, hb⟩ := hcontact ⟨e, i.castSucc⟩ ⟨f, j⟩ hedge (by simp) htime hpoint
    exact (hnot b hb).elim

/-- At an internal bend of a polygonal embedding, the only incident segment ends are
the two consecutive occurrences of its route. This includes bends of closed loop routes. -/
theorem IsEmbedding.segment_ends_at_bend {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (e : Fin G.edges.length) (i : Fin (D.route e).bends)
    (k : D.SegmentIndex × Bool)
    (hp : rayEndpoint D.segmentStart D.segmentFinish k =
      (D.route e).point i.castSucc.succ) :
    k = (⟨e, i.castSucc⟩, true) ∨ k = (⟨e, i.succ⟩, false) :=
  segment_ends_at_bend_of_contacts hD.simple (fun a b hab _ _ ht hu h =>
    let ⟨side, _, hend, _, _⟩ := hD.edge_contacts a.1 b.1 hab a.2 b.2 _ _
      (endpoint_parameters_mem_Icc ht) (endpoint_parameters_mem_Icc hu) h
    ⟨side, hend⟩) e i k hp

/-- At an internal bend of a simple route in a regular drawing, the only incident
segment ends are the two consecutive occurrences of that route. -/
theorem HasRegularContacts.segment_ends_at_bend {G : Graph} {D : PolygonalDrawing G}
    (hD : D.HasRegularContacts) (hsimple : ∀ e, (D.route e).IsSimple)
    (e : Fin G.edges.length) (i : Fin (D.route e).bends) (k : D.SegmentIndex × Bool)
    (hp : rayEndpoint D.segmentStart D.segmentFinish k =
      (D.route e).point i.castSucc.succ) :
    k = (⟨e, i.castSucc⟩, true) ∨ k = (⟨e, i.succ⟩, false) :=
  segment_ends_at_bend_of_contacts hsimple (fun a b hab _ _ ht hu h =>
    let ⟨v, hv, he⟩ := hD.shared_ends_are_vertices a b hab ht hu h
    let ⟨side, hend, _⟩ := hD.vertex_contacts a.1 a.2 _
      (endpoint_parameters_mem_Icc ht) v hv he.symm
    ⟨side, hend⟩) e i k hp

/-- Every segment end at a declared vertex is an actual original graph dart there.
Internal bends cannot be mistaken for vertex incidences. -/
theorem segment_end_at_vertex_of_contacts {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (hcontacts : ∀ e (i : Fin (D.route e).segments) t, t ∈ Set.Icc 0 1 →
      (D.route e).eval i t = D.vertex v →
      ∃ b, (D.route e).AtEnd i t b ∧ Dart.vertex (e, b) = v)
    (k : D.SegmentIndex × Bool)
    (hp : rayEndpoint D.segmentStart D.segmentFinish k = D.vertex v) :
    ∃ d : Dart G, d.vertex = v ∧ D.segmentEnd d = k := by
  rcases k with ⟨⟨e, i⟩, tag⟩
  rw [D.segment_endpoint_eq_eval] at hp
  obtain ⟨b, hb, hvertex⟩ := hcontacts e i _ (by cases tag <;> simp) hp
  refine ⟨(e, b), hvertex, ?_⟩
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hi1 : (i.val : ℝ) + 1 ≤ (D.route e).segments := by exact_mod_cast i.isLt
  cases b <;> cases tag <;>
    simp only [Route.AtEnd, Route.position, Bool.false_eq_true, ↓reduceIte] at hb
  · have hi : i = 0 := Fin.ext (Nat.cast_eq_zero (R := ℝ).mp (by linarith))
    subst i
    rfl
  · linarith
  · linarith
  · dsimp [Route.segments] at hb
    push_cast at hb
    have hi : i = Fin.last (D.route e).bends := Fin.ext <| by
      rw [Fin.val_last]
      exact (Nat.cast_inj (R := ℝ)).mp (by linarith)
    subst i
    rfl

/-- Segment ends at declared vertices of an embedding are actual graph darts there. -/
theorem IsEmbedding.segment_end_at_vertex {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) (hv : v ∈ G.vertices) (k : D.SegmentIndex × Bool)
    (hp : rayEndpoint D.segmentStart D.segmentFinish k = D.vertex v) :
    ∃ d : Dart G, d.vertex = v ∧ D.segmentEnd d = k :=
  D.segment_end_at_vertex_of_contacts v (fun e i t ht => hD.vertex_contacts e i t ht v hv) k hp

/-- A polygonal embedding of a declared loopless graph has regular contacts. Looplessness
is needed for injectivity of the listed points, including both original ends. -/
theorem IsEmbedding.hasRegularContacts {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (hG : ∀ d : Dart G, d.vertex ∈ G.vertices)
    (hloopless : ∀ e : Fin G.edges.length,
      Dart.vertex (G := G) (e, false) ≠ Dart.vertex (e, true)) : D.HasRegularContacts := by
  have endpointTime (e : Fin G.edges.length) (i : Fin ((D.route e).segments + 1)) :
      ∃ j : Fin (D.route e).segments, ∃ t ∈ Set.Icc (0 : ℝ) 1,
        (D.route e).eval j t = (D.route e).point i ∧
        (D.route e).position j t = i.val :=
    Fin.lastCases
      ⟨Fin.last (D.route e).bends, 1, by simp, by simp [Route.eval, Route.segments],
        by simp [Route.position, Route.segments]⟩
      (fun j => ⟨j, 0, by simp, AffineMap.lineMap_apply_zero _ _, by simp [Route.position]⟩) i
  have pointInjective (e : Fin G.edges.length) : Function.Injective (D.route e).point :=
    fun i j hij => by
      have hopen : (D.route e).start ≠ (D.route e).finish := by
        change (D.route e).endpoint false ≠ (D.route e).endpoint true
        rw [D.endpoint_eq, D.endpoint_eq]
        exact hD.vertex_ne (hG (e, false)) (hG (e, true)) (hloopless e)
      obtain ⟨a, s, hs, ha, hposA⟩ := endpointTime e i
      obtain ⟨b, t, ht, hb, hposB⟩ := endpointTime e j
      have h :=
        (hD.simple e).position_eq_of_eval_eq hopen a b hs ht (ha.trans (hij.trans hb.symm))
      rw [hposA, hposB] at h
      exact Fin.ext (by exact_mod_cast h)
  have endAvoid (i j : D.SegmentIndex) (b : Bool) :
      rayEndpoint D.segmentStart D.segmentFinish (i, b) ∉
        openSegment ℝ (D.segmentStart j) (D.segmentFinish j) := by
    rw [openSegment_eq_image_lineMap]
    rintro ⟨t, ht, he⟩
    by_cases hij : i = j
    · subst i
      have ht' := ((hD.simple j.1).index_time_eq_of_eval_eq_of_mem_Ioo j.2 j.2 ht
        (by cases b <;> simp) (he.trans (D.segment_endpoint_eq_eval j b))).2
      cases b
      · exact ht.1.ne' ht'
      · exact ht.2.ne ht'
    · refine hD.segment_interior_disjoint j i hij t ht ?_
      rw [he]
      cases b <;> simp [rayEndpoint, left_mem_segment, right_mem_segment]
  have disjointOpen (i j : D.SegmentIndex) (hne : i ≠ j) (z : ℂ)
      (hi : z ∈ openSegment ℝ (D.segmentStart i) (D.segmentFinish i))
      (hj : z ∈ openSegment ℝ (D.segmentStart j) (D.segmentFinish j)) : False := by
    rw [openSegment_eq_image_lineMap] at hi
    obtain ⟨t, ht, rfl⟩ := hi
    exact hD.segment_interior_disjoint i j (Ne.symm hne) t ht (openSegment_subset_segment ℝ _ _ hj)
  refine ⟨pointInjective, hD.vertex_contacts, fun i j => ⟨endAvoid i j false, endAvoid i j true⟩,
    fun i j h z hi hj => (disjointOpen i j h z hi hj).elim,
    fun f z h => disjointOpen (f 0) (f 1)
      (fun he => (by decide : (0 : Fin 3) ≠ 1) (f.injective he)) z (h 0) (h 1),
    fun i j hij s t hs ht he => ?_⟩
  have hs' := endpoint_parameters_mem_Icc hs
  obtain ⟨b, _, hb, _, _⟩ :=
    hD.edge_contacts i.1 j.1 hij i.2 j.2 s t hs' (endpoint_parameters_mem_Icc ht) he
  exact ⟨Dart.vertex (G := G) (i.1, b), hG (i.1, b), (D.endpoint_eq i.1 b).symm.trans
    ((D.route i.1).at_eq_endpoint i.2 hs' b hb).symm⟩

end Cslib.Complexity.Graph.PolygonalDrawing
