/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SegmentArrangement
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Sectors
public import CslibFrontier.Foundations.Geometry.Polygonal.RouteIntersectionParity
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.FaceDartColors
import CslibFrontier.Foundations.Algebra.BigOperators.Fin

/-!
# Right-side colors of polygonal drawings

The construction uses one internally chosen ray direction, actual segment endpoints,
and angular prefix sums. Segment interiors transport colors, the two bend germs transport
them through each bend, and literal clockwise realization identifies the empty vertex sectors.
`HasRegularContacts.exists_dart_colors` includes the indexed route crossing parity in
the sum of the two endpoint colors.
`HasRegularContacts.exists_faceColors_of_pairwise_even_crossings` and
`IsEmbedding.exists_faceColors` give colors on the actual face quotient.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal

variable {G : Graph} {D : PolygonalDrawing G}

open Classical in
private noncomputable def endpointSet (D : PolygonalDrawing G) : Finset ℂ :=
  Finset.univ.image D.segmentStart ∪ Finset.univ.image D.segmentFinish

private structure Frame (D : PolygonalDrawing G) where
  u : ℂ
  nonzero : u ≠ 0
  heights : Set.InjOn (fun z => (u * z).im) (↑(endpointSet D) : Set ℂ)

private def Frame.a (F : Frame D) (i : D.SegmentIndex) : ℂ := F.u * D.segmentStart i
private def Frame.b (F : Frame D) (i : D.SegmentIndex) : ℂ := F.u * D.segmentFinish i

private theorem Frame.mem_start (_F : Frame D) (i : D.SegmentIndex) :
    D.segmentStart i ∈ endpointSet D := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

private theorem Frame.mem_finish (_F : Frame D) (i : D.SegmentIndex) :
    D.segmentFinish i ∈ endpointSet D := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

private theorem Frame.endpoint (F : Frame D) (k : D.SegmentIndex × Bool) :
    rayEndpoint F.a F.b k = F.u * rayEndpoint D.segmentStart D.segmentFinish k := by
  rcases k with ⟨i, tag⟩
  cases tag <;> rfl

private theorem Frame.vector (F : Frame D) (k : D.SegmentIndex × Bool) :
    rayEndVector F.a F.b k = F.u * rayEndVector D.segmentStart D.segmentFinish k := by
  rcases k with ⟨i, tag⟩
  cases tag <;> simp [rayEndVector, a, b, mul_sub]

private theorem Frame.mem_endpoint (F : Frame D) (k : D.SegmentIndex × Bool) :
    rayEndpoint D.segmentStart D.segmentFinish k ∈ endpointSet D := by
  rcases k with ⟨i, tag⟩
  cases tag
  · exact F.mem_start i
  · exact F.mem_finish i

private theorem Frame.height (F : Frame D) (hsimple : ∀ e, (D.route e).IsSimple)
    (i : D.SegmentIndex) : (F.a i).im ≠ (F.b i).im := by
  intro h
  exact (hsimple i.1).segment_ne i.2 (F.heights (F.mem_start i) (F.mem_finish i) h)

private noncomputable def Frame.scale (F : Frame D) : ℂ →ᵃ[ℝ] ℂ :=
  ((LinearMap.mulLeft ℂ F.u).restrictScalars ℝ).toAffineMap

private theorem Frame.scale_injective (F : Frame D) : Function.Injective F.scale :=
  fun _ _ h => mul_left_cancel₀ F.nonzero h

private theorem Frame.lineMap (F : Frame D) (i : D.SegmentIndex) (t : ℝ) :
    AffineMap.lineMap (F.a i) (F.b i) t =
      F.u * AffineMap.lineMap (D.segmentStart i) (D.segmentFinish i) t :=
  (F.scale.apply_lineMap _ _ t).symm

private theorem Frame.open_inter (F : Frame D) (i j : D.SegmentIndex) :
    openSegment ℝ (F.a i) (F.b i) ∩ openSegment ℝ (F.a j) (F.b j) =
      F.scale '' (openSegment ℝ (D.segmentStart i) (D.segmentFinish i) ∩
        openSegment ℝ (D.segmentStart j) (D.segmentFinish j)) := by
  rw [Set.image_inter F.scale_injective, image_openSegment ℝ F.scale, image_openSegment ℝ F.scale]
  rfl

private theorem Frame.disjoint (F : Frame D) (hD : D.IsEmbedding)
    (i j : D.SegmentIndex) (hne : j ≠ i) (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
    AffineMap.lineMap (F.a i) (F.b i) t ∉ segment ℝ (F.a j) (F.b j) := by
  rw [segment_eq_image_lineMap]
  rintro ⟨s, hs, heq⟩
  rw [F.lineMap, F.lineMap] at heq
  exact hD.segment_interior_disjoint i j hne t ht
    (mul_left_cancel₀ F.nonzero heq ▸ lineMap_mem_segment ℝ _ _ hs)

private theorem Frame.remote (F : Frame D)
    (hcontact : ∀ (k : D.SegmentIndex × Bool) j,
      rayEndpoint D.segmentStart D.segmentFinish k ∈
        segment ℝ (D.segmentStart j) (D.segmentFinish j) →
      D.segmentStart j = rayEndpoint D.segmentStart D.segmentFinish k ∨
      D.segmentFinish j = rayEndpoint D.segmentStart D.segmentFinish k)
    (k : D.SegmentIndex × Bool) (j : D.SegmentIndex)
    (ha : F.a j ≠ rayEndpoint F.a F.b k) (hb : F.b j ≠ rayEndpoint F.a F.b k) :
    (rayEndpoint F.a F.b k).im ≠ (F.a j).im ∧
      (rayEndpoint F.a F.b k).im ≠ (F.b j).im ∧
      rayEndpoint F.a F.b k ∉ segment ℝ (F.a j) (F.b j) := by
  have ha' : D.segmentStart j ≠ rayEndpoint D.segmentStart D.segmentFinish k := fun h => ha <| by
    rw [F.endpoint]
    exact congrArg (F.u * ·) h
  have hb' : D.segmentFinish j ≠ rayEndpoint D.segmentStart D.segmentFinish k := fun h => hb <| by
    rw [F.endpoint]
    exact congrArg (F.u * ·) h
  refine ⟨fun h => ha'
      (F.heights (F.mem_endpoint k) (F.mem_start j) (by rwa [F.endpoint] at h)).symm,
    fun h => hb' (F.heights (F.mem_endpoint k) (F.mem_finish j) (by rwa [F.endpoint] at h)).symm,
    ?_⟩
  rw [segment_eq_image_lineMap]
  rintro ⟨t, ht, heq⟩
  rw [F.lineMap, F.endpoint] at heq
  exact (hcontact k j (mul_left_cancel₀ F.nonzero heq ▸ lineMap_mem_segment ℝ _ _ ht)).elim ha' hb'

private structure Frame.Contacts (F : Frame D) : Prop where
  height : ∀ i, (F.a i).im ≠ (F.b i).im
  distinct : ∀ k e : D.SegmentIndex × Bool, rayEndpoint F.a F.b e = rayEndpoint F.a F.b k →
    turnArg (rayEndVector F.a F.b e) = turnArg (rayEndVector F.a F.b k) → e = k
  atBend : ∀ e (i : Fin (D.route e).bends) (k : D.SegmentIndex × Bool),
    rayEndpoint D.segmentStart D.segmentFinish k = (D.route e).point i.castSucc.succ →
    k = (⟨e, i.castSucc⟩, true) ∨ k = (⟨e, i.succ⟩, false)
  atVertex : ∀ v ∈ G.vertices, ∀ k : D.SegmentIndex × Bool,
    rayEndpoint D.segmentStart D.segmentFinish k = D.vertex v →
    ∃ d : Dart G, d.vertex = v ∧ D.segmentEnd d = k

private theorem Frame.contacts_of_embedding (F : Frame D) (hD : D.IsEmbedding) :
    F.Contacts := by
  refine ⟨F.height hD.simple, ?_, hD.segment_ends_at_bend, hD.segment_end_at_vertex⟩
  apply rayEndVector_injective_of_open_inter_subsingleton F.a F.b
    (fun i h => F.height hD.simple i (congrArg Complex.im h))
  rintro i j hij z ⟨hzi, hzj⟩
  rw [openSegment_eq_image_lineMap] at hzi
  obtain ⟨t, ht, rfl⟩ := hzi
  exact (F.disjoint hD i j hij.symm t ht (openSegment_subset_segment ℝ _ _ hzj)).elim

private theorem Frame.regular_open_inter (F : Frame D) (hD : D.HasRegularContacts)
    (i j : D.SegmentIndex) (hij : i ≠ j) :
    (openSegment ℝ (F.a i) (F.b i) ∩ openSegment ℝ (F.a j) (F.b j)).Subsingleton := by
  rw [F.open_inter]
  exact (hD.open_inter_subsingleton i j hij).image _

private theorem Frame.contacts_of_regular (F : Frame D) (hD : D.HasRegularContacts)
    (hsimple : ∀ e, (D.route e).IsSimple) : F.Contacts := by
  refine ⟨F.height hsimple, ?_, hD.segment_ends_at_bend hsimple, ?_⟩
  · exact rayEndVector_injective_of_open_inter_subsingleton F.a F.b
      (fun i h => F.height hsimple i (congrArg Complex.im h)) (F.regular_open_inter hD)
  · intro v hv
    exact D.segment_end_at_vertex_of_contacts v (fun e i t ht => hD.vertex_contacts e i t ht v hv)

private theorem Frame.even (F : Frame D) (x : Fin G.edges.length → Bool) (hx : G.VertexEven x)
    (p : ℂ) :
    (∑ i : D.SegmentIndex, ((if F.a i = p then x i.1 else 0) +
      (if F.b i = p then x i.1 else 0))) = false :=
  D.segment_endpoints_even x hx F.u p

private noncomputable def Frame.color (F : Frame D) (x : Fin G.edges.length → Bool)
    (k : D.SegmentIndex × Bool) : Bool :=
  rayGermColor F.a F.b (fun i => x i.1) (rayEndpoint F.a F.b k) (rayEndVector F.a F.b k)

private theorem Frame.color_adjacent (F : Frame D) (hc : F.Contacts)
    (x : Fin G.edges.length → Bool) (hx : G.VertexEven x) (p : ℂ)
    (k l : D.SegmentIndex × Bool)
    (hk : rayEndpoint F.a F.b k = p) (hl : rayEndpoint F.a F.b l = p) (hkl : k ≠ l)
    (hgap : ∀ j : D.SegmentIndex × Bool, rayEndpoint F.a F.b j = p → j ≠ k → j ≠ l →
      ¬sbtw ((rayEndVector F.a F.b k).arg : Real.Angle)
        ((rayEndVector F.a F.b j).arg : Real.Angle)
        ((rayEndVector F.a F.b l).arg : Real.Angle)) :
    F.color x k + F.color x l = x k.1.1 := by
  unfold Frame.color
  rw [hk, hl]
  exact rayGermColor_adjacent F.a F.b (fun i => x i.1) hc.height p
    (F.even x hx p) k l hk hl hkl
    (fun j f hj hf h => hc.distinct f j (hj.trans hf.symm) h) hgap

private theorem Frame.color_ends (F : Frame D) (hD : D.IsEmbedding) (hc : F.Contacts)
    (x : Fin G.edges.length → Bool) (hx : G.VertexEven x) (i : D.SegmentIndex) :
    F.color x (i, false) + F.color x (i, true) = x i.1 := by
  exact rayGermColor_ends F.a F.b (fun i => x i.1) hc.height (F.even x hx) i
    (F.disjoint hD i) (F.remote hD.segment_endpoint_contact) hc.distinct

private theorem Frame.color_bend (F : Frame D) (hc : F.Contacts)
    (x : Fin G.edges.length → Bool) (hx : G.VertexEven x)
    (e : Fin G.edges.length) (i : Fin (D.route e).bends) :
    F.color x (⟨e, i.castSucc⟩, true) + F.color x (⟨e, i.succ⟩, false) = x e := by
  let k : D.SegmentIndex × Bool := (⟨e, i.castSucc⟩, true)
  let l : D.SegmentIndex × Bool := (⟨e, i.succ⟩, false)
  let p := F.u * (D.route e).point i.castSucc.succ
  refine F.color_adjacent hc x hx p k l rfl rfl
    (fun h => Bool.false_ne_true (congrArg Prod.snd h).symm) fun j hj hjk hjl => ?_
  rw [F.endpoint] at hj
  exact ((hc.atBend e i j (mul_left_cancel₀ F.nonzero hj)).elim hjk hjl).elim

private theorem Frame.color_route_ends_of_segment_crossings (F : Frame D)
    (x : Fin G.edges.length → Bool) (e : Fin G.edges.length)
    (crossings : Fin (D.route e).segments → Bool)
    (hsegment : ∀ i, F.color x (⟨e, i⟩, false) + F.color x (⟨e, i⟩, true) =
      x e + crossings i)
    (hbend : ∀ i : Fin (D.route e).bends,
      F.color x (⟨e, i.castSucc⟩, true) + F.color x (⟨e, i.succ⟩, false) = x e) :
    F.color x (D.segmentEnd (e, false)) + F.color x (D.segmentEnd (e, true)) =
      x e + ∑ i, crossings i := by
  let p (i : Fin (D.route e).segments) := F.color x (⟨e, i⟩, false)
  let q (i : Fin (D.route e).segments) := F.color x (⟨e, i⟩, true)
  let n := (D.route e).bends
  have telescope :
      (∑ i : Fin (n + 1), (p i + q i)) + (∑ i : Fin n, (q i.castSucc + p i.succ)) =
        p 0 + q (Fin.last n) := by
    simpa only [BooleanRing.sub_eq_add, add_comm] using
      Fin.sum_univ_adjacent_differences (n := n) p q
  change p 0 + q (Fin.last n) = _
  rw [← telescope, Finset.sum_congr rfl (fun i _ => hsegment i),
    Finset.sum_congr rfl (fun i _ => hbend i), Finset.sum_add_distrib,
    Fin.sum_univ_succ (fun _ : Fin (n + 1) => x e)]
  calc
    _ = (x e + ∑ i, crossings i) + ((∑ _i : Fin n, x e) + ∑ _i : Fin n, x e) := by ac_rfl
    _ = _ := by rw [BooleanRing.add_self, add_zero]

private theorem Frame.color_route_ends (F : Frame D) (hD : D.IsEmbedding) (hc : F.Contacts)
    (x : Fin G.edges.length → Bool) (hx : G.VertexEven x) (e : Fin G.edges.length) :
    F.color x (D.segmentEnd (e, false)) + F.color x (D.segmentEnd (e, true)) = x e := by
  simpa only [Finset.sum_const_zero, add_zero] using
    F.color_route_ends_of_segment_crossings x e (fun _ => 0)
      (fun i => (F.color_ends hD hc x hx ⟨e, i⟩).trans (add_zero _).symm) (F.color_bend hc x hx e)

private theorem Frame.color_vertex (F : Frame D) (hc : F.Contacts)
    {r : RotationSystem G} (hR : D.Realizes r)
    (x : Fin G.edges.length → Bool) (hx : G.VertexEven x)
    (d : Dart G) (hv : d.vertex ∈ G.vertices) :
    F.color x (D.segmentEnd d) + F.color x (D.segmentEnd (r.rotate.symm d)) = x d.1 := by
  classical
  let a := r.rotate.symm d
  let k := D.segmentEnd d
  let l := D.segmentEnd a
  let p := F.u * D.vertex d.vertex
  have har : r.rotate a = d := r.rotate.apply_symm_apply d
  have hav : a.vertex = d.vertex := by rw [← har, r.vertex_rotate]
  have hk : rayEndpoint F.a F.b k = p := by rw [F.endpoint, D.segmentEnd_endpoint]
  have hl : rayEndpoint F.a F.b l = p := by rw [F.endpoint, D.segmentEnd_endpoint, hav]
  have hclass (j : D.SegmentIndex × Bool) (hj : rayEndpoint F.a F.b j = p) :
      ∃ c : Dart G, c.vertex = d.vertex ∧ D.segmentEnd c = j := by
    rw [F.endpoint] at hj
    exact hc.atVertex d.vertex hv j (mul_left_cancel₀ F.nonzero hj)
  by_cases had : a = d
  · have hfixed : r.rotate d = d := had ▸ har
    have hsum : (∑ j : D.SegmentIndex × Bool,
        if rayEndpoint F.a F.b j = p then x j.1.1 else 0) = x d.1 := by
      rw [Finset.sum_eq_single k (fun j _ hj => ite_eq_right fun hp => hj ?_) (by simp)]
      · exact ite_eq_left hk
      · obtain ⟨c, hcv, hcj⟩ := hclass j hp
        exact (((r.sameCycle_iff c d).mpr hcv).eq_of_right hfixed ▸ hcj).symm
    have heven : (∑ j : D.SegmentIndex × Bool,
        if rayEndpoint F.a F.b j = p then x j.1.1 else 0) = 0 := by
      simpa only [Fintype.sum_prod_type, Fintype.sum_bool, rayEndpoint,
        Bool.false_eq_true, ↓reduceIte, add_comm, Bool.zero_eq_false] using F.even x hx p
    change F.color x (D.segmentEnd d) + F.color x (D.segmentEnd a) = x d.1
    rw [had, BooleanRing.add_self, hsum.symm.trans heven]
  · refine F.color_adjacent hc x hx p k l hk hl (fun h => had (D.segmentEnd_injective h.symm))
      fun j hj hjk hjl => ?_
    obtain ⟨c, hcv, rfl⟩ := hclass j hj
    change ¬sbtw ((rayEndVector F.a F.b (D.segmentEnd d)).arg : Real.Angle)
      ((rayEndVector F.a F.b (D.segmentEnd c)).arg : Real.Angle)
      ((rayEndVector F.a F.b (D.segmentEnd a)).arg : Real.Angle)
    simp only [F.vector, D.segmentEnd_vector]
    rw [sbtw_arg_mul_iff F.u (D.germ d) (D.germ c) (D.germ a) F.nonzero
      (hR.nonzero d) (hR.nonzero c) (hR.nonzero a)]
    exact hR.not_sbtw_inverse_rotate d c hcv (fun h => hjk (congrArg D.segmentEnd h))
      (fun h => hjl (congrArg D.segmentEnd h))

open Classical in
private noncomputable def Frame.crossingParity (F : Frame D) (x : Fin G.edges.length → Bool)
    (i : D.SegmentIndex) : Bool :=
  ∑ j, (@ite Bool (j = i) (Classical.propDecidable _) 0 (x j.1)) * decide
    ((openSegment ℝ (F.a j) (F.b j) ∩ openSegment ℝ (F.a i) (F.b i)).Nonempty)

private theorem Frame.color_regular_segment (F : Frame D) (hD : D.HasRegularContacts)
    (hc : F.Contacts) (x : Fin G.edges.length → Bool) (hx : G.VertexEven x) (i : D.SegmentIndex) :
    F.color x (i, false) + F.color x (i, true) = x i.1 + F.crossingParity x i := by
  have hnodes (j : D.SegmentIndex) (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
      AffineMap.lineMap (F.a i) (F.b i) t ≠ F.a j ∧
      AffineMap.lineMap (F.a i) (F.b i) t ≠ F.b j := by
    have hmem := lineMap_mem_openSegment ℝ (D.segmentStart i) (D.segmentFinish i) ht
    obtain ⟨ha, hb⟩ := hD.endpoints_avoid_interiors j i
    rw [F.lineMap]
    exact ⟨fun h => ha (mul_left_cancel₀ F.nonzero h ▸ hmem),
      fun h => hb (mul_left_cancel₀ F.nonzero h ▸ hmem)⟩
  have hcontact (k : D.SegmentIndex × Bool) (j : D.SegmentIndex)
      (hp : rayEndpoint D.segmentStart D.segmentFinish k ∈
        segment ℝ (D.segmentStart j) (D.segmentFinish j)) :
      D.segmentStart j = rayEndpoint D.segmentStart D.segmentFinish k ∨
        D.segmentFinish j = rayEndpoint D.segmentStart D.segmentFinish k := by
    by_contra! h
    have hopen := mem_openSegment_of_ne_left_right h.1 h.2 hp
    rcases k with ⟨k, tag⟩
    cases tag
    · exact (hD.endpoints_avoid_interiors k j).1 hopen
    · exact (hD.endpoints_avoid_interiors k j).2 hopen
  exact rayGermColor_ends_add_eq_crossings F.a F.b (fun j => x j.1) hc.height
    (F.even x hx) i (fun j _ _ => hnodes j)
    (fun j hji _ => F.regular_open_inter hD j i hji)
    (fun side => F.remote hcontact (i, side)) (fun side => hc.distinct (i, side))

private theorem Frame.sum_crossingParity (F : Frame D) (x : Fin G.edges.length → Bool)
    (e : Fin G.edges.length) (hsimple : (D.route e).IsSimple) :
    (∑ i : Fin (D.route e).segments, F.crossingParity x ⟨e, i⟩) =
      ∑ f : Fin G.edges.length, (if f = e then 0 else x f) *
        (D.route f).intersectionParity (D.route e) := by
  classical
  unfold Frame.crossingParity
  simp_rw [F.open_inter, Set.image_nonempty, Fintype.sum_sigma]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases hfe : f = e
  · subst f
    rw [ite_eq_left rfl, zero_mul]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hji : j = i
    · subst j
      simp
    · have hn : ¬(openSegment ℝ (D.segmentStart ⟨e, j⟩) (D.segmentFinish ⟨e, j⟩) ∩
          openSegment ℝ (D.segmentStart ⟨e, i⟩) (D.segmentFinish ⟨e, i⟩)).Nonempty := by
        rintro ⟨z, hj, hi⟩
        rw [openSegment_eq_image_lineMap] at hj hi
        obtain ⟨s, hs, hsz⟩ := hj
        obtain ⟨t, ht, htz⟩ := hi
        exact hji (hsimple.index_time_eq_of_eval_eq_of_mem_Ioo j i hs
          ⟨ht.1.le, ht.2.le⟩ (hsz.trans htz.symm)).1
      simp [hn, ← Bool.zero_eq_false]
  · simp only [Sigma.mk.injEq, hfe, false_and, ↓reduceIte,
      Route.intersectionParity, Finset.mul_sum, segmentStart, segmentFinish]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      congrArg (x f * ·) (Bool.decide_congr Iff.rfl)

open Classical in
/-- A vertex-even edge selection on a regular polygonal drawing with simple routes has
clockwise-side colors on its darts. The sum across a route is its label plus the indexed
crossings with the other selected routes. The sum across an empty vertex sector is the
label of its first ray in counterclockwise order. -/
theorem HasRegularContacts.exists_dart_colors {G : Graph} {D : PolygonalDrawing G}
    (hD : D.HasRegularContacts) (hsimple : ∀ e, (D.route e).IsSimple)
    {r : RotationSystem G} (hR : D.Realizes r)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (x : Fin G.edges.length → Bool) (hx : G.VertexEven x) :
    ∃ color : Dart G → Bool,
      (∀ e, color (e, false) + color (e, true) = x e +
        ∑ f : Fin G.edges.length, (if f = e then 0 else x f) *
          (D.route f).intersectionParity (D.route e)) ∧
      (∀ d, color d + color (r.rotate.symm d) = x d.1) := by
  classical
  obtain ⟨u, hu, hheight⟩ := exists_mul_im_injOn (endpointSet D)
  let F : Frame D := ⟨u, hu, hheight⟩
  have hc := F.contacts_of_regular hD hsimple
  exact ⟨fun d => F.color x (D.segmentEnd d),
    fun e => F.sum_crossingParity x e (hsimple e) ▸ F.color_route_ends_of_segment_crossings x e
      (fun i => F.crossingParity x ⟨e, i⟩) (fun i => F.color_regular_segment hD hc x hx ⟨e, i⟩)
      (F.color_bend hc x hx e),
    fun d => F.color_vertex hc hR x hx d (RotationSystem.vertex_mem hG d)⟩

private theorem faceColors_of_route_and_sector_colors {r : RotationSystem G}
    (x : Fin G.edges.length → Bool) (color : Dart G → Bool)
    (hedge : ∀ e, color (e, false) + color (e, true) = x e)
    (hsector : ∀ d, color d + color (r.rotate.symm d) = x d.1) :
    ∃ q : r.Face → Bool, r.faceBoundary q = x := by
  have edge : ∀ d : Dart G, color d + color d.reverse = x d.1
    | (e, false) => hedge e
    | (e, true) => (add_comm _ _).trans (hedge e)
  refine r.exists_faceColors_of_dartColors x (fun d => color d.reverse) (fun d => ?_) fun d => ?_
  · have step := add_left_cancel ((add_comm _ _).trans ((edge (r.rotate d).reverse).trans
      (hsector (r.rotate d).reverse.reverse).symm))
    simpa only [RotationSystem.faceNext, Dart.reverse_reverse, Equiv.symm_apply_apply] using step
  · rw [Dart.reverse_reverse, ← Bool.add_eq_xor, add_comm]
    exact edge d

/-- In a regular polygonal drawing with simple routes and even crossings between
every distinct edge pair, every vertex-even selection is an actual face boundary
of the clockwise rotation. -/
theorem HasRegularContacts.exists_faceColors_of_pairwise_even_crossings
    {G : Graph} {D : PolygonalDrawing G}
    (hD : D.HasRegularContacts) (hsimple : ∀ e, (D.route e).IsSimple)
    (heven : ∀ e f, e ≠ f → (D.route e).intersectionParity (D.route f) = false)
    {r : RotationSystem G} (hR : D.Realizes r)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (x : Fin G.edges.length → Bool) (hx : G.VertexEven x) :
    ∃ q : r.Face → Bool, r.faceBoundary q = x := by
  classical
  obtain ⟨color, he, hsector⟩ := hD.exists_dart_colors hsimple hR hG x hx
  apply faceColors_of_route_and_sector_colors x color _ hsector
  intro e
  rw [he]
  refine add_eq_left.mpr (Finset.sum_eq_zero fun f _ => ?_)
  by_cases h : f = e
  · simp [h]
  · simp [h, heven f e h, ← Bool.zero_eq_false]

/-- Every vertex-even indexed edge label of an actual polygonal embedding is the
boundary of colors on the actual face quotient of the literally realized clockwise
rotation. The multiplier and all side transport are constructed internally from the
finite real-affine segments. No genus or topological separation hypothesis is used. -/
theorem IsEmbedding.exists_faceColors {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) {r : RotationSystem G} (hR : D.Realizes r)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (x : Fin G.edges.length → Bool) (hx : G.VertexEven x) :
    ∃ q : r.Face → Bool, r.faceBoundary q = x := by
  classical
  obtain ⟨u, hu, hheight⟩ := exists_mul_im_injOn (endpointSet D)
  let F : Frame D := ⟨u, hu, hheight⟩
  have hc := F.contacts_of_embedding hD
  let color (d : Dart G) : Bool := F.color x (D.segmentEnd d)
  exact faceColors_of_route_and_sector_colors x color (F.color_route_ends hD hc x hx)
    (fun d => F.color_vertex hc hR x hx d (RotationSystem.vertex_mem hG d))

end Cslib.Complexity.Graph.PolygonalDrawing
