/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RegularContacts
public import CslibFrontier.Foundations.Geometry.Polygonal.RouteIntersectionParity
import CslibFrontier.Foundations.Geometry.FiniteLineAvoidance
import CslibFrontier.Foundations.Geometry.Polygonal.CrossingSplice
import CslibFrontier.Foundations.Geometry.Polygonal.Germs
import Mathlib.Logic.Embedding.Basic

/-!
# Smoothing one crossing of a polygonal graph drawing

The splice of a self-crossing stays away from every other edge. At an exterior
point, the open segment occurrences in the new drawing embed into the original
occurrences with their supporting affine spans preserved. In the splice disk
there is at most one open occurrence through any point. This is original finite geometry.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal

private abbrev RouteThrough (p : Route) (w : ℂ) :=
  {k : Fin p.segments // w ∈ openSegment ℝ (p.point k.castSucc) (p.point k.succ)}

private abbrev DrawingThrough {G : Graph} (D : PolygonalDrawing G) (w : ℂ) :=
  (f : Fin G.edges.length) × RouteThrough (D.route f) w

private noncomputable abbrev segmentSpan (p : Route) (k : Fin p.segments) :=
  affineSpan ℝ ({p.point k.castSucc, p.point k.succ} : Set ℂ)

private def throughIndex {G : Graph} (D : PolygonalDrawing G) (w : ℂ) :
    DrawingThrough D w ↪ D.SegmentIndex :=
  (Function.Embedding.refl _).sigmaMap fun _ => Function.Embedding.subtype _

/-- Smooth a given self-crossing while retaining regular contacts throughout the drawing.
The crossing point is removed, the other routes stay fixed, and the modified route preserves
its two outgoing directions and its crossing parity against every other edge. -/
theorem HasRegularContacts.exists_regular_splice {G : Graph}
    {D : PolygonalDrawing G} (hD : D.HasRegularContacts) (e : Fin G.edges.length)
    (i j : Fin (D.route e).segments) (hij : i < j) {z : ℂ}
    (hi : z ∈ openSegment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ))
    (hj : z ∈ openSegment ℝ ((D.route e).point j.castSucc) ((D.route e).point j.succ)) :
    ∃ E : PolygonalDrawing G,
      E.vertex = D.vertex ∧ (∀ f ≠ e, E.route f = D.route f) ∧
      (∀ b, ∃ c : ℝ, 0 < c ∧ (E.route e).germ b = c • (D.route e).germ b) ∧
      (∀ f ≠ e, (E.route e).intersectionParity (E.route f) =
        (D.route e).intersectionParity (D.route f)) ∧
      openSegmentCrossings E.segmentStart E.segmentFinish ⊆
        openSegmentCrossings D.segmentStart D.segmentFinish \ {z} ∧
      E.HasRegularContacts := by
  classical
  let a : D.SegmentIndex := ⟨e, i⟩
  let b : D.SegmentIndex := ⟨e, j⟩
  have hab : a ≠ b := fun h => hij.ne (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  have hz : z ∈ openSegmentCrossings D.segmentStart D.segmentFinish := ⟨a, b, hab, hi, hj⟩
  obtain ⟨_, ρ, hpos, _, hvertices, hends, hlocal⟩ := hD.exists_crossing_neighborhoods
  let B := Metric.closedBall z (ρ z)
  have hB : z ∈ B := Metric.mem_closedBall_self (hpos z hz).le
  have hnodes (n : Fin ((D.route e).segments + 1)) : (D.route e).point n ∉ B := by
    refine Fin.lastCases ?_ (fun k => (hends z hz ⟨e, k⟩).1) n
    simpa only [segmentFinish, Fin.succ_last] using (hends z hz ⟨e, Fin.last (D.route e).bends⟩).2
  have hpair := segment_inter_subsingleton_of_affineSpan_ne
    (hD.lines_ne_at_intersections a b hab z hi hj)
  have hpieces (k : Fin (D.route e).segments) (hki : k ≠ i) (hkj : k ≠ j) :
      Disjoint (segment ℝ ((D.route e).point k.castSucc) ((D.route e).point k.succ)) B :=
    (hlocal a b hab z hi hj ⟨e, k⟩
      (fun h => hki (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
      (fun h => hkj (eq_of_heq (Sigma.mk.inj_iff.mp h).2))).symm
  have hsupport (f : Fin G.edges.length) (hf : f ≠ e) : Disjoint B (D.route f).support := by
    apply Set.disjoint_left.mpr
    intro w hw hs
    obtain ⟨k, u, hu, rfl⟩ := ((D.route f).mem_support_iff w).mp hs
    have hne : ∀ c : Fin (D.route e).segments, (⟨f, k⟩ : D.SegmentIndex) ≠ ⟨e, c⟩ :=
      fun _ h => hf (congrArg Sigma.fst h)
    exact Set.disjoint_left.mp (hlocal a b hab z hi hj ⟨f, k⟩ (hne i) (hne j))
      hw (lineMap_mem_segment ℝ _ _ hu)
  obtain ⟨q, hstart, hfinish, _, _, hparity, hgerms, hsub, _, hcontacts, _,
    hvisit, hpoints, havoid, hopen, _⟩ :=
    (D.route e).exists_splice_of_isolated_crossing i j hij (hpos z hz) hi hj hpair hnodes hpieces
  have hqend (side : Bool) : q.endpoint side = (D.route e).endpoint side := by
    cases side
    · exact hstart
    · exact hfinish
  let E : PolygonalDrawing G := {
    vertex := D.vertex
    route := Function.update D.route e q
    endpoint_eq := by
      intro f side
      by_cases hf : f = e
      · subst f
        rw [Function.update_self, ← D.endpoint_eq]
        exact hqend side
      · rw [Function.update_of_ne hf, D.endpoint_eq] }
  have he : E.route e = q := Function.update_self e q D.route
  have he' (f : Fin G.edges.length) (hf : f ≠ e) : E.route f = D.route f :=
    Function.update_of_ne hf q D.route
  have hside (f : Fin G.edges.length) {w : ℂ} (hw : w ∈ B)
      (hm : w ∈ (E.route f).support) : f = e := by
    by_contra hn
    exact Set.disjoint_left.mp (hsupport f hn) hw (he' f hn ▸ hm)
  have hinside (w : ℂ) (hw : w ∈ B) : Subsingleton (DrawingThrough E w) := by
    have hedge (x : DrawingThrough E w) : x.1 = e :=
      hside x.1 hw (Set.mem_iUnion.mpr
        ⟨x.2.val, openSegment_subset_segment ℝ _ _ x.2.property⟩)
    have hq : Subsingleton (RouteThrough q w) := ⟨by
      intro k l
      apply Subtype.ext
      by_contra hne
      exact (hsub ⟨k.val, l.val, hne, k.property, l.property⟩).2 hw⟩
    have hE : Subsingleton (RouteThrough (E.route e) w) := by rwa [he]
    refine ⟨?_⟩
    rintro ⟨f, k⟩ ⟨g, l⟩
    have hf := hedge ⟨f, k⟩
    have hg := hedge ⟨g, l⟩
    change f = e at hf
    change g = e at hg
    subst f
    subst g
    exact congrArg (Sigma.mk e) (hE.elim k l)
  have houtside (w : ℂ) (hw : w ∉ B) :
      ∃ F : DrawingThrough E w ↪ DrawingThrough D w,
        ∀ x, segmentSpan (E.route x.1) x.2.val = segmentSpan (D.route (F x).1) (F x).2.val := by
    have hf (f : Fin G.edges.length) :
        ∃ g : RouteThrough (E.route f) w ↪ RouteThrough (D.route f) w,
          ∀ k, segmentSpan (E.route f) k.val = segmentSpan (D.route f) (g k).val := by
      by_cases hfe : f = e
      · subst f
        rw [he]
        exact hopen w hw
      · rw [he' f hfe]
        exact ⟨Function.Embedding.refl _, fun _ => rfl⟩
    choose g hg using hf
    exact ⟨(Function.Embedding.refl _).sigmaMap g, fun x => hg x.1 x.2⟩
  have hpair_at (a b : E.SegmentIndex) (hab : a ≠ b) (w : ℂ)
      (ha : w ∈ openSegment ℝ (E.segmentStart a) (E.segmentFinish a))
      (hb : w ∈ openSegment ℝ (E.segmentStart b) (E.segmentFinish b)) : w ∉ B := by
    intro hw
    let a' : DrawingThrough E w := ⟨a.1, ⟨a.2, ha⟩⟩
    let b' : DrawingThrough E w := ⟨b.1, ⟨b.2, hb⟩⟩
    exact hab (congrArg (throughIndex E w) ((hinside w hw).elim a' b'))
  have htrace (f : Fin G.edges.length) :
      ∀ (k : Fin (E.route f).segments) {t : ℝ}, t ∈ Set.Icc 0 1 →
        (E.route f).eval k t ∉ B →
        ∃ (l : Fin (D.route f).segments) (u : ℝ), u ∈ Set.Icc 0 1 ∧
          (D.route f).eval l u = (E.route f).eval k t ∧ (t ∈ Set.Ioo 0 1 ↔ u ∈ Set.Ioo 0 1) := by
    by_cases hf : f = e
    · subst f
      rw [he]
      exact hvisit
    · rw [he' f hf]
      exact fun k t ht _ => ⟨k, t, ht, rfl, Iff.rfl⟩
  have hqvertex (k : Fin q.segments) (s : ℝ) (hs : s ∈ Set.Icc 0 1)
      (v : ℕ) (hv : v ∈ G.vertices) (hsV : q.eval k s = D.vertex v) :
      ∃ b, q.AtEnd k s b ∧ Dart.vertex (e, b) = v := by
    have hw : q.eval k s ∉ B := hsV.symm ▸ hvertices z hz v hv
    obtain ⟨a, t, ht, ha, _⟩ := hvisit k hs hw
    obtain ⟨b, _, hbV⟩ := hD.vertex_contacts e a t ht v hv (ha.trans hsV)
    refine ⟨b, ?_, hbV⟩
    by_contra hn
    have hEval : q.eval (q.endSegment b) (Route.endTime b 0) = D.vertex v := by
      rw [q.eval_near_end, zero_smul, add_zero, hqend, D.endpoint_eq, hbV]
    have hPos : q.position k s ≠ q.position (q.endSegment b) (Route.endTime b 0) := by
      rw [q.position_near_end, sub_zero]
      exact hn
    obtain ⟨a₀, a₁, t₀, t₁, ht₀, ht₁, h₀, h₁, hne, _, _⟩ :=
      hcontacts k (q.endSegment b) hs (Route.endTime_mem b ⟨le_rfl, zero_le_one⟩)
        hw (hsV.trans hEval.symm) hPos
    obtain ⟨b₀, hb₀, hV₀⟩ := hD.vertex_contacts e a₀ t₀ ht₀ v hv (h₀.trans hsV)
    obtain ⟨b₁, hb₁, hV₁⟩ := hD.vertex_contacts e a₁ t₁ ht₁ v hv (h₁.trans hEval)
    have hend : (D.route e).endpoint b₀ = (D.route e).endpoint b₁ := by
      rw [D.endpoint_eq, D.endpoint_eq, hV₀, hV₁]
    have hneEnds : (D.route e).start ≠ (D.route e).finish := by
      intro h
      have hh := congrArg Fin.val (hD.points_injective e h)
      simp only [Fin.val_zero, Fin.val_last, Route.segments] at hh
      omega
    have hbool : b₀ = b₁ := by
      cases b₀ <;> cases b₁
      · rfl
      · exact (hneEnds hend).elim
      · exact (hneEnds hend.symm).elim
      · rfl
    subst b₁
    exact hne (hb₀.trans hb₁.symm)
  have hqAvoid (n : Fin (q.segments + 1)) (k : Fin q.segments) :
      q.point n ∉ openSegment ℝ (q.point k.castSucc) (q.point k.succ) := by
    apply havoid _ n k
    intro a l
    refine Fin.lastCases ?_ (fun c => (hD.endpoints_avoid_interiors ⟨e, c⟩ ⟨e, l⟩).1) a
    simpa only [segmentStart, segmentFinish, Route.segments, Fin.succ_last] using
      (hD.endpoints_avoid_interiors ⟨e, Fin.last (D.route e).bends⟩ ⟨e, l⟩).2
  have hqMixed :
      ∀ (k l : Fin (E.route e).segments) {s t : ℝ}, s ∈ ({0, 1} : Set ℝ) →
        t ∈ Set.Ioo 0 1 → (E.route e).eval k s ≠ (E.route e).eval l t := by
    rw [he]
    intro k l s t hs ht h
    have hm : q.eval k s ∈ openSegment ℝ (q.point l.castSucc) (q.point l.succ) :=
      h.symm ▸ lineMap_mem_openSegment ℝ _ _ ht
    rcases Set.mem_insert_iff.mp hs with rfl | hs'
    · exact hqAvoid k.castSucc l (by simpa only [Route.eval, AffineMap.lineMap_apply_zero] using hm)
    · rw [Set.mem_singleton_iff] at hs'
      subst s
      exact hqAvoid k.succ l (by simpa only [Route.eval, AffineMap.lineMap_apply_one] using hm)
  have hMixed (f g : Fin G.edges.length) (k : Fin (E.route f).segments)
      (l : Fin (E.route g).segments) {s t : ℝ} (hs : s ∈ ({0, 1} : Set ℝ))
      (ht : t ∈ Set.Ioo 0 1) (h : (E.route f).eval k s = (E.route g).eval l t) : False := by
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 \ Set.Ioo 0 1 := by
      rwa [Set.Icc_sdiff_Ioo_same zero_le_one]
    have ht' := Set.Ioo_subset_Icc_self ht
    by_cases hw : (E.route f).eval k s ∈ B
    · have hf := hside f hw ((E.route f).at_mem_support k hs'.1)
      have hg := hside g (h ▸ hw) ((E.route g).at_mem_support l ht')
      subst f
      subst g
      exact hqMixed k l hs ht h
    · obtain ⟨a, u, hu, ha, hsu⟩ := htrace f k hs'.1 hw
      obtain ⟨b, v, _, hb, htv⟩ := htrace g l ht' (h ▸ hw)
      have hu' : u ∈ ({0, 1} : Set ℝ) := by
        rw [← Set.Icc_sdiff_Ioo_same zero_le_one]
        exact ⟨hu, fun hv => hs'.2 (hsu.mpr hv)⟩
      have hm : (D.route f).eval a u ∈ openSegment ℝ
          (D.segmentStart ⟨g, b⟩) (D.segmentFinish ⟨g, b⟩) := by
        rw [ha, h, ← hb]
        exact lineMap_mem_openSegment ℝ _ _ (htv.mp ht)
      rcases Set.mem_insert_iff.mp hu' with rfl | hu'
      · exact (hD.endpoints_avoid_interiors ⟨f, a⟩ ⟨g, b⟩).1
          (by simpa only [segmentStart, Route.eval, AffineMap.lineMap_apply_zero] using hm)
      · rw [Set.mem_singleton_iff] at hu'
        subst u
        exact (hD.endpoints_avoid_interiors ⟨f, a⟩ ⟨g, b⟩).2
          (by simpa only [segmentFinish, Route.eval, AffineMap.lineMap_apply_one] using hm)
  refine ⟨E, rfl, he', ?_, ?_, ?_, ?_⟩
  · rw [he]
    exact hgerms
  · intro f hf
    rw [he, he' f hf]
    exact hparity _ (hsupport f hf)
  · rintro w ⟨a, b, hab, ha, hb⟩
    have hw := hpair_at a b hab w ha hb
    obtain ⟨F, _⟩ := houtside w hw
    let a' : DrawingThrough E w := ⟨a.1, ⟨a.2, ha⟩⟩
    let b' : DrawingThrough E w := ⟨b.1, ⟨b.2, hb⟩⟩
    have hab' : a' ≠ b' := fun h => hab (congrArg (throughIndex E w) h)
    refine ⟨⟨throughIndex D w (F a'), throughIndex D w (F b'),
      (throughIndex D w).injective.ne (F.injective.ne hab'), (F a').2.property,
      (F b').2.property⟩, ?_⟩
    exact fun hz' => hw ((Set.mem_singleton_iff.mp hz').symm ▸ hB)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    by_cases hf : f = e
    · subst f
      rw [he]
      exact hpoints (hD.points_injective e)
    · rw [he' f hf]
      exact hD.points_injective f
  · intro f
    by_cases hf : f = e
    · subst f
      rw [he]
      exact hqvertex
    · rw [he' f hf]
      exact hD.vertex_contacts f
  · intro a b
    constructor <;> intro h <;> rw [openSegment_eq_image_lineMap] at h <;>
      obtain ⟨t, ht, heq⟩ := h
    · exact hMixed a.1 b.1 a.2 b.2 (Or.inl rfl) ht
        (by simpa only [Route.eval, AffineMap.lineMap_apply_zero, segmentStart, segmentFinish]
          using heq.symm)
    · exact hMixed a.1 b.1 a.2 b.2 (Or.inr rfl) ht
        (by simpa only [Route.eval, AffineMap.lineMap_apply_one, segmentStart, segmentFinish]
          using heq.symm)
  · intro a b hab w ha hb
    obtain ⟨F, hF⟩ := houtside w (hpair_at a b hab w ha hb)
    let a' : DrawingThrough E w := ⟨a.1, ⟨a.2, ha⟩⟩
    let b' : DrawingThrough E w := ⟨b.1, ⟨b.2, hb⟩⟩
    have hab' : a' ≠ b' := fun h => hab (congrArg (throughIndex E w) h)
    change segmentSpan (E.route a'.1) a'.2.val ≠ segmentSpan (E.route b'.1) b'.2.val
    rw [hF a', hF b']
    exact hD.lines_ne_at_intersections (throughIndex D w (F a')) (throughIndex D w (F b'))
      ((throughIndex D w).injective.ne (F.injective.ne hab')) w
      (F a').2.property (F b').2.property
  · intro f w hf
    let g : Fin 3 ↪ DrawingThrough E w :=
      ⟨fun k => ⟨(f k).1, ⟨(f k).2, hf k⟩⟩, fun _ _ h =>
        f.injective (congrArg (throughIndex E w) h)⟩
    by_cases hw : w ∈ B
    · exact (by decide : (0 : Fin 3) ≠ 1) (g.injective ((hinside w hw).elim (g 0) (g 1)))
    · obtain ⟨F, _⟩ := houtside w hw
      exact hD.no_open_triple ((g.trans F).trans (throughIndex D w)) w
        (fun k => (F (g k)).2.property)
  · intro a b hab s t hs ht h
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 \ Set.Ioo 0 1 := by
      rwa [Set.Icc_sdiff_Ioo_same zero_le_one]
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 \ Set.Ioo 0 1 := by
      rwa [Set.Icc_sdiff_Ioo_same zero_le_one]
    have hw : (E.route a.1).eval a.2 s ∉ B := by
      intro hw
      exact hab ((hside a.1 hw ((E.route a.1).at_mem_support a.2 hs'.1)).trans
        (hside b.1 (h ▸ hw) ((E.route b.1).at_mem_support b.2 ht'.1)).symm)
    obtain ⟨a', s', hsa, heA, hclassA⟩ := htrace a.1 a.2 hs'.1 hw
    obtain ⟨b', t', htb, heB, hclassB⟩ := htrace b.1 b.2 ht'.1 (h ▸ hw)
    have hs'' : s' ∈ ({0, 1} : Set ℝ) := by
      rw [← Set.Icc_sdiff_Ioo_same zero_le_one]
      exact ⟨hsa, fun h => hs'.2 (hclassA.mpr h)⟩
    have ht'' : t' ∈ ({0, 1} : Set ℝ) := by
      rw [← Set.Icc_sdiff_Ioo_same zero_le_one]
      exact ⟨htb, fun h => ht'.2 (hclassB.mpr h)⟩
    have hOld := hD.shared_ends_are_vertices ⟨a.1, a'⟩ ⟨b.1, b'⟩ hab
      hs'' ht'' (heA.trans (h.trans heB.symm))
    exact heA ▸ hOld

end Cslib.Complexity.Graph.PolygonalDrawing
