/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary-import tests for drawings with crossings)

import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.IntersectionParity
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Equality
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Equivalence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Two vertices joined by a straight edge and a zigzag with one or two open crossings. -/

set_option linter.privateModule false

namespace CslibFrontierTests.PolygonalCrossingColors

open Cslib.Complexity Cslib.Complexity.Graph Cslib.Complexity.Graph.PolygonalDrawing
open Cslib.Polygonal

private abbrev G : Graph := ⟨[0, 1], [(0, 1), (0, 1)]⟩
private abbrev left : ℂ := ⟨0, 0⟩
private abbrev right : ℂ := ⟨4, 0⟩
private abbrev straight : Route := Route.line left right
private abbrev zig (odd : Bool) : Route :=
  ⟨3, ![left, ⟨1, 1⟩, ⟨2, if odd then 2 else -1⟩, ⟨3, if odd then -1 else 1⟩, right]⟩

private abbrev drawing (odd : Bool) : PolygonalDrawing G where
  vertex v := if v = 0 then left else right
  route e := if e = 0 then straight else zig odd
  endpoint_eq e b := by
    fin_cases e <;> cases b <;> rfl

private theorem line_re (t : ℝ) : (straight.eval 0 t).re = 4 * t := by
  change ((AffineMap.lineMap left right) t).re = _
  norm_num [AffineMap.lineMap_apply_module']; ring

private theorem line_im (t : ℝ) : (straight.eval 0 t).im = 0 := by
  change ((AffineMap.lineMap left right) t).im = 0
  norm_num [AffineMap.lineMap_apply_module']

private theorem zig_re (odd : Bool) (i : Fin (zig odd).segments) (t : ℝ) :
    ((zig odd).eval i t).re = (i.val : ℝ) + t := by
  cases odd <;> fin_cases i <;>
    norm_num [zig, Route.eval, AffineMap.lineMap_apply_module'] <;> ring

private theorem simple (odd : Bool) (e : Fin G.edges.length) :
    ((drawing odd).route e).IsSimple := by
  fin_cases e
  · intro i j s t _ _ h
    have hi : i = 0 := Subsingleton.elim (α := Fin 1) _ _
    have hj : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    subst i
    subst j
    have h' := congrArg Complex.re h
    change (straight.eval 0 s).re = (straight.eval 0 t).re at h'
    rw [line_re, line_re] at h'
    exact Or.inl (congrArg (straight.position 0) (by linarith))
  · intro i j s t _ _ h
    have h' := congrArg Complex.re h
    change ((zig odd).eval i s).re = ((zig odd).eval j t).re at h'
    rw [zig_re, zig_re] at h'
    exact Or.inl h'

private theorem vertex_contact (odd : Bool) (e : Fin G.edges.length)
    (i : Fin ((drawing odd).route e).segments) (t : ℝ) (_ : t ∈ Set.Icc 0 1)
    (v : ℕ) (hv : v ∈ G.vertices) (he : ((drawing odd).route e).eval i t = (drawing odd).vertex v) :
    ∃ b, ((drawing odd).route e).AtEnd i t b ∧ Dart.vertex (e, b) = v := by
  have hv' : v = 0 ∨ v = 1 := by simpa [G] using hv
  have hr := congrArg Complex.re he
  fin_cases e
  · have hi : i = 0 := Subsingleton.elim (α := Fin 1) _ _
    subst i
    rcases hv' with rfl | rfl
    · change (straight.eval 0 t).re = 0 at hr
      rw [line_re] at hr
      refine ⟨false, ?_, rfl⟩
      change straight.AtEnd 0 t false
      have he : t = 0 := by linarith
      norm_num [Route.AtEnd, Route.position, he]
    · change (straight.eval 0 t).re = 4 at hr
      rw [line_re] at hr
      refine ⟨true, ?_, rfl⟩
      change straight.AtEnd 0 t true
      have he : t = 1 := by linarith
      norm_num [Route.AtEnd, Route.position, Route.line, he]
  · rcases hv' with rfl | rfl
    · change ((zig odd).eval i t).re = 0 at hr
      rw [zig_re] at hr
      exact ⟨false, hr, rfl⟩
    · change ((zig odd).eval i t).re = 4 at hr
      rw [zig_re] at hr
      refine ⟨true, ?_, rfl⟩
      change (zig odd).AtEnd i t true
      change (i.val : ℝ) + t = ((4 : ℕ) : ℝ)
      exact hr.trans (by norm_num)

private theorem point_injective (odd : Bool) (e : Fin G.edges.length) :
    Function.Injective ((drawing odd).route e).point := by
  intro i j h
  have re := congrArg Complex.re h
  fin_cases e
  · change (straight.point i).re = (straight.point j).re at re
    fin_cases i <;> fin_cases j
    · rfl
    · change (0 : ℝ) = 4 at re
      norm_num at re
    · change (4 : ℝ) = 0 at re
      norm_num at re
    · rfl
  · change ((zig odd).point i).re = ((zig odd).point j).re at re
    have x (k : Fin 5) : ((zig odd).point k).re = (k.val : ℝ) := by
      cases odd <;> fin_cases k <;> norm_num [zig]
    rw [x i, x j] at re
    exact Fin.ext (by exact_mod_cast re)

private theorem same_edge_open_disjoint (odd : Bool) (i j : (drawing odd).SegmentIndex)
    (he : i.1 = j.1) (hn : i ≠ j) {p : ℂ}
    (hp : p ∈ openSegment ℝ ((drawing odd).segmentStart i) ((drawing odd).segmentFinish i))
    (hq : p ∈ openSegment ℝ ((drawing odd).segmentStart j) ((drawing odd).segmentFinish j)) :
    False := by
  rcases i with ⟨e, i⟩
  rcases j with ⟨f, j⟩
  change e = f at he
  subst f
  rw [openSegment_eq_image_lineMap] at hp hq
  obtain ⟨s, hs, hs'⟩ := hp
  obtain ⟨t, ht, ht'⟩ := hq
  exact hn (by rw [((simple odd e).index_time_eq_of_eval_eq_of_mem_Ioo i j hs
    ⟨ht.1.le, ht.2.le⟩ (hs'.trans ht'.symm)).1])

private theorem avoids (odd : Bool) (i j : (drawing odd).SegmentIndex) (b : Bool) :
    ((drawing odd).route i.1).eval i.2 (if b then 1 else 0) ∉
      openSegment ℝ ((drawing odd).segmentStart j) ((drawing odd).segmentFinish j) := by
  rcases i with ⟨e, i⟩
  rcases j with ⟨f, j⟩
  intro h
  rw [openSegment_eq_image_lineMap] at h
  obtain ⟨t, ht, he⟩ := h
  by_cases hef : e = f
  · subst f
    have htime : (if b then (1 : ℝ) else 0) ∈ Set.Icc 0 1 := by cases b <;> simp
    have h' := ((simple odd e).index_time_eq_of_eval_eq_of_mem_Ioo j i ht htime he).2
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h' <;> linarith [ht.1, ht.2]
  have hr := congrArg Complex.re he
  have hm := congrArg Complex.im he
  have hreg0 : ¬(e = 0 ∧ f = 0) := fun h => hef (h.1.trans h.2.symm)
  have hreg1 : ¬(e = 1 ∧ f = 1) := fun h => hef (h.1.trans h.2.symm)
  fin_cases e <;> fin_cases f
  · exact hreg0 ⟨rfl, rfl⟩
  · have hi : i = 0 := Subsingleton.elim (α := Fin 1) _ _
    subst i
    have hrt : ((zig odd).eval j t).re = (straight.eval 0 (if b then 1 else 0)).re := hr
    rw [zig_re, line_re] at hrt
    have hj := j.isLt
    have hlo := Nat.cast_nonneg (α := ℝ) j.val
    have hhi : (j.val : ℝ) + 1 ≤ 4 := by exact_mod_cast hj
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrt <;>
      linarith [ht.1, ht.2]
  · have hj : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    subst j
    change (straight.eval 0 t).im = ((zig odd).eval i (if b then 1 else 0)).im at hm
    change (straight.eval 0 t).re = ((zig odd).eval i (if b then 1 else 0)).re at hr
    rw [line_im] at hm
    rw [line_re, zig_re] at hr
    cases odd <;> cases b <;> fin_cases i
    all_goals norm_num [zig, Route.eval, AffineMap.lineMap_apply_module'] at hm
    all_goals norm_num at hr
    all_goals linarith [ht.1, ht.2]
  · exact hreg1 ⟨rfl, rfl⟩

private theorem supporting_lines_ne (odd : Bool) (j : Fin (zig odd).segments) :
    affineSpan ℝ ({left, right} : Set ℂ) ≠
      affineSpan ℝ ({(zig odd).point j.castSucc, (zig odd).point j.succ} : Set ℂ) := by
  intro h
  have onLine {p : ℂ} (hp : p ∈ affineSpan ℝ ({left, right} : Set ℂ)) : p.im = 0 := by
    obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hp
    exact line_im t
  have h₀ := onLine (h ▸ left_mem_affineSpan_pair ℝ ((zig odd).point j.castSucc)
    ((zig odd).point j.succ))
  have h₁ := onLine (h ▸ right_mem_affineSpan_pair ℝ ((zig odd).point j.castSucc)
    ((zig odd).point j.succ))
  cases odd <;> fin_cases j
  all_goals norm_num [zig] at h₀
  all_goals norm_num [zig] at h₁

private theorem shared (odd : Bool) : (drawing odd).SharedSegmentEndsAreVertices := by
  intro i j hne s t hs ht he
  rcases i with ⟨e, i⟩
  rcases j with ⟨f, j⟩
  change e ≠ f at hne
  fin_cases e <;> fin_cases f
  · exact (hne rfl).elim
  · have hi : i = 0 := Subsingleton.elim (α := Fin 1) _ _
    subst i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact ⟨0, by decide, (AffineMap.lineMap_apply_zero left right).symm⟩
    · exact ⟨1, by decide, (AffineMap.lineMap_apply_one left right).symm⟩
  · have hj : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    subst j
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact ⟨0, by decide, (he.trans (AffineMap.lineMap_apply_zero left right)).symm⟩
    · exact ⟨1, by decide, (he.trans (AffineMap.lineMap_apply_one left right)).symm⟩
  · exact (hne rfl).elim

private theorem regular (odd : Bool) : (drawing odd).HasRegularContacts where
  points_injective := point_injective odd
  vertex_contacts := vertex_contact odd
  endpoints_avoid_interiors i j := by
    have ha := avoids odd i j false
    have hb := avoids odd i j true
    rw [← (drawing odd).segment_endpoint_eq_eval i false] at ha
    rw [← (drawing odd).segment_endpoint_eq_eval i true] at hb
    exact ⟨ha, hb⟩
  lines_ne_at_intersections i j hn _ hp hq := by
    by_cases h : i.1 = j.1
    · exact (same_edge_open_disjoint odd i j h hn hp hq).elim
    · rcases i with ⟨e, i⟩
      rcases j with ⟨f, j⟩
      change e ≠ f at h
      fin_cases e <;> fin_cases f
      · exact (h rfl).elim
      · have hi : i = 0 := Subsingleton.elim (α := Fin 1) _ _
        subst i
        exact supporting_lines_ne odd j
      · have hj : j = 0 := Subsingleton.elim (α := Fin 1) _ _
        subst j
        exact (supporting_lines_ne odd i).symm
      · exact (h rfl).elim
  no_open_triple f _ h := by
    have hp : ∀ g : Fin 3 → Fin 2, ∃ i j, i ≠ j ∧ g i = g j := by decide
    obtain ⟨i, j, hn, he⟩ := hp (fun i => (f i).1)
    exact same_edge_open_disjoint odd (f i) (f j) he (f.injective.ne hn) (h i) (h j)
  shared_ends_are_vertices := shared odd

private def rotation : RotationSystem G where
  rotate := Equiv.swap (0, false) (1, false) * Equiv.swap (0, true) (1, true)
  sameCycle_iff := by decide

private theorem realizes (odd : Bool) : (drawing odd).Realizes rotation where
  nonzero d := (simple odd d.1).germ_ne_zero d.2
  directions_injective a b hv he := by
    let D := drawing odd
    apply D.segmentEnd_injective
    apply rayEndVector_injective_of_open_inter_subsingleton D.segmentStart D.segmentFinish
      (fun i => (simple odd i.1).segment_ne i.2) (regular odd).open_inter_subsingleton
    · rw [D.segmentEnd_endpoint, D.segmentEnd_endpoint, hv]
    · rw [D.segmentEnd_vector, D.segmentEnd_vector]
      have harg : (D.germ a).arg = (D.germ b).arg := Complex.arg_coe_angle_eq_iff.mp he
      have hsign : (D.germ a).im < 0 ↔ (D.germ b).im < 0 := by
        rw [← Complex.arg_neg_iff, ← Complex.arg_neg_iff, harg]
      by_cases h : (D.germ b).im < 0
      · simp only [turnArg, h, hsign.mpr h, harg, ↓reduceIte]
      · simp only [turnArg, h, mt hsign.mp h, harg, ↓reduceIte]
  clockwise a b c hab hbc hneab hnebc hneac := by
    have tags : ∀ a b : Fin 2 × Bool,
        Dart.vertex (G := G) a = Dart.vertex (G := G) b → a.2 = b.2 := by decide
    have h : ∀ i j k : Fin 2, i ≠ j → j ≠ k → i ≠ k → False := by decide
    exact (h a.1 b.1 c.1
      (fun he => hneab (Prod.ext he (tags a b hab)))
      (fun he => hnebc (Prod.ext he (tags b c hbc)))
      (fun he => hneac (Prod.ext he (tags a b hab |>.trans (tags b c hbc))))).elim

private theorem line_open (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 4) :
    (⟨x, 0⟩ : ℂ) ∈ openSegment ℝ left right := by
  rw [openSegment_eq_image_lineMap]
  refine ⟨x / 4, ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
  apply Complex.ext
  · change (straight.eval 0 (x / 4)).re = x
    rw [line_re]
    ring
  · exact line_im _

private theorem cross_at (odd : Bool) (j : Fin (zig odd).segments) (t : ℝ)
    (ht : t ∈ Set.Ioo 0 1) (hi : ((zig odd).eval j t).im = 0) :
    (openSegment ℝ left right ∩
      openSegment ℝ ((zig odd).point j.castSucc) ((zig odd).point j.succ)).Nonempty := by
  have hj : (j.val : ℝ) + 1 ≤ 4 := by exact_mod_cast j.isLt
  have hj0 := Nat.cast_nonneg (α := ℝ) j.val
  have hx : ((zig odd).eval j t).re ∈ Set.Ioo (0 : ℝ) 4 := by
    rw [zig_re]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hz : (⟨((zig odd).eval j t).re, 0⟩ : ℂ) = (zig odd).eval j t :=
    Complex.ext rfl hi.symm
  have hm : (zig odd).eval j t ∈ openSegment ℝ left right := hz ▸ line_open _ hx
  exact ⟨_, hm, lineMap_mem_openSegment ℝ _ _ ht⟩

private theorem hit_iff (odd : Bool) (j : Fin (zig odd).segments) :
    (openSegment ℝ left right ∩
      openSegment ℝ ((zig odd).point j.castSucc) ((zig odd).point j.succ)).Nonempty ↔
      j = 2 ∨ (odd = false ∧ j = 1) := by
  constructor
  · rintro ⟨z, ha, hb⟩
    rw [openSegment_eq_image_lineMap] at ha hb
    obtain ⟨s, _, he⟩ := ha
    obtain ⟨t, ht, hf⟩ := hb
    have hi : ((zig odd).eval j t).im = 0 :=
      (congrArg Complex.im (hf.trans he.symm)).trans (line_im s)
    cases odd <;> fin_cases j
    all_goals try exact Or.inl rfl
    all_goals try exact Or.inr ⟨rfl, rfl⟩
    all_goals norm_num [zig, Route.eval, AffineMap.lineMap_apply_module'] at hi
    all_goals linarith [ht.1, ht.2]
  · cases odd
    · rintro (rfl | ⟨_, rfl⟩)
      · exact cross_at false 2 (1 / 2) (by norm_num)
          (by norm_num [zig, Route.eval, AffineMap.lineMap_apply_module'])
      · exact cross_at false 1 (1 / 2) (by norm_num)
          (by norm_num [zig, Route.eval, AffineMap.lineMap_apply_module'])
    · rintro (rfl | ⟨hh, _⟩)
      · exact cross_at true 2 (2 / 3) (by norm_num)
          (by norm_num [zig, Route.eval, AffineMap.lineMap_apply_module'])
      · cases hh

private theorem crossing_parity (odd : Bool) :
    (straight.intersectionParity (zig odd)) = odd := by
  classical
  unfold Route.intersectionParity
  change (∑ _ : Fin 1, ∑ j : Fin 4, decide
    ((openSegment ℝ left right ∩
      openSegment ℝ ((zig odd).point j.castSucc) ((zig odd).point j.succ)).Nonempty)) = odd
  rw [Fin.sum_univ_one, Finset.sum_congr rfl (fun j _ => Bool.decide_congr (hit_iff odd j))]
  cases odd <;> decide

-- Reversing the straight edge preserves its actual odd crossing with the zigzag.
-- Returning along the same edge counts that crossing a second time.
example :
    (∃ p : Route, p.start = right ∧ p.finish = left ∧
      p.germ false = (drawing true).germ (0, true) ∧ p.intersectionParity (zig true) = true) ∧
    (∃ p : Route, p.start = right ∧ p.finish = right ∧
      p.support = straight.support ∧ p.intersectionParity (zig true) = false) := by
  constructor
  · let path : Fin 1 → Dart G := fun _ => (0, true)
    let p := (drawing true).dartSequenceRoute path
    obtain ⟨hstart, hfinish, hfirst, _, _, hparity⟩ :=
      (drawing true).dartSequenceRoute_spec path (fun i => i.elim0)
    refine ⟨p, hstart, hfinish, hfirst, ?_⟩
    have hp := hparity 1
    rw [Fin.sum_univ_one] at hp
    exact hp.trans (crossing_parity true)
  · let path : Fin 2 → Dart G := ![(0, true), (0, false)]
    let p := (drawing true).dartSequenceRoute path
    have hstep : ∀ i : Fin 1, (path i.castSucc).reverse.vertex = (path i.succ).vertex :=
      by decide
    obtain ⟨hstart, hfinish, _, _, hsupport, hparity⟩ :=
      (drawing true).dartSequenceRoute_spec path hstep
    refine ⟨p, hstart, hfinish, ?_, ?_⟩
    · have hedge (i : Fin 2) : (path i).1 = 0 := by fin_cases i <;> rfl
      have hstraight : (drawing true).route 0 = straight := rfl
      exact hsupport.trans (Set.iUnion_eq_const fun i =>
        congrArg Route.support ((congrArg (drawing true).route (hedge i)).trans hstraight))
    · have hp := hparity 1
      rw [Fin.sum_univ_two] at hp
      change p.intersectionParity (zig true) =
        straight.intersectionParity (zig true) + straight.intersectionParity (zig true) at hp
      rw [crossing_parity true] at hp
      exact hp

-- The reversed straight segment and a forward zigzag segment retain distinct labels and
-- their own evaluation rules in the concatenated route.
example :
    let path : Fin 2 → Dart G := ![(0, true), (1, false)]
    let p := (drawing true).dartSequenceRoute path
    ∃ e : ((i : Fin 2) × Fin ((drawing true).route (path i).1).segments) ≃ Fin p.segments,
      e ⟨0, 0⟩ ≠ e ⟨1, 2⟩ ∧ ∀ t : ℝ,
        p.eval (e ⟨0, 0⟩) t = straight.eval 0 (1 - t) ∧
        p.eval (e ⟨1, 2⟩) t = (zig true).eval 2 t := by
  dsimp only
  let path : Fin 2 → Dart G := ![(0, true), (1, false)]
  have hstep : ∀ i : Fin 1, (path i.castSucc).reverse.vertex = (path i.succ).vertex := by decide
  obtain ⟨e, he⟩ := (drawing true).exists_dartSequenceRoute_segment_equiv path hstep
  refine ⟨e, ?_, fun t => ⟨he 0 0 t, he 1 2 t⟩⟩
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Sigma.fst (e.injective h))

private theorem all_selected_even : G.VertexEven (fun _ => true) := by
  intro v
  classical
  change (∑ d : Fin 2 × Bool, if Dart.vertex (G := G) d = v then true else 0) = false
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, Fintype.sum_bool]
  change ((if 1 = v then true else 0) + (if 0 = v then true else 0)) +
    ((if 1 = v then true else 0) + (if 0 = v then true else 0)) = false
  rw [BooleanRing.add_self, Bool.zero_eq_false]

-- The even case has a real crossing on each of the two middle zigzag segments.
example : (openSegment ℝ left right ∩
    openSegment ℝ ((zig false).point (1 : Fin 4).castSucc)
      ((zig false).point (1 : Fin 4).succ)).Nonempty ∧
    ∃ E : PolygonalDrawing G, E.IsEmbedding ∧ E.Realizes rotation := by
  refine ⟨(hit_iff false 1).mpr (Or.inr ⟨rfl, rfl⟩), ?_⟩
  have heven : ∀ e f, e ≠ f →
      ((drawing false).route e).intersectionParity ((drawing false).route f) = false := by
    intro e f h
    fin_cases e <;> fin_cases f
    · exact (h rfl).elim
    · exact crossing_parity false
    · exact (Route.intersectionParity_symm _ _).trans (crossing_parity false)
    · exact (h rfl).elim
  obtain ⟨r, hr, E, hE, hEr⟩ :=
    (regular false).exists_embedding_of_pairwise_even_crossings (simple false) heven (by decide)
  have heq : r = rotation :=
    RotationSystem.ext_rotate (Equiv.ext fun d => hr.rotate_eq (realizes false) d)
  exact ⟨E, hE, heq ▸ hEr⟩

-- The single crossing in the odd case cancels the selected straight edge's label.
example :
    ∃ color : Dart G → Bool, color (0, false) + color (0, true) = false := by
  classical
  obtain ⟨color, hedge, _⟩ := (regular true).exists_dart_colors (simple true) (realizes true)
    (by decide) (fun _ => true) all_selected_even
  refine ⟨color, (hedge 0).trans ?_⟩
  have ho : ((drawing true).route 1).intersectionParity ((drawing true).route 0) = true :=
    (Route.intersectionParity_symm _ _).trans (crossing_parity true)
  change true + (∑ f : Fin 2, (if f = 0 then 0 else true) *
    ((drawing true).route f).intersectionParity ((drawing true).route 0)) = false
  rw [Fin.sum_univ_two, ho]
  simp [Bool.add_eq_xor, ← Bool.zero_eq_false, ← Bool.one_eq_true]

-- A disk around one of the even drawing's two crossings misses the neighboring bend
-- and the other crossing segment, although that segment lies on the same zigzag edge.
example :
    let D := drawing false
    let i : D.SegmentIndex := ⟨0, 0⟩
    let j : D.SegmentIndex := ⟨1, 1⟩
    let k : D.SegmentIndex := ⟨1, 2⟩
    ∃ z : ℂ, ∃ r > (0 : ℝ),
      z ∈ openSegment ℝ (D.segmentStart i) (D.segmentFinish i) ∧
      z ∈ openSegment ℝ (D.segmentStart j) (D.segmentFinish j) ∧
      D.segmentFinish j ∉ Metric.closedBall z r ∧
      Disjoint (Metric.closedBall z r) (segment ℝ (D.segmentStart k) (D.segmentFinish k)) := by
  intro D i j k
  obtain ⟨z, hi, hj⟩ := (hit_iff false 1).mpr (Or.inr ⟨rfl, rfl⟩)
  have hij : i ≠ j := by decide
  obtain ⟨_, ρ, hpos, _, _, hends, hseg⟩ := (regular false).exists_crossing_neighborhoods
  have hz : z ∈ Cslib.Polygonal.openSegmentCrossings D.segmentStart D.segmentFinish :=
    ⟨i, j, hij, hi, hj⟩
  exact ⟨z, ρ z, hpos z hz, hi, hj, (hends z hz j).2,
    hseg i j hij z hi hj k (by decide) (by decide)⟩

end CslibFrontierTests.PolygonalCrossingColors
