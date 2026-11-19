/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitRestriction
public import CslibFrontier.Foundations.Geometry.Polygonal.Segment
import Mathlib.Tactic.FinCases

/-!
# Trisection of an indexed polygonal route

Cut the first and last segments at positive outgoing times. The three routes follow
the original traversal order and preserve all real points of the original route.
The parameter law identifies the ends of each new route exactly, including when both
cuts lie in one original segment. This is original finite geometry.
-/

public section

namespace Cslib.Polygonal.Route

/-- The initial chord, retained middle route and final chord, in source order. -/
@[expose] noncomputable def trisect (p : Route) (s t : ℝ) : Fin 3 → Route :=
  ![line p.start (p.cutEnds s t).start, p.cutEnds s t, line (p.cutEnds s t).finish p.finish]

/-- The four boundaries of the pieces in the original route's position parameter. -/
@[expose] def trisectionBounds (p : Route) (s t : ℝ) : Fin 4 → ℝ :=
  ![0, s, (p.segments : ℝ) - t, p.segments]

/-- Positive, nonoverlapping cuts give three strictly ordered position intervals. -/
theorem strictMono_trisectionBounds (p : Route) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    StrictMono (p.trisectionBounds s t) := by
  refine Fin.strictMono_iff_lt_succ.mpr ?_
  intro k
  fin_cases k
  · exact hs
  · change s < (p.segments : ℝ) - t
    have hn : (1 : ℝ) ≤ (p.segments : ℝ) := by
      exact_mod_cast Nat.le_add_left 1 p.bends
    linarith
  · exact sub_lt_self _ ht

private theorem eval_start_zero (p : Route) : p.eval 0 0 = p.start := by
  simp [eval, start]

private theorem eval_finish_one (p : Route) : p.eval (Fin.last p.bends) 1 = p.finish := by
  simp [eval, finish, segments]

private theorem eval_between (p : Route) (j : Fin p.segments) (a b u : ℝ) :
    AffineMap.lineMap (p.eval j a) (p.eval j b) u =
      p.eval j (AffineMap.lineMap a b u) :=
  ((AffineMap.lineMap (p.point j.castSucc) (p.point j.succ)).apply_lineMap a b u).symm

private theorem eval_trisect_first (p : Route) (s t : ℝ)
    (i : Fin (p.trisect s t 0).segments) (u : ℝ) :
    (p.trisect s t 0).eval i u = p.eval 0 (s * u) := by
  change Fin 1 at i
  change (line p.start (p.cutEnds s t).start).eval i u = _
  have hstart : (p.cutEnds s t).start = p.eval 0 s := p.endpoint_cutEnds s t false
  calc
    _ = AffineMap.lineMap p.start (p.cutEnds s t).start u := eval_line _ _ i u
    _ = _ := by
      rw [hstart, ← p.eval_start_zero, p.eval_between]
      congr 1
      rw [AffineMap.lineMap_apply_ring']
      ring

private theorem eval_trisect_last (p : Route) (s t : ℝ)
    (i : Fin (p.trisect s t 2).segments) (u : ℝ) :
    (p.trisect s t 2).eval i u = p.eval (Fin.last p.bends) (1 - t + t * u) := by
  change Fin 1 at i
  change (line (p.cutEnds s t).finish p.finish).eval i u = _
  have hfinish : (p.cutEnds s t).finish = p.eval (Fin.last p.bends) (1 - t) :=
    p.endpoint_cutEnds s t true
  calc
    _ = AffineMap.lineMap (p.cutEnds s t).finish p.finish u := eval_line _ _ i u
    _ = _ := by
      rw [hfinish, ← p.eval_finish_one, p.eval_between]
      congr 1
      rw [AffineMap.lineMap_apply_ring']
      ring

private theorem middle_position_lower (p : Route) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (i : Fin p.segments) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    s ≤ p.position i (p.cutTime s t i u) ∧
      (p.position i (p.cutTime s t i u) = s ↔ (p.cutEnds s t).AtEnd i u false) := by
  by_cases hi : i.val = 0
  · have hi0 : i = 0 := Fin.ext hi
    subst i
    have hb := (p.cutTime_bounds hs.le ht.le hst 0 hu).1
    have he := p.cutTime_eq_lower_iff hs.le ht.le hst 0 u
    simpa [AtEnd, position, cutLower] using And.intro hb he
  · have hi1 : (1 : ℝ) ≤ i.val := by exact_mod_cast (show 1 ≤ i.val by omega)
    have hr := p.cutTime_mem hs.le ht.le hst i hu
    change s ≤ (i.val : ℝ) + p.cutTime s t i u ∧
      ((i.val : ℝ) + p.cutTime s t i u = s ↔ (i.val : ℝ) + u = 0)
    exact ⟨by linarith [hr.1], iff_of_false (by linarith [hr.1]) (by linarith [hu.1])⟩

private theorem middle_position_upper (p : Route) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (i : Fin p.segments) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    p.position i (p.cutTime s t i u) ≤ (p.segments : ℝ) - t ∧
      (p.position i (p.cutTime s t i u) = (p.segments : ℝ) - t ↔
        (p.cutEnds s t).AtEnd i u true) := by
  change (i.val : ℝ) + p.cutTime s t i u ≤ (p.segments : ℝ) - t ∧
    ((i.val : ℝ) + p.cutTime s t i u = (p.segments : ℝ) - t ↔
      (i.val : ℝ) + u = (p.segments : ℝ))
  by_cases hi : i.val + 1 = p.segments
  · have hic : (i.val : ℝ) + 1 = p.segments := by exact_mod_cast hi
    have hb : p.cutTime s t i u ≤ 1 - t := by
      simpa only [cutUpper, hi, ite_true] using (p.cutTime_bounds hs.le ht.le hst i hu).2
    have he : p.cutTime s t i u = 1 - t ↔ u = 1 := by
      simpa only [cutUpper, hi, ite_true] using p.cutTime_eq_upper_iff hs.le ht.le hst i u
    refine ⟨by linarith, ?_⟩
    constructor
    · intro hz
      have hu1 := he.mp (by linarith)
      linarith
    · intro hz
      have hr := he.mpr (by linarith)
      linarith
  · have hic : (i.val : ℝ) + 2 ≤ p.segments := by
      exact_mod_cast (show i.val + 2 ≤ p.segments by omega)
    have hr := p.cutTime_mem hs.le ht.le hst i hu
    exact ⟨by linarith [hr.2], iff_of_false (by linarith [hr.2]) (by linarith [hu.2])⟩

/-- Each closed piece parameter has a parameter on the original route at the same
point. It lies in the corresponding closed interval and reaches a boundary exactly
when the piece parameter is at the corresponding end. -/
theorem exists_trisect_eval (p : Route) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (k : Fin 3) (i : Fin (p.trisect s t k).segments) (u : ℝ) (hu : u ∈ Set.Icc 0 1) :
    ∃ (j : Fin p.segments) (r : ℝ), r ∈ Set.Icc 0 1 ∧
      p.eval j r = (p.trisect s t k).eval i u ∧
      p.position j r ∈ Set.Icc (p.trisectionBounds s t k.castSucc) (p.trisectionBounds s t k.succ) ∧
      (p.position j r = p.trisectionBounds s t k.castSucc ↔ (p.trisect s t k).AtEnd i u false) ∧
      (p.position j r = p.trisectionBounds s t k.succ ↔ (p.trisect s t k).AtEnd i u true) := by
  have hline (a b : ℂ) (side : Bool) :
      (line a b).AtEnd 0 u side ↔ u = if side then 1 else 0 := by
    cases side <;> simp [AtEnd, position, line]
  have cancel (a : ℝ) (ha : a ≠ 0) (v : ℝ) : a * u = a * v ↔ u = v :=
    ⟨mul_left_cancel₀ ha, congrArg (a * ·)⟩
  fin_cases k
  · change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    have hpos : p.position 0 (s * u) = s * u := by simp [position]
    have hlo : 0 ≤ s * u := mul_nonneg hs.le hu.1
    have hhi : s * u ≤ s := by simpa using mul_le_mul_of_nonneg_left hu.2 hs.le
    refine ⟨0, s * u, ⟨hlo, hhi.trans (by linarith)⟩,
      (p.eval_trisect_first s t 0 u).symm, ?_⟩
    change p.position 0 (s * u) ∈ Set.Icc 0 s ∧
      (p.position 0 (s * u) = 0 ↔ (line p.start (p.cutEnds s t).start).AtEnd 0 u false) ∧
      (p.position 0 (s * u) = s ↔ (line p.start (p.cutEnds s t).start).AtEnd 0 u true)
    rw [hpos, hline, hline]
    refine ⟨⟨hlo, hhi⟩, ?_, ?_⟩
    · change s * u = 0 ↔ u = 0
      simpa only [mul_zero] using cancel s hs.ne' 0
    · change s * u = s ↔ u = 1
      simpa only [mul_one] using cancel s hs.ne' 1
  · change Fin p.segments at i
    obtain ⟨hl, hL⟩ := p.middle_position_lower hs ht hst i hu
    obtain ⟨hh, hH⟩ := p.middle_position_upper hs ht hst i hu
    exact ⟨i, _, p.cutTime_mem hs.le ht.le hst i hu, (p.eval_cutEnds s t i u).symm,
      ⟨hl, hh⟩, hL, hH⟩
  · change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    let r := 1 - t + t * u
    have hlo : 0 ≤ t * u := mul_nonneg ht.le hu.1
    have hhi : t * u ≤ t := by simpa using mul_le_mul_of_nonneg_left hu.2 ht.le
    have hr : r ∈ Set.Icc 0 1 := ⟨by dsimp [r]; linarith, by dsimp [r]; linarith⟩
    have hpos : p.position (Fin.last p.bends) r = (p.segments : ℝ) - t + t * u := by
      simp only [position, Fin.val_last, segments, Nat.cast_add, Nat.cast_one]
      dsimp [r]
      ring
    refine ⟨Fin.last p.bends, r, hr, (p.eval_trisect_last s t 0 u).symm, ?_⟩
    change p.position (Fin.last p.bends) r ∈ Set.Icc ((p.segments : ℝ) - t) p.segments ∧
      (p.position (Fin.last p.bends) r = (p.segments : ℝ) - t ↔
        (line (p.cutEnds s t).finish p.finish).AtEnd 0 u false) ∧
      (p.position (Fin.last p.bends) r = p.segments ↔
        (line (p.cutEnds s t).finish p.finish).AtEnd 0 u true)
    rw [hpos, hline, hline]
    refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
    · change (p.segments : ℝ) - t + t * u = (p.segments : ℝ) - t ↔ u = 0
      constructor
      · intro he
        exact (cancel t ht.ne' 0).mp (by rw [mul_zero]; linarith)
      · intro he
        rw [he, mul_zero, add_zero]
    · change (p.segments : ℝ) - t + t * u = p.segments ↔ u = 1
      constructor
      · intro he
        exact (cancel t ht.ne' 1).mp (by rw [mul_one]; linarith)
      · intro he
        rw [he, mul_one, sub_add_cancel]

/-- Each of the three pieces is simple when the original route is simple.
The original route may have the same start and finish. -/
theorem IsSimple.trisect {p : Route} (hp : p.IsSimple) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) (k : Fin 3) :
    (p.trisect s t k).IsSimple := by
  fin_cases k
  · change (line p.start (p.cutEnds s t).start).IsSimple
    apply isSimple_line
    intro he
    rw [← p.eval_start_zero] at he
    have hend : (p.cutEnds s t).start = p.eval 0 s := p.endpoint_cutEnds s t false
    rw [hend] at he
    exact hs.ne' (AffineMap.lineMap_injective ℝ (hp.segment_ne 0) he).symm
  · exact hp.cutEnds hs.le ht.le hst
  · change (line (p.cutEnds s t).finish p.finish).IsSimple
    apply isSimple_line
    intro he
    have hend : (p.cutEnds s t).finish = p.eval (Fin.last p.bends) (1 - t) :=
      p.endpoint_cutEnds s t true
    rw [hend, ← p.eval_finish_one] at he
    have h := AffineMap.lineMap_injective ℝ (hp.segment_ne (Fin.last p.bends)) he
    linarith

/-- The pieces cover precisely the continuous support of the original route. -/
theorem support_trisect (p : Route) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    (⋃ k : Fin 3, (p.trisect s t k).support) = p.support := by
  have preimage {a b r : ℝ} (hab : a ≤ b) (hr : r ∈ Set.Icc a b) :
      ∃ u ∈ Set.Icc (0 : ℝ) 1, AffineMap.lineMap a b u = r := by
    rwa [← segment_eq_Icc hab, segment_eq_image_lineMap] at hr
  ext z
  constructor
  · intro hz
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
    obtain ⟨i, u, hu, he⟩ := ((p.trisect s t k).mem_support_iff z).mp hk
    obtain ⟨j, r, hr, h, _, _, _⟩ := p.exists_trisect_eval hs ht hst k i u hu
    exact (p.mem_support_iff z).mpr ⟨j, r, hr, h.trans he⟩
  · intro hz
    obtain ⟨i, r, hr, rfl⟩ := (p.mem_support_iff z).mp hz
    rcases lt_or_ge r (p.cutLower s i) with hlow | hlow
    · have hi : i = 0 := by
        by_contra h
        have hn : i.val ≠ 0 := fun e => h (Fin.ext e)
        simp only [cutLower, ite_eq_right hn] at hlow
        exact (not_lt_of_ge hr.1) hlow
      subst i
      change r < s at hlow
      obtain ⟨u, hu, he⟩ := preimage hs.le ⟨hr.1, hlow.le⟩
      have hr' : s * u = r := by rw [AffineMap.lineMap_apply_ring'] at he; linarith
      refine Set.mem_iUnion.mpr ⟨0, ((p.trisect s t 0).mem_support_iff _).mpr ⟨0, u, hu, ?_⟩⟩
      rw [p.eval_trisect_first, hr']
    · rcases le_or_gt r (p.cutUpper t i) with hupp | hupp
      · have hlu := (p.cut_bounds hs.le ht.le hst i).2.1
        obtain ⟨u, hu, he⟩ := preimage hlu.le ⟨hlow, hupp⟩
        refine Set.mem_iUnion.mpr
          ⟨1, ((p.trisect s t 1).mem_support_iff _).mpr ⟨i, u, hu, ?_⟩⟩
        change (p.cutEnds s t).eval i u = _
        rw [eval_cutEnds, show p.cutTime s t i u = r from he]
      · have hi : i = Fin.last p.bends := by
          by_contra h
          have hn : i.val + 1 ≠ p.segments := by
            intro he
            apply h
            apply Fin.ext
            simp only [Fin.val_last]
            unfold segments at he
            omega
          simp only [cutUpper, ite_eq_right hn] at hupp
          exact (not_lt_of_ge hr.2) hupp
        subst i
        have hupp' : 1 - t < r := by simpa [cutUpper, segments] using hupp
        obtain ⟨u, hu, he⟩ := preimage (show 1 - t ≤ (1 : ℝ) by linarith) ⟨hupp'.le, hr.2⟩
        have hr' : 1 - t + t * u = r := by rw [AffineMap.lineMap_apply_ring'] at he; linarith
        refine Set.mem_iUnion.mpr
          ⟨2, ((p.trisect s t 2).mem_support_iff _).mpr ⟨0, u, hu, ?_⟩⟩
        rw [p.eval_trisect_last, hr']

end Cslib.Polygonal.Route
