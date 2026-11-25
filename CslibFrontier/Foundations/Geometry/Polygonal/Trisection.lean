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
cuts lie in one original segment. `exists_subroute_between` restricts to an interval
with cuts on any two ordered source segments. This is original finite geometry.
-/

public section

namespace Cslib.Polygonal.Route

/-- The initial chord, retained middle route and final chord, in source order. -/
@[expose] noncomputable def trisect (p : Route) (s t : ℝ) : Fin 3 → Route :=
  ![line p.start (p.cutEnds s t).start, p.cutEnds s t, line (p.cutEnds s t).finish p.finish]

/-- The old start, first cut, last cut and old finish, in traversal order. -/
@[expose] noncomputable def trisectionPoints (p : Route) (s t : ℝ) : Fin 4 → ℂ :=
  ![p.start, p.eval (p.endSegment false) (endTime false s),
    p.eval (p.endSegment true) (endTime true t), p.finish]

/-- Each piece joins the consecutive source boundary points in traversal order. -/
theorem endpoint_trisect (p : Route) (s t : ℝ) (k : Fin 3) (b : Bool) :
    (p.trisect s t k).endpoint b =
      p.trisectionPoints s t (if b then k.succ else k.castSucc) := by
  have hl : (p.cutEnds s t).start = p.eval (p.endSegment false) (endTime false s) :=
    p.endpoint_cutEnds s t false
  have hr : (p.cutEnds s t).finish = p.eval (p.endSegment true) (endTime true t) :=
    p.endpoint_cutEnds s t true
  fin_cases k <;> cases b
  · rfl
  · exact hl
  · exact hl
  · exact hr
  · exact hr
  · rfl

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

private theorem lineMap_cut (p : Route) (b : Bool) (v u : ℝ) :
    AffineMap.lineMap (p.endpoint b) (p.eval (p.endSegment b) (endTime b v)) u =
      p.eval (p.endSegment b) (endTime b (v * u)) := by
  rw [p.eval_near_end b v, p.eval_near_end b (v * u), AffineMap.lineMap_apply_module',
    add_sub_cancel_left, smul_smul, mul_comm u v, add_comm]

private theorem eval_trisect_first (p : Route) (s t : ℝ)
    (i : Fin (p.trisect s t 0).segments) (u : ℝ) :
    (p.trisect s t 0).eval i u = p.eval 0 (s * u) := by
  change Fin 1 at i
  change (line p.start (p.cutEnds s t).start).eval i u = _
  have hstart : (p.cutEnds s t).start = p.eval (p.endSegment false) (endTime false s) :=
    p.endpoint_cutEnds s t false
  calc
    _ = AffineMap.lineMap p.start (p.cutEnds s t).start u := eval_line _ _ i u
    _ = _ := by
      rw [hstart]
      exact p.lineMap_cut false s u

private theorem endTime_last (t u : ℝ) :
    endTime true (t * (1 - u)) = 1 - t + t * u := by
  change 1 - t * (1 - u) = _
  ring

private theorem eval_trisect_last (p : Route) (s t : ℝ)
    (i : Fin (p.trisect s t 2).segments) (u : ℝ) :
    (p.trisect s t 2).eval i u = p.eval (Fin.last p.bends) (1 - t + t * u) := by
  change Fin 1 at i
  change (line (p.cutEnds s t).finish p.finish).eval i u = _
  have hfinish : (p.cutEnds s t).finish = p.eval (p.endSegment true) (endTime true t) :=
    p.endpoint_cutEnds s t true
  calc
    _ = AffineMap.lineMap (p.cutEnds s t).finish p.finish u := eval_line _ _ i u
    _ = AffineMap.lineMap p.finish (p.eval (p.endSegment true) (endTime true t)) (1 - u) := by
      rw [hfinish, ← AffineMap.lineMap_apply_one_sub p.finish _ u]
    _ = _ := by
      rw [← endTime_last]
      exact p.lineMap_cut true t (1 - u)

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
    have hpos : p.position 0 (s * u) = s * u := p.position_near_end false (s * u)
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
      change p.position (p.endSegment true) (1 - t + t * u) = _
      rw [← endTime_last, p.position_near_end]
      change (p.segments : ℝ) - t * (1 - u) = _
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
  have hcut (b : Bool) (h : (if b then t else s) ≠ 0) :
      (p.cutEnds s t).endpoint b ≠ p.endpoint b := by
    rw [p.endpoint_cutEnds, p.eval_near_end]
    intro he
    exact (smul_ne_zero h (hp.germ_ne_zero b)) (add_left_cancel (he.trans (add_zero _).symm))
  fin_cases k
  · exact isSimple_line (hcut false hs.ne').symm
  · exact hp.cutEnds hs.le ht.le hst
  · exact isSimple_line (hcut true ht.ne')

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

/-- Cut out a nonempty portion of a route between local times `s` on segment `i` and `t`
on segment `j`. The new segments keep the original interval of indices in order,
with affine time reparameterization only at the cut ends. If `i` and
`j` differ, their local times are independent. -/
theorem exists_subroute_between (p : Route) (i j : Fin p.segments) (hij : i ≤ j)
    {s t : ℝ} (hs : s ∈ Set.Ico 0 1) (ht : t ∈ Set.Ioc 0 1)
    (hst : i = j → s < t) :
    ∃ q : Route, ∃ e : Fin q.segments ≃o Set.Icc i j,
      q.start = p.eval i s ∧ q.finish = p.eval j t ∧ ∀ k,
        let lo := if (e k).val = i then s else 0
        let hi := if (e k).val = j then t else 1
        0 ≤ lo ∧ lo < hi ∧ hi ≤ 1 ∧ ∀ u : ℝ,
          q.eval k u = p.eval (e k).val (AffineMap.lineMap lo hi u) := by
  have hij' : i.val ≤ j.val := hij
  let r : Route := ⟨j.val - i.val, fun k => p.point ⟨i.val + k.val, by
    have hk : k.val < j.val - i.val + 2 := k.isLt
    have hj : j.val < p.bends + 1 := j.isLt
    omega⟩⟩
  let q := r.cutEnds s (1 - t)
  let source (k : Fin r.segments) : Fin p.segments := ⟨i.val + k.val, by
    have hk := k.isLt
    change k.val < j.val - i.val + 1 at hk
    have hj := j.isLt
    omega⟩
  let e : Fin q.segments ≃o Set.Icc i j := {
    toEquiv := {
      toFun k := ⟨source k, by
        have hk := k.isLt
        change k.val < j.val - i.val + 1 at hk
        change i.val ≤ i.val + k.val ∧ i.val + k.val ≤ j.val
        omega⟩
      invFun k := ⟨k.val.val - i.val, by
        have hk : k.val.val ≤ j.val := k.property.2
        change k.val.val - i.val < j.val - i.val + 1
        omega⟩
      left_inv := fun k => Fin.ext (by change i.val + k.val - i.val = k.val; omega)
      right_inv := fun k => Subtype.ext (Fin.ext (by
        have hk : i.val ≤ k.val.val := k.property.1
        change i.val + (k.val.val - i.val) = k.val.val
        omega)) }
    map_rel_iff' := by
      intro a b
      change i.val + a.val ≤ i.val + b.val ↔ a.val ≤ b.val
      omega }
  have heval (k : Fin q.segments) (u : ℝ) : r.eval k u = p.eval (e k).val u := rfl
  have hfirst : (e 0).val = i := Fin.ext (by change i.val + 0 = i.val; omega)
  have hlast : (e (Fin.last r.bends)).val = j :=
    Fin.ext (by change i.val + (j.val - i.val) = j.val; omega)
  refine ⟨q, e, ?_, ?_, ?_⟩
  · change (r.cutEnds s (1 - t)).endpoint false = _
    rw [endpoint_cutEnds]
    change r.eval 0 s = _
    exact (heval 0 s).trans (congrArg (fun k => p.eval k s) hfirst)
  · change (r.cutEnds s (1 - t)).endpoint true = _
    rw [endpoint_cutEnds]
    change r.eval (Fin.last r.bends) (1 - (1 - t)) = _
    rw [sub_sub_cancel]
    exact (heval (Fin.last r.bends) t).trans (congrArg (fun k => p.eval k t) hlast)
  · intro k
    let lo := if (e k).val = i then s else 0
    let hi := if (e k).val = j then t else 1
    have hki : k.val = 0 ↔ (e k).val = i := by
      constructor
      · intro hk
        exact Fin.ext (by change i.val + k.val = i.val; omega)
      · intro h
        have h' : i.val + k.val = i.val := congrArg Fin.val h
        omega
    have hkj : k.val + 1 = r.segments ↔ (e k).val = j := by
      change k.val + 1 = j.val - i.val + 1 ↔ _
      constructor
      · intro hk
        exact Fin.ext (by change i.val + k.val = j.val; omega)
      · intro h
        have h' : i.val + k.val = j.val := congrArg Fin.val h
        omega
    have hlo : r.cutLower s k = lo := by simp only [cutLower, lo, hki]
    have hhi : r.cutUpper (1 - t) k = hi := by simp only [cutUpper, hi, hkj, sub_sub_cancel]
    have hbounds : 0 ≤ lo ∧ lo < hi ∧ hi ≤ 1 := by
      dsimp only [lo, hi]
      split_ifs with h₁ h₂ h₂
      · exact ⟨hs.1, hst (h₁.symm.trans h₂), ht.2⟩
      · exact ⟨hs.1, hs.2, le_rfl⟩
      · exact ⟨le_rfl, ht.1, ht.2⟩
      · exact ⟨le_rfl, zero_lt_one, le_rfl⟩
    obtain ⟨hl, hlt, hh⟩ := hbounds
    refine ⟨hl, hlt, hh, fun u => ?_⟩
    calc
      q.eval k u = r.eval k (r.cutTime s (1 - t) k u) := r.eval_cutEnds s (1 - t) k u
      _ = p.eval (e k).val (r.cutTime s (1 - t) k u) := heval k _
      _ = p.eval (e k).val (AffineMap.lineMap lo hi u) :=
        congrArg (p.eval (e k).val) (congrArg₂ (fun a b : ℝ => AffineMap.lineMap a b u) hlo hhi)

end Cslib.Polygonal.Route
