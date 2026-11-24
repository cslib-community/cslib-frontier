/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitRestriction
public import CslibFrontier.Foundations.Geometry.Polygonal.RouteIntersectionParity

/-!
# Intersection parity after cutting route ends

Cutting a route preserves its indexed open-segment incidence with a second route
when the removed end segments meet the second route only at the original endpoints.
The cuts may have length zero, and constant segments retain their singleton incidence.
-/

public section

namespace Cslib.Polygonal.Route

private theorem eval_mem_segment_eval (p : Route) (i : Fin p.segments) {a b v : ℝ}
    (hav : a ≤ v) (hvb : v ≤ b) : p.eval i v ∈ segment ℝ (p.eval i a) (p.eval i b) := by
  let f : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap (p.point i.castSucc) (p.point i.succ)
  change f v ∈ segment ℝ (f a) (f b)
  rw [← image_segment ℝ f, segment_eq_Icc (hav.trans hvb)]
  exact ⟨v, ⟨hav, hvb⟩, rfl⟩

/-- Cutting either or both ends of a route preserves the parity of its indexed open
intersections with any route that meets the removed end segments only at the original ends. -/
theorem intersectionParity_cutEnds_left {p q : Route}
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t < 1)
    (hstart : ∀ z ∈ segment ℝ p.start (p.cutEnds s t).start, z ∈ q.support → z = p.start)
    (hfinish : ∀ z ∈ segment ℝ (p.cutEnds s t).finish p.finish, z ∈ q.support → z = p.finish) :
    (p.cutEnds s t).intersectionParity q = p.intersectionParity q := by
  classical
  unfold intersectionParity
  change (∑ i : Fin p.segments, ∑ j : Fin q.segments, _) = _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply decide_eq_decide.mpr
  obtain ⟨hl, hlu, hh⟩ := p.cut_bounds hs ht hst i
  constructor
  · rintro ⟨z, hz, hzq⟩
    rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨u, hu, he⟩ := hz
    change (p.cutEnds s t).eval i u = z at he
    rw [p.eval_cutEnds] at he
    have htime : p.cutTime s t i u ∈ Set.Ioo (p.cutLower s i) (p.cutUpper t i) := by
      rw [← openSegment_eq_Ioo hlu]
      exact lineMap_mem_openSegment ℝ _ _ hu
    exact ⟨z, he ▸ lineMap_mem_openSegment ℝ _ _
      ⟨hl.trans_lt htime.1, htime.2.trans_le hh⟩, hzq⟩
  · rintro ⟨z, hz, hzq⟩
    rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨v, hv, he⟩ := hz
    change p.eval i v = z at he
    by_cases hdeg : p.point i.castSucc = p.point i.succ
    · have hcut : (p.cutEnds s t).eval i v = z := by
        rw [p.eval_cutEnds]
        simpa only [eval, hdeg, AffineMap.lineMap_same_apply] using he
      exact ⟨z, hcut ▸ lineMap_mem_openSegment ℝ _ _ hv, hzq⟩
    have hinj : Function.Injective (p.eval i) := AffineMap.lineMap_injective ℝ hdeg
    have hqz : z ∈ q.support :=
      Set.mem_iUnion.mpr ⟨j, openSegment_subset_segment ℝ _ _ hzq⟩
    -- In a nonconstant segment, an interior parameter cannot equal the endpoint's parameter.
    have hlow : p.cutLower s i < v := by
      by_cases hi : i.val = 0
      · have hi' : i = 0 := Fin.ext hi
        subst i
        change s < v
        by_contra! hvs
        have hm := eval_mem_segment_eval p 0 hv.1.le hvs
        have hzero : p.eval 0 0 = p.start := by
          simp only [eval, AffineMap.lineMap_apply_zero, start, Fin.castSucc_zero]
        have hcut : (p.cutEnds s t).start = p.eval 0 s := p.endpoint_cutEnds s t false
        rw [hzero, ← hcut, he] at hm
        exact hv.1.ne' (hinj (he.trans ((hstart z hm hqz).trans hzero.symm)))
      · simpa only [cutLower, ite_eq_right hi] using hv.1
    have hhigh : v < p.cutUpper t i := by
      by_cases hi : i.val + 1 = p.segments
      · rw [cutUpper, ite_eq_left hi]
        have hi' : i = Fin.last p.bends := Fin.ext (Nat.add_right_cancel hi)
        subst i
        by_contra! htv
        have hm := eval_mem_segment_eval p (Fin.last p.bends) htv hv.2.le
        have hone : p.eval (Fin.last p.bends) 1 = p.finish := by
          simp only [eval, AffineMap.lineMap_apply_one, finish, Fin.succ_last]
        have hcut : (p.cutEnds s t).finish = p.eval (Fin.last p.bends) (1 - t) :=
          p.endpoint_cutEnds s t true
        rw [← hcut, hone, he] at hm
        exact hv.2.ne (hinj (he.trans ((hfinish z hm hqz).trans hone.symm)))
      · simpa only [cutUpper, ite_eq_right hi] using hv.2
    have hv' : v ∈ openSegment ℝ (p.cutLower s i) (p.cutUpper t i) := by
      rw [openSegment_eq_Ioo hlu]
      exact ⟨hlow, hhigh⟩
    rw [openSegment_eq_image_lineMap] at hv'
    obtain ⟨u, hu, huv⟩ := hv'
    have hcut : (p.cutEnds s t).eval i u = z :=
      (p.eval_cutEnds s t i u).trans ((congrArg (p.eval i) huv).trans he)
    exact ⟨z, hcut ▸ lineMap_mem_openSegment ℝ _ _ hu, hzq⟩

end Cslib.Polygonal.Route
