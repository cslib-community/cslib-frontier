/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitRestriction
public import CslibFrontier.Foundations.Geometry.Polygonal.RouteIntersectionParity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Basic

/-!
# Intersection parity after cutting route ends

Cutting a route preserves its indexed open-segment incidence with a second route
when the removed end segments meet the second route only at the original endpoints.
The cuts may have length zero, and constant segments retain their singleton incidence.
A middle portion of a straight segment can also be removed when the comparison route
avoids it. Each surviving intersection is counted on exactly one of the two remnants.
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
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => decide_eq_decide.mpr ?_
  obtain ⟨hl, hlu, hh⟩ := p.cut_bounds hs ht hst i
  constructor
  · rintro ⟨z, hz, hzq⟩
    obtain ⟨u, hu, he⟩ := (openSegment_eq_image_lineMap ℝ _ _).subset hz
    change (p.cutEnds s t).eval i u = z at he
    rw [p.eval_cutEnds] at he
    have htime : p.cutTime s t i u ∈ Set.Ioo (p.cutLower s i) (p.cutUpper t i) := by
      rw [← openSegment_eq_Ioo hlu]
      exact lineMap_mem_openSegment ℝ _ _ hu
    exact ⟨z, he ▸ lineMap_mem_openSegment ℝ _ _
      ⟨hl.trans_lt htime.1, htime.2.trans_le hh⟩, hzq⟩
  · rintro ⟨z, hz, hzq⟩
    obtain ⟨v, hv, he⟩ := (openSegment_eq_image_lineMap ℝ _ _).subset hz
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
      · obtain rfl : i = 0 := Fin.ext hi
        change s < v
        by_contra! hvs
        have hm := eval_mem_segment_eval p 0 hv.1.le hvs
        have hzero : p.eval 0 0 = p.start := by simp [eval, start]
        have hcut : (p.cutEnds s t).start = p.eval 0 s := p.endpoint_cutEnds s t false
        rw [hzero, ← hcut, he] at hm
        exact hv.1.ne' (hinj (he.trans ((hstart z hm hqz).trans hzero.symm)))
      · simpa only [cutLower, ite_eq_right hi] using hv.1
    have hhigh : v < p.cutUpper t i := by
      by_cases hi : i.val + 1 = p.segments
      · rw [cutUpper, ite_eq_left hi]
        obtain rfl : i = Fin.last p.bends := Fin.ext (Nat.add_right_cancel hi)
        by_contra! htv
        have hm := eval_mem_segment_eval p (Fin.last p.bends) htv hv.2.le
        have hone : p.eval (Fin.last p.bends) 1 = p.finish := by simp [eval, finish]
        have hcut : (p.cutEnds s t).finish = p.eval (Fin.last p.bends) (1 - t) :=
          p.endpoint_cutEnds s t true
        rw [← hcut, hone, he] at hm
        exact hv.2.ne (hinj (he.trans ((hfinish z hm hqz).trans hone.symm)))
      · simpa only [cutUpper, ite_eq_right hi] using hv.2
    obtain ⟨u, hu, huv⟩ := (openSegment_eq_image_lineMap ℝ _ _).subset
      ((openSegment_eq_Ioo hlu).symm.subset ⟨hlow, hhigh⟩)
    have hcut : (p.cutEnds s t).eval i u = z :=
      (p.eval_cutEnds s t i u).trans ((congrArg (p.eval i) huv).trans he)
    exact ⟨z, hcut ▸ lineMap_mem_openSegment ℝ _ _ hu, hzq⟩

/-- Removing a middle interval of a straight segment disjoint from the comparison route
preserves the sum of crossing parities on the two outside pieces. Convexity prevents one
comparison segment from meeting both pieces without touching the removed interval. -/
theorem intersectionParity_line_split_of_disjoint {a b : ℂ} {q : Route} {l u : ℝ}
    (hl : 0 < l) (hlu : l < u) (hu : u < 1)
    (hsep : Disjoint (segment ℝ (AffineMap.lineMap a b l) (AffineMap.lineMap a b u)) q.support) :
    (line a b).intersectionParity q =
      (line a (AffineMap.lineMap a b l)).intersectionParity q +
        (line (AffineMap.lineMap a b u) b).intersectionParity q := by
  classical
  let F := AffineMap.lineMap (k := ℝ) a b
  have hsum (c d : ℂ) : (line c d).intersectionParity q =
      ∑ j : Fin q.segments, decide ((openSegment ℝ c d ∩
        openSegment ℝ (q.point j.castSucc) (q.point j.succ)).Nonempty) := by
    change (∑ _ : Fin 1, ∑ j : Fin q.segments, decide ((openSegment ℝ c d ∩
      openSegment ℝ (q.point j.castSucc) (q.point j.succ)).Nonempty)) = _
    exact Fin.sum_univ_one _
  rw [hsum, hsum, hsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  let J := openSegment ℝ (q.point j.castSucc) (q.point j.succ)
  have himage (s t : ℝ) (hst : s < t) : F '' Set.Ioo s t = openSegment ℝ (F s) (F t) := by
    rw [← openSegment_eq_Ioo hst, image_openSegment]
  have hleft : openSegment ℝ a (F l) = F '' Set.Ioo 0 l := by
    simpa only [F, AffineMap.lineMap_apply_zero] using (himage 0 l hl).symm
  have hright : openSegment ℝ (F u) b = F '' Set.Ioo u 1 := by
    simpa only [F, AffineMap.lineMap_apply_one] using (himage u 1 hu).symm
  change decide ((openSegment ℝ a b ∩ J).Nonempty) =
    decide ((openSegment ℝ a (F l) ∩ J).Nonempty) +
      decide ((openSegment ℝ (F u) b ∩ J).Nonempty)
  rw [openSegment_eq_image_lineMap ℝ a b, hleft, hright]
  let hit (s t : ℝ) := (F '' Set.Ioo s t ∩ J).Nonempty
  change decide (hit 0 1) = decide (hit 0 l) + decide (hit u 1)
  have hsupport : J ⊆ q.support := fun _ hw =>
    Set.mem_iUnion.mpr ⟨j, openSegment_subset_segment ℝ _ _ hw⟩
  have hcover : hit 0 1 ↔ hit 0 l ∨ hit u 1 := by
    constructor
    · rintro ⟨w, ⟨t, ht, rfl⟩, hw⟩
      by_cases htl : t < l
      · exact Or.inl ⟨F t, ⟨t, ⟨ht.1, htl⟩, rfl⟩, hw⟩
      · have hut : u < t := by
          by_contra! htu
          have hm : F t ∈ segment ℝ (F l) (F u) := by
            rw [← image_segment ℝ F, segment_eq_Icc hlu.le]
            exact ⟨t, ⟨le_of_not_gt htl, htu⟩, rfl⟩
          exact Set.disjoint_left.mp hsep hm (hsupport hw)
        exact Or.inr ⟨F t, ⟨t, ⟨hut, ht.2⟩, rfl⟩, hw⟩
    · rintro (⟨w, ⟨t, ht, rfl⟩, hw⟩ | ⟨w, ⟨t, ht, rfl⟩, hw⟩)
      · exact ⟨F t, ⟨t, ⟨ht.1, ht.2.trans (hlu.trans hu)⟩, rfl⟩, hw⟩
      · exact ⟨F t, ⟨t, ⟨(hl.trans hlu).trans ht.1, ht.2⟩, rfl⟩, hw⟩
  have hexclusive : hit 0 l → hit u 1 → False := by
    rintro ⟨w, ⟨s, hs, rfl⟩, hws⟩ ⟨w', ⟨t, ht, rfl⟩, hwt⟩
    have hm : F l ∈ segment ℝ (F s) (F t) := by
      rw [← image_segment ℝ F, segment_eq_Icc (hs.2.trans (hlu.trans ht.1)).le]
      exact ⟨l, ⟨hs.2.le, (hlu.trans ht.1).le⟩, rfl⟩
    have hconv : Convex ℝ J := convex_openSegment _ _
    exact Set.disjoint_left.mp hsep (left_mem_segment ℝ _ _)
      (hsupport (hconv.segment_subset hws hwt hm))
  by_cases hL : hit 0 l <;> by_cases hR : hit u 1
  · exact (hexclusive hL hR).elim
  all_goals simp [hcover, hL, hR, Bool.zero_eq_false]

end Cslib.Polygonal.Route
