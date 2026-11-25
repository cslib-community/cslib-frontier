/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.RayParityIntersections
import Mathlib.Analysis.Convex.Basic

/-!
# Transport of ray parity along segment interiors

Removing the observed segment leaves endpoint jumps unchanged at every interior height.
The straight-observation intersection law counts the remaining crossings between two
interior parameters. On an isolated segment that sum vanishes. Both orders of the cut
parameters are admitted, including coincident heights with remote listed endpoints.
-/

public section

namespace Cslib.Polygonal

/-- A point on a nonhorizontal segment never counts that same segment as a crossing:
the horizontal ray excludes its base point. -/
theorem not_rayCrosses_lineMap {a b : ℂ} (hab : a.im ≠ b.im) (t : ℝ) :
    ¬RayCrosses a b (AffineMap.lineMap a b t) := by
  have hden : b.im - a.im ≠ 0 := sub_ne_zero.mpr hab.symm
  have him := lineMap_im a b t
  have hre : (AffineMap.lineMap a b t).re = horizontalIntercept a b
      (AffineMap.lineMap a b t).im := by
    rw [him]
    simp only [horizontalIntercept]
    rw [show a.im + t * (b.im - a.im) - a.im = t * (b.im - a.im) by ring,
      mul_div_cancel_right₀ t hden]
    simp only [AffineMap.lineMap_apply_module', Complex.add_re, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.sub_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  exact fun h => (ne_of_lt h.2.2) hre

open Classical in
/-- Along the interior of an observed segment, the change in ray parity equals the
weighted crossings of the intervening portion with the other segments. Their listed
endpoints avoid the observed interior, and the two observation points avoid their
closed supports. The observed segment is omitted from the crossing sum. -/
theorem rayParity_lineMap_add_eq_sum_intersections_of_even {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) (hheight : ∀ i, (a i).im ≠ (b i).im)
    (heven : ∀ p : ℂ, (∑ i, ((if a i = p then x i else 0) +
      (if b i = p then x i else 0))) = false)
    (i : ι)
    (hnodes : ∀ j, j ≠ i → x j = true → ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      AffineMap.lineMap (a i) (b i) u ≠ a j ∧ AffineMap.lineMap (a i) (b i) u ≠ b j)
    {s t : ℝ} (hs : s ∈ Set.Ioo 0 1) (ht : t ∈ Set.Ioo 0 1) (hst : s ≠ t)
    (hsAvoid : ∀ j, j ≠ i → x j = true →
      AffineMap.lineMap (a i) (b i) s ∉ segment ℝ (a j) (b j))
    (htAvoid : ∀ j, j ≠ i → x j = true →
      AffineMap.lineMap (a i) (b i) t ∉ segment ℝ (a j) (b j)) :
    rayParity a b x (AffineMap.lineMap (a i) (b i) t) +
        rayParity a b x (AffineMap.lineMap (a i) (b i) s) =
      ∑ j, (if j = i then 0 else x j) * decide
        ((openSegment ℝ (a j) (b j) ∩
          openSegment ℝ (AffineMap.lineMap (a i) (b i) s)
            (AffineMap.lineMap (a i) (b i) t)).Nonempty) := by
  classical
  let point (u : ℝ) := AffineMap.lineMap (a i) (b i) u
  let y (j : ι) : Bool := if j = i then 0 else x j
  have hremove (u : ℝ) : rayParity a b x (point u) = rayParity a b y (point u) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = i
    · subst j
      simp only [point, not_rayCrosses_lineMap (hheight i), ↓reduceIte]
    · simp only [y, hj, ↓reduceIte]
  have hcut (z : ℂ) (hz : z ∈ segment ℝ (point s) (point t)) :
      ∃ u ∈ Set.Ioo (0 : ℝ) 1, point u = z := by
    rw [← image_segment ℝ (AffineMap.lineMap (a i) (b i)) s t] at hz
    obtain ⟨u, hu, huz⟩ := hz
    exact ⟨u, (convex_Ioo (0 : ℝ) 1).segment_subset hs ht hu, huz⟩
  have hother (j : ι) (hy : y j = true) : j ≠ i ∧ x j = true := by
    by_cases hj : j = i
    · simp [y, hj, Bool.zero_eq_false] at hy
    · exact ⟨hj, by simpa only [y, ite_eq_right hj] using hy⟩
  have hjump (z : ℂ) (hz : z ∈ segment ℝ (point s) (point t)) :
      (∑ j, y j * (decide ((a j).im = z.im ∧ z.re < (a j).re) +
        decide ((b j).im = z.im ∧ z.re < (b j).re))) = 0 := by
    obtain ⟨u, hu, rfl⟩ := hcut z hz
    have hdiff : (b i).im - (a i).im ≠ 0 := sub_ne_zero.mpr (hheight i).symm
    have him : (point u).im = (a i).im + u * ((b i).im - (a i).im) :=
      lineMap_im (a i) (b i) u
    have ha : (a i).im ≠ (point u).im := fun h =>
      mul_ne_zero hu.1.ne' hdiff (by linarith)
    have hb : (b i).im ≠ (point u).im := fun h =>
      mul_ne_zero (sub_ne_zero.mpr hu.2.ne') hdiff (by linarith)
    rw [← sum_rayParity_endpoint_jumps_eq_zero a b x heven (point u)]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst j
      simp only [ha, hb, false_and, decide_false, ← Bool.zero_eq_false, add_zero, mul_zero]
    · simp only [y, hj, ↓reduceIte]
  have hcd : (point s).im ≠ (point t).im := fun heq => by
    have hs' : (point s).im = (a i).im + s * ((b i).im - (a i).im) := lineMap_im (a i) (b i) s
    have ht' : (point t).im = (a i).im + t * ((b i).im - (a i).im) := lineMap_im (a i) (b i) t
    exact hst (mul_right_cancel₀ (sub_ne_zero.mpr (hheight i).symm) (by linarith))
  rw [hremove s, hremove t]
  exact rayParity_endpoints_add_eq_sum_intersections_of_endpoint_jumps_eq_zero
    a b y (point s) (point t) hheight hcd
    (fun j hy => hsAvoid j (hother j hy).1 (hother j hy).2)
    (fun j hy => htAvoid j (hother j hy).1 (hother j hy).2)
    (fun j hy hz =>
      let ⟨u, hu, huz⟩ := hcut _ hz
      (hnodes j (hother j hy).1 (hother j hy).2 u hu).1 huz)
    (fun j hy hz =>
      let ⟨u, hu, huz⟩ := hcut _ hz
      (hnodes j (hother j hy).1 (hother j hy).2 u hu).2 huz)
    hjump

/-- Ray parity on the open interior of one segment is constant if no other listed
segment meets that interior. The segment itself is omitted by the strict base-point
convention. Endpoint jumps from other segments cancel even when their heights occur
inside the observed segment's height range. -/
theorem rayParity_lineMap_eq_of_even {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) (hheight : ∀ i, (a i).im ≠ (b i).im)
    (heven : ∀ p : ℂ, (∑ i, ((if a i = p then x i else 0) +
      (if b i = p then x i else 0))) = false)
    (i : ι) (hisolated : ∀ j, j ≠ i → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      AffineMap.lineMap (a i) (b i) t ∉ segment ℝ (a j) (b j))
    {s t : ℝ} (hs : s ∈ Set.Ioo 0 1) (ht : t ∈ Set.Ioo 0 1) :
    rayParity a b x (AffineMap.lineMap (a i) (b i) s) =
      rayParity a b x (AffineMap.lineMap (a i) (b i) t) := by
  classical
  by_cases hst : s = t
  · subst t
    rfl
  have h := rayParity_lineMap_add_eq_sum_intersections_of_even a b x hheight heven i
    (fun j hj _ u hu => ⟨
      fun he => hisolated j hj u hu (he ▸ left_mem_segment ℝ (a j) (b j)),
      fun he => hisolated j hj u hu (he ▸ right_mem_segment ℝ (a j) (b j))⟩)
    hs ht hst (fun j hj _ => hisolated j hj s hs) (fun j hj _ => hisolated j hj t ht)
  have hzero : (∑ j, (if j = i then 0 else x j) * decide
      ((openSegment ℝ (a j) (b j) ∩ openSegment ℝ
        (AffineMap.lineMap (a i) (b i) s) (AffineMap.lineMap (a i) (b i) t)).Nonempty)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j = i
    · simp [hj]
    have hno : ¬(openSegment ℝ (a j) (b j) ∩ openSegment ℝ
        (AffineMap.lineMap (a i) (b i) s) (AffineMap.lineMap (a i) (b i) t)).Nonempty := by
      rintro ⟨z, hz⟩
      rw [← image_openSegment ℝ (AffineMap.lineMap (a i) (b i)) s t] at hz
      obtain ⟨u, hu, rfl⟩ := hz.2
      exact hisolated j hj u ((convex_Ioo (0 : ℝ) 1).openSegment_subset hs ht hu)
        (openSegment_subset_segment ℝ _ _ hz.1)
    simp [hj, hno, ← Bool.zero_eq_false]
  rw [hzero] at h
  exact ((BooleanRing.add_eq_zero' _ _).mp h).symm

end Cslib.Polygonal
