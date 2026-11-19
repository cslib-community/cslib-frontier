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
# Transport of ray parity along isolated segment interiors

Removing the observed segment leaves endpoint jumps unchanged at every interior height.
The straight-observation intersection law then gives transport: isolation makes every
actual open intersection indicator zero. Both orders of the cut endpoints are admitted;
no positive clearance from other endpoint heights is required. The elementary self-ray
exclusion remains in this module for its existing germ consumers.
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
    change z ∈ segment ℝ (AffineMap.lineMap (a i) (b i) s)
      (AffineMap.lineMap (a i) (b i) t) at hz
    rw [← image_segment ℝ (AffineMap.lineMap (a i) (b i)) s t] at hz
    obtain ⟨u, hu, huz⟩ := hz
    exact ⟨u, (convex_Ioo (0 : ℝ) 1).segment_subset hs ht hu, huz⟩
  have havoid (z : ℂ) (hz : z ∈ segment ℝ (point s) (point t))
      (j : ι) (hy : y j = true) : z ∉ segment ℝ (a j) (b j) := by
    have hji : j ≠ i := by
      intro hj
      simp only [y, hj, ↓reduceIte, Bool.zero_eq_false, Bool.false_eq_true] at hy
    obtain ⟨u, hu, rfl⟩ := hcut z hz
    exact hisolated j hji u hu
  have hjump (z : ℂ) (hz : z ∈ segment ℝ (point s) (point t)) :
      (∑ j, y j * (decide ((a j).im = z.im ∧ z.re < (a j).re) +
        decide ((b j).im = z.im ∧ z.re < (b j).re))) = 0 := by
    obtain ⟨u, hu, rfl⟩ := hcut z hz
    have him : (point u).im = (a i).im + u * ((b i).im - (a i).im) :=
      lineMap_im (a i) (b i) u
    have ha : (a i).im ≠ (point u).im := by
      rw [him]
      rcases lt_or_gt_of_ne (hheight i) with h | h <;> nlinarith [hu.1]
    have hb : (b i).im ≠ (point u).im := by
      rw [him]
      rcases lt_or_gt_of_ne (hheight i) with h | h <;> nlinarith [hu.2]
    rw [← sum_rayParity_endpoint_jumps_eq_zero a b x heven (point u)]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = i
    · subst j
      simp only [ha, hb, false_and, decide_false, ← Bool.zero_eq_false, add_zero, mul_zero]
    · simp only [y, hj, ↓reduceIte]
  have hcd : (point s).im ≠ (point t).im := by
    rw [show (point s).im = (a i).im + s * ((b i).im - (a i).im) from
      lineMap_im (a i) (b i) s,
      show (point t).im = (a i).im + t * ((b i).im - (a i).im) from
      lineMap_im (a i) (b i) t]
    intro heq
    apply hst
    exact mul_right_cancel₀ (sub_ne_zero.mpr (hheight i).symm) (by linarith)
  have hno (j : ι) (hy : y j = true) :
      ¬(openSegment ℝ (a j) (b j) ∩ openSegment ℝ (point s) (point t)).Nonempty := by
    rintro ⟨z, hz⟩
    exact havoid z (openSegment_subset_segment ℝ _ _ hz.2) j hy
      (openSegment_subset_segment ℝ _ _ hz.1)
  have h := rayParity_endpoints_add_eq_sum_intersections_of_endpoint_jumps_eq_zero
    a b y (point s) (point t) hheight hcd
    (fun j hy => havoid _ (left_mem_segment ℝ _ _) j hy)
    (fun j hy => havoid _ (right_mem_segment ℝ _ _) j hy)
    (fun j hy hz => havoid _ hz j hy (left_mem_segment ℝ _ _))
    (fun j hy hz => havoid _ hz j hy (right_mem_segment ℝ _ _))
    hjump
  have hzero : (∑ j, y j * decide
      ((openSegment ℝ (a j) (b j) ∩ openSegment ℝ (point s) (point t)).Nonempty)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hy : y j = true
    · simp only [hno j hy, decide_false, Bool.mul_eq_and, Bool.and_false, Bool.zero_eq_false]
    · have hy' : y j = false := Bool.eq_false_iff.mpr hy
      simp [hy', Bool.zero_eq_false, Bool.mul_eq_and]
  rw [hzero] at h
  rw [hremove s, hremove t]
  exact ((BooleanRing.add_eq_zero' _ _).mp h).symm

end Cslib.Polygonal
