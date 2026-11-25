/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Local plane moves in a square

A displacement of length less than the square's half-width extends to an injective
piecewise-affine map of the plane. The map fixes the boundary and exterior. Its displacement
is proportional to the distance to the boundary in the maximum norm.

This is original geometry. The supplied affine walls permit exact transport of polygonal routes.
-/

public section

namespace Cslib.Polygonal

private noncomputable def squareTent (a : ℂ) (r : ℝ) (z : ℂ) : ℝ :=
  max (r - max |z.re - a.re| |z.im - a.im|) 0

private theorem squareTent_sub_le (a : ℂ) (r : ℝ) (z w : ℂ) :
    |squareTent a r z - squareTent a r w| ≤ ‖z - w‖ := by
  let p := max |z.re - a.re| |z.im - a.im|
  let q := max |w.re - a.re| |w.im - a.im|
  have hsub : (r - p) - (r - q) = q - p := by ring
  calc
    _ ≤ |(r - p) - (r - q)| := abs_max_sub_max_le_abs _ _ 0
    _ = |p - q| := by rw [hsub, abs_sub_comm q p]
    _ ≤ max |(z.re - a.re) - (w.re - a.re)| |(z.im - a.im) - (w.im - a.im)| :=
      (abs_max_sub_max_le_max _ _ _ _).trans (max_le_max
        (abs_abs_sub_abs_le_abs_sub _ _) (abs_abs_sub_abs_le_abs_sub _ _))
    _ ≤ ‖z - w‖ := by
      rw [sub_sub_sub_cancel_right, sub_sub_sub_cancel_right]
      simpa only [Complex.sub_re, Complex.sub_im] using
        max_le (Complex.abs_re_le_norm (z - w)) (Complex.abs_im_le_norm (z - w))

private theorem affine_order_on_segment (f g : ℂ →ᵃ[ℝ] ℝ) (x y : ℂ)
    (h : 0 ∉ Set.Ioo (min ((f - g) x) ((f - g) y)) (max ((f - g) x) ((f - g) y))) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, f (AffineMap.lineMap x y t) ≤ g (AffineMap.lineMap x y t)) ∨
      (∀ t ∈ Set.Icc (0 : ℝ) 1, g (AffineMap.lineMap x y t) ≤ f (AffineMap.lineMap x y t)) := by
  have hs : (g x ≤ f x ∧ g y ≤ f y) ∨ (f x ≤ g x ∧ f y ≤ g y) := by
    simpa only [Set.mem_Ioo, not_and_or, not_lt, le_min_iff, max_le_iff,
      FunLike.coe_sub, Pi.sub_apply, sub_nonneg, sub_nonpos] using h
  have hle (p q : ℂ →ᵃ[ℝ] ℝ) (hx : p x ≤ q x) (hy : p y ≤ q y) (t : ℝ)
      (ht : t ∈ Set.Icc 0 1) : p (AffineMap.lineMap x y t) ≤ q (AffineMap.lineMap x y t) := by
    rw [AffineMap.apply_lineMap p, AffineMap.apply_lineMap q,
      AffineMap.lineMap_apply_ring, AffineMap.lineMap_apply_ring]
    exact add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left hy ht.1)
  exact hs.elim (fun h => Or.inr (hle g f h.1 h.2)) (fun h => Or.inl (hle f g h.1 h.2))

private noncomputable def offset (f : ℂ →ᵃ[ℝ] ℝ) (a : ℂ) : ℂ →ᵃ[ℝ] ℝ :=
  f - AffineMap.const ℝ ℂ (f a)

private noncomputable def face (r : ℝ) (f : ℂ →ᵃ[ℝ] ℝ) : ℂ →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ ℂ r - f

/-- Move a point to any point within distance `r`, with an injective map that fixes
the boundary and exterior of the axis-aligned square of half-width `r`. The map preserves
straight interpolation on segments that do not straddle any of the returned affine walls. -/
theorem exists_square_move (a b : ℂ) {r : ℝ} (hr : 0 < r) (hb : ‖b - a‖ < r) :
    ∃ (F : ℂ → ℂ) (walls : List (ℂ →ᵃ[ℝ] ℝ)), Function.Injective F ∧ F a = b ∧
      (∀ z, r ≤ max |z.re - a.re| |z.im - a.im| → F z = z) ∧
      ∀ x y : ℂ, (∀ f ∈ walls, 0 ∉ Set.Ioo (min (f x) (f y)) (max (f x) (f y))) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          F (AffineMap.lineMap x y t) = AffineMap.lineMap (F x) (F y) t := by
  let v : ℂ := r⁻¹ • (b - a)
  have hv : ‖v‖ < 1 := by
    change ‖r⁻¹ • (b - a)‖ < 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), ← div_eq_inv_mul]
    exact (div_lt_one hr).mpr hb
  let F (z : ℂ) := z + squareTent a r z • v
  let u := offset Complex.reCLM.toLinearMap.toAffineMap a
  let w := offset Complex.imCLM.toLinearMap.toAffineMap a
  let pieces : List (ℂ →ᵃ[ℝ] ℝ) := [face r u, face r (-u), face r w, face r (-w), 0]
  refine ⟨F, pieces.flatMap (fun f => pieces.map (fun g => f - g)), ?_, ?_, ?_, ?_⟩
  · intro z y h
    by_contra hne
    have he : z - y = (squareTent a r y - squareTent a r z) • v := by
      rw [sub_smul, sub_eq_sub_iff_add_eq_add, add_comm (squareTent a r y • v)]
      exact h
    have hl := ((congrArg norm he).trans (norm_smul _ _)).trans_le (mul_le_mul_of_nonneg_right
      ((squareTent_sub_le a r y z).trans_eq (norm_sub_rev y z)) (norm_nonneg v))
    exact (not_lt_of_ge hl) (mul_lt_of_lt_one_right (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) hv)
  · change a + squareTent a r a • (r⁻¹ • (b - a)) = b
    simp only [squareTent, sub_self, abs_zero, max_self, sub_zero, max_eq_left hr.le,
      smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  · intro z hz
    change z + squareTent a r z • v = z
    simp only [squareTent, max_eq_right (sub_nonpos.mpr hz), zero_smul, add_zero]
  · intro x y hcuts
    have hpair {f g : ℂ →ᵃ[ℝ] ℝ} (hf : f ∈ pieces) (hg : g ∈ pieces) :
        0 ∉ Set.Ioo (min ((f - g) x) ((f - g) y)) (max ((f - g) x) ((f - g) y)) :=
      hcuts _ (List.mem_flatMap.mpr ⟨f, hf, List.mem_map.mpr ⟨g, hg, rfl⟩⟩)
    have hmin {f g : ℂ →ᵃ[ℝ] ℝ} (hf : f ∈ pieces) (hg : g ∈ pieces) :
        ∃ m ∈ pieces, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          min (f (AffineMap.lineMap x y t)) (g (AffineMap.lineMap x y t)) =
            m (AffineMap.lineMap x y t) := by
      rcases affine_order_on_segment f g x y (hpair hf hg) with h | h
      · exact ⟨f, hf, fun t ht => min_eq_left (h t ht)⟩
      · exact ⟨g, hg, fun t ht => min_eq_right (h t ht)⟩
    obtain ⟨p, hp, he₁⟩ := hmin (f := face r u) (g := face r (-u))
      (by simp [pieces]) (by simp [pieces])
    obtain ⟨q, hq, he₂⟩ := hmin (f := face r w) (g := face r (-w))
      (by simp [pieces]) (by simp [pieces])
    obtain ⟨m, hm, he₃⟩ := hmin hp hq
    have he (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
        squareTent a r (AffineMap.lineMap x y t) = max (m (AffineMap.lineMap x y t)) 0 := by
      let z := AffineMap.lineMap x y t
      have hfaces : squareTent a r z =
          max (min (min (face r u z) (face r (-u) z)) (min (face r w z) (face r (-w) z))) 0 := by
        change _ = max (min (min (r - (z.re - a.re)) (r - -(z.re - a.re)))
          (min (r - (z.im - a.im)) (r - -(z.im - a.im)))) 0
        simp only [squareTent, min_sub_sub_left, ← abs_eq_max_neg]
      rw [hfaces, he₁ t ht, he₂ t ht, he₃ t ht]
    have hzero : (0 : ℂ →ᵃ[ℝ] ℝ) ∈ pieces := by simp [pieces]
    have hchoice : ∃ T : ℂ →ᵃ[ℝ] ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        squareTent a r (AffineMap.lineMap x y t) = T (AffineMap.lineMap x y t) := by
      rcases affine_order_on_segment m 0 x y (hpair hm hzero) with h | h
      · exact ⟨0, fun t ht => (he t ht).trans (max_eq_right (h t ht))⟩
      · exact ⟨m, fun t ht => (he t ht).trans (max_eq_left (h t ht))⟩
    obtain ⟨T, hT⟩ := hchoice
    let H := AffineMap.id ℝ ℂ + ((LinearMap.id.smulRight v : ℝ →ₗ[ℝ] ℂ).toAffineMap.comp T)
    have happ (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
        F (AffineMap.lineMap x y t) = H (AffineMap.lineMap x y t) := by
      change _ + squareTent a r (AffineMap.lineMap x y t) • v =
        _ + T (AffineMap.lineMap x y t) • v
      rw [hT t ht, AffineMap.id_apply]
    have hx : F x = H x := by
      simpa only [AffineMap.lineMap_apply_zero] using happ 0 ⟨le_rfl, zero_le_one⟩
    have hy : F y = H y := by
      simpa only [AffineMap.lineMap_apply_one] using happ 1 ⟨zero_le_one, le_rfl⟩
    intro t ht
    calc
      _ = H (AffineMap.lineMap x y t) := happ t ht
      _ = AffineMap.lineMap (H x) (H y) t := AffineMap.apply_lineMap H x y t
      _ = _ := by rw [← hx, ← hy]

end Cslib.Polygonal
