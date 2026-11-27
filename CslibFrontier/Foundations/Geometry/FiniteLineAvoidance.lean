/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Segment
import CslibFrontier.Foundations.Geometry.Polygonal.RayParityDirection
import CslibFrontier.Foundations.Geometry.Polygonal.RayParity
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Choosing a point away from finitely many proper lines

`Cslib.exists_mem_ball_avoiding_lines` chooses an actual point in any positive open ball.
Each forbidden line is given by two distinct endpoints and all real affine parameters.
No new line representation or coordinate-complexity statement is introduced. This original
finite-coordinate lemma is intended for auxiliary comparison routes in positioned-embedding
necessity; it does not construct an embedding or a motion.
-/

public section

namespace Cslib

/-- Every positive complex-plane ball contains a point outside all members of a finite
family of proper supporting lines. The finite direction and intercept choices are internal. -/
theorem exists_mem_ball_avoiding_lines {ι : Type*} [Finite ι]
    (a b : ι → ℂ) (hab : ∀ i, a i ≠ b i) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ w ∈ Metric.ball z ρ, ∀ i (t : ℝ), AffineMap.lineMap (a i) (b i) t ≠ w := by
  classical
  let _ := Fintype.ofFinite ι
  let endpoints := Finset.univ.image a ∪ Finset.univ.image b
  obtain ⟨u, hu, hinj⟩ := Polygonal.exists_mul_im_injOn endpoints
  have hheight (i : ι) : (u * a i).im ≠ (u * b i).im := by
    intro h
    apply hab i
    exact hinj (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) h
  let bad := Finset.univ.image fun i : ι =>
    Polygonal.horizontalIntercept (u * a i) (u * b i) (u * z).im - (u * z).re
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  obtain ⟨t, ht, hnot⟩ := (Set.Ioo_infinite (mul_pos hρ hnorm)).exists_notMem_finset bad
  let w := z + (t : ℂ) / u
  have huw : u * w = u * z + (t : ℂ) := by
    dsimp only [w]
    field_simp [hu]
  refine ⟨w, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm,
      show w - z = (t : ℂ) / u by dsimp only [w]; ring,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
    exact (div_lt_iff₀ hnorm).mpr ht.2
  · intro i s heq
    let f : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℂ u).restrictScalars ℝ
    have hm : AffineMap.lineMap (u * a i) (u * b i) s = u * w := by
      change AffineMap.lineMap (f (a i)) (f (b i)) s = f w
      calc
        _ = f (AffineMap.lineMap (a i) (b i) s) :=
          (f.toAffineMap.apply_lineMap _ _ _).symm
        _ = f w := congrArg f heq
    have him := congrArg Complex.im hm
    rw [Polygonal.lineMap_im, huw, Complex.add_im, Complex.ofReal_im, add_zero] at him
    have hden : (u * b i).im - (u * a i).im ≠ 0 := sub_ne_zero.mpr (hheight i).symm
    have hs : s = ((u * z).im - (u * a i).im) /
        ((u * b i).im - (u * a i).im) := by
      apply (eq_div_iff hden).mpr
      linarith
    have hre : (u * z).re + t =
        Polygonal.horizontalIntercept (u * a i) (u * b i) (u * z).im := by
      calc
        (u * z).re + t = (u * w).re := by rw [huw]; rfl
        _ = (AffineMap.lineMap (u * a i) (u * b i) s).re :=
          congrArg Complex.re hm.symm
        _ = AffineMap.lineMap (u * a i).re (u * b i).re s := by
          change Complex.reCLM.toLinearMap.toAffineMap
            (AffineMap.lineMap (u * a i) (u * b i) s) = _
          exact AffineMap.apply_lineMap _ _ _ _
        _ = _ := by
          rw [hs, AffineMap.lineMap_apply_ring']
          dsimp only [Polygonal.horizontalIntercept]
          ring
    apply hnot
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by linarith⟩

end Cslib
