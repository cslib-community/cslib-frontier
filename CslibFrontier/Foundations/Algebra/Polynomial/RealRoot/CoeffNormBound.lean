/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial root bounds)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Polynomial.CoeffNorm1
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# Real root bounds from the integer coefficient norm

Cauchy's bound implies that a real root of a nonzero integer polynomial has absolute value
strictly less than its coefficient ℓ₁ norm plus one. The leading coefficient has norm at least
one. This is the bound used for exclusion of exceptional parameters in lean-canny.
-/

public section

namespace Polynomial

/-- Every real root has absolute value less than the integer coefficient norm plus one. -/
theorem abs_lt_coeffNorm1_add_one_of_eval₂_eq_zero {p : Polynomial ℤ} (hp : p ≠ 0) {x : ℝ}
    (hx : p.eval₂ (Int.castRingHom ℝ) x = 0) : |x| < (p.coeffNorm1 : ℝ) + 1 := by
  let f := Int.castRingHom ℝ
  have hf : Function.Injective f := Int.cast_injective
  let q := p.map f
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hp
  have hroot : q.IsRoot x := by simpa only [IsRoot.def, q, eval_map] using hx
  have hnorm (a : ℤ) : ‖f a‖ = (a.natAbs : ℝ) := by
    change ‖(a : ℝ)‖ = _
    rw [Real.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hl : 1 ≤ ‖q.leadingCoeff‖₊ := by
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one, leadingCoeff_map_of_injective hf p, hnorm]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp))
  let s := (Finset.range q.natDegree).sup (fun i => ‖q.coeff i‖₊)
  have hs : s ≤ (p.coeffNorm1 : NNReal) := Finset.sup_le fun i _ => by
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_natCast, coeff_map, hnorm]
    exact_mod_cast natAbs_coeff_le_coeffNorm1 p i
  have hlt : ‖x‖₊ < (p.coeffNorm1 : NNReal) + 1 := by
    refine (hroot.norm_lt_cauchyBound hq).trans_le ?_
    rw [cauchyBound]
    exact add_le_add ((div_le_self zero_le hl).trans hs) le_rfl
  rw [← Real.norm_eq_abs, ← coe_nnNorm]
  exact_mod_cast hlt

/-- A nonzero real root has absolute value greater than the reciprocal of the coefficient
norm plus one, by applying the upper bound to the reversed polynomial. -/
theorem inv_coeffNorm1_add_one_lt_abs_of_eval₂_eq_zero {p : Polynomial ℤ} (hp : p ≠ 0)
    {x : ℝ} (hx : p.eval₂ (Int.castRingHom ℝ) x = 0) (hx₀ : x ≠ 0) :
    ((p.coeffNorm1 : ℝ) + 1)⁻¹ < |x| := by
  let := invertibleOfNonzero hx₀
  have hroot : p.reverse.eval₂ (Int.castRingHom ℝ) x⁻¹ = 0 := by
    simpa only [invOf_eq_inv] using (eval₂_reverse_eq_zero_iff (Int.castRingHom ℝ) x p).mpr hx
  have h := abs_lt_coeffNorm1_add_one_of_eval₂_eq_zero (reverse_eq_zero.not.mpr hp) hroot
  rw [coeffNorm1_reverse, abs_inv] at h
  exact (inv_lt_comm₀ (abs_pos.mpr hx₀) (by positivity)).mp h

/-- On a real interval of radius at least one, the coefficient norm times the radius
raised to the degree bounds the absolute value of the evaluation. -/
theorem abs_eval₂_le_coeffNorm1_mul_pow (p : Polynomial ℤ) {x R : ℝ}
    (hR : 1 ≤ R) (hx : |x| ≤ R) :
    |p.eval₂ (Int.castRingHom ℝ) x| ≤ (p.coeffNorm1 : ℝ) * R ^ p.natDegree := by
  rw [eval₂_eq_sum, Polynomial.sum]
  simp only [Int.coe_castRingHom]
  calc
    _ ≤ ∑ i ∈ p.support, |(p.coeff i : ℝ) * x ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ p.support, |(p.coeff i : ℝ)| * R ^ p.natDegree := by
      refine Finset.sum_le_sum fun i hi => ?_
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left
        ((pow_le_pow_left₀ (abs_nonneg _) hx i).trans
          (pow_le_pow_right₀ hR (le_natDegree_of_mem_supp i hi))) (abs_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul, coeffNorm1, Nat.cast_sum]
      simp only [Nat.cast_natAbs, Int.cast_abs]

end Polynomial
