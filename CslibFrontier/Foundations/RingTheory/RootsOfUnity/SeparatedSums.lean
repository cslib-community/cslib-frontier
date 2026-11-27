/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, complex roots of unity)

public import CslibFrontier.Init
public import Mathlib.Analysis.Complex.Basic
import CslibFrontier.Foundations.Analysis.Normed.Ring.PowSub
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# Separating tuples of roots of unity with geometric weights

Distances between distinct complex `ell`th roots of unity are bounded below using the
vanishing geometric sum. A coefficient polynomial of the difference of two tuples then has
a bounded Cauchy radius, so evaluation at a sufficiently large integer distinguishes the tuples.

Adapted from `UnityRootSeparation` and `UnityWeightedSum` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, reusing the contraction power estimate.
-/

public section

namespace Complex

open Finset Polynomial
open scoped BigOperators NNReal

private theorem one_le_mul_norm_sub_one_of_pow_eq_one {ell : ℕ} (hell : ell ≠ 0)
    {z : ℂ} (hz : z ^ ell = 1) (hne : z ≠ 1) : 1 ≤ (ell : ℝ) * ‖z - 1‖ := by
  have hnorm := norm_eq_one_of_pow_eq_one hz hell
  have hgeom := geom_sum_mul z ell
  rw [hz, sub_self] at hgeom
  have hsum := (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)
  have hdiff : (∑ k ∈ range ell, (1 - z ^ k)) = (ell : ℂ) := by
    rw [sum_sub_distrib, hsum]
    simp
  have hb : (ell : ℝ) ≤ (ell : ℝ) * ((ell : ℝ) * ‖z - 1‖) := by
    calc
      _ = ‖∑ k ∈ range ell, (1 - z ^ k)‖ := by rw [hdiff]; simp
      _ ≤ ∑ k ∈ range ell, ‖1 - z ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ range ell, (ell : ℝ) * ‖z - 1‖ := by
        apply sum_le_sum
        intro k hk
        calc
          ‖1 - z ^ k‖ = ‖z ^ k - (1 : ℂ) ^ k‖ := by rw [one_pow, norm_sub_rev]
          _ ≤ (k : ℝ) * ‖z - 1‖ := norm_pow_sub_pow_le_of_norm_le_one hnorm.le (by simp) k
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_range.mp hk).le)
            (norm_nonneg _)
      _ = _ := by simp
  exact le_of_mul_le_mul_left (by simpa only [mul_one] using hb)
    (by exact_mod_cast Nat.pos_of_ne_zero hell)

/-- Distinct complex `ell`th roots of unity are separated by at least `1 / ell`. -/
theorem one_le_mul_norm_sub_of_pow_eq_one {ell : ℕ} (hell : ell ≠ 0)
    {z w : ℂ} (hz : z ^ ell = 1) (hw : w ^ ell = 1) (hne : z ≠ w) :
    1 ≤ (ell : ℝ) * ‖z - w‖ := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, zero_pow hell] at hw
    exact zero_ne_one hw
  have hratio : (z / w) ^ ell = 1 := by rw [div_pow, hz, hw, div_self one_ne_zero]
  have hratio1 : z / w ≠ 1 := fun h => hne ((div_eq_one_iff_eq hw0).mp h)
  have h := one_le_mul_norm_sub_one_of_pow_eq_one hell hratio hratio1
  rwa [div_sub_one hw0, norm_div, norm_eq_one_of_pow_eq_one hw hell, div_one] at h

/-- Geometric weights with integer base at least `2 * ell + 1` distinguish tuples of
complex `ell`th roots of unity. -/
theorem eq_of_weighted_sum_eq_of_pow_eq_one {ell R n : ℕ} (hell : ell ≠ 0)
    (hR : 2 * ell + 1 ≤ R) {z w : Fin n → ℂ}
    (hz : ∀ i, z i ^ ell = 1) (hw : ∀ i, w i ^ ell = 1)
    (hsum : (∑ i, (R : ℂ) ^ i.val * z i) = ∑ i, (R : ℂ) ^ i.val * w i) : z = w := by
  classical
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ w i := by simpa only [funext_iff, not_forall] using hne
  let P := Polynomial.ofFn n (fun i => z i - w i)
  have hP : P ≠ 0 := by
    intro h
    have hc := congrArg (fun p : ℂ[X] => p.coeff i.val) h
    rw [show P.coeff i.val = z i - w i from ofFn_coeff_eq_val_of_lt _ i.isLt, coeff_zero] at hc
    exact hi (sub_eq_zero.mp hc)
  have hdeg : P.natDegree < n := ofFn_natDegree_lt (by have := i.isLt; omega) _
  have hcoeff (k : ℕ) : ‖P.coeff k‖₊ ≤ (2 : ℝ≥0) := by
    by_cases hk : k < n
    · have hc : P.coeff k = z ⟨k, hk⟩ - w ⟨k, hk⟩ := ofFn_coeff_eq_val_of_lt _ hk
      apply NNReal.coe_le_coe.mp
      simp only [coe_nnNorm, NNReal.coe_ofNat, hc]
      exact (norm_sub_le _ _).trans_eq (by
        rw [norm_eq_one_of_pow_eq_one (hz _) hell, norm_eq_one_of_pow_eq_one (hw _) hell]
        norm_num)
    · rw [show P.coeff k = 0 from ofFn_coeff_eq_zero_of_ge _ (by omega)]
      simp
  let j : Fin n := ⟨P.natDegree, hdeg⟩
  have hlead : P.leadingCoeff = z j - w j := by
    rw [← coeff_natDegree]
    exact ofFn_coeff_eq_val_of_lt _ hdeg
  have hj : z j ≠ w j := fun h => (leadingCoeff_ne_zero.mpr hP) (by rw [hlead, h, sub_self])
  have hsep : 1 ≤ (ell : ℝ≥0) * ‖P.leadingCoeff‖₊ := by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_one, NNReal.coe_mul, NNReal.coe_natCast, coe_nnNorm, hlead] using
      one_le_mul_norm_sub_of_pow_eq_one hell (hz j) (hw j) hj
  have hleadpos : 0 < ‖P.leadingCoeff‖₊ := nnNorm_pos.mpr (leadingCoeff_ne_zero.mpr hP)
  have hb : P.cauchyBound ≤ 2 * (ell : ℝ≥0) + 1 := by
    unfold Polynomial.cauchyBound
    apply add_le_add _ le_rfl
    apply (div_le_iff₀ hleadpos).mpr
    calc
      _ ≤ 2 := Finset.sup_le (fun k _ => hcoeff k)
      _ = 2 * 1 := (mul_one _).symm
      _ ≤ 2 * ((ell : ℝ≥0) * ‖P.leadingCoeff‖₊) := mul_le_mul_of_nonneg_left hsep (by positivity)
      _ = _ := by rw [mul_assoc]
  have hroot : P.IsRoot (R : ℂ) := by
    change (Polynomial.ofFn n (fun i => z i - w i)).eval (R : ℂ) = 0
    rw [ofFn_eq_sum_monomial, eval_finsetSum]
    simp only [eval_monomial, sub_mul, sum_sub_distrib]
    exact sub_eq_zero.mpr (by simpa only [mul_comm] using hsum)
  have h := (hroot.norm_lt_cauchyBound hP).trans_le hb
  rw [show ‖(R : ℂ)‖₊ = (R : ℝ≥0) by apply NNReal.eq; simp] at h
  exact (not_lt_of_ge (by exact_mod_cast hR : (2 : ℝ≥0) * ell + 1 ≤ R)) h

end Complex
