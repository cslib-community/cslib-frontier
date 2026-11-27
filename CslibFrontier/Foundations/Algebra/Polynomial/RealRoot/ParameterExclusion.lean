/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, bivariate polynomial specialization)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.Polynomial.ResultantCoeffNorm
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.CoeffNormBound
import Mathlib.Data.Nat.Size

/-!
# Excluding roots by power-of-two specialization

For an integer bivariate polynomial, the value cutoff and parameter are powers of two whose
exponents depend only on degree and logarithmic coefficient bounds. The chosen value section
and a nonzero derivative resultant do not vanish at the chosen parameter.

Adapted from `LeanCanny.CountingHierarchy.LargeSpecializationBounds` and
`IntegerAlgebraicThreshold` at lean-canny commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open Finset

/-- A large integer substitution for the outer variable leaves a nonzero polynomial in the
inner variable. The original bivariate norm bounds every polynomial row of inner coefficients. -/
theorem eval_C_ne_zero_of_bivariateCoeffNorm1_add_one_le {P : Polynomial (Polynomial ℤ)}
    (hP : P ≠ 0) {a : ℤ} (ha : P.bivariateCoeffNorm1 + 1 ≤ a.natAbs) :
    P.eval (C a) ≠ 0 := by
  let k := P.leadingCoeff.natDegree
  let row : Polynomial ℤ := ∑ i ∈ P.support, monomial i ((P.coeff i).coeff k)
  have hr : row ≠ 0 := by
    have hcoeff : row.coeff P.natDegree = P.leadingCoeff.leadingCoeff := by
      rw [show row.coeff P.natDegree = _ from finsetSum_coeff _ _ _,
        sum_eq_single P.natDegree]
      · rw [coeff_monomial_same, coeff_natDegree, coeff_natDegree]
      · exact fun i _ hi => coeff_monomial_of_ne _ (Ne.symm hi)
      · exact fun hi => (hi (natDegree_mem_support_of_ne_zero hP)).elim
    exact fun hz => (leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP))
      (by simpa only [hz, coeff_zero] using hcoeff.symm)
  have hm : row.coeffNorm1 ≤ P.bivariateCoeffNorm1 := by
    refine (coeffNorm1_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
    rw [← C_mul_X_pow_eq_monomial]
    exact (coeffNorm1_mul_X_pow_le _ _).trans
      ((coeffNorm1_C _).trans_le (natAbs_coeff_le_coeffNorm1 _ _))
  have heval : row.eval a = (P.eval (C a)).coeff k := by
    change (evalRingHom a) (∑ i ∈ P.support, monomial i ((P.coeff i).coeff k)) = _
    rw [map_sum, eval_eq_sum, Polynomial.sum, finsetSum_coeff]
    refine sum_congr rfl fun i _ => ?_
    rw [coe_evalRingHom, eval_monomial, ← map_pow, coeff_mul_C]
  intro hz
  have hzero : row.eval a = 0 := by rw [heval, hz, coeff_zero]
  have hroot : row.eval₂ (Int.castRingHom ℝ) (a : ℝ) = 0 := by
    change row.eval₂ (Int.castRingHom ℝ) ((Int.castRingHom ℝ) a) = 0
    rw [eval₂_at_apply, hzero, map_zero]
  have hlt := abs_lt_coeffNorm1_add_one_of_eval₂_eq_zero hr hroot
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast] at hlt
  have hle : row.coeffNorm1 + 1 ≤ a.natAbs := (Nat.add_le_add_right hm 1).trans ha
  exact (not_lt_of_ge (by exact_mod_cast hle)) hlt

/-- The exponent of the parameter needed to exceed both exclusion-polynomial bounds.
`D` bounds the outer degree, and `2 ^ H` bounds the input bivariate coefficient norm. -/
@[expose] def parameterExclusionExponent (D H : ℕ) : ℕ :=
  max ((2 * D).size * (2 * D) + (D.size + H) * (2 * D)) (H + (H + 1) * D) + 1

private theorem add_one_le_pow_two {M K E : ℕ} (hM : M ≤ 2 ^ K) (hE : K + 1 ≤ E) :
    M + 1 ≤ 2 ^ E := by
  calc
    _ ≤ 2 ^ K * 2 := by have := Nat.one_le_two_pow (n := K); omega
    _ = 2 ^ (K + 1) := (pow_succ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hE

/-- The chosen parameter exceeds the coefficient norm of the value section plus one. -/
theorem coeffNorm1_eval_C_add_one_le_parameterExclusion {P : Polynomial (Polynomial ℤ)} {D H : ℕ}
    (hD : P.natDegree ≤ D) (hH : P.bivariateCoeffNorm1 ≤ 2 ^ H) :
    (P.eval (C ((2 : ℤ) ^ (H + 1)))).coeffNorm1 + 1 ≤ 2 ^ parameterExclusionExponent D H := by
  let a : ℤ := 2 ^ (H + 1)
  have ha : a.natAbs = 2 ^ (H + 1) := by simp [a, Int.natAbs_pow]
  have hsection : (P.eval (C a)).coeffNorm1 ≤ 2 ^ (H + (H + 1) * D) := by
    calc
      _ ≤ P.bivariateCoeffNorm1 * a.natAbs ^ P.natDegree :=
        coeffNorm1_eval_C_le P a (by rw [ha]; exact Nat.one_le_two_pow)
      _ ≤ 2 ^ H * (2 ^ (H + 1)) ^ D := by
        rw [ha]
        exact Nat.mul_le_mul hH (Nat.pow_le_pow_right Nat.one_le_two_pow hD)
      _ = _ := by rw [← pow_mul, ← pow_add]
  exact add_one_le_pow_two hsection (Nat.succ_le_succ (le_max_right _ _))

private theorem resultant_le_pow_two {P : Polynomial (Polynomial ℤ)} {D H : ℕ}
    (hD : P.natDegree ≤ D) (hH : P.bivariateCoeffNorm1 ≤ 2 ^ H) :
    (P.resultant P.derivative).coeffNorm1 ≤
      2 ^ ((2 * D).size * (2 * D) + (D.size + H) * (2 * D)) := by
  have hfactorial : (2 * D).factorial ≤ (2 ^ (2 * D).size) ^ (2 * D) :=
    (Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left (Nat.lt_size_self _).le _)
  have hA : max 1 (max 1 D * 2 ^ H) ≤ 2 ^ (D.size + H) := by
    rw [pow_add]
    refine max_le (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) ?_
    exact Nat.mul_le_mul_right _ (max_le Nat.one_le_two_pow (Nat.lt_size_self _).le)
  calc
    _ ≤ (2 * D).factorial * max 1 (max 1 D * 2 ^ H) ^ (2 * D) :=
      coeffNorm1_resultant_derivative_le P hD hH
    _ ≤ (2 ^ (2 * D).size) ^ (2 * D) * (2 ^ (D.size + H)) ^ (2 * D) :=
      Nat.mul_le_mul hfactorial (Nat.pow_le_pow_left hA _)
    _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add]

/-- Choose a value cutoff and parameter at powers of two from degree and norm bounds. At the
chosen parameter neither the value section nor the nonzero derivative resultant vanishes. -/
theorem eval₂_ne_zero_at_parameterExclusion {P : Polynomial (Polynomial ℤ)} {D H : ℕ}
    (hP : P ≠ 0) (hres : P.resultant P.derivative ≠ 0)
    (hD : P.natDegree ≤ D) (hH : P.bivariateCoeffNorm1 ≤ 2 ^ H) :
    let a : ℤ := 2 ^ (H + 1)
    let u : ℝ := 2 ^ parameterExclusionExponent D H
    (P.eval (C a)).eval₂ (Int.castRingHom ℝ) u ≠ 0 ∧
      (P.resultant P.derivative).eval₂ (Int.castRingHom ℝ) u ≠ 0 := by
  intro a u
  have ha : a.natAbs = 2 ^ (H + 1) := by simp [a, Int.natAbs_pow]
  have hnonzero : P.eval (C a) ≠ 0 := by
    apply eval_C_ne_zero_of_bivariateCoeffNorm1_add_one_le hP
    rw [ha]
    exact add_one_le_pow_two hH le_rfl
  have exclude {q : Polynomial ℤ} (hq : q ≠ 0)
      (hb : q.coeffNorm1 + 1 ≤ 2 ^ parameterExclusionExponent D H) :
      q.eval₂ (Int.castRingHom ℝ) u ≠ 0 := by
    intro hroot
    have hlt := abs_lt_coeffNorm1_add_one_of_eval₂_eq_zero hq hroot
    rw [abs_of_nonneg (by positivity : 0 ≤ u)] at hlt
    have hle : (q.coeffNorm1 : ℝ) + 1 ≤ u := by
      dsimp [u]
      exact_mod_cast hb
    exact (not_lt_of_ge hle) hlt
  exact ⟨exclude hnonzero (coeffNorm1_eval_C_add_one_le_parameterExclusion hD hH),
    exclude hres (add_one_le_pow_two (resultant_le_pow_two hD hH)
      (Nat.succ_le_succ (le_max_left _ _)))⟩

end Polynomial
