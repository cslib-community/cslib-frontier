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
public import Mathlib.Data.Nat.Size
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.CoeffNormBound
import CslibFrontier.Foundations.RingTheory.Polynomial.ValueResultant

/-!
# Dyadic bounds on polynomial values at real algebraic roots

The degree bounds and logarithmic coefficient norm bounds on an integer source
and test give a dyadic interval for the magnitude of each nonzero test value.
Cauchy's root bound controls the evaluation radius, and the reciprocal-root
bound for the value resultant separates nonzero values from zero.

Adapted from `AlgebraicTestValueBounds` in lean-canny at commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

/-- One exponent controls the reciprocal lower bound and the upper bound for the test magnitude.
`D` and `E` bound the source and test degrees, and `2 ^ b` and `2 ^ c` bound their norms. -/
@[expose] def algebraicValuePrecision (D E b c : ℕ) : ℕ :=
  let N := D + E
  max ((N.size + max b (c + 1)) * N + 1) (c + E * (b + 1))

/-- One dyadic precision for a qualifying test and all derivatives, when both
input polynomials have degree at most `D` and coefficient norm at most `2 ^ b`. -/
@[expose] def derivativeRootLabelPrecision (D b : ℕ) : ℕ :=
  algebraicValuePrecision D D b (iterateDerivativeNormExponent D b)

private theorem coeffNorm1_valueResultant_le_two_pow {p g : Polynomial ℤ} {D E b c : ℕ}
    (hD : p.natDegree ≤ D) (hE : g.natDegree ≤ E)
    (hb : p.coeffNorm1 ≤ 2 ^ b) (hc : g.coeffNorm1 ≤ 2 ^ c) :
    (p.valueResultant g).coeffNorm1 ≤ 2 ^ (((D + E).size + max b (c + 1)) * (D + E)) := by
  let N := D + E
  let A := max p.coeffNorm1 (1 + g.coeffNorm1)
  have hN : p.natDegree + g.natDegree ≤ N := Nat.add_le_add hD hE
  have hA₁ : 1 ≤ A := (Nat.le_add_right 1 _).trans (le_max_right _ _)
  have hc' : 1 + g.coeffNorm1 ≤ 2 ^ (c + 1) := by
    rw [Nat.add_comm 1]
    exact Nat.succ_le_of_lt (hc.trans_lt (Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self c)))
  have hA : A ≤ 2 ^ max b (c + 1) := max_le
    (hb.trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _)))
    (hc'.trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _)))
  calc
    _ ≤ N.factorial * A ^ N := (coeffNorm1_valueResultant_le p g).trans
      (Nat.mul_le_mul (Nat.factorial_le hN) (Nat.pow_le_pow_right hA₁ hN))
    _ ≤ (2 ^ N.size) ^ N * (2 ^ max b (c + 1)) ^ N :=
      Nat.mul_le_mul (N.factorial_le_pow.trans (Nat.pow_le_pow_left N.lt_size_self.le N))
        (Nat.pow_le_pow_left hA N)
    _ = _ := by rw [← mul_pow, ← pow_add, ← pow_mul]

/-- At a real root of a nonzero integer polynomial, a test value is either zero or its
absolute value lies between the reciprocal of the chosen power of two and that power. -/
theorem eval₂_eq_zero_or_dyadic_bounds {p g : Polynomial ℤ} (hp : p ≠ 0) {D E b c : ℕ}
    (hD : p.natDegree ≤ D) (hE : g.natDegree ≤ E)
    (hb : p.coeffNorm1 ≤ 2 ^ b) (hc : g.coeffNorm1 ≤ 2 ^ c)
    {x : ℝ} (hx : p.eval₂ (Int.castRingHom ℝ) x = 0) :
    let v := g.eval₂ (Int.castRingHom ℝ) x
    let R := (2 : ℝ) ^ algebraicValuePrecision D E b c
    v = 0 ∨ (R⁻¹ ≤ |v| ∧ |v| ≤ R) := by
  dsimp only
  let v := g.eval₂ (Int.castRingHom ℝ) x
  by_cases hv : v = 0
  · exact Or.inl hv
  right
  constructor
  · let N := D + E
    let F := p.valueResultant g
    have hr : F.eval₂ (Int.castRingHom ℝ) v = 0 := by
      simpa only [F, v, IsRoot.def, eval_map] using
        isRoot_valueResultant hp g (by simpa only [IsRoot.def, eval_map] using hx)
    have hsep := inv_coeffNorm1_add_one_lt_abs_of_eval₂_eq_zero
      (valueResultant_ne_zero_and_natDegree hp g).1 hr hv
    have hM : F.coeffNorm1 + 1 ≤ 2 ^ algebraicValuePrecision D E b c := by
      apply Nat.succ_le_of_lt
      apply (coeffNorm1_valueResultant_le_two_pow hD hE hb hc).trans_lt
      apply Nat.pow_lt_pow_right one_lt_two
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self ((N.size + max b (c + 1)) * N))
        (le_max_left _ _)
    have hMR : (F.coeffNorm1 : ℝ) + 1 ≤ (2 : ℝ) ^ algebraicValuePrecision D E b c := by
      exact_mod_cast hM
    exact (inv_anti₀ (by positivity) hMR).trans hsep.le
  · have hroot := abs_lt_coeffNorm1_add_one_of_eval₂_eq_zero hp hx
    have hM : p.coeffNorm1 + 1 ≤ 2 ^ (b + 1) :=
      Nat.succ_le_of_lt (hb.trans_lt (Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self b)))
    have hMR : (p.coeffNorm1 : ℝ) + 1 ≤ (2 : ℝ) ^ (b + 1) := by exact_mod_cast hM
    have hR : (1 : ℝ) ≤ (2 : ℝ) ^ (b + 1) := one_le_pow₀ (by norm_num)
    have hcoeff : (g.coeffNorm1 : ℝ) ≤ (2 : ℝ) ^ c := by exact_mod_cast hc
    calc
      _ ≤ (g.coeffNorm1 : ℝ) * ((2 : ℝ) ^ (b + 1)) ^ g.natDegree :=
        abs_eval₂_le_coeffNorm1_mul_pow g hR (hroot.le.trans hMR)
      _ ≤ (2 : ℝ) ^ c * ((2 : ℝ) ^ (b + 1)) ^ E :=
        mul_le_mul hcoeff (pow_le_pow_right₀ hR hE) (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (c + E * (b + 1)) := by rw [← pow_mul, ← pow_add, Nat.mul_comm E]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (le_max_right _ _)

end Polynomial
