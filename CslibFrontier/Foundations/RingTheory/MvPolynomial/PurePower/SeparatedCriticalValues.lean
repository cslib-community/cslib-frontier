/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, critical equations in pure-power quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CriticalSystem
public import Mathlib.Analysis.Complex.Basic
import CslibFrontier.Foundations.RingTheory.RootsOfUnity.SeparatedSums
import Mathlib.Tactic.Ring

/-!
# Distinct initial values for a separated power potential

At the separated centers times roots of unity, the initial potential is affine in the
root tuple. The weights are powers of an explicit integer base and distinguish all such
tuples. This is the distinct-value step for initial characteristic-polynomial separability.

Adapted from `SeparatedCriticalValues` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial.CriticalSystem

open scoped BigOperators

private theorem eval_potentialPolynomial_mul_of_pow_eq_one {S : Type*} [CommRing S] {n : ℕ}
    (ell : ℕ) (a z : Fin n → S) (hz : ∀ i, z i ^ ell = 1) :
    eval (fun i => a i * z i) (potentialPolynomial ell a) =
      (ell + 1 : ℕ) * (∑ i, a i ^ (ell + 1)) -
        (ell : S) * (∑ i, a i ^ (ell + 1) * z i) := by
  rw [potentialPolynomial, map_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_add, map_sub, map_mul, map_pow, eval_X, eval_C, mul_pow,
    pow_succ, hz, Nat.cast_add, Nat.cast_one]
  ring

/-- Initial potential values at the separated centers distinguish tuples of roots of unity. -/
theorem eq_of_eval_potentialPolynomial_eq_of_pow_eq_one {n ell : ℕ} (hell : 1 ≤ ell)
    {z w : Fin n → ℂ} (hz : ∀ i, z i ^ ell = 1) (hw : ∀ i, w i ^ ell = 1)
    (hvalue : eval (fun i => (separatedCenters ell i : ℂ) * z i)
        (potentialPolynomial ell (fun i => (separatedCenters ell i : ℂ))) =
      eval (fun i => (separatedCenters ell i : ℂ) * w i)
        (potentialPolynomial ell (fun i => (separatedCenters ell i : ℂ)))) : z = w := by
  let R := (4 * ell) ^ (ell + 1)
  have hR : 2 * ell + 1 ≤ R := by
    have hbase : 4 * ell ≤ (4 * ell) ^ (ell + 1) := le_self_pow₀ (by omega) (by omega)
    omega
  have hell0 : ell ≠ 0 := by omega
  have hcast : (ell : ℂ) ≠ 0 := by exact_mod_cast hell0
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast (by omega : R ≠ 0)
  rw [eval_potentialPolynomial_mul_of_pow_eq_one ell _ z hz,
    eval_potentialPolynomial_mul_of_pow_eq_one ell _ w hw] at hvalue
  have hs := mul_left_cancel₀ hcast (sub_right_inj.mp hvalue)
  have hweight (i : Fin n) : (separatedCenters ell i : ℂ) ^ (ell + 1) =
      (R : ℂ) * (R : ℂ) ^ i.val := by
    change (((4 * ell) ^ (i.val + 1) : ℕ) : ℂ) ^ (ell + 1) = _
    rw [Nat.cast_pow, pow_right_comm, ← Nat.cast_pow]
    change (R : ℂ) ^ (i.val + 1) = _
    rw [pow_succ']
  simp_rw [hweight, mul_assoc] at hs
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hs
  exact Complex.eq_of_weighted_sum_eq_of_pow_eq_one hell0 hR hz hw (mul_left_cancel₀ hR0 hs)

end MvPolynomial.CriticalSystem
