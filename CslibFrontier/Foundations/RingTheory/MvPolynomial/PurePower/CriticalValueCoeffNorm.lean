/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, critical equations in pure-power quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CoeffNorm1
public import CslibFrontier.Foundations.Data.MvPolynomial.ParameterCoeffNorm
public import CslibFrontier.Foundations.Data.Polynomial.BivariateCoeffNorm1
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CharpolyCoeffNorm
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValuePolynomial
import Mathlib.Data.Nat.Size

/-!
# Coefficient norm of the symbolic critical-value polynomial

For an integer input with coefficient norm at most `2 ^ b`, the arity, pure-power degree
and `b` give an explicit binary exponent bounding the coefficient norm of the symbolic
critical-value polynomial. This bound supplies the norm hypothesis for choosing a
parameter that avoids repeated critical values and a prescribed cutoff.

Adapted from `SeparatedPotentialMass` and `ParametricCriticalBounds` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. The lower relations and the deformed potential
share a common norm allowance, and the characteristic-polynomial estimate uses the
sharper residue bound for the actual quotient.
-/

public section

namespace MvPolynomial.CriticalSystem

open MvPolynomial
open scoped BigOperators

private theorem pow_two_le_pow_two {a b : ℕ} (h : a ≤ b) : (2 : ℕ) ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

/-- A common binary norm allowance for the separated critical relations and objective. -/
@[expose] def criticalSystemCoeffNormExponent (n ell b : ℕ) : ℕ :=
  (3 * n + 1).size + ((ell + 1).size + max ((ell + 1) * (n * (4 * ell).size)) b)

/-- A binary coefficient-norm exponent for the symbolic critical-value polynomial of
an input with arity `n`, pure-power degree `ell` and coefficient norm at most `2 ^ b`.
The bound uses the same coefficient allowance for the lower relations and the deformed
potential. -/
@[expose] def parametricValueCoeffNormExponent (n ell b : ℕ) : ℕ :=
  let R := criticalSystemCoeffNormExponent n ell b
  PurePower.multiplicationMatrixCharpolyCoeffNormExponent n ell (ell + 1) R R

/-- The symbolic critical relations and objective share the coefficient-norm budget
`criticalSystemCoeffNormExponent n ell b`. -/
theorem criticalSystem_norm_le {n ell b : ℕ} (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (hb : F.coeffNorm1 ≤ 2 ^ b) :
    let a (i : Fin n) := Polynomial.C (separatedCenters ell i : ℤ)
    let G := F.map Polynomial.C
    let R := criticalSystemCoeffNormExponent n ell b
    (∀ i, ParameterCoeffNorm.norm (criticalLower ell a Polynomial.X G i) ≤ 2 ^ R) ∧
    ParameterCoeffNorm.norm (deformedPolynomial ell a Polynomial.X G) ≤ 2 ^ R := by
  classical
  dsimp only
  let a (i : Fin n) := Polynomial.C (separatedCenters ell i : ℤ)
  let G := F.map Polynomial.C
  let c := n * (4 * ell).size
  let k := (ell + 1).size + max ((ell + 1) * c) b
  change (∀ i, ParameterCoeffNorm.norm (criticalLower ell a Polynomial.X G i) ≤
    2 ^ ((3 * n + 1).size + k)) ∧
    ParameterCoeffNorm.norm (deformedPolynomial ell a Polynomial.X G) ≤
      2 ^ ((3 * n + 1).size + k)
  have hcenter (i : Fin n) : Polynomial.coeffNorm1 (a i) ≤ 2 ^ c := by
    change Polynomial.coeffNorm1 (Polynomial.C (separatedCenters ell i : ℤ)) ≤ 2 ^ c
    rw [Polynomial.coeffNorm1_C, Int.natAbs_natCast, separatedCenters]
    exact (Nat.pow_le_pow_right (by omega : 1 ≤ 4 * ell) (Nat.succ_le_of_lt i.isLt)).trans
      ((Nat.pow_le_pow_left (Nat.lt_size_self (4 * ell)).le _).trans_eq
        (by rw [← pow_mul, Nat.mul_comm]))
  have hpower (i : Fin n) {j : ℕ} (hj : j ≤ ell + 1) :
      Polynomial.coeffNorm1 (a i ^ j) ≤ 2 ^ max ((ell + 1) * c) b := calc
    _ ≤ (2 ^ c) ^ j :=
      (Polynomial.coeffNorm1_pow_le _ _).trans (Nat.pow_le_pow_left (hcenter i) _)
    _ = 2 ^ (j * c) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ _ := pow_two_le_pow_two ((Nat.mul_le_mul_right c hj).trans (le_max_left ..))
  have hscale : Polynomial.coeffNorm1 ((ell + 1 : ℕ) : Polynomial ℤ) ≤ 2 ^ (ell + 1).size := by
    rw [← Polynomial.C_eq_natCast, Polynomial.coeffNorm1_C, Int.natAbs_natCast]
    exact (Nat.lt_size_self _).le
  have hscaled (i : Fin n) {j : ℕ} (hj : j ≤ ell + 1) :
      Polynomial.coeffNorm1 ((ell + 1 : ℕ) * a i ^ j) ≤ 2 ^ k :=
    (Polynomial.coeffNorm1_mul_le _ _).trans
      ((Nat.mul_le_mul hscale (hpower i hj)).trans_eq (pow_add 2 _ _).symm)
  have hX : Polynomial.coeffNorm1 (Polynomial.X : Polynomial ℤ) = 1 := by
    simpa only [mul_one, Polynomial.coeffNorm1_one] using
      Polynomial.coeffNorm1_X_mul (1 : Polynomial ℤ)
  have hG : ParameterCoeffNorm.norm G ≤ 2 ^ max ((ell + 1) * c) b := by
    change ParameterCoeffNorm.norm (F.map Polynomial.C) ≤ _
    rw [ParameterCoeffNorm.map_C]
    exact hb.trans (pow_two_le_pow_two (le_max_right ..))
  have htotal : (3 * n + 1) * 2 ^ k ≤ 2 ^ ((3 * n + 1).size + k) :=
    (Nat.mul_le_mul_right _ (Nat.lt_size_self _).le).trans_eq (pow_add 2 _ _).symm
  constructor
  · intro i
    have hconst : ParameterCoeffNorm.norm (C (a i ^ ell) : MvPolynomial (Fin n) (Polynomial ℤ)) ≤
        2 ^ k := by
      rw [ParameterCoeffNorm.C]
      exact (hpower i (Nat.le_succ _)).trans (pow_two_le_pow_two (Nat.le_add_left ..))
    have hder : ParameterCoeffNorm.norm (C Polynomial.X * pderiv i G) ≤ 2 ^ k := by
      refine (ParameterCoeffNorm.mul_le _ _).trans ?_
      rw [ParameterCoeffNorm.C, hX, one_mul]
      refine (ParameterCoeffNorm.pderiv_le _ _).trans
        ((Nat.mul_le_mul ((totalDegree_map_le Polynomial.C F).trans hF) hG).trans ?_)
      exact (Nat.mul_le_mul_right _ ((Nat.le_succ ell).trans (Nat.lt_size_self _).le)).trans_eq
        (pow_add 2 _ _).symm
    calc
      _ ≤ 2 ^ k + 2 ^ k :=
        (ParameterCoeffNorm.sub_le _ _).trans (Nat.add_le_add hconst hder)
      _ = 2 * 2 ^ k := by rw [two_mul]
      _ ≤ (3 * n + 1) * 2 ^ k := Nat.mul_le_mul_right _ (by have := i.isLt; omega)
      _ ≤ _ := htotal
  · let p (i : Fin n) : MvPolynomial (Fin n) (Polynomial ℤ) :=
      X i ^ (ell + 1) - C ((ell + 1 : ℕ) * a i ^ ell) * X i +
        C ((ell + 1 : ℕ) * a i ^ (ell + 1))
    have hterm (i : Fin n) : ParameterCoeffNorm.norm (p i) ≤ 3 * 2 ^ k := by
      have hp : ParameterCoeffNorm.norm (X i ^ (ell + 1) : MvPolynomial (Fin n) (Polynomial ℤ)) ≤
          2 ^ k := by
        refine (ParameterCoeffNorm.pow_le _ _).trans ?_
        rw [ParameterCoeffNorm.X, one_pow]
        exact Nat.one_le_two_pow
      have hl : ParameterCoeffNorm.norm
          (C ((ell + 1 : ℕ) * a i ^ ell) * X i) ≤ 2 ^ k := by
        refine (ParameterCoeffNorm.mul_le _ _).trans ?_
        rw [ParameterCoeffNorm.C, ParameterCoeffNorm.X, mul_one]
        exact hscaled i (Nat.le_succ _)
      have hc : ParameterCoeffNorm.norm
          (C ((ell + 1 : ℕ) * a i ^ (ell + 1)) : MvPolynomial (Fin n) (Polynomial ℤ)) ≤ 2 ^ k := by
        rw [ParameterCoeffNorm.C]
        exact hscaled i le_rfl
      exact (ParameterCoeffNorm.add_le _ _).trans
        ((Nat.add_le_add ((ParameterCoeffNorm.sub_le _ _).trans (Nat.add_le_add hp hl)) hc).trans_eq
          (by omega))
    have hsum : ParameterCoeffNorm.norm (potentialPolynomial ell a) ≤ n * (3 * 2 ^ k) := by
      change ParameterCoeffNorm.norm (∑ i, p i) ≤ _
      refine (ParameterCoeffNorm.sum_le _ _).trans
        ((Finset.sum_le_sum (fun i _ => hterm i)).trans_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    have hperturb : ParameterCoeffNorm.norm
        (C ((ell + 1 : ℕ) * (Polynomial.X : Polynomial ℤ)) * G) ≤ 2 ^ k := by
      refine (ParameterCoeffNorm.mul_le _ _).trans ?_
      rw [ParameterCoeffNorm.C, mul_comm _ Polynomial.X, Polynomial.coeffNorm1_X_mul]
      exact (Nat.mul_le_mul hscale hG).trans_eq (pow_add 2 _ _).symm
    exact (ParameterCoeffNorm.add_le _ _).trans
      ((Nat.add_le_add hsum hperturb).trans ((show n * (3 * 2 ^ k) + 2 ^ k =
        (3 * n + 1) * 2 ^ k by ring).le.trans htotal))

/-- The symbolic critical-value polynomial has a coefficient-norm bound from the
input degree and the binary exponent of its coefficient norm. -/
theorem parametricValuePolynomial_bivariateCoeffNorm1_le {n ell b : ℕ} (hell : 2 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (hb : F.coeffNorm1 ≤ 2 ^ b) :
    (parametricValuePolynomial (by omega : 1 ≤ ell) F hF).bivariateCoeffNorm1 ≤
      2 ^ parametricValueCoeffNormExponent n ell b := by
  let a (i : Fin n) := Polynomial.C (separatedCenters ell i : ℤ)
  let G := F.map Polynomial.C
  have hG : G.totalDegree ≤ ell := (totalDegree_map_le Polynomial.C F).trans hF
  obtain ⟨hrnorm, hvnorm⟩ := criticalSystem_norm_le (by omega) F hF hb
  exact PurePower.bivariateCoeffNorm1_multiplicationMatrix_charpoly_le_pow_two hell
    (criticalLower ell a Polynomial.X G) (criticalLower_degree ell (by omega) a Polynomial.X G hG)
    hrnorm (deformedPolynomial ell a Polynomial.X G)
    (totalDegree_deformedPolynomial_le ell a Polynomial.X G (hG.trans (Nat.le_succ _)))
    hvnorm

end MvPolynomial.CriticalSystem
