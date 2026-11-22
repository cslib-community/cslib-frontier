/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, pure-power polynomial quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.ParameterCoeffNorm
public import CslibFrontier.Foundations.Data.Polynomial.BivariateCoeffNorm1
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.MultiplicationMatrix
public import Mathlib.Data.Nat.Size
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Charpoly.CoeffNorm
import CslibFrontier.Foundations.LinearAlgebra.Matrix.DeterminantWeight
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.ResidueCoeffNorm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Coefficient norms of pure-power quotient characteristic polynomials

The Jacobian norm follows from the norms of the lower relations. The finite residue formula
then bounds the positive power traces, and Newton's identity bounds the characteristic
polynomial of multiplication in the quotient. All coefficients lie in `ℤ[X]`.

Adapted from `LeanCanny.CountingHierarchy.QuotientMassBounds` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. The bounds keep their natural-number factors
explicit, use the sharper residue bound, and retain the power of the multiplier's norm.
-/

public section

namespace MvPolynomial.PurePower

/-- Bound the parameter coefficient norm of the Jacobian of the actual pure-power relations. -/
theorem parameterCoeffNorm_jacobian_le {n d R : ℕ}
    (r : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (hr : ∀ i, (r i).totalDegree ≤ d) (hR : ∀ i, ParameterCoeffNorm.norm (r i) ≤ R) :
    ParameterCoeffNorm.norm (jacobian (d + 1) r) ≤ n.factorial * ((d + 1) * (1 + R)) ^ n := by
  classical
  have hentry (i j : Fin n) :
      ParameterCoeffNorm.norm (pderiv j (X i ^ (d + 1) - r i)) ≤ (d + 1) * (1 + R) := by
    have hdeg : (X i ^ (d + 1) - r i).totalDegree ≤ d + 1 := by
      refine (totalDegree_sub _ _).trans (max_le ?_ ((hr i).trans (Nat.le_succ d)))
      rw [totalDegree_X_pow]
    have hnorm : ParameterCoeffNorm.norm (X i ^ (d + 1) - r i) ≤ 1 + R := by
      refine (ParameterCoeffNorm.sub_le _ _).trans (Nat.add_le_add ?_ (hR i))
      simpa only [ParameterCoeffNorm.X, one_pow] using
        ParameterCoeffNorm.pow_le (X i : MvPolynomial (Fin n) (Polynomial ℤ)) (d + 1)
    exact (ParameterCoeffNorm.pderiv_le _ j).trans (Nat.mul_le_mul hdeg hnorm)
  unfold jacobian
  have h := Matrix.det_weight_le ParameterCoeffNorm.zero ParameterCoeffNorm.one.le
    ParameterCoeffNorm.add_le ParameterCoeffNorm.mul_le ParameterCoeffNorm.neg
    (Matrix.of (fun i j => pderiv j (X i ^ (d + 1) - r i)))
    (fun i j => by simpa only [Matrix.of_apply] using hentry i j)
  rwa [Fintype.card_fin] at h

/-- Bound the bivariate coefficient norm of the actual quotient characteristic polynomial.
Here `D` is the quotient dimension, `B` bounds the residue numerator degrees through `D`,
and `A` bounds the geometric growth of the positive power traces. -/
theorem bivariateCoeffNorm1_multiplicationMatrix_charpoly_le {n d Ω V R : ℕ} (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (hr : ∀ i, (r i).totalDegree ≤ d) (hR : ∀ i, ParameterCoeffNorm.norm (r i) ≤ R)
    (hR1 : 1 ≤ R) (v : MvPolynomial (Fin n) (Polynomial ℤ)) (hdeg : v.totalDegree ≤ Ω)
    (hV : ParameterCoeffNorm.norm v ≤ V) (hV1 : 1 ≤ V) :
    let D := (d + 1) ^ n
    let B := D * Ω + n * d
    let A := (B + 1) ^ n * (n.factorial * ((d + 1) * (1 + R)) ^ n) * R ^ B * V
    (multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly.bivariateCoeffNorm1 ≤
      (D + 1) * A ^ D := by
  classical
  dsimp only
  let D := (d + 1) ^ n
  let B := D * Ω + n * d
  let J := n.factorial * ((d + 1) * (1 + R)) ^ n
  let C := (B + 1) ^ n * J * R ^ B
  change _ ≤ (D + 1) * (C * V) ^ D
  have hcard : Fintype.card (NormalIndex n (d + 1)) = D := by
    simp [NormalIndex, D]
  have hC : 1 ≤ C := by
    have hpos : 0 < C := by
      dsimp only [C, J]
      exact Nat.mul_pos (Nat.mul_pos (by positivity) (by positivity)) (by positivity)
    omega
  have hA := Nat.mul_le_mul hC hV1
  rw [show (D + 1) * (C * V) ^ D =
    (Fintype.card (NormalIndex n (d + 1)) + 1) * (C * V) ^
      Fintype.card (NormalIndex n (d + 1)) by rw [hcard]]
  refine Matrix.bivariateCoeffNorm1_charpoly_le_of_trace_pow _ (by simpa only [one_mul] using hA) ?_
  intro k hk hkD
  rw [hcard] at hkD
  rw [multiplicationMatrix_trace_pow d hd r hr v k]
  have hB : (v ^ k * jacobian (d + 1) r).totalDegree ≤ B :=
    (totalDegree_mul _ _).trans (Nat.add_le_add ((totalDegree_pow _ _).trans
      (Nat.mul_le_mul hkD hdeg)) (totalDegree_jacobian_le d r hr))
  have hnum : ParameterCoeffNorm.norm (v ^ k * jacobian (d + 1) r) ≤ V ^ k * J :=
    (ParameterCoeffNorm.mul_le _ _).trans (Nat.mul_le_mul
      ((ParameterCoeffNorm.pow_le _ _).trans (Nat.pow_le_pow_left hV _))
      (parameterCoeffNorm_jacobian_le r hr hR))
  calc
    _ ≤ (B + 1) ^ n * (ParameterCoeffNorm.norm (v ^ k * jacobian (d + 1) r) * R ^ B) :=
      coeffNorm1_residue_le (by omega) hR1 r (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) hR _ hB
    _ ≤ (B + 1) ^ n * ((V ^ k * J) * R ^ B) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hnum)
    _ = C * V ^ k := by dsimp only [C]; ac_rfl
    _ ≤ (C * V) ^ k := by
      rw [mul_pow]
      exact Nat.mul_le_mul_right _ (Nat.le_pow (by omega))

/-- A binary norm budget for quotient characteristic polynomials, with multiplier degree
at most `Ω`, multiplier norm at most `2 ^ bv` and relation norms at most `2 ^ br`. -/
@[expose] def multiplicationMatrixCharpolyCoeffNormExponent (n ell Ω bv br : ℕ) : ℕ :=
  let D := ell ^ n
  let B := D * Ω + n * (ell - 1)
  (D + 1).size + ((B + 1).size * n + (n.size + ell.size + (br + 1)) * n + br * B + bv) * D

/-- Bound the bivariate norm of a quotient characteristic polynomial by a power of two
using the binary budgets of the input norms. -/
theorem bivariateCoeffNorm1_multiplicationMatrix_charpoly_le_pow_two
    {n ell Ω bv br : ℕ} (hell : 2 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (hr : ∀ i, (r i).totalDegree < ell) (hR : ∀ i, ParameterCoeffNorm.norm (r i) ≤ 2 ^ br)
    (v : MvPolynomial (Fin n) (Polynomial ℤ)) (hdeg : v.totalDegree ≤ Ω)
    (hV : ParameterCoeffNorm.norm v ≤ 2 ^ bv) :
    (multiplicationMatrix (by omega : 1 ≤ ell) r hr v).charpoly.bivariateCoeffNorm1 ≤
      2 ^ multiplicationMatrixCharpolyCoeffNormExponent n ell Ω bv br := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ell ≠ 0)
  let D := (d + 1) ^ n
  let B := D * Ω + n * d
  let A := (B + 1) ^ n * (n.factorial * ((d + 1) * (1 + 2 ^ br)) ^ n) * (2 ^ br) ^ B * 2 ^ bv
  have hq : _ ≤ (D + 1) * A ^ D :=
    bivariateCoeffNorm1_multiplicationMatrix_charpoly_le (by omega) r
      (fun i => Nat.le_of_lt_succ (hr i)) hR Nat.one_le_two_pow v hdeg hV Nat.one_le_two_pow
  have hscale : (d + 1) * (1 + 2 ^ br) ≤ 2 ^ ((d + 1).size + (br + 1)) := by
    rw [pow_add 2 (d + 1).size, pow_succ (2 : ℕ) br]
    exact Nat.mul_le_mul (Nat.lt_size_self _).le (by have := Nat.one_le_two_pow (n := br); omega)
  have hJ : n.factorial * ((d + 1) * (1 + 2 ^ br)) ^ n ≤
      2 ^ ((n.size + (d + 1).size + (br + 1)) * n) := by
    rw [Nat.add_assoc, pow_mul, pow_add 2 n.size, mul_pow (2 ^ n.size)]
    exact Nat.mul_le_mul (n.factorial_le_pow.trans (Nat.pow_le_pow_left (Nat.lt_size_self _).le _))
      (Nat.pow_le_pow_left hscale _)
  have hA : A ≤ 2 ^ ((B + 1).size * n + (n.size + (d + 1).size + (br + 1)) * n +
      br * B + bv) := by
    dsimp only [A]
    conv_rhs =>
      rw [pow_add 2 _ bv, pow_add 2 _ (br * B),
        pow_add 2 ((B + 1).size * n), pow_mul 2 (B + 1).size, pow_mul 2 br B]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.lt_size_self _).le _) hJ))
  refine hq.trans ((Nat.mul_le_mul (Nat.lt_size_self _).le (Nat.pow_le_pow_left hA _)).trans_eq ?_)
  rw [← pow_mul, ← pow_add]
  simp only [multiplicationMatrixCharpolyCoeffNormExponent, Nat.succ_sub_one]
  rfl

/-- Bound the integer determinant of multiplication in a pure-power quotient by the
characteristic polynomial norm budget. Embed the inputs as constant parameter polynomials
and use the degree-zero characteristic coefficient. -/
theorem natAbs_multiplicationMatrix_det_le_pow_two {n ell Ω bv br : ℕ} (hell : 2 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) ℤ)
    (hr : ∀ i, (r i).totalDegree < ell) (hR : ∀ i, (r i).coeffNorm1 ≤ 2 ^ br)
    (v : MvPolynomial (Fin n) ℤ) (hdeg : v.totalDegree ≤ Ω) (hV : v.coeffNorm1 ≤ 2 ^ bv) :
    (multiplicationMatrix (by omega : 1 ≤ ell) r hr v).det.natAbs ≤
      2 ^ multiplicationMatrixCharpolyCoeffNormExponent n ell Ω bv br := by
  let M := multiplicationMatrix (by omega : 1 ≤ ell) r hr v
  have h := bivariateCoeffNorm1_multiplicationMatrix_charpoly_le_pow_two hell
    (fun i => (r i).map Polynomial.C)
    (fun i => (totalDegree_map_le Polynomial.C _).trans_lt (hr i))
    (fun i => by simpa only [ParameterCoeffNorm.map_C] using hR i)
    (v.map Polynomial.C) ((totalDegree_map_le _ _).trans hdeg)
    (by simpa only [ParameterCoeffNorm.map_C] using hV)
  have hmap : (M.charpoly.map Polynomial.C).bivariateCoeffNorm1 ≤
      2 ^ multiplicationMatrixCharpolyCoeffNormExponent n ell Ω bv br := by
    dsimp only [M]
    rw [← Matrix.charpoly_map, multiplicationMatrix_map]
    exact h
  have hc := (Polynomial.coeffNorm1_coeff_le_bivariateCoeffNorm1 (M.charpoly.map Polynomial.C)
    0).trans hmap
  rw [Matrix.det_eq_sign_charpoly_coeff]
  simpa only [Polynomial.coeff_map, Polynomial.coeffNorm1_C, Int.natAbs_mul, Int.natAbs_pow,
    Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul, M] using hc

end MvPolynomial.PurePower
