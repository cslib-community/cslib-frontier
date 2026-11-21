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
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Charpoly.CoeffNorm
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.ResidueCoeffNorm

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

open scoped BigOperators

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
  rw [jacobian, Matrix.det_apply]
  refine (ParameterCoeffNorm.sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), ((d + 1) * (1 + R)) ^ n := by
      apply Finset.sum_le_sum
      intro σ _
      have hsign (p : MvPolynomial (Fin n) (Polynomial ℤ)) :
          ParameterCoeffNorm.norm (Equiv.Perm.sign σ • p) = ParameterCoeffNorm.norm p := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · rw [h, one_smul]
        · rw [h, Units.neg_smul, one_smul, ParameterCoeffNorm.neg]
      rw [hsign]
      refine (ParameterCoeffNorm.prod_le _ _).trans ?_
      simpa only [Matrix.of_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (Finset.prod_le_prod fun i _ => hentry (σ i) i :
          (∏ i : Fin n, ParameterCoeffNorm.norm (pderiv i (X (σ i) ^ (d + 1) - r (σ i)))) ≤
            ∏ _i : Fin n, (d + 1) * (1 + R))
    _ = _ := by simp [Fintype.card_perm]

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

end MvPolynomial.PurePower
