/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, polynomial substitution)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CoeffNorm1
import CslibFrontier.Foundations.Data.MvPolynomial.Substitution

/-!
# Fixed-power sections of multivariate polynomials

A power section replaces the second variable by a power of the first, keeping the other
variables in order. The substitution multiplies the degree by at most `e + 1` and does
not increase the coefficient norm. Adapted from `PowerSectionPolynomial` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial

variable {m : ℕ}

private noncomputable def powerSectionImage (e : ℕ) :
    Fin (m + 2) → MvPolynomial (Fin (m + 1)) ℤ :=
  Fin.cases (X 0) (Fin.cases (X 0 ^ e) (fun i : Fin m => X i.succ))

/-- Substitute the `e`th power of coordinate zero for coordinate one, keeping the first
coordinate and the trailing parameter block. -/
noncomputable def powerSection (e : ℕ) (P : MvPolynomial (Fin (m + 2)) ℤ) :
    MvPolynomial (Fin (m + 1)) ℤ :=
  aeval (powerSectionImage e) P

/-- Evaluate the section by inserting the power in the second coordinate of the original
polynomial. -/
theorem eval₂_powerSection {S : Type*} [CommRing S] (φ : ℤ →+* S) (e : ℕ)
    (P : MvPolynomial (Fin (m + 2)) ℤ) (t : S) (x : Fin m → S) :
    eval₂ φ (Fin.cons t x) (powerSection e P) =
      eval₂ φ (Fin.cons t (Fin.cons (t ^ e) x)) P := by
  change eval₂ φ (Fin.cons t x) (eval₂ C (powerSectionImage e) P) = _
  rw [← eval₂_assoc]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;>
    simp only [powerSectionImage, Fin.cases_zero, Fin.cases_succ, Fin.cons_zero,
      Fin.cons_succ, eval₂_X, eval₂_pow]

/-- The fixed-power section multiplies total degree by at most `e + 1`. -/
theorem totalDegree_powerSection_le (e : ℕ) (P : MvPolynomial (Fin (m + 2)) ℤ) :
    (powerSection e P).totalDegree ≤ P.totalDegree * (e + 1) := by
  apply totalDegree_aeval_le_mul
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simp [powerSectionImage]
  · exact (totalDegree_pow _ _).trans (by simp)
  · simp [powerSectionImage]

/-- The fixed-power section does not increase the sum of absolute coefficients. -/
theorem coeffNorm1_powerSection_le (e : ℕ) (P : MvPolynomial (Fin (m + 2)) ℤ) :
    (powerSection e P).coeffNorm1 ≤ P.coeffNorm1 := by
  have hnorm (i : Fin (m + 2)) : (powerSectionImage e i).coeffNorm1 ≤ 1 := by
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simp [powerSectionImage]
    · exact (coeffNorm1_pow_le _ _).trans_eq (by simp)
    · simp [powerSectionImage]
  change (aeval (powerSectionImage e) P).coeffNorm1 ≤ ∑ s ∈ P.support, (P.coeff s).natAbs
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
  refine (coeffNorm1_mul_le _ _).trans ?_
  rw [coeffNorm1_C]
  have hprod : (∏ i ∈ s.support, powerSectionImage e i ^ s i).coeffNorm1 ≤ 1 := by
    refine (coeffNorm1_prod_le _ _).trans ?_
    calc
      _ ≤ ∏ i ∈ s.support, (1 : ℕ) :=
        Finset.prod_le_prod fun i _ =>
          (coeffNorm1_pow_le _ _).trans ((Nat.pow_le_pow_left (hnorm i) _).trans_eq (one_pow _))
      _ = 1 := Finset.prod_const_one
  exact (Nat.mul_le_mul_left _ hprod).trans_eq (Nat.mul_one _)

end MvPolynomial
