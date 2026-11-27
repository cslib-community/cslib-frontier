/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, multivariate polynomial coefficients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CoeffNorm1
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# First-variable coefficient polynomials

Viewing a multivariate polynomial as univariate in coordinate zero gives coefficient
polynomials in the remaining coordinates. The evaluation agrees with successive substitution,
and each coefficient inherits the original degree and coefficient norm bounds.

Adapted from `FirstVariableCoefficients` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial

variable {n : ℕ} {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Evaluating the polynomial split at coordinate zero agrees with evaluating the
original multivariate polynomial at the assembled point. -/
theorem eval₂_finSuccEquiv (f : R →+* S) (y : S) (x : Fin n → S)
    (P : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n P).eval₂ (eval₂Hom f x) y = eval₂ f (Fin.cons y x) P := by
  have h : (Polynomial.eval₂RingHom (eval₂Hom f x) y).comp (finSuccEquiv R n).toRingHom =
      eval₂Hom f (Fin.cons y x) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [eval₂Hom_C]
      change (finSuccEquiv R n (C c)).eval₂ (eval₂Hom f x) y = f c
      simp only [finSuccEquiv_apply, eval₂Hom_C, RingHom.comp_apply, Polynomial.eval₂_C]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [finSuccEquiv_X_zero]
      · simp [finSuccEquiv_X_succ]
  exact DFunLike.congr_fun h P

/-- Removing the first variable cannot increase the total degree of a coefficient. -/
theorem totalDegree_coeff_finSuccEquiv_le (P : MvPolynomial (Fin (n + 1)) R) (i : ℕ) :
    ((finSuccEquiv R n P).coeff i).totalDegree ≤ P.totalDegree := by
  by_cases h : (finSuccEquiv R n P).coeff i = 0
  · simp [h]
  · exact (Nat.le_add_right _ _).trans (totalDegree_coeff_finSuccEquiv_add_le P i h)

/-- Each coefficient polynomial uses a subset of the integer coefficients of the input. -/
theorem coeffNorm1_coeff_finSuccEquiv_le (P : MvPolynomial (Fin (n + 1)) ℤ) (i : ℕ) :
    ((finSuccEquiv ℤ n P).coeff i).coeffNorm1 ≤ P.coeffNorm1 := by
  let Q := (finSuccEquiv ℤ n P).coeff i
  have hinj : Function.Injective (Finsupp.cons i : (Fin n →₀ ℕ) → (Fin (n + 1) →₀ ℕ)) := by
    intro a b h
    simpa only [Finsupp.tail_cons] using congrArg Finsupp.tail h
  calc
    Q.coeffNorm1 = ∑ m ∈ Q.support.image (Finsupp.cons i), (P.coeff m).natAbs := by
      rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
      simp only [coeffNorm1, Q, finSuccEquiv_coeff_coeff]
    _ ≤ P.coeffNorm1 := by
      dsimp only [Q]
      rw [image_support_finSuccEquiv]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)

end MvPolynomial
