/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.Substitution
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Module.Pi

/-!
# Restricting a multivariate polynomial to an affine line

Substituting `uᵢ + t vᵢ` for each variable gives a univariate polynomial. Its degree is bounded
by the total degree, by the sum of individual degrees of the moving coordinates, and by the
degree of the single variable in the axis-parallel case.
-/

public section

namespace MvPolynomial

open Finset

variable {ι R : Type*} [CommSemiring R]

/-- Polynomial obtained by evaluating `P` on the parameterized affine line `u + t • v`. -/
noncomputable def restrictAffineLine (P : MvPolynomial ι R) (u v : ι → R) : Polynomial R :=
  aeval (fun i => Polynomial.C (u i) + Polynomial.C (v i) * Polynomial.X) P

theorem eval_restrictAffineLine (P : MvPolynomial ι R) (u v : ι → R) (t : R) :
    (P.restrictAffineLine u v).eval t = eval (u + t • v) P := by
  rw [restrictAffineLine, eval_polynomial_aeval]
  exact congrArg (fun x => eval x P) (by
    funext i
    simp only [Polynomial.eval_add, Polynomial.eval_C_mul, Polynomial.eval_C, Polynomial.eval_X,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm (v i) t])

private theorem natDegree_affineInput_le (u v : R) :
    (Polynomial.C u + Polynomial.C v * Polynomial.X).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
  exact Polynomial.natDegree_mul_le.trans (by
    rw [Polynomial.natDegree_C, zero_add]
    exact Polynomial.natDegree_X_le)

/-- Restriction to any affine line has degree at most the total degree. -/
theorem natDegree_restrictAffineLine_le (P : MvPolynomial ι R) (u v : ι → R) :
    (P.restrictAffineLine u v).natDegree ≤ P.totalDegree := by
  unfold restrictAffineLine
  simpa only [Nat.mul_one] using natDegree_aeval_le_mul
    (fun i => natDegree_affineInput_le (u i) (v i)) P

/-- Only variables with nonzero direction coordinates contribute to the degree. -/
theorem natDegree_restrictAffineLine_le_sum_degreeOf [Fintype ι] [DecidableEq R]
    (P : MvPolynomial ι R) (u v : ι → R) :
    (P.restrictAffineLine u v).natDegree ≤ ∑ i with v i ≠ 0, P.degreeOf i := by
  classical
  unfold restrictAffineLine
  refine natDegree_aeval_le_of_support (w := fun i => if v i = 0 then 0 else 1) ?_ ?_
  · intro i
    by_cases hi : v i = 0
    · simp [hi]
    · simpa only [ite_eq_right hi] using natDegree_affineInput_le (u i) (v i)
  · intro s hs
    rw [Finsupp.sum]
    calc
      _ ≤ ∑ i, P.degreeOf i * (if v i = 0 then 0 else 1) := by
        refine (sum_le_sum fun i _ =>
          Nat.mul_le_mul_right _ (degreeOf_le_iff.mp le_rfl s hs)).trans ?_
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
      _ = _ := by simp [Finset.sum_filter, mul_ite, ne_eq, ite_not]

/-- Axis-parallel restriction has degree at most that of the moving variable. -/
theorem natDegree_restrictAffineLine_single_le [DecidableEq ι]
    (P : MvPolynomial ι R) (u : ι → R) (i : ι) :
    (P.restrictAffineLine u (Pi.single i (1 : R))).natDegree ≤ P.degreeOf i := by
  classical
  unfold restrictAffineLine
  refine natDegree_aeval_le_of_support (w := fun j => if j = i then 1 else 0) ?_ ?_
  · intro j
    by_cases hj : j = i
    · rw [ite_eq_left hj]
      exact natDegree_affineInput_le _ _
    · simp [hj]
  · intro s hs
    rw [Finsupp.sum]
    simp only [mul_ite, mul_one, mul_zero]
    by_cases hi : i ∈ s.support
    · simpa [hi] using degreeOf_le_iff.mp (le_rfl : P.degreeOf i ≤ P.degreeOf i) s hs
    · simp [hi]

end MvPolynomial
