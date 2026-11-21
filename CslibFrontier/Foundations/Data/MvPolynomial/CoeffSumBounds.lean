/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
module
-- upstream: candidate (Mathlib, multivariate polynomial coefficient sums)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Weighted coefficient sums of multivariate polynomials

Subadditive and submultiplicative coefficient weights pass to the sum over the monomials.
The same bounds apply to absolute values of integers and to norms of polynomial coefficients.
-/

public section
namespace MvPolynomial

open Finset

variable {ι R S : Type*} [CommSemiring R]

/-- The weighted coefficient sum of a subadditive weight is subadditive. -/
theorem sum_add_le_of_subadditive [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]
    {ν : R → S} (h0 : ν 0 = 0) (hadd : ∀ a b, ν (a + b) ≤ ν a + ν b)
    (p q : MvPolynomial ι R) :
    ((p + q).coeff.sum fun _ a => ν a) ≤
      (p.coeff.sum fun _ a => ν a) + q.coeff.sum fun _ a => ν a := by
  classical
  have hs (r : MvPolynomial ι R) (s : Finset (ι →₀ ℕ)) (h : r.support ⊆ s) :
      (r.coeff.sum fun _ a => ν a) = ∑ i ∈ s, ν (r.coeff i) :=
    Finsupp.sum_of_support_subset r.coeff h (fun _ a => ν a) (fun _ _ => h0)
  let s := p.support ∪ q.support
  rw [hs (p + q) s (fun _ h => support_add h), hs p s subset_union_left,
    hs q s subset_union_right, ← sum_add_distrib]
  exact sum_le_sum fun i _ => by
    simpa only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using hadd (p.coeff i) (q.coeff i)

/-- The weighted coefficient sum of a subadditive, submultiplicative weight is
submultiplicative. -/
theorem sum_mul_le_of_submultiplicative [CommSemiring S] [PartialOrder S] [IsOrderedRing S]
    {ν : R → S} (h0 : ν 0 = 0) (hadd : ∀ a b, ν (a + b) ≤ ν a + ν b)
    (hmul : ∀ a b, ν (a * b) ≤ ν a * ν b) (p q : MvPolynomial ι R) :
    ((p * q).coeff.sum fun _ a => ν a) ≤
      (p.coeff.sum fun _ a => ν a) * q.coeff.sum fun _ a => ν a := by
  classical
  let N : MvPolynomial ι R → S := fun r => r.coeff.sum fun _ a => ν a
  have hN0 : N 0 = 0 := by simp [N, MvPolynomial.sum_def]
  have hNadd : ∀ r s, N (r + s) ≤ N r + N s := sum_add_le_of_subadditive h0 hadd
  change N (p * q) ≤ N p * N q
  conv_lhs => rw [p.as_sum, q.as_sum]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, monomial_mul_monomial]
  calc
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, N (monomial (i + j) (p.coeff i * q.coeff j)) :=
      (le_sum_of_subadditive N hN0.le hNadd _ _).trans
        (sum_le_sum fun i _ => le_sum_of_subadditive N hN0.le hNadd _ _)
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, ν (p.coeff i) * ν (q.coeff j) :=
      sum_le_sum fun i _ => sum_le_sum fun j _ =>
        (sum_monomial_eq h0).trans_le (hmul _ _)
    _ = N p * N q := (sum_mul_sum _ _ _ _).symm

end MvPolynomial
