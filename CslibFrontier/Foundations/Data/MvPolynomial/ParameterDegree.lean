/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, degree bounds for polynomial coefficients)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Multivariate polynomials with a bounded degree in the coefficient parameter

The bounds apply coefficientwise in the independent polynomial parameter. Adapted from
`HasParameterDegree` in lean-canny's `ParameterDegree` at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, using coefficient convolution and the
coefficient formula for partial derivatives.
-/

public section

namespace MvPolynomial

/-- Every coefficient polynomial has natural degree at most `h` in the parameter. -/
@[expose] def HasParameterDegree {ι R : Type*} [CommSemiring R]
    (p : MvPolynomial ι (Polynomial R)) (h : ℕ) : Prop :=
  ∀ m, (p.coeff m).natDegree ≤ h

namespace HasParameterDegree

variable {ι R : Type*} [CommSemiring R]
variable {p q : MvPolynomial ι (Polynomial R)} {h k : ℕ}

/-- Increase a bound on the parameter degree. -/
theorem mono (hp : HasParameterDegree p h) (hk : h ≤ k) : HasParameterDegree p k :=
  fun m => (hp m).trans hk

/-- The parameter degree of an outer monomial is bounded by the degree of its coefficient. -/
theorem monomial (m : ι →₀ ℕ) (a : Polynomial R) (ha : a.natDegree ≤ h) :
    HasParameterDegree (MvPolynomial.monomial m a) h := by
  intro j
  classical
  rw [coeff_monomial]
  split_ifs <;> simp [ha]

/-- The parameter degree of an outer constant is bounded by its coefficient's degree. -/
theorem C (a : Polynomial R) (ha : a.natDegree ≤ h) :
    HasParameterDegree (MvPolynomial.C a : MvPolynomial ι (Polynomial R)) h :=
  monomial 0 a ha

/-- An outer indeterminate has parameter degree zero. -/
theorem X (i : ι) : HasParameterDegree (MvPolynomial.X i : MvPolynomial ι (Polynomial R)) 0 :=
  monomial _ 1 (by simp)

/-- Promoting the coefficients of a polynomial to constants gives parameter degree zero. -/
theorem map_C (p : MvPolynomial ι R) : HasParameterDegree (p.map Polynomial.C) 0 := by
  intro m
  rw [coeff_map, Polynomial.natDegree_C]

/-- The sum of two polynomials has parameter degree at most the larger bound. -/
theorem add (hp : HasParameterDegree p h) (hq : HasParameterDegree q k) :
    HasParameterDegree (p + q) (max h k) := by
  intro m
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le_max (hp m) (hq m))

/-- A finite sum preserves any common bound on its terms. -/
theorem sum {J : Type*} (s : Finset J) (f : J → MvPolynomial ι (Polynomial R))
    (hf : ∀ j ∈ s, HasParameterDegree (f j) h) : HasParameterDegree (∑ j ∈ s, f j) h := by
  intro m
  rw [coeff_sum]
  exact Polynomial.natDegree_sum_le_of_forall_le s _ (fun j hj => hf j hj m)

/-- The parameter degrees add under multiplication as upper bounds. -/
theorem mul (hp : HasParameterDegree p h) (hq : HasParameterDegree q k) :
    HasParameterDegree (p * q) (h + k) := by
  intro m
  classical
  rw [coeff_mul]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ =>
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hp j.1) (hq j.2))

/-- Powers multiply the parameter-degree bound by the exponent. -/
theorem pow (hp : HasParameterDegree p h) (j : ℕ) : HasParameterDegree (p ^ j) (j * h) := by
  induction j with
  | zero =>
    simpa only [pow_zero, Nat.zero_mul, MvPolynomial.C_1] using
      (C (ι := ι) (1 : Polynomial R) Polynomial.natDegree_one.le)
  | succ j ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hp

/-- A product is bounded by the sum of the parameter-degree bounds of its factors. -/
theorem prod {J : Type*} (s : Finset J) (f : J → MvPolynomial ι (Polynomial R)) (b : J → ℕ)
    (hf : ∀ j ∈ s, HasParameterDegree (f j) (b j)) :
    HasParameterDegree (∏ j ∈ s, f j) (∑ j ∈ s, b j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty, Finset.sum_empty, MvPolynomial.C_1] using
      (C (ι := ι) (1 : Polynomial R) Polynomial.natDegree_one.le)
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self j s)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Differentiating in an outer variable preserves the parameter-degree bound. -/
theorem pderiv (hp : HasParameterDegree p h) (i : ι) :
    HasParameterDegree (MvPolynomial.pderiv i p) h := by
  intro m
  rw [coeff_pderiv]
  refine Polynomial.natDegree_mul_le.trans ?_
  simpa only [← Nat.cast_add_one, Polynomial.natDegree_natCast, Nat.add_zero] using
    hp (m + Finsupp.single i 1)

/-- Negation preserves the bound on the parameter degree. -/
theorem neg {R : Type*} [CommRing R] {p : MvPolynomial ι (Polynomial R)}
    (hp : HasParameterDegree p h) : HasParameterDegree (-p) h := by
  intro m
  simpa only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, Polynomial.natDegree_neg] using hp m

/-- The difference of two polynomials has parameter degree at most the larger bound. -/
theorem sub {R : Type*} [CommRing R] {p q : MvPolynomial ι (Polynomial R)}
    (hp : HasParameterDegree p h) (hq : HasParameterDegree q k) :
    HasParameterDegree (p - q) (max h k) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

end HasParameterDegree
end MvPolynomial
