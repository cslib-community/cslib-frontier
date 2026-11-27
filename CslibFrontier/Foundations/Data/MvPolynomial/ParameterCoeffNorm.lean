/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial coefficient norms)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CoeffNorm1
public import CslibFrontier.Foundations.Data.Polynomial.CoeffNorm1
public import Mathlib.Algebra.MvPolynomial.Equiv
import CslibFrontier.Foundations.Data.MvPolynomial.CoeffSumBounds
import CslibFrontier.Foundations.Data.MvPolynomial.Substitution
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Coefficient norms with polynomial parameters

Sum the ordinary integer polynomial coefficient norms over the outer monomials. This gives
arithmetic bounds used in the pure-power residue estimate. Constant promotion preserves the
integer multivariate coefficient norm. With multivariate coefficients, the sum of the
individual coefficient norms equals the norm after joining the variable blocks or
bringing a univariate outer variable into the multivariate index type.

Adapted from `LeanCanny.CountingHierarchy.ParameterMass` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial

private theorem coeffNorm1_eq_sum_of_coefficients {ι κ J : Type*}
    (q : MvPolynomial ι ℤ) (s : Finset J) (f : J → MvPolynomial κ ℤ)
    (e : (Σ _ : J, κ →₀ ℕ) ≃ (ι →₀ ℕ)) (hzero : ∀ j ∉ s, f j = 0)
    (hcoeff : ∀ j m, q.coeff (e ⟨j, m⟩) = (f j).coeff m) :
    q.coeffNorm1 = ∑ j ∈ s, (f j).coeffNorm1 := by
  classical
  symm
  unfold coeffNorm1
  rw [Finset.sum_sigma']
  refine Finset.sum_equiv e ?_ ?_
  · rintro ⟨j, m⟩
    simp only [Finset.mem_sigma, mem_support_iff, hcoeff]
    refine ⟨And.right, fun hm => ⟨?_, hm⟩⟩
    by_contra hj
    exact hm (by rw [hzero j hj]; rfl)
  · rintro ⟨j, m⟩ _
    rw [hcoeff]

/-- Joining two variable blocks preserves the sum of their nested integer coefficient norms. -/
theorem coeffNorm1_sumRingEquiv_symm {ι κ : Type*}
    (p : MvPolynomial ι (MvPolynomial κ ℤ)) :
    ((sumRingEquiv ℤ ι κ).symm p).coeffNorm1 = ∑ m ∈ p.support, (p.coeff m).coeffNorm1 := by
  let q := (sumRingEquiv ℤ ι κ).symm p
  let e : (Σ _ : ι →₀ ℕ, κ →₀ ℕ) ≃ (ι ⊕ κ →₀ ℕ) :=
    (Equiv.sigmaEquivProd _ _).trans Finsupp.sumFinsuppEquivProdFinsupp.symm
  refine coeffNorm1_eq_sum_of_coefficients q p.support p.coeff e
    (fun _ hm => notMem_support_iff.mp hm) ?_
  intro a b
  change q.coeff (a.sumElim b) = (p.coeff a).coeff b
  simpa only [q, RingEquiv.apply_symm_apply] using (coeff_coeff_sumRingEquiv q a b).symm

/-- Bringing the outer variable into the index type preserves the sum of the
integer coefficient norms, with the outer variable indexed by `none`. -/
theorem coeffNorm1_optionEquivLeft_symm {κ : Type*} (p : Polynomial (MvPolynomial κ ℤ)) :
    ((optionEquivLeft ℤ κ).symm p).coeffNorm1 = p.sum (fun _ q => q.coeffNorm1) := by
  let q := (optionEquivLeft ℤ κ).symm p
  let e : (Σ _ : ℕ, κ →₀ ℕ) ≃ (Option κ →₀ ℕ) :=
    (Equiv.sigmaEquivProd _ _).trans Finsupp.optionEquiv.symm
  rw [Polynomial.sum_def]
  refine coeffNorm1_eq_sum_of_coefficients q p.support p.coeff e
    (fun j hj => Polynomial.notMem_support_iff.mp hj) ?_
  intro j m
  change q.coeff (m.optionElim j) = (p.coeff j).coeff m
  simpa only [q, AlgEquiv.apply_symm_apply] using (optionEquivLeft_coeff_coeff ℤ q j m).symm

end MvPolynomial

namespace MvPolynomial.ParameterCoeffNorm

open MvPolynomial
open scoped BigOperators

variable {ι : Type*}

/-- Sum the integer coefficient norms of the outer polynomial's coefficients. -/
@[expose] noncomputable def norm (p : MvPolynomial ι (Polynomial ℤ)) : ℕ :=
  ∑ m ∈ p.support, Polynomial.coeffNorm1 (p.coeff m)

/-- The zero polynomial has norm zero. -/
@[simp] theorem zero : norm (0 : MvPolynomial ι (Polynomial ℤ)) = 0 := by simp [norm]

/-- A monomial has the norm of its coefficient. -/
@[simp] theorem monomial (m : ι →₀ ℕ) (a : Polynomial ℤ) :
    norm (MvPolynomial.monomial m a) = Polynomial.coeffNorm1 a := by
  rw [norm, ← MvPolynomial.sum_def]
  exact MvPolynomial.sum_monomial_eq (by simp)

/-- A constant has the norm of its coefficient. -/
@[simp] theorem C (a : Polynomial ℤ) :
    norm (MvPolynomial.C a : MvPolynomial ι (Polynomial ℤ)) = Polynomial.coeffNorm1 a :=
  monomial 0 a
/-- The constant one has norm one. -/
@[simp] theorem one : norm (1 : MvPolynomial ι (Polynomial ℤ)) = 1 := by
  rw [← MvPolynomial.C_1, C, ← Polynomial.C_1, Polynomial.coeffNorm1_C]
  rfl
/-- An outer variable has norm one. -/
@[simp] theorem X (i : ι) : norm (MvPolynomial.X i : MvPolynomial ι (Polynomial ℤ)) = 1 := by
  change norm (MvPolynomial.monomial (Finsupp.single i 1) 1) = 1
  rw [monomial, ← Polynomial.C_1, Polynomial.coeffNorm1_C]
  rfl

/-- Promoting integer coefficients to constant parameter polynomials preserves norm. -/
@[simp] theorem map_C (p : MvPolynomial ι ℤ) :
    norm (p.map Polynomial.C) = MvPolynomial.coeffNorm1 p := by
  simp only [norm, MvPolynomial.support_map_of_injective p Polynomial.C_injective,
    MvPolynomial.coeff_map, Polynomial.coeffNorm1_C, MvPolynomial.coeffNorm1]

/-- Each parameter coefficient is bounded by the full norm. -/
theorem coeff_le (p : MvPolynomial ι (Polynomial ℤ)) (m : ι →₀ ℕ) :
    Polynomial.coeffNorm1 (p.coeff m) ≤ norm p := by
  simpa only [norm, MvPolynomial.sum_def] using
    Finsupp.single_eval_le_sum p.coeff (g := Polynomial.coeffNorm1)
      Polynomial.coeffNorm1_zero (fun _ => Nat.zero_le _) m

/-- Specializing the coefficient parameter multiplies the norm bound by at most
`a.natAbs ^ D` when every parameter coefficient has degree at most `D`. -/
theorem coeffNorm1_map_evalRingHom_le (p : MvPolynomial ι (Polynomial ℤ)) (a : ℤ)
    (ha : 1 ≤ a.natAbs) {D : ℕ} (hD : ∀ m, (p.coeff m).natDegree ≤ D) :
    (p.map (Polynomial.evalRingHom a)).coeffNorm1 ≤ norm p * a.natAbs ^ D := by
  rw [MvPolynomial.coeffNorm1_eq_sum_of_support_subset _ _ (support_map_subset _ _),
    norm, Finset.sum_mul]
  simp only [coeff_map, Polynomial.coe_evalRingHom]
  refine Finset.sum_le_sum fun m _ => (Polynomial.natAbs_eval_le_coeffNorm1 _ a ha).trans ?_
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right ha (hD m))

/-- The parameter coefficient norm satisfies the triangle inequality. -/
theorem add_le (p q : MvPolynomial ι (Polynomial ℤ)) : norm (p + q) ≤ norm p + norm q :=
  sum_add_le_of_subadditive Polynomial.coeffNorm1_zero Polynomial.coeffNorm1_add_le p q

/-- Negation preserves the parameter coefficient norm. -/
@[simp] theorem neg (p : MvPolynomial ι (Polynomial ℤ)) : norm (-p) = norm p := by
  simp [norm]

/-- The norm of a difference is bounded by the sum of the norms. -/
theorem sub_le (p q : MvPolynomial ι (Polynomial ℤ)) : norm (p - q) ≤ norm p + norm q := by
  simpa only [sub_eq_add_neg, neg] using add_le p (-q)

/-- A finite sum has norm at most the sum of the norms. -/
theorem sum_le {J : Type*} (s : Finset J) (p : J → MvPolynomial ι (Polynomial ℤ)) :
    norm (∑ j ∈ s, p j) ≤ ∑ j ∈ s, norm (p j) :=
  Finset.le_sum_of_subadditive norm zero.le add_le s p

/-- The parameter coefficient norm is submultiplicative. -/
theorem mul_le (p q : MvPolynomial ι (Polynomial ℤ)) : norm (p * q) ≤ norm p * norm q :=
  sum_mul_le_of_submultiplicative Polynomial.coeffNorm1_zero Polynomial.coeffNorm1_add_le
    Polynomial.coeffNorm1_mul_le p q

/-- Powers satisfy the corresponding coefficient norm bound. -/
theorem pow_le (p : MvPolynomial ι (Polynomial ℤ)) (n : ℕ) : norm (p ^ n) ≤ norm p ^ n :=
  sum_pow_le_of_submultiplicative Polynomial.coeffNorm1_zero Polynomial.coeffNorm1_one.le
    Polynomial.coeffNorm1_add_le Polynomial.coeffNorm1_mul_le p n

/-- A finite product has norm at most the product of the norms. -/
theorem prod_le {J : Type*} (s : Finset J) (p : J → MvPolynomial ι (Polynomial ℤ)) :
    norm (∏ j ∈ s, p j) ≤ ∏ j ∈ s, norm (p j) :=
  Finset.le_prod_of_submultiplicative norm one.le mul_le s p

/-- An outer partial derivative increases the norm by at most the outer total degree. -/
theorem pderiv_le (p : MvPolynomial ι (Polynomial ℤ)) (i : ι) :
    norm (pderiv i p) ≤ p.totalDegree * norm p :=
  sum_pderiv_le_of_subadditive Polynomial.coeffNorm1_zero Polynomial.coeffNorm1_add_le p i

end MvPolynomial.ParameterCoeffNorm
