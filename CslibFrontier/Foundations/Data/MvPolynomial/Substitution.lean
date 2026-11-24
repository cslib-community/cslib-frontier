/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, degree bound and chain rule for substitution)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.BigOperators
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees

/-!
# Substitution: total degree and the chain rule

Substituting polynomials of total degree at most `k` for the variables of a polynomial `P`
multiplies the total degree by at most `k` (`MvPolynomial.totalDegree_aeval_le_mul`). In
particular, an affine change of variables does not raise the total degree
(`MvPolynomial.totalDegree_aeval_le`). The same bound holds for the degree of a substitution of
univariate polynomials (`MvPolynomial.natDegree_aeval_le_mul`). Partial derivatives of a
substitution follow the chain rule (`MvPolynomial.pderiv_aeval`).

## Main results

* `MvPolynomial.totalDegree_aeval_le_mul`: substituting polynomials of degree at most `k`
  multiplies the degree by at most `k`.
* `MvPolynomial.totalDegree_aeval_le`: substituting polynomials of degree at most `1` does not raise
  the degree.
* `MvPolynomial.totalDegree_sumRingEquiv_le`: viewing one variable block as coefficient
  parameters does not raise the degree in the other block.
* `MvPolynomial.eval₂_sumRingEquiv`: evaluate the two blocks separately or together.
* `MvPolynomial.natDegree_aeval_le_of_support`: bound the degree by weighted monomial degrees.
* `MvPolynomial.natDegree_aeval_le_mul`: substituting univariate polynomials of degree at most
  `k`, over an algebra, gives a polynomial of degree at most `k` times the total degree.
* `MvPolynomial.eval_polynomial_aeval`: evaluating a substitution of univariate polynomials.
* `MvPolynomial.pderiv_aeval`: the chain rule for formal partial derivatives.
-/

public section

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-- Substituting polynomials of total degree at most `k` for the variables multiplies the total
degree by at most `k`. -/
theorem totalDegree_aeval_le_mul {g : τ → MvPolynomial σ R} {k : ℕ}
    (hg : ∀ i, (g i).totalDegree ≤ k) (P : MvPolynomial τ R) :
    (aeval g P).totalDegree ≤ P.totalDegree * k := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ s.support, (g i ^ s i).totalDegree
      ≤ ∑ i ∈ s.support, s i * k :=
        Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))
    _ = (s.sum fun _ e => e) * k := by rw [Finsupp.sum, Finset.sum_mul]
    _ ≤ P.totalDegree * k := Nat.mul_le_mul_right _ (le_totalDegree hs)

/-- Substituting polynomials of total degree at most `1` for the variables does not raise the total
degree. -/
theorem totalDegree_aeval_le {g : τ → MvPolynomial σ R} (hg : ∀ i, (g i).totalDegree ≤ 1)
    (P : MvPolynomial τ R) : (aeval g P).totalDegree ≤ P.totalDegree :=
  (totalDegree_aeval_le_mul hg P).trans_eq (Nat.mul_one _)

/-- Retaining one block of variables in the coefficient ring does not increase the
total degree in the other block. -/
theorem totalDegree_sumRingEquiv_le (P : MvPolynomial (σ ⊕ τ) R) :
    (sumRingEquiv R σ τ P).totalDegree ≤ P.totalDegree := by
  let g : σ ⊕ τ → MvPolynomial σ (MvPolynomial τ R) := Sum.elim X (C ∘ X)
  let f := (aeval g).toRingHom.comp (map (C : R →+* MvPolynomial τ R))
  have hf : (sumRingEquiv R σ τ).toRingHom = f := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f, MvPolynomial.algebraMap_eq]
    · intro i
      cases i <;> simp [f, g]
  change ((sumRingEquiv R σ τ).toRingHom P).totalDegree ≤ _
  rw [hf]
  refine (totalDegree_aeval_le (g := g) ?_ _).trans (totalDegree_map_le _ _)
  intro i
  cases i with
  | inl i => exact totalDegree_X_le i
  | inr i => simp [g]

/-- Evaluating a split polynomial evaluates its coefficient variables in the second block
and its remaining variables in the first block. -/
theorem eval₂_sumRingEquiv {S : Type*} [CommSemiring S] (φ : R →+* S)
    (x : σ → S) (z : τ → S) (P : MvPolynomial (σ ⊕ τ) R) :
    eval₂ (eval₂Hom φ z) x (sumRingEquiv R σ τ P) = eval₂ φ (Sum.elim x z) P := by
  have h : (eval₂Hom (eval₂Hom φ z) x).comp (sumRingEquiv R σ τ).toRingHom =
      eval₂Hom φ (Sum.elim x z) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, eval₂Hom_C]
      change eval₂Hom (eval₂Hom φ z) x (sumRingEquiv R σ τ (C r)) = φ r
      rw [sumRingEquiv_C, eval₂Hom_C, eval₂Hom_C]
    · intro i
      cases i <;> simp [sumRingEquiv_X_inl, sumRingEquiv_X_inr]
  exact DFunLike.congr_fun h P

/-- Taking a coefficient in each retained block recovers the original coefficient. -/
theorem coeff_coeff_sumRingEquiv (P : MvPolynomial (σ ⊕ τ) R)
    (s : σ →₀ ℕ) (t : τ →₀ ℕ) :
    ((sumRingEquiv R σ τ P).coeff s).coeff t = P.coeff (s.sumElim t) := by
  change (AddMonoidAlgebra.mapDomainRingEquiv R Finsupp.sumFinsuppAddEquivProdFinsupp P).coeff
    (s, t) = _
  rw [AddMonoidAlgebra.coeff_mapDomainRingEquiv, Finsupp.equivMapDomain_apply]
  rfl

/-- The degree of a retained coefficient is at most the original total degree. -/
theorem totalDegree_coeff_sumRingEquiv_le (P : MvPolynomial (σ ⊕ τ) R) (s : σ →₀ ℕ) :
    ((sumRingEquiv R σ τ P).coeff s).totalDegree ≤ P.totalDegree := by
  classical
  refine Finset.sup_le fun t ht => ?_
  have ht' : s.sumElim t ∈ P.support := by
    simpa only [mem_support_iff, coeff_coeff_sumRingEquiv] using ht
  refine le_trans ?_ (le_totalDegree ht')
  have hsplit : s.sumElim t =
      s.embDomain Function.Embedding.inl + t.embDomain Function.Embedding.inr := by
    ext j
    cases j <;> simp
  rw [hsplit, Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl)]
  simp only [Finsupp.sum_embDomain, Nat.le_add_left]

/-- Bound the degree of a univariate substitution by a weighted degree of each original
monomial. The weight of a variable is any upper bound on the degree of its replacement. -/
theorem natDegree_aeval_le_of_support {A : Type*} [CommSemiring A] [Algebra R A]
    {g : τ → Polynomial A} {w : τ → ℕ} {P : MvPolynomial τ R} {d : ℕ}
    (hg : ∀ i, (g i).natDegree ≤ w i)
    (hP : ∀ s ∈ P.support, s.sum (fun i e => e * w i) ≤ d) :
    (aeval g P).natDegree ≤ d := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  rw [aeval_monomial, Finsupp.prod]
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.algebraMap_apply, Polynomial.natDegree_C, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  exact (Finset.sum_le_sum fun i _ =>
    Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hg i))).trans (hP s hs)

/-- Substituting univariate polynomials of degree at most `k`, with coefficients in an
`R`-algebra, for the variables gives a polynomial of degree at most `k` times the total
degree. -/
theorem natDegree_aeval_le_mul {A : Type*} [CommSemiring A] [Algebra R A]
    {g : τ → Polynomial A} {k : ℕ} (hg : ∀ i, (g i).natDegree ≤ k)
    (P : MvPolynomial τ R) : (aeval g P).natDegree ≤ P.totalDegree * k := by
  refine natDegree_aeval_le_of_support hg fun s hs => ?_
  rw [Finsupp.sum, ← Finset.sum_mul]
  exact Nat.mul_le_mul_right _ (le_totalDegree hs)

/-- Evaluating a substitution of univariate polynomials at `x` evaluates the polynomial at the
values of the substituted polynomials at `x`. -/
theorem eval_polynomial_aeval (g : τ → Polynomial R) (P : MvPolynomial τ R) (x : R) :
    Polynomial.eval x (aeval g P) = eval (fun i => Polynomial.eval x (g i)) P := by
  rw [← Polynomial.coe_aeval_eq_eval, comp_aeval_apply]
  simp only [Polynomial.coe_aeval_eq_eval, aeval_eq_eval]

/-- **Chain rule** for formal partial derivatives under polynomial substitution. -/
theorem pderiv_aeval [Fintype τ] (L : τ → MvPolynomial σ R) (p : MvPolynomial τ R) (i : σ) :
    pderiv i (aeval L p) = ∑ k, aeval L (pderiv k p) * pderiv i (L k) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have hk : ∑ l, aeval L (pderiv l (X k : MvPolynomial τ R)) * pderiv i (L l) =
        pderiv i (L k) := by
      simp [pderiv_X, Pi.single_apply]
    rw [map_mul, aeval_X, pderiv_mul, hp]
    simp only [pderiv_mul, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul]
    rw [← hk, Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun l _ => by ring)
      (Finset.sum_congr rfl fun l _ => by ring)

end MvPolynomial
