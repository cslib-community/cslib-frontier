/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, pure-power polynomial residues)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.ParameterCoeffNorm
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Residue
import CslibFrontier.Foundations.Data.MvPolynomial.CoeffSumBounds
import Mathlib.Data.Fintype.BigOperators

/-!
# Coefficient norms of pure-power residues

For a numerator of total degree at most `B`, only terms with index sum at most `B`
contribute. If all lower relations have coefficient norm at most `R ≥ 1`, a term has
norm at most the numerator norm times `R ^ B`. The rectangular index count bounds the
number of contributions. The same proof works for any subadditive, submultiplicative
coefficient weight, including integer coefficient norms with one or several parameters.

Adapted from `LeanCanny.CountingHierarchy.ResidueMassBounds` and
`LeanCanny.CountingHierarchy.MultivariateResidueMass` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, using the total-degree vanishing bound to
replace the source exponent `n * B` by `B`.
-/

public section

namespace MvPolynomial.PurePower

open scoped BigOperators

/-- A nonnegative coefficient weight satisfying the triangle and product inequalities
bounds the residue. Only terms with index sum at most the numerator degree bound `B`
contribute, and `(B + 1) ^ n` bounds the number of rectangular indices. -/
theorem residue_weight_le {S : Type*} [CommRing S] {w : S → ℕ}
    (hzero : w 0 = 0) (hone : w 1 ≤ 1)
    (hadd : ∀ a b, w (a + b) ≤ w a + w b) (hmul : ∀ a b, w (a * b) ≤ w a * w b)
    {n ell B R : ℕ} (hell : 1 ≤ ell) (hR : 1 ≤ R)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (hM : ∀ i, (r i).coeff.sum (fun _ a => w a) ≤ R)
    (v : MvPolynomial (Fin n) S) (hB : v.totalDegree ≤ B) :
    w (residue ell r v) ≤ (B + 1) ^ n * (v.coeff.sum (fun _ a => w a) * R ^ B) := by
  classical
  let norm (p : MvPolynomial (Fin n) S) := p.coeff.sum (fun _ a => w a)
  have hnorm_mul (p q : MvPolynomial (Fin n) S) : norm (p * q) ≤ norm p * norm q :=
    sum_mul_le_of_submultiplicative hzero hadd hmul p q
  have hnorm_one : norm 1 ≤ 1 := by
    change (C (1 : S) : MvPolynomial (Fin n) S).coeff.sum (fun _ a => w a) ≤ 1
    rw [sum_C hzero]
    exact hone
  have hcoeff (p : MvPolynomial (Fin n) S) (m : Fin n →₀ ℕ) : w (p.coeff m) ≤ norm p :=
    Finsupp.single_eval_le_sum p.coeff (g := w) hzero (fun _ => Nat.zero_le _) m
  change w (residue ell r v) ≤ (B + 1) ^ n * (norm v * R ^ B)
  rw [residue_eq_truncated hell r hr v hB]
  change w (∑ j ∈ indices n B, term ell r v j) ≤ _
  refine (Finset.le_sum_of_subadditive w hzero.le hadd _ _).trans ?_
  have hterm (j : Fin n → ℕ) : w (term ell r v j) ≤ norm v * R ^ B := by
    by_cases hj : (∑ i, j i) ≤ B
    · refine (hcoeff _ _).trans ((hnorm_mul _ _).trans ?_)
      apply Nat.mul_le_mul_left
      refine (Finset.le_prod_of_submultiplicative norm hnorm_one hnorm_mul _ _).trans ?_
      calc
        _ ≤ ∏ i : Fin n, R ^ j i := Finset.prod_le_prod fun i _ =>
          (sum_pow_le_of_submultiplicative hzero hone hadd hmul (r i) (j i)).trans
            (Nat.pow_le_pow_left (hM i) _)
        _ = R ^ (∑ i, j i) := by rw [Finset.prod_pow_eq_pow_sum]
        _ ≤ R ^ B := Nat.pow_le_pow_right hR hj
    · rw [term_eq_zero_of_degree_lt hell r hr v j (by omega), hzero]
      exact Nat.zero_le _
  calc
    _ ≤ ∑ _j ∈ indices n B, norm v * R ^ B := Finset.sum_le_sum fun j _ => hterm j
    _ = _ := by simp [indices, Fintype.card_piFinset]

/-- Bound the coefficient norm of the residue with a univariate parameter. -/
theorem coeffNorm1_residue_le {n ell B R : ℕ} (hell : 1 ≤ ell) (hR : 1 ≤ R)
    (r : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (hr : ∀ i, (r i).totalDegree < ell) (hM : ∀ i, ParameterCoeffNorm.norm (r i) ≤ R)
    (v : MvPolynomial (Fin n) (Polynomial ℤ)) (hB : v.totalDegree ≤ B) :
    Polynomial.coeffNorm1 (residue ell r v) ≤
      (B + 1) ^ n * (ParameterCoeffNorm.norm v * R ^ B) := by
  simpa only [sum_def, ParameterCoeffNorm.norm] using
    residue_weight_le Polynomial.coeffNorm1_zero Polynomial.coeffNorm1_one.le
      Polynomial.coeffNorm1_add_le Polynomial.coeffNorm1_mul_le hell hR r hr
      (fun i => by simpa only [sum_def, ParameterCoeffNorm.norm] using hM i) v hB

/-- Bound the coefficient norm of the residue with multivariate parameters, using
the norm after joining the two variable blocks for each input polynomial. -/
theorem coeffNorm1_residue_multivariate_le {τ : Type*} {n ell B R : ℕ}
    (hell : 1 ≤ ell) (hR : 1 ≤ R) (r : Fin n → MvPolynomial (Fin n) (MvPolynomial τ ℤ))
    (hr : ∀ i, (r i).totalDegree < ell)
    (hM : ∀ i, ((sumRingEquiv ℤ (Fin n) τ).symm (r i)).coeffNorm1 ≤ R)
    (v : MvPolynomial (Fin n) (MvPolynomial τ ℤ)) (hB : v.totalDegree ≤ B) :
    (residue ell r v).coeffNorm1 ≤
      (B + 1) ^ n * (((sumRingEquiv ℤ (Fin n) τ).symm v).coeffNorm1 * R ^ B) := by
  simpa only [sum_def, ← coeffNorm1_sumRingEquiv_symm] using
    residue_weight_le coeffNorm1_zero coeffNorm1_one.le coeffNorm1_add_le coeffNorm1_mul_le
      hell hR r hr (fun i => by simpa only [sum_def, ← coeffNorm1_sumRingEquiv_symm] using hM i)
      v hB

end MvPolynomial.PurePower
