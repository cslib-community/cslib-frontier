/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate (Mathlib, restriction of a polynomial to a line)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.AffineLine
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic

/-!
# A multivariate polynomial along a line

`MvPolynomial.line u p` is the univariate polynomial `t ↦ p (t • u)`: the restriction of `p` to the
line through `0` and `u`, the case of origin `0` of `MvPolynomial.affineLineHom`
(`CslibFrontier/Foundations/Data/MvPolynomial/AffineLine.lean`). Its constant coefficient is that of
`p` (`MvPolynomial.coeff_zero_line`), and its value at `1` is the value of `p` at `u`
(`MvPolynomial.eval_one_line`); for a polynomial of low degree that value is the sum of its first
coefficients along the line (`MvPolynomial.sum_coeff_line_eq_eval`). `Polynomial.coeff_mul_succ`
splits a positive coefficient of a product into the parts that involve a constant coefficient and
the rest.

Along a line, the coefficient of degree `i` of `p` is the value at the point of its homogeneous part
of degree `i` (`MvPolynomial.coeff_line`).

From the proof of Lemma K.2 of *VP ≠ VNP over every field* [AnthropicVPVNP2026], modules
`Nc.LowDegree`, `Nc.Acc.Line` and `Paper.LowDeg` (`line_coeff_eq`).

## Main definitions

* `MvPolynomial.line`.

## Main results

* `MvPolynomial.line_apply`: `line u` is `restrictAffineLine` with origin `0` and direction `u`;
  `MvPolynomial.line_X`.
* `MvPolynomial.coeff_line`, `MvPolynomial.coeff_zero_line`, `MvPolynomial.eval_one_line`,
  `MvPolynomial.sum_coeff_line_eq_eval`, `Polynomial.coeff_mul_succ`.
-/

public section

namespace MvPolynomial

variable {F : Type*} [CommSemiring F] {σ : Type*}

/-- `p` along the line through `0` and `u`: the polynomial `t ↦ p (t • u)`, the affine line
`0 + t • u`. -/
@[expose] noncomputable def line (u : σ → F) : MvPolynomial σ F →ₐ[F] Polynomial F :=
  affineLineHom 0 u

theorem line_apply (u : σ → F) (p : MvPolynomial σ F) : line u p = p.restrictAffineLine 0 u :=
  rfl

@[simp] theorem line_X (u : σ → F) (i : σ) : line u (X i) = Polynomial.C (u i) * Polynomial.X := by
  simp [line, affineLineHom]

/-- The constant coefficient along a line is the constant coefficient. -/
theorem coeff_zero_line (u : σ → F) (p : MvPolynomial σ F) :
    (line u p).coeff 0 = constantCoeff p := by
  rw [Polynomial.coeff_zero_eq_eval_zero, line_apply, eval_restrictAffineLine, zero_smul,
    add_zero, ← eval_zero]

/-- At `t = 1` the line passes through `u`. -/
theorem eval_one_line (u : σ → F) (p : MvPolynomial σ F) : (line u p).eval 1 = eval u p := by
  rw [line_apply, eval_restrictAffineLine, one_smul, zero_add]

/-- A polynomial of total degree at most `d` is the sum of its first `n > d` coefficients along any
line, evaluated at `1`. -/
theorem sum_coeff_line_eq_eval (u : σ → F) (p : MvPolynomial σ F) {d n : ℕ}
    (hd : p.totalDegree ≤ d) (hn : d < n) :
    ∑ i ∈ Finset.range n, (line u p).coeff i = eval u p := by
  have hdeg : (line u p).natDegree ≤ d := (natDegree_restrictAffineLine_le p 0 u).trans hd
  rw [← eval_one_line, Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hdeg hn)]
  simp

/-- The part of degree i is what the point scales by the ith power. -/
theorem coeff_line (u : σ → F) (p : MvPolynomial σ F) (i : ℕ) :
    (line u p).coeff i = eval u (homogeneousComponent i p) := by
  classical
  induction p using induction_on' with
  | monomial d a =>
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2
      (isHomogeneous_monomial a rfl : (monomial d a).IsHomogeneous d.degree))]
    have e : line u (monomial d a) =
        Polynomial.C (eval u (monomial d a)) * Polynomial.X ^ d.degree := by
      simp only [line, affineLineHom, Pi.zero_apply, map_zero, zero_add, aeval_monomial,
        eval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_eq]
      simp only [Finsupp.degree, mul_assoc]
      rfl
    rw [e, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp
  | add p q hp hq => simp [map_add, hp, hq]

end MvPolynomial

namespace Polynomial

variable {F : Type*} [CommSemiring F]

/-- A positive coefficient of a product: the two terms with a constant coefficient, and the products
of positive coefficients. -/
theorem coeff_mul_succ (a b : Polynomial F) (m : ℕ) :
    (a * b).coeff (m + 1) = a.coeff 0 * b.coeff (m + 1) + b.coeff 0 * a.coeff (m + 1) +
      ∑ j ∈ Finset.range m, a.coeff (j + 1) * b.coeff (m - j) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_succ']
  simp only [Nat.sub_zero, Nat.sub_self, Nat.add_sub_add_right]
  ring

end Polynomial
