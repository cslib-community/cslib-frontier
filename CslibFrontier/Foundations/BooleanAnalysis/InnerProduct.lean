/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.PolynomialThreshold
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# The Fourier spectrum of the inner product

The inner product modulo two of two `n`-bit strings, as a function on the cube over `ι ⊕ ι`
(`BitString.innerProduct`), has the flattest possible Fourier spectrum: read as signs, its
coefficient on a set `S` is `(-1) ^ |S_L ∩ S_R| / 2 ^ n`, where `S_L` and `S_R` are the parts of
`S` in the two halves (`BitString.fourierCoeff_signVal_innerProduct`), so every coefficient has
absolute value `2 ^ (-n)` (`BitString.abs_fourierCoeff_signVal_innerProduct`)
[O'Donnell, Exercise 1.1(g)][ODonnell2014]. Splitting a string into its halves `x` and `y`, the
character of `S` is the product of the characters of `S_L` and `S_R` (`BitString.chi_sumElim`),
and `(-1) ^ (x ⬝ᵥ y)` is the character of the support of `x` at `y`
(`BitString.signVal_dotProduct`), so by orthogonality averaging `(-1) ^ (x ⬝ᵥ y) χ_{S_R}(y)` over
`y` leaves only `x = 1_{S_R}`.

Since every coefficient is `2 ^ (-n)` in absolute value, a polynomial threshold representation of
the inner product over a family `T` of monomials has `|T| 2 ^ (-n) ≥ 1` by Theorem 5.10, so it uses
at least `2 ^ n` monomials [O'Donnell, Corollary 5.11][ODonnell2014]. This holds for every nonzero
`p` that is `≥ 0` where the inner product is `false` and `≤ 0` where it is `true`, which covers the
book's representations `f = sgn(p)` with `sgn(0) = 1`
(`BitString.two_pow_le_card_innerProduct_of_nonneg_mul`), and for nowhere-vanishing ones
(`BitString.IsPTFOn.two_pow_le_card_innerProduct`).

## Usage

Open `Cslib` and `Cslib.BitString`. `IsPTFOn T f`, from
`CslibFrontier.Foundations.BooleanAnalysis.PolynomialThreshold`, says that `f`, read as signs, is
the sign of a nowhere-zero real polynomial whose Fourier coefficients vanish outside the family `T`
of monomials. A string on `ι ⊕ ι` with halves `x` and `y` is `Sum.elim x y`, on which
`innerProduct_sumElim` evaluates the inner product as `x ⬝ᵥ y`; `S.toLeft` and `S.toRight` are the
parts `S_L` and `S_R` of a set `S`, and `chi_sumElim` splits a character along them. Use
`IsPTFOn.two_pow_le_card_innerProduct` for nowhere-vanishing representations, and
`two_pow_le_card_innerProduct_of_nonneg_mul` when `p` may vanish: it asks only that `p ≠ 0` and
that `signVal (innerProduct z) * p z` is never negative, so it covers `f = sgn(p)` with
`sgn(0) = 1` (its docstring explains why `p ≠ 0` is needed). The checked client checks that the
inner product of one pair is `AND`, computes coefficients on one and two pairs of bits and a
character of a set on `ι ⊕ ι`, shows that the inner product of two pairs is a threshold function
over all `16` sets but not over the constant term and the two monomials `x₀ y₀`, `x₁ y₁`, and
checks both remarks on `p ≠ 0`, in
[`CslibFrontierTests/BooleanAnalysisInnerProduct.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisInnerProduct.lean).

## Main definitions

* `Cslib.BitString.innerProduct`: the inner product modulo two of the two halves of a string.

## Main results

* `Cslib.BitString.fourierCoeff_signVal_innerProduct`,
  `Cslib.BitString.abs_fourierCoeff_signVal_innerProduct`: its Fourier coefficients
  (Exercise 1.1(g)).
* `Cslib.BitString.two_pow_le_card_innerProduct_of_nonneg_mul`,
  `Cslib.BitString.IsPTFOn.two_pow_le_card_innerProduct`: Corollary 5.11.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inner product modulo two of the two halves of a string on `ι ⊕ ι`. Read as signs, it is
the book's `IP_{2n}(x, y) = (-1) ^ (x · y)` [O'Donnell, Exercise 1.1(g)][ODonnell2014]. -/
def innerProduct (z : ι ⊕ ι → Bool) : Bool :=
  (z ∘ Sum.inl) ⬝ᵥ (z ∘ Sum.inr)

omit [DecidableEq ι] in
/-- The inner product of the string with halves `x` and `y` is `x ⬝ᵥ y`. -/
@[simp] theorem innerProduct_sumElim (x y : ι → Bool) : innerProduct (Sum.elim x y) = x ⬝ᵥ y := by
  simp only [innerProduct, Sum.elim_comp_inl, Sum.elim_comp_inr]

/-- **The Fourier coefficients of the inner product** [O'Donnell, Exercise 1.1(g)][ODonnell2014]:
read as signs, the inner product modulo two on `ι ⊕ ι` has coefficient
`(-1) ^ |S_L ∩ S_R| / 2 ^ |ι|` on `S`, with `S_L`, `S_R` the parts of `S` in the two halves. -/
theorem fourierCoeff_signVal_innerProduct (S : Finset (ι ⊕ ι)) :
    fourierCoeff (fun z => signVal (innerProduct z)) S =
      (-1) ^ #(S.toLeft ∩ S.toRight) / 2 ^ Fintype.card ι := by
  have hx (x : ι → Bool) :
      ({i | x i} : Finset ι) = S.toRight ↔ x = fun i => decide (i ∈ S.toRight) := by
    simp only [Finset.ext_iff, funext_iff, mem_filter, mem_univ, true_and, mem_toRight]
    exact forall_congr' fun i => by cases x i <;> simp
  -- first the coefficient is `χ_{S_L}(1_{S_R}) / 2 ^ |ι|`
  have hchi : fourierCoeff (fun z => signVal (innerProduct z)) S =
      chi ℝ S.toLeft (fun i => decide (i ∈ S.toRight)) / 2 ^ Fintype.card ι := by
    rw [fourierCoeff, Fintype.expect_sumElim]
    simp only [innerProduct_sumElim, chi_sumElim, signVal_dotProduct,
      mul_left_comm _ (chi ℝ S.toLeft _), ← mul_expect, expect_chi_mul_chi, hx, mul_ite,
      mul_one, mul_zero]
    rw [Fintype.expect_eq_sum_div_card, sum_ite_eq', ite_eq_left (mem_univ _), Fintype.card_fun,
      Fintype.card_bool]
    push_cast
    rfl
  rw [hchi, chi_eq_prod_signVal]
  simp only [signVal, decide_eq_true_eq, prod_ite_mem, prod_const]

/-- Every Fourier coefficient of the inner product has absolute value `2 ^ (-|ι|)`
[O'Donnell, Exercise 1.1(g)][ODonnell2014]. -/
theorem abs_fourierCoeff_signVal_innerProduct (S : Finset (ι ⊕ ι)) :
    |fourierCoeff (fun z => signVal (innerProduct z)) S| = 1 / 2 ^ Fintype.card ι := by
  rw [fourierCoeff_signVal_innerProduct, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (by positivity)]

/-- Theorem 5.10's bound `1 ≤ ∑_{S ∈ T} |ÎP(S)|` gives `2 ^ |ι| ≤ |T|`. -/
private theorem two_pow_le_card_of_one_le_sum_abs {T : Finset (Finset (ι ⊕ ι))}
    (h : 1 ≤ ∑ S ∈ T, |fourierCoeff (fun z => signVal (innerProduct z)) S|) :
    2 ^ Fintype.card ι ≤ #T := by
  simp only [abs_fourierCoeff_signVal_innerProduct, sum_const, nsmul_eq_mul, mul_one_div,
    le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ Fintype.card ι), one_mul] at h
  exact_mod_cast h

/-- **Threshold representations of the inner product that may vanish need at least `2 ^ n`
monomials** [O'Donnell, Corollary 5.11][ODonnell2014]: if a nonzero `p` satisfies
`IP(z) p(z) ≥ 0` for every `z`, with the inner product read as signs, and the Fourier coefficients
of `p` vanish outside `T`, then `|T| ≥ 2 ^ n`. Taking `T` the support of `p̂`, the sparsity of `p`
is at least `2 ^ n`. This covers the book's `f = sgn(p)` with `sgn(0) = 1`, and more: where `p = 0`
the inner product may take either value. The hypothesis `p ≠ 0` is needed for every `n`, since
`p = 0` and `T = ∅` meet the others. The book leaves `p ≢ 0` implicit; for its representations
this matters only at `n = 0`, where `IP_0 = 1 = sgn(0)` is represented by `p = 0`. -/
theorem two_pow_le_card_innerProduct_of_nonneg_mul {T : Finset (Finset (ι ⊕ ι))}
    {p : (ι ⊕ ι → Bool) → ℝ} (hpT : ∀ S ∉ T, fourierCoeff p S = 0) (hp₀ : p ≠ 0)
    (hp : ∀ z, 0 ≤ signVal (innerProduct z) * p z) : 2 ^ Fintype.card ι ≤ #T :=
  two_pow_le_card_of_one_le_sum_abs (one_le_sum_abs_fourierCoeff_of_nonneg_mul hpT hp₀ hp)

/-- **Nowhere-vanishing threshold representations of the inner product need at least `2 ^ n`
monomials** [O'Donnell, Corollary 5.11][ODonnell2014]: a nowhere-vanishing polynomial threshold
representation (`IsPTFOn`) of the inner product modulo two of two `n`-bit strings over a family
`T` of monomials has `|T| ≥ 2 ^ n`. -/
theorem IsPTFOn.two_pow_le_card_innerProduct {T : Finset (Finset (ι ⊕ ι))}
    (h : IsPTFOn T innerProduct) : 2 ^ Fintype.card ι ≤ #T :=
  two_pow_le_card_of_one_le_sum_abs h.one_le_sum_abs_fourierCoeff

end Cslib.BitString
