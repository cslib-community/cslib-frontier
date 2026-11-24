/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.PolynomialThreshold
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.BooleanAnalysis.InnerProduct

/-!
# The PTF sparsity of the inner product

The inner product modulo two of the two halves of a `2n`-bit string, `fstBits z ⬝ᵥ sndBits z`, has
every Fourier coefficient of absolute value `2 ^ (-n)` when read as signs
(`BitString.abs_fourierCoeff_signVal_dotProduct_fstBits_sndBits`)
[O'Donnell, Exercise 1.1(g)][ODonnell2014]. So a polynomial threshold representation of it over
a family `T` of monomials has `|T| 2 ^ (-n) ≥ 1` by Theorem 5.10, and uses at least `2 ^ n`
monomials
[O'Donnell, Corollary 5.11][ODonnell2014]. This holds for every nonzero `p` that is `≥ 0` where
the inner product is `false` and `≤ 0` where it is `true`, which covers the book's representations
`f = sgn(p)` with `sgn(0) = 1`
(`BitString.two_pow_le_card_dotProduct_fstBits_sndBits_of_nonneg_mul`), and for nowhere-vanishing
ones (`BitString.IsPTFOn.two_pow_le_card_dotProduct_fstBits_sndBits`).

## Usage

Open `Cslib` and `Cslib.BitString`. `IsPTFOn T f`, from
`CslibFrontier.Foundations.BooleanAnalysis.PolynomialThreshold`, says that `f`, read as signs, is
the sign of a nowhere-zero real polynomial whose Fourier coefficients vanish outside the family `T`
of monomials. The inner product is `fun z : BitString (n + n) => fstBits z ⬝ᵥ sndBits z`, whose
spectrum `CslibFrontier.Foundations.BooleanAnalysis.InnerProduct` computes; a mask `S` on
`Fin (n + n)` has its `x`-part at `Fin.castAdd n i` and its `y`-part at `Fin.natAdd n i`. Use
`IsPTFOn.two_pow_le_card_dotProduct_fstBits_sndBits` for nowhere-vanishing representations, and
`two_pow_le_card_dotProduct_fstBits_sndBits_of_nonneg_mul` when `p` may vanish: it asks only that
`p ≠ 0` and that `signVal (fstBits z ⬝ᵥ sndBits z) * p z` is never negative, so it covers
`f = sgn(p)` with `sgn(0) = 1` (its docstring explains why `p ≠ 0` is needed). The checked client
computes coefficients on one and two pairs of bits, shows that the inner product of two pairs is a
threshold function over all `16` sets but not over the constant term and the two monomials
`x₀ y₀`, `x₁ y₁`, and checks both remarks on `p ≠ 0`, in
[`CslibFrontierTests/BooleanAnalysisInnerProductPTF.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisInnerProductPTF.lean).

## Main results

* `Cslib.BitString.two_pow_le_card_dotProduct_fstBits_sndBits_of_nonneg_mul`,
  `Cslib.BitString.IsPTFOn.two_pow_le_card_dotProduct_fstBits_sndBits`: Corollary 5.11.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- Theorem 5.10's bound `1 ≤ ∑_{S ∈ T} |ÎP(S)|` gives `2 ^ n ≤ |T|`. -/
private theorem two_pow_le_card_of_one_le_sum_abs {T : Finset (Finset (Fin (n + n)))}
    (h : 1 ≤ ∑ S ∈ T,
      |fourierCoeff (fun z : BitString (n + n) => signVal (fstBits z ⬝ᵥ sndBits z)) S|) :
    2 ^ n ≤ #T := by
  simp only [abs_fourierCoeff_signVal_dotProduct_fstBits_sndBits, sum_const, nsmul_eq_mul,
    mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n), one_mul] at h
  exact_mod_cast h

/-- **Threshold representations of the inner product that may vanish need at least `2 ^ n`
monomials** [O'Donnell, Corollary 5.11][ODonnell2014]: if a nonzero `p` satisfies
`IP(z) p(z) ≥ 0` for every `z`, with the inner product `fstBits z ⬝ᵥ sndBits z` read as signs, and
the Fourier coefficients of `p` vanish outside `T`, then `|T| ≥ 2 ^ n`. Taking `T` the support of
`p̂`, the sparsity of `p` is at least `2 ^ n`. This covers the book's `f = sgn(p)` with
`sgn(0) = 1`, and more: where `p = 0` the inner product may take either value. The hypothesis
`p ≠ 0` is needed for every `n`, since `p = 0` and `T = ∅` meet the others. The book leaves
`p ≢ 0` implicit; for its representations this matters only at `n = 0`, where `IP_0 = 1 = sgn(0)`
is represented by `p = 0`. -/
theorem two_pow_le_card_dotProduct_fstBits_sndBits_of_nonneg_mul
    {T : Finset (Finset (Fin (n + n)))} {p : BitString (n + n) → ℝ}
    (hpT : ∀ S ∉ T, fourierCoeff p S = 0) (hp₀ : p ≠ 0)
    (hp : ∀ z, 0 ≤ signVal (fstBits z ⬝ᵥ sndBits z) * p z) : 2 ^ n ≤ #T :=
  two_pow_le_card_of_one_le_sum_abs (one_le_sum_abs_fourierCoeff_of_nonneg_mul hpT hp₀ hp)

/-- **Nowhere-vanishing threshold representations of the inner product need at least `2 ^ n`
monomials** [O'Donnell, Corollary 5.11][ODonnell2014]: a nowhere-vanishing polynomial threshold
representation (`IsPTFOn`) of the inner product modulo two `fstBits z ⬝ᵥ sndBits z` of the two
halves of a `2n`-bit string over a family `T` of monomials has `|T| ≥ 2 ^ n`. -/
theorem IsPTFOn.two_pow_le_card_dotProduct_fstBits_sndBits {T : Finset (Finset (Fin (n + n)))}
    (h : IsPTFOn T fun z : BitString (n + n) => fstBits z ⬝ᵥ sndBits z) : 2 ^ n ≤ #T :=
  two_pow_le_card_of_one_le_sum_abs h.one_le_sum_abs_fourierCoeff

end Cslib.BitString
