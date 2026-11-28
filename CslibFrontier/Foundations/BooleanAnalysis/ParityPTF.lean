/-
Copyright (c) 2026 Josh Liebow-Feeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Liebow-Feeser
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.PolynomialThreshold
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# The PTF degree of parity (Minsky–Papert)

Every polynomial threshold representation of the parity `parityOn S` of a set `S` of coordinates,
over a family `T` of monomials, must include `S` in `T`, and in particular any polynomial threshold
function computing `parity n` has degree at least `n`
[Minsky and Papert (1969); 1988 expanded edition, Theorem 3.1.1, §3.1, pp. 56–57][MinskyPapert1969]
[O'Donnell, Exercise 5.10(a)][ODonnell2014] (the locator in the 1969 printing remains unverified).
Since `signVal (parityOn S x) = χ_S(x)`, `parityOn S` is a polynomial threshold function over `{S}`,
so the degree bound `n` is tight, including the constant case `n = 0`
(`Cslib.BitString.isPTF_parity_iff`).

Following `CslibFrontier.Foundations.BooleanAnalysis.PolynomialThreshold`,
the lower bound is stated both for nowhere-vanishing representations (`Cslib.BitString.IsPTFOn`,
`Cslib.BitString.IsPTF`) and for any nonzero real function `p` satisfying
`0 ≤ signVal (parityOn S x) * p x` everywhere
(`Cslib.BitString.fourierCoeff_pos_of_nonneg_mul_parityOn`,
`Cslib.BitString.le_of_nonneg_mul_parity`). The latter allows zeros of `p`, covering `f = sgn(p)`
with `sgn(0) = 1`, provided `p ≠ 0`; this hypothesis is necessary since `p = 0` meets the sign
condition for every `f` and every `T`.

## Main results

* `Cslib.BitString.fourierCoeff_pos_of_nonneg_mul_parityOn`: any nonzero `p` agreeing in sign with
  `parityOn S` where `p ≠ 0` has `0 < p̂(S)`.
* `Cslib.BitString.mem_of_nonneg_mul_parityOn`,
  `Cslib.BitString.card_le_of_nonneg_mul_parityOn`,
  `Cslib.BitString.le_of_nonneg_mul_parity`: zeros-allowed PTF lower bounds for `parityOn S` and
  `parity n`.
* `Cslib.BitString.isPTFOn_parityOn_iff`, `Cslib.BitString.isPTF_parityOn_iff`,
  `Cslib.BitString.isPTF_parity_iff`: tight characterizations of when `parityOn S` and `parity n`
  are polynomial threshold functions.

## References

* [M. Minsky, S. Papert, *Perceptrons: An Introduction to Computational Geometry*][MinskyPapert1969]
  (original 1969; verified in the 1988 expanded edition, Ch. 3, §3.1, Theorem 3.1.1, pp. 56–57;
  1969 printing locator unverified)
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Minsky–Papert correlation positivity for parity**: if `p` is not identically zero and
`0 ≤ signVal (parityOn S x) * p x` for every `x`, then `p` has strictly positive Fourier
coefficient on `S`, because `𝔼 x, χ_S(x) p(x) = 𝔼 x, |p(x)| > 0`
[Minsky and Papert (1969); 1988 expanded edition, Theorem 3.1.1, §3.1, pp. 56–57][MinskyPapert1969]
[O'Donnell, Exercise 5.10(a)][ODonnell2014]. -/
theorem fourierCoeff_pos_of_nonneg_mul_parityOn {S : Finset ι} {p : (ι → Bool) → ℝ}
    (hp₀ : p ≠ 0) (hp : ∀ x, 0 ≤ signVal (parityOn S x) * p x) :
    0 < fourierCoeff p S := by
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hp₀
  calc 0 < 𝔼 x, |p x| :=
        expect_pos' (fun x _ => abs_nonneg _) ⟨x₀, mem_univ x₀, abs_pos.2 hx₀⟩
    _ = 𝔼 x, signVal (parityOn S x) * p x :=
        expect_congr rfl fun x _ => (signVal_mul_eq_abs hp x).symm
    _ = fourierCoeff p S := by
        simp only [fourierCoeff, chi_eq_signVal_parityOn, mul_comm]

/-- **Monomial-support lower bound for parity (zeros allowed)**: if a nonzero `p` whose Fourier
coefficients vanish outside `T` satisfies `0 ≤ signVal (parityOn S x) * p x` everywhere, then
`S ∈ T`
[Minsky and Papert (1969); 1988 expanded edition, Theorem 3.1.1, §3.1, pp. 56–57][MinskyPapert1969]
[O'Donnell, Exercise 5.10(a)][ODonnell2014]. -/
theorem mem_of_nonneg_mul_parityOn {T : Finset (Finset ι)} {S : Finset ι}
    {p : (ι → Bool) → ℝ} (hpT : ∀ U ∉ T, fourierCoeff p U = 0)
    (hp₀ : p ≠ 0) (hp : ∀ x, 0 ≤ signVal (parityOn S x) * p x) : S ∈ T :=
  by_contra fun hS => (fourierCoeff_pos_of_nonneg_mul_parityOn hp₀ hp).ne' (hpT S hS)

/-- **Minsky–Papert degree lower bound for `parityOn S` (zeros allowed)**: if a nonzero `p` of
Fourier degree at most `k` satisfies `0 ≤ signVal (parityOn S x) * p x` everywhere, then `#S ≤ k`
[Minsky and Papert (1969); 1988 expanded edition, Theorem 3.1.1, §3.1, pp. 56–57][MinskyPapert1969]
[O'Donnell, Exercise 5.10(a)][ODonnell2014]. -/
theorem card_le_of_nonneg_mul_parityOn {S : Finset ι} {k : ℕ} {p : (ι → Bool) → ℝ}
    (hpk : ∀ U, k < #U → fourierCoeff p U = 0)
    (hp₀ : p ≠ 0) (hp : ∀ x, 0 ≤ signVal (parityOn S x) * p x) : #S ≤ k :=
  not_lt.1 fun hlt => (fourierCoeff_pos_of_nonneg_mul_parityOn hp₀ hp).ne' (hpk S hlt)

/-- **Minsky–Papert degree-`n` PTF lower bound for `parity` (zeros allowed)**: if a nonzero
`p : BitString n → ℝ` of Fourier degree at most `k` satisfies `0 ≤ signVal (parity n x) * p x`
for every `x`, then `n ≤ k`
[Minsky and Papert (1969); 1988 expanded edition, Theorem 3.1.1, §3.1, pp. 56–57][MinskyPapert1969]
[O'Donnell, Exercise 5.10(a)][ODonnell2014]. -/
theorem le_of_nonneg_mul_parity {n k : ℕ} {p : BitString n → ℝ}
    (hpk : ∀ S : Finset (Fin n), k < #S → fourierCoeff p S = 0)
    (hp₀ : p ≠ 0) (hp : ∀ x, 0 ≤ signVal (parity n x) * p x) : n ≤ k := by
  simpa [parity] using card_le_of_nonneg_mul_parityOn hpk hp₀ hp

/-- **Exact PTF family characterization for `parityOn S`**: `parityOn S` is a polynomial
threshold function over `T` if and only if `S ∈ T`
[Minsky and Papert (1969); 1988 expanded edition, Theorem 3.1.1, §3.1, pp. 56–57][MinskyPapert1969]
[O'Donnell, Exercise 5.10(a)][ODonnell2014]. -/
theorem isPTFOn_parityOn_iff {T : Finset (Finset ι)} {S : Finset ι} :
    IsPTFOn T (parityOn S) ↔ S ∈ T := by
  refine ⟨fun ⟨p, hpT, hp⟩ => mem_of_nonneg_mul_parityOn hpT ?_ fun x => (hp x).le,
    fun hST => isPTFOn_of_fourierCoeff_eq_zero fun U hU => ?_⟩
  · rintro rfl
    simpa using hp (Classical.arbitrary _)
  · rw [fourierCoeff_signVal_parityOn]
    exact ite_eq_right_iff.2 fun h => absurd (h ▸ hST) hU

/-- **Tight PTF degree characterization for `parityOn S`**: `parityOn S` is a polynomial
threshold function of degree at most `k` if and only if `#S ≤ k`
[Minsky and Papert (1969); 1988 expanded edition, Theorem 3.1.1, §3.1, pp. 56–57][MinskyPapert1969]
[O'Donnell, Exercise 5.10(a)][ODonnell2014]. -/
theorem isPTF_parityOn_iff {k : ℕ} {S : Finset ι} :
    IsPTF k (parityOn S) ↔ #S ≤ k := by
  simp only [IsPTF, isPTFOn_parityOn_iff, mem_filter, mem_univ, true_and]

/-- **Minsky–Papert theorem**: the `n`-bit parity function is a polynomial threshold function of
degree at most `k` if and only if `n ≤ k`
[Minsky and Papert (1969); 1988 expanded edition, Theorem 3.1.1, §3.1, pp. 56–57][MinskyPapert1969]
[O'Donnell, Exercise 5.10(a)][ODonnell2014]. -/
theorem isPTF_parity_iff {n k : ℕ} :
    IsPTF k (parity n) ↔ n ≤ k := by
  simp only [parity, isPTF_parityOn_iff, card_univ, Fintype.card_fin]

end Cslib.BitString
