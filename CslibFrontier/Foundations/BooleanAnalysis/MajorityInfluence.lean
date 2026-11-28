/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import CslibFrontier.Foundations.BooleanAnalysis.CentralLimit
import CslibFrontier.Foundations.BooleanAnalysis.Majority

/-!
# The total influence of majority

The total influence of the majority of `n` bits, read as signs, is `I[Majₙ] = 𝔼 |x₁ + ⋯ + xₙ|`
(`BitString.totalInfluence_majority_eq_expect_abs`): majority is monotone, so its total influence is
the sum of its degree-one coefficients [O'Donnell, Proposition 2.31][ODonnell2014], and that sum
is `𝔼 Majₙ(x) (x₁ + ⋯ + xₙ) = 𝔼 |x₁ + ⋯ + xₙ|` [O'Donnell, proof of Theorem 2.33][ODonnell2014].
By the central limit theorem on the cube, `I[Majₙ] / √n = 𝔼 |∑ᵢ xᵢ / √n| → √(2 / π)`
(`BitString.tendsto_totalInfluence_majority_div_sqrt`), the leading term of
`I[Majₙ] = √(2/π) √n + O(n^{-1/2})` in [O'Donnell, Theorem 2.33][ODonnell2014]. The book's
`Majₙ` is defined for odd `n`, where it is the library's `majority n`; along odd `n = 2m + 1`
the statement is `BitString.tendsto_totalInfluence_majority_two_mul_add_one_div_sqrt`. The
library's `majority n` breaks ties towards `true`, and the limit holds along all `n`.

The error term `O(n^{-1/2})` is not formalized.

## Main results

* `Cslib.BitString.totalInfluence_majority_eq_expect_abs`: `I[Majₙ] = 𝔼 |x₁ + ⋯ + xₙ|`.
* `Cslib.BitString.tendsto_totalInfluence_majority_div_sqrt`,
  `Cslib.BitString.tendsto_totalInfluence_majority_two_mul_add_one_div_sqrt`:
  `I[Majₙ] / √n → √(2 / π)`, along all `n` and along odd `n`.

## Usage

Majority is `majority n : BooleanFunction n`, true when at least `(n + 1) / 2` bits are true, and
read as signs by `fun x => signVal (majority n x)`. The checked clients in
[CslibFrontierTests/BooleanAnalysisMajorityInfluence.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisMajorityInfluence.lean)
compute `I[Maj₃] = 3 / 2` both through the identity and as the average sensitivity, and derive
`I[Majₙ] / n → 0` and, along odd `n`, `I[Majₙ] < √n` eventually.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Filter Topology Real
open scoped BigOperators

/-- **The total influence of majority** is the mean absolute sum of the signs,
`I[Majₙ] = 𝔼 |x₁ + ⋯ + xₙ|` [O'Donnell, Proposition 2.31 and proof of Theorem 2.33][ODonnell2014].
-/
theorem totalInfluence_majority_eq_expect_abs (n : ℕ) :
    totalInfluence (fun x : BitString n => signVal (majority n x)) =
      𝔼 x : BitString n, |∑ i, signVal (x i)| := by
  rw [totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone monotone_majority,
    sum_fourierCoeff_singleton_majority]

/-- **The asymptotic total influence of majority**: `I[Majₙ] / √n → √(2 / π)`, the leading term of
`I[Majₙ] = √(2/π) √n + O(n^{-1/2})` [O'Donnell, Theorem 2.33][ODonnell2014]. The library's
`majority n` breaks ties towards `true`, so the limit is along all `n`. -/
theorem tendsto_totalInfluence_majority_div_sqrt :
    Tendsto (fun n : ℕ => totalInfluence (fun x : BitString n => signVal (majority n x)) / √n)
      atTop (𝓝 √(2 / π)) := by
  refine tendsto_expect_abs_inv_sqrt_mul_sum_signVal.congr fun n => ?_
  rw [totalInfluence_majority_eq_expect_abs, expect_div]
  refine expect_congr rfl fun x _ => ?_
  rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (sqrt_nonneg _)), div_eq_inv_mul]

/-- **The asymptotic total influence of majority, along odd `n`**: for the book's `Majₙ` with
`n = 2m + 1`, `I[Majₙ] / √n → √(2 / π)` as `m → ∞` [O'Donnell, Theorem 2.33][ODonnell2014]. -/
theorem tendsto_totalInfluence_majority_two_mul_add_one_div_sqrt :
    Tendsto (fun m : ℕ => totalInfluence (fun x : BitString (2 * m + 1) =>
        signVal (majority (2 * m + 1) x)) / √((2 * m + 1 : ℕ) : ℝ)) atTop (𝓝 √(2 / π)) :=
  tendsto_totalInfluence_majority_div_sqrt.comp
    (tendsto_atTop_mono (fun m => show m ≤ 2 * m + 1 by omega) tendsto_id)

end Cslib.BitString
