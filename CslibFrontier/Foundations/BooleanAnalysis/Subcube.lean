/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
import Mathlib.Algebra.BigOperators.Field

/-!
# The Fourier expansion of a subcube

The indicator of the subcube where the coordinates in `K` agree with `b` is
`∑_{S ⊆ K} χ_S(b) χ_S(x) / 2 ^ |K|` (`BitString.sum_powerset_chi_mul_chi`), so its Fourier
coefficient on `S` is `χ_S(b) / 2 ^ |K|` when `S ⊆ K`, and `0` otherwise
(`BitString.fourierCoeff_ite_forall_mem_eq`). A subcube of codimension `k` has density `2 ^ (-k)`
(`BitString.expect_ite_forall_mem_eq`, by counting) and degree-one weight `W¹ = k 2 ^ (-2k)`
(`BitString.levelWeight_one_ite_forall_mem_eq`, stated with `BitString.levelWeight 1`)
[O'Donnell, Proposition 5.24][ODonnell2014], left as the book's Exercise 5.29; for example
`AND_k` is the indicator of the subcube where `k` coordinates are `true`. The book takes `k ≥ 1`;
the results here hold for every codimension, the whole cube included.

The statements take the decidability of the subcube condition as an instance argument, as
Mathlib's `Finset.sum_boole` does, so that they rewrite indicators written with any instance.

## Usage

Import this module and open `Cslib.BitString`. The subcube where the coordinates in `K` agree with
`b : ι → Bool` is written inline as the indicator
`fun x => if ∀ i ∈ K, x i = b i then (1 : ℝ) else 0`, with no named definition; indicators
written over `Fin n`, with any decidability instance, rewrite directly.
`BitString.fourierCoeff_ite_forall_mem_eq K b S` gives its coefficient on `S`,
`chi ℝ S b / 2 ^ #K` when `S ⊆ K` and `0` otherwise, and
`BitString.levelWeight_one_ite_forall_mem_eq K b` gives its degree-one weight
`levelWeight 1 _ = #K / 4 ^ #K`; `BitString.levelWeight_one` turns it into the sum
`∑ i, fourierCoeff _ {i} ^ 2`. Its density `2⁻¹ ^ #K` is `BitString.expect_ite_forall_mem_eq K b`,
in `CslibFrontier.Foundations.Data.BitString.AgreeExpect`. The expansion behind the coefficients,
`BitString.sum_powerset_chi_mul_chi`, holds over any commutative ring `R`; at `K = univ` it is
`BitString.sum_chi_mul_chi`. The checked clients in
[CslibFrontierTests/BooleanAnalysisSubcube.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisSubcube.lean)
evaluate the expansion at two pairs of points on `Fin 2`, compute the density `1 / 4`, the
coefficient `-1 / 4` on `{0}` and the degree-one weight `1 / 8` of the conjunction of two bits,
and check a zero coefficient outside `K`, the density of the whole cube, and the density and a
positive coefficient of the subcube where `x₀ = true` and `x₁ = false`.

## Main results

* `Cslib.BitString.fourierCoeff_ite_forall_mem_eq`: the Fourier coefficients of a subcube.
* `Cslib.BitString.levelWeight_one_ite_forall_mem_eq`: the degree-one weight of a subcube,
  Proposition 5.24.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Fourier coefficients of a subcube**: the indicator of the subcube where the coordinates
in `K` agree with `b` has coefficient `χ_S(b) / 2 ^ |K|` on the subsets `S` of `K`, and `0` on the
other sets. At `K = univ` this is the point indicator of `fourierCoeff_ite_eq`. -/
theorem fourierCoeff_ite_forall_mem_eq (K : Finset ι) (b : ι → Bool)
    [DecidablePred fun x : ι → Bool => ∀ i ∈ K, x i = b i] (S : Finset ι) :
    fourierCoeff (fun x => if ∀ i ∈ K, x i = b i then (1 : ℝ) else 0) S =
      if S ⊆ K then chi ℝ S b / 2 ^ #K else 0 := by
  have h (x : ι → Bool) : (if ∀ i ∈ K, x i = b i then (1 : ℝ) else 0) =
      ∑ T, (if T ⊆ K then chi ℝ T b / 2 ^ #K else 0) * chi ℝ T x := by
    simp only [ite_mul, zero_mul]
    rw [← sum_filter, filter_subset_univ]
    simp only [div_mul_eq_mul_div, ← sum_div]
    rw [sum_congr rfl fun T _ => mul_comm _ _, sum_powerset_chi_mul_chi, ite_div, zero_div,
      div_self (pow_ne_zero _ two_ne_zero)]
  simp only [h]
  exact fourierCoeff_sum_mul_chi _ S

/-- **The degree-one weight of a subcube** [O'Donnell, Proposition 5.24][ODonnell2014]: the
indicator of a subcube of codimension `k = |K|` has `W¹ = k 2 ^ (-2k)`, for every `k ≥ 0`. Its
density `2 ^ (-k)`, the other half of the proposition, is `expect_ite_forall_mem_eq`. -/
theorem levelWeight_one_ite_forall_mem_eq (K : Finset ι) (b : ι → Bool)
    [DecidablePred fun x : ι → Bool => ∀ i ∈ K, x i = b i] :
    levelWeight 1 (fun x => if ∀ i ∈ K, x i = b i then (1 : ℝ) else 0) = #K / 4 ^ #K := by
  have h (i : ι) : (signVal (b i) / 2 ^ #K) ^ 2 = 1 / 4 ^ #K := by
    rw [div_pow, ← sq_abs, abs_signVal, ← pow_mul, mul_comm, pow_mul]
    norm_num
  simp only [levelWeight_one, fourierCoeff_ite_forall_mem_eq, singleton_subset_iff,
    chi_singleton, ite_pow, zero_pow two_ne_zero, h, sum_ite_mem, univ_inter, sum_const,
    nsmul_eq_mul]
  ring

end Cslib.BitString
