/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Bernoulli
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.BooleanAnalysis.MultilinearExtension
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Independent bits with given means

Draw each bit `a i` of a string `a : ι → Bool` independently so that its sign `signVal (a i)` has
mean `μ i ∈ [-1, 1]`, that is `a i = true` (the sign `-1`) with probability `(1 - μ i) / 2`. The
string `a` then has probability `∏ i, (1 + signVal (a i) μ i) / 2` (`BitString.meanWeight`),
nonnegative for means in `[-1, 1]` (`BitString.meanWeight_nonneg`), and the total probability is
one (`BitString.sum_meanWeight`). At the signs of a string `x` this is the point mass at `x`
(`BitString.meanWeight_signVal`). With every mean `1 - 2 p` it is the Bernoulli mask of rate `p`
(`BitString.meanWeight_const`). In the coordinates `(1 - μ i) / 2`, the probabilities that the
bits are `true`, it is the indicator polynomial of `a`
(`BitString.meanWeight_eq_eval_indicatorPoly`), so the expectation of `f` is its multilinear
extension `BitString.multilinearExtension` at that point
(`BitString.sum_meanWeight_mul_eq_eval_multilinearExtension`).

The character of `S` has expectation `∏_{i ∈ S} μ i` (`BitString.sum_meanWeight_mul_chi`), so the
expectation of any real function `f` is its Fourier expansion `∑_S f̂(S) ∏_{i ∈ S} μ i` evaluated
at the point `μ` (`BitString.sum_meanWeight_mul_eq_sum_fourierCoeff`)
[O'Donnell, Exercise 1.4][ODonnell2014]. This is how [O'Donnell, Exercise 7.20(c)][ODonnell2014]
evaluates a constraint at a randomized assignment.

## Usage

Open `Cslib.BitString`. The means are a function `μ : ι → ℝ`; for concrete means on `Fin n`
write them as a vector such as `![1 / 2, -1 / 3]`. To evaluate a weight, rewrite with
`BitString.meanWeight_def` and expand the product (`Fin.prod_univ_two`). The identities
`BitString.sum_meanWeight`, `BitString.sum_meanWeight_mul_chi` and
`BitString.sum_meanWeight_mul_eq_sum_fourierCoeff` hold for every real `μ`; only
`BitString.meanWeight_nonneg` needs `|μ i| ≤ 1`. A sum `∑ a, meanWeight μ a * f a` is then
computed from the Fourier coefficients of `f`, or, through
`BitString.sum_meanWeight_mul_eq_eval_multilinearExtension`, from its multilinear extension
in the `{0, 1}` coordinates. The checked clients in
[CslibFrontierTests/BooleanAnalysisHastadTest.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisHastadTest.lean)
evaluate a weight at means `1/2, 0`, the point mass at signs, the Bernoulli mask at equal means,
Exercise 1.4 for the parity of two bits, and the indicator polynomial and multilinear extension
at the matching `{0, 1}` point.

## Main definitions

* `Cslib.BitString.meanWeight`: the probability of a string whose bits are independent with given
  means.

## Main results

* `Cslib.BitString.meanWeight_nonneg`, `Cslib.BitString.sum_meanWeight`,
  `Cslib.BitString.meanWeight_signVal`, `Cslib.BitString.meanWeight_const`: the weights form a
  distribution, the point mass at the signs of a string, and the Bernoulli mask at equal means.
* `Cslib.BitString.meanWeight_eq_eval_indicatorPoly`,
  `Cslib.BitString.sum_meanWeight_mul_eq_eval_multilinearExtension`: the same in the `{0, 1}`
  coordinates of `BitString.multilinearExtension`.
* `Cslib.BitString.sum_meanWeight_mul_chi`,
  `Cslib.BitString.sum_meanWeight_mul_eq_sum_fourierCoeff`: the expectation of a character, and
  of any function through its Fourier expansion.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The probability of the string `a` when its bits are independent and the sign of bit `i` has
mean `μ i`: bit `i` is `true`, the sign `-1`, with probability `(1 - μ i) / 2`. The weights are
nonnegative when every `|μ i| ≤ 1`. -/
noncomputable def meanWeight (μ : ι → ℝ) (a : ι → Bool) : ℝ :=
  ∏ i, (1 + signVal (a i) * μ i) / 2

/-- The defining formula of `meanWeight`. -/
theorem meanWeight_def (μ : ι → ℝ) (a : ι → Bool) :
    meanWeight μ a = ∏ i, (1 + signVal (a i) * μ i) / 2 := by
  rw [meanWeight]

/-- For means in `[-1, 1]` the weights are nonnegative. -/
theorem meanWeight_nonneg {μ : ι → ℝ} (hμ : ∀ i, |μ i| ≤ 1) (a : ι → Bool) :
    0 ≤ meanWeight μ a :=
  Finset.prod_nonneg fun i _ => by
    have h := abs_le.1 (hμ i)
    cases a i <;> simp only [signVal_true, signVal_false] <;> linarith

/-- With every mean `1 - 2 p`, the weights are those of the Bernoulli mask of rate `p`. -/
theorem meanWeight_const (p : ℝ) (a : ι → Bool) :
    meanWeight (fun _ => 1 - 2 * p) a = bernoulliWeight p a := by
  refine Finset.prod_congr rfl fun i _ => ?_
  cases a i <;> simp only [signVal_true, signVal_false, Bool.false_eq_true, ite_true,
    ite_false] <;> ring

/-- In the coordinates `(1 - μ i) / 2`, the probabilities that the bits are `true`, the weight of
`a` is the value of its indicator polynomial. -/
theorem meanWeight_eq_eval_indicatorPoly (μ : ι → ℝ) (a : ι → Bool) :
    meanWeight μ a = MvPolynomial.eval (fun i => (1 - μ i) / 2) (indicatorPoly a) := by
  rw [eval_indicatorPoly_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases a i <;> simp only [signVal_true, signVal_false, Bool.false_eq_true, ite_true,
    ite_false] <;> ring

/-- **The expectation of a function under independent bits with means `μ`** is the value of its
multilinear extension at the point `(1 - μ i) / 2` of the probabilities that the bits are
`true`. -/
theorem sum_meanWeight_mul_eq_eval_multilinearExtension [DecidableEq ι] (μ : ι → ℝ)
    (f : (ι → Bool) → ℝ) :
    ∑ a, meanWeight μ a * f a =
      MvPolynomial.eval (fun i => (1 - μ i) / 2) (multilinearExtension f) := by
  rw [eval_multilinearExtension_eq_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [meanWeight_eq_eval_indicatorPoly, mul_comm]

/-- **The expectation of a character** under independent bits with means `μ` is
`∏_{i ∈ S} μ i`. -/
theorem sum_meanWeight_mul_chi [DecidableEq ι] (μ : ι → ℝ) (S : Finset ι) :
    ∑ a, meanWeight μ a * chi ℝ S a = ∏ i ∈ S, μ i := by
  have hbit (i : ι) : ∑ b : Bool, (1 + signVal b * μ i) / 2 *
      (if i ∈ S then (-1) ^ b.toNat else 1) = if i ∈ S then μ i else 1 := by
    split_ifs <;> simp only [Fintype.sum_bool, signVal_true, signVal_false, Bool.toNat_true,
      Bool.toNat_false, pow_zero, pow_one] <;> ring
  simp only [meanWeight, chi_eq_prod_univ, ← prod_mul_distrib]
  rw [← Fintype.prod_sum fun i (b : Bool) =>
    (1 + signVal b * μ i) / 2 * if i ∈ S then (-1) ^ b.toNat else 1]
  simp only [hbit, prod_ite_mem, univ_inter]

/-- The weights of independent bits with means `μ` sum to one. -/
theorem sum_meanWeight [DecidableEq ι] (μ : ι → ℝ) : ∑ a, meanWeight μ a = 1 := by
  simpa using sum_meanWeight_mul_chi μ ∅

/-- **The expectation of a function under independent bits with means `μ`** is its Fourier
expansion `∑_S f̂(S) ∏_{i ∈ S} μ i`, the multilinear extension of `f` at the point `μ`
[O'Donnell, Exercise 1.4][ODonnell2014]. -/
theorem sum_meanWeight_mul_eq_sum_fourierCoeff [DecidableEq ι] (μ : ι → ℝ)
    (f : (ι → Bool) → ℝ) :
    ∑ a, meanWeight μ a * f a = ∑ S, fourierCoeff f S * ∏ i ∈ S, μ i := by
  simp only [← sum_meanWeight_mul_chi, mul_sum]
  conv_lhs => enter [2, a]; rw [← sum_fourierCoeff_mul_chi f a, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun S _ => sum_congr rfl fun a _ => by ring

/-- At the signs of a string `x`, the bits are `x` itself: the weights are the point mass at
`x`. -/
theorem meanWeight_signVal (x a : ι → Bool) :
    meanWeight (fun i => signVal (x i)) a = if a = x then 1 else 0 := by
  have hbit (i : ι) : (1 + signVal (a i) * signVal (x i)) / 2 = if a i = x i then 1 else 0 := by
    cases a i <;> cases x i <;> norm_num
  simp only [meanWeight, hbit, Fintype.prod_boole, funext_iff]

end Cslib.BitString
