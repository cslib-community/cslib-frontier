/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Bernoulli
public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import Mathlib.Analysis.Real.Sqrt

/-!
# `p`-biased Fourier analysis

Under the `p`-biased distribution each bit is `true`, read as `-1`, independently with probability
`p` (`BitString.bernoulliAverage`). With `μ = 1 - 2p` and `σ = 2 √(p (1 - p))` the mean and the
standard deviation of a bit read as a sign, the **biased basis function** is
`φ(b) = (signVal b - μ) / σ` (`BitString.biasedBasis`) [O'Donnell, Definition 8.39][ODonnell2014],
and the **biased characters** are `φ_S(x) = ∏_{i ∈ S} φ(xᵢ)` (`BitString.biasedChi`), with the
**biased Fourier coefficients** `f̂(S) = 𝔼_p[f φ_S]` (`BitString.biasedFourierCoeff`)
[O'Donnell, Definition 8.40][ODonnell2014].

For `0 < p < 1` a bit's `φ` has mean `0` and second moment `1`, so the biased characters are
orthonormal under the `p`-biased distribution
(`BitString.bernoulliAverage_biasedChi_mul_biasedChi`).
The indicator of agreeing with `y` in one bit is `π_p(yᵢ) (1 + φ(xᵢ) φ(yᵢ))`, so the indicator of
the point `y` is `bernoulliWeight p y ∑_S φ_S(x) φ_S(y)`, with `bernoulliWeight p y = ∏ᵢ π_p(yᵢ)`
the product mass at `y`, which gives the **biased Fourier expansion**
`f = ∑_S f̂(S) φ_S` (`BitString.sum_biasedFourierCoeff_mul_biasedChi`) and **Plancherel's
identity** `𝔼_p[f g] = ∑_S f̂(S) ĝ(S)`
(`BitString.bernoulliAverage_mul_eq_sum_biasedFourierCoeff_mul`).
The coefficient on `∅` is the mean (`BitString.biasedFourierCoeff_empty`), so the covariance and the
variance are the same sums over the nonempty sets
(`BitString.bernoulliAverage_sub_bernoulliAverage_mul_sub_bernoulliAverage_eq_sum`,
`BitString.bernoulliAverage_sub_bernoulliAverage_sq_eq_sum_biasedFourierCoeff_sq`); with Parseval
these are the five formulas of [O'Donnell, Proposition 8.16][ODonnell2014] for this basis.
Conditioning on bit `i` (`BitString.bernoulliAverage_eq_bernoulliAverage_update`) pairs each string
with its flip at `i`: for every `p`, `𝔼_p[f · (signVal (x i) - μ)] = 4p(1 - p) 𝔼_p[D_{x_i} f]`, with
`D_{x_i}` the usual derivative `BitString.derivative`
(`BitString.bernoulliAverage_mul_signVal_sub`), so for `0 < p < 1` the coefficient on `{i}` is
`σ 𝔼_p[D_{x_i} f]` (`BitString.biasedFourierCoeff_singleton`), the step of the proof of
[O'Donnell, (8.8)][ODonnell2014] that gives the Margulis–Russo Formula in the book's form
(`BitString.hasDerivAt_bernoulliAverage_one_sub_div_two` of
`CslibFrontier.Foundations.BooleanAnalysis.MargulisRusso`). A dictator `xᵢ` is `μ + σ φ_{i}`, so its
coefficients are `μ` on `∅`, `σ` on `{i}` and `0` elsewhere
(`BitString.biasedFourierCoeff_dictator`) [O'Donnell, Example 8.41][ODonnell2014].

The book writes `±1` bits with `π_p(-1) = p`; here `true` is the bit of probability `p`, which is
`-1` under `signVal`, so the book's `φ(1) = √(p/q)` and `φ(-1) = -√(q/p)` are
`BitString.biasedBasis_false` and `BitString.biasedBasis_true`. Outside `0 < p < 1` the definitions
still make sense, with `σ = 0` and `φ = 0`; the basis facts take `0 < p < 1`. The book proves
orthonormality and completeness (Proposition 8.13) and the five formulas of Proposition 8.16 for
every product Fourier basis of a finite product space; here they are proved for this two-point
basis on bits only, and the expansion comes from the point-indicator identity rather than from a
dimension count.

## Usage

Open `Cslib.BitString`. The `p`-biased expectation is `bernoulliAverage p`, the coefficient
`f̂(S)` is `biasedFourierCoeff p f S` and `φ_S(x)` is `biasedChi p S x`. Pass `hp : 0 < p` and
`hp1 : p < 1` to the expansion, Parseval, Plancherel, the covariance and the variance,
orthonormality, the dictator's coefficients and the degree-one formula; the mean
`biasedFourierCoeff_empty` and the pairing identity `bernoulliAverage_mul_signVal_sub` hold for
every `p`. To compute the biased coefficients of a function written in the usual characters,
substitute `signVal (x i) = μ + σ φ_{i}` as in `biasedFourierCoeff_dictator`; at `p = 1/2`,
`biasedFourierCoeff_one_half` and `biasedChi_one_half` return to `fourierCoeff` and `chi`.

Checked clients compute the basis at rates `1/4`, `1/3` and `3/4`, check orthonormality, the
expansion and the coefficients of indicator bits and dictators, derive `σ² = 1 - μ²` from
Parseval, the correlation `μ²` of two dictators from Plancherel, the variance `σ²` of a dictator
and the zero covariance of two dictators, and return to the uniform case at `p = 1/2`, in
[`CslibFrontierTests/BooleanAnalysisBiasedFourier.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisBiasedFourier.lean).

## Main definitions

* `Cslib.BitString.biasedStd`, `Cslib.BitString.biasedBasis`, `Cslib.BitString.biasedChi`,
  `Cslib.BitString.biasedFourierCoeff`: the `p`-biased Fourier basis and coefficients.

## Main results

* `Cslib.BitString.bernoulliAverage_biasedChi_mul_biasedChi`: orthonormality.
* `Cslib.BitString.bernoulliWeight_mul_sum_biasedChi_mul_biasedChi`: the indicator of a point.
* `Cslib.BitString.sum_biasedFourierCoeff_mul_biasedChi`: the biased Fourier expansion.
* `Cslib.BitString.biasedFourierCoeff_empty`: the coefficient on `∅` is the mean.
* `Cslib.BitString.bernoulliAverage_mul_eq_sum_biasedFourierCoeff_mul`,
  `Cslib.BitString.bernoulliAverage_sq_eq_sum_biasedFourierCoeff_sq`: Plancherel and Parseval.
* `Cslib.BitString.bernoulliAverage_sub_bernoulliAverage_mul_sub_bernoulliAverage_eq_sum`,
  `Cslib.BitString.bernoulliAverage_sub_bernoulliAverage_sq_eq_sum_biasedFourierCoeff_sq`: the
  covariance and the variance.
* `Cslib.BitString.bernoulliAverage_mul_signVal_sub`,
  `Cslib.BitString.biasedFourierCoeff_singleton`: degree-one coefficients as mean derivatives.
* `Cslib.BitString.biasedFourierCoeff_dictator`: Example 8.41.
* `Cslib.BitString.biasedBasis_false`, `Cslib.BitString.biasedBasis_true`: the values of the
  basis.
* `Cslib.BitString.biasedBasis_one_sub`: exchanging `p` and `1 - p` complements the bit.
* `Cslib.BitString.biasedChi_one_half`, `Cslib.BitString.biasedFourierCoeff_one_half`: the
  uniform case.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard deviation `σ = 2 √(p (1 - p))` of a `p`-biased bit read as a sign. Outside
`0 < p < 1` it is `0`, since `√` of a nonpositive number is `0`. -/
noncomputable def biasedStd (p : ℝ) : ℝ :=
  2 * √(p * (1 - p))

/-- The **`p`-biased basis function** `φ(b) = (signVal b - μ) / σ`, with `μ = 1 - 2p`
[O'Donnell, Definition 8.39][ODonnell2014]. Outside `0 < p < 1`, where `σ = 0`, it is `0`. -/
noncomputable def biasedBasis (p : ℝ) (b : Bool) : ℝ :=
  (signVal b - (1 - 2 * p)) / biasedStd p

/-- The **`p`-biased character** `φ_S(x) = ∏_{i ∈ S} φ(xᵢ)`
[O'Donnell, Definition 8.40][ODonnell2014]. -/
noncomputable def biasedChi (p : ℝ) (S : Finset ι) (x : ι → Bool) : ℝ :=
  ∏ i ∈ S, biasedBasis p (x i)

/-- The **`p`-biased Fourier coefficient** `f̂(S) = 𝔼_p[f φ_S]`
[O'Donnell, Definition 8.40][ODonnell2014]. -/
noncomputable def biasedFourierCoeff (p : ℝ) (f : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  bernoulliAverage p fun x => f x * biasedChi p S x

section Bit

variable {p : ℝ}

/-- The variance of a `p`-biased bit read as a sign: `σ² = 4 p (1 - p)`. -/
theorem biasedStd_sq (hp : 0 ≤ p) (hp1 : p ≤ 1) : biasedStd p ^ 2 = 4 * (p * (1 - p)) := by
  rw [biasedStd, mul_pow, Real.sq_sqrt (mul_nonneg hp (by linarith))]
  norm_num

/-- The standard deviation `σ` is positive for `0 < p < 1`. -/
theorem biasedStd_pos (hp : 0 < p) (hp1 : p < 1) : 0 < biasedStd p :=
  mul_pos two_pos (Real.sqrt_pos.2 (mul_pos hp (by linarith)))

/-- The standard deviation `σ` is nonzero for `0 < p < 1`. -/
theorem biasedStd_ne_zero (hp : 0 < p) (hp1 : p < 1) : biasedStd p ≠ 0 :=
  (biasedStd_pos hp hp1).ne'

/-- The basis function has mean zero under the `p`-biased distribution. -/
theorem biasedBasis_mean (p : ℝ) :
    (1 - p) * biasedBasis p false + p * biasedBasis p true = 0 := by
  simp only [biasedBasis, signVal_false, signVal_true]
  ring

/-- The basis function has second moment one under the `p`-biased distribution. -/
theorem biasedBasis_sq_mean (hp : 0 < p) (hp1 : p < 1) :
    (1 - p) * biasedBasis p false ^ 2 + p * biasedBasis p true ^ 2 = 1 := by
  have hσ := biasedStd_ne_zero hp hp1
  have hσ2 := biasedStd_sq hp.le hp1.le
  simp only [biasedBasis, signVal_false, signVal_true, div_pow]
  field_simp
  rw [hσ2]
  ring

/-- The indicator of agreeing with `c` in one bit is `π_p(c) (1 + φ(b) φ(c))`. -/
private theorem ite_mul_one_add_biasedBasis_mul_biasedBasis (hp : 0 < p) (hp1 : p < 1)
    (b c : Bool) :
    (if c then p else 1 - p) * (1 + biasedBasis p b * biasedBasis p c) =
      if b = c then (1 : ℝ) else 0 := by
  have hσ := biasedStd_ne_zero hp hp1
  have hσ2 := biasedStd_sq hp.le hp1.le
  cases b <;> cases c <;>
    simp only [biasedBasis, signVal_false, signVal_true, ↓reduceIte, Bool.false_eq_true,
      Bool.true_eq_false] <;>
    field_simp <;> rw [hσ2] <;> ring

/-- The basis function at `false`, the book's `1`, is `√(p / q)` with `q = 1 - p`: the formula
`φ(1) = √(p/q)` after [O'Donnell, Definition 8.39][ODonnell2014]. -/
theorem biasedBasis_false (hp : 0 < p) (hp1 : p < 1) : biasedBasis p false = √(p / (1 - p)) := by
  have h1 : 0 < 1 - p := by linarith
  rw [biasedBasis, biasedStd, signVal_false, Real.sqrt_div' _ h1.le, Real.sqrt_mul hp.le]
  have : 0 < √p := Real.sqrt_pos.2 hp
  have : 0 < √(1 - p) := Real.sqrt_pos.2 h1
  field_simp
  rw [Real.sq_sqrt hp.le]
  ring

/-- Exchanging the rates `p` and `1 - p` and complementing the bit negates the basis function:
`φ_{1-p}(¬b) = -φ_p(b)`. -/
theorem biasedBasis_one_sub (p : ℝ) (b : Bool) : biasedBasis (1 - p) (!b) = -biasedBasis p b := by
  have h : biasedStd (1 - p) = biasedStd p := by
    rw [biasedStd, biasedStd, sub_sub_cancel, mul_comm p]
  rw [biasedBasis, biasedBasis, h, signVal_not]
  ring

/-- The basis function at `true`, the book's `-1`, is `-√(q / p)` with `q = 1 - p`: the formula
`φ(-1) = -√(q/p)` after [O'Donnell, Definition 8.39][ODonnell2014]. -/
theorem biasedBasis_true (hp : 0 < p) (hp1 : p < 1) : biasedBasis p true = -√((1 - p) / p) := by
  have h := biasedBasis_one_sub p true
  rw [Bool.not_true, biasedBasis_false (by linarith) (by linarith), sub_sub_cancel] at h
  linarith

end Bit

omit [Fintype ι] [DecidableEq ι] in
/-- At `p = 1/2` the biased characters are the usual characters. -/
theorem biasedChi_one_half (S : Finset ι) (x : ι → Bool) : biasedChi (1 / 2) S x = chi ℝ S x := by
  have : biasedStd (1 / 2) = 1 := by
    rw [biasedStd, show (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    norm_num
  rw [biasedChi, chi_eq_prod_signVal]
  refine prod_congr rfl fun i _ => ?_
  rw [biasedBasis, this]
  ring

/-- At `p = 1/2` the biased Fourier coefficients are the usual Fourier coefficients. -/
theorem biasedFourierCoeff_one_half (f : (ι → Bool) → ℝ) (S : Finset ι) :
    biasedFourierCoeff (1 / 2) f S = fourierCoeff f S := by
  simp only [biasedFourierCoeff, biasedChi_one_half, bernoulliAverage_one_half, fourierCoeff]

section Expansion

variable {p : ℝ}

/-- A biased character as a product over all coordinates. -/
theorem biasedChi_eq_prod_univ (p : ℝ) (S : Finset ι) (x : ι → Bool) :
    biasedChi p S x = ∏ i, if i ∈ S then biasedBasis p (x i) else 1 :=
  (Fintype.prod_ite_mem S _).symm

omit [Fintype ι] [DecidableEq ι] in
/-- The biased character of the empty set is the constant `1`. -/
@[simp] theorem biasedChi_empty (p : ℝ) (x : ι → Bool) : biasedChi p ∅ x = 1 :=
  prod_empty

/-- The biased Fourier coefficient on the empty set is the mean, the first formula of
[O'Donnell, Proposition 8.16][ODonnell2014]; it holds for every `p`. -/
@[simp] theorem biasedFourierCoeff_empty (p : ℝ) (f : (ι → Bool) → ℝ) :
    biasedFourierCoeff p f ∅ = bernoulliAverage p f := by
  simp only [biasedFourierCoeff, biasedChi_empty, mul_one]

/-- **The biased characters are orthonormal** under the `p`-biased distribution, for
`0 < p < 1`: the orthonormality half of [O'Donnell, Proposition 8.13][ODonnell2014] for bits. -/
theorem bernoulliAverage_biasedChi_mul_biasedChi (hp : 0 < p) (hp1 : p < 1) (S T : Finset ι) :
    bernoulliAverage p (fun x => biasedChi p S x * biasedChi p T x) = if S = T then 1 else 0 := by
  simp only [biasedChi_eq_prod_univ, ← prod_mul_distrib]
  rw [bernoulliAverage_prod p fun i b =>
    (if i ∈ S then biasedBasis p b else 1) * if i ∈ T then biasedBasis p b else 1]
  split_ifs with hST
  · subst hST
    refine prod_eq_one fun i _ => ?_
    split_ifs
    · simpa [sq] using biasedBasis_sq_mean hp hp1
    · ring
  · obtain ⟨i, hi⟩ : ∃ i, ¬(i ∈ S ↔ i ∈ T) := by simpa [Finset.ext_iff] using hST
    refine prod_eq_zero (mem_univ i) ?_
    by_cases hS : i ∈ S <;> simpa [hS, ← not_iff.1 hi] using biasedBasis_mean p

omit [DecidableEq ι] in
/-- The indicator of the point `y` is `bernoulliWeight p y ∑_S φ_S(x) φ_S(y)`, where
`bernoulliWeight p y = ∏ᵢ π_p(yᵢ)` is the product mass at `y`. -/
theorem bernoulliWeight_mul_sum_biasedChi_mul_biasedChi (hp : 0 < p) (hp1 : p < 1)
    (x y : ι → Bool) :
    bernoulliWeight p y * ∑ S, biasedChi p S x * biasedChi p S y =
      if x = y then (1 : ℝ) else 0 := by
  have h : ∑ S, biasedChi p S x * biasedChi p S y =
      ∏ i, (1 + biasedBasis p (x i) * biasedBasis p (y i)) := by
    rw [prod_one_add, powerset_univ]
    exact sum_congr rfl fun S _ => (prod_mul_distrib ..).symm
  rw [h, bernoulliWeight, ← prod_mul_distrib]
  simp only [ite_mul_one_add_biasedBasis_mul_biasedBasis hp hp1]
  rw [prod_boole]
  simp [funext_iff]

/-- **The biased Fourier expansion** [O'Donnell, Definition 8.40][ODonnell2014]: for
`0 < p < 1`, `f = ∑_S f̂(S) φ_S`. -/
theorem sum_biasedFourierCoeff_mul_biasedChi (hp : 0 < p) (hp1 : p < 1) (f : (ι → Bool) → ℝ)
    (x : ι → Bool) : ∑ S, biasedFourierCoeff p f S * biasedChi p S x = f x := by
  simp only [biasedFourierCoeff, bernoulliAverage, sum_mul]
  rw [sum_comm]
  calc ∑ y, ∑ S, bernoulliWeight p y * (f y * biasedChi p S y) * biasedChi p S x
      = ∑ y, f y * (if x = y then 1 else 0) := by
        refine sum_congr rfl fun y _ => ?_
        rw [← bernoulliWeight_mul_sum_biasedChi_mul_biasedChi hp hp1, mul_sum, mul_sum]
        exact sum_congr rfl fun S _ => by ring
    _ = f x := by simp

/-- **Plancherel's identity** for biased Fourier coefficients, for `0 < p < 1`, one of the formulas
of [O'Donnell, Proposition 8.16][ODonnell2014]. -/
theorem bernoulliAverage_mul_eq_sum_biasedFourierCoeff_mul (hp : 0 < p) (hp1 : p < 1)
    (f g : (ι → Bool) → ℝ) :
    bernoulliAverage p (fun x => f x * g x) =
      ∑ S, biasedFourierCoeff p f S * biasedFourierCoeff p g S := by
  have hg (x : ι → Bool) : f x * g x = ∑ S, biasedFourierCoeff p g S * (f x * biasedChi p S x) := by
    conv_lhs => rw [← sum_biasedFourierCoeff_mul_biasedChi hp hp1 g x]
    rw [mul_sum]
    exact sum_congr rfl fun S _ => by ring
  simp only [hg, bernoulliAverage_sum, bernoulliAverage_const_mul]
  exact sum_congr rfl fun S _ => mul_comm _ _

/-- **Parseval's identity** for biased Fourier coefficients, for `0 < p < 1`, one of the formulas
of [O'Donnell, Proposition 8.16][ODonnell2014]. -/
theorem bernoulliAverage_sq_eq_sum_biasedFourierCoeff_sq (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) :
    bernoulliAverage p (fun x => f x ^ 2) = ∑ S, biasedFourierCoeff p f S ^ 2 := by
  simpa only [sq] using bernoulliAverage_mul_eq_sum_biasedFourierCoeff_mul hp hp1 f f

/-- **The covariance is the sum of the products of the biased Fourier coefficients on the nonempty
sets**, for `0 < p < 1`, one of the formulas of [O'Donnell, Proposition 8.16][ODonnell2014]. -/
theorem bernoulliAverage_sub_bernoulliAverage_mul_sub_bernoulliAverage_eq_sum (hp : 0 < p)
    (hp1 : p < 1) (f g : (ι → Bool) → ℝ) :
    bernoulliAverage p (fun x => (f x - bernoulliAverage p f) * (g x - bernoulliAverage p g)) =
      ∑ S with S ≠ ∅, biasedFourierCoeff p f S * biasedFourierCoeff p g S := by
  rw [bernoulliAverage_sub_bernoulliAverage_mul_sub_bernoulliAverage,
    bernoulliAverage_mul_eq_sum_biasedFourierCoeff_mul hp hp1, ← biasedFourierCoeff_empty,
    ← biasedFourierCoeff_empty, ← add_sum_erase _ _ (mem_univ ∅), add_sub_cancel_left,
    filter_ne']

/-- **The variance is the biased Fourier weight on the nonempty sets**, for `0 < p < 1`, one of the
formulas of [O'Donnell, Proposition 8.16][ODonnell2014]. -/
theorem bernoulliAverage_sub_bernoulliAverage_sq_eq_sum_biasedFourierCoeff_sq (hp : 0 < p)
    (hp1 : p < 1) (f : (ι → Bool) → ℝ) :
    bernoulliAverage p (fun x => (f x - bernoulliAverage p f) ^ 2) =
      ∑ S with S ≠ ∅, biasedFourierCoeff p f S ^ 2 := by
  simpa only [sq] using
    bernoulliAverage_sub_bernoulliAverage_mul_sub_bernoulliAverage_eq_sum hp hp1 f f

/-- **The biased Fourier coefficients of a dictator** [O'Donnell, Example 8.41][ODonnell2014]: for
`0 < p < 1`, the dictator `xᵢ`, read as a sign, is `μ + σ φ_{i}`, so its coefficients are `μ` on
`∅`, `σ` on `{i}` and `0` elsewhere. -/
theorem biasedFourierCoeff_dictator (hp : 0 < p) (hp1 : p < 1) (i : ι) (S : Finset ι) :
    biasedFourierCoeff p (fun x => signVal (x i)) S =
      (if S = ∅ then 1 - 2 * p else 0) + if S = {i} then biasedStd p else 0 := by
  have hσ := biasedStd_ne_zero hp hp1
  have hx (x : ι → Bool) : signVal (x i) =
      (1 - 2 * p) * biasedChi p ∅ x + biasedStd p * biasedChi p {i} x := by
    simp only [biasedChi, prod_empty, prod_singleton, biasedBasis, mul_one]
    field_simp
    ring
  simp only [biasedFourierCoeff, hx, add_mul, mul_assoc]
  rw [bernoulliAverage_add, bernoulliAverage_const_mul, bernoulliAverage_const_mul,
    bernoulliAverage_biasedChi_mul_biasedChi hp hp1,
    bernoulliAverage_biasedChi_mul_biasedChi hp hp1]
  simp only [mul_ite, mul_one, mul_zero, @eq_comm _ ∅ S, @eq_comm _ ({i} : Finset ι) S]

/-- Pairing across bit `i` against the centered sign of bit `i`: with `μ = 1 - 2p`, the mean of
`signVal (x i)`, the `p`-biased expectation of `h · (signVal (x i) - μ)` is `4p(1 - p)` times that
of the derivative `Dᵢ h`, for every `p`. Since `σ² = 4p(1 - p)`, this is the step
`𝔼_p[D_{x_i} f] = σ⁻¹ f̂^{(p)}(i)` of the book's proof of (8.8)
(`BitString.biasedFourierCoeff_singleton`). -/
theorem bernoulliAverage_mul_signVal_sub (h : (ι → Bool) → ℝ) (p : ℝ) (i : ι) :
    (bernoulliAverage p fun x => h x * (signVal (x i) - (1 - 2 * p))) =
      4 * p * (1 - p) * bernoulliAverage p (derivative i h) := by
  rw [bernoulliAverage_eq_bernoulliAverage_update p i, ← bernoulliAverage_const_mul]
  congr 1
  funext x
  simp only [Function.update_self, derivative, signVal_false, signVal_true]
  ring

/-- The step `f̂(i) = σ 𝔼_p[D_{x_i} f]` of the proof of [O'Donnell, (8.8)][ODonnell2014] (p. 225):
for `0 < p < 1`, a degree-one biased coefficient is `σ` times a mean derivative, where `D_{x_i} f`
is the usual derivative `BitString.derivative`, so that `σ D_{x_i}` is the book's biased derivative
`Dᵢ` of its Definition 8.44. -/
theorem biasedFourierCoeff_singleton (hp : 0 < p) (hp1 : p < 1) (i : ι) (f : (ι → Bool) → ℝ) :
    biasedFourierCoeff p f {i} = biasedStd p * bernoulliAverage p (derivative i f) := by
  have hσ := biasedStd_ne_zero hp hp1
  have hc : biasedFourierCoeff p f {i} =
      (biasedStd p)⁻¹ * bernoulliAverage p fun x => f x * (signVal (x i) - (1 - 2 * p)) := by
    rw [biasedFourierCoeff, ← bernoulliAverage_const_mul]
    congr 1
    funext x
    rw [biasedChi, prod_singleton, biasedBasis]
    ring
  rw [hc, bernoulliAverage_mul_signVal_sub, ← mul_assoc, ← mul_assoc]
  congr 1
  field_simp
  rw [biasedStd_sq hp.le hp1.le]
  ring

end Expansion

end Cslib.BitString
