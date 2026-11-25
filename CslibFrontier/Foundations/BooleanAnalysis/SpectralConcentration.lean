/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
import Mathlib.Tactic.Linarith

/-!
# Spectral concentration on collections of sets

The spectrum of `f` is `ε`-concentrated on a collection `F` of sets when its Fourier weight off
`F` is at most `ε`, `∑_{S ∉ F} f̂(S) ^ 2 ≤ ε` [O'Donnell, Definition 3.28][ODonnell2014]. The
results here bound the weight on an arbitrary collection `T` of sets, so they apply to
`T = Fᶜ` and to the degree tails `T = {S | k < |S|}` of [O'Donnell, Definition 3.1][ODonnell2014]
alike; `CslibFrontier.Foundations.BooleanAnalysis.Concentration` bounds the degree tails from
total influence and noise sensitivity instead. By Parseval's identity the weight of any `f`
on `T` is at most `‖f‖₂ ^ 2` (`BitString.sum_fourierCoeff_sq_le_expect_sq`), and applied to
`f - g`:

* if `ĝ` vanishes on `T`, the weight of `f` on `T` is at most `‖f - g‖₂ ^ 2`
  (`BitString.sum_fourierCoeff_sq_le_expect_sub_sq`), as in the proof of
  [O'Donnell, Theorem 3.29][ODonnell2014]; with `‖f - g‖₂ ^ 2 = 4 Pr[f ≠ g]` for Boolean functions
  read as signs (`BitString.expect_sq_signVal_sub_signVal`), a Boolean function close to one of
  degree at most `k` has little weight above degree `k`;
* the weight of `g` on `T` is at most twice the weight of `f` on `T` plus twice `‖f - g‖₂ ^ 2`
  (`BitString.sum_fourierCoeff_sq_le_two_mul_add`): concentration survives approximation
  [O'Donnell, Exercise 3.17][ODonnell2014].

Coefficients of absolute value at most `θ` on `T` weigh at most `θ ‖f̂‖₁` there
(`BitString.sum_fourierCoeff_sq_le_mul_sum_abs`), the estimate behind the Kushilevitz–Mansour
algorithm (`UniformLearning.uniformError_kmHypothesis_le`). So a function with small spectral
`1`-norm is `ε`-concentrated on a collection of at most `‖f̂‖₁ ^ 2 / ε` sets
(`BitString.exists_card_le_sum_fourierCoeff_sq_le`) [O'Donnell, Exercise 3.16][ODonnell2014]; the
proof takes the sets `S` with `ε ≤ ‖f̂‖₁ |f̂(S)|`. Against any collection `F`, the coefficients of
absolute value at most `θ` on `T` weigh at most their weight off `F` plus `#F θ²`
(`BitString.sum_fourierCoeff_sq_le_sum_compl_add`), the estimate behind learning concentrated
classes (`UniformLearning.kmLearner_learns_concentrated`).

## Usage

Open `Cslib` and `Cslib.BitString`. The weight `W_T[f]` of a real function on a collection
`T : Finset (Finset ι)` is written `∑ S ∈ T, fourierCoeff f S ^ 2`; take `T = Fᶜ` for
concentration on `F`, `T = {S | t < #S}` (written `∑ S with t < #S`) for the degree tail, and
`∑ S with ¬S ⊆ J` for the sets that are not subsets of `J`. The squared distance `‖f - g‖₂ ^ 2` is
`𝔼 x, (f x - g x) ^ 2` and the spectral `1`-norm `‖f̂‖₁` is `∑ S, |fourierCoeff f S|`. A Boolean
function enters through `fun x => signVal (f x)`. For `g` of degree at most `t`
(`(fun x => signVal (g x)) ∈ lowDegree ℝ ι t`), `BitString.fourierCoeff_eq_zero_of_mem_lowDegree`
gives the vanishing hypothesis of `BitString.sum_fourierCoeff_sq_le_expect_sub_sq` on the degree
tail, and `BitString.expect_sq_signVal_sub_signVal` rewrites the distance as
`4 * (hammingDist f g / 2 ^ Fintype.card ι)`: a Boolean function at relative Hamming distance `δ`
from one of degree at most `t` has weight at most `4 δ` above degree `t`. The book's form of
Exercise 3.17, with `ε₁`-concentration of `f` and `‖f - g‖₂ ^ 2 ≤ ε₂`, follows from
`BitString.sum_fourierCoeff_sq_le_two_mul_add` by `linarith`. The collection of Exercise 3.16 feeds
`BitString.hammingDist_signRound_sum_mul_chi_div_le`: rounding the expansion of a Boolean function
on that collection to signs errs on at most an `ε` fraction of inputs. Checked clients test each
bound on characters of two and three bits, derive the close-to-low-degree corollary and the book's
form of Exercise 3.17, and combine Exercise 3.16 with sign rounding, in
[`CslibFrontierTests/BooleanAnalysisSpectralConcentration.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisSpectralConcentration.lean).

## Main results

* `Cslib.BitString.sum_fourierCoeff_sq_le_expect_sq`: Bessel's inequality on a collection of sets.
* `Cslib.BitString.sum_fourierCoeff_sq_le_expect_sub_sq`: approximation by a function with no
  weight on `T`.
* `Cslib.BitString.sum_fourierCoeff_sq_le_two_mul_add`: Exercise 3.17.
* `Cslib.BitString.sum_fourierCoeff_sq_le_mul_sum_abs`,
  `Cslib.BitString.sum_fourierCoeff_sq_le_sum_compl_add`: the weight of small coefficients.
* `Cslib.BitString.exists_card_le_sum_fourierCoeff_sq_le`: Exercise 3.16.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Bessel's inequality**: the Fourier weight of `f` on any collection `T` of sets is at most
`‖f‖₂ ^ 2 = 𝔼_x f(x) ^ 2`, by Parseval's identity. -/
theorem sum_fourierCoeff_sq_le_expect_sq (T : Finset (Finset ι)) (f : (ι → Bool) → ℝ) :
    ∑ S ∈ T, fourierCoeff f S ^ 2 ≤ 𝔼 x, f x ^ 2 := by
  rw [expect_sq_eq_sum_fourierCoeff_sq]
  exact sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _

/-- **Approximation by a function with no weight on `T`**: if `ĝ` vanishes on `T` then the
weight of `f` on `T` is at most `‖f - g‖₂ ^ 2`. -/
theorem sum_fourierCoeff_sq_le_expect_sub_sq {T : Finset (Finset ι)} {f g : (ι → Bool) → ℝ}
    (hg : ∀ S ∈ T, fourierCoeff g S = 0) :
    ∑ S ∈ T, fourierCoeff f S ^ 2 ≤ 𝔼 x, (f x - g x) ^ 2 :=
  (sum_congr rfl fun S hS => by rw [fourierCoeff_sub, hg S hS, sub_zero]).trans_le
    (sum_fourierCoeff_sq_le_expect_sq T fun x => f x - g x)

/-- **Concentration survives approximation**: the weight of `g` on `T` is at most
`2 (W_T[f] + ‖f - g‖₂ ^ 2)`; so if the spectrum of `f` is `ε₁`-concentrated on `F` and
`‖f - g‖₂ ^ 2 ≤ ε₂`, then the spectrum of `g` is `2 (ε₁ + ε₂)`-concentrated on `F`, taking
`T = Fᶜ` [O'Donnell, Exercise 3.17][ODonnell2014]. -/
theorem sum_fourierCoeff_sq_le_two_mul_add (T : Finset (Finset ι)) (f g : (ι → Bool) → ℝ) :
    ∑ S ∈ T, fourierCoeff g S ^ 2 ≤
      2 * (∑ S ∈ T, fourierCoeff f S ^ 2 + 𝔼 x, (f x - g x) ^ 2) := by
  have h : ∑ S ∈ T, fourierCoeff g S ^ 2 ≤ ∑ S ∈ T, (2 * fourierCoeff f S ^ 2 +
      2 * (fourierCoeff f S - fourierCoeff g S) ^ 2) :=
    sum_le_sum fun S _ => by nlinarith [sq_nonneg (2 * fourierCoeff f S - fourierCoeff g S)]
  have hfg := sum_fourierCoeff_sq_le_expect_sq T fun x => f x - g x
  simp only [fourierCoeff_sub] at hfg
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at h
  linarith

/-- **The weight of small coefficients**: if every coefficient of `f` on `T` has absolute value at
most `θ`, then the weight of `f` on `T` is at most `θ ‖f̂‖₁`. -/
theorem sum_fourierCoeff_sq_le_mul_sum_abs {T : Finset (Finset ι)} {f : (ι → Bool) → ℝ} {θ : ℝ}
    (hθ : 0 ≤ θ) (h : ∀ S ∈ T, |fourierCoeff f S| ≤ θ) :
    ∑ S ∈ T, fourierCoeff f S ^ 2 ≤ θ * ∑ S, |fourierCoeff f S| := by
  rw [mul_sum]
  refine (sum_le_sum fun S hS => ?_).trans
    (sum_le_univ_sum_of_nonneg fun _ => mul_nonneg hθ (abs_nonneg _))
  rw [← sq_abs, sq]
  exact mul_le_mul_of_nonneg_right (h S hS) (abs_nonneg _)

/-- **The weight of small coefficients against a collection**: if every coefficient of `f` on `T`
has absolute value at most `θ`, then the weight of `f` on `T` is at most its weight off any
collection `F` plus `#F θ²`. With `T` the sets whose coefficient is below `θ`, this bounds what the
Kushilevitz–Mansour search misses for a function concentrated on `F`. -/
theorem sum_fourierCoeff_sq_le_sum_compl_add {T : Finset (Finset ι)} {f : (ι → Bool) → ℝ}
    {θ : ℝ} (h : ∀ S ∈ T, |fourierCoeff f S| ≤ θ) (F : Finset (Finset ι)) :
    ∑ S ∈ T, fourierCoeff f S ^ 2 ≤ ∑ S ∈ Fᶜ, fourierCoeff f S ^ 2 + #F * θ ^ 2 := by
  rw [← sum_filter_add_sum_filter_not T (fun S => S ∈ F), add_comm]
  refine add_le_add (sum_le_sum_of_subset_of_nonneg
    (fun S hS => mem_compl.2 (mem_filter.1 hS).2) fun _ _ _ => sq_nonneg _) ?_
  calc ∑ S ∈ T with S ∈ F, fourierCoeff f S ^ 2 ≤ ∑ _S ∈ T with _S ∈ F, θ ^ 2 :=
        sum_le_sum fun S hS => by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h S (mem_filter.1 hS).1) 2
    _ = #(T.filter fun S => S ∈ F) * θ ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ #F * θ ^ 2 := by
        gcongr
        exact fun S hS => (mem_filter.1 hS).2

/-- **Small spectral `1`-norm forces concentration on few sets**: the spectrum of `f` is
`ε`-concentrated on a collection of at most `‖f̂‖₁ ^ 2 / ε` sets
[O'Donnell, Exercise 3.16][ODonnell2014]. -/
theorem exists_card_le_sum_fourierCoeff_sq_le (f : (ι → Bool) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset (Finset ι), (#F : ℝ) ≤ (∑ S, |fourierCoeff f S|) ^ 2 / ε ∧
      ∑ S ∈ Fᶜ, fourierCoeff f S ^ 2 ≤ ε := by
  set N := ∑ S, |fourierCoeff f S|
  rcases (sum_nonneg fun _ _ => abs_nonneg _ : 0 ≤ N).eq_or_lt with hN0 | hN
  · -- All coefficients vanish, so the empty collection works.
    refine ⟨∅, by rw [card_empty, Nat.cast_zero]; positivity, ?_⟩
    refine (sum_eq_zero fun S _ => ?_).trans_le hε.le
    rw [sq_eq_zero_iff, ← abs_eq_zero]
    exact (sum_eq_zero_iff_of_nonneg fun _ _ => abs_nonneg _).1 hN0.symm S (mem_univ S)
  refine ⟨({S | ε ≤ N * |fourierCoeff f S|} : Finset (Finset ι)), ?_, ?_⟩
  · -- Each kept set carries at least `ε / N` of the `1`-norm.
    rw [le_div_iff₀ hε, sq, ← nsmul_eq_mul, mul_sum]
    exact (card_nsmul_le_sum _ _ _ fun S hS => (mem_filter.1 hS).2).trans
      (sum_le_univ_sum_of_nonneg fun _ => by positivity)
  · -- Each discarded coefficient is below `ε / N`.
    refine (sum_fourierCoeff_sq_le_mul_sum_abs (θ := ε / N) (by positivity) fun S hS => ?_).trans_eq
      (div_mul_cancel₀ _ hN.ne')
    rw [le_div_iff₀' hN]
    exact (not_le.1 (by simpa using hS)).le

end Cslib.BitString
