/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Foundations.Combinatorics.Hoeffding
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.BitString.Rademacher

/-!
# The Level-1 Inequality

A function `f` on the cube with values in `[-1, 1]` and `α = 𝔼 |f| ≤ 1/2` has degree-one weight
`W¹[f] ≤ 16 α ^ 2 ln (1 / α)` (`BitString.levelWeight_one_le_of_abs_le_one`): functions of small
`L¹` norm have small degree-one weight. This is the **Level-1 Inequality**
`W¹[f] ≤ O(α ^ 2 log (1 / α))` [O'Donnell, Section 5.4, p. 126][ODonnell2014], with the explicit
constant `16`, in the generality of the book's proof (p. 128), which follows its Remark 5.28. For
a `{0, 1}`-valued `f`, the indicator of a set, the sharp form `W¹[f] ≤ 2 α ^ 2 ln (1 / α)` of
Remark 5.28 holds for every `α`; it is `BitString.levelWeight_one_indicator_le` in
`CslibFrontier.Foundations.BooleanAnalysis.LevelK`, proved through small-set expansion.

The proof is the book's: with `σ ^ 2 = W¹[f]` and `ℓ = f^{=1} / σ`, the correlation `σ = 𝔼[f ℓ]`
splits at `|ℓ| = s` into at most `α s` and the tail `𝔼[|ℓ| 1{|ℓ| ≥ s}]`. The book bounds the tail
by integrating Hoeffding's bound (its Lemma 5.31). Here Cauchy–Schwarz and Hoeffding's bound
(`BitString.card_filter_le_abs_sum_mul_signVal_le`) bound it by `√(2 exp (-s ^ 2 / 2))`, which
is `√2 α` at `s = 2 √(ln (1 / α))`. This loses only in the constant: the book's choice of `s`
gives `(2 + o(1)) α ^ 2 ln (1 / α)`, asymptotically the sharp `2 α ^ 2 ln (1 / α)` of its
Remark 5.28.

Not included, and tracked on [#2131](https://github.com/cslib-community/cslib-frontier/issues/2131):
the sharp constant of Remark 5.28 for `[-1, 1]`-valued functions, Lemma 5.31 itself,
Corollary 5.32 and the `2/π` Theorem.

## Usage

Open `Cslib` and `Cslib.BitString`. The degree-one weight `W¹[f]` is `levelWeight 1 f`, which
`BitString.levelWeight_one` rewrites as `∑ i, fourierCoeff f {i} ^ 2`. A function with values in
`[-1, 1]` enters directly, with `α = 𝔼 x, |f x| ≤ 1 / 2`; a Boolean function read as `0` or `1`
through `fun x => bitVal ℝ (f x)` is such a function, with `α` its mean, but for it the sharp
`BitString.levelWeight_one_indicator_le` (applied to `{x | f x = true}`) is stronger and needs no
bound on `α`. The logarithm is natural, so `log α⁻¹` is the book's `ln (1 / α)`. Hoeffding's bound
for weighted sums of signs, which the proof uses for the tail of `ℓ`, is
`BitString.card_filter_le_abs_sum_mul_signVal_le` in
`CslibFrontier.Foundations.Combinatorics.Hoeffding`: at most
`2 * 2 ^ Fintype.card ι * exp (-(t ^ 2 / (2 * ∑ i, a i ^ 2)))` strings `x` have
`t ≤ |∑ i, a i * signVal (x i)|`. Checked clients bound the degree-one weight of the two-bit AND
by `log 4` and of minus half of it by `log 8 / 4`, and apply Hoeffding's bound to four unweighted
signs, in
[`CslibFrontierTests/BooleanAnalysisLevelOneInequality.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisLevelOneInequality.lean);
the seven-bit `{0, 1}`-valued witness (`α = 1 / 128`), where the sharp bound is below the trivial
`α (1 - α)`, is in
[`CslibFrontierTests/BooleanAnalysisLevelK.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisLevelK.lean).

## Main results

* `Cslib.BitString.levelWeight_one_le_of_abs_le_one`: the Level-1 Inequality for `[-1, 1]`-valued
  functions.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The tail of a normalized linear form `ℓ = ∑ i, c i xᵢ` in random signs: if
`∑ i, c i ^ 2 = 1` and `0 ≤ s`, then `𝔼[|ℓ| 1{|ℓ| ≥ s}] ≤ √(2 exp (-s ^ 2 / 2))`, by Cauchy–Schwarz
and Hoeffding's bound. This is the counterpart of [O'Donnell, Lemma 5.31][ODonnell2014], which
bounds `𝔼[|ℓ| 1{|ℓ| > s}]` by `(2 s + 2) exp (-s ^ 2 / 2)` for `s ≥ 1` by integrating Hoeffding's
bound. -/
private theorem expect_abs_sum_mul_signVal_mul_ite_le {c : ι → ℝ} (hc : ∑ i, c i ^ 2 = 1) {s : ℝ}
    (hs : 0 ≤ s) :
    𝔼 x : ι → Bool, |∑ i, c i * signVal (x i)| *
        (if s ≤ |∑ i, c i * signVal (x i)| then 1 else 0) ≤ √(2 * exp (-(s ^ 2 / 2))) := by
  refine (expect_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
  simp only [sq_abs, expect_sq_sum_mul_signVal, hc, sqrt_one, one_mul, Fintype.expect_boole_sq]
  refine sqrt_le_sqrt ?_
  have hcard := card_filter_le_abs_sum_mul_signVal_le c hs
  rw [hc, mul_one] at hcard
  rw [nnratCast_dens, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat,
    div_le_iff₀ (by positivity)]
  linarith

/-- **The Level-1 Inequality for `[-1, 1]`-valued functions**: a function `f` on the cube with
values in `[-1, 1]` and `α = 𝔼 |f| ≤ 1/2` has degree-one weight `W¹[f] ≤ 16 α ^ 2 ln (1 / α)`
[O'Donnell, Level-1 Inequality, Section 5.4, p. 126][ODonnell2014]. The book states
`O(α ^ 2 log (1 / α))` for `{0, 1}`-valued `f`, and its proof (p. 128), following Remark 5.28,
takes `f` with values in `[-1, 1]` and `α = 𝔼 |f|`, as here. The constant is the explicit `16`
in place of `O(1)`; the book's sharper `2 + o(1)` is not proved in this setting. The logarithm is
natural, where the book's `log` is `log₂` (List of Notation, p. xvi); this changes only the
constant inside `O(·)`. For `{0, 1}`-valued `f` the sharp `BitString.levelWeight_one_indicator_le`
in `CslibFrontier.Foundations.BooleanAnalysis.LevelK` is stronger. When `α = 0`, `f = 0` and both
sides vanish. -/
theorem levelWeight_one_le_of_abs_le_one {f : (ι → Bool) → ℝ} (hf : ∀ x, |f x| ≤ 1)
    (hα : 𝔼 x, |f x| ≤ 1 / 2) :
    levelWeight 1 f ≤ 16 * (𝔼 x, |f x|) ^ 2 * log (𝔼 x, |f x|)⁻¹ := by
  set α := 𝔼 x, |f x|
  set a : ι → ℝ := fun i => fourierCoeff f {i}
  set W := ∑ i, a i ^ 2
  rw [levelWeight_one]
  change W ≤ 16 * α ^ 2 * log α⁻¹
  have hα₀ : 0 ≤ α := expect_nonneg fun x _ => abs_nonneg (f x)
  rcases (show 0 ≤ W from sum_nonneg fun _ _ => sq_nonneg _).eq_or_lt with hW | hW
  · rw [← hW]
    have : 0 ≤ log α⁻¹ := by
      rw [log_inv]
      linarith [log_nonpos hα₀ (by linarith : α ≤ 1)]
    positivity
  -- Normalize the degree-one part: `ℓ = f^{=1} / σ` with `σ = √W`.
  set σ := √W
  have hσ : 0 < σ := sqrt_pos.2 hW
  have hσσ : σ ^ 2 = W := sq_sqrt hW.le
  set c : ι → ℝ := fun i => a i / σ
  have hc : ∑ i, c i ^ 2 = 1 := by
    simp only [c, div_pow, ← sum_div, hσσ]
    exact div_self hW.ne'
  have hfℓ : 𝔼 x, f x * ∑ i, c i * signVal (x i) = σ := by
    simp_rw [mul_sum, ← chi_singleton, mul_left_comm (f _), expect_sum_comm, ← mul_expect]
    simp only [c, a, fourierCoeff, div_mul_eq_mul_div, ← sq, ← sum_div]
    rw [div_eq_iff hσ.ne', ← sq, hσσ]
    simp only [W, a, fourierCoeff]
  -- The threshold `s = 2 √(ln (1 / α))`, with `ln (1 / α) ≥ 1 - α ≥ 1 / 2`.
  have hα₀' : 0 < α := by
    refine hα₀.lt_of_ne fun h => hW.ne' ?_
    have hzero := (Fintype.expect_eq_zero_iff_of_nonneg fun x => abs_nonneg (f x)).1 h.symm
    have hf₀ (x : ι → Bool) : f x = 0 := abs_eq_zero.1 (congrFun hzero x)
    simp [W, a, fourierCoeff, hf₀]
  set L := log α⁻¹
  have hL : 1 / 2 ≤ L := by
    linarith [one_sub_inv_le_log_of_pos (inv_pos.2 hα₀'), inv_inv α]
  set s := 2 * √L
  have hs : 0 ≤ s := by positivity
  have hss : s ^ 2 = 4 * L := by
    rw [mul_pow, sq_sqrt (by linarith)]
    ring
  -- Split the correlation at `|ℓ| = s`.
  have hsplit (x : ι → Bool) : f x * ∑ i, c i * signVal (x i) ≤
      s * |f x| + |∑ i, c i * signVal (x i)| *
        (if s ≤ |∑ i, c i * signVal (x i)| then 1 else 0) := by
    set l := ∑ i, c i * signVal (x i)
    have hfl : f x * l ≤ |f x| * |l| := (le_abs_self _).trans_eq (abs_mul _ _)
    have := abs_nonneg (f x)
    split_ifs with h
    · nlinarith [hf x, abs_nonneg l]
    · nlinarith [mul_le_mul_of_nonneg_left (not_le.1 h).le this]
  -- The tail: `Pr[|ℓ| ≥ s] ≤ 2 exp (-s ^ 2 / 2) = 2 α ^ 2`.
  have htail := expect_abs_sum_mul_signVal_mul_ite_le hc hs
  have hexp : exp (-(s ^ 2 / 2)) = α ^ 2 := by
    rw [hss, show -(4 * L / 2) = log α + log α by simp only [L, log_inv]; ring, exp_add,
      exp_log hα₀']
    ring
  rw [hexp, sqrt_mul (by norm_num), sqrt_sq hα₀] at htail
  have hmain : σ ≤ s * α + √2 * α := by
    calc σ = 𝔼 x, f x * ∑ i, c i * signVal (x i) := hfℓ.symm
      _ ≤ 𝔼 x : ι → Bool, (s * |f x| + |∑ i, c i * signVal (x i)| *
            (if s ≤ |∑ i, c i * signVal (x i)| then 1 else 0)) :=
          expect_le_expect fun x _ => hsplit x
      _ ≤ s * α + √2 * α := by
          rw [expect_add_distrib, ← mul_expect]
          linarith [htail]
  have hsqrt2 : √2 ≤ s := sqrt_le_iff.2 ⟨hs, by linarith⟩
  calc W = σ ^ 2 := hσσ.symm
    _ ≤ (2 * s * α) ^ 2 := pow_le_pow_left₀ hσ.le (by nlinarith) 2
    _ = 16 * α ^ 2 * L := by rw [mul_pow, mul_pow, hss]; ring

end Cslib.BitString
