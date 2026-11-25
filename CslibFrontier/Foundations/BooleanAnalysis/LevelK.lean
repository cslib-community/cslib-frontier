/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
public import CslibFrontier.Foundations.BooleanAnalysis.Noise
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.BooleanAnalysis.SmallSetExpansion
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Level-`k` Inequalities and the sharp Level-1 Inequality

Let `A` be a set of the cube `ι → Bool` with indicator `1_A = A.indicator 1` and volume
`α = 𝔼 x, 1_A x`, and write `W^{≤k}[1_A] = ∑_{|S| ≤ k} 1̂_A(S) ^ 2` for its Fourier weight up to
degree `k`, the empty set included as in the book. Since `ρ ^ |S| ≥ ρ ^ k` for `|S| ≤ k`, the
Fourier formula for the noise stability gives `ρ ^ k W^{≤k}[f] ≤ Stab_ρ[f]` for `0 ≤ ρ ≤ 1`
(`BitString.pow_mul_sum_filter_card_le_le_noiseStability`). Small-set expansion bounds
`Stab_ρ[1_A]`, so indicators of small sets have little Fourier weight at low degrees:

* at `ρ = 1 / 3`, Corollary 9.8 gives `W^{≤k}[1_A] ≤ 3 ^ k α ^ (3 / 2)` for every `k`
  (`BitString.sum_filter_card_le_fourierCoeff_indicator_sq_le_three_pow`)
  [O'Donnell, (9.7), Section 9.2, p. 256][ODonnell2014];
* the Small-Set Expansion Theorem at `ρ = k / (2 ln (1 / α))` gives the **Level-`k`
  Inequalities** `W^{≤k}[1_A] ≤ (2e / k · ln (1 / α)) ^ k α ^ 2` for `1 ≤ k ≤ 2 ln (1 / α)`
  (`BitString.sum_filter_card_le_fourierCoeff_indicator_sq_le_log_pow`)
  [O'Donnell, Level-k Inequalities, Section 9.5, p. 264][ODonnell2014];
* at degree one, `α ^ 2 + ρ W¹[1_A] ≤ Stab_ρ[1_A]` gives
  `W¹[1_A] ≤ (α ^ (2 / (1 + ρ)) - α ^ 2) / ρ` for `0 < ρ ≤ 1`
  (`BitString.levelWeight_one_indicator_le_rpow`)
  [O'Donnell, Exercise 9.18(a), p. 273][ODonnell2014],
  and letting `ρ → 0⁺` gives the **sharp Level-1 Inequality** `W¹[1_A] ≤ 2 α ^ 2 ln (1 / α)`
  (`BitString.levelWeight_one_indicator_le`) [O'Donnell, Exercise 9.18(b), p. 273][ODonnell2014],
  the `{0, 1}`-valued case of [O'Donnell, Remark 5.28, p. 126][ODonnell2014].

The logarithm is natural, as in the book's `ln`. Sets stand for the book's `{0, 1}`-valued
functions `f = 1_A`. Remark 5.28 also asserts the sharp bound for `[-1, 1]`-valued functions with
`α = 𝔼 |f|`; that extension is not formalized here and is tracked on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131), as is Exercise 9.19. For
`[-1, 1]`-valued functions, the Level-1 Inequality with the constant `16`, proved by the book's
Section 5.4 argument, is `BitString.levelWeight_one_le_of_abs_le_one` in
`CslibFrontier.Foundations.BooleanAnalysis.LevelOneInequality`.

## Usage

Open `Cslib` and `Cslib.BitString`. A set `A : Set (ι → Bool)` enters through its indicator
`A.indicator 1`, with volume `𝔼 x, A.indicator 1 x`; the degree-one weight is
`levelWeight 1 (A.indicator 1)`, and the weight up to degree `k` is written as the sum
`∑ S with #S ≤ k, fourierCoeff (A.indicator 1) S ^ 2`. For a Boolean function `f`, take
`A = {x | f x = true}`. The hypothesis `k ≤ 2 * log (𝔼 x, A.indicator 1 x)⁻¹` of the Level-`k`
Inequalities forces `0 < α < 1`: at `α = 1` the logarithm is `0`, and at `α = 0` it is Lean's
`log 0 = 0`, where the book's `ln (1 / α)` is undefined. The general bound
`ρ ^ k W^{≤k}[f] ≤ Stab_ρ[f]` holds for every real function. Checked clients on the one-bit subcube
of volume `1 / 2`, where Exercise 9.18(a) is attained at `ρ = 1`, on a point of the three-bit cube
at `k = 2`, and on a point of the seven-bit cube (`α = 1 / 128`), where the sharp bound and the
`k = 1` bound beat the trivial `W¹[1_A] ≤ α (1 - α)` and `W^{≤1}[1_A] ≤ α`, are in
[`CslibFrontierTests/BooleanAnalysisLevelK.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisLevelK.lean).

## Main results

* `Cslib.BitString.pow_mul_sum_filter_card_le_le_noiseStability`: `ρ ^ k W^{≤k}[f] ≤ Stab_ρ[f]`.
* `Cslib.BitString.sum_filter_card_le_fourierCoeff_indicator_sq_le_three_pow`: inequality (9.7).
* `Cslib.BitString.sum_filter_card_le_fourierCoeff_indicator_sq_le_log_pow`: the Level-`k`
  Inequalities.
* `Cslib.BitString.levelWeight_one_indicator_le_rpow`: Exercise 9.18(a).
* `Cslib.BitString.levelWeight_one_indicator_le`: the sharp Level-1 Inequality.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Real Filter
open scoped BigOperators Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Noise stability bounds the low-degree weight**: for `0 ≤ ρ ≤ 1`,
`ρ ^ k W^{≤k}[f] ≤ Stab_ρ[f]`, since `Stab_ρ[f] = ∑_S ρ ^ |S| f̂(S) ^ 2` and `ρ ^ |S| ≥ ρ ^ k` for
`|S| ≤ k`. A step of (9.7) (Section 9.2, p. 256) and of the proof of the Level-k Inequalities
(Section 9.5, p. 264) [O'Donnell][ODonnell2014]. -/
theorem pow_mul_sum_filter_card_le_le_noiseStability {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (k : ℕ)
    (f : (ι → Bool) → ℝ) :
    ρ ^ k * ∑ S with #S ≤ k, fourierCoeff f S ^ 2 ≤ noiseStability ρ f := by
  rw [noiseStability_eq_sum, mul_sum, sum_filter]
  refine sum_le_sum fun S _ => ?_
  split_ifs with hS
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hρ hρ' hS) (sq_nonneg _)
  · positivity

/-- **Level-`k` inequalities from Corollary 9.8**: for a set `A` of volume `α` and every `k`,
`W^{≤k}[1_A] ≤ 3 ^ k α ^ (3 / 2)`, since `α ^ (3 / 2) ≥ Stab_{1/3}[1_A] ≥ 3 ^ (-k) W^{≤k}[1_A]`
[O'Donnell, (9.7), Section 9.2, p. 256][ODonnell2014]. -/
theorem sum_filter_card_le_fourierCoeff_indicator_sq_le_three_pow (A : Set (ι → Bool)) (k : ℕ) :
    ∑ S with #S ≤ k, fourierCoeff (A.indicator 1) S ^ 2 ≤
      3 ^ k * (𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x) ^ (3 / 2 : ℝ) := by
  have h := (pow_mul_sum_filter_card_le_le_noiseStability (ρ := 1 / 3) (by norm_num)
    (by norm_num) k (A.indicator 1)).trans (noiseStability_one_third_indicator_le A)
  refine (?_ : _ = 3 ^ k * ((1 / 3 : ℝ) ^ k * _)).trans_le
    (mul_le_mul_of_nonneg_left h (by positivity))
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- **The Level-`k` Inequalities**: a set `A` of volume `α` has
`W^{≤k}[1_A] ≤ (2e / k · ln (1 / α)) ^ k α ^ 2` for `1 ≤ k ≤ 2 ln (1 / α)`
[O'Donnell, Level-k Inequalities, Section 9.5, p. 264][ODonnell2014]. The book's
`f : {-1, 1}ⁿ → {0, 1}` is the indicator `1_A`. By the Small-Set Expansion Theorem,
`W^{≤k}[1_A] ≤ ρ ^ (-k) Stab_ρ[1_A] ≤ ρ ^ (-k) α ^ (2 (1 - ρ))` for `0 < ρ ≤ 1`, and
`ρ = k / (2 ln (1 / α))` makes the right side `(2e / k · ln (1 / α)) ^ k α ^ 2`. -/
theorem sum_filter_card_le_fourierCoeff_indicator_sq_le_log_pow {k : ℕ} (hk : 0 < k)
    (A : Set (ι → Bool))
    (hkα : (k : ℝ) ≤ 2 * log (𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x)⁻¹) :
    ∑ S with #S ≤ k, fourierCoeff (A.indicator 1) S ^ 2 ≤
      (2 * exp 1 / k * log (𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x)⁻¹) ^ k *
        (𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x) ^ 2 := by
  set α := 𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x
  set L := log α⁻¹
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hL : 0 < L := by linarith
  have hα₀ : 0 < α := (expect_nonneg fun x _ =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) x).lt_of_ne' fun h =>
      hL.ne' (by simp [L, show α = 0 from h])
  have hα₁ : α < 1 := (log_neg_iff hα₀).1 (by simp only [L, log_inv] at hL; linarith)
  set ρ := (k : ℝ) / (2 * L)
  have hρ₀ : 0 < ρ := by positivity
  have hρ₁ : ρ ≤ 1 := (div_le_one (by positivity)).2 hkα
  -- `ρ ^ k W^{≤k} ≤ Stab_ρ ≤ α ^ (2 / (1 + ρ)) ≤ α ^ (2 (1 - ρ)) = α ^ 2 e ^ k`
  have hW := (pow_mul_sum_filter_card_le_le_noiseStability hρ₀.le hρ₁ k
    (A.indicator 1)).trans (noiseStability_indicator_le hρ₀.le hρ₁ A)
  have hexp : α ^ (2 / (1 + ρ)) ≤ α ^ 2 * exp k := by
    refine (rpow_le_rpow_of_exponent_ge (z := 2 * (1 - ρ)) hα₀ hα₁.le
      ((le_div_iff₀ (by linarith)).2 (by nlinarith))).trans_eq ?_
    rw [show 2 * (1 - ρ) = (2 : ℝ) + -(2 * ρ) by ring, rpow_add hα₀, rpow_two,
      rpow_def_of_pos hα₀]
    congr 2
    rw [show log α = -L by simp [L]]
    simp only [ρ]
    field_simp
  refine ((le_div_iff₀ (pow_pos hρ₀ k)).2 ((mul_comm _ _).trans_le (hW.trans hexp))).trans_eq ?_
  rw [show 2 * exp 1 / k * L = exp 1 / ρ by simp only [ρ]; field_simp, div_pow (exp 1) ρ k,
    ← exp_nat_mul, mul_one]
  ring

/-- **The degree-one weight through noise stability**: a set `A` of volume `α` has
`W¹[1_A] ≤ (α ^ (2 / (1 + ρ)) - α ^ 2) / ρ` for `0 < ρ ≤ 1`, since
`α ^ 2 + ρ W¹[1_A] ≤ Stab_ρ[1_A] ≤ α ^ (2 / (1 + ρ))`
[O'Donnell, Exercise 9.18(a), Section 9.7, p. 273][ODonnell2014]. -/
theorem levelWeight_one_indicator_le_rpow {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1)
    (A : Set (ι → Bool)) :
    levelWeight 1 (A.indicator 1) ≤
      ((𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x) ^ (2 / (1 + ρ)) -
        (𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x) ^ 2) / ρ := by
  -- the degree-zero and degree-one terms of the level-weight sum
  have hW : (𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x) ^ 2 + ρ * levelWeight 1 (A.indicator 1) ≤
      noiseStability ρ (A.indicator 1) := by
    rcases (Fintype.card ι).eq_zero_or_pos with hι | hι
    · rw [levelWeight_eq_zero_of_card_lt (by omega), mul_zero, add_zero]
      exact sq_expect_le_noiseStability hρ.le _
    · simpa only [pow_zero, one_mul, pow_one, levelWeight_zero,
        ← noiseStability_eq_sum_levelWeight] using
        add_le_sum (s := range (Fintype.card ι + 1))
          (f := fun k => ρ ^ k * levelWeight k (A.indicator 1))
          (fun k _ => mul_nonneg (pow_nonneg hρ.le k) (levelWeight_nonneg k _))
          (mem_range.2 (by omega)) (mem_range.2 (by omega)) zero_ne_one
  rw [le_div_iff₀ hρ, mul_comm]
  linarith [noiseStability_indicator_le hρ.le hρ' A]

/-- **The sharp Level-1 Inequality**: a set `A` of volume `α` has `W¹[1_A] ≤ 2 α ^ 2 ln (1 / α)`
[O'Donnell, Exercise 9.18(b), Section 9.7, p. 273][ODonnell2014], the `{0, 1}`-valued case of
[O'Donnell, Remark 5.28, Section 5.4, p. 126][ODonnell2014]. The book's
`f : {-1, 1}ⁿ → {0, 1}` is the indicator `1_A`, and every `α` is allowed, not only `α ≤ 1 / 2`.
Remark 5.28's extension to `[-1, 1]`-valued functions is not formalized. As `ρ → 0⁺` the bound of
Exercise 9.18(a) tends to the derivative of `ρ ↦ α ^ (2 / (1 + ρ))` at `0`, which is
`2 α ^ 2 ln (1 / α)`. Both sides vanish when `α = 0`. -/
theorem levelWeight_one_indicator_le (A : Set (ι → Bool)) :
    levelWeight 1 (A.indicator 1) ≤
      2 * (𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x) ^ 2 *
        log (𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x)⁻¹ := by
  set α := 𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x
  rcases (expect_nonneg fun x _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x :
    (0 : ℝ) ≤ α).eq_or_lt with hα | hα
  · have h := levelWeight_one_indicator_le_rpow zero_lt_one le_rfl A
    rw [show 𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x = 0 from hα.symm] at h
    rw [show α = 0 from hα.symm]
    simpa using h
  -- the derivative of `ρ ↦ α ^ (2 / (1 + ρ))` at `0`
  have hg : HasDerivAt (fun ρ : ℝ => 2 / (1 + ρ)) (-2) 0 := by
    simpa [div_eq_mul_inv] using
      (((hasDerivAt_id (0 : ℝ)).const_add 1).inv (by norm_num)).const_mul 2
  have hd : HasDerivAt (fun ρ : ℝ => α ^ (2 / (1 + ρ))) (2 * α ^ 2 * log α⁻¹) 0 := by
    convert hg.const_rpow hα using 1
    rw [log_inv]
    norm_num
    ring
  have hlim := hd.tendsto_slope_zero_right
  simp only [zero_add, add_zero, smul_eq_mul, div_one, rpow_two] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ρ hρ
  simpa only [div_eq_inv_mul] using levelWeight_one_indicator_le_rpow hρ.1 hρ.2 A

end Cslib.BitString
