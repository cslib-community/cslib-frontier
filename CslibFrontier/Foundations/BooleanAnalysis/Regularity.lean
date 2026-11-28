/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
import CslibFrontier.Foundations.BooleanAnalysis.Influence

/-!
# Regular functions

A real function `f` on the cube is *`ε`-regular* if `|f̂(S)| ≤ ε` for every nonempty `S`
(`BitString.IsFourierRegular`) [O'Donnell, Definition 6.2][ODonnell2014]. Every Fourier
coefficient is at most `𝔼 |f|` in absolute value (`BitString.abs_fourierCoeff_le_expect_abs`)
[O'Donnell, Exercise 3.9][ODonnell2014], so every function is `‖f‖₁`-regular
(`BitString.isFourierRegular_expect_abs`)
[O'Donnell, Remark 6.3][ODonnell2014]. A function is `0`-regular exactly when it is constant
(`BitString.isFourierRegular_zero_iff`), and a character of a nonempty set is not `ε`-regular for
any `ε < 1` (`BitString.not_isFourierRegular_chi`) [O'Donnell, Example 6.4][ODonnell2014].

Regularity is detected by the fourth moment of the spectrum: an `ε`-regular `f` has
`∑_S f̂(S) ^ 4 - (𝔼 f) ^ 4 ≤ ε ^ 2 Var[f]`, while a function that is not `ε`-regular has
`∑_S f̂(S) ^ 4 - (𝔼 f) ^ 4 ≥ ε ^ 4`
(`BitString.sum_fourierCoeff_pow_four_sub_le_of_isFourierRegular`,
`BitString.pow_four_le_sum_fourierCoeff_pow_four_sub_of_not_isFourierRegular`)
[O'Donnell, Proposition 6.7][ODonnell2014].

## Main definitions

* `Cslib.BitString.IsFourierRegular`: `ε`-regular functions.

## Main results

* `Cslib.BitString.isFourierRegular_expect_abs`, `Cslib.BitString.isFourierRegular_zero_iff`,
  `Cslib.BitString.not_isFourierRegular_chi`: every function is `‖f‖₁`-regular, the `0`-regular
  functions are the constants, and characters are not `ε`-regular below `1`.
* `Cslib.BitString.sum_fourierCoeff_pow_four_sub_le_of_isFourierRegular`,
  `Cslib.BitString.pow_four_le_sum_fourierCoeff_pow_four_sub_of_not_isFourierRegular`:
  Proposition 6.7.

## Usage

Open `Cslib.BitString`. `IsFourierRegular ε f` is stated for any real `f : (ι → Bool) → ℝ`; a
Boolean function enters as `fun x => signVal (f x)`. The definition is exposed, so a client proves
it by `fun S hS => …` from a bound on each nonempty coefficient. In
`isFourierRegular_expect_abs f` the regularity parameter is `𝔼 x, |f x|`, which is
`Cslib.lpNorm 1 f` by `Cslib.lpNorm_one`. Proposition 6.7 writes the variance as
`𝔼 x, (f x - 𝔼 y, f y) ^ 2`, the form of `expect_sub_expect_sq_eq_sum_fourierCoeff_sq`; its second
half needs `0 ≤ ε`: for negative `ε` and nonempty `ι` no function is `ε`-regular, and a constant
then violates the bound. The checked clients in
[CslibFrontierTests/BooleanAnalysisRegularity.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisRegularity.lean)
show that constants are `0`-regular and that `χ_{0}` on three bits is not constant, is `1`-regular
but not `1/2`-regular, and satisfies both halves of Proposition 6.7. The other cases of
[O'Donnell, Example 6.4][ODonnell2014] (random functions, indicators of affine subspaces, inner
product and complete quadratic, majority) and `(ε, δ)`-regularity are not formalized.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real function on the cube is *`ε`-regular* if its Fourier coefficients on the nonempty sets
are at most `ε` in absolute value. -/
@[expose] def IsFourierRegular (ε : ℝ) (f : (ι → Bool) → ℝ) : Prop :=
  ∀ S : Finset ι, S.Nonempty → |fourierCoeff f S| ≤ ε

/-- **Every function is `‖f‖₁`-regular** [O'Donnell, Remark 6.3][ODonnell2014]. -/
theorem isFourierRegular_expect_abs (f : (ι → Bool) → ℝ) :
    IsFourierRegular (𝔼 x, |f x|) f :=
  fun S _ => abs_fourierCoeff_le_expect_abs f S

/-- **The `0`-regular functions are the constants** [O'Donnell, Example 6.4][ODonnell2014]. -/
theorem isFourierRegular_zero_iff {f : (ι → Bool) → ℝ} :
    IsFourierRegular 0 f ↔ ∃ c, f = fun _ => c := by
  constructor
  · intro h
    refine ⟨𝔼 x, f x, fourierCoeff_injective (funext fun S => ?_)⟩
    rw [fourierCoeff_const]
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp
    · rw [ite_eq_right hS.ne_empty]
      exact abs_nonpos_iff.1 (h S hS)
  · rintro ⟨c, rfl⟩ S hS
    rw [fourierCoeff_const, ite_eq_right hS.ne_empty, abs_zero]

/-- **A character is not `ε`-regular below `1`** [O'Donnell, Example 6.4][ODonnell2014]: a
character of a nonempty set has coefficient `1` on that set, so it is not `ε`-regular for any
`ε < 1`. -/
theorem not_isFourierRegular_chi {S : Finset ι} (hS : S.Nonempty) {ε : ℝ} (hε : ε < 1) :
    ¬ IsFourierRegular ε (chi ℝ S) := fun h => by
  have := h S hS
  rw [fourierCoeff_chi, ite_eq_left rfl, abs_one] at this
  linarith

/-- The fourth moment of the spectrum above the mean is the sum of the fourth powers of the
coefficients on the nonempty sets. -/
private theorem sum_fourierCoeff_pow_four_sub (f : (ι → Bool) → ℝ) :
    ∑ S, fourierCoeff f S ^ 4 - (𝔼 x, f x) ^ 4 = ∑ S ∈ univ.erase ∅, fourierCoeff f S ^ 4 := by
  rw [sum_erase_eq_sub (mem_univ _), fourierCoeff_empty]

/-- **Regular functions have small fourth spectral moment**
[O'Donnell, Proposition 6.7][ODonnell2014]: if `f` is `ε`-regular, then
`∑_S f̂(S) ^ 4 - (𝔼 f) ^ 4 ≤ ε ^ 2 Var[f]`. -/
theorem sum_fourierCoeff_pow_four_sub_le_of_isFourierRegular {ε : ℝ} {f : (ι → Bool) → ℝ}
    (h : IsFourierRegular ε f) :
    ∑ S, fourierCoeff f S ^ 4 - (𝔼 x, f x) ^ 4 ≤ ε ^ 2 * 𝔼 x, (f x - 𝔼 y, f y) ^ 2 := by
  rw [sum_fourierCoeff_pow_four_sub, expect_sub_expect_sq_eq_sum_fourierCoeff_sq, ← filter_ne',
    mul_sum]
  refine sum_le_sum fun S hS => ?_
  have hS' : S.Nonempty := nonempty_iff_ne_empty.2 (mem_filter.1 hS).2
  have hsq : fourierCoeff f S ^ 2 ≤ ε ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h S hS') 2
  calc fourierCoeff f S ^ 4 = fourierCoeff f S ^ 2 * fourierCoeff f S ^ 2 := by ring
    _ ≤ ε ^ 2 * fourierCoeff f S ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- **Irregular functions have large fourth spectral moment**
[O'Donnell, Proposition 6.7][ODonnell2014]: for `ε ≥ 0`, if `f` is not `ε`-regular, then
`∑_S f̂(S) ^ 4 - (𝔼 f) ^ 4 ≥ ε ^ 4`. -/
theorem pow_four_le_sum_fourierCoeff_pow_four_sub_of_not_isFourierRegular {ε : ℝ} (hε : 0 ≤ ε)
    {f : (ι → Bool) → ℝ} (h : ¬ IsFourierRegular ε f) :
    ε ^ 4 ≤ ∑ S, fourierCoeff f S ^ 4 - (𝔼 x, f x) ^ 4 := by
  simp only [IsFourierRegular, not_forall, not_le] at h
  obtain ⟨S, hS, hlt⟩ := h
  rw [sum_fourierCoeff_pow_four_sub]
  calc ε ^ 4 ≤ fourierCoeff f S ^ 4 :=
        (pow_le_pow_left₀ hε hlt.le 4).trans_eq (Even.pow_abs (by decide) _)
    _ ≤ ∑ S ∈ univ.erase ∅, fourierCoeff f S ^ 4 :=
        single_le_sum (f := fun S => fourierCoeff f S ^ 4) (fun _ _ => by positivity)
          (mem_erase.2 ⟨hS.ne_empty, mem_univ S⟩)

end Cslib.BitString
