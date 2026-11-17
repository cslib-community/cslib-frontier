/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.Data.BitString.Sign.Rounding
import Mathlib.Tactic.Positivity

/-!
# Rounding a real approximation to its sign

A real function `g` on the cube rounds to the Boolean function that is `true`, the sign `-1`,
exactly where `g` is negative (`BitString.signRound`). If `g` approximates a Boolean function `f`,
read as signs, in mean square, then the rounding is close to `f`: the fraction of the points where
they differ is at most `𝔼_x (f x - g x)²` (`BitString.hammingDist_signRound_div_le_expect_sq_sub`),
since a point where the signs differ contributes at least one to the mean square
[O'Donnell, Section 3.4][ODonnell2014].

By Parseval's identity, the mean-square distance from a function `F` to a combination
`∑_{S ∈ T} c_S χ_S` of the characters of a family `T` of sets is the squared error of the weights
on `T` plus the Fourier weight of `F` off `T` (`BitString.expect_sq_sub_sum_mul_chi`). So
estimating the Fourier coefficients of `f` on a family carrying almost all of its weight, and
rounding, approximates `f` (`BitString.hammingDist_signRound_sum_mul_chi_div_le`): the principle
of the low-degree algorithm of Linial, Mansour and Nisan [LinialMansourNisan1993].

## Main results

* `Cslib.BitString.hammingDist_signRound_div_le_expect_sq_sub`: rounding a mean-square
  approximation of a Boolean function to its sign approximates the function.
* `Cslib.BitString.expect_sq_sub_sum_mul_chi`: the mean-square distance to a combination of
  characters, by Parseval's identity.
* `Cslib.BitString.hammingDist_signRound_sum_mul_chi_div_le`: rounding approximate Fourier
  coefficients on a family of sets.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Rounding to the sign** [O'Donnell, Section 3.4][ODonnell2014]: the rounding of `g` differs
from `f` on at most a fraction `𝔼_x (f x - g x)²` of the points, reading `f` as signs. -/
theorem hammingDist_signRound_div_le_expect_sq_sub (f : (ι → Bool) → Bool)
    (g : (ι → Bool) → ℝ) :
    (hammingDist (signRound g) f : ℝ) / 2 ^ Fintype.card ι ≤
      𝔼 x, (signVal (f x) - g x) ^ 2 := by
  rw [expect_eq_sum_div_card, card_univ, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow,
    Nat.cast_ofNat]
  exact div_le_div_of_nonneg_right (hammingDist_signRound_le_sum_sq_sub f g) (by positivity)

/-- The mean-square distance from `F` to the combination `∑_{S ∈ T} c_S χ_S` of characters is the
squared error of the weights on `T` plus the Fourier weight of `F` off `T`. -/
theorem expect_sq_sub_sum_mul_chi (F : (ι → Bool) → ℝ) (T : Finset (Finset ι))
    (c : Finset ι → ℝ) :
    𝔼 x, (F x - ∑ S ∈ T, c S * chi ℝ S x) ^ 2 =
      ∑ S ∈ T, (fourierCoeff F S - c S) ^ 2 + ∑ S ∈ Tᶜ, fourierCoeff F S ^ 2 := by
  set c' : Finset ι → ℝ := fun S => if S ∈ T then c S else 0 with hc'
  have hg (x : ι → Bool) : ∑ S ∈ T, c S * chi ℝ S x = ∑ S, c' S * chi ℝ S x := by
    simp only [c', ite_mul, zero_mul, sum_ite_mem, univ_inter]
  simp only [hg]
  rw [expect_sq_eq_sum_fourierCoeff_sq, ← sum_add_sum_compl T]
  congr 1
  · refine sum_congr rfl fun S hS => ?_
    rw [fourierCoeff_sub, fourierCoeff_sum_mul_chi]
    simp [c', hS]
  · refine sum_congr rfl fun S hS => ?_
    rw [fourierCoeff_sub, fourierCoeff_sum_mul_chi]
    simp [c', mem_compl.1 hS]

/-- **Learning from approximate Fourier coefficients** [O'Donnell, Section 3.4][ODonnell2014]:
rounding the combination `∑_{S ∈ T} c_S χ_S` of characters to its sign misclassifies at most a
fraction `∑_{S ∈ T} (f̂(S) - c_S)² + ∑_{S ∉ T} f̂(S)²` of the points, where `f̂` are the Fourier
coefficients of `f` read as signs. -/
theorem hammingDist_signRound_sum_mul_chi_div_le (f : (ι → Bool) → Bool) (T : Finset (Finset ι))
    (c : Finset ι → ℝ) :
    (hammingDist (signRound fun x => ∑ S ∈ T, c S * chi ℝ S x) f : ℝ) / 2 ^ Fintype.card ι ≤
      ∑ S ∈ T, (fourierCoeff (fun x => signVal (f x)) S - c S) ^ 2 +
        ∑ S ∈ Tᶜ, fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
  rw [← expect_sq_sub_sum_mul_chi]
  exact hammingDist_signRound_div_le_expect_sq_sub f _

end Cslib.BitString
