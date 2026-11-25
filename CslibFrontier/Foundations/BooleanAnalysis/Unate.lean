/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Monotone
public import CslibFrontier.Foundations.BooleanAnalysis.PolynomialThreshold
import CslibFrontier.Foundations.BooleanAnalysis.FourierDegree

/-!
# Linear threshold functions are unate

A Boolean function is *unate* (`BitString.IsUnate`, in
`CslibFrontier.Foundations.BooleanAnalysis.Monotone`) if in every direction `i`, raising bit `i`
either never lowers its value or never raises it [O'Donnell, Exercise 2.5][ODonnell2014]. Every
linear threshold function is unate (`BitString.IsPTF.isUnate`)
[O'Donnell, Exercise 2.6][ODonnell2014]: if `F = (-1) ^ f` is the sign of `p` of degree at most
one, the derivative of `p` in `i` is the constant `p̂({i})`, so flipping bit `i` moves `p`, and
with it its sign `F`, always in the same direction. Unate functions on `n` coordinates have total
influence at most `√n` (`BitString.IsUnate.totalInfluence_le_sqrt_card`)
[O'Donnell, Exercise 2.23][ODonnell2014], so linear threshold functions do too
(`BitString.IsPTF.totalInfluence_le_sqrt_card`); this is the input to Peres's theorem in
`CslibFrontier.Foundations.BooleanAnalysis.Peres`.

## Main results

* `Cslib.BitString.IsPTF.isUnate`: linear threshold functions are unate.
* `Cslib.BitString.IsPTF.totalInfluence_le_sqrt_card`: linear threshold functions have total
  influence at most `√n`.

## Usage

Open `Cslib.BitString`. A linear threshold function is `IsPTF 1 f`; `IsUnateIn i f`, `IsUnate f`,
the characterization `Cslib.BitString.abs_fourierCoeff_singleton_eq_influence_iff`
(Exercise 2.5(a)) and the unate bounds `Cslib.BitString.IsUnate.totalInfluence_le_sqrt_card_mul`
and `Cslib.BitString.IsUnate.totalInfluence_le_sqrt_card` (Exercise 2.23) are in
`CslibFrontier.Foundations.BooleanAnalysis.Monotone`. Exercise 2.5(b), the bound
`I[f] ≤ √(2/π) √n + O(n^(-1/2))` for unate `f` through Theorem 2.33, which would improve the
constant of Peres's theorem to `√(2/π)`, is not proved; tracked on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131).

The checked clients in
[CslibFrontierTests/BooleanAnalysisPeres.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisPeres.lean)
show that `¬x₀ ∧ x₁` is a linear threshold function that is unate but neither monotone nor
antitone, check that the majority of three bits is unate with `I ≤ √3`, and show that the parity
of two bits is not unate, hence not a linear threshold function.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Function

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- **Linear threshold functions are unate** [O'Donnell, Exercise 2.6][ODonnell2014]: if `f`, read
as signs, is the sign of `p` of degree at most one, flipping bit `i` from `false` to `true` changes
`p` by the constant `-2 p̂({i})`, so it moves the sign of `p` always in the same direction. -/
theorem IsPTF.isUnate {f : (ι → Bool) → Bool} (hf : IsPTF 1 f) : IsUnate f := by
  obtain ⟨p, hpdeg, hp⟩ := isPTF_iff.1 hf
  intro i
  have hd (x : ι → Bool) : p (update x i false) - p (update x i true) = 2 * fourierCoeff p {i} := by
    have := derivative_eq_fourierCoeff_singleton_of_fourierCoeff_eq_zero p hpdeg i x
    rw [derivative] at this
    linarith
  -- The sign of `f` at a point is determined by the sign of `p` there.
  have hsign (y : ι → Bool) : f y = decide (p y < 0) := by
    have := hp y
    cases h : f y <;> simp only [h, signVal_false, signVal_true, one_mul, neg_mul,
      Left.neg_pos_iff] at this ⊢ <;> simp [this, this.le, not_lt.2]
  rcases le_total 0 (fourierCoeff p {i}) with hi | hi
  · refine Or.inl fun x => ?_
    rw [hsign, hsign]
    have := hd x
    by_cases h : p (update x i false) < 0
    · have h' : p (update x i true) < 0 := by linarith
      simp only [h, h', decide_true, le_refl]
    · simp only [h, decide_false, Bool.false_le]
  · refine Or.inr fun x => ?_
    rw [hsign, hsign]
    have := hd x
    by_cases h : p (update x i true) < 0
    · have h' : p (update x i false) < 0 := by linarith
      simp only [h, h', decide_true, le_refl]
    · simp only [h, decide_false, Bool.false_le]

/-- **Linear threshold functions have total influence at most `√n`**: a linear threshold function
on `n` coordinates, read as signs, has total influence at most `√n`
[O'Donnell, Exercises 2.6 and 2.23][ODonnell2014]. -/
theorem IsPTF.totalInfluence_le_sqrt_card {f : (ι → Bool) → Bool} (hf : IsPTF 1 f) :
    totalInfluence (fun x => signVal (f x)) ≤ √(Fintype.card ι) :=
  hf.isUnate.totalInfluence_le_sqrt_card

end Cslib.BitString
