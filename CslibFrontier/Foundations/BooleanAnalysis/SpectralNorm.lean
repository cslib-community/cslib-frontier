/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.CharacterProjection
import CslibFrontier.Foundations.BooleanAnalysis.FourierRestriction
import CslibFrontier.Foundations.Data.Finset.SymmDiff
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Fourier spectral bounds

Every affine Boolean function has Fourier spectral norm one, and every Boolean function on
at most two coordinates has spectral norm at most two.

Suppose every character of a vector of Boolean functions has Fourier spectral norm at most
`B`. Adjoining a Boolean function of selected coordinates multiplies this joint bound by at
most the spectral norm of the function being adjoined. The selection can repeat coordinates.

The joint hypothesis accounts for shared intermediate values in circuits: the Fourier
expansion of one new gate produces products of old characters, which
are again old characters. Thus a gate is charged once, however its predecessors are reused.

Multiplying a real function `f` by a character `χ_T` shifts its coefficients by `T ∆ ·`
(`BitString.fourierCoeff_chi_mul`), so expanding `f` in characters writes each coefficient of the
pointwise product `f g` as `∑ T, f̂ T * ĝ (T ∆ S)` (`BitString.fourierCoeff_mul`). Since
`S ↦ T ∆ S` permutes the sets, the spectral norm `‖f̂‖₁ = ∑ S, |f̂ S|` is submultiplicative,
`‖(f g)^‖₁ ≤ ‖f̂‖₁ ‖ĝ‖₁` (`BitString.sum_abs_fourierCoeff_mul_le`)
[O'Donnell, Exercise 3.6][ODonnell2014]; in particular `‖(f²)^‖₁ ≤ ‖f̂‖₁²`
(`BitString.sum_abs_fourierCoeff_sq_le_sq`). A character has spectral norm one
(`BitString.sum_abs_fourierCoeff_chi`), and multiplying by a character keeps the spectral norm
(`BitString.sum_abs_fourierCoeff_chi_mul`).

The coefficient on `S` of the restriction fixing the coordinates outside `J` to `z` sums the
coefficients `f̂(U)` with `U ∩ J = S`, each times `χ_{U \ J}(z)`
(`BitString.fourierCoeff_piecewise`). Hence the restriction has spectral norm at most `‖f̂‖₁`
(`BitString.sum_abs_fourierCoeff_piecewise_le`) [O'Donnell, Exercise 3.7(a)][ODonnell2014], and so
has the function `z ↦ f_{J|z}^(S)`, O'Donnell's `F_{S|J} f`
(`BitString.sum_abs_fourierCoeff_fourierCoeff_piecewise_le`), a consequence of
[O'Donnell, Proposition 3.21][ODonnell2014].

## Main results

* `Cslib.BitString.sum_abs_fourierCoeff_signVal_eq_one_of_isAffine`: affine Boolean functions
  have spectral norm one.
* `Cslib.BitString.sum_abs_fourierCoeff_signVal_le_two_of_card_le_two`: Boolean functions on
  at most two coordinates have spectral norm at most two.
* `Cslib.BitString.sum_abs_fourierCoeff_sum_mul_le`: the spectral triangle inequality for a
  finite linear combination.
* `Cslib.BitString.sum_abs_fourierCoeff_chi_append_le`: adjoining a Boolean coordinate
  preserves a joint spectral bound with the stated multiplicative cost.
* `Cslib.BitString.fourierCoeff_mul`: the Fourier coefficients of a pointwise product.
* `Cslib.BitString.sum_abs_fourierCoeff_mul_le`: the spectral norm is submultiplicative.
* `Cslib.BitString.sum_abs_fourierCoeff_sq_le_sq`: the spectral norm of a square.
* `Cslib.BitString.sum_abs_fourierCoeff_chi`: a character has spectral norm one.
* `Cslib.BitString.sum_abs_fourierCoeff_chi_mul`: multiplying by a character keeps the spectral
  norm.
* `Cslib.BitString.sum_abs_fourierCoeff_piecewise_le`,
  `Cslib.BitString.sum_abs_fourierCoeff_fourierCoeff_piecewise_le`: restrictions do not increase
  the spectral norm.

## Usage

Open `Cslib.BitString`. The statements on products, characters and restrictions are about the
spectral norm `∑ S, |fourierCoeff f S|` of a real `f : (ι → Bool) → ℝ`; a Boolean function enters
as `fun x => signVal (f x)`. For a product, `fourierCoeff_mul f g S` expands a coefficient of
`fun x => f x * g x`, and `sum_abs_fourierCoeff_mul_le f g` and `sum_abs_fourierCoeff_sq_le_sq f`
bound its spectral norm. A restriction is written `fun x => f (J.piecewise x z)`: the coordinates
in `J` stay free and the others are fixed to `z`. Small-bias distributions fool functions of small
spectral norm and their squares (`Cslib.BitString.IsSmallBias.fools`,
`Cslib.BitString.IsSmallBias.fools_sq` in `CslibFrontier.Probability.Fooling`), which is how the
derandomized BLR test and the deterministic Fourier estimates use these bounds. The checked
clients in
[CslibFrontierTests/BooleanAnalysisSpectralNorm.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisSpectralNorm.lean)
show that a character has spectral norm `1` and that `‖(χ_S²)^‖₁ ≤ ‖χ̂_S‖₁²` is attained. For
`χ_{0} + χ_{1}` on two bits, of spectral norm `2`, they bound by `2` the spectral norms of its
product with `χ_{0}`, of its restrictions and of the coefficient of a restriction as a function of
the fixed bits.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open Finset
open scoped BigOperators symmDiff

namespace Cslib.BitString

variable {ι α κ : Type*} [Fintype ι] [DecidableEq ι]

/-- A character has spectral norm one: `‖χ̂_T‖₁ = 1`. -/
theorem sum_abs_fourierCoeff_chi (T : Finset ι) : ∑ S, |fourierCoeff (chi ℝ T) S| = 1 := by
  simp only [fourierCoeff_chi, apply_ite abs, abs_one, abs_zero, sum_ite_eq, mem_univ, ite_true]

/-- An affine Boolean function has spectral norm one: its sign function is a character
multiplied by the sign of its constant term. -/
theorem sum_abs_fourierCoeff_signVal_eq_one_of_isAffine
    {f : (ι → Bool) → Bool} (hf : IsAffine f) :
    ∑ S, |fourierCoeff (fun x => signVal (f x)) S| = 1 := by
  obtain ⟨T, hsign⟩ := exists_signVal_eq_mul_chi_of_isAffine hf
  simp only [hsign, fourierCoeff_const_mul, abs_mul, abs_signVal, one_mul,
    sum_abs_fourierCoeff_chi]

/-- A Boolean function on at most two coordinates has spectral norm at most two, by
Cauchy–Schwarz and Parseval's identity. -/
theorem sum_abs_fourierCoeff_signVal_le_two_of_card_le_two (hι : Fintype.card ι ≤ 2)
    (f : (ι → Bool) → Bool) : ∑ S, |fourierCoeff (fun x => signVal (f x)) S| ≤ 2 := by
  have hcs := sum_mul_sq_le_sq_mul_sq (R := ℝ) (univ : Finset (Finset ι))
    (fun S => |fourierCoeff (fun x => signVal (f x)) S|) (fun _ => 1)
  have hsq : (∑ S, |fourierCoeff (fun x => signVal (f x)) S|) ^ 2 ≤
      (2 : ℝ) ^ Fintype.card ι := by
    simpa [sq_abs, sum_fourierCoeff_sq_signVal, Fintype.card_finset] using hcs
  have hpow : (2 : ℝ) ^ Fintype.card ι ≤ 4 := by
    calc (2 : ℝ) ^ Fintype.card ι ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hι
      _ = 4 := by norm_num
  nlinarith

/-- The spectral norm of a finite linear combination is at most the corresponding weighted
sum of spectral norms. -/
theorem sum_abs_fourierCoeff_sum_mul_le [Fintype α]
    (c : α → ℝ) (f : α → (ι → Bool) → ℝ) :
    ∑ S, |fourierCoeff (fun x => ∑ i, c i * f i x) S| ≤
      ∑ i, |c i| * ∑ S, |fourierCoeff (f i) S| := by
  simp only [fourierCoeff_sum_mul]
  calc
    ∑ S, |∑ i, c i * fourierCoeff (f i) S| ≤
        ∑ S, ∑ i, |c i| * |fourierCoeff (f i) S| := by
      exact sum_le_sum fun S _ => (abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_mul])
    _ = ∑ i, |c i| * ∑ S, |fourierCoeff (f i) S| := by
      rw [sum_comm]
      simp only [mul_sum]

/-- Adjoining a Boolean function of selected coordinates multiplies a uniform spectral
bound for all characters by at most the spectral norm of the adjoined function. The map
`args` may repeat coordinates. -/
theorem sum_abs_fourierCoeff_chi_append_le
    [Fintype α] [DecidableEq α] [Finite κ]
    (v : (ι → Bool) → κ → Bool) (φ : (α → Bool) → Bool) (args : α → κ) {B : ℝ}
    (hbound : ∀ T : Finset κ,
      ∑ U, |fourierCoeff (fun x => chi ℝ T (v x)) U| ≤ B)
    (S : Finset (Option κ)) :
    ∑ U, |fourierCoeff
      (fun x => chi ℝ S (fun o => o.elim (φ (v x ∘ args)) (v x))) U| ≤
      (∑ T, |fourierCoeff (fun y => signVal (φ y)) T|) * B := by
  classical
  let := Fintype.ofFinite κ
  have hB : 0 ≤ B := (sum_nonneg fun _ _ => abs_nonneg _).trans (hbound ∅)
  by_cases hnone : none ∈ S
  · have heq :
        (fun x => chi ℝ S (fun o => o.elim (φ (v x ∘ args)) (v x))) =
          fun x => ∑ T, fourierCoeff (fun y => signVal (φ y)) T *
            chi ℝ (symmDiff (projectSet args T) S.eraseNone) (v x) := by
      exact funext fun x => chi_append_eq_sum φ args S hnone (v x)
    rw [heq]
    refine (sum_abs_fourierCoeff_sum_mul_le _ _).trans ?_
    calc
      ∑ T, |fourierCoeff (fun y => signVal (φ y)) T| *
          ∑ U, |fourierCoeff
            (fun x => chi ℝ (symmDiff (projectSet args T) S.eraseNone) (v x)) U| ≤
          ∑ T, |fourierCoeff (fun y => signVal (φ y)) T| * B :=
        sum_le_sum fun T _ => mul_le_mul_of_nonneg_left (hbound _) (abs_nonneg _)
      _ = (∑ T, |fourierCoeff (fun y => signVal (φ y)) T|) * B := (sum_mul ..).symm
  · simp only [chi_option_elim, hnone, ite_false, one_mul]
    calc
      ∑ U, |fourierCoeff (fun x => chi ℝ S.eraseNone (v x)) U| ≤ B := hbound _
      _ = 1 * B := (one_mul B).symm
      _ ≤ (∑ T, |fourierCoeff (fun y => signVal (φ y)) T|) * B :=
        mul_le_mul_of_nonneg_right (one_le_sum_abs_fourierCoeff_signVal φ) hB

/-! ### Products, characters and restrictions -/

/-- The Fourier coefficients of a pointwise product: `(f g)^(S) = ∑_T f̂(T) ĝ(T ∆ S)`. -/
theorem fourierCoeff_mul (f g : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (fun x => f x * g x) S =
      ∑ T, fourierCoeff f T * fourierCoeff g (symmDiff T S) := by
  have h : (fun x => f x * g x) = fun x => ∑ T, fourierCoeff f T * (chi ℝ T x * g x) := by
    funext x
    conv_lhs => rw [← sum_fourierCoeff_mul_chi f x]
    rw [sum_mul]
    exact sum_congr rfl fun T _ => mul_assoc _ _ _
  rw [h, fourierCoeff_sum_mul]
  simp only [fourierCoeff_chi_mul]

/-- **The spectral norm is submultiplicative**: `‖(f g)^‖₁ ≤ ‖f̂‖₁ ‖ĝ‖₁`
[O'Donnell, Exercise 3.6][ODonnell2014]. -/
theorem sum_abs_fourierCoeff_mul_le (f g : (ι → Bool) → ℝ) :
    ∑ S, |fourierCoeff (fun x => f x * g x) S| ≤
      (∑ S, |fourierCoeff f S|) * ∑ S, |fourierCoeff g S| := by
  calc ∑ S, |fourierCoeff (fun x => f x * g x) S|
      ≤ ∑ S, ∑ T, |fourierCoeff f T| * |fourierCoeff g (symmDiff T S)| :=
        sum_le_sum fun S _ => by
          rw [fourierCoeff_mul]
          exact (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun T _ => abs_mul _ _)
    _ = (∑ S, |fourierCoeff f S|) * ∑ S, |fourierCoeff g S| := by
        rw [sum_comm, sum_mul]
        refine sum_congr rfl fun T _ => ?_
        rw [← mul_sum, Fintype.sum_symmDiff T fun S => |fourierCoeff g S|]

/-- **The spectral norm of a square**: `‖(f²)^‖₁ ≤ ‖f̂‖₁²`, the case `g = f` of
[O'Donnell, Exercise 3.6][ODonnell2014]. -/
theorem sum_abs_fourierCoeff_sq_le_sq (f : (ι → Bool) → ℝ) :
    ∑ S, |fourierCoeff (fun x => f x ^ 2) S| ≤ (∑ S, |fourierCoeff f S|) ^ 2 := by
  simpa only [sq] using sum_abs_fourierCoeff_mul_le f f

/-- **Multiplying by a character keeps the spectral norm**: `‖(χ_U f)^‖₁ = ‖f̂‖₁`, since the
coefficients of `χ_U f` are those of `f` shifted by `U ∆ ·`. -/
theorem sum_abs_fourierCoeff_chi_mul (U : Finset ι) (f : (ι → Bool) → ℝ) :
    ∑ S, |fourierCoeff (fun x => chi ℝ U x * f x) S| = ∑ S, |fourierCoeff f S| := by
  simp only [fourierCoeff_chi_mul]
  exact Fintype.sum_symmDiff U fun S => |fourierCoeff f S|

/-- **Restrictions do not increase the spectral norm**: fixing the coordinates outside `J` to `z`
gives a function of spectral norm at most `‖f̂‖₁` [O'Donnell, Exercise 3.7(a)][ODonnell2014]. -/
theorem sum_abs_fourierCoeff_piecewise_le (f : (ι → Bool) → ℝ) (J : Finset ι) (z : ι → Bool) :
    ∑ S, |fourierCoeff (fun x => f (J.piecewise x z)) S| ≤ ∑ U, |fourierCoeff f U| := by
  simp only [fourierCoeff_piecewise]
  calc ∑ S, |∑ U with U ∩ J = S, fourierCoeff f U * chi ℝ (U \ J) z|
      ≤ ∑ S, ∑ U with U ∩ J = S, |fourierCoeff f U| :=
        sum_le_sum fun S _ => (abs_sum_le_sum_abs _ _).trans_eq
          (sum_congr rfl fun U _ => by rw [abs_mul, abs_chi, mul_one])
    _ = ∑ U, |fourierCoeff f U| := sum_fiberwise _ _ _

/-- **The coefficient of a restriction, as a function of the fixed bits, has small spectral
norm**: the coefficient on `S` of the restriction fixing the coordinates outside `J` to `z`, as a
function of `z` (O'Donnell's `F_{S|J} f`), has spectral norm at most `‖f̂‖₁`, a consequence of
[O'Donnell, Proposition 3.21][ODonnell2014]. -/
theorem sum_abs_fourierCoeff_fourierCoeff_piecewise_le (f : (ι → Bool) → ℝ) (J S : Finset ι) :
    ∑ V, |fourierCoeff (fun z => fourierCoeff (fun x => f (J.piecewise x z)) S) V| ≤
      ∑ U, |fourierCoeff f U| := by
  have h : (fun z => fourierCoeff (fun x => f (J.piecewise x z)) S) = fun z =>
      ∑ U, (if U ∩ J = S then fourierCoeff f U else 0) * chi ℝ (U \ J) z := by
    funext z
    simp only [fourierCoeff_piecewise, sum_filter, ite_mul, zero_mul]
  rw [h]
  refine (sum_abs_fourierCoeff_sum_mul_le _ _).trans (sum_le_sum fun U _ => ?_)
  rw [sum_abs_fourierCoeff_chi, mul_one]
  split_ifs <;> simp

end Cslib.BitString
