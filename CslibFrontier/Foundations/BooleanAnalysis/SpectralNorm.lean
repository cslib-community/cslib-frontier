/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.CharacterProjection
public import CslibFrontier.Foundations.Data.BitString.Affine
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Fourier spectral bounds for Boolean functions

Every affine Boolean function has Fourier spectral norm one, and every Boolean function on
at most two coordinates has spectral norm at most two.

Suppose every character of a vector of Boolean functions has Fourier spectral norm at most
`B`. Adjoining a Boolean function of selected coordinates multiplies this joint bound by at
most the spectral norm of the function being adjoined. The selection can repeat coordinates.

The joint hypothesis accounts for shared intermediate values in circuits: the Fourier
expansion of one new gate produces products of old characters, which
are again old characters. Thus a gate is charged once, however its predecessors are reused.

## Main results

* `Cslib.BitString.sum_abs_fourierCoeff_signVal_eq_one_of_isAffine`: affine Boolean functions
  have spectral norm one.
* `Cslib.BitString.sum_abs_fourierCoeff_signVal_le_two_of_card_le_two`: Boolean functions on
  at most two coordinates have spectral norm at most two.
* `Cslib.BitString.sum_abs_fourierCoeff_sum_mul_le`: the spectral triangle inequality for a
  finite linear combination.
* `Cslib.BitString.sum_abs_fourierCoeff_chi_append_le`: adjoining a Boolean coordinate
  preserves a joint spectral bound with the stated multiplicative cost.
-/

public section

open Finset
open scoped BigOperators symmDiff

namespace Cslib.BitString

variable {ι α κ : Type*} [Fintype ι] [DecidableEq ι]

/-- An affine Boolean function has spectral norm one: its sign function is a character
multiplied by the sign of its constant term. -/
theorem sum_abs_fourierCoeff_signVal_eq_one_of_isAffine
    {f : (ι → Bool) → Bool} (hf : IsAffine f) :
    ∑ S, |fourierCoeff (fun x => signVal (f x)) S| = 1 := by
  obtain ⟨T, -, hT⟩ := exists_affine_of_add_add
    (M := (univ : Finset ι)) (fun x y h => congrArg f (funext fun i => h i (mem_univ i))) hf
  have hsign : (fun x => signVal (f x)) = fun x => signVal (f 0) * chi ℝ T x := by
    funext x
    rw [hT x, Bool.add_eq_xor, signVal_xor, chi_eq_signVal_parityOn]
    congr 2
    exact (parityOn_eq_sum T x).symm
  simp [hsign, fourierCoeff_const_mul, fourierCoeff_chi, apply_ite abs]

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
  have hcoeff (S : Finset ι) :
      fourierCoeff (fun x => ∑ i, c i * f i x) S =
        ∑ i, c i * fourierCoeff (f i) S := by
    simp only [fourierCoeff, sum_mul, mul_assoc]
    rw [expect_sum_comm]
    simp only [← mul_expect]
  simp only [hcoeff]
  calc
    ∑ S, |∑ i, c i * fourierCoeff (f i) S| ≤
        ∑ S, ∑ i, |c i| * |fourierCoeff (f i) S| := by
      exact sum_le_sum fun S _ => (abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_mul])
    _ = ∑ i, |c i| * ∑ S, |fourierCoeff (f i) S| := by
      rw [sum_comm]
      simp only [mul_sum]

private theorem chi_option_elim [Finite κ] [DecidableEq κ]
    (S : Finset (Option κ)) (b : Bool) (y : κ → Bool) :
    chi ℝ S (fun o => o.elim b y) =
      (if none ∈ S then signVal b else 1) * chi ℝ S.eraseNone y := by
  let := Fintype.ofFinite κ
  simp only [chi_eq_prod_univ, Fintype.prod_option, Option.elim_none, Option.elim_some,
    mem_eraseNone, signVal_eq_neg_one_pow]

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
      funext x
      rw [chi_option_elim, ite_eq_left hnone,
        ← sum_fourierCoeff_mul_chi (fun y => signVal (φ y)) (v x ∘ args), sum_mul]
      apply sum_congr rfl
      intro T _
      rw [mul_assoc, chi_comp_eq_chi_projectSet, chi_mul_chi]
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

end Cslib.BitString
