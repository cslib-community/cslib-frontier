/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.CharacterProjection
import CslibFrontier.Foundations.BooleanAnalysis.LowDegreeGranularity
import Mathlib.Algebra.BigOperators.Field

/-!
# Fourier denominators under Boolean composition

Suppose every character of a vector of Boolean functions has Fourier coefficients in
`2 ^ (-a) ℤ`, and a Boolean function `φ` has coefficients in `2 ^ (-b) ℤ`. Adjoining `φ` of
selected coordinates gives coefficients in `2 ^ (-(a + b)) ℤ` for every character of the
extended vector. Coordinate selections may repeat: character projection cancels repetitions
modulo two, so the bound applies to shared circuit workspaces.

Affine Boolean functions have integral Fourier coefficients. Every Boolean function of at
most two bits has half-integral Fourier coefficients. These two cases charge only nonlinear
gates when the composition result is applied to fan-in-two circuits.

## Main results

* `Cslib.BitString.exists_fourierCoeff_signVal_eq_intCast_of_isAffine`: integral coefficients
  for affine Boolean functions.
* `Cslib.BitString.exists_fourierCoeff_chi_append_eq_intCast_div_two_pow`: the joint denominator
  bound after adjoining one Boolean coordinate.
-/

public section

open Finset
open scoped BigOperators symmDiff

namespace Cslib.BitString

variable {ι α κ : Type*} [Fintype ι] [DecidableEq ι]

/-- Every Fourier coefficient of an affine Boolean function, read as signs, is an integer. -/
theorem exists_fourierCoeff_signVal_eq_intCast_of_isAffine
    {f : (ι → Bool) → Bool} (hf : IsAffine f) (S : Finset ι) :
    ∃ z : ℤ, fourierCoeff (fun x => signVal (f x)) S = z := by
  classical
  obtain ⟨T, hT⟩ := exists_signVal_eq_mul_chi_of_isAffine hf
  refine ⟨if T = S then (-1 : ℤ) ^ (f 0).toNat else 0, ?_⟩
  rw [hT, fourierCoeff_const_mul, fourierCoeff_chi]
  by_cases h : T = S <;> simp [h, signVal_eq_neg_one_pow]

/-- Every Fourier coefficient of a Boolean function of at most two coordinates, read as
signs, is an integer divided by two. -/
theorem exists_fourierCoeff_signVal_eq_intCast_div_two_of_card_le_two
    (hι : Fintype.card ι ≤ 2) (f : (ι → Bool) → Bool) (S : Finset ι) :
    ∃ z : ℤ, fourierCoeff (fun x => signVal (f x)) S = z / 2 := by
  simpa using exists_fourierCoeff_signVal_eq_intCast_div_two_pow_of_mem_lowDegree f
    (lowDegree_mono hι (mem_lowDegree_self (fun x => signVal (f x)))) S

/-- Adjoining a Boolean function with coefficient denominators dividing `2 ^ b` to a vector
whose characters have coefficient denominators dividing `2 ^ a` gives a common denominator
`2 ^ (a + b)` for every character of the extended vector. Repeated arguments are allowed. -/
theorem exists_fourierCoeff_chi_append_eq_intCast_div_two_pow
    [Fintype α] [DecidableEq α] [Finite κ]
    (v : (ι → Bool) → κ → Bool) (φ : (α → Bool) → Bool) (args : α → κ) {a b : ℕ}
    (hv : ∀ T : Finset κ, ∀ U : Finset ι,
      ∃ z : ℤ, fourierCoeff (fun x => chi ℝ T (v x)) U = z / 2 ^ a)
    (hφ : ∀ T : Finset α, ∃ z : ℤ,
      fourierCoeff (fun x => signVal (φ x)) T = z / 2 ^ b)
    (S : Finset (Option κ)) (U : Finset ι) :
    ∃ z : ℤ, fourierCoeff
      (fun x => chi ℝ S (fun o => o.elim (φ (v x ∘ args)) (v x))) U = z / 2 ^ (a + b) := by
  classical
  let := Fintype.ofFinite κ
  by_cases hnone : none ∈ S
  · choose c hc using hφ
    choose d hd using fun T : Finset α => hv (symmDiff (projectSet args T) S.eraseNone) U
    have heq :
        (fun x => chi ℝ S (fun o => o.elim (φ (v x ∘ args)) (v x))) =
          fun x => ∑ T, fourierCoeff (fun y => signVal (φ y)) T *
            chi ℝ (symmDiff (projectSet args T) S.eraseNone) (v x) :=
      funext fun x => chi_append_eq_sum φ args S hnone (v x)
    refine ⟨∑ T, c T * d T, ?_⟩
    rw [heq, fourierCoeff_sum_mul, Int.cast_sum, sum_div]
    refine sum_congr rfl fun T _ => ?_
    rw [hc T, hd T, Int.cast_mul, pow_add, div_mul_div_comm, mul_comm (2 ^ b : ℝ)]
  · simp only [chi_option_elim, hnone, ite_false, one_mul]
    obtain ⟨z, hz⟩ := hv S.eraseNone U
    refine ⟨z * 2 ^ b, ?_⟩
    rw [hz, pow_add]
    push_cast
    field_simp

end Cslib.BitString
