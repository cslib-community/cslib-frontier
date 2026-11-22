/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Foundations.Analysis.LpNorm
import CslibFrontier.Foundations.BooleanAnalysis.LinearityRejection
import CslibFrontier.Foundations.BooleanAnalysis.UncertaintyPrinciple

/-! # The uncertainty principle

The character `χ_{0}` on two bits is nonzero at all four inputs and has the single nonzero
coefficient `χ̂_{0}({0}) = 1`: the uncertainty principle applies to it, and it attains the bound
`1 · 1 = 1` with equality (`4 · 1 = 2 ^ 2` in counts). The function `1 - [x = 0]` is nonzero at
three of the four inputs and has all four coefficients nonzero, so it satisfies the bound strictly,
`3/4 · 4 = 3`. The zero function shows that the hypothesis `f ≠ 0` cannot be dropped. The two
halves of O'Donnell's Exercise 3.9 are checked on `χ_{0}`, where both are attained, and the bound
behind the second on a combination of two characters, where it is attained too.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.BooleanAnalysisUncertaintyPrinciple

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- `χ_{0}` on two bits is nonzero everywhere. -/
private theorem filter_chi_zero_ne_zero :
    ({x | chi ℝ {(0 : Fin 2)} x ≠ 0} : Finset (Fin 2 → Bool)) = univ :=
  filter_true_of_mem fun x _ => by rw [← abs_pos, abs_chi]; exact one_pos

/-- `χ_{0}` on two bits has the single nonzero coefficient `χ̂_{0}({0}) = 1`. -/
private theorem card_fourierCoeff_chi_zero_ne_zero :
    #{S : Finset (Fin 2) | fourierCoeff (chi ℝ {(0 : Fin 2)}) S ≠ 0} = 1 := by
  simp only [fourierCoeff_chi, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
  exact card_eq_one.2 ⟨{0}, by ext S; simp [eq_comm]⟩

/-- `χ_{0}` is not the zero function. -/
private theorem chi_zero_ne_zero : chi ℝ {(0 : Fin 2)} ≠ 0 := fun h => by
  simpa using congrFun h 0

/-- The uncertainty principle for `χ_{0}` on two bits, in both forms, and attained:
`dens · count = 1 · 1 = 1` and `4 · 1 = 2 ^ 2`. -/
example :
    1 ≤ (dens {x : Fin 2 → Bool | chi ℝ {(0 : Fin 2)} x ≠ 0} : ℝ) *
        #{S : Finset (Fin 2) | fourierCoeff (chi ℝ {(0 : Fin 2)}) S ≠ 0} ∧
      (dens {x : Fin 2 → Bool | chi ℝ {(0 : Fin 2)} x ≠ 0} : ℝ) *
        #{S : Finset (Fin 2) | fourierCoeff (chi ℝ {(0 : Fin 2)}) S ≠ 0} = 1 ∧
      2 ^ Fintype.card (Fin 2) ≤
        #{x : Fin 2 → Bool | chi ℝ {(0 : Fin 2)} x ≠ 0} *
          #{S : Finset (Fin 2) | fourierCoeff (chi ℝ {(0 : Fin 2)}) S ≠ 0} ∧
      #{x : Fin 2 → Bool | chi ℝ {(0 : Fin 2)} x ≠ 0} *
          #{S : Finset (Fin 2) | fourierCoeff (chi ℝ {(0 : Fin 2)}) S ≠ 0} =
        2 ^ Fintype.card (Fin 2) := by
  refine ⟨one_le_dens_mul_card_fourierCoeff_ne_zero chi_zero_ne_zero, ?_,
    two_pow_card_le_card_mul_card_fourierCoeff_ne_zero chi_zero_ne_zero, ?_⟩ <;>
  · rw [filter_chi_zero_ne_zero, card_fourierCoeff_chi_zero_ne_zero]
    simp

/-- The function `1 - [x = 0]` on two bits, nonzero at three of the four inputs, with
coefficients `3/4` on `∅` and `-1/4` elsewhere: the uncertainty principle holds strictly,
`dens · count = 3/4 · 4 = 3`. -/
example :
    1 ≤ (dens {x : Fin 2 → Bool | (1 - if x = 0 then 1 else 0 : ℝ) ≠ 0} : ℝ) *
        #{S : Finset (Fin 2) |
          fourierCoeff (fun x : Fin 2 → Bool => 1 - if x = 0 then (1 : ℝ) else 0) S ≠ 0} ∧
      (dens {x : Fin 2 → Bool | (1 - if x = 0 then 1 else 0 : ℝ) ≠ 0} : ℝ) *
        #{S : Finset (Fin 2) |
          fourierCoeff (fun x : Fin 2 → Bool => 1 - if x = 0 then (1 : ℝ) else 0) S ≠ 0} = 3 := by
  have hcoeff (S : Finset (Fin 2)) :
      fourierCoeff (fun x : Fin 2 → Bool => 1 - if x = 0 then (1 : ℝ) else 0) S =
        (if S = ∅ then 1 else 0) - 1 / 4 := by
    rw [fourierCoeff_sub (fun _ => (1 : ℝ)) (fun x => if x = 0 then (1 : ℝ) else 0) S,
      fourierCoeff_const, fourierCoeff_ite_eq, chi_zero, Fintype.card_fin]
    norm_num
  have hF : #{S : Finset (Fin 2) |
      fourierCoeff (fun x : Fin 2 → Bool => 1 - if x = 0 then (1 : ℝ) else 0) S ≠ 0} = 4 := by
    rw [filter_true_of_mem fun S _ => by rw [hcoeff]; split_ifs <;> norm_num, card_univ]
    simp
  have hG : ({x | (1 - if x = 0 then 1 else 0 : ℝ) ≠ 0} : Finset (Fin 2 → Bool)) =
      univ.erase 0 := by
    ext x
    by_cases hx : x = 0 <;> simp [hx]
  have h1 : (fun _ : Fin 2 => true) ≠ 0 := by decide
  refine ⟨one_le_dens_mul_card_fourierCoeff_ne_zero fun h => ?_, ?_⟩
  · have := congrFun h fun _ => true
    simp [h1] at this
  · rw [hF, hG, nnratCast_dens, card_erase_of_mem (mem_univ _), card_univ]
    simp

/-- The hypothesis `f ≠ 0` is needed: for the zero function both supports are empty, so neither
form of the bound holds. -/
example :
    ¬ 1 ≤ (dens {x : Fin 2 → Bool | (fun _ => (0 : ℝ)) x ≠ 0} : ℝ) *
        #{S : Finset (Fin 2) | fourierCoeff (fun _ : Fin 2 → Bool => (0 : ℝ)) S ≠ 0} ∧
      ¬ 2 ^ Fintype.card (Fin 2) ≤
        #{x : Fin 2 → Bool | (fun _ => (0 : ℝ)) x ≠ 0} *
          #{S : Finset (Fin 2) | fourierCoeff (fun _ : Fin 2 → Bool => (0 : ℝ)) S ≠ 0} := by
  simp [fourierCoeff_const]

/-- `‖f̂‖∞ ≤ ‖f‖₁` for `χ_{0}` on two bits: every coefficient is at most `lpNorm 1 χ_{0} = 1`,
and the coefficient at `{0}` attains it. -/
example :
    (∀ S, |fourierCoeff (chi ℝ {(0 : Fin 2)}) S| ≤ lpNorm 1 (chi ℝ {(0 : Fin 2)})) ∧
      lpNorm 1 (chi ℝ {(0 : Fin 2)}) = 1 ∧ |fourierCoeff (chi ℝ {(0 : Fin 2)}) {0}| = 1 := by
  have hL : lpNorm 1 (chi ℝ {(0 : Fin 2)}) = 1 := by
    simp only [lpNorm_one, abs_chi, expect_const univ_nonempty]
  refine ⟨fun S => ?_, hL, by simp [fourierCoeff_chi]⟩
  rw [lpNorm_one]
  exact abs_fourierCoeff_le_expect_abs _ S

/-- `‖f‖∞ ≤ ‖f̂‖₁` for `χ_{0}` on two bits: the spectral 1-norm of `χ_{0}` is `1`, so its values
are at most `1` in absolute value, and every input attains it. -/
example :
    ∑ S, |fourierCoeff (chi ℝ {(0 : Fin 2)}) S| = 1 ∧
      (∀ x, |chi ℝ {(0 : Fin 2)} x| ≤ 1) ∧ ∀ x, |chi ℝ {(0 : Fin 2)} x| = 1 := by
  have hsum : ∑ S, |fourierCoeff (chi ℝ {(0 : Fin 2)}) S| = 1 := by
    simp only [fourierCoeff_chi, apply_ite, abs_one, abs_zero, sum_ite_eq, mem_univ, ite_true]
  exact ⟨hsum, fun x => hsum ▸ abs_le_sum_abs_fourierCoeff _ x, fun x => abs_chi _ x⟩

/-- A combination of characters is at most the sum of its absolute weights: on two bits,
`|2 χ_{0} - 3 χ_{1}| ≤ 5` at every input, with equality where the two bits differ. -/
example :
    (∀ x : Fin 2 → Bool, |∑ S ∈ ({{0}, {1}} : Finset (Finset (Fin 2))),
        (if S = {0} then (2 : ℝ) else -3) * chi ℝ S x| ≤ 5) ∧
      |∑ S ∈ ({{0}, {1}} : Finset (Finset (Fin 2))),
        (if S = {0} then (2 : ℝ) else -3) * chi ℝ S ![false, true]| = 5 := by
  refine ⟨fun x => (abs_sum_mul_chi_le _ _ x).trans_eq ?_, ?_⟩ <;>
  · rw [sum_pair (by decide)]
    norm_num [chi_singleton]

end CslibFrontierTests.BooleanAnalysisUncertaintyPrinciple
