/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.Analysis.LpNorm
public import CslibFrontier.Foundations.BooleanAnalysis.UncertaintyPrinciple
import CslibFrontier.Foundations.BooleanAnalysis.LinearityRejection

/-! # The uncertainty principle

The character `χ_{0}` on two bits is nonzero at all four inputs and has the single nonzero
coefficient `χ̂_{0}({0}) = 1`: the uncertainty principle applies to it, and it attains the bound
`1 · 1 = 1` with equality (`4 · 1 = 2 ^ 2` in counts). The function `1 - [x = 0]` is nonzero at
three of the four inputs and has all four coefficients nonzero, so it satisfies the bound strictly,
`3/4 · 4 = 3`. The zero function shows that the hypothesis `f ≠ 0` cannot be dropped. The two
halves of O'Donnell's Exercise 3.9 are checked on `χ_{0}`, where both are attained, and the bound
behind the second on a combination of two characters, where it is attained too.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisUncertaintyPrinciple

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- The uncertainty principle for `χ_{0}` on two bits, attained: `dens · count = 1 · 1 = 1`. -/
theorem one_le_dens_mul_card_chi_zero :
    1 ≤ (dens {x : Fin 2 → Bool | chi ℝ {(0 : Fin 2)} x ≠ 0} : ℝ) *
        #{S : Finset (Fin 2) | fourierCoeff (chi ℝ {(0 : Fin 2)}) S ≠ 0} ∧
      (dens {x : Fin 2 → Bool | chi ℝ {(0 : Fin 2)} x ≠ 0} : ℝ) *
        #{S : Finset (Fin 2) | fourierCoeff (chi ℝ {(0 : Fin 2)}) S ≠ 0} = 1 := by
  refine ⟨one_le_dens_mul_card_fourierCoeff_ne_zero fun h => ?_, ?_⟩
  · have := congrFun h 0
    simp at this
  · rw [filter_true_of_mem fun x _ => by rw [← abs_pos, abs_chi]; exact one_pos, dens_univ]
    simp only [fourierCoeff_chi, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
    rw [card_eq_one.2 ⟨{0}, by ext S; simp [eq_comm]⟩]
    norm_num

/-- The uncertainty principle for `χ_{0}` on two bits, counting form. -/
theorem uncertainty_chi_zero :
    2 ^ Fintype.card (Fin 2) ≤
      #{x : Fin 2 → Bool | chi ℝ {0} x ≠ 0} *
        #{S : Finset (Fin 2) | fourierCoeff (chi ℝ {(0 : Fin 2)}) S ≠ 0} := by
  refine two_pow_card_le_card_mul_card_fourierCoeff_ne_zero fun h => ?_
  have := congrFun h 0
  simp at this

/-- The function `1 - [x = 0]` on two bits, nonzero at three of the four inputs, with
coefficients `3/4` on `∅` and `-1/4` elsewhere: the uncertainty principle holds strictly,
`dens · count = 3/4 · 4 = 3`. -/
theorem one_le_dens_mul_card_one_sub_indicator :
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
  have heq : (dens {x : Fin 2 → Bool | (1 - if x = 0 then 1 else 0 : ℝ) ≠ 0} : ℝ) *
      #{S : Finset (Fin 2) |
        fourierCoeff (fun x : Fin 2 → Bool => 1 - if x = 0 then (1 : ℝ) else 0) S ≠ 0} = 3 := by
    rw [hF, hG, nnratCast_dens, card_erase_of_mem (mem_univ _), card_univ]
    simp
  have h1 : (fun _ : Fin 2 => true) ≠ 0 := by decide
  refine ⟨one_le_dens_mul_card_fourierCoeff_ne_zero fun h => ?_, heq⟩
  have := congrFun h fun _ => true
  simp [h1] at this

/-- `χ_{0}` on two bits attains the uncertainty principle: `4 · 1 = 2 ^ 2`. -/
theorem card_mul_card_chi_zero :
    #{x : Fin 2 → Bool | chi ℝ {(0 : Fin 2)} x ≠ 0} *
      #{S : Finset (Fin 2) | fourierCoeff (chi ℝ {(0 : Fin 2)}) S ≠ 0} =
        2 ^ Fintype.card (Fin 2) := by
  have h1 : #{x : Fin 2 → Bool | chi ℝ {(0 : Fin 2)} x ≠ 0} = 4 := by
    rw [filter_true_of_mem fun x _ => by rw [← abs_pos, abs_chi]; exact one_pos, card_univ]
    simp
  have h2 : #{S : Finset (Fin 2) | fourierCoeff (chi ℝ {(0 : Fin 2)}) S ≠ 0} = 1 := by
    simp only [fourierCoeff_chi, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
    rw [card_eq_one]
    exact ⟨{0}, by ext S; simp [eq_comm]⟩
  rw [h1, h2, Fintype.card_fin]
  norm_num

/-- The hypothesis `f ≠ 0` is needed: for the zero function both counts vanish. -/
theorem not_uncertainty_zero :
    ¬ 2 ^ Fintype.card (Fin 2) ≤
      #{x : Fin 2 → Bool | (fun _ => (0 : ℝ)) x ≠ 0} *
        #{S : Finset (Fin 2) | fourierCoeff (fun _ : Fin 2 → Bool => (0 : ℝ)) S ≠ 0} := by
  simp [fourierCoeff_const]

/-- `‖f̂‖∞ ≤ ‖f‖₁` for `χ_{0}` on two bits: every coefficient is at most `lpNorm 1 χ_{0} = 1`,
and the coefficient at `{0}` attains it. -/
theorem abs_fourierCoeff_chi_zero_le_lpNorm_one :
    (∀ S, |fourierCoeff (chi ℝ {(0 : Fin 2)}) S| ≤ lpNorm 1 (chi ℝ {(0 : Fin 2)})) ∧
      lpNorm 1 (chi ℝ {(0 : Fin 2)}) = 1 ∧ |fourierCoeff (chi ℝ {(0 : Fin 2)}) {0}| = 1 := by
  have hL : lpNorm 1 (chi ℝ {(0 : Fin 2)}) = 1 := by
    simp only [lpNorm_one, abs_chi, expect_const univ_nonempty]
  refine ⟨fun S => ?_, hL, by simp [fourierCoeff_chi]⟩
  rw [lpNorm_one]
  exact abs_fourierCoeff_le_expect_abs _ S

/-- `‖f‖∞ ≤ ‖f̂‖₁` for `χ_{0}` on two bits: the spectral 1-norm of `χ_{0}` is `1`, so its values
are at most `1` in absolute value, and every input attains it. -/
theorem abs_chi_zero_le_sum_abs_fourierCoeff :
    ∑ S, |fourierCoeff (chi ℝ {(0 : Fin 2)}) S| = 1 ∧
      (∀ x, |chi ℝ {(0 : Fin 2)} x| ≤ 1) ∧ ∀ x, |chi ℝ {(0 : Fin 2)} x| = 1 := by
  have hsum : ∑ S, |fourierCoeff (chi ℝ {(0 : Fin 2)}) S| = 1 := by
    simp only [fourierCoeff_chi, apply_ite, abs_one, abs_zero, sum_ite_eq, mem_univ, ite_true]
  exact ⟨hsum, fun x => hsum ▸ abs_le_sum_abs_fourierCoeff _ x, fun x => abs_chi _ x⟩

/-- A combination of characters is at most the sum of its absolute weights: on two bits,
`|2 χ_{0} - 3 χ_{1}| ≤ 5` at every input, with equality where the two bits differ. -/
theorem abs_two_chi_sub_three_chi_le :
    (∀ x : Fin 2 → Bool, |∑ S ∈ ({{0}, {1}} : Finset (Finset (Fin 2))),
        (if S = {0} then (2 : ℝ) else -3) * chi ℝ S x| ≤ 5) ∧
      |∑ S ∈ ({{0}, {1}} : Finset (Finset (Fin 2))),
        (if S = {0} then (2 : ℝ) else -3) * chi ℝ S ![false, true]| = 5 := by
  refine ⟨fun x => (abs_sum_mul_chi_le _ _ x).trans_eq ?_, ?_⟩ <;>
  · rw [sum_pair (by decide)]
    norm_num [chi_singleton]

end CslibFrontierTests.BooleanAnalysisUncertaintyPrinciple
