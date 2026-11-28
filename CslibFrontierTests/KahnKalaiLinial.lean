/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.KahnKalaiLinial
public import CslibFrontier.Foundations.BooleanAnalysis.Tribes
import CslibFrontier.Foundations.BooleanAnalysis.TribesInfluence

/-! # Tests for the KKL Edge-Isoperimetric Theorem and the Kahn–Kalai–Linial theorem

The convexity step is applied to `χ_{0} + χ_{0,1}` on two bits, whose Fourier weight is split
between two levels. For a dictator, `Var = I = 1`, and the KKL Edge-Isoperimetric Theorem gives
`(9 / 1) 9^{-1} = 1`, the maximum possible influence. The Kahn–Kalai–Linial theorem is applied to
the nearly balanced Tribes function, whose variance is at least `3 / 4`. -/

set_option linter.privateModule false

public section

namespace CslibFrontierTests.KahnKalaiLinial

open Cslib BitString Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A dictator `x ↦ x i`, read as signs, is the character `χ_{i}`. -/
private theorem signVal_dictator_eq_chi (i : ι) :
    (fun x : ι → Bool => signVal (x i)) = chi ℝ {i} :=
  funext fun x => (chi_singleton i x).symm

/-- A dictator has variance `1`: its Fourier weight is all on `{i}`. -/
private theorem variance_dictator (i : ι) :
    𝔼 x : ι → Bool, (signVal (x i) - 𝔼 y : ι → Bool, signVal (y i)) ^ 2 = 1 := by
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq, signVal_dictator_eq_chi, sum_filter,
    sum_eq_single {i} (fun S _ hS => by simp [fourierCoeff_chi, Ne.symm hS]) (by simp)]
  simp [fourierCoeff_chi]

/-- A dictator has total influence `1`. -/
private theorem totalInfluence_dictator (i : ι) :
    totalInfluence (fun x : ι → Bool => signVal (x i)) = 1 := by
  rw [signVal_dictator_eq_chi, totalInfluence_chi, card_singleton, Nat.cast_one]

/-- The real function `χ_{0} + χ_{0,1}` on two bits. -/
private abbrev twoLevels : (Fin 2 → Bool) → ℝ := fun x => chi ℝ {0} x + chi ℝ {0, 1} x

/-- The Fourier weight of `χ_{0} + χ_{0,1}` is `1` on each of `{0}` and `{0, 1}`, and `0`
elsewhere. -/
private theorem sum_mul_fourierCoeff_twoLevels_sq {s : Finset (Finset (Fin 2))} (h0 : {0} ∈ s)
    (h01 : {0, 1} ∈ s) (g : Finset (Fin 2) → ℝ) :
    ∑ S ∈ s, g S * fourierCoeff twoLevels S ^ 2 = g {0} + g {0, 1} := by
  have h : ({0} : Finset (Fin 2)) ≠ {0, 1} := by decide
  rw [sum_eq_add {0} {0, 1} h (fun S _ hS => ?_) (by simp [h0]) (by simp [h01])]
  · simp [fourierCoeff_add, h, h.symm]
  · simp [fourierCoeff_add, Ne.symm hS.1, Ne.symm hS.2]

/-- `χ_{0} + χ_{0,1}` has variance `2`. -/
private theorem variance_twoLevels : 𝔼 x, (twoLevels x - 𝔼 y, twoLevels y) ^ 2 = 2 := by
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq]
  have h := sum_mul_fourierCoeff_twoLevels_sq (s := univ.filter (· ≠ ∅)) (by simp) (by simp)
    fun _ => 1
  simp only [one_mul] at h
  rw [h]
  norm_num

/-- `χ_{0} + χ_{0,1}` has total influence `1 + 2 = 3`. -/
private theorem totalInfluence_twoLevels : totalInfluence twoLevels = 3 := by
  rw [totalInfluence_eq_sum_card_mul_fourierCoeff_sq,
    sum_mul_fourierCoeff_twoLevels_sq (mem_univ _) (mem_univ _)]
  norm_num

/-- **The convexity step on two levels**: for `χ_{0} + χ_{0,1}`, with `Var = 2` and `I = 3`, it
reads `2 · 3^{-3/2} ≤ 3^{-1} + 3^{-2} = 4 / 9`. -/
example : 2 * (1 / 3 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 / 9 := by
  have h := expect_sub_expect_sq_mul_one_third_rpow_le twoLevels
  rw [variance_twoLevels, totalInfluence_twoLevels,
    sum_mul_fourierCoeff_twoLevels_sq (by simp) (by simp)] at h
  norm_num at h ⊢
  linarith

/-- **The KKL Edge-Isoperimetric Theorem on a dictator**: on every index set, for a dictator
`x ↦ x i` (`Var = I = 1`) the theorem gives a coordinate of influence at least `1`, the maximum
possible. -/
example (i : ι) : ∃ j, 1 ≤ influence j fun x : ι → Bool => signVal (x i) := by
  obtain ⟨j, hj⟩ := exists_nine_div_sq_mul_one_ninth_rpow_le_influence (fun x : ι → Bool => x i)
    (by rw [variance_dictator]; norm_num)
  rw [variance_dictator, totalInfluence_dictator] at hj
  exact ⟨j, by norm_num at hj; exact hj⟩

/-- **The Kahn–Kalai–Linial theorem for Tribes**: the nearly balanced Tribes function on
`n = s w` bits, `s = tribesSize w` and `w ≥ 2`, has variance at least `3 / 4`, so the theorem gives
a coordinate of influence at least `3 log n / (16 n)`. -/
example {w : ℕ} (hw : 2 ≤ w) :
    ∃ k, 3 * Real.log (tribesSize w * w : ℕ) / (16 * (tribesSize w * w : ℕ)) ≤
      influence k (fun x => signVal (tribes w (tribesSize w) x)) := by
  have hs : 1 ≤ tribesSize w :=
    le_trans Nat.one_le_two_pow (two_pow_sub_one_le_tribesSize (by omega))
  have : Nonempty (Fin (tribesSize w * w)) := ⟨⟨0, Nat.mul_pos hs (by omega)⟩⟩
  obtain ⟨k, hk⟩ :=
    exists_expect_sub_expect_sq_mul_log_card_div_le_influence (tribes w (tribesSize w))
  refine ⟨k, le_trans ?_ hk⟩
  rw [Fintype.card_fin]
  have hV := three_div_four_le_expect_sub_expect_sq_tribes hw
  have hL : 0 ≤ Real.log (tribesSize w * w : ℕ) / (4 * (tribesSize w * w : ℕ)) :=
    div_nonneg (Real.log_natCast_nonneg _) (by positivity)
  calc 3 * Real.log (tribesSize w * w : ℕ) / (16 * (tribesSize w * w : ℕ))
      = 3 / 4 * (Real.log (tribesSize w * w : ℕ) / (4 * (tribesSize w * w : ℕ))) := by ring
    _ ≤ _ * (Real.log (tribesSize w * w : ℕ) / (4 * (tribesSize w * w : ℕ))) :=
        mul_le_mul_of_nonneg_right hV hL
    _ = _ := by ring

end CslibFrontierTests.KahnKalaiLinial
