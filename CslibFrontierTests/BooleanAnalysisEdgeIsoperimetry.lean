/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.EdgeIsoperimetry
import CslibFrontier.Foundations.Data.Finset.Expect

/-! # Tests for the edge-isoperimetric inequality -/

public section

namespace CslibFrontierTests.BooleanAnalysisEdgeIsoperimetry

open Cslib Cslib.BitString Finset Function

/-- The whole square: each of its 4 points has 2 neighbours in it, so it spans `8 = 4 log₂ 4`
directed edges and the bound is attained. -/
example : ∑ x ∈ (univ : Finset (Fin 2 → Bool)), (#{i | update x i (!x i) ∈ univ} : ℝ) = 8 ∧
    (#(univ : Finset (Fin 2 → Bool)) : ℝ) * Real.logb 2 #(univ : Finset (Fin 2 → Bool)) = 8 := by
  refine ⟨by simp; norm_num, ?_⟩
  rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [show ((2 ^ 2 : ℕ) : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one one_lt_two]
  norm_num

/-- Three corners of the square span 4 directed edges. -/
theorem sum_card_filter_update_mem_corners :
    ∑ x ∈ ({x | x 0 = true ∨ x 1 = true} : Finset (Fin 2 → Bool)),
      (#{i | update x i (!x i) ∈ ({x | x 0 = true ∨ x 1 = true} : Finset (Fin 2 → Bool))} : ℝ) =
        4 := by
  rw [← Nat.cast_sum]
  norm_cast

/-- The edge bound applied to the three corners gives `4 ≤ 3 log₂ 3`. -/
example : (4 : ℝ) ≤ 3 * Real.logb 2 3 := by
  have h := sum_card_filter_update_mem_le ({x | x 0 = true ∨ x 1 = true} : Finset (Fin 2 → Bool))
  rw [sum_card_filter_update_mem_corners,
    show #({x | x 0 = true ∨ x 1 = true} : Finset (Fin 2 → Bool)) = 3 by decide] at h
  exact_mod_cast h

/-- The dictator `x ↦ x 0` on three bits is at relative Hamming distance `1/2` from either
constant. -/
theorem hammingDist_dictator_div (b : Bool) :
    (hammingDist (fun x : Fin 3 → Bool => x 0) (fun _ => b) : ℝ) / 2 ^ Fintype.card (Fin 3) =
      1 / 2 := by
  rw [show hammingDist (fun x : Fin 3 → Bool => x 0) (fun _ => b) = 4 by cases b <;> decide]
  norm_num

/-- The min form for the dictator `x ↦ x 0`, with `α = 1/2`, meets the bound `1 ≤ I[f]`. -/
example : 1 ≤ totalInfluence (fun x : Fin 3 → Bool => signVal (x 0)) := by
  have h := two_mul_min_mul_logb_inv_le_totalInfluence (fun x : Fin 3 → Bool => x 0)
  rw [hammingDist_dictator_div, hammingDist_dictator_div] at h
  norm_num at h
  exact h

/-- The conjunction of two bits is true on a quarter of the square: its relative Hamming distance
to the constant `false` is `1/4`. -/
theorem hammingDist_and_false_div :
    (hammingDist (fun x : Fin 2 → Bool => x 0 && x 1) (fun _ => false) : ℝ) /
      2 ^ Fintype.card (Fin 2) = 1 / 4 := by
  rw [show hammingDist (fun x : Fin 2 → Bool => x 0 && x 1) (fun _ => false) = 1 by decide]
  norm_num

/-- The conjunction of two bits, a subcube of density `1/4`, has total influence `1`. -/
theorem totalInfluence_and :
    totalInfluence (fun x : Fin 2 → Bool => signVal (x 0 && x 1)) = 1 := by
  simp only [totalInfluence, influence_signVal, Fintype.expect_eq_sum_div_card, Fin.sum_univ_two,
    Fin.sum_univ_cons_bool, Fintype.card_fun]
  simp [Fin.cons_zero, Fin.cons_one, Fintype.card_bool]
  norm_num

/-- The form for either constant, applied to the conjunction of two bits with `b = false`
(`α = 1/4`), gives `1 ≤ I[f]`. -/
example : 1 ≤ totalInfluence (fun x : Fin 2 → Bool => signVal (x 0 && x 1)) := by
  have h := two_mul_hammingDist_div_mul_logb_inv_le_totalInfluence
    (fun x : Fin 2 → Bool => x 0 && x 1) false
  rw [hammingDist_and_false_div, show (1 / 4 : ℝ)⁻¹ = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one one_lt_two] at h
  norm_num at h
  exact h

/-- The edge-isoperimetric inequality is attained by the conjunction of two bits: the bound
`2 · (1/4) · log₂ 4 = 1` equals its total influence. -/
example : 2 * ((hammingDist (fun x : Fin 2 → Bool => x 0 && x 1) (fun _ => false) : ℝ) /
        2 ^ Fintype.card (Fin 2)) *
      Real.logb 2 ((hammingDist (fun x : Fin 2 → Bool => x 0 && x 1) (fun _ => false) : ℝ) /
        2 ^ Fintype.card (Fin 2))⁻¹ =
      totalInfluence (fun x : Fin 2 → Bool => signVal (x 0 && x 1)) := by
  rw [hammingDist_and_false_div, totalInfluence_and, show (1 / 4 : ℝ)⁻¹ = 2 ^ (2 : ℕ) by norm_num,
    Real.logb_pow, Real.logb_self_eq_one one_lt_two]
  norm_num

end CslibFrontierTests.BooleanAnalysisEdgeIsoperimetry
