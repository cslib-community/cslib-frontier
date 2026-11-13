/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import CslibFrontier.Foundations.BooleanAnalysis.MajorityInfluence
public import Mathlib.Analysis.Real.Pi.Bounds
import CslibFrontier.Foundations.Data.Finset.Expect

/-! # The total influence of majority

The majority of three bits has total influence `3 / 2`: by the identity `I[Maj₃] = 𝔼 |x₁ + x₂ + x₃|`
(the sum is `±3` on two of the eight inputs and `±1` on the other six), and independently as the
average sensitivity (two pivotal bits on each of the six non-unanimous inputs). The total influence
of majority grows like `√(2 / π) √n`: so it is `o(n)`, and along odd `n` it is eventually below
`√n`.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisMajorityInfluence

open Cslib Cslib.BitString Filter Finset Topology Real
open scoped BigOperators

-- `I[Maj₃] = 3 / 2` through the identity `I[Majₙ] = 𝔼 |x₁ + ⋯ + xₙ|`.
example : totalInfluence (fun x : BitString 3 => signVal (majority 3 x)) = 3 / 2 := by
  rw [totalInfluence_majority_eq_expect_abs]
  simp only [Fin.expect_univ_cons, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_zero, Fintype.expect_bool, Fintype.expect_unique]
  norm_num

-- `I[Maj₃] = 3 / 2` independently, as the average sensitivity.
example : totalInfluence (fun x : BitString 3 => signVal (majority 3 x)) = 3 / 2 := by
  rw [totalInfluence_signVal, Fintype.expect_eq_sum_div_card]
  have h : ∑ x : BitString 3,
      #{i | majority 3 (Function.update x i (!x i)) ≠ majority 3 x} = 12 := by
    decide
  rw [← Nat.cast_sum, h]
  norm_num

-- The total influence of majority is `o(n)`: `I[Majₙ] / n = (I[Majₙ] / √n) · (√n)⁻¹ → 0`.
example : Tendsto (fun n : ℕ => totalInfluence (fun x : BitString n => signVal (majority n x)) / n)
    atTop (𝓝 0) := by
  have h := tendsto_totalInfluence_majority_div_sqrt.mul
    (tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  rw [Function.comp_apply, Function.comp_apply, ← div_eq_mul_inv, div_div,
    mul_self_sqrt (Nat.cast_nonneg _)]

-- Along odd `n = 2m + 1`, where `majority n` is the book's `Majₙ`, the total influence is
-- eventually below `√n`, since `√(2 / π) < 1`.
example : ∀ᶠ m : ℕ in atTop, totalInfluence (fun x : BitString (2 * m + 1) =>
    signVal (majority (2 * m + 1) x)) < √((2 * m + 1 : ℕ) : ℝ) := by
  have h : √(2 / π) < 1 := by
    rw [sqrt_lt' one_pos, one_pow, div_lt_one pi_pos]
    linarith [pi_gt_three]
  filter_upwards [tendsto_totalInfluence_majority_two_mul_add_one_div_sqrt.eventually
    (gt_mem_nhds h)] with m hm
  rwa [div_lt_one (sqrt_pos.2 (by positivity))] at hm

end CslibFrontierTests.BooleanAnalysisMajorityInfluence
