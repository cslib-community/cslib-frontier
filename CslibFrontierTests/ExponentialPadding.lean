/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.EXP
import CslibFrontier.Computability.Complexity.FineGrained.Padding
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exponential padding and a unary majorant at a sublinear power. -/

open Cslib.Complexity Turing.MultiTapeTM

example :
    {y : List Bool | (fun _ : List Bool × ℕ => false) (y, 2 ^ y.length) = true} ∈ E encBits ∧
      {y : List Bool | (fun _ : List Bool × ℕ => true) (y, 2 ^ y.length) = true} ∈
        E encBits :=
  ⟨setOf_mem_E_of_computableInPolyTime_pad (ComputableInPolyTime.const false),
    setOf_mem_E_of_computableInPolyTime_pad (ComputableInPolyTime.const true)⟩

/-- A machine can allocate a seed of at least `2 ^ √(n + 1) * (n + 1)` bits with a power
below one. Check the length guarantee at `n = 3`, where the requested length is exactly 16. -/
example :
    ∃ (q : ℝ) (seedLength : ℕ → ℕ), 1 / 2 < q ∧ q < 1 ∧
      ComputableInPowerExpTime seedLength encUnary encUnary id q ∧ 16 ≤ seedLength 3 := by
  obtain ⟨q, seedLength, hq, _, hq₁, hseed, hlen⟩ :=
    exists_computableInPowerExpTime_unary_majorant (p := 1 / 2)
      (ComputableInPolyTime.id' : ComputableInPolyTime id encUnary encUnary) (by norm_num) 1 1
  refine ⟨q, seedLength, hq, hq₁, hseed, ?_⟩
  have h := hlen 3
  have hsqrt : (3 + 1 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (3 + 1 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [encUnary_apply, List.length_replicate, Nat.cast_ofNat, Nat.cast_one,
    one_mul, pow_one, hsqrt] at h
  rw [Real.rpow_two] at h
  exact_mod_cast (show (16 : ℝ) ≤ seedLength 3 by linarith)
