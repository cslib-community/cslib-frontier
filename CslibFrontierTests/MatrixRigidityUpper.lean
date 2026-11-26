/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.Random
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Matrix rigidity upper bounds and random matrices over finite fields

Ordinary-import `module` client checks for `Matrix.rigidity_le_mul_sub`,
`Matrix.rigidity_le_sq_sub`, and the finite-field counting and random-matrix bounds in
`CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.Random`:
* Rectangular upper bound `(3 - 1) (5 - 1) = 8` on `3 × 5` matrices over `ℚ`, strictly below the
  entry-count bound `3 · 5 = 15`.
* Tightness of `(n - r) ^ 2` on `!![1, 1; 1, -1]` over `ℚ` at `r = 0` (`4`) and `r = 1` (`1`).
* Concrete low-rank and bounded-rigidity counts on `4 × 4` binary matrices (`< 512` of rank `≤ 1`
  and `≤ 8704` of `1`-rigidity `< 2`, out of `65536`).
* High-probability lower bound on `64 × 64` matrices over `𝔽₂` at `r = 16`: more than a
  `1 - 2 ^ -1152` fraction have rigidity at least `76`, above the rank-deficit bound `64 - 16 = 48`.
* Rectangular existence (`30 ≤ A.rigidity 4`) and high-probability (`> 1 - 2 ^ -61` for
  `25 ≤ A.rigidity 4`) bounds on `16 × 32` matrices over `𝔽₂`.
* Exact maximal rigidity `(m - r) (n - r)` with positive density over `ZMod 101` (`2 × 2`,
  `> 37 / 101`) and `ZMod 257` (`2 × 3` at `r = 1`, `> 1 / 257`).
-/

-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.MatrixRigidityUpper

open Finset Matrix

/-! ### Rectangular and square upper bounds -/

-- Every `3 × 5` rational matrix has `1`-rigidity at most `(3 - 1) * (5 - 1) = 8 < 15`.
example (A : Matrix (Fin 3) (Fin 5) ℚ) : A.rigidity 1 ≤ 8 := by
  simpa using A.rigidity_le_mul_sub 1

-- `!![1, 1; 1, -1]` attains the square upper bound `(2 - r) ^ 2` at both `r = 0` and `r = 1`.
private def hadamardTwo : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 1, -1]

example : hadamardTwo.rigidity 0 = 4 ∧ hadamardTwo.rigidity 1 = 1 := by
  refine ⟨?_, le_antisymm (by simpa using hadamardTwo.rigidity_le_sq_sub 1) ?_⟩
  · rw [rigidity_zero, diffCount_eq_card_filter]
    decide
  · have hdet : hadamardTwo.det ≠ 0 := by
      rw [hadamardTwo, det_fin_two_of]
      norm_num
    have hunit : IsUnit hadamardTwo :=
      (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hrank : hadamardTwo.rank = 2 := by
      rw [rank_of_isUnit _ hunit, Fintype.card_fin]
    have hlow := hadamardTwo.rank_sub_le_rigidity 1
    omega

/-! ### Concrete finite-field counts over `𝔽₂` -/

-- Fewer than `512` of the `65536` binary `4 × 4` matrices have rank at most `1`.
example : #{B : Matrix (Fin 4) (Fin 4) (ZMod 2) | B.rank ≤ 1} < 512 := by
  have h := card_rank_le_mul_lt (m := Fin 4) (n := Fin 4) (K := ZMod 2) 1
  generalize #{B : Matrix (Fin 4) (Fin 4) (ZMod 2) | B.rank ≤ 1} = c at h ⊢
  rw [ZMod.card, Fintype.card_fin] at h
  omega

-- At most `8704` of the `65536` binary `4 × 4` matrices have `1`-rigidity strictly below `2`.
example : #{A : Matrix (Fin 4) (Fin 4) (ZMod 2) | A.rigidity 1 < 2} ≤ 8704 := by
  have h := card_rigidity_lt_mul_le (m := Fin 4) (n := Fin 4) (K := ZMod 2) 1 2
  generalize #{A : Matrix (Fin 4) (Fin 4) (ZMod 2) | A.rigidity 1 < 2} = c at h ⊢
  rw [ZMod.card, Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_one] at h
  norm_num at h
  omega

/-! ### High-probability and existence bounds over `𝔽₂` -/

private theorem log_two_64 : Nat.log 2 64 = 6 := by
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, Nat.log_pow one_lt_two]

private theorem log_two_512 : Nat.log 2 (16 * 32) = 9 := by
  rw [show 16 * 32 = 2 ^ 9 by norm_num, Nat.log_pow one_lt_two]

-- More than a `1 - 2 ^ -1152` fraction of `64 × 64` matrices over `𝔽₂` have `16`-rigidity `≥ 76`
-- (strictly exceeding the trivial rank-deficit bound `64 - 16 = 48`).
example :
    1 - ((2 : ℝ)⁻¹) ^ 1152 <
      (#{A : Matrix (Fin 64) (Fin 64) (ZMod 2) | 76 ≤ A.rigidity 16} : ℝ) /
        Fintype.card (Matrix (Fin 64) (Fin 64) (ZMod 2)) := by
  have h := one_sub_inv_pow_lt_card_sq_div_log_le_rigidity (n := Fin 64) (K := ZMod 2) 16
  generalize Fintype.card (Matrix (Fin 64) (Fin 64) (ZMod 2)) = total at h ⊢
  rw [ZMod.card, Fintype.card_fin, log_two_64,
    show (64 - 16) ^ 2 / 2 = 1152 by norm_num,
    show (64 - 16) ^ 2 / (4 * 6 + 6) = 76 by norm_num, Nat.cast_ofNat] at h
  exact h

-- Some `16 × 32` matrix over `𝔽₂` has `4`-rigidity at least `30`.
example : ∃ A : Matrix (Fin 16) (Fin 32) (ZMod 2), 30 ≤ A.rigidity 4 := by
  have h := exists_div_log_le_rigidity (m := Fin 16) (n := Fin 32) (K := ZMod 2) 4
  rw [ZMod.card, Fintype.card_fin, Fintype.card_fin, log_two_512,
    show (16 - 4) * (32 - 4) / (9 + 2) = 30 by norm_num] at h
  exact h

-- More than a `1 - 2 ^ -61` fraction of `16 × 32` matrices over `𝔽₂` have `4`-rigidity `≥ 25`.
example :
    1 - ((2 : ℝ)⁻¹) ^ 61 <
      (#{A : Matrix (Fin 16) (Fin 32) (ZMod 2) | 25 ≤ A.rigidity 4} : ℝ) /
        Fintype.card (Matrix (Fin 16) (Fin 32) (ZMod 2)) := by
  have h := one_sub_inv_pow_lt_card_le_rigidity_div
    (m := Fin 16) (n := Fin 32) (K := ZMod 2) (r := 4) (s := 25) (t := 61)
    (by rw [ZMod.card, Fintype.card_fin, Fintype.card_fin, log_two_512])
  rw [ZMod.card, Nat.cast_ofNat] at h
  exact h

/-! ### Exact maximal rigidity over large prime fields -/

private instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩
private instance : Fact (Nat.Prime 257) := ⟨by norm_num⟩

-- Over `𝔽₁₀₁`, more than `37 / 101` of all `2 × 2` matrices attain exact `1`-rigidity `1`.
example :
    (37 / 101 : ℝ) <
      (#{A : Matrix (Fin 2) (Fin 2) (ZMod 101) | A.rigidity 1 = 1} : ℝ) /
        Fintype.card (Matrix (Fin 2) (Fin 2) (ZMod 101)) := by
  have h := one_sub_lt_card_rigidity_eq_mul_sub_div (m := Fin 2) (n := Fin 2) (K := ZMod 101) 1
  generalize Fintype.card (Matrix (Fin 2) (Fin 2) (ZMod 101)) = total at h ⊢
  rw [ZMod.card, Fintype.card_fin, show (2 - 1) * (2 - 1) = 1 by norm_num,
    show (1 : ℝ) - 4 * (2 : ℝ) ^ (2 * 2) / (101 : ℕ) = 37 / 101 by norm_num] at h
  exact h

-- Over `𝔽₂₅₇`, a positive fraction (`> 1 / 257`) of `2 × 3` matrices attain exact `1`-rigidity
-- `(2 - 1) * (3 - 1) = 2`.
example :
    (1 / 257 : ℝ) <
      (#{A : Matrix (Fin 2) (Fin 3) (ZMod 257) | A.rigidity 1 = 2} : ℝ) /
        Fintype.card (Matrix (Fin 2) (Fin 3) (ZMod 257)) := by
  have h := one_sub_lt_card_rigidity_eq_mul_sub_div (m := Fin 2) (n := Fin 3) (K := ZMod 257) 1
  generalize Fintype.card (Matrix (Fin 2) (Fin 3) (ZMod 257)) = total at h ⊢
  rw [ZMod.card, Fintype.card_fin, Fintype.card_fin, show (2 - 1) * (3 - 1) = 2 by norm_num,
    show (1 : ℝ) - 4 * (2 : ℝ) ^ (2 * 3) / (257 : ℕ) = 1 / 257 by norm_num] at h
  exact h

end CslibFrontierTests.MatrixRigidityUpper
