/-
Copyright (c) 2026 Samuel Schlesinger, vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, vvauted
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.Data.Nat.InverseAckermann

/-! Values and boundary regimes of `Nat.ackermann`, `Nat.inverseAckermann`, and
`Nat.inverseAckermannTwo`. -/

public section

namespace CslibFrontierTests.InverseAckermann

open Nat

example : ackermann 0 5 = 6 ∧ ackermann 1 0 = 1 ∧ ackermann 1 4 = 9 ∧ ackermann 2 1 = 7 := by
  decide

example : ackermann 3 1 = 2047 := ackermann_three_one

-- Small single-parameter values via structural recursion and `decide`.
example :
    inverseAckermann 0 = 1 ∧
      inverseAckermann 1 = 1 ∧
      inverseAckermann 3 = 1 ∧
      inverseAckermann 4 = 2 ∧
      inverseAckermann 63 = 2 := by
  decide

-- Exact jump from `2` to `3` at `n = 64` (`Nat.log 2 64 + 1 = 7 = ackermann 2 1`).
example : inverseAckermann 64 = 3 := by
  refine le_antisymm ?_ ?_
  · rw [inverseAckermann_le_iff (by decide : 1 ≤ 3), ackermann_three_one]
    decide
  · by_contra h
    have hle : inverseAckermann 64 ≤ 2 := by omega
    have h2 : ackermann 2 1 = 7 := by decide
    rw [inverseAckermann_le_iff (by decide : 1 ≤ 2), h2] at hle
    have hlog : Nat.log 2 64 = 6 := by decide
    omega

-- Two-parameter regimes at `(m, n)`: dense linear collapse (`= 1`) and intermediate (`= 2`, `= 3`).
example :
    inverseAckermannTwo 100 16 = 1 ∧
      inverseAckermannTwo 384 64 = 1 := by
  decide

example : inverseAckermannTwo 256 64 = 2 := by
  refine le_antisymm ?_ ?_
  · rw [inverseAckermannTwo, inverseAckermannAt_le_iff (by decide : 1 ≤ 2),
      max_eq_right (by decide : 1 ≤ 256 / 64 + 1), ackermann_two]
    decide
  · by_contra h
    have hle : inverseAckermannTwo 256 64 ≤ 1 := by omega
    rw [inverseAckermannTwo, inverseAckermannAt_le_iff (Nat.le_refl 1),
      max_eq_right (by decide : 1 ≤ 256 / 64 + 1), ackermann_one] at hle
    have hlog : Nat.log 2 64 = 6 := by decide
    have hdiv : 256 / 64 = 4 := by decide
    omega

example : inverseAckermannTwo 0 64 = 3 := by
  rw [inverseAckermannTwo_of_lt (by decide)]
  refine le_antisymm ?_ ?_
  · rw [inverseAckermann_le_iff (by decide : 1 ≤ 3), ackermann_three_one]
    decide
  · by_contra h
    have hle : inverseAckermann 64 ≤ 2 := by omega
    have h2 : ackermann 2 1 = 7 := by decide
    rw [inverseAckermann_le_iff (by decide : 1 ≤ 2), h2] at hle
    have hlog : Nat.log 2 64 = 6 := by decide
    omega

-- Practical universe sizes below `2 ^ 2046` never exceed `3`.
example : inverseAckermann 1024 ≤ 3 := by
  rw [inverseAckermann_le_iff (by decide : 1 ≤ 3), ackermann_three_one]
  decide

end CslibFrontierTests.InverseAckermann
