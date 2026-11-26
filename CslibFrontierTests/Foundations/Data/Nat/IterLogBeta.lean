/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.Data.Nat.IterLog

/-! Tests for `Nat.iterClog`, `Nat.iterPow2`, and `Nat.iterClogBeta`. -/

public section

namespace CslibFrontierTests.IterLogBeta

open Nat

-- Concrete evaluations at `k = 0` and boundary inputs `n = 0, 1, 2, 16, 32`.
example :
    iterClog 0 0 = 0 ∧
      iterClog 0 1 = 1 ∧
      iterClog 0 32 = 32 ∧
      iterPow2 0 5 = 5 := by
  decide

example :
    iterClog 1 0 = 0 ∧
      iterClog 1 1 = 0 ∧
      iterClog 1 2 = 1 ∧
      iterClog 2 16 = 2 ∧
      iterClog 3 16 = 1 ∧
      iterClog 3 32 = 2 ∧
      iterClog 4 32 = 1 := by
  decide

example :
    iterPow2 1 3 = 8 ∧
      iterPow2 2 3 = 256 ∧
      iterPow2 3 1 = 16 ∧
      iterPow2 4 1 = 65536 := by
  decide

-- Generalized stopping-index values at `t = 0, 1, 2, 4, 5` and `n = 0, 1, 2, 16, 32, 65536`.
example :
    iterClogBeta 0 0 = 1 ∧
      iterClogBeta 0 1 = 1 ∧
      iterClogBeta 1 2 = 1 ∧
      iterClogBeta 0 16 = 3 ∧
      iterClogBeta 1 16 = 3 ∧
      iterClogBeta 2 16 = 2 ∧
      iterClogBeta 4 16 = 1 := by
  decide

example :
    iterClogBeta 1 32 = 4 ∧
      iterClogBeta 2 32 = 3 ∧
      iterClogBeta 3 32 = 2 ∧
      iterClogBeta 5 32 = 1 ∧
      iterClogBeta 1 65536 = 4 ∧
      iterClogBeta 1 65537 = 5 ∧
      iterClogBeta 4 65536 = 2 := by
  decide

-- Threshold equivalence, monotonicity, and `logStar` / `iterLog` comparisons.
example (k n x : ℕ) : iterClog k n ≤ x ↔ n ≤ iterPow2 k x :=
  iterClog_le_iff_le_iterPow2 k n x

example {a b : ℕ} (h : a ≤ b) : iterClog 3 a ≤ iterClog 3 b :=
  iterClog_mono 3 h

example {j k : ℕ} (h : j ≤ k) (n : ℕ) : iterClog k n ≤ iterClog j n :=
  iterClog_anti_left n h

example (n : ℕ) : iterClog 3 n ≤ iterLog 3 n + 1 :=
  iterClog_le_iterLog_add_one (by decide) n

example (t n : ℕ) {a b : ℕ} (hab : a ≤ b) :
    iterClogBeta t a ≤ iterClogBeta t b ∧ iterClogBeta b n ≤ iterClogBeta a n :=
  ⟨iterClogBeta_mono_right t hab, iterClogBeta_anti_left n hab⟩

example (n : ℕ) : iterClogBeta 0 n = max 1 (logStar n) :=
  iterClogBeta_of_le_one (Nat.zero_le 1) n

example (t n : ℕ) : iterClogBeta t n ≤ max 1 (logStar n) :=
  iterClogBeta_le_max_one_logStar t n

example {t n k : ℕ} (hk : 1 ≤ k) : iterClogBeta t n ≤ k ↔ iterClog k n ≤ max 1 t :=
  iterClogBeta_le_iff hk

example (t n : ℕ) : iterClogBeta t n = 1 ↔ n ≤ 2 ^ max 1 t :=
  iterClogBeta_eq_one_iff

example : iterClogBeta (100 / 5) 5 < iterClogBeta (100 / 200) 200 :=
  iterClogBeta_div_lt_of_mul_le (by decide) (by decide) (by decide) (by decide)

example : iterClogBeta (1000 / 30) 30 < iterClogBeta (1000 / 200) 200 :=
  iterClogBeta_div_lt_of_mul_le (by decide) (by decide) (by decide) (by decide)

example (m n t : ℕ) (ht : 2 * m / n ≤ max 1 t) :
    m * iterClogBeta t n ≤ 2 * m + 6 * n * max 1 (iterClog 1 n) ∧
      m * iterClogBeta t n ≤ 3 * m + 8 * n * max 1 (iterClog 2 n) ∧
      m * iterClogBeta t n ≤ 4 * m + 10 * n * max 1 (iterClog 3 n) :=
  ⟨mul_iterClogBeta_le_of_div_le 1 m n t ht,
    mul_iterClogBeta_le_of_div_le 2 m n t ht,
    mul_iterClogBeta_le_of_div_le 3 m n t ht⟩

example (m n : ℕ) :
    m * iterClogBeta (2 * m / n) n ≤ 2 * m + 12 * n * max 1 (iterLog 1 n) ∧
      m * iterClogBeta (2 * m / n) n ≤ 3 * m + 16 * n * max 1 (iterLog 2 n) ∧
      m * iterClogBeta (2 * m / n) n ≤ 4 * m + 20 * n * max 1 (iterLog 3 n) :=
  ⟨mul_iterClogBeta_div_le_iterLog (by decide : 1 ≤ 1) m n,
    mul_iterClogBeta_div_le_iterLog (by decide : 1 ≤ 2) m n,
    mul_iterClogBeta_div_le_iterLog (by decide : 1 ≤ 3) m n⟩

end CslibFrontierTests.IterLogBeta
