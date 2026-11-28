/-
Copyright (c) 2026 Samuel Schlesinger, Vhalan Anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Vhalan Anandarajah
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.TimeSpace.LowerBound
import Mathlib.Data.Nat.Sqrt

set_option linter.privateModule false

open Cslib.Complexity Turing.MultiTapeTM

/-- The Arora–Barak time and space exponents satisfy the strict tradeoff. -/
example {t s : ℕ → ℕ} {Ct Cs : ℕ}
    (ht : ∀ n, t n ^ 5 ≤ Ct * (n + 1) ^ 6) (hs : ∀ n, s n ^ 5 ≤ Cs * (n + 1)) :
    ¬ NTIME encBits id ⊆ TISP encBits t s :=
  not_NTIME_linear_subset_TISP (p := 6) (q := 5) (r := 1) (by decide) (by decide)
    (by decide) ht (fun n => by simpa only [pow_one] using hs n)

/-- The concrete time budget is a fourth root of a fifth power, with constant work space. -/
example : ¬ NTIME encBits id ⊆
    TISP encBits (fun n => ((n + 1) ^ 5).sqrt.sqrt) (fun _ => 1) := by
  apply not_NTIME_linear_subset_TISP (p := 5) (q := 4) (r := 0) (Ct := 1) (Cs := 1)
    (by decide) (by decide) (by decide)
  · intro n
    simp only [one_mul]
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
    exact (Nat.pow_le_pow_left (Nat.sqrt_le' _) 2).trans (Nat.sqrt_le' _)
  · simp
