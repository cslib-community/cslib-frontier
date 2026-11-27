/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Fib/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Log

/-!
# Fibonacci growth bounds for height-balanced trees

A binary tree whose sibling heights differ by at most one has at least `Nat.fib (h + 2)` leaves
(or nodes, counted suitably) at height `h`. These lemmas turn that count into the logarithmic
height bound `h ≤ 2 * Nat.log 2 n`, without real numbers. AVL trees, ropes and Fibonacci heaps
share them.

## Main results

* `Nat.fib_max_add_three_le`: the inductive step for sibling heights `n` and `m` that differ by at
  most one, `Nat.fib (max n m + 3) ≤ Nat.fib (n + 2) + Nat.fib (m + 2)`.
* `Nat.two_pow_half_succ_le_fib`: `2 ^ ((h + 1) / 2) ≤ Nat.fib (h + 2)`.
* `Nat.le_two_mul_log_of_fib_le`: `Nat.fib (h + 2) ≤ n` implies `h ≤ 2 * Nat.log 2 n`.
-/

public section

namespace Nat

/-- The Fibonacci step for a node whose children have heights `n` and `m` differing by at most
one: `Nat.fib (max n m + 3) ≤ Nat.fib (n + 2) + Nat.fib (m + 2)`. -/
theorem fib_max_add_three_le {n m : ℕ} (hnm : n ≤ m + 1) (hmn : m ≤ n + 1) :
    fib (max n m + 3) ≤ fib (n + 2) + fib (m + 2) := by
  wlog hle : m ≤ n generalizing n m
  · simpa only [max_comm, Nat.add_comm (fib (n + 2))] using this hmn hnm (by omega)
  rw [max_eq_left hle]
  exact fib_add_two.trans_le ((Nat.add_le_add_right (fib_mono (by omega)) _).trans_eq
    (Nat.add_comm _ _))

/-- Fibonacci numbers grow at least as fast as `√2`: `2 ^ ((h + 1) / 2) ≤ Nat.fib (h + 2)`. -/
theorem two_pow_half_succ_le_fib : ∀ h : ℕ, 2 ^ ((h + 1) / 2) ≤ fib (h + 2)
  | 0 => by decide
  | 1 => by decide
  | h + 2 => by
    have ih := two_pow_half_succ_le_fib h
    have hmono : fib (h + 2) ≤ fib (h + 2 + 1) := fib_le_fib_succ
    rw [Nat.add_right_comm h 2 1, Nat.add_div_right _ zero_lt_two, Nat.pow_succ, fib_add_two]
    omega

/-- A height `h` with `Nat.fib (h + 2) ≤ n` is at most `2 * Nat.log 2 n`. -/
theorem le_two_mul_log_of_fib_le {h n : ℕ} (hf : fib (h + 2) ≤ n) : h ≤ 2 * log 2 n := by
  have := le_log_of_pow_le (by decide) ((two_pow_half_succ_le_fib h).trans hf)
  omega

end Nat
