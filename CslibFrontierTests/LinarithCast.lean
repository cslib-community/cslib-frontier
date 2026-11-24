/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Basic.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! # `cast_linarith`: natural-number and integer facts in an ordered field -/

namespace CslibFrontierTests.LinarithCast

/-! ### What `linarith` misses -/

-- `linarith` casts `h` to `ℤ`, not to `ℝ`.
example (a b : ℕ) (h : a ≤ b) : (a : ℝ) ≤ b + 1 := by
  fail_if_success linarith
  cast_linarith

/-! ### Comparisons that are cast -/

-- A strict comparison is used as `a + 1 ≤ b`, which `ℝ` does not know from `a < b`.
example (a b : ℕ) (h : a < b) : (a : ℝ) + 1 ≤ b := by cast_linarith

example (a b : ℤ) (h : a < b) : (a : ℝ) + 1 ≤ b := by cast_linarith

example (a b : ℤ) (h : a ≤ b) (x : ℚ) (hx : x ≤ a) : x ≤ b := by cast_linarith

example (a b : ℤ) (h : a = b) (x : ℚ) (hx : x ≤ a) : x ≤ b := by cast_linarith

-- A negated comparison, and a field other than `ℝ`.
example (a b : ℕ) (h : ¬b ≤ a) : (a : ℚ) + 1 ≤ b := by cast_linarith

-- An equation; the casts are pushed through `+` and `*`.
example (a b c : ℕ) (h : a + 2 * b = c) (x : ℝ) (hx : x ≤ a) : x + 2 * b ≤ c := by
  cast_linarith

-- Products stay atoms, as in `linarith`.
example (a b : ℕ) (h : a * b ≤ 4) : (a : ℝ) * b ≤ 4 := by cast_linarith

-- A truncated subtraction stays a cast atom.
example (a b : ℕ) (h : a - b ≤ 3) : ((a - b : ℕ) : ℝ) ≤ 3 := by cast_linarith

-- The goal can be `False`; the field comes from the hypotheses.
example (a b : ℕ) (h : a < b) (x : ℝ) (h₁ : (b : ℝ) ≤ x) (h₂ : x < a + 1) : False := by
  cast_linarith

-- The casts in the field are pushed too: `↑(a + b)` is the sum `↑a + ↑b`.
example (a b : ℕ) (x : ℝ) (h : x ≤ a + b) : x ≤ ((a + b : ℕ) : ℝ) := by
  fail_if_success linarith
  cast_linarith

-- The nonnegativity of a cast natural number is known.
example (n : ℕ) (x : ℝ) (h : x + n ≤ 0) : x ≤ 0 := by cast_linarith

/-! ### Hypothesis lists -/

example (a b : ℕ) (h : a ≤ b) (x : ℝ) (hx : x = a) : x ≤ b := by cast_linarith only [h, hx]

-- Supplied terms are cast too.
example (k n : ℕ) (f : ℕ → ℕ) (hf : ∀ m, f m ≤ 2 * m) (hk : k ≤ n) : (f k : ℝ) ≤ 2 * n := by
  cast_linarith only [hf k, hk]

/-! ### Local definitions -/

-- `set` replaces the cast by a local definition; the two are the same atom.
example (a b : ℕ) (h : a ≤ b) : (a : ℝ) ≤ b + 1 := by
  set x : ℝ := (a : ℝ)
  cast_linarith only [h]

example (V : Type) [Finite V] (k : ℕ) (h : Nat.card V ≤ 2 * k) : (Nat.card V : ℝ) / 2 ≤ k := by
  set n : ℝ := (Nat.card V : ℝ) with hn
  cast_linarith

/-! ### `cast_nlinarith` -/

example (a : ℕ) (h : 2 ≤ a) : (4 : ℝ) ≤ (a : ℝ) ^ 2 := by cast_nlinarith

example (a b : ℕ) (ha : 1 ≤ a) (hb : 3 ≤ b) (x : ℝ) (hx : x ≤ 3) : x ≤ (a : ℝ) * b := by
  cast_nlinarith

/-! ### Attached `!` -/

example (a b : ℕ) (h : a < b) : (a : ℝ) + 1 ≤ b := by cast_linarith! [h]

example (a : ℕ) (h : 2 ≤ a) : (4 : ℝ) ≤ (a : ℝ) ^ 2 := by cast_nlinarith!

/-! ### Preprocessor lists without `natToInt` -/

-- The cast runs after `filterComparisons`, which turns `¬ b ≤ a` into `a < b`.
example (a b : ℤ) (h : ¬ b ≤ a) : (a : ℚ) + 1 ≤ b := by
  cast_linarith (config := { preprocessors :=
    [Mathlib.Tactic.Linarith.filterComparisons, Mathlib.Tactic.Linarith.compWithZero] })

/-! ### Failures and other types -/

-- A nonlinear fact about the naturals is not derived.
example (a : ℕ) : (a : ℝ) ≤ (a : ℝ) ^ 2 := by
  fail_if_success cast_linarith
  exact_mod_cast Nat.le_self_pow two_ne_zero a

-- Without an ordered field, it is `linarith`.
example (a b : ℕ) (h : a < b) : a + 1 ≤ b := by cast_linarith

end CslibFrontierTests.LinarithCast
