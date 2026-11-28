/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Rat/Lemmas.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring

/-!
# Clearing rational denominators

`Rat.clearDenom_entry` computes the integer obtained by scaling a rational by a multiple
of its denominator. It is shared by rational matrix and integer-programming reductions.
-/

public section

/-- Clearing a single rational denominator by multiplying with a multiple `d` of `q.den`. -/
theorem Rat.clearDenom_entry {q : ℚ} {d : ℕ} (hdvd : q.den ∣ d) :
    (d : ℚ) * q = ((q.num * ((d / q.den : ℕ) : ℤ) : ℤ) : ℚ) := by
  have hden_ne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 q.pos.ne'
  have hden_mul : ((d / q.den : ℕ) : ℚ) * (q.den : ℚ) = (d : ℚ) := by
    exact_mod_cast Nat.div_mul_cancel hdvd
  calc
    (d : ℚ) * q = ((d / q.den : ℕ) : ℚ) * (q.den : ℚ) * q := by rw [hden_mul]
    _ = ((d / q.den : ℕ) : ℚ) * ((q.den : ℚ) * (q.num / (q.den : ℚ))) := by
          rw [Rat.num_div_den]; ring
    _ = ((d / q.den : ℕ) : ℚ) * (q.num : ℚ) := by rw [mul_div_cancel₀ _ hden_ne]
    _ = ((q.num * ((d / q.den : ℕ) : ℤ) : ℤ) : ℚ) := by
          simp only [Int.cast_mul, Int.cast_natCast]; ring
