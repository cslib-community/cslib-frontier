/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Fintype/Fin.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Fin

/-!
# Counting the indices of `Fin n` above a threshold

Mathlib's `Fin.card_filter_val_lt` counts the indices of `Fin n` below a threshold `m` as
`min n m`. `Fin.card_filter_le_val` is the complementary count, `n - m`, in truncated
subtraction, so it needs no hypothesis relating `m` and `n`.
-/

public section

namespace Fin

open Finset

/-- The indices of `Fin n` at or above `m` number `n - m`. -/
theorem card_filter_le_val {n : ℕ} (m : ℕ) : #{i : Fin n | m ≤ (i : ℕ)} = n - m := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) fun i => (i : ℕ) < m
  simp only [not_lt, card_filter_val_lt, card_univ, Fintype.card_fin] at h
  omega

end Fin
