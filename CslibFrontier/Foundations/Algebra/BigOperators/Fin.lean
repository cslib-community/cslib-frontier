/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/BigOperators/Fin.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Abel

/-!
# Truncation and telescoping of finite sums

A finite-vector sum agrees with a shorter range sum when all omitted summands vanish.
`sum_univ_adjacent_differences` telescopes differences along a sequence of indexed pairs.
-/

public section

open Finset
namespace Fin

/-- A sum over `Fin n` of a function vanishing from `k` on is a sum over `range k`. -/
theorem sum_eq_sum_range_of_eq_zero {M : Type*} [AddCommMonoid M] {n k : ℕ} (hk : k ≤ n)
    (f : ℕ → M) (hf : ∀ j, k ≤ j → f j = 0) :
    ∑ j : Fin n, f j = ∑ j ∈ range k, f j := by
  rw [Fin.sum_univ_eq_sum_range f n, ← Finset.sum_range_add_sum_Ico _ hk]
  rw [Finset.sum_eq_zero (s := Ico k n) fun j hj => hf j (Finset.mem_Ico.1 hj).1, add_zero]

/-- The differences within indexed pairs and across consecutive pairs telescope
to the difference from the first entry to the last exit. -/
theorem sum_univ_adjacent_differences {M : Type*} [AddCommGroup M] {n : ℕ}
    (entry exit : Fin (n + 1) → M) :
    (∑ i, (exit i - entry i)) + ∑ i : Fin n, (entry i.succ - exit i.castSucc) =
      exit (Fin.last n) - entry 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Fin.sum_univ_castSucc exit, Fin.sum_univ_succ entry]
  abel

end Fin
