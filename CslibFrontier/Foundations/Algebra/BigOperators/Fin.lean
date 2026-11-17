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

/-!
# Truncating finite sums with a zero tail

A finite-vector sum agrees with a shorter range sum when all omitted summands vanish.
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

end Fin
