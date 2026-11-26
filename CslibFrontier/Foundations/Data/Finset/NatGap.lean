/-
Copyright (c) 2026 Vincent Palma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma
-/

module
-- upstream: candidate (Mathlib, finset gaps)

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Max

/-!
# Gaps in finite sets of natural numbers

A finite set admits a threshold separating its elements by any prescribed gap, with the
threshold bounded by the gap width times the number of elements.

## Main results

* `Finset.exists_gap_le_mul_card`: find a bounded threshold such that every element lies at
  least the prescribed distance below it or strictly above it.
-/

public section

namespace Finset

/-- A finite set of natural numbers has a threshold at most `d * s.card` such that every element
lies at least `d` below the threshold or strictly above it. -/
theorem exists_gap_le_mul_card (s : Finset ℕ) (d : ℕ) :
    ∃ D ≤ d * s.card, ∀ t ∈ s, t + d ≤ D ∨ D < t := by
  induction s using Finset.induction_on_max with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert m s hm ih =>
    rw [card_insert_of_notMem fun h => lt_irrefl m (hm m h), Nat.mul_succ]
    by_cases h : m ≤ d * s.card
    · exact ⟨d * s.card + d, le_rfl, (forall_mem_insert _ _ _).2 ⟨Or.inl (by omega),
        fun t ht => Or.inl (Nat.add_le_add_right ((hm t ht).le.trans h) d)⟩⟩
    · obtain ⟨D, hD, hgap⟩ := ih
      exact ⟨D, hD.trans (Nat.le_add_right _ _),
        (forall_mem_insert _ _ _).2 ⟨Or.inr (hD.trans_lt (not_le.1 h)), hgap⟩⟩

end Finset
