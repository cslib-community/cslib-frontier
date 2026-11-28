/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/Countdown.lean`)

public import CslibFrontier.Init
import Mathlib.Data.List.GetD

/-!
# Counting down to a mapped list element

`List.foldl_countdown` describes a left fold that decrements a counter and captures a mapped
element when the counter reaches one. A zero counter preserves the captured value. This lets
streaming input readers share the same selection argument across symbol representations.
-/

public section

namespace List

/-- Counting down from `k` captures the mapped element at position `k - 1` if `k` is positive
and at most the list length; otherwise it preserves `cur`. The counter saturates at zero. -/
theorem foldl_countdown {α β : Type*} (f : α → β) (l : List α) (k : ℕ) (cur : β) (d : α) :
    l.foldl (fun p a => (p.1 - 1, if p.1 = 1 then f a else p.2)) (k, cur) =
      (k - l.length, if 0 < k ∧ k ≤ l.length then f (l.getD (k - 1) d) else cur) := by
  induction l generalizing k cur with
  | nil => simp; omega
  | cons a l ih =>
    rw [foldl_cons, ih]
    rcases k with _ | (_ | k)
    · simp
    · simp
    · simp only [Nat.add_one_sub_one, length_cons, Nat.succ_pos, true_and, getD_cons_succ]
      refine Prod.ext (by omega) ?_
      split_ifs <;> first | rfl | omega

end List
