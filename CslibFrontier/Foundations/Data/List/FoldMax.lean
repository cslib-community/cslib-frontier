/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Order.Defs.LinearOrder

/-!
# Order bounds for `List.foldl max`

## Main results

* `List.le_foldl_max_self`: folding `max` never decreases the initial accumulator.
* `List.mem_le_foldl_max`: every element of `l` is bounded above by `l.foldl max a`.
* `List.foldl_max_le`: `l.foldl max a ≤ b` whenever `a ≤ b` and every element of `l` is `≤ b`.
-/

public section

namespace List

section LinearOrder

variable {α : Type*} [LinearOrder α]

/-- Folding `max` across `l` never decreases the initial accumulator `a`. -/
theorem le_foldl_max_self : ∀ (l : List α) (a : α), a ≤ l.foldl max a
  | [], _ => le_rfl
  | x :: xs, a => (le_max_left a x).trans (le_foldl_max_self xs (max a x))

/-- Every element of `l` is bounded above by `l.foldl max a`. -/
theorem mem_le_foldl_max {l : List α} {a x : α} (hx : x ∈ l) : x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => nomatch hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right a x).trans (le_foldl_max_self ys _)
    · exact ih hx

/-- `l.foldl max a ≤ b` whenever `a ≤ b` and every element of `l` is at most `b`. -/
theorem foldl_max_le {l : List α} {a b : α} (ha : a ≤ b) (hl : ∀ x ∈ l, x ≤ b) :
    l.foldl max a ≤ b := by
  induction l generalizing a with
  | nil => exact ha
  | cons y ys ih =>
    exact ih (max_le ha (hl y List.mem_cons_self)) fun x hx =>
      hl x (List.mem_cons_of_mem y hx)

end LinearOrder

end List
