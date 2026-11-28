/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib Logic/Function/Basic)

public import CslibFrontier.Init
public import Mathlib.Logic.Function.Basic

/-!
# Pointwise evaluation and kernel lemmas for `Function.update`

Updating the identity at `b` to `a` identifies just those two points without requiring
distinctness, finiteness or injectivity (`Function.update_id_apply_eq_iff`), and updating entry
`(a, b)` of a two-argument function leaves every other pair of arguments unchanged
(`Function.update_update_apply_of_ne`).
-/

public section

namespace Function

/-- A one-point update of the identity equates precisely equal points or the selected pair. -/
theorem update_id_apply_eq_iff {α : Sort*} [DecidableEq α] (a b x y : α) :
    update id b a x = update id b a y ↔
      x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  by_cases hx : x = b <;> by_cases hy : y = b <;>
    simp only [update_apply, hx, hy, ite_true, ite_false, id_eq] <;> grind

/-- Updating entry `(a, b)` of a two-argument function leaves every other entry unchanged. -/
theorem update_update_apply_of_ne {α β γ : Sort*} [DecidableEq α] [DecidableEq β]
    {f : α → β → γ} {a x : α} {b y : β} {val : γ} (h : ¬(x = a ∧ y = b)) :
    update f a (update (f a) b val) x y = f x y := by
  by_cases hx : x = a
  · subst hx
    simp [show y ≠ b from fun hy => h ⟨rfl, hy⟩]
  · simp [hx]

end Function
