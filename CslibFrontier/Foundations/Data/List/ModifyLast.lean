/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/ModifyLast.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.List.ModifyLast

/-!
# Length and entries of `List.modifyLast`

`List.modifyLast f l` applies `f` to the last entry of `l` and leaves the others alone. This file
records the two facts that index-wise arguments about it need: the length is unchanged, and the
entry at position `i` is `f l[i]` when `i` is the last position and `l[i]` otherwise. Both follow
from Mathlib's `List.modifyLast_concat`.

## Main results

* `List.length_modifyLast`: `(l.modifyLast f).length = l.length`.
* `List.getElem_modifyLast`: the entry at `i` is `f l[i]` if `i + 1 = l.length`, else `l[i]`.
-/

public section

namespace List

variable {α : Type*}

@[simp]
theorem length_modifyLast (f : α → α) (l : List α) : (l.modifyLast f).length = l.length := by
  rcases eq_nil_or_concat l with rfl | ⟨init, a, rfl⟩
  · rfl
  · simp [concat_eq_append, modifyLast_concat]

/-- `List.modifyLast f` changes only the last entry, where it applies `f`. -/
theorem getElem_modifyLast (f : α → α) (l : List α) {i : ℕ} (hi : i < (l.modifyLast f).length) :
    (l.modifyLast f)[i] =
      if i + 1 = l.length then f (l[i]'(by simpa using hi)) else l[i]'(by simpa using hi) := by
  rcases eq_nil_or_concat l with rfl | ⟨init, a, rfl⟩
  · simp at hi
  · simp only [concat_eq_append, modifyLast_concat, length_append, length_singleton,
      Nat.add_right_cancel_iff]
    by_cases h : i < init.length
    · simp [getElem_append_left h, show i ≠ init.length by omega]
    · have hi' : i = init.length := by simp at hi; omega
      subst hi'
      simp

end List
