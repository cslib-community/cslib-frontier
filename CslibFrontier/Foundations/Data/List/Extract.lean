/-
Copyright (c) 2026 Samuel Schlesinger, Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Sparsa Roychowdhury
-/

module
-- upstream: candidate (Lean core, `Init/Data/List/Nat/TakeDrop.lean`)

public import CslibFrontier.Init

/-!
# Adjacent factors of a list

`List.extract l a b` is the factor of `l` from position `a` (included) to `b` (excluded). Two
adjacent factors concatenate to the factor spanning both (`List.extract_append_extract`).
Proofs about factors of words, such as matched pushes and pops of a run or the factors of a
concatenation of languages, split a factor at an intermediate position with it.

## Main results

* `List.extract_append_extract`: `l.extract a b ++ l.extract b c = l.extract a c` for
  `a ≤ b ≤ c`.
-/

public section

namespace List

/-- Two adjacent factors of a list concatenate to the factor spanning both. -/
theorem extract_append_extract {α : Type*} (l : List α) {a b c : ℕ} (hab : a ≤ b)
    (hbc : b ≤ c) : l.extract a b ++ l.extract b c = l.extract a c := by
  simp only [extract_eq_take_drop]
  rw [show c - a = (b - a) + (c - b) by omega, take_add, drop_drop, Nat.add_sub_cancel' hab]

end List
