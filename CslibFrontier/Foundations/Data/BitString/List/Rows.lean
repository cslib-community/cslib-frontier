/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List

/-!
# Flattening and replacing fixed-width rows of bit lists

Splitting a bit list of length `count * width` into `count` rows of width `width` via
`Cslib.BitString.listRows` and concatenating the rows recovers the original list, and replacing a
row via `Cslib.BitString.replaceRow` with a `width`-bit word produces a `count * width`-bit list.

## Main results

* `Cslib.BitString.flatten_listRows_of_length`: `(listRows count width w).flatten = w` when
  `w.length = count * width`.
* `Cslib.BitString.length_replaceRow`: `(replaceRow width count j x word).length = count * width`
  when `x.length = width`.
-/

public section

namespace Cslib.BitString

/-- Splitting a list of length `count * width` into `count` rows of width `width` and flattening
the rows recovers the original list. -/
theorem flatten_listRows_of_length {count width : ℕ} {w : List Bool}
    (hw : w.length = count * width) :
    (listRows count width w).flatten = w := by
  have heq : w = List.ofFn (ofList (count * width) w) := (ofFn_ofList hw).symm
  conv_lhs => rw [heq, listRows_ofFn, ← ofFn_blocksEquiv_symm]
  simp [blocksEquiv_symm_block, ← heq]

/-- Replacing one fixed-width row with a `width`-bit word produces a `count * width`-bit list. -/
@[simp] theorem length_replaceRow {width count j : ℕ} {x : List Bool} (hx : x.length = width)
    (word : List Bool) :
    (replaceRow width count j x word).length = count * width := by
  unfold replaceRow
  induction count with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton]
    split_ifs <;> simp [hx, Nat.succ_mul]

end Cslib.BitString
