/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List

/-!
# Flattening fixed-width rows of bit lists

Splitting a bit list of length `count * width` into `count` rows of width `width` via
`Cslib.BitString.listRows` and concatenating the rows recovers the original list.

## Main results

* `Cslib.BitString.flatten_listRows_of_length`: `(listRows count width w).flatten = w` when
  `w.length = count * width`.
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

end Cslib.BitString
