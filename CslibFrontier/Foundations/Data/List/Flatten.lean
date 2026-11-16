/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/Flatten.lean`)

public import CslibFrontier.Init

/-!
# Block boundaries in a flattened list

A list of blocks `L : List (List α)`, flattened, is read from left to right one block at a time.
Block `j` starts at the length of the first `j` blocks flattened: dropping that many entries leaves
block `j` followed by the later blocks (`List.drop_flatten_take`), and the boundary after block `j`
is the one before it plus the length of block `j` (`List.length_flatten_take_succ`). Mathlib's
`List.drop_sum_flatten` is a weaker form of the first fact: with the boundary written as a sum of
block lengths, dropping that many entries leaves `(L.drop j).flatten`, without block `j` split
off.

## Main results

* `List.drop_flatten_take`: the flattened list from the start of block `j`.
* `List.length_flatten_take_succ`: the boundary after block `j`.
-/

public section

namespace List

variable {α : Type*}

/-- Dropping the first `j` blocks of a flattened list leaves block `j` followed by the later
blocks. -/
theorem drop_flatten_take (L : List (List α)) {j : ℕ} (hj : j < L.length) :
    L.flatten.drop (L.take j).flatten.length = L[j] ++ (L.drop (j + 1)).flatten := by
  calc L.flatten.drop (L.take j).flatten.length
      = ((L.take j).flatten ++ (L.drop j).flatten).drop (L.take j).flatten.length := by
        rw [← flatten_append, take_append_drop]
    _ = (L.drop j).flatten := drop_left
    _ = L[j] ++ (L.drop (j + 1)).flatten := by
        rw [drop_eq_getElem_cons hj, flatten_cons]

/-- The first `j + 1` blocks of a list, flattened, are as long as the first `j` and block `j`
together. -/
theorem length_flatten_take_succ (L : List (List α)) {j : ℕ} (hj : j < L.length) :
    (L.take (j + 1)).flatten.length = (L.take j).flatten.length + L[j].length := by
  rw [take_succ_eq_append_getElem hj, flatten_append, length_append]
  simp

end List
