/-
Copyright (c) 2026 Paulo Matos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Matos
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Cutting a list into chunks

`List.chunks B l` cuts `l` into consecutive chunks of `max 1 B` elements, in order; the last chunk
may be shorter. Each chunk is built with `List.take` and the rest of the list with `List.drop`.
Unlike Batteries' `List.toChunks`, it works on lists throughout and treats `B = 0` as `B = 1`.

## Main definitions

* `List.chunks`: consecutive chunks of `max 1 B` elements.

## Main results

* `List.flatten_chunks`: the chunks flatten back to the list.
* `List.length_pos_and_le_of_mem_chunks`: every chunk has between `1` and `max 1 B` elements.
-/

public section

namespace List

variable {α : Type*}

/-- Cut a list into consecutive chunks of `max 1 B` elements; the last may be shorter. -/
@[expose] def chunks (B : ℕ) : List α → List (List α)
  | [] => []
  | x :: xs => (x :: xs.take (B - 1)) :: chunks B (xs.drop (B - 1))
termination_by xs => xs.length

/-- Chunking keeps the elements in order. -/
@[simp] theorem flatten_chunks (B : ℕ) (l : List α) : (l.chunks B).flatten = l := by
  induction l using chunks.induct B with
  | case1 => simp [chunks]
  | case2 x xs ih => simp [chunks, ih]

/-- Every chunk has between `1` and `max 1 B` elements. -/
theorem length_pos_and_le_of_mem_chunks {B : ℕ} {l c : List α} (hc : c ∈ l.chunks B) :
    0 < c.length ∧ c.length ≤ max 1 B := by
  induction l using chunks.induct B with
  | case1 => simp [chunks] at hc
  | case2 x xs ih =>
    rw [chunks, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only [List.length_cons, List.length_take]; omega
    · exact ih hc

end List
