/-
Copyright (c) 2026 Paulo Matos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paulo Matos
-/

module
-- upstream: candidate

public import CslibFrontier.Init
-- `import all` to unfold `List.toChunks` and its loop `List.toChunks.go`, whose bodies Batteries
-- does not expose and about which it states no lemmas.
import all Batteries.Data.List.Basic

/-!
# Chunks of a list

Batteries' `List.toChunks n l` cuts `l` into consecutive chunks of `n` elements, in order; the last
chunk may be shorter, and `n = 0` gives the whole list as one chunk. Batteries states no lemmas
about it. This file proves its two basic contracts through the accumulator loop `toChunks.go`.

## Main results

* `List.flatten_toChunks`: the chunks flatten back to the list.
* `List.length_pos_and_le_of_mem_toChunks`: for `0 < n`, every chunk has between `1` and `n`
  elements.
-/

public section

namespace List

variable {α : Type*}

private theorem flatten_toChunks_go (n : ℕ) (l : List α) (acc₁ : Array α)
    (acc₂ : Array (List α)) :
    (toChunks.go n l acc₁ acc₂).flatten = acc₂.toList.flatten ++ acc₁.toList ++ l := by
  induction l generalizing acc₁ acc₂ with
  | nil => simp [toChunks.go]
  | cons x xs ih =>
    rw [toChunks.go]
    split <;> simp [ih]

/-- The chunks flatten back to the list. -/
@[simp] theorem flatten_toChunks (n : ℕ) (l : List α) : (l.toChunks n).flatten = l := by
  match n, l with
  | _, [] => simp [toChunks]
  | 0, x :: xs => simp [toChunks]
  | k + 1, x :: xs => simp [toChunks, flatten_toChunks_go]

private theorem length_of_mem_toChunks_go {n : ℕ} (hn : 0 < n) (l : List α) (acc₁ : Array α)
    (acc₂ : Array (List α)) (h₁ : 0 < acc₁.size ∧ acc₁.size ≤ n)
    (h₂ : ∀ c ∈ acc₂.toList, 0 < c.length ∧ c.length ≤ n) :
    ∀ c ∈ toChunks.go n l acc₁ acc₂, 0 < c.length ∧ c.length ≤ n := by
  induction l generalizing acc₁ acc₂ with
  | nil =>
    simp only [toChunks.go, Array.toList_push, mem_append, mem_singleton]
    rintro c (hc | rfl)
    · exact h₂ c hc
    · simpa using h₁
  | cons x xs ih =>
    rw [toChunks.go]
    split
    · refine ih _ _ (by simp; omega) fun c hc => ?_
      simp only [Array.toList_push, mem_append, mem_singleton] at hc
      rcases hc with hc | rfl
      · exact h₂ c hc
      · simpa using h₁
    · rename_i hne
      refine ih _ _ ?_ h₂
      simp only [beq_iff_eq] at hne
      simp only [Array.size_push]
      omega

/-- For `0 < n`, every chunk has between `1` and `n` elements. -/
theorem length_pos_and_le_of_mem_toChunks {n : ℕ} (hn : 0 < n) {l c : List α}
    (hc : c ∈ l.toChunks n) : 0 < c.length ∧ c.length ≤ n := by
  match n, l, hn with
  | _, [], _ => simp [toChunks] at hc
  | k + 1, x :: xs, hn =>
    exact length_of_mem_toChunks_go hn xs #[x] #[] (by simp) (by simp) c
      (by simpa [toChunks] using hc)

end List
