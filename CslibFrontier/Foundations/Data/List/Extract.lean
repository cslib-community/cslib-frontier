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
adjacent factors concatenate to the factor spanning both (`List.extract_append_extract`), a factor
is an infix (`List.extract_isInfix`), and a factor of a factor is a factor
(`List.extract_extract`).
Proofs about factors of words, such as matched pushes and pops of a run or the factors of a
concatenation of languages, split a factor at an intermediate position with it.

## Main results

* `List.extract_append_extract`: `l.extract a b ++ l.extract b c = l.extract a c` for
  `a ≤ b ≤ c`.
* `List.extract_extract`: `(l.extract a b).extract c d = l.extract (a + c) (a + d)` for
  `a + d ≤ b`.
* `List.extract_append_left`, `List.extract_append_right`: factors of an append that lie in one
  of its parts.
* `List.getElem?_extract`, `List.mem_extract_iff_getElem?`: the entries of a factor by position.
-/

public section

namespace List

/-- Two adjacent factors of a list concatenate to the factor spanning both. -/
theorem extract_append_extract {α : Type*} (l : List α) {a b c : ℕ} (hab : a ≤ b)
    (hbc : b ≤ c) : l.extract a b ++ l.extract b c = l.extract a c := by
  simp only [extract_eq_take_drop]
  rw [show c - a = (b - a) + (c - b) by omega, take_add, drop_drop, Nat.add_sub_cancel' hab]

/-- A prefix of a factor is a factor. -/
theorem take_extract {α : Type*} (l : List α) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (l.extract a c).take (b - a) = l.extract a b := by
  simp only [extract_eq_take_drop, take_take]
  rw [Nat.min_eq_left (by omega)]

/-- The factor of length one at a position is the entry there. -/
theorem extract_eq_singleton {α : Type*} {l : List α} {a : ℕ} {x : α} (h : l[a]? = some x) :
    l.extract a (a + 1) = [x] := by
  obtain ⟨ha, rfl⟩ := getElem?_eq_some_iff.mp h
  rw [extract_eq_take_drop, drop_eq_getElem_cons ha, Nat.add_sub_cancel_left]
  rfl

/-- Entry `k` of the factor from position `a` is entry `a + k` of the list. -/
theorem getElem?_extract {α : Type*} (l : List α) {a b k : ℕ} (hk : k < b - a) :
    (l.extract a b)[k]? = l[a + k]? := by
  simp [extract_eq_take_drop, hk]

/-- The entries of a factor are the entries of the list at the positions inside it. -/
theorem mem_extract_iff_getElem? {α : Type*} {l : List α} {a b : ℕ} {x : α} :
    x ∈ l.extract a b ↔ ∃ k, a ≤ k ∧ k < b ∧ l[k]? = some x := by
  rw [mem_iff_getElem?]
  constructor
  · rintro ⟨k, hk⟩
    rw [extract_eq_take_drop, getElem?_take] at hk
    split_ifs at hk with hkb
    rw [getElem?_drop] at hk
    exact ⟨a + k, by omega, by omega, hk⟩
  · rintro ⟨k, hak, hkb, hk⟩
    exact ⟨k - a, by rw [l.getElem?_extract (by omega), Nat.add_sub_cancel' hak, hk]⟩

/-- A factor of a list is an infix of it. -/
theorem extract_isInfix {α : Type*} (l : List α) (a b : ℕ) : l.extract a b <:+: l := by
  rw [extract_eq_take_drop]
  exact (take_prefix _ _).isInfix.trans (drop_suffix _ _).isInfix

/-- A factor of a factor of a list is a factor of the list. -/
theorem extract_extract {α : Type*} (l : List α) {a b c d : ℕ} (h : a + d ≤ b) :
    (l.extract a b).extract c d = l.extract (a + c) (a + d) := by
  simp only [extract_eq_take_drop, drop_take, take_take, drop_drop]
  congr 1
  omega

/-- Shifting both ends of a factor past a new head. -/
theorem extract_cons_succ {α : Type*} (x : α) (l : List α) (a b : ℕ) :
    (x :: l).extract (a + 1) (b + 1) = l.extract a b := by
  simp [extract]

/-- A factor of the right part of an append, with positions shifted by the left part. -/
theorem extract_append_left {α : Type*} (l l' : List α) (a b : ℕ) :
    (l ++ l').extract (l.length + a) (l.length + b) = l'.extract a b := by
  rw [extract_eq_take_drop, extract_eq_take_drop, drop_append, drop_of_length_le (by omega),
    nil_append, show l.length + a - l.length = a by omega,
    show l.length + b - (l.length + a) = b - a by omega]

/-- A factor that ends inside the left part of an append is a factor of the left part. -/
theorem extract_append_right {α : Type*} (l l' : List α) {a b : ℕ} (hb : b ≤ l.length) :
    (l ++ l').extract a b = l.extract a b := by
  rw [extract_eq_take_drop, extract_eq_take_drop]
  by_cases ha : a ≤ l.length
  · rw [drop_append_of_le_length ha, take_append_of_le_length (by simp; omega)]
  · rw [show b - a = 0 by omega, take_zero, take_zero]

end List
