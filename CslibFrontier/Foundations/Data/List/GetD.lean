/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/GetD.lean`)

public import CslibFrontier.Init
import Mathlib.Data.List.GetD

/-!
# Defaulted lookups

A defaulted lookup `l.getD i d` at an index `i < l.length` returns an entry of `l`. Statements
that read lists with `getD` use this to apply a property of all entries; the general case, where
the lookup may return the default, is `List.getD_mem_or`.

A lookup at a wire number `v`, counted from `1`, reads the same entry when `v` is first capped at
one past the length of the list: every index at or beyond the length reads the default. Programs
that receive `v` in binary cap it this way to bound it by the list.

## Main results

* `List.getD_mem`: `l.getD i d ∈ l` for `i < l.length`.
* `List.getD_map_of_lt`: `(l.map f).getD i d₁ = f (l.getD i d₀)` for `i < l.length`.
* `List.getD_min_length_succ_sub_one`: capping the index at one past the end changes no lookup.
* `List.getD_append_replicate`: padding with copies of the default changes no lookup.
-/

public section

namespace List

/-- An in-range defaulted lookup returns an entry of the list, whatever the default. -/
theorem getD_mem {α : Type*} (d : α) {l : List α} {i : ℕ} (hi : i < l.length) :
    l.getD i d ∈ l := by
  rw [getD_eq_getElem _ _ hi]
  exact getElem_mem hi

/-- An in-range defaulted lookup on `l.map f` applies `f` to `l.getD i d₀`, whatever the
defaults. -/
theorem getD_map_of_lt {α β : Type*} (f : α → β) (l : List α) (d₀ : α) (d₁ : β)
    {i : ℕ} (hi : i < l.length) :
    (l.map f).getD i d₁ = f (l.getD i d₀) := by
  rw [getD_eq_getElem _ _ (by simp [hi]), getElem_map, getD_eq_getElem _ _ hi]

/-- Capping a wire number `v`, counted from `1`, at one past the end of the list changes no
defaulted lookup: indices at or beyond the length all read the default. -/
theorem getD_min_length_succ_sub_one {α : Type*} (l : List α) (d : α) (v : ℕ) :
    l.getD (min (l.length + 1) v - 1) d = l.getD (v - 1) d := by
  rcases Nat.le_total (l.length + 1) v with h | h
  · rw [Nat.min_eq_left h, Nat.add_sub_cancel, getD_eq_default _ _ (Nat.le_refl _),
      getD_eq_default _ _ (by omega)]
  · rw [Nat.min_eq_right h]

/-- Padding a list with copies of the default changes no defaulted lookup. -/
theorem getD_append_replicate {α : Type*} (l : List α) (d : α) (m j : ℕ) :
    (l ++ replicate m d).getD j d = l.getD j d := by
  rcases Nat.lt_or_ge j l.length with h | h
  · exact getD_append _ _ _ _ h
  · rw [getD_append_right _ _ _ _ h, getD_eq_default _ _ h]
    rcases Nat.lt_or_ge (j - l.length) m with h' | h'
    · exact getD_replicate d h'
    · exact getD_eq_default _ _ (by simpa using h')

end List
