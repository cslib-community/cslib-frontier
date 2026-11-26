/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Batteries.Data.List.Perm
import Mathlib.Data.List.TakeDrop

/-!
# Adjacent exchange and mapping

These characterizations use the existing total `List.swap`; out-of-range exchanges retain
all data. They connect stable sorting traces to their accompanying value words.
-/

public section

namespace List

/-- An adjacent exchange has the usual take/two-entries/drop form, with whole-list identity
when the second position is out of range. -/
theorem swap_adjacent_eq_take_drop {α : Type*} (xs : List α) (j : ℕ) :
    xs.swap j (j+1) = if h : j+1<xs.length then
      xs.take j ++ [xs[j+1], xs[j]'(by omega)] ++ xs.drop (j+2) else xs := by
  induction j generalizing xs with
  | zero =>
    match xs with
    | [] | [_] | _ :: _ :: _ => simp [List.swap]
  | succ j ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      rw [List.swap_cons, ih]
      by_cases h : j+1<xs.length <;>
        simp [h, List.take_succ_cons, List.drop_succ_cons]

/-- Mapping a payload commutes with the existing total exchange, including its invalid
index identity branches. -/
theorem map_swap {α β : Type*} (f : α → β) (xs : List α) (i j : ℕ) :
    (xs.swap i j).map f = (xs.map f).swap i j := by
  by_cases hi : i<xs.length <;> by_cases hj : j<xs.length <;>
    simp [List.swap_eq, hi, hj, List.map_set]

end List
