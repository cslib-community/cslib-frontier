/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Search.Frontier

/-!
# Tests for search frontiers

* The sorted-list frontier is lawful at concrete key and element types, including an infinite
  key type.
* Inserting `3, 1, 2` and popping returns the elements in order of key, then fails on the empty
  frontier.
* Among equal keys, the sorted-list frontier pops the most recently inserted element first (a
  property of this implementation, not of the specification).
-/

namespace CslibFrontierTests.Algorithms.Lean.Search.Frontier

open Cslib.Algorithms.Lean.Search

/-- The sorted-list frontier with natural-number keys and string elements. -/
abbrev F : Frontier (SortedListFrontier ℕ String) ℕ String := Frontier.sortedList

/-! ### The specification holds -/

example : F.Lawful := Frontier.lawful_sortedList

example :
    (Frontier.sortedList : Frontier (SortedListFrontier ℤ (List Bool)) ℤ (List Bool)).Lawful :=
  Frontier.lawful_sortedList

/-! ### Pops come out in order of key -/

/-- The frontier holding `c`, `a`, `b` with keys `3`, `1`, `2`, inserted in that order. -/
def cab : SortedListFrontier ℕ String := F.insert 2 "b" (F.insert 1 "a" (F.insert 3 "c" F.empty))

example : cab.toList = [(1, "a"), (2, "b"), (3, "c")] := by decide

example : (F.popMin? cab).map Prod.fst = some "a" := by decide

example : ((F.popMin? cab).bind fun p => F.popMin? p.2).map Prod.fst = some "b" := by decide

/-- Three pops empty the frontier and a fourth fails. -/
example :
    ((F.popMin? cab).bind fun p => (F.popMin? p.2).bind fun p => (F.popMin? p.2).bind fun p =>
      F.popMin? p.2) = none := by
  decide

/-- The contents are the inserted keyed elements. -/
example : F.contents cab = {(1, "a"), (2, "b"), (3, "c")} := by decide

/-! ### Tie-breaking of the reference implementation -/

/-- With equal keys, the last inserted element is popped first. -/
example : (F.popMin? (F.insert 0 "new" (F.insert 0 "old" F.empty))).map Prod.fst = some "new" := by
  decide

end CslibFrontierTests.Algorithms.Lean.Search.Frontier
