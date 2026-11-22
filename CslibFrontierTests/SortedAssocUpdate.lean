/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.Data.List.SortedAssoc.Update

/-!
# Sorted association list update examples

Checked examples for the comparator-polymorphic insert and erase scans of `Cslib.SortedAssoc`:
their pure instances on a sorted list, and a list that is not sorted, on which the erase scan
removes one entry where the model function removes every entry with the key.
-/

public section

namespace CslibFrontierTests.SortedAssocUpdate

open Cslib Cslib.SortedAssoc

/-! ### Insertion -/

example : Id.run (insertM leI 3 "c" [(1, "a"), (5, "e")]) = [(1, "a"), (3, "c"), (5, "e")] := by
  decide
example : Id.run (insertM leI 5 "z" [(1, "a"), (5, "e")]) = [(1, "a"), (5, "z")] := by decide
example : Id.run (insertM leI 9 "i" [(1, "a"), (5, "e")]) = [(1, "a"), (5, "e"), (9, "i")] := by
  decide
example : Id.run (insertM leI 1 "a" ([] : List (ℕ × String))) = [(1, "a")] := by decide

/-! ### Erasure -/

example : Id.run (eraseM leI 5 [(1, "a"), (5, "e")]) = [(1, "a")] := by decide
example : Id.run (eraseM leI 3 [(1, "a"), (5, "e")]) = [(1, "a"), (5, "e")] := by decide
example : Id.run (eraseM leI 1 ([] : List (ℕ × String))) = [] := by decide

/-- The scans are the model functions: insertion on any list, erasure on a sorted one. -/
example :
    Id.run (insertM leI 3 "c" [(5, "e"), (1, "a")]) = insert 3 "c" [(5, "e"), (1, "a")] ∧
      Id.run (eraseM leI 5 [(1, "a"), (5, "e")]) = SortedAssoc.erase 5 [(1, "a"), (5, "e")] :=
  ⟨idRun_insertM 3 "c" _, idRun_eraseM (by decide) 5⟩

/-- Sortedness is needed: the scan removes one entry, the model removes every entry with the
key. -/
example :
    Id.run (eraseM leI 3 [(3, "x"), (1, "a"), (3, "y")]) = [(1, "a"), (3, "y")] ∧
      SortedAssoc.erase 3 [(3, "x"), (1, "a"), (3, "y")] = [(1, "a")] := by
  decide

end CslibFrontierTests.SortedAssocUpdate
