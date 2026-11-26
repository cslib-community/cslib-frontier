/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Assemble
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Lookup
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Search
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.Registers

/-!
# Binary search as a structured pointer-machine program

`Structured.search` searches a linked tree for the key in data register zero and returns the
matching node in pointer register zero, or null. It meets the specification `SearchResult` of
`Search`.

Structured programs have no jump out of a loop, so a successful search leaves the loop by
copying the cursor into the register that the loop compares it with, pointer register five.

The proof follows the program: the loop is unfolded once per node by induction on the tree, the
step is executed symbolically, and what the program leaves unchanged is read off its text.

## Main results

* `search_correct`: the search implements `SearchTree.contains` within
  `7 * searchVisits + 3` instructions.
* `search_executes`: its assembled program halts within `7 * searchVisits + 4` instructions.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine.Structured

open Cslib.PointerMachine

variable {M : Model} {extra regs : ℕ}

open Register in
/-- One step of the search: move the cursor to the child on the side of the key searched for,
or stop at a node with that key. -/
@[expose] def searchStep (lt : M.Test) : Code M (layout extra regs) := pm[
  here := cur[key];
  if lt query here then [ cur ← cur[left] ] else [
    if lt here query then [ cur ← cur[right] ] else [ stop ← cur ] ] ]

open Register in
/-- Search from pointer register zero for the key in data register zero. Pointer register five
and data register one are temporary. -/
@[expose] def search (lt : M.Test) : Code M (layout extra regs) := pm[
  stop ← null;
  while cur ≠ stop do [ ⟪searchStep lt⟫ ] ]

variable [LinearOrder M.Value] (lt : M.Test)
    (compare : ∀ a b, M.evalTest lt a b = decide (a < b))

include compare

/-- The cursor of `y` is at a node of `t` with key `q`, if there is one, and is null otherwise. -/
private def Found (q : M.Value) (t : BinaryTree (Label M extra))
    (y : State M (layout extra regs)) : Prop :=
  (y.ptr 0).isSome = contains q (keys t) ∧
    ∀ a, y.ptr 0 = some a →
      ∃ path label, t.get path = some label ∧ label.address = a ∧ label.data 0 = q

/-- The loop, from the root of a represented subtree. -/
private theorem loop (t : BinaryTree (Label M extra)) (x : State M (layout extra regs))
    (parent : Pointer) (rep : Represents x.heap parent t) (cursor : x.ptr 0 = root t)
    (nil : x.ptr 5 = none) :
    WP (.loopUntil (.ptrEq 0 5) (searchStep lt)) x fun y n =>
      n ≤ 7 * searchVisits (x.data 0) (keys t) + 2 ∧ Found (x.data 0) t y := by
  induction t generalizing x parent with
  | nil =>
    exact Program.WP.loopUntil_exit (by simp [pm_simps, cursor, nil, root])
      ⟨by omega, by rw [cursor]; rfl, by simp [cursor, root]⟩
  | node a l r il ir =>
    have read : x.deref 0 = some (record (root l) (root r) parent a) := by
      simpa [State.deref, cursor, root] using rep.1
    refine Program.WP.loopUntil_iter (by simp [pm_simps, cursor, nil, root]) ?_
    by_cases less : x.data 0 < a.data 0
    · pm_exec [searchStep, read, record, compare, less]
      refine (il _ (some a.address) (by exact rep.2.1) (by simp) (by simp [nil])).mono ?_
      rintro y n ⟨time, found, key⟩
      refine ⟨?_, by simpa [keys, BinaryTree.map, contains, less] using found, fun b hb => ?_⟩
      · simp [keys, BinaryTree.map, searchVisits, less] at time ⊢; omega
      · obtain ⟨path, label, get, address, same⟩ := key b hb
        exact ⟨.bit0 path, label, get, address, by simpa using same⟩
    · by_cases greater : a.data 0 < x.data 0
      · pm_exec [searchStep, read, record, compare, less, greater]
        refine (ir _ (some a.address) (by exact rep.2.2) (by simp)
          (by simp [nil])).mono ?_
        rintro y n ⟨time, found, key⟩
        refine ⟨?_, by simpa [keys, BinaryTree.map, contains, less, greater] using found,
          fun b hb => ?_⟩
        · simp [keys, BinaryTree.map, searchVisits, less, greater] at time ⊢; omega
        · obtain ⟨path, label, get, address, same⟩ := key b hb
          exact ⟨.bit1 path, label, get, address, by simpa using same⟩
      · pm_exec [searchStep, read, record, compare, less, greater]
        refine Program.WP.loopUntil_exit (by simp [pm_simps]) ⟨?_, ?_, fun b hb => ?_⟩
        · simp only [keys, BinaryTree.map, searchVisits, less, greater, ↓reduceIte]
          omega
        · simp [keys, BinaryTree.map, contains, less, greater, cursor, root]
        · exact ⟨.one, a, rfl, by simpa [cursor, root] using hb,
            le_antisymm (le_of_not_gt less) (le_of_not_gt greater)⟩

/-- The search implements `SearchTree.contains`, within seven instructions per visited node plus
three for clearing the stop register, stopping at the key and leaving the loop. -/
theorem search_correct (x : State M (layout extra regs))
    (t : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents x.heap parent t) (cursor : x.ptr 0 = root t) :
    ∃ y, ExecWithin (search lt) x y (7 * searchVisits (x.data 0) (keys t) + 3) ∧
      SearchResult x y t := by
  obtain ⟨y, run, found, key⟩ :
      ∃ y, ExecWithin (search lt) x y (7 * searchVisits (x.data 0) (keys t) + 3) ∧
        Found (x.data 0) t y := by
    apply WP.exists_execWithin
    pm_exec [search]
    refine (loop lt compare t _ parent (by exact rep) (by exact cursor) rfl).mono ?_
    rintro y n ⟨time, post⟩
    exact ⟨by simp at time; omega, post⟩
  have heap := run.heap_eq (by pm_frame)
  refine ⟨y, run, heap, fun i hi => run.data_keep [1] (by pm_frame) (by simpa using hi),
    fun i h0 h5 => run.ptr_keep [0, 5] (by pm_frame) (by simp [h0, h5]), found, fun a ha => ?_⟩
  obtain ⟨path, label, get, address, same⟩ := key a ha
  obtain ⟨node, lookup, data⟩ := rep.get get
  exact ⟨path, label, node, get, address, by rw [heap, ← address]; exact lookup, data,
    by rw [data]; exact same⟩

/-- The assembled search halts within seven instructions per visited node plus four, including
the `halt`. -/
theorem search_executes (x : State M (layout extra regs))
    (t : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents x.heap parent t) (cursor : x.ptr 0 = root t) (pc : x.pc = 0) :
    ∃ y time, Executes (search lt).program x y time ∧
      time ≤ 7 * searchVisits (x.data 0) (keys t) + 4 ∧ SearchResult x y t := by
  obtain ⟨y, run, res⟩ := search_correct lt compare x t parent rep cursor
  obtain ⟨time, bound, exec⟩ := run.executes pc
  exact ⟨_, time, exec, bound, res.heap, res.data, res.ptr, res.found, res.key⟩

end Cslib.DataStructure.SearchTree.PointerMachine.Structured
