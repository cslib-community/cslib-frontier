/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Representation
public import Mathlib.Data.Tree.Get

/-!
# Binary search by a pointer-machine program

The fixed program `search` implements Frontier's `SearchTree.contains` by following
left/right links. It returns the matching node in pointer register zero, or null on failure.
Data register zero holds the query; register one is temporary. No record is changed or allocated.
A scalar predicate implementing strict key comparison is the only required primitive.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine

open Cslib.PointerMachine

variable {M : Model} {extra regs : ℕ}

/-- Search from pointer register zero for the key in data register zero. Pointer register
five is cleared for null tests; data register one is temporary. All other registers are preserved.
Both successful and unsuccessful searches terminate at explicit halt instructions. -/
@[expose] def search (lt : M.Test) : List (Instr M (layout extra regs)) :=
  [.null 5, .ifPtrEq 0 5 10, .loadData 1 0 0, .ifTest lt 0 1 6,
   .ifTest lt 1 0 8, .halt, .loadPtr 0 0 0, .goto 1, .loadPtr 0 1 0, .goto 1, .halt]

private def next (x : State M (layout extra regs)) (p : Pointer) (v : M.Value)
    (pc : ℕ) : State M (layout extra regs) :=
  { x.setPtr 0 p with data := Function.update x.data 1 v, pc }

variable [LinearOrder M.Value] (lt : M.Test)
    (compare : ∀ a b, M.evalTest lt a b = decide (a < b))

include compare

private theorem left_steps (x : State M (layout extra regs)) (n : Record M (layout extra regs))
    (pc : x.pc = 1) (nil : x.ptr 5 = none) (addr : x.ptr 0 ≠ none)
    (read : x.deref 0 = some n) (less : x.data 0 < n.data 0) :
    Runs (search lt) x (next x (n.ptr 0) (n.data 0) 1) 5 := by
  change (x.ptr 0).bind (x.heap[·]?) = some n at read
  let y := x.setData 1 (n.data 0)
  refine .head x { x with pc := 2 } _ _ ?_
    (.head _ { y with pc := 3 } _ _ ?_
      (.head _ { y with pc := 6 } _ _ ?_
        (.head _ (next x (n.ptr 0) (n.data 0) 7) _ _ ?_
          (.single ?_))))
  all_goals simp [step, search, Instr.effect, Instr.next, State.setPtr, State.setData,
    State.deref, next, y, pc, nil, addr, read, compare, less]

private theorem right_steps (x : State M (layout extra regs)) (n : Record M (layout extra regs))
    (pc : x.pc = 1) (nil : x.ptr 5 = none) (addr : x.ptr 0 ≠ none)
    (read : x.deref 0 = some n) (notLess : ¬ x.data 0 < n.data 0)
    (greater : n.data 0 < x.data 0) :
    Runs (search lt) x (next x (n.ptr 1) (n.data 0) 1) 6 := by
  change (x.ptr 0).bind (x.heap[·]?) = some n at read
  let y := x.setData 1 (n.data 0)
  refine .head x { x with pc := 2 } _ _ ?_
    (.head _ { y with pc := 3 } _ _ ?_
      (.head _ { y with pc := 4 } _ _ ?_
        (.head _ { y with pc := 8 } _ _ ?_
          (.head _ (next x (n.ptr 1) (n.data 0) 9) _ _ ?_
            (.single ?_)))))
  all_goals simp [step, search, Instr.effect, Instr.next, State.setPtr, State.setData,
    State.deref, next, y, pc, nil, addr, read, compare, notLess, greater]

private theorem found_steps (x : State M (layout extra regs)) (n : Record M (layout extra regs))
    (pc : x.pc = 1) (nil : x.ptr 5 = none) (addr : x.ptr 0 ≠ none)
    (read : x.deref 0 = some n) (equal : x.data 0 = n.data 0) :
    Runs (search lt) x (next x (x.ptr 0) (n.data 0) 5) 4 := by
  change (x.ptr 0).bind (x.heap[·]?) = some n at read
  let y := x.setData 1 (n.data 0)
  refine .head x { x with pc := 2 } _ _ ?_
    (.head _ { y with pc := 3 } _ _ ?_
      (.head _ { y with pc := 4 } _ _ ?_ (.single ?_)))
  all_goals simp [step, search, Instr.effect, Instr.next, State.setPtr, State.setData,
    State.deref, next, y, pc, nil, addr, read, compare, equal]

private theorem loop (t : BinaryTree (Label M extra))
    (x : State M (layout extra regs)) (parent : Pointer)
    (rep : Represents x.heap parent t) (cursor : x.ptr 0 = root t)
    (pc : x.pc = 1) (nil : x.ptr 5 = none) :
    ∃ p v n, n ≤ 6 * searchVisits (x.data 0) (keys t) + 1 ∧
      Runs (search lt) x (next x p v (if p.isSome then 5 else 10)) n ∧
      p.isSome = contains (x.data 0) (keys t) ∧
      (∀ a, p = some a → ∃ path label rec,
        t.get path = some label ∧ label.address = a ∧ x.heap[a]? = some rec ∧
        rec.data = label.data ∧ rec.data 0 = x.data 0) := by
  induction t generalizing x parent with
  | nil =>
    refine ⟨none, x.data 1, 1, by simp [keys], .single ?_, rfl, nofun⟩
    simp [step, search, pc, cursor, root, nil, Instr.next, Instr.effect, next, State.setPtr]
  | node a l r il ir =>
    have read : x.deref 0 = some (record (root l) (root r) parent a) := by
      simpa [State.deref, cursor, root] using rep.1
    have addr : x.ptr 0 ≠ none := by simp [cursor, root]
    by_cases less : x.data 0 < a.data 0
    · let y := next x (root l) (a.data 0) 1
      obtain ⟨p, v, n, bound, run, found, key⟩ := il y (some a.address) rep.2.1
        (by simp [y, next, State.setPtr]) rfl (by simp [y, next, State.setPtr, nil])
      have first := left_steps lt compare x _ pc nil addr read less
      refine ⟨p, v, 5 + n, ?_,
        by simpa [record, y, next, State.setPtr, Function.update_idem] using first.trans run,
        by simpa [keys, BinaryTree.map, contains, less, y, next] using found,
        fun b hb => (key b hb).elim fun path h => ⟨.bit0 path, h⟩⟩
      have b : n ≤ 6 * searchVisits (x.data 0) (keys l) + 1 := by simpa [y, next] using bound
      simp only [keys, BinaryTree.map, searchVisits, less, ↓reduceIte]
      change 5 + n ≤ 6 * (1 + searchVisits (x.data 0) (keys l)) + 1
      omega
    · by_cases greater : a.data 0 < x.data 0
      · let y := next x (root r) (a.data 0) 1
        obtain ⟨p, v, n, bound, run, found, key⟩ := ir y (some a.address) rep.2.2
          (by simp [y, next, State.setPtr]) rfl (by simp [y, next, State.setPtr, nil])
        have first := right_steps lt compare x _ pc nil addr read less greater
        refine ⟨p, v, 6 + n, ?_,
          by simpa [record, y, next, State.setPtr, Function.update_idem] using first.trans run,
          by simpa [keys, BinaryTree.map, contains, less, greater, y, next] using found,
          fun b hb => (key b hb).elim fun path h => ⟨.bit1 path, h⟩⟩
        have b : n ≤ 6 * searchVisits (x.data 0) (keys r) + 1 := by simpa [y, next] using bound
        simp only [keys, BinaryTree.map, searchVisits, less, greater, ↓reduceIte]
        change 6 + n ≤ 6 * (1 + searchVisits (x.data 0) (keys r)) + 1
        omega
      · have equal : x.data 0 = a.data 0 := le_antisymm (le_of_not_gt greater) (le_of_not_gt less)
        refine ⟨some a.address, a.data 0, 4,
          by simp [keys, BinaryTree.map, searchVisits, less, greater],
          by simpa [cursor, root, record] using found_steps lt compare x _ pc nil addr read equal,
          by simp [keys, BinaryTree.map, contains, less, greater], ?_⟩
        rintro b ⟨⟩
        exact ⟨.one, a, _, rfl, rfl, rep.1, rfl, equal.symm⟩

/-- Search returns a matching node or null and preserves the heap and every register
outside its declared cursor, null and temporary registers. -/
structure SearchResult (x y : State M (layout extra regs))
    (t : BinaryTree (Label M extra)) : Prop where
  /-- Searching neither changes records nor allocates. -/
  heap : y.heap = x.heap
  /-- All scalar registers except temporary register one are preserved. -/
  data : ∀ i, i ≠ 1 → y.data i = x.data i
  /-- All pointer registers except cursor zero and null register five are preserved. -/
  ptr : ∀ i, i ≠ 0 → i ≠ 5 → y.ptr i = x.ptr i
  /-- Nonnull output agrees with the existing functional search. -/
  found : (y.ptr 0).isSome = contains (x.data 0) (keys t)
  /-- A nonnull output belongs to this tree, with its complete scalar payload intact. -/
  key : ∀ a, y.ptr 0 = some a → ∃ path label rec,
    t.get path = some label ∧ label.address = a ∧ y.heap[a]? = some rec ∧
    rec.data = label.data ∧ rec.data 0 = x.data 0

/-- The fixed search program implements `SearchTree.contains`, with at most six
instructions per visited node plus three instructions for setup and termination.
The count includes halt and unsuccessful searches. Ordering is needed only to interpret
`contains` as set membership, not for agreement with that functional algorithm. -/
theorem search_correct (x : State M (layout extra regs))
    (t : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents x.heap parent t) (cursor : x.ptr 0 = root t) (pc : x.pc = 0) :
    ∃ y time, Executes (search lt) x y time ∧
      time ≤ 6 * searchVisits (x.data 0) (keys t) + 3 ∧ SearchResult x y t := by
  let start : State M (layout extra regs) := { x.setPtr 5 none with pc := 1 }
  obtain ⟨p, v, n, bound, run, found, key⟩ := loop lt compare t start parent rep
    (by simpa [start, State.setPtr] using cursor) rfl (by simp [start, State.setPtr])
  let finish := next start p v (if p.isSome then 5 else 10)
  refine ⟨finish, n + 2, ⟨n + 1, ?_, ?_, by omega⟩, ?_, ?_⟩
  · exact run.head _ _ _ _ (by simp [step, search, pc, start, Instr.effect, Instr.next])
  · cases p <;> simp [finish, next, search]
  · have b : n ≤ 6 * searchVisits (x.data 0) (keys t) + 1 := bound
    omega
  · refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · intro i hi; simp [finish, next, start, hi, State.setPtr]
    · intro i hi hj; simp [finish, next, start, hi, hj, State.setPtr]
    · simpa [finish, next, start, State.setPtr] using found
    · simpa [finish, next, start, State.setPtr] using key

end Cslib.DataStructure.SearchTree.PointerMachine
