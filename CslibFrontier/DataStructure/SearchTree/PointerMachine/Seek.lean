/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Context

/-!
# Searching with a parent cursor and comparison path

`seek` follows the ordinary binary-search decisions while retaining the immediate parent in
register two, including when the search reaches an empty child. Its ghost context records
ancestors and the inequalities that selected each child, for subsequent insertion proofs.
The program is read-only and uses no machine stack. This is an original implementation of
Frontier's functional search, with explicit pointer-machine instruction accounting.
-/

public section
namespace Cslib.DataStructure.SearchTree.PointerMachine
open Cslib.PointerMachine
variable {M : Model} {extra regs : ℕ}

/-- Search from cursor zero for query data register zero, retaining the parent in pointer two.
Pointer five is null scratch and data one is comparison scratch. -/
@[expose] def seek (lt : M.Test) : List (Instr M (layout extra regs)) :=
  [.null 5, .null 2, .ifPtrEq 0 5 13, .loadData 1 0 0,
   .ifTest lt 0 1 7, .ifTest lt 1 0 10, .halt,
   .movePtr 2 0, .loadPtr 0 0 0, .goto 2,
   .movePtr 2 0, .loadPtr 0 1 0, .goto 2, .halt]

/-- Every ancestor frame records the strict comparison that selected its focused child. -/
@[expose] def SearchPath [LT M.Value] (query : M.Value) : List (Frame M extra) → Prop
  | [] => True
  | .left label _ :: cs => query < label.data 0 ∧ SearchPath query cs
  | .right _ label :: cs => label.data 0 < query ∧ SearchPath query cs

private def next (x : State M (layout extra regs)) (p parent : Pointer) (v : M.Value)
    (pc : ℕ) : State M (layout extra regs) :=
  { (x.setPtr 0 p).setPtr 2 parent with data := Function.update x.data 1 v, pc }

variable [LinearOrder M.Value] (lt : M.Test)
    (compare : ∀ a b, M.evalTest lt a b = decide (a < b))
include compare

/-- An unsuccessful search path selects a vacant parent slot. The concrete comparison
with that parent's key chooses exactly the side recorded by the ghost context. -/
theorem SearchPath.vacant (s : State M (layout extra regs)) (cs : List (Frame M extra))
    (path : SearchPath (s.data 0) cs) (rep : Represents s.heap none (plug cs .nil))
    (parent : s.ptr 2 = contextParent cs) (rootReg : s.ptr 1 = root (plug cs .nil)) :
    let parentKey := ((s.deref 2).map (fun n => n.data 0)).getD (s.data 2)
    let side : Fin 2 := if M.evalTest lt (s.data 0) parentKey then 0 else 1
    (match s.ptr 2 with
      | none => s.ptr 1 = none
      | some a => ∃ par, s.heap[a]? = some par ∧
          par.ptr (if M.evalTest lt (s.data 0) (par.data 0) then 0 else 1) = none) ∧
    (match cs with
      | [] => True
      | .left _ _ :: _ => side = 0
      | .right _ _ :: _ => side = 1) := by
  have context := ((represents_plug_iff s.heap cs .nil).mp rep).2
  cases cs with
  | nil => simpa [parent, contextParent, plug, root] using rootReg
  | cons frame cs =>
    cases frame with
    | left label sibling =>
      dsimp only
      rw [parent]
      exact ⟨⟨_, context.1, by simp [root, record, compare, path.1]⟩,
        by simp [State.deref, parent, contextParent, context.1, record, compare, path.1]⟩
    | right sibling label =>
      have less : ¬ s.data 0 < label.data 0 := not_lt_of_gt path.1
      dsimp only
      rw [parent]
      exact ⟨⟨_, context.1, by simp [root, record, compare, less]⟩,
        by simp [State.deref, parent, contextParent, context.1, record, compare, less]⟩

private theorem left_steps (x : State M (layout extra regs)) (n : Record M (layout extra regs))
    (pc : x.pc = 2) (nil : x.ptr 5 = none) (addr : x.ptr 0 ≠ none)
    (read : x.deref 0 = some n) (less : x.data 0 < n.data 0) :
    Runs (seek lt) x (next x (n.ptr 0) (x.ptr 0) (n.data 0) 2) 6 := by
  change (x.ptr 0).bind (x.heap[·]?) = some n at read
  let y := x.setData 1 (n.data 0)
  refine .head x { x with pc := 3 } _ _ ?_
    (.head _ { y with pc := 4 } _ _ ?_
      (.head _ { y with pc := 7 } _ _ ?_
        (.head _ { y.setPtr 2 (x.ptr 0) with pc := 8 } _ _ ?_
          (.head _ (next x (n.ptr 0) (x.ptr 0) (n.data 0) 9) _ _ ?_
            (.single ?_)))))
  all_goals simp [step, seek, Instr.effect, Instr.next, State.setPtr, State.setData,
    State.deref, next, y, pc, nil, addr, read, compare, less, Function.update_comm]

private theorem right_steps (x : State M (layout extra regs)) (n : Record M (layout extra regs))
    (pc : x.pc = 2) (nil : x.ptr 5 = none) (addr : x.ptr 0 ≠ none)
    (read : x.deref 0 = some n) (notLess : ¬ x.data 0 < n.data 0)
    (greater : n.data 0 < x.data 0) :
    Runs (seek lt) x (next x (n.ptr 1) (x.ptr 0) (n.data 0) 2) 7 := by
  change (x.ptr 0).bind (x.heap[·]?) = some n at read
  let y := x.setData 1 (n.data 0)
  refine .head x { x with pc := 3 } _ _ ?_
    (.head _ { y with pc := 4 } _ _ ?_
      (.head _ { y with pc := 5 } _ _ ?_
        (.head _ { y with pc := 10 } _ _ ?_
          (.head _ { y.setPtr 2 (x.ptr 0) with pc := 11 } _ _ ?_
            (.head _ (next x (n.ptr 1) (x.ptr 0) (n.data 0) 12) _ _ ?_
              (.single ?_))))))
  all_goals simp [step, seek, Instr.effect, Instr.next, State.setPtr, State.setData,
    State.deref, next, y, pc, nil, addr, read, compare, notLess, greater, Function.update_comm]

private theorem found_steps (x : State M (layout extra regs)) (n : Record M (layout extra regs))
    (pc : x.pc = 2) (nil : x.ptr 5 = none) (addr : x.ptr 0 ≠ none)
    (read : x.deref 0 = some n) (equal : x.data 0 = n.data 0) :
    Runs (seek lt) x (next x (x.ptr 0) (x.ptr 2) (n.data 0) 6) 4 := by
  change (x.ptr 0).bind (x.heap[·]?) = some n at read
  let y := x.setData 1 (n.data 0)
  refine .head x { x with pc := 3 } _ _ ?_
    (.head _ { y with pc := 4 } _ _ ?_
      (.head _ { y with pc := 5 } _ _ ?_ (.single ?_)))
  all_goals simp [step, seek, Instr.effect, Instr.next, State.setPtr, State.setData,
    State.deref, next, y, pc, nil, addr, read, compare, equal]

private theorem loop (t : BinaryTree (Label M extra))
    (x : State M (layout extra regs)) (cs : List (Frame M extra))
    (rep : Represents x.heap (contextParent cs) t) (cursor : x.ptr 0 = root t)
    (parent : x.ptr 2 = contextParent cs) (path : SearchPath (x.data 0) cs)
    (pc : x.pc = 2) (nil : x.ptr 5 = none) :
    ∃ ds f v n, n ≤ 7 * searchVisits (x.data 0) (keys t) + 1 ∧
      Runs (seek lt) x (next x (root f) (contextParent ds) v
        (if (root f).isSome then 6 else 13)) n ∧
      plug cs t = plug ds f ∧ SearchPath (x.data 0) ds ∧
      (match f with | .nil => True | .node a _ _ => a.data 0 = x.data 0) ∧
      (root f).isSome = contains (x.data 0) (keys t) := by
  induction t generalizing x cs with
  | nil =>
    refine ⟨cs, .nil, x.data 1, 1, by simp [keys], .single ?_, rfl, path, trivial, rfl⟩
    have cur : x.ptr 0 = none := cursor
    have eq : next x none (contextParent cs) (x.data 1) 13 = { x with pc := 13 } := by
      simp only [next, State.setPtr, ← parent, ← cur, Function.update_eq_self]
    simpa only [root, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, eq] using
      (show step (seek lt) x = some { x with pc := 13 } by
        simp [step, seek, pc, cur, nil, Instr.next, Instr.effect])
  | node a l r il ir =>
    have read : x.deref 0 = some (record (root l) (root r) (contextParent cs) a) := by
      simpa [State.deref, cursor, root] using rep.1
    have addr : x.ptr 0 ≠ none := by simp [cursor, root]
    by_cases less : x.data 0 < a.data 0
    · let y := next x (root l) (some a.address) (a.data 0) 2
      obtain ⟨ds, f, v, n, bound, run, whole, sp, stop, found⟩ :=
        il y (.left a r :: cs) rep.2.1
          (by simp [y, next, State.setPtr]) (by simp [y, next, State.setPtr, contextParent])
          (by simpa [SearchPath, y, next] using And.intro less path)
          rfl (by simp [y, next, State.setPtr, nil])
      have first : Runs (seek lt) x y 6 := by
        simpa [record, cursor, root, y] using left_steps lt compare x _ pc nil addr read less
      refine ⟨ds, f, v, 6 + n, ?_, by simpa [record, y, next, State.setPtr, cursor, root,
          Function.update_comm, Function.update_idem] using first.trans run, whole,
        by simpa [y, next] using sp, by simpa [y, next] using stop,
        by simpa [keys, BinaryTree.map, contains, less, y, next] using found⟩
      have b : n ≤ 7 * searchVisits (x.data 0) (keys l) + 1 := by simpa [y, next] using bound
      simp only [keys, BinaryTree.map, searchVisits, less, ↓reduceIte]
      change 6 + n ≤ 7 * (1 + searchVisits (x.data 0) (keys l)) + 1
      omega
    · by_cases greater : a.data 0 < x.data 0
      · let y := next x (root r) (some a.address) (a.data 0) 2
        obtain ⟨ds, f, v, n, bound, run, whole, sp, stop, found⟩ :=
          ir y (.right l a :: cs) rep.2.2
            (by simp [y, next, State.setPtr]) (by simp [y, next, State.setPtr, contextParent])
            (by simpa [SearchPath, y, next] using And.intro greater path)
            rfl (by simp [y, next, State.setPtr, nil])
        have first : Runs (seek lt) x y 7 := by
          simpa [record, cursor, root, y] using
            right_steps lt compare x _ pc nil addr read less greater
        refine ⟨ds, f, v, 7 + n, ?_, by simpa [record, y, next, State.setPtr, cursor, root,
            Function.update_comm, Function.update_idem] using first.trans run, whole,
          by simpa [y, next] using sp, by simpa [y, next] using stop,
          by simpa [keys, BinaryTree.map, contains, less, greater, y, next] using found⟩
        have b : n ≤ 7 * searchVisits (x.data 0) (keys r) + 1 := by simpa [y, next] using bound
        simp only [keys, BinaryTree.map, searchVisits, less, greater, ↓reduceIte]
        change 7 + n ≤ 7 * (1 + searchVisits (x.data 0) (keys r)) + 1
        omega
      · have equal : x.data 0 = a.data 0 := le_antisymm (le_of_not_gt greater) (le_of_not_gt less)
        refine ⟨cs, .node a l r, a.data 0, 4, ?_, ?_, rfl, path, equal.symm, ?_⟩
        · simp [keys, BinaryTree.map, searchVisits, less, greater]
        · simpa [cursor, root, record, parent] using
            found_steps lt compare x _ pc nil addr read equal
        · simp [root, keys, BinaryTree.map, contains, less, greater]

/-- A search focus and its ancestor context, with the comparison decisions and register frame.
The context is mathematical proof data, not storage used by the machine. -/
structure SeekResult (x y : State M (layout extra regs))
    (whole focus : BinaryTree (Label M extra)) (cs : List (Frame M extra)) : Prop where
  /-- No record is modified or allocated. -/
  heap : y.heap = x.heap
  /-- Only comparison scratch data register one may change. -/
  data : ∀ i, i ≠ 1 → y.data i = x.data i
  /-- Only cursor, parent and null scratch pointers may change. -/
  ptr : ∀ i, i ≠ 0 → i ≠ 2 → i ≠ 5 → y.ptr i = x.ptr i
  /-- The cursor identifies the final focus. -/
  cursor : y.ptr 0 = root focus
  /-- The parent survives even when the focus is empty. -/
  parent : y.ptr 2 = contextParent cs
  /-- The original whole tree is recovered from the returned focus and context. -/
  reconstruction : whole = plug cs focus
  /-- The focused subtree retains its complete heap representation. -/
  rep : Represents y.heap (contextParent cs) focus
  /-- All ancestor links and sibling subtrees retain their representation. -/
  context : ContextRep y.heap (root focus) cs
  /-- Each descent follows the query comparison at its ancestor. -/
  path : SearchPath (x.data 0) cs
  /-- The focus is empty or its root key equals the query. -/
  stop : match focus with | .nil => True | .node a _ _ => a.data 0 = x.data 0
  /-- A nonnull focus agrees with the existing functional search. -/
  found : (y.ptr 0).isSome = contains (x.data 0) (keys whole)

/-- Parent-preserving search uses at most seven instructions per visited node plus four
for initialization and termination, including halt. It returns the entire comparison path;
no ordering premise is needed for agreement with the functional search algorithm. -/
theorem seek_correct (x : State M (layout extra regs))
    (t : BinaryTree (Label M extra)) (rep : Represents x.heap none t)
    (cursor : x.ptr 0 = root t) (pc : x.pc = 0) :
    ∃ y time cs focus, Executes (seek lt) x y time ∧
      time ≤ 7 * searchVisits (x.data 0) (keys t) + 4 ∧ SeekResult x y t focus cs := by
  let start : State M (layout extra regs) := { (x.setPtr 5 none).setPtr 2 none with pc := 2 }
  obtain ⟨cs, focus, v, n, bound, run, whole, path, stop, found⟩ :=
    loop lt compare t start [] rep (by simpa [start, State.setPtr] using cursor)
      (by simp [start, State.setPtr, contextParent]) trivial rfl
      (by simp [start, State.setPtr])
  let finish := next start (root focus) (contextParent cs) v
    (if (root focus).isSome then 6 else 13)
  refine ⟨finish, n + 3, cs, focus, ⟨n + 2, ?_, ?_, by omega⟩, ?_, ?_⟩
  · refine .head x { x.setPtr 5 none with pc := 1 } _ _ ?_
      (.head _ start _ _ ?_ run)
    · simp [step, seek, pc, Instr.effect, Instr.next]
    · simp [step, seek, start, Instr.effect, Instr.next, State.setPtr]
  · cases focus <;> simp [finish, next, seek, root]
  · have b : n ≤ 7 * searchVisits (x.data 0) (keys t) + 1 := bound; omega
  · have reps := (represents_plug_iff x.heap cs focus).mp (whole ▸ rep)
    refine ⟨rfl, fun i hi => by simp [finish, next, start, hi, State.setPtr],
      fun i h0 h2 h5 => by simp [finish, next, start, h0, h2, h5, State.setPtr],
      by simp [finish, next, State.setPtr], by simp [finish, next, State.setPtr], whole, reps.1,
      reps.2, path, by cases focus <;> exact stop,
      by simpa [finish, next, start, State.setPtr] using found⟩

end Cslib.DataStructure.SearchTree.PointerMachine
