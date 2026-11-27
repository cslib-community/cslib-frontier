/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Assemble
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Seek
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.Registers

/-!
# Parent-preserving search as a structured pointer-machine program

`Structured.seek` is the search of `Seek` written as a structured program. It follows the
ordinary binary-search decisions while retaining the immediate parent in register two,
including when the search reaches an empty child, and meets the same specification `SeekResult`.

As in `Structured.search`, a successful search leaves the loop by copying the cursor into the
register that the loop compares it with, pointer register five.

## Main definitions

* `seek`: the structured search program.

## Main results

* `seek_correct`: it returns the focus and its ancestor context within
  `8 * searchVisits + 3` instructions.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine.Structured

open Cslib.PointerMachine

variable {M : Model} {extra regs : ℕ}

open Register in
/-- One step of the search: move the cursor to the child on the side of the key searched for,
remembering its parent, or stop at a node with that key. -/
@[expose] def seekStep (lt : M.Test) : Code M (layout extra regs) := pm[
  here := cur[key];
  if lt query here then [ par ← cur; cur ← cur[left] ] else [
    if lt here query then [ par ← cur; cur ← cur[right] ] else [ stop ← cur ] ] ]

open Register in
/-- Search from cursor zero for query data register zero, retaining the parent in pointer two.
Pointer five and data one are scratch. -/
@[expose] def seek (lt : M.Test) : Code M (layout extra regs) := pm[
  stop ← null;
  par ← null;
  while cur ≠ stop do [ ⟪seekStep lt⟫ ] ]

variable [LinearOrder M.Value] (lt : M.Test)
    (compare : ∀ a b, M.evalTest lt a b = decide (a < b))

include compare

/-- The search stopped at the focus `f` in the context `ds`: the cursor is its root and register
two its parent, and `f` is empty or has the key `q` at its root. -/
private def Sought (q : M.Value) (whole : BinaryTree (Label M extra))
    (y : State M (layout extra regs)) (ds : List (Frame M extra))
    (f : BinaryTree (Label M extra)) : Prop :=
  y.ptr 0 = root f ∧ y.ptr 2 = contextParent ds ∧ whole = plug ds f ∧ SearchPath q ds ∧
    (match f with | .nil => True | .node a _ _ => a.data 0 = q)

/-- The loop, from the root of a represented focus in its context. -/
private theorem loop (t : BinaryTree (Label M extra)) (x : State M (layout extra regs))
    (cs : List (Frame M extra)) (rep : Represents x.heap (contextParent cs) t)
    (cursor : x.ptr 0 = root t) (parent : x.ptr 2 = contextParent cs)
    (path : SearchPath (x.data 0) cs) (nil : x.ptr 5 = none) :
    WP (.loopUntil (.ptrEq 0 5) (seekStep lt)) x fun y n =>
      n ≤ 8 * searchVisits (x.data 0) (keys t) + 1 ∧
      ∃ ds f, Sought (x.data 0) (plug cs t) y ds f ∧
        (root f).isSome = contains (x.data 0) (keys t) := by
  induction t generalizing x cs with
  | nil =>
    exact Program.WP.loopUntil_exit (by simp [pm_simps, cursor, nil, root])
      ⟨by omega, cs, .nil, ⟨cursor, parent, rfl, path, trivial⟩, rfl⟩
  | node a l r il ir =>
    have read : x.deref 0 = some (record (root l) (root r) (contextParent cs) a) := by
      simpa [State.deref, cursor, root] using rep.1
    refine Program.WP.loopUntil_iter (by simp [pm_simps, cursor, nil, root]) ?_
    by_cases less : x.data 0 < a.data 0
    · pm_exec [seekStep, read, record, compare, less]
      refine (il _ (.left a r :: cs) (by exact rep.2.1) (by simp)
        (by simp [cursor, root, contextParent])
        (by simpa [SearchPath] using And.intro less path) (by simp [nil])).mono ?_
      rintro y n ⟨time, ds, f, sought, found⟩
      refine ⟨?_, ds, f, by simpa [plug] using sought,
        by simpa [keys, BinaryTree.map, contains, less] using found⟩
      simp [keys, BinaryTree.map, searchVisits, less] at time ⊢
      omega
    · by_cases greater : a.data 0 < x.data 0
      · pm_exec [seekStep, read, record, compare, less, greater]
        refine (ir _ (.right l a :: cs) (by exact rep.2.2) (by simp)
          (by simp [cursor, root, contextParent])
          (by simpa [SearchPath] using And.intro greater path) (by simp [nil])).mono ?_
        rintro y n ⟨time, ds, f, sought, found⟩
        refine ⟨?_, ds, f, by simpa [plug] using sought,
          by simpa [keys, BinaryTree.map, contains, less, greater] using found⟩
        simp [keys, BinaryTree.map, searchVisits, less, greater] at time ⊢
        omega
      · pm_exec [seekStep, read, record, compare, less, greater]
        refine Program.WP.loopUntil_exit (by simp [pm_simps])
          ⟨?_, cs, .node a l r, ⟨by simp [cursor], by simp [parent], rfl, path,
            le_antisymm (le_of_not_gt less) (le_of_not_gt greater)⟩, ?_⟩
        · simp only [keys, BinaryTree.map, searchVisits, less, greater, ↓reduceIte]
          omega
        · simp [root, keys, BinaryTree.map, contains, less, greater]

/-- Parent-preserving search uses at most eight instructions per visited node plus three for
initialization and leaving the loop. It returns the entire comparison path; no ordering premise
is needed for agreement with the functional search algorithm. -/
theorem seek_correct (x : State M (layout extra regs))
    (t : BinaryTree (Label M extra)) (rep : Represents x.heap none t)
    (cursor : x.ptr 0 = root t) :
    ∃ y cs focus, ExecWithin (seek lt) x y (8 * searchVisits (x.data 0) (keys t) + 3) ∧
      SeekResult x y t focus cs := by
  have main : ∃ y, ExecWithin (seek lt) x y (8 * searchVisits (x.data 0) (keys t) + 3) ∧
      ∃ ds f, Sought (x.data 0) t y ds f ∧
        (root f).isSome = contains (x.data 0) (keys t) := by
    apply WP.exists_execWithin
    pm_exec [seek]
    refine (loop lt compare t _ [] (by exact rep)
      (by exact cursor) rfl trivial rfl).mono fun y n ⟨time, post⟩ =>
      ⟨by simp at time; omega, post⟩
  obtain ⟨y, run, cs, focus, ⟨cur, par, whole, path, stop⟩, found⟩ := main
  have heap := run.heap_eq (by pm_frame)
  have reps := (represents_plug_iff x.heap cs focus).mp (whole ▸ rep)
  exact ⟨y, cs, focus, run, heap, fun i hi => run.data_keep [1] (by pm_frame) (by simpa using hi),
    fun i h0 h2 h5 => run.ptr_keep [0, 2, 5] (by pm_frame) (by simp [h0, h2, h5]), cur, par,
    whole, heap ▸ reps.1, heap ▸ reps.2, path, by cases focus <;> exact stop,
    by rw [cur]; exact found⟩

end Cslib.DataStructure.SearchTree.PointerMachine.Structured
