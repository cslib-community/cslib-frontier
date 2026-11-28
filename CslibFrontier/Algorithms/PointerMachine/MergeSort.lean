/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Assemble

/-!
# Natural merge sort on the pointer machine

The input is a null-terminated singly linked list with one key per record. Each pass
cuts consecutive nondecreasing runs and merges adjacent pairs by relinking their nodes.
When one run is exhausted, the remaining suffix is spliced in one operation on the output link.
The first pair starts the output list, so later appends can write directly to its tail.
Ties go to the earlier run. The program stops after a pass finds only one run, and
returns the head in the original register. It uses no allocation or scalar arithmetic.

## Main definitions

* `layout`, `head`: the fixed list layout and input and output register.
* `code`: the sorter, parameterized by a key comparison supplied by the machine model.
* `heap_length_eq`: executions preserve the number of allocated records.
-/

public section

namespace Cslib.Algorithms.PointerMachine.MergeSort

open Cslib.PointerMachine

/-- Pointer registers, two key registers, and one successor and key field per record. -/
@[expose, reducible] def layout : Layout := ⟨12, 2, 1, 1⟩

/-- The list head at entry and after sorting. -/
abbrev head : Fin layout.ptrRegs := 0

private abbrev nil : Fin layout.ptrRegs := 1
private abbrev pending : Fin layout.ptrRegs := 2
private abbrev left : Fin layout.ptrRegs := 3
private abbrev right : Fin layout.ptrRegs := 4
private abbrev result : Fin layout.ptrRegs := 5
private abbrev tail : Fin layout.ptrRegs := 6
private abbrev last : Fin layout.ptrRegs := 7
private abbrev probe : Fin layout.ptrRegs := 8
private abbrev merged : Fin layout.ptrRegs := 9
private abbrev leftLast : Fin layout.ptrRegs := 10
private abbrev rightLast : Fin layout.ptrRegs := 11

variable {M : Model}

local infixr:70 " ▷ " => Program.Code.seq

private def move (dst src : Fin layout.ptrRegs) : Code M layout :=
  .op (.movePtr dst src)

private def clear (r : Fin layout.ptrRegs) : Code M layout := .op (.null r)

private def readNext (dst src : Fin layout.ptrRegs) : Code M layout :=
  .op (.loadPtr dst 0 src)

private def writeNext (dst src : Fin layout.ptrRegs) : Code M layout :=
  .op (.storePtr 0 dst src)

-- Isolate the run starting at pending, saving its tail and advancing pending past it.
private def cutRun (lt : M.Test) (runTail : Fin layout.ptrRegs) : Code M layout :=
  move runTail pending ▷ readNext pending runTail ▷ move probe pending ▷
  .loopUntil (.ptrEq probe nil)
    (.op (.loadData 0 0 probe) ▷ .op (.loadData 1 0 runTail) ▷
      .branch (.data lt 0 1)
        (clear probe)
        (move runTail probe ▷ readNext pending runTail ▷ move probe pending)) ▷
  writeNext runTail nil

private def startOutput (first final : Fin layout.ptrRegs) : Code M layout :=
  move result first ▷ move tail final

private def appendRun (first final : Fin layout.ptrRegs) : Code M layout :=
  writeNext tail first ▷ move tail final

-- Save the successor before attaching the chosen node to the output.
private def emit (attach : Fin layout.ptrRegs → Fin layout.ptrRegs → Code M layout)
    (src : Fin layout.ptrRegs) : Code M layout :=
  move last src ▷ readNext src src ▷ attach last last

private def emitLeast (lt : M.Test)
    (attach : Fin layout.ptrRegs → Fin layout.ptrRegs → Code M layout) : Code M layout :=
  .op (.loadData 0 0 right) ▷ .op (.loadData 1 0 left) ▷
    .branch (.data lt 0 1) (emit attach right) (emit attach left)

private def mergeRuns (lt : M.Test) : Code M layout :=
  .loopUntil (.ptrEq left nil)
    (.branch (.ptrEq right nil)
      (appendRun left leftLast ▷ clear left)
      (emitLeast lt appendRun)) ▷
  .branch (.ptrEq right nil) .skip (appendRun right rightLast)

-- The first pair starts an output list. Later pairs use its existing tail.
private def mergePair (lt : M.Test) (first : Bool) : Code M layout :=
  move left pending ▷ cutRun lt leftLast ▷ move right pending ▷
  .branch (.ptrEq right nil)
    ((if first then startOutput else appendRun) left leftLast)
    (move merged right ▷ cutRun lt rightLast ▷
      (if first then emitLeast lt startOutput else .skip) ▷ mergeRuns lt)

private def mergePass (lt : M.Test) : Code M layout :=
  move pending head ▷ clear merged ▷ mergePair lt true ▷
  .loopUntil (.ptrEq pending nil) (mergePair lt false) ▷
  move head result

/-- Stably sort a singly linked list in place. The predicate `lt` tests strict key order. -/
def code (lt : M.Test) : Code M layout :=
  clear nil ▷ move merged head ▷ .loopUntil (.ptrEq merged nil) (mergePass lt)

/-- Every execution keeps the original number of records. -/
theorem heap_length_eq {lt : M.Test} {x y : State M layout} {t : ℕ}
    (h : Exec (code lt) x y t) : y.heap.length = x.heap.length := by
  refine Program.Exec.invariant_ops (I := instructionSet M layout)
    (fun z : State M layout => z.heap.length = x.heap.length) h ?_ rfl
  intro o ho a b hab ha
  change some (o.effect a) = some b at hab
  cases Option.some.inj hab
  suffices (o.effect a).heap.length = a.heap.length from this.trans ha
  cases o with
  | loadPtr _ _ base | loadData _ _ base =>
    cases he : a.deref base <;> simp [Op.effect, Op.instr, Instr.effect, he, State.setPtr,
      State.setData]
  | storePtr _ base _ | storeData _ base _ =>
    cases hp : a.ptr base <;> simp [Op.effect, Op.instr, Instr.effect, State.modify, hp]
  | create =>
    simp [code, mergePass, mergePair, mergeRuns, emitLeast, emit, startOutput, appendRun,
      cutRun, clear, move, readNext, writeNext] at ho
  | _ => rfl

end Cslib.Algorithms.PointerMachine.MergeSort
