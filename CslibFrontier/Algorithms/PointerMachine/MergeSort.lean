/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Assemble
public import CslibFrontier.Computability.PointerMachine.WordRAM.NaturalSimulation
public import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Sort

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
* `Segment`: the representation of an allocated linked list segment.
* `instructionBound`: the instruction budget including the final halt.

## Main results

* `executes_sort`: any prepared null-terminated chain with distinct addresses sorts
  within the instruction budget and retains its keys and allocated records.
* `wordRAM_executes_sort`: the compiled natural-key sorter has the same output and
  a sevenfold instruction bound.
* `heap_length_eq`: structured executions preserve the number of allocated records.

The proof counts maximal nondecreasing runs. A pass produces at most half as many
runs, rounded up. Its time bound charges separately for scanning the input and for
joining consecutive sorted runs.
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

private def compareHeads (leftPtr rightPtr : Fin layout.ptrRegs) : Code M layout :=
  .op (.loadData 0 0 rightPtr) ▷ .op (.loadData 1 0 leftPtr)

private def scanBody (lt : M.Test) (runTail : Fin layout.ptrRegs) : Code M layout :=
  compareHeads runTail probe ▷ .branch (.data lt 0 1) (clear probe)
      (move runTail probe ▷ readNext pending runTail ▷ move probe pending)

private def runScan (lt : M.Test) (runTail : Fin layout.ptrRegs) : Code M layout :=
  .loopUntil (.ptrEq probe nil) (scanBody lt runTail)

-- Isolate the run starting at pending, saving its tail and advancing pending past it.
private def cutRun (lt : M.Test) (runTail : Fin layout.ptrRegs) : Code M layout :=
  move runTail pending ▷ readNext pending runTail ▷ move probe pending ▷
  runScan lt runTail ▷ writeNext runTail nil

private def startOutput (first final : Fin layout.ptrRegs) : Code M layout :=
  move result first ▷ move tail final

private def appendRun (first final : Fin layout.ptrRegs) : Code M layout :=
  writeNext tail first ▷ move tail final

private def takeHead (src : Fin layout.ptrRegs) : Code M layout :=
  move last src ▷ readNext src src

-- Save the successor before attaching the chosen node to the output.
private def emit (attach : Fin layout.ptrRegs → Fin layout.ptrRegs → Code M layout)
    (src : Fin layout.ptrRegs) : Code M layout :=
  takeHead src ▷ attach last last

private def emitLeast (lt : M.Test)
    (attach : Fin layout.ptrRegs → Fin layout.ptrRegs → Code M layout) : Code M layout :=
  compareHeads left right ▷ .branch (.data lt 0 1) (emit attach right) (emit attach left)

private def mergeRuns (lt : M.Test) : Code M layout :=
  .loopUntil (.ptrEq left nil)
    (.branch (.ptrEq right nil)
      (appendRun left leftLast ▷ clear left)
      (emitLeast lt appendRun)) ▷
  .branch (.ptrEq right nil) .skip (appendRun right rightLast)

private def finishPair (lt : M.Test) (first : Bool) : Code M layout :=
  (if first then emitLeast lt startOutput else .skip) ▷ mergeRuns lt

-- The first pair starts an output list. Later pairs use its existing tail.
private def mergePair (lt : M.Test) (first : Bool) : Code M layout :=
  move left pending ▷ cutRun lt leftLast ▷ move right pending ▷
  .branch (.ptrEq right nil)
    ((if first then startOutput else appendRun) left leftLast)
    (move merged right ▷ cutRun lt rightLast ▷ finishPair lt first)

private def mergeTail (lt : M.Test) : Code M layout :=
  .loopUntil (.ptrEq pending nil) (mergePair lt false)

private def mergePass (lt : M.Test) : Code M layout :=
  move pending head ▷ clear merged ▷ mergePair lt true ▷
  mergeTail lt ▷ move head result

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
    simp [code, mergePass, mergeTail, mergePair, finishPair, mergeRuns, emitLeast, emit, takeHead,
      startOutput, appendRun, cutRun, runScan, scanBody, compareHeads, clear, move, readNext,
      writeNext] at ho
  | _ => rfl

private abbrev SortState (M : Model) := State M layout

/-- The key stored at an allocated list address. Outside the heap this returns the
model's undefined value. -/
@[expose] def key (x : State M layout) (a : ℕ) : M.Value :=
  ((x.heap[a]?).map (fun node => node.data 0)).getD M.undefined

private def next (x : SortState M) (a : ℕ) : Pointer :=
  (x.heap[a]?).bind (fun node => node.ptr 0)

private def front (xs : List ℕ) (endPtr : Pointer) : Pointer :=
  match xs with
  | [] => endPtr
  | a :: _ => some a

/-- Every node of the segment is allocated, and its link points to the next node or to
`endPtr` at the end. Pairwise distinct addresses are an independent input requirement. -/
def Segment (x : State M layout) : List ℕ → Pointer → Prop
  | [], _ => True
  | a :: xs, endPtr =>
      a < x.heap.length ∧ next x a = front xs endPtr ∧ Segment x xs endPtr

private theorem front_append (xs ys : List ℕ) (endPtr : Pointer) :
    front (xs ++ ys) endPtr = front xs (front ys endPtr) := by
  cases xs <;> rfl

private theorem front_null (xs : List ℕ) : front xs none = xs.head? := by
  cases xs <;> rfl

private theorem segment_append {x : SortState M} {xs ys : List ℕ} {endPtr : Pointer} :
    Segment x (xs ++ ys) endPtr ↔ Segment x xs (front ys endPtr) ∧ Segment x ys endPtr := by
  induction xs with
  | nil => simp [Segment]
  | cons a xs ih =>
    simp only [List.cons_append, Segment, front_append, ih, and_assoc]

private theorem segment_congr {x y : SortState M} {xs : List ℕ} {endPtr : Pointer}
    (h : Segment x xs endPtr) (hlen : x.heap.length = y.heap.length)
    (hnext : ∀ a ∈ xs, next x a = next y a) : Segment y xs endPtr := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
    obtain ⟨ha, hhead, htail⟩ := h
    exact ⟨hlen ▸ ha, (hnext a (by simp)).symm.trans hhead,
      ih htail (fun b hb => hnext b (by simp [hb]))⟩

private theorem segment_heap {x y : SortState M} {xs : List ℕ} {endPtr : Pointer}
    (h : Segment x xs endPtr) (hheap : x.heap = y.heap) : Segment y xs endPtr :=
  segment_congr h (congrArg List.length hheap)
    (fun a _ => by unfold next; rw [hheap])

private theorem segment_lt {x : SortState M} {xs : List ℕ} {endPtr : Pointer}
    (h : Segment x xs endPtr) {a : ℕ} (ha : a ∈ xs) : a < x.heap.length := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem ha
  exact ((segment_append.mp h).2).1

private def setNext (x : SortState M) (a : ℕ) (p : Pointer) : SortState M :=
  { x with heap := x.heap.modify a (fun node => { node with ptr := Function.update node.ptr 0 p }) }

private theorem length_setNext (x : SortState M) (a : ℕ) (p : Pointer) :
    (setNext x a p).heap.length = x.heap.length := by
  simp [setNext]

private theorem key_setNext (x : SortState M) (a b : ℕ) (p : Pointer) :
    key (setNext x a p) b = key x b := by
  by_cases h : a = b <;> simp [key, setNext, h, Option.map_map,
    Function.comp_def]

private theorem next_setNext_ne (x : SortState M) (a b : ℕ) (p : Pointer) (h : a ≠ b) :
    next (setNext x a p) b = next x b := by
  simp [next, setNext, h]

private theorem next_setNext_self (x : SortState M) (a : ℕ) (p : Pointer)
    (ha : a < x.heap.length) : next (setNext x a p) a = p := by
  simp [next, setNext, List.getElem?_eq_getElem ha]

private theorem exec_move (x : SortState M) (r s : Fin layout.ptrRegs) :
    Exec (move (M := M) r s) x (x.setPtr r (x.ptr s)) 1 :=
  Exec.op

private theorem exec_clear (x : SortState M) (r : Fin layout.ptrRegs) :
    Exec (clear (M := M) r) x (x.setPtr r none) 1 :=
  Exec.op

private theorem exec_readNext (x : SortState M) (r s : Fin layout.ptrRegs) (a : ℕ)
    (hs : x.ptr s = some a) (ha : a < x.heap.length) :
    Exec (readNext (M := M) r s) x (x.setPtr r (next x a)) 1 := by
  apply Program.Exec.op
  change some ((Instr.loadPtr r 0 s).effect x) = _
  simp [Instr.effect, State.deref, hs, List.getElem?_eq_getElem ha, next]

private theorem exec_readKey (x : SortState M) (r : Fin layout.dataRegs)
    (s : Fin layout.ptrRegs) (a : ℕ) (hs : x.ptr s = some a) (ha : a < x.heap.length) :
    Exec (.op (.loadData r 0 s)) x (x.setData r (key x a)) 1 := by
  apply Program.Exec.op
  change some ((Instr.loadData r 0 s).effect x) = _
  simp [Instr.effect, State.deref, hs, List.getElem?_eq_getElem ha, key]

private theorem exec_writeNext (x : SortState M) (r s : Fin layout.ptrRegs) (a : ℕ)
    (hr : x.ptr r = some a) :
    Exec (writeNext (M := M) r s) x (setNext x a (x.ptr s)) 1 := by
  apply Program.Exec.op
  change some ((Instr.storePtr 0 r s).effect x) = _
  simp [Instr.effect, State.modify, hr, setNext]

private def afterLoad (x : SortState M) (a b : ℕ) : SortState M :=
  (x.setData 0 (key x b)).setData 1 (key x a)

private theorem exec_compareHeads (x : SortState M) (leftPtr rightPtr : Fin layout.ptrRegs)
    (a b : ℕ) (hLeft : x.ptr leftPtr = some a) (hRight : x.ptr rightPtr = some b)
    (ha : a < x.heap.length) (hb : b < x.heap.length) :
    Exec (compareHeads leftPtr rightPtr) x (afterLoad x a b) 2 :=
  Program.Exec.seq (exec_readKey x 0 rightPtr b hRight hb)
    (exec_readKey _ 1 leftPtr a hLeft ha)

private def afterScanAdvance (x : SortState M) (runTail : Fin layout.ptrRegs) (b : ℕ) :
    SortState M :=
  ((x.setPtr runTail (some b)).setPtr pending (next x b)).setPtr probe (next x b)

private theorem exec_scanAdvance (x : SortState M) (runTail : Fin layout.ptrRegs) (b : ℕ)
    (hpb : x.ptr probe = some b) (hb : b < x.heap.length) :
    Exec (move runTail probe ▷ readNext pending runTail ▷ move probe pending)
      x (afterScanAdvance x runTail b) 3 := by
  have hm := exec_move x runTail probe
  rw [hpb] at hm
  let z := x.setPtr runTail (some b)
  let y := z.setPtr pending (next x b)
  have hn := exec_readNext z pending runTail b (by simp [z, State.setPtr]) hb
  have hp := exec_move y probe pending
  have he : y.ptr pending = next x b := by simp [y, State.setPtr]
  rw [he] at hp
  exact Program.Exec.seq hm (Program.Exec.seq hn hp)

private structure ScanResult [LinearOrder M.Value] (x y : SortState M)
    (runTail : Fin layout.ptrRegs) (a : ℕ) (rest : List ℕ) where
  used : List ℕ
  remaining : List ℕ
  split : rest = used ++ remaining
  ordered : (a :: used).Pairwise (fun i j => key x i ≤ key x j)
  tail_eq : y.ptr runTail = (a :: used).getLast?
  pending_eq : y.ptr pending = remaining.head?
  descends : ∀ i j, (a :: used).getLast? = some i → remaining.head? = some j →
    key x j < key x i
  heap_eq : y.heap = x.heap
  ptr_eq : ∀ r, r ≠ runTail → r ≠ pending → r ≠ probe → y.ptr r = x.ptr r

private theorem exec_scan [LinearOrder M.Value] (lt : M.Test)
    (hcmp : ∀ a b, M.evalTest lt a b = decide (a < b)) (runTail : Fin layout.ptrRegs)
    (htp : runTail ≠ pending) (htq : runTail ≠ probe) (htn : runTail ≠ nil)
    (x : SortState M) (a : ℕ) (rest : List ℕ) (hseg : Segment x (a :: rest) none)
    (htail : x.ptr runTail = some a) (hp : x.ptr pending = rest.head?)
    (hq : x.ptr probe = rest.head?) (hn : x.ptr nil = none) :
    ∃ (y : SortState M) (out : ScanResult x y runTail a rest),
      ExecWithin (runScan lt runTail) x y
        (9 * out.used.length + if out.remaining = [] then 1 else 7) := by
  induction rest generalizing x a with
  | nil =>
    refine ⟨x, ⟨[], [], rfl, by simp, by simpa using htail, hp,
      fun _ _ _ h => by simp at h, rfl, fun _ _ _ _ => rfl⟩, ?_⟩
    change ExecWithin (.loopUntil (.ptrEq probe nil) _) x x 1
    exact Program.ExecWithin.loopUntil_exit (show x.ptr probe = x.ptr nil by rw [hq, hn]; rfl)
  | cons b rest ih =>
    have hqa : x.ptr probe = some b := hq
    have ha := hseg.1
    have hb := hseg.2.2.1
    let z := afterLoad x a b
    have hloads := exec_compareHeads x runTail probe a b htail hqa ha hb
    have hztest : (Test.data lt 0 1).Holds z ↔ key x b < key x a := by
      simp [z, afterLoad, Test.Holds, State.setData, hcmp]
    have hcont : ¬(Test.ptrEq probe nil).Holds x := by
      change x.ptr probe ≠ x.ptr nil
      rw [hqa, hn]
      exact Option.some_ne_none b
    by_cases hd : key x b < key x a
    · let y := z.setPtr probe none
      have hstop : (Test.ptrEq probe nil).Holds y := by
        change y.ptr probe = y.ptr nil
        simp [y, z, afterLoad, State.setData, State.setPtr, show nil ≠ probe by decide, hn]
      have hbranch := Program.Exec.branch_pos (I := instructionSet M layout) (t := Test.data lt 0 1)
        (hztest.2 hd)
        (neg := move runTail probe ▷ readNext pending runTail ▷ move probe pending)
        (exec_clear z probe)
      have hbody : Exec (scanBody lt runTail) x y 4 :=
        Program.Exec.seq hloads hbranch
      refine ⟨y, ⟨[], b :: rest, rfl, by simp, ?_, ?_, ?_, rfl, ?_⟩, ?_⟩
      · simpa [y, z, afterLoad, State.setData, State.setPtr, htq] using htail
      · simpa [y, z, afterLoad, State.setData, State.setPtr,
          show pending ≠ probe by decide] using hp
      · intro i j hi hj
        have he₁ : a = i := Option.some.inj hi
        have he₂ : b = j := Option.some.inj hj
        simpa [← he₁, ← he₂] using hd
      · intro r _ _ hrq
        simp [y, z, afterLoad, State.setData, State.setPtr, hrq]
      · simpa [runScan] using
          Program.Exec.loopUntil_iter (I := instructionSet M layout) hcont hbody
            (Program.Exec.loopUntil_exit hstop) |>.within
    · let w := afterScanAdvance z runTail b
      have hmove := exec_scanAdvance z runTail b hqa hb
      have hbranch := Program.Exec.branch_neg (I := instructionSet M layout)
        (t := Test.data lt 0 1) (fun h => hd (hztest.1 h)) (pos := clear probe) hmove
      have hbody : Exec (scanBody lt runTail) x w 7 :=
        Program.Exec.seq hloads hbranch
      have hwheap : w.heap = x.heap := rfl
      have hwptr (r : Fin layout.ptrRegs) (hr : r ≠ runTail) (hrp : r ≠ pending)
          (hrq : r ≠ probe) : w.ptr r = x.ptr r := by
        simp [w, z, afterScanAdvance, afterLoad, State.setData, State.setPtr, hr, hrp, hrq]
      have hwTail : w.ptr runTail = some b := by
        simp [w, afterScanAdvance, State.setPtr, htp, htq]
      have hwNext : next z b = rest.head? := hseg.2.2.2.1.trans (front_null rest)
      have hwPending : w.ptr pending = rest.head? := by
        simp [w, afterScanAdvance, State.setPtr, show pending ≠ probe by decide, hwNext]
      have hwProbe : w.ptr probe = rest.head? := by
        simp [w, afterScanAdvance, State.setPtr, hwNext]
      obtain ⟨y, out, he⟩ := ih w b (segment_heap hseg.2.2 hwheap.symm)
        hwTail hwPending hwProbe ((hwptr nil htn.symm (by decide) (by decide)).trans hn)
      refine ⟨y, ⟨b :: out.used, out.remaining, congrArg (b :: ·) out.split, ?_,
        by simpa only [List.getLast?_cons_cons] using out.tail_eq,
        out.pending_eq, ?_, out.heap_eq.trans hwheap, ?_⟩, ?_⟩
      · have hsort : (b :: out.used).Pairwise (fun i j => key x i ≤ key x j) := by
          simpa only [key, hwheap] using out.ordered
        refine List.pairwise_cons.mpr ⟨?_, hsort⟩
        intro c hc
        have hab : key x a ≤ key x b := le_of_not_gt hd
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hab
        · exact hab.trans (List.rel_of_pairwise_cons hsort hc)
      · intro i j hi hj
        simpa only [key, hwheap] using out.descends i j
          (by simpa only [List.getLast?_cons_cons] using hi) hj
      · intro r hr hp hq
        exact (out.ptr_eq r hr hp hq).trans (hwptr r hr hp hq)
      · exact (Program.ExecWithin.loopUntil_iter (I := instructionSet M layout)
          hcont hbody.within he).mono (by simp only [List.length_cons]; omega)

private structure HeapFrame (x y : SortState M) (written : List ℕ) : Prop where
  length_eq : y.heap.length = x.heap.length
  key_eq : ∀ a, key y a = key x a
  next_eq : ∀ a, a ∉ written → next y a = next x a

private theorem HeapFrame.segment {x y : SortState M} {written xs : List ℕ} {p : Pointer}
    (h : HeapFrame x y written) (hx : Segment x xs p) (hdisj : ∀ a ∈ xs, a ∉ written) :
    Segment y xs p :=
  segment_congr hx h.length_eq.symm fun a ha => (h.next_eq a (hdisj a ha)).symm

private theorem segment_setNext_last {x : SortState M} {run : List ℕ} {a : ℕ} {old p : Pointer}
    (h : Segment x run old) (hn : run.Nodup) (hLast : run.getLast? = some a) :
    Segment (setNext x a p) run p := by
  obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp hLast
  have hnd := List.nodup_append.mp hn
  obtain ⟨hp, ha⟩ := segment_append.mp h
  refine segment_append.mpr ⟨?_, ?_⟩
  · exact segment_congr hp (length_setNext x a p).symm fun b hb => (next_setNext_ne x a b p
      (fun he => (hnd.2.2 b hb a (by simp)) he.symm)).symm
  · exact ⟨(length_setNext x a p).symm ▸ ha.1, next_setNext_self x a p ha.1, trivial⟩

private structure CutResult [LinearOrder M.Value] (x y : SortState M)
    (runTail : Fin layout.ptrRegs) (input : List ℕ) where
  run : List ℕ
  suffix : List ℕ
  split : input = run ++ suffix
  nonempty : run ≠ []
  ordered : run.Pairwise (fun i j => key x i ≤ key x j)
  tail_eq : y.ptr runTail = run.getLast?
  pending_eq : y.ptr pending = suffix.head?
  descends : ∀ i j, run.getLast? = some i → suffix.head? = some j → key x j < key x i
  chain : Segment y run none
  rest : Segment y suffix none
  frame : HeapFrame x y run
  ptr_eq : ∀ r, r ≠ runTail → r ≠ pending → r ≠ probe → y.ptr r = x.ptr r

private theorem exec_cutRun [LinearOrder M.Value] (lt : M.Test)
    (hcmp : ∀ a b, M.evalTest lt a b = decide (a < b)) (runTail : Fin layout.ptrRegs)
    (htp : runTail ≠ pending) (htq : runTail ≠ probe) (htn : runTail ≠ nil)
    (x : SortState M) (a : ℕ) (xs : List ℕ) (hseg : Segment x (a :: xs) none)
    (huniq : (a :: xs).Nodup) (hp : x.ptr pending = some a) (hn : x.ptr nil = none) :
    ∃ (y : SortState M) (out : CutResult x y runTail (a :: xs)),
      ExecWithin (cutRun lt runTail) x y
        (9 * out.run.length + 2 - if out.suffix = [] then 6 else 0) := by
  let v := x.setPtr runTail (some a)
  let w := v.setPtr pending (next x a)
  let z := w.setPtr probe (next x a)
  have hm := exec_move x runTail pending
  rw [hp] at hm
  have hr := exec_readNext v pending runTail a (by simp [v, State.setPtr]) hseg.1
  have hmove := exec_move w probe pending
  have hwnext : w.ptr pending = next x a := by simp [w, State.setPtr]
  rw [hwnext] at hmove
  have hab : next x a = xs.head? := hseg.2.1.trans (front_null xs)
  have hframe (r : Fin layout.ptrRegs) (hr : r ≠ runTail) (hrp : r ≠ pending)
      (hrq : r ≠ probe) : z.ptr r = x.ptr r := by
    simp [z, w, v, State.setPtr, hr, hrp, hrq]
  have ht : z.ptr runTail = some a := by simp [z, w, v, State.setPtr, htp, htq]
  have hp' : z.ptr pending = xs.head? := by
    simp [z, w, State.setPtr, show pending ≠ probe by decide, hab]
  have hq : z.ptr probe = xs.head? := by simp [z, State.setPtr, hab]
  have hz : z.heap = x.heap := rfl
  obtain ⟨s, scan, hscan⟩ := exec_scan lt hcmp runTail htp htq htn z a xs
    (segment_heap hseg hz.symm) ht hp' hq ((hframe nil htn.symm (by decide) (by decide)).trans hn)
  have hshe : s.heap = x.heap := scan.heap_eq.trans hz
  let first := a :: scan.used
  let rest := scan.remaining
  have hsplit : a :: xs = first ++ rest := congrArg (a :: ·) scan.split
  have hnone : first.getLast? ≠ none := by simp [first]
  obtain ⟨aLast, hLast⟩ := Option.ne_none_iff_exists'.mp hnone
  have ht' : s.ptr runTail = some aLast := scan.tail_eq.trans hLast
  have hn' : s.ptr nil = none :=
    (scan.ptr_eq nil htn.symm (by decide) (by decide)).trans
      ((hframe nil htn.symm (by decide) (by decide)).trans hn)
  have hcut := exec_writeNext s runTail nil aLast ht'
  rw [hn'] at hcut
  let y := setNext s aLast none
  have hnd := List.nodup_append.mp (hsplit ▸ huniq)
  obtain ⟨hfirst, hrest⟩ := segment_append.mp (hsplit ▸ hseg)
  have hframe' : HeapFrame x y first := by
    refine ⟨(length_setNext s aLast none).trans (congrArg List.length hshe), ?_, ?_⟩
    · intro b
      exact (key_setNext s aLast b none).trans (by unfold key; rw [hshe])
    · intro b hb
      have hmLast : aLast ∈ first := by
        obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hLast
        rw [hpre]
        simp
      have he : aLast ≠ b := fun eq => hb (eq ▸ hmLast)
      exact (next_setNext_ne s aLast b none he).trans (by unfold next; rw [hshe])
  refine ⟨y, ⟨first, rest, hsplit, by simp [first], ?_, scan.tail_eq, scan.pending_eq, ?_,
    segment_setNext_last (segment_heap hfirst hshe.symm) hnd.1 hLast,
    hframe'.segment hrest (fun b hb ha => hnd.2.2 b ha b hb rfl), hframe', ?_⟩, ?_⟩
  · simpa only [key, hz] using scan.ordered
  · intro i j hi hj
    simpa only [key, hz] using scan.descends i j hi hj
  · intro r hr hrp hrq
    exact (scan.ptr_eq r hr hrp hrq).trans (hframe r hr hrp hrq)
  · exact (Program.ExecWithin.seq hm.within
      (Program.ExecWithin.seq hr.within (Program.ExecWithin.seq hmove.within
        (Program.ExecWithin.seq hscan hcut.within)))).mono (by
          simp only [first, rest, List.length_cons]
          split <;> omega)

private theorem HeapFrame.trans {x y z : SortState M} {a b c : List ℕ}
    (h₁ : HeapFrame x y a) (h₂ : HeapFrame y z b)
    (ha : ∀ i ∈ a, i ∈ c) (hb : ∀ i ∈ b, i ∈ c) : HeapFrame x z c :=
  ⟨h₂.length_eq.trans h₁.length_eq, fun i => (h₂.key_eq i).trans (h₁.key_eq i),
    fun i hi => (h₂.next_eq i fun h => hi (hb i h)).trans (h₁.next_eq i fun h => hi (ha i h))⟩

private theorem HeapFrame.of_heap {x y : SortState M} {written : List ℕ}
    (h : y.heap = x.heap) : HeapFrame x y written :=
  ⟨congrArg List.length h, fun i => by unfold key; rw [h],
    fun i _ => by unfold next; rw [h]⟩

private theorem setNext_frame (x : SortState M) (a : ℕ) (p : Pointer) :
    HeapFrame x (setNext x a p) [a] :=
  ⟨length_setNext x a p, fun b => key_setNext x a b p,
    fun b hb => next_setNext_ne x a b p (fun he => hb (by simp [he]))⟩

private def afterAppend (x : SortState M) (first final : Fin layout.ptrRegs) (a : ℕ) :
    SortState M :=
  (setNext x a (x.ptr first)).setPtr tail (x.ptr final)

private theorem exec_append (x : SortState M) (first final : Fin layout.ptrRegs) (a : ℕ)
    (ht : x.ptr tail = some a) : Exec (appendRun first final) x (afterAppend x first final a) 2 :=
  Program.Exec.seq (exec_writeNext x tail first a ht) (exec_move _ tail final)

private theorem append_segment {x : SortState M} {pre xs : List ℕ}
    {old endPtr : Pointer} {a : ℕ} {first final : Fin layout.ptrRegs}
    (hp : Segment x pre old) (hx : Segment x xs endPtr) (hn : (pre ++ xs).Nodup)
    (ha : pre.getLast? = some a) (hf : x.ptr first = front xs endPtr) :
    Segment (afterAppend x first final a) (pre ++ xs) endPtr := by
  have huniq := List.nodup_append.mp hn
  have hamem : a ∈ pre := by
    obtain ⟨prior, eq⟩ := List.getLast?_eq_some_iff.mp ha
    rw [eq]
    simp
  refine segment_append.mpr ⟨?_, ?_⟩
  · rw [← hf]
    exact segment_heap (segment_setNext_last hp huniq.1 ha) rfl
  · exact segment_heap ((setNext_frame x a (x.ptr first)).segment hx fun b hb hab =>
      huniq.2.2 a hamem b hb ((List.mem_singleton.mp hab).symm)) rfl

private theorem exec_emitPrefix (x : SortState M) (src : Fin layout.ptrRegs) (a : ℕ)
    (hSrc : src ≠ last) (hs : x.ptr src = some a)
    (ha : a < x.heap.length) :
    Exec (takeHead src) x
      ((x.setPtr last (some a)).setPtr src (next x a)) 2 := by
  have hm := exec_move x last src
  rw [hs] at hm
  exact Program.Exec.seq hm
    (exec_readNext _ src src a (by simp [State.setPtr, hSrc, hs]) ha)

private def mergedList [LinearOrder M.Value] (x : SortState M) (xs ys : List ℕ) : List ℕ :=
  xs.merge ys (fun a b => decide (key x a ≤ key x b))

private theorem mergedList_congr [LinearOrder M.Value] {x y : SortState M}
    (h : ∀ a, key y a = key x a) (xs ys : List ℕ) :
    mergedList y xs ys = mergedList x xs ys := by
  simp [mergedList, h]

private def afterEmit (x : SortState M) (src : Fin layout.ptrRegs) (a t : ℕ) : SortState M :=
  afterAppend ((x.setPtr last (some a)).setPtr src (next x a)) last last t

private theorem exec_emitAppend (x : SortState M) (src : Fin layout.ptrRegs) (a t : ℕ)
    (hsrc : src ≠ last) (hsrcTail : src ≠ tail) (hs : x.ptr src = some a)
    (ht : x.ptr tail = some t) (ha : a < x.heap.length) :
    Exec (emit appendRun src) x (afterEmit x src a t) 4 := by
  have hprefix := exec_emitPrefix x src a hsrc hs ha
  have htail :
      (((x.setPtr last (some a)).setPtr src (next x a)).ptr tail) = some t := by
    simpa [State.setPtr, hsrcTail.symm, show tail ≠ last by decide] using ht
  exact Program.Exec.seq hprefix (exec_append _ last last t htail)

private theorem afterEmit_frame (x : SortState M) (src : Fin layout.ptrRegs) (a t : ℕ)
    (hsrc : src ≠ last) : HeapFrame x (afterEmit x src a t) [t] := by
  let w := (x.setPtr last (some a)).setPtr src (next x a)
  have hw : w.ptr last = some a := by simp [w, State.setPtr, hsrc.symm]
  have hheap : (afterEmit x src a t).heap = (setNext x t (some a)).heap := by
    simp only [afterEmit, afterAppend, State.setPtr, setNext]
    exact congrArg (fun p => x.heap.modify t
      (fun node => { node with ptr := Function.update node.ptr 0 p })) hw
  exact (setNext_frame x t (some a)).trans (HeapFrame.of_heap (written := []) hheap)
    (fun _ h => h) (by simp)

private theorem afterEmit_ptr {x : SortState M} {src : Fin layout.ptrRegs} {a t : ℕ}
    (r : Fin layout.ptrRegs) (hrt : r ≠ tail) (hrs : r ≠ src) (hrl : r ≠ last) :
    (afterEmit x src a t).ptr r = x.ptr r := by
  simp [afterEmit, afterAppend, setNext, State.setPtr, hrt, hrs, hrl]

private theorem afterEmit_tail (x : SortState M) (src : Fin layout.ptrRegs) (a t : ℕ)
    (hs : src ≠ last) : (afterEmit x src a t).ptr tail = some a := by
  simp [afterEmit, afterAppend, State.setPtr, hs.symm]

private theorem afterEmit_src (x : SortState M) (src : Fin layout.ptrRegs) (a t : ℕ)
    (hs : src ≠ tail) : (afterEmit x src a t).ptr src = next x a := by
  simp [afterEmit, afterAppend, setNext, State.setPtr, hs]

private theorem afterEmit_segment {x : SortState M} {src : Fin layout.ptrRegs}
    {pre rest : List ℕ} {a t : ℕ} {p : Pointer}
    (hsrc : src ≠ last) (hp : Segment x pre p) (hs : Segment x (a :: rest) none)
    (hnd : (pre ++ a :: rest).Nodup) (ht : pre.getLast? = some t) :
    Segment (afterEmit x src a t) (pre ++ [a]) (front rest none) := by
  let w := (x.setPtr last (some a)).setPtr src (next x a)
  have hw : w.ptr last = some a := by simp [w, State.setPtr, hsrc.symm]
  have hsingleton : Segment w [a] (front rest none) := ⟨hs.1, hs.2.1, trivial⟩
  have hsub : List.Sublist [a] (a :: rest) := List.singleton_sublist.mpr List.mem_cons_self
  have hnodup := hnd.sublist (hsub.append_left pre)
  exact append_segment (segment_heap hp (y := w) rfl) hsingleton hnodup ht hw

private theorem mergedList_cons_cons [LinearOrder M.Value] (x : SortState M)
    (a b : ℕ) (as bs : List ℕ) :
    mergedList x (a :: as) (b :: bs) =
      if key x b < key x a then b :: mergedList x (a :: as) bs
      else a :: mergedList x as (b :: bs) := by
  by_cases h : key x b < key x a
  · simp [mergedList, h, not_le.mpr h]
  · simp [mergedList, h, le_of_not_gt h]

private structure MergeState (x : SortState M) (pre xs ys : List ℕ) : Prop where
  nodup : (pre ++ xs ++ ys).Nodup
  nonempty : pre ≠ []
  output : ∃ p, Segment x pre p
  chainLeft : Segment x xs none
  chainRight : Segment x ys none
  outputTail : x.ptr tail = pre.getLast?
  leftHead : x.ptr left = xs.head?
  rightHead : x.ptr right = ys.head?
  leftTail : xs ≠ [] → x.ptr leftLast = xs.getLast?
  rightTail : ys ≠ [] → x.ptr rightLast = ys.getLast?
  nil_eq : x.ptr nil = none

private structure MergeResult [LinearOrder M.Value]
    (x y : SortState M) (pre xs ys : List ℕ) : Prop where
  output : Segment y (pre ++ mergedList x xs ys) none
  tail_eq : y.ptr tail = (pre ++ mergedList x xs ys).getLast?
  frame : HeapFrame x y (pre ++ xs ++ ys)
  ptr_eq : ∀ r, r ≠ tail → r ≠ left → r ≠ right → r ≠ last → y.ptr r = x.ptr r

private theorem getLast_some {xs : List ℕ} (hn : xs ≠ []) :
    ∃ a, xs.getLast? = some a :=
  Option.ne_none_iff_exists'.mp (fun h => hn (List.getLast?_eq_none_iff.mp h))

private theorem last_mem {xs : List ℕ} {a : ℕ} (ha : xs.getLast? = some a) : a ∈ xs := by
  obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp ha
  simp

private theorem exec_emitLeast_right [LinearOrder M.Value] (lt : M.Test)
    (hcmp : ∀ a b, M.evalTest lt a b = decide (a < b))
    (x : SortState M) (pre : List ℕ) (a b t : ℕ) (as bs : List ℕ)
    (h : MergeState x pre (a :: as) (b :: bs)) (ht : pre.getLast? = some t)
    (hlt : key x b < key x a) :
    ExecWithin (emitLeast lt appendRun) x (afterEmit (afterLoad x a b) right b t) 8 := by
  let w := afterLoad x a b
  have ht' : w.ptr tail = some t := h.outputTail.trans ht
  have hloads := exec_compareHeads x left right a b h.leftHead h.rightHead
    h.chainLeft.1 h.chainRight.1
  have he := exec_emitAppend w right b t (by decide) (by decide) h.rightHead ht' h.chainRight.1
  have htest : (Test.data lt 0 1).Holds w := by
    simp [w, afterLoad, Test.Holds, State.setData, hcmp, hlt]
  exact (Program.ExecWithin.seq hloads.within
    ((Program.Exec.branch_pos (I := instructionSet M layout) (t := Test.data lt 0 1)
      (neg := emit appendRun left) htest he).within)).mono (by decide)

private theorem exec_emitLeast_left [LinearOrder M.Value] (lt : M.Test)
    (hcmp : ∀ a b, M.evalTest lt a b = decide (a < b))
    (x : SortState M) (pre : List ℕ) (a b t : ℕ) (as bs : List ℕ)
    (h : MergeState x pre (a :: as) (b :: bs)) (ht : pre.getLast? = some t)
    (hlt : ¬key x b < key x a) :
    ExecWithin (emitLeast lt appendRun) x (afterEmit (afterLoad x a b) left a t) 8 := by
  let w := afterLoad x a b
  have ht' : w.ptr tail = some t := h.outputTail.trans ht
  have hloads := exec_compareHeads x left right a b h.leftHead h.rightHead
    h.chainLeft.1 h.chainRight.1
  have he := exec_emitAppend w left a t (by decide) (by decide) h.leftHead ht' h.chainLeft.1
  have htest : ¬(Test.data lt 0 1).Holds w := by
    simp [w, afterLoad, Test.Holds, State.setData, hcmp, hlt]
  exact Program.ExecWithin.seq hloads.within
    ((Program.Exec.branch_neg (I := instructionSet M layout) (t := Test.data lt 0 1)
      (pos := emit appendRun right) htest he).within)

private theorem afterEmit_keep {x : SortState M} {src : Fin layout.ptrRegs} {a t : ℕ}
    {xs pre : List ℕ} {p : Pointer} (hs : src ≠ last)
    (hnd : (pre ++ xs).Nodup) (ht : pre.getLast? = some t) (hseg : Segment x xs p) :
    Segment (afterEmit x src a t) xs p :=
  (afterEmit_frame x src a t hs).segment hseg fun b hb hbt =>
    (List.nodup_append.mp hnd).2.2 t (last_mem ht) b hb ((List.mem_singleton.mp hbt).symm)

private theorem split_exec {I : Program.InstructionSet} {c d : Program.Code I.Op I.Test}
    {x y : I.Data} {T : ℕ} (he : Program.Exec I (c ▷ d) x y T) :
    ∃ z m n, Program.Exec I c x z m ∧ Program.Exec I d z y n ∧ m + n = T := by
  cases he with
  | seq h₁ h₂ => exact ⟨_, _, _, h₁, h₂, rfl⟩

private theorem merge_step {x y z : SortState M} {lt : M.Test} {T : ℕ}
    (hLeft : x.ptr left ≠ x.ptr nil) (hRight : x.ptr right ≠ x.ptr nil)
    (hEmit : ExecWithin (emitLeast lt appendRun) x y 8) (hRest : ExecWithin (mergeRuns lt) y z T) :
    ExecWithin (mergeRuns lt) x z (T + 12) := by
  obtain ⟨k, hk, h⟩ := hRest
  unfold mergeRuns at h
  obtain ⟨v, a, b, hLoop, hFinish, hcost⟩ := split_exec h
  have hBody := Program.ExecWithin.branch_neg (I := instructionSet M layout)
    (t := Test.ptrEq right nil) (pos := appendRun left leftLast ▷ clear left) hRight hEmit
  exact (Program.ExecWithin.seq (Program.ExecWithin.loopUntil_iter (I := instructionSet M layout)
    (t := Test.ptrEq left nil) hLeft hBody hLoop.within) hFinish.within).mono (by omega)

private theorem exec_mergeRuns [LinearOrder M.Value] (lt : M.Test)
    (hcmp : ∀ a b, M.evalTest lt a b = decide (a < b))
    (x : SortState M) (pre xs ys : List ℕ) (s : MergeState x pre xs ys)
    (hpos : 0 < xs.length + ys.length) :
    ∃ y, ExecWithin (mergeRuns lt) x y (12 * (xs.length + ys.length - 1) + 8) ∧
      MergeResult x y pre xs ys := by
  induction hn : xs.length + ys.length using Nat.strong_induction_on generalizing x pre xs ys with
  | ind n ih =>
    obtain ⟨endPtr, hpre⟩ := s.output
    obtain ⟨t, ht⟩ := getLast_some s.nonempty
    have htail := s.outputTail.trans ht
    have htmem := last_mem ht
    cases xs with
    | nil =>
      cases ys with
      | nil => simp at hpos
      | cons b bs =>
        have hl : x.ptr left = x.ptr nil := s.leftHead.trans s.nil_eq.symm
        have hr : x.ptr right ≠ x.ptr nil := by
          simp [s.rightHead, s.nil_eq]
        let y := afterAppend x right rightLast t
        have hafter := exec_append x right rightLast t htail
        have hpost := Program.Exec.branch_neg (I := instructionSet M layout)
          (t := Test.ptrEq right nil) (pos := .skip) hr hafter
        have hrun : Exec (mergeRuns lt) x y 5 := Program.Exec.seq
          (Program.Exec.loopUntil_exit (I := instructionSet M layout)
            (t := Test.ptrEq left nil) hl) hpost
        have hseg := append_segment (final := rightLast) hpre s.chainRight
          (by simpa only [List.append_nil] using s.nodup) ht (s.rightHead.trans (front_null _).symm)
        refine ⟨y, hrun.within.mono (by omega), ?_⟩
        refine ⟨by simpa only [mergedList, List.nil_merge] using hseg, ?_, ?_, ?_⟩
        · change x.ptr rightLast = (pre ++ mergedList x [] (b :: bs)).getLast?
          rw [mergedList, List.nil_merge, List.getLast?_append_of_ne_nil pre (by simp)]
          exact s.rightTail (by simp)
        · exact (setNext_frame x t (x.ptr right)).trans (HeapFrame.of_heap (written := []) rfl)
            (by
              simp only [List.mem_singleton, forall_eq, List.append_nil]
              exact List.mem_append_left (b :: bs) htmem)
            (by simp)
        · intro r hr _ _ _
          simp [y, afterAppend, State.setPtr, setNext, hr]
    | cons a as =>
      cases ys with
      | nil =>
        have hl : x.ptr left ≠ x.ptr nil := by simp [s.leftHead, s.nil_eq]
        have hr : x.ptr right = x.ptr nil := s.rightHead.trans s.nil_eq.symm
        let v := afterAppend x left leftLast t
        let y := v.setPtr left none
        have hafter := exec_append x left leftLast t htail
        have hbody := Program.Exec.branch_pos (I := instructionSet M layout)
          (t := Test.ptrEq right nil) (neg := emitLeast lt appendRun) hr
          (Program.Exec.seq hafter (exec_clear v left))
        have hyl : y.ptr left = y.ptr nil := by
          simp [y, v, afterAppend, State.setPtr, setNext, show nil ≠ left by decide,
            show nil ≠ tail by decide, s.nil_eq]
        have hyr : y.ptr right = y.ptr nil := by
          simp [y, v, afterAppend, State.setPtr, setNext, show nil ≠ left by decide,
            show nil ≠ tail by decide, show right ≠ left by decide, show right ≠ tail by decide, hr]
        have hrun : Exec (mergeRuns lt) x y 8 := Program.Exec.seq
          (Program.Exec.loopUntil_iter (I := instructionSet M layout)
            (t := Test.ptrEq left nil) hl hbody (Program.Exec.loopUntil_exit hyl))
          (Program.Exec.branch_pos (I := instructionSet M layout) (t := Test.ptrEq right nil)
            (neg := appendRun right rightLast) hyr Program.Exec.skip)
        have hseg := append_segment (final := leftLast) hpre s.chainLeft
          (by simpa only [List.append_nil] using s.nodup) ht (s.leftHead.trans (front_null _).symm)
        refine ⟨y, hrun.within.mono (by omega), ?_⟩
        refine ⟨by simpa only [mergedList, List.merge_right] using
          segment_heap hseg (y := y) rfl, ?_, ?_, ?_⟩
        · change x.ptr leftLast = (pre ++ mergedList x (a :: as) []).getLast?
          rw [mergedList, List.merge_right, List.getLast?_append_of_ne_nil pre (by simp)]
          exact s.leftTail (by simp)
        · exact (setNext_frame x t (x.ptr left)).trans (HeapFrame.of_heap (written := []) rfl)
            (by
              simp only [List.mem_singleton, forall_eq, List.append_nil]
              exact List.mem_append_left (a :: as) htmem)
            (by simp)
        · intro r hr hl _ _
          simp [y, v, afterAppend, State.setPtr, setNext, hr, hl]
      | cons b bs =>
        have hl : x.ptr left ≠ x.ptr nil := by simp [s.leftHead, s.nil_eq]
        have hr : x.ptr right ≠ x.ptr nil := by simp [s.rightHead, s.nil_eq]
        let w := afterLoad x a b
        by_cases hlt : key x b < key x a
        · let z := afterEmit w right b t
          have he := exec_emitLeast_right lt hcmp x pre a b t as bs s ht hlt
          have hf : HeapFrame x z [t] :=
            (HeapFrame.of_heap (x := x) (y := w) (written := []) rfl).trans
              (afterEmit_frame w right b t (by decide)) (by simp) (fun _ h => h)
          have hp (r : Fin layout.ptrRegs) (hr₁ : r ≠ tail) (hr₂ : r ≠ right) (hr₃ : r ≠ last) :
              z.ptr r = x.ptr r := afterEmit_ptr r hr₁ hr₂ hr₃
          have hperm : (pre ++ (a :: as) ++ b :: bs).Perm
              (pre ++ [b] ++ (a :: as) ++ bs) := by
            simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
              using (List.perm_middle (a := b) (l₁ := a :: as) (l₂ := bs)).append_left pre
          have hn' := hperm.nodup_iff.mp s.nodup
          have hsubRight : (pre ++ b :: bs).Nodup :=
            (by
              have huniq := s.nodup
              rw [List.append_assoc] at huniq
              exact huniq.sublist ((List.sublist_append_right (a :: as) _).append_left pre))
          have hst : MergeState z (pre ++ [b]) (a :: as) bs := by
            refine ⟨by simpa only [List.append_assoc] using hn', by simp, ⟨front bs none,
              afterEmit_segment (by decide) (segment_heap hpre (y := w) rfl)
                (segment_heap s.chainRight (y := w) rfl) hsubRight ht⟩,
              ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact afterEmit_keep (by decide) (List.nodup_append.mp s.nodup).1 ht
                (segment_heap s.chainLeft (y := w) rfl)
            · exact afterEmit_keep (by decide) (by
                exact List.Nodup.sublist
                  ((List.Sublist.cons b (List.Sublist.refl bs)).append_left pre) hsubRight)
                ht (segment_heap s.chainRight.2.2 (y := w) rfl)
            · rw [afterEmit_tail w right b t (by decide)]
              simp
            · exact (hp left (by decide) (by decide) (by decide)).trans s.leftHead
            · exact (afterEmit_src w right b t (by decide)).trans
                (s.chainRight.2.1.trans (front_null bs))
            · intro h
              exact (hp leftLast (by decide) (by decide) (by decide)).trans (s.leftTail h)
            · intro h
              exact (hp rightLast (by decide) (by decide) (by decide)).trans
                ((s.rightTail (by simp)).trans (List.getLast?_cons_of_ne_nil h))
            · exact (hp nil (by decide) (by decide) (by decide)).trans s.nil_eq
          obtain ⟨y, hy, hout⟩ := ih ((a :: as).length + bs.length) (by simp at hn ⊢; omega)
            z (pre ++ [b]) (a :: as) bs hst (by simp) rfl
          have hlist : pre ++ mergedList x (a :: as) (b :: bs) =
              (pre ++ [b]) ++ mergedList z (a :: as) bs := by
            rw [mergedList_cons_cons, ite_eq_left hlt, mergedList_congr hf.key_eq]
            simp
          refine ⟨y, (merge_step hl hr he hy).mono (by
            simp only [← hn, List.length_cons]
            omega), ?_⟩
          refine ⟨hlist.symm ▸ hout.output, hlist.symm ▸ hout.tail_eq, ?_, ?_⟩
          · exact hf.trans hout.frame (by
              simp only [List.mem_singleton, forall_eq]
              exact List.mem_append_left (b :: bs) (List.mem_append_left (a :: as) htmem))
              (fun i hi => hperm.mem_iff.mpr (by simpa only [List.append_assoc] using hi))
          · intro r hrt hrl hrr hrlast
            exact (hout.ptr_eq r hrt hrl hrr hrlast).trans (hp r hrt hrr hrlast)
        · let z := afterEmit w left a t
          have he := exec_emitLeast_left lt hcmp x pre a b t as bs s ht hlt
          have hf : HeapFrame x z [t] :=
            (HeapFrame.of_heap (x := x) (y := w) (written := []) rfl).trans
              (afterEmit_frame w left a t (by decide)) (by simp) (fun _ h => h)
          have hp (r : Fin layout.ptrRegs) (hr₁ : r ≠ tail) (hr₂ : r ≠ left) (hr₃ : r ≠ last) :
              z.ptr r = x.ptr r := afterEmit_ptr r hr₁ hr₂ hr₃
          have hn' : ((pre ++ [a]) ++ as ++ b :: bs).Nodup := by
            simpa only [List.append_assoc, List.singleton_append] using s.nodup
          have hsubLeft : (pre ++ a :: as).Nodup := (List.nodup_append.mp s.nodup).1
          have hst : MergeState z (pre ++ [a]) as (b :: bs) := by
            refine ⟨hn', by simp, ⟨front as none,
              afterEmit_segment (by decide) (segment_heap hpre (y := w) rfl)
                (segment_heap s.chainLeft (y := w) rfl) hsubLeft ht⟩,
              ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact afterEmit_keep (by decide) (by
                exact List.Nodup.sublist
                  ((List.Sublist.cons a (List.Sublist.refl as)).append_left pre) hsubLeft)
                ht (segment_heap s.chainLeft.2.2 (y := w) rfl)
            · exact afterEmit_keep (by decide) (by
                have huniq := s.nodup
                rw [List.append_assoc] at huniq
                exact huniq.sublist ((List.sublist_append_right (a :: as) _).append_left pre))
                ht (segment_heap s.chainRight (y := w) rfl)
            · rw [afterEmit_tail w left a t (by decide)]
              simp
            · exact (afterEmit_src w left a t (by decide)).trans
                (s.chainLeft.2.1.trans (front_null as))
            · exact (hp right (by decide) (by decide) (by decide)).trans s.rightHead
            · intro h
              exact (hp leftLast (by decide) (by decide) (by decide)).trans
                ((s.leftTail (by simp)).trans (List.getLast?_cons_of_ne_nil h))
            · intro h
              exact (hp rightLast (by decide) (by decide) (by decide)).trans (s.rightTail h)
            · exact (hp nil (by decide) (by decide) (by decide)).trans s.nil_eq
          obtain ⟨y, hy, hout⟩ := ih (as.length + (b :: bs).length) (by simp at hn ⊢; omega)
            z (pre ++ [a]) as (b :: bs) hst (by simp) rfl
          have hlist : pre ++ mergedList x (a :: as) (b :: bs) =
              (pre ++ [a]) ++ mergedList z as (b :: bs) := by
            rw [mergedList_cons_cons, ite_eq_right hlt, mergedList_congr hf.key_eq]
            simp
          refine ⟨y, (merge_step hl hr he hy).mono (by
            simp only [← hn, List.length_cons]
            omega), ?_⟩
          refine ⟨hlist.symm ▸ hout.output, hlist.symm ▸ hout.tail_eq, ?_, ?_⟩
          · exact hf.trans hout.frame (by
              simp only [List.mem_singleton, forall_eq]
              exact List.mem_append_left (b :: bs) (List.mem_append_left (a :: as) htmem))
              (by simp only [List.append_assoc, List.singleton_append]; exact fun _ h => h)
          · intro r hrt hrl hrr hrlast
            exact (hout.ptr_eq r hrt hrl hrr hrlast).trans (hp r hrt hrl hrlast)

private def afterStart (x : SortState M) (first final : Fin layout.ptrRegs) : SortState M :=
  (x.setPtr result (x.ptr first)).setPtr tail (x.ptr final)

private theorem exec_startOutput (x : SortState M) (first final : Fin layout.ptrRegs)
    (hfinal : final ≠ result) :
    Exec (startOutput first final) x (afterStart x first final) 2 := by
  have hm := exec_move (x.setPtr result (x.ptr first)) tail final
  have hf : (x.setPtr result (x.ptr first)).ptr final = x.ptr final := by
    simp [State.setPtr, hfinal]
  rw [hf] at hm
  exact Program.Exec.seq (exec_move x result first) hm

private def firstEmit (x : SortState M) (src : Fin layout.ptrRegs) (a : ℕ) : SortState M :=
  (((x.setPtr last (some a)).setPtr src (next x a)).setPtr result (some a)).setPtr tail (some a)

private theorem exec_firstEmit (x : SortState M) (src : Fin layout.ptrRegs) (a : ℕ)
    (hsrc : src ≠ last) (ha : a < x.heap.length) (hhead : x.ptr src = some a) :
    Exec (emit startOutput src) x (firstEmit x src a) 4 := by
  let z := (x.setPtr last (some a)).setPtr src (next x a)
  have hlast : z.ptr last = some a := by simp [z, State.setPtr, hsrc.symm]
  have hafter : afterStart z last last = firstEmit x src a := by
    simp only [afterStart, hlast]
    rfl
  rw [← hafter]
  exact Program.Exec.seq (exec_emitPrefix x src a hsrc hhead ha)
    (exec_startOutput z last last (by decide))

private theorem firstEmit_ptr {x : SortState M} {src : Fin layout.ptrRegs} {a : ℕ}
    (r : Fin layout.ptrRegs) (hsrc : r ≠ src) (hl : r ≠ last) (hresult : r ≠ result)
    (htail : r ≠ tail) : (firstEmit x src a).ptr r = x.ptr r := by
  simp [firstEmit, State.setPtr, hsrc, hl, hresult, htail]

private structure PairMergeResult [LinearOrder M.Value]
    (x y : SortState M) (pre xs ys : List ℕ) : Prop where
  output : Segment y (pre ++ mergedList x xs ys) none
  head_eq : y.ptr result = (pre ++ mergedList x xs ys).head?
  tail_eq : y.ptr tail = (pre ++ mergedList x xs ys).getLast?
  frame : HeapFrame x y (pre ++ xs ++ ys)
  ptr_eq : ∀ r, r ≠ result → r ≠ tail → r ≠ left → r ≠ right → r ≠ last →
    y.ptr r = x.ptr r

private theorem exec_initialMerge [LinearOrder M.Value] (lt : M.Test)
    (hcmp : ∀ a b, M.evalTest lt a b = decide (a < b))
    (x : SortState M) (a b : ℕ) (as bs : List ℕ)
    (hn : ((a :: as) ++ b :: bs).Nodup)
    (hleft : Segment x (a :: as) none) (hright : Segment x (b :: bs) none)
    (ha : x.ptr left = some a) (hb : x.ptr right = some b)
    (hta : x.ptr leftLast = (a :: as).getLast?) (htb : x.ptr rightLast = (b :: bs).getLast?)
    (hnil : x.ptr nil = none) :
    ∃ y, ExecWithin (emitLeast lt startOutput ▷ mergeRuns lt) x y
          (12 * ((a :: as).length + (b :: bs).length - 1) + 8) ∧
      PairMergeResult x y [] (a :: as) (b :: bs) := by
  let w := afterLoad x a b
  have hloads := exec_compareHeads x left right a b ha hb hleft.1 hright.1
  have htest : (Test.data lt 0 1).Holds w ↔ key x b < key x a := by
    simp [w, afterLoad, Test.Holds, State.setData, hcmp]
  by_cases h : key x b < key x a
  · let z := firstEmit w right b
    have hfirstEmit := exec_firstEmit w right b (by decide) hright.1 hb
    have hfirst : ExecWithin (emitLeast lt startOutput) x z 8 :=
      (Program.ExecWithin.seq hloads.within
        ((Program.Exec.branch_pos (I := instructionSet M layout) (t := Test.data lt 0 1)
          (neg := emit startOutput left) (htest.2 h) hfirstEmit).within)).mono (by decide)
    have hp (r : Fin layout.ptrRegs) (hr : r ≠ right) (hl : r ≠ last)
        (hresult : r ≠ result) (htail : r ≠ tail) : z.ptr r = x.ptr r :=
      firstEmit_ptr r hr hl hresult htail
    have hs : MergeState z [b] (a :: as) bs := by
      refine ⟨List.perm_middle.nodup_iff.mp hn, by simp, ⟨front bs none,
        hright.1, hright.2.1, trivial⟩, segment_heap hleft (y := z) rfl,
        segment_heap hright.2.2 (y := z) rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · exact (hp left (by decide) (by decide) (by decide) (by decide)).trans ha
      · have hsrc : z.ptr right = next x b := rfl
        exact hsrc.trans (hright.2.1.trans (front_null bs))
      · intro _
        exact (hp leftLast (by decide) (by decide) (by decide) (by decide)).trans hta
      · intro hbs
        exact (hp rightLast (by decide) (by decide) (by decide) (by decide)).trans
          (htb.trans (List.getLast?_cons_of_ne_nil hbs))
      · exact (hp nil (by decide) (by decide) (by decide) (by decide)).trans hnil
    obtain ⟨y, he, hout⟩ := exec_mergeRuns lt hcmp z [b] (a :: as) bs hs (by simp)
    have hframe : HeapFrame x z [] := HeapFrame.of_heap rfl
    have hlist : [] ++ mergedList x (a :: as) (b :: bs) =
        [b] ++ mergedList z (a :: as) bs := by
      rw [mergedList_cons_cons, ite_eq_left h, mergedList_congr hframe.key_eq]
      rfl
    refine ⟨y, (Program.ExecWithin.seq hfirst he).mono (by
      simp only [List.length_cons]
      omega), ?_⟩
    refine ⟨hlist.symm ▸ hout.output, ?_, hlist.symm ▸ hout.tail_eq, ?_, ?_⟩
    · rw [hlist, hout.ptr_eq result (by decide) (by decide) (by decide) (by decide)]
      rfl
    · exact hframe.trans hout.frame (by simp) (fun i hi => by
        simp only [List.nil_append]
        exact List.perm_middle.mem_iff.mpr hi)
    · intro r hr hta' hl hrr hlast
      exact (hout.ptr_eq r hta' hl hrr hlast).trans (hp r hrr hlast hr hta')
  · let z := firstEmit w left a
    have hfirstEmit := exec_firstEmit w left a (by decide) hleft.1 ha
    have hfirst : ExecWithin (emitLeast lt startOutput) x z 8 :=
      Program.ExecWithin.seq hloads.within
        ((Program.Exec.branch_neg (I := instructionSet M layout) (t := Test.data lt 0 1)
          (pos := emit startOutput right) (fun ht => h (htest.1 ht)) hfirstEmit).within)
    have hp (r : Fin layout.ptrRegs) (hr : r ≠ left) (hl : r ≠ last)
        (hresult : r ≠ result) (htail : r ≠ tail) : z.ptr r = x.ptr r :=
      firstEmit_ptr r hr hl hresult htail
    have hs : MergeState z [a] as (b :: bs) := by
      refine ⟨hn, by simp, ⟨front as none, hleft.1, hleft.2.1, trivial⟩,
        segment_heap hleft.2.2 (y := z) rfl, segment_heap hright (y := z) rfl, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · rfl
      · have hsrc : z.ptr left = next x a := rfl
        exact hsrc.trans (hleft.2.1.trans (front_null as))
      · exact (hp right (by decide) (by decide) (by decide) (by decide)).trans hb
      · intro has
        exact (hp leftLast (by decide) (by decide) (by decide) (by decide)).trans
          (hta.trans (List.getLast?_cons_of_ne_nil has))
      · intro _
        exact (hp rightLast (by decide) (by decide) (by decide) (by decide)).trans htb
      · exact (hp nil (by decide) (by decide) (by decide) (by decide)).trans hnil
    obtain ⟨y, he, hout⟩ := exec_mergeRuns lt hcmp z [a] as (b :: bs) hs (by simp)
    have hframe : HeapFrame x z [] := HeapFrame.of_heap rfl
    have hlist : [] ++ mergedList x (a :: as) (b :: bs) =
        [a] ++ mergedList z as (b :: bs) := by
      rw [mergedList_cons_cons, ite_eq_right h, mergedList_congr hframe.key_eq]
      rfl
    refine ⟨y, (Program.ExecWithin.seq hfirst he).mono (by
      simp only [List.length_cons]
      omega), ?_⟩
    refine ⟨hlist.symm ▸ hout.output, ?_, hlist.symm ▸ hout.tail_eq, ?_, ?_⟩
    · rw [hlist, hout.ptr_eq result (by decide) (by decide) (by decide) (by decide)]
      rfl
    · exact hframe.trans hout.frame (by simp) (by simp)
    · intro r hr hta' hl hrr hlast
      exact (hout.ptr_eq r hta' hl hrr hlast).trans (hp r hl hlast hr hta')

private theorem exec_finishPair [LinearOrder M.Value] (lt : M.Test)
    (hcmp : ∀ a b, M.evalTest lt a b = decide (a < b)) (first : Bool)
    (x : SortState M) (pre : List ℕ) (a b : ℕ) (as bs : List ℕ)
    (hfirst : first = true ↔ pre = []) (hnd : (pre ++ (a :: as) ++ b :: bs).Nodup)
    (hpre : Segment x pre none) (hhead : pre ≠ [] → x.ptr result = pre.head?)
    (htail : pre ≠ [] → x.ptr tail = pre.getLast?)
    (hleft : Segment x (a :: as) none) (hright : Segment x (b :: bs) none)
    (ha : x.ptr left = some a) (hb : x.ptr right = some b)
    (hta : x.ptr leftLast = (a :: as).getLast?) (htb : x.ptr rightLast = (b :: bs).getLast?)
    (hnil : x.ptr nil = none) :
    ∃ y, ExecWithin (finishPair lt first) x y
          (12 * ((a :: as).length + (b :: bs).length - 1) + 8) ∧
      PairMergeResult x y pre (a :: as) (b :: bs) := by
  cases first with
  | true =>
    have hp := hfirst.mp rfl
    subst pre
    exact exec_initialMerge lt hcmp x a b as bs hnd hleft hright ha hb hta htb hnil
  | false =>
    have hne : pre ≠ [] := fun h => by simp [h] at hfirst
    have hs : MergeState x pre (a :: as) (b :: bs) :=
      ⟨hnd, hne, ⟨none, hpre⟩, hleft, hright, htail hne, ha, hb, fun _ => hta, fun _ => htb, hnil⟩
    obtain ⟨y, he, hout⟩ := exec_mergeRuns lt hcmp x pre (a :: as) (b :: bs) hs (by simp)
    refine ⟨y, ?_, ⟨hout.output, ?_, hout.tail_eq, hout.frame, fun r _ => hout.ptr_eq r⟩⟩
    · simpa only [finishPair, Bool.false_eq_true, ite_false, Nat.zero_add] using
        Program.ExecWithin.seq (T₁ := 0) Program.ExecWithin.skip he
    · rw [hout.ptr_eq result (by decide) (by decide) (by decide) (by decide),
        hhead hne, List.head?_append_of_ne_nil _ hne]

private theorem exec_singleRun [LinearOrder M.Value] (first : Bool)
    (x : SortState M) (pre run : List ℕ) (hfirst : first = true ↔ pre = [])
    (hnd : (pre ++ run).Nodup) (hpre : Segment x pre none)
    (hhead : pre ≠ [] → x.ptr result = pre.head?)
    (htail : pre ≠ [] → x.ptr tail = pre.getLast?)
    (hchain : Segment x run none) (hrun : run ≠ [])
    (hleft : x.ptr left = run.head?) (hlast : x.ptr leftLast = run.getLast?) :
    ∃ y, ExecWithin ((if first then startOutput else appendRun) left leftLast) x y 2 ∧
      PairMergeResult x y pre run [] := by
  cases first with
  | true =>
    have hp := hfirst.mp rfl
    subst pre
    let y := afterStart x left leftLast
    refine ⟨y, (exec_startOutput x left leftLast (by decide)).within, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · simpa only [List.nil_append, mergedList, List.merge_right] using
        segment_heap hchain (y := y) rfl
    · change x.ptr left = ([] ++ mergedList x run []).head?
      simpa only [List.nil_append, mergedList, List.merge_right] using hleft
    · change x.ptr leftLast = ([] ++ mergedList x run []).getLast?
      simpa only [List.nil_append, mergedList, List.merge_right] using hlast
    · exact HeapFrame.of_heap rfl
    · intro r hresult htail _ _ _
      simp [y, afterStart, State.setPtr, hresult, htail]
  | false =>
    have hne : pre ≠ [] := fun h => by simp [h] at hfirst
    obtain ⟨a, ha⟩ := getLast_some hne
    let y := afterAppend x left leftLast a
    have hf := append_segment (final := leftLast) hpre hchain hnd ha
      (hleft.trans (front_null run).symm)
    refine ⟨y, (exec_append x left leftLast a ((htail hne).trans ha)).within,
      ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · simpa only [mergedList, List.merge_right] using hf
    · change x.ptr result = (pre ++ mergedList x run []).head?
      rw [mergedList, List.merge_right, List.head?_append_of_ne_nil _ hne]
      exact hhead hne
    · change x.ptr leftLast = (pre ++ mergedList x run []).getLast?
      rw [mergedList, List.merge_right, List.getLast?_append_of_ne_nil _ hrun]
      exact hlast
    · exact (setNext_frame x a (x.ptr left)).trans (HeapFrame.of_heap (written := []) rfl)
        (by
          simp only [List.mem_singleton, forall_eq, List.append_nil]
          exact List.mem_append_left run (last_mem ha))
        (by simp)
    · intro r _ htail _ _ _
      simp [y, afterAppend, setNext, State.setPtr, htail]

private def runCount {α : Type*} [LinearOrder α] (key : ℕ → α) : List ℕ → ℕ
  | [] => 0
  | [_] => 1
  | a :: b :: xs => runCount key (b :: xs) + if key b < key a then 1 else 0

private theorem runCount_append_of_descends {α : Type*} [LinearOrder α] (key : ℕ → α)
    {xs ys : List ℕ} (hne : xs ≠ [])
    (hord : xs.Pairwise (fun i j => key i ≤ key j))
    (hdesc : ∀ i j, xs.getLast? = some i → ys.head? = some j → key j < key i) :
    runCount key (xs ++ ys) = 1 + runCount key ys := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => rfl
      | cons b ys =>
        have hab := hdesc a b rfl rfl
        simp [runCount, hab, Nat.add_comm]
    | cons b xs =>
      have hab := (List.pairwise_cons.mp hord).1 b List.mem_cons_self
      have hord' := (List.pairwise_cons.mp hord).2
      have hdesc' : ∀ i j, (b :: xs).getLast? = some i → ys.head? = some j → key j < key i := by
        exact hdesc
      simpa only [List.cons_append, runCount, ite_eq_right (not_lt_of_ge hab), Nat.add_zero]
        using ih (by simp) hord' hdesc'

private theorem runCount_of_sorted {α : Type*} [LinearOrder α] (key : ℕ → α)
    {xs : List ℕ} (hne : xs ≠ []) (hord : xs.Pairwise (fun i j => key i ≤ key j)) :
    runCount key xs = 1 := by
  simpa [runCount] using runCount_append_of_descends key (ys := []) hne hord (by simp)

private theorem runCount_append_le {α : Type*} [LinearOrder α] (key : ℕ → α)
    (xs ys : List ℕ) : runCount key (xs ++ ys) ≤ runCount key xs + runCount key ys := by
  induction xs with
  | nil => simp [runCount]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp [runCount]
      | cons b ys =>
        simp only [List.cons_append, List.nil_append, runCount]
        split <;> omega
    | cons b xs =>
      simp only [List.cons_append] at ih
      simp only [List.cons_append, runCount]
      omega

private theorem runCount_pos {α : Type*} [LinearOrder α] (key : ℕ → α)
    {xs : List ℕ} (h : xs ≠ []) : 0 < runCount key xs := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    cases xs with
    | nil => simp [runCount]
    | cons b xs =>
      have hpos := ih (by simp)
      rw [runCount]
      omega

private theorem runCount_le_length {α : Type*} [LinearOrder α] (key : ℕ → α)
    (xs : List ℕ) : runCount key xs ≤ xs.length := by
  induction xs with
  | nil => exact le_rfl
  | cons a xs ih =>
    cases xs with
    | nil => exact le_rfl
    | cons b xs =>
      rw [runCount, List.length_cons]
      split <;> omega

private theorem clog_half_succ_le {r : ℕ} (hr : 1 < r) :
    Nat.clog 2 ((r + 1) / 2) + 1 ≤ Nat.clog 2 r := by
  have h : r + 2 - 1 = r + 1 := by omega
  have he := Nat.clog_of_one_lt Nat.one_lt_two hr
  rw [h] at he
  exact he.ge

private def sortBudget (n runs : ℕ) : ℕ :=
  (21 * n + 4) * Nat.clog 2 runs + 14 * (runs - 1) + 9 * n + 8

private theorem sortBudget_step {n runs next : ℕ} (hr : 1 < runs) (hn : next ≤ (runs + 1) / 2) :
    21 * n + 7 * ((runs + 1) / 2) + 4 + sortBudget n next ≤ sortBudget n runs := by
  have hlog : Nat.clog 2 next + 1 ≤ Nat.clog 2 runs :=
    (Nat.add_le_add_right (Nat.clog_mono_right (b := 2) hn) 1).trans (clog_half_succ_le hr)
  have hscan := Nat.mul_le_mul_left (21 * n + 4) hlog
  rw [Nat.mul_add, Nat.mul_one] at hscan
  have hpairs : 7 * ((runs + 1) / 2) + 14 * (next - 1) ≤ 14 * (runs - 1) := by omega
  unfold sortBudget
  omega

private theorem sortBudget_initial {n runs : ℕ} (hn : 0 < n) (hr : runs ≤ n) :
    3 + sortBudget n runs ≤ 21 * n * Nat.clog 2 n + 34 * n + 5 * Nat.clog 2 n - 4 := by
  have hlog := Nat.mul_le_mul_left (21 * n + 4) (Nat.clog_mono_right (b := 2) hr)
  simp only [Nat.add_mul] at hlog
  unfold sortBudget
  simp only [Nat.add_mul]
  omega

private theorem HeapFrame.heap_congr {x y x' y' : SortState M} {written : List ℕ}
    (h : HeapFrame x y written) (hx : x.heap = x'.heap) (hy : y.heap = y'.heap) :
    HeapFrame x' y' written := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← hx, ← hy]
    exact h.length_eq
  · intro a
    unfold key
    rw [← hx, ← hy]
    exact h.key_eq a
  · intro a ha
    unfold next
    rw [← hx, ← hy]
    exact h.next_eq a ha

private theorem mergedList_perm [LinearOrder M.Value] (x : SortState M) (xs ys : List ℕ) :
    (mergedList x xs ys).Perm (xs ++ ys) :=
  List.merge_perm_append _

private theorem mergedList_ordered [LinearOrder M.Value] (x : SortState M) {xs ys : List ℕ}
    (hx : xs.Pairwise fun i j => key x i ≤ key x j)
    (hy : ys.Pairwise fun i j => key x i ≤ key x j) :
    (mergedList x xs ys).Pairwise fun i j => key x i ≤ key x j := by
  have htrans (a b c : ℕ) (hab : decide (key x a ≤ key x b) = true)
      (hbc : decide (key x b ≤ key x c) = true) : decide (key x a ≤ key x c) = true :=
    decide_eq_true ((of_decide_eq_true hab).trans (of_decide_eq_true hbc))
  have htotal (a b : ℕ) : (decide (key x a ≤ key x b) || decide (key x b ≤ key x a)) = true := by
    simpa using le_total (key x a) (key x b)
  simpa only [mergedList, decide_eq_true_eq] using
    List.pairwise_merge htrans htotal xs ys (by simpa using hx) (by simpa using hy)

private structure PairInput (x : SortState M) (first : Bool) (pre input : List ℕ) : Prop where
  nodup : (pre ++ input).Nodup
  output : Segment x pre none
  remaining : Segment x input none
  first_eq : first = true ↔ pre = []
  head_eq : pre ≠ [] → x.ptr result = pre.head?
  tail_eq : pre ≠ [] → x.ptr tail = pre.getLast?
  pending_eq : x.ptr pending = input.head?
  nil_eq : x.ptr nil = none

private structure PairResult [LinearOrder M.Value]
    (x y : SortState M) (pre input : List ℕ) where
  chunk : List ℕ
  rest : List ℕ
  mergedTwo : Bool
  nonempty : chunk ≠ []
  permutation : (chunk ++ rest).Perm input
  ordered : chunk.Pairwise (fun i j => key x i ≤ key x j)
  output : Segment y (pre ++ chunk) none
  remaining : Segment y rest none
  head_eq : y.ptr result = (pre ++ chunk).head?
  tail_eq : y.ptr tail = (pre ++ chunk).getLast?
  pending_eq : y.ptr pending = rest.head?
  nil_eq : y.ptr nil = none
  frame : HeapFrame x y (pre ++ chunk)
  runCount_eq : runCount (key x) input = (if mergedTwo then 2 else 1) + runCount (key x) rest
  exhausted : mergedTwo = false → rest = []
  merged_eq : if mergedTwo then y.ptr merged ≠ none else y.ptr merged = x.ptr merged

private theorem cut_head {x y : SortState M} [LinearOrder M.Value] {r : Fin layout.ptrRegs}
    {a : ℕ} {xs : List ℕ} (cut : CutResult x y r (a :: xs)) : cut.run.head? = some a := by
  have he := congrArg List.head? cut.split
  rw [List.head?_append_of_ne_nil _ cut.nonempty] at he
  exact he.symm

private theorem exec_mergePair [LinearOrder M.Value] (lt : M.Test)
    (hcmp : ∀ a b, M.evalTest lt a b = decide (a < b)) (first : Bool)
    (x : SortState M) (pre : List ℕ) (a : ℕ) (as : List ℕ)
    (s : PairInput x first pre (a :: as)) :
    ∃ (y : SortState M) (out : PairResult x y pre (a :: as)),
      ExecWithin (mergePair lt first) x y
        (if out.mergedTwo then 21 * out.chunk.length + 5 else 9 * out.chunk.length + 1) := by
  let v := x.setPtr left (some a)
  have hm := exec_move x left pending
  rw [s.pending_eq] at hm
  obtain ⟨u, lcut, hcut⟩ := exec_cutRun lt hcmp leftLast (by decide) (by decide) (by decide)
    v a as (segment_heap s.remaining (y := v) rfl) (List.nodup_append.mp s.nodup).2.1
    (by exact s.pending_eq) (by exact s.nil_eq)
  let z := u.setPtr right (u.ptr pending)
  have hleft : z.ptr left = lcut.run.head? :=
    (lcut.ptr_eq left (by decide) (by decide) (by decide)).trans (cut_head lcut).symm
  have hright : z.ptr right = lcut.suffix.head? := lcut.pending_eq
  have hnil : z.ptr nil = none :=
    (lcut.ptr_eq nil (by decide) (by decide) (by decide)).trans s.nil_eq
  have hleftLast : z.ptr leftLast = lcut.run.getLast? := lcut.tail_eq
  have hpending : z.ptr pending = lcut.suffix.head? := lcut.pending_eq
  have hnd : (pre ++ lcut.run ++ lcut.suffix).Nodup := by
    rw [List.append_assoc, ← lcut.split]
    exact s.nodup
  have hf : HeapFrame x z lcut.run := lcut.frame.heap_congr rfl rfl
  have hpre : Segment z pre none :=
    hf.segment s.output (fun i hi hirun => (List.nodup_append.mp
      (List.nodup_append.mp hnd).1).2.2 i hi i hirun rfl)
  have hhead : pre ≠ [] → z.ptr result = pre.head? := fun hn =>
    (lcut.ptr_eq result (by decide) (by decide) (by decide)).trans (s.head_eq hn)
  have htail : pre ≠ [] → z.ptr tail = pre.getLast? := fun hn =>
    (lcut.ptr_eq tail (by decide) (by decide) (by decide)).trans (s.tail_eq hn)
  have hzMerged : z.ptr merged = x.ptr merged :=
    lcut.ptr_eq merged (by decide) (by decide) (by decide)
  have hL : Segment z lcut.run none := segment_heap lcut.chain (y := z) rfl
  have hR : Segment z lcut.suffix none := segment_heap lcut.rest (y := z) rfl
  have hlCount : runCount (key x) (a :: as) = 1 + runCount (key x) lcut.suffix :=
    (congrArg (runCount (key x)) lcut.split).trans
      (runCount_append_of_descends (key x) lcut.nonempty lcut.ordered lcut.descends)
  by_cases hs : lcut.suffix = []
  · have htest : z.ptr right = z.ptr nil := by rw [hright, hs, hnil]; rfl
    obtain ⟨y, he, out⟩ := exec_singleRun first z pre lcut.run s.first_eq
      (List.nodup_append.mp hnd).1 hpre hhead htail hL lcut.nonempty hleft hleftLast
    have hy : HeapFrame x y (pre ++ lcut.run) :=
      hf.trans out.frame (fun i hi => List.mem_append_right pre hi)
        (by simp only [List.append_nil]; exact fun _ h => h)
    have keep (r : Fin layout.ptrRegs) (hr : r ≠ result)
        (ht : r ≠ tail) (hl : r ≠ left) (hright : r ≠ right) (hlast : r ≠ last) :
        y.ptr r = z.ptr r := out.ptr_eq r hr ht hl hright hlast
    have hlastFrame : Segment y [] none := trivial
    refine ⟨y, ⟨lcut.run, [], false, lcut.nonempty, ?_, lcut.ordered, ?_, hlastFrame,
      ?_, ?_, ?_, ?_, hy, ?_, fun _ => rfl, ?_⟩, ?_⟩
    · exact List.Perm.of_eq (hs ▸ lcut.split.symm)
    · simpa only [mergedList, List.merge_right] using out.output
    · simpa only [mergedList, List.merge_right] using out.head_eq
    · simpa only [mergedList, List.merge_right] using out.tail_eq
    · exact (keep pending (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (hs ▸ hpending)
    · exact (keep nil (by decide) (by decide) (by decide) (by decide) (by decide)).trans hnil
    · exact hs ▸ hlCount
    · exact (keep merged (by decide) (by decide) (by decide) (by decide) (by decide)).trans hzMerged
    · have hpost := Program.ExecWithin.branch_pos (I := instructionSet M layout)
        (t := Test.ptrEq right nil) (neg := move merged right ▷ cutRun lt rightLast ▷
          finishPair lt first) htest he
      unfold mergePair
      apply (Program.ExecWithin.seq hm.within
        (Program.ExecWithin.seq hcut (Program.ExecWithin.seq (exec_move u right pending).within
          hpost))).mono
      have hlen := List.length_pos_iff.mpr lcut.nonempty
      simp [hs]
      omega
  · obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hs
    have htest : z.ptr right ≠ z.ptr nil := by rw [hright, hbs, hnil]; simp
    let q := z.setPtr merged (some b)
    have hm' := exec_move z merged right
    have hRptr : z.ptr right = some b := hright.trans (congrArg List.head? hbs)
    rw [hRptr] at hm'
    have hbsSeg : Segment q (b :: bs) none := hbs ▸ segment_heap hR (y := q) rfl
    have hbsNodup : (b :: bs).Nodup := hbs ▸ (List.nodup_append.mp hnd).2.1
    have hqPending : q.ptr pending = some b := hpending.trans (congrArg List.head? hbs)
    obtain ⟨w, rcut, hrCut⟩ := exec_cutRun lt hcmp rightLast (by decide) (by decide) (by decide)
      q b bs hbsSeg hbsNodup hqPending hnil
    have hsplit : lcut.suffix = rcut.run ++ rcut.suffix := hbs.trans rcut.split
    have hnd' : (pre ++ lcut.run ++ rcut.run ++ rcut.suffix).Nodup := by
      rw [List.append_assoc (pre ++ lcut.run), ← hsplit]
      exact hnd
    have hframeR : HeapFrame z w rcut.run := rcut.frame.heap_congr rfl rfl
    have hpreSeg : Segment w pre none :=
      hframeR.segment hpre (fun i hi hj => (List.nodup_append.mp
        (List.nodup_append.mp hnd').1).2.2 i (List.mem_append_left _ hi) i hj rfl)
    have hleftSeg : Segment w lcut.run none :=
      hframeR.segment hL (fun i hi hj => (List.nodup_append.mp
        (List.nodup_append.mp hnd').1).2.2 i (List.mem_append_right _ hi) i hj rfl)
    have hRightHead : w.ptr right = rcut.run.head? :=
      (rcut.ptr_eq right (by decide) (by decide) (by decide)).trans
        (hRptr.trans (cut_head rcut).symm)
    have hLeftHead : w.ptr left = lcut.run.head? :=
      (rcut.ptr_eq left (by decide) (by decide) (by decide)).trans hleft
    have hlastLeft : w.ptr leftLast = lcut.run.getLast? :=
      (rcut.ptr_eq leftLast (by decide) (by decide) (by decide)).trans hleftLast
    have hnilW : w.ptr nil = none :=
      (rcut.ptr_eq nil (by decide) (by decide) (by decide)).trans hnil
    have hheadW : pre ≠ [] → w.ptr result = pre.head? := fun hn =>
      (rcut.ptr_eq result (by decide) (by decide) (by decide)).trans (hhead hn)
    have htailW : pre ≠ [] → w.ptr tail = pre.getLast? := fun hn =>
      (rcut.ptr_eq tail (by decide) (by decide) (by decide)).trans (htail hn)
    have hmergedW : w.ptr merged = some b := rcut.ptr_eq merged (by decide) (by decide) (by decide)
    obtain ⟨d, ds, hLeftRun⟩ := List.exists_cons_of_ne_nil lcut.nonempty
    obtain ⟨e, es, hRightRun⟩ := List.exists_cons_of_ne_nil rcut.nonempty
    obtain ⟨y, he, out⟩ := exec_finishPair lt hcmp first w pre d e ds es s.first_eq
      (hLeftRun ▸ hRightRun ▸ (List.nodup_append.mp hnd').1) hpreSeg hheadW htailW
      (hLeftRun ▸ hleftSeg) (hRightRun ▸ rcut.chain)
      (hLeftHead.trans (congrArg List.head? hLeftRun))
      (hRightHead.trans (congrArg List.head? hRightRun))
      (hLeftRun ▸ hlastLeft) (hRightRun ▸ rcut.tail_eq) hnilW
    let chunk := mergedList w (d :: ds) (e :: es)
    have hperm : chunk.Perm (lcut.run ++ rcut.run) :=
      hLeftRun.symm ▸ hRightRun.symm ▸ mergedList_perm w (d :: ds) (e :: es)
    have hlen : chunk.length = lcut.run.length + rcut.run.length := by
      simpa only [List.length_append] using hperm.length_eq
    have hChunkNe : chunk ≠ [] := fun hh => by
      have hl := List.length_pos_iff.mpr lcut.nonempty
      rw [hh] at hlen
      simp only [List.length_nil] at hlen
      omega
    have hleftFrame : HeapFrame x w (pre ++ lcut.run ++ rcut.run) :=
      hf.trans hframeR (fun i hi => List.mem_append_left _ (List.mem_append_right pre hi))
        (fun i hi => List.mem_append_right _ hi)
    have hprePerm : (pre ++ chunk).Perm (pre ++ lcut.run ++ rcut.run) := by
      rw [List.append_assoc]
      exact hperm.append_left _
    have hy : HeapFrame x y (pre ++ chunk) :=
      hleftFrame.trans out.frame (fun i hi => hprePerm.mem_iff.mpr hi)
        (fun i hi => hprePerm.mem_iff.mpr (hLeftRun.symm ▸ hRightRun.symm ▸ hi))
    have hwhole : a :: as = (lcut.run ++ rcut.run) ++ rcut.suffix :=
      (lcut.split.trans (congrArg (lcut.run ++ ·) hsplit)).trans (List.append_assoc _ _ _).symm
    have hpermAll : (chunk ++ rcut.suffix).Perm (a :: as) :=
      (hperm.append_right _).trans (List.Perm.of_eq hwhole.symm)
    have hord : chunk.Pairwise (fun i j => key x i ≤ key x j) := by
      rw [show key x = key w from (funext hleftFrame.key_eq).symm]
      apply mergedList_ordered w
      · rw [show key w = key x from funext hleftFrame.key_eq, ← hLeftRun]
        exact lcut.ordered
      · rw [show key w = key q from funext rcut.frame.key_eq, ← hRightRun]
        exact rcut.ordered
    have hkeys : key q = key x := funext hf.key_eq
    have hrCount : runCount (key x) lcut.suffix = 1 + runCount (key x) rcut.suffix := by
      rw [← hkeys, hsplit]
      exact runCount_append_of_descends (key q) rcut.nonempty rcut.ordered rcut.descends
    have hzRest : Segment y rcut.suffix none :=
      out.frame.segment rcut.rest fun i hi hj => (List.nodup_append.mp hnd').2.2
        i (hLeftRun.symm ▸ hRightRun.symm ▸ hj) i hi rfl
    refine ⟨y, ⟨chunk, rcut.suffix, true, hChunkNe, hpermAll, hord, out.output, hzRest,
      out.head_eq, out.tail_eq, ?_, ?_, hy, ?_, by simp, ?_⟩, ?_⟩
    · exact (out.ptr_eq pending (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        rcut.pending_eq
    · exact (out.ptr_eq nil (by decide) (by decide) (by decide) (by decide) (by decide)).trans hnilW
    · simp only [hlCount, hrCount, ite_true]
      omega
    · rw [out.ptr_eq merged (by decide) (by decide) (by decide) (by decide) (by decide),
        hmergedW]
      simp
    · have hpost := Program.ExecWithin.branch_neg (I := instructionSet M layout)
        (t := Test.ptrEq right nil)
        (pos := (if first then startOutput else appendRun) left leftLast)
        htest (Program.ExecWithin.seq hm'.within (Program.ExecWithin.seq hrCut he))
      unfold mergePair
      apply (Program.ExecWithin.seq hm.within
        (Program.ExecWithin.seq hcut (Program.ExecWithin.seq (exec_move u right pending).within
          hpost))).mono
      have hl := List.length_pos_iff.mpr lcut.nonempty
      have hr := List.length_pos_iff.mpr rcut.nonempty
      have hlEq := congrArg List.length hLeftRun
      have hrEq := congrArg List.length hRightRun
      change _ ≤ 21 * chunk.length + 5
      simp only [ite_eq_right hs, Nat.sub_zero]
      split <;> omega

private structure PassTailResult [LinearOrder M.Value]
    (x y : SortState M) (pre input : List ℕ) where
  output : List ℕ
  permutation : output.Perm (pre ++ input)
  chain : Segment y output none
  result_eq : y.ptr result = output.head?
  nil_eq : y.ptr nil = none
  merged_nonempty : x.ptr merged ≠ none → y.ptr merged ≠ none
  frame : HeapFrame x y (pre ++ input)
  runs_le : runCount (key x) output ≤
    runCount (key x) pre + (runCount (key x) input + 1) / 2

private theorem PairResult.keepsMerged [LinearOrder M.Value] {x y : SortState M}
    {pre input : List ℕ} (out : PairResult x y pre input) :
    x.ptr merged ≠ none → y.ptr merged ≠ none := by
  cases hc : out.mergedTwo with
  | true => exact fun _ => by simpa only [hc, ite_true] using out.merged_eq
  | false =>
    intro h
    have he : y.ptr merged = x.ptr merged := by simpa [hc] using out.merged_eq
    exact he ▸ h

private theorem PairResult.remainingRunCount [LinearOrder M.Value] {x y : SortState M}
    {pre input : List ℕ} (out : PairResult x y pre input) :
    (runCount (key x) out.rest + 1) / 2 + 1 ≤ (runCount (key x) input + 1) / 2 := by
  cases hc : out.mergedTwo with
  | true =>
    have he : runCount (key x) input = 2 + runCount (key x) out.rest := by
      simpa only [hc, ite_true] using out.runCount_eq
    omega
  | false =>
    have hnil := out.exhausted hc
    have he : runCount (key x) input = 1 := by
      simpa [hc, hnil, runCount] using out.runCount_eq
    simp [he, hnil, runCount]

private theorem exec_mergeTail [LinearOrder M.Value] (lt : M.Test)
    (hcmp : ∀ a b, M.evalTest lt a b = decide (a < b))
    (x : SortState M) (pre input : List ℕ) (s : PairInput x false pre input) :
    ∃ (y : SortState M) (_out : PassTailResult x y pre input),
      ExecWithin (mergeTail lt) x y
        (21 * input.length + 7 * ((runCount (key x) input + 1) / 2) + 1) := by
  induction hn : runCount (key x) input using Nat.strong_induction_on generalizing x pre input with
  | ind n ih =>
    cases input with
    | nil =>
      have hpre : pre ≠ [] := fun h => by simpa [h] using s.first_eq
      have hstop : x.ptr pending = x.ptr nil := s.pending_eq.trans s.nil_eq.symm
      refine ⟨x, ⟨pre, by simp, s.output, s.head_eq hpre, s.nil_eq, id, HeapFrame.of_heap rfl,
        by simp [runCount]⟩, ?_⟩
      change ExecWithin (.loopUntil (.ptrEq pending nil) _) x x _
      exact (Program.ExecWithin.loopUntil_exit (I := instructionSet M layout)
        (t := Test.ptrEq pending nil) hstop).mono (by omega)
    | cons a as =>
      have hactive : x.ptr pending ≠ x.ptr nil := by simp [s.pending_eq, s.nil_eq]
      obtain ⟨z, pair, hz⟩ := exec_mergePair lt hcmp false x pre a as s
      have hperm : (pre ++ pair.chunk ++ pair.rest).Perm (pre ++ a :: as) := by
        rw [List.append_assoc]
        exact pair.permutation.append_left pre
      have hpreNe : pre ++ pair.chunk ≠ [] := by simp [pair.nonempty]
      have hsz : PairInput z false (pre ++ pair.chunk) pair.rest :=
        ⟨hperm.nodup_iff.mpr s.nodup, pair.output, pair.remaining, by simp [hpreNe],
          fun _ => pair.head_eq, fun _ => pair.tail_eq, pair.pending_eq, pair.nil_eq⟩
      have hkey : key z = key x := funext pair.frame.key_eq
      have hstep : runCount (key z) pair.rest < n := by
        rw [hkey, ← hn]
        have he := pair.runCount_eq
        split at he <;> omega
      obtain ⟨y, out, hy⟩ := ih (runCount (key z) pair.rest) hstep z
        (pre ++ pair.chunk) pair.rest hsz rfl
      have hfr : HeapFrame x y (pre ++ a :: as) :=
        pair.frame.trans out.frame
          (fun i hi => hperm.mem_iff.mp (List.mem_append_left pair.rest hi))
          (fun i hi => hperm.mem_iff.mp hi)
      have hpieces : runCount (key x) (pre ++ pair.chunk) ≤ runCount (key x) pre + 1 :=
        (runCount_append_le (key x) pre pair.chunk).trans_eq
          (congrArg (runCount (key x) pre + ·)
            (runCount_of_sorted (key x) pair.nonempty pair.ordered))
      have hpairs := pair.remainingRunCount
      have hsize := pair.permutation.length_eq
      simp only [List.length_append, List.length_cons] at hsize
      refine ⟨y, ⟨out.output, out.permutation.trans hperm, out.chain, out.result_eq, out.nil_eq,
        out.merged_nonempty ∘ pair.keepsMerged, hfr, ?_⟩, ?_⟩
      · have ho := out.runs_le
        rw [hkey] at ho
        omega
      · have hbound := hz.mono (show _ ≤ 21 * pair.chunk.length + 5 by split <;> omega)
        exact (Program.ExecWithin.loopUntil_iter (I := instructionSet M layout)
          (t := Test.ptrEq pending nil) hactive hbound hy).mono (by
            rw [hkey]
            simp only [List.length_cons]
            omega)

private structure PassResult [LinearOrder M.Value] (x y : SortState M) (input : List ℕ) where
  output : List ℕ
  permutation : output.Perm input
  chain : Segment y output none
  head_eq : y.ptr head = output.head?
  nil_eq : y.ptr nil = none
  frame : HeapFrame x y input
  runs_le : runCount (key x) output ≤ (runCount (key x) input + 1) / 2
  stop_iff : y.ptr merged = none ↔ runCount (key x) input = 1
  sorted_if_stop : y.ptr merged = none → output.Pairwise (fun a b => key x a ≤ key x b)

private def passBudget (n runs : ℕ) : ℕ :=
  if runs = 1 then 9 * n + 5 else 21 * n + 7 * ((runs + 1) / 2) + 2

private theorem exec_mergePass [LinearOrder M.Value] (lt : M.Test)
    (hcmp : ∀ a b, M.evalTest lt a b = decide (a < b))
    (x : SortState M) (a : ℕ) (as : List ℕ)
    (hSeg : Segment x (a :: as) none) (hNd : (a :: as).Nodup)
    (hhead : x.ptr head = some a) (hnil : x.ptr nil = none) :
    ∃ (y : SortState M) (_out : PassResult x y (a :: as)),
      ExecWithin (mergePass lt) x y (passBudget (a :: as).length (runCount (key x) (a :: as))) := by
  let w := x.setPtr pending (some a)
  let z := w.setPtr merged none
  have hm := exec_move x pending head
  rw [hhead] at hm
  have hclear := exec_clear w merged
  have hzSeg : Segment z (a :: as) none := segment_heap hSeg (y := z) rfl
  have hzNil : z.ptr nil = none := by exact hnil
  have hzPending : z.ptr pending = (a :: as).head? := rfl
  have hpairState : PairInput z true [] (a :: as) :=
    ⟨hNd, trivial, hzSeg, by simp, fun h => False.elim (h rfl),
      fun h => False.elim (h rfl), hzPending, hzNil⟩
  obtain ⟨u, p, hp⟩ := exec_mergePair lt hcmp true z [] a as hpairState
  have hkeysZ : key z = key x := rfl
  have hkeysU : key u = key x := (funext p.frame.key_eq).trans hkeysZ
  have hpPerm : (p.chunk ++ p.rest).Perm (a :: as) := p.permutation
  have hpLen := hpPerm.length_eq
  simp only [List.length_append, List.length_cons] at hpLen
  have hc := p.runCount_eq
  rw [hkeysZ] at hc
  cases ht : p.mergedTwo with
  | false =>
    have hrest : p.rest = [] := p.exhausted ht
    have hcount : runCount (key x) (a :: as) = 1 := by
      simpa [ht, hrest, runCount] using hc
    have hpr : p.chunk.Perm (a :: as) := by simpa only [hrest, List.append_nil] using hpPerm
    have huMerged : u.ptr merged = none := by
      have he : u.ptr merged = z.ptr merged := by simpa [ht] using p.merged_eq
      exact he.trans rfl
    have hstop : u.ptr pending = u.ptr nil := by rw [p.pending_eq, hrest, p.nil_eq]; rfl
    have heTail : ExecWithin (mergeTail lt) u u 1 :=
      Program.ExecWithin.loopUntil_exit (I := instructionSet M layout)
        (t := Test.ptrEq pending nil) hstop
    let y := u.setPtr head (u.ptr result)
    have hmove := exec_move u head result
    have hframe : HeapFrame x y (a :: as) :=
      (p.frame.heap_congr (x' := x) (y' := y) rfl rfl).trans (HeapFrame.of_heap (written := []) rfl)
        (by simpa only [List.nil_append] using fun i hi => hpr.mem_iff.mp hi) (by simp)
    have hord : p.chunk.Pairwise (fun i j => key x i ≤ key x j) := by
      simpa only [hkeysZ] using p.ordered
    refine ⟨y, ⟨p.chunk, hpr, ?_, ?_, p.nil_eq, hframe, ?_, ?_, fun _ => hord⟩, ?_⟩
    · simpa only [List.nil_append] using segment_heap p.output (y := y) rfl
    · change u.ptr result = p.chunk.head?
      simpa only [List.nil_append] using p.head_eq
    · rw [hcount, runCount_of_sorted (key x) p.nonempty hord]
    · change u.ptr merged = none ↔ runCount (key x) (a :: as) = 1
      simp [huMerged, hcount]
    · have hp' : ExecWithin (mergePair lt true) z u (9 * p.chunk.length + 1) := by
        simpa [ht] using hp
      unfold mergePass
      apply (Program.ExecWithin.seq hm.within
        (Program.ExecWithin.seq hclear.within
          (Program.ExecWithin.seq hp' (Program.ExecWithin.seq heTail hmove.within)))).mono
      simp only [passBudget, hcount, ite_true]
      have hpLength := hpr.length_eq
      omega
  | true =>
    have hcount : runCount (key x) (a :: as) = 2 + runCount (key x) p.rest := by
      simpa only [ht, ite_true] using hc
    have hmore : runCount (key x) (a :: as) ≠ 1 := by omega
    have huMerged : u.ptr merged ≠ none := by simpa only [ht, ite_true] using p.merged_eq
    have hpNe : p.chunk ≠ [] := p.nonempty
    have hs : PairInput u false p.chunk p.rest := by
      refine ⟨hpPerm.nodup_iff.mpr hNd, ?_, p.remaining, by simp [hpNe], ?_, ?_, p.pending_eq,
        p.nil_eq⟩
      · simpa only [List.nil_append] using p.output
      · intro _
        simpa only [List.nil_append] using p.head_eq
      · intro _
        simpa only [List.nil_append] using p.tail_eq
    obtain ⟨v, tailRes, hv⟩ := exec_mergeTail lt hcmp u p.chunk p.rest hs
    let y := v.setPtr head (v.ptr result)
    have hmove := exec_move v head result
    have hframe : HeapFrame x y (a :: as) :=
      (p.frame.heap_congr (x' := x) (y' := u) rfl rfl).trans
        (tailRes.frame.heap_congr (x' := u) (y' := y) rfl rfl)
        (by simpa only [List.nil_append] using
          fun i hi => hpPerm.mem_iff.mp (List.mem_append_left p.rest hi))
        (fun i hi => hpPerm.mem_iff.mp hi)
    have hnonstop : y.ptr merged ≠ none := tailRes.merged_nonempty huMerged
    refine ⟨y, ⟨tailRes.output, tailRes.permutation.trans hpPerm,
      segment_heap tailRes.chain (y := y) rfl, tailRes.result_eq, tailRes.nil_eq, hframe,
      ?_, ?_, fun h => (hnonstop h).elim⟩, ?_⟩
    · have ht' := tailRes.runs_le
      rw [hkeysU] at ht'
      have hord : p.chunk.Pairwise (fun i j => key x i ≤ key x j) := by
        simpa only [hkeysZ] using p.ordered
      rw [runCount_of_sorted (key x) p.nonempty hord] at ht'
      omega
    · simp [hmore, hnonstop]
    · have hp' : ExecWithin (mergePair lt true) z u (21 * p.chunk.length + 5) := by
        simpa only [ht, ite_true] using hp
      unfold mergePass
      apply (Program.ExecWithin.seq hm.within
        (Program.ExecWithin.seq hclear.within
          (Program.ExecWithin.seq hp' (Program.ExecWithin.seq hv hmove.within)))).mono
      simp only [passBudget, ite_eq_right hmore, hkeysU, List.length_cons]
      omega

/-- The empty segment requires no records. -/
@[simp] theorem segment_nil (x : State M layout) (p : Pointer) : Segment x [] p := by
  simp [Segment]

/-- A segment starting at an address requires an allocated node whose link reaches the following
node or the terminal pointer. -/
theorem segment_cons_iff (x : State M layout) (a : ℕ) (xs : List ℕ) (p : Pointer) :
    Segment x (a :: xs) p ↔ a < x.heap.length ∧
      (x.heap[a]?).bind (fun node => node.ptr 0) = xs.head?.or p ∧ Segment x xs p := by
  have hfront : front xs p = xs.head?.or p := by cases xs <;> rfl
  simp only [Segment, next, hfront]

/-- The final head and linked order, and the payload and space guarantees of sorting. -/
structure SortedOutput [LinearOrder M.Value] (x y : State M layout)
    (input output : List ℕ) : Prop where
  /-- The program returns the sorted list in its head register. -/
  head_eq : y.ptr head = output.head?
  /-- The sorted list is a null-terminated chain. -/
  chain : Segment y output none
  /-- Sorting retains exactly the original addresses. -/
  permutation : output.Perm input
  /-- The keys are nondecreasing along the output chain. -/
  ordered : output.Pairwise (fun a b => key x a ≤ key x b)
  /-- Sorting preserves the payload of each record. -/
  key_eq : ∀ a, key y a = key x a
  /-- The heap has the same number of records after sorting. -/
  heap_length_eq : y.heap.length = x.heap.length

/-- Reading the keys along the final chain gives the reference list sort. -/
theorem SortedOutput.payloads_eq [LinearOrder M.Value] {x y : State M layout}
    {input output : List ℕ} (h : SortedOutput x y input output) :
    output.map (key y) = (input.map (key x)).mergeSort := by
  rw [show key y = key x from funext h.key_eq]
  exact ((h.permutation.map (key x)).trans (List.mergeSort_perm _ _).symm).eq_of_pairwise'
    (List.pairwise_map.mpr h.ordered) (List.pairwise_mergeSort' _ _)

private theorem exec_sortLoop [LinearOrder M.Value] (lt : M.Test)
    (hcmp : ∀ a b, M.evalTest lt a b = decide (a < b))
    (x : SortState M) (input : List ℕ) (hchain : Segment x input none)
    (hnd : input.Nodup) (hhead : x.ptr head = input.head?)
    (hinput : input ≠ []) (hnil : x.ptr nil = none) (hactive : x.ptr merged ≠ none) :
    ∃ y output, ExecWithin (.loopUntil (.ptrEq merged nil) (mergePass lt)) x y
        (sortBudget input.length (runCount (key x) input)) ∧ SortedOutput x y input output := by
  induction hn : runCount (key x) input using Nat.strong_induction_on generalizing x input with
  | ind r ih =>
    cases input with
    | nil => contradiction
    | cons a as =>
      have hall : x.ptr merged ≠ x.ptr nil := hnil.symm ▸ hactive
      obtain ⟨z, pass, hz⟩ := exec_mergePass lt hcmp x a as hchain hnd hhead hnil
      have hkeys : key z = key x := funext pass.frame.key_eq
      have hOutputNonempty : pass.output ≠ [] :=
        fun he => by simpa [he] using pass.permutation.length_eq
      have hOutputSize := pass.permutation.length_eq
      by_cases hstop : z.ptr merged = none
      · have hr : r = 1 := hn ▸ pass.stop_iff.mp hstop
        have hdone : z.ptr merged = z.ptr nil := hstop.trans pass.nil_eq.symm
        have hrun := Program.ExecWithin.loopUntil_iter (I := instructionSet M layout)
          (t := Test.ptrEq merged nil) hall hz
          (Program.ExecWithin.loopUntil_exit hdone)
        refine ⟨z, pass.output, hrun.mono ?_,
          ⟨pass.head_eq, pass.chain, pass.permutation, pass.sorted_if_stop hstop,
            pass.frame.key_eq, pass.frame.length_eq⟩⟩
        simp [sortBudget, passBudget, hn, hr]
      · have hr : 1 < r := by
          have hpos := runCount_pos (key x) (by simp : a :: as ≠ [])
          have hne : r ≠ 1 := hn ▸ fun he => hstop (pass.stop_iff.mpr he)
          omega
        have hR : runCount (key z) pass.output ≤ (r + 1) / 2 := by
          rw [hkeys]
          exact hn ▸ pass.runs_le
        have hlt : runCount (key z) pass.output < r := by omega
        obtain ⟨y, out, hy, hafter⟩ := ih (runCount (key z) pass.output) hlt z pass.output
          pass.chain (pass.permutation.nodup_iff.mpr hnd) pass.head_eq
          hOutputNonempty pass.nil_eq hstop rfl
        have hrun := Program.ExecWithin.loopUntil_iter (I := instructionSet M layout)
          (t := Test.ptrEq merged nil) hall hz hy
        refine ⟨y, out, hrun.mono ?_, ⟨hafter.head_eq, hafter.chain,
          hafter.permutation.trans pass.permutation, ?_,
          fun i => (hafter.key_eq i).trans (pass.frame.key_eq i),
          hafter.heap_length_eq.trans pass.frame.length_eq⟩⟩
        · have hbudget := sortBudget_step (n := (a :: as).length) hr hR
          rw [hOutputSize]
          simp only [passBudget, hn, ite_eq_right (show r ≠ 1 by omega)]
          omega
        · simpa only [hkeys] using hafter.ordered

/-- An upper bound on the number of flat instructions, including the halt, on a list of
length `n`. -/
@[expose] def instructionBound (n : ℕ) : ℕ :=
  if n = 0 then 4 else 21 * n * Nat.clog 2 n + 34 * n + 5 * Nat.clog 2 n - 4

/-- With a supplied strict key comparison, the native pointer program sorts any prepared
null-terminated list with distinct node addresses. The timed execution includes the halt and
initializer, and starts with the input records and head register supplied. -/
theorem executes_sort [LinearOrder M.Value] (lt : M.Test)
    (hcmp : ∀ a b, M.evalTest lt a b = decide (a < b))
    (x : State M layout) (input : List ℕ) (hchain : Segment x input none)
    (hnd : input.Nodup) (hhead : x.ptr head = input.head?) (hpc : x.pc = 0) :
    ∃ y t output, Executes (code lt).program x y t ∧
      t ≤ instructionBound input.length ∧ SortedOutput x y input output := by
  let v := x.setPtr nil none
  let w := v.setPtr merged (x.ptr head)
  have hclear := exec_clear x nil
  have hmove : Exec (move merged head) v w 1 := exec_move v merged head
  have hnil : w.ptr nil = none := rfl
  have hwhead : w.ptr head = input.head? := hhead
  have hprefix : w.heap = x.heap := rfl
  cases input with
  | nil =>
    have hstop : w.ptr merged = w.ptr nil := hhead.trans hnil.symm
    have hloop := Program.Exec.loopUntil_exit (I := instructionSet M layout)
      (t := Test.ptrEq merged nil) (body := mergePass lt) hstop
    have he : Exec (code lt) x w 3 := Program.Exec.seq hclear (Program.Exec.seq hmove hloop)
    let y := { w with pc := (code lt).size }
    exact ⟨y, 4, [], he.executes hpc, by simp [instructionBound],
      ⟨hwhead, segment_nil .., List.Perm.nil, List.Pairwise.nil, fun _ => rfl, rfl⟩⟩
  | cons a as =>
    have hactive : w.ptr merged ≠ none := fun he =>
      Option.some_ne_none a (hhead.symm.trans he)
    obtain ⟨z, out, hz, ho⟩ := exec_sortLoop lt hcmp w (a :: as)
      (segment_heap hchain hprefix.symm) hnd hwhead (by simp) hnil hactive
    have hfull : ExecWithin (code lt) x z (1 + (1 + sortBudget (a :: as).length
        (runCount (key w) (a :: as)))) :=
      Program.ExecWithin.seq hclear.within (Program.ExecWithin.seq hmove.within hz)
    obtain ⟨time, htime, he⟩ := hfull.executes hpc
    let y := { z with pc := (code lt).size }
    have hb := sortBudget_initial (n := (a :: as).length)
      (by simp) (runCount_le_length (key w) (a :: as))
    refine ⟨y, time, out, he, ?_,
      ⟨ho.head_eq, segment_heap ho.chain (y := y) rfl, ho.permutation, ?_,
        fun i => (ho.key_eq i).trans rfl, ho.heap_length_eq.trans (congrArg List.length hprefix)⟩⟩
    · have hlen : (a :: as).length ≠ 0 :=
        (List.length_pos_iff.mpr (by simp)).ne'
      rw [instructionBound, ite_eq_right hlen]
      omega
    · exact ho.ordered

section WordRAM

open Cslib.PointerMachine.WordRAM

private theorem naturalProgram_no_create (r : Fin layout.ptrRegs) :
    Instr.create r ∉ (code (M := Natural.model) Natural.Test.lt).program := by
  let allocates : Instr Natural.model layout → Bool
    | .create _ => true
    | _ => false
  have h : ((code (M := Natural.model) Natural.Test.lt).program).any allocates = false := by decide
  intro hr
  exact (List.any_eq_false.mp h _ hr) rfl

/-- Compiling the natural-key sorter costs at most seven word-RAM instructions per pointer
instruction, including the halt, when the prepared state and execution bound fit the word size. -/
theorem wordRAM_executes_of_executes {w time limit b : ℕ} {x y : State Natural.model layout}
    (valid : x.Valid) (execution : Executes (code Natural.Test.lt).program x y time)
    (bound : time ≤ limit) (initial : x.DataValid (· ≤ b))
    (memory : Cslib.WordRAM.Fits w (nodeAddr layout (x.heap.length + limit)))
    (values : Cslib.WordRAM.Fits w (b + limit)) :
    let program := (code (M := Natural.model) Natural.Test.lt).program
    let compiler := Natural.scalars layout
    ∃ z k, k + 1 ≤ 7 * time ∧
      Cslib.WordRAM.Runs w (compiler.compile program)
        ⟨compiler.blockSize program * x.pc, encodeState compiler.encode x⟩
        ⟨compiler.blockSize program * y.pc, z⟩ k ∧ Repr compiler.encode y z ∧
      Cslib.WordRAM.step w (compiler.compile program)
        ⟨compiler.blockSize program * y.pc, z⟩ = .halt 0 := by
  obtain ⟨z, k, hcost, hruns, hrepr, hhalt⟩ :=
    Natural.executes_compile valid execution bound initial memory values
  have overhead := Natural.overhead_le_of_no_create _ naturalProgram_no_create
  exact ⟨z, k, hcost.trans (Nat.mul_le_mul_right _ overhead), hruns, hrepr, hhalt⟩

/-- From the encoded prepared list, the compiled natural-key sorter produces the same linked
order and payloads as the pointer sorter. For a nonempty input the bound is
`147 * N * L + 238 * N + 35 * L - 28`, where `L = Nat.clog 2 N`. The count includes halt. -/
theorem wordRAM_executes_sort {w b : ℕ} (x : State Natural.model layout)
    (input : List ℕ) (valid : x.Valid) (chain : Segment x input none) (distinct : input.Nodup)
    (head_eq : x.ptr head = input.head?) (pc : x.pc = 0) (initial : x.DataValid (· ≤ b))
    (memory : Cslib.WordRAM.Fits w
      (nodeAddr layout (x.heap.length + instructionBound input.length)))
    (values : Cslib.WordRAM.Fits w (b + instructionBound input.length)) :
    let n := input.length
    let L := Nat.clog 2 n
    let program := (code (M := Natural.model) Natural.Test.lt).program
    let compiler := Natural.scalars layout
    ∃ y output z k, SortedOutput x y input output ∧
      k + 1 ≤ (if n = 0 then 28 else 147 * n * L + 238 * n + 35 * L - 28) ∧
      Cslib.WordRAM.Runs w (compiler.compile program) ⟨0, encodeState compiler.encode x⟩
        ⟨compiler.blockSize program * y.pc, z⟩ k ∧ Repr compiler.encode y z ∧
      Cslib.WordRAM.step w (compiler.compile program)
        ⟨compiler.blockSize program * y.pc, z⟩ = .halt 0 := by
  obtain ⟨y, t, output, hrun, htime, hsorted⟩ :=
    executes_sort Natural.Test.lt (fun _ _ => rfl) x input chain distinct head_eq pc
  obtain ⟨z, k, hcost, hruns, hrepr, hhalt⟩ :=
    wordRAM_executes_of_executes valid hrun htime initial memory values
  refine ⟨y, output, z, k, hsorted, ?_, ?_, hrepr, hhalt⟩
  · refine hcost.trans ((Nat.mul_le_mul_left 7 htime).trans ?_)
    change 7 * instructionBound input.length ≤ _
    by_cases hn : input.length = 0 <;>
      simp [instructionBound, hn, Nat.mul_sub, Nat.mul_add, ← Nat.mul_assoc]
  · simpa only [pc, Nat.mul_zero] using hruns

end WordRAM

end Cslib.Algorithms.PointerMachine.MergeSort
