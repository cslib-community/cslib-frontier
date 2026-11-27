/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.PointerMachine.Local

/-!
# Buffered merge sort with local addresses

The two merge buffers contain references to key records. Reading a head follows its stored
reference, and writing a head copies the reference. Scratch and run cursors move by one cell.
The buffers exchange roles after each pass.

The supplied key area stores the key and original index in consecutive cells. The program
initializes the reference buffer by walking the key area, runs the merge passes, and reads
back numeric indices into the first buffer's payloads.

## Main definitions

* `code`: the structured local-address sorter.
* `inputState`, `permutation`: the prepared input and the numeric output.
-/

public section

namespace Cslib.Algorithms.WordRAM.MergeSort.LocalRef

open Cslib.WordRAM.Local

/-- Scalar operations used for the run lengths and counters. -/
inductive Scalar where
  | add
  | sub

/-- Natural-number keys and counters with addition, subtraction, and less-than. -/
@[expose, reducible] def model : Cslib.PointerMachine.Model where
  Value := ℕ
  undefined := 0
  Op := Scalar
  Test := Unit
  evalOp
    | .add, a, b => a + b
    | .sub, a, b => a - b
  evalTest _ a b := decide (a < b)

private abbrev key : Fin 9 := 0
private abbrev perm : Fin 9 := 1
private abbrev src : Fin 9 := 2
private abbrev dst : Fin 9 := 3
private abbrev left : Fin 9 := 4
private abbrev right : Fin 9 := 5
private abbrev out : Fin 9 := 6
private abbrev lkey : Fin 9 := 7
private abbrev rkey : Fin 9 := 8

private abbrev zero : Fin 11 := 0
private abbrev one : Fin 11 := 1
private abbrev len : Fin 11 := 2
private abbrev width : Fin 11 := 3
private abbrev remain : Fin 11 := 4
private abbrev lcount : Fin 11 := 5
private abbrev rcount : Fin 11 := 6
private abbrev walk : Fin 11 := 7
private abbrev lvalue : Fin 11 := 8
private abbrev rvalue : Fin 11 := 9
private abbrev two : Fin 11 := 10

private abbrev SortCode := Program.Code (Op model 9 11) (Test model 9 11)
private abbrev instr := @Program.Code.op (Op model 9 11) (Test model 9 11)
local infixr:70 " ▷ " => Program.Code.seq

private def less (a b : Fin 11) : Test model 9 11 := .scalar () a b

private def next (r : Fin 9) : SortCode := instr (.move .next r r)

private def dec (r : Fin 11) : SortCode := instr (.scalar .sub r r one)

private def copyScalar (dst src : Fin 11) : SortCode := instr (.copyData dst src)

private def copyRef (dst src : Fin 9) : SortCode := instr (.copyAddr dst src)

private def emit (head item : Fin 9) (count : Fin 11) : SortCode :=
  instr (.storeAddr out item) ▷ next out ▷ next head ▷ dec count

private def initReferences : SortCode :=
  copyRef out perm ▷ copyScalar remain len ▷
    .loopUntil (less remain one)
      (instr (.storeAddr out key) ▷ next out ▷ next key ▷ next key ▷ dec remain)

private def takeRun (count : Fin 11) : SortCode :=
  .branch (less remain width) (copyScalar count remain) (copyScalar count width) ▷
    instr (.scalar .sub remain remain count)

private def mergePair : SortCode :=
  takeRun lcount ▷ takeRun rcount ▷
  copyRef right left ▷ copyScalar walk lcount ▷
  .loopUntil (less walk one) (next right ▷ dec walk) ▷
  .loopUntil (less lcount one)
    (instr (.loadAddr lkey left) ▷
      .branch (less zero rcount)
        (instr (.loadAddr rkey right) ▷ instr (.loadData lvalue lkey) ▷
          instr (.loadData rvalue rkey) ▷
          .branch (less rvalue lvalue) (emit right rkey rcount) (emit left lkey lcount))
        (emit left lkey lcount)) ▷
  .loopUntil (less rcount one) (instr (.loadAddr rkey right) ▷ emit right rkey rcount) ▷
  copyRef left right

private def mergePass : SortCode :=
  copyScalar remain len ▷ copyRef left src ▷ copyRef out dst ▷
  .loopUntil (less remain one) mergePair ▷
  copyRef left src ▷ copyRef src dst ▷ copyRef dst left ▷
  instr (.scalar .add width width width)

private def readPermutation : SortCode :=
  copyRef out perm ▷ copyScalar remain len ▷
  .loopUntil (less remain one)
    (instr (.loadAddr key src) ▷ next key ▷ instr (.loadData lvalue key) ▷
      instr (.storeData out lvalue) ▷ next out ▷ next src ▷ dec remain)

-- The two-cell output is initially zero. Only the entry for the second key needs a write.
private def sortTwo : SortCode :=
  instr (.loadData lvalue key) ▷ next key ▷ next key ▷ instr (.loadData rvalue key) ▷
  copyRef out perm ▷
  .branch (less rvalue lvalue)
    (instr (.storeData out one))
    (next out ▷ instr (.storeData out one))

/-- Sort references by key and write their original indices into the output buffer. -/
def code : Program.Code (Op model 9 11) (Test model 9 11) :=
  .branch (less two len)
    (initReferences ▷ copyScalar width one ▷ .loop (less width len) mergePass ▷ readPermutation)
    (.branch (less one len) sortTwo .skip)

private def permBase (n : ℕ) : ℕ := 2 * n + 1

private def scratchBase (n : ℕ) : ℕ := 3 * n + 2

/-- Prepared state with alternating key and index payloads and two empty reference buffers.
Each area has a spare cell for the cursor after its last item.
The first buffer starts with zero payloads. For two keys, a comparison determines which
output cell receives index one. -/
def inputState (keys : List ℕ) : Data model (4 * keys.length + 3) 9 11 :=
  let n := keys.length
  { addr := fun r =>
      if r = key then some ⟨0, by omega⟩
      else if r = perm ∨ r = src then some ⟨permBase n, by unfold permBase; omega⟩
      else if r = dst then some ⟨scratchBase n, by unfold scratchBase; omega⟩
      else none
    scalars := fun r => if r = len then n else if r = one then 1 else if r = two then 2 else 0
    values := fun a =>
      if a.val < 2 * n then
        if a.val % 2 = 0 then keys[a.val / 2]?.getD 0 else a.val / 2
      else 0
    refs := fun _ => none }

/-- Read the numeric permutation from the first buffer. -/
def permutation {n : ℕ} (x : Data model (4 * n + 3) 9 11) : List ℕ :=
  List.ofFn fun i : Fin n => x.values ⟨permBase n + i.val, by
    have := i.isLt
    unfold permBase
    omega⟩

end Cslib.Algorithms.WordRAM.MergeSort.LocalRef
