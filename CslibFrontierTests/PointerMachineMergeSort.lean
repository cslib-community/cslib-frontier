/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

meta import CslibFrontier.Algorithms.PointerMachine.MergeSort

/-! # Executable checks for in-place pointer-machine merge sort -/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.PointerMachineMergeSort

open Cslib.PointerMachine Cslib.Algorithms.PointerMachine.MergeSort

private meta abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Empty
  Test := Unit
  evalOp op := op.elim
  evalTest _ a b := decide (a < b)

private meta def program := (code (M := model) ()).program

-- The physical order of the records is independent of the input list order.
private meta def input (keys order : List ℕ) : State model layout :=
  ⟨0, fun r => if r = head then order.head? else none, fun _ => 0,
    (List.range keys.length).map fun i =>
      ⟨fun _ => (order.dropWhile (· != i)).tail.head?, fun _ => keys[i]?.getD 0⟩⟩

private meta def execute : ℕ → State model layout → Option (State model layout)
  | 0, _ => none
  | fuel + 1, x =>
    match step program x with
    | some y => execute fuel y
    | none => if x.pc == (code (M := model) ()).size then some x else none

-- Read exactly the expected number of nodes and require a null terminator.
private meta def readList (heap : List (Record model layout)) :
    ℕ → Pointer → Option (List ℕ)
  | 0, none => some []
  | n + 1, some i => do
    let node ← heap[i]?
    let rest ← readList heap n (node.ptr 0)
    pure (i :: rest)
  | _, _ => none

private meta def checksSort (keys order : List ℕ) : Bool :=
  match execute (100 * (order.length + 1) ^ 2) (input keys order) with
  | none => false
  | some y =>
    y.heap.map (fun node => node.data 0) == keys &&
      readList y.heap order.length (y.ptr head) ==
        some (order.mergeSort fun i j => keys[i]?.getD 0 ≤ keys[j]?.getD 0)

#guard checksSort [] []
#guard checksSort [7] [0]
#guard checksSort [4, 1, 4, 0, 3, 2, 0] [5, 3, 6, 0, 1, 2, 4]
#guard checksSort [2, 2, 0, 1] [1, 0, 3]

private meta def ternaryLists : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (ternaryLists n).flatMap fun xs => [0, 1, 2].map (· :: xs)

#guard (List.range 7).all fun n =>
  (ternaryLists n).all fun keys => checksSort keys (List.range n)

end CslibFrontierTests.PointerMachineMergeSort
