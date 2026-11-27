/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

meta import CslibFrontier.Algorithms.WordRAM.MergeSort
meta import CslibFrontier.Algorithms.WordRAM.MergeSort.Local
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval

/-! # Executable checks for buffered merge sort with local addresses -/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.WordRAMLocalMergeSort

open Cslib Cslib.WordRAM Cslib.Algorithms.WordRAM.MergeSort

private meta def localResult (keys : List ℕ) : Option (List ℕ × ℕ) :=
  let n := keys.length
  let x := LocalRef.inputState keys
  let x := { x with values := fun a => if a.val < n then x.values a else 99 }
  (Program.Code.eval (Local.instructionSet LocalRef.model (3 * n) 9 11)
    n LocalRef.code x).map fun (x, steps) =>
      (LocalRef.permutation (n := n) x, steps)

private meta def indexedResult (keys : List ℕ) : Option (List ℕ × ℕ) :=
  let n := keys.length
  let x : Data 18 :=
    ⟨fun r => if r = Reg.len then n else if r = Reg.keyBase then 0
      else if r = Reg.permBase then n else if r = Reg.bufBase then 2 * n else 0,
     fun i => keys[i]?.getD 0⟩
  (mergeSortPerm.evalImpl (Nat.log2 (4 * n + 2) + 3) n x).map fun (y, steps) =>
    ((List.range n).map fun i => y.mem (n + i), steps)

private meta def duplicateKeys : List ℕ := [4, 1, 4, 0, 3, 2, 0]

#guard localResult [] == some ([], 6)
#guard localResult [42] == some ([0], 6)
#guard (localResult [1, 1]).map Prod.fst == some [0, 1]
#guard (localResult [1, 0]).map Prod.fst == some [1, 0]
#guard (localResult duplicateKeys).map Prod.fst == some [3, 6, 1, 5, 4, 0, 2]

private meta def agreesAndUsesFewerSteps (keys : List ℕ) : Bool :=
  match localResult keys, indexedResult keys with
  | some (localPerm, localCost), some (indexedPerm, indexedCost) =>
    localPerm == indexedPerm && localCost < indexedCost
  | _, _ => false

private meta def listsOver (alphabet : List ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | m + 1 => (listsOver alphabet m).flatMap fun xs => alphabet.map (· :: xs)

#guard (List.range 7).all fun n => (listsOver [0, 1, 2] n).all agreesAndUsesFewerSteps

private meta def mixed (n : ℕ) : List ℕ :=
  (List.range n).map fun i => ((i * 47 + 11) % 113) % 17

private meta def counts (keys : List ℕ) : Option (ℕ × ℕ) := do
  let (indexedPerm, indexedCost) ← indexedResult keys
  let (localPerm, localCost) ← localResult keys
  if indexedPerm == localPerm then some (indexedCost, localCost) else none

#guard counts [1, 0] == some (86, 11)
#guard counts [0, 1] == some (86, 12)
#guard counts (List.range 32) == some (4078, 3082)
#guard counts (List.range 32).reverse == some (4078, 3162)
#guard counts (mixed 128) == some (23574, 17255)

private meta def compiledRun
    (program : List (PointerMachine.Instr LocalRef.model (Local.layout 9 11))) :
    ℕ → PointerMachine.State LocalRef.model (Local.layout 9 11) →
      PointerMachine.State LocalRef.model (Local.layout 9 11)
  | 0, x => x
  | fuel + 1, x =>
    match PointerMachine.step program x with
    | none => x
    | some y => compiledRun program fuel y

#guard match localResult duplicateKeys with
  | none => false
  | some (expected, steps) =>
    let n := duplicateKeys.length
    let c := Local.compile LocalRef.code
    let x := Local.encode (LocalRef.inputState duplicateKeys)
    let y := compiledRun c.program steps x
    y.pc == c.size && y.heap.length == 3 * n &&
      (y.heap.take n).map (fun cell => cell.data 0) == duplicateKeys &&
      ((List.range n).map fun i => (y.heap[n + i]?).elim 0 fun cell => cell.data 0)
        == expected

end CslibFrontierTests.WordRAMLocalMergeSort
