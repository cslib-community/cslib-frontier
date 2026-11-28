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
  (Program.Code.eval (Local.instructionSet LocalRef.model (3 * n) 8 11)
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
#guard counts (List.range 32) == some (4078, 3049)
#guard counts (List.range 32).reverse == some (4078, 3129)
#guard counts (mixed 128) == some (23574, 17210)

private meta def compiledRun
    (program : List (PointerMachine.Instr LocalRef.model (Local.layout 8 11))) :
    ℕ → PointerMachine.State LocalRef.model (Local.layout 8 11) →
      PointerMachine.State LocalRef.model (Local.layout 8 11)
  | 0, x => x
  | fuel + 1, x =>
    match PointerMachine.step program x with
    | none => x
    | some y => compiledRun program fuel y

private meta def checksCompiledResult (keys : List ℕ) (expectedBase : ℕ) : Bool :=
  match localResult keys with
    | none => false
    | some (expected, steps) =>
      let n := keys.length
      let c := Local.compile LocalRef.code
      let x := Local.encode (LocalRef.inputState keys)
      let y := compiledRun c.program steps x
      y.pc == c.size && y.heap.length == 3 * n &&
        (y.heap.take n).map (fun cell => cell.data 0) == keys &&
        (match y.ptr LocalRef.resultReg with
          | none => false
          | some base =>
            base == expectedBase &&
              ((y.heap.drop base).take n).map (fun cell => cell.data 0) == expected)

#guard checksCompiledResult duplicateKeys 14
#guard checksCompiledResult [3, 1, 2, 1] 4

private meta def runWordRAM (w : ℕ) (program : Array (Instr .standard 20)) :
    ℕ → ℕ → FastData 20 → ℕ → Option (FastData 20 × ℕ × ℕ)
  | 0, _, _, _ => none
  | fuel + 1, pc, x, steps =>
    match program[pc]? with
    | some (.op o) => do
      let y ← o.evalFast w x
      runWordRAM w program fuel (pc + 1) y (steps + 1)
    | some (.jump t) => runWordRAM w program fuel t x (steps + 1)
    | some (.branch c t) =>
      runWordRAM w program fuel (if c.holdsFast x then t else pc + 1) x (steps + 1)
    | some (.halt i) => some (x, x.reg i, steps + 1)
    | _ => none

private meta def directResult (keys : List ℕ) : Option (List ℕ × ℕ) := do
  let n := keys.length
  let w := Nat.log2 (max (5 * n + 2) (keys.foldl max 0)) + 2
  let input := LocalRef.wordRAMInput keys
  let (y, base, t) ← runWordRAM w LocalRef.wordRAMProgram.toArray (100 * (n + 1) ^ 2)
    input.pc (.ofData input.data) 0
  pure ((List.range n).map (fun i => y.read (base + 2 * i)), t)

#guard (List.range 7).all fun n =>
  (listsOver [0, 1, 2] n).all fun keys =>
    match directResult keys, indexedResult keys with
    | some (direct, t), some (indexed, u) => direct == indexed && t < u + 1
    | _, _ => false

#guard (directResult (mixed 128)).map Prod.snd == some 19865

end CslibFrontierTests.WordRAMLocalMergeSort
