/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.DataStructure.AVLTree.PointerMachine.Structured.Dictionary
import CslibFrontier.Computability.WordRAM.PointerMachine.Defs

/-! The structured AVL dictionary, assembled and run on the machine: writes with a single
rotation, a double rotation, a replacement and a stored zero, reads of present and missing keys,
the framing of other keys and a client register, and the instruction counts against the proved
bounds. -/

-- This regression module intentionally exports no declarations.
set_option linter.privateModule false

open Cslib.PointerMachine Cslib.DataStructure
open SearchTree.PointerMachine
open AVLTree.PointerMachine
open AVLTree.PointerMachine.Dictionary (WriteResult Stores)
open AVLTree.PointerMachine.Dictionary.Structured

private abbrev model := Cslib.WordRAM.PointerMachine.model 8

private abbrev writeCode : List (Instr model (layout 2 3)) :=
  (write (M := model) (.constant 0) .maxSucc .lt .heavy .le).program

private abbrev readCode : List (Instr model (layout 2 3)) :=
  (read (M := model) (.constant 0) .lt).program

/-- Run `code` for at most `fuel` instructions, counting those executed before it halts. -/
private def runCount (code : List (Instr model (layout 2 3))) :
    ℕ → State model (layout 2 3) → State model (layout 2 3) × ℕ
  | 0, s => (s, 0)
  | fuel + 1, s =>
    match step code s with
    | none => (s, 0)
    | some t => let (u, n) := runCount code fuel t; (u, n + 1)

private def label (address key height value : ℕ) : Label model 2 :=
  ⟨address, fun f => if f = 0 then key else if f = 1 then height else value⟩

/-- The tree with root 20 and left child 10, of height two. -/
private def initial (query value : ℕ) : State model (layout 2 3) where
  pc := 0
  ptr i := if i = 1 then some 0 else none
  data i := if i = 0 then query else if i = 3 then value else 77
  heap := [record (some 1) none none (label 0 20 2 200),
    record none none (some 0) (label 1 10 1 100)]

private def written (query value : ℕ) : State model (layout 2 3) × ℕ :=
  runCount writeCode 400 (initial query value)

private def readBack (s : State model (layout 2 3)) (query : ℕ) : ℕ × ℕ :=
  let (t, n) := runCount readCode 60 { s.setData 0 query with pc := 0 }
  (t.data 3, n)

-- Both programs halt at their last instruction.
example : (written 5 50).1.pc + 1 = writeCode.length := by decide +kernel
example : (runCount readCode 60 (initial 10 0)).1.pc + 1 = readCode.length := by decide +kernel

-- Inserting 5 rotates the root once; the other values and the client register are retained.
example : (written 5 50).1.ptr 1 = some 1 ∧ (written 5 50).1.heap.length = 3 ∧
    (written 5 50).1.data 4 = 77 := by decide +kernel
example : (readBack (written 5 50).1 5).1 = 50 ∧ (readBack (written 5 50).1 20).1 = 200 ∧
    (readBack (written 5 50).1 10).1 = 100 := by decide +kernel

-- Inserting 15 rotates twice and promotes the fresh node.
example : (written 15 150).1.ptr 1 = some 2 ∧ (written 15 150).1.heap.length = 3 := by
  decide +kernel
example : (readBack (written 15 150).1 15).1 = 150 ∧ (readBack (written 15 150).1 20).1 = 200 ∧
    (readBack (written 15 150).1 10).1 = 100 := by decide +kernel

-- Inserting 30 needs no rotation.
example : (written 30 3).1.ptr 1 = some 0 ∧ (written 30 3).1.heap.length = 3 ∧
    (readBack (written 30 3).1 30).1 = 3 := by decide +kernel

-- Replacement and stored zero need no allocation; a missing key reads zero too.
example : (written 20 9).1.heap.length = 2 ∧ (readBack (written 20 9).1 20).1 = 9 ∧
    (readBack (written 20 9).1 10).1 = 100 := by decide +kernel
example : (written 10 0).1.heap.length = 2 ∧ (readBack (written 10 0).1 10).1 = 0 ∧
    (readBack (written 10 0).1 30).1 = 0 := by decide +kernel

-- Instruction counts before the `halt`: writes with one rotation, two rotations, no rotation,
-- a replacement at the root and one at its child, then reads. At height two the proved bounds
-- are `112 * height + 35 = 259` for a write and `7 * height + 6 = 20` for a read.
example : ([5, 15, 30, 20, 10].map fun q => (written q 1).2) = [133, 169, 77, 27, 38] := by
  decide +kernel
example : ([5, 10, 15, 20, 30].map fun q => (readBack (initial 0 0) q).2) =
    [15, 18, 17, 13, 12] := by decide +kernel

-- The correctness theorem has an instance for every address and value, on the empty tree.
private def empty (query value : ℕ) : State model (layout 2 3) :=
  { State.empty with data := fun i => if i = 0 then query else if i = 3 then value else 77 }

example (query value : ℕ) : ∃ t tree time,
    Executes writeCode (empty query value) { t with pc := writeCode.length - 1 } time ∧
      time ≤ 36 ∧ WriteResult id (empty query value) t tree .nil (fun _ => 0) := by
  obtain ⟨t, tree, run, result⟩ := write_correct (M := model) (.constant 0) .maxSucc .lt .heavy
    .le id (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (empty query value) .nil .nil (fun _ => 0) trivial trivial AVLTree.valid_nil
    AddressesDistinct.nil (Stores.empty (M := model) 0) rfl
  obtain ⟨time, bound, exec⟩ := run.executes rfl
  exact ⟨t, tree, time, by simpa [Code.program] using exec, bound, result⟩
