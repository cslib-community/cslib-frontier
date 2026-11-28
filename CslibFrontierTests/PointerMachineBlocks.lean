/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.Computability.PointerMachine.Program

/-! Compose two independently proved blocks at nonzero offsets. The second block branches
over allocation, so incorrect branch relocation would change termination or the heap. -/

-- This regression module intentionally exports no declarations.
set_option linter.privateModule false

open Cslib.PointerMachine

private abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Empty
  Test := Empty
  evalOp o := nomatch o
  evalTest t := nomatch t

private abbrev layout : Layout := ⟨2, 1, 1, 1⟩
private abbrev first : List (Instr model layout) := [.null 0, .halt]
private abbrev second : List (Instr model layout) :=
  [.ifPtrEq 0 0 2, .create 0, .halt]

private def program : List (Instr model layout) :=
  [.goto 1] ++ first.map (Instr.relocate 1 3) ++
    second.map (Instr.relocate 3 6) ++ [.halt]

example (s : State model layout) (pc : s.pc = 0) :
    Runs program { s with pc := 1 } { s.setPtr 0 none with pc := 6 } 4 := by
  let middle : State model layout := { s.setPtr 0 none with pc := 1 }
  have hfirst : Executes first s middle 2 :=
    ⟨1, .single (by simp [step, first, pc, middle, Instr.effect, Instr.next]), rfl, rfl⟩
  let start : State model layout := { middle with pc := 0 }
  let finish : State model layout := { start with pc := 2 }
  have hsecond : Executes second start finish 2 :=
    ⟨1, .single (by simp [step, second, start, finish, Instr.effect, Instr.next]), rfl, rfl⟩
  have a := hfirst.inBlock [.goto 1] (second.map (Instr.relocate 3 6) ++ [.halt]) 3
  have b := hsecond.inBlock ([.goto 1] ++ first.map (Instr.relocate 1 3)) [.halt] 6
  have a' : Runs program { s with pc := 1 } { middle with pc := 3 } 2 := by
    simpa [program, pc, List.append_assoc] using a
  have b' : Runs program { middle with pc := 3 } { s.setPtr 0 none with pc := 6 } 2 := by
    simpa [program, first, second, start, finish, middle, List.append_assoc] using b
  exact a'.trans b'

private def initial : State model layout :=
  { State.empty with ptr := fun _ => some 0, heap := [Record.blank] }

private def result : State model layout :=
  (fun x => (step program x).getD x)^[6] initial

example : result.pc = 6 := by decide
example : result.ptr 0 = none ∧ result.ptr 1 = some 0 := by decide
example : result.heap.length = 1 := by decide

private abbrev branchModel : Model :=
  { model with Test := Unit, evalTest := fun _ a _ => decide (a = 0) }

private abbrev yesCode : List (Instr branchModel layout) := [.halt]
private abbrev noCode : List (Instr branchModel layout) := [.create 0, .halt]

example (s : State branchModel layout) (pc : s.pc = 0) (zero : s.data 0 = 0) :
    Executes (branch () 0 0 yesCode noCode) s { s with pc := 4 } 3 := by
  have yes : Executes yesCode s s 1 := ⟨0, .refl _, by simp [yesCode, pc], rfl⟩
  have chosen : Executes
      (if branchModel.evalTest () (s.data 0) (s.data 0) then yesCode else noCode) s s 1 := by
    simpa [branchModel, zero] using yes
  exact Executes.branch () 0 0 yesCode noCode pc chosen

example (s : State branchModel layout) (pc : s.pc = 0) (nonzero : s.data 0 ≠ 0) :
    Executes (branch () 0 0 yesCode noCode) s
      { (Instr.create 0).effect s with pc := 4 } 4 := by
  let out : State branchModel layout := { (Instr.create 0).effect s with pc := 1 }
  have no : Executes noCode s out 2 :=
    ⟨1, .single (by simp [step, noCode, pc, Instr.next, out]), rfl, rfl⟩
  have chosen : Executes
      (if branchModel.evalTest () (s.data 0) (s.data 0) then yesCode else noCode) s out 2 := by
    simpa [branchModel, nonzero] using no
  exact Executes.branch () 0 0 yesCode noCode pc chosen

private def sequenced : State model layout :=
  (fun x => (step (sequence first second) x).getD x)^[5] initial

example : sequenced.pc = 5 := by decide
example : sequenced.ptr 0 = none ∧ sequenced.ptr 1 = initial.ptr 1 := by decide
example : sequenced.heap.length = 1 ∧ sequenced.data 0 = initial.data 0 := by decide

-- Fixed-size assembly embeds a certified routine after another block and skips padding.
private def padded (_ : ℕ) (_ : Bool) : List (Instr model layout) :=
  [.null 0, .goto 9, .goto 99]

example (s : State model layout) (pc : s.pc = 0) :
    Runs (Cslib.Program.compileBlocks padded 4 [false, true])
      { s with pc := 3 } { s.setPtr 0 none with pc := 9 } 2 := by
  let finish : State model layout := { s.setPtr 0 none with pc := 1 }
  have run : Executes first s finish 2 :=
    ⟨1, .single (by simp [step, first, pc, finish, Instr.effect, Instr.next]), rfl, rfl⟩
  have embedded := run.inCompiledBlock (block := padded) (k := 3)
    (start := 4) (j := 1) (next := 9) (source := [false, true])
    (suffix := [.goto 99]) (fun _ _ _ => rfl) (by rfl) (by rfl)
  simpa [pc, finish] using embedded

example : (Cslib.Program.compileBlocks padded 4 [false, true])[4]? = some (.goto 9) := by
  exact Cslib.Program.getElem?_compileBlocks (block := padded) (k := 3)
    (start := 4) (j := 1) (n := 1) (fun _ _ _ => rfl) (by rfl) (by rfl)
