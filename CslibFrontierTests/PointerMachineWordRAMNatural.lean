/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.Computability.PointerMachine.WordRAM.Natural

/-! Natural scalar certificates satisfy their contracts for every register alias pattern.
Concrete assembled programs exercise both scratch-register destinations and word-boundary cases. -/

set_option linter.privateModule false

open Cslib.PointerMachine Cslib.PointerMachine.WordRAM
open Natural
open Cslib.WordRAM (Code ExecWithin)

private abbrev layout : Layout := ⟨1, 1, 1, 1⟩
private abbrev S := scalars layout

private def initial : Cslib.WordRAM.Data (regCount layout) where
  regs r := r.val + 1
  mem a := a % 16

-- These satisfying clients quantify over all registers, so d=a, d=b, a=b and aliases with
-- either temporary are included, without assumptions that rule those cases out.
example (o : Operation) (d a b : Fin (regCount layout)) :
    ∃ y, ExecWithin 4 (S.op o d a b) initial y (S.opTime o) ∧
      ScalarResult d (model.evalOp o (a.val + 1) (b.val + 1)) initial y := by
  apply S.op_spec 4 o d a b initial (a.val + 1) (b.val + 1) rfl rfl trivial
  have ha : a.val < 8 := a.isLt
  have hb : b.val < 8 := b.isLt
  change model.evalOp o (a.val + 1) (b.val + 1) < 16
  cases o <;> simp only [model] <;> omega

example (p : Test) (d a b : Fin (regCount layout)) :
    ∃ y, ExecWithin 4 (S.test p d a b) initial y (S.testTime p) ∧
      ScalarResult d (if model.evalTest p (a.val + 1) (b.val + 1) then 1 else 0) initial y := by
  apply S.test_spec 4 p d a b initial (a.val + 1) (b.val + 1) rfl rfl ?_ (by decide)
  cases p with
  | lt | le => trivial
  | heavy =>
    have ha : a.val < 8 := a.isLt
    change a.val + 1 - (b.val + 1) < 16
    omega

private def execute (code : Code .standard (regCount layout)) (dst : Fin (regCount layout))
    (x : Cslib.WordRAM.Data (regCount layout) := initial) : Option (ℕ × ℕ) :=
  Cslib.WordRAM.run 4 (code.assemble 0 ++ [.halt dst]) 10 ⟨0, x⟩

example : execute (S.op .zero 0 0 0) 0 = some (0, 2) := by decide +kernel
example : execute (S.op .maxSucc (addrReg layout) (valueReg layout) (addrReg layout))
    (addrReg layout) = some (7, 6) := by decide +kernel
example : execute (S.op .maxSucc (valueReg layout) (addrReg layout) (valueReg layout))
    (valueReg layout) = some (7, 5) := by decide +kernel
example : execute (S.op .maxSucc (addrReg layout) (addrReg layout) (addrReg layout))
    (addrReg layout) = some (6, 6) := by decide +kernel
example : execute (S.test .lt (addrReg layout) (addrReg layout) (valueReg layout))
    (addrReg layout) = some (1, 3) := by decide +kernel
example : execute (S.test .le (valueReg layout) (addrReg layout) (valueReg layout))
    (valueReg layout) = some (1, 4) := by decide +kernel

-- b is the largest word: computing b+1 would fault; the certified subtraction route succeeds.
example : execute (S.test .heavy (addrReg layout) (addrReg layout) (valueReg layout))
    (addrReg layout) ((initial.set (addrReg layout) 0).set (valueReg layout) 15) = some (0, 6) := by
  decide +kernel
example : execute (S.test .heavy (valueReg layout) (addrReg layout) (valueReg layout))
    (valueReg layout) ((initial.set (addrReg layout) 15).set (valueReg layout) 0) =
      some (1, 5) := by
  decide +kernel
example : execute (S.test .heavy (addrReg layout) (addrReg layout) (addrReg layout))
    (addrReg layout) = some (0, 6) := by decide +kernel

example : S.TestSafe 4 .heavy 0 15 ∧ ¬S.TestSafe 4 .heavy 16 0 := by
  change (0 : ℕ) < 16 ∧ ¬16 < 16
  decide
-- The maximum-plus-one certificate requires a fitting result; the machine faults at overflow.
example : execute (S.op .maxSucc (addrReg layout) (addrReg layout) (addrReg layout))
    (addrReg layout) (initial.set (addrReg layout) 15) = none := by decide +kernel
