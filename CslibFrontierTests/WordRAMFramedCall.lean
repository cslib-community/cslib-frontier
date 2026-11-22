/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.WordRAM.SymbolicExec.ListLoop
import CslibFrontier.Computability.WordRAM.ListArray
import CslibFrontier.Computability.WordRAM.Notation

/-!
# Framed calls and list loops in symbolic execution

A loop sums the cells of an array (`wram_fold`), and a caller adds a register the loop never
writes to the sum. The loop's contract says nothing about that register: the framed call keeps
it, because the loop's code does not write it. The call leaves out the contract's hypotheses; a
hypothesis that is not among the caller's facts follows the continuation as a goal.
-/

namespace CslibFrontierTests.WordRAMFramedCall

open Cslib.WordRAM Cslib.WordRAM.Block

private abbrev acc : Fin 6 := 0
private abbrev ptr : Fin 6 := 1
private abbrev stop : Fin 6 := 2
private abbrev one : Fin 6 := 3
private abbrev tmp : Fin 6 := 4
private abbrev keep : Fin 6 := 5

/-- Add the cell at `ptr` to `acc`, and move `ptr` to the next cell. -/
private def addCell : Code .standard 6 := ram[ tmp ← *ptr; acc ← acc + tmp; ptr ← ptr + one ]

/-- Add the cells in `[ptr, stop)` to `acc`. -/
private def sumLoop : Code .standard 6 := .loop (.lt ptr stop) addCell

/-- Add the cells, then the register `keep`. -/
private def sumPlus : Code .standard 6 := ram[ ⟪sumLoop⟫; acc ← acc + keep ]

/-- The loop adds the list at `ptr`. Its invariant states the registers the body writes; the
constant `one` and the bound `stop` are read in the entry data `x`. -/
private theorem sumLoop_spec {w : ℕ} (l : List ℕ) (x : Data 6) (hone : x.regs one = 1)
    (hl : HoldsList (x.regs ptr) l x.mem) (hstop : x.regs ptr + l.length = x.regs stop)
    (hfit : Fits w (x.regs acc + l.sum)) (hfitp : Fits w (x.regs stop)) :
    ∃ y, ExecWithin w sumLoop x y (5 * l.length + 2) ∧ y.mem = x.mem ∧
      y.regs acc = x.regs acc + l.sum := by
  wram_fold (fun rest y => y.mem = x.mem ∧ y.regs ptr + rest.length = x.regs stop ∧
      HoldsList (y.regs ptr) rest x.mem ∧ y.regs acc + rest.sum = x.regs acc + l.sum)
    over l cost (fun _ => 3)
  case init => exact ⟨rfl, hstop, hl, rfl⟩
  case exit => rintro v m ⟨-, he, -⟩; omega
  case step =>
    rintro a rest v m ⟨rfl, he, hl', hs⟩
    obtain ⟨ha, hrest⟩ := holdsList_cons_iff.mp hl'
    simp only [List.sum_cons] at hs
    refine ⟨by omega, ?_⟩
    unfold addCell
    wram_exec [ha, hone]
    wram_simp
    exact ⟨by omega, hrest, by omega⟩
  case post =>
    rintro v m ⟨rfl, he, -, hs⟩
    exact ⟨by simp; omega, rfl, by simpa using hs⟩

/-- The contract of the loop does not mention `keep`, and its hypotheses are left out of the call.
After the call `keep` is read in the caller's data. -/
example {w : ℕ} (l : List ℕ) (x : Data 6) (hone : x.regs one = 1)
    (hl : HoldsList (x.regs ptr) l x.mem) (hstop : x.regs ptr + l.length = x.regs stop)
    (hfit : Fits w (x.regs acc + l.sum + x.regs keep)) (hfitp : Fits w (x.regs stop)) :
    ∃ y, ExecWithin w sumPlus x y (5 * l.length + 3) ∧ y.mem = x.mem ∧
      y.regs acc = x.regs acc + l.sum + x.regs keep := by
  refine WP.exists_execWithin (WP.seq ?_)
  wram_call (sumLoop_spec l _ ..) framed with v m ⟨rfl, hacc⟩
  wram_exec [hacc]
  wram_simp

/-- A hypothesis of the contract that is not among the caller's facts is not dropped: it follows
the continuation as a goal. -/
example {w : ℕ} (l : List ℕ) (x : Data 6) (hone : x.regs one = 1)
    (hl : HoldsList (x.regs ptr) (l ++ []) x.mem) (hstop : x.regs ptr + l.length = x.regs stop)
    (hfit : Fits w (x.regs acc + l.sum)) (hfitp : Fits w (x.regs stop)) :
    ∃ y, ExecWithin w sumLoop x y (5 * l.length + 2) ∧ y.regs acc = x.regs acc + l.sum := by
  refine WP.exists_execWithin ?_
  wram_call (sumLoop_spec l _ ..) framed with v m ⟨-, hacc⟩
  · exact ⟨le_rfl, hacc⟩
  · simpa using hl

/-- A contract of another program does not apply. -/
example {w : ℕ} (x : Data 6) (Q : Data 6 → ℕ → Prop) (h : WP w addCell x Q) :
    WP w addCell x Q := by
  fail_if_success wram_call (sumLoop_spec (w := w) [] x ..) framed with v m ⟨hm, -⟩
  exact h

end CslibFrontierTests.WordRAMFramedCall
