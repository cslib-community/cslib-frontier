/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Computability.WordRAM.Notation
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith

/-!
# A charged native integer square root

## Main definitions

* `NatSqrt.program`: successive squares.

## Main results

* `NatSqrt.exec`: integer square root in a square-root number of native instructions.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.NatSqrt

open Cslib.WordRAM

/-- Input integer, preserved. -/
abbrev arg : Fin 6 := 0
/-- Current root and output. -/
abbrev root : Fin 6 := 1
/-- Successor of the current root. -/
abbrev next : Fin 6 := 2
/-- Square of the successor. -/
abbrev square : Fin 6 := 3
/-- Constant one. -/
abbrev one : Fin 6 := 4
/-- Input plus one. -/
abbrev bound : Fin 6 := 5

/-- Advance the root and compute the next square. -/
def body : Code .standard 6 := ram[
  root ← next; next ← next + one; square ← next * next ]

/-- A fixed program for the integer square root, with all square computations charged. -/
def program : Code .standard 6 :=
  .seq (ram[ root ← #0; next ← #1; square ← #1; one ← #1; bound ← arg + one ])
    (.loop (.lt square bound) body)

/-- Compute `Nat.sqrt n` in at most `5 sqrt(n) + 7` instructions, preserving input and memory.
The linear bound `4n + 4` covers the final unsuccessful square as well as all counters. -/
theorem exec {w : ℕ} (x : Data 6) (hfit : Fits w (4 * x.regs arg + 4)) :
    ∃ y, ExecWithin w program x y (5 * Nat.sqrt (x.regs arg) + 7) ∧
      y.regs root = Nat.sqrt (x.regs arg) ∧ y.regs arg = x.regs arg ∧ y.mem = x.mem ∧
      y.regs one = 1 := by
  let n := x.regs arg
  wram_exec [program]
  let I (y : Data 6) : Prop := y.regs arg = n ∧ y.regs one = 1 ∧ y.regs bound = n + 1 ∧
    y.regs next = y.regs root + 1 ∧ y.regs square = y.regs next * y.regs next ∧
    y.regs root ≤ Nat.sqrt n ∧ y.mem = x.mem
  refine WP.of_spec
    (ExecWithin.loop_invariant (T := 3) I (fun y => Nat.sqrt n - y.regs root) ?_ ?_) ?_
  · rintro y ⟨ha, ho, hb, hn, hsq, hr, hm⟩ hc
    have hsmall : y.regs next * y.regs next ≤ n := by
      simp only [Cond.holds_lt, hsq, hb] at hc; omega
    have hnext : y.regs next ≤ Nat.sqrt n := Nat.le_sqrt.mpr hsmall
    have hnn : y.regs next ≤ x.regs arg := hnext.trans (Nat.sqrt_le_self n)
    have hsquare : Fits w ((y.regs next + 1) * (y.regs next + 1)) := by
      fits [show (y.regs next + 1) * (y.regs next + 1) ≤ 4 * x.regs arg + 4 by nlinarith]
    wram_exec [body, ho]
    dsimp only [I]
    wram_simp [ha, ho, hb, hnext, hm]
    omega
  · dsimp only [I, n]; wram_simp [Nat.zero_le]
  · rintro y ⟨⟨ha, ho, hb, hn, hsq, hr, hm⟩, hc⟩
    have hlarge : n < (y.regs root + 1) * (y.regs root + 1) := by
      simp only [Cond.holds_lt, hsq, hn, hb] at hc; omega
    have hout : y.regs root = Nat.sqrt n := by have := Nat.sqrt_lt.mpr hlarge; omega
    exact ⟨by wram_simp; dsimp only [n] at *; omega, hout, ha, hm, ho⟩

/-- Run successive squares on any injectively chosen registers. -/
theorem exec_rename {r w : ℕ} (f : Fin 6 → Fin r) (hf : f.Injective) (x : Data r)
    (hfit : Fits w (4 * x.regs (f arg) + 4)) :
    ∃ y, ExecWithin w (program.rename f) x y (5 * Nat.sqrt (x.regs (f arg)) + 7) ∧
      y.regs (f root) = Nat.sqrt (x.regs (f arg)) ∧
      y.regs (f arg) = x.regs (f arg) ∧ y.mem = x.mem ∧ y.regs (f one) = 1 := by
  obtain ⟨y, hy, hpost, -⟩ := ExecWithin.rename_post hf (exec (x.comap f) hfit)
  exact ⟨y, hy, hpost⟩

end Cslib.Algorithms.WordRAM.NatSqrt
