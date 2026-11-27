/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Algorithms.WordRAM.NatLog
import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Computability.WordRAM.Notation
public import Mathlib.Data.Nat.Log

/-!
# A charged native ceiling binary logarithm

## Main definitions

* `NatClog.program`: successive ceiling division by two.

## Main results

* `NatClog.exec`: the ceiling logarithm with a logarithmic charged instruction bound.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.NatClog

open Cslib.WordRAM

/-- Quotient, initially the input. -/
abbrev arg : Fin 4 := 0
/-- Ceiling logarithm output. -/
abbrev result : Fin 4 := 1
/-- Constant one. -/
abbrev one : Fin 4 := 2
/-- Constant two. -/
abbrev two : Fin 4 := 3

/-- Divide the quotient by two and increment the answer. -/
def body : Code .standard 4 := ram[ arg ← arg + one; arg ← arg / two; result ← result + one ]

/-- Fixed code for `Nat.clog 2`, including its value zero at input zero. -/
def program : Code .standard 4 :=
  .seq (ram[ result ← #0; one ← #1; two ← #2 ]) (.loop (.lt one arg) body)

/-- Ceiling logarithm, initialized constants and unchanged memory; the quotient is consumed. -/
def Post (x y : Data 4) : Prop :=
  y.regs result = Nat.clog 2 (x.regs arg) ∧ y.mem = x.mem ∧
  y.regs one = 1 ∧ y.regs two = 2

/-- Compute the ceiling binary logarithm in at most `5 ⌈log₂ n⌉ + 5` instructions.
Memory is untouched and the input quotient is consumed. -/
theorem exec {w : ℕ} (x : Data 4) (h2 : Fits w 2) (hn : Fits w (x.regs arg + 1))
    (hout : Fits w (Nat.clog 2 (x.regs arg) + 1)) :
    ∃ y, ExecWithin w program x y (5 * Nat.clog 2 (x.regs arg) + 5) ∧ Post x y := by
  refine NatLog.exec_halving body (Nat.clog 2)
    (fun _ ha => Nat.clog_of_right_le_one ha 2) x h2 ?_
  intro y hgt harg ho ht hsum hm
  unfold body
  dsimp only [NatLog.arg, NatLog.result, NatLog.one, NatLog.two, arg, result, one, two] at *
  have hclog := Nat.clog_of_two_le (b := 2) (by decide) (by omega : 2 ≤ y.regs 0)
  rw [show y.regs 0 + 2 - 1 = y.regs 0 + 1 by omega] at hclog
  wram_exec [ho, ht]
  wram_simp [ho, ht, hm]
  exact ⟨by omega, hclog⟩

/-- Run the routine on any injectively chosen registers. -/
theorem exec_rename {r w : ℕ} (f : Fin 4 → Fin r) (hf : f.Injective) (x : Data r)
    (h2 : Fits w 2) (hn : Fits w (x.regs (f arg) + 1))
    (hout : Fits w (Nat.clog 2 (x.regs (f arg)) + 1)) :
    ∃ y, ExecWithin w (program.rename f) x y (5 * Nat.clog 2 (x.regs (f arg)) + 5) ∧
      y.regs (f result) = Nat.clog 2 (x.regs (f arg)) ∧ y.mem = x.mem ∧
      y.regs (f one) = 1 ∧ y.regs (f two) = 2 := by
  obtain ⟨y, hy, hpost, -⟩ := ExecWithin.rename_post hf (exec (x.comap f) h2 hn hout)
  exact ⟨y, hy, hpost⟩

end Cslib.Algorithms.WordRAM.NatClog
