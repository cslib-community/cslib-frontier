/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Computability.WordRAM.Notation
public import Mathlib.Data.Nat.GCD.Basic

/-!
# A charged native greatest common divisor

Euclid's algorithm with one native remainder per round. The second argument strictly decreases,
so the number of rounds is at most that argument; this crude bound suffices for callers whose
second argument is itself polynomially bounded.

## Main definitions

* `NatGcd.program`: Euclid's algorithm on two registers.

## Main results

* `NatGcd.exec`: `Nat.gcd a b` within `5 b + 3` instructions, preserving memory.
* `NatGcd.exec_rename`: the same on injectively chosen registers.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.NatGcd

open Cslib.WordRAM

/-- First argument, and the output. -/
abbrev a : Fin 4 := 0
/-- Second argument; zero on exit. -/
abbrev b : Fin 4 := 1
/-- Remainder scratch. -/
abbrev t : Fin 4 := 2
/-- Constant zero. -/
abbrev zero : Fin 4 := 3

/-- One round of Euclid's algorithm: `(a, b) ↦ (b, a mod b)`. -/
def body : Code .standard 4 := ram[ t ← a % b; a ← b; b ← t ]

/-- Euclid's algorithm, looping while the second argument is positive. -/
def program : Code .standard 4 := ram[ zero ← #0; while zero < b do [ ⟪body⟫ ] ]

/-- Compute `Nat.gcd a b` within `5 b + 3` instructions, preserving memory. Every register value
stays below `max a b`, so no fit hypothesis beyond the arguments is needed. -/
theorem exec {w : ℕ} (x : Data 4) (ha : Fits w (x.regs a)) (hb : Fits w (x.regs b)) :
    ∃ y, ExecWithin w program x y (5 * x.regs b + 3) ∧
      y.regs a = Nat.gcd (x.regs a) (x.regs b) ∧ y.mem = x.mem := by
  wram_exec [program]
  let I (y : Data 4) : Prop := y.regs zero = 0 ∧
    Nat.gcd (y.regs a) (y.regs b) = Nat.gcd (x.regs a) (x.regs b) ∧
    Fits w (y.regs a) ∧ Fits w (y.regs b) ∧ y.mem = x.mem
  refine WP.of_spec (ExecWithin.loop_invariant (T := 3) I (fun y => y.regs b) ?_ ?_) ?_
  · rintro y ⟨hz, hg, hfa, hfb, hm⟩ hc
    have hpos : 0 < y.regs b := by simpa only [Cond.holds_lt, hz] using hc
    wram_exec [body]
    dsimp only [I]
    wram_simp [hz, hfb, hm]
    refine ⟨⟨?_, by fits⟩, Nat.mod_lt _ hpos⟩
    rw [← hg, Nat.gcd_comm (y.regs b), ← Nat.gcd_rec, Nat.gcd_comm]
  · dsimp only [I]; wram_simp [ha, hb]
  · rintro y ⟨⟨hz, hg, -, -, hm⟩, hc⟩
    have hb0 : y.regs b = 0 := by simp only [Cond.holds_lt, hz] at hc; omega
    exact ⟨by wram_simp; omega, by rwa [hb0, Nat.gcd_zero_right] at hg, hm⟩

/-- Run Euclid's algorithm on any injectively chosen registers. -/
theorem exec_rename {r w : ℕ} (f : Fin 4 → Fin r) (hf : f.Injective) (x : Data r)
    (ha : Fits w (x.regs (f a))) (hb : Fits w (x.regs (f b))) :
    ∃ y, ExecWithin w (program.rename f) x y (5 * x.regs (f b) + 3) ∧
      y.regs (f a) = Nat.gcd (x.regs (f a)) (x.regs (f b)) ∧ y.mem = x.mem := by
  obtain ⟨y, hy, hpost, -⟩ := ExecWithin.rename_post hf (exec (x.comap f) ha hb)
  exact ⟨y, hy, hpost⟩

end Cslib.Algorithms.WordRAM.NatGcd
