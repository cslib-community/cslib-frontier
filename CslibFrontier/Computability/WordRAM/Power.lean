/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Native natural powers

## Main definitions

* `Power.program`: repeated native multiplication, with base and exponent in registers.

## Main results

* `Power.exec`: `b^n` within `4n+5` instructions, with input-derived intermediate fits.
-/

@[expose] public section

namespace Cslib.WordRAM.Power

/-- Result accumulator, initially one. -/
abbrev value : Fin 5 := 0
/-- Number of completed multiplications. -/
abbrev counter : Fin 5 := 1
/-- Input base. -/
abbrev base : Fin 5 := 2
/-- Input exponent. -/
abbrev exponent : Fin 5 := 3
/-- Constant one, initialized by the routine. -/
abbrev one : Fin 5 := 4

/-- One multiplication and one counter increment. -/
def body : Code .standard 5 := ram[ value ← value * base; counter ← counter + one ]

/-- A fixed program for natural exponentiation by repeated multiplication. -/
def program : Code .standard 5 :=
  .seq (ram[ value ← #1; counter ← #0; one ← #1 ]) (.loop (.lt counter exponent) body)

/-- Output value, loop counters, input readback and memory after exponentiation. -/
def Post (b n : ℕ) (x y : Data 5) : Prop :=
  y.regs value = b ^ n ∧
  y.regs counter = n ∧ y.regs one = 1 ∧ y.mem = x.mem ∧
  y.regs base = b ∧ y.regs exponent = n

/-- The routine is uniform in its arguments and preserves memory and both input registers.
Every multiplication fit follows from the final power and exponent bound. -/
theorem exec {w : ℕ} (b n : ℕ) (hb : 1 ≤ b) (x : Data 5)
    (hx : x.regs base = b) (hn : x.regs exponent = n) (hfit : Fits w (b ^ n + n + 2)) :
    ∃ y, ExecWithin w program x y (4 * n + 5) ∧ Post b n x y := by
  unfold Post program
  wram_exec
  let P (j : ℕ) (y : Data 5) : Prop :=
    y.regs base = b ∧ y.regs exponent = n ∧ y.regs one = 1 ∧ y.regs value = b ^ j ∧ y.mem = x.mem
  refine WP.of_spec (ExecWithin.loop_count (N := n) (T := 2) P (fun _ hy => hy.2.1) ?_ ?_ ?_) ?_
  · rintro y ⟨hbv, hnv, ho, hv, hm⟩ hc_lt
    have hp : Fits w (b ^ (y.regs counter + 1)) := by
      fits [Nat.pow_le_pow_right hb (show y.regs counter + 1 ≤ n by omega)]
    wram_exec [body, hbv, ho, hv, ← pow_succ]
    dsimp only [P]
    wram_simp [hbv, hnv, ho, hm]
  · wram_simp [Nat.zero_le]
  · dsimp only [P]; wram_simp [hx, hn, pow_zero]
  · rintro y ⟨⟨hyb, hyn, hy1, hyv, hym⟩, hj⟩
    exact ⟨by wram_simp; omega, hyv, hj, hy1, hym, hyb, hyn⟩

end Cslib.WordRAM.Power
