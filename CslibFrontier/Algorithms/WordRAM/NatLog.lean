/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import Mathlib.Tactic.Linarith
public import CslibFrontier.Computability.WordRAM.Notation
public import Mathlib.Data.Nat.Log

/-!
# A charged native binary logarithm

## Main definitions

* `NatLog.program`: successive division by two.

## Main results

* `NatLog.exec_halving`: shared specification for four-register halving loops.
* `NatLog.exec`: the floor logarithm with a logarithmic charged instruction bound.
* `NatLog.shiftLoop_exec`: the same logarithm by right shifts, on any three registers.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.NatLog

open Cslib.WordRAM

/-- Quotient, initially the input. -/
abbrev arg : Fin 4 := 0
/-- Floor logarithm output. -/
abbrev result : Fin 4 := 1
/-- Constant one. -/
abbrev one : Fin 4 := 2
/-- Constant two. -/
abbrev two : Fin 4 := 3

/-- Divide the quotient by two and increment the answer. -/
def body : Code .standard 4 := ram[ arg ← arg / two; result ← result + one ]

/-- Fixed code for `Nat.log 2`, including its value zero at input zero. -/
def program : Code .standard 4 :=
  .seq (ram[ result ← #0; one ← #1; two ← #2 ]) (.loop (.lt one arg) body)

/-- Shared specification for halving loops initialized with `result ← #0; one ← #1; two ← #2`:
if each iteration from `1 < y.regs arg ≤ x.regs arg` executes `c` within `T` instructions while
advancing `result` by `1` and decreasing `f (y.regs arg)` by `1` (with `f a = 0` for `a ≤ 1`),
the program leaves `f (x.regs arg)` in `result` within `(T + 2) * f (x.regs arg) + 5`
instructions. -/
theorem exec_halving {w T : ℕ} (c : Code .standard 4) (f : ℕ → ℕ)
    (hf0 : ∀ a ≤ 1, f a = 0) (x : Data 4) (h2 : Fits w 2)
    (hstep : ∀ y : Data 4, 1 < y.regs arg → y.regs arg ≤ x.regs arg →
      y.regs one = 1 → y.regs two = 2 →
      y.regs result + f (y.regs arg) = f (x.regs arg) → y.mem = x.mem →
      ∃ z, ExecWithin w c y z T ∧ z.regs one = 1 ∧ z.regs two = 2 ∧
        z.regs arg ≤ x.regs arg ∧ z.regs result = y.regs result + 1 ∧
        f (y.regs arg) = f (z.regs arg) + 1 ∧ z.mem = x.mem) :
    ∃ y, ExecWithin w (.seq (ram[ result ← #0; one ← #1; two ← #2 ]) (.loop (.lt one arg) c)) x y
        ((T + 2) * f (x.regs arg) + 5) ∧
      y.regs result = f (x.regs arg) ∧ y.mem = x.mem ∧
      y.regs one = 1 ∧ y.regs two = 2 := by
  wram_exec
  let I (y : Data 4) : Prop := y.regs one = 1 ∧ y.regs two = 2 ∧ y.regs arg ≤ x.regs arg ∧
    y.regs result + f (y.regs arg) = f (x.regs arg) ∧ y.mem = x.mem
  refine WP.of_spec (ExecWithin.loop_invariant (T := T) I (fun y => f (y.regs arg)) ?_ ?_) ?_
  · rintro y ⟨ho, ht, harg, hsum, hm⟩ hc
    obtain ⟨z, he, z1, z2, zarg, zres, zf, zm⟩ :=
      hstep y (by simpa only [Cond.holds_lt, ho] using hc) harg ho ht hsum hm
    exact ⟨z, he, ⟨z1, z2, zarg, by omega, zm⟩, by omega⟩
  · dsimp only [I]; wram_simp [le_rfl]
  · rintro y ⟨⟨ho, ht, _, hsum, hm⟩, hc⟩
    have hzero : f (y.regs arg) = 0 := hf0 _ (by simp only [Cond.holds_lt, ho, not_lt] at hc; omega)
    exact ⟨by wram_simp; nlinarith, by omega, hm, ho, ht⟩

/-- Compute the floor binary logarithm in at most `4 log₂ n + 5` instructions.
Memory is untouched and the input quotient is consumed. -/
theorem exec {w : ℕ} (x : Data 4) (h2 : Fits w 2) (hn : Fits w (x.regs arg))
    (hout : Fits w (Nat.log 2 (x.regs arg) + 1)) :
    ∃ y, ExecWithin w program x y (4 * Nat.log 2 (x.regs arg) + 5) ∧
      y.regs result = Nat.log 2 (x.regs arg) ∧ y.mem = x.mem ∧
      y.regs one = 1 ∧ y.regs two = 2 := by
  refine exec_halving body (Nat.log 2)
    (fun a ha => Nat.log_eq_zero_iff.mpr (.inl (by omega))) x h2 ?_
  intro y hgt harg ho ht hsum hm
  have hpos : 0 < Nat.log 2 (y.regs arg) := Nat.log_pos (by decide) hgt
  wram_exec [body, ho, ht]
  wram_simp [ho, ht, hm]
  exact ⟨(Nat.div_le_self _ _).trans harg, by rw [Nat.log_div_base]; omega⟩

/-- Run the routine on any injectively chosen registers. -/
theorem exec_rename {r w : ℕ} (f : Fin 4 → Fin r) (hf : f.Injective) (x : Data r)
    (h2 : Fits w 2) (hn : Fits w (x.regs (f arg)))
    (hout : Fits w (Nat.log 2 (x.regs (f arg)) + 1)) :
    ∃ y, ExecWithin w (program.rename f) x y (4 * Nat.log 2 (x.regs (f arg)) + 5) ∧
      y.regs (f result) = Nat.log 2 (x.regs (f arg)) ∧ y.mem = x.mem ∧
      y.regs (f one) = 1 ∧ y.regs (f two) = 2 := by
  obtain ⟨y, hy, hpost, -⟩ := ExecWithin.rename_post hf (exec (x.comap f) h2 hn hout)
  exact ⟨y, hy, hpost⟩

/-- Halving by right shifts on any three distinct registers: from `rem = n ≥ 1` and `idx = 0`,
`while one < rem do [rem ← rem >>> one; idx ← idx + one]` leaves `idx = Nat.log 2 n` within
`4 * Nat.log 2 n + 2` instructions. Memory and every register other than `rem` and `idx` are
unchanged. `Cslib.WordRAM.ExactLog.log2Loop` is the exact-basis counterpart. -/
theorem shiftLoop_exec {r w n : ℕ} {one rem idx : Fin r} (hor : one ≠ rem) (hoi : one ≠ idx)
    (hri : rem ≠ idx) {x : Data r} (hn : 1 ≤ n) (hone : x.regs one = 1) (hrem : x.regs rem = n)
    (hidx : x.regs idx = 0) (hn_fit : Fits w n) (hlg_fit : Fits w (Nat.log 2 n)) :
    ∃ y, ExecWithin (B := .standard) w
        (.loop (.lt one rem) ram[rem ← rem >>> one; idx ← idx + one]) x y
        (4 * Nat.log 2 n + 2) ∧
      y.mem = x.mem ∧ y.regs idx = Nat.log 2 n ∧
      ∀ i, i ≠ rem → i ≠ idx → y.regs i = x.regs i := by
  let I (y : Data r) : Prop :=
    y.mem = x.mem ∧ (∀ i, i ≠ rem → i ≠ idx → y.regs i = x.regs i) ∧
    1 ≤ y.regs rem ∧ y.regs rem ≤ n ∧ y.regs idx + Nat.log 2 (y.regs rem) = Nat.log 2 n
  have hbody (y : Data r) (hy : I y) (hc : (Cond.lt one rem).Holds y) :
      ∃ z, ExecWithin (B := .standard) w ram[rem ← rem >>> one; idx ← idx + one] y z 2 ∧
        I z ∧ Nat.log 2 (z.regs rem) < Nat.log 2 (y.regs rem) := by
    obtain ⟨hym, hyf, _, hyr_le, hy_sum⟩ := hy
    have hy1 : y.regs one = 1 := (hyf one hor hoi).trans hone
    have hgt1 : 1 < y.regs rem := by simpa only [Cond.holds_lt, hy1] using hc
    have hshr : y.regs rem >>> 1 = y.regs rem / 2 := by rw [Nat.shiftRight_eq_div_pow, pow_one]
    have hlog : Nat.log 2 (y.regs rem) = Nat.log 2 (y.regs rem / 2) + 1 :=
      Nat.log_of_one_lt_of_le (by decide) (by omega)
    wram_exec [hy1, hshr]
    dsimp only [I]
    wram_simp [hym]
    refine ⟨⟨fun i hir hii => by wram_simp [hir, hii, hyf i hir hii], ?_, ?_, ?_⟩, ?_⟩ <;> omega
  obtain ⟨y, he, ⟨hym, hyf, hyr_ge, _, hy_sum⟩, hnc⟩ := ExecWithin.loop_invariant I
    (fun y => Nat.log 2 (y.regs rem)) hbody
    ⟨rfl, fun _ _ _ => rfl, by omega, hrem.le, by rw [hidx, hrem, zero_add]⟩
  have hy1 : y.regs one = 1 := (hyf one hor hoi).trans hone
  have hyr_eq1 : y.regs rem = 1 := by simp only [Cond.holds_lt, hy1, not_lt] at hnc; omega
  rw [hyr_eq1, Nat.log_one_right, add_zero] at hy_sum
  exact ⟨y, he.mono (by rw [hrem]; omega), hym, hy_sum, hyf⟩

end Cslib.Algorithms.WordRAM.NatLog
