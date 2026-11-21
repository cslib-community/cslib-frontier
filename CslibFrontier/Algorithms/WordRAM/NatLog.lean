/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec
public import CslibFrontier.Computability.WordRAM.Notation
public import Mathlib.Data.Nat.Log

/-!
# A charged native binary logarithm

## Main definitions

* `NatLog.program`: successive division by two.

## Main results

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

/-- Compute the floor binary logarithm in at most `4 log₂ n + 5` instructions.
Memory is untouched and the input quotient is consumed. -/
theorem exec {w : ℕ} (x : Data 4) (h2 : Fits w 2) (hn : Fits w (x.regs arg))
    (hout : Fits w (Nat.log 2 (x.regs arg) + 1)) :
    ∃ y, ExecWithin w program x y (4 * Nat.log 2 (x.regs arg) + 5) ∧
      y.regs result = Nat.log 2 (x.regs arg) ∧ y.mem = x.mem ∧
      y.regs one = 1 ∧ y.regs two = 2 := by
  let I (y : Data 4) : Prop := y.regs one = 1 ∧ y.regs two = 2 ∧
    y.regs arg ≤ x.regs arg ∧
    y.regs result + Nat.log 2 (y.regs arg) = Nat.log 2 (x.regs arg) ∧ y.mem = x.mem
  have hbody (y : Data 4) (hy : I y) (hc : (Cond.lt one arg).Holds y) :
      ∃ z, ExecWithin w body y z 2 ∧ I z ∧
        Nat.log 2 (z.regs arg) < Nat.log 2 (y.regs arg) := by
    obtain ⟨ho, ht, harg, hsum, hm⟩ := hy
    have hgt : 1 < y.regs arg := by simpa only [Cond.holds_lt, ho] using hc
    have hpos : 0 < Nat.log 2 (y.regs arg) := Nat.log_pos (by decide) (by omega)
    have hdiv : Fits w (y.regs arg / 2) := hn.of_le ((Nat.div_le_self _ _).trans harg)
    have hinc : Fits w (y.regs result + 1) := hout.of_le (by omega)
    wram_exec [body, ho, ht]
    wram_simp [I, ho, ht, hm, Nat.log_div_base]
    omega
  let x₀ := ((x.set result 0).set one 1).set two 2
  have hx₀ : I x₀ := by simp +decide [I, x₀, arg, result, one, two]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => Nat.log 2 (y.regs arg)) hbody hx₀
  obtain ⟨ho, ht, harg, hsum, hm⟩ := hy
  have hzero : Nat.log 2 (y.regs arg) = 0 := by
    have hle : y.regs arg ≤ 1 := by simpa only [Cond.holds_lt, ho, not_lt] using hc
    exact Nat.log_eq_zero_iff.mpr (Or.inl (by omega))
  refine ⟨y, ?_, by omega, hm, ho, ht⟩
  wram_exec [program]
  refine WP.of_execWithin he ?_
  wram_simp [x₀]
  omega

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
  have hbody : ∀ y, I y → (Cond.lt one rem).Holds y →
      ∃ z, ExecWithin (B := .standard) w ram[rem ← rem >>> one; idx ← idx + one] y z 2 ∧
        I z ∧ Nat.log 2 (z.regs rem) < Nat.log 2 (y.regs rem) := by
    intro y ⟨hym, hyf, hyr_ge, hyr_le, hy_sum⟩ hc
    have hy1 : y.regs one = 1 := (hyf one hor hoi).trans hone
    have hgt1 : 1 < y.regs rem := by simpa [Cond.holds_lt, hy1] using hc
    have hshr_eq : y.regs rem >>> 1 = y.regs rem / 2 := by
      rw [Nat.shiftRight_eq_div_pow, pow_one]
    have hlog_step : Nat.log 2 (y.regs rem) = Nat.log 2 (y.regs rem / 2) + 1 :=
      Nat.log_of_one_lt_of_le (by decide) (by omega)
    have hfit_rem : Fits w (y.regs rem / 2) := hn_fit.of_le (by omega)
    have hfit_idx : Fits w (y.regs idx + 1) := hlg_fit.of_le (by omega)
    wram_exec [hy1, hshr_eq]
    refine ⟨⟨hym, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro i hir hii
      wram_simp [hir, hii]
      exact hyf i hir hii
    all_goals wram_simp
    all_goals omega
  have hx : I x := ⟨rfl, fun _ _ _ => rfl, by omega, hrem.le, by rw [hidx, hrem, zero_add]⟩
  obtain ⟨y, he, ⟨hym, hyf, hyr_ge, _, hy_sum⟩, hnc⟩ :=
    ExecWithin.loop_invariant I (fun y => Nat.log 2 (y.regs rem)) hbody hx
  have hy1 : y.regs one = 1 := (hyf one hor hoi).trans hone
  have hyr_eq1 : y.regs rem = 1 := by
    have : ¬(1 < y.regs rem) := by simpa [Cond.holds_lt, hy1] using hnc
    omega
  rw [hyr_eq1, Nat.log_one_right, add_zero] at hy_sum
  exact ⟨y, he.mono (by rw [hrem]; omega), hym, hy_sum, hyf⟩

end Cslib.Algorithms.WordRAM.NatLog
