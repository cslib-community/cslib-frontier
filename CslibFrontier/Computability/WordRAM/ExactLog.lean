/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Structured
public import Mathlib.Data.Nat.Log
import CslibFrontier.Computability.WordRAM.SymbolicExec
import Mathlib.Tactic.FinCases

/-!
# Exact-basis Word-RAM binary logarithms and arithmetic helpers

This file provides structured subprograms over `Cslib.WordRAM.Basis.exact` for floor and ceiling
base-`2` logarithms (`log2Loop` and `clog2Loop`), an equal-cost register-maximum gadget (`maxCode`),
and an `.exactBin` execution helper (`exec_exactBin`).

Whereas `Cslib.Algorithms.WordRAM.NatLog` and `Cslib.Algorithms.WordRAM.NatClog` are
`Code .standard 4` programs with `ExecWithin` upper bounds, the subprograms here operate in the
`.exact` basis using right-shift division by `2` (`>>> 1`) and carry exact closed-form `Exec` step
counts (`4 * Nat.log 2 rem + 2` and `5 * Nat.clog 2 rem + 2`) together with explicit final-state
formulas (`log2LoopData` and `clog2LoopData`) for embedding via `Code.rename`.

## Main definitions

* `Cslib.WordRAM.ExactLog.maxCode`: 3-instruction equal-cost branch computing the
  maximum of two registers.
* `Cslib.WordRAM.ExactLog.log2Body`,
  `Cslib.WordRAM.ExactLog.log2Loop`,
  `Cslib.WordRAM.ExactLog.log2LoopData`: floor-`log₂` loop over `Basis.exact`.
* `Cslib.WordRAM.ExactLog.clog2Body`,
  `Cslib.WordRAM.ExactLog.clog2Loop`,
  `Cslib.WordRAM.ExactLog.clog2LoopData`: ceiling-`log₂` loop over `Basis.exact`.

## Main results

* `Cslib.WordRAM.ExactLog.exec_exactBin`: single-instruction execution of `.exactBin`.
* `Cslib.WordRAM.ExactLog.maxCode_exec`: 3-instruction execution of `maxCode`.
* `Cslib.WordRAM.ExactLog.log2Loop_exec`: exact `4 * Nat.log 2 rem + 2`-instruction
  execution of `log2Loop`.
* `Cslib.WordRAM.ExactLog.clog2Loop_exec`: exact `5 * Nat.clog 2 rem + 2`-instruction
  execution of `clog2Loop`.
-/

public section

namespace Cslib.WordRAM.ExactLog

open Cslib.WordRAM

/-- Execute a single `.exactBin` operation when `evalExact` returns `some v` and `Fits w v`. -/
theorem exec_exactBin {w r : ℕ} {f : BinOp} {dst i j : Fin r} {d : Data r} {v : ℕ}
    (hev : f.evalExact (d.regs i) (d.regs j) = some v) (hfit : Fits w v) :
    Exec w (.op (.exactBin f dst i j) : Code .exact r) d (d.set dst v) 1 := by
  apply Exec.op
  rw [Op.eval_exactBin, hev]
  exact Data.put_of_fits hfit

/-- 3-instruction equal-cost branch setting register `dst` to `max (x.regs a) (x.regs b)`. -/
@[expose] def maxCode {n : ℕ} (dst a b : Fin n) : Code .exact n :=
  .branch (.lt a b) (.seq (.op (.copy dst b)) (.op (.copy dst dst))) (.op (.copy dst a))

/-- `maxCode dst a b` executes deterministically in 3 instructions and sets `dst` to
`max (x.regs a) (x.regs b)`. -/
theorem maxCode_exec {w n : ℕ} (dst a b : Fin n) (x : Data n) :
    Exec w (maxCode dst a b) x (x.set dst (max (x.regs a) (x.regs b))) 3 := by
  refine WP.Exact.exec ?_
  unfold maxCode
  wram_exec
  · rw [Data.set_set, max_eq_right hc.le]
  · rw [max_eq_left (not_lt.mp hc)]

/-- One iteration of the floor-`log₂` loop on `Data 3` (`reg 0 = rem`, `reg 1 = acc`,
`reg 2 = 1`): shifts `rem` right by `1` (`rem / 2`) and increments `acc`. -/
@[expose] def log2Body : Code .exact 3 :=
  .seq (.op (.exactBin .shiftRight 0 0 2))
       (.op (.exactBin .add 1 1 2))

/-- Floor-`log₂` loop `while 1 < rem do [ rem ← rem >>> 1; acc ← acc + 1 ]`. -/
@[expose] def log2Loop : Code .exact 3 :=
  .loop (.lt 2 0) log2Body

/-- Closed-form final state of `log2Loop` starting from `rem` in register `0` and `acc` in
register `1`. -/
@[expose] def log2LoopData (rem acc : ℕ) (x : Data 3) : Data 3 :=
  (x.set 0 (if rem = 0 then 0 else 1)).set 1 (acc + Nat.log 2 rem)

/-- `log2Loop` executes deterministically in `4 * Nat.log 2 rem + 2` instructions, accumulating
`acc + Nat.log 2 rem` into register `1` and preserving all memory. -/
theorem log2Loop_exec {w : ℕ} (rem : ℕ) {acc : ℕ} {x : Data 3}
    (hrem : x.regs 0 = rem) (hacc : x.regs 1 = acc) (hone : x.regs 2 = 1)
    (hfit_rem : Fits w rem) (hfit_acc : Fits w (acc + Nat.log 2 rem)) :
    Exec w log2Loop x (log2LoopData rem acc x) (4 * Nat.log 2 rem + 2) := by
  induction rem using Nat.strong_induction_on generalizing acc x with
  | _ rem ih =>
    by_cases hlt : 1 < rem
    · have hlog : Nat.log 2 rem = Nat.log 2 (rem / 2) + 1 :=
        Nat.log_of_one_lt_of_le (by decide) (by omega)
      have hfit_div : Fits w (rem / 2) := hfit_rem.of_le (Nat.div_le_self rem 2)
      refine WP.Exact.exec (WP.Exact.loop_iter (by simp [Cond.Holds, hrem, hone, hlt]) ?_)
      unfold log2Body
      wram_exec [hrem, hacc, hone, Nat.shiftRight_eq_div_pow]
      refine WP.Exact.of_exec (ih (rem / 2) (by omega) (acc := acc + 1) (by wram_simp)
        (by wram_simp) (by wram_simp [hone]) hfit_div (hfit_acc.of_le (by omega)))
        ⟨by omega, ?_⟩
      ext i : 2
      · fin_cases i <;> wram_simp [log2LoopData, hlog, show rem ≠ 0 by omega,
          show rem / 2 ≠ 0 by omega]
        omega
      · rfl
    · have hlog0 : Nat.log 2 rem = 0 := Nat.log_of_lt (by omega)
      refine WP.Exact.exec (WP.Exact.loop_exit (by simp [Cond.Holds, hrem, hone, hlt])
        ⟨by omega, ?_⟩)
      ext i : 2
      · fin_cases i <;> simp [log2LoopData, hlog0, hacc, hrem]
        split_ifs <;> omega
      · rfl

/-- Body of `clog2Loop` on `Data 3` (`reg 0 = rem`, `reg 1 = acc`, `reg 2 = 1`): updates
`rem ← (rem + 1) >>> 1` (`= (rem + 1) / 2`) and `acc ← acc + 1`. -/
@[expose] def clog2Body : Code .exact 3 :=
  .seq (.op (.exactBin .add 0 0 2))
  (.seq (.op (.exactBin .shiftRight 0 0 2))
        (.op (.exactBin .add 1 1 2)))

/-- Ceiling-`log₂` loop `while 1 < rem do [ rem ← (rem + 1) >>> 1; acc ← acc + 1 ]`. -/
@[expose] def clog2Loop : Code .exact 3 :=
  .loop (.lt 2 0) clog2Body

/-- Closed-form final state of `clog2Loop`. -/
@[expose] def clog2LoopData (rem acc : ℕ) (x : Data 3) : Data 3 :=
  (x.set 0 (if rem = 0 then 0 else 1)).set 1 (acc + Nat.clog 2 rem)

/-- `clog2Loop` executes deterministically in `5 * Nat.clog 2 rem + 2` instructions, accumulating
`acc + Nat.clog 2 rem` into register `1` and preserving all memory. -/
theorem clog2Loop_exec {w : ℕ} (rem : ℕ) {acc : ℕ} {x : Data 3}
    (hrem : x.regs 0 = rem) (hacc : x.regs 1 = acc) (hone : x.regs 2 = 1)
    (hfit_rem1 : Fits w (rem + 1)) (hfit_acc : Fits w (acc + Nat.clog 2 rem)) :
    Exec w clog2Loop x (clog2LoopData rem acc x) (5 * Nat.clog 2 rem + 2) := by
  induction rem using Nat.strong_induction_on generalizing acc x with
  | _ rem ih =>
    by_cases hlt : 1 < rem
    · have hclog : Nat.clog 2 rem = Nat.clog 2 ((rem + 1) / 2) + 1 :=
        Nat.clog_of_one_lt (by decide) hlt
      have hfit_div1 : Fits w ((rem + 1) / 2 + 1) := hfit_rem1.of_le (by omega)
      have hfit_div : Fits w ((rem + 1) / 2) := hfit_div1.of_le (by omega)
      refine WP.Exact.exec (WP.Exact.loop_iter (by simp [Cond.Holds, hrem, hone, hlt]) ?_)
      unfold clog2Body
      wram_exec [hrem, hacc, hone, Nat.shiftRight_eq_div_pow]
      refine WP.Exact.of_exec (ih ((rem + 1) / 2) (by omega) (acc := acc + 1) (by wram_simp)
        (by wram_simp) (by wram_simp [hone]) hfit_div1 (hfit_acc.of_le (by omega)))
        ⟨by omega, ?_⟩
      ext i : 2
      · fin_cases i <;> wram_simp [clog2LoopData, hclog, show rem ≠ 0 by omega,
          show (rem + 1) / 2 ≠ 0 by omega]
        omega
      · rfl
    · have hclog0 : Nat.clog 2 rem = 0 := Nat.clog_of_right_le_one (by omega) 2
      refine WP.Exact.exec (WP.Exact.loop_exit (by simp [Cond.Holds, hrem, hone, hlt])
        ⟨by omega, ?_⟩)
      ext i : 2
      · fin_cases i <;> simp [clog2LoopData, hclog0, hacc, hrem]
        split_ifs <;> omega
      · rfl

end Cslib.WordRAM.ExactLog
