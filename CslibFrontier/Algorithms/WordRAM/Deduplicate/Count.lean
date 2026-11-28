/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Deduplicate.Model
public import CslibFrontier.Computability.WordRAM.ListArray
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Native counting of one adjacent run

The counter tests the array bound before every read and stops at the first different word.
No sorting or counting oracle is used. The mathematical end index is a proof parameter and
does not occur in the code or a register.

## Main definitions

* `Count.body`, `Count.code`: the native run-counting loop.

## Main results

* `Count.exec`: every matching input position advances the cursor, with linear charged time.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Deduplicate

open Cslib.WordRAM

/-- Input length. -/
abbrev len : Fin 16 := 0
/-- Sorted input array. -/
abbrev src : Fin 16 := 1
/-- Unique-key output array. -/
abbrev keys : Fin 16 := 2
/-- Multiplicity output array. -/
abbrev counts : Fin 16 := 3
/-- Input cursor. -/
abbrev idx : Fin 16 := 4
/-- Number of completed output runs. -/
abbrev out : Fin 16 := 5
/-- Current run key. -/
abbrev key : Fin 16 := 6
/-- Current run multiplicity. -/
abbrev count : Fin 16 := 7
/-- Loaded input word. -/
abbrev value : Fin 16 := 8
/-- Address temporary. -/
abbrev addr : Fin 16 := 9
/-- Constant one. -/
abbrev one : Fin 16 := 10
/-- Run-counting loop flag. -/
abbrev active : Fin 16 := 11

namespace Count

/-- Read the next word only if the cursor is in bounds; count it or end the run. -/
def body : Code .standard 16 := ram[
  if idx < len then [
    addr ← src + idx; value ← *addr;
    if value = key then [ count ← count + one; idx ← idx + one ]
      else [ active ← #0 ]
  ] else [ active ← #0 ] ]

/-- Count from the current cursor, starting with zero count and flag one. -/
def code : Code .standard 16 := .loop (.eq active one) body

/-- Count a maximal adjacent run in `8c+10` instructions, including the terminating test.
`stop` is a proof parameter: execution learns the boundary solely through charged comparisons
and loads. The source memory is unchanged. Empty runs are also admitted by this kernel. -/
theorem exec {w s n start stop k : ℕ} (x : Data 16)
    (hn : x.regs len = n) (hs : x.regs src = s) (hi : x.regs idx = start)
    (hk : x.regs key = k) (hc : x.regs count = 0)
    (ha : x.regs active = 1) (ho : x.regs one = 1)
    (hle : start ≤ stop) (hstop : stop ≤ n)
    (hmem : ∀ j, start ≤ j → j < stop → x.mem (s + j) = k)
    (hnext : stop < n → x.mem (s + stop) ≠ k)
    (hfit : Fits w (s + n)) :
    ∃ y, ExecWithin w code x y (8 * (stop - start) + 10) ∧
      y.regs idx = stop ∧ y.regs count = stop - start ∧ y.mem = x.mem := by
  let I (y : Data 16) : Prop :=
    y.regs len = n ∧ y.regs src = s ∧ y.regs key = k ∧ y.regs one = 1 ∧
    start ≤ y.regs idx ∧ y.regs idx ≤ stop ∧ y.regs count = y.regs idx - start ∧
    y.regs active ≤ 1 ∧ (y.regs active = 0 → y.regs idx = stop) ∧ y.mem = x.mem
  have hbody (y : Data 16) (hy : I y) (hcond : (Cond.eq active one).Holds y) :
      ∃ z, ExecWithin w body y z 6 ∧ I z ∧
        stop - z.regs idx + z.regs active < stop - y.regs idx + y.regs active := by
    obtain ⟨hyn, hys, hyk, hyo, hlo, hhi, hyc, hya, hyend, hym⟩ := hy
    have hyflag : y.regs active = 1 := by simpa only [Cond.holds_eq, hyo] using hcond
    apply WP.exists_execWithin
    unfold body
    by_cases hlt : y.regs idx < stop
    · have hread : y.mem (s + y.regs idx) = k := hym ▸ hmem _ hlo hlt
      wram_exec * [hread]
      wram_simp * [I, hym]
      exact ⟨⟨by omega, by omega, by omega, by simp⟩, by omega⟩
    · have hend : y.regs idx = stop := by omega
      by_cases hsn : stop < n
      · have hread : y.mem (s + stop) ≠ k := hym ▸ hnext hsn
        wram_exec * [hend]
        wram_simp * [I, hend, hyflag, hym, hle, le_rfl, implies_true]
      · wram_exec * [hend]
        wram_simp * [I, hend, hyflag, hym, hle, le_rfl, implies_true]
  have hx : I x := ⟨hn, hs, hk, ho, by omega, by omega, by omega, by omega, by omega, rfl⟩
  obtain ⟨y, he, hy, hnot⟩ := ExecWithin.loop_invariant I
    (fun y => stop - y.regs idx + y.regs active) hbody hx
  obtain ⟨_, _, _, hyo, _, _, hyc, hya, hyend, hym⟩ := hy
  have hend : y.regs idx = stop := hyend (by simp only [Cond.holds_eq, hyo] at hnot; omega)
  refine ⟨y, ?_, hend, hend ▸ hyc, hym⟩
  simpa only [code, hi, ha, Nat.add_mul, Nat.one_mul, Nat.mul_comm, Nat.add_assoc] using he

end Count
end Cslib.Algorithms.WordRAM.Deduplicate
