/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Allocation

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Copying arrays on the word RAM

The seven-register copy routine charges every address calculation, load, store, increment,
and loop test. Source and destination may be disjoint in either order or equal.
It is a fixed program: neither the length nor either address is baked into the code.

## Main definitions

* `Cslib.WordRAM.ArrayCopy.src`, `Cslib.WordRAM.ArrayCopy.dst`, `Cslib.WordRAM.ArrayCopy.len`,
  `Cslib.WordRAM.ArrayCopy.idx`, `Cslib.WordRAM.ArrayCopy.addr`, `Cslib.WordRAM.ArrayCopy.value`,
  `Cslib.WordRAM.ArrayCopy.one`: the seven registers of the copy routine.
* `Cslib.WordRAM.ArrayCopy.body`, `Cslib.WordRAM.ArrayCopy.program`: single-word loop body and
  full copying program between addresses supplied in registers.
* `Cslib.WordRAM.ArrayCopy.copyPrefix`: mathematical specification of the writes.

## Main results

* `Cslib.WordRAM.ArrayCopy.exec`: copying `n` words within `7 * n + 4` instructions,
  preserving the source and all cells outside the destination.
* `Cslib.WordRAM.ArrayCopy.exec_of_separated_or_eq`: the same native program also supports
  disjoint blocks in the reverse address order or identical source and destination.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.ArrayCopy

/-- The memory after copying a prefix into a destination block. -/
def copyPrefix (mem : ℕ → ℕ) (src dst k : ℕ) : ℕ → ℕ :=
  fun a => if dst ≤ a ∧ a < dst + k then mem (src + (a - dst)) else mem a

/-- Copying zero words leaves memory unchanged. -/
@[simp]
theorem copyPrefix_zero (mem : ℕ → ℕ) (src dst : ℕ) : copyPrefix mem src dst 0 = mem := by
  funext a; simp [copyPrefix]

/-- Reading within the copied destination block returns the corresponding source word. -/
theorem copyPrefix_read {mem : ℕ → ℕ} {src dst k j : ℕ} (hj : j < k) :
    copyPrefix mem src dst k (dst + j) = mem (src + j) := by
  simp [copyPrefix, hj]

/-- Memory cells outside `[dst, dst + k)` are unchanged by `copyPrefix`. -/
theorem copyPrefix_outside {mem : ℕ → ℕ} {src dst k a : ℕ}
    (ha : ¬(dst ≤ a ∧ a < dst + k)) : copyPrefix mem src dst k a = mem a := by
  simp [copyPrefix, ha]

theorem copyPrefix_succ (mem : ℕ → ℕ) (src dst k : ℕ) :
    copyPrefix mem src dst (k + 1) =
      Function.update (copyPrefix mem src dst k) (dst + k) (mem (src + k)) := by
  funext a
  by_cases ha : a = dst + k
  · subst a; simp [copyPrefix]
  · simp only [copyPrefix, Function.update_of_ne ha,
      show (dst ≤ a ∧ a < dst + (k + 1)) ↔ (dst ≤ a ∧ a < dst + k) by omega]

/-- Source base, destination base, length, index, temporary address, value, and one. -/
abbrev src : Fin 7 := 0
/-- Destination base. -/
abbrev dst : Fin 7 := 1
/-- Number of words. -/
abbrev len : Fin 7 := 2
/-- Loop index. -/
abbrev idx : Fin 7 := 3
/-- Temporary address. -/
abbrev addr : Fin 7 := 4
/-- Temporary value. -/
abbrev value : Fin 7 := 5
/-- Constant one. -/
abbrev one : Fin 7 := 6

/-- Five data instructions per copied word. -/
def body : Code .standard 7 := ram[
  addr ← src + idx; value ← *addr; addr ← dst + idx; *addr ← value; idx ← idx + one ]

/-- A fixed copying program with all three parameters in registers. -/
def program : Code .standard 7 := ram[ idx ← #0; one ← #1; while idx < len do [ ⟪body⟫ ] ]

/-- Low-level structured copying charges register setup and all loop instructions, excluding
the final halt. The one-past-end addresses must fit a word. Boundedness of the input memory and
registers is a separate premise when using `ExecWithin.bounded` to obtain bounded-word execution. -/
theorem exec_of_separated_or_eq {w : ℕ} (x : Data 7) (h1 : Fits w 1)
    (hs : Fits w (x.regs src + x.regs len))
    (hd : Fits w (x.regs dst + x.regs len))
    (hdisj : x.regs src + x.regs len ≤ x.regs dst ∨
      x.regs dst + x.regs len ≤ x.regs src ∨ x.regs src = x.regs dst) :
    ∃ y, ExecWithin w program x y (7 * x.regs len + 4) ∧
      y.mem = copyPrefix x.mem (x.regs src) (x.regs dst) (x.regs len) ∧
      y.regs src = x.regs src ∧ y.regs dst = x.regs dst ∧ y.regs len = x.regs len := by
  wram_exec [program]
  let P (j : ℕ) (y : Data 7) : Prop :=
    y.regs src = x.regs src ∧ y.regs dst = x.regs dst ∧ y.regs len = x.regs len ∧
    y.regs one = 1 ∧ y.mem = copyPrefix x.mem (x.regs src) (x.regs dst) j
  refine WP.of_spec
    (ExecWithin.loop_count (N := x.regs len) (T := 5) P (fun _ hy => hy.2.2.1) ?_ ?_ ?_) ?_
  · rintro y ⟨hys, hyd, hyl, hyo, hym⟩ hi
    have hread : y.mem (x.regs src + y.regs idx) = x.mem (x.regs src + y.regs idx) := by
      rw [hym]; exact copyPrefix_outside (by rcases hdisj with h | h | h <;> omega)
    wram_exec [body, hys, hyd, hyo, hread]
    dsimp only [P]
    wram_simp [hys, hyd, hyl, hyo, hym, ← copyPrefix_succ]
  · wram_simp [Nat.zero_le]
  · dsimp only [P]; wram_simp [copyPrefix_zero]
  · rintro y ⟨⟨hys, hyd, hyl, _, hym⟩, _⟩
    exact ⟨by wram_simp; omega, hym, hys, hyd, hyl⟩

/-- Forward copying between disjoint arrays, retaining the original calling convention. -/
theorem exec {w : ℕ} (x : Data 7) (h1 : Fits w 1)
    (hs : Fits w (x.regs src + x.regs len))
    (hd : Fits w (x.regs dst + x.regs len))
    (hdisj : x.regs src + x.regs len ≤ x.regs dst) :
    ∃ y, ExecWithin w program x y (7 * x.regs len + 4) ∧
      y.mem = copyPrefix x.mem (x.regs src) (x.regs dst) (x.regs len) ∧
      y.regs src = x.regs src ∧ y.regs dst = x.regs dst ∧ y.regs len = x.regs len :=
  exec_of_separated_or_eq x h1 hs hd (Or.inl hdisj)

end Cslib.WordRAM.ArrayCopy

end
