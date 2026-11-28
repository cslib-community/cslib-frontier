/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Setup
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# One native tile-prefix update

## Main results

* `Wanted.exec_prefixStep`: load the actual bucket count, store its immutable start and
  mutable cursor, and advance the running sum with every instruction charged.

This stage lemma is an internal implementation API for the complete grouping execution.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- One actual prefix update; the two stored cells are the only possible memory changes. -/
theorem exec_prefixStep {w L m N Q t : ℕ} (key : ℕ → ℕ)
    (ht : t < numBands L m N ^ 2) (x : Data 96) (hx : Parameters L m N Q x)
    (hi : x.regs index = t) (hs : x.regs total = Nat.count (fun k => key k < t) Q)
    (hc : x.mem (countAddress L Q + t) = Nat.count (fun k => key k = t) Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w prefixStep x y 8 ∧ Parameters L m N Q y ∧
      y.regs index = t + 1 ∧ y.regs total = Nat.count (fun k => key k < (t + 1)) Q ∧
      y.mem (offsetAddress L m N Q + t) = Nat.count (fun k => key k < t) Q ∧
      y.mem (cursorAddressBase L m N Q + t) = Nat.count (fun k => key k < t) Q ∧
      (∀ a, a ≠ offsetAddress L m N Q + t → a ≠ cursorAddressBase L m N Q + t →
        y.mem a = x.mem a) := by
  have hl := local_fits hfit
  have hend := memoryLimit_eq L m N Q
  have h10 := Nat.zero_le (10 ^ L)
  have hf (v : ℕ) (hv : v ≤ memoryLimit L m N Q) : Fits w v := hl.of_le (by omega)
  have hcount : Fits w (countAddress L Q + t) := hf _ (by
    unfold countAddress tableAddress inputLimit
    omega)
  have hoff : Fits w (offsetAddress L m N Q + t) := hf _ (by
    unfold offsetAddress countAddress tableAddress inputLimit
    omega)
  have hcursor : Fits w (cursorAddressBase L m N Q + t) := hf _ (by
    unfold cursorAddressBase offsetAddress countAddress tableAddress inputLimit
    omega)
  have hadd : Fits w (Nat.count (fun k => key k < t) Q + Nat.count (fun k => key k = t) Q) :=
    hf _ (by
    rw [← CountingSort.count_lt_succ]
    have := Nat.count_le (fun i => key i < t + 1) (n := Q)
    omega)
  have hnext : Fits w (t + 1) := hf _ (by omega)
  have hsep : offsetAddress L m N Q + t ≠ cursorAddressBase L m N Q + t := by
    unfold cursorAddressBase
    omega
  refine WP.exists_execWithin ?_
  wram_exec * [prefixStep, hcount, hoff, hcursor, hadd, hnext]
  refine ⟨by regs_frame, by wram_simp, ?_, ?_, ?_, ?_⟩
  · wram_simp
    exact (CountingSort.count_lt_succ key Q t).symm
  · wram_simp [hsep]
  · wram_simp
  · intro a ho hcur
    wram_simp [ho, hcur]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
