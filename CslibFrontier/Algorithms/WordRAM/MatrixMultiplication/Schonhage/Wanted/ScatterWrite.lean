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
# Native stable-scatter stores

## Main results

* `Wanted.exec_scatterWrite`: store one computed code and original position at the actual
  cursor, then increment that cursor and the original-input counter.

This is an internal implementation API. The scatter position is the existing counting-sort
formula, whose range follows from the original input length, rather than an execution oracle.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Three actual memory stores suffice for one stable occurrence. Address fits and
separation follow from the original query length and the proved counting-sort position. -/
theorem exec_scatterWrite {w L m N Q n v : ℕ} (key : ℕ → ℕ) (hn : n < Q)
    (hk : key n < numBands L m N ^ 2) (x : Data 96) (hx : Parameters L m N Q x)
    (hi : x.regs index = n) (ht : x.regs tile = key n)
    (hv : x.regs (packRegisters code) = v)
    (hc : x.mem (cursorAddressBase L m N Q + key n) = CountingSort.position key Q n)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w scatterWrite x y 9 ∧ Parameters L m N Q y ∧ y.regs index = n + 1 ∧
      y.mem (codeAddress L m N Q + CountingSort.position key Q n) = v ∧
      y.mem (originalAddress L m N Q + CountingSort.position key Q n) = n ∧
      y.mem (cursorAddressBase L m N Q + key n) = CountingSort.position key Q n + 1 ∧
      (∀ a, a ≠ cursorAddressBase L m N Q + key n →
        a ≠ codeAddress L m N Q + CountingSort.position key Q n →
        a ≠ originalAddress L m N Q + CountingSort.position key Q n → y.mem a = x.mem a) := by
  let p := CountingSort.position key Q n
  have hp : p < Q := CountingSort.position_lt key hn
  have hl := local_fits hfit
  have hend := memoryLimit_eq L m N Q
  have h10 := Nat.zero_le (10 ^ L)
  have h2 := Nat.zero_le (2 ^ L)
  have hf (v : ℕ) (hv : v ≤ memoryLimit L m N Q) : Fits w v := hl.of_le (by omega)
  have hcursor : Fits w (cursorAddressBase L m N Q + key n) := hf _ (by
    unfold cursorAddressBase offsetAddress countAddress tableAddress inputLimit; omega)
  have hcode : Fits w (codeAddress L m N Q + p) := hf _ (by
    unfold memoryLimit originalAddress; omega)
  have horig : Fits w (originalAddress L m N Q + p) := hf _ (by unfold memoryLimit; omega)
  have hnext : Fits w (p + 1) := hf _ (by omega)
  have hnnext : Fits w (n + 1) := hf _ (by omega)
  have hcurcode : cursorAddressBase L m N Q + key n < codeAddress L m N Q := by
    unfold codeAddress; omega
  have hcodeorig : codeAddress L m N Q + p < originalAddress L m N Q := by
    unfold originalAddress; omega
  dsimp only [p] at hcode horig hnext
  simp only [packRegisters, code] at hv
  refine WP.exists_execWithin ?_
  unfold scatterWrite packRegisters
  wram_exec * [hcursor, hcode, horig, hnext, hnnext]
  refine ⟨by regs_frame, by wram_simp, ?_, ?_, ?_, ?_⟩
  · have hne1 : codeAddress L m N Q + p ≠ cursorAddressBase L m N Q + key n := by omega
    have hne2 : codeAddress L m N Q + p ≠ originalAddress L m N Q + p := by omega
    dsimp only [p] at hne1 hne2
    wram_simp [hne1, hne2]
  · have hne1 : originalAddress L m N Q + p ≠ cursorAddressBase L m N Q + key n := by omega
    dsimp only [p] at hne1
    wram_simp [hne1]
  · wram_simp
  · intro a hc' hk' ho'
    wram_simp [hc', hk', ho']

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
