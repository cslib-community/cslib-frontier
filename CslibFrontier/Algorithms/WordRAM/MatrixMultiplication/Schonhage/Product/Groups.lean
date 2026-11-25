/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Transfer
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Memory
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Saving actual routing arrays across producer calls

## Main results

* `QueriedProduct.exec_saveOffsets`: save all computed offsets, including the terminal word.
* `QueriedProduct.exec_saveCodes`: save the actual grouped query codes.
* `QueriedProduct.exec_saveOriginals`: save the actual original-position permutation.

Each internal interface proves its charged copy execution. The protected outputs are copied
from actual router memory, without constructing or supplying a routing certificate.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Every low routing source precedes the protected destinations. -/
public theorem group_copy_bounds (L m N Q : ℕ) :
    Wanted.offsetAddress L m N Q + numBands L m N ^ 2 + 1 ≤ Wanted.memoryLimit L m N Q ∧
      Wanted.codeAddress L m N Q + Q ≤ Wanted.memoryLimit L m N Q ∧
      Wanted.originalAddress L m N Q + Q ≤ Wanted.memoryLimit L m N Q ∧
      Wanted.memoryLimit L m N Q ≤ offsetBase L m N Q ∧
      offsetBase L m N Q + numBands L m N ^ 2 + 1 ≤ memoryEnd L m N Q ∧
      codeBase L m N Q + Q ≤ memoryEnd L m N Q ∧
      originalBase L m N Q + Q ≤ memoryEnd L m N Q := by
  have h10 := Nat.zero_le (10 ^ L)
  simp only [Wanted.memoryLimit, Wanted.originalAddress, Wanted.codeAddress,
      Wanted.cursorAddressBase,
    offsetBase, snapshotBase, memoryEnd, stampBase, scratchBase, outputBase, groupedBase,
    originalBase, codeBase]
  omega

/-- Actual argument setup and native copying preserve the caller protocol and every other
register beyond the copy routine. This is an internal producer-consumer execution interface. -/
public theorem exec_saveOffsets {w L m N Q : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x)
    (hsrc : x.regs (bank Wanted.offsets) = Wanted.offsetAddress L m N Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w saveOffsets x y (7 * numBands L m N ^ 2 + 17) ∧ Parameters L m N Q y ∧
      y.mem = ArrayCopy.copyPrefix x.mem (Wanted.offsetAddress L m N Q)
        (offsetBase L m N Q) (numBands L m N ^ 2 + 1) ∧
      (∀ i, 7 ≤ i.val → i ≠ Reg.source → i ≠ Reg.destination → i ≠ Reg.length →
        y.regs i = x.regs i) := by
  have hb := group_copy_bounds L m N Q
  have hn : Fits w (numBands L m N ^ 2 + 1) := allocated_fits hfit (by omega)
  obtain ⟨y, he, hy⟩ := exec_setupCopy x hp hfit
    (show ExecWithin (B := .standard) w (.seq (.op (.copy Reg.source (bank Wanted.offsets))) (ram[
        Reg.destination ← Reg.offsets; Reg.length ← Reg.tiles + Reg.one ])) x
        (((x.set Reg.source (Wanted.offsetAddress L m N Q)).set Reg.destination
          (offsetBase L m N Q)).set Reg.length (numBands L m N ^ 2 + 1)) 3 by wram_exec * [hn])
    (by omega) (by omega) (Or.inl (by omega))
  exact ⟨y, he.mono (by omega), hy⟩

/-- Actual argument setup and native copying preserve the caller protocol and every other
register beyond the copy routine. This is an internal producer-consumer execution interface. -/
public theorem exec_saveCodes {w L m N Q : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x)
    (hsrc : x.regs (bank Wanted.codes) = Wanted.codeAddress L m N Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w saveCodes x y (7 * Q + 10) ∧ Parameters L m N Q y ∧
      y.mem = ArrayCopy.copyPrefix x.mem (Wanted.codeAddress L m N Q)
        (codeBase L m N Q) (Q) ∧
      (∀ i, 7 ≤ i.val → i ≠ Reg.source → i ≠ Reg.destination → i ≠ Reg.length →
        y.regs i = x.regs i) := by
  have hb := group_copy_bounds L m N Q
  have horder : offsetBase L m N Q ≤ codeBase L m N Q := by unfold codeBase; omega
  exact exec_setupCopy x hp hfit
    (show ExecWithin (B := .standard) w (.seq (.op (.copy Reg.source (bank Wanted.codes))) (ram[
        Reg.destination ← Reg.codes; Reg.length ← Reg.queryCount ])) x
        (((x.set Reg.source (Wanted.codeAddress L m N Q)).set Reg.destination
          (codeBase L m N Q)).set Reg.length Q) 3 by wram_exec *)
    (by omega) (by omega) (Or.inl (by omega))

/-- Actual argument setup and native copying preserve the caller protocol and every other
register beyond the copy routine. This is an internal producer-consumer execution interface. -/
public theorem exec_saveOriginals {w L m N Q : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x)
    (hsrc : x.regs (bank Wanted.originals) = Wanted.originalAddress L m N Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w saveOriginals x y (7 * Q + 10) ∧ Parameters L m N Q y ∧
      y.mem = ArrayCopy.copyPrefix x.mem (Wanted.originalAddress L m N Q)
        (originalBase L m N Q) (Q) ∧
      (∀ i, 7 ≤ i.val → i ≠ Reg.source → i ≠ Reg.destination → i ≠ Reg.length →
        y.regs i = x.regs i) := by
  have hb := group_copy_bounds L m N Q
  have horder : offsetBase L m N Q ≤ originalBase L m N Q := by unfold originalBase codeBase; omega
  exact exec_setupCopy x hp hfit
    (show ExecWithin (B := .standard) w (.seq (.op (.copy Reg.source (bank Wanted.originals))) (ram[
        Reg.destination ← Reg.originals; Reg.length ← Reg.queryCount ])) x
        (((x.set Reg.source (Wanted.originalAddress L m N Q)).set Reg.destination
          (originalBase L m N Q)).set Reg.length Q) 3 by wram_exec *)
    (by omega) (by omega) (Or.inl (by omega))

/-- Save all three actual routing arrays before the second producer reuses low memory.
Every protected value is read from the router's executed memory, and the complete outside
frame includes the protected original input and all untouched low cells. -/
public theorem exec_saveGroups {w L m N Q : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x) (wp : Wanted.Parameters L m N Q (x.comap bank))
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w saveGroups x y (7 * numBands L m N ^ 2 + 14 * Q + 37) ∧
      Parameters L m N Q y ∧
      (∀ t ≤ numBands L m N ^ 2,
        y.mem (offsetBase L m N Q + t) = x.mem (Wanted.offsetAddress L m N Q + t)) ∧
      (∀ j < Q, y.mem (codeBase L m N Q + j) = x.mem (Wanted.codeAddress L m N Q + j)) ∧
      (∀ j < Q, y.mem (originalBase L m N Q + j) =
        x.mem (Wanted.originalAddress L m N Q + j)) ∧
      (∀ a, a < offsetBase L m N Q ∨ originalBase L m N Q + Q ≤ a → y.mem a = x.mem a) := by
  obtain ⟨a, ha, ap, am, af⟩ := exec_saveOffsets x hp wp.offsets hfit
  obtain ⟨b, hb, bp, bm, bf⟩ := exec_saveCodes a ap (by regs_frame) hfit
  obtain ⟨y, hy, yp, ym, _⟩ := exec_saveOriginals b bp (by regs_frame) hfit
  have hbounds := group_copy_bounds L m N Q
  have hoff : offsetBase L m N Q + (numBands L m N ^ 2 + 1) = codeBase L m N Q := rfl
  have hcode : codeBase L m N Q + Q = originalBase L m N Q := rfl
  refine ⟨y, (ha.seq (hb.seq hy)).mono (by omega), yp, fun t ht => ?_, fun j hj => ?_,
    fun j hj => ?_, fun p hp => ?_⟩
  · rw [ym, ArrayCopy.copyPrefix_outside (by omega), bm, ArrayCopy.copyPrefix_outside (by omega),
      am, ArrayCopy.copyPrefix_read (by omega)]
  · rw [ym, ArrayCopy.copyPrefix_outside (by omega), bm, ArrayCopy.copyPrefix_read hj,
      am, ArrayCopy.copyPrefix_outside (by omega)]
  · rw [ym, ArrayCopy.copyPrefix_read hj, bm, ArrayCopy.copyPrefix_outside (by omega),
      am, ArrayCopy.copyPrefix_outside (by omega)]
  · rw [ym, ArrayCopy.copyPrefix_outside (by omega), bm, ArrayCopy.copyPrefix_outside (by omega),
      am, ArrayCopy.copyPrefix_outside (by omega)]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
