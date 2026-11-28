/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandMemory
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandHeader

/-!
# Native copies used by the band-preparation caller

## Main results

* `BandPreparation.exec_copyKernel`: reuse the actual array-copy program in its fixed low
  register bank, preserving every persistent register and permitting both address orders.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM

/-- The seven low copy registers are embedded injectively. -/
theorem copyRegisters_injective : Function.Injective copyRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 96 => i.val) h)

/-- The unchanged encoder occupies precisely its original low register bank. -/
theorem encoderRegisters_injective : Function.Injective encoderRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 96 => i.val) h)

/-- Copying uses only the original seven-register routine and its actual native cost.
The persistent high register bank is untouched; arbitrary outside memory is preserved
by the explicit `copyPrefix` result. -/
theorem exec_copyKernel {w : ℕ} (x : Data 96) (h1 : Fits w 1)
    (hs : Fits w (x.regs copySrc + x.regs copyLen))
    (hd : Fits w (x.regs copyDst + x.regs copyLen))
    (hsep : x.regs copySrc + x.regs copyLen ≤ x.regs copyDst ∨
      x.regs copyDst + x.regs copyLen ≤ x.regs copySrc ∨ x.regs copySrc = x.regs copyDst) :
    ∃ y, ExecWithin w (ArrayCopy.program.rename copyRegisters) x y (7 * x.regs copyLen + 4) ∧
      y.mem = ArrayCopy.copyPrefix x.mem (x.regs copySrc) (x.regs copyDst) (x.regs copyLen) ∧
      (∀ i, 7 ≤ i.val → y.regs i = x.regs i) := by
  obtain ⟨y, he, ⟨hm, _, _, _⟩, frame⟩ := ExecWithin.rename_post copyRegisters_injective
    (ArrayCopy.exec_of_separated_or_eq (x.comap copyRegisters) h1 hs hd hsep)
  refine ⟨y, he, hm, ?_⟩
  intro i hi
  exact frame i (by
    intro j hj
    have hv := congrArg Fin.val hj
    have := j.isLt
    change j.val = i.val at hv
    omega)

/-- Protect the entire original initialized prefix, including header zero, with the actual
native copy. Source words and all memory outside the snapshot block remain untouched. -/
theorem exec_saveInput {w L m N : ℕ} (x : Data 96) (hx : HeaderPost L m N x)
    (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w saveInput x y (7 * inputEnd m N + 7) ∧
      y.mem = ArrayCopy.copyPrefix x.mem 0 (snapshotBase L m N) (inputEnd m N) ∧
      (∀ i, 7 ≤ i.val → y.regs i = x.regs i) := by
  have hb : Fits w (inputEnd m N) := (memory_fits hfit).of_le (input_le_memoryEnd L m N)
  have hi : Fits w (snapshotBase L m N + inputEnd m N) :=
    (memory_fits hfit).of_le (inverse_le_memoryEnd L m N)
  wram_exec * [saveInput]
  wram_call (exec_copyKernel _ (small_fits hfit (by decide)) (by wram_simp; exact hb)
    (by wram_simp; exact hi) (Or.inl (by wram_simp; exact input_le_snapshot L m N)))
    with y ⟨hm, hf⟩
  refine ⟨by wram_simp; omega, by wram_simp at hm; exact hm, ?_⟩
  intro i hi'
  rw [hf i hi']
  have hne : i ≠ copySrc ∧ i ≠ copyDst ∧ i ≠ copyLen := by
    simp only [copySrc, copyDst, copyLen, ne_eq, Fin.ext_iff]
    omega
  wram_simp [hne.1, hne.2.1, hne.2.2]

/-- Restore the complete original input using the reverse disjoint-copy case. This copies
the actual protected words rather than reconstructing or assuming the input is unchanged. -/
theorem exec_restoreInput {w L m N : ℕ} (x : Data 96) (hx : HeaderPost L m N x)
    (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w restoreInput x y (7 * inputEnd m N + 7) ∧
      y.mem = ArrayCopy.copyPrefix x.mem (snapshotBase L m N) 0 (inputEnd m N) ∧
      (∀ i, 7 ≤ i.val → y.regs i = x.regs i) := by
  have hb : Fits w (inputEnd m N) := (memory_fits hfit).of_le (input_le_memoryEnd L m N)
  have hi : Fits w (snapshotBase L m N + inputEnd m N) :=
    (memory_fits hfit).of_le (inverse_le_memoryEnd L m N)
  wram_exec * [restoreInput]
  wram_call (exec_copyKernel _ (small_fits hfit (by decide)) (by wram_simp; exact hi)
    (by wram_simp; exact hb) (Or.inr (Or.inl (by wram_simp; exact input_le_snapshot L m N))))
    with y ⟨hm, hf⟩
  refine ⟨by wram_simp; omega, by wram_simp at hm; exact hm, ?_⟩
  intro i hi'
  rw [hf i hi']
  have hne : i ≠ copySrc ∧ i ≠ copyDst ∧ i ≠ copyLen := by
    simp only [copySrc, copyDst, copyLen, ne_eq, Fin.ext_iff]
    omega
  wram_simp [hne.1, hne.2.1, hne.2.2]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
