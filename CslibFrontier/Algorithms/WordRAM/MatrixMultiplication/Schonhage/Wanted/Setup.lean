/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Memory
public import CslibFrontier.Algorithms.MatrixMultiplication.Schonhage.BandBounds
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Actual initialization of wanted-query parameters

## Main results

* `Wanted.exec_setup`: read the query count and compute all relocated addresses natively.
* `Wanted.exec_tables`: scalar/header/count setup and actual valid-mask tables from the
  original four input words, preserving every original query word.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Expanded allocated size, useful without hiding any arithmetic behind a layout record. -/
theorem memoryLimit_eq (L m N Q : ℕ) :
    memoryLimit L m N Q = 6 + 4 * Q + 2 * 2 ^ L + 3 * numBands L m N ^ 2 := by
  simp only [memoryLimit, originalAddress, codeAddress, cursorAddressBase,
    offsetAddress, countAddress, tableAddress, inputLimit]
  omega

/-- The original numerical word budget covers every scalar used by the grouping loops. -/
theorem local_fits {w L m N Q : ℕ} (hfit : Fits w (wordBudget L m N Q)) :
    Fits w (16 * (L + N + Q + memoryLimit L m N Q + 10 ^ L + 2 ^ L +
      numBands L m N ^ 2 + 16)) := by
  apply hfit.of_le
  unfold wordBudget routeBudget
  omega

/-- Relocate the actual computed-table parameters after the input and allocate all
count/prefix/cursor/code/permutation arrays using charged native arithmetic. -/
theorem exec_setup {w L m N Q : ℕ} (x : Data 96)
    (hx : BandPreparation.BandParameters L m N x) (hQ : x.mem 4 = Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w setup x y 16 ∧ Parameters L m N Q y ∧ y.mem = x.mem := by
  have hl := local_fits hfit
  have hend := memoryLimit_eq L m N Q
  have hf (v : ℕ) (hv : v ≤ memoryLimit L m N Q + 10 ^ L) : Fits w v :=
    hl.of_le (by omega)
  have hB : bandSize L m ≤ 10 ^ L :=
    (bandSize_le_seven_pow L m).trans (Nat.pow_le_pow_left (by decide) _)
  have h5 : Fits w 5 := hf _ (by omega)
  have h4 : Fits w 4 := hf _ (by omega)
  have hq2 : Fits w (Q * 2) := hf _ (by omega)
  have hb : Fits w (bandSize L m) := hf _ (by omega)
  have ht2 : Fits w (numBands L m N * numBands L m N) := hf _ (by rw [← sq]; omega)
  simp only [bandSize] at hb
  obtain ⟨hi, ht, hc, ho, hcur0, hcur, hco, horig, hefit⟩ :
      Fits w (inputLimit Q) ∧ Fits w (tableAddress L Q) ∧ Fits w (countAddress L Q) ∧
      Fits w (offsetAddress L m N Q) ∧ Fits w (offsetAddress L m N Q + numBands L m N ^ 2) ∧
      Fits w (cursorAddressBase L m N Q) ∧ Fits w (codeAddress L m N Q) ∧
      Fits w (originalAddress L m N Q) ∧ Fits w (memoryLimit L m N Q) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine hf _ ?_ <;>
      simp only [memoryLimit, originalAddress, codeAddress, cursorAddressBase, offsetAddress,
        countAddress, tableAddress, inputLimit] <;> omega
  simp only [memoryLimit, originalAddress, codeAddress, cursorAddressBase, offsetAddress,
    countAddress, tableAddress, inputLimit, pow_two] at hi ht hc ho hcur0 hcur hco horig hefit
  refine WP.exists_execWithin ?_
  wram_exec * [setup, hQ, h4, h5, hq2, hi, ht, hc, hb, ht2, ho, hcur0, hcur, hco, horig, hefit]
  refine ⟨?_, rfl⟩
  refine ⟨?_, ?_, by wram_simp, by wram_simp, by wram_simp; rfl,
    by wram_simp; simp only [offsetAddress, countAddress, tableAddress, inputLimit, pow_two],
    by wram_simp; simp only [cursorAddressBase, offsetAddress, countAddress, tableAddress,
      inputLimit, pow_two],
    by wram_simp; simp only [codeAddress, cursorAddressBase, offsetAddress, countAddress,
      tableAddress, inputLimit, pow_two],
    by wram_simp; simp only [originalAddress, codeAddress, cursorAddressBase, offsetAddress,
      countAddress, tableAddress, inputLimit, pow_two],
    by wram_simp [pow_two], by wram_simp; rfl,
    by wram_simp; simp only [memoryLimit, originalAddress, codeAddress, cursorAddressBase,
      offsetAddress, countAddress, tableAddress, inputLimit, pow_two]⟩
  · constructor <;> solve | wram_simp * | (wram_simp *; rfl)
  · constructor <;> solve | wram_simp * | (wram_simp *; rfl)

/-- The initialized producer of the tables used by routing, without invoking any encoders.
The only memory changes are the two relocated mask tables after the complete query input. -/
theorem exec_tables {w L m N Q : ℕ} (hm : m ≤ L) (x : Data 96)
    (hL : x.mem 1 = L) (hmemory : x.mem 2 = m) (hN : x.mem 3 = N) (hQ : x.mem 4 = Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w (.seq BandPreparation.header (.seq BandPreparation.countCode
      (.seq setup BandPreparation.tablesCode))) x y
        (16 * L + (12 * L + 33) * 2 ^ L + 85) ∧ Parameters L m N Q y ∧
      (∀ gh : Fin (K0 L m) × Fin (K0 L m),
        y.mem (tableAddress L Q + (MaskTable.pairRank gh).val) =
          (MaskTable.selectedMask gh).val) ∧
      (∀ a, a < inputLimit Q ∨ tableAddress L Q + 2 ^ L ≤ a → y.mem a = x.mem a) := by
  have h10 := Nat.zero_le (10 ^ L)
  have h2 := Nat.zero_le (2 ^ L)
  have hpfit : Fits w (BandPreparation.wordBudget L m N) :=
    hfit.of_le (by unfold wordBudget; omega)
  obtain ⟨h, hh, hparams, hmem⟩ := BandPreparation.exec_header hm x hL hmemory hN hpfit
  obtain ⟨c, hc, cp, cm⟩ := BandPreparation.exec_countCode h hparams hpfit
  obtain ⟨s, hs, sp, sm⟩ := exec_setup c cp (by rw [cm, hmem]; exact hQ) hfit
  have htfit : Fits w (inputLimit Q + tableAddress L Q + 2 ^ L + L + 4) := by
    apply (local_fits hfit).of_le
    have := memoryLimit_eq L m N Q
    unfold tableAddress inputLimit
    omega
  obtain ⟨y, hy, _, _, hforward, hf⟩ := BandPreparation.exec_tables L m
    (inputLimit Q) (tableAddress L Q) s sp.tables (by rfl) htfit
  refine ⟨y, ?_, by regs_frame, hforward, ?_⟩
  · exact (hh.seq (hc.seq (hs.seq hy))).mono
      (by nlinarith only [Nat.zero_le ((6 * L + 16) * 2 ^ L)])
  · intro a ha
    unfold tableAddress at *
    rw [hf a (by omega) (by omega), sm, cm, hmem]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
