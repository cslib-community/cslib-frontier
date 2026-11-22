/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.FrontProgram
public import Mathlib.Data.Nat.Log
import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandFlat
import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.Program
import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Width
import CslibFrontier.Computability.WordRAM.Admission
import CslibFrontier.Computability.WordRAM.Width
import CslibFrontier.Foundations.Data.Nat.PowClog

/-!
# Original-input width admission for routed native box products

A binary ceiling logarithm of original magnitude and allocation envelopes admits the
whole fixed program. The threshold is data read from the original input; physical
width is never read. Minimum-width words have an explicit original-input envelope.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM

/-- Sufficient physical width derived from original dimensions, threshold and entry magnitude. -/
@[expose] def admissionWidth (L m t N Q A : ℕ) : ℕ :=
  Nat.clog 2 (magnitudeBound L A + wordBudget L m t N Q + 1) + 3

/-- Width admission is positive even for zero-size matrices and zero-magnitude entries. -/
theorem admissionWidth_pos (L m t N Q A : ℕ) : 0 < admissionWidth L m t N Q A := by
  unfold admissionWidth
  omega

/-- Original-input logarithmic admission derives all separate scalar and signed budgets. -/
theorem admission_bounds {W L m t N Q A : ℕ}
    (hW : admissionWidth L m t N Q A ≤ W) :
    0 < W - 2 ∧ magnitudeBound L A < 2 ^ ((W - 2) - 1) ∧
      Fits W (wordBudget L m t N Q) := by
  have hs : Nat.clog 2 (magnitudeBound L A + wordBudget L m t N Q + 1) ≤ (W - 2) - 1 := by
    unfold admissionWidth at hW
    omega
  refine ⟨by unfold admissionWidth at hW; omega, ?_, ?_⟩
  · exact fits_of_lt_clog_le
      (by omega : magnitudeBound L A < magnitudeBound L A + wordBudget L m t N Q + 1) hs
  · exact fits_of_lt_clog_le
      (by omega : wordBudget L m t N Q < magnitudeBound L A + wordBudget L m t N Q + 1) (by omega)

/-- Original-input word/support envelope, independent of larger admitted physical widths. -/
@[expose] def wordBound (L m t N Q A : ℕ) : ℕ :=
  16 * (magnitudeBound L A + wordBudget L m t N Q + 1)

/-- Every minimum-admission word is strictly below the same original-input envelope. -/
theorem pow_admissionWidth_lt_wordBound (L m t N Q A : ℕ) :
    2 ^ admissionWidth L m t N Q A < wordBound L m t N Q A := by
  let budget := magnitudeBound L A + wordBudget L m t N Q + 1
  have h : 2 ^ Nat.clog 2 budget < 2 * budget :=
    Nat.pow_clog_lt_mul Nat.one_lt_two (Nat.succ_ne_zero _)
  change 2 ^ (Nat.clog 2 budget + 3) < 16 * budget
  rw [pow_add]
  omega

/-- Complete native code, including halt, has constant size independently of all inputs. -/
theorem program_size_le (bits : Bool) : (program bits).size + 1 ≤ 32768 := by
  have hw := Wanted.program_length_le
  have hb := BandPreparation.program_length_le
  simp only [Code.program, List.length_append, Code.length_assemble,
    List.length_singleton] at hw hb
  have hqb := BoxBatch.queryProgram_size_le
  have hload : loadThreshold.size ≤ 512 := by decide +kernel
  have hpre :
      (Code.seq QueriedProduct.parameters (.seq QueriedProduct.layout
        (.seq QueriedProduct.saveInput QueriedProduct.prepareQueries))).size ≤ 1024 := by
    decide +kernel
  have hsave : QueriedProduct.saveGroups.size ≤ 256 := by decide +kernel
  have hmat : (QueriedProduct.prepareMatrices bits).size ≤ 128 := by
    cases bits <;> decide +kernel
  have hgeom : prepareGeometry.size ≤ 1024 := by decide +kernel
  have harg : tileArguments.size ≤ 128 := by decide +kernel
  have htile : BoxTable.tile.size ≤ 1024 := by decide +kernel
  have hcopy :
      (Code.seq copyResults
        (ram[ QueriedProduct.Reg.index ←
          QueriedProduct.Reg.index + QueriedProduct.Reg.one ])).size ≤ 64 := by
    decide +kernel
  have htail : (Code.seq QueriedProduct.reconstruct restoreInput).size ≤ 128 := by
    decide +kernel
  simp only [program, front, QueriedProduct.prepareRouting, evaluateTiles, tileStep,
    Code.size, Code.size_rename] at hpre hcopy htail ⊢
  omega

/-- Neither input mode reads physical width. -/
theorem not_readsWidth (bits : Bool) : ¬(program bits).ReadsWidth := by
  have hw := Wanted.not_readsWidth
  have hb := BandPreparation.not_readsWidth
  have hqb := BoxBatch.not_readsWidth
  have hload : ¬loadThreshold.ReadsWidth := by decide +kernel
  have hpre :
      ¬(Code.seq QueriedProduct.parameters (.seq QueriedProduct.layout
        (.seq QueriedProduct.saveInput QueriedProduct.prepareQueries))).ReadsWidth := by
    decide +kernel
  have hsave : ¬QueriedProduct.saveGroups.ReadsWidth := by decide +kernel
  have hmat : ¬(QueriedProduct.prepareMatrices bits).ReadsWidth := by
    cases bits <;> decide +kernel
  have hgeom : ¬prepareGeometry.ReadsWidth := by decide +kernel
  have harg : ¬tileArguments.ReadsWidth := by decide +kernel
  have htile : ¬BoxTable.tile.ReadsWidth := by decide +kernel
  have hcopy :
      ¬(Code.seq copyResults
        (ram[ QueriedProduct.Reg.index ←
          QueriedProduct.Reg.index + QueriedProduct.Reg.one ])).ReadsWidth := by
    decide +kernel
  have htail : ¬(Code.seq QueriedProduct.reconstruct restoreInput).ReadsWidth := by
    decide +kernel
  simp only [program, front, QueriedProduct.prepareRouting, evaluateTiles, tileStep,
    Code.ReadsWidth, Code.readsWidth_rename] at hpre hcopy htail ⊢
  tauto

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
