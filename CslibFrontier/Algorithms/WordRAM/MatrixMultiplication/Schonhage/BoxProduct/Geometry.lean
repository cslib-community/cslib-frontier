/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.State
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall


/-!
# One actual shared box-geometry construction for all tiles

The constructor consumes original depth, inner count, threshold and an actual directory
pointer. Its computed records, retained-value base and compact count are saved in the high
bank. No assumed table or geometry execution is supplied to this stage.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Construct shared geometry exactly once, save its actual addresses/count and initialize
the reusable sparse-result allocation and tile index. -/
theorem exec_prepareGeometry {w L m t N Q : ℕ} (x : Data 160)
    (hp : QueriedProduct.Parameters L m N Q x) (ht : x.regs Reg.threshold = t)
    (hfit : Fits w (wordBudget L m t N Q)) :
    ∃ y, ExecWithin w prepareGeometry x y (BoxTable.geometryTime L m t + 17) ∧
      QueriedProduct.Parameters L m N Q y ∧ Parameters L m t N Q y ∧
      y.regs QueriedProduct.Reg.index = 0 ∧ Geometry L m t N Q y.mem ∧
      (∀ p, ¬(directoryBase L m N Q ≤ p ∧ p < valueBase L m t N Q) →
        y.mem p = x.mem p) := by
  let D := directoryBase L m N Q
  let R := recordBase L m t N Q
  let V := valueBase L m t N Q
  let K := (boxes L m t).card
  have hT : 10 ^ L ≤ (L + 1) * 10 ^ L := Nat.le_mul_of_pos_left _ (by omega)
  have fBudget : Fits w (wordBudget L m t N Q) := hfit
  unfold wordBudget at fBudget
  have fK : Fits w (((L + 1) * 10 ^ L + 10) * 5 + V + K) := allocated_fits hfit (by
    unfold memoryEnd resultBase stackBase BoxQuery.stackCapacity; dsimp only [V, K]; omega)
  have htime : 12 + (4 * L + 20 + (11 * L + 28) * ((m - t + 1) * 10 ^ L)) + 5 ≤
      BoxTable.geometryTime L m t + 17 := by
    unfold BoxTable.geometryTime; omega
  unfold prepareGeometry geometryHead geometryFinish
  dsimp only
  have fGeom : Fits w (D + (D + (m - t + 1) * 10 ^ L) +
      6 * ((m - t + 1) * 10 ^ L) + 10 ^ L + L + m + 12) :=
    hfit.of_le (by unfold wordBudget; dsimp only [D]; omega)
  wram_exec * [ht]
  wram_call (BoxTable.exec_geometry (w := w) (L := L) (m := m) (t := t) (D := D)) canonical
    with z ⟨zp, zK, zV, zcat⟩
  rw [show D + (m - t + 1) * 10 ^ L = R from rfl] at zp
  rw [show D + (m - t + 1) * 10 ^ L + 3 * K = V from rfl] at zV
  wram_exec * [zK, zV, zp.records]
  refine ⟨by regs_frame, ?_, by wram_simp, ⟨zcat.directory, zcat.code, zcat.stars, zcat.stride⟩, ?_⟩
  · refine ⟨by regs_frame, by regs_frame, by wram_simp; rfl, by wram_simp; rfl, by wram_simp, ?_⟩
    wram_simp; unfold resultBase stackBase BoxQuery.stackCapacity; dsimp only [V, K]; omega
  · intro p hp'
    unfold valueBase recordBase at hp'
    wram_simp
    exact zcat.frame p (by dsimp only [D]; omega)
      (by rw [BoxTable.count_eligible_eq_card_boxes]; dsimp only [R, D]; omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
