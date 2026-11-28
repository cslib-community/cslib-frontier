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
# Actual span capture and complete box-ABI restoration

The existing checked native span arithmetic is reused. Its computed low pointers are
captured before those registers are repurposed, and every scalar read by the retained
box constructor is restored. Scratch values from earlier queries may be arbitrary.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual checked span arithmetic and complete box argument restoration, including the
saved query cursors and real temporary-to-grouped copy arguments. -/
theorem exec_tileArguments {w L m t N Q j a b : ℕ} (x : Data 160)
    (hp : QueriedProduct.Parameters L m N Q x) (hb : Parameters L m t N Q x)
    (hx : x.regs QueriedProduct.Reg.index = j) (hj : j < numBands L m N ^ 2)
    (ha : x.mem (QueriedProduct.offsetBase L m N Q + j) = a)
    (hstop : x.mem (QueriedProduct.offsetBase L m N Q + j + 1) = b)
    (hab : a ≤ b) (hbQ : b ≤ Q) (hfit : Fits w (wordBudget L m t N Q)) :
    ∃ y, ExecWithin w tileArguments x y 44 ∧
      QueriedProduct.Parameters L m N Q y ∧ Parameters L m t N Q y ∧ y.mem = x.mem ∧
      y.regs QueriedProduct.Reg.index = j ∧
      BoxTable.CatalogueParameters L (m - t) (directoryBase L m N Q)
        (recordBase L m t N Q) (y.comap boxBank) ∧
      (y.comap boxBank).regs BoxTable.Reg.inner = m ∧
      (y.comap boxBank).regs BoxTable.Reg.threshold = t ∧
      (y.comap boxBank).regs BoxTable.Reg.values = valueBase L m t N Q ∧
      (y.comap boxBank).regs BoxTable.Reg.count = (boxes L m t).card ∧
      (y.comap boxBank).regs BoxTable.Reg.arrayA =
        BandPreparation.catalogueBase L m N + j / numBands L m N * 10 ^ L ∧
      (y.comap boxBank).regs BoxTable.Reg.arrayB =
        BandPreparation.catalogueBase L m N +
          (numBands L m N + j % numBands L m N) * 10 ^ L ∧
      (y.comap boxBank).regs BoxBatch.Reg.next = QueriedProduct.codeBase L m N Q + a ∧
      (y.comap boxBank).regs BoxBatch.Reg.stop = QueriedProduct.codeBase L m N Q + b ∧
      (y.comap boxBank).regs BoxBatch.Reg.output = resultBase L m t N Q ∧
      y.regs QueriedProduct.Reg.destination = QueriedProduct.groupedBase L m N Q + a ∧
      y.regs QueriedProduct.Reg.length = b - a := by
  have fq : Fits w (QueriedProduct.codeBase L m N Q + a + (b - a)) := by
    apply allocated_fits hfit
    have h10 := Nat.zero_le (10 ^ L)
    unfold memoryEnd resultBase stackBase valueBase recordBase directoryBase
      QueriedProduct.memoryEnd QueriedProduct.stampBase QueriedProduct.scratchBase
      QueriedProduct.outputBase QueriedProduct.groupedBase QueriedProduct.originalBase
    omega
  have fH : Fits w (m - t) := hfit.of_le (by unfold wordBudget; omega)
  have fS : Fits w (m - t + 1) := hfit.of_le (by unfold wordBudget; omega)
  have fST : Fits w ((m - t + 1) * 10 ^ L) := hfit.of_le (by unfold wordBudget; omega)
  refine WP.exists_execWithin ?_
  unfold tileArguments batchArguments restoreBoxArguments
  dsimp only
  wram_call (QueriedProduct.exec_tileArguments x hp hx hj ha hstop hab hbQ (old_fits hfit))
    with u ⟨up, um, ui, _, uL, uA, uB, uq, un, uo, _⟩
  have f10 : Fits w 10 := hfit.of_le (by unfold wordBudget; omega)
  wram_exec * [uL, uA, uB, uq, un, uo]
  wram_call (BoxTable.exec_constants (w := w)) canonical
    with c ⟨c0, c1, c10, c9, c3, cm, _⟩
  wram_exec * [c0, c1, c10, c9, c3]
  refine ⟨by regs_frame, by regs_frame, by wram_simp; exact cm.trans um, by regs_frame,
    by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
    by regs_frame, by regs_frame, by regs_frame, ?_, by regs_frame,
    by regs_frame, by regs_frame⟩
  have cstop : c.regs BoxBatch.Reg.stop = QueriedProduct.codeBase L m N Q + a + (b - a) := by
    regs_frame
  wram_simp [cstop]
  omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
