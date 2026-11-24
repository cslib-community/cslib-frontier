/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Front
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Transfer
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Actual restoration of the original matrix, coordinate and threshold words

The unchanged native copy restores every original matrix/coordinate word and the native
length header from its protected snapshot. Two final instructions restore the additional
threshold word, which was retained in a high register before producer reuse.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM

/-- Actual restoration copy and threshold store, with their complete memory readback. -/
theorem exec_restoreInput {W L m t N Q : ℕ} (x : Data 160)
    (hp : QueriedProduct.Parameters L m N Q x) (ht : x.regs Reg.threshold = t)
    (hfit : Fits W (wordBudget L m t N Q)) :
    ∃ y, ExecWithin W restoreInput x y (7 * QueriedProduct.inputEnd m N Q + 12) ∧
      QueriedProduct.Parameters L m N Q y ∧
      y.mem = Function.update
        (ArrayCopy.copyPrefix x.mem (QueriedProduct.snapshotBase L m N Q) 0
          (QueriedProduct.inputEnd m N Q)) (QueriedProduct.inputEnd m N Q) t := by
  have hfI : Fits W (QueriedProduct.inputEnd m N Q) :=
    hfit.of_le (by unfold wordBudget QueriedProduct.wordBudget; omega)
  refine WP.exists_execWithin ?_
  unfold restoreInput restoreThreshold
  wram_call (QueriedProduct.exec_restoreInput x hp (old_fits hfit)) with u ⟨up, um⟩
  have ut : u.regs Reg.threshold = t := by regs_frame
  wram_exec * [ut]
  refine ⟨by regs_frame, ?_⟩
  wram_simp [um]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
