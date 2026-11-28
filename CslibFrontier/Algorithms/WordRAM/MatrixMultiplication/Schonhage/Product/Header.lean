/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Memory
import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Setup
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Charged protected-buffer calculation

## Main results

* `QueriedProduct.exec_layout`: calculate every persistent scalar from the actual producer
  header and original request count, with all intermediate fits derived from original inputs.

This is an internal execution API. It receives ordinary header equalities and a numerical
input bound, not a supplied layout or intermediate-state certificate.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual native layout calculation, preserving all original memory. -/
public theorem exec_layout {w L m N Q : ℕ} (x : Data 160)
    (hp : BandPreparation.BandParameters L m N (x.comap bank)) (hQ : x.mem 4 = Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w layout x y 50 ∧ Parameters L m N Q y ∧ y.mem = x.mem := by
  have hl := caller_fits hfit
  have h2 : 2 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  have h7 : 7 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
  have hsmall (v : ℕ) (hv : v ≤ 16 * (L + N + Q + memoryEnd L m N Q + 16)) :
      Fits w v := hl.of_le hv
  have reg {r v} (h : (x.comap bank).regs r = v) : x.regs (bank r) = v := h
  refine WP.exists_execWithin ?_
  wram_exec (disch := refine hsmall _ ?_; simp only [memoryEnd, stampBase, scratchBase,
    outputBase, groupedBase, originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
    BandPreparation.memoryEnd, Wanted.memoryLimit_eq]; ring_nf; omega)
    [layout, hQ, reg hp.fixed.levels, reg hp.fixed.inner, reg hp.fixed.rows, reg hp.columns,
      reg hp.masks, reg hp.cells, reg hp.leaves, reg hp.bands, reg hp.catalogue]
  refine ⟨?_, rfl⟩
  constructor <;> solve
    | wram_simp
    | (wram_simp; ring)
    | (wram_simp
       simp only [inputEnd, queryInputBase, snapshotBase, offsetBase, codeBase,
         originalBase, groupedBase, outputBase, scratchBase, stampBase, memoryEnd,
         BandPreparation.memoryEnd, Wanted.memoryLimit_eq, pow_two]
       ring)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
