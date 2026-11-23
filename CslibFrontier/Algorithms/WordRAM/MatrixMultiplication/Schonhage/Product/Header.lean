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
  have hb0 : x.regs (bank BandPreparation.levels) = L := hp.fixed.levels
  have hb1 : x.regs (bank BandPreparation.inner) = m := hp.fixed.inner
  have hb2 : x.regs (bank BandPreparation.rows) = N := hp.fixed.rows
  have hb3 : x.regs (bank BandPreparation.columns) = D m := hp.columns
  have hb4 : x.regs (bank BandPreparation.masks) = 2 ^ L := hp.masks
  have hb5 : x.regs (bank BandPreparation.cells) = 7 ^ L := hp.cells
  have hb6 : x.regs (bank BandPreparation.leaves) = 10 ^ L := hp.leaves
  have hb7 : x.regs (bank BandPreparation.bands) = numBands L m N := hp.bands
  have hb8 : x.regs (bank BandPreparation.catalogue) = BandPreparation.catalogueBase L m N :=
    hp.catalogue
  refine WP.exists_execWithin ?_
  unfold layout
  wram_exec (disch := refine hsmall _ ?_; simp only [memoryEnd, stampBase, scratchBase,
    outputBase, groupedBase, originalBase, codeBase, offsetBase, snapshotBase, inputEnd,
    BandPreparation.memoryEnd, Wanted.memoryLimit_eq]; ring_nf; omega)
    [hQ, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8]
  refine ⟨?_, rfl⟩
  constructor <;> solve
    | wram_simp
    | (wram_simp; ring)
    | (wram_simp
       simp only [inputEnd, queryInputBase, snapshotBase, offsetBase, codeBase,
         originalBase, groupedBase, outputBase, scratchBase, stampBase, memoryEnd,
         BandPreparation.memoryEnd, Wanted.memoryLimit_eq, pow_two])
    | (wram_simp
       simp only [inputEnd, queryInputBase, snapshotBase, offsetBase, codeBase,
         originalBase, groupedBase, outputBase, scratchBase, stampBase, memoryEnd,
         BandPreparation.memoryEnd, Wanted.memoryLimit_eq, pow_two]
       ring)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
