/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Transfer
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Computing each tile's actual kernel arguments

## Main results

* `QueriedProduct.exec_tileArguments`: load real group endpoints, divide the tile index,
  compute shared catalogue/query/output pointers and populate the existing native kernel ABI.

The span values in this internal interface describe the actual saved offset words. The full
caller establishes their bounds from its executed counting/prefix/scatter passes.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual tile-index arithmetic and kernel-argument setup cost twenty-one instructions.
Only the two real offset words are read. Every unsigned arithmetic fit follows from the
original allocation bound and the computed span bounds. -/
public theorem exec_tileArguments {w L m N Q t a b : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x) (hx : x.regs Reg.index = t) (ht : t < numBands L m N ^ 2)
    (ha : x.mem (offsetBase L m N Q + t) = a)
    (hb : x.mem (offsetBase L m N Q + t + 1) = b) (hab : a ≤ b) (hbQ : b ≤ Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w tileArguments x y 21 ∧ Parameters L m N Q y ∧ y.mem = x.mem ∧
      y.regs Reg.index = t ∧ y.regs Reg.epoch = x.regs Reg.epoch ∧
      (y.comap bank).regs PrunedQuery.inputDepth = L ∧
      (y.comap bank).regs PrunedQuery.arrayA =
        BandPreparation.catalogueBase L m N + t / numBands L m N * 10 ^ L ∧
      (y.comap bank).regs PrunedQuery.arrayB =
        BandPreparation.catalogueBase L m N +
          (numBands L m N + t % numBands L m N) * 10 ^ L ∧
      (y.comap bank).regs PrunedQuery.queries = codeBase L m N Q + a ∧
      (y.comap bank).regs PrunedQuery.queryCount = b - a ∧
      (y.comap bank).regs PrunedQuery.output = groupedBase L m N Q + a ∧
      (y.comap bank).regs PrunedQuery.scratch = scratchBase L m N Q ∧
      (y.comap bank).regs PrunedQuery.epoch = x.regs Reg.epoch := by
  let B := numBands L m N
  let H := 10 ^ L
  let C := BandPreparation.catalogueBase L m N
  have hB : 0 < B := by dsimp [B] at *; nlinarith only [ht, Nat.zero_le t]
  have hH : 1 ≤ H := Nat.one_le_pow L _ (by decide)
  have hr : t / B < B := (Nat.div_lt_iff_lt_mul hB).mpr (by simpa [B, pow_two] using ht)
  have hc : t % B < B := Nat.mod_lt t hB
  have hrH : t / B * H ≤ B * H := Nat.mul_le_mul_right H hr.le
  have hcH : (t % B + B) * H ≤ 2 * B * H := Nat.mul_le_mul_right H (by omega)
  have horder : C + 2 * B * H ≤ memoryEnd L m N Q := by
    have h := (producers_le_snapshot L m N Q).1
    have h' := (transfer_bounds L m N Q).2.1
    dsimp only [C, B, H, BandPreparation.memoryEnd] at *
    omega
  have hcodes : codeBase L m N Q + Q ≤ memoryEnd L m N Q := by
    unfold memoryEnd stampBase scratchBase outputBase groupedBase originalBase; omega
  have hgroups : groupedBase L m N Q + Q ≤ memoryEnd L m N Q := by
    unfold memoryEnd stampBase scratchBase outputBase; omega
  have htiles : offsetBase L m N Q + B ^ 2 + 1 ≤ memoryEnd L m N Q := by
    dsimp only [B]; unfold codeBase at hcodes; omega
  have foffset : Fits w (offsetBase L m N Q + t) :=
    allocated_fits hfit (by dsimp only [B] at *; omega)
  have fnext : Fits w (offsetBase L m N Q + t + 1) :=
    allocated_fits hfit (by dsimp only [B] at *; omega)
  have frow : Fits w (t / B) := allocated_fits hfit (by nlinarith only [hr, hH, horder])
  have fcol : Fits w (t % B) := allocated_fits hfit (by nlinarith only [hc, hH, horder])
  have frowH : Fits w (t / B * H) := allocated_fits hfit (by nlinarith only [hrH, horder])
  have fleft : Fits w (t / B * H + C) := allocated_fits hfit (by nlinarith only [hrH, horder])
  have fcb : Fits w (t % B + B) := allocated_fits hfit (by
    nlinarith only [hcH, hH, horder, Nat.zero_le (t % B + B)])
  have fcbH : Fits w ((t % B + B) * H) := allocated_fits hfit (by omega)
  have fright : Fits w ((t % B + B) * H + C) := allocated_fits hfit (by omega)
  have fq : Fits w (codeBase L m N Q + a) := allocated_fits hfit (by omega)
  have fo : Fits w (groupedBase L m N Q + a) := allocated_fits hfit (by omega)
  have fn : Fits w (b - a) := allocated_fits hfit (by omega)
  dsimp only [B, H, C] at frow fcol frowH fleft fcb fcbH fright
  refine WP.exists_execWithin ?_
  unfold tileArguments
  wram_exec * [ha, hb, foffset, fnext, frow, fcol, frowH, fleft, fcb, fcbH, fright, fq, fo, fn]
  refine ⟨by regs_frame, rfl, ?_⟩
  simp only [Data.comap_regs]
  wram_simp [hx]
  exact ⟨by ring, by ring⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
