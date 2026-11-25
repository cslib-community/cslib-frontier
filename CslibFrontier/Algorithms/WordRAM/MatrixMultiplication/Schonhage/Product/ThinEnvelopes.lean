/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Layout
import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Setup

/-!
# Thin-regime layout envelopes for queried products

In the source regime `D m ^ 18 ≤ N`, the queried product's protected-buffer layout
(`QueriedProduct.wordBudget`, `QueriedProduct.memoryEnd`) has polynomial magnitude, word-budget
and memory-end envelopes at every level `m ≤ L ≤ 21 * m`.
The queried product (level `19 * m`) and the routed box product (level `21 * m`) both take their
logarithmic admission widths from this one bound.

## Main results

* `QueriedProduct.thin_envelopes_of_le`: in the source regime `D m ^ 18 ≤ N`, at every level
  `m ≤ L ≤ 21 * m`, polynomial magnitude, word-budget and memory-end envelopes.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

private theorem thin_envelopes_of_bounds {L m N Q A Z : ℕ}
    (hz : 1 ≤ Z) (hN0 : N ≤ Z) (hQ0 : Q ≤ Z) (hA0 : A ≤ Z)
    (h10 : 10 ^ L ≤ Z) (h2 : 2 ^ L ≤ Z) (h7 : 7 ^ L ≤ Z) (hL : L ≤ Z)
    (hD : D m ≤ Z) (hB : numBands L m N ≤ Z) (hall : PrunedQuery.epochAllowance L ≤ 2 * Z) :
    magnitudeBound L A + wordBudget L m N Q + 1 ≤ 2 ^ 40 * Z ^ 5 ∧
      memoryEnd L m N Q ≤ 128 * Z ^ 2 := by
  have hz1 : 1 ≤ Z ^ 2 := Nat.one_le_pow _ _ hz
  have hz2 : Z ≤ Z ^ 2 := Nat.le_self_pow (by decide) _
  have hz23 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hz (by decide)
  have hz35 : Z ^ 3 ≤ Z ^ 5 := Nat.pow_le_pow_right hz (by decide)
  have hZ1 : (Z + 1) * Z = Z ^ 2 + Z := by rw [Nat.add_mul, Nat.one_mul, ← sq]
  have hii : inputEnd m N Q ≤ 9 * Z ^ 2 := by
    calc inputEnd m N Q ≤ 5 + 2 * (Z * Z) + 2 * Z := by dsimp only [inputEnd]; gcongr
      _ ≤ 9 * Z ^ 2 := by rw [← sq]; omega
  have hbe : BandPreparation.memoryEnd L m N ≤ 21 * Z ^ 2 := by
    calc BandPreparation.memoryEnd L m N
        ≤ ((4 + 2 * (Z * Z) + (2 + Z + Z) + Z) + (4 + 2 * (Z * Z)) + Z + Z) + 2 * Z * Z := by
          simp only [BandPreparation.memoryEnd, BandPreparation.catalogueBase,
            BandPreparation.tableBase, BandPreparation.inverseBase, BandPreparation.snapshotBase,
            BandPreparation.inputEnd, Encoding.scratchBase, Encoding.outputBase]
          gcongr
      _ ≤ 21 * Z ^ 2 := by rw [mul_assoc 2 Z Z, ← sq]; omega
  have hwe : Wanted.memoryLimit L m N Q ≤ 15 * Z ^ 2 := by
    calc Wanted.memoryLimit L m N Q ≤ 6 + 4 * Z + 2 * Z + 3 * Z ^ 2 := by
          rw [Wanted.memoryLimit_eq]; gcongr
      _ ≤ 15 * Z ^ 2 := by omega
  have hcc : codeBase L m N Q ≤ 56 * Z ^ 2 := by
    calc codeBase L m N Q ≤ (21 * Z ^ 2 + 15 * Z ^ 2 + 9 * Z ^ 2) + 9 * Z ^ 2 + Z ^ 2 + 1 := by
          dsimp only [codeBase, offsetBase, snapshotBase]; gcongr
      _ ≤ 56 * Z ^ 2 := by omega
  have hou : outputBase L m N Q ≤ 59 * Z ^ 2 := by
    calc outputBase L m N Q ≤ 56 * Z ^ 2 + Z + Z + Z := by
          dsimp only [outputBase, groupedBase, originalBase]; gcongr
      _ ≤ 59 * Z ^ 2 := by omega
  have hff : scratchBase L m N Q ≤ 60 * Z ^ 2 := by
    calc scratchBase L m N Q ≤ 59 * Z ^ 2 + Z := by dsimp only [scratchBase]; gcongr
      _ ≤ 60 * Z ^ 2 := by omega
  have hee : memoryEnd L m N Q ≤ 128 * Z ^ 2 := by
    calc memoryEnd L m N Q ≤ 60 * Z ^ 2 + 4 * (Z + 1) + 2 * (Z + 1) * Z + Z := by
          dsimp only [memoryEnd, stampBase]; gcongr
      _ ≤ 128 * Z ^ 2 := by rw [Nat.mul_assoc 2, hZ1]; omega
  have hep : epochBound L m N ≤ 3 * Z ^ 3 := by
    calc epochBound L m N ≤ Z ^ 2 * (1 + 2 * Z) := by dsimp only [epochBound]; gcongr
      _ = Z ^ 2 + 2 * Z ^ 3 := by
          rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm (Z ^ 2) 2, Nat.mul_assoc,
            ← pow_succ]
      _ ≤ 3 * Z ^ 3 := by omega
  have hbb : BandPreparation.wordBudget L m N ≤ 2048 * Z ^ 2 := by
    calc BandPreparation.wordBudget L m N
        ≤ 256 * (Z + Z + Z * Z + Z + Z + 2 * Z * Z + 1) := by
          dsimp only [BandPreparation.wordBudget]; gcongr
      _ ≤ 2048 * Z ^ 2 := by rw [mul_assoc 2 Z Z, ← sq]; omega
  have hwb : Wanted.wordBudget L m N Q ≤ 2 ^ 20 * Z ^ 2 := by
    have hrb : Wanted.routeBudget L m N (Wanted.tableAddress L Q) ≤ 1024 * Z ^ 2 := by
      calc Wanted.routeBudget L m N (Wanted.tableAddress L Q)
          ≤ 64 * (Z + Z + (Z * 2 + 5 + Z) + Z ^ 2 + Z + Z + 1) := by
            dsimp only [Wanted.routeBudget, Wanted.tableAddress, Wanted.inputLimit]; gcongr
        _ ≤ 1024 * Z ^ 2 := by omega
    calc Wanted.wordBudget L m N Q
        ≤ 256 * (2048 * Z ^ 2 + 1024 * Z ^ 2 + 15 * Z ^ 2 + Z + Z + Z + Z ^ 2 + Z + Z + 16) := by
          dsimp only [Wanted.wordBudget]; gcongr
      _ ≤ 2 ^ 20 * Z ^ 2 := by omega
  have hkb : PrunedQuery.kernelBudget L (scratchBase L m N Q)
      (BandPreparation.memoryEnd L m N) (BandPreparation.memoryEnd L m N)
      (codeBase L m N Q) (outputBase L m N Q) Q (epochBound L m N) ≤ 4096 * Z ^ 3 := by
    calc PrunedQuery.kernelBudget L (scratchBase L m N Q)
          (BandPreparation.memoryEnd L m N) (BandPreparation.memoryEnd L m N)
          (codeBase L m N Q) (outputBase L m N Q) Q (epochBound L m N)
        ≤ (256 * (Z + 1) * Z + 32 * Z + 512) +
            ((8 * (60 * Z ^ 2) + 64 * (Z + 1) * Z + 21 * Z ^ 2 + 21 * Z ^ 2 + 2 * Z +
              (3 * Z ^ 3 + 1) + 2 * Z + 128) + 4 * (56 * Z ^ 2 + 59 * Z ^ 2 + Z + 1)) := by
          dsimp only [PrunedQuery.kernelBudget, PrunedQuery.addressBound,
            PrunedQuery.evaluationBudget, PrunedQuery.nodeBudget]
          gcongr
      _ ≤ 4096 * Z ^ 3 := by rw [Nat.mul_assoc 256, Nat.mul_assoc 64, hZ1]; omega
  have hab : wordBudget L m N Q ≤ 2 ^ 32 * Z ^ 3 := by
    calc wordBudget L m N Q
        ≤ 1024 * (2048 * Z ^ 2 + 2 ^ 20 * Z ^ 2 + 4096 * Z ^ 3 + 128 * Z ^ 2 +
            9 * Z ^ 2 + Z + Z + Z + 16) := by
          dsimp only [wordBudget]; gcongr
      _ ≤ 2 ^ 32 * Z ^ 3 := by omega
  have hmg : magnitudeBound L A ≤ 4 * Z ^ 5 := by
    calc magnitudeBound L A ≤ Z * Z + Z * Z + Z * ((Z * Z) * (Z * Z)) + Z := by
          dsimp only [magnitudeBound, PrunedQuery.magnitudeBound]; gcongr
      _ ≤ 4 * Z ^ 5 := by
          have hZ5 : Z * ((Z * Z) * (Z * Z)) = Z ^ 5 := by ring
          rw [hZ5, ← sq]; omega
  exact ⟨by omega, hee⟩

/-- **Thin-regime envelopes at any level up to `21 * m`.** In the source regime
`D m ^ 18 ≤ N`, at every level `L` with `m ≤ L ≤ 21 * m`, the layout's magnitude, word budget
and memory end are bounded by explicit polynomials in `N + Q + A + 2`. The deliberately loose
integer constants leave a uniform logarithmic-width margin. -/
public theorem thin_envelopes_of_le (L m N Q A : ℕ) (hm : m ≤ L) (hL21 : L ≤ 21 * m)
    (hN : D m ^ 18 ≤ N) :
    magnitudeBound L A + wordBudget L m N Q + 1 ≤ 2 ^ 40 * (N + Q + A + 2) ^ 10 ∧
      memoryEnd L m N Q ≤ 128 * (N + Q + A + 2) ^ 4 := by
  let S := N + Q + A + 2
  let Z := S ^ 2
  have hs : 2 ≤ S := by dsimp only [S]; omega
  have hz : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have hsz : S ≤ Z := Nat.le_self_pow (by decide) _
  have hNN : N ≤ S := by dsimp only [S]; omega
  have hN0 : N ≤ Z := hNN.trans hsz
  have hQ0 : Q ≤ Z := (show Q ≤ S by dsimp only [S]; omega).trans hsz
  have hA0 : A ≤ Z := (show A ≤ S by dsimp only [S]; omega).trans hsz
  have hp : 10 ^ L ≤ N ^ 2 := by
    calc 10 ^ L ≤ 10 ^ (21 * m) := Nat.pow_le_pow_right (by decide) hL21
      _ = (10 ^ 21) ^ m := by rw [pow_mul]
      _ ≤ (4 ^ 36) ^ m := Nat.pow_le_pow_left (by decide) m
      _ = (D m ^ 18) ^ 2 := by
        simp only [D, ← pow_mul]
        congr 1
        omega
      _ ≤ N ^ 2 := Nat.pow_le_pow_left hN 2
  have h10 : 10 ^ L ≤ Z := hp.trans (Nat.pow_le_pow_left hNN 2)
  have h2 : 2 ^ L ≤ Z := (Nat.pow_le_pow_left (by decide : 2 ≤ 10) _).trans h10
  have h7 : 7 ^ L ≤ Z := (Nat.pow_le_pow_left (by decide : 7 ≤ 10) _).trans h10
  have hL : L ≤ Z := (Nat.lt_pow_self (by decide : 1 < 10)).le.trans h10
  have hD : D m ≤ Z := ((Nat.le_self_pow (by decide : 18 ≠ 0) _).trans hN).trans hN0
  have hbandpos : 0 < bandSize L m := Nat.mul_pos (K0_pos hm) (N0_pos _ _)
  have hbands : numBands L m N ≤ N := by
    apply Nat.le_of_lt_succ
    change (N + bandSize L m - 1) / bandSize L m < N + 1
    apply (Nat.div_lt_iff_lt_mul hbandpos).mpr
    have hmul := Nat.le_mul_of_pos_right N hbandpos
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hB : numBands L m N ≤ Z := hbands.trans hN0
  have hall : PrunedQuery.epochAllowance L ≤ 2 * Z := by
    unfold PrunedQuery.epochAllowance
    omega
  simpa only [Z, S, ← pow_mul, Nat.reduceMul] using
    thin_envelopes_of_bounds hz hN0 hQ0 hA0 h10 h2 h7 hL hD hB hall

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
