/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.RegisterFrame
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.Program

/-!
# Actual native CountPrime workspace calculation

The existing native power routine computes the padded side from the computed depth.
Ordinary arithmetic instructions then calculate every matrix/residue/spread/workspace
pointer. The register assertions below describe the actual resulting state; no layout
object is supplied to the program. All intermediate fits follow from one original-parameter
numerical envelope. This module performs no allocation, clearing or memory copy.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- Original-parameter physical envelope for real layout arithmetic and power evaluation. -/
@[expose] def layoutWordBound (n p k scratch : ℕ) : ℕ :=
  scratch + 3 * (n * n) + 2 ^ k + 4 * (4 ^ k * p) + k + 2 * p + 16

/-- The actual metadata words computed by the native layout routine. This internal
postcondition contains no execution, time or multiplication contract. -/
structure LayoutRegisters (n p k scratch : ℕ) (x : Data 128) : Prop where
  /-- Original side survives the power call and all pointer arithmetic. -/
  side_eq : x.regs Reg.side = n
  /-- Original modulus survives. -/
  modulus_eq : x.regs Reg.modulus = p
  /-- Computed depth survives. -/
  depth_eq : x.regs Reg.depth = k
  /-- Original workspace base survives. -/
  scratch_eq : x.regs Reg.scratch = scratch
  /-- Actual native power result. -/
  paddedSide_eq : x.regs Reg.paddedSide = 2 ^ k
  /-- Original matrix length. -/
  cells_eq : x.regs Reg.cells = n * n
  /-- Padded cyclic-coefficient matrix length. -/
  area_eq : x.regs Reg.area = 4 ^ k * p
  /-- Padded scalar-matrix length. -/
  paddedCells_eq : x.regs Reg.paddedCells = 4 ^ k
  /-- Canonical signed positive modulus word. -/
  encodedModulus_eq : x.regs Reg.encodedModulus = 2 * p
  /-- First actual residue block. -/
  residueAB_eq : x.regs Reg.residueAB = scratch
  /-- Second actual residue block. -/
  residueBC_eq : x.regs Reg.residueBC = scratch + n * n
  /-- Third actual residue block. -/
  residueAC_eq : x.regs Reg.residueAC = scratch + 2 * (n * n)
  /-- Actual spread table. -/
  spread_eq : x.regs Reg.spread = scratch + 3 * (n * n)
  /-- Actual first coefficient matrix. -/
  matrixP_eq : x.regs Reg.matrixP = scratch + 3 * (n * n) + 2 ^ k
  /-- Actual second coefficient matrix. -/
  matrixQ_eq : x.regs Reg.matrixQ = scratch + 3 * (n * n) + 2 ^ k + 4 ^ k * p
  /-- Actual product coefficient matrix. -/
  matrixR_eq : x.regs Reg.matrixR = scratch + 3 * (n * n) + 2 ^ k + 2 * (4 ^ k * p)
  /-- Reusable native Strassen scratch begins after all three coefficient matrices. -/
  productScratch_eq : x.regs Reg.productScratch =
    scratch + 3 * (n * n) + 2 ^ k + 3 * (4 ^ k * p)

/-- Registers actually written by layout, including the complete low power bank. -/
@[expose] def LayoutLocal (i : Fin 128) : Prop := i.val < 5 ∨ i = Reg.paddedSide ∨
  i = Reg.cells ∨ i = Reg.paddedCells ∨ i = Reg.area ∨ i = Reg.encodedModulus ∨
  i = Reg.residueAB ∨ i = Reg.residueBC ∨ i = Reg.residueAC ∨ i = Reg.spread ∨
  i = Reg.matrixP ∨ i = Reg.matrixQ ∨ i = Reg.matrixR ∨ i = Reg.productScratch

instance (i : Fin 128) : Decidable (LayoutLocal i) :=
  inferInstanceAs (Decidable (i.val < 5 ∨ i = Reg.paddedSide ∨
    i = Reg.cells ∨ i = Reg.paddedCells ∨ i = Reg.area ∨ i = Reg.encodedModulus ∨
    i = Reg.residueAB ∨ i = Reg.residueBC ∨ i = Reg.residueAC ∨ i = Reg.spread ∨
    i = Reg.matrixP ∨ i = Reg.matrixQ ∨ i = Reg.matrixR ∨ i = Reg.productScratch))

/-- Compute every layout word through actual power/arithmetic instructions. All memory and
original argument registers survive; every intermediate fit follows from original n,p,k,scratch. -/
theorem exec_layout {w n p k scratch : ℕ} (x : Data 128)
    (hp : 0 < p) (hn : x.regs Reg.side = n) (hpr : x.regs Reg.modulus = p)
    (hk : x.regs Reg.depth = k) (hs : x.regs Reg.scratch = scratch)
    (h2 : x.regs Reg.two = 2) (hw : Fits w (layoutWordBound n p k scratch)) :
    ∃ y, ExecWithin w layout x y (4 * k + 20) ∧ LayoutRegisters n p k scratch y ∧
      y.mem = x.mem ∧ ∀ i, ¬LayoutLocal i → y.regs i = x.regs i := by
  have hsquare : 2 ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; rfl
  have harea : 4 ^ k ≤ 4 ^ k * p := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 ^ k) (Nat.succ_le_of_lt hp)
  have hwb : Fits w (scratch + 3 * (n * n) + 2 ^ k + 4 * (4 ^ k * p) + k + 2 * p + 16) := hw
  refine WP.exists_execWithin ?_
  unfold layout
  wram_exec [h2, hk]
  wram_call (Power.exec 2 k (by decide) _
    (by wram_simp) (by wram_simp) (hwb.of_le (by omega)))
    canonical (Fin.castLE_injective _) with s ⟨value, _, _, memory, _, _⟩
  have value' : s.regs 0 = 2 ^ k := value
  wram_exec [value', hn, hpr, hs, h2, hsquare]
  refine ⟨⟨by wram_simp [hn], by wram_simp [hpr], by wram_simp [hk], by wram_simp [hs],
      by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp; omega, by wram_simp, by wram_simp,
      by wram_simp; omega, by wram_simp; omega, by wram_simp; omega,
      by wram_simp; omega, by wram_simp; omega, by wram_simp; omega⟩,
    by wram_simp [memory], fun i hi => ?_⟩
  have hn' (j : Fin 128) (hj : LayoutLocal j) : i ≠ j := fun he => hi (he ▸ hj)
  have hval : 5 ≤ i.val := Nat.le_of_not_lt fun h => hi (Or.inl h)
  have hne2 : i ≠ Reg.low2 ∧ i ≠ Reg.low3 := by
    constructor <;> (intro h; subst i; contradiction)
  repeat rw [Data.set_regs_of_ne (hn' _ (by decide))]
  rw [Data.extend_castLE_regs_of_le _ _ i hval]
  wram_simp [hne2.1, hne2.2]

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
