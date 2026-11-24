/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Properties
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Computed modulus and normalized source bank

The native setup executes `MemoryWindow.dynamicSetupBank` on the actual copied-word sum. It
normalizes only the fixed source register bank. Every memory word, original argument and selector
register is preserved; no clean window or precomputed modulus is supplied.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM

/-- The explicit physical margin covers the source width, scalar-size sum and power setup. -/
theorem setup_fits {W b n D g p total : ℕ}
    (hfit : Fits W (b + 4 * windowSize n D g p total + 1024)) :
    sourceWidth n D g p total ≤ W ∧
      n + D + g + p + total + 4 ≤ windowSize n D g p total ∧
      sourceWidth n D g p total < windowSize n D g p total ∧
      6166 ≤ windowSize n D g p total := by
  obtain ⟨-, hw, -, hsize, hwidth, hc⟩ :=
    MemoryWindow.dynamicWidth_fits (b := b) (widthCoeff := 6166) (S := n + D + g + p + total + 4)
      (by decide) (by omega) (hfit.of_le (Nat.le_add_right _ 1024))
  exact ⟨hw, hsize, hwidth, hc.le⟩

/-- Actual computed setup at every admitted physical width. Register normalization is charged
and source fits are postconditions of that code, not final caller assumptions. -/
theorem exec_setup {W : ℕ} (x : Data 640)
    (hfit : Fits W (x.regs Reg.base +
      4 * windowSize (x.regs Reg.n) (x.regs Reg.dimension) (x.regs Reg.groups)
        (x.regs Reg.prime) (x.regs Reg.total) + 1024)) :
    let n := x.regs Reg.n
    let D := x.regs Reg.dimension
    let g := x.regs Reg.groups
    let p := x.regs Reg.prime
    let total := x.regs Reg.total
    ∃ y, ExecWithin W setup x y
        (24669 * Nat.clog 2 (n + D + g + p + total + 4) + 439) ∧
      y.mem = x.mem ∧
      y.regs (sourceBank MemoryWindow.Reg.base) = x.regs Reg.base ∧
      y.regs (sourceBank MemoryWindow.Reg.modulus) = windowSize n D g p total ∧
      (∀ i : Fin 416, Fits (sourceWidth n D g p total) (y.regs (sourceReg i))) ∧
      ∀ j : Fin 640, j.val < 160 ∨ (600 ≤ j.val ∧ j.val < 608) → y.regs j = x.regs j := by
  let n := x.regs Reg.n
  let D := x.regs Reg.dimension
  let g := x.regs Reg.groups
  let p := x.regs Reg.prime
  let total := x.regs Reg.total
  let b := x.regs Reg.base
  let S := n + D + g + p + total + 4
  have fit : Fits W (b + 4 * windowSize n D g p total + 1024) := hfit
  obtain ⟨-, hS, -, -⟩ := setup_fits fit
  have hsize : Fits W S := fit.of_le (by omega)
  have hpow_inj : Function.Injective powerBank := fun i j h =>
    Fin.ext (by simpa only [powerBank] using Nat.add_left_cancel (congrArg Fin.val h))
  have hbase_ne (k : Fin 5) : powerBank k ≠ Reg.base := fun hk => by
    have := k.isLt; have hv := congrArg Fin.val hk; dsimp only [powerBank, Reg.base] at hv; omega
  obtain ⟨s, hs, sval, smem, sbase⟩ :
      ∃ s, ExecWithin W sizeArgument x s 7 ∧ s.regs (powerBank 0) = S ∧
        s.mem = x.mem ∧ s.regs Reg.base = b := by
    unfold sizeArgument
    wram_exec
    exact ⟨by wram_simp; rfl, rfl, by wram_simp; rfl⟩
  obtain ⟨y, hy, ymem, ymatch, ybound, -⟩ :=
    MemoryWindow.exec_dynamicSetupBank (r := 416) sourceBank_injective hpow_inj hbase_ne
      (by decide) (by decide : 1 ≤ 6166) (by dsimp only [S]; omega)
      s sbase sval (fit.of_le (Nat.le_add_right _ 1024))
  have he : ExecWithin W setup x y (24669 * Nat.clog 2 S + 439) :=
    (hs.seq hy).mono (by omega)
  refine ⟨y, he, ymem.trans smem, ymatch.base_eq, ymatch.modulus_eq, fun i => ybound.1 i,
    fun j hj => he.regs_eq (program_preserves j hj).2.1⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
