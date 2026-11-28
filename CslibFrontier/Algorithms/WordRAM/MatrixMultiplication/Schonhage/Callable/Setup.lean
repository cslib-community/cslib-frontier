/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Program
public import CslibFrontier.Computability.WordRAM.MemoryWindow.Dynamic
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Computed virtual width and register normalization

Setup reads the actual original headers and executes `MemoryWindow.dynamicSetup` using the
ceiling-logarithm and natural-power programs. No logarithm, modulus, bounded initial scratch or
source register certificate is supplied in the input.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct

open Cslib.WordRAM

/-- The explicit physical numerical margin covers setup and the smaller native source width. -/
theorem setup_fits {W b N Q : ℕ} (hfit : Fits W (b + 4 * windowSize N Q + 1024)) :
    sourceWidth N Q ≤ W ∧ N + Q + 3 ≤ windowSize N Q ∧
      sourceWidth N Q < windowSize N Q := by
  obtain ⟨-, hw, -, hS, hwidth, -⟩ :=
    MemoryWindow.dynamicWidth_fits (b := b) (widthCoeff := 128) (S := N + Q + 3)
      (by decide) (by omega) (hfit.of_le (Nat.le_add_right _ 1024))
  exact ⟨hw, hS, hwidth⟩

/-- Actual setup computes the modulus, normalizes the fixed source register bank and preserves
every caller memory word. Its charge is logarithmic in original dimensions and query count. -/
theorem exec_setup {W b N Q : ℕ} (x : Data 163) (hb : x.regs Reg.base = b)
    (hN : x.mem (b + 3) = N) (hQ : x.mem (b + 4) = Q)
    (hfit : Fits W (b + 4 * windowSize N Q + 1024)) :
    ∃ y, ExecWithin W setup x y (517 * Nat.clog 2 (N + Q + 3) + 184) ∧
      y.mem = x.mem ∧
      MemoryWindow.Matches (sourceWidth N Q) b
        (MemoryWindow.view (sourceWidth N Q) b y) y ∧
      (MemoryWindow.view (sourceWidth N Q) b y).Bounded (sourceWidth N Q) := by
  obtain ⟨-, hS, -⟩ := setup_fits hfit
  have hsize : Fits W (N + Q + 3) := hfit.of_le (by omega)
  obtain ⟨s, hs, ss, sm, sb⟩ :
      ∃ s, ExecWithin W readSize x s 9 ∧ s.regs (powerBank 0) = N + Q + 3 ∧
        s.mem = x.mem ∧ s.regs MemoryWindow.Reg.base = b := by
    wram_exec [readSize, hb, hN, hQ, hsize]
    refine ⟨rfl, rfl, ?_⟩
    wram_simp
    exact hb
  have hbase_ne (k : Fin 5) : powerBank k ≠ MemoryWindow.Reg.base := by
    have hk := k.isLt
    simp only [powerBank, MemoryWindow.Reg.base, ne_eq, Fin.ext_iff, Fin.val_castAdd]
    omega
  obtain ⟨y, hy, ym, ymatch, ybound⟩ :=
    MemoryWindow.exec_dynamicSetup (r := 160) (Fin.castAdd_injective 5 158) hbase_ne
      (by decide : 1 ≤ 128) (by omega : 2 ≤ N + Q + 3) s sb ss
      (hfit.of_le (Nat.le_add_right _ 1024))
  exact ⟨y, (hs.seq hy).mono (by omega), ym.trans sm, ymatch, ybound⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct
