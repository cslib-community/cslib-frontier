/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Strassen.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Charged quadrant-pointer computation

The controller's matrix-pointer fields are in the high bank, and the computed helper
arguments are in the low bank. The static quadrant number selects finite code; its runtime
offset multiplication and address addition are ordinary charged instructions.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

/-- Compute one of the four actual contiguous-quadrant pointers, preserving memory and
every register except the chosen low argument and the offset temporary. -/
theorem exec_quadrant {w t : ℕ} (base dst : Fin 64) (x : Data 64)
    (hbt : base ≠ Reg.temporary) (ht : t < 4)
    (hw : Fits w (x.regs base + 4 * x.regs Reg.quarter + 4)) :
    ∃ y, ExecWithin w (quadrant base dst t) x y 3 ∧ y.mem = x.mem ∧
      y.regs dst = x.regs base + t * x.regs Reg.quarter ∧
      ∀ i, i ≠ dst → i ≠ Reg.temporary → y.regs i = x.regs i := by
  have hmul := Nat.mul_le_mul_right (x.regs Reg.quarter) (show t ≤ 3 by omega)
  have hprod : Fits w (t * x.regs Reg.quarter) := by fits [hmul]
  have hsum : Fits w (x.regs base + t * x.regs Reg.quarter) := by fits [hmul]
  apply WP.exists_execWithin
  unfold quadrant
  by_cases ht0 : t = 0
  · simp only [ht0, ↓reduceIte]
    wram_exec
    wram_simp [ht0, Nat.zero_mul]
    exact fun i hi _ => Data.set_regs_of_ne hi _
  · simp only [ht0, ↓reduceIte]
    wram_exec
    wram_simp
    exact fun i hi htemp => by wram_simp

end Cslib.Algorithms.WordRAM.Strassen
