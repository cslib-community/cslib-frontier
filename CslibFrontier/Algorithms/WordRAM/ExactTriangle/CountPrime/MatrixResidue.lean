/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.Access

/-!
# Actual guarded CountPrime residue reads

Both native coordinate comparisons run before a real row-major source read. A padded cell
uses the runtime modulus as an out-of-range key, causing the subsequent actual coefficient
loop to write zeros. BC transposition is part of the real address computation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- Execute both real padding guards and the admitted source read, or select the padding
sentinel. Even invalid coordinates never cause an unchecked source-memory access. -/
theorem exec_matrixResidue {w : ℕ} (transpose : Bool) (x : Data 128)
    (hw : Fits w (x.regs Reg.residueSource + x.regs Reg.side * x.regs Reg.side +
      x.regs Reg.modulus)) :
    ∃ y, ExecWithin w (matrixResidue transpose) x y 8 ∧ y.mem = x.mem ∧
      y.regs Reg.residue =
        (if x.regs Reg.row < x.regs Reg.side ∧ x.regs Reg.column < x.regs Reg.side then
          x.mem (x.regs Reg.residueSource +
            if transpose then x.regs Reg.column * x.regs Reg.side + x.regs Reg.row
            else x.regs Reg.row * x.regs Reg.side + x.regs Reg.column)
        else x.regs Reg.modulus) ∧
      ∀ i, i ≠ Reg.address → i ≠ Reg.temporary → i ≠ Reg.residue → y.regs i = x.regs i := by
  by_cases h : x.regs Reg.row < x.regs Reg.side ∧ x.regs Reg.column < x.regs Reg.side
  · obtain ⟨y, hy, hm, hv, hregs⟩ := exec_readResidue transpose x h.1 h.2 (hw.of_le (by omega))
    refine ⟨y, (ExecWithin.branch_pos (by simpa only [Cond.holds_lt] using h.1)
      (ExecWithin.branch_pos (by simpa only [Cond.holds_lt] using h.2) hy)).mono (by omega),
      hm, by simpa only [h.1, h.2, and_self, ite_true] using hv, hregs⟩
  · let y := x.set Reg.residue (x.regs Reg.modulus)
    have hset : ExecWithin (B := .standard) w (ram[ Reg.residue ← Reg.modulus ]) x y 1 := .copy
    have he : ExecWithin w (matrixResidue transpose) x y 8 := by
      by_cases hr : x.regs Reg.row < x.regs Reg.side
      · exact (ExecWithin.branch_pos (by simpa only [Cond.holds_lt] using hr)
          (ExecWithin.branch_neg
            (by simpa only [Cond.holds_lt] using fun hc => h ⟨hr, hc⟩) hset)).mono (by omega)
      · exact (ExecWithin.branch_neg (by simpa only [Cond.holds_lt] using hr) hset).mono (by omega)
    exact ⟨y, he, rfl, by simp only [y, Data.set, Function.update_self, h, ite_false],
      fun _ _ _ hi => Function.update_of_ne hi _ _⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
