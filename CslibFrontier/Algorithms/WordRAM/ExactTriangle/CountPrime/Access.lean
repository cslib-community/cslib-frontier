/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.Spread
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Tactic.StrideOmega

/-!
# Charged native modular-counter matrix accesses

The Morton block reads two actual words from the previously computed spread table. The
residue block computes the actual row-major address, transposing BC when requested. These
are internal stage contracts; the composed counter supplies the table through its proved
construction and the residues through the existing native signed-remainder loop.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- Six actual instructions read the table and compute the Morton index. The input row and
column and the original table pointer are preserved. -/
theorem exec_morton {w k : ℕ} (x : Data 128) (h2 : x.regs Reg.two = 2)
    (hr : x.regs Reg.row < 2 ^ k) (hc : x.regs Reg.column < 2 ^ k)
    (htable : ∀ j < 2 ^ k, x.mem (x.regs Reg.spread + j) = Nat.Morton.spread j)
    (hw : Fits w (x.regs Reg.spread + 4 ^ k + 2 ^ k)) :
    ∃ y, ExecWithin w morton x y 6 ∧ y.mem = x.mem ∧
      y.regs Reg.position = Nat.Morton.index (x.regs Reg.row) (x.regs Reg.column) ∧
      ∀ i, i ≠ Reg.address → i ≠ Reg.rowSpread → i ≠ Reg.columnSpread →
        i ≠ Reg.position → y.regs i = x.regs i := by
  have hreadr := htable _ hr
  have hreadc := htable _ hc
  have hi := Nat.Morton.index_lt hr hc
  unfold Nat.Morton.index at hi
  unfold morton
  wram_exec [h2, hreadr, hreadc]
  exact ⟨rfl, by wram_simp [Nat.Morton.index, Nat.mul_comm],
    fun i ha hr hc hp => by wram_simp [ha, hr, hc, hp]⟩

/-- Four actual instructions perform an admitted original-matrix residue read. The
transpose is fixed code selection, while both coordinates and the pointer are runtime data. -/
theorem exec_readResidue {w : ℕ} (transpose : Bool) (x : Data 128)
    (hr : x.regs Reg.row < x.regs Reg.side) (hc : x.regs Reg.column < x.regs Reg.side)
    (hw : Fits w (x.regs Reg.residueSource + x.regs Reg.side * x.regs Reg.side)) :
    ∃ y, ExecWithin w (readResidue transpose) x y 4 ∧ y.mem = x.mem ∧
      y.regs Reg.residue = x.mem (x.regs Reg.residueSource +
        if transpose then x.regs Reg.column * x.regs Reg.side + x.regs Reg.row
        else x.regs Reg.row * x.regs Reg.side + x.regs Reg.column) ∧
      ∀ i, i ≠ Reg.address → i ≠ Reg.temporary → i ≠ Reg.residue → y.regs i = x.regs i := by
  cases transpose <;>
    (simp only [readResidue, Bool.false_eq_true, ↓reduceIte]
     wram_exec
     · exact ⟨rfl, by wram_simp, fun i ha ht hr => by wram_simp [ha, ht, hr]⟩
     all_goals stride_omega)

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
