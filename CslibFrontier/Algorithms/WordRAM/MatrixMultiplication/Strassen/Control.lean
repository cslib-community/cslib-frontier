/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Strassen.Frame
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Native Strassen clearing and stack returns

These internal execution lemmas reuse the existing `zeroFill_exec` implementation. The
clearing footprint is one current output matrix, never a whole caller catalogue or window.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

/-- Clear the actual current output, deriving its end pointer and charging every store.
Only the two cursor registers change. -/
theorem exec_clear {w : ℕ} (x : Data 64) (h0 : x.regs Reg.zero = 0)
    (h1 : x.regs Reg.one = 1) (hw : Fits w (x.regs Reg.output + x.regs Reg.size)) :
    ∃ y, ExecWithin w clear x y (4 * x.regs Reg.size + 4) ∧
      y.mem = WordRAM.clear x.mem (x.regs Reg.output) (x.regs Reg.size) ∧
      ∀ i, i ≠ Reg.address → i ≠ Reg.index → y.regs i = x.regs i := by
  let z := (x.set Reg.address (x.regs Reg.output)).set Reg.index
    (x.regs Reg.output + x.regs Reg.size)
  have hsetup : ExecWithin w
      (ram[ Reg.address ← Reg.output; Reg.index ← Reg.output + Reg.size ]) x z 2 := by
    wram_exec
  have he := zeroFill_exec (x := z) (w := w)
    (cur := Reg.address) (stop := Reg.index) (zero := Reg.zero) (one := Reg.one)
    (by decide) (by decide) (by decide)
    (by wram_simp [z]; exact h0)
    (by wram_simp [z]; exact h1)
    (by wram_simp [z]; omega)
    (by wram_simp [z]; exact hw)
  have hcount : z.regs Reg.index - z.regs Reg.address = x.regs Reg.size := by
    wram_simp [z]
  let y : Data 64 := ⟨Function.update z.regs Reg.address (z.regs Reg.index),
    WordRAM.clear z.mem (z.regs Reg.address) (z.regs Reg.index - z.regs Reg.address)⟩
  refine ⟨y, (hsetup.seq he.within).mono (by rw [hcount]; omega), ?_, fun i ha hi => ?_⟩
  · dsimp only [y]; rw [hcount]; rfl
  · simp only [y, z, Data.set, Function.update_of_ne ha, Function.update_of_ne hi]

/-- Return to the parent or finish the root in three instructions.
The subtraction is charged, and its fit follows from the actual frame pointer. -/
theorem exec_pop {w : ℕ} (x : Data 64) (h7 : x.regs Reg.frameWidth = 7)
    (hw : Fits w (x.regs Reg.frame)) :
    ∃ y, ExecWithin w pop x y 3 ∧ y.mem = x.mem ∧
      y.regs Reg.frame =
        (if x.regs Reg.frames < x.regs Reg.frame then x.regs Reg.frame - 7
          else x.regs Reg.frame) ∧
      y.regs Reg.active =
        (if x.regs Reg.frames < x.regs Reg.frame then x.regs Reg.active else 0) ∧
      ∀ i, i ≠ Reg.frame → i ≠ Reg.active → y.regs i = x.regs i := by
  apply WP.exists_execWithin
  wram_exec [pop, h7]
  all_goals
    wram_simp [hc]
    exact fun i hf ha => by wram_simp

end Cslib.Algorithms.WordRAM.Strassen
