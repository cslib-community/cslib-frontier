/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Charged strict-minimum updates

The selector's actual comparison code retains its first minimum, including ties. This local
execution rule does not assume that the input count was computed by a counter; that separate
composition obligation belongs to the full prime-selection controller.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM

/-- The ineligible branch executes one actual copy and leaves the complete state unchanged. -/
theorem exec_nop {w : ℕ} (x : Data 160) : ExecWithin w nop x x 1 := by
  have hself : x.set Reg.best (x.regs Reg.best) = x := by
    apply Data.ext
    · exact Function.update_eq_self _ _
    · rfl
  simpa only [nop, hself] using
    (ExecWithin.copy (w := w) (x := x) (d := Reg.best) (s := Reg.best))

/-- Update a first strict minimum in at most five actual instructions, without touching memory
or any register outside the three result registers. The `found` input is a Boolean word. -/
theorem exec_keep {w : ℕ} (x : Data 160) (hz : x.regs Reg.zero = 0)
    (ho : x.regs Reg.one = 1) (hf : x.regs Reg.found = 0 ∨ x.regs Reg.found = 1) :
    ∃ y, ExecWithin w keep x y 5 ∧
      y.regs Reg.best =
        (if x.regs Reg.found = 0 ∨ x.regs Reg.countResult < x.regs Reg.bestCount then
          x.regs Reg.cursor else x.regs Reg.best) ∧
      y.regs Reg.bestCount =
        (if x.regs Reg.found = 0 ∨ x.regs Reg.countResult < x.regs Reg.bestCount then
          x.regs Reg.countResult else x.regs Reg.bestCount) ∧
      y.regs Reg.found = 1 ∧ y.mem = x.mem ∧
      ∀ i, i ≠ Reg.best → i ≠ Reg.bestCount → i ≠ Reg.found → y.regs i = x.regs i := by
  unfold keep
  wram_exec [hz, ho]
  · exact ⟨by wram_simp [hc, true_or], by wram_simp [hc, true_or], by wram_simp, rfl,
      fun i hb hc' hf' => by wram_simp [hb, hc', hf']⟩
  · rename_i h0
    exact ⟨by wram_simp [h0, hc, false_or], by wram_simp [h0, hc, false_or],
      by wram_simp [hf.resolve_left h0], rfl,
      fun i hb hc' _ => by wram_simp [hb, hc']⟩
  · rename_i h0
    exact ⟨by wram_simp [h0, hc, false_or], by wram_simp [h0, hc, false_or],
      by wram_simp [hf.resolve_left h0], rfl, fun i _ _ _ => by wram_simp⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
