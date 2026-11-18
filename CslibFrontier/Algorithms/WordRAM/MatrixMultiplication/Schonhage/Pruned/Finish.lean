/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Node
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Actual return after all ten child terms

## Main results

* `PrunedQuery.exec_node_finish`: read the completed frame and return through the real
  controller comparisons, preserving all memory.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- The stored term counter is read and compared with ten. The controller then either
terminates the root or selects the parent's accumulation phase, within 26 instructions. -/
theorem exec_node_finish {w L f a0 b0 d : ℕ} (x : Data registers)
    (hregs : KernelRegs L f a0 b0 x) (hd : x.regs level = d) (hdL : d ≤ L)
    (hm : x.regs mode = 1) (hterm : x.mem (f + 4 * d + 3) = 10)
    (hw : Fits w (8 * f + 64 * (L + 1) * 10 ^ L + 128)) :
    ∃ y, ExecWithin w step x y 26 ∧ KernelRegs L f a0 b0 y ∧ y.mem = x.mem ∧
      y.regs level = (if d = 0 then 0 else d - 1) ∧
      y.regs mode = (if d = 0 then 1 else 2) ∧
      y.regs active = (if d = 0 then 0 else x.regs active) ∧
      y.regs epoch = x.regs epoch := by
  have hL : L + 1 ≤ (L + 1) * 10 ^ L := by
    nlinarith only [Nat.one_le_pow L 10 (by decide)]
  obtain ⟨u, hu, humem, _, _, _, _, hut, _, _, _, _, _, hureg⟩ :=
    hregs.exec_loadFrame hd hdL hw
  have fixed (i : Fin registers) (hi : ¬LoadFrameLocal i) : u.regs i = x.regs i :=
    hureg i hi
  have hut' : u.regs term = 10 := hut.trans hterm
  have hu0 : u.regs nil = 0 := by regs_frame
  have hu1 : u.regs one = 1 := by regs_frame
  have hu10 : u.regs ten = 10 := by regs_frame
  have hum : u.regs mode = 1 := by regs_frame
  have hud : u.regs level = d := by regs_frame
  obtain ⟨y, hy, hymem, hyl, hym, hya, _⟩ := exec_pop u hu0 hu1
    (hw.of_le (by rw [hud]; nlinarith only [hL, hdL]))
  have hcall : ExecWithin w dispatch u y 6 := hy.branch_neg
    (by simp only [Cond.holds_lt, hut', hu10, lt_self_iff_false, not_false_eq_true])
  have hbranch : ExecWithin w
      (ram[ if mode = nil then [ ⟪enter⟫ ] else [
        if mode = one then [ ⟪dispatch⟫ ] else [ ⟪accumulate⟫ ] ] ]) u y 9 :=
    (hcall.branch_pos (by simp only [Cond.holds_eq, hum, hu1])).branch_neg
      (by simp only [Cond.holds_eq, hum, hu0]; decide)
  have he : ExecWithin w step x y 26 := hu.seq hbranch
  exact ⟨y, he, hregs.of_step he, hymem.trans humem,
    by simpa only [hud] using hyl, by simpa only [hud, hum] using hym,
    by simpa only [hud, fixed active (by decide)] using hya,
    by regs_frame⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
