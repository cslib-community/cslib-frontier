/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.StackMemory
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Parameters
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Actual root-task initialization

The reusable query computes its stack base immediately after the retained compact
table, resets its accumulator and constants, and writes all five root fields before
the first native pop. Dirty stack memory and arbitrary old temporaries are supported.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Complete actual query setup with a real initialized root and exact memory frame. -/
theorem exec_setup {w L t Q AA BB D V K : ℕ} (x : Data registers) (η : OutStr L)
    (hL : x.regs BoxTable.Reg.levels = L) (ht : x.regs BoxTable.Reg.threshold = t)
    (hT : x.regs BoxTable.Reg.span = 10 ^ L) (hQ : x.regs Reg.query = Q)
    (hA : x.regs BoxTable.Reg.arrayA = AA) (hB : x.regs BoxTable.Reg.arrayB = BB)
    (hD : x.regs BoxTable.Reg.directory = D) (hV : x.regs BoxTable.Reg.values = V)
    (hK : x.regs BoxTable.Reg.count = K) (hfit : Fits w (V + K + 20)) :
    ∃ y, ExecWithin w setup x y 26 ∧ Parameters L t Q AA BB D V K (V + K) y ∧
      y.regs Reg.top = 1 ∧ y.regs Reg.answer = Signed.encode 0 ∧
      StackMemory η (V + K) [[]] y.mem ∧
      y.mem = writeTask (V + K) 0 0 0 0 0 1 x.mem := by
  refine WP.exists_execWithin ?_
  unfold setup setupScalars
  wram_call (BoxTable.exec_constants x (hfit.of_le (by omega)))
    with u ⟨u0, u1, u10, u9, _, um, uf⟩
  have uV : u.regs BoxTable.Reg.values = V := by regs_frame
  have uK : u.regs BoxTable.Reg.count = K := by regs_frame
  wram_exec [*]
  wram_call ((WordStack.push_exec (baseAddr := V + K) (cap := 1) (prefixTaskSpec η)
    Reg.stack Reg.top Reg.cursor Reg.five BoxTable.Reg.one pushFields [] [] _
    (by decide) (by decide) (by decide) (by decide)
    (by wram_simp) (by wram_simp; rfl) (by wram_simp) (by regs_frame)
    (fun i => by
      match i with
      | 0 | 2 | 3 | 4 => simp +decide [pushFields, usedFrom, starsFrom]
      | 1 => simp +decide [pushFields, prefixCode_nil])
    trivial (by decide) (hfit.of_le (by omega))).imp fun y h => ⟨h.1.within, h.2⟩)
    with y ⟨hyt, hstack, hym, _, hyf⟩
  refine ⟨by omega, by regs_frame, hyt, ?_, hstack, ?_⟩
  · rw [show Signed.encode 0 = 0 from rfl]
    regs_frame
  · dsimp only [RecordSpec.write, prefixTaskSpec] at hym
    simpa only [writeTask, List.length_nil, prefixCode_nil, usedFrom, starsFrom, pow_zero,
      Data.set_mem, um] using hym

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
