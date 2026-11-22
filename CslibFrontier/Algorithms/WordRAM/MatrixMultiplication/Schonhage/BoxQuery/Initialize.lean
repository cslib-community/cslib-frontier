/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.StackMemory
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Parameters
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

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
  obtain ⟨u, hu, u0, u1, u10, u9, _, um, uf⟩ := BoxTable.exec_constants x
    (hfit.of_le ((by decide : 10 ≤ 20).trans (Nat.le_add_left _ _)))
  have uV : u.regs BoxTable.Reg.values = V := by regs_frame
  have uK : u.regs BoxTable.Reg.count = K := by regs_frame
  have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  have hfF : Fits w (V + K) := hfit.of_le (by omega)
  let v0 := ((u.set Reg.five 5).set Reg.answer 0).set Reg.stack (V + K)
  let v1 := ((v0.set Reg.top 0).set Reg.depth 0).set Reg.childCode 0
  let v := ((v1.set Reg.childUsed 0).set Reg.childStars 0).set Reg.childPower 1
  have hv : ExecWithin w setupScalars u v 9 := by
    ram_eval [setupScalars, v, v1, v0, uV, uK, hf0, hfF,
      Reg.five, Reg.answer, Reg.stack, Reg.top, Reg.depth, Reg.childCode,
      Reg.childUsed, Reg.childStars, Reg.childPower, BoxTable.Reg.values,
      BoxTable.Reg.count, Fin.mk.injEq]
  obtain ⟨y, hy_exec, hyt, hstack, hym, _, hyf⟩ :=
    WordStack.push_exec (baseAddr := V + K) (cap := 1) (prefixTaskSpec η)
      Reg.stack Reg.top Reg.cursor Reg.five BoxTable.Reg.one pushFields [] [] v
      (by decide) (by decide) (by decide) (by decide)
      (by simp +decide [v, v1, v0])
      (by simp +decide [v, v1])
      (by simp +decide [v, v1, v0])
      (by regs_frame)
      (fun i => by
        match i with
        | 0 | 2 | 3 | 4 => simp +decide [v, v1, pushFields, usedFrom, starsFrom]
        | 1 => simp +decide [v, v1, pushFields, prefixCode_nil])
      trivial (by decide) (hfit.of_le (by omega))
  have he : ExecWithin w setup x y 26 := hu.seq (hv.seq hy_exec.within)
  refine ⟨y, he, ?_, hyt, ?_, hstack, ?_⟩
  · constructor
    · regs_frame
    · regs_frame
    · regs_frame
    · regs_frame
    · regs_frame
    · regs_frame
    · regs_frame
    · regs_frame
    · regs_frame
    · rw [hyf _ (by decide)]
      simp +decide [v, v1, v0]
    · rw [hyf _ (by decide)]
      simp +decide [v, v1, v0]
    · regs_frame
    · regs_frame
    · regs_frame
    · regs_frame
  · rw [hyf _ (by decide)]
    simp +decide [v, v1, v0, Signed.encode]
  · dsimp only [RecordSpec.write, prefixTaskSpec] at hym
    simpa only [writeTask, List.length_nil, prefixCode_nil, usedFrom, starsFrom, pow_zero,
      v, v1, v0, Data.set_mem, um] using hym

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
