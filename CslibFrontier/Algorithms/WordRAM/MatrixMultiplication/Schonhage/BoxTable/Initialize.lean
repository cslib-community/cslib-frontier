/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.InputLayout
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Native box-table input adaptation

The actual header loads, reused power code and pointer arithmetic locate the original
two leaf arrays and the first writable word. No array or workspace is copied or cleared.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM

/-- Actual scalar header loads with unchanged memory. -/
theorem exec_inputHeaders {w L m t : ℕ} (x : Data registers)
    (hL : x.mem 1 = L) (hm : x.mem 2 = m) (ht : x.mem 3 = t)
    (hfit : Fits w 3) :
    ∃ y, ExecWithin w inputHeaders x y 6 ∧ y.regs Reg.levels = L ∧
      y.regs Reg.inner = m ∧ y.regs Reg.threshold = t ∧ y.mem = x.mem := by
  unfold inputHeaders
  wram_exec [hL, hm, ht]
  wram_simp

/-- Complete native initialization from the three actual input header words. -/
theorem exec_loadInput {w L m t : ℕ} (x : Data registers)
    (hL : x.mem 1 = L) (hm : x.mem 2 = m) (ht : x.mem 3 = t)
    (hfit : Fits w (2 * 10 ^ L + L + 12)) :
    ∃ y, ExecWithin w loadInput x y (4 * L + 19) ∧
      y.regs Reg.levels = L ∧ y.regs Reg.inner = m ∧ y.regs Reg.threshold = t ∧
      y.regs Reg.arrayA = 4 ∧ y.regs Reg.arrayB = 4 + 10 ^ L ∧
      y.regs Reg.directory = directoryBase L ∧ y.mem = x.mem := by
  refine WP.exists_execWithin ?_
  unfold loadInput inputPointers
  wram_call (exec_inputHeaders x hL hm ht (hfit.of_le (by omega)))
    with a ⟨aL, am, ath, haμ⟩
  wram_call (exec_constants a (hfit.of_le (by omega)))
    with b ⟨_, _, b10, _, _, hbμ, bf⟩
  wram_call (exec_span b (by regs_frame) b10 (hfit.of_le (by omega)))
    with c ⟨cT, _, hcμ, cf⟩
  wram_exec [*]
  refine ⟨by regs_frame, by regs_frame, by regs_frame,
    by wram_simp, by wram_simp, ?_, by wram_simp; exact hcμ.trans (hbμ.trans haμ)⟩
  wram_simp
  unfold directoryBase
  omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
