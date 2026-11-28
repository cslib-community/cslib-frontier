/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Program
import CslibFrontier.Computability.WordRAM.Record

/-!
# Native saving and restoration of original ExactTriangle arguments

These internal execution rules charge every copy and keep the original memory unchanged.
Old registers are arbitrary; the parameter and solver stages receive their arguments from
real copies, not from a precomputed layout or an assumed caller-state relation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM

private theorem save_preserves_low : ∀ j : Fin 640, j.val < 143 → save.Preserves j := by
  decide +kernel

private theorem restore_preserves_high : ∀ j : Fin 640, 7 ≤ j.val → restore.Preserves j := by
  decide +kernel

/-- Eight actual instructions save the original protocol and seed the real parameter input. -/
theorem exec_save {W : ℕ} (x : Data 640) (h0 : Fits W 0) :
    ∃ y, ExecWithin W save x y 8 ∧ y.mem = x.mem ∧
      y.regs Reg.savedBound = x.regs Reg.bound ∧
      y.regs CallableFixedPrime.Reg.n = x.regs Reg.side ∧
      y.regs CallableFixedPrime.Reg.ab = x.regs Reg.ab ∧
      y.regs CallableFixedPrime.Reg.bc = x.regs Reg.bc ∧
      y.regs CallableFixedPrime.Reg.ac = x.regs Reg.ac ∧
      y.regs CallableFixedPrime.Reg.base = x.regs Reg.free ∧
      y.regs (parameterBank DyadicParameters.Reg.side) = x.regs Reg.side ∧
      y.regs CallableFixedPrime.Reg.prime = 0 ∧
      ∀ j : Fin 640, j.val < 143 → y.regs j = x.regs j := by
  let _ := h0
  refine WP.exists_execWithin_preserves (fun j hj => save_preserves_low j hj) ?_
  wram_exec [save]
  intro hpres
  exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp, by wram_simp, by wram_simp, by wram_simp, hpres⟩

/-- Seven actual copies return the raw verdict and restore the six original host arguments. -/
theorem exec_restore {W : ℕ} (x : Data 640) :
    ∃ y, ExecWithin W restore x y 7 ∧ y.mem = x.mem ∧
      y.regs Reg.side = x.regs CallableFixedPrime.Reg.n ∧
      y.regs Reg.bound = x.regs Reg.savedBound ∧
      y.regs Reg.ab = x.regs CallableFixedPrime.Reg.ab ∧
      y.regs Reg.bc = x.regs CallableFixedPrime.Reg.bc ∧
      y.regs Reg.ac = x.regs CallableFixedPrime.Reg.ac ∧
      y.regs Reg.free = x.regs CallableFixedPrime.Reg.base ∧
      y.regs Reg.result = x.regs CallableFixedPrime.Reg.found ∧
      ∀ j : Fin 640, 7 ≤ j.val → y.regs j = x.regs j := by
  refine WP.exists_execWithin_preserves (fun j hj => restore_preserves_high j hj) ?_
  wram_exec [restore]
  intro hpres
  exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp, by wram_simp, by wram_simp, hpres⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
