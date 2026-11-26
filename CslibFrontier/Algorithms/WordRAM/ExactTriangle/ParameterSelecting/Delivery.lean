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
# Charged selector and exhaustive-solver argument delivery

These internal interfaces describe the actual eight-copy selector delivery and six-copy slow
protocol. They neither compute an uncharged layout nor assume that a callee accepts relocated
registers: the entire actual callee bank is transported by the existing execution semantics.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM

private theorem selectArguments_preserves : ∀ j : Fin 640,
    143 ≤ j.val → j ≠ CallableFixedPrime.Reg.dimension → j ≠ CallableFixedPrime.Reg.groups →
      selectArguments.Preserves j := by decide +kernel

private theorem slowArguments_preserves : ∀ j : Fin 640,
    6 ≤ j.val → slowArguments.Preserves j := by decide +kernel

/-- Deliver computed D,g and the original source pointers to the actual selector in eight copies. -/
theorem exec_selectArguments {W : ℕ} (x : Data 640) :
    ∃ y, ExecWithin W selectArguments x y 8 ∧ y.mem = x.mem ∧
      y.regs CallableFixedPrime.Reg.dimension =
        x.regs (parameterBank DyadicParameters.Reg.window) ∧
      y.regs CallableFixedPrime.Reg.groups = x.regs (parameterBank DyadicParameters.Reg.groups) ∧
      y.regs (selectorBank PrimeSelection.Reg.side) = x.regs CallableFixedPrime.Reg.n ∧
      y.regs (selectorBank PrimeSelection.Reg.window) =
        x.regs (parameterBank DyadicParameters.Reg.window) ∧
      y.regs (selectorBank PrimeSelection.Reg.inputAB) = x.regs CallableFixedPrime.Reg.ab ∧
      y.regs (selectorBank PrimeSelection.Reg.inputBC) = x.regs CallableFixedPrime.Reg.bc ∧
      y.regs (selectorBank PrimeSelection.Reg.inputAC) = x.regs CallableFixedPrime.Reg.ac ∧
      y.regs (selectorBank PrimeSelection.Reg.scratch) = x.regs CallableFixedPrime.Reg.base ∧
      ∀ j : Fin 640, 143 ≤ j.val → j ≠ CallableFixedPrime.Reg.dimension →
        j ≠ CallableFixedPrime.Reg.groups → y.regs j = x.regs j := by
  refine WP.exists_execWithin_preserves
    (P := fun j : Fin 640 =>
      143 ≤ j.val ∧ j ≠ CallableFixedPrime.Reg.dimension ∧ j ≠ CallableFixedPrime.Reg.groups)
    (fun j hj => selectArguments_preserves j hj.1 hj.2.1 hj.2.2) ?_
  unfold selectArguments
  wram_exec
  intro hpres
  exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    fun j hj hd hg => hpres j ⟨hj, hd, hg⟩⟩

/-- Deliver the unchanged original six-word host protocol before the real exhaustive call. -/
theorem exec_slowArguments {W : ℕ} (x : Data 640) :
    ∃ y, ExecWithin W slowArguments x y 6 ∧ y.mem = x.mem ∧
      y.regs Reg.side = x.regs CallableFixedPrime.Reg.n ∧
      y.regs Reg.bound = x.regs Reg.savedBound ∧
      y.regs Reg.ab = x.regs CallableFixedPrime.Reg.ab ∧
      y.regs Reg.bc = x.regs CallableFixedPrime.Reg.bc ∧
      y.regs Reg.ac = x.regs CallableFixedPrime.Reg.ac ∧
      y.regs Reg.free = x.regs CallableFixedPrime.Reg.base ∧
      ∀ j : Fin 640, 6 ≤ j.val → y.regs j = x.regs j := by
  refine WP.exists_execWithin_preserves (fun j hj => slowArguments_preserves j hj) ?_
  unfold slowArguments
  wram_exec
  intro hpres
  exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp, by wram_simp, by wram_simp, hpres⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
