/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.DyadicParameters.Exec
public import CslibFrontier.Computability.WordRAM.Width
import CslibFrontier.Computability.WordRAM.Admission
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Initialized halting native parameter preparation

Input is the single raw original dimension n. The actual header, logarithm, two powers,
parameter readback and regime flag all refer to one final state. The same code works at every
larger admitted physical width. All original memory is preserved.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.DyadicParameters

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Positive physical width admitting the original scalar and every computed parameter. -/
@[expose] def admissionWidth (n : ℕ) : ℕ := Nat.clog 2 (wordBudget n + 1)

/-- The original scalar is loaded by two actual native instructions before parameter setup. -/
@[expose] def entryProgram : Code .standard 16 :=
  .seq (ram[ Reg.divisor ← #1; Reg.side ← *Reg.divisor ]) program

/-- The initialized code remains fixed, including halt, and cannot read physical width. -/
theorem entryProgram_fixed : (entryProgram.program Reg.fast).length ≤ 128 ∧
    ¬(entryProgram.program Reg.fast).ReadsWidth := by decide +kernel

/-- The original-input width threshold is always positive. -/
theorem admissionWidth_pos (n : ℕ) : 0 < admissionWidth n := by
  apply Nat.clog_pos (by decide)
  unfold wordBudget
  omega

/-- Actual initialized execution at every admitted width. All original memory is preserved. -/
theorem exec_input {W n : ℕ} (hW : admissionWidth n ≤ W) :
    InputFits W [n] ∧
    ∃ y, ExecWithin W entryProgram (.init [n]) y (timeBound n + 2) ∧
      y.regs Reg.side = n ∧ y.regs Reg.blocks = ParameterChoice.blocks n ∧
      y.regs Reg.level = ParameterChoice.level n ∧
      y.regs Reg.window = ParameterChoice.window n ∧
      y.regs Reg.groups = ParameterChoice.groups n ∧
      y.regs Reg.tensorDepth = ParameterChoice.tensorDepth n ∧
      y.regs Reg.fast = (if 0 < ParameterChoice.blocks n then 1 else 0) ∧
      y.Bounded W ∧ y.mem = (Data.init [n] : Data 16).mem := by
  have hfit : Fits W (wordBudget n) :=
    fits_of_lt_clog_le (Nat.lt_succ_self _) hW
  have h1 : Fits W 1 := hfit.of_le (by unfold wordBudget; omega)
  have hn : Fits W n := hfit.of_le (by unfold wordBudget; omega)
  have hi : InputFits W [n] := ⟨by simpa using h1, by simpa using hn⟩
  have hmem1 : (Data.init [n] : Data 16).mem 1 = n := by simp [Data.init]
  have hfull : ∃ y, ExecWithin W entryProgram (.init [n]) y (timeBound n + 2) ∧
      Post n (.init [n]) y := by
    refine WP.exists_execWithin ?_
    wram_exec [entryProgram, hmem1]
    wram_call (exec _ (by wram_simp) hfit) with y hy
    exact ⟨by wram_simp; omega, by simpa only [Post, Data.set_mem] using hy⟩
  obtain ⟨y, full, hs, hb, hl, hd, hg, hL, hf, hm⟩ := hfull
  exact ⟨hi, y, full, hs, hb, hl, hd, hg, hL, hf, full.bounded (.init hi), hm⟩

/-- Same-state actual prefix and halt, with every output connected to the original dimension.
All instructions, including input loading and halt, have logarithmic total charge. -/
theorem runs_input {W n : ℕ} (hW : admissionWidth n ≤ W) :
    InputFits W [n] ∧
    ∃ y t, t + 1 ≤ 16 * Nat.log 2 n + 36 ∧
      Runs W (entryProgram.program Reg.fast) (State.init [n]) ⟨entryProgram.size, y⟩ t ∧
      Executes W (entryProgram.program Reg.fast) (State.init [n]) (y.regs Reg.fast) (t + 1) ∧
      y.regs Reg.side = n ∧ y.regs Reg.blocks = ParameterChoice.blocks n ∧
      y.regs Reg.level = ParameterChoice.level n ∧
      y.regs Reg.window = ParameterChoice.window n ∧
      y.regs Reg.groups = ParameterChoice.groups n ∧
      y.regs Reg.tensorDepth = ParameterChoice.tensorDepth n ∧
      y.regs Reg.fast = (if 0 < ParameterChoice.blocks n then 1 else 0) ∧
      y.Bounded W ∧ y.mem = (Data.init [n] : Data 16).mem := by
  obtain ⟨hi, y, ⟨t, ht, he⟩, hs, hb, hl, hd, hg, hL, hf, hy, hm⟩ := exec_input hW
  have budget := timeBound_le n
  refine ⟨hi, y, t, by omega, ?_, ?_, hs, hb, hl, hd, hg, hL, hf, hy, hm⟩
  · simpa only [State.init, Nat.zero_add] using he.runs (pc := 0)
      (p := entryProgram.program Reg.fast) (Program.Contains.self _).append_left
  · simpa only [State.init] using he.executes Reg.fast

/-- Every successful wider prefix has words and support controlled by original n rather than
that chosen physical width. -/
theorem bounded_reachable {W n : ℕ} (hW : admissionWidth n ≤ W)
    (s : State 16) (t : ℕ)
    (hr : Runs W (entryProgram.program Reg.fast) (State.init [n]) s t) :
    (∀ i, s.data.regs i < 2 ^ admissionWidth n) ∧
      (∀ a, s.data.mem a < 2 ^ admissionWidth n) ∧
      ∀ a, 2 ^ admissionWidth n ≤ a → s.data.mem a = 0 := by
  obtain ⟨hi, _, _, _, _, halt, _⟩ := runs_input (n := n) le_rfl
  exact hr.prefix_bounds_init entryProgram_fixed.2 hW hi halt le_rfl

end Cslib.Algorithms.WordRAM.ExactTriangle.DyadicParameters
