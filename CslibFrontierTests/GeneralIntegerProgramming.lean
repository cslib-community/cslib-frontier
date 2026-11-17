/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.GeneralIntegerProgramming.Hardness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! Ordinary-import clients for integer solutions and integer feasibility. -/

set_option linter.privateModule false

open Cslib.Complexity Matrix Mathlib.Tactic.Matrix

-- Negative integer coordinates are admitted. Neither zero nor a Boolean assignment works.
example : IntegerProgram.check (⟨1, [⟨[1], -2⟩, ⟨[-1], 3⟩]⟩, [-2]) = true := by
  norm_num [IntegerProgram.check, ListMatrix.dotProduct_eq, _root_.dotProduct, ofList_apply]
example : IntegerProgram.check (⟨1, [⟨[1], -2⟩, ⟨[-1], 3⟩]⟩, [0]) = false := by
  norm_num [IntegerProgram.check, ListMatrix.dotProduct_eq, _root_.dotProduct, ofList_apply]
example : (⟨1, [⟨[1], -2⟩, ⟨[-1], 3⟩]⟩ : IntegerProgram) ∈ IntegerProgram.Feasible :=
  IntegerProgram.mem_of_check (w := [-2]) (by
    norm_num [IntegerProgram.check, ListMatrix.dotProduct_eq, _root_.dotProduct, ofList_apply])

-- The rationally feasible equation `2x = 1` has no integer solution.
example : (⟨1, [⟨[2], 1⟩, ⟨[-2], -1⟩]⟩ : IntegerProgram) ∉ IntegerProgram.Feasible := by
  rintro ⟨x, hx⟩
  have h1 := hx ⟨[2], 1⟩ (by simp)
  have h2 := hx ⟨[-2], -1⟩ (by simp)
  norm_num [Fin.sum_univ_one] at h1 h2
  omega

-- Zero-variable systems still check their constant inequalities.
example : IntegerProgram.check (⟨0, [⟨[], 0⟩]⟩, []) = true := by
  norm_num [IntegerProgram.check, ListMatrix.dotProduct_eq, _root_.dotProduct, ofList_apply]
example : IntegerProgram.check (⟨0, [⟨[], -1⟩]⟩, []) = false := by
  norm_num [IntegerProgram.check, ListMatrix.dotProduct_eq, _root_.dotProduct, ofList_apply]

-- A dependent integer equality system receives a bounded INTEGER solution to the SAME rhs.
example : ∃ x : Fin 2 → ℤ, 0 ≤ x ∧
    (!![2, -3] : Matrix (Fin 1) (Fin 2) ℤ) *ᵥ x = ![1] ∧
    ∀ j, x j ≤ (nonnegIntSolutionBound 1 2 3 : ℕ) := by
  apply exists_nonneg_int_mulVec_eq_le (x₀ := ![2, 1])
  · intro i j
    fin_cases i
    fin_cases j <;> norm_num
  · intro i
    fin_cases i
    norm_num
  · intro j
    fin_cases j <;> norm_num
  · ext i
    fin_cases i
    norm_num [mulVec, dotProduct, Fin.sum_univ_two]

-- The reduction excludes an impossible Boolean equation, although x = 2 is an integer solution.
example : IntegerProgram.ofZeroOne [⟨[1], 2⟩] ∉ IntegerProgram.Feasible := by
  rw [IntegerProgram.ofZeroOne_mem_iff]
  rintro ⟨x, hx⟩
  have h := hx ⟨[1], 2⟩ (by simp)
  have hbound := Bool.toNat_le (x 0)
  simp at h
  omega
