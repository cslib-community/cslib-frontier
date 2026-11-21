/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.Symmetrize

/-! # Symmetrization with different local dimensions and opposite answers -/

set_option linter.privateModule false

open Cslib.PCP Cslib.Quantum Matrix
open scoped Kronecker

private noncomputable def oppositeAnswers : QuantumStrategy Unit Unit Bool Bool (Fin 1) Bool where
  state := EuclideanSpace.single (0, false) 1
  norm_state := by simp
  alice _ := POVM.const false
  bob _ := POVM.const true

/-- The two disjoint role branches have equal weight even when the original
players have different local dimensions and give different answers. -/
example :
    oppositeAnswers.symmetrize.prob () () false true = 1 / 2 ∧
    oppositeAnswers.symmetrize.prob () () true false = 1 / 2 ∧
    oppositeAnswers.symmetrize.prob () () false false = 0 := by
  have h₁ : oppositeAnswers.prob () () false true = 1 := by
    rw [QuantumStrategy.prob_eq]
    simp [oppositeAnswers, POVM.const]
  have h₂ : oppositeAnswers.prob () () true false = 0 := by
    rw [QuantumStrategy.prob_eq]
    simp [oppositeAnswers, POVM.const]
  have h₃ : oppositeAnswers.prob () () false false = 0 := by
    rw [QuantumStrategy.prob_eq]
    simp [oppositeAnswers, POVM.const]
  simp only [QuantumStrategy.symmetrize_prob, h₁, h₂, h₃, zero_add, add_zero, zero_div,
    and_self]
