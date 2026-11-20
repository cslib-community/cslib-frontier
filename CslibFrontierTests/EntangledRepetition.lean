/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.AveragedAnswerStates
import CslibFrontier.Computability.PCP.TwoProverGame.EntangledRepetition
import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson

/-! # Entangled repetition of CHSH -/

set_option linter.privateModule false

open Cslib.PCP.TwoProverGame
open scoped Real

example {n : ℕ} (hn : 0 < n) : (chsh.pow n).quantumValue ≤ Real.cos (π / 8) ^ 2 := by
  rw [← quantumValue_chsh]
  exact chsh.quantumValue_pow_le_of_pos hn

open Cslib.PCP (QuantumStrategy)
open Cslib.Probability.PMF (coin)
open scoped unitInterval

private noncomputable def echoStrategy :
    QuantumStrategy Bool Bool (Fin 2 → Bool) (Fin 2 → Bool) (Fin 1) (Fin 1) :=
  QuantumStrategy.ofDeterministic (fun x _ => x) (fun y _ => y)

/-- The branch with both checked answers true has weight `1 - η` when the coin
replaces Alice's true input by false and Bob's input is always true. -/
example (η : I) :
    ‖echoStrategy.averagedCheckedVector {0}
      ((coin η).bind fun erase => PMF.pure (!erase)) (PMF.pure true)
      (fun _ => true) (fun _ => true)‖ ^ 2 = 1 - (η : ℝ) := by
  classical
  have h (x : Bool) :
      ‖echoStrategy.averagedCheckedVector {0} (PMF.pure x) (PMF.pure true)
        (fun _ => true) (fun _ => true)‖ ^ 2 = if x then 1 else 0 := by
    rw [QuantumStrategy.norm_averagedCheckedVector_sq]
    simp only [PMF.pure_bind, echoStrategy, QuantumStrategy.checkedAnswers,
      QuantumStrategy.answers_ofDeterministic, PMF.pure_map, Prod.map_apply, PMF.pure_apply]
    cases x
    · have hn : (fun _ : ({0} : Finset (Fin 2)) => true) ≠ fun _ => false :=
        fun e => Bool.noConfusion (congrFun e ⟨0, by simp⟩)
      simp [Prod.mk.injEq, hn]
    · simp
  have hmix : (fun erase : Bool => PMF.pure (!erase)) =
      (fun erase => if erase then PMF.pure false else PMF.pure true) := by
    funext erase
    cases erase <;> rfl
  rw [hmix, QuantumStrategy.norm_averagedCheckedVector_sq_coin, h, h]
  simp

/-- Independent play gives the lower end of the interval for repeated CHSH. -/
example (n : ℕ) : (Real.cos (π / 8) ^ 2) ^ n ≤ (chsh.pow n).quantumValue := by
  rw [← quantumValue_chsh]
  exact chsh.pow_quantumValue_le_quantumValue_pow n
