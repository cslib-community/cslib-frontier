/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Classes.QPH
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

set_option linter.privateModule false

namespace CslibFrontierTests.QuantumPolynomialHierarchy

open Cslib.Complexity Cslib.Quantum Turing.MultiTapeTM

private noncomputable def basisProof (b : Bool) : MixedProof 1 :=
  ⟨pureState (ket (fun _ => b)), isDensityMatrix_pureState (norm_ket _)⟩

private theorem basisProof_ne : basisProof false ≠ basisProof true := by
  intro h
  have hh := congrArg (fun s : MixedProof 1 => s.val (fun _ => false) (fun _ => false)) h
  have hbits : (fun _ : Fin 1 => false) ≠ fun _ => true :=
    fun h => Bool.false_ne_true (congrFun h 0)
  simp [basisProof, ket_apply, hbits] at hh

/-- In the universal-first prefix, the second proof can depend on the first one. -/
example : quantifiedProofs (MixedProof 1) 2 false (fun ρ => ρ 0 = ρ 1) := by
  change ∀ ρ : MixedProof 1, ∃ σ : MixedProof 1, ρ = σ
  exact fun ρ => ⟨ρ, rfl⟩

/-- Reversing the prefix fails because there are distinct one-qubit states. -/
example : ¬ quantifiedProofs (MixedProof 1) 2 true (fun ρ => ρ 0 = ρ 1) := by
  change ¬ (∃ ρ : MixedProof 1, ∀ σ : MixedProof 1, ρ = σ)
  rintro ⟨ρ, hρ⟩
  exact basisProof_ne ((hρ _).symm.trans (hρ _))

private abbrev verifier : UniformQuantifiedVerifier 2 where
  width n := n + 2
  gates _ := []
  computableInPolyTime_width := ComputableInPolyTime.unary_succ.comp .unary_succ
  computableInPolyTime_gates := .const []
  le_width _ := Nat.le_add_right _ _
  width_pos _ := by omega
  wellFormed := by simp
  proofWidth _ := 1
  computableInPolyTime_proofWidth := .const 1
  add_proofWidth_le _ := le_rfl

/-- The verifier can initialize its two positions with different proof states. -/
example : IsDensityMatrix (verifier.inputDensity [] ![basisProof true, basisProof false]) :=
  verifier.isDensityMatrix_inputDensity _ _

end CslibFrontierTests.QuantumPolynomialHierarchy
