/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSAT.Tractable
-- Reuse the existing private NAE/nullary fixtures and their checked mathematical hypotheses.
import all CslibFrontierTests.CSPCyclicCompiler
-- Reuse the private pin language and its common-majority proof.
import all CslibFrontierTests.CSPTractability

/-!
# Native supplied-rotation tractability clients

The endpoint is imported ordinarily. The internal test import reuses the existing `naeSelf`,
`naeDelta`, `nullarySelf`, `nullaryDelta` and `pins_majority` proofs rather than repeating them.
Clients obtain native deciders from the two endpoints and prove opposite answers on actual raw
records, with valid certificates on both satisfiable and inconsistent constraints.
-/

open Cslib.Logic Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.BitString
open Cslib.Complexity Cslib.Complexity.CSP Turing.MultiTapeTM
open CSPCyclicCompilerTests
open CslibFrontierTests.CSPTractability

public section

namespace CSPRotationSATTractableTests

-- The additional branch provides a native decider separating an NAE constraint from the same
-- constraint with all three argument positions identified. Both supplied rotations are valid.
example : ∃ f : RotationInstance Unit → Bool,
    ComputableInPolyTime f (encRotationInstance encUnit) encBool ∧
      f ⟨naeInput, naeCert⟩ = true ∧ f ⟨naeRepeated, naeRepeatedCert⟩ = false := by
  obtain ⟨f, hf, hcorrect⟩ := RotationCSPSAT.mem_P_of_cyclicDifference
    encUnit naeArity naeSem (fun r _ => naeSelf r) (fun r _ => naeDelta r)
  refine ⟨f, hf, (hcorrect _).mp ?_, ?_⟩
  · exact ⟨by decide, by decide, fun v => decide (v = 0), by decide⟩
  · apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨_, _, σ, hσ⟩ := (hcorrect _).mpr h
    cases hv : σ 7 <;> simp [naeRepeated, CSP.eval, Constraint.eval, naeSem, hv] at hσ

-- The compiled branch handles an empty relation without requiring it to be a delta-matroid.
example : ∃ f : RotationInstance Bool → Bool,
    ComputableInPolyTime f (encRotationInstance encBool) encBool ∧
      f ⟨[⟨true, []⟩], ⟨[]⟩⟩ = true ∧ f ⟨[⟨false, []⟩], ⟨[]⟩⟩ = false := by
  obtain ⟨f, hf, hcorrect⟩ := RotationCSPSAT.mem_P_of_cyclicDifference
    encBool nullaryArity nullarySem (fun r _ => nullarySelf r) nullaryDelta
  refine ⟨f, hf, (hcorrect _).mp ?_, ?_⟩
  · exact ⟨by decide, by decide, fun _ => false, by decide⟩
  · apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨_, _, σ, hσ⟩ := (hcorrect _).mpr h
    simp [CSP.eval, Constraint.eval, nullarySem] at hσ

-- Ordinary majority tractability separates consistent and conflicting pins on a binary name.
-- Both successor tables pass the full check, so the negative answer is semantic.
example : ∃ f : RotationInstance Bool → Bool,
    ComputableInPolyTime f (encRotationInstance encBool) encBool ∧
      f ⟨[⟨true, [2 ^ 100]⟩], ⟨[0, 1]⟩⟩ = true ∧
        verifyRotationCertificate ([⟨true, [2 ^ 100]⟩, ⟨false, [2 ^ 100]⟩] : CSP Bool ℕ)
          ⟨[2, 1, 0, 3]⟩ = true ∧
        f ⟨[⟨true, [2 ^ 100]⟩, ⟨false, [2 ^ 100]⟩], ⟨[2, 1, 0, 3]⟩⟩ = false := by
  have h : HasSchaeferPolymorphism unary pin :=
    .inr (.inr (.inr (.inr (.inl pins_majority))))
  obtain ⟨f, hf, hcorrect⟩ := RotationCSPSAT.mem_P_of_hasSchaeferPolymorphism
    encBool unary pin h
  refine ⟨f, hf, (hcorrect _).mp ?_, by decide, ?_⟩
  · exact ⟨by decide, by decide, fun _ => true, by decide⟩
  · apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨_, _, σ, hσ⟩ := (hcorrect _).mpr h
    cases hv : σ (2 ^ 100) <;> simp [CSP.eval, Constraint.eval, pin] at hσ

end CSPRotationSATTractableTests
