/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of native binary-polynomial trial components)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BinaryIrreducible

/-! Ordinary-import clients for binary polynomial trial tests and their native iteration. -/

set_option linter.privateModule false

open Cslib Turing.BinaryField Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

-- X² + X + 1 is irreducible; X² + 1 has divisor X + 1.
example : isIrreducibleCode 7 = true := by decide
example : isIrreducibleCode 5 = false := by decide
example : divisorPasses 5 3 = false := by decide
example : divisorPasses 7 3 = true := by decide

-- Zero/one divisors pass the degree guard; candidate zero/one still fails irreducibility.
example : divisorPasses 0 0 = true := by decide
example : isIrreducibleCode 0 = false := by decide
example : isIrreducibleCode 1 = false := by decide

-- The live cursor advances even when the accumulated answer has become false.
example : (trialRun ⟨5, 2, 2⟩).good = false ∧ (trialRun ⟨5, 2, 2⟩).divisor = 4 := by decide
example : (trialRun ⟨7, 2, 2⟩).good = true := by decide
example : (trialRun ⟨5, 3, 0⟩).good = true ∧ (trialRun ⟨5, 3, 0⟩).divisor = 3 := by decide

-- Compose binary successor arithmetic with the actual native irreducibility test.
example : ComputableInSpace (fun n : ℕ => isIrreducibleCode (n + 1))
    encNat encBool (fun n => (encNat n).length) := by
  have hid : ComputableInSpace (fun n : ℕ => n) encNat encNat
      (fun n => (encNat n).length) := of_inO (ComputableInO.of_eq fun _ => rfl)
  exact budget_comp_linear isIrreducibleCode_inSpace (budget_natSucc hid)

-- The returned native register record can be consumed through its named accumulator field.
example : ComputableInSpace (fun p : TrialInput => (trialRun p).good)
    encTrialInput encBool (fun p => (encTrialInput p).length) :=
  encTrialState_good_budget trialRun_inSpace
