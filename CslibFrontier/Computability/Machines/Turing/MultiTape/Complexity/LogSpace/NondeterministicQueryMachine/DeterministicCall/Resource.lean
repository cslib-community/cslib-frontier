/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.DeterministicCall
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Routines
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases

/-!
# Workspace for deterministic calls in a binary-choice query machine

The rejecting-choice adapter stores an optional deterministic state. Its transition keeps
the original optional read, and a true selector discards the state. The adapted query,
transition, and halt test use linear workspace when the deterministic operations do.
-/

public section

namespace Turing.QueryMachine

open MultiTapeTM MultiTapeTM.ComputableInSpace
open NondeterministicQueryMachine (encReadChoice)

/-- The rejecting-choice adapter preserves linear workspace for the query, transition and
halt test. The transition input carries the original optional read and the binary selector. -/
theorem withRejectingChoice_parts_inSpace {τ : Type} (M : QueryMachine τ)
    (encS : τ ↪ List Bool)
    (hq : ComputableInSpace M.query encS encNat fun s => (encS s).length)
    (hn : ComputableInSpace M.next (encStateRead encS) encS fun p => (encStateRead encS p).length)
    (hh : ComputableInSpace M.halted encS encBool fun s => (encS s).length) :
    let B := M.withRejectingChoice
    let enc := encOption encS
    let encNext := encPair enc encReadChoice
    ComputableInSpace B.query enc encNat (fun s => (enc s).length) ∧
    ComputableInSpace B.next encNext enc (fun p => (encNext p).length) ∧
    ComputableInSpace B.halted enc encBool (fun s => (enc s).length) := by
  intro B enc encNext
  refine ⟨optionElim 0 hq, ?_, optionElim true hh⟩
  let encAnswer := encOption encBool
  have hstate := fst enc encReadChoice
  have htail := snd enc encReadChoice
  have hnext := budget_optionSome
    (budget_comp_linear hn (budget_prod (snd encAnswer encS) (fst encAnswer encS)))
  have hmap := optionElimSnd (budget_const (encIn := encAnswer) (encB := enc) none (.refl _)) hnext
  have hcontinue := budget_comp_linear hmap (budget_prod (fst' htail) hstate)
  exact (budget_ite (snd' htail) (budget_const none (.refl _)) hcontinue).of_enc_eq
    fun ⟨state, _, choice⟩ => by cases state <;> cases choice <;> rfl

end Turing.QueryMachine
