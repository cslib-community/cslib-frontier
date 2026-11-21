/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop.Resource
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Retain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp

/-!
# Retained context at source-round entry

A source scan re-enters a single round at its current radius and tally. Callback entries can
also use immutable loop data, for example the seed and field context of a weighted graph.
The round reuses the scalar controller while retaining that data on every branch.

## Main definitions

* `Turing.DoubleCounting.SourceRoundLoop.retainedRoundEntry`: the entry from loop registers.
* `Turing.DoubleCounting.SourceRoundLoop.retainedRound`: the re-entrant round machine.

## Main results

* `Turing.DoubleCounting.SourceRoundLoop.retainedRoundEntry_inSpace`: linear workspace for entry.
* `Turing.DoubleCounting.SourceRoundLoop.retainedRound_firstHalting`: agreement with scalar replay.
-/

public section

namespace Turing.DoubleCounting.SourceRoundLoop

open MultiTapeTM ComputableInSpace NondeterministicQueryMachine

variable {κ τ : Type} (size source : κ → ℕ)

/-- A round starts with the original context and the current scalar round entry. -/
@[expose] def retainedRoundEntry (r : Registers κ) : κ × SourceRound.MachineState τ :=
  (r.context, SourceRound.entry (roundContext size source r))

/-- Enter a retained round in workspace linear in the encoded loop registers. -/
theorem retainedRoundEntry_inSpace (encContext : κ ↪ List Bool) (encCallee : τ ↪ List Bool)
    (hsize : ComputableInSpace size encContext encNat (fun c => (encContext c).length))
    (hsource : ComputableInSpace source encContext encNat (fun c => (encContext c).length)) :
    ComputableInSpace (retainedRoundEntry size source)
      (encRegisters encContext) (encPair encContext (SourceRound.encMachineState τ encCallee))
      (fun r => (encRegisters encContext r).length) :=
  budget_prod (encRegisters_context_budget encContext (budget_id (.refl _)))
    (roundEntry_inSpace size source encContext encCallee hsize hsource)

variable (callee : NondeterministicQueryMachine τ)
  (calleeStart : κ → SourceRound.Context → SourceRound.Request → τ)
  (calleeReply : τ → Option Bool)

/-- A fixed round reads the enclosing context when starting each callback. -/
@[expose] def retainedRound (r : Registers κ) :
    NondeterministicQueryMachine (κ × SourceRound.MachineState τ) :=
  retain (Equiv.refl _) (fun k =>
    SourceRound.machine (roundContext size source r) callee (calleeStart k) calleeReply) r.context

/-- Changing the retained data and scalar registers at entry preserves the round transitions. -/
theorem retainedRound_withInit (r next : Registers κ) :
    (retainedRound size source callee calleeStart calleeReply r).withInit
      (retainedRoundEntry size source next) =
    retainedRound size source callee calleeStart calleeReply next := by
  unfold retainedRound
  rw [show retainedRoundEntry (τ := τ) size source next =
    (Equiv.refl _).symm (next.context, SourceRound.entry (roundContext size source next)) from rfl,
    retain_withInit]
  simp only [SourceRound.machine_withInit]

/-- Every selector replay preserves the context and runs the scalar round on the original word. -/
theorem retainedRound_run (r : Registers κ) (input bits : List Bool) :
    (retainedRound size source callee calleeStart calleeReply r).run input bits =
      (r.context, (SourceRound.machine (roundContext size source r) callee
        (calleeStart r.context) calleeReply).run input bits) :=
  replay_retain (Equiv.refl _) (fun k =>
    SourceRound.machine (roundContext size source r) callee (calleeStart k) calleeReply)
    r.context r.context input bits (SourceRound.entry (roundContext size source r))

/-- The retained round first halts on exactly the scalar round's selector lists. -/
theorem retainedRound_firstHalting (r : Registers κ) (input bits : List Bool) :
    (retainedRound size source callee calleeStart calleeReply r).FirstHalting input bits
      (retainedRoundEntry size source r) ↔
    (SourceRound.machine (roundContext size source r) callee
      (calleeStart r.context) calleeReply).FirstHalting input bits
      (SourceRound.entry (roundContext size source r)) :=
  firstHalting_retain (Equiv.refl _) (fun k =>
    SourceRound.machine (roundContext size source r) callee (calleeStart k) calleeReply)
    r.context r.context input bits (SourceRound.entry (roundContext size source r))

end Turing.DoubleCounting.SourceRoundLoop
