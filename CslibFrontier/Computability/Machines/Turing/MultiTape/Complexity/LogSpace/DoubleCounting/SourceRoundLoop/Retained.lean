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
* `Turing.DoubleCounting.SourceRoundLoop.retainedRound_haltsWithin`: a clock for every branch.
* `Turing.DoubleCounting.SourceRoundLoop.retainedRound_length_run_le`: encoded prefix-state bound.
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

/-- Step the retained round in linear workspace, using its immutable context at callback entry. -/
theorem retainedRound_next_inSpace (r : Registers κ) (encContext : κ ↪ List Bool)
    (encCallee : τ ↪ List Bool)
    (hs : ComputableInSpace (fun (k, q) => calleeStart k q.context (SourceRound.request q))
      (encPair encContext SourceRound.encState) encCallee
      (fun p => (encPair encContext SourceRound.encState p).length))
    (hf : ComputableInSpace calleeReply encCallee (encOption encBool)
      (fun s => (encCallee s).length))
    (hh : ComputableInSpace callee.halted encCallee encBool (fun s => (encCallee s).length))
    (hn : ComputableInSpace callee.next (encPair encCallee encReadChoice) encCallee
      (fun p => (encPair encCallee encReadChoice p).length)) :
    let encRound := encPair encContext (SourceRound.encMachineState τ encCallee)
    let encStep := encPair encRound encReadChoice
    ComputableInSpace (retainedRound size source callee calleeStart calleeReply r).next
      encStep encRound (fun p => (encStep p).length) := by
  let encRound := encPair encContext (SourceRound.encMachineState τ encCallee)
  exact budget_prod (fst' (fst encRound encReadChoice))
    (SourceRound.machine_next_withParameter_inSpace encContext encCallee
      (roundContext size source r) callee calleeStart calleeReply hs hf hh hn)

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

/-- A common callback clock bounds every retained round branch, including rejection. -/
theorem retainedRound_haltsWithin (r : Registers κ) (input : List Bool) (clock : ℕ)
    (hclock : ∀ req, req.InRange (size r.context) →
      callee.HaltsFrom input (calleeStart r.context (roundContext size source r) req) clock) :
    (retainedRound size source callee calleeStart calleeReply r).HaltsWithin input
      (SourceRound.roundClock (size r.context) clock) := by
  intro bits hlen
  rw [retainedRound_run]
  exact SourceRound.haltsWithin (roundContext size source r) callee (calleeStart r.context)
    calleeReply input clock hclock bits hlen

/-- The retained round charges one framed copy of the context in addition to the scalar state. -/
@[expose] def retainedRoundStateBound (encContext : κ ↪ List Bool) (r : Registers κ)
    (calleeBound : ℕ) : ℕ :=
  2 * (encContext r.context).length + 1 +
    SourceRound.roundStateBound (roundContext size source r) calleeBound

/-- The workspace bound includes both the immutable context and the suspended scalar round.
It holds for every selector prefix, including selectors that cause rejection. -/
theorem retainedRound_length_run_le (r : Registers κ) (encContext : κ ↪ List Bool)
    (encCallee : τ ↪ List Bool) (input bits : List Bool) (calleeBound : ℕ)
    (hcallee : ∀ req, req.InRange (size r.context) → ∀ choices,
      (encCallee (callee.replay input choices
        (calleeStart r.context (roundContext size source r) req))).length ≤ calleeBound) :
    (encPair encContext (SourceRound.encMachineState τ encCallee)
      ((retainedRound size source callee calleeStart calleeReply r).run input bits)).length ≤
      retainedRoundStateBound size source encContext r calleeBound := by
  rw [retainedRound_run, length_encPair, retainedRoundStateBound]
  exact Nat.add_le_add_left
    (SourceRound.length_encMachineState_run_le encCallee (roundContext size source r)
      callee (calleeStart r.context) calleeReply input bits calleeBound hcallee) _

/-- Continuing retained rounds preserve the same loop invariant as scalar rounds. -/
theorem retainedRound_admissible_closed (context : κ) (limit : ℕ) (input : List Bool) :
    Closed (retainedRound size source callee calleeStart calleeReply (start context limit))
      (retainedRoundEntry size source) (SourceRound.answer ∘ Prod.snd) input
      (Admissible context (size context) limit) := by
  intro r hr hpositive bits a hanswer _ _
  rw [← run_withInit, retainedRound_withInit, retainedRound_run] at hanswer
  exact admissible_advance_of_round_answer size source callee (calleeStart r.context)
    calleeReply hr hpositive input bits hanswer

end Turing.DoubleCounting.SourceRoundLoop
