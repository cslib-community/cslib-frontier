/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop.Resource
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.CallReplay

/-!
# Typed round replies in the native source loop

A successful return from the re-entered round machine consumes a complete typed round trace
and the false return selector. The rest of the selector list is available to the source loop.

## Main results

* `readSourceRoundReply_iff` characterizes the complete typed prefix and exact suffix.
* `firstHalting_iff_replayTypedRounds` matches successful loop occurrences with typed scans and
  the final membership replay.
-/

public section

namespace Turing.DoubleCounting.SourceRoundLoop

open Cslib.DoubleCounting NondeterministicQueryMachine

/-- The loop's round parser consumes a complete typed round replay and the false return selector,
leaving the suffix for the next round or the final membership callback. -/
theorem readSourceRoundReply_iff {κ τ : Type} (size source : κ → ℕ)
    (callee : NondeterministicQueryMachine τ)
    (calleeStart : SourceRound.Context → SourceRound.Request → τ)
    (calleeReply : τ → Option Bool) (initial r : Registers κ)
    (input bits : List Bool) (update : RoundUpdate) (suffix : List Bool) :
    let round := SourceRound.machine (roundContext size source initial) callee calleeStart
      calleeReply
    round.readReply SourceRound.answer input (SourceRound.entry (roundContext size source r))
      bits = some (update, suffix) ↔
      ∃ roundBits, bits = roundBits ++ false :: suffix ∧
        SourceRound.replayScan (roundContext size source r) callee calleeStart calleeReply input
          roundBits = some (update, []) := by
  dsimp only
  rw [readReply_iff]
  refine exists_congr fun roundBits => and_congr_right' ?_
  have hscan := SourceRound.firstHalting_iff_replayScan (roundContext size source r)
    callee calleeStart calleeReply input roundBits update
  rw [← SourceRound.machine_withInit (roundContext size source initial),
    firstHalting_withInit, run_withInit] at hscan
  exact hscan

section TypedLoop

variable {κ τ μ : Type} (size source : κ → ℕ)
  (callee : NondeterministicQueryMachine τ)
  (calleeStart : SourceRound.Context → SourceRound.Request → τ)
  (calleeReply : τ → Option Bool) (input : List Bool)

private def TypedReturn (r : Registers κ) (bits : List Bool) (out : RoundUpdate × List Bool) :
    Prop :=
  ∃ roundBits, bits = roundBits ++ false :: out.2 ∧
    SourceRound.replayScan (roundContext size source r) callee calleeStart calleeReply input
      roundBits = some (out.1, [])

/-- The typed scan's update and the unused selectors after its false return selector.
The complete scan prefix determines the reply uniquely. -/
noncomputable def typedRoundReply (r : Registers κ) (bits : List Bool) :
    Option (RoundUpdate × List Bool) := by
  classical
  exact if h : ∃ out, TypedReturn size source callee calleeStart calleeReply input r bits out
    then some h.choose else none

private theorem typedRoundReply_eq (initial r : Registers κ) (bits : List Bool) :
    typedRoundReply size source callee calleeStart calleeReply input r bits =
      readReply (SourceRound.machine (roundContext size source initial)
        callee calleeStart calleeReply) SourceRound.answer input
        (SourceRound.entry (roundContext size source r)) bits := by
  classical
  have hspec (out : RoundUpdate × List Bool) :
      readReply (SourceRound.machine (roundContext size source initial)
        callee calleeStart calleeReply) SourceRound.answer input
        (SourceRound.entry (roundContext size source r)) bits = some out ↔
        TypedReturn size source callee calleeStart calleeReply input r bits out :=
    readSourceRoundReply_iff size source callee calleeStart calleeReply initial r input bits
      out.1 out.2
  unfold typedRoundReply
  split
  · rename_i h
    exact ((hspec h.choose).mpr h.choose_spec).symm
  · rename_i h
    cases he : (SourceRound.machine (roundContext size source initial)
        callee calleeStart calleeReply).readReply SourceRound.answer input
        (SourceRound.entry (roundContext size source r)) bits with
    | none => rfl
    | some out => exact (h ⟨out, (hspec out).mp he⟩).elim

/-- A typed round reply consumes a complete scan and exactly one false return selector. -/
theorem typedRoundReply_iff (r : Registers κ) (bits : List Bool) (update : RoundUpdate)
    (suffix : List Bool) :
    typedRoundReply size source callee calleeStart calleeReply input r bits =
      some (update, suffix) ↔
    ∃ roundBits, bits = roundBits ++ false :: suffix ∧
      SourceRound.replayScan (roundContext size source r) callee calleeStart calleeReply input
        roundBits = some (update, []) := by
  rw [typedRoundReply_eq size source callee calleeStart calleeReply input r]
  exact readSourceRoundReply_iff size source callee calleeStart calleeReply r r
    input bits update suffix

variable (member : NondeterministicQueryMachine μ)
  (memberStart : Registers κ → μ) (memberReply : μ → Option Bool)

/-- Replay the existing fuel-bounded loop using typed finite scans for the rounds.
A round consumes its complete scan and one false return selector. At stabilization the
membership callback runs with the current radius and tally. The result includes the unused suffix.
The typed round reply is determined by the supplied selector list. -/
@[expose] noncomputable def replayTypedRounds (r : Registers κ) (bits : List Bool) :
    Option (Option ControllerVerdict × List Bool) :=
  (runRoundsWith (m := StateT (List Bool) Option)
    (fun fuel radius tally =>
      typedRoundReply size source callee calleeStart calleeReply input
        ⟨r.context, fuel, radius, tally⟩)
    (fun fuel radius tally =>
      member.readReply memberReply input (memberStart ⟨r.context, fuel, radius, tally⟩))
    r.fuel r.radius r.tally).run bits

/-- The complete loop has a successful first halt precisely when its typed replay returns the
same verdict and consumes the entire selector list. Equal verdicts do not identify selector lists
from different callback occurrences. -/
theorem firstHalting_iff_replayTypedRounds (context : κ) (limit : ℕ)
    (bits : List Bool) (verdict : ControllerVerdict) :
    let M := withSourceRound size source callee calleeStart calleeReply context limit member
      memberStart memberReply
    M.FirstHalting input bits M.init ∧ M.run input bits = .inr (some verdict) ↔
      replayTypedRounds size source callee calleeStart calleeReply input member memberStart
        memberReply (start context limit) bits = some (some verdict, []) := by
  have h := firstHalting_iff_replayRounds (start context limit)
    (SourceRound.machine (roundContext size source (start context limit))
      callee calleeStart calleeReply)
    (fun r => SourceRound.entry (roundContext size source r)) SourceRound.answer
    member memberStart memberReply input bits verdict
  have hread (r : Registers κ) :=
    funext (typedRoundReply_eq size source callee calleeStart calleeReply input
      (start context limit) r)
  simpa only [withSourceRound, replayRounds, replayTypedRounds, hread] using h

end TypedLoop

end Turing.DoubleCounting.SourceRoundLoop
