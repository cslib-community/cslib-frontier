/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRound
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Dispatch

/-! Checked scalar traces for the source controller's tie and rejection results. -/

set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingSourceRound

open Turing Turing.DoubleCounting.SourceRound MultiTapeTM

private def context : Context := ⟨3, 0, 0, ⟨2, 0⟩⟩

private def reply : NondeterministicQueryMachine (Option Bool) where
  init := none
  query _ := 0
  next p := p.1
  halted _ := true
  accept := Option.isSome

private def start (_ : Context) : Request → Option Bool
  | .edge u v => some (decide (u < 2 ∧ v = 2))
  | .member u => some (decide (u < 2))

private def scalarRound := machine context reply start id

private def membershipReply : NondeterministicQueryMachine Bool where
  init := false
  query _ := 0
  next p := p.1
  halted _ := true
  accept _ := true

private def mixedStart (ctx : Context) (req : Request) : Option Bool ⊕ Bool :=
  match req with
  | .edge .. => .inl (start ctx req)
  | .member v => .inr (decide (v < 2))

private def mixedReply := reply.dispatch membershipReply

private def mixedFinish : Option Bool ⊕ Bool → Option Bool := Sum.elim id some

private def tieRound := machine context mixedReply mixedStart mixedFinish

-- The first two vertices are already in the round. Both reach the third vertex.
example :
    let q := tieRound.run [] (List.replicate 16 false)
    tieRound.halted q = true ∧ (answer q).map (·.bad) = some true ∧
      (answer q).map (·.tally.count) = some 3 := by decide +kernel

private theorem tie_firstHalting :
    tieRound.FirstHalting [] (List.replicate 16 false) tieRound.init := by
  refine ⟨by decide +kernel, ?_⟩
  intro n hn
  simp only [List.length_replicate] at hn
  interval_cases n <;> decide +kernel

/-- A tied result is a successful scan occurrence with its full updated tally. -/
example : replayScan context mixedReply mixedStart mixedFinish [] (List.replicate 16 false) =
    some (⟨⟨3, 1⟩, true⟩, []) :=
  (firstHalting_iff_replayScan context mixedReply mixedStart mixedFinish _ _ _).mp
    ⟨tie_firstHalting, rfl⟩

/-- A tied round remains successful and has only one complete selector list. -/
example : {bits : List Bool | tieRound.FirstHalting [] bits tieRound.init ∧
    (answer (tieRound.run [] bits)).isSome} = {List.replicate 16 false} := by
  have hu := subsingleton_successful_firstHalting context mixedReply mixedStart mixedFinish [] (by
    intro req _ left hl right hr
    have hempty (bits : List Bool) (h : mixedReply.FirstHalting [] bits (mixedStart context req)) :
        bits = [] := by
      cases req with
      | edge u v =>
        exact (reply.firstHalting_iff_nil_of_halted [] bits _ rfl).mp
          ((reply.firstHalting_dispatch_inl membershipReply [] bits _).mp h)
      | member v =>
        exact (membershipReply.firstHalting_iff_nil_of_halted [] bits _ rfl).mp
          ((reply.firstHalting_dispatch_inr membershipReply [] bits _).mp h)
    exact (hempty left hl.1).trans (hempty right hr.1).symm)
  exact hu.eq_singleton_of_mem ⟨tie_firstHalting, rfl⟩

private def rejectRound := machine context reply
  (fun ctx request => match request with
    | .edge .. => none
    | .member _ => start ctx request) id

-- A missing reply on the first edge call rejects the round.
example :
    let q := rejectRound.run [] (List.replicate 8 false)
    rejectRound.halted q = true ∧ (answer q).isNone = true := by decide +kernel

private inductive CallbackState where
  | pending (request : Request)
  | finished (reply : Option Bool)

private def readReply (request : Request) (bit : Option Bool) : Option Bool :=
  match request with
  | .edge u v => bit.map fun b => b && decide (u < 2 ∧ v = 2)
  | .member u => some (decide (u < 2))

private def callback : NondeterministicQueryMachine CallbackState where
  init := .finished none
  query _ := 0
  next := fun
    | (.pending request, bit, _) => .finished (readReply request bit)
    | (.finished result, _, _) => .finished result
  halted := fun
    | .pending _ => false
    | .finished _ => true
  accept _ := true

private def finish : CallbackState → Option Bool
  | .pending _ => none
  | .finished result => result

/-- A live edge call retains its tag and reads the original word during its own step. -/
example :
    let combined := callback.dispatch membershipReply
    Sum.elim finish some (combined.replay [true] [true] (.inl (.pending (.edge 0 2)))) =
      some true := by
  dsimp only
  rw [callback.replay_dispatch]
  rfl

private def round := machine context callback (fun _ => .pending) finish

/-- Reading an edge bit on the original input distinguishes a tie from a missing reply. -/
example :
    let tied := round.run [true] (List.replicate 24 false)
    let rejected := round.run [] (List.replicate 12 false)
    round.halted tied = true ∧ (answer tied).map (·.bad) = some true ∧
      round.halted rejected = true ∧ (answer rejected).isNone = true := by
  decide +kernel

/-- Any selector prefix on a missing edge reply stays within the scalar round envelope. -/
example (choices : List Bool) :
    let q := (round.run [] choices).controller
    q.cursor ≤ 3 ∧ q.update.tally.count ≤ 2 + q.cursor ∧
      q.update.tally.lengthSum ≤ q.cursor := by
  simpa only [round, context, Nat.zero_add, Nat.mul_one] using
    (run_scalar_bounds context callback (fun _ => .pending) finish [] choices).2

/-- The encoded prefix includes the full suspended caller and optional callee. -/
example (choices : List Bool) :
    (encMachineState (Option Bool) (encOption encBool) (scalarRound.run [] choices)).length ≤
      roundStateBound context 2 := by
  have hcallee (req : Request) (_ : req.InRange context.size) (bits : List Bool) :
      (encOption encBool (reply.replay [] bits (start context req))).length ≤ 2 := by
    cases reply.replay [] bits (start context req) with
    | none => decide
    | some flag => cases flag <;> decide
  exact length_encMachineState_run_le (encOption encBool) context reply start id
    [] choices 2 hcallee

/-- The common clock covers wrong routing selectors as well as valid calls. -/
example : scalarRound.HaltsWithin [] (roundClock context.size 0) :=
  Turing.DoubleCounting.SourceRound.haltsWithin context reply start id [] 0 (fun _ _ _ _ => rfl)

example :
    ComputableInSpace (entry (τ := Option Bool)) encContext
      (encMachineState (Option Bool) (encOption encBool)) (fun ctx => (encContext ctx).length) :=
  entry_inSpace _

example :
    ComputableInSpace (answer (τ := Option Bool))
      (encMachineState (Option Bool) (encOption encBool))
      (encOption Turing.DoubleCounting.encRoundUpdate)
      (fun q => (encMachineState (Option Bool) (encOption encBool) q).length) :=
  answer_inSpace _

private def allMembers (_ : Context) (_ : Request) : Option Bool := some true

private theorem nativeRoutines :
    Nonempty (NondeterministicQueryMachine.Routines (machine context reply allMembers id)
      (fun _ : Bool => entry context) encBool (fun _ => 1)) := by
  open ComputableInSpace in
  refine exists_routines encBool (encOption encBool) context reply allMembers id
    (fun _ => context) (fun _ => 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact constZero context |>.mono_le (fun _ => by decide)
  · intro b
    cases b <;> decide
  · exact (budget_const (some true) (.refl _)).of_enc_eq fun _ => rfl
  · exact of_inO (ComputableInDegree.id' (enc := encOption encBool)).inO_one
  · exact (budget_const 0 (.refl _)).of_enc_eq fun _ => rfl
  · exact (budget_const true (.refl _)).of_enc_eq fun _ => rfl
  · exact (fst (encOption encBool) NondeterministicQueryMachine.encReadChoice).of_enc_eq
      fun _ => rfl
  · refine ⟨roundStateBound context 2, fun a bits => ?_⟩
    rw [Nat.mul_one]
    apply length_encMachineState_run_le (D := 2)
    intro req _ selectors
    cases h : reply.replay (encBool a) selectors (allMembers context req) with
    | none => decide
    | some value => cases value <;> decide

open NondeterministicQueryMachine in
/-- Three passing membership calls give exactly one native occurrence list for their selectors. -/
example : ∃ R : Routines (machine context reply allMembers id)
    (fun _ : Bool => entry context) encBool (fun _ => 1),
    ∃! indices, ∃ final, Native.replayChoices R.I R.P R.F R.C
      (R.machine.initCfg (encBool true)) indices = some (List.replicate 6 false, final) ∧
      final.Halted := by
  obtain ⟨R⟩ := nativeRoutines
  refine ⟨R, (R.existsUnique_replay_iff true _).mpr ⟨by decide +kernel, ?_⟩⟩
  intro n hn
  simp only [List.length_replicate] at hn
  interval_cases n <;> decide +kernel

open NondeterministicQueryMachine in
/-- At a sufficient native clock, count passing occurrences against the complete typed scans. -/
example : ∃ (R : Routines (machine context reply allMembers id)
    (fun _ : Bool => entry context) encBool (fun _ => 1)) (fuel : ℕ),
    ((Native.countingMachine R.I R.P R.F R.C).branchCount
      (fun out => decide (out = [true])) fuel (R.machine.initCfg (encBool true)) : ℕ∞) =
    {bits : List Bool | ∃ update,
      replayScan context reply allMembers id (encBool true) bits = some (update, [])}.encard := by
  obtain ⟨R⟩ := nativeRoutines
  have hhalt : ((machine context reply allMembers id).withInit (entry context)).HaltsWithin
      (encBool true) (roundClock context.size 0) := by
    rw [machine_withInit]
    exact Turing.DoubleCounting.SourceRound.haltsWithin context reply allMembers id _ 0
      (fun _ _ _ _ => rfl)
  obtain ⟨fuel, hclock⟩ := R.exists_runsInTime true hhalt
  exact ⟨R, fuel, branchCount_eq_encard_replayScan R true hclock⟩

end CslibFrontierTests.DoubleCountingSourceRound
