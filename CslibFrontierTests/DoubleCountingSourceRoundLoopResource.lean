/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop.Replay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop.Retained

/-! A concrete single-round machine composed with the multi-round source loop. -/

set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingSourceRoundLoopResource

open Turing MultiTapeTM ComputableInSpace NondeterministicQueryMachine
open Turing.DoubleCounting
open Turing.DoubleCounting.SourceRoundLoop

private def callback : NondeterministicQueryMachine Unit where
  init := ()
  query := fun _ => 0
  next := fun _ => ()
  halted := fun _ => true
  accept := fun _ => true

private def oneVertex (_ : Unit) : ℕ := 1

private def source (_ : Unit) : ℕ := 0

private def entry (_ : Turing.DoubleCounting.SourceRound.Context)
    (_ : Turing.DoubleCounting.SourceRound.Request) : Unit := ()

private def memberEntry (_ : Registers Unit) : Unit := ()

private def scan :=
  withSourceRound oneVertex source callback entry (fun _ => some true) () 1
    callback memberEntry (fun _ => some false)

example : ComputableInSpace
    (fun r => Turing.DoubleCounting.SourceRound.entry (roundContext oneVertex source r))
    (encRegisters encUnit) (Turing.DoubleCounting.SourceRound.encMachineState Unit encUnit)
    (fun r => (encRegisters encUnit r).length) :=
  roundEntry_inSpace oneVertex source encUnit encUnit
    (budget_const 1 (.refl _)) (budget_const 0 (.refl _))

-- The first call counts no new vertex, and the final membership call returns a valid negative.
example : (scan.run [] [false, false, false, false]) = .inr (some (.decided false)) := rfl

/-- Whole-loop typed replay consumes the stabilized negative and excludes an invalid return. -/
example :
    let replay := replayTypedRounds oneVertex source callback entry (fun _ => some true) []
      callback memberEntry (fun _ => some false) (start () 1)
    replay [false, false, false, false] = some (some (.decided false), []) ∧
      ∀ verdict, replay [false, false, true, false] ≠ some (some verdict, []) := by
  dsimp only
  have h (bits : List Bool) (verdict : Cslib.DoubleCounting.ControllerVerdict) :=
    firstHalting_iff_replayTypedRounds oneVertex source callback entry (fun _ => some true) []
      callback memberEntry (fun _ => some false) () 1 bits verdict
  constructor
  · exact (h _ _).mp ⟨NondeterministicQueryMachine.firstHalting_append_singleton scan []
      [false, false, false] false rfl rfl, rfl⟩
  · intro verdict hr
    obtain ⟨_, hrun⟩ := (h _ _).mpr hr
    change (scan.run [] [false, false, true, false]) = .inr (some verdict) at hrun
    have hrejected : scan.run [] [false, false, true, false] = .inr none := rfl
    rw [hrejected] at hrun
    cases hrun

-- Enter a different register state and leave two bits for the enclosing loop.
example :
    let initial : Registers Unit := ⟨(), 3, 2, ⟨0, 0⟩⟩
    let r := start () 1
    let round := SourceRound.machine (roundContext oneVertex source initial) callback entry
      (fun _ => some true)
    let run := round.readReply SourceRound.answer [] (SourceRound.entry
      (roundContext oneVertex source r))
    run [false, false, false, true, false] = some (⟨⟨1, 0⟩, false⟩, [true, false]) ∧
      run [false, false, true, true, false] = none := by
  dsimp only
  constructor
  · apply (readSourceRoundReply_iff oneVertex source callback entry (fun _ => some true)
      _ _ [] _ _ _).mpr
    refine ⟨[false, false], rfl, (SourceRound.firstHalting_iff_replayScan _ callback entry
      (fun _ => some true) [] [false, false] _).mp ⟨?_, rfl⟩⟩
    exact NondeterministicQueryMachine.firstHalting_append_singleton _ [] [false] false rfl rfl
  · rfl

-- The same concrete machine has the composed clock on every branch and every input.
example (input : List Bool) : scan.HaltsWithin input 15 := by
  simpa only [scan, oneVertex, SourceRound.roundClock] using
    withSourceRound_haltsWithin oneVertex source callback entry (fun _ => some true) () 1
      callback memberEntry (fun _ => some false) input 0 0
      (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

private def stateBound : ℕ :=
  2 * registerStateBound encUnit () (oneVertex ()) 1 +
    max (SourceRound.roundStateBound ⟨oneVertex (), source (), 1,
      ⟨1 + 1 * oneVertex (), oneVertex () * 1 * 1⟩⟩ 0) 0 + (encNat 1).length + 4

-- The bound includes the actual suspended single-round state and the outer registers.
private theorem length_scan_run_le (input choices : List Bool) :
    (encState encUnit (SourceRound.encMachineState Unit encUnit)
      encUnit (scan.run input choices)).length ≤ stateBound :=
  withSourceRound_length_run_le oneVertex source callback entry (fun _ => some true) () 1
    encUnit encUnit encUnit callback memberEntry (fun _ => some false) input 0 0
    (fun _ _ _ _ _ => Nat.zero_le 0) (fun _ _ _ => Nat.zero_le 0) choices

private def nativeBudget (input : List Bool) : ℕ :=
  Nat.log2 input.length + stateBound + 1

private theorem nativeRoutines :
    Nonempty (Routines scan (fun _ : List Bool => scan.init) encBits nativeBudget) := by
  refine withSourceRound_exists_routines oneVertex source callback entry (fun _ => some true)
    () 1 encBits nativeBudget encUnit encUnit encUnit callback memberEntry (fun _ => some false)
    (fun _ => ()) (fun _ => 1)
    ((ComputableInSpace.constZero (start () 1)).mono_le fun _ => Nat.zero_le _) ?_
    (budget_const 1 (.refl _)) (budget_const 0 (.refl _))
    (budget_const () (.refl _)) (budget_const (some true) (.refl _)) (budget_const 0 (.refl _))
    (budget_const true (.refl _)) (budget_const () (.refl _)) (budget_const () (.refl _))
    (budget_const (some false) (.refl _)) (budget_const 0 (.refl _))
    (budget_const true (.refl _)) (budget_const () (.refl _)) ⟨1, ?_⟩
  · intro input
    simp only [nativeBudget, encBits_apply]
    omega
  · intro input bits
    rw [Nat.one_mul]
    exact (length_scan_run_le (encBits input) bits).trans (by unfold nativeBudget; omega)

/-- The composed machine has exactly one native occurrence for the passing negative trace. -/
example : ∃ R : Routines scan (fun _ : List Bool => scan.init) encBits nativeBudget,
    ∃! indices, ∃ final,
      Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg []) indices =
        some ([false, false, false, false], final) ∧ final.Halted ∧ final.output = [true] := by
  obtain ⟨R⟩ := nativeRoutines
  let roundStart (r : Registers Unit) : SourceRound.MachineState Unit :=
    SourceRound.entry (roundContext oneVertex source r)
  let round := SourceRound.machine (roundContext oneVertex source (start () 1))
    callback entry (fun _ => some true)
  refine ⟨R, (native_firstHalting_accept_iff (start () 1) round roundStart SourceRound.answer
    callback memberEntry (fun _ => some false) (fun _ => start () 1) R []
      [false, false, false, false]).mpr ?_⟩
  refine ⟨.decided false, (firstHalting_iff_replayRounds (start () 1) round roundStart
    SourceRound.answer callback memberEntry (fun _ => some false) [] _ _).mp ⟨?_, rfl⟩⟩
  exact scan.firstHalting_append_singleton [] [false, false, false] false rfl rfl

private def retainedSize (_ : Bool) : ℕ := 1

private def retainedSource (_ : Bool) : ℕ := 0

private def optionalCallback : NondeterministicQueryMachine (Option Bool) where
  init := none
  query _ := 0
  next p := p.1
  halted _ := true
  accept := Option.isSome

private def retainedStart (enabled : Bool) (_ : SourceRound.Context)
    (_ : SourceRound.Request) : Option Bool :=
  if enabled then some true else none

private def retainedLoop :=
  machine (start false 1)
    (retainedRound retainedSize retainedSource optionalCallback retainedStart id (start false 1))
    (retainedRoundEntry retainedSize retainedSource) (SourceRound.answer ∘ Prod.snd)
    callback (fun _ => ()) (fun _ => some true)

/-- The same source loop re-enters with new immutable context and obtains a round reply. -/
example :
    let selectors := [false, false, false, false]
    retainedLoop.run [] selectors = .inr none ∧
      (retainedLoop.withInit (enterRound (retainedRoundEntry retainedSize retainedSource)
        (start true 1))).run [] selectors =
        .inr (some (.decided true)) := ⟨rfl, rfl⟩

/-- Re-entry uses the scalar round's strict first-halting condition. -/
example (bits : List Bool) :
    let r := start true 1
    let round := retainedRound retainedSize retainedSource optionalCallback retainedStart id
      (start false 1)
    let entry := retainedRoundEntry retainedSize retainedSource r
    round.FirstHalting [] bits entry ↔
      (SourceRound.machine (roundContext retainedSize retainedSource r) optionalCallback
        (retainedStart true) id).FirstHalting [] bits
        (SourceRound.entry (roundContext retainedSize retainedSource r)) := by
  dsimp only
  rw [← firstHalting_withInit, retainedRound_withInit]
  exact retainedRound_firstHalting retainedSize retainedSource optionalCallback retainedStart id
    (start true 1) [] bits

example :
    ComputableInSpace (retainedRoundEntry (τ := Option Bool) retainedSize retainedSource)
      (encRegisters encBool)
      (encPair encBool (SourceRound.encMachineState (Option Bool) (encOption encBool)))
      (fun r => (encRegisters encBool r).length) :=
  retainedRoundEntry_inSpace retainedSize retainedSource encBool (encOption encBool)
    (budget_const 1 (.refl _)) (budget_const 0 (.refl _))

end CslibFrontierTests.DoubleCountingSourceRoundLoopResource
