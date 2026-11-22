/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler.Machine
meta import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler.Machine

/-! Check the scheduler's same-input and single-selector call protocol. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONSeedSchedulerMachine

open Cslib.Complexity.STCON Cslib.Complexity.STCON.SeedSchedulerMachine Cslib.DoubleCounting
open Turing

private def setup : SeedSearchSetup :=
  ⟨⟨⟨0, 1, 2, 0⟩, ⟨⟨2, 1, 4⟩, 2, 4⟩⟩, 0, 2⟩

private def scan : NondeterministicQueryMachine (ℕ ⊕ Option Bool) where
  init := .inl 0
  query := Sum.elim id (fun _ => 0)
  next | (_, read, choice) => .inr (if choice then none else read)
  halted := Sum.elim (fun _ => false) (fun _ => true)
  accept := Sum.elim (fun _ => false) Option.isSome

private def verdict : ℕ ⊕ Option Bool → Option ControllerVerdict :=
  Sum.elim (fun _ => none) (Option.map ControllerVerdict.decided)

private def scheduler := machine setup scan (fun r => .inl r.sourceID) verdict

-- The common clock also covers a rejecting selector or a read past the input.
example (w : List Bool) : scheduler.HaltsWithin w 24 := by
  refine Cslib.Complexity.STCON.SeedSchedulerMachine.haltsWithin setup scan
    (fun r => .inl r.sourceID) verdict w 1 ?_
  intro _ _ _ _ bits hlen
  obtain ⟨bit, rfl⟩ := List.length_eq_one_iff.mp hlen
  rfl

-- The designated source reads position 0 and the other root reads position 2.
-- The negative designated reply survives that positive indexed scan.
set_option linter.hashCommand false in
#guard
  let final := scheduler.run [false, false, true] (List.replicate 5 false)
  decide (reply final = some (some ⟨0, false⟩)) && !(scheduler.accept final)

set_option linter.hashCommand false in
#guard
  let final := scheduler.run [true, false, false] (List.replicate 5 false)
  scheduler.accept final && decide (reply final = some (some ⟨0, true⟩))

-- A true selector on the skipped root rejects the branch.
set_option linter.hashCommand false in
#guard
  let final := scheduler.run [false, false, true] [false, false, true]
  scheduler.halted final && (reply final).isNone

-- A manually constructed active state can retain a frame whose root would be skipped.
-- Its missing verdict still goes through the shared transition.
set_option linter.hashCommand false in
#guard
  let frame := seedSchedulerFrame setup 0 (some (0, false)) setup.sourceID
  match scheduler.step [] (.inl (.inr (frame, .inr none))) false with
  | .inl (.inr (next, .inl 2)) => next.cursor == 1 && next.answer == some false
  | _ => false

-- A zero seed limit exhausts the search without entering the scanner.
set_option linter.hashCommand false in
#guard
  let search := { setup.parameters.search with seedLimit := 0 }
  let parameters := { setup.parameters with search }
  let emptyScheduler := machine { setup with parameters } scan (fun r => .inl r.sourceID) verdict
  emptyScheduler.halted emptyScheduler.init &&
    decide (reply emptyScheduler.init = some none) && !(emptyScheduler.accept emptyScheduler.init)

example (w : List Bool) (frame : SeedSchedulerFrame) (pos : ℕ) (bit : Bool) :
    scheduler.step w (.inl (.inr (frame, .inl pos))) bit =
      .inl (.inr (frame, scan.step w (.inl pos) bit)) :=
  step_liveScan setup scan _ verdict w frame (.inl pos) bit rfl

/-- A skipped root and a positive indexed scan leave their exact suffix to the scheduler.
The eventual terminal answer is the designated negative answer. -/
example (skipped indexed : SeedSchedulerFrame) (hneedsScan : indexed.needsScan = true)
    (henter : resume (σ := ℕ ⊕ Option Bool) (fun r => .inl r.sourceID) skipped none =
      .inl (.inr (indexed, .inl 2))) :
    let w := [false, false, true]
    let start : SeedScanRequest → ℕ ⊕ Option Bool := fun r => .inl r.sourceID
    let answer : Option Answer := some ⟨0, false⟩
    let resumed := resume start indexed (some (.decided true))
    scheduler.FirstHalting w [false, false, false] (.inl (.inl skipped)) ∧
      scheduler.replay w [false, false, false] (.inl (.inl skipped)) = .inr (some answer) ↔
    scheduler.FirstHalting w [] resumed ∧ scheduler.replay w [] resumed = .inr (some answer) := by
  intro w start answer resumed
  have hparse : scan.readReply verdict w (.inl 2) [false, false] =
      some (.decided true, []) := rfl
  change (machine setup scan start verdict).FirstHalting w _ _ ∧
    (machine setup scan start verdict).replay w _ _ = _ ↔ _
  have hskip := firstHalting_skip_iff setup scan start verdict w skipped
    [false, false, false] answer
  have hscan := firstHalting_scan_iff setup scan start verdict w indexed (.inl 2)
    [false, false] answer hneedsScan
  dsimp only at hskip hscan
  rw [hskip]
  simp only [List.cons.injEq, true_and, exists_eq_left']
  rw [show resume start skipped none = _ from henter, hscan, hparse]
  simp [resumed, scheduler, start]

open MultiTapeTM ComputableInSpace in
/-- All scheduler observations fit within the budget of the live state producer. -/
example {α σ : Type} {enc : α ↪ List Bool} {S : α → ℕ} (encScan : σ ↪ List Bool)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict)
    (hquery : ComputableInSpace scan.query encScan encNat (fun s => (encScan s).length))
    {state : α → State σ} (hstate : ComputableInSpace state enc (encState encScan) S) :
    let M := machine setup scan start verdict
    ComputableInSpace (fun a => M.query (state a)) enc encNat S ∧
      ComputableInSpace (fun a => M.halted (state a)) enc encBool S ∧
      ComputableInSpace (fun a => reply (state a)) enc (encOption (encOption encAnswer)) S ∧
      ComputableInSpace (fun a => M.accept (state a)) enc encBool S := by
  obtain ⟨hq, hh, hr, ha⟩ := observations_inSpace encScan setup scan start verdict hquery
  exact ⟨budget_comp_linear hq hstate, budget_comp_linear hh hstate,
    budget_comp_linear hr hstate, budget_comp_linear ha hstate⟩

end CslibFrontierTests.STCONSeedSchedulerMachine
