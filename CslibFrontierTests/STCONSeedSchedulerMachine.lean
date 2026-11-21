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

end CslibFrontierTests.STCONSeedSchedulerMachine
