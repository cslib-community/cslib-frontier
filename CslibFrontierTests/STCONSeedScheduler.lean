/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler
meta import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler

/-! Ordinary-import clients for the binary seed and source scheduler. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONSeedScheduler

open Cslib.Complexity.STCON Cslib.DoubleCounting
open Turing Turing.MultiTapeTM

-- Original positions 0 and 1 map to subdivision IDs 0 and 2.
private def setup : SeedSearchSetup :=
  ⟨⟨⟨0, 1, 2, 0⟩, ⟨⟨2, 1, 4⟩, 2, 4⟩⟩, 0, 2⟩

private theorem sourceValid : setup.sourceID < setup.parameters.search.subdivision.vertexCount :=
  by decide

private theorem rootValid (i : ℕ) (hi : i < setup.parameters.search.subdivision.originalCount) :
    setup.originalSourceID i < setup.parameters.search.subdivision.vertexCount := by
  change i < 2 at hi
  rw [SeedSearchSetup.originalSourceID]
  change (1 + 1) * i < 4
  omega

-- Seed zero fails at the other source. Seed one is selected with the designated `false`
-- answer, even though the other source answers `true`. Each of the two successful
-- verdicts at seed zero continues to seed one, where the two outcomes multiply.
private def scan (f : SeedSchedulerFrame) : List (Option ControllerVerdict) :=
  if f.answer.isNone then [some (.decided false), some (.decided false)]
  else if f.cursor == 1 && f.request.sourceID == 2 then
    if f.request.seed == 0 then [some (.bad 0)] else [some (.decided true)]
  else []

set_option linter.hashCommand false in
#guard (runSeedSchedulerFor setup sourceValid rootValid scan).map
    (Option.map fun a => (a.seed.val, a.reachable)) == List.replicate 4 (some (1, false))

private def rejecting (_ : SeedSchedulerFrame) :
    OptionT (StateM ℕ) (Option ControllerVerdict) :=
  OptionT.mk fun t => (none, t + 1)

set_option linter.hashCommand false in
#guard
  let result := (runSeedSchedulerFor setup sourceValid rootValid rejecting).run 0
  result.1.isNone && result.2 == 1

example (t : ℕ) :
    ((runSeedSchedulerFor setup sourceValid rootValid rejecting).run t).2 ≤ t + 12 :=
  runSeedSchedulerFor_clock id 1 setup sourceValid rootValid rfl rejecting
    (fun _ _ _ _ _ _ => le_rfl) t

example : ComputableInSpace seedScanRequest
    (encPair encSeedSearchSetup (encPair encNat (encOption encNat))) encSeedScanRequest
    (fun p => (encPair encSeedSearchSetup (encPair encNat (encOption encNat)) p).length) :=
  seedScanRequest_inSpace

example (state : ℕ) :
    let frame := seedSchedulerFrame setup 1 none setup.sourceID
    frame.request = seedScanRequest (setup, 1, none) ∧
      (encPair encSeedSchedulerFrame encNat (frame, state)).length ≤
        24 * (encSeedSearchSetup setup).length + (encNat state).length + 19 :=
  ⟨seedSchedulerFrame_designated_request setup 1,
    length_seedSchedulerCall_le encNat setup rfl ⟨1, by decide⟩
      none ⟨setup.sourceID, sourceValid⟩ state⟩

example (state : ℕ) :
    let frame := seedSchedulerFrame setup 1 (some (1, false)) (setup.originalSourceID 1)
    frame.request = seedScanRequest (setup, 1, some 1) ∧
      (encPair encSeedSchedulerFrame encNat (frame, state)).length ≤
        24 * (encSeedSearchSetup setup).length + (encNat state).length + 19 :=
  ⟨seedSchedulerFrame_indexed_request setup 1 1 false,
    length_seedSchedulerCall_le encNat setup rfl ⟨1, by decide⟩
      (some (⟨1, by decide⟩, false)) ⟨setup.originalSourceID 1, rootValid 1 (by decide)⟩ state⟩

-- The same entry point accepts the native initializer's IDs and root lookup certificates.
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (input : List Bool) (scanner : SeedScanRequest → List (Option ControllerVerdict)) :
    let s := configurationSeedSearchSetup ntm c input
    let hs := (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c input).1
    let hr := fun (_ : ℕ) hp =>
      configurationSeedSearchSetup_originalSourceID_lt_vertexCount ntm c input hp
    runSeedSchedulerFor s hs hr (fun f => scanner f.request) =
      runSeedSearchIndexed
        (fun bits u => scanner ⟨s, (Cslib.BitString.equivFin _ bits).val, u.val⟩)
        (fun j => ⟨s.originalSourceID j.val, hr _ j.isLt⟩) ⟨s.sourceID, hs⟩ :=
  runSeedSchedulerFor_eq _ _ _ scanner

end CslibFrontierTests.STCONSeedScheduler
