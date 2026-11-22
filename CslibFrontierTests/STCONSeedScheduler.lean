/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceContext.Scheduler
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
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

-- Skip the designated root, try the other root, and restart after the bad verdict.
-- The next seed keeps its designated negative answer even though its other root is positive.
set_option linter.hashCommand false in
#guard
  let run := do
    let designated ← seedSchedulerCandidate setup 0
    let .inl skip ← seedSchedulerStep designated (some (.decided false)) | none
    if skip.needsScan then none else
    let .inl indexed ← seedSchedulerStep skip none | none
    if !indexed.needsScan || indexed.request.sourceID != 2 then none else
    let .inl next ← seedSchedulerStep indexed (some (.bad 0)) | none
    if next.request.seed != 1 || !next.needsScan then none else
    let .inl skip ← seedSchedulerStep next (some (.decided false)) | none
    let .inl indexed ← seedSchedulerStep skip none | none
    let .inr answer ← seedSchedulerStep indexed (some (.decided true)) | none
    pure answer
  run == some (some false)

set_option linter.hashCommand false in
#guard
  match seedSchedulerCandidate setup 3 with
  | none => false
  | some last =>
    (seedSchedulerStep last none).isNone &&
      (match seedSchedulerStep last (some (.bad 0)) with
       | some (.inr none) => true
       | _ => false)

example {f g : SeedSchedulerFrame} {reply : Option ControllerVerdict}
    (hf : f.Valid) (h : seedSchedulerStep f reply = some (.inl g)) :
    g.Valid ∧ g.request.setup = f.request.setup :=
  let progress := seedSchedulerStep_progress hf h
  ⟨progress.1, progress.2.1⟩

open ComputableInSpace in
/-- Initialize a candidate and inspect its scan guard under the caller's input budget. -/
example :
    let E := encPair encSeedSearchSetup encNat
    ComputableInSpace (fun p => (seedSchedulerCandidate p.1 p.2).map
      SeedSchedulerFrame.needsScan) E (encOption encBool) (fun p => (E p).length) := by
  intro E
  have hentry := seedSchedulerCandidate_budget (fst encSeedSearchSetup encNat)
    (snd encSeedSearchSetup encNat)
  have hguard := SeedSchedulerFrame.needsScan_budget
    (budget_id (enc := encSeedSchedulerFrame) (.refl _))
  have hmap := optionElim (encE := encOption encBool) none (budget_optionSome hguard)
  exact (budget_comp_linear hmap hentry).of_enc_eq fun p => by
    cases seedSchedulerCandidate p.1 p.2 <;> rfl

open ComputableInSpace in
/-- The scheduler can advance without a reply within the budget of the live frame. -/
example {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {frame : α → SeedSchedulerFrame}
    (hframe : ComputableInSpace frame enc encSeedSchedulerFrame S) :
    ComputableInSpace (fun a => seedSchedulerStep (frame a) none)
      enc encSeedSchedulerStepResult S :=
  budget_comp_linear seedSchedulerStep_noReply_inSpace hframe

open ComputableInSpace in
/-- The frame and source-loop verdict can arrive from separate producers at a shared budget. -/
example {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {frame : α → SeedSchedulerFrame} {reply : α → Option ControllerVerdict}
    (hframe : ComputableInSpace frame enc encSeedSchedulerFrame S)
    (hreply : ComputableInSpace reply enc
      (encOption Turing.DoubleCounting.SourceRoundLoop.encVerdict) S) :
    ComputableInSpace (fun a => seedSchedulerStep (frame a) (reply a))
      enc encSeedSchedulerStepResult S :=
  budget_comp_linear seedSchedulerStep_inSpace (budget_prod hframe hreply)

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

open Cslib.Code.JustesenFamily ComputableInSpace in
/-- The scheduler's binary request can feed the context adapter under the existing budget. -/
example :
    let encArgs := encPair encSeedSearchSetup (encPair encNat (encOption encNat))
    let E := encPair encArgs encFieldContext
    ComputableInSpace (fun p => justesenSourceContextOfRequest (seedScanRequest p.1) p.2)
      E encJustesenSourceContext (fun p => (E p).length) := by
  intro encArgs E
  exact justesenSourceContextOfRequest_budget
    (budget_comp_linear seedScanRequest_inSpace (fst encArgs encFieldContext))
    (snd encArgs encFieldContext)

/-- Both scheduler entries use the original word's weighted adjacency and designated target.
Only the selected source ID differs. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) (rank position : ℕ) :
    let s := configurationSeedSearchSetup ntm c w
    let field := configurationFieldContext ntm c w
    let designated := justesenSourceContextOfRequest (seedScanRequest (s, rank, none)) field
    let indexed := justesenSourceContextOfRequest (seedScanRequest (s, rank, some position)) field
    designated.adjacency = configurationJustesenSubdivisionContext ntm c w rank ∧
      indexed.adjacency = designated.adjacency ∧
      designated.sourceID = s.sourceID ∧ indexed.sourceID = s.originalSourceID position ∧
      designated.targetID = s.targetID ∧ indexed.targetID = s.targetID := by
  intro s field designated indexed
  dsimp only [designated, indexed]
  rw [← seedSchedulerFrame_designated_request,
    ← seedSchedulerFrame_indexed_request s rank position false]
  exact ⟨justesenSourceContextOfRequest_adjacency_eq ntm c w rank s.sourceID,
    rfl, rfl, rfl, rfl, rfl⟩

end CslibFrontierTests.STCONSeedScheduler
