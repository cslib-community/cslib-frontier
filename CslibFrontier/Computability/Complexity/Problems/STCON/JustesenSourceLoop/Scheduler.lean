/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceContext.Scheduler
public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceLoop
public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler.Correct
public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler.Machine
import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler.Replay
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Retain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute

/-!
# Justesen source loop for scheduler requests

The seed scheduler can start the retained source loop directly from a scan request and the
prepared field context. The entry uses the subdivision's vertex count as fuel and shares the
workspace budget of the request and field producers. A single scheduler machine carries the
prepared field in its state and uses it to start each scan on the original input.

## Main definitions

* `Cslib.Complexity.STCON.justesenSourceLoopEntryOfRequest`: enter the concrete source loop.
* `Cslib.Complexity.STCON.justesenSeedScheduler`: the scheduler with a retained field.
* `Cslib.Complexity.STCON.configurationJustesenSeedSchedulerEntry`: its entry for an original word.

## Main results

* `Cslib.Complexity.STCON.justesenSourceLoopEntryOfRequest_budget`: the full-fuel entry
  uses the shared workspace budget.
* `Cslib.Complexity.STCON.justesenSourceLoopEntryOfRequest_eq`: the scheduler and original-word
  initializers agree at any requested source.
* `Cslib.Complexity.STCON.justesenSeedScheduler_observations_inSpace`:
  query, halt and acceptance in linear workspace in the encoded state.
* `Cslib.Complexity.STCON.justesenSeedScheduler_next_inSpace`:
  a scheduler transition in linear workspace in the encoded state and read/selector input.
* `Cslib.Complexity.STCON.configurationJustesenSeedScheduler_replay`: re-entering the fixed
  scheduler agrees with the scheduler initialized for the original word.
* `Cslib.Complexity.STCON.configurationJustesenSeedSchedulerScan_existsUnique_firstHalting`:
  a valid requested scan has exactly one first-halting selector list returning a verdict.
* `Cslib.Complexity.STCON.configurationJustesenSeedSchedulerScan_readReply_correct`:
  parsed scanner replies give the first tie or the reachability verdict for the requested source.
* `Cslib.Complexity.STCON.configurationJustesenSeedSchedulerScan_firstHalting_eq_reference` and
  `Cslib.Complexity.STCON.configurationJustesenSeedSchedulerScan_readReply_eq_reference`:
  first-halting and parsed replies agree with the mathematical reference callback.
* `Cslib.Complexity.STCON.configurationJustesenSeedScheduler_replay_correct`:
  the unique successful replay returns the least min-isolating seed and decides reachability.
* `Cslib.Complexity.STCON.configurationJustesenSeedSchedulerEntry_inSpace`:
  construct the original-word entry within the logarithmic workspace budget.
* `Cslib.Complexity.STCON.configurationJustesenSeedScheduler_haltsWithin_clock`:
  a common polynomial selector clock for every branch.
* `Cslib.Complexity.STCON.configurationJustesenSeedScheduler_length_run_le_log`:
  logarithmic encoded state length on every selector prefix.
* `Cslib.Complexity.STCON.configurationJustesenSeedScheduler_exists_routines`:
  compile the retained scheduler on the original word with logarithmic space and polynomial time.
* `Cslib.Complexity.STCON.configurationJustesenSeedScheduler_acceptCount`:
  the native accepting count is one exactly on reachable instances and zero otherwise.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily Cslib.DoubleCounting Cslib.Reachability.Hoza
open _root_.Turing _root_.Turing.DoubleCounting
open _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace

/-- Enter the concrete retained round or terminate immediately at zero fuel. -/
@[expose] def justesenSourceLoopEntryOfRequest (request : SeedScanRequest) (field : FieldContext) :
    JustesenSourceLoopState :=
  SourceRoundLoop.enterRound justesenRetainedSourceRoundEntry
    (justesenSourceRegistersOfRequest request field)

/-- The callback entry uses the shared workspace budget of the request and field producers. -/
theorem justesenSourceLoopEntryOfRequest_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {request : α → SeedScanRequest} {field : α → FieldContext}
    (hrequest : ComputableInSpace request enc encSeedScanRequest S)
    (hfield : ComputableInSpace field enc encFieldContext S) :
    ComputableInSpace (fun a => justesenSourceLoopEntryOfRequest (request a) (field a))
      enc encJustesenSourceLoopState S :=
  budget_comp_linear
    (SourceRoundLoop.enterRound_inSpace encJustesenSourceContext encJustesenRetainedSourceRoundState
      (MembershipTally.encRetainedState encJustesenSubdivisionContext encJustesenSubdivisionState)
      justesenRetainedSourceRoundEntry justesenRetainedSourceRoundEntry_inSpace)
    (justesenSourceRegistersOfRequest_budget hrequest hfield)

/-- The scheduler's concrete entry agrees with the original-word initializer at any source. -/
theorem justesenSourceLoopEntryOfRequest_eq {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) (rank source : ℕ) :
    let setup := configurationSeedSearchSetup ntm c w
    justesenSourceLoopEntryOfRequest ⟨setup, rank, source⟩ (configurationFieldContext ntm c w) =
      (justesenSourceLoop ntm c
        ⟨configurationJustesenSubdivisionContext ntm c w rank, source, setup.targetID⟩
        setup.parameters.search.subdivision.vertexCount).init :=
  congrArg (SourceRoundLoop.enterRound justesenRetainedSourceRoundEntry)
    (justesenSourceRegistersOfRequest_eq ntm c w rank source)

/-- The concrete scheduler's scanner uses the source loop's fixed transitions. -/
noncomputable def justesenSeedSchedulerScan {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    NondeterministicQueryMachine JustesenSourceLoopState :=
  justesenSourceLoop ntm c ⟨configurationJustesenSubdivisionContext ntm c [] 0, 0, 0⟩ 0

/-- Run the scheduler for a given setup and prepared field, re-entering the source loop
at the request-specific state for each scan. -/
noncomputable def justesenSeedSchedulerFor {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (setup : SeedSearchSetup) (field : FieldContext) :
    NondeterministicQueryMachine (SeedSchedulerMachine.State JustesenSourceLoopState) :=
  SeedSchedulerMachine.machine setup (justesenSeedSchedulerScan ntm c)
    (fun request => justesenSourceLoopEntryOfRequest request field) SourceRoundLoop.reply

/-- The scheduler retains the prepared field alongside its existing state. -/
abbrev JustesenSeedSchedulerState :=
  FieldContext × SeedSchedulerMachine.State JustesenSourceLoopState

/-- Frame the retained field before the scheduler state. -/
def encJustesenSeedSchedulerState : JustesenSeedSchedulerState ↪ List Bool :=
  encPair encFieldContext (SeedSchedulerMachine.encState encJustesenSourceLoopState)

/-- One query machine for every prepared field and setup. Re-entry supplies the data for
the actual input word. -/
noncomputable def justesenSeedScheduler {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    NondeterministicQueryMachine JustesenSeedSchedulerState :=
  NondeterministicQueryMachine.retain (Equiv.refl _)
    (justesenSeedSchedulerFor ntm c (configurationSeedSearchSetup ntm c []))
    (configurationFieldContext ntm c [])

/-- The fixed scheduler's query, halt and acceptance observations use workspace linear in
the encoded retained state. -/
theorem justesenSeedScheduler_observations_inSpace {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    let E := encJustesenSeedSchedulerState
    let M := justesenSeedScheduler ntm c
    ComputableInSpace M.query E encNat (fun s => (E s).length) ∧
      ComputableInSpace M.halted E encBool (fun s => (E s).length) ∧
      ComputableInSpace M.accept E encBool (fun s => (E s).length) := by
  intro E M
  let setup := configurationSeedSearchSetup ntm c []
  let field := configurationFieldContext ntm c []
  have hscan := (justesenSourceLoop_parts_inSpace ntm c
    ⟨configurationJustesenSubdivisionContext ntm c [] 0, 0, 0⟩ 0).1
  obtain ⟨hq, hh, _, ha⟩ := SeedSchedulerMachine.observations_inSpace
    encJustesenSourceLoopState setup (justesenSeedSchedulerScan ntm c)
    (fun request => justesenSourceLoopEntryOfRequest request field) SourceRoundLoop.reply hscan
  have hstate := snd encFieldContext (SeedSchedulerMachine.encState encJustesenSourceLoopState)
  refine ⟨(budget_comp_linear hq hstate).of_enc_eq ?_,
    (budget_comp_linear hh hstate).of_enc_eq ?_, (budget_comp_linear ha hstate).of_enc_eq ?_⟩ <;>
    rintro ⟨retained, state⟩ <;>
    obtain ⟨hquery, hhalted, haccept⟩ := SeedSchedulerMachine.observations_eq setup setup
      (justesenSeedSchedulerScan ntm c)
      (fun request => justesenSourceLoopEntryOfRequest request retained)
      (fun request => justesenSourceLoopEntryOfRequest request field) SourceRoundLoop.reply
  · exact congrArg encNat (congrFun hquery state)
  · exact congrArg encBool (congrFun hhalted state)
  · exact congrArg encBool (congrFun haccept state)

open NondeterministicQueryMachine in
/-- A step of the fixed scheduler uses linear workspace in the encoded state and read/selector
input. If it enters a scan, the scan uses the field stored in that state. -/
theorem justesenSeedScheduler_next_inSpace {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    let E := encPair encJustesenSeedSchedulerState encReadChoice
    ComputableInSpace (justesenSeedScheduler ntm c).next E encJustesenSeedSchedulerState
      (fun p => (E p).length) := by
  let setup := configurationSeedSearchSetup ntm c []
  let scan := justesenSeedSchedulerScan ntm c
  let encState := SeedSchedulerMachine.encState encJustesenSourceLoopState
  have hstart := justesenSourceLoopEntryOfRequest_budget
    (fst encSeedScanRequest encFieldContext) (snd encSeedScanRequest encFieldContext)
  obtain ⟨_, hnext, hhalt, hreply⟩ := justesenSourceLoop_parts_inSpace ntm c
    ⟨configurationJustesenSubdivisionContext ntm c [] 0, 0, 0⟩ 0
  have hstep := SeedSchedulerMachine.next_withContext_inSpace encFieldContext
    encJustesenSourceLoopState setup scan (fun p => justesenSourceLoopEntryOfRequest p.1 p.2)
    SourceRoundLoop.reply hstart hhalt hreply hnext
  have hstate := fst encJustesenSeedSchedulerState encReadChoice
  have hfield := budget_comp_linear (fst encFieldContext encState) hstate
  have hinner := budget_comp_linear (snd encFieldContext encState) hstate
  have hinput := snd encJustesenSeedSchedulerState encReadChoice
  have hnextInner := budget_comp_linear hstep (budget_prod hinner (budget_prod hfield hinput))
  exact (budget_prod hfield hnextInner).of_enc_eq fun ⟨⟨_, _⟩, _⟩ => rfl

/-- Enter candidate zero with the setup and retained field computed on the original word. -/
noncomputable def configurationJustesenSeedSchedulerEntry {k : ℕ} {State : Type}
    [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    JustesenSeedSchedulerState :=
  let field := configurationFieldContext ntm c w
  (field, (justesenSeedSchedulerFor ntm c (configurationSeedSearchSetup ntm c w) field).init)

/-- The fixed scheduler's original-word entry uses logarithmic workspace and charges its
encoded output, including the retained field. -/
theorem configurationJustesenSeedSchedulerEntry_inSpace {k : ℕ} {State : Type}
    [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ComputableInSpace (configurationJustesenSeedSchedulerEntry ntm c)
      encBits encJustesenSeedSchedulerState (fun w => Nat.log2 w.length + 1) := by
  have hbudget (w : List Bool) : Nat.log2 (encBits w).length ≤ Nat.log2 w.length + 1 := by
    simpa only [encBits_apply] using Nat.le_succ (Nat.log2 w.length)
  have hsetup := ((configurationSeedSearchSetup_inLogSpace ntm c).inSpace_of_length_log
    (by simpa only [encBits_apply] using length_configurationSeedSearchSetup_le_log ntm c)).mono_le
      hbudget
  have hfield := ((configurationFieldContext_inLogSpace ntm c).inSpace_of_length_log
    (by simpa only [encBits_apply] using length_configurationFieldContext_le_log ntm c)).mono_le
      hbudget
  have hstart := justesenSourceLoopEntryOfRequest_budget
    (fst encSeedScanRequest encFieldContext) (snd encSeedScanRequest encFieldContext)
  have hinit := SeedSchedulerMachine.init_withContext_budget encFieldContext
    encJustesenSourceLoopState (justesenSeedSchedulerScan ntm c)
    (fun p => justesenSourceLoopEntryOfRequest p.1 p.2) SourceRoundLoop.reply hstart hsetup hfield
  exact budget_prod hfield hinit

/-- Every selector replay from an original-word entry retains the field and agrees with
the scheduler initialized directly for that word, including rejected replays. -/
theorem configurationJustesenSeedScheduler_replay {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w bits : List Bool) :
    let field := configurationFieldContext ntm c w
    (justesenSeedScheduler ntm c).replay w bits
      (configurationJustesenSeedSchedulerEntry ntm c w) =
      (field, (justesenSeedSchedulerFor ntm c (configurationSeedSearchSetup ntm c w) field).run
        w bits) := by
  intro field
  let empty := configurationSeedSearchSetup ntm c []
  let setup := configurationSeedSearchSetup ntm c w
  let family := justesenSeedSchedulerFor ntm c empty
  let entered := justesenSeedSchedulerFor ntm c setup field
  let e := Equiv.refl JustesenSeedSchedulerState
  change (NondeterministicQueryMachine.retain e family (configurationFieldContext ntm c [])).replay
    w bits (e.symm (field, entered.init)) = (field, entered.run w bits)
  rw [NondeterministicQueryMachine.replay_retain]
  have hentry : (family field).withInit entered.init = entered :=
    SeedSchedulerMachine.machine_withInit empty setup (justesenSeedSchedulerScan ntm c)
      (fun request => justesenSourceLoopEntryOfRequest request field) SourceRoundLoop.reply
  exact congrArg (fun M : NondeterministicQueryMachine _ => (field, M.run w bits)) hentry

private theorem justesenSeedSchedulerScan_withInit_of_valid {k : ℕ} {State : Type}
    [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool)
    (f : SeedSchedulerFrame) (hs : f.request.setup = configurationSeedSearchSetup ntm c w)
    (hv : f.Valid) :
    let I := configurationInstance ntm c w
    let setup := configurationSeedSearchSetup ntm c w
    let n := setup.parameters.search.subdivision.vertexCount
    ∃ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source : Fin n),
      seed.val = f.request.seed ∧ source.val = f.request.sourceID ∧
      (justesenSeedSchedulerScan ntm c).withInit
        (justesenSourceLoopEntryOfRequest f.request (configurationFieldContext ntm c w)) =
        justesenSourceLoop ntm c
          ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, setup.targetID⟩
          n := by
  intro I setup n
  rcases f with ⟨⟨saved, rank, source⟩, cursor, answer⟩
  obtain rfl : saved = setup := hs
  have hrank : rank < setup.parameters.search.seedLimit := hv.seed_lt
  rw [configurationSeedScheduler_seedLimit ntm c w,
    (configurationSeedSearchSetup_endpoints ntm c w).1] at hrank
  have hends := configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w
  have hroot := fun j hj => configurationSeedSearchSetup_originalSourceID_lt_vertexCount
    ntm c w (position := j) hj
  have hsource : source < n := hv.source_lt hends.1 hroot
  exact ⟨⟨rank, hrank⟩, ⟨source, hsource⟩, rfl, rfl,
    (justesenSourceLoopEntryOfRequest_eq ntm c w rank source).symm ▸
      justesenSourceLoop_withInit ntm c _ _ 0 n⟩

/-- A valid scheduler frame has exactly one scanner trace that first halts with a verdict.
A tie and either Boolean reachability verdict are successful returns. -/
theorem configurationJustesenSeedSchedulerScan_existsUnique_firstHalting
    {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (w : List Bool) (frame : SeedSchedulerFrame)
    (hsetup : frame.request.setup = configurationSeedSearchSetup ntm c w) (hvalid : frame.Valid) :
    let scan := justesenSeedSchedulerScan ntm c
    let entry := justesenSourceLoopEntryOfRequest frame.request (configurationFieldContext ntm c w)
    ∃! bits, scan.FirstHalting w bits entry ∧
      (SourceRoundLoop.reply (scan.replay w bits entry)).isSome := by
  intro scan entry
  obtain ⟨seed, source, _, _, hreenter⟩ :=
    justesenSeedSchedulerScan_withInit_of_valid ntm c w frame hsetup hvalid
  let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
  let target : Fin n := ⟨(configurationSeedSearchSetup ntm c w).targetID,
    (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w).2⟩
  let context : JustesenSourceContext :=
    ⟨configurationJustesenSubdivisionContext ntm c w seed.val, source.val, target.val⟩
  let loop := justesenSourceLoop ntm c context n
  let entered := scan.withInit entry
  change entered = loop at hreenter
  change ∃! bits, entered.FirstHalting w bits entered.init ∧
    (SourceRoundLoop.reply (entered.run w bits)).isSome
  rw [hreenter]
  exact (existsUnique_congr (justesenSourceLoop_firstHalting_reply_iff ntm c context n w)).mpr
    (configurationJustesenSourceLoop_existsUnique_firstHalting ntm c w seed source target)

private theorem configurationJustesenSeedSchedulerScan_firstHalting_correct
    {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (w : List Bool) (frame : SeedSchedulerFrame)
    (hsetup : frame.request.setup = configurationSeedSearchSetup ntm c w) (hvalid : frame.Valid)
    (bits : List Bool) (verdict : ControllerVerdict) :
    let scan := justesenSeedSchedulerScan ntm c
    let entry := justesenSourceLoopEntryOfRequest frame.request (configurationFieldContext ntm c w)
    scan.FirstHalting w bits entry →
    SourceRoundLoop.reply (scan.replay w bits entry) = some verdict →
    let I := configurationInstance ntm c w
    let setup := configurationSeedSearchSetup ntm c w
    let n := setup.parameters.search.subdivision.vertexCount
    let target : Fin n := ⟨setup.targetID,
      (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w).2⟩
    let edge := generatedSubdivisionAdj (layeredDigraph I)
      (configurationSubdivisionIndex ntm c w)
      (fun j => frame.request.seed.testBit j.val)
    ∃ source : Fin n, source.val = frame.request.sourceID ∧
      verdict.Correct edge source target := by
  intro scan entry hfirst hret I setup n target edge
  obtain ⟨seed, source, hseed, hsource, hreenter⟩ :=
    justesenSeedSchedulerScan_withInit_of_valid ntm c w frame hsetup hvalid
  have hrun : (scan.withInit entry).run w bits = .inr (some verdict) := by
    rw [NondeterministicQueryMachine.run_withInit]
    revert hret
    cases scan.replay w bits entry <;> simp [SourceRoundLoop.reply]
  change (scan.withInit entry).FirstHalting w bits (scan.withInit entry).init at hfirst
  rw [hreenter] at hfirst hrun
  have hcorrect := configurationJustesenSourceLoop_correct ntm c w seed source target
    bits verdict hfirst hrun
  refine ⟨source, hsource, ?_⟩
  have hbits : (Cslib.BitString.equivFin _).symm seed =
      fun j => frame.request.seed.testBit j.val :=
    funext fun j => by rw [Cslib.BitString.equivFin_symm_apply, hseed]
  simpa only [configurationJustesenSubdivisionAdjacent, decide_eq_true_eq, hbits] using hcorrect

/-- A parsed scanner reply gives the first radius without a unique passing transcript,
or gives the correct reachability answer with unique transcripts at every radius.
The graph uses the seed rank and source recorded by the scheduler frame. -/
theorem configurationJustesenSeedSchedulerScan_readReply_correct
    {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (w : List Bool) (frame : SeedSchedulerFrame)
    (hsetup : frame.request.setup = configurationSeedSearchSetup ntm c w) (hvalid : frame.Valid)
    (bits rest : List Bool) (verdict : ControllerVerdict)
    (hreply : (justesenSeedSchedulerScan ntm c).readReply SourceRoundLoop.reply w
      (justesenSourceLoopEntryOfRequest frame.request (configurationFieldContext ntm c w))
      bits = some (verdict, rest)) :
    let I := configurationInstance ntm c w
    let setup := configurationSeedSearchSetup ntm c w
    let n := setup.parameters.search.subdivision.vertexCount
    let target : Fin n := ⟨setup.targetID,
      (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w).2⟩
    let edge := generatedSubdivisionAdj (layeredDigraph I)
      (configurationSubdivisionIndex ntm c w)
      (fun j => frame.request.seed.testBit j.val)
    ∃ source : Fin n, source.val = frame.request.sourceID ∧
      verdict.Correct edge source target := by
  obtain ⟨trace, _, hfirst, hret⟩ := (NondeterministicQueryMachine.readReply_iff
    (justesenSeedSchedulerScan ntm c) SourceRoundLoop.reply w bits
    (justesenSourceLoopEntryOfRequest frame.request (configurationFieldContext ntm c w))
    verdict rest).mp hreply
  exact configurationJustesenSeedSchedulerScan_firstHalting_correct
    ntm c w frame hsetup hvalid trace verdict hfirst hret

/-- A scanner's first-halting trace and decoded verdict agree with the mathematical
reference callback on the same request. -/
theorem configurationJustesenSeedSchedulerScan_firstHalting_eq_reference
    {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (w : List Bool) (frame : SeedSchedulerFrame)
    (hsetup : frame.request.setup = configurationSeedSearchSetup ntm c w) (hvalid : frame.Valid)
    (bits : List Bool) (verdict : ControllerVerdict) :
    let scan := justesenSeedSchedulerScan ntm c
    let entry := justesenSourceLoopEntryOfRequest frame.request (configurationFieldContext ntm c w)
    scan.FirstHalting w bits entry →
    SourceRoundLoop.reply (scan.replay w bits entry) = some verdict →
    configurationSeedSchedulerReferenceScan ntm c w frame.request = some verdict := by
  intro _ _ hfirst hret
  obtain ⟨source, hsource, hcorrect⟩ :=
    configurationJustesenSeedSchedulerScan_firstHalting_correct ntm c w frame hsetup hvalid
      bits verdict hfirst hret
  obtain ⟨reference, hscan, href⟩ :=
    configurationSeedSchedulerReferenceScan_correct ntm c w frame.request
      (hsource ▸ source.isLt)
  have heq : source = ⟨frame.request.sourceID, hsource ▸ source.isLt⟩ := Fin.ext hsource
  rw [hscan, href.eq (heq ▸ hcorrect)]

/-- Every parsed concrete scan reply agrees with the mathematical reference callback. -/
theorem configurationJustesenSeedSchedulerScan_readReply_eq_reference
    {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (w : List Bool) (frame : SeedSchedulerFrame)
    (hsetup : frame.request.setup = configurationSeedSearchSetup ntm c w) (hvalid : frame.Valid)
    (bits rest : List Bool) (verdict : ControllerVerdict)
    (hreply : (justesenSeedSchedulerScan ntm c).readReply SourceRoundLoop.reply w
      (justesenSourceLoopEntryOfRequest frame.request (configurationFieldContext ntm c w))
      bits = some (verdict, rest)) :
    configurationSeedSchedulerReferenceScan ntm c w frame.request = some verdict := by
  obtain ⟨trace, _, hfirst, hret⟩ := (NondeterministicQueryMachine.readReply_iff
    (justesenSeedSchedulerScan ntm c) SourceRoundLoop.reply w bits
    (justesenSourceLoopEntryOfRequest frame.request (configurationFieldContext ntm c w))
    verdict rest).mp hreply
  exact configurationJustesenSeedSchedulerScan_firstHalting_eq_reference
    ntm c w frame hsetup hvalid trace verdict hfirst hret

/-- On the original input, exactly one first-halting scheduler replay returns a result.
That result selects the least min-isolating rank and decides the STCON instance, including
when the designated target is unreachable. -/
theorem configurationJustesenSeedScheduler_replay_correct
    {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let setup := configurationSeedSearchSetup ntm c w
    let M := justesenSeedScheduler ntm c
    let entry := configurationJustesenSeedSchedulerEntry ntm c w
    let reply := fun bits => SeedSchedulerMachine.reply (M.replay w bits entry).2
    ∃ (answer : SeedSchedulerMachine.Answer) (bits : List Bool),
      answer.seed < setup.parameters.search.seedLimit ∧
      (layeredDigraph I).IsMinIsolating (generatedWeight (fun j => answer.seed.testBit j.val)) ∧
      (∀ i : Fin (2 ^ setup.parameters.search.seedWidth), i.val < answer.seed →
        ¬ (layeredDigraph I).IsMinIsolating (generatedWeight (fun j => i.val.testBit j.val))) ∧
      (answer.reachable = true ↔ I ∈ STCON) ∧
      M.FirstHalting w bits entry ∧ reply bits = some (some answer) ∧
      ∀ other, M.FirstHalting w other entry → (reply other).isSome → other = bits := by
  intro I setup M entry reply
  let field := configurationFieldContext ntm c w
  let scan := justesenSeedSchedulerScan ntm c
  let start := fun r => justesenSourceLoopEntryOfRequest r field
  let entered := justesenSeedSchedulerFor ntm c setup field
  let empty := configurationSeedSearchSetup ntm c []
  let family := justesenSeedSchedulerFor ntm c empty
  let oracle := fun r => [configurationSeedSchedulerReferenceScan ntm c w r]
  have hspec (f : SeedSchedulerFrame) (hs : f.request.setup = setup) (hv : f.Valid) :
      ∃! bits, scan.FirstHalting w bits (start f.request) ∧
        (SourceRoundLoop.reply (scan.replay w bits (start f.request))).isSome :=
    configurationJustesenSeedSchedulerScan_existsUnique_firstHalting ntm c w f hs hv
  obtain ⟨bits, hfirst, hresult⟩ :=
    SeedSchedulerMachine.exists_successful_firstHalting setup scan start SourceRoundLoop.reply w
      (fun f hs hv _ => (hspec f hs hv).exists)
  have hunique :=
    SeedSchedulerMachine.subsingleton_successful_firstHalting setup scan start
      SourceRoundLoop.reply w fun f hs hv _ _ hl _ hr => (hspec f hs hv).unique hl hr
  obtain ⟨answer, hanswer⟩ := Option.isSome_iff_exists.mp hresult
  obtain ⟨actual, hactual, hpack⟩ := SeedSchedulerMachine.runSeedSchedulerFor_eq_of_firstHalting
    setup (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w).1
    (fun _ hp => configurationSeedSearchSetup_originalSourceID_lt_vertexCount ntm c w hp)
    (configurationSeedScheduler_seedLimit ntm c w) scan start SourceRoundLoop.reply w oracle
    (fun f hs hv _ trace value hhalt hret => congrArg (fun x => [x])
      (configurationJustesenSeedSchedulerScan_firstHalting_eq_reference
        ntm c w f hs hv trace value hhalt hret))
    bits answer hfirst hanswer
  obtain ⟨result, hmath, hmin, hleast, hreach⟩ :=
    configurationSeedSchedulerReference_correct ntm c w
  obtain rfl : actual = some result := List.singleton_inj.mp (hactual.symm.trans hmath)
  let selected : SeedSchedulerMachine.Answer := ⟨result.seed.val, result.reachable⟩
  obtain rfl : answer = some selected := hpack.symm
  have hhalt (trace : List Bool) :
      M.FirstHalting w trace entry ↔ entered.FirstHalting w trace entered.init := by
    let e := Equiv.refl JustesenSeedSchedulerState
    change (NondeterministicQueryMachine.retain e family
      (configurationFieldContext ntm c [])).FirstHalting w trace (e.symm (field, entered.init)) ↔ _
    have hinit : (family field).withInit entered.init = entered :=
      SeedSchedulerMachine.machine_withInit empty setup scan start SourceRoundLoop.reply
    rw [NondeterministicQueryMachine.firstHalting_retain,
      ← (family field).firstHalting_withInit entered.init, hinit]
  have hreply (trace : List Bool) :
      reply trace = SeedSchedulerMachine.reply (entered.run w trace) :=
    congrArg (fun s => SeedSchedulerMachine.reply s.2)
      (configurationJustesenSeedScheduler_replay ntm c w trace)
  have hseed : selected.seed < setup.parameters.search.seedLimit :=
    (configurationSeedScheduler_seedLimit ntm c w).symm ▸ result.seed.isLt
  exact ⟨selected, bits, hseed, hmin, hleast, hreach, (hhalt bits).mpr hfirst,
    (hreply bits).trans hanswer, fun other hother hr =>
      hunique ⟨(hhalt other).mp hother, hreply other ▸ hr⟩ ⟨hfirst, hresult⟩⟩

/-- Every selector prefix of the fixed retained-field scheduler fits in logarithmically
many bits in the original input length, including replays that reject. -/
theorem configurationJustesenSeedScheduler_length_run_le_log {k : ℕ} {State : Type}
    [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w bits : List Bool, (encJustesenSeedSchedulerState
      ((justesenSeedScheduler ntm c).replay w bits
        (configurationJustesenSeedSchedulerEntry ntm c w))).length ≤
          C * (Nat.log2 w.length + 1) := by
  obtain ⟨F, hfield⟩ := length_configurationFieldContext_le_log ntm c
  obtain ⟨A, hsetup⟩ := length_configurationSeedSearchSetup_le_log ntm c
  obtain ⟨B, hscan⟩ := configurationJustesenSourceLoop_length_run_le_log ntm c
  refine ⟨2 * F + 24 * A + B + 22, fun w bits => ?_⟩
  let setup := configurationSeedSearchSetup ntm c w
  let field := configurationFieldContext ntm c w
  let bound := Nat.log2 w.length + 1
  let n := setup.parameters.search.subdivision.vertexCount
  let scan := justesenSeedSchedulerScan ntm c
  let start := fun r => justesenSourceLoopEntryOfRequest r field
  have hends := configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w
  have hroot := fun j hj => configurationSeedSearchSetup_originalSourceID_lt_vertexCount
    ntm c w (position := j) hj
  have hcap (f : SeedSchedulerFrame) (hs : f.request.setup = setup)
      (hv : f.Valid)
      (_ : f.needsScan = true) (choices : List Bool) :
      (encJustesenSourceLoopState (scan.replay w choices (start f.request))).length ≤
        B * bound := by
    obtain ⟨seed, source, _, _, hreenter⟩ :=
      justesenSeedSchedulerScan_withInit_of_valid ntm c w f hs hv
    have h := hscan w seed source ⟨setup.targetID, hends.2⟩ n le_rfl choices
    rw [← hreenter] at h
    exact h
  have hmachine := SeedSchedulerMachine.length_run_le setup scan start SourceRoundLoop.reply
    encJustesenSourceLoopState w (B * bound) hends.1 hroot hcap bits
  rw [configurationJustesenSeedScheduler_replay ntm c w bits]
  change (encPair encFieldContext (SeedSchedulerMachine.encState encJustesenSourceLoopState)
    (field, (justesenSeedSchedulerFor ntm c setup field).run w bits)).length ≤ _
  rw [length_encPair]
  have hF : (encFieldContext field).length ≤ F * bound := hfield w
  have hA : (encSeedSearchSetup setup).length ≤ A * bound := hsetup w
  have hM : (SeedSchedulerMachine.encState encJustesenSourceLoopState
      ((justesenSeedSchedulerFor ntm c setup field).run w bits)).length ≤
        24 * (encSeedSearchSetup setup).length + B * bound + 21 := hmachine
  have hconst : 22 ≤ 22 * bound := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  change _ ≤ (2 * F + 24 * A + B + 22) * bound
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

/-- Charge the full-fuel scan and one return selector at each designated or indexed frame. -/
noncomputable def configurationJustesenSeedSchedulerClock {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) : ℕ :=
  let size := (configurationSeedSearchSetup ntm c w).parameters.search
  size.seedLimit * ((1 + size.subdivision.originalCount) *
    (configurationJustesenSourceLoopClock ntm c w + 1))

/-- The scheduler's selector clock is polynomial in the original word length. -/
theorem configurationJustesenSeedSchedulerClock_polyBounded {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (configurationJustesenSeedSchedulerClock ntm c) :=
  configurationSeedScheduler_clock_polyBounded ntm c
    ((configurationJustesenSourceLoopClock_polyBounded ntm c).add (.const 1))

/-- Every scheduler branch, including rejection and either designated answer, halts within
the common clock at the original-word entry. -/
theorem configurationJustesenSeedScheduler_haltsWithin_clock {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    NondeterministicQueryMachine.HaltsWithin
      ((justesenSeedScheduler ntm c).withInit (configurationJustesenSeedSchedulerEntry ntm c w))
      w (configurationJustesenSeedSchedulerClock ntm c w) := by
  let setup := configurationSeedSearchSetup ntm c w
  let empty := configurationSeedSearchSetup ntm c []
  let field := configurationFieldContext ntm c w
  let scan := justesenSeedSchedulerScan ntm c
  let start := fun r => justesenSourceLoopEntryOfRequest r field
  let clock := configurationJustesenSourceLoopClock ntm c w
  have hends := configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w
  have hscan (f : SeedSchedulerFrame) (hs : f.request.setup = setup) (hv : f.Valid)
      (_ : f.needsScan = true) : (scan.withInit (start f.request)).HaltsWithin w clock := by
    obtain ⟨seed, source, _, _, hreenter⟩ :=
      justesenSeedSchedulerScan_withInit_of_valid ntm c w f hs hv
    change NondeterministicQueryMachine.HaltsWithin ((justesenSeedSchedulerScan ntm c).withInit
      (justesenSourceLoopEntryOfRequest f.request (configurationFieldContext ntm c w))) w clock
    rw [hreenter]
    exact configurationJustesenSourceLoop_haltsWithin_clock ntm c w
      seed source ⟨setup.targetID, hends.2⟩ _ le_rfl
  have hscheduler := SeedSchedulerMachine.haltsWithin setup scan start SourceRoundLoop.reply
    w clock hscan
  intro bits hlen
  rw [NondeterministicQueryMachine.run_withInit,
    configurationJustesenSeedScheduler_replay ntm c w bits]
  change (justesenSeedSchedulerFor ntm c empty field).halted
    ((justesenSeedSchedulerFor ntm c setup field).run w bits) = true
  have hhalt := congrArg NondeterministicQueryMachine.halted
    (SeedSchedulerMachine.machine_withInit empty setup scan start SourceRoundLoop.reply)
  change (justesenSeedSchedulerFor ntm c empty field).halted =
    (justesenSeedSchedulerFor ntm c setup field).halted at hhalt
  rw [hhalt]
  exact hscheduler bits hlen

open NondeterministicQueryMachine in
/-- Compile the fixed retained-field scheduler on the original input. All native
branches use logarithmic visited-cell space and stop within a uniform polynomial clock. -/
theorem configurationJustesenSeedScheduler_exists_routines {k : ℕ} {State : Type}
    [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    let M := justesenSeedScheduler ntm c
    let entry := configurationJustesenSeedSchedulerEntry ntm c
    let S := fun w : List Bool => Nat.log2 w.length + 1
    ∃ R : Routines M entry encBits S, ∃ L d, ∀ w,
      R.machine.RunsInSpace w (L * S w) ∧ R.machine.RunsInTime w (polyClock d w.length) := by
  intro M entry S
  obtain ⟨hq, hh, ha⟩ := justesenSeedScheduler_observations_inSpace ntm c
  obtain ⟨C, hprefix⟩ := configurationJustesenSeedScheduler_length_run_le_log ntm c
  obtain ⟨R⟩ : Nonempty (Routines M entry encBits S) :=
    M.exists_routines hq (justesenSeedScheduler_next_inSpace ntm c) hh ha entry S
      (fun w => by simp only [encBits_apply, S, le_refl])
      (configurationJustesenSeedSchedulerEntry_inSpace ntm c)
      ⟨C, fun w bits => by simpa only [run_withInit, encBits_apply] using hprefix w bits⟩
  obtain ⟨L, d, hbounds⟩ := R.exists_logSpace_polyClock
    (time := configurationJustesenSeedSchedulerClock ntm c)
    (fun w => by simpa only [encBits_apply] using
      configurationJustesenSeedScheduler_haltsWithin_clock ntm c w)
  exact ⟨R, L, d, fun w => by simpa only [encBits_apply] using hbounds w⟩

open Classical NondeterministicQueryMachine in
/-- The compiled scheduler has one accepting occurrence when the configuration target is
reachable, and zero otherwise, at any clock sufficient for all native branches. -/
theorem configurationJustesenSeedScheduler_acceptCount {k : ℕ} {State : Type}
    [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (R : Routines (justesenSeedScheduler ntm c) (configurationJustesenSeedSchedulerEntry ntm c)
      encBits (fun w => Nat.log2 w.length + 1))
    (w : List Bool) {clock : ℕ} (hclock : R.machine.RunsInTime w clock) :
    (Native.countingMachine R.I R.P R.F R.C).acceptCount clock (R.machine.initCfg w) =
      if configurationInstance ntm c w ∈ STCON then 1 else 0 := by
  let I := configurationInstance ntm c w
  let M := justesenSeedScheduler ntm c
  let entry := configurationJustesenSeedSchedulerEntry ntm c w
  let reply (trace : List Bool) := SeedSchedulerMachine.reply (M.replay w trace entry).2
  obtain ⟨answer, bits, _, _, _, hreach, hfirst, hreply, hunique⟩ :=
    configurationJustesenSeedScheduler_replay_correct ntm c w
  have haccept (trace : List Bool) : M.accept (M.replay w trace entry) = true ↔
      ∃ a, reply trace = some (some a) ∧ a.reachable = true := by
    let final := M.replay w trace entry
    exact SeedSchedulerMachine.machine_accept_iff (configurationSeedSearchSetup ntm c [])
      (justesenSeedSchedulerScan ntm c) (fun r => justesenSourceLoopEntryOfRequest r final.1)
      SourceRoundLoop.reply final.2
  have htrace (trace : List Bool) :
      (M.FirstHalting w trace entry ∧ M.accept (M.replay w trace entry) = true) ↔
        trace = bits ∧ I ∈ STCON := by
    rw [haccept]
    constructor
    · rintro ⟨hhalt, a, ha, hhit⟩
      obtain rfl := hunique trace hhalt (Option.isSome_iff_exists.mpr ⟨_, ha⟩)
      obtain rfl : a = answer := Option.some.inj (Option.some.inj (ha.symm.trans hreply))
      exact ⟨rfl, hreach.mp hhit⟩
    · rintro ⟨rfl, hmem⟩
      exact ⟨hfirst, answer, hreply, hreach.mpr hmem⟩
  have hset : {trace : List Bool |
      M.FirstHalting w trace entry ∧ M.accept (M.replay w trace entry) = true} =
        if I ∈ STCON then {bits} else ∅ := by
    ext trace
    rw [Set.mem_ofPred_eq, htrace]
    by_cases h : I ∈ STCON <;> simp [h]
  rw [← Nat.cast_inj (R := ℕ∞)]
  calc
    _ = {trace : List Bool |
        M.FirstHalting w trace entry ∧ M.accept (M.replay w trace entry) = true}.encard :=
      R.acceptCount_eq_encard_firstHalting w hclock
    _ = _ := by
      rw [hset]
      change (if I ∈ STCON then ({bits} : Set (List Bool)) else ∅).encard =
        ↑(if I ∈ STCON then (1 : ℕ) else 0)
      by_cases hmem : I ∈ STCON <;> simp [hmem]

end Cslib.Complexity.STCON
