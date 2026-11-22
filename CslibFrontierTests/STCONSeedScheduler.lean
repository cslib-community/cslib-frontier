/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceLoop.Scheduler
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
meta import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler

/-! Ordinary-import clients for the binary seed and source scheduler. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONSeedScheduler

open Cslib.Complexity.STCON Cslib.DoubleCounting
open Turing Turing.DoubleCounting Turing.MultiTapeTM

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

-- A terminal native transition retains the designated negative answer after a positive reply.
example (scan : SeedScanRequest → List (Option ControllerVerdict))
    (hscan : scan ⟨setup, 1, setup.originalSourceID 1⟩ = [some (.decided true)]) :
    runSeedSchedulerForFrom setup sourceValid rootValid scan 1 (some (1, false)) =
      [some ⟨1, false⟩] := by
  let frame := seedSchedulerFrame setup 1 (some (1, false)) (setup.originalSourceID 1)
  have hvalid : frame.Valid := seedSchedulerFrame_indexed_valid setup (by decide) (by decide) false
  have hlast :
      ¬frame.cursor + 1 < frame.request.setup.parameters.search.subdivision.originalCount :=
    by decide
  have hstep : seedSchedulerStep frame (some (.decided true)) = some (.inr (some false)) := by
    simpa only [ite_eq_right hlast] using seedSchedulerStep_indexed_decided frame rfl true
  exact runSeedSchedulerForFrom_step setup sourceValid rootValid scan rfl hvalid rfl hstep
    (by intro value hv _; cases hv; exact hscan)

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

open Cslib.Code.JustesenFamily ComputableInSpace in
/-- The scheduler's request and field can enter the concrete loop at the same budget. -/
example :
    let encArgs := encPair encSeedSearchSetup (encPair encNat (encOption encNat))
    let E := encPair encArgs encFieldContext
    ComputableInSpace (fun p => justesenSourceLoopEntryOfRequest (seedScanRequest p.1) p.2)
      E encJustesenSourceLoopState (fun p => (E p).length) := by
  intro encArgs E
  exact justesenSourceLoopEntryOfRequest_budget
    (budget_comp_linear seedScanRequest_inSpace (fst encArgs encFieldContext))
    (snd encArgs encFieldContext)

open ComputableInSpace Turing.NondeterministicQueryMachine in
/-- The scheduler can call all four operations within the budget of its live state and selector. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    (context : JustesenSourceContext) (limit : ℕ)
    {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {state : α → JustesenSourceLoopState} {choice : α → Option Bool × Bool}
    (hstate : ComputableInSpace state enc encJustesenSourceLoopState S)
    (hchoice : ComputableInSpace choice enc encReadChoice S) :
    let M := justesenSourceLoop ntm c context limit
    ComputableInSpace (fun a => M.query (state a)) enc encNat S ∧
      ComputableInSpace (fun a => M.next (state a, choice a)) enc encJustesenSourceLoopState S ∧
      ComputableInSpace (fun a => M.halted (state a)) enc encBool S ∧
      ComputableInSpace (fun a => SourceRoundLoop.reply (state a)) enc
        (encOption SourceRoundLoop.encVerdict) S := by
  obtain ⟨hq, hn, hh, hr⟩ := justesenSourceLoop_parts_inSpace ntm c context limit
  exact ⟨budget_comp_linear hq hstate, budget_comp_linear hn (budget_prod hstate hchoice),
    budget_comp_linear hh hstate, budget_comp_linear hr hstate⟩

/-- The designated and indexed scheduler requests enter the original-word native loop. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) (rank position : ℕ) :
    let s := configurationSeedSearchSetup ntm c w
    let n := s.parameters.search.subdivision.vertexCount
    let field := configurationFieldContext ntm c w
    let adj := configurationJustesenSubdivisionContext ntm c w rank
    justesenSourceLoopEntryOfRequest (seedScanRequest (s, rank, none)) field =
      (justesenSourceLoop ntm c ⟨adj, s.sourceID, s.targetID⟩ n).init ∧
    justesenSourceLoopEntryOfRequest (seedScanRequest (s, rank, some position)) field =
      (justesenSourceLoop ntm c ⟨adj, s.originalSourceID position, s.targetID⟩ n).init := by
  intro s n field adj
  rw [← seedSchedulerFrame_designated_request,
    ← seedSchedulerFrame_indexed_request s rank position false]
  exact ⟨justesenSourceLoopEntryOfRequest_eq ntm c w rank s.sourceID,
    justesenSourceLoopEntryOfRequest_eq ntm c w rank (s.originalSourceID position)⟩

/-- The fixed machine preserves the initialized field and returns the initialized scheduler's
terminal observation on the original word. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w bits : List Bool) :
    let field := configurationFieldContext ntm c w
    let setup := configurationSeedSearchSetup ntm c w
    let endState := (justesenSeedScheduler ntm c).replay w bits
      (configurationJustesenSeedSchedulerEntry ntm c w)
    endState.1 = field ∧
      SeedSchedulerMachine.reply endState.2 =
        SeedSchedulerMachine.reply ((justesenSeedSchedulerFor ntm c setup field).run w bits) := by
  intro field setup endState
  have h := configurationJustesenSeedScheduler_replay ntm c w bits
  exact ⟨congrArg Prod.fst h, congrArg (fun q => SeedSchedulerMachine.reply q.2) h⟩

/-- The same clock bounds the fixed scheduler at every original-word entry. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    PolyBounded List.length (configurationJustesenSeedSchedulerClock ntm c) ∧
      NondeterministicQueryMachine.HaltsWithin
        ((justesenSeedScheduler ntm c).withInit (configurationJustesenSeedSchedulerEntry ntm c w))
        w (configurationJustesenSeedSchedulerClock ntm c w) :=
  ⟨configurationJustesenSeedSchedulerClock_polyBounded ntm c,
    configurationJustesenSeedScheduler_haltsWithin_clock ntm c w⟩

/-- Candidate zero has one designated scan trace returning the reference verdict. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) (frame : SeedSchedulerFrame)
    (h : seedSchedulerCandidate (configurationSeedSearchSetup ntm c w) 0 = some frame) :
    let scan := justesenSeedSchedulerScan ntm c
    let entry := justesenSourceLoopEntryOfRequest frame.request (configurationFieldContext ntm c w)
    (∃! bits, scan.FirstHalting w bits entry ∧
      (SourceRoundLoop.reply (scan.replay w bits entry)).isSome) ∧
    ∃ bits verdict, scan.FirstHalting w bits entry ∧
      SourceRoundLoop.reply (scan.replay w bits entry) = some verdict ∧
      configurationSeedSchedulerReferenceScan ntm c w frame.request = some verdict := by
  obtain ⟨hvalid, hsetup, _⟩ := seedSchedulerCandidate_valid h
  have htrace := configurationJustesenSeedSchedulerScan_existsUnique_firstHalting
    ntm c w frame hsetup hvalid
  obtain ⟨bits, hfirst, hsome⟩ := htrace.exists
  obtain ⟨verdict, hreply⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨htrace, bits, verdict, hfirst, hreply,
    configurationJustesenSeedSchedulerScan_firstHalting_eq_reference
      ntm c w frame hsetup hvalid bits verdict hfirst hreply⟩

/-- A negative reply at candidate zero matches the mathematical scanner and rules out a path
to the setup's target in the subdivision for the all-zero seed. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w bits rest : List Bool) (frame : SeedSchedulerFrame)
    (hcandidate : seedSchedulerCandidate (configurationSeedSearchSetup ntm c w) 0 = some frame)
    (hreply : (justesenSeedSchedulerScan ntm c).readReply SourceRoundLoop.reply w
      (justesenSourceLoopEntryOfRequest frame.request (configurationFieldContext ntm c w))
      bits = some (.decided false, rest)) :
    let I := configurationInstance ntm c w
    let s := configurationSeedSearchSetup ntm c w
    let n := s.parameters.search.subdivision.vertexCount
    let edge := Cslib.Reachability.Hoza.generatedSubdivisionAdj (layeredDigraph I)
      (configurationSubdivisionIndex ntm c w) (fun _ => false)
    configurationSeedSchedulerReferenceScan ntm c w frame.request = some (.decided false) ∧
      ∃ source : Fin n, source.val = frame.request.sourceID ∧
        ¬ Relation.ReflTransGen edge source
          ⟨s.targetID, (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w).2⟩ := by
  obtain ⟨hvalid, hsetup, hseed⟩ := seedSchedulerCandidate_valid hcandidate
  obtain ⟨source, hsource, _, hreach⟩ :=
    configurationJustesenSeedSchedulerScan_readReply_correct
      ntm c w frame hsetup hvalid bits rest (.decided false) hreply
  refine ⟨configurationJustesenSeedSchedulerScan_readReply_eq_reference
    ntm c w frame hsetup hvalid bits rest (.decided false) hreply, source, hsource, fun hpath => ?_⟩
  have hfalse := hreach.mpr (by simpa only [hseed, Nat.zero_testBit] using hpath)
  cases hfalse

/-- The native compiler can compose the observations under any retained-state producer's budget. -/
example {k : ℕ} {State α : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) {enc : α ↪ List Bool} {S : α → ℕ} {state : α → JustesenSeedSchedulerState}
    (hs : ComputableInSpace state enc encJustesenSeedSchedulerState S) :
    let M := justesenSeedScheduler ntm c
    ComputableInSpace (fun a => M.query (state a)) enc encNat S ∧
      ComputableInSpace (fun a => M.halted (state a)) enc encBool S ∧
      ComputableInSpace (fun a => M.accept (state a)) enc encBool S := by
  obtain ⟨hq, hh, ha⟩ := justesenSeedScheduler_observations_inSpace ntm c
  exact ⟨ComputableInSpace.budget_comp_linear hq hs,
    ComputableInSpace.budget_comp_linear hh hs, ComputableInSpace.budget_comp_linear ha hs⟩

open Cslib.Complexity in
/-- The retained scheduler returns the original machine's decision on its unique successful
trace, for any input on which the simulated machine obeys its space bound. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) (hspace : ntm.RunsInSpace w (c * (Nat.log2 w.length + 1))) :
    let M := justesenSeedScheduler ntm c
    let entry := configurationJustesenSeedSchedulerEntry ntm c w
    let reply := fun trace => SeedSchedulerMachine.reply (M.replay w trace entry).2
    ∃ (answer : SeedSchedulerMachine.Answer) (bits : List Bool),
      (answer.reachable = true ↔ ntm.Accepts w) ∧
      M.FirstHalting w bits entry ∧ reply bits = some (some answer) ∧
      ∀ other, M.FirstHalting w other entry → (reply other).isSome → other = bits := by
  obtain ⟨answer, bits, _, _, _, hreach, hfirst, hreply, hunique⟩ :=
    configurationJustesenSeedScheduler_replay_correct ntm c w
  exact ⟨answer, bits, hreach.trans (configurationInstance_mem_iff ntm c hspace),
    hfirst, hreply, hunique⟩

/-- The original word produces the full retained entry within the compiler's budget. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ComputableInSpace (configurationJustesenSeedSchedulerEntry ntm c)
      encBits encJustesenSeedSchedulerState (fun w => Nat.log2 w.length + 1) :=
  configurationJustesenSeedSchedulerEntry_inSpace ntm c

open NondeterministicQueryMachine ComputableInSpace in
/-- A transition composes with separate producers for the retained state and read/selector input. -/
example {k : ℕ} {State α : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) {enc : α ↪ List Bool} {S : α → ℕ} {state : α → JustesenSeedSchedulerState}
    {input : α → Option Bool × Bool}
    (hs : ComputableInSpace state enc encJustesenSeedSchedulerState S)
    (hi : ComputableInSpace input enc encReadChoice S) :
    ComputableInSpace (fun a => (justesenSeedScheduler ntm c).next (state a, input a))
      enc encJustesenSeedSchedulerState S :=
  budget_comp_linear (justesenSeedScheduler_next_inSpace ntm c) (budget_prod hs hi)

open Classical Cslib.Complexity NondeterministicQueryMachine in
/-- One compiled scheduler meets the native resource bounds, preserves acceptance,
and has exactly one accepting occurrence on each accepted input. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    let M := justesenSeedScheduler ntm c
    let entry := configurationJustesenSeedSchedulerEntry ntm c
    ∃ R : Routines M entry encBits (fun w => Nat.log2 w.length + 1), ∃ L d, ∀ w,
      R.machine.RunsInSpace w (L * (Nat.log2 w.length + 1)) ∧
      R.machine.RunsInTime w (polyClock d w.length) ∧
      (R.machine.Accepts w ↔ (M.withInit (entry w)).Accepts w) ∧
      (ntm.RunsInSpace w (c * (Nat.log2 w.length + 1)) →
        (Native.countingMachine R.I R.P R.F R.C).acceptCount (polyClock d w.length)
          (R.machine.initCfg w) = if ntm.Accepts w then 1 else 0) := by
  obtain ⟨R, L, d, h⟩ := configurationJustesenSeedScheduler_exists_routines ntm c
  refine ⟨R, L, d, fun w => ⟨(h w).1, (h w).2, R.accepts_iff w, fun hspace => ?_⟩⟩
  simpa only [configurationInstance_mem_iff ntm c hspace] using
    configurationJustesenSeedScheduler_acceptCount ntm c R w (h w).2

end CslibFrontierTests.STCONSeedScheduler
