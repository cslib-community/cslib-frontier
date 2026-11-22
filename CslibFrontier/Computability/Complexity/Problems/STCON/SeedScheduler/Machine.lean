/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.CallReplay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision.HozaSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Same-input seed scheduler

The binary scheduler keeps its frame during each source scan. The callback reads the original
input. Only the false selector resumes the scheduler from a completed scan or advances a
skipped designated root.

## Main definitions

* `SeedSchedulerMachine.State`: pending skip, active scan, or finished search.
* `SeedSchedulerMachine.machine`: compose the scheduler transition with a supplied scan.
* `SeedSchedulerMachine.resume`: continue after a skipped root or a returned verdict.
* `SeedSchedulerMachine.reply`: observe exhaustion or the chosen seed rank and designated answer
  on a successful branch.

## Main results

* `SeedSchedulerMachine.enter_inSpace` and `SeedSchedulerMachine.init_budget`: enter a
  supplied scan or skip phase within the caller's workspace budget.
* `SeedSchedulerMachine.resume_inSpace`: process the scheduler's control result in space
  linear in the paired frame and verdict encoding.
* `SeedSchedulerMachine.next_inSpace`: advance the scheduler in space linear in its encoded
  state, read bit, and selector.
* `SeedSchedulerMachine.observations_inSpace`: query, halt, terminal reply, and acceptance
  use space linear in the encoded state.
* `SeedSchedulerMachine.step_liveScan`: a live scan takes the callback's step on the same input.
* `SeedSchedulerMachine.firstHalting_scan_iff`: split a successful scan and the resumed trace.
* `SeedSchedulerMachine.firstHalting_skip_iff`: split a skipped root's false selector and suffix.
* `SeedSchedulerMachine.exists_successful_firstHalting`: assemble successful scan traces.
* `SeedSchedulerMachine.haltsWithin`: one clock for all branches given the scanner clock.
* `SeedSchedulerMachine.length_run_le`: bound the state size on every selector prefix.
-/

public section

namespace Cslib.Complexity.STCON.SeedSchedulerMachine

open Cslib.DoubleCounting Cslib.Reachability.Hoza
open _root_.Turing _root_.Turing.MultiTapeTM

/-- A selected binary seed and its designated reachability answer. -/
structure Answer where
  /-- Seed rank in increasing binary order. -/
  seed : ℕ
  /-- The answer returned by the designated scan. -/
  reachable : Bool
  deriving DecidableEq

/-- Encode the binary rank and the designated answer. -/
enc_structure encAnswer : Answer where
  seed : encNat, reachable : encBool

/-- The terminal payload records rejection, exhaustion, or a selected answer. -/
abbrev State (σ : Type) :=
  (SeedSchedulerFrame ⊕ (SeedSchedulerFrame × σ)) ⊕ Option (Option Answer)

/-- Frame the active scheduler and callback state, or encode the terminal payload. -/
def encState {σ : Type} (encScan : σ ↪ List Bool) : State σ ↪ List Bool :=
  encSum (encSum encSeedSchedulerFrame (encPair encSeedSchedulerFrame encScan))
    (encOption (encOption encAnswer))

/-- Start the requested scan if needed, or enter the deterministic skip phase. -/
@[expose] def enter {σ : Type} (start : SeedScanRequest → σ) (frame : SeedSchedulerFrame) :
    State σ :=
  if frame.needsScan then .inl (.inr (frame, start frame.request)) else .inl (.inl frame)

/-- Apply the local scheduler transition and enter its next frame or terminal state. -/
@[expose] def resume {σ : Type} (start : SeedScanRequest → σ) (frame : SeedSchedulerFrame)
    (verdict : Option ControllerVerdict) : State σ :=
  match seedSchedulerStep frame verdict with
  | none => .inr none
  | some (.inl next) => enter start next
  | some (.inr answer) => .inr (some (answer.map fun bit => ⟨frame.request.seed, bit⟩))

/-- Read a successful terminal result. The outer option is absent for a live or rejected state.
An exhausted search has a present outer option and no answer. -/
@[expose] def reply {σ : Type} : State σ → Option (Option Answer)
  | .inl _ => none
  | .inr result => result

/-- Scan the designated source and then the indexed roots on the original read-only input.
Accept when the terminal result contains a positive designated answer. -/
def machine {σ : Type} (setup : SeedSearchSetup) (scan : NondeterministicQueryMachine σ)
    (start : SeedScanRequest → σ) (verdict : σ → Option ControllerVerdict) :
    NondeterministicQueryMachine (State σ) where
  init := (seedSchedulerCandidate setup 0).elim (.inr (some none)) (enter start)
  query
    | .inl (.inr (_, s)) => scan.query s
    | _ => 0
  next
    | (.inl (.inl frame), _, choice) =>
      if choice then .inr none else resume start frame none
    | (.inl (.inr (frame, s)), read, choice) =>
      if scan.halted s then
        if choice then .inr none else resume start frame (verdict s)
      else .inl (.inr (frame, scan.next (s, read, choice)))
    | (.inr result, _, _) => .inr result
  halted
    | .inl _ => false
    | .inr _ => true
  accept s := ((reply s).join.map Answer.reachable).getD false

/-- Changing the initial setup changes only the scheduler's entry. -/
theorem machine_withInit {σ : Type} (setup next : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) :
    (machine setup scan start verdict).withInit (machine next scan start verdict).init =
      machine next scan start verdict := by
  unfold machine NondeterministicQueryMachine.withInit
  rfl

/-- Changing the initial setup or scan entry leaves query, halt, and acceptance unchanged. -/
theorem observations_eq {σ : Type} (setup next : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start restart : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) :
    let M := machine setup scan start verdict
    let N := machine next scan restart verdict
    M.query = N.query ∧ M.halted = N.halted ∧ M.accept = N.accept :=
  ⟨rfl, rfl, rfl⟩

open _root_.Turing.MultiTapeTM.ComputableInSpace in
/-- Enter a skipped root or an active scan within space linear in the encoded frame. -/
theorem enter_inSpace {σ : Type} (encScan : σ ↪ List Bool) (start : SeedScanRequest → σ)
    (hstart : ComputableInSpace start encSeedScanRequest encScan
      (fun r => (encSeedScanRequest r).length)) :
    ComputableInSpace (enter start) encSeedSchedulerFrame (encState encScan)
      (fun f => (encSeedSchedulerFrame f).length) := by
  let scanState := encPair encSeedSchedulerFrame encScan
  let live := encSum encSeedSchedulerFrame scanState
  let terminal := encOption (encOption encAnswer)
  have hframe := budget_id (enc := encSeedSchedulerFrame) (.refl _)
  have hentry := budget_comp_linear hstart (encSeedSchedulerFrame_request_budget hframe)
  have hscan := budget_comp_linear (of_inO (ComputableInO.inr encSeedSchedulerFrame scanState))
    (budget_prod hframe hentry)
  have hskip := of_inO (ComputableInO.inl encSeedSchedulerFrame scanState)
  have hlive := budget_ite (SeedSchedulerFrame.needsScan_budget hframe) hscan hskip
  exact (budget_comp_linear (of_inO (ComputableInO.inl live terminal)) hlive).of_enc_eq fun f => by
    change encState encScan (enter start f) = encState encScan
      (.inl (if f.needsScan then .inr (f, start f.request) else .inl f))
    unfold enter
    split <;> rfl

open _root_.Turing.MultiTapeTM.ComputableInSpace in
/-- Construct the scheduler's initial state under the setup producer's workspace budget. -/
theorem init_budget {α σ : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (encScan : σ ↪ List Bool) (scan : NondeterministicQueryMachine σ)
    (start : SeedScanRequest → σ) (verdict : σ → Option ControllerVerdict)
    (hstart : ComputableInSpace start encSeedScanRequest encScan
      (fun r => (encSeedScanRequest r).length))
    {setup : α → SeedSearchSetup} (hsetup : ComputableInSpace setup enc encSeedSearchSetup S) :
    ComputableInSpace (fun a => (machine (setup a) scan start verdict).init)
      enc (encState encScan) S := by
  have hzero := (constZero (encIn := enc) (encB := encNat) 0).mono_le (fun a => Nat.zero_le (S a))
  have hcandidate := seedSchedulerCandidate_budget hsetup hzero
  have hentry := optionElim (.inr (some none)) (enter_inSpace encScan start hstart)
  exact (budget_comp_linear hentry hcandidate).of_enc_eq fun _ => rfl

open _root_.Turing.MultiTapeTM.ComputableInSpace in
/-- Resume the scheduler in workspace linear in the paired frame and optional verdict.
A completed answer keeps the seed rank from the retained frame. -/
theorem resume_inSpace {σ : Type} (encScan : σ ↪ List Bool) (start : SeedScanRequest → σ)
    (hstart : ComputableInSpace start encSeedScanRequest encScan
      (fun r => (encSeedScanRequest r).length)) :
    let E := encPair encSeedSchedulerFrame
      (encOption _root_.Turing.DoubleCounting.SourceRoundLoop.encVerdict)
    ComputableInSpace (fun p => resume start p.1 p.2) E (encState encScan)
      (fun p => (E p).length) := by
  let F := encSeedSchedulerFrame
  let R := encState encScan
  let live := encSum F (encPair F encScan)
  let terminal := encOption (encOption encAnswer)
  let verdict := encOption _root_.Turing.DoubleCounting.SourceRoundLoop.encVerdict
  have hcontinue := budget_comp_linear (enter_inSpace encScan start hstart) (snd F F)
  have hframeWithBit := fst F encBool
  have hrank := encSeedScanRequest_seed_budget (encSeedSchedulerFrame_request_budget hframeWithBit)
  have hresult := encAnswer_mk_budget hrank (snd F encBool)
  have hnoAnswer := budget_const (encIn := F) (encB := encOption encAnswer) none (.refl _)
  have hanswer := optionElimSnd hnoAnswer (budget_optionSome hresult)
  have hfinish := budget_comp_linear (of_inO (ComputableInO.inr live terminal))
    (budget_optionSome hanswer)
  have hreject := budget_const (encIn := F) (encB := R) (.inr none) (.refl _)
  have hdispatch := optionElimSnd hreject (sumElimSnd hcontinue hfinish)
  have hinput := budget_prod (fst F verdict) seedSchedulerStep_inSpace
  exact (budget_comp_linear hdispatch hinput).of_enc_eq fun p => by
    unfold resume
    cases seedSchedulerStep p.1 p.2 with
    | none => rfl
    | some result =>
      cases result with
      | inl next => rfl
      | inr answer => cases answer <;> rfl

open _root_.Turing.MultiTapeTM.ComputableInSpace in
/-- Query, read the phase tag or terminal reply, and test acceptance in space linear in
the encoded scheduler state. Only the active scan's query uses a supplied certificate. -/
theorem observations_inSpace {σ : Type} (encScan : σ ↪ List Bool) (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict)
    (hquery : ComputableInSpace scan.query encScan encNat (fun s => (encScan s).length)) :
    let E := encState encScan
    let M := machine setup scan start verdict
    ComputableInSpace M.query E encNat (fun s => (E s).length) ∧
      ComputableInSpace M.halted E encBool (fun s => (E s).length) ∧
      ComputableInSpace reply E (encOption (encOption encAnswer)) (fun s => (E s).length) ∧
      ComputableInSpace M.accept E encBool (fun s => (E s).length) := by
  intro E M
  let live := encSum encSeedSchedulerFrame (encPair encSeedSchedulerFrame encScan)
  let terminal := encOption (encOption encAnswer)
  have hquerySkip := budget_const (encIn := encSeedSchedulerFrame) (encB := encNat) 0 (.refl _)
  have hqueryScan := budget_comp_linear hquery (snd encSeedSchedulerFrame encScan)
  have hqueryTerminal := budget_const (encIn := terminal) (encB := encNat) 0 (.refl _)
  have hqueryMachine : ComputableInSpace M.query E encNat (fun s => (E s).length) :=
    (sumElim (sumElim hquerySkip hqueryScan) hqueryTerminal).of_enc_eq fun
      | .inl (.inl _) | .inl (.inr _) | .inr _ => rfl
  have hhaltLive := budget_const (encIn := live) (encB := encBool) false (.refl _)
  have hhaltTerminal := budget_const (encIn := terminal) (encB := encBool) true (.refl _)
  have hhalt : ComputableInSpace M.halted E encBool (fun s => (E s).length) :=
    (sumElim hhaltLive hhaltTerminal).of_enc_eq fun | .inl _ | .inr _ => rfl
  have hreplyLive := budget_const (encIn := live) (encB := terminal) none (.refl _)
  have hreplyTerminal := budget_id (enc := terminal) (.refl _)
  have hreply : ComputableInSpace reply E terminal (fun s => (E s).length) :=
    (sumElim hreplyLive hreplyTerminal).of_enc_eq fun | .inl _ | .inr _ => rfl
  have hanswer := encAnswer_reachable_budget (budget_id (enc := encAnswer) (.refl _))
  have haccept := budget_comp_linear (optionElim false (optionElim false hanswer)) hreply
  exact ⟨hqueryMachine, hhalt, hreply, haccept.of_enc_eq fun
    | .inl _ | .inr none | .inr (some none) | .inr (some (some _)) => rfl⟩

open _root_.Turing.MultiTapeTM.ComputableInSpace NondeterministicQueryMachine in
/-- Forward a live scanner transition or resume its caller, using workspace linear in the
encoded scheduler state and the read and selector bits. -/
theorem next_inSpace {σ : Type} (encScan : σ ↪ List Bool) (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict)
    (hstart : ComputableInSpace start encSeedScanRequest encScan
      (fun r => (encSeedScanRequest r).length))
    (hhalt : ComputableInSpace scan.halted encScan encBool (fun s => (encScan s).length))
    (hverdict : ComputableInSpace verdict encScan
      (encOption _root_.Turing.DoubleCounting.SourceRoundLoop.encVerdict)
      (fun s => (encScan s).length))
    (hnext : ComputableInSpace scan.next (encPair encScan encReadChoice) encScan
      (fun p => (encPair encScan encReadChoice p).length)) :
    let E := encState encScan
    let P := encPair E encReadChoice
    ComputableInSpace (machine setup scan start verdict).next P E (fun p => (P p).length) := by
  let F := encSeedSchedulerFrame
  let A := encPair F encScan
  let L := encSum F A
  let T := encOption (encOption encAnswer)
  let E := encState encScan
  let V := encOption _root_.Turing.DoubleCounting.SourceRoundLoop.encVerdict
  have hresume := resume_inSpace encScan start hstart
  have hskipFrame := fst F encReadChoice
  have hskipChoice := snd' (snd F encReadChoice)
  have hskipReject := budget_const (encIn := encPair F encReadChoice) (encB := E) (.inr none)
    (.refl _)
  have hnoVerdict := budget_const (encIn := encPair F encReadChoice) (encB := V) none (.refl _)
  have hskip := budget_ite hskipChoice hskipReject
    (budget_comp_linear hresume (budget_prod hskipFrame hnoVerdict))
  have hactive := fst A encReadChoice
  have hread := snd A encReadChoice
  have hsuspended := fst' hactive
  have hscan := snd' hactive
  have hreturn := budget_comp_linear hresume
    (budget_prod hsuspended (budget_comp_linear hverdict hscan))
  have hscanReject := budget_const (encIn := encPair A encReadChoice) (encB := E) (.inr none)
    (.refl _)
  have hliveState := budget_prod hsuspended (budget_comp_linear hnext (budget_prod hscan hread))
  have hlive := budget_comp_linear (of_inO (ComputableInO.inl L T))
    (budget_comp_linear (of_inO (ComputableInO.inr F A)) hliveState)
  have hrun := budget_ite (budget_comp_linear hhalt hscan)
    (budget_ite (snd' hread) hscanReject hreturn) hlive
  have hfinished := budget_comp_linear (of_inO (ComputableInO.inr L T)) (fst T encReadChoice)
  refine (sumElimFst (sumElimFst hskip hrun) hfinished).of_enc_eq ?_
  rintro ⟨(f | ⟨f, s⟩) | result, read, bit⟩
  · cases bit <;> rfl
  · cases scan.halted s <;> cases bit <;> rfl
  · rfl

/-- The live callback sees the original query answer and selector, and its caller frame
is unchanged by the step. -/
theorem step_liveScan {σ : Type} (setup : SeedSearchSetup) (scan : NondeterministicQueryMachine σ)
    (start : SeedScanRequest → σ) (verdict : σ → Option ControllerVerdict)
    (w : List Bool) (frame : SeedSchedulerFrame) (s : σ) (choice : Bool)
    (hlive : scan.halted s = false) :
    (machine setup scan start verdict).step w (.inl (.inr (frame, s))) choice =
      .inl (.inr (frame, scan.step w s choice)) := by
  simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read, machine, hlive]

private theorem step_haltedScan {σ : Type} (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) (input : List Bool)
    (frame : SeedSchedulerFrame) (s : σ) (selector : Bool) (hhalt : scan.halted s = true) :
    (machine setup scan start verdict).step input (.inl (.inr (frame, s))) selector =
      if selector then .inr none else resume start frame (verdict s) := by
  simp [NondeterministicQueryMachine.step, machine, hhalt]

/-- A successful first halt from an active scan consumes its parsed verdict and then
first halts from the resumed scheduler, using the parser's unmodified suffix.
The frame must request a scan, as it does when `enter` selects the active phase. -/
theorem firstHalting_scan_iff {σ : Type} (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) (w : List Bool)
    (frame : SeedSchedulerFrame) (state : σ) (bits : List Bool) (answer : Option Answer)
    (hscan : frame.needsScan = true) :
    let M := machine setup scan start verdict
    let active : State σ := .inl (.inr (frame, state))
    M.FirstHalting w bits active ∧ M.replay w bits active = .inr (some answer) ↔
      ∃ value rest, scan.readReply verdict w state bits = some (value, rest) ∧
        M.FirstHalting w rest (resume start frame (some value)) ∧
        M.replay w rest (resume start frame (some value)) = .inr (some answer) := by
  intro M active
  refine NondeterministicQueryMachine.successful_call_iff M scan w
    (fun s => .inl (.inr (frame, s))) verdict (fun v => resume start frame (some v))
    (.inr none) (.inr (some answer)) rfl (by simp) rfl (fun _ => rfl)
    (step_liveScan setup scan start verdict w frame) ?_ state bits
  intro s selector hhalt
  rw [step_haltedScan setup scan start verdict w frame s selector hhalt]
  cases hv : verdict s with
  | none => simp [resume, seedSchedulerStep_noReply_of_needsScan frame hscan]
  | some v => rfl

/-- The initial state enters the zero seed candidate when it exists. -/
theorem machine_init {σ : Type} (setup : SeedSearchSetup) (scan : NondeterministicQueryMachine σ)
    (start : SeedScanRequest → σ) (verdict : σ → Option ControllerVerdict) :
    (machine setup scan start verdict).init =
      (seedSchedulerCandidate setup 0).elim (.inr (some none)) (enter start) := by simp [machine]

/-- The scheduler halts precisely in the terminal phase, including rejection and exhaustion. -/
theorem machine_halted {σ : Type} (setup : SeedSearchSetup) (scan : NondeterministicQueryMachine σ)
    (start : SeedScanRequest → σ) (verdict : σ → Option ControllerVerdict) (state : State σ) :
    (machine setup scan start verdict).halted state = state.isRight := by
  cases state <;> rfl

/-- A successful first halt from a skipped root consumes exactly one false selector
before continuing the search. -/
theorem firstHalting_skip_iff {σ : Type} (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) (w : List Bool)
    (frame : SeedSchedulerFrame) (bits : List Bool) (answer : Option Answer) :
    let M := machine setup scan start verdict
    let skip : State σ := .inl (.inl frame)
    M.FirstHalting w bits skip ∧ M.replay w bits skip = .inr (some answer) ↔
      ∃ rest, bits = false :: rest ∧ M.FirstHalting w rest (resume start frame none) ∧
        M.replay w rest (resume start frame none) = .inr (some answer) := by
  intro M skip
  cases bits with
  | nil => simp [skip]
  | cons selector bits =>
    have hskip : M.halted skip = false := rfl
    rw [M.firstHalting_cons_iff, M.replay_cons, hskip]
    cases selector
    · have hstep : M.step w skip false = resume start frame none := rfl
      simp [hstep]
    · have hstep : M.step w skip true = .inr none := rfl
      have hhalt : M.halted (.inr none) = true := rfl
      simp [hstep, M.replay_of_halted w hhalt]

private def offset (f : SeedSchedulerFrame) : ℕ :=
  if f.answer.isSome then f.cursor + 1 else 0

private def remaining (f : SeedSchedulerFrame) : ℕ :=
  let size := f.request.setup.parameters.search
  (size.seedLimit - f.request.seed) * (size.subdivision.originalCount + 1) - offset f

private theorem offset_lt {f : SeedSchedulerFrame} (hf : f.Valid) :
    offset f < f.request.setup.parameters.search.subdivision.originalCount + 1 := by
  cases h : f.answer with
  | none => simp [offset, h]
  | some answer =>
    simp only [SeedSchedulerFrame.Valid, h] at hf
    simp [offset, h]
    omega

private theorem remaining_pos {f : SeedSchedulerFrame} (hf : f.Valid) : 0 < remaining f := by
  have hs := hf.seed_lt
  have ho := offset_lt hf
  have hmul := Nat.mul_le_mul_right
    (f.request.setup.parameters.search.subdivision.originalCount + 1)
    (show 1 ≤ f.request.setup.parameters.search.seedLimit - f.request.seed by omega)
  simp only [Nat.one_mul] at hmul
  exact Nat.sub_pos_of_lt (ho.trans_le hmul)

private theorem remaining_lt {f g : SeedSchedulerFrame} {reply : Option ControllerVerdict}
    (hf : f.Valid) (h : seedSchedulerStep f reply = some (.inl g)) :
    remaining g < remaining f := by
  obtain ⟨hg, hsetup, hprogress⟩ := seedSchedulerStep_progress hf h
  have hs := hf.seed_lt
  have hgseed := hg.seed_lt
  rw [hsetup] at hgseed
  have ho := offset_lt hf
  have hpositive := remaining_pos hg
  simp only [remaining, hsetup] at hpositive ⊢
  rcases hprogress with hseed | ⟨hseed, hcursor⟩
  · let limit := f.request.setup.parameters.search.seedLimit
    have hmul := Nat.mul_le_mul_right
      (f.request.setup.parameters.search.subdivision.originalCount + 1)
      (show limit - g.request.seed + 1 ≤ limit - f.request.seed by
        dsimp only [limit]
        omega)
    simp only [Nat.add_mul, Nat.one_mul, limit] at hmul
    omega
  · have hpos : offset f < offset g := by
      rcases hcursor with ⟨hnone, hsome⟩ | hcursor
      · cases h : g.answer with
        | none => simp [h] at hsome
        | some answer => simp [offset, hnone, h]
      · cases h : g.answer with
        | none =>
          simp only [SeedSchedulerFrame.Valid, h] at hg
          omega
        | some answer =>
          cases ha : f.answer with
          | none => simp [offset, ha, h]
          | some bit => simpa [offset, ha, h] using hcursor
    rw [hseed] at hpositive ⊢
    omega

/-- One scanner clock for each valid requested scan bounds all scheduler branches. Each
remaining seed has at most one designated frame and one frame per original root, with one
additional selector per frame for a skip or return. -/
theorem haltsWithin {σ : Type} (setup : SeedSearchSetup) (scan : NondeterministicQueryMachine σ)
    (start : SeedScanRequest → σ) (verdict : σ → Option ControllerVerdict) (input : List Bool)
    (clock : ℕ)
    (hscan : ∀ frame : SeedSchedulerFrame,
      frame.request.setup = setup → frame.Valid → frame.needsScan = true →
      (scan.withInit (start frame.request)).HaltsWithin input clock) :
    (machine setup scan start verdict).HaltsWithin input
      (setup.parameters.search.seedLimit *
        ((1 + setup.parameters.search.subdivision.originalCount) * (clock + 1))) := by
  let M := machine setup scan start verdict
  have terminal (result : Option (Option Answer)) (bits : List Bool) :
      M.halted (M.replay input bits (.inr result)) = true := by
    rw [M.replay_of_halted input (by rfl)]
    rfl
  have fromFrame (f : SeedSchedulerFrame) (hsetup : f.request.setup = setup) (hf : f.Valid)
      (bits : List Bool) (hlen : remaining f * (clock + 1) ≤ bits.length) :
      M.halted (M.replay input bits (enter start f)) = true := by
    induction hr : remaining f using Nat.strongRecOn generalizing f bits with
    | ind fuel ih =>
      have hpos := remaining_pos hf
      have hbudget : remaining f * (clock + 1) =
          (remaining f - 1) * (clock + 1) + (clock + 1) := by
        conv_lhs => rw [show remaining f = (remaining f - 1) + 1 by omega]
        rw [Nat.add_mul, Nat.one_mul]
      have afterStep (selector : Bool) (reply : Option ControllerVerdict) (rest : List Bool)
          (hrest : (remaining f - 1) * (clock + 1) ≤ rest.length) :
          M.halted (M.replay input rest
            (if selector then .inr none else resume start f reply)) = true := by
        cases selector with
        | true => exact terminal none rest
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, resume]
          cases he : seedSchedulerStep f reply with
          | none => exact terminal none rest
          | some result =>
            cases result with
            | inr answer => exact terminal _ rest
            | inl next =>
              obtain ⟨hvalid, hsame, _⟩ := seedSchedulerStep_progress hf he
              have hlt := remaining_lt hf he
              have hle : remaining next ≤ remaining f - 1 := by omega
              exact ih (remaining next) (hr ▸ hlt) next (hsame.trans hsetup) hvalid rest
                ((Nat.mul_le_mul_right _ hle).trans hrest) rfl
      by_cases hneeds : f.needsScan = true
      · have hlong : clock < bits.length := by omega
        obtain ⟨prefixBits, selector, rest, rfl, hprefix, hfirst⟩ :=
          scan.exists_firstHalting_prefix_with_next input bits (start f.request)
            clock (hscan f hsetup hf hneeds) hlong
        rw [enter, ite_eq_left hneeds, M.replay_append,
          M.replay_map_of_live input scan (fun s => .inl (.inr (f, s)))
            (step_liveScan setup scan start verdict input f) prefixBits (start f.request) hfirst.2,
          M.replay_cons]
        rw [step_haltedScan setup scan start verdict input f _ selector hfirst.1]
        simp only [List.length_append, List.length_cons] at hlen
        exact afterStep selector _ rest (by omega)
      · cases bits with
        | nil =>
          simp only [List.length_nil] at hlen
          omega
        | cons selector rest =>
          rw [enter, ite_eq_right hneeds, M.replay_cons]
          have hstep : M.step input (.inl (.inl f)) selector =
              (if selector then .inr none else resume start f none) := rfl
          rw [hstep]
          simp only [List.length_cons] at hlen
          exact afterStep selector none rest (by omega)
  intro bits hlen
  change M.halted (M.replay input bits M.init) = true
  rw [machine_init]
  cases hentry : seedSchedulerCandidate setup 0 with
  | none => exact terminal (some none) bits
  | some f =>
    obtain ⟨hf, hs, hz⟩ := seedSchedulerCandidate_valid hentry
    apply fromFrame f hs hf bits
    simp only [remaining, hs, hz, Nat.sub_zero]
    rw [hlen, Nat.add_comm 1, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
private def PrefixState {σ : Type} (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (w : List Bool) : State σ → Prop
  | .inl (.inl f) => f.Valid ∧ f.request.setup = setup
  | .inl (.inr (f, state)) =>
    f.Valid ∧ f.request.setup = setup ∧ f.needsScan = true ∧
      ∃ bits, scan.replay w bits (start f.request) = state
  | .inr (some (some a)) => a.seed < setup.parameters.search.seedLimit
  | .inr none | .inr (some none) => True

private theorem prefixState_enter {σ : Type} {setup : SeedSearchSetup}
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (w : List Bool) {f : SeedSchedulerFrame} (hf : f.Valid) (hs : f.request.setup = setup) :
    PrefixState setup scan start w (enter start f) := by
  unfold enter
  split
  · exact ⟨hf, hs, ‹f.needsScan = true›, [], rfl⟩
  · exact ⟨hf, hs⟩

private theorem prefixState_resume {σ : Type} {setup : SeedSearchSetup}
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (w : List Bool) {f : SeedSchedulerFrame} (hf : f.Valid) (hs : f.request.setup = setup)
    (result : Option ControllerVerdict) :
    PrefixState setup scan start w (resume start f result) := by
  unfold resume
  split
  · trivial
  · rename_i next hnext
    obtain ⟨hv, he, _⟩ := seedSchedulerStep_progress hf hnext
    exact prefixState_enter scan start w hv (he.trans hs)
  · rename_i answer _
    cases answer
    · trivial
    · exact hs ▸ hf.seed_lt

private theorem prefixState_step {σ : Type} {setup : SeedSearchSetup}
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) (w : List Bool)
    {state : State σ} (h : PrefixState setup scan start w state) (bit : Bool) :
    PrefixState setup scan start w ((machine setup scan start verdict).step w state bit) := by
  cases state with
  | inr result =>
    rw [NondeterministicQueryMachine.step_of_halted _ _ (by rfl)]
    exact h
  | inl frame =>
    cases frame with
    | inl f =>
      obtain ⟨hf, hs⟩ := h
      cases bit
      · exact prefixState_resume scan start w hf hs none
      · trivial
    | inr active =>
      obtain ⟨f, s⟩ := active
      obtain ⟨hf, hs, hscan, bits, rfl⟩ := h
      cases hh : scan.halted (scan.replay w bits (start f.request))
      · rw [step_liveScan _ _ _ _ _ _ _ _ hh]
        exact ⟨hf, hs, hscan, bits ++ [bit], scan.replay_append w bits [bit] _⟩
      · rw [step_haltedScan _ _ _ _ _ _ _ _ hh]
        cases bit
        · exact prefixState_resume scan start w hf hs
            (verdict (scan.replay w bits (start f.request)))
        · trivial

/-- Every selector prefix of the same-input scheduler, including rejecting branches,
uses at most the uniform scanner state bound plus a linear allowance for the retained
setup and frame. The scanner bound applies to valid frames that request a scan on the
original input. -/
theorem length_run_le {σ : Type} (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) (encScan : σ ↪ List Bool)
    (w : List Bool) (scanBound : ℕ)
    (hsource : setup.sourceID < setup.parameters.search.subdivision.vertexCount)
    (hroot : ∀ j < setup.parameters.search.subdivision.originalCount,
      setup.originalSourceID j < setup.parameters.search.subdivision.vertexCount)
    (hscan : ∀ f : SeedSchedulerFrame, f.request.setup = setup → f.Valid →
      f.needsScan = true → ∀ bits,
        (encScan (scan.replay w bits (start f.request))).length ≤ scanBound)
    (bits : List Bool) :
    (encState encScan ((machine setup scan start verdict).run w bits)).length ≤
      24 * (encSeedSearchSetup setup).length + scanBound + 21 := by
  let M := machine setup scan start verdict
  have hinit : PrefixState setup scan start w M.init := by
    change PrefixState setup scan start w
      ((seedSchedulerCandidate setup 0).elim (.inr (some none)) (enter start))
    cases hc : seedSchedulerCandidate setup 0 with
    | none => trivial
    | some f =>
      obtain ⟨hf, hs, _⟩ := seedSchedulerCandidate_valid hc
      exact prefixState_enter scan start w hf hs
  have hrun : PrefixState setup scan start w (M.run w bits) := by
    induction bits using List.reverseRecOn with
    | nil => exact hinit
    | append_singleton bits bit ih =>
      rw [M.run_append]
      exact prefixState_step scan start verdict w ih bit
  have frameLength {f : SeedSchedulerFrame} (hf : f.Valid) (hs : f.request.setup = setup) :
      (encSeedSchedulerFrame f).length ≤ 12 * (encSeedSearchSetup setup).length + 9 :=
    hs ▸ hf.length_le (hs.symm ▸ hsource) (hs.symm ▸ hroot)
  change (encState encScan (M.run w bits)).length ≤ _
  generalize M.run w bits = state at hrun ⊢
  cases state with
  | inl live =>
    cases live with
    | inl f =>
      obtain ⟨hf, hs⟩ := hrun
      have hframe := frameLength hf hs
      simp only [encState, encSum_inl, List.length_cons]
      omega
    | inr active =>
      obtain ⟨f, s⟩ := active
      obtain ⟨hf, hs, hneeds, choices, rfl⟩ := hrun
      have hframe := frameLength hf hs
      have hcallback := hscan f hs hf hneeds choices
      simp only [encState, encSum_inl, encSum_inr, List.length_cons, length_encPair]
      omega
  | inr result =>
    rcases result with _ | (_ | answer)
    · simp [encState]
    · simp [encState]
    · have hseed : answer.seed < setup.parameters.search.seedLimit := hrun
      have hlength := (length_encNat_mono hseed.le).trans
        ((encSeedSearchSize_seedLimit_length_le setup.parameters.search).trans
          ((encSeedSearchParameters_search_length_le setup.parameters).trans
            (encSeedSearchSetup_parameters_length_le setup)))
      simp only [encState, encSum_inr, encOption_some, encAnswer_apply, length_encPair,
        encBool_apply, List.length_cons, List.length_nil]
      omega

/-- If each requested scan from a valid frame has a first-halting replay with a verdict,
the initialized scheduler has a first-halting replay with a result. The result can be a
selected seed with either decision, or exhaustion. -/
theorem exists_successful_firstHalting {σ : Type} (setup : SeedSearchSetup)
    (scan : NondeterministicQueryMachine σ) (start : SeedScanRequest → σ)
    (verdict : σ → Option ControllerVerdict) (input : List Bool)
    (hscan : ∀ f : SeedSchedulerFrame,
      f.request.setup = setup → f.Valid → f.needsScan = true →
      ∃ bits, scan.FirstHalting input bits (start f.request) ∧
        (verdict (scan.replay input bits (start f.request))).isSome) :
    let M := machine setup scan start verdict
    ∃ bits, M.FirstHalting input bits M.init ∧ (reply (M.run input bits)).isSome := by
  let M := machine setup scan start verdict
  have terminal (answer : Option Answer) :
      M.FirstHalting input [] (.inr (some answer)) ∧
        M.replay input [] (.inr (some answer)) = .inr (some answer) :=
    ⟨(M.firstHalting_iff_nil_of_halted input [] _ (by rfl)).mpr rfl,
      M.replay_nil input _⟩
  have fromFrame (f : SeedSchedulerFrame) (hsetup : f.request.setup = setup) (hf : f.Valid) :
      ∃ bits answer, M.FirstHalting input bits (enter start f) ∧
        M.replay input bits (enter start f) = .inr (some answer) := by
    induction hr : remaining f using Nat.strongRecOn generalizing f with
    | ind fuel ih =>
      have afterStep (returned : Option ControllerVerdict)
          (hreturned : f.needsScan = true → returned.isSome) :
          ∃ rest answer, M.FirstHalting input rest (resume start f returned) ∧
            M.replay input rest (resume start f returned) = .inr (some answer) := by
        obtain ⟨result, hstep⟩ :=
          Option.isSome_iff_exists.mp (seedSchedulerStep_isSome f returned hreturned)
        rw [resume, hstep]
        cases result with
        | inr answer => exact ⟨[], _, terminal _⟩
        | inl next =>
          obtain ⟨hvalid, hsame, _⟩ := seedSchedulerStep_progress hf hstep
          exact ih (remaining next) (hr ▸ remaining_lt hf hstep) next
            (hsame.trans hsetup) hvalid rfl
      by_cases hneeds : f.needsScan = true
      · obtain ⟨prefixBits, hfirst, hpresent⟩ := hscan f hsetup hf hneeds
        obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp hpresent
        obtain ⟨rest, answer, hsuffix⟩ := afterStep (some value) (fun _ => rfl)
        refine ⟨prefixBits ++ false :: rest, answer, ?_⟩
        rw [enter, ite_eq_left hneeds]
        exact (firstHalting_scan_iff setup scan start verdict input f (start f.request)
          _ answer hneeds).mpr ⟨value, rest, (scan.readReply_iff verdict input _ _ _ _).mpr
            ⟨prefixBits, rfl, hfirst, hvalue⟩, hsuffix⟩
      · obtain ⟨rest, answer, hsuffix⟩ := afterStep none (fun h => (hneeds h).elim)
        refine ⟨false :: rest, answer, ?_⟩
        rw [enter, ite_eq_right hneeds]
        exact (firstHalting_skip_iff setup scan start verdict input f _ answer).mpr
          ⟨rest, rfl, hsuffix⟩
  suffices ∃ bits answer, M.FirstHalting input bits M.init ∧
      M.replay input bits M.init = .inr (some answer) by
    obtain ⟨bits, answer, hfirst, hreply⟩ := this
    refine ⟨bits, hfirst, ?_⟩
    change (reply (M.replay input bits M.init)).isSome
    rw [hreply]
    rfl
  rw [machine_init]
  cases hentry : seedSchedulerCandidate setup 0 with
  | none => exact ⟨[], none, terminal none⟩
  | some frame =>
    obtain ⟨hvalid, hsetup, _⟩ := seedSchedulerCandidate_valid hentry
    exact fromFrame frame hsetup hvalid

end Cslib.Complexity.STCON.SeedSchedulerMachine
