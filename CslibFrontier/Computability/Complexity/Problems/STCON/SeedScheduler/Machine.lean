/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.CallReplay

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

* `SeedSchedulerMachine.step_liveScan`: a live scan takes the callback's step on the same input.
* `SeedSchedulerMachine.firstHalting_scan_iff`: split a successful scan and the resumed trace.
* `SeedSchedulerMachine.firstHalting_skip_iff`: split a skipped root's false selector and suffix.
-/

public section

namespace Cslib.Complexity.STCON.SeedSchedulerMachine

open Cslib.DoubleCounting
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
def resume {σ : Type} (start : SeedScanRequest → σ) (frame : SeedSchedulerFrame)
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

/-- The live callback sees the original query answer and selector, and its caller frame
is unchanged by the step. -/
theorem step_liveScan {σ : Type} (setup : SeedSearchSetup) (scan : NondeterministicQueryMachine σ)
    (start : SeedScanRequest → σ) (verdict : σ → Option ControllerVerdict)
    (w : List Bool) (frame : SeedSchedulerFrame) (s : σ) (choice : Bool)
    (hlive : scan.halted s = false) :
    (machine setup scan start verdict).step w (.inl (.inr (frame, s))) choice =
      .inl (.inr (frame, scan.step w s choice)) := by
  simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read, machine, hlive]

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
  have hstep : M.step w (.inl (.inr (frame, s))) selector =
      if selector then .inr none else resume start frame (verdict s) := by
    simp [M, NondeterministicQueryMachine.step, machine, hhalt]
  rw [hstep]
  cases hv : verdict s with
  | none => simp [resume, seedSchedulerStep_noReply_of_needsScan frame hscan]
  | some v => rfl

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

end Cslib.Complexity.STCON.SeedSchedulerMachine
