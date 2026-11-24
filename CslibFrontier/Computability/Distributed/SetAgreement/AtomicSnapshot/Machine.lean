/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Model
public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Unbounded single-writer atomic snapshot transition system

Defines process states (`ActiveScan`, `ProcSnapshotState`), global configurations
(`SnapshotState`), atomic transition labels (`SnapshotEvent`), single-register transition function
(`stepSnapshot`), and labelled transition system (`snapshotLTS`, `SnapshotReachable`) following
[AfekAttiyaDolevGafniMerrittShavit1993], §3, Figure 3.

## Main definitions

* `Cslib.Distributed.SetAgreement.ScanMode`, `Cslib.Distributed.SetAgreement.CollectPhase`,
  `Cslib.Distributed.SetAgreement.ActiveScan`, `Cslib.Distributed.SetAgreement.ProcSnapshotState`,
  `Cslib.Distributed.SetAgreement.SnapshotState`, `Cslib.Distributed.SetAgreement.SnapshotEvent`:
  process states, global configurations, and atomic single-register LTS events.
* `Cslib.Distributed.SetAgreement.completeHistoryAt`, `Cslib.Distributed.SetAgreement.finishScan`,
  `Cslib.Distributed.SetAgreement.stepSnapshot`: atomic step transition semantics.
* `Cslib.Distributed.SetAgreement.snapshotLTS`,
  `Cslib.Distributed.SetAgreement.SnapshotReachable`: labelled transition system and reachability.
-/

public section

namespace Cslib.Distributed.SetAgreement

open Finset

/-! ### Unbounded single-writer algorithm state machine (`Figure 3`) -/

/-- Whether an active `scan_i` is serving an external `ScanRequest_i` or the embedded scan inside
`UpdateRequest_i(val)`. -/
inductive ScanMode (Data : Type*) where
  /-- Top-level client `scan` operation. -/
  | external
  /-- Embedded `scan` inside `update(val)` (line 1 of `update_i` in Figure 3). -/
  | embedded (val : Data)
  deriving @[expose] DecidableEq

/-- Which of the two sequential collects in Figure 3 lines 2–3 is currently executing. -/
inductive CollectPhase where
  /-- First collect (`a[1..n] := collect`, line 2). -/
  | collectA
  /-- Second collect (`b[1..n] := collect`, line 3). -/
  | collectB
  deriving @[expose] DecidableEq

/-- Local variables of an active `scan_i` loop ([AfekAttiyaDolevGafniMerrittShavit1993], Figure 3,
p. 8). -/
@[ext]
structure ActiveScan (P Data : Type*) where
  /-- Whether this scan is top-level or embedded inside an `update`. -/
  mode : ScanMode Data
  /-- Index of the enclosing client operation in `SnapshotState.history`. -/
  opId : ℕ
  /-- Processes observed to move once in an earlier double collect (`moved[j] = 1`). -/
  moved : Finset P
  /-- Current collect pass (`collectA` or `collectB`). -/
  phase : CollectPhase
  /-- Remaining registers still to read one-by-one in the current collect pass. -/
  rem : List P
  /-- Accumulated register records read during `collectA`. -/
  collectAVal : P → SnapshotReg P Data
  /-- Accumulated register records read during `collectB`. -/
  collectBVal : P → SnapshotReg P Data

/-- Local control state of a single process `i : P` in Figure 3. -/
inductive ProcSnapshotState (P Data : Type*) where
  /-- No pending operation (`H_i = ⊥`). -/
  | idle
  /-- Executing the double-collect `scan_i` loop (top-level or embedded). -/
  | scanning (st : ActiveScan P Data)
  /-- Embedded `scan_i` completed with `snap`; ready to execute atomic write
  `r_i := (val, r_i.seq + 1, snap)` (line 2 of `update_i` in Figure 3). -/
  | readyToWrite (opId : ℕ) (val : Data) (snap : P → Data)

/-- Computable test for whether a process control state is `.idle`. -/
@[expose]
def ProcSnapshotState.isIdle {P Data : Type*} : ProcSnapshotState P Data → Bool
  | .idle => true
  | .scanning _ | .readyToWrite _ _ _ => false

@[simp]
theorem ProcSnapshotState.isIdle_eq_true {P Data : Type*} (ps : ProcSnapshotState P Data) :
    ps.isIdle = true ↔ ps = .idle := by
  cases ps <;> simp [ProcSnapshotState.isIdle]

/-- Global configuration of the unbounded single-writer snapshot implementation. -/
@[ext]
structure SnapshotState (P Data : Type*) where
  /-- Array of `n` single-writer, `n`-reader atomic registers `r_1, …, r_n`. -/
  reg : P → SnapshotReg P Data
  /-- Per-process local control states. -/
  proc : P → ProcSnapshotState P Data
  /-- Recorded client invocation/completion history for linearizability verification. -/
  history : List (SnapshotOpRecord P Data)
  /-- Global transition counter (`history` timestamps). -/
  stepCount : ℕ

/-- Initial configuration: all registers hold `(dInit, 0, fun _ => dInit)`, all processes are
`idle`, and `history` is empty. -/
@[expose]
def SnapshotState.init {P Data : Type*} (dInit : Data) : SnapshotState P Data where
  reg _ := SnapshotReg.init dInit
  proc _ := .idle
  history := []
  stepCount := 0

/-- Atomic transition labels of the snapshot implementation: client invocations or one atomic step
of process `i` (reading at most **one** register `reg j` or writing `reg i`). -/
inductive SnapshotEvent (P Data : Type*) where
  /-- Idle process `i` invokes `ScanRequest_i`. -/
  | invokeScan (i : P)
  /-- Idle process `i` invokes `UpdateRequest_i(val)`. -/
  | invokeUpdate (i : P) (val : Data)
  /-- Active process `i` executes one atomic step (a single register read, local loop check, or
  single-writer register write). -/
  | step (i : P)
  deriving @[expose] DecidableEq

/-- Mark history record `opId` with a new `status` if in bounds. -/
@[expose]
def completeHistoryAt {P Data : Type*} (hist : List (SnapshotOpRecord P Data)) (opId : ℕ)
    (st : SnapshotOpStatus P Data) : List (SnapshotOpRecord P Data) :=
  match hist[opId]? with
  | none => hist
  | some rec => hist.set opId { rec with status := st }

/-- Finish a completed `scan_i` (either returning `snap` to an external caller or advancing an
embedded `update_i` to `readyToWrite`). -/
@[expose]
def finishScan {P Data : Type*} [DecidableEq P] (s : SnapshotState P Data) (i : P)
    (mode : ScanMode Data) (opId : ℕ) (snap : P → Data) : SnapshotState P Data :=
  match mode with
  | .external =>
    { reg := s.reg
      proc := Function.update s.proc i .idle
      history := completeHistoryAt s.history opId (.doneScan s.stepCount snap)
      stepCount := s.stepCount + 1 }
  | .embedded val =>
    { reg := s.reg
      proc := Function.update s.proc i (.readyToWrite opId val snap)
      history := s.history
      stepCount := s.stepCount + 1 }

/-- Deterministic partial step function executing one atomic `SnapshotEvent` (`none` when the
precondition is not enabled). Every `.step i` accesses **at most one** shared register; relative to
[AfekAttiyaDolevGafniMerrittShavit1993] Figure 1 (p. 4), external scan completion (`finishScan`) is
fused with `.doneScan` and `update_i`'s atomic register write (`readyToWrite`) is fused with
`.doneUpdate`. -/
@[expose]
def stepSnapshot {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P) (dInit : Data)
    (s : SnapshotState P Data) (ev : SnapshotEvent P Data) : Option (SnapshotState P Data) :=
  match ev with
  | .invokeScan i =>
    match s.proc i with
    | .idle =>
      let opId := s.history.length
      let dummy := fun _ : P => SnapshotReg.init (P := P) dInit
      let st : ActiveScan P Data := ⟨.external, opId, ∅, .collectA, ord.elems, dummy, dummy⟩
      some
        { reg := s.reg
          proc := Function.update s.proc i (.scanning st)
          history := s.history ++ [⟨i, .scan, s.stepCount, .pending⟩]
          stepCount := s.stepCount + 1 }
    | _ => none
  | .invokeUpdate i val =>
    match s.proc i with
    | .idle =>
      let opId := s.history.length
      let dummy := fun _ : P => SnapshotReg.init (P := P) dInit
      let st : ActiveScan P Data := ⟨.embedded val, opId, ∅, .collectA, ord.elems, dummy, dummy⟩
      some
        { reg := s.reg
          proc := Function.update s.proc i (.scanning st)
          history := s.history ++ [⟨i, .update val, s.stepCount, .pending⟩]
          stepCount := s.stepCount + 1 }
    | _ => none
  | .step i =>
    match s.proc i with
    | .idle => none
    | .scanning st =>
      match st.phase, st.rem with
      | .collectA, j :: rest =>
        -- Atomic single-register read of `s.reg j` during `collectA`
        let st' : ActiveScan P Data :=
          { st with rem := rest, collectAVal := Function.update st.collectAVal j (s.reg j) }
        some
          { s with
            proc := Function.update s.proc i (.scanning st')
            stepCount := s.stepCount + 1 }
      | .collectA, [] =>
        -- Finished `collectA`; begin `collectB`
        let st' : ActiveScan P Data := { st with phase := .collectB, rem := ord.elems }
        some
          { s with
            proc := Function.update s.proc i (.scanning st')
            stepCount := s.stepCount + 1 }
      | .collectB, j :: rest =>
        -- Atomic single-register read of `s.reg j` during `collectB`
        let st' : ActiveScan P Data :=
          { st with rem := rest, collectBVal := Function.update st.collectBVal j (s.reg j) }
        some
          { s with
            proc := Function.update s.proc i (.scanning st')
            stepCount := s.stepCount + 1 }
      | .collectB, [] =>
        -- Local evaluation of lines 4–10 of Figure 3 (zero shared-register accesses)
        if ∀ k : P, (st.collectAVal k).seq = (st.collectBVal k).seq then
          some (finishScan s i st.mode st.opId fun k => (st.collectBVal k).data)
        else
          match ord.elems.find? fun k =>
              decide ((st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved) with
          | some k =>
            -- Borrow the embedded snapshot view written by updater `k` (moved twice!)
            some (finishScan s i st.mode st.opId (st.collectBVal k).view)
          | none =>
            -- Record all processes observed to move and start next double-collect pass
            let changed := univ.filter fun k => (st.collectAVal k).seq ≠ (st.collectBVal k).seq
            let st' : ActiveScan P Data :=
              { st with moved := st.moved ∪ changed, phase := .collectA, rem := ord.elems }
            some
              { s with
                proc := Function.update s.proc i (.scanning st')
                stepCount := s.stepCount + 1 }
    | .readyToWrite opId val snap =>
      -- Atomic single-writer write `r_i := (val, r_i.seq + 1, snap)` (line 2 of `update_i`)
      let newReg : SnapshotReg P Data := ⟨val, (s.reg i).seq + 1, snap⟩
      some
        { reg := Function.update s.reg i newReg
          proc := Function.update s.proc i .idle
          history := completeHistoryAt s.history opId (.doneUpdate s.stepCount)
          stepCount := s.stepCount + 1 }

/-- `Cslib.LTS` of the unbounded single-writer atomic snapshot implementation. -/
@[expose]
def snapshotLTS {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P) (dInit : Data) :
    Cslib.LTS (SnapshotState P Data) (SnapshotEvent P Data) where
  Tr s ev s' := stepSnapshot ord dInit s ev = some s'

/-- Reachability from `SnapshotState.init dInit` in `snapshotLTS`. -/
@[expose]
def SnapshotReachable {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) (s : SnapshotState P Data) : Prop :=
  ∃ tr : List (SnapshotEvent P Data),
    (snapshotLTS ord dInit).MTr (SnapshotState.init dInit) tr s

end Cslib.Distributed.SetAgreement
