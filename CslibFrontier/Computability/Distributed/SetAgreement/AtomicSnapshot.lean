/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
import Cslib.Foundations.Semantics.LTS.Execution
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Wait-free single-writer atomic snapshot memory

As an unbounded sequence-numbered single-writer step toward `#7504`, this module formalizes the
unbounded wait-free single-writer atomic snapshot algorithm of Afek, Attiya, Dolev, Gafni, Merritt,
and Shavit ([AfekAttiyaDolevGafniMerrittShavit1993], §§2.1, 3, Figures 1 and 3, Lemmas 3.1–3.4, and
Theorem 1; author PDF pp. 4–10, JACM 40(4):873–890).

Each process `i : P` owns a single-writer, multi-reader (`SWMR`) atomic register
`SnapshotReg P Data` holding `(data, seq, view)` (initialized to `(dInit, 0, fun _ => dInit)`).
Crucially, `collect` is **not** modeled as an atomic multi-register read: each step of `collectA`
or `collectB` reads **one** register `s.reg j` at a time along a `ScanOrder P`, allowing arbitrary
interleaved reads, writes, invocations, and crashes by other processes between any two register
reads. Relative to Figure 1 (p. 4) and §3.1 (pp. 7–8), which separate internal `Scan_i` /
`Update_i(d)` transitions from external `ScanReturn_i` / `UpdateReturn_i` outputs, `stepSnapshot`
fuses `scan_i`'s final local decision (`finishScan`) with `.doneScan` and fuses `update_i`'s atomic
register write (`readyToWrite`) with `.doneUpdate`.

* **Operations (`Figure 3`):**
  - `scan_i`: maintains `moved : Finset P` (initialized to `∅`) and repeatedly performs two
    sequential single-register-at-a-time collects `a` (`collectA`) and `b` (`collectB`). If
    `∀ j, (a j).seq = (b j).seq`, it returns `fun j => (b j).data` (successful double collect).
    Otherwise, if some process `j` with `(a j).seq ≠ (b j).seq` already belongs to `moved`
    (observed moving twice), `scan_i` borrows and returns `(b j).view`; otherwise all processes
    whose sequence numbers changed are added to `moved` and the loop repeats.
  - `update_i(val)`: executes an embedded `scan_i` to obtain a snapshot `snap`, then performs a
    single atomic write `reg i := ⟨val, (reg i).seq + 1, snap⟩`.
* **Correctness and Linearizability (`Lemmas 3.1–3.3`, `Theorem 1`, steps toward `#7504`):**
  - `SnapshotTrace.memSnapshot_eq_of_clean_double_collect` (after Lemma 3.1): if `a` and `b`
    observe identical sequence numbers across all registers, no register was written between its
    `collectA` read and its `collectB` read, so `fun j => (b j).data` equals the instantaneous
    memory state throughout the interval between the two collects.
  - `unbounded_exists_interval_snapshot_of_trace` (after Lemmas 3.2–3.3): if `scan_i` observes `j`
    move in two distinct double collects, the `update_j` that wrote the second value began strictly
    after `scan_i` started and wrote before `scan_i` finished, so its embedded view is already a
    valid snapshot inside `scan_i`'s interval; hence every completed `scan` returns `memSnapshot` at
    some historical state inside its execution interval.
  - `unbounded_snapshotLinearizable_of_reachable` (after Theorem 1): every reachable execution
    history of the unbounded sequence-numbered single-writer algorithm is Herlihy–Wing linearizable
    against the canonical single-writer snapshot sequential specification (`Figure 1`).
* **Wait-Free `O(n²)` Step Complexity (`Lemma 3.4`):**
  - Because `#moved` strictly increases on every unsuccessful double-collect iteration and is
    bounded by `n = Fintype.card P`, at most `n + 1` iterations occur. The per-process potential
    `remainingSteps` is at most `(2n + 2)(n + 1) + 1 = 2n² + 4n + 3` (`O(n²)`, with at most
    `2n(n + 1)` shared-register reads and at most `1` shared-register write), strictly decreases on
    every step of `i`, and is invariant under all steps of `j ≠ i`, yielding unconditional solo and
    concurrent wait-free termination (`exists_solo_completion`).

### Scope note

This module formalizes the **unbounded** sequence-numbered single-writer construction as a step
toward `#7504` (after [AfekAttiyaDolevGafniMerrittShavit1993], §3, Theorem 1). Their
bounded-register toggle/handshake single-writer (§4, Theorem 2) and multi-writer (§5, Theorem 3)
constructions remain open in `#7504`.

## Main definitions

* `Cslib.Distributed.SetAgreement.SnapshotReg`, `Cslib.Distributed.SetAgreement.memSnapshot`:
  single-writer `(data, seq, view)` register and instantaneous global data vector.
* `Cslib.Distributed.SetAgreement.ScanOrder`, `Cslib.Distributed.SetAgreement.ScanOrder.fin`:
  duplicate-free register collect order covering `P`.
* `Cslib.Distributed.SetAgreement.SnapshotOpKind`,
  `Cslib.Distributed.SetAgreement.SnapshotOpStatus`,
  `Cslib.Distributed.SetAgreement.SnapshotOpRecord`: client `scan` / `update` operations and
  execution history records.
* `Cslib.Distributed.SetAgreement.ScanMode`, `Cslib.Distributed.SetAgreement.CollectPhase`,
  `Cslib.Distributed.SetAgreement.ActiveScan`, `Cslib.Distributed.SetAgreement.ProcSnapshotState`,
  `Cslib.Distributed.SetAgreement.SnapshotState`, `Cslib.Distributed.SetAgreement.SnapshotEvent`:
  operational process states, global configurations, and atomic single-register LTS events.
* `Cslib.Distributed.SetAgreement.snapshotLTS`, `Cslib.Distributed.SetAgreement.SnapshotTrace`:
  labelled transition system and execution traces from `SnapshotState.init`.
* `Cslib.Distributed.SetAgreement.seqSnapshotValid`,
  `Cslib.Distributed.SetAgreement.IsSnapshotLinearization`,
  `Cslib.Distributed.SetAgreement.SnapshotLinearizable`: sequential canonical single-writer
  snapshot semantics and Herlihy–Wing linearizability.
* `Cslib.Distributed.SetAgreement.remainingSteps`,
  `Cslib.Distributed.SetAgreement.remainingRegOps`: per-process wait-free step and shared-register
  operation potentials (`O(n²)`).

## Main results

* `Cslib.Distributed.SetAgreement.SnapshotTrace.memSnapshot_eq_of_clean_double_collect`: unbounded
  clean double-collect step (after Lemma 3.1).
* `Cslib.Distributed.SetAgreement.unbounded_exists_interval_snapshot_of_trace`: unbounded interval
  snapshot step (after Lemmas 3.2–3.3).
* `Cslib.Distributed.SetAgreement.unbounded_snapshotLinearizable_of_reachable`: unbounded
  single-writer snapshot linearizability step (after Theorem 1).
* `Cslib.Distributed.SetAgreement.remainingSteps_le_quad`,
  `Cslib.Distributed.SetAgreement.remainingRegOps_invokeScan`,
  `Cslib.Distributed.SetAgreement.remainingRegOps_invokeUpdate`,
  `Cslib.Distributed.SetAgreement.remainingSteps_lt_of_step`,
  `Cslib.Distributed.SetAgreement.remainingSteps_eq_of_other`,
  `Cslib.Distributed.SetAgreement.exists_solo_completion`: wait-free `O(n²)` step and
  register-access bounds (after Lemma 3.4).

## References

* [Y. Afek, H. Attiya, D. Dolev, E. Gafni, M. Merritt, N. Shavit, *Atomic Snapshots of Shared
  Memory*][AfekAttiyaDolevGafniMerrittShavit1993]
-/

public section

namespace Cslib.Distributed.SetAgreement

open Finset

/-! ### Single-writer registers and scan orders -/

/-- Single-writer, multi-reader (`SWMR`) register owned by one process in the unbounded snapshot
algorithm ([AfekAttiyaDolevGafniMerrittShavit1993], §3, Figure 3, p. 8). -/
@[ext]
structure SnapshotReg (P Data : Type*) where
  /-- Current data word written by the owner process. -/
  data : Data
  /-- Monotone sequence number incremented by `1` on each `update` write. -/
  seq : ℕ
  /-- Snapshot view obtained by the embedded `scan` of the writing `update`. -/
  view : P → Data

instance instDecidableEqSnapshotReg {P Data : Type*} [Fintype P] [DecidableEq Data] :
    DecidableEq (SnapshotReg P Data) := fun r₁ r₂ =>
  decidable_of_iff (r₁.data = r₂.data ∧ r₁.seq = r₂.seq ∧ ∀ p, r₁.view p = r₂.view p)
    ⟨fun ⟨hd, hs, hv⟩ => SnapshotReg.ext hd hs (funext hv),
     fun h => ⟨congrArg SnapshotReg.data h, congrArg SnapshotReg.seq h,
       fun p => congrFun (congrArg SnapshotReg.view h) p⟩⟩

/-- Initial register state `(dInit, 0, fun _ => dInit)`. -/
@[expose]
def SnapshotReg.init {P Data : Type*} (dInit : Data) : SnapshotReg P Data where
  data := dInit
  seq := 0
  view _ := dInit

/-- Instantaneous snapshot of the `data` fields across all single-writer registers
(`snapshot(τ_k)` in [AfekAttiyaDolevGafniMerrittShavit1993], §3.1, p. 8). -/
@[expose]
def memSnapshot {P Data : Type*} (reg : P → SnapshotReg P Data) : P → Data :=
  fun j => (reg j).data

/-- Duplicate-free register reading order covering all processes `P` for `collect`. -/
structure ScanOrder (P : Type*) where
  /-- Ordered list of registers read during each `collect`. -/
  elems : List P
  /-- Each register appears at most once per `collect`. -/
  nodup : elems.Nodup
  /-- Every process in `P` appears in `elems`. -/
  complete : ∀ j : P, j ∈ elems

/-- Canonical `0, 1, …, n - 1` scan order on `Fin n`. -/
@[expose]
def ScanOrder.fin (n : ℕ) : ScanOrder (Fin n) where
  elems := List.finRange n
  nodup := List.nodup_finRange n
  complete := List.mem_finRange

theorem ScanOrder.length_eq_card {P : Type*} [Fintype P] (ord : ScanOrder P) :
    ord.elems.length = Fintype.card P := by
  classical
  have hfin : ord.elems.toFinset = (univ : Finset P) := by
    ext j
    simp only [List.mem_toFinset, mem_univ, iff_true]
    exact ord.complete j
  rw [← List.toFinset_card_of_nodup ord.nodup, hfin, card_univ]

/-! ### Client operations, history records, and canonical snapshot linearizability -/

/-- Client operation kind on a single-writer atomic snapshot memory. -/
inductive SnapshotOpKind (Data : Type*) where
  /-- Instantaneous full-memory read (`ScanRequest_i`). -/
  | scan
  /-- Single-writer word update (`UpdateRequest_i(val)`). -/
  | update (val : Data)
  deriving @[expose] DecidableEq

/-- Completion status of a recorded client operation in an execution history. -/
inductive SnapshotOpStatus (P Data : Type*) where
  /-- Invoked and not yet returned. -/
  | pending
  /-- Completed `scan` returning `snap` at trace transition `respStep`. -/
  | doneScan (respStep : ℕ) (snap : P → Data)
  /-- Completed `update` returning at trace transition `respStep`. -/
  | doneUpdate (respStep : ℕ)

instance instDecidableEqSnapshotOpStatus {P Data : Type*} [Fintype P] [DecidableEq Data] :
    DecidableEq (SnapshotOpStatus P Data) := fun s₁ s₂ =>
  match s₁, s₂ with
  | .pending, .pending => isTrue rfl
  | .doneScan r₁ v₁, .doneScan r₂ v₂ =>
    decidable_of_iff (r₁ = r₂ ∧ ∀ p, v₁ p = v₂ p)
      ⟨fun ⟨hr, hv⟩ => hr ▸ funext hv ▸ rfl,
       fun h => by injection h with hr hv; exact ⟨hr, fun p => congrFun hv p⟩⟩
  | .doneUpdate r₁, .doneUpdate r₂ =>
    decidable_of_iff (r₁ = r₂) ⟨fun h => h ▸ rfl, fun h => by injection h⟩
  | .pending, .doneScan _ _ | .pending, .doneUpdate _
  | .doneScan _ _, .pending | .doneScan _ _, .doneUpdate _
  | .doneUpdate _, .pending | .doneUpdate _, .doneScan _ _ => isFalse nofun

/-- Recorded operation entry in an execution history of a snapshot memory. -/
@[ext]
structure SnapshotOpRecord (P Data : Type*) where
  /-- Invoking process `i : P` (for `update`, also the updated cell index). -/
  caller : P
  /-- Operation kind (`scan` or `update val`). -/
  kind : SnapshotOpKind Data
  /-- Trace step index at which the client invoked the operation. -/
  invStep : ℕ
  /-- Current completion status and response timestamp/payload. -/
  status : SnapshotOpStatus P Data

instance instDecidableEqSnapshotOpRecord {P Data : Type*} [Fintype P] [DecidableEq P]
    [DecidableEq Data] : DecidableEq (SnapshotOpRecord P Data) := fun r₁ r₂ =>
  decidable_of_iff
    (r₁.caller = r₂.caller ∧ r₁.kind = r₂.kind ∧ r₁.invStep = r₂.invStep ∧
      r₁.status = r₂.status)
    ⟨fun ⟨hc, hk, hi, hs⟩ => SnapshotOpRecord.ext hc hk hi hs,
     fun h => ⟨congrArg SnapshotOpRecord.caller h, congrArg SnapshotOpRecord.kind h,
       congrArg SnapshotOpRecord.invStep h, congrArg SnapshotOpRecord.status h⟩⟩

/-- Whether a recorded snapshot operation has returned. -/
@[expose]
def SnapshotOpRecord.isCompleted {P Data : Type*} (rec : SnapshotOpRecord P Data) : Bool :=
  match rec.status with
  | .pending => false
  | .doneScan _ _ | .doneUpdate _ => true

/-- Response step of a completed operation (`none` if still pending). -/
@[expose]
def SnapshotOpRecord.respStep? {P Data : Type*} (rec : SnapshotOpRecord P Data) : Option ℕ :=
  match rec.status with
  | .pending => none
  | .doneScan t _ | .doneUpdate t => some t

/-- Sequential canonical single-writer snapshot check (`Figure 1` of
[AfekAttiyaDolevGafniMerrittShavit1993], p. 4): replay operation indices `seq` from initial memory
`mem : P → Data`, updating `mem caller := val` on completed updates and verifying `snap = mem` on
completed scans. -/
@[expose]
def seqSnapshotValid {P Data : Type*} [DecidableEq P] (mem : P → Data)
    (hist : List (SnapshotOpRecord P Data)) : List ℕ → Prop
  | [] => True
  | idx :: rest =>
    match hist[idx]? with
    | none => False
    | some rec =>
      match rec.kind, rec.status with
      | .scan, .doneScan _ snap =>
        snap = mem ∧ seqSnapshotValid mem hist rest
      | .update val, .doneUpdate _ =>
        seqSnapshotValid (Function.update mem rec.caller val) hist rest
      | .update val, .pending =>
        seqSnapshotValid (Function.update mem rec.caller val) hist rest
      | _, _ => False

/-- Sequential memory state produced after replaying a list of operation indices from `mem`. -/
@[expose]
def seqSnapshotMemAfter {P Data : Type*} [DecidableEq P] (mem : P → Data)
    (hist : List (SnapshotOpRecord P Data)) : List ℕ → (P → Data)
  | [] => mem
  | idx :: rest =>
    let mem' :=
      match hist[idx]? with
      | some rec =>
        match rec.kind with
        | .update val => Function.update mem rec.caller val
        | .scan => mem
      | none => mem
    seqSnapshotMemAfter mem' hist rest

theorem seqSnapshotValid_append {P Data : Type*} [DecidableEq P] (mem : P → Data)
    (hist : List (SnapshotOpRecord P Data)) (xs ys : List ℕ) :
    seqSnapshotValid mem hist (xs ++ ys) ↔
      seqSnapshotValid mem hist xs ∧
        seqSnapshotValid (seqSnapshotMemAfter mem hist xs) hist ys := by
  induction xs generalizing mem with
  | nil => simp only [List.nil_append, seqSnapshotValid, seqSnapshotMemAfter, true_and]
  | cons idx xs ih =>
    simp only [List.cons_append, seqSnapshotValid, seqSnapshotMemAfter]
    cases hget : hist[idx]? with
    | none => simp only [false_and]
    | some rec =>
      rcases rec with ⟨caller, kind, invStep, status⟩
      cases kind with
      | scan =>
        cases status with
        | pending => simp only [false_and]
        | doneScan t snap =>
          rw [ih mem, and_assoc]
        | doneUpdate t => simp only [false_and]
      | update val =>
        cases status with
        | pending => exact ih (Function.update mem caller val)
        | doneScan t snap => simp only [false_and]
        | doneUpdate t => exact ih (Function.update mem caller val)

/-- `seq` is a valid Herlihy–Wing linearization of snapshot history `hist` from initial value
`dInit` ([AfekAttiyaDolevGafniMerrittShavit1993], §2.1, Definition 1):
1. `seq` is duplicate-free (`seq.Nodup`) with all indices `< hist.length`,
2. every completed operation in `hist` appears in `seq` (and any other entry in `seq` is a pending
   `update` that has already taken effect),
3. real-time precedence holds (`respStep op₁ ≤ invStep op₂` implies `op₁` precedes `op₂` in `seq`),
4. `seqSnapshotValid (fun _ => dInit) hist seq` holds. -/
structure IsSnapshotLinearization {P Data : Type*} [DecidableEq P] (dInit : Data)
    (hist : List (SnapshotOpRecord P Data)) (seq : List ℕ) : Prop where
  /-- No operation is linearized twice. -/
  nodup : seq.Nodup
  /-- Every index in `seq` refers to a valid entry in `hist`. -/
  index_lt : ∀ i ∈ seq, i < hist.length
  /-- Every completed operation in `hist` is linearized in `seq`. -/
  complete : ∀ i (hi : i < hist.length), hist[i].isCompleted = true → i ∈ seq
  /-- Real-time order: if `i` returned at step `r` and `j` was invoked at step `u` with `r ≤ u`,
  then `i` precedes `j` in `seq`. -/
  realTime : ∀ i ∈ seq, ∀ j ∈ seq, ∀ r,
    (hist[i]?.bind SnapshotOpRecord.respStep?) = some r →
    ∀ recJ, hist[j]? = some recJ → r ≤ recJ.invStep →
    seq.idxOf i < seq.idxOf j
  /-- Sequential canonical single-writer snapshot validity along `seq`. -/
  valid : seqSnapshotValid (fun _ => dInit) hist seq

/-- An execution history `hist` is *linearizable* against the canonical single-writer snapshot
memory with initial value `dInit`. -/
@[expose]
def SnapshotLinearizable {P Data : Type*} [DecidableEq P] (dInit : Data)
    (hist : List (SnapshotOpRecord P Data)) : Prop :=
  ∃ seq : List ℕ, IsSnapshotLinearization dInit hist seq

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

@[simp]
private theorem length_completeHistoryAt {P Data : Type*} (hist : List (SnapshotOpRecord P Data))
    (opId : ℕ) (st : SnapshotOpStatus P Data) :
    (completeHistoryAt hist opId st).length = hist.length := by
  unfold completeHistoryAt
  cases hist[opId]? with
  | none => rfl
  | some _ => exact List.length_set

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

/-! ### Wait-free `O(n²)` step complexity (`Lemma 3.4`) -/

/-- Remaining protocol steps (including local loop-boundary evaluations) for process `i` to finish
its current operation (`0` when `idle`). -/
@[expose]
def remainingSteps {P Data : Type*} (ord : ScanOrder P) :
    ProcSnapshotState P Data → ℕ
  | .idle => 0
  | .readyToWrite _ _ _ => 1
  | .scanning st =>
    let n := ord.elems.length
    let remIters := n - #st.moved
    let iterRem :=
      match st.phase with
      | .collectA => st.rem.length + n + 2
      | .collectB => st.rem.length + 1
    let writeStep := match st.mode with | .external => 0 | .embedded _ => 1
    remIters * (2 * n + 2) + iterRem + writeStep

/-- Remaining shared-register operations (`Read` or `Write`, excluding purely local transitions)
for process `i` to finish its current operation (`0` when `idle`). -/
@[expose]
def remainingRegOps {P Data : Type*} (ord : ScanOrder P) :
    ProcSnapshotState P Data → ℕ
  | .idle => 0
  | .readyToWrite _ _ _ => 1
  | .scanning st =>
    let n := ord.elems.length
    let remIters := n - #st.moved
    let iterReads :=
      match st.phase with
      | .collectA => st.rem.length + n
      | .collectB => st.rem.length
    let writeOp := match st.mode with | .external => 0 | .embedded _ => 1
    remIters * (2 * n) + iterReads + writeOp

/-- Whether transition `stepSnapshot ord dInit s (.step i)` performs a shared-register `Read` or
`Write` (`true`) versus a local loop evaluation (`false`). -/
@[expose]
def isRegAccessStep {P Data : Type*} (s : SnapshotState P Data) (i : P) : Bool :=
  match s.proc i with
  | .idle => false
  | .readyToWrite _ _ _ => true
  | .scanning st =>
    match st.rem with
    | _ :: _ => true
    | [] => false

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemma 3.4, p. 10][AfekAttiyaDolevGafniMerrittShavit1993]): in every state with
`st.rem.length ≤ n`, `remainingSteps` is at most `(2n + 2)(n + 1) + 1 = 2n² + 4n + 3` where
`n = Fintype.card P`. -/
theorem remainingSteps_le_quad {P Data : Type*} [Fintype P] (ord : ScanOrder P)
    (ps : ProcSnapshotState P Data)
    (hrem : ∀ st, ps = .scanning st → st.rem.length ≤ ord.elems.length) :
    remainingSteps ord ps ≤
      (2 * Fintype.card P + 2) * (Fintype.card P + 1) + 1 := by
  have hn := ord.length_eq_card
  cases ps with
  | idle =>
    simp only [remainingSteps]
    omega
  | readyToWrite _ _ _ =>
    simp only [remainingSteps]
    omega
  | scanning st =>
    have hr := hrem st rfl
    simp only [remainingSteps]
    have hle : ord.elems.length - #st.moved ≤ ord.elems.length := Nat.sub_le _ _
    have hmul : (ord.elems.length - #st.moved) * (2 * ord.elems.length + 2) ≤
        ord.elems.length * (2 * ord.elems.length + 2) :=
      Nat.mul_le_mul_right _ hle
    cases st.phase <;> cases st.mode <;> dsimp only <;> nlinarith

private def SnapshotEvent.actor {P Data : Type*} : SnapshotEvent P Data → P
  | .invokeScan j | .invokeUpdate j _ | .step j => j

private theorem stepSnapshot_invokeScan_eq {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} {s s' : SnapshotState P Data} {i : P}
    (h : stepSnapshot ord dInit s (.invokeScan i) = some s') :
    s.proc i = .idle ∧
      (let opId := s.history.length
       let dummy := fun _ : P => SnapshotReg.init (P := P) dInit
       let st : ActiveScan P Data := ⟨.external, opId, ∅, .collectA, ord.elems, dummy, dummy⟩
       ({ s with
           proc := Function.update s.proc i (.scanning st)
           history := s.history ++ [⟨i, .scan, s.stepCount, .pending⟩]
           stepCount := s.stepCount + 1 } : SnapshotState P Data) = s') := by
  unfold stepSnapshot at h
  cases hpi : s.proc i <;> simp only [hpi, Option.some.injEq, reduceCtorEq] at h
  exact ⟨rfl, h⟩

private theorem stepSnapshot_invokeUpdate_eq {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} {s s' : SnapshotState P Data} {i : P} {val : Data}
    (h : stepSnapshot ord dInit s (.invokeUpdate i val) = some s') :
    s.proc i = .idle ∧
      (let opId := s.history.length
       let dummy := fun _ : P => SnapshotReg.init (P := P) dInit
       let st : ActiveScan P Data := ⟨.embedded val, opId, ∅, .collectA, ord.elems, dummy, dummy⟩
       ({ s with
           proc := Function.update s.proc i (.scanning st)
           history := s.history ++ [⟨i, .update val, s.stepCount, .pending⟩]
           stepCount := s.stepCount + 1 } : SnapshotState P Data) = s') := by
  unfold stepSnapshot at h
  cases hpi : s.proc i <;> simp only [hpi, Option.some.injEq, reduceCtorEq] at h
  exact ⟨rfl, h⟩

/-- Every transition `stepSnapshot ord dInit s ev = some s'` updates `proc` only at `ev.actor`,
and either performs a `readyToWrite` register write or leaves `s.reg` unchanged while modifying
`s.history` by at most appending a `.pending` record or completing a `.scan` record. -/
private theorem stepSnapshot_effect {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} {s s' : SnapshotState P Data} {ev : SnapshotEvent P Data}
    (h : stepSnapshot ord dInit s ev = some s') :
    (∃ ps, s'.proc = Function.update s.proc ev.actor ps) ∧
      ((∃ j opId val snap,
          ev = .step j ∧
          s.proc j = .readyToWrite opId val snap ∧
          s' = { reg := Function.update s.reg j ⟨val, (s.reg j).seq + 1, snap⟩
                 proc := Function.update s.proc j .idle
                 history := completeHistoryAt s.history opId (.doneUpdate s.stepCount)
                 stepCount := s.stepCount + 1 }) ∨
        ((¬∃ j opId val snap, ev = .step j ∧ s.proc j = .readyToWrite opId val snap) ∧
          s'.reg = s.reg ∧
          (s'.history = s.history ∨
            (∃ rec, rec.status = .pending ∧ s'.history = s.history ++ [rec]) ∨
            (∃ j st snap, ev = .step j ∧ s.proc j = .scanning st ∧ st.mode = .external ∧
              s'.history =
                completeHistoryAt s.history st.opId (.doneScan s.stepCount snap))))) := by
  have finishScan_eff : ∀ {j : P} {st : ActiveScan P Data} (snap : P → Data)
      (hscan : s.proc j = .scanning st) (hfin : finishScan s j st.mode st.opId snap = s'),
      (∃ ps, s'.proc = Function.update s.proc j ps) ∧
        s'.reg = s.reg ∧
        (s'.history = s.history ∨
          (∃ rec, rec.status = .pending ∧ s'.history = s.history ++ [rec]) ∨
          (∃ j' st' snap', SnapshotEvent.step (Data := Data) j = .step j' ∧
            s.proc j' = .scanning st' ∧ st'.mode = .external ∧
            s'.history = completeHistoryAt s.history st'.opId (.doneScan s.stepCount snap'))) := by
    intro j st snap hscan hfin
    subst hfin
    cases hm : st.mode with
    | external =>
      exact ⟨⟨.idle, rfl⟩, rfl, Or.inr (Or.inr ⟨j, st, snap, rfl, hscan, hm, rfl⟩)⟩
    | embedded val =>
      exact ⟨⟨.readyToWrite st.opId val snap, rfl⟩, rfl, Or.inl rfl⟩
  rcases ev with j | ⟨j, val⟩ | j
  · obtain ⟨-, rfl⟩ := stepSnapshot_invokeScan_eq h
    exact ⟨⟨_, rfl⟩, Or.inr ⟨(by rintro ⟨_, _, _, _, h1, _⟩; cases h1), rfl,
      Or.inr (Or.inl ⟨_, rfl, rfl⟩)⟩⟩
  · obtain ⟨-, rfl⟩ := stepSnapshot_invokeUpdate_eq h
    exact ⟨⟨_, rfl⟩, Or.inr ⟨(by rintro ⟨_, _, _, _, h1, _⟩; cases h1), rfl,
      Or.inr (Or.inl ⟨_, rfl, rfl⟩)⟩⟩
  · unfold stepSnapshot at h
    cases hpj : s.proc j with
    | idle => simp only [hpj] at h; nomatch h
    | readyToWrite opId val snap =>
      simp only [hpj, Option.some.injEq] at h
      subst h
      exact ⟨⟨.idle, rfl⟩, Or.inl ⟨j, opId, val, snap, rfl, hpj, rfl⟩⟩
    | scanning st =>
      simp only [hpj] at h
      have hnw : ¬∃ j' opId val snap,
          SnapshotEvent.step (Data := Data) j = .step j' ∧
            s.proc j' = .readyToWrite opId val snap := by
        rintro ⟨_, _, _, _, h1, h2⟩; cases h1; rw [hpj] at h2; cases h2
      cases hph : st.phase <;> cases hrem : st.rem <;> simp only [hph, hrem] at h
      · injection h with hs'; subst hs'; exact ⟨⟨_, rfl⟩, Or.inr ⟨hnw, rfl, Or.inl rfl⟩⟩
      · injection h with hs'; subst hs'; exact ⟨⟨_, rfl⟩, Or.inr ⟨hnw, rfl, Or.inl rfl⟩⟩
      · split_ifs at h with hclean
        · injection h with hs'
          obtain ⟨hp, hr, hh⟩ := finishScan_eff _ hpj hs'
          exact ⟨hp, Or.inr ⟨hnw, hr, hh⟩⟩
        · cases hfind : (ord.elems.find? fun k =>
              decide ((st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved)) <;>
            simp only [hfind, Option.some.injEq] at h
          · subst h; exact ⟨⟨_, rfl⟩, Or.inr ⟨hnw, rfl, Or.inl rfl⟩⟩
          · obtain ⟨hp, hr, hh⟩ := finishScan_eff _ hpj h
            exact ⟨hp, Or.inr ⟨hnw, hr, hh⟩⟩
      · injection h with hs'; subst hs'; exact ⟨⟨_, rfl⟩, Or.inr ⟨hnw, rfl, Or.inl rfl⟩⟩

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemma 3.4, p. 10][AfekAttiyaDolevGafniMerrittShavit1993]): immediately after
`invokeScan i`, `remainingRegOps` equals `2 * n * (n + 1)` (`O(n²)` shared-register reads, bounded
across subsequent steps by `remainingSteps_lt_of_step`). -/
theorem remainingRegOps_invokeScan {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) {s s' : SnapshotState P Data} {i : P}
    (h : stepSnapshot ord dInit s (.invokeScan i) = some s') :
    remainingRegOps ord (s'.proc i) = 2 * Fintype.card P * (Fintype.card P + 1) := by
  obtain ⟨-, rfl⟩ := stepSnapshot_invokeScan_eq h
  simp only [Function.update_self, remainingRegOps, card_empty, Nat.sub_zero,
    ord.length_eq_card]
  ring

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemma 3.4, p. 10][AfekAttiyaDolevGafniMerrittShavit1993]): immediately after
`invokeUpdate i val`, `remainingRegOps` equals `2 * n * (n + 1) + 1` (`O(n²)` shared-register reads
plus `1` write, bounded across subsequent steps by `remainingSteps_lt_of_step`). -/
theorem remainingRegOps_invokeUpdate {P Data : Type*} [Fintype P] [DecidableEq P]
    (ord : ScanOrder P) (dInit : Data) {s s' : SnapshotState P Data} {i : P} {val : Data}
    (h : stepSnapshot ord dInit s (.invokeUpdate i val) = some s') :
    remainingRegOps ord (s'.proc i) = 2 * Fintype.card P * (Fintype.card P + 1) + 1 := by
  obtain ⟨-, rfl⟩ := stepSnapshot_invokeUpdate_eq h
  simp only [Function.update_self, remainingRegOps, card_empty, Nat.sub_zero,
    ord.length_eq_card]
  ring

/-- Any event performed by another process `j ≠ i` leaves `i`'s local state and `remainingSteps`
completely unchanged. -/
theorem proc_eq_of_other_event {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) {s s' : SnapshotState P Data} {ev : SnapshotEvent P Data} {i : P}
    (hne : ev ≠ .invokeScan i ∧ (∀ v, ev ≠ .invokeUpdate i v) ∧ ev ≠ .step i)
    (h : stepSnapshot ord dInit s ev = some s') :
    s'.proc i = s.proc i := by
  obtain ⟨⟨ps, hproc⟩, -⟩ := stepSnapshot_effect h
  have hij : i ≠ ev.actor := by
    rcases ev with j | ⟨j, v⟩ | j <;> intro heq <;> subst heq
    · exact hne.1 rfl
    · exact hne.2.1 v rfl
    · exact hne.2.2 rfl
  rw [hproc, Function.update_of_ne hij]

theorem remainingSteps_eq_of_other {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) {s s' : SnapshotState P Data} {ev : SnapshotEvent P Data} {i : P}
    (hne : ev ≠ .invokeScan i ∧ (∀ v, ev ≠ .invokeUpdate i v) ∧ ev ≠ .step i)
    (h : stepSnapshot ord dInit s ev = some s') :
    remainingSteps ord (s'.proc i) = remainingSteps ord (s.proc i) :=
  congrArg (remainingSteps ord) (proc_eq_of_other_event ord dInit hne h)

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemma 3.4, p. 10][AfekAttiyaDolevGafniMerrittShavit1993]): every atomic `.step i` of
an active process `i` strictly decreases `remainingSteps ord (s.proc i)`, and decreases
`remainingRegOps` whenever a shared register is accessed (`isRegAccessStep`). -/
theorem remainingSteps_lt_of_step {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) {s s' : SnapshotState P Data} {i : P}
    (h : stepSnapshot ord dInit s (.step i) = some s') :
    remainingSteps ord (s'.proc i) < remainingSteps ord (s.proc i) ∧
      remainingRegOps ord (s'.proc i) + (if isRegAccessStep s i then 1 else 0) ≤
        remainingRegOps ord (s.proc i) := by
  unfold stepSnapshot at h
  cases hpi : s.proc i with
  | idle => simp only [hpi] at h; nomatch h
  | readyToWrite opId val snap =>
    simp only [hpi] at h
    injection h with hs'
    subst hs'
    simp only [isRegAccessStep, hpi, ↓reduceIte, Function.update_self, remainingSteps,
      remainingRegOps, Nat.zero_lt_one, le_refl, and_self]
  | scanning st =>
    simp only [hpi] at h
    cases hph : st.phase with
    | collectA =>
      cases hrem : st.rem with
      | cons j rest =>
        simp only [hph, hrem] at h
        injection h with hs'
        subst hs'
        simp only [isRegAccessStep, hpi, hrem, ↓reduceIte, Function.update_self,
          remainingSteps, remainingRegOps, hph, List.length_cons]
        cases st.mode <;> dsimp only <;> constructor <;> omega
      | nil =>
        simp only [hph, hrem] at h
        injection h with hs'
        subst hs'
        simp only [isRegAccessStep, hpi, hrem, Bool.false_eq_true, ↓reduceIte,
          Function.update_self, remainingSteps, remainingRegOps, hph, List.length_nil]
        cases st.mode <;> dsimp only <;> constructor <;> omega
    | collectB =>
      cases hrem : st.rem with
      | cons j rest =>
        simp only [hph, hrem] at h
        injection h with hs'
        subst hs'
        simp only [isRegAccessStep, hpi, hrem, ↓reduceIte, Function.update_self,
          remainingSteps, remainingRegOps, hph, List.length_cons]
        cases st.mode <;> dsimp only <;> constructor <;> omega
      | nil =>
        simp only [hph, hrem] at h
        split_ifs at h with hclean
        · injection h with hs'
          subst hs'
          simp only [isRegAccessStep, hpi, hrem, Bool.false_eq_true, ↓reduceIte,
            remainingSteps, remainingRegOps, hph, List.length_nil]
          unfold finishScan
          cases st.mode <;> simp only [Function.update_self] <;> constructor <;> omega
        · cases hfind : (ord.elems.find? fun k =>
              decide ((st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved)) with
          | some k =>
            simp only [hfind] at h
            injection h with hs'
            subst hs'
            simp only [isRegAccessStep, hpi, hrem, Bool.false_eq_true, ↓reduceIte,
              remainingSteps, remainingRegOps, hph, List.length_nil]
            unfold finishScan
            cases st.mode <;> simp only [Function.update_self] <;> constructor <;> omega
          | none =>
            simp only [hfind] at h
            injection h with hs'
            subst hs'
            -- Since `¬ hclean` and `find? = none`, some `k₀` moved with `k₀ ∉ st.moved`!
            push Not at hclean
            obtain ⟨k₀, hk₀_ne⟩ := hclean
            have hk₀_not_moved : k₀ ∉ st.moved := by
              intro hk₀_in
              have hnone := List.find?_eq_none.mp hfind k₀ (ord.complete k₀)
              simp only [decide_eq_true_eq, not_and] at hnone
              exact hnone hk₀_ne hk₀_in
            set changed := univ.filter fun k => (st.collectAVal k).seq ≠ (st.collectBVal k).seq
            have hsub : insert k₀ st.moved ⊆ st.moved ∪ changed := by
              intro x hx
              rcases mem_insert.mp hx with rfl | hx
              · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ x, hk₀_ne⟩)
              · exact mem_union_left _ hx
            have hcard_lt : #st.moved < #(st.moved ∪ changed) := by
              calc #st.moved < #(insert k₀ st.moved) := by
                    rw [card_insert_of_notMem hk₀_not_moved]
                    omega
                _ ≤ #(st.moved ∪ changed) := card_le_card hsub
            have hcard_ub : #(st.moved ∪ changed) ≤ ord.elems.length := by
              rw [ord.length_eq_card]
              exact card_le_univ _
            have hrem_lt : ord.elems.length - #(st.moved ∪ changed) + 1 ≤
                ord.elems.length - #st.moved := by
              omega
            simp only [isRegAccessStep, hpi, hrem, Bool.false_eq_true, ↓reduceIte,
              Function.update_self, remainingSteps, remainingRegOps, hph, List.length_nil,
              Nat.add_zero]
            have hmul₁ :
                (ord.elems.length - #(st.moved ∪ changed) + 1) * (2 * ord.elems.length + 2) ≤
                (ord.elems.length - #st.moved) * (2 * ord.elems.length + 2) :=
              Nat.mul_le_mul_right _ hrem_lt
            have hmul₂ :
                (ord.elems.length - #(st.moved ∪ changed) + 1) * (2 * ord.elems.length) ≤
                (ord.elems.length - #st.moved) * (2 * ord.elems.length) :=
              Nat.mul_le_mul_right _ hrem_lt
            cases st.mode <;> dsimp only <;> constructor <;> nlinarith

/-- Whenever `s.proc i ≠ .idle`, `.step i` is enabled (`stepSnapshot ord dInit s (.step i)` returns
`some s'`). -/
theorem step_enabled_of_not_idle {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) (s : SnapshotState P Data) (i : P) (hact : s.proc i ≠ .idle) :
    ∃ s', stepSnapshot ord dInit s (.step i) = some s' := by
  unfold stepSnapshot
  cases hpi : s.proc i with
  | idle => exact absurd hpi hact
  | readyToWrite opId val snap =>
    simp only [hpi]
    exact ⟨_, rfl⟩
  | scanning st =>
    simp only [hpi]
    cases st.phase <;> cases st.rem
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · split_ifs
      · exact ⟨_, rfl⟩
      · cases (ord.elems.find? fun k =>
            decide ((st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved)) <;>
          exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemma 3.4, p. 10][AfekAttiyaDolevGafniMerrittShavit1993]): from any state `s`, running
process `i` alone drives `i` to `.idle` in at most `remainingSteps ord (s.proc i)` transitions. -/
theorem exists_solo_completion {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) (s : SnapshotState P Data) (i : P) :
    ∃ (k : ℕ) (s' : SnapshotState P Data),
      k ≤ remainingSteps ord (s.proc i) ∧
      (snapshotLTS ord dInit).MTr s (List.replicate k (.step i)) s' ∧
      s'.proc i = .idle := by
  by_cases hact : s.proc i = .idle
  · exact ⟨0, s, Nat.zero_le _, Cslib.LTS.MTr.refl, hact⟩
  · obtain ⟨s₁, hs₁⟩ := step_enabled_of_not_idle ord dInit s i hact
    have hlt := (remainingSteps_lt_of_step ord dInit hs₁).1
    obtain ⟨k, s', hk_le, hmtr, hidle⟩ := exists_solo_completion ord dInit s₁ i
    refine ⟨k + 1, s', by omega, ?_, hidle⟩
    rw [List.replicate_succ]
    exact Cslib.LTS.MTr.stepL hs₁ hmtr
termination_by remainingSteps ord (s.proc i)

/-! ### Execution traces, Lemmas 3.1–3.3, and Theorem 1 (Linearizability) -/

/-- An indexed execution trace of `snapshotLTS ord dInit` starting from `SnapshotState.init dInit`:
`states` has length `events.length + 1`, `states[0] = init`, and each `events[t]` steps `states[t]`
to `states[t + 1]`. -/
structure SnapshotTrace {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) where
  /-- Sequence of executed atomic events. -/
  events : List (SnapshotEvent P Data)
  /-- Sequence of visited configurations (`length = events.length + 1`). -/
  states : List (SnapshotState P Data)
  /-- Length alignment. -/
  states_length : states.length = events.length + 1
  /-- Initial configuration is `SnapshotState.init dInit`. -/
  head_eq : states[0]'(by omega) = SnapshotState.init dInit
  /-- Valid step relation at every index `t < events.length`. -/
  step_valid : ∀ t (ht : t < events.length),
    stepSnapshot ord dInit (states[t]'(by omega)) events[t] =
      some (states[t + 1]'(by omega))

namespace SnapshotTrace

variable {P Data : Type*} [Fintype P] [DecidableEq P] {ord : ScanOrder P} {dInit : Data}

/-- State at index `t` of trace `τ` (clamped at the final state if `t ≥ τ.states.length`). -/
@[expose]
def stateAt (τ : SnapshotTrace ord dInit) (t : ℕ) : SnapshotState P Data :=
  if ht : t < τ.states.length then τ.states[t]
  else τ.states[τ.events.length]'(by have := τ.states_length; omega)

@[simp]
theorem stateAt_zero (τ : SnapshotTrace ord dInit) : τ.stateAt 0 = SnapshotState.init dInit := by
  have h0 : 0 < τ.states.length := by have := τ.states_length; omega
  simp only [stateAt, h0, ↓reduceDIte, τ.head_eq]

theorem stateAt_step (τ : SnapshotTrace ord dInit) {t : ℕ} (ht : t < τ.events.length) :
    stepSnapshot ord dInit (τ.stateAt t) τ.events[t] = some (τ.stateAt (t + 1)) := by
  have ht₁ : t < τ.states.length := by have := τ.states_length; omega
  have ht₂ : t + 1 < τ.states.length := by have := τ.states_length; omega
  simp only [stateAt, ht₁, ht₂, ↓reduceDIte]
  exact τ.step_valid t ht

/-- Convert any `MTr` reachability derivation from `init` into a `SnapshotTrace`. -/
theorem of_mtr {tr : List (SnapshotEvent P Data)} {s : SnapshotState P Data}
    (hmtr : (snapshotLTS ord dInit).MTr (SnapshotState.init dInit) tr s) :
    ∃ τ : SnapshotTrace ord dInit, τ.events = tr ∧ τ.stateAt tr.length = s := by
  obtain ⟨states, hex⟩ := Cslib.LTS.Execution.of_mTr hmtr
  refine ⟨⟨tr, states, hex.length, hex.start, hex.trans⟩, rfl, ?_⟩
  have hlt : tr.length < states.length := by have := hex.length; omega
  simp only [stateAt, hlt, ↓reduceDIte, hex.last']

/-- Predicate identifying when event `t < τ.events.length` is the atomic register write of
`update_j` (`proc j = .readyToWrite ...` and `events[t] = .step j`). -/
private def isWriteStep (τ : SnapshotTrace ord dInit) (j : P) (t : ℕ) : Prop :=
  ∃ (ht : t < τ.events.length) (opId : ℕ) (val : Data) (snap : P → Data),
    τ.events[t]'ht = .step j ∧ (τ.stateAt t).proc j = .readyToWrite opId val snap

/-- Single-step register change characterization: `reg j` changes at step `t` **if and only if**
`isWriteStep τ j t` holds, in which case `(reg j).seq` increments by `1`. -/
private theorem reg_step_iff (τ : SnapshotTrace ord dInit) (j : P) {t : ℕ}
    (ht : t < τ.events.length) :
    ((τ.stateAt (t + 1)).reg j = (τ.stateAt t).reg j ∧ ¬ τ.isWriteStep j t) ∨
      ∃ opId val snap,
        τ.events[t] = .step j ∧
        (τ.stateAt t).proc j = .readyToWrite opId val snap ∧
        (τ.stateAt (t + 1)).reg j = ⟨val, ((τ.stateAt t).reg j).seq + 1, snap⟩ ∧
        (τ.stateAt (t + 1)).proc j = .idle := by
  rcases (stepSnapshot_effect (τ.stateAt_step ht)).2 with
      ⟨i, opId, val, snap, hev, hpi, hs'⟩ | ⟨hnw, hreg, -⟩
  · by_cases hij : j = i
    · subst hij
      right
      refine ⟨opId, val, snap, hev, hpi, ?_, ?_⟩ <;> simp only [hs', Function.update_self]
    · left
      refine ⟨by simp only [hs', Function.update_of_ne hij], ?_⟩
      rintro ⟨_, _, _, _, h1, _⟩
      exact hij (SnapshotEvent.step.inj (h1.symm.trans hev))
  · exact Or.inl ⟨congrFun hreg j, fun ⟨_, id, v, sn, he, hp⟩ => hnw ⟨j, id, v, sn, he, hp⟩⟩

/-- Sequence numbers on `reg j` are monotone along any trace, and equal across `[t₁, t₂]` iff
`reg j` is constant across `[t₁, t₂]`. -/
private theorem seq_mono_and_const_of_eq (τ : SnapshotTrace ord dInit) (j : P) {t₁ t₂ : ℕ}
    (hle : t₁ ≤ t₂) (ht₂ : t₂ ≤ τ.events.length) :
    ((τ.stateAt t₁).reg j).seq ≤ ((τ.stateAt t₂).reg j).seq ∧
      (((τ.stateAt t₁).reg j).seq = ((τ.stateAt t₂).reg j).seq →
        ∀ v, t₁ ≤ v → v ≤ t₂ → (τ.stateAt v).reg j = (τ.stateAt t₂).reg j) := by
  induction t₂ with
  | zero =>
    have ht₁ : t₁ = 0 := Nat.eq_zero_of_le_zero hle
    subst ht₁
    refine ⟨le_rfl, fun _ v _ hv => ?_⟩
    rw [Nat.eq_zero_of_le_zero hv]
  | succ t₂ ih =>
    by_cases hlt : t₁ ≤ t₂
    · obtain ⟨hmono, hconst⟩ := ih hlt (Nat.le_of_succ_le ht₂)
      rcases τ.reg_step_iff j (Nat.lt_of_succ_le ht₂) with ⟨hreg_eq, -⟩ |
          ⟨_, _, _, -, -, hreg_upd, -⟩
      · refine ⟨hreg_eq ▸ hmono, fun hseq v hv₁ hv₂ => ?_⟩
        rw [hreg_eq] at hseq ⊢
        rcases Nat.of_le_succ hv₂ with hv₂' | rfl
        · exact hconst hseq v hv₁ hv₂'
        · exact hreg_eq
      · have hseq_succ : ((τ.stateAt (t₂ + 1)).reg j).seq = ((τ.stateAt t₂).reg j).seq + 1 := by
          rw [hreg_upd]
        exact ⟨by omega, fun hseq => absurd hseq (by omega)⟩
    · have heq : t₁ = t₂ + 1 := by omega
      subst heq
      exact ⟨le_rfl, fun _ v hv₁ hv₂ => by rw [Nat.le_antisymm hv₂ hv₁]⟩

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemma 3.1, p. 9][AfekAttiyaDolevGafniMerrittShavit1993]): suppose for each process
`j : P`, `a j = (τ.stateAt (tA j)).reg j` and `b j = (τ.stateAt (tB j)).reg j` with
`tA j ≤ u ≤ w ≤ tB j ≤ τ.events.length`. If `∀ j, (a j).seq = (b j).seq`, then for every state index
`v` with `u ≤ v ≤ w`, `memSnapshot (τ.stateAt v).reg = fun j => (b j).data`. -/
theorem memSnapshot_eq_of_clean_double_collect (τ : SnapshotTrace ord dInit)
    {tA tB : P → ℕ} {u w : ℕ}
    (htA : ∀ j, tA j ≤ u) (huw : u ≤ w) (htB : ∀ j, w ≤ tB j)
    (hbound : ∀ j, tB j ≤ τ.events.length)
    (hseq : ∀ j, ((τ.stateAt (tA j)).reg j).seq = ((τ.stateAt (tB j)).reg j).seq)
    {v : ℕ} (huv : u ≤ v) (hvw : v ≤ w) :
    memSnapshot (τ.stateAt v).reg = fun j => ((τ.stateAt (tB j)).reg j).data := by
  funext j
  have hle : tA j ≤ tB j := le_trans (htA j) (le_trans huw (htB j))
  have hreg := (τ.seq_mono_and_const_of_eq j hle (hbound j)).2 (hseq j) v
    (le_trans (htA j) huv) (le_trans hvw (htB j))
  exact congrArg SnapshotReg.data hreg

/-- If `((τ.stateAt t₁).reg j).seq ≠ ((τ.stateAt t₂).reg j).seq` for `t₁ ≤ t₂ ≤ τ.events.length`,
then `j` executed an atomic register write `isWriteStep τ j w` at some step `t₁ ≤ w < t₂`. -/
private theorem exists_writeStep_of_seq_ne (τ : SnapshotTrace ord dInit) (j : P) {t₁ t₂ : ℕ}
    (hle : t₁ ≤ t₂) (ht₂ : t₂ ≤ τ.events.length)
    (hne : ((τ.stateAt t₁).reg j).seq ≠ ((τ.stateAt t₂).reg j).seq) :
    ∃ w, t₁ ≤ w ∧ w < t₂ ∧ τ.isWriteStep j w := by
  induction t₂ with
  | zero =>
    rw [Nat.eq_zero_of_le_zero hle] at hne
    exact absurd rfl hne
  | succ t₂ ih =>
    by_cases hlt : t₁ ≤ t₂
    · rcases τ.reg_step_iff j (Nat.lt_of_succ_le ht₂) with ⟨hreg_eq, -⟩ |
          ⟨opId, val, snap, hev, hproc, -, -⟩
      · rw [hreg_eq] at hne
        obtain ⟨w, hw₁, hw₂, hw⟩ := ih hlt (Nat.le_of_succ_le ht₂) hne
        exact ⟨w, hw₁, Nat.lt_succ_of_lt hw₂, hw⟩
      · exact ⟨t₂, hlt, Nat.lt_succ_self t₂,
          ⟨Nat.lt_of_succ_le ht₂, opId, val, snap, hev, hproc⟩⟩
    · have heq : t₁ = t₂ + 1 := by omega
      subst heq
      exact absurd rfl hne

/-- If `(τ.stateAt t).reg j` has `.seq > 0` (`t ≤ τ.events.length`), there is a most recent
`isWriteStep τ j w` with `w < t` such that `(τ.stateAt t).reg j = (τ.stateAt (w + 1)).reg j` and
no write by `j` occurred in `[w + 1, t)`. -/
private theorem exists_last_writeStep_of_seq_pos (τ : SnapshotTrace ord dInit) (j : P) {t : ℕ}
    (ht : t ≤ τ.events.length) (hpos : 0 < ((τ.stateAt t).reg j).seq) :
    ∃ w, w < t ∧ τ.isWriteStep j w ∧
      (τ.stateAt t).reg j = (τ.stateAt (w + 1)).reg j ∧
      ∀ m, w + 1 ≤ m → m < t → ¬ τ.isWriteStep j m := by
  induction t with
  | zero =>
    rw [stateAt_zero] at hpos
    exact absurd hpos (Nat.not_lt_zero _)
  | succ t ih =>
    rcases τ.reg_step_iff j (Nat.lt_of_succ_le ht) with ⟨hreg_eq, hnotw⟩ |
        ⟨opId, val, snap, hev, hproc, -, -⟩
    · rw [hreg_eq] at hpos
      obtain ⟨w, hwt, hw, hreg_w, hnow⟩ := ih (Nat.le_of_succ_le ht) hpos
      refine ⟨w, Nat.lt_succ_of_lt hwt, hw, hreg_w ▸ hreg_eq, fun m hm₁ hm₂ => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm₂ with hm₂' | rfl
      · exact hnow m hm₁ hm₂'
      · exact hnotw
    · exact ⟨t, Nat.lt_succ_self t, ⟨Nat.lt_of_succ_le ht, opId, val, snap, hev, hproc⟩,
        rfl, fun _ hm₁ hm₂ => by omega⟩

private theorem zero_mem_idleFilter (τ : SnapshotTrace ord dInit) (i : P) (t : ℕ) :
    0 ∈ (range (t + 1)).filter fun m => ((τ.stateAt m).proc i).isIdle :=
  mem_filter.mpr ⟨mem_range.mpr (Nat.zero_lt_succ t), by rw [stateAt_zero]; rfl⟩

/-- Proof-only helper: the largest step index `m ≤ t` at which `(τ.stateAt m).proc i = .idle`
(well-defined since `m = 0` always has `(τ.stateAt 0).proc i = .idle`). -/
private def lastIdleStep (τ : SnapshotTrace ord dInit) (i : P) (t : ℕ) : ℕ :=
  ((range (t + 1)).filter fun m => ((τ.stateAt m).proc i).isIdle).max'
    ⟨0, τ.zero_mem_idleFilter i t⟩

private theorem lastIdleStep_le (τ : SnapshotTrace ord dInit) (i : P) (t : ℕ) :
    τ.lastIdleStep i t ≤ t := by
  have hmem := Finset.max'_mem
    ((range (t + 1)).filter fun m => ((τ.stateAt m).proc i).isIdle)
    ⟨0, τ.zero_mem_idleFilter i t⟩
  exact Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hmem).1)

private theorem le_lastIdleStep_of_idle (τ : SnapshotTrace ord dInit) (i : P) {m t : ℕ}
    (hle : m ≤ t) (hidle : (τ.stateAt m).proc i = .idle) :
    m ≤ τ.lastIdleStep i t := by
  apply Finset.le_max'
  exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hle),
    (ProcSnapshotState.isIdle_eq_true _).mpr hidle⟩

private theorem lastIdleStep_eq_of_step_not_idle (τ : SnapshotTrace ord dInit) (i : P) {t : ℕ}
    (hnot : (τ.stateAt (t + 1)).proc i ≠ .idle) :
    τ.lastIdleStep i (t + 1) =
      if ((τ.stateAt t).proc i).isIdle then t else τ.lastIdleStep i t := by
  apply le_antisymm
  · have hmem := Finset.max'_mem
      ((range (t + 2)).filter fun m => ((τ.stateAt m).proc i).isIdle)
      ⟨0, τ.zero_mem_idleFilter i (t + 1)⟩
    obtain ⟨hr, hid⟩ := mem_filter.mp hmem
    rw [ProcSnapshotState.isIdle_eq_true] at hid
    have hlt : τ.lastIdleStep i (t + 1) ≤ t := by
      have hle := Nat.lt_succ_iff.mp (mem_range.mp hr)
      rcases Nat.of_le_succ hle with h | h
      · exact h
      · change _ = t + 1 at h
        rw [h] at hid
        exact absurd hid hnot
    split_ifs with htidle
    · exact hlt
    · exact τ.le_lastIdleStep_of_idle i hlt hid
  · split_ifs with htidle
    · exact τ.le_lastIdleStep_of_idle i (Nat.le_succ t)
        ((ProcSnapshotState.isIdle_eq_true _).mp htidle)
    · exact τ.le_lastIdleStep_of_idle i
        (le_trans (τ.lastIdleStep_le i t) (Nat.le_succ t))
        (by
          have hmem := Finset.max'_mem
            ((range (t + 1)).filter fun m => ((τ.stateAt m).proc i).isIdle)
            ⟨0, τ.zero_mem_idleFilter i t⟩
          exact (ProcSnapshotState.isIdle_eq_true _).mp (mem_filter.mp hmem).2)

private theorem getElem_of_eq {α : Type*} {xs ys : List α} (h : xs = ys) {i : ℕ}
    (hxi : i < xs.length) (hyi : i < ys.length) : xs[i]'hxi = ys[i]'hyi := by
  subst h; rfl

private theorem getElem_congr_idx {α : Type*} (xs : List α) {i j : ℕ} (h : i = j)
    (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

/-- Combined trace invariant at step `t ≤ τ.events.length` powering Lemmas 3.1–3.3 and Theorem 1:
1. `(τ.stateAt t).stepCount = t`.
2. For every register `j` with `((τ.stateAt t).reg j).seq > 0` whose most recent write occurred at
   `w < t`, there exists a serialization state `v` with `τ.lastIdleStep j w + 1 ≤ v ≤ w` such that
   `memSnapshot (τ.stateAt v).reg = ((τ.stateAt t).reg j).view`.
3. For every active process `i`:
   - if `proc i = .readyToWrite opId val snap`: `opId < history.length`, `history[opId]` is pending
     `update val` by `i` with `invStep = τ.lastIdleStep i t < t`, and there exists `v` with
     `invStep + 1 ≤ v ≤ t` and `memSnapshot (τ.stateAt v).reg = snap`;
   - if `proc i = .scanning st`: `opId < history.length`, `history[opId]` is pending (`scan` or
     `update val` matching `st.mode`) by `i` with `invStep = τ.lastIdleStep i t < t`, and there
     exists an iteration-start step `iterStart` (`invStep + 1 ≤ iterStart ≤ t`) such that:
     * every `k ∈ st.moved` executed `isWriteStep τ k w₁` at some `invStep + 1 ≤ w₁ < iterStart`,
     * if `st.phase = .collectA`: every `k ∉ st.rem` was read at some `iterStart ≤ tA ≤ t`
       (`st.collectAVal k = (τ.stateAt tA).reg k`),
     * if `st.phase = .collectB`: there exists `u` (`iterStart ≤ u ≤ t`) such that every `k : P`
       was read in `collectA` at some `iterStart ≤ tA ≤ u` and every `k ∉ st.rem` was read in
       `collectB` at some `u ≤ tB ≤ t`.
4. For every history index `id < history.length` with record `rec`:
   - if `rec.status = .pending`, then `proc rec.caller` is active with `opId = id` and
     `rec.invStep = τ.lastIdleStep rec.caller t < t`;
   - if `rec.status = .doneScan resp snap`, then `rec.kind = .scan`, `rec.invStep < resp < t`, and
     there exists `v` with `rec.invStep + 1 ≤ v ≤ resp` and
     `memSnapshot (τ.stateAt v).reg = snap`;
   - if `rec.status = .doneUpdate resp`, then `rec.kind = .update val` (for some `val`),
     `rec.invStep < resp < t`, `τ.isWriteStep rec.caller resp`, and
     `((τ.stateAt (resp + 1)).reg rec.caller).data = val`;
   - conversely, EVERY `isWriteStep τ j w` with `w < t` has a unique `id < history.length` with
     `caller = j` and `status = .doneUpdate w`. -/
private structure TraceInv (τ : SnapshotTrace ord dInit) (t : ℕ) : Prop where
  stepCount_eq : (τ.stateAt t).stepCount = t
  reg_view_valid : ∀ j w, w < t → τ.isWriteStep j w →
    ∃ v, τ.lastIdleStep j w + 1 ≤ v ∧ v ≤ w ∧
      memSnapshot (τ.stateAt v).reg = ((τ.stateAt (w + 1)).reg j).view
  proc_ready : ∀ i opId val snap,
    (τ.stateAt t).proc i = .readyToWrite opId val snap →
    ∃ (hId : opId < (τ.stateAt t).history.length),
      (τ.stateAt t).history[opId]'hId =
        ⟨i, .update val, τ.lastIdleStep i t, .pending⟩ ∧
      τ.lastIdleStep i t < t ∧
      ∃ v, τ.lastIdleStep i t + 1 ≤ v ∧ v ≤ t ∧ memSnapshot (τ.stateAt v).reg = snap
  proc_scan : ∀ i st,
    (τ.stateAt t).proc i = .scanning st →
    ∃ (hId : st.opId < (τ.stateAt t).history.length),
      (τ.stateAt t).history[st.opId]'hId =
        ⟨i, match st.mode with | .external => .scan | .embedded val => .update val,
          τ.lastIdleStep i t, .pending⟩ ∧
      τ.lastIdleStep i t < t ∧
      ∃ iterStart, τ.lastIdleStep i t + 1 ≤ iterStart ∧ iterStart ≤ t ∧
        (∀ k ∈ st.moved, ∃ w₁, τ.lastIdleStep i t + 1 ≤ w₁ ∧ w₁ < iterStart ∧
          τ.isWriteStep k w₁) ∧
        (st.phase = .collectA →
          ∀ k, k ∉ st.rem →
            ∃ tA, iterStart ≤ tA ∧ tA ≤ t ∧ st.collectAVal k = (τ.stateAt tA).reg k) ∧
        (st.phase = .collectB →
          ∃ u, iterStart ≤ u ∧ u ≤ t ∧
            (∀ k, ∃ tA, iterStart ≤ tA ∧ tA ≤ u ∧ st.collectAVal k = (τ.stateAt tA).reg k) ∧
            (∀ k, k ∉ st.rem →
              ∃ tB, u ≤ tB ∧ tB ≤ t ∧ st.collectBVal k = (τ.stateAt tB).reg k))
  hist_pending : ∀ id (hId : id < (τ.stateAt t).history.length),
    ((τ.stateAt t).history[id]'hId).status = .pending →
    ((τ.stateAt t).history[id]'hId).invStep =
      τ.lastIdleStep ((τ.stateAt t).history[id]'hId).caller t ∧
    ((τ.stateAt t).history[id]'hId).invStep < t ∧
      ((∃ st, (τ.stateAt t).proc ((τ.stateAt t).history[id]'hId).caller = .scanning st ∧
          st.opId = id) ∨
       (∃ val snap, (τ.stateAt t).proc ((τ.stateAt t).history[id]'hId).caller =
          .readyToWrite id val snap))
  hist_doneScan : ∀ id (hId : id < (τ.stateAt t).history.length) resp snap,
    ((τ.stateAt t).history[id]'hId).status = .doneScan resp snap →
    ((τ.stateAt t).history[id]'hId).kind = .scan ∧
    ((τ.stateAt t).history[id]'hId).invStep < resp ∧ resp < t ∧
      ∃ v, ((τ.stateAt t).history[id]'hId).invStep + 1 ≤ v ∧ v ≤ resp ∧
        memSnapshot (τ.stateAt v).reg = snap
  hist_doneUpdate : ∀ id (hId : id < (τ.stateAt t).history.length) resp,
    ((τ.stateAt t).history[id]'hId).status = .doneUpdate resp →
    ∃ val, ((τ.stateAt t).history[id]'hId).kind = .update val ∧
      ((τ.stateAt t).history[id]'hId).invStep < resp ∧ resp < t ∧
      τ.isWriteStep ((τ.stateAt t).history[id]'hId).caller resp ∧
      (τ.stateAt (resp + 1)).reg ((τ.stateAt t).history[id]'hId).caller =
        ⟨val, ((τ.stateAt resp).reg ((τ.stateAt t).history[id]'hId).caller).seq + 1,
          ((τ.stateAt (resp + 1)).reg ((τ.stateAt t).history[id]'hId).caller).view⟩
  writeStep_in_hist : ∀ j w, w < t → τ.isWriteStep j w →
    ∃ (id : ℕ) (hId : id < (τ.stateAt t).history.length),
      ((τ.stateAt t).history[id]'hId).caller = j ∧
      ((τ.stateAt t).history[id]'hId).status = .doneUpdate w

omit [Fintype P] [DecidableEq P] in
private theorem active_opId_unique {s : SnapshotState P Data} {i : P} {id₁ id₂ : ℕ}
    (h₁ : (∃ st, s.proc i = .scanning st ∧ st.opId = id₁) ∨
          (∃ val snap, s.proc i = .readyToWrite id₁ val snap))
    (h₂ : (∃ st, s.proc i = .scanning st ∧ st.opId = id₂) ∨
          (∃ val snap, s.proc i = .readyToWrite id₂ val snap)) :
    id₁ = id₂ := by
  rcases h₁ with ⟨st₁, hp₁, rfl⟩ | ⟨v₁, sn₁, hp₁⟩ <;>
    rcases h₂ with ⟨st₂, hp₂, rfl⟩ | ⟨v₂, sn₂, hp₂⟩
  · rw [hp₁] at hp₂; injection hp₂ with h; rw [h]
  · rw [hp₁] at hp₂; cases hp₂
  · rw [hp₁] at hp₂; cases hp₂
  · rw [hp₁] at hp₂; injection hp₂

/-- Helper checking that when `proc i` stays non-idle from `t` to `t + 1` (and was non-idle at
`t`), `lastIdleStep i (t + 1) = lastIdleStep i t`. -/
private theorem lastIdleStep_keep (τ : SnapshotTrace ord dInit) (i : P) {t : ℕ}
    (h0 : (τ.stateAt t).proc i ≠ .idle) (h1 : (τ.stateAt (t + 1)).proc i ≠ .idle) :
    τ.lastIdleStep i (t + 1) = τ.lastIdleStep i t := by
  rw [τ.lastIdleStep_eq_of_step_not_idle i h1]
  split_ifs with hid
  · exact absurd ((ProcSnapshotState.isIdle_eq_true _).mp hid) h0
  · rfl

/-- Per-actor frame lemma for `TraceInv`: given `TraceInv τ t`, if actor `i` transitions from `t`
to `t + 1` leaving every other process `p ≠ i` unchanged and modifying `history` at most at a
single index `modId` (either `modId = history.length` for an append/no-op, or an existing pending
entry of `i`), then all frame obligations for `p ≠ i`, `id ≠ modId`, and `w < t` follow
automatically from `TraceInv τ t`. -/
private theorem TraceInv.of_actor_step {τ : SnapshotTrace ord dInit} {t : ℕ}
    (inv : TraceInv τ t) (i : P) (modId : ℕ)
    (hstepCount : (τ.stateAt (t + 1)).stepCount = t + 1)
    (hproc_other : ∀ p, p ≠ i → (τ.stateAt (t + 1)).proc p = (τ.stateAt t).proc p)
    (hhist_len : (τ.stateAt t).history.length ≤ (τ.stateAt (t + 1)).history.length)
    (hbound_unchanged : ∀ id, id < (τ.stateAt (t + 1)).history.length → id ≠ modId →
      id < (τ.stateAt t).history.length)
    (hhist_unchanged : ∀ id (h₁ : id < (τ.stateAt (t + 1)).history.length)
      (h₀ : id < (τ.stateAt t).history.length), id ≠ modId →
        (τ.stateAt (t + 1)).history[id]'h₁ = (τ.stateAt t).history[id]'h₀)
    (hmod_old : ∀ (h₀ : modId < (τ.stateAt t).history.length),
      ((τ.stateAt t).history[modId]'h₀).caller = i ∧
        ((τ.stateAt t).history[modId]'h₀).status = .pending)
    (hreg_t : ∀ j, τ.isWriteStep j t →
      ∃ v, τ.lastIdleStep j t + 1 ≤ v ∧ v ≤ t ∧
        memSnapshot (τ.stateAt v).reg = ((τ.stateAt (t + 1)).reg j).view)
    (hready_i : ∀ opId val snap,
      (τ.stateAt (t + 1)).proc i = .readyToWrite opId val snap →
      ∃ (hId : opId < (τ.stateAt (t + 1)).history.length),
        (τ.stateAt (t + 1)).history[opId]'hId =
          ⟨i, .update val, τ.lastIdleStep i (t + 1), .pending⟩ ∧
        τ.lastIdleStep i (t + 1) < t + 1 ∧
        ∃ v, τ.lastIdleStep i (t + 1) + 1 ≤ v ∧ v ≤ t + 1 ∧
          memSnapshot (τ.stateAt v).reg = snap)
    (hscan_i : ∀ st,
      (τ.stateAt (t + 1)).proc i = .scanning st →
      ∃ (hId : st.opId < (τ.stateAt (t + 1)).history.length),
        (τ.stateAt (t + 1)).history[st.opId]'hId =
          ⟨i, match st.mode with | .external => .scan | .embedded val => .update val,
            τ.lastIdleStep i (t + 1), .pending⟩ ∧
        τ.lastIdleStep i (t + 1) < t + 1 ∧
        ∃ iterStart, τ.lastIdleStep i (t + 1) + 1 ≤ iterStart ∧ iterStart ≤ t + 1 ∧
          (∀ k ∈ st.moved, ∃ w₁, τ.lastIdleStep i (t + 1) + 1 ≤ w₁ ∧ w₁ < iterStart ∧
            τ.isWriteStep k w₁) ∧
          (st.phase = .collectA →
            ∀ k, k ∉ st.rem →
              ∃ tA, iterStart ≤ tA ∧ tA ≤ t + 1 ∧ st.collectAVal k = (τ.stateAt tA).reg k) ∧
          (st.phase = .collectB →
            ∃ u, iterStart ≤ u ∧ u ≤ t + 1 ∧
              (∀ k, ∃ tA, iterStart ≤ tA ∧ tA ≤ u ∧ st.collectAVal k = (τ.stateAt tA).reg k) ∧
              (∀ k, k ∉ st.rem →
                ∃ tB, u ≤ tB ∧ tB ≤ t + 1 ∧ st.collectBVal k = (τ.stateAt tB).reg k)))
    (hpending_i : ∀ id (hId : id < (τ.stateAt (t + 1)).history.length),
      (id = modId ∨ ((τ.stateAt (t + 1)).history[id]'hId).caller = i) →
      ((τ.stateAt (t + 1)).history[id]'hId).status = .pending →
      ((τ.stateAt (t + 1)).history[id]'hId).invStep =
        τ.lastIdleStep ((τ.stateAt (t + 1)).history[id]'hId).caller (t + 1) ∧
      ((τ.stateAt (t + 1)).history[id]'hId).invStep < t + 1 ∧
        ((∃ st, (τ.stateAt (t + 1)).proc ((τ.stateAt (t + 1)).history[id]'hId).caller =
            .scanning st ∧ st.opId = id) ∨
         (∃ val snap, (τ.stateAt (t + 1)).proc ((τ.stateAt (t + 1)).history[id]'hId).caller =
            .readyToWrite id val snap)))
    (hdoneScan_mod : ∀ (hId : modId < (τ.stateAt (t + 1)).history.length) resp snap,
      ((τ.stateAt (t + 1)).history[modId]'hId).status = .doneScan resp snap →
      ((τ.stateAt (t + 1)).history[modId]'hId).kind = .scan ∧
      ((τ.stateAt (t + 1)).history[modId]'hId).invStep < resp ∧ resp < t + 1 ∧
        ∃ v, ((τ.stateAt (t + 1)).history[modId]'hId).invStep + 1 ≤ v ∧ v ≤ resp ∧
          memSnapshot (τ.stateAt v).reg = snap)
    (hdoneUpdate_mod : ∀ (hId : modId < (τ.stateAt (t + 1)).history.length) resp,
      ((τ.stateAt (t + 1)).history[modId]'hId).status = .doneUpdate resp →
      ∃ val, ((τ.stateAt (t + 1)).history[modId]'hId).kind = .update val ∧
        ((τ.stateAt (t + 1)).history[modId]'hId).invStep < resp ∧ resp < t + 1 ∧
        τ.isWriteStep ((τ.stateAt (t + 1)).history[modId]'hId).caller resp ∧
        (τ.stateAt (resp + 1)).reg ((τ.stateAt (t + 1)).history[modId]'hId).caller =
          ⟨val, ((τ.stateAt resp).reg ((τ.stateAt (t + 1)).history[modId]'hId).caller).seq + 1,
            ((τ.stateAt (resp + 1)).reg ((τ.stateAt (t + 1)).history[modId]'hId).caller).view⟩)
    (hwrite_t : ∀ j, τ.isWriteStep j t →
      ∃ (id : ℕ) (hId : id < (τ.stateAt (t + 1)).history.length),
        ((τ.stateAt (t + 1)).history[id]'hId).caller = j ∧
        ((τ.stateAt (t + 1)).history[id]'hId).status = .doneUpdate t) :
    TraceInv τ (t + 1) where
  stepCount_eq := hstepCount
  reg_view_valid j w hw hwrite := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw' | rfl
    · exact inv.reg_view_valid j w hw' hwrite
    · exact hreg_t j hwrite
  proc_ready p opId val snap hp := by
    by_cases hpi : p = i
    · subst hpi; exact hready_i opId val snap hp
    · have hp_old : (τ.stateAt t).proc p = .readyToWrite opId val snap :=
        (hproc_other p hpi) ▸ hp
      have hkeep := τ.lastIdleStep_keep p (by rw [hp_old]; nofun) (by rw [hp]; nofun)
      obtain ⟨hId₀, hrec₀, hlt₀, v, hv₁, hv₂, hsnap⟩ := inv.proc_ready p opId val snap hp_old
      have hId₁ : opId < (τ.stateAt (t + 1)).history.length := lt_of_lt_of_le hId₀ hhist_len
      have hne_mod : opId ≠ modId := by
        intro heq; subst heq
        exact hpi ((congrArg SnapshotOpRecord.caller hrec₀).symm.trans (hmod_old hId₀).1)
      refine ⟨hId₁, ?_, by omega, v, by omega, by omega, hsnap⟩
      rw [hhist_unchanged opId hId₁ hId₀ hne_mod, hkeep]
      exact hrec₀
  proc_scan p st hp := by
    by_cases hpi : p = i
    · subst hpi; exact hscan_i st hp
    · have hp_old : (τ.stateAt t).proc p = .scanning st := (hproc_other p hpi) ▸ hp
      have hkeep := τ.lastIdleStep_keep p (by rw [hp_old]; nofun) (by rw [hp]; nofun)
      obtain ⟨hId₀, hrec₀, hlt₀, iterS, hi₁, hi₂, hm₀, ha₀, hb₀⟩ := inv.proc_scan p st hp_old
      have hId₁ : st.opId < (τ.stateAt (t + 1)).history.length := lt_of_lt_of_le hId₀ hhist_len
      have hne_mod : st.opId ≠ modId := by
        intro heq
        have hidx := getElem_congr_idx (τ.stateAt t).history heq hId₀ (heq ▸ hId₀)
        exact hpi ((congrArg SnapshotOpRecord.caller (hrec₀.symm.trans hidx)).trans
          (hmod_old (heq ▸ hId₀)).1)
      refine ⟨hId₁, ?_, by omega, iterS, by omega, by omega, ?_, ?_, ?_⟩
      · rw [hhist_unchanged st.opId hId₁ hId₀ hne_mod, hkeep]; exact hrec₀
      · intro k hk; rw [hkeep]; exact hm₀ k hk
      · intro hA k hk
        obtain ⟨tA, a1, a2, a3⟩ := ha₀ hA k hk
        exact ⟨tA, a1, by omega, a3⟩
      · intro hB
        obtain ⟨u, u1, u2, ha, hb⟩ := hb₀ hB
        refine ⟨u, u1, by omega, ha, fun k hk => ?_⟩
        obtain ⟨tB, b1, b2, b3⟩ := hb k hk
        exact ⟨tB, b1, by omega, b3⟩
  hist_pending id hId₁ hpend := by
    by_cases hcase : id = modId ∨ ((τ.stateAt (t + 1)).history[id]'hId₁).caller = i
    · exact hpending_i id hId₁ hcase hpend
    · push Not at hcase
      have hId₀ := hbound_unchanged id hId₁ hcase.1
      have hrec_eq := hhist_unchanged id hId₁ hId₀ hcase.1
      rw [hrec_eq] at hpend hcase ⊢
      obtain ⟨hinv, hlt₀, hact_old⟩ := inv.hist_pending id hId₀ hpend
      have hnot_old : (τ.stateAt t).proc ((τ.stateAt t).history[id]'hId₀).caller ≠ .idle := by
        rcases hact_old with ⟨_, hp, -⟩ | ⟨_, _, hp⟩ <;> rw [hp] <;> nofun
      have hproc_same := hproc_other _ hcase.2
      have hkeep := τ.lastIdleStep_keep _ hnot_old (hproc_same ▸ hnot_old)
      rw [hkeep, hproc_same]
      exact ⟨hinv, by omega, hact_old⟩
  hist_doneScan id hId₁ resp snap hdone := by
    by_cases hid : id = modId
    · subst hid; exact hdoneScan_mod hId₁ resp snap hdone
    · have hId₀ := hbound_unchanged id hId₁ hid
      rw [hhist_unchanged id hId₁ hId₀ hid] at hdone ⊢
      obtain ⟨hk, hi, hr, v, hv⟩ := inv.hist_doneScan id hId₀ resp snap hdone
      exact ⟨hk, hi, by omega, v, hv⟩
  hist_doneUpdate id hId₁ resp hdone := by
    by_cases hid : id = modId
    · subst hid; exact hdoneUpdate_mod hId₁ resp hdone
    · have hId₀ := hbound_unchanged id hId₁ hid
      rw [hhist_unchanged id hId₁ hId₀ hid] at hdone ⊢
      obtain ⟨val', hk, hi, hr, hw, hd⟩ := inv.hist_doneUpdate id hId₀ resp hdone
      exact ⟨val', hk, hi, by omega, hw, hd⟩
  writeStep_in_hist j w hw hwrite := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw' | rfl
    · obtain ⟨id, hId₀, hc, hs⟩ := inv.writeStep_in_hist j w hw' hwrite
      have hId₁ : id < (τ.stateAt (t + 1)).history.length := lt_of_lt_of_le hId₀ hhist_len
      have hne_mod : id ≠ modId := by
        intro heq; subst heq
        exact absurd ((hmod_old hId₀).2.symm.trans hs) nofun
      refine ⟨id, hId₁, ?_, ?_⟩ <;> rw [hhist_unchanged id hId₁ hId₀ hne_mod]
      · exact hc
      · exact hs
    · exact hwrite_t j hwrite

/-- Specialization of `TraceInv.of_actor_step` for `.invokeScan i` and `.invokeUpdate i val`. -/
private theorem TraceInv.of_invoke {τ : SnapshotTrace ord dInit} {t : ℕ}
    (inv : TraceInv τ t) (i : P) (mode : ScanMode Data)
    (hpi : (τ.stateAt t).proc i = .idle)
    (hnow : ¬∃ j, τ.isWriteStep j t)
    (hs₁ :
      let opId := (τ.stateAt t).history.length
      let dummy := fun _ : P => SnapshotReg.init (P := P) dInit
      let st : ActiveScan P Data := ⟨mode, opId, ∅, .collectA, ord.elems, dummy, dummy⟩
      let kind := match mode with | .external => .scan | .embedded v => .update v
      ({ reg := (τ.stateAt t).reg
         proc := Function.update (τ.stateAt t).proc i (.scanning st)
         history := (τ.stateAt t).history ++ [⟨i, kind, (τ.stateAt t).stepCount, .pending⟩]
         stepCount := (τ.stateAt t).stepCount + 1 } : SnapshotState P Data) =
        τ.stateAt (t + 1)) :
    TraceInv τ (t + 1) := by
  let kind : SnapshotOpKind Data := match mode with | .external => .scan | .embedded v => .update v
  let dummy := fun _ : P => SnapshotReg.init (P := P) dInit
  let st_new : ActiveScan P Data :=
    ⟨mode, (τ.stateAt t).history.length, ∅, .collectA, ord.elems, dummy, dummy⟩
  have hlast_i : τ.lastIdleStep i (t + 1) = t := by
    have hnot : (τ.stateAt (t + 1)).proc i ≠ .idle := by
      rw [← hs₁]; simp only [Function.update_self]; nofun
    rw [τ.lastIdleStep_eq_of_step_not_idle i hnot, (ProcSnapshotState.isIdle_eq_true _).mpr hpi]
    simp only [↓reduceIte]
  have hhist_eq : (τ.stateAt (t + 1)).history =
      (τ.stateAt t).history ++ [⟨i, kind, t, .pending⟩] := by
    rw [← hs₁, inv.stepCount_eq]; cases mode <;> rfl
  have hlen1 : (τ.stateAt (t + 1)).history.length = (τ.stateAt t).history.length + 1 := by
    rw [hhist_eq, List.length_append, List.length_singleton]
  have hget_new : ∀ hId : (τ.stateAt t).history.length < (τ.stateAt (t + 1)).history.length,
      (τ.stateAt (t + 1)).history[(τ.stateAt t).history.length]'hId = ⟨i, kind, t, .pending⟩ := by
    intro hId
    rw [getElem_of_eq hhist_eq hId (by rw [List.length_append, List.length_singleton]; omega)]
    simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_singleton]
  refine inv.of_actor_step i (τ.stateAt t).history.length
    (by rw [← hs₁, inv.stepCount_eq])
    (fun p hp => by rw [← hs₁]; exact Function.update_of_ne hp _ _)
    (by omega)
    (fun id h₁ hne => by omega)
    (fun id h₁ h₀ _ => by
      rw [getElem_of_eq hhist_eq h₁ (by rw [List.length_append]; omega),
        List.getElem_append_left h₀])
    (fun h₀ => absurd h₀ (lt_irrefl _))
    (fun j hw => absurd ⟨j, hw⟩ hnow)
    (fun _ _ _ hp => by rw [← hs₁] at hp; simp only [Function.update_self] at hp; cases hp)
    ?_ ?_
    (fun hId _ _ hdone => by rw [hget_new hId] at hdone; cases hdone)
    (fun hId _ hdone => by rw [hget_new hId] at hdone; cases hdone)
    (fun j hw => absurd ⟨j, hw⟩ hnow)
  · intro st hp
    rw [← hs₁] at hp
    simp only [Function.update_self, ProcSnapshotState.scanning.injEq] at hp
    subst hp
    dsimp only [st_new]
    refine ⟨by omega, ?_, by omega, t + 1, by omega, le_rfl,
      fun k hk => absurd hk (notMem_empty k),
      fun _ k hk => absurd (ord.complete k) hk, fun hph => by cases hph⟩
    rw [hget_new (by omega), hlast_i]; cases mode <;> rfl
  · intro id hId hcase hpend
    by_cases hid : id = (τ.stateAt t).history.length
    · subst hid
      simp only [hget_new hId, hlast_i, Nat.lt_succ_self, true_and]
      exact Or.inl ⟨st_new, by rw [← hs₁]; exact Function.update_self _ _ _, rfl⟩
    · have hId₀ : id < (τ.stateAt t).history.length := by omega
      have hrec_eq : (τ.stateAt (t + 1)).history[id]'hId = (τ.stateAt t).history[id]'hId₀ := by
        rw [getElem_of_eq hhist_eq hId (by rw [List.length_append]; omega),
          List.getElem_append_left hId₀]
      have hci : ((τ.stateAt t).history[id]'hId₀).caller = i := hrec_eq ▸ hcase.resolve_left hid
      rw [hrec_eq] at hpend
      obtain ⟨-, -, hact_old⟩ := inv.hist_pending id hId₀ hpend
      rcases hact_old with ⟨_, hp, -⟩ | ⟨_, _, hp⟩ <;> rw [hci, hpi] at hp <;> cases hp

/-- Specialization of `TraceInv.of_actor_step` when active scan `st` of `i` transitions to a
non-idle local state `ps_new` without modifying `reg` or `history`. -/
private theorem TraceInv.of_local_active {τ : SnapshotTrace ord dInit} {t : ℕ}
    (inv : TraceInv τ t) {i : P} {st : ActiveScan P Data}
    (hpi : (τ.stateAt t).proc i = .scanning st)
    (hnow : ¬∃ j, τ.isWriteStep j t)
    (ps_new : ProcSnapshotState P Data) (hps_ne : ps_new ≠ .idle)
    (hs_eq : { (τ.stateAt t) with
                proc := Function.update (τ.stateAt t).proc i ps_new
                stepCount := (τ.stateAt t).stepCount + 1 } = τ.stateAt (t + 1))
    (hact_new : (∃ s0, ps_new = .scanning s0 ∧ s0.opId = st.opId) ∨
      (∃ v0 sn0, ps_new = .readyToWrite st.opId v0 sn0))
    (hready_i : ∀ id' v' sn', ps_new = .readyToWrite id' v' sn' →
      ∃ (hId₁ : id' < (τ.stateAt (t + 1)).history.length),
        (τ.stateAt (t + 1)).history[id']'hId₁ =
          ⟨i, .update v', τ.lastIdleStep i (t + 1), .pending⟩ ∧
        τ.lastIdleStep i (t + 1) < t + 1 ∧
        ∃ v, τ.lastIdleStep i (t + 1) + 1 ≤ v ∧ v ≤ t + 1 ∧ memSnapshot (τ.stateAt v).reg = sn')
    (hscan_i : ∀ st', ps_new = .scanning st' →
      ∃ (hId₁ : st'.opId < (τ.stateAt (t + 1)).history.length),
        (τ.stateAt (t + 1)).history[st'.opId]'hId₁ =
          ⟨i, match st'.mode with | .external => .scan | .embedded val => .update val,
            τ.lastIdleStep i (t + 1), .pending⟩ ∧
        τ.lastIdleStep i (t + 1) < t + 1 ∧
        ∃ iterS', τ.lastIdleStep i (t + 1) + 1 ≤ iterS' ∧ iterS' ≤ t + 1 ∧
          (∀ k ∈ st'.moved, ∃ w₁, τ.lastIdleStep i (t + 1) + 1 ≤ w₁ ∧ w₁ < iterS' ∧
            τ.isWriteStep k w₁) ∧
          (st'.phase = .collectA →
            ∀ k, k ∉ st'.rem →
              ∃ tA, iterS' ≤ tA ∧ tA ≤ t + 1 ∧ st'.collectAVal k = (τ.stateAt tA).reg k) ∧
          (st'.phase = .collectB →
            ∃ u, iterS' ≤ u ∧ u ≤ t + 1 ∧
              (∀ k, ∃ tA, iterS' ≤ tA ∧ tA ≤ u ∧ st'.collectAVal k = (τ.stateAt tA).reg k) ∧
              (∀ k, k ∉ st'.rem →
                ∃ tB, u ≤ tB ∧ tB ≤ t + 1 ∧ st'.collectBVal k = (τ.stateAt tB).reg k))) :
    TraceInv τ (t + 1) := by
  have hhist_eq : (τ.stateAt (t + 1)).history = (τ.stateAt t).history := by rw [← hs_eq]
  refine inv.of_actor_step i (τ.stateAt t).history.length
    (by rw [← hs_eq, inv.stepCount_eq])
    (fun p hp => by rw [← hs_eq]; exact Function.update_of_ne hp _ _)
    (by rw [hhist_eq])
    (fun id h₁ _ => hhist_eq ▸ h₁)
    (fun id h₁ h₀ _ => getElem_of_eq hhist_eq h₁ h₀)
    (fun h₀ => absurd h₀ (lt_irrefl _))
    (fun j hw => absurd ⟨j, hw⟩ hnow)
    (fun id' v' sn' hp => hready_i id' v' sn' (by
      rw [← hs_eq] at hp; dsimp only at hp; rwa [Function.update_self] at hp))
    (fun st' hp => hscan_i st' (by
      rw [← hs_eq] at hp; dsimp only at hp; rwa [Function.update_self] at hp))
    ?_
    (fun h₁ => absurd (hhist_eq ▸ h₁) (lt_irrefl _))
    (fun h₁ => absurd (hhist_eq ▸ h₁) (lt_irrefl _))
    (fun j hw => absurd ⟨j, hw⟩ hnow)
  intro id hId₁ hcase hpend
  have hId₀ : id < (τ.stateAt t).history.length := hhist_eq ▸ hId₁
  have hrec_eq := getElem_of_eq hhist_eq hId₁ hId₀
  have hci : ((τ.stateAt t).history[id]'hId₀).caller = i :=
    hrec_eq ▸ hcase.resolve_left (Nat.ne_of_lt hId₀)
  rw [hrec_eq] at hpend ⊢
  obtain ⟨hinv, hlt₀, hact_old⟩ := inv.hist_pending id hId₀ hpend
  have hid_eq : id = st.opId :=
    active_opId_unique (hci ▸ hact_old) (Or.inl ⟨st, hpi, rfl⟩)
  subst id
  have hpi_new : (τ.stateAt (t + 1)).proc i = ps_new := by
    rw [← hs_eq]; exact Function.update_self _ _ _
  have hkeep := τ.lastIdleStep_keep i (by rw [hpi]; nofun) (hpi_new ▸ hps_ne)
  rw [hci] at hinv ⊢
  rw [hkeep, hpi_new]
  exact ⟨hinv, by omega, hact_new⟩

/-- Specialization of `TraceInv.of_actor_step` when active operation `activeId` of `i` completes
(`newSt ≠ .pending`) and `proc i` returns to `.idle`. -/
private theorem TraceInv.of_complete {τ : SnapshotTrace ord dInit} {t : ℕ}
    (inv : TraceInv τ t) {i : P} {activeId : ℕ} (hId : activeId < (τ.stateAt t).history.length)
    (oldKind : SnapshotOpKind Data) (newSt : SnapshotOpStatus P Data) (hnew_ne : newSt ≠ .pending)
    (hrec_i : (τ.stateAt t).history[activeId]'hId = ⟨i, oldKind, τ.lastIdleStep i t, .pending⟩)
    (hact_i : (∃ s0, (τ.stateAt t).proc i = .scanning s0 ∧ s0.opId = activeId) ∨
      (∃ v0 sn0, (τ.stateAt t).proc i = .readyToWrite activeId v0 sn0))
    (hstepCount : (τ.stateAt (t + 1)).stepCount = t + 1)
    (hproc_eq : (τ.stateAt (t + 1)).proc = Function.update (τ.stateAt t).proc i .idle)
    (hhist_upd : (τ.stateAt (t + 1)).history =
      completeHistoryAt (τ.stateAt t).history activeId newSt)
    (hreg_t : ∀ j, τ.isWriteStep j t →
      ∃ v, τ.lastIdleStep j t + 1 ≤ v ∧ v ≤ t ∧
        memSnapshot (τ.stateAt v).reg = ((τ.stateAt (t + 1)).reg j).view)
    (hdoneScan_new : ∀ resp snap, newSt = .doneScan resp snap →
      oldKind = .scan ∧ τ.lastIdleStep i t < resp ∧ resp < t + 1 ∧
        ∃ v, τ.lastIdleStep i t + 1 ≤ v ∧ v ≤ resp ∧ memSnapshot (τ.stateAt v).reg = snap)
    (hdoneUpdate_new : ∀ resp, newSt = .doneUpdate resp →
      ∃ val, oldKind = .update val ∧ τ.lastIdleStep i t < resp ∧ resp < t + 1 ∧
        τ.isWriteStep i resp ∧
        (τ.stateAt (resp + 1)).reg i =
          ⟨val, ((τ.stateAt resp).reg i).seq + 1, ((τ.stateAt (resp + 1)).reg i).view⟩)
    (hwrite_t : ∀ j, τ.isWriteStep j t → j = i ∧ newSt = .doneUpdate t) :
    TraceInv τ (t + 1) := by
  have hget_op : (τ.stateAt t).history[activeId]? =
      some ⟨i, oldKind, τ.lastIdleStep i t, .pending⟩ := by
    rw [List.getElem?_eq_getElem hId, hrec_i]
  have hset : (τ.stateAt (t + 1)).history =
      (τ.stateAt t).history.set activeId ⟨i, oldKind, τ.lastIdleStep i t, newSt⟩ := by
    rw [hhist_upd]; simp only [completeHistoryAt, hget_op]
  have hlen_eq : (τ.stateAt (t + 1)).history.length = (τ.stateAt t).history.length := by
    rw [hset, List.length_set]
  have hnew_at : ∀ h₁ : activeId < (τ.stateAt (t + 1)).history.length,
      (τ.stateAt (t + 1)).history[activeId]'h₁ = ⟨i, oldKind, τ.lastIdleStep i t, newSt⟩ := by
    intro h₁
    rw [getElem_of_eq hset h₁ (by simp only [List.length_set]; exact hId)]
    exact List.getElem_set_self (by simp only [List.length_set]; exact hId)
  have hunch : ∀ id (h₁ : id < (τ.stateAt (t + 1)).history.length)
      (h₀ : id < (τ.stateAt t).history.length), id ≠ activeId →
      (τ.stateAt (t + 1)).history[id]'h₁ = (τ.stateAt t).history[id]'h₀ := by
    intro id h₁ h₀ hne
    rw [getElem_of_eq hset h₁ (by simp only [List.length_set]; exact h₀)]
    exact List.getElem_set_ne (Ne.symm hne) (by simp only [List.length_set]; exact h₀)
  refine inv.of_actor_step i activeId hstepCount
    (fun p hp => by rw [hproc_eq, Function.update_of_ne hp])
    (by omega)
    (fun id h₁ _ => hlen_eq ▸ h₁)
    hunch
    (fun h₀ => by rw [hrec_i]; exact ⟨rfl, rfl⟩)
    hreg_t
    (fun _ _ _ hp => by rw [hproc_eq, Function.update_self] at hp; cases hp)
    (fun _ hp => by rw [hproc_eq, Function.update_self] at hp; cases hp)
    ?_
    (fun h₁ resp snap hdone => by rw [hnew_at h₁] at hdone ⊢; exact hdoneScan_new resp snap hdone)
    (fun h₁ resp hdone => by rw [hnew_at h₁] at hdone ⊢; exact hdoneUpdate_new resp hdone)
    (fun j hw => by
      obtain ⟨rfl, hst⟩ := hwrite_t j hw
      have h₁ : activeId < (τ.stateAt (t + 1)).history.length := hlen_eq.symm ▸ hId
      exact ⟨activeId, h₁, by rw [hnew_at h₁], by rw [hnew_at h₁]; exact hst⟩)
  intro id hId₁ hcase hpend
  by_cases hid : id = activeId
  · subst hid; rw [hnew_at hId₁] at hpend; exact absurd hpend hnew_ne
  · have hId₀ : id < (τ.stateAt t).history.length := hlen_eq ▸ hId₁
    have hrec_eq := hunch id hId₁ hId₀ hid
    have hci : ((τ.stateAt t).history[id]'hId₀).caller = i := hrec_eq ▸ hcase.resolve_left hid
    rw [hrec_eq] at hpend
    obtain ⟨-, -, hact_old⟩ := inv.hist_pending id hId₀ hpend
    exact absurd (active_opId_unique (hci ▸ hact_old) hact_i) hid

/-- Key inductive proof of `TraceInv τ t` for every `t ≤ τ.events.length`. -/
private theorem traceInv_holds (τ : SnapshotTrace ord dInit) :
    ∀ t ≤ τ.events.length, TraceInv τ t := by
  intro t ht
  induction t with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [stateAt_zero, SnapshotState.init]
    · intro _ w hw; omega
    · intro i _ _ _ hp; rw [stateAt_zero] at hp; cases hp
    · intro i _ hp; rw [stateAt_zero] at hp; cases hp
    · intro id hId; rw [stateAt_zero] at hId; cases hId
    · intro id hId; rw [stateAt_zero] at hId; cases hId
    · intro id hId; rw [stateAt_zero] at hId; cases hId
    · intro _ w hw; omega
  | succ t ih =>
    have ht_lt : t < τ.events.length := Nat.lt_of_succ_le ht
    have inv := ih (Nat.le_of_succ_le ht)
    have hstep := τ.stateAt_step ht_lt
    rcases hev : τ.events[t] with i | ⟨i, val⟩ | i
    · rw [hev] at hstep
      obtain ⟨hpi, hs₁⟩ := stepSnapshot_invokeScan_eq hstep
      exact inv.of_invoke i .external hpi
        (by rintro ⟨_, _, _, _, _, h1, _⟩; rw [hev] at h1; cases h1) hs₁
    · rw [hev] at hstep
      obtain ⟨hpi, hs₁⟩ := stepSnapshot_invokeUpdate_eq hstep
      exact inv.of_invoke i (.embedded val) hpi
        (by rintro ⟨_, _, _, _, _, h1, _⟩; rw [hev] at h1; cases h1) hs₁
    · rw [hev] at hstep
      unfold stepSnapshot at hstep
      cases hpi : (τ.stateAt t).proc i with
      | idle => simp only [hpi] at hstep; nomatch hstep
      | readyToWrite opId val snap =>
        simp only [hpi, Option.some.injEq] at hstep
        obtain ⟨hId, hrec_i, hlt_t, v_snap, hv₁, hv₂, hsnap_eq⟩ :=
          inv.proc_ready i opId val snap hpi
        have hji_of_write : ∀ {j}, τ.isWriteStep j t → j = i := by
          rintro j ⟨_, _, _, _, h1, _⟩
          exact SnapshotEvent.step.inj (h1.symm.trans hev)
        exact inv.of_complete hId (.update val) (.doneUpdate t) nofun hrec_i
          (Or.inr ⟨val, snap, hpi⟩)
          (by rw [← hstep, inv.stepCount_eq])
          (by rw [← hstep])
          (by rw [← hstep, inv.stepCount_eq])
          (fun j hw => by
            obtain rfl := hji_of_write hw
            have hview_eq : ((τ.stateAt (t + 1)).reg j).view = snap := by
              simp only [← hstep, Function.update_self]
            exact ⟨v_snap, hv₁, hv₂, hsnap_eq.trans hview_eq.symm⟩)
          (fun _ _ h => nomatch h)
          (fun resp hdone => by
            injection hdone with hresp; subst hresp
            refine ⟨val, rfl, hlt_t, Nat.lt_succ_self t, ⟨ht_lt, opId, val, snap, hev, hpi⟩, ?_⟩
            simp only [← hstep, Function.update_self])
          (fun j hw => ⟨hji_of_write hw, rfl⟩)
      | scanning st =>
        simp only [hpi] at hstep
        have hnow : ¬∃ j, τ.isWriteStep j t := by
          rintro ⟨j, _, _, _, _, h1, h2⟩
          rw [hev] at h1; injection h1 with hji; subst hji
          rw [hpi] at h2; cases h2
        obtain ⟨hId, hrec_i, hlt_t, iterS, hi₁, hi₂, hmov, hcA, hcB⟩ := inv.proc_scan i st hpi
        have finishScan_inv : ∀ (snap : P → Data),
            (∃ v, τ.lastIdleStep i t + 1 ≤ v ∧ v ≤ t ∧ memSnapshot (τ.stateAt v).reg = snap) →
            finishScan (τ.stateAt t) i st.mode st.opId snap = τ.stateAt (t + 1) →
            TraceInv τ (t + 1) := by
          intro snap ⟨v_snap, hv₁, hv₂, hsnap_eq⟩ hfin
          cases hm : st.mode with
          | embedded val =>
            rw [hm] at hfin hrec_i
            unfold finishScan at hfin
            have hhist_eq : (τ.stateAt (t + 1)).history = (τ.stateAt t).history := by rw [← hfin]
            have hnot1 : (τ.stateAt (t + 1)).proc i ≠ .idle := by
              simp only [← hfin, Function.update_self]; nofun
            have hkeep := τ.lastIdleStep_keep i (by rw [hpi]; nofun) hnot1
            refine inv.of_local_active hpi hnow (.readyToWrite st.opId val snap) nofun hfin
              (Or.inr ⟨val, snap, rfl⟩) ?_ (fun _ h => nomatch h)
            intro id' v' sn' heq
            injection heq with h1 h2 h3; subst h1 h2 h3
            have hId₁ : st.opId < (τ.stateAt (t + 1)).history.length := hhist_eq ▸ hId
            refine ⟨hId₁, ?_, by omega, v_snap, by omega, by omega, hsnap_eq⟩
            rw [getElem_of_eq hhist_eq hId₁ hId, hkeep]; exact hrec_i
          | external =>
            rw [hm] at hfin hrec_i
            unfold finishScan at hfin
            exact inv.of_complete hId .scan (.doneScan t snap) nofun hrec_i
              (Or.inl ⟨st, hpi, rfl⟩)
              (by rw [← hfin, inv.stepCount_eq])
              (by rw [← hfin])
              (by rw [← hfin, inv.stepCount_eq])
              (fun j hw => absurd ⟨j, hw⟩ hnow)
              (fun resp sn hdone => by
                injection hdone with hresp hsn; subst hresp hsn
                exact ⟨rfl, hlt_t, Nat.lt_succ_self t, v_snap, hv₁, hv₂, hsnap_eq⟩)
              (fun _ h => nomatch h)
              (fun j hw => absurd ⟨j, hw⟩ hnow)
        have continueScan_inv : ∀ (st_next : ActiveScan P Data),
            st_next.opId = st.opId → st_next.mode = st.mode →
            ({ (τ.stateAt t) with
                proc := Function.update (τ.stateAt t).proc i (.scanning st_next)
                stepCount := (τ.stateAt t).stepCount + 1 } = τ.stateAt (t + 1)) →
            (∃ iterS', τ.lastIdleStep i t + 1 ≤ iterS' ∧ iterS' ≤ t + 1 ∧
              (∀ k ∈ st_next.moved, ∃ w₁, τ.lastIdleStep i t + 1 ≤ w₁ ∧ w₁ < iterS' ∧
                τ.isWriteStep k w₁) ∧
              (st_next.phase = .collectA →
                ∀ k, k ∉ st_next.rem →
                  ∃ tA, iterS' ≤ tA ∧ tA ≤ t + 1 ∧
                    st_next.collectAVal k = (τ.stateAt tA).reg k) ∧
              (st_next.phase = .collectB →
                ∃ u, iterS' ≤ u ∧ u ≤ t + 1 ∧
                  (∀ k, ∃ tA, iterS' ≤ tA ∧ tA ≤ u ∧
                    st_next.collectAVal k = (τ.stateAt tA).reg k) ∧
                  (∀ k, k ∉ st_next.rem →
                    ∃ tB, u ≤ tB ∧ tB ≤ t + 1 ∧
                      st_next.collectBVal k = (τ.stateAt tB).reg k))) →
            TraceInv τ (t + 1) := by
          intro st_next hop_eq hmode_eq hs_eq hnext
          have hhist_eq : (τ.stateAt (t + 1)).history = (τ.stateAt t).history := by rw [← hs_eq]
          have hnot1 : (τ.stateAt (t + 1)).proc i ≠ .idle := by
            simp only [← hs_eq, Function.update_self]; nofun
          have hkeep := τ.lastIdleStep_keep i (by rw [hpi]; nofun) hnot1
          refine inv.of_local_active hpi hnow (.scanning st_next) nofun hs_eq
            (Or.inl ⟨st_next, rfl, hop_eq⟩) (fun _ _ _ h => nomatch h) ?_
          intro st' heq
          injection heq with h1; subst h1
          have hId₁ : st_next.opId < (τ.stateAt (t + 1)).history.length := by
            rw [hhist_eq, hop_eq]; exact hId
          refine ⟨hId₁, ?_, by omega, hkeep ▸ hnext⟩
          rw [getElem_of_eq hhist_eq hId₁ (hop_eq ▸ hId),
            getElem_congr_idx _ hop_eq (hop_eq ▸ hId) hId, hkeep, hmode_eq]
          exact hrec_i
        cases hph : st.phase with
        | collectA =>
          cases hrem : st.rem with
          | cons j rest =>
            simp only [hph, hrem, Option.some.injEq] at hstep
            refine continueScan_inv
              { st with phase := .collectA, rem := rest,
                        collectAVal := Function.update st.collectAVal j ((τ.stateAt t).reg j) }
              rfl rfl hstep ⟨iterS, hi₁, by omega, hmov, ?_, by intro hB; cases hB⟩
            intro _ k hk
            dsimp only at hk ⊢
            by_cases hkj : k = j
            · subst hkj; exact ⟨t, hi₂, by omega, Function.update_self _ _ _⟩
            · have hk_not : k ∉ j :: rest := by simp only [List.mem_cons, not_or]; exact ⟨hkj, hk⟩
              obtain ⟨tA, a1, a2, a3⟩ := hcA hph k (hrem ▸ hk_not)
              exact ⟨tA, a1, by omega, (Function.update_of_ne hkj _ _).trans a3⟩
          | nil =>
            simp only [hph, hrem, Option.some.injEq] at hstep
            refine continueScan_inv { st with phase := .collectB, rem := ord.elems }
              rfl rfl hstep ⟨iterS, hi₁, by omega, hmov, (by intro hA; cases hA), fun _ => ?_⟩
            refine ⟨t, hi₂, by omega,
              fun k => hcA hph k (by simp only [hrem, List.not_mem_nil, not_false_eq_true]),
              fun k hk => absurd (ord.complete k) hk⟩
        | collectB =>
          obtain ⟨u, hu₁, hu₂, ha_all, hb_rem⟩ := hcB hph
          cases hrem : st.rem with
          | cons j rest =>
            simp only [hph, hrem, Option.some.injEq] at hstep
            refine continueScan_inv
              { st with phase := .collectB, rem := rest,
                        collectBVal := Function.update st.collectBVal j ((τ.stateAt t).reg j) }
              rfl rfl hstep ⟨iterS, hi₁, by omega, hmov, (by intro hA; cases hA), fun _ => ?_⟩
            refine ⟨u, hu₁, by omega, ha_all, fun k hk => ?_⟩
            dsimp only at hk ⊢
            by_cases hkj : k = j
            · subst hkj; exact ⟨t, hu₂, by omega, Function.update_self _ _ _⟩
            · have hk_not : k ∉ j :: rest := by simp only [List.mem_cons, not_or]; exact ⟨hkj, hk⟩
              obtain ⟨tB, b1, b2, b3⟩ := hb_rem k (hrem ▸ hk_not)
              exact ⟨tB, b1, by omega, (Function.update_of_ne hkj _ _).trans b3⟩
          | nil =>
            simp only [hph, hrem] at hstep
            have hb_all : ∀ k, ∃ tB, u ≤ tB ∧ tB ≤ t ∧
                st.collectBVal k = (τ.stateAt tB).reg k := fun k =>
              hb_rem k (by simp only [hrem, List.not_mem_nil, not_false_eq_true])
            split_ifs at hstep with hclean
            · injection hstep with hs₁
              choose tA htA₁ htA₂ htA_eq using ha_all
              choose tB htB₁ htB₂ htB_eq using hb_all
              have hseq_eq : ∀ k,
                  ((τ.stateAt (tA k)).reg k).seq = ((τ.stateAt (tB k)).reg k).seq := fun k => by
                have := hclean k; rwa [htA_eq k, htB_eq k] at this
              have hsnap_u : memSnapshot (τ.stateAt u).reg =
                  fun k => (st.collectBVal k).data := by
                have h31 := τ.memSnapshot_eq_of_clean_double_collect htA₂ le_rfl htB₁
                  (fun k => le_trans (htB₂ k) (Nat.le_of_succ_le ht)) hseq_eq le_rfl le_rfl
                rw [h31]; funext k; rw [htB_eq k]
              exact finishScan_inv _ ⟨u, le_trans hi₁ hu₁, hu₂, hsnap_u⟩ hs₁
            · cases hfind : (ord.elems.find? fun k =>
                  decide ((st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved)) with
              | some k =>
                simp only [hfind, Option.some.injEq] at hstep
                have hk_bool := List.find?_some hfind
                have hk_pred : (st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved :=
                  of_decide_eq_true hk_bool
                obtain ⟨w₁, hw₁_lo, hw₁_hi, hw₁_write⟩ := hmov k hk_pred.2
                obtain ⟨tA, htA₁, htA₂, htA_eq⟩ := ha_all k
                obtain ⟨tB, htB₁, htB₂, htB_eq⟩ := hb_all k
                have hseq_ne : ((τ.stateAt tA).reg k).seq ≠ ((τ.stateAt tB).reg k).seq := by
                  have := hk_pred.1; rwa [htA_eq, htB_eq] at this
                obtain ⟨w₂, hw₂_lo, hw₂_hi, hw₂_write⟩ :=
                  τ.exists_writeStep_of_seq_ne k (le_trans htA₂ htB₁)
                    (le_trans htB₂ (Nat.le_of_succ_le ht)) hseq_ne
                have hpos : 0 < ((τ.stateAt tB).reg k).seq := by
                  rcases τ.reg_step_iff (t := w₂) k (by omega) with
                      ⟨-, hnw⟩ | ⟨_, _, _, -, -, hreg', -⟩
                  · exact absurd hw₂_write hnw
                  · have hmono := (τ.seq_mono_and_const_of_eq (t₁ := w₂ + 1) k hw₂_hi
                      (le_trans htB₂ (Nat.le_of_succ_le ht))).1
                    have hseq_w₂ : ((τ.stateAt (w₂ + 1)).reg k).seq =
                        ((τ.stateAt w₂).reg k).seq + 1 := by rw [hreg']
                    omega
                obtain ⟨w_star, hw_star_lt, hw_star_write, hw_star_reg, hnow_after⟩ :=
                  τ.exists_last_writeStep_of_seq_pos k
                    (le_trans htB₂ (Nat.le_of_succ_le ht)) hpos
                have hw₂_le_star : w₂ ≤ w_star := by
                  by_contra hlt_star
                  exact hnow_after w₂ (by omega) hw₂_hi hw₂_write
                have hidle_w₁ : (τ.stateAt (w₁ + 1)).proc k = .idle := by
                  rcases τ.reg_step_iff (t := w₁) k (by omega) with
                      ⟨-, hnw⟩ | ⟨_, _, _, -, -, -, hidle'⟩
                  · exact absurd hw₁_write hnw
                  · exact hidle'
                have hlast_ge : w₁ + 1 ≤ τ.lastIdleStep k w_star :=
                  τ.le_lastIdleStep_of_idle k (by omega) hidle_w₁
                obtain ⟨v_k, hv_k_lo, hv_k_hi, hv_k_snap⟩ :=
                  inv.reg_view_valid k w_star (by omega) hw_star_write
                have hview_eq :
                    (st.collectBVal k).view = ((τ.stateAt (w_star + 1)).reg k).view := by
                  rw [htB_eq, hw_star_reg]
                exact finishScan_inv _
                  ⟨v_k, by omega, by omega, hv_k_snap.trans hview_eq.symm⟩ hstep
              | none =>
                simp only [hfind, Option.some.injEq] at hstep
                let changed := univ.filter fun k =>
                  (st.collectAVal k).seq ≠ (st.collectBVal k).seq
                refine continueScan_inv
                  { st with moved := st.moved ∪ changed, phase := .collectA, rem := ord.elems }
                  rfl rfl hstep ⟨t + 1, by omega, le_rfl, ?_,
                    fun _ k hk => absurd (ord.complete k) hk, by intro hB; cases hB⟩
                intro k hk
                dsimp only at hk
                rcases mem_union.mp hk with hk_old | hk_new
                · obtain ⟨w₁, h1, h2, h3⟩ := hmov k hk_old
                  exact ⟨w₁, h1, by omega, h3⟩
                · have hne_k := (mem_filter.mp hk_new).2
                  obtain ⟨tA, htA₁, htA₂, htA_eq⟩ := ha_all k
                  obtain ⟨tB, htB₁, htB₂, htB_eq⟩ := hb_all k
                  rw [htA_eq, htB_eq] at hne_k
                  obtain ⟨w₁, hw₁_lo, hw₁_hi, hw₁_w⟩ :=
                    τ.exists_writeStep_of_seq_ne k (le_trans htA₂ htB₁)
                      (le_trans htB₂ (Nat.le_of_succ_le ht)) hne_k
                  exact ⟨w₁, by omega, by omega, hw₁_w⟩

end SnapshotTrace

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemmas 3.2–3.3, pp. 9–10][AfekAttiyaDolevGafniMerrittShavit1993]): for every execution
trace `τ` and every completed `scan` record `(id, resp, snap)` in the final history
`(τ.stateAt τ.events.length).history`, there exists a state index `v` strictly inside the scan's
execution interval (`invStep < v ≤ resp`) at which the instantaneous shared-memory state
`memSnapshot (τ.stateAt v).reg` equals `snap`. -/
theorem unbounded_exists_interval_snapshot_of_trace {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} (τ : SnapshotTrace ord dInit)
    {id : ℕ} (hId : id < (τ.stateAt τ.events.length).history.length)
    {resp : ℕ} {snap : P → Data}
    (hdone : ((τ.stateAt τ.events.length).history[id]'hId).status = .doneScan resp snap) :
    let entry := (τ.stateAt τ.events.length).history[id]'hId
    entry.kind = .scan ∧ entry.invStep < resp ∧ resp < τ.events.length ∧
      ∃ v, entry.invStep + 1 ≤ v ∧ v ≤ resp ∧ memSnapshot (τ.stateAt v).reg = snap :=
  (τ.traceInv_holds τ.events.length le_rfl).hist_doneScan id hId resp snap hdone

private theorem seqSnapshotMemAfter_append {P Data : Type*} [DecidableEq P] (mem : P → Data)
    (hist : List (SnapshotOpRecord P Data)) (xs ys : List ℕ) :
    seqSnapshotMemAfter mem hist (xs ++ ys) =
      seqSnapshotMemAfter (seqSnapshotMemAfter mem hist xs) hist ys := by
  induction xs generalizing mem with
  | nil => rfl
  | cons _ _ ih => exact ih _

private theorem getElem_completeHistoryAt_of_status_ne {P Data : Type*}
    {hist : List (SnapshotOpRecord P Data)} {opId k : ℕ} {newSt st : SnapshotOpStatus P Data}
    (hne : st ≠ newSt) (hk : k < (completeHistoryAt hist opId newSt).length)
    (hst : ((completeHistoryAt hist opId newSt)[k]'hk).status = st) :
    ∃ hk₀ : k < hist.length, (completeHistoryAt hist opId newSt)[k]'hk = hist[k]'hk₀ := by
  have hk₀ : k < hist.length := (length_completeHistoryAt hist opId newSt) ▸ hk
  refine ⟨hk₀, ?_⟩
  by_cases hop : opId < hist.length
  · have hset : completeHistoryAt hist opId newSt =
        hist.set opId { hist[opId] with status := newSt } := by
      simp only [completeHistoryAt, List.getElem?_eq_getElem hop]
    rw [SnapshotTrace.getElem_of_eq hset hk (by simp only [List.length_set]; exact hk₀)] at hst ⊢
    by_cases hko : k = opId
    · subst hko
      rw [List.getElem_set_self] at hst
      exact absurd hst.symm hne
    · rw [List.getElem_set_ne (Ne.symm hko)]
  · have hset : completeHistoryAt hist opId newSt = hist := by
      simp only [completeHistoryAt, List.getElem?_eq_none (Nat.le_of_not_lt hop)]
    exact SnapshotTrace.getElem_of_eq hset hk hk₀

/-- Distinct history entries never carry the same `.doneUpdate w` completion step. -/
private theorem doneUpdate_inj_of_trace {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} (τ : SnapshotTrace ord dInit) :
    ∀ t ≤ τ.events.length,
      ∀ id₁ id₂ (h₁ : id₁ < (τ.stateAt t).history.length)
        (h₂ : id₂ < (τ.stateAt t).history.length) w,
        ((τ.stateAt t).history[id₁]'h₁).status = .doneUpdate w →
        ((τ.stateAt t).history[id₂]'h₂).status = .doneUpdate w →
        id₁ = id₂ := by
  intro t ht
  induction t with
  | zero =>
    intro id₁ _ h₁; rw [SnapshotTrace.stateAt_zero] at h₁; cases h₁
  | succ t ih =>
    have ht_lt : t < τ.events.length := Nat.lt_of_succ_le ht
    have inv := τ.traceInv_holds t (Nat.le_of_succ_le ht)
    have ih_t := ih (Nat.le_of_succ_le ht)
    intro id₁ id₂ h₁ h₂ w hst₁ hst₂
    rcases (stepSnapshot_effect (τ.stateAt_step ht_lt)).2 with
        ⟨i, opId, val, snap, -, hpi, hs₁⟩ |
        ⟨-, -, hhist | ⟨rec, hpend, hhist⟩ | ⟨_, st, sn, -, -, -, hhist⟩⟩
    · have hhist : (τ.stateAt (t + 1)).history =
          completeHistoryAt (τ.stateAt t).history opId (.doneUpdate t) := by
        rw [hs₁, inv.stepCount_eq]
      by_cases hwt : w = t
      · subst w
        have eq_opId : ∀ {k} (hk : k < (τ.stateAt (t + 1)).history.length),
            ((τ.stateAt (t + 1)).history[k]'hk).status = .doneUpdate t → k = opId := by
          intro k hk hst
          by_contra hne
          have hk_c : k < (completeHistoryAt (τ.stateAt t).history opId (.doneUpdate t)).length :=
            hhist ▸ hk
          have hk₀ : k < (τ.stateAt t).history.length :=
            (length_completeHistoryAt _ _ _) ▸ hk_c
          obtain ⟨hOp, hrec_i, -, -⟩ := inv.proc_ready i opId val snap hpi
          have hget_op : (τ.stateAt t).history[opId]? =
              some ⟨i, .update val, τ.lastIdleStep i t, .pending⟩ := by
            rw [List.getElem?_eq_getElem hOp, hrec_i]
          have hset : (τ.stateAt (t + 1)).history =
              (τ.stateAt t).history.set opId
                ⟨i, .update val, τ.lastIdleStep i t, .doneUpdate t⟩ := by
            rw [hhist]; simp only [completeHistoryAt, hget_op]
          rw [SnapshotTrace.getElem_of_eq hset hk (by simp only [List.length_set]; exact hk₀),
            List.getElem_set_ne (Ne.symm hne)] at hst
          obtain ⟨_, -, -, hlt_w, -⟩ := inv.hist_doneUpdate k hk₀ t hst
          omega
        exact (eq_opId h₁ hst₁).trans (eq_opId h₂ hst₂).symm
      · have hne_st : SnapshotOpStatus.doneUpdate (P := P) (Data := Data) w ≠ .doneUpdate t :=
          fun h => hwt (SnapshotOpStatus.doneUpdate.inj h)
        have h₁' := hhist ▸ h₁
        have h₂' := hhist ▸ h₂
        rw [SnapshotTrace.getElem_of_eq hhist h₁ h₁'] at hst₁
        rw [SnapshotTrace.getElem_of_eq hhist h₂ h₂'] at hst₂
        obtain ⟨hk₁, heq₁⟩ := getElem_completeHistoryAt_of_status_ne hne_st h₁' hst₁
        obtain ⟨hk₂, heq₂⟩ := getElem_completeHistoryAt_of_status_ne hne_st h₂' hst₂
        exact ih_t id₁ id₂ hk₁ hk₂ w (heq₁ ▸ hst₁) (heq₂ ▸ hst₂)
    · exact ih_t id₁ id₂ (hhist ▸ h₁) (hhist ▸ h₂) w
        (by rwa [SnapshotTrace.getElem_of_eq hhist h₁ (hhist ▸ h₁)] at hst₁)
        (by rwa [SnapshotTrace.getElem_of_eq hhist h₂ (hhist ▸ h₂)] at hst₂)
    · have lt_old : ∀ {k} (hk : k < (τ.stateAt (t + 1)).history.length),
          ((τ.stateAt (t + 1)).history[k]'hk).status = .doneUpdate w →
          ∃ hk₀ : k < (τ.stateAt t).history.length,
            ((τ.stateAt t).history[k]'hk₀).status = .doneUpdate w := by
        intro k hk hst
        have hk₀ : k < (τ.stateAt t).history.length := by
          by_contra hge
          have heq : k = (τ.stateAt t).history.length := by
            rw [hhist, List.length_append, List.length_singleton] at hk; omega
          subst heq
          rw [SnapshotTrace.getElem_of_eq hhist hk
            (by rw [List.length_append, List.length_singleton]; omega)] at hst
          simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
            List.getElem_singleton, hpend] at hst
          cases hst
        refine ⟨hk₀, ?_⟩
        rwa [SnapshotTrace.getElem_of_eq hhist hk (by rw [List.length_append]; omega),
          List.getElem_append_left hk₀] at hst
      obtain ⟨hk₁, hs₁'⟩ := lt_old h₁ hst₁
      obtain ⟨hk₂, hs₂'⟩ := lt_old h₂ hst₂
      exact ih_t id₁ id₂ hk₁ hk₂ w hs₁' hs₂'
    · have h₁' := hhist ▸ h₁
      have h₂' := hhist ▸ h₂
      rw [SnapshotTrace.getElem_of_eq hhist h₁ h₁'] at hst₁
      rw [SnapshotTrace.getElem_of_eq hhist h₂ h₂'] at hst₂
      obtain ⟨hk₁, heq₁⟩ := getElem_completeHistoryAt_of_status_ne (fun h => by cases h) h₁' hst₁
      obtain ⟨hk₂, heq₂⟩ := getElem_completeHistoryAt_of_status_ne (fun h => by cases h) h₂' hst₂
      exact ih_t id₁ id₂ hk₁ hk₂ w (heq₁ ▸ hst₁) (heq₂ ▸ hst₂)

/-- Internal trace-level proof of `unbounded_snapshotLinearizable_of_reachable`. -/
private theorem snapshotLinearizable_of_trace {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} (τ : SnapshotTrace ord dInit) :
    SnapshotLinearizable dInit (τ.stateAt τ.events.length).history := by
  classical
  set T := τ.events.length
  have inv := τ.traceInv_holds T le_rfl
  have hinj := doneUpdate_inj_of_trace τ T le_rfl
  let scanPoint (invStep resp : ℕ) (snap : P → Data) : ℕ :=
    if h : ∃ v, invStep + 1 ≤ v ∧ v ≤ resp ∧ memSnapshot (τ.stateAt v).reg = snap then
      Classical.choose h
    else 0
  have scanPoint_spec : ∀ {invStep resp : ℕ} {snap : P → Data},
      (∃ v, invStep + 1 ≤ v ∧ v ≤ resp ∧ memSnapshot (τ.stateAt v).reg = snap) →
      invStep + 1 ≤ scanPoint invStep resp snap ∧
        scanPoint invStep resp snap ≤ resp ∧
        memSnapshot (τ.stateAt (scanPoint invStep resp snap)).reg = snap := by
    intro invStep resp snap hex
    dsimp only [scanPoint]; simp only [hex, ↓reduceDIte]; exact Classical.choose_spec hex
  let blockOf : ℕ → Option ℕ := fun id =>
    match (τ.stateAt T).history[id]? with
    | none => none
    | some entry =>
      match entry.status with
      | .pending => none
      | .doneUpdate w => some w
      | .doneScan resp snap => some (scanPoint entry.invStep resp snap)
  let scansAt : ℕ → List ℕ := fun t =>
    (List.range (τ.stateAt T).history.length).filter fun id =>
      decide (blockOf id = some t ∧
        ∃ r sn, ((τ.stateAt T).history[id]?.map SnapshotOpRecord.status) =
          some (.doneScan r sn))
  let updatesAt : ℕ → List ℕ := fun t =>
    (List.range (τ.stateAt T).history.length).filter fun id =>
      decide (blockOf id = some t ∧
        ∃ w, ((τ.stateAt T).history[id]?.map SnapshotOpRecord.status) =
          some (.doneUpdate w))
  let chunk : ℕ → List ℕ := fun t => scansAt t ++ updatesAt t
  let prefixSeq : ℕ → List ℕ := fun k => (List.range k).flatMap chunk
  have mem_scansAt_iff : ∀ t id, id ∈ scansAt t ↔
      ∃ (hId : id < (τ.stateAt T).history.length) (r : ℕ) (sn : P → Data),
        ((τ.stateAt T).history[id]'hId).status = .doneScan r sn ∧
        scanPoint ((τ.stateAt T).history[id]'hId).invStep r sn = t := by
    intro t id
    dsimp only [scansAt]
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨hId, hblk, r, sn, hmap⟩
      have hget := List.getElem?_eq_getElem (l := (τ.stateAt T).history) hId
      rw [hget, Option.map_some, Option.some.injEq] at hmap
      dsimp only [blockOf] at hblk
      simp only [hget, hmap, Option.some.injEq] at hblk
      exact ⟨hId, r, sn, hmap, hblk⟩
    · rintro ⟨hId, r, sn, hstat, hsp⟩
      have hget := List.getElem?_eq_getElem (l := (τ.stateAt T).history) hId
      refine ⟨hId, ?_, r, sn, by rw [hget, Option.map_some, hstat]⟩
      dsimp only [blockOf]; simp only [hget, hstat, hsp]
  have mem_updatesAt_iff : ∀ t id, id ∈ updatesAt t ↔
      ∃ hId : id < (τ.stateAt T).history.length,
        ((τ.stateAt T).history[id]'hId).status = .doneUpdate t := by
    intro t id
    dsimp only [updatesAt]
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨hId, hblk, w, hmap⟩
      have hget := List.getElem?_eq_getElem (l := (τ.stateAt T).history) hId
      rw [hget, Option.map_some, Option.some.injEq] at hmap
      dsimp only [blockOf] at hblk
      simp only [hget, hmap, Option.some.injEq] at hblk
      exact ⟨hId, hblk ▸ hmap⟩
    · rintro ⟨hId, hstat⟩
      have hget := List.getElem?_eq_getElem (l := (τ.stateAt T).history) hId
      refine ⟨hId, ?_, t, by rw [hget, Option.map_some, hstat]⟩
      dsimp only [blockOf]; simp only [hget, hstat]
  have hchunk_blk : ∀ t x, x ∈ chunk t → blockOf x = some t := by
    intro t x hx
    rcases List.mem_append.mp hx with hx | hx <;>
      dsimp only [scansAt, updatesAt] at hx <;>
      simp only [List.mem_filter, decide_eq_true_eq] at hx <;>
      exact hx.2.1
  have scansAt_valid : ∀ t ≤ T,
      seqSnapshotMemAfter (memSnapshot (τ.stateAt t).reg) (τ.stateAt T).history (scansAt t) =
        memSnapshot (τ.stateAt t).reg ∧
      seqSnapshotValid (memSnapshot (τ.stateAt t).reg) (τ.stateAt T).history (scansAt t) := by
    intro t _
    suffices ∀ xs : List ℕ,
        (∀ id ∈ xs,
          ∃ (hId : id < (τ.stateAt T).history.length) (resp : ℕ) (snap : P → Data),
            ((τ.stateAt T).history[id]'hId).kind = .scan ∧
            ((τ.stateAt T).history[id]'hId).status = .doneScan resp snap ∧
            snap = memSnapshot (τ.stateAt t).reg) →
        seqSnapshotMemAfter (memSnapshot (τ.stateAt t).reg) (τ.stateAt T).history xs =
          memSnapshot (τ.stateAt t).reg ∧
        seqSnapshotValid (memSnapshot (τ.stateAt t).reg) (τ.stateAt T).history xs by
      refine this (scansAt t) fun id hid => ?_
      obtain ⟨hId, r, sn, hstat, hsp⟩ := (mem_scansAt_iff t id).mp hid
      have hscan := inv.hist_doneScan id hId r sn hstat
      have hv_spec := scanPoint_spec hscan.2.2.2
      rw [hsp] at hv_spec
      exact ⟨hId, r, sn, hscan.1, hstat, hv_spec.2.2.symm⟩
    intro xs hpred
    induction xs with
    | nil => exact ⟨rfl, trivial⟩
    | cons id rest ih_s =>
      obtain ⟨hId, resp, snap, hkind, hstat, hsnap⟩ := hpred id List.mem_cons_self
      obtain ⟨hm_rest, hv_rest⟩ := ih_s fun x hx => hpred x (List.mem_cons_of_mem id hx)
      have hget := List.getElem?_eq_getElem (l := (τ.stateAt T).history) hId
      simp only [seqSnapshotMemAfter, seqSnapshotValid, hget, hkind, hstat]
      exact ⟨hm_rest, hsnap, hv_rest⟩
  have updatesAt_valid : ∀ t < T,
      seqSnapshotMemAfter (memSnapshot (τ.stateAt t).reg) (τ.stateAt T).history (updatesAt t) =
        memSnapshot (τ.stateAt (t + 1)).reg ∧
      seqSnapshotValid (memSnapshot (τ.stateAt t).reg) (τ.stateAt T).history (updatesAt t) := by
    intro t ht_lt
    by_cases hw : ∃ j, τ.isWriteStep j t
    · obtain ⟨j, hjw⟩ := hw
      obtain ⟨id₀, hId₀, hcaller₀, hstat₀⟩ := inv.writeStep_in_hist j t ht_lt hjw
      have hget₀ := List.getElem?_eq_getElem (l := (τ.stateAt T).history) hId₀
      have hupd_eq : updatesAt t = [id₀] := by
        have hmem_iff : ∀ x, x ∈ updatesAt t ↔ x = id₀ := fun x => by
          rw [mem_updatesAt_iff]
          exact ⟨fun ⟨hx, hs⟩ => hinj x id₀ hx hId₀ t hs hstat₀, fun h => h ▸ ⟨hId₀, hstat₀⟩⟩
        have hnd : (updatesAt t).Nodup := (List.nodup_range).filter _
        cases hlist : updatesAt t with
        | nil => exact absurd (hlist ▸ (hmem_iff id₀).mpr rfl) List.not_mem_nil
        | cons a tl =>
          obtain rfl : a = id₀ := (hmem_iff a).mp (hlist ▸ List.mem_cons_self)
          cases tl with
          | nil => rfl
          | cons b _ =>
            obtain rfl : b = a := (hmem_iff b).mp
              (hlist ▸ List.mem_cons_of_mem a List.mem_cons_self)
            rw [hlist, List.nodup_cons] at hnd
            exact absurd List.mem_cons_self hnd.1
      rw [hupd_eq]
      obtain ⟨val, hkind₀, -, -, -, hreg₀⟩ := inv.hist_doneUpdate id₀ hId₀ t hstat₀
      refine ⟨?_, by simp only [seqSnapshotValid, hget₀, hkind₀, hstat₀]⟩
      simp only [seqSnapshotMemAfter, hget₀, hkind₀, hcaller₀]
      funext p
      by_cases hpj : p = j
      · subst hpj
        have hreg_j := hcaller₀ ▸ hreg₀
        rw [Function.update_self, memSnapshot, hreg_j]
      · rw [Function.update_of_ne hpj, memSnapshot]
        rcases τ.reg_step_iff p ht_lt with ⟨hreg_eq, -⟩ | ⟨_, _, _, hev_p, -, -, -⟩
        · exact (congrArg SnapshotReg.data hreg_eq).symm
        · obtain ⟨_, _, _, _, hev_j, -⟩ := hjw
          exact absurd (SnapshotEvent.step.inj (hev_p.symm.trans hev_j)) hpj
    · have hupd_nil : updatesAt t = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro x hx
        obtain ⟨hx_lt, hstat⟩ := (mem_updatesAt_iff t x).mp hx
        obtain ⟨_, -, -, -, hw_x, -⟩ := inv.hist_doneUpdate x hx_lt t hstat
        exact hw ⟨_, hw_x⟩
      rw [hupd_nil]
      refine ⟨?_, trivial⟩
      dsimp only [seqSnapshotMemAfter]
      funext p
      rcases τ.reg_step_iff p ht_lt with ⟨hreg_eq, -⟩ | ⟨opId, val, snap, hev_p, hproc_p, -, -⟩
      · exact (congrArg SnapshotReg.data hreg_eq).symm
      · exact absurd ⟨p, ht_lt, opId, val, snap, hev_p, hproc_p⟩ hw
  have updatesAt_T : updatesAt T = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro x hx
    obtain ⟨hx_lt, hstat⟩ := (mem_updatesAt_iff T x).mp hx
    obtain ⟨_, -, -, hw_lt, -⟩ := inv.hist_doneUpdate x hx_lt T hstat
    omega
  have prefix_valid : ∀ k ≤ T + 1,
      seqSnapshotValid (fun _ => dInit) (τ.stateAt T).history (prefixSeq k) ∧
      (k ≤ T → seqSnapshotMemAfter (fun _ => dInit) (τ.stateAt T).history (prefixSeq k) =
        memSnapshot (τ.stateAt k).reg) := by
    intro k hk
    induction k with
    | zero =>
      dsimp only [prefixSeq]
      refine ⟨by simp only [List.range_zero, List.flatMap_nil, seqSnapshotValid], fun _ => ?_⟩
      simp only [List.range_zero, List.flatMap_nil, seqSnapshotMemAfter,
        SnapshotTrace.stateAt_zero]
      rfl
    | succ k ih_k =>
      obtain ⟨hv_k, hm_k⟩ := ih_k (Nat.le_of_succ_le hk)
      have hk_le_T : k ≤ T := Nat.le_of_succ_le_succ hk
      have hflat : prefixSeq (k + 1) = prefixSeq k ++ scansAt k ++ updatesAt k := by
        dsimp only [prefixSeq, chunk]
        simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.append_assoc]
      obtain ⟨hm_sc, hv_sc⟩ := scansAt_valid k hk_le_T
      simp only [hflat, seqSnapshotValid_append, seqSnapshotMemAfter_append, hm_k hk_le_T, hm_sc]
      rcases Nat.lt_or_eq_of_le hk_le_T with hk_lt | rfl
      · obtain ⟨hm_up, hv_up⟩ := updatesAt_valid k hk_lt
        exact ⟨⟨⟨hv_k, hv_sc⟩, hv_up⟩, fun _ => hm_up⟩
      · rw [updatesAt_T]
        exact ⟨⟨⟨hv_k, hv_sc⟩, trivial⟩, fun h => absurd h (by omega)⟩
  refine ⟨prefixSeq (T + 1), ?_, ?_, ?_, ?_, (prefix_valid (T + 1) le_rfl).1⟩
  · have hchunk_nd : ∀ t, (chunk t).Nodup := by
      intro t
      dsimp only [chunk]
      rw [List.nodup_append]
      refine ⟨(List.nodup_range).filter _, (List.nodup_range).filter _, fun a ha b hb hab => ?_⟩
      subst hab
      obtain ⟨hId₁, _, _, hs₁, -⟩ := (mem_scansAt_iff t a).mp ha
      obtain ⟨_, hs₂⟩ := (mem_updatesAt_iff t a).mp hb
      exact absurd (hs₁.symm.trans hs₂) nofun
    dsimp only [prefixSeq]
    rw [List.nodup_flatMap]
    refine ⟨fun t _ => hchunk_nd t,
      List.Pairwise.imp (fun {t₁ t₂} hne x hx₁ hx₂ => ?_) (List.nodup_range)⟩
    exact hne (Option.some.inj ((hchunk_blk t₁ x hx₁).symm.trans (hchunk_blk t₂ x hx₂)))
  · intro x hx
    dsimp only [prefixSeq] at hx
    simp only [List.mem_flatMap, List.mem_range] at hx
    obtain ⟨t, -, hxt⟩ := hx
    rcases List.mem_append.mp hxt with hxt | hxt
    · exact ((mem_scansAt_iff t x).mp hxt).1
    · exact ((mem_updatesAt_iff t x).mp hxt).1
  · intro id hId hcomp
    dsimp only [prefixSeq]
    simp only [List.mem_flatMap, List.mem_range]
    cases hst : ((τ.stateAt T).history[id]'hId).status with
    | pending =>
      simp only [SnapshotOpRecord.isCompleted, hst, Bool.false_eq_true] at hcomp
    | doneUpdate w =>
      obtain ⟨_, -, -, hw_lt, -⟩ := inv.hist_doneUpdate id hId w hst
      exact ⟨w, by omega, List.mem_append_right _ ((mem_updatesAt_iff w id).mpr ⟨hId, hst⟩)⟩
    | doneScan resp snap =>
      have hsc := inv.hist_doneScan id hId resp snap hst
      have hv_spec := scanPoint_spec hsc.2.2.2
      exact ⟨scanPoint ((τ.stateAt T).history[id]'hId).invStep resp snap,
        by have := hsc.2.2.1; omega,
        List.mem_append_left _ ((mem_scansAt_iff _ id).mpr ⟨hId, resp, snap, hst, rfl⟩)⟩
  · intro i hi j hj r hresp_i recJ hget_j hr_le
    obtain ⟨t₁, ht₁_lt, hi_chunk⟩ : ∃ t₁ < T + 1, i ∈ chunk t₁ := by
      dsimp only [prefixSeq] at hi; simpa only [List.mem_flatMap, List.mem_range] using hi
    obtain ⟨t₂, ht₂_lt, hj_chunk⟩ : ∃ t₂ < T + 1, j ∈ chunk t₂ := by
      dsimp only [prefixSeq] at hj; simpa only [List.mem_flatMap, List.mem_range] using hj
    have hb₁ := hchunk_blk t₁ i hi_chunk
    have hb₂ := hchunk_blk t₂ j hj_chunk
    have ht₁_le_r : t₁ ≤ r := by
      obtain ⟨recI, hget_i, hresp_eq⟩ := Option.bind_eq_some_iff.mp hresp_i
      obtain ⟨hId_i, rfl⟩ := List.getElem?_eq_some_iff.mp hget_i
      dsimp only [blockOf] at hb₁; simp only [hget_i] at hb₁
      cases hst_i : ((τ.stateAt T).history[i]'hId_i).status with
      | pending => simp only [hst_i] at hb₁; nomatch hb₁
      | doneScan resp snap =>
        simp only [hst_i, SnapshotOpRecord.respStep?, Option.some.injEq] at hb₁ hresp_eq
        have hv_spec := scanPoint_spec (inv.hist_doneScan i hId_i resp snap hst_i).2.2.2
        omega
      | doneUpdate w =>
        simp only [hst_i, SnapshotOpRecord.respStep?, Option.some.injEq] at hb₁ hresp_eq
        omega
    have hinv_lt_t₂ : recJ.invStep + 1 ≤ t₂ := by
      obtain ⟨hId_j, rfl⟩ := List.getElem?_eq_some_iff.mp hget_j
      dsimp only [blockOf] at hb₂; simp only [hget_j] at hb₂
      cases hst_j : ((τ.stateAt T).history[j]'hId_j).status with
      | pending => simp only [hst_j] at hb₂; nomatch hb₂
      | doneScan resp snap =>
        simp only [hst_j, Option.some.injEq] at hb₂
        have hv_spec := scanPoint_spec (inv.hist_doneScan j hId_j resp snap hst_j).2.2.2
        omega
      | doneUpdate w =>
        simp only [hst_j, Option.some.injEq] at hb₂
        obtain ⟨_, -, hinv_lt, -⟩ := inv.hist_doneUpdate j hId_j w hst_j
        omega
    have ht₁_lt_t₂ : t₁ < t₂ := by omega
    have hsplit_range : List.range (T + 1) = List.range t₂ ++ (List.range (T + 1)).drop t₂ :=
      (List.take_append_drop t₂ (List.range (T + 1))).symm.trans
        (by rw [List.take_range, Nat.min_eq_left (by omega)])
    have hseq_split : prefixSeq (T + 1) =
        (List.range t₂).flatMap chunk ++ ((List.range (T + 1)).drop t₂).flatMap chunk := by
      dsimp only [prefixSeq]; conv_lhs => rw [hsplit_range]; exact List.flatMap_append
    have hi_left : i ∈ (List.range t₂).flatMap chunk :=
      List.mem_flatMap.mpr ⟨t₁, List.mem_range.mpr ht₁_lt_t₂, hi_chunk⟩
    have hj_not_left : j ∉ (List.range t₂).flatMap chunk := by
      intro hj_in
      obtain ⟨t', ht'_lt, hj_t'⟩ := List.mem_flatMap.mp hj_in
      have := Option.some.inj ((hchunk_blk t' j hj_t').symm.trans hb₂)
      have := List.mem_range.mp ht'_lt
      omega
    rw [hseq_split, List.idxOf_append_of_mem hi_left, List.idxOf_append_of_notMem hj_not_left]
    exact lt_of_lt_of_le (List.idxOf_lt_length_of_mem hi_left) (Nat.le_add_right _ _)

/-- Unbounded sequence-numbered single-writer snapshot step for #7504 (after
[Afek et al., Theorem 1, p. 10][AfekAttiyaDolevGafniMerrittShavit1993]): every reachable
configuration `s` of `snapshotLTS ord dInit` has a linearizable operation history
`SnapshotLinearizable dInit s.history` against the canonical single-writer snapshot specification
(Section 4 bounded-register and Section 5 multi-writer snapshots remain open in #7504). -/
theorem unbounded_snapshotLinearizable_of_reachable {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} {s : SnapshotState P Data}
    (hreach : SnapshotReachable ord dInit s) :
    SnapshotLinearizable dInit s.history := by
  obtain ⟨tr, hmtr⟩ := hreach
  obtain ⟨τ, rfl, rfl⟩ := SnapshotTrace.of_mtr hmtr
  exact snapshotLinearizable_of_trace τ

end Cslib.Distributed.SetAgreement
