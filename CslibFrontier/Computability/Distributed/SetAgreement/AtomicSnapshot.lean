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
  cases hpi : s.proc i with
  | idle =>
    simp only [hpi] at h
    injection h with hs'
    exact ⟨rfl, hs'⟩
  | readyToWrite _ _ _ => simp only [hpi] at h; nomatch h
  | scanning _ => simp only [hpi] at h; nomatch h

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
  cases hpi : s.proc i with
  | idle =>
    simp only [hpi] at h
    injection h with hs'
    exact ⟨rfl, hs'⟩
  | readyToWrite _ _ _ => simp only [hpi] at h; nomatch h
  | scanning _ => simp only [hpi] at h; nomatch h

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemma 3.4, p. 10][AfekAttiyaDolevGafniMerrittShavit1993]): immediately after
`invokeScan i`, `remainingRegOps` equals `2 * n * (n + 1)` (`O(n²)` shared-register reads, bounded
across subsequent steps by `remainingSteps_lt_of_step`). -/
theorem remainingRegOps_invokeScan {P Data : Type*} [Fintype P] [DecidableEq P] (ord : ScanOrder P)
    (dInit : Data) {s s' : SnapshotState P Data} {i : P}
    (h : stepSnapshot ord dInit s (.invokeScan i) = some s') :
    remainingRegOps ord (s'.proc i) = 2 * Fintype.card P * (Fintype.card P + 1) := by
  obtain ⟨-, hs'⟩ := stepSnapshot_invokeScan_eq h
  subst hs'
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
  obtain ⟨-, hs'⟩ := stepSnapshot_invokeUpdate_eq h
  subst hs'
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
  rcases ev with j | ⟨j, val⟩ | j
  · have hij : i ≠ j := fun heq => hne.1 (heq ▸ rfl)
    obtain ⟨-, hs'⟩ := stepSnapshot_invokeScan_eq h
    subst hs'
    exact Function.update_of_ne hij _ _
  · have hij : i ≠ j := fun heq => hne.2.1 val (heq ▸ rfl)
    obtain ⟨-, hs'⟩ := stepSnapshot_invokeUpdate_eq h
    subst hs'
    exact Function.update_of_ne hij _ _
  · have hij : i ≠ j := fun heq => hne.2.2 (heq ▸ rfl)
    unfold stepSnapshot at h
    cases hpj : s.proc j with
    | idle => simp only [hpj] at h; nomatch h
    | readyToWrite opId val snap =>
      simp only [hpj] at h
      injection h with hs'
      subst hs'
      exact Function.update_of_ne hij _ _
    | scanning st =>
      simp only [hpj] at h
      rcases hph : st.phase with _ | _ <;> rcases hrem : st.rem with _ | ⟨k, rest⟩ <;>
        simp only [hph, hrem] at h
      · injection h with hs'
        subst hs'
        exact Function.update_of_ne hij _ _
      · injection h with hs'
        subst hs'
        exact Function.update_of_ne hij _ _
      · split_ifs at h with hclean
        · injection h with hs'
          subst hs'
          unfold finishScan
          cases st.mode <;> exact Function.update_of_ne hij _ _
        · cases hfind : (ord.elems.find? fun k =>
              decide ((st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved)) with
          | some k =>
            simp only [hfind] at h
            injection h with hs'
            subst hs'
            unfold finishScan
            cases st.mode <;> exact Function.update_of_ne hij _ _
          | none =>
            simp only [hfind] at h
            injection h with hs'
            subst hs'
            exact Function.update_of_ne hij _ _
      · injection h with hs'
        subst hs'
        exact Function.update_of_ne hij _ _

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
  induction hfuel : remainingSteps ord (s.proc i) using Nat.strong_induction_on generalizing s with
  | _ m ih =>
    subst hfuel
    by_cases hact : s.proc i = .idle
    · exact ⟨0, s, Nat.zero_le _, Cslib.LTS.MTr.refl, hact⟩
    · obtain ⟨s₁, hs₁⟩ := step_enabled_of_not_idle ord dInit s i hact
      have hlt := (remainingSteps_lt_of_step ord dInit hs₁).1
      obtain ⟨k, s', hk_le, hmtr, hidle⟩ := ih _ hlt s₁ rfl
      refine ⟨k + 1, s', by omega, ?_, hidle⟩
      rw [List.replicate_succ]
      exact Cslib.LTS.MTr.stepL hs₁ hmtr

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
  suffices ∀ (s₀ s₁ : SnapshotState P Data) (tr : List (SnapshotEvent P Data)),
      (snapshotLTS ord dInit).MTr s₀ tr s₁ →
      ∃ (states : List (SnapshotState P Data)) (hlen : states.length = tr.length + 1),
        (∀ h0 : 0 < states.length, states[0]'h0 = s₀) ∧
        (∀ hlast : tr.length < states.length, states[tr.length]'hlast = s₁) ∧
        (∀ t (ht : t < tr.length),
          stepSnapshot ord dInit (states[t]'(by omega)) tr[t] =
            some (states[t + 1]'(by omega))) by
    obtain ⟨states, hlen, h0, hlast, hstep⟩ := this _ _ tr hmtr
    refine ⟨⟨tr, states, hlen, h0 (by omega), hstep⟩, rfl, ?_⟩
    have hlt : tr.length < states.length := by omega
    simp only [stateAt, hlt, ↓reduceDIte, hlast hlt]
  intro s₀ s₁ tr h
  induction h with
  | refl =>
    exact ⟨[ _ ], rfl, fun _ => rfl, fun _ => rfl, fun _ ht => nomatch ht⟩
  | @stepL s₀ ev s_mid tr s₁ hstep _ ih =>
    obtain ⟨sts, hlen, h0, hlast, hvalid⟩ := ih
    refine ⟨s₀ :: sts, by simp only [List.length_cons, hlen], fun _ => rfl, ?_, ?_⟩
    · intro hl
      simp only [List.length_cons, List.getElem_cons_succ]
      exact hlast (by omega)
    · intro t ht
      cases t with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, h0 (by omega)]
        exact hstep
      | succ t =>
        simp only [List.getElem_cons_succ]
        exact hvalid t (Nat.lt_of_succ_lt_succ ht)

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
  have hstep := τ.stateAt_step ht
  rcases hev : τ.events[t] with i | ⟨i, v⟩ | i
  · rw [hev] at hstep
    obtain ⟨-, hs'⟩ := stepSnapshot_invokeScan_eq hstep
    left
    refine ⟨by rw [← hs'], ?_⟩
    rintro ⟨_, _, _, _, h1, _⟩
    rw [hev] at h1
    cases h1
  · rw [hev] at hstep
    obtain ⟨-, hs'⟩ := stepSnapshot_invokeUpdate_eq hstep
    left
    refine ⟨by rw [← hs'], ?_⟩
    rintro ⟨_, _, _, _, h1, _⟩
    rw [hev] at h1
    cases h1
  · rw [hev] at hstep
    unfold stepSnapshot at hstep
    cases hpi : (τ.stateAt t).proc i with
    | idle => simp only [hpi] at hstep; nomatch hstep
    | readyToWrite opId val snap =>
      simp only [hpi] at hstep
      injection hstep with hs'
      by_cases hij : j = i
      · subst hij
        right
        refine ⟨opId, val, snap, rfl, hpi, ?_, ?_⟩
        · rw [← hs']
          exact Function.update_self _ _ _
        · rw [← hs']
          exact Function.update_self _ _ _
      · left
        refine ⟨by rw [← hs']; exact Function.update_of_ne hij _ _, ?_⟩
        rintro ⟨_, _, _, _, h1, _⟩
        rw [hev] at h1
        injection h1 with hji
        exact hij hji.symm
    | scanning st =>
      simp only [hpi] at hstep
      have hnotw : ¬ τ.isWriteStep j t := by
        rintro ⟨_, _, _, _, h1, h2⟩
        rw [hev] at h1
        injection h1 with hij
        subst hij
        rw [hpi] at h2
        cases h2
      left
      refine ⟨?_, hnotw⟩
      cases hph : st.phase <;> cases hrem : st.rem <;> simp only [hph, hrem] at hstep
      · injection hstep with hs'
        rw [← hs']
      · injection hstep with hs'
        rw [← hs']
      · split_ifs at hstep with hclean
        · injection hstep with hs'
          rw [← hs']
          unfold finishScan
          cases st.mode <;> rfl
        · cases hfind : (ord.elems.find? fun k =>
              decide ((st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved)) <;>
            simp only [hfind] at hstep
          · injection hstep with hs'
            rw [← hs']
          · injection hstep with hs'
            rw [← hs']
            unfold finishScan
            cases st.mode <;> rfl
      · injection hstep with hs'
        rw [← hs']

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
    -- Helper: preserve `reg_view_valid` whenever no write occurs at step `t`
    have reg_unchanged_valid :
        ¬ (∃ j, τ.isWriteStep j t) →
        ∀ j w, w < t + 1 → τ.isWriteStep j w →
          ∃ v, τ.lastIdleStep j w + 1 ≤ v ∧ v ≤ w ∧
            memSnapshot (τ.stateAt v).reg = ((τ.stateAt (w + 1)).reg j).view := by
      intro hnow j w hw hwrite
      rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw' | rfl
      · exact inv.reg_view_valid j w hw' hwrite
      · exact absurd ⟨j, hwrite⟩ hnow
    -- Shared helper for `.invokeScan i` and `.invokeUpdate i val`
    have invoke_inv : ∀ (i : P) (mode : ScanMode Data),
        (τ.stateAt t).proc i = .idle →
        ¬ (∃ j, τ.isWriteStep j t) →
        (let opId := (τ.stateAt t).history.length
         let dummy := fun _ : P => SnapshotReg.init (P := P) dInit
         let st : ActiveScan P Data := ⟨mode, opId, ∅, .collectA, ord.elems, dummy, dummy⟩
         let kind := match mode with | .external => .scan | .embedded v => .update v
         ({ reg := (τ.stateAt t).reg
            proc := Function.update (τ.stateAt t).proc i (.scanning st)
            history := (τ.stateAt t).history ++ [⟨i, kind, (τ.stateAt t).stepCount, .pending⟩]
            stepCount := (τ.stateAt t).stepCount + 1 } : SnapshotState P Data) =
          τ.stateAt (t + 1)) →
        TraceInv τ (t + 1) := by
      intro i mode hpi hnow hs₁
      let kind : SnapshotOpKind Data :=
        match mode with | .external => .scan | .embedded v => .update v
      let dummy := fun _ : P => SnapshotReg.init (P := P) dInit
      let st_new : ActiveScan P Data :=
        ⟨mode, (τ.stateAt t).history.length, ∅, .collectA, ord.elems, dummy, dummy⟩
      have hlast_i : τ.lastIdleStep i (t + 1) = t := by
        have hnot : (τ.stateAt (t + 1)).proc i ≠ .idle := by
          rw [← hs₁]; simp only [Function.update_self]; nofun
        rw [τ.lastIdleStep_eq_of_step_not_idle i hnot,
          (ProcSnapshotState.isIdle_eq_true _).mpr hpi]
        simp only [↓reduceIte]
      have hhist_eq : (τ.stateAt (t + 1)).history =
          (τ.stateAt t).history ++ [⟨i, kind, t, .pending⟩] := by
        rw [← hs₁, inv.stepCount_eq]
        cases mode <;> rfl
      refine ⟨by rw [← hs₁]; simp only [inv.stepCount_eq],
        reg_unchanged_valid hnow, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro p opId v' snap hp
        by_cases hpi' : p = i
        · subst hpi'; rw [← hs₁] at hp; simp only [Function.update_self] at hp; cases hp
        · have hp_old : (τ.stateAt t).proc p = .readyToWrite opId v' snap := by
            rw [← hs₁] at hp; dsimp only at hp; rwa [Function.update_of_ne hpi'] at hp
          have hkeep := τ.lastIdleStep_keep p (by rw [hp_old]; nofun) (by rw [hp]; nofun)
          obtain ⟨hId, hrec, hlt_t, v, hv₁, hv₂, hsnap⟩ := inv.proc_ready p opId v' snap hp_old
          have hId₁ : opId < (τ.stateAt (t + 1)).history.length := by
            rw [hhist_eq, List.length_append]; omega
          refine ⟨hId₁, ?_, by omega, v, by omega, by omega, hsnap⟩
          rw [getElem_of_eq hhist_eq hId₁ (by rw [List.length_append]; omega),
            List.getElem_append_left hId, hkeep]
          exact hrec
      · intro p st hp
        by_cases hpi' : p = i
        · subst hpi'
          rw [← hs₁] at hp
          simp only [Function.update_self, ProcSnapshotState.scanning.injEq] at hp
          subst hp
          have hId₁ : (τ.stateAt t).history.length < (τ.stateAt (t + 1)).history.length := by
            rw [hhist_eq, List.length_append, List.length_singleton]; omega
          refine ⟨hId₁, ?_, by omega, t + 1, by omega, le_rfl, ?_, ?_, ?_⟩
          · rw [getElem_of_eq hhist_eq hId₁
              (by rw [List.length_append, List.length_singleton]; omega)]
            simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
              List.getElem_singleton, hlast_i]
            cases mode <;> rfl
          · intro k hk; exact absurd hk (notMem_empty k)
          · intro _ k hk; exact absurd (ord.complete k) hk
          · intro hph; cases hph
        · have hp_old : (τ.stateAt t).proc p = .scanning st := by
            rw [← hs₁] at hp; dsimp only at hp; rwa [Function.update_of_ne hpi'] at hp
          have hkeep := τ.lastIdleStep_keep p (by rw [hp_old]; nofun) (by rw [hp]; nofun)
          obtain ⟨hId, hrec, hlt_t, iterS, hi₁, hi₂, hmov, hcA, hcB⟩ :=
            inv.proc_scan p st hp_old
          have hId₁ : st.opId < (τ.stateAt (t + 1)).history.length := by
            rw [hhist_eq, List.length_append]; omega
          refine ⟨hId₁, ?_, by omega, iterS, by omega, by omega, ?_, ?_, ?_⟩
          · rw [getElem_of_eq hhist_eq hId₁ (by rw [List.length_append]; omega),
              List.getElem_append_left hId, hkeep]
            exact hrec
          · intro k hk; rw [hkeep]; exact hmov k hk
          · intro hA k hk
            obtain ⟨tA, h₁, h₂, h₃⟩ := hcA hA k hk
            exact ⟨tA, h₁, by omega, h₃⟩
          · intro hB
            obtain ⟨u, hu₁, hu₂, ha, hb⟩ := hcB hB
            refine ⟨u, hu₁, by omega, ha, fun k hk => ?_⟩
            obtain ⟨tB, h₁, h₂, h₃⟩ := hb k hk
            exact ⟨tB, h₁, by omega, h₃⟩
      · intro id hId hpend
        have hid_le : id ≤ (τ.stateAt t).history.length := by
          rw [hhist_eq, List.length_append, List.length_singleton] at hId; omega
        rcases Nat.lt_or_eq_of_le hid_le with hlt_id | rfl
        · have hrec_eq :
              (τ.stateAt (t + 1)).history[id]'hId = (τ.stateAt t).history[id]'hlt_id := by
            rw [getElem_of_eq hhist_eq hId (by rw [List.length_append]; omega),
              List.getElem_append_left hlt_id]
          rw [hrec_eq] at hpend ⊢
          obtain ⟨hinv, hlt_t, hact_old⟩ := inv.hist_pending id hlt_id hpend
          have hne_i : ((τ.stateAt t).history[id]'hlt_id).caller ≠ i := by
            intro heq
            rcases hact_old with ⟨st, hp, -⟩ | ⟨v', sn', hp⟩ <;> rw [heq, hpi] at hp <;> cases hp
          have hnot_old :
              (τ.stateAt t).proc ((τ.stateAt t).history[id]'hlt_id).caller ≠ .idle := by
            rcases hact_old with ⟨_, hp, -⟩ | ⟨_, _, hp⟩ <;> rw [hp] <;> nofun
          have hproc_same : (τ.stateAt (t + 1)).proc ((τ.stateAt t).history[id]'hlt_id).caller =
              (τ.stateAt t).proc ((τ.stateAt t).history[id]'hlt_id).caller := by
            rw [← hs₁]; exact Function.update_of_ne hne_i _ _
          have hkeep := τ.lastIdleStep_keep _ hnot_old (by rw [hproc_same]; exact hnot_old)
          rw [hkeep, hproc_same]
          exact ⟨hinv, by omega, hact_old⟩
        · have hrec_new : (τ.stateAt (t + 1)).history[(τ.stateAt t).history.length]'hId =
              ⟨i, kind, t, .pending⟩ := by
            rw [getElem_of_eq hhist_eq hId
              (by rw [List.length_append, List.length_singleton]; omega)]
            simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
              List.getElem_singleton]
          simp only [hrec_new, hlast_i, Nat.lt_succ_self, true_and]
          refine Or.inl ⟨st_new, ?_, rfl⟩
          rw [← hs₁]; exact Function.update_self _ _ _
      · intro id hId resp snap hdone
        have hlt_id : id < (τ.stateAt t).history.length := by
          by_contra hge
          have heq : id = (τ.stateAt t).history.length := by
            rw [hhist_eq, List.length_append, List.length_singleton] at hId; omega
          subst heq
          rw [getElem_of_eq hhist_eq hId
            (by rw [List.length_append, List.length_singleton]; omega)] at hdone
          simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
            List.getElem_singleton] at hdone
          cases hdone
        have hrec_eq :
            (τ.stateAt (t + 1)).history[id]'hId = (τ.stateAt t).history[id]'hlt_id := by
          rw [getElem_of_eq hhist_eq hId (by rw [List.length_append]; omega),
            List.getElem_append_left hlt_id]
        rw [hrec_eq] at hdone ⊢
        obtain ⟨hk, hi, hr, v, hv⟩ := inv.hist_doneScan id hlt_id resp snap hdone
        exact ⟨hk, hi, by omega, v, hv⟩
      · intro id hId resp hdone
        have hlt_id : id < (τ.stateAt t).history.length := by
          by_contra hge
          have heq : id = (τ.stateAt t).history.length := by
            rw [hhist_eq, List.length_append, List.length_singleton] at hId; omega
          subst heq
          rw [getElem_of_eq hhist_eq hId
            (by rw [List.length_append, List.length_singleton]; omega)] at hdone
          simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
            List.getElem_singleton] at hdone
          cases hdone
        have hrec_eq :
            (τ.stateAt (t + 1)).history[id]'hId = (τ.stateAt t).history[id]'hlt_id := by
          rw [getElem_of_eq hhist_eq hId (by rw [List.length_append]; omega),
            List.getElem_append_left hlt_id]
        rw [hrec_eq] at hdone ⊢
        obtain ⟨val', hk, hi, hr, hw, hd⟩ := inv.hist_doneUpdate id hlt_id resp hdone
        exact ⟨val', hk, hi, by omega, hw, hd⟩
      · intro j w hw hwrite
        rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw' | rfl
        · obtain ⟨id, hId, hc, hs⟩ := inv.writeStep_in_hist j w hw' hwrite
          have hId₁ : id < (τ.stateAt (t + 1)).history.length := by
            rw [hhist_eq, List.length_append]; omega
          refine ⟨id, hId₁, ?_, ?_⟩ <;>
            rw [getElem_of_eq hhist_eq hId₁ (by rw [List.length_append]; omega),
              List.getElem_append_left hId]
          · exact hc
          · exact hs
        · exact absurd ⟨j, hwrite⟩ hnow
    rcases hev : τ.events[t] with i | ⟨i, val⟩ | i
    · -- Case 1: `.invokeScan i`
      rw [hev] at hstep
      obtain ⟨hpi, hs₁⟩ := stepSnapshot_invokeScan_eq hstep
      exact invoke_inv i .external hpi
        (by rintro ⟨_, _, _, _, _, h1, _⟩; rw [hev] at h1; cases h1) hs₁
    · -- Case 2: `.invokeUpdate i val`
      rw [hev] at hstep
      obtain ⟨hpi, hs₁⟩ := stepSnapshot_invokeUpdate_eq hstep
      exact invoke_inv i (.embedded val) hpi
        (by rintro ⟨_, _, _, _, _, h1, _⟩; rw [hev] at h1; cases h1) hs₁
    · -- Case 3: `.step i`
      rw [hev] at hstep
      unfold stepSnapshot at hstep
      -- Shared preservation of `proc_ready`, `proc_scan`, and `hist_pending` whenever active
      -- operation `activeId` of `i` completes (`newSt ≠ .pending`) and `proc i` returns to `.idle`!
      have idleComplete_preserve :
          ∀ (activeId : ℕ) (hId : activeId < (τ.stateAt t).history.length)
            (oldKind : SnapshotOpKind Data) (newSt : SnapshotOpStatus P Data),
          newSt ≠ .pending →
          (τ.stateAt t).history[activeId]'hId = ⟨i, oldKind, τ.lastIdleStep i t, .pending⟩ →
          ((∃ s0, (τ.stateAt t).proc i = .scanning s0 ∧ s0.opId = activeId) ∨
            (∃ v0 sn0, (τ.stateAt t).proc i = .readyToWrite activeId v0 sn0)) →
          (τ.stateAt (t + 1)).proc = Function.update (τ.stateAt t).proc i .idle →
          (τ.stateAt (t + 1)).history =
            completeHistoryAt (τ.stateAt t).history activeId newSt →
          (∀ p, p ≠ i → ∀ k, (τ.stateAt (t + 1)).reg k = (τ.stateAt t).reg k ∨ True) →
          (τ.stateAt (t + 1)).history.length = (τ.stateAt t).history.length ∧
          (∀ id (h₁ : id < (τ.stateAt (t + 1)).history.length)
              (h₀ : id < (τ.stateAt t).history.length),
            (τ.stateAt (t + 1)).history[id]'h₁ =
              if id = activeId then ⟨i, oldKind, τ.lastIdleStep i t, newSt⟩
              else (τ.stateAt t).history[id]'h₀) ∧
          (∀ p id' v' sn',
            (τ.stateAt (t + 1)).proc p = .readyToWrite id' v' sn' →
            ∃ (hId₁ : id' < (τ.stateAt (t + 1)).history.length),
              (τ.stateAt (t + 1)).history[id']'hId₁ =
                ⟨p, .update v', τ.lastIdleStep p (t + 1), .pending⟩ ∧
              τ.lastIdleStep p (t + 1) < t + 1 ∧
              ∃ v, τ.lastIdleStep p (t + 1) + 1 ≤ v ∧ v ≤ t + 1 ∧
                memSnapshot (τ.stateAt v).reg = sn') ∧
          (∀ p st',
            (τ.stateAt (t + 1)).proc p = .scanning st' →
            ∃ (hId₁ : st'.opId < (τ.stateAt (t + 1)).history.length),
              (τ.stateAt (t + 1)).history[st'.opId]'hId₁ =
                ⟨p, match st'.mode with | .external => .scan | .embedded val => .update val,
                  τ.lastIdleStep p (t + 1), .pending⟩ ∧
              τ.lastIdleStep p (t + 1) < t + 1 ∧
              ∃ iterS', τ.lastIdleStep p (t + 1) + 1 ≤ iterS' ∧ iterS' ≤ t + 1 ∧
                (∀ k ∈ st'.moved, ∃ w₁, τ.lastIdleStep p (t + 1) + 1 ≤ w₁ ∧ w₁ < iterS' ∧
                  τ.isWriteStep k w₁) ∧
                (st'.phase = .collectA →
                  ∀ k, k ∉ st'.rem →
                    ∃ tA, iterS' ≤ tA ∧ tA ≤ t + 1 ∧
                      st'.collectAVal k = (τ.stateAt tA).reg k) ∧
                (st'.phase = .collectB →
                  ∃ u, iterS' ≤ u ∧ u ≤ t + 1 ∧
                    (∀ k, ∃ tA, iterS' ≤ tA ∧ tA ≤ u ∧
                      st'.collectAVal k = (τ.stateAt tA).reg k) ∧
                    (∀ k, k ∉ st'.rem →
                      ∃ tB, u ≤ tB ∧ tB ≤ t + 1 ∧
                        st'.collectBVal k = (τ.stateAt tB).reg k))) ∧
          (∀ id (hId' : id < (τ.stateAt (t + 1)).history.length),
            ((τ.stateAt (t + 1)).history[id]'hId').status = .pending →
            ((τ.stateAt (t + 1)).history[id]'hId').invStep =
              τ.lastIdleStep ((τ.stateAt (t + 1)).history[id]'hId').caller (t + 1) ∧
            ((τ.stateAt (t + 1)).history[id]'hId').invStep < t + 1 ∧
              ((∃ st', (τ.stateAt (t + 1)).proc
                  ((τ.stateAt (t + 1)).history[id]'hId').caller = .scanning st' ∧
                  st'.opId = id) ∨
               (∃ v' sn', (τ.stateAt (t + 1)).proc
                  ((τ.stateAt (t + 1)).history[id]'hId').caller =
                  .readyToWrite id v' sn'))) := by
        intro activeId hId oldKind newSt hnew_ne hrec_i hact_i hproc_eq hhist_upd _
        have hhist_len : (τ.stateAt (t + 1)).history.length = (τ.stateAt t).history.length := by
          rw [hhist_upd]; exact length_completeHistoryAt _ _ _
        have hhist_at : ∀ id (h₁ : id < (τ.stateAt (t + 1)).history.length)
            (h₀ : id < (τ.stateAt t).history.length),
            (τ.stateAt (t + 1)).history[id]'h₁ =
              if id = activeId then ⟨i, oldKind, τ.lastIdleStep i t, newSt⟩
              else (τ.stateAt t).history[id]'h₀ := by
          intro id h₁ h₀
          have hget_op : (τ.stateAt t).history[activeId]? =
              some ⟨i, oldKind, τ.lastIdleStep i t, .pending⟩ := by
            rw [List.getElem?_eq_getElem hId, hrec_i]
          have hset : (τ.stateAt (t + 1)).history =
              (τ.stateAt t).history.set activeId
                ⟨i, oldKind, τ.lastIdleStep i t, newSt⟩ := by
            rw [hhist_upd]; simp only [completeHistoryAt, hget_op]
          rw [getElem_of_eq hset h₁ (by simp only [List.length_set]; exact h₀)]
          split_ifs with heq
          · subst id; exact List.getElem_set_self (by simp only [List.length_set]; exact h₀)
          · exact List.getElem_set_ne (Ne.symm heq) (by simp only [List.length_set]; exact h₀)
        refine ⟨hhist_len, hhist_at, ?_, ?_, ?_⟩
        · intro p id' v' sn' hp
          by_cases hpi' : p = i
          · subst hpi'; rw [hproc_eq] at hp; simp only [Function.update_self] at hp; cases hp
          · have hp_old : (τ.stateAt t).proc p = .readyToWrite id' v' sn' := by
              rw [hproc_eq] at hp; rwa [Function.update_of_ne hpi'] at hp
            have hkeep := τ.lastIdleStep_keep p (by rw [hp_old]; nofun) (by rw [hp]; nofun)
            obtain ⟨hId', hrec', hlt', v, h1, h2, h3⟩ := inv.proc_ready p id' v' sn' hp_old
            have hne_id : id' ≠ activeId := by
              intro heq; subst id'
              have := congrArg SnapshotOpRecord.caller (hrec'.symm.trans hrec_i)
              exact hpi' this
            refine ⟨by omega, ?_, by omega, v, by omega, by omega, h3⟩
            rw [hhist_at id' (by omega) hId',
              ite_eq_right_iff.mpr fun h => absurd h hne_id, hkeep]
            exact hrec'
        · intro p st' hp
          by_cases hpi' : p = i
          · subst hpi'; rw [hproc_eq] at hp; simp only [Function.update_self] at hp; cases hp
          · have hp_old : (τ.stateAt t).proc p = .scanning st' := by
              rw [hproc_eq] at hp; rwa [Function.update_of_ne hpi'] at hp
            have hkeep := τ.lastIdleStep_keep p (by rw [hp_old]; nofun) (by rw [hp]; nofun)
            obtain ⟨hId', hrec', hlt', iterS', h1, h2, hm', ha', hb'⟩ :=
              inv.proc_scan p st' hp_old
            have hne_id : st'.opId ≠ activeId := by
              intro heq
              have hidx := getElem_congr_idx (τ.stateAt t).history heq hId' hId
              have := congrArg SnapshotOpRecord.caller (hrec'.symm.trans (hidx.trans hrec_i))
              exact hpi' this
            refine ⟨by omega, ?_, by omega, iterS', by omega, by omega, ?_, ?_, ?_⟩
            · rw [hhist_at st'.opId (by omega) hId',
                ite_eq_right_iff.mpr fun h => absurd h hne_id, hkeep]
              exact hrec'
            · intro k hk; rw [hkeep]; exact hm' k hk
            · intro hA k hk
              obtain ⟨tA, a1, a2, a3⟩ := ha' hA k hk
              exact ⟨tA, a1, by omega, a3⟩
            · intro hB
              obtain ⟨u, u1, u2, ha, hb⟩ := hb' hB
              refine ⟨u, u1, by omega, ha, fun k hk => ?_⟩
              obtain ⟨tB, b1, b2, b3⟩ := hb k hk
              exact ⟨tB, b1, by omega, b3⟩
        · intro id hId' hpend
          have hId0 : id < (τ.stateAt t).history.length := by omega
          have hne_id : id ≠ activeId := by
            intro heq; subst id
            have hnew := hhist_at activeId hId' hId0
            simp only [↓reduceIte] at hnew
            rw [hnew] at hpend
            exact hnew_ne hpend
          have hrec_eq : (τ.stateAt (t + 1)).history[id]'hId' =
              (τ.stateAt t).history[id]'hId0 := by
            rw [hhist_at id hId' hId0, ite_eq_right_iff.mpr fun h => absurd h hne_id]
          rw [hrec_eq] at hpend ⊢
          obtain ⟨hinv, hlt', hact_old⟩ := inv.hist_pending id hId0 hpend
          have hne_i : ((τ.stateAt t).history[id]'hId0).caller ≠ i := by
            intro heq
            rw [heq] at hact_old
            exact hne_id (active_opId_unique hact_old hact_i)
          have hnot_old :
              (τ.stateAt t).proc ((τ.stateAt t).history[id]'hId0).caller ≠ .idle := by
            rcases hact_old with ⟨_, hp, -⟩ | ⟨_, _, hp⟩ <;> rw [hp] <;> nofun
          have hproc_same :
              (τ.stateAt (t + 1)).proc ((τ.stateAt t).history[id]'hId0).caller =
              (τ.stateAt t).proc ((τ.stateAt t).history[id]'hId0).caller := by
            rw [hproc_eq]; exact Function.update_of_ne hne_i _ _
          have hkeep := τ.lastIdleStep_keep _ hnot_old (by rw [hproc_same]; exact hnot_old)
          rw [hkeep, hproc_same]
          exact ⟨hinv, by omega, hact_old⟩
      cases hpi : (τ.stateAt t).proc i with
      | idle => simp only [hpi] at hstep; nomatch hstep
      | readyToWrite opId val snap =>
        -- Subcase 3a: Atomic register write (`line 2` of `update_i` in Figure 3)
        simp only [hpi] at hstep
        injection hstep with hs₁
        obtain ⟨hId, hrec_i, hlt_t, v_snap, hv₁, hv₂, hsnap_eq⟩ :=
          inv.proc_ready i opId val snap hpi
        obtain ⟨hhist_len, hhist_at, hpr_ready, hpr_scan, h_pend⟩ :=
          idleComplete_preserve opId hId (.update val) (.doneUpdate t) (by nofun) hrec_i
            (Or.inr ⟨val, snap, hpi⟩) (by rw [← hs₁])
            (by rw [← hs₁]; simp only [inv.stepCount_eq]) (fun _ _ _ => Or.inr trivial)
        refine ⟨by rw [← hs₁]; simp only [inv.stepCount_eq], ?_,
          hpr_ready, hpr_scan, h_pend, ?_, ?_, ?_⟩
        · intro j w hw hwrite
          rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw' | rfl
          · exact inv.reg_view_valid j w hw' hwrite
          · have hji : j = i := by
              obtain ⟨_, _, _, _, h1, _⟩ := hwrite
              rw [hev] at h1; injection h1 with hji'; exact hji'.symm
            subst hji
            have hview_eq : ((τ.stateAt (w + 1)).reg j).view = snap := by
              rw [← hs₁]; simp only [Function.update_self]
            rw [hview_eq]
            exact ⟨v_snap, hv₁, hv₂, hsnap_eq⟩
        · intro id hId' resp sn hdone
          have hId0 : id < (τ.stateAt t).history.length := by omega
          have hne_id : id ≠ opId := by
            intro heq; subst id
            have hnew := hhist_at opId hId' hId0
            simp only [↓reduceIte] at hnew
            rw [hnew] at hdone
            cases hdone
          have hrec_eq : (τ.stateAt (t + 1)).history[id]'hId' = (τ.stateAt t).history[id]'hId0 := by
            rw [hhist_at id hId' hId0, ite_eq_right_iff.mpr fun h => absurd h hne_id]
          rw [hrec_eq] at hdone ⊢
          obtain ⟨hk, hi, hr, v, hv⟩ := inv.hist_doneScan id hId0 resp sn hdone
          exact ⟨hk, hi, by omega, v, hv⟩
        · intro id hId' resp hdone
          have hId0 : id < (τ.stateAt t).history.length := by omega
          by_cases heq : id = opId
          · subst id
            have hrec_new := hhist_at opId hId' hId0
            simp only [↓reduceIte] at hrec_new
            rw [hrec_new] at hdone ⊢
            injection hdone with hresp
            subst resp
            refine ⟨val, rfl, hlt_t, Nat.lt_succ_self t,
              ⟨ht_lt, opId, val, snap, hev, hpi⟩, ?_⟩
            rw [← hs₁]; simp only [Function.update_self]
          · have hrec_eq : (τ.stateAt (t + 1)).history[id]'hId' =
                (τ.stateAt t).history[id]'hId0 := by
              rw [hhist_at id hId' hId0, ite_eq_right_iff.mpr fun h => absurd h heq]
            rw [hrec_eq] at hdone ⊢
            obtain ⟨val', hk, hi, hr, hw, hd⟩ := inv.hist_doneUpdate id hId0 resp hdone
            exact ⟨val', hk, hi, by omega, hw, hd⟩
        · intro j w hw hwrite
          rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw' | rfl
          · obtain ⟨id, hId0, hc, hs⟩ := inv.writeStep_in_hist j w hw' hwrite
            have hne_id : id ≠ opId := by
              intro heq; subst id; rw [hrec_i] at hs; cases hs
            refine ⟨id, by omega, ?_, ?_⟩ <;>
              rw [hhist_at id (by omega) hId0, ite_eq_right_iff.mpr fun h => absurd h hne_id]
            · exact hc
            · exact hs
          · have hji : j = i := by
              obtain ⟨_, _, _, _, h1, _⟩ := hwrite
              rw [hev] at h1; injection h1 with hji'; exact hji'.symm
            subst hji
            refine ⟨opId, by omega, ?_, ?_⟩ <;>
              simp only [hhist_at opId (by omega) hId, ↓reduceIte]
      | scanning st =>
        -- Subcase 3b: Step inside `scan_i`
        simp only [hpi] at hstep
        have hnow : ¬ ∃ j, τ.isWriteStep j t := by
          rintro ⟨j, _, _, _, _, h1, h2⟩
          rw [hev] at h1; injection h1 with hji; subst hji
          rw [hpi] at h2; cases h2
        obtain ⟨hId, hrec_i, hlt_t, iterS, hi₁, hi₂, hmov, hcA, hcB⟩ := inv.proc_scan i st hpi
        -- Shared helper when `i` transitions from `.scanning st` to a non-idle `ps_new` without
        -- modifying `reg` or `history`!
        have localActive_inv : ∀ (ps_new : ProcSnapshotState P Data),
            ps_new ≠ .idle →
            ({ (τ.stateAt t) with
                proc := Function.update (τ.stateAt t).proc i ps_new
                stepCount := (τ.stateAt t).stepCount + 1 } = τ.stateAt (t + 1)) →
            ((∃ s0, ps_new = .scanning s0 ∧ s0.opId = st.opId) ∨
              (∃ v0 sn0, ps_new = .readyToWrite st.opId v0 sn0)) →
            (∀ id' v' sn', ps_new = .readyToWrite id' v' sn' →
              ∃ (hId₁ : id' < (τ.stateAt (t + 1)).history.length),
                (τ.stateAt (t + 1)).history[id']'hId₁ =
                  ⟨i, .update v', τ.lastIdleStep i (t + 1), .pending⟩ ∧
                τ.lastIdleStep i (t + 1) < t + 1 ∧
                ∃ v, τ.lastIdleStep i (t + 1) + 1 ≤ v ∧ v ≤ t + 1 ∧
                  memSnapshot (τ.stateAt v).reg = sn') →
            (∀ st', ps_new = .scanning st' →
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
                      ∃ tA, iterS' ≤ tA ∧ tA ≤ t + 1 ∧
                        st'.collectAVal k = (τ.stateAt tA).reg k) ∧
                  (st'.phase = .collectB →
                    ∃ u, iterS' ≤ u ∧ u ≤ t + 1 ∧
                      (∀ k, ∃ tA, iterS' ≤ tA ∧ tA ≤ u ∧
                        st'.collectAVal k = (τ.stateAt tA).reg k) ∧
                      (∀ k, k ∉ st'.rem →
                        ∃ tB, u ≤ tB ∧ tB ≤ t + 1 ∧
                          st'.collectBVal k = (τ.stateAt tB).reg k))) →
            TraceInv τ (t + 1) := by
          intro ps_new hps_ne hs_eq hact_new hready_i hscan_i
          have hhist_eq : (τ.stateAt (t + 1)).history = (τ.stateAt t).history := by rw [← hs_eq]
          refine ⟨by rw [← hs_eq]; simp only [inv.stepCount_eq],
            reg_unchanged_valid hnow, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro p id' v' sn' hp
            by_cases hpi' : p = i
            · subst hpi'
              rw [← hs_eq] at hp; dsimp only at hp; rw [Function.update_self] at hp
              exact hready_i id' v' sn' hp
            · have hp_old : (τ.stateAt t).proc p = .readyToWrite id' v' sn' := by
                rw [← hs_eq] at hp; dsimp only at hp; rwa [Function.update_of_ne hpi'] at hp
              have hkeep := τ.lastIdleStep_keep p (by rw [hp_old]; nofun) (by rw [hp]; nofun)
              obtain ⟨hId', hrec', hlt', v, h1, h2, h3⟩ := inv.proc_ready p id' v' sn' hp_old
              have hId₁ : id' < (τ.stateAt (t + 1)).history.length := hhist_eq ▸ hId'
              refine ⟨hId₁, ?_, by omega, v, by omega, by omega, h3⟩
              rw [getElem_of_eq hhist_eq hId₁ hId', hkeep]; exact hrec'
          · intro p st' hp
            by_cases hpi' : p = i
            · subst hpi'
              rw [← hs_eq] at hp; dsimp only at hp; rw [Function.update_self] at hp
              exact hscan_i st' hp
            · have hp_old : (τ.stateAt t).proc p = .scanning st' := by
                rw [← hs_eq] at hp; dsimp only at hp; rwa [Function.update_of_ne hpi'] at hp
              have hkeep := τ.lastIdleStep_keep p (by rw [hp_old]; nofun) (by rw [hp]; nofun)
              obtain ⟨hId', hrec', hlt', iterS', h1, h2, hm', ha', hb'⟩ :=
                inv.proc_scan p st' hp_old
              have hId₁ : st'.opId < (τ.stateAt (t + 1)).history.length := hhist_eq ▸ hId'
              refine ⟨hId₁, ?_, by omega, iterS', by omega, by omega, ?_, ?_, ?_⟩
              · rw [getElem_of_eq hhist_eq hId₁ hId', hkeep]; exact hrec'
              · intro k hk; rw [hkeep]; exact hm' k hk
              · intro hA k hk
                obtain ⟨tA, a1, a2, a3⟩ := ha' hA k hk
                exact ⟨tA, a1, by omega, a3⟩
              · intro hB
                obtain ⟨u, u1, u2, ha, hb⟩ := hb' hB
                refine ⟨u, u1, by omega, ha, fun k hk => ?_⟩
                obtain ⟨tB, b1, b2, b3⟩ := hb k hk
                exact ⟨tB, b1, by omega, b3⟩
          · intro id hId' hpend
            have hId0 : id < (τ.stateAt t).history.length := hhist_eq ▸ hId'
            have hrec_eq := getElem_of_eq hhist_eq hId' hId0
            rw [hrec_eq] at hpend ⊢
            obtain ⟨hinv, hlt', hact_old⟩ := inv.hist_pending id hId0 hpend
            by_cases hci : ((τ.stateAt t).history[id]'hId0).caller = i
            · have hid_eq : id = st.opId := by
                have hact_i : (∃ s0, (τ.stateAt t).proc i = .scanning s0 ∧ s0.opId = st.opId) ∨
                    (∃ v0 sn0, (τ.stateAt t).proc i = .readyToWrite st.opId v0 sn0) :=
                  Or.inl ⟨st, hpi, rfl⟩
                rw [hci] at hact_old
                exact active_opId_unique hact_old hact_i
              subst id
              have hpi_new : (τ.stateAt (t + 1)).proc i = ps_new := by
                rw [← hs_eq]; exact Function.update_self _ _ _
              have hkeep := τ.lastIdleStep_keep i (by rw [hpi]; nofun) (hpi_new ▸ hps_ne)
              rw [hci] at hinv ⊢
              rw [hkeep, hpi_new]
              exact ⟨hinv, by omega, hact_new⟩
            · have hnot_old :
                  (τ.stateAt t).proc ((τ.stateAt t).history[id]'hId0).caller ≠ .idle := by
                rcases hact_old with ⟨_, hp, -⟩ | ⟨_, _, hp⟩ <;> rw [hp] <;> nofun
              have hproc_same :
                  (τ.stateAt (t + 1)).proc ((τ.stateAt t).history[id]'hId0).caller =
                  (τ.stateAt t).proc ((τ.stateAt t).history[id]'hId0).caller := by
                rw [← hs_eq]; exact Function.update_of_ne hci _ _
              have hkeep := τ.lastIdleStep_keep _ hnot_old (by rw [hproc_same]; exact hnot_old)
              rw [hkeep, hproc_same]
              exact ⟨hinv, by omega, hact_old⟩
          · intro id hId' resp sn hdone
            have hId0 : id < (τ.stateAt t).history.length := hhist_eq ▸ hId'
            have hrec_eq := getElem_of_eq hhist_eq hId' hId0
            rw [hrec_eq] at hdone ⊢
            obtain ⟨hk, hi, hr, v, hv⟩ := inv.hist_doneScan id hId0 resp sn hdone
            exact ⟨hk, hi, by omega, v, hv⟩
          · intro id hId' resp hdone
            have hId0 : id < (τ.stateAt t).history.length := hhist_eq ▸ hId'
            have hrec_eq := getElem_of_eq hhist_eq hId' hId0
            rw [hrec_eq] at hdone ⊢
            obtain ⟨val', hk, hi, hr, hw, hd⟩ := inv.hist_doneUpdate id hId0 resp hdone
            exact ⟨val', hk, hi, by omega, hw, hd⟩
          · intro j w hw hwrite
            rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw' | rfl
            · obtain ⟨id, hId0, hc, hs⟩ := inv.writeStep_in_hist j w hw' hwrite
              have hId₁ : id < (τ.stateAt (t + 1)).history.length := hhist_eq ▸ hId0
              refine ⟨id, hId₁, ?_, ?_⟩ <;> rw [getElem_of_eq hhist_eq hId₁ hId0]
              · exact hc
              · exact hs
            · exact absurd ⟨j, hwrite⟩ hnow
        -- Common helper when `finishScan` completes the scan with a valid interval snapshot `snap`!
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
              rw [← hfin]; simp only [Function.update_self]; nofun
            have hkeep := τ.lastIdleStep_keep i (by rw [hpi]; nofun) hnot1
            refine localActive_inv (.readyToWrite st.opId val snap) (by nofun) hfin
              (Or.inr ⟨val, snap, rfl⟩) ?_ (fun _ h => by cases h)
            intro id' v' sn' heq
            injection heq with h1 h2 h3
            subst h1 h2 h3
            have hId₁ : st.opId < (τ.stateAt (t + 1)).history.length := hhist_eq ▸ hId
            refine ⟨hId₁, ?_, by omega, v_snap, by omega, by omega, hsnap_eq⟩
            rw [getElem_of_eq hhist_eq hId₁ hId, hkeep]; exact hrec_i
          | external =>
            rw [hm] at hfin hrec_i
            unfold finishScan at hfin
            obtain ⟨hhist_len, hhist_at, hpr_ready, hpr_scan, h_pend⟩ :=
              idleComplete_preserve st.opId hId .scan (.doneScan t snap) (by nofun) hrec_i
                (Or.inl ⟨st, hpi, rfl⟩) (by rw [← hfin])
                (by rw [← hfin]; simp only [inv.stepCount_eq]) (fun _ _ _ => Or.inr trivial)
            refine ⟨by rw [← hfin]; simp only [inv.stepCount_eq],
              reg_unchanged_valid hnow, hpr_ready, hpr_scan, h_pend, ?_, ?_, ?_⟩
            · intro id hId' resp sn hdone
              have hId0 : id < (τ.stateAt t).history.length := by omega
              by_cases heq : id = st.opId
              · subst id
                have hrec_new := hhist_at st.opId hId' hId0
                simp only [↓reduceIte] at hrec_new
                rw [hrec_new] at hdone ⊢
                injection hdone with hresp hsn
                subst resp sn
                exact ⟨rfl, hlt_t, Nat.lt_succ_self t, v_snap, hv₁, hv₂, hsnap_eq⟩
              · have hrec_eq : (τ.stateAt (t + 1)).history[id]'hId' =
                    (τ.stateAt t).history[id]'hId0 := by
                  rw [hhist_at id hId' hId0, ite_eq_right_iff.mpr fun h => absurd h heq]
                rw [hrec_eq] at hdone ⊢
                obtain ⟨hk, hi, hr, v, hv⟩ := inv.hist_doneScan id hId0 resp sn hdone
                exact ⟨hk, hi, by omega, v, hv⟩
            · intro id hId' resp hdone
              have hId0 : id < (τ.stateAt t).history.length := by omega
              have hne_id : id ≠ st.opId := by
                intro heq; subst id
                have hnew := hhist_at st.opId hId' hId0
                simp only [↓reduceIte] at hnew
                rw [hnew] at hdone
                cases hdone
              have hrec_eq : (τ.stateAt (t + 1)).history[id]'hId' =
                  (τ.stateAt t).history[id]'hId0 := by
                rw [hhist_at id hId' hId0, ite_eq_right_iff.mpr fun h => absurd h hne_id]
              rw [hrec_eq] at hdone ⊢
              obtain ⟨val', hk, hi, hr, hw, hd⟩ := inv.hist_doneUpdate id hId0 resp hdone
              exact ⟨val', hk, hi, by omega, hw, hd⟩
            · intro j w hw hwrite
              rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw' | rfl
              · obtain ⟨id, hId0, hc, hs⟩ := inv.writeStep_in_hist j w hw' hwrite
                have hne_id : id ≠ st.opId := by
                  intro heq; subst id; rw [hrec_i] at hs; cases hs
                refine ⟨id, by omega, ?_, ?_⟩ <;>
                  rw [hhist_at id (by omega) hId0, ite_eq_right_iff.mpr fun h => absurd h hne_id]
                · exact hc
                · exact hs
              · exact absurd ⟨j, hwrite⟩ hnow
        -- Helper when `scan_i` stays in `.scanning st_next` without touching `reg` or `history`!
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
            rw [← hs_eq]; simp only [Function.update_self]; nofun
          have hkeep := τ.lastIdleStep_keep i (by rw [hpi]; nofun) hnot1
          refine localActive_inv (.scanning st_next) (by nofun) hs_eq
            (Or.inl ⟨st_next, rfl, hop_eq⟩) (fun _ _ _ h => by cases h) ?_
          intro st' heq
          injection heq with h1
          subst h1
          have hId₁ : st_next.opId < (τ.stateAt (t + 1)).history.length := by
            rw [hhist_eq, hop_eq]; exact hId
          refine ⟨hId₁, ?_, by omega, ?_⟩
          · rw [getElem_of_eq hhist_eq hId₁ (hop_eq ▸ hId),
              getElem_congr_idx _ hop_eq (hop_eq ▸ hId) hId, hkeep, hmode_eq]
            exact hrec_i
          · rw [hkeep]; exact hnext
        -- Now dispatch the 4 subcases of `(st.phase, st.rem)`!
        cases hph : st.phase with
        | collectA =>
          cases hrem : st.rem with
          | cons j rest =>
            simp only [hph, hrem] at hstep
            injection hstep with hs₁
            refine continueScan_inv
              { st with phase := .collectA, rem := rest,
                        collectAVal := Function.update st.collectAVal j ((τ.stateAt t).reg j) }
              rfl rfl hs₁ ⟨iterS, hi₁, by omega, hmov, ?_, ?_⟩
            · intro _ k hk
              dsimp only at hk ⊢
              by_cases hkj : k = j
              · subst hkj
                exact ⟨t, hi₂, by omega, Function.update_self _ _ _⟩
              · have hk_not : k ∉ j :: rest := by
                  simp only [List.mem_cons, not_or]; exact ⟨hkj, hk⟩
                obtain ⟨tA, a1, a2, a3⟩ := hcA hph k (hrem ▸ hk_not)
                exact ⟨tA, a1, by omega, (Function.update_of_ne hkj _ _).trans a3⟩
            · intro hB; cases hB
          | nil =>
            simp only [hph, hrem] at hstep
            injection hstep with hs₁
            refine continueScan_inv { st with phase := .collectB, rem := ord.elems }
              rfl rfl hs₁ ⟨iterS, hi₁, by omega, hmov, ?_, ?_⟩
            · intro hA; cases hA
            · intro _
              refine ⟨t, hi₂, by omega, ?_, ?_⟩
              · intro k
                exact hcA hph k (by simp only [hrem, List.not_mem_nil, not_false_eq_true])
              · intro k hk; exact absurd (ord.complete k) hk
        | collectB =>
          obtain ⟨u, hu₁, hu₂, ha_all, hb_rem⟩ := hcB hph
          cases hrem : st.rem with
          | cons j rest =>
            simp only [hph, hrem] at hstep
            injection hstep with hs₁
            refine continueScan_inv
              { st with phase := .collectB, rem := rest,
                        collectBVal := Function.update st.collectBVal j ((τ.stateAt t).reg j) }
              rfl rfl hs₁ ⟨iterS, hi₁, by omega, hmov, ?_, ?_⟩
            · intro hA; cases hA
            · intro _
              refine ⟨u, hu₁, by omega, ha_all, fun k hk => ?_⟩
              dsimp only at hk ⊢
              by_cases hkj : k = j
              · subst hkj
                exact ⟨t, hu₂, by omega, Function.update_self _ _ _⟩
              · have hk_not : k ∉ j :: rest := by
                  simp only [List.mem_cons, not_or]; exact ⟨hkj, hk⟩
                obtain ⟨tB, b1, b2, b3⟩ := hb_rem k (hrem ▸ hk_not)
                exact ⟨tB, b1, by omega, (Function.update_of_ne hkj _ _).trans b3⟩
          | nil =>
            simp only [hph, hrem] at hstep
            have hb_all : ∀ k, ∃ tB, u ≤ tB ∧ tB ≤ t ∧
                st.collectBVal k = (τ.stateAt tB).reg k := fun k =>
              hb_rem k (by simp only [hrem, List.not_mem_nil, not_false_eq_true])
            split_ifs at hstep with hclean
            · -- **Clean Double Collect (Lemma 3.1)!**
              injection hstep with hs₁
              choose tA htA₁ htA₂ htA_eq using ha_all
              choose tB htB₁ htB₂ htB_eq using hb_all
              have hseq_eq : ∀ k,
                  ((τ.stateAt (tA k)).reg k).seq = ((τ.stateAt (tB k)).reg k).seq := by
                intro k
                have := hclean k
                rwa [htA_eq k, htB_eq k] at this
              have hsnap_u : memSnapshot (τ.stateAt u).reg =
                  fun k => (st.collectBVal k).data := by
                have h31 := τ.memSnapshot_eq_of_clean_double_collect htA₂ le_rfl htB₁
                  (fun k => le_trans (htB₂ k) (Nat.le_of_succ_le ht)) hseq_eq le_rfl le_rfl
                rw [h31]
                funext k
                rw [htB_eq k]
              exact finishScan_inv _ ⟨u, le_trans hi₁ hu₁, hu₂, hsnap_u⟩ hs₁
            · -- Unsuccessful double collect: check if some `k` moved twice (`Lemma 3.2`)!
              cases hfind : (ord.elems.find? fun k =>
                  decide ((st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved)) with
              | some k =>
                simp only [hfind] at hstep
                injection hstep with hs₁
                have hk_bool := List.find?_some hfind
                have hk_pred : (st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved :=
                  of_decide_eq_true hk_bool
                obtain ⟨w₁, hw₁_lo, hw₁_hi, hw₁_write⟩ := hmov k hk_pred.2
                obtain ⟨tA, htA₁, htA₂, htA_eq⟩ := ha_all k
                obtain ⟨tB, htB₁, htB₂, htB_eq⟩ := hb_all k
                have hseq_ne : ((τ.stateAt tA).reg k).seq ≠ ((τ.stateAt tB).reg k).seq := by
                  have := hk_pred.1
                  rwa [htA_eq, htB_eq] at this
                obtain ⟨w₂, hw₂_lo, hw₂_hi, hw₂_write⟩ :=
                  τ.exists_writeStep_of_seq_ne k (le_trans htA₂ htB₁)
                    (le_trans htB₂ (Nat.le_of_succ_le ht)) hseq_ne
                -- Hence `(τ.stateAt tB).reg k` has `.seq > 0`!
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
                -- Note `w₂ ≤ w_star` (otherwise `hnow_after w₂` contradicts `hw₂_write`!)
                have hw₂_le_star : w₂ ≤ w_star := by
                  by_contra hlt_star
                  exact hnow_after w₂ (by omega) hw₂_hi hw₂_write
                -- At `w₁ + 1`, `proc k = .idle` because `isWriteStep τ k w₁`!
                have hidle_w₁ : (τ.stateAt (w₁ + 1)).proc k = .idle := by
                  rcases τ.reg_step_iff (t := w₁) k (by omega) with
                      ⟨-, hnw⟩ | ⟨_, _, _, -, -, -, hidle'⟩
                  · exact absurd hw₁_write hnw
                  · exact hidle'
                have hw₁_lt_star : w₁ + 1 ≤ w_star := by omega
                have hlast_ge : w₁ + 1 ≤ τ.lastIdleStep k w_star :=
                  τ.le_lastIdleStep_of_idle k hw₁_lt_star hidle_w₁
                obtain ⟨v_k, hv_k_lo, hv_k_hi, hv_k_snap⟩ :=
                  inv.reg_view_valid k w_star (by omega) hw_star_write
                have hview_eq :
                    (st.collectBVal k).view = ((τ.stateAt (w_star + 1)).reg k).view := by
                  rw [htB_eq, hw_star_reg]
                exact finishScan_inv _
                  ⟨v_k, by omega, by omega, hv_k_snap.trans hview_eq.symm⟩ hs₁
              | none =>
                simp only [hfind] at hstep
                injection hstep with hs₁
                let changed := univ.filter fun k =>
                  (st.collectAVal k).seq ≠ (st.collectBVal k).seq
                refine continueScan_inv
                  { st with moved := st.moved ∪ changed, phase := .collectA, rem := ord.elems }
                  rfl rfl hs₁ ⟨t + 1, by omega, le_rfl, ?_, ?_, ?_⟩
                · intro k hk
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
                · intro _ k hk; exact absurd (ord.complete k) hk
                · intro hB; cases hB

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
    intro id₁ _ h₁
    rw [SnapshotTrace.stateAt_zero] at h₁
    cases h₁
  | succ t ih =>
    have ht_lt : t < τ.events.length := Nat.lt_of_succ_le ht
    have inv := τ.traceInv_holds t (Nat.le_of_succ_le ht)
    have ih_t := ih (Nat.le_of_succ_le ht)
    have hstep := τ.stateAt_step ht_lt
    intro id₁ id₂ h₁ h₂ w hst₁ hst₂
    -- Helper when history appends one `.pending` record
    have append_pending_case : ∀ rec_new,
        rec_new.status = .pending →
        (τ.stateAt (t + 1)).history = (τ.stateAt t).history ++ [rec_new] →
        id₁ = id₂ := by
      intro rec_new hpend hhist
      have hlt₁ : id₁ < (τ.stateAt t).history.length := by
        by_contra hge
        have heq : id₁ = (τ.stateAt t).history.length := by
          rw [hhist, List.length_append, List.length_singleton] at h₁; omega
        subst heq
        simp only [hhist, List.getElem_append_right (le_refl _), Nat.sub_self,
          List.getElem_singleton] at hst₁
        rw [hpend] at hst₁; cases hst₁
      have hlt₂ : id₂ < (τ.stateAt t).history.length := by
        by_contra hge
        have heq : id₂ = (τ.stateAt t).history.length := by
          rw [hhist, List.length_append, List.length_singleton] at h₂; omega
        subst heq
        simp only [hhist, List.getElem_append_right (le_refl _), Nat.sub_self,
          List.getElem_singleton] at hst₂
        rw [hpend] at hst₂; cases hst₂
      simp only [hhist, List.getElem_append_left hlt₁] at hst₁
      simp only [hhist, List.getElem_append_left hlt₂] at hst₂
      exact ih_t id₁ id₂ hlt₁ hlt₂ w hst₁ hst₂
    rcases hev : τ.events[t] with i | ⟨i, val⟩ | i
    · rw [hev] at hstep
      obtain ⟨-, hs₁⟩ := stepSnapshot_invokeScan_eq hstep
      exact append_pending_case _ rfl (by rw [← hs₁])
    · rw [hev] at hstep
      obtain ⟨-, hs₁⟩ := stepSnapshot_invokeUpdate_eq hstep
      exact append_pending_case _ rfl (by rw [← hs₁])
    · rw [hev] at hstep; unfold stepSnapshot at hstep
      cases hpi : (τ.stateAt t).proc i with
      | idle => simp only [hpi] at hstep; nomatch hstep
      | readyToWrite opId val snap =>
        simp only [hpi] at hstep
        injection hstep with hs₁
        obtain ⟨hOp, hrec_i, -, -⟩ := inv.proc_ready i opId val snap hpi
        have hget_op : (τ.stateAt t).history[opId]? =
            some ⟨i, .update val, τ.lastIdleStep i t, .pending⟩ := by
          rw [List.getElem?_eq_getElem hOp, hrec_i]
        have hset : (τ.stateAt (t + 1)).history =
            (τ.stateAt t).history.set opId
              ⟨i, .update val, τ.lastIdleStep i t, .doneUpdate t⟩ := by
          rw [← hs₁]; simp only [completeHistoryAt, hget_op, inv.stepCount_eq]
        have hlen_eq : (τ.stateAt (t + 1)).history.length = (τ.stateAt t).history.length := by
          rw [hset, List.length_set]
        by_cases heq₁ : id₁ = opId <;> by_cases heq₂ : id₂ = opId
        · exact heq₁.trans heq₂.symm
        · subst id₁
          rw [SnapshotTrace.getElem_of_eq hset h₁ (by simp only [List.length_set]; exact hOp),
            List.getElem_set_self] at hst₁
          injection hst₁ with hw_eq; subst w
          rw [SnapshotTrace.getElem_of_eq hset h₂
            (by simp only [List.length_set]; exact hlen_eq ▸ h₂),
            List.getElem_set_ne (Ne.symm heq₂)] at hst₂
          obtain ⟨_, -, -, hwt, -⟩ := inv.hist_doneUpdate id₂ (hlen_eq ▸ h₂) t hst₂
          omega
        · subst id₂
          rw [SnapshotTrace.getElem_of_eq hset h₂ (by simp only [List.length_set]; exact hOp),
            List.getElem_set_self] at hst₂
          injection hst₂ with hw_eq; subst w
          rw [SnapshotTrace.getElem_of_eq hset h₁
            (by simp only [List.length_set]; exact hlen_eq ▸ h₁),
            List.getElem_set_ne (Ne.symm heq₁)] at hst₁
          obtain ⟨_, -, -, hwt, -⟩ := inv.hist_doneUpdate id₁ (hlen_eq ▸ h₁) t hst₁
          omega
        · rw [SnapshotTrace.getElem_of_eq hset h₁
            (by simp only [List.length_set]; exact hlen_eq ▸ h₁),
            List.getElem_set_ne (Ne.symm heq₁)] at hst₁
          rw [SnapshotTrace.getElem_of_eq hset h₂
            (by simp only [List.length_set]; exact hlen_eq ▸ h₂),
            List.getElem_set_ne (Ne.symm heq₂)] at hst₂
          exact ih_t id₁ id₂ (hlen_eq ▸ h₁) (hlen_eq ▸ h₂) w hst₁ hst₂
      | scanning st =>
        simp only [hpi] at hstep
        have finish_case : ∀ snap,
            finishScan (τ.stateAt t) i st.mode st.opId snap = τ.stateAt (t + 1) → id₁ = id₂ := by
          intro snap hfin
          unfold finishScan at hfin
          cases hm : st.mode
          · -- `.external`: sets `st.opId` to `.doneScan`, not `.doneUpdate`
            rw [hm] at hfin
            have hlen_eq : (τ.stateAt (t + 1)).history.length = (τ.stateAt t).history.length := by
              rw [← hfin]; exact length_completeHistoryAt _ _ _
            obtain ⟨hOp, hrec_i, -, -⟩ := inv.proc_scan i st hpi
            rw [hm] at hrec_i
            have hget_op : (τ.stateAt t).history[st.opId]? =
                some ⟨i, .scan, τ.lastIdleStep i t, .pending⟩ := by
              rw [List.getElem?_eq_getElem hOp, hrec_i]
            have hset : (τ.stateAt (t + 1)).history =
                (τ.stateAt t).history.set st.opId
                  ⟨i, .scan, τ.lastIdleStep i t, .doneScan t snap⟩ := by
              rw [← hfin]; simp only [completeHistoryAt, hget_op, inv.stepCount_eq]
            have hne₁ : id₁ ≠ st.opId := by
              intro heq; subst id₁
              rw [SnapshotTrace.getElem_of_eq hset h₁ (by simp only [List.length_set]; exact hOp),
                List.getElem_set_self] at hst₁
              cases hst₁
            have hne₂ : id₂ ≠ st.opId := by
              intro heq; subst id₂
              rw [SnapshotTrace.getElem_of_eq hset h₂ (by simp only [List.length_set]; exact hOp),
                List.getElem_set_self] at hst₂
              cases hst₂
            rw [SnapshotTrace.getElem_of_eq hset h₁
              (by simp only [List.length_set]; exact hlen_eq ▸ h₁),
              List.getElem_set_ne (Ne.symm hne₁)] at hst₁
            rw [SnapshotTrace.getElem_of_eq hset h₂
              (by simp only [List.length_set]; exact hlen_eq ▸ h₂),
              List.getElem_set_ne (Ne.symm hne₂)] at hst₂
            exact ih_t id₁ id₂ (hlen_eq ▸ h₁) (hlen_eq ▸ h₂) w hst₁ hst₂
          · -- `.embedded`: history unchanged
            rw [hm] at hfin
            have hhist : (τ.stateAt (t + 1)).history = (τ.stateAt t).history := by rw [← hfin]
            exact ih_t id₁ id₂ (hhist ▸ h₁) (hhist ▸ h₂) w
              (by rwa [SnapshotTrace.getElem_of_eq hhist h₁ (hhist ▸ h₁)] at hst₁)
              (by rwa [SnapshotTrace.getElem_of_eq hhist h₂ (hhist ▸ h₂)] at hst₂)
        cases hph : st.phase <;> cases hrem : st.rem <;> simp only [hph, hrem] at hstep
        · injection hstep with hs₁
          have hhist : (τ.stateAt (t + 1)).history = (τ.stateAt t).history := by rw [← hs₁]
          exact ih_t id₁ id₂ (hhist ▸ h₁) (hhist ▸ h₂) w
            (by rwa [SnapshotTrace.getElem_of_eq hhist h₁ (hhist ▸ h₁)] at hst₁)
            (by rwa [SnapshotTrace.getElem_of_eq hhist h₂ (hhist ▸ h₂)] at hst₂)
        · injection hstep with hs₁
          have hhist : (τ.stateAt (t + 1)).history = (τ.stateAt t).history := by rw [← hs₁]
          exact ih_t id₁ id₂ (hhist ▸ h₁) (hhist ▸ h₂) w
            (by rwa [SnapshotTrace.getElem_of_eq hhist h₁ (hhist ▸ h₁)] at hst₁)
            (by rwa [SnapshotTrace.getElem_of_eq hhist h₂ (hhist ▸ h₂)] at hst₂)
        · split_ifs at hstep with hclean
          · injection hstep with hs₁; exact finish_case _ hs₁
          · cases hfind : (ord.elems.find? fun k =>
                decide ((st.collectAVal k).seq ≠ (st.collectBVal k).seq ∧ k ∈ st.moved)) <;>
              simp only [hfind] at hstep
            · injection hstep with hs₁
              have hhist : (τ.stateAt (t + 1)).history = (τ.stateAt t).history := by rw [← hs₁]
              exact ih_t id₁ id₂ (hhist ▸ h₁) (hhist ▸ h₂) w
                (by rwa [SnapshotTrace.getElem_of_eq hhist h₁ (hhist ▸ h₁)] at hst₁)
                (by rwa [SnapshotTrace.getElem_of_eq hhist h₂ (hhist ▸ h₂)] at hst₂)
            · injection hstep with hs₁; exact finish_case _ hs₁
        · injection hstep with hs₁
          have hhist : (τ.stateAt (t + 1)).history = (τ.stateAt t).history := by rw [← hs₁]
          exact ih_t id₁ id₂ (hhist ▸ h₁) (hhist ▸ h₂) w
            (by rwa [SnapshotTrace.getElem_of_eq hhist h₁ (hhist ▸ h₁)] at hst₁)
            (by rwa [SnapshotTrace.getElem_of_eq hhist h₂ (hhist ▸ h₂)] at hst₂)

/-- Internal trace-level proof of `unbounded_snapshotLinearizable_of_reachable`. -/
private theorem snapshotLinearizable_of_trace {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} (τ : SnapshotTrace ord dInit) :
    SnapshotLinearizable dInit (τ.stateAt τ.events.length).history := by
  classical
  set T := τ.events.length
  have inv := τ.traceInv_holds T le_rfl
  have hinj := doneUpdate_inj_of_trace τ T le_rfl
  -- Assign each completed operation `id < history.length` its trace block `blockOf id ≤ T`:
  -- - completed scan: chosen serialization state `v` (`invStep + 1 ≤ v ≤ resp`)
  -- - completed update: write step `w = resp` (`invStep < w < T`)
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
    dsimp only [scanPoint]
    simp only [hex, ↓reduceDIte]
    exact Classical.choose_spec hex
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
  -- Properties of `scansAt t` and `updatesAt t`
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
      apply this (scansAt t)
      intro id hid
      dsimp only [scansAt] at hid
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hid
      obtain ⟨hId, hblk, r, sn, hmap⟩ := hid
      have hget : (τ.stateAt T).history[id]? = some ((τ.stateAt T).history[id]'hId) :=
        List.getElem?_eq_getElem hId
      rw [hget, Option.map_some, Option.some.injEq] at hmap
      dsimp only [blockOf] at hblk
      simp only [hget, hmap, Option.some.injEq] at hblk
      have hscan := inv.hist_doneScan id hId r sn hmap
      have hv_spec := scanPoint_spec hscan.2.2.2
      rw [hblk] at hv_spec
      exact ⟨hId, r, sn, hscan.1, hmap, hv_spec.2.2.symm⟩
    intro xs hpred
    induction xs with
    | nil => exact ⟨rfl, trivial⟩
    | cons id rest ih_s =>
      obtain ⟨hId, resp, snap, hkind, hstat, hsnap⟩ := hpred id List.mem_cons_self
      obtain ⟨hm_rest, hv_rest⟩ := ih_s fun x hx => hpred x (List.mem_cons_of_mem id hx)
      have hget : (τ.stateAt T).history[id]? = some ((τ.stateAt T).history[id]'hId) :=
        List.getElem?_eq_getElem hId
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
      have hget₀ : (τ.stateAt T).history[id₀]? = some ((τ.stateAt T).history[id₀]'hId₀) :=
        List.getElem?_eq_getElem hId₀
      have hupd_eq : updatesAt t = [id₀] := by
        have hmem_iff : ∀ x, x ∈ updatesAt t ↔ x = id₀ := by
          intro x
          dsimp only [updatesAt]
          simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
          constructor
          · rintro ⟨hx, hblk, w, hmap⟩
            have hgetx : (τ.stateAt T).history[x]? = some ((τ.stateAt T).history[x]'hx) :=
              List.getElem?_eq_getElem hx
            rw [hgetx, Option.map_some, Option.some.injEq] at hmap
            dsimp only [blockOf] at hblk
            simp only [hgetx, hmap, Option.some.injEq] at hblk
            subst w
            exact hinj x id₀ hx hId₀ t hmap hstat₀
          · rintro rfl
            refine ⟨hId₀, ?_, t, ?_⟩
            · dsimp only [blockOf]; simp only [hget₀, hstat₀]
            · rw [hget₀, Option.map_some, hstat₀]
        have hnd : (updatesAt t).Nodup := (List.nodup_range).filter _
        cases hlist : updatesAt t with
        | nil =>
          have := (hmem_iff id₀).mpr rfl
          rw [hlist] at this; cases this
        | cons a tl =>
          have ha : a = id₀ := (hmem_iff a).mp (hlist ▸ List.mem_cons_self)
          subst ha
          cases tl with
          | nil => rfl
          | cons b _ =>
            have hb : b = a := (hmem_iff b).mp
              (hlist ▸ List.mem_cons_of_mem a List.mem_cons_self)
            subst hb
            rw [hlist, List.nodup_cons] at hnd
            exact absurd List.mem_cons_self hnd.1
      rw [hupd_eq]
      obtain ⟨val, hkind₀, -, -, -, hreg₀⟩ := inv.hist_doneUpdate id₀ hId₀ t hstat₀
      refine ⟨?_, ?_⟩
      · simp only [seqSnapshotMemAfter, hget₀, hkind₀, hcaller₀]
        funext p
        by_cases hpj : p = j
        · subst hpj
          have hreg_j := hcaller₀ ▸ hreg₀
          rw [Function.update_self, memSnapshot, hreg_j]
        · rw [Function.update_of_ne hpj, memSnapshot]
          rcases τ.reg_step_iff p ht_lt with ⟨hreg_eq, -⟩ | ⟨_, _, _, hev_p, -, -, -⟩
          · exact (congrArg SnapshotReg.data hreg_eq).symm
          · obtain ⟨_, _, _, _, hev_j, -⟩ := hjw
            rw [hev_p] at hev_j; injection hev_j with hpj'
            exact absurd hpj' hpj
      · simp only [seqSnapshotValid, hget₀, hkind₀, hstat₀]
    · have hupd_nil : updatesAt t = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro x hx
        dsimp only [updatesAt] at hx
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
        obtain ⟨hx_lt, hblk, w, hmap⟩ := hx
        have hgetx : (τ.stateAt T).history[x]? = some ((τ.stateAt T).history[x]'hx_lt) :=
          List.getElem?_eq_getElem hx_lt
        rw [hgetx, Option.map_some, Option.some.injEq] at hmap
        dsimp only [blockOf] at hblk
        simp only [hgetx, hmap, Option.some.injEq] at hblk
        subst w
        obtain ⟨_, -, -, -, hw_x, -⟩ := inv.hist_doneUpdate x hx_lt t hmap
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
    dsimp only [updatesAt] at hx
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
    obtain ⟨hx_lt, hblk, w, hmap⟩ := hx
    have hgetx : (τ.stateAt T).history[x]? = some ((τ.stateAt T).history[x]'hx_lt) :=
      List.getElem?_eq_getElem hx_lt
    rw [hgetx, Option.map_some, Option.some.injEq] at hmap
    dsimp only [blockOf] at hblk
    simp only [hgetx, hmap, Option.some.injEq] at hblk
    subst w
    obtain ⟨_, -, -, hw_lt, -⟩ := inv.hist_doneUpdate x hx_lt T hmap
    omega
  -- Inductive validity over `prefixSeq k` for `k ≤ T + 1`
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
      have hm_at_k := hm_k hk_le_T
      have hflat : prefixSeq (k + 1) = prefixSeq k ++ scansAt k ++ updatesAt k := by
        dsimp only [prefixSeq, chunk]
        simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.append_assoc]
      obtain ⟨hm_sc, hv_sc⟩ := scansAt_valid k hk_le_T
      simp only [hflat, seqSnapshotValid_append, seqSnapshotMemAfter_append, hm_at_k, hm_sc]
      rcases Nat.lt_or_eq_of_le hk_le_T with hk_lt | rfl
      · obtain ⟨hm_up, hv_up⟩ := updatesAt_valid k hk_lt
        exact ⟨⟨⟨hv_k, hv_sc⟩, hv_up⟩, fun _ => hm_up⟩
      · rw [updatesAt_T]
        exact ⟨⟨⟨hv_k, hv_sc⟩, trivial⟩, fun h => absurd h (by omega)⟩
  -- Witness `seq := prefixSeq (T + 1)`!
  refine ⟨prefixSeq (T + 1), ?_, ?_, ?_, ?_, (prefix_valid (T + 1) le_rfl).1⟩
  · -- 1. `Nodup` of `prefixSeq (T + 1)`
    have hchunk_nd : ∀ t, (chunk t).Nodup := by
      intro t
      dsimp only [chunk]
      rw [List.nodup_append]
      refine ⟨(List.nodup_range).filter _, (List.nodup_range).filter _, fun a ha b hb hab => ?_⟩
      subst hab
      dsimp only [scansAt, updatesAt] at ha hb
      simp only [List.mem_filter, decide_eq_true_eq] at ha hb
      obtain ⟨r, sn, h1⟩ := ha.2.2
      obtain ⟨w, h2⟩ := hb.2.2
      have hcon := Option.some.inj (h1.symm.trans h2)
      nomatch hcon
    have hchunk_blk : ∀ t x, x ∈ chunk t → blockOf x = some t := by
      intro t x hx
      rcases List.mem_append.mp hx with hx | hx <;>
        dsimp only [scansAt, updatesAt] at hx <;>
        simp only [List.mem_filter, decide_eq_true_eq] at hx <;>
        exact hx.2.1
    dsimp only [prefixSeq]
    rw [List.nodup_flatMap]
    refine ⟨fun t _ => hchunk_nd t, ?_⟩
    refine List.Pairwise.imp (fun {t₁ t₂} hne x hx₁ hx₂ => ?_) (List.nodup_range)
    have hb₁ := hchunk_blk t₁ x hx₁
    have hb₂ := hchunk_blk t₂ x hx₂
    rw [hb₁] at hb₂; injection hb₂ with heq
    exact hne heq
  · -- 2. `index_lt`: every `i ∈ prefixSeq (T + 1)` satisfies `i < history.length`
    intro x hx
    dsimp only [prefixSeq] at hx
    simp only [List.mem_flatMap, List.mem_range] at hx
    obtain ⟨t, -, hxt⟩ := hx
    rcases List.mem_append.mp hxt with hxt | hxt <;>
      dsimp only [scansAt, updatesAt] at hxt <;>
      simp only [List.mem_filter, List.mem_range] at hxt <;>
      exact hxt.1
  · -- 3. `complete`: every completed operation `i < history.length` belongs to `prefixSeq (T + 1)`
    intro id hId hcomp
    have hget : (τ.stateAt T).history[id]? = some ((τ.stateAt T).history[id]'hId) :=
      List.getElem?_eq_getElem hId
    dsimp only [prefixSeq]
    simp only [List.mem_flatMap, List.mem_range]
    cases hst : ((τ.stateAt T).history[id]'hId).status with
    | pending =>
      simp only [SnapshotOpRecord.isCompleted, hst, Bool.false_eq_true] at hcomp
    | doneUpdate w =>
      obtain ⟨_, -, -, hw_lt, -⟩ := inv.hist_doneUpdate id hId w hst
      refine ⟨w, by omega, List.mem_append_right _ ?_⟩
      dsimp only [updatesAt]
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      refine ⟨hId, ?_, w, ?_⟩
      · dsimp only [blockOf]; simp only [hget, hst]
      · rw [hget, Option.map_some, hst]
    | doneScan resp snap =>
      have hsc := inv.hist_doneScan id hId resp snap hst
      have hv_spec := scanPoint_spec hsc.2.2.2
      refine ⟨scanPoint ((τ.stateAt T).history[id]'hId).invStep resp snap,
        by have := hsc.2.2.1; omega, List.mem_append_left _ ?_⟩
      dsimp only [scansAt]
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      refine ⟨hId, ?_, resp, snap, ?_⟩
      · dsimp only [blockOf]; simp only [hget, hst]
      · rw [hget, Option.map_some, hst]
  · -- 4. `realTime`: `respStep i ≤ invStep j` implies `blockOf i < blockOf j`
    intro i hi j hj r hresp_i recJ hget_j hr_le
    have hchunk_blk : ∀ t x, x ∈ chunk t → blockOf x = some t := by
      intro t x hx
      rcases List.mem_append.mp hx with hx | hx <;>
        dsimp only [scansAt, updatesAt] at hx <;>
        simp only [List.mem_filter, decide_eq_true_eq] at hx <;>
        exact hx.2.1
    obtain ⟨t₁, ht₁_lt, hi_chunk⟩ : ∃ t₁ < T + 1, i ∈ chunk t₁ := by
      dsimp only [prefixSeq] at hi
      simpa only [List.mem_flatMap, List.mem_range] using hi
    obtain ⟨t₂, ht₂_lt, hj_chunk⟩ : ∃ t₂ < T + 1, j ∈ chunk t₂ := by
      dsimp only [prefixSeq] at hj
      simpa only [List.mem_flatMap, List.mem_range] using hj
    have hb₁ := hchunk_blk t₁ i hi_chunk
    have hb₂ := hchunk_blk t₂ j hj_chunk
    -- Show `t₁ ≤ r`!
    have ht₁_le_r : t₁ ≤ r := by
      by_cases hId_i : i < (τ.stateAt T).history.length
      · have hget_i : (τ.stateAt T).history[i]? = some ((τ.stateAt T).history[i]'hId_i) :=
          List.getElem?_eq_getElem hId_i
        rw [hget_i, Option.bind_some] at hresp_i
        dsimp only [blockOf] at hb₁
        simp only [hget_i] at hb₁
        cases hst_i : ((τ.stateAt T).history[i]'hId_i).status with
        | pending =>
          simp only [hst_i] at hb₁; nomatch hb₁
        | doneScan resp snap =>
          simp only [hst_i, SnapshotOpRecord.respStep?] at hb₁ hresp_i
          injection hb₁ with ht₁_eq; injection hresp_i with hr_eq
          have hv_spec := scanPoint_spec (inv.hist_doneScan i hId_i resp snap hst_i).2.2.2
          omega
        | doneUpdate w =>
          simp only [hst_i, SnapshotOpRecord.respStep?] at hb₁ hresp_i
          injection hb₁ with ht₁_eq; injection hresp_i with hr_eq
          omega
      · have hget_i : (τ.stateAt T).history[i]? = none :=
          List.getElem?_eq_none (Nat.le_of_not_lt hId_i)
        dsimp only [blockOf] at hb₁
        simp only [hget_i] at hb₁
        nomatch hb₁
    -- Show `recJ.invStep + 1 ≤ t₂`!
    have hinv_lt_t₂ : recJ.invStep + 1 ≤ t₂ := by
      have ⟨hId_j, hrecJ_eq⟩ := List.getElem?_eq_some_iff.mp hget_j
      dsimp only [blockOf] at hb₂
      simp only [hget_j] at hb₂
      rw [← hrecJ_eq] at hb₂
      cases hst_j : ((τ.stateAt T).history[j]'hId_j).status with
      | pending =>
        simp only [hst_j] at hb₂; nomatch hb₂
      | doneScan resp snap =>
        simp only [hst_j] at hb₂
        injection hb₂ with ht₂_eq
        have hv_spec := scanPoint_spec (inv.hist_doneScan j hId_j resp snap hst_j).2.2.2
        rw [← hrecJ_eq]
        omega
      | doneUpdate w =>
        simp only [hst_j] at hb₂
        injection hb₂ with ht₂_eq
        obtain ⟨_, -, hinv_lt, -⟩ := inv.hist_doneUpdate j hId_j w hst_j
        rw [← hrecJ_eq]
        omega
    have ht₁_lt_t₂ : t₁ < t₂ := by omega
    -- Split `List.range (T + 1)` at `t₂`: `i` lies in `(List.range t₂).flatMap chunk`, while `j` is
    -- NOT in `(List.range t₂).flatMap chunk`!
    have hsplit_range : List.range (T + 1) = List.range t₂ ++ (List.range (T + 1)).drop t₂ :=
      (List.take_append_drop t₂ (List.range (T + 1))).symm.trans
        (by rw [List.take_range, Nat.min_eq_left (by omega)])
    have hseq_split : prefixSeq (T + 1) =
        (List.range t₂).flatMap chunk ++ ((List.range (T + 1)).drop t₂).flatMap chunk := by
      dsimp only [prefixSeq]
      conv_lhs => rw [hsplit_range]
      exact List.flatMap_append
    have hi_left : i ∈ (List.range t₂).flatMap chunk :=
      List.mem_flatMap.mpr ⟨t₁, List.mem_range.mpr ht₁_lt_t₂, hi_chunk⟩
    have hj_not_left : j ∉ (List.range t₂).flatMap chunk := by
      intro hj_in
      obtain ⟨t', ht'_lt, hj_t'⟩ := List.mem_flatMap.mp hj_in
      have hb' := hchunk_blk t' j hj_t'
      rw [hb₂] at hb'; injection hb' with heq
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
