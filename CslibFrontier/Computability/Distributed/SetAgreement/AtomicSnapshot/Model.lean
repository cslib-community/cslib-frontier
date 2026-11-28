/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

/-!
# Snapshot registers, scan orders, histories, and linearizability

Defines single-writer multi-reader registers (`SnapshotReg`), collect scan orders (`ScanOrder`),
client history records (`SnapshotOpKind`, `SnapshotOpStatus`, `SnapshotOpRecord`), and
Herlihy–Wing linearizability (`IsSnapshotLinearization`, `SnapshotLinearizable`) against the
canonical sequential snapshot specification (`seqSnapshotValid`,
[AfekAttiyaDolevGafniMerrittShavit1993], §2.1, Figure 1, Definition 1).

## Main definitions

* `Cslib.Distributed.SetAgreement.SnapshotReg`, `Cslib.Distributed.SetAgreement.memSnapshot`,
  `Cslib.Distributed.SetAgreement.ScanOrder`, `Cslib.Distributed.SetAgreement.ScanOrder.fin`:
  single-writer registers and duplicate-free collect orders.
* `Cslib.Distributed.SetAgreement.SnapshotOpKind`,
  `Cslib.Distributed.SetAgreement.SnapshotOpStatus`,
  `Cslib.Distributed.SetAgreement.SnapshotOpRecord`: execution history records.
* `Cslib.Distributed.SetAgreement.seqSnapshotValid`,
  `Cslib.Distributed.SetAgreement.seqSnapshotMemAfter`,
  `Cslib.Distributed.SetAgreement.IsSnapshotLinearization`,
  `Cslib.Distributed.SetAgreement.SnapshotLinearizable`: sequential snapshot validity and
  Herlihy–Wing linearizability.

## Main results

* `Cslib.Distributed.SetAgreement.ScanOrder.length_eq_card`: scan-order length equals `|P|`.
* `Cslib.Distributed.SetAgreement.seqSnapshotValid_append`: sequential replay across append.
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
  rw [← List.toFinset_card_of_nodup ord.nodup,
    eq_univ_iff_forall.mpr fun j => List.mem_toFinset.mpr (ord.complete j), card_univ]

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
  | nil => simp [seqSnapshotValid, seqSnapshotMemAfter]
  | cons idx xs ih =>
    simp only [List.cons_append, seqSnapshotValid, seqSnapshotMemAfter]
    rcases hist[idx]? with _ | ⟨caller, _ | val, _, _ | ⟨t, snap⟩ | t⟩ <;> simp [ih, and_assoc]

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

end Cslib.Distributed.SetAgreement
