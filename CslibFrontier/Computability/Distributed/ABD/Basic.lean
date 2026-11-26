/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.Filter

/-!
# Asynchronous crash-fault message passing and linearizable atomic register specification

This module models deterministic asynchronous point-to-point message passing with crash faults and
client `read` / `write` invocations, together with the linearizability (atomicity) and wait-free
termination specifications for emulating a shared multi-writer multi-reader atomic register
([AttiyaBarNoyDolev1995]; [LynchShvartsman1997]).

Following `Cslib.FLP`, processes in a finite set `P` communicate over an unordered multiset of
in-flight point-to-point envelopes (`Envelope P M`), and crash faults are modeled through the
fairness condition (`Protocol.Fair F`): every envelope addressed to a non-faulty process `dest ∉ F`
is eventually delivered, while faulty processes `p ∈ F` may stop receiving messages or taking steps
at any point in an execution (including initially or mid-broadcast). Unlike the per-edge ping-pong
channels and message/time accounting of [AttiyaBarNoyDolev1995] (§§2.1, 3–4) or the conditional
delay bounds of [LynchShvartsman1997] (§4.3), `Protocol` tracks pure asynchronous reachability and
eventual delivery outside `F`.

Each idle process `p : P` may invoke `OpKind.read` or `OpKind.write v` via `Action.invoke p kind`.
Every invocation appends an `OpRecord P V` to the global execution `history` recording its caller,
operation kind, invocation step `invStep`, and completion status (`pending`,
`doneRead respStep val`, or `doneWrite respStep`). An execution history `hist` is *linearizable*
(`Linearizable v₀ hist`) if there exists a duplicate-free sequence `seq : List ℕ` of operation
indices containing every completed operation and optionally a subset of pending writes such that:

* `seq` respects the real-time precedence order `prec hist` (`op₁` completed strictly before `op₂`
  was invoked implies `op₁` precedes `op₂` in `seq`), and
* executing `seq` sequentially from initial register value `v₀` obeys atomic read/write semantics
  (`seqValid`, equivalently `seqValid_iff_registerValAfter`: every completed `read` returns the
  value written by the immediately preceding `write` in `seq`, or `v₀` if none precedes it).

When `Fintype.card P ≤ 1`, a single process needs no network coordination: `localRegisterProtocol`
executes `read` and `write` locally in zero messages and satisfies `ImplementsAtomicRegister v₀ t`
for every fault bound `t`.

### Relationship to `Cslib.DistributedConsistency`

Upstream `Cslib.DistributedConsistency` (`AbstractExecution.Linearizability`, following Burckhardt
2014) axiomatizes consistency guarantees over abstract event sets equipped with declarative
visibility (`vis`) and arbitration (`ar`) relations on a `ReplicatedDataType`. Here `Linearizable`
instead formalizes Herlihy–Wing shared-register linearizability directly on finite operational LTS
histories `List (OpRecord P V)`, handling incomplete execution prefixes via subsets of pending
writes and providing a kernel-reducible `Decidable` instance (`instDecidableLinearizable`) for
concrete protocol traces.

## Main definitions

* `Cslib.Distributed.ABD.Envelope`: point-to-point message envelope carrying `src`, `dest`, `body`.
* `Cslib.Distributed.ABD.OpKind`, `Cslib.Distributed.ABD.OpResp`,
  `Cslib.Distributed.ABD.OpStatus`, `Cslib.Distributed.ABD.OpRecord`: client register invocations,
  responses, and recorded history entries.
* `Cslib.Distributed.ABD.prec`: real-time strict precedence on `OpRecord` indices (`respStep <
  invStep`).
* `Cslib.Distributed.ABD.seqValid`, `Cslib.Distributed.ABD.registerValAfter`,
  `Cslib.Distributed.ABD.IsLinearization`, `Cslib.Distributed.ABD.Linearizable`: sequential
  register semantics and Herlihy–Wing linearizability of an execution history.
* `Cslib.Distributed.ABD.StepOut`, `Cslib.Distributed.ABD.PendingOp`,
  `Cslib.Distributed.ABD.ProcState`, `Cslib.Distributed.ABD.State`,
  `Cslib.Distributed.ABD.Action`, `Cslib.Distributed.ABD.Protocol`: asynchronous register-emulation
  protocol and its labelled transition system `Protocol.lts`.
* `Cslib.Distributed.ABD.Protocol.Fair`, `Cslib.Distributed.ABD.Protocol.AdmissibleRun`: fair
  delivery to non-faulty processes `∉ F` and admissible infinite executions.
* `Cslib.Distributed.ABD.Protocol.ImplementsAtomicRegister`: safety (`linearizable`) and wait-free
  liveness (`terminates`) against up to `t` crash faults.
* `Cslib.Distributed.ABD.localRegisterProtocol`: zero-message local register protocol for at most
  one process.

## Main results

* `Cslib.Distributed.ABD.prec_irrefl`, `Cslib.Distributed.ABD.prec_trans`: real-time precedence is
  irreflexive and transitive on well-timed histories.
* `Cslib.Distributed.ABD.seqValid_iff_registerValAfter`: `seqValid` holds iff every entry in `seq`
  is a completed read or (completed or pending) write and every completed read returns
  `registerValAfter v₀ hist (seq.take k)`.
* `Cslib.Distributed.ABD.instDecidableLinearizable`: computable `Decidable` instance for
  `Linearizable v₀ hist` when `[DecidableEq V]`.
* `Cslib.Distributed.ABD.deliverHistory_entry_preserves`,
  `Cslib.Distributed.ABD.Protocol.mTr_history_entry_preserves`: transitions preserve `caller`,
  `kind`, and `invStep` of existing history records.
* `Cslib.Distributed.ABD.Protocol.exists_fair_omegaExecution`,
  `Cslib.Distributed.ABD.Protocol.Reachable.exists_admissibleRun`: every state extends via a
  delivery-only fair suffix to an infinite execution.
* `Cslib.Distributed.ABD.Protocol.linearizable_iff_admissible`: reachable-state linearizability is
  equivalent to prefix linearizability along all `t`-fault admissible runs.
* `Cslib.Distributed.ABD.implementsAtomicRegister_local_of_card_le_one`: `localRegisterProtocol`
  implements a wait-free linearizable register for every `t` when `Fintype.card P ≤ 1`.

## References

* [H. Attiya, A. Bar-Noy, D. Dolev, *Sharing memory robustly in message-passing
  systems*][AttiyaBarNoyDolev1995]
* [N. A. Lynch, A. A. Shvartsman, *Robust emulation of shared memory using dynamic
  quorum-acknowledged broadcasts*][LynchShvartsman1997]
-/

public section

namespace Cslib.Distributed.ABD

open Cslib Cslib.ωSequence

/-! ### Envelopes and broadcast helper -/

/-- A point-to-point message envelope in transit from `src` to `dest` carrying payload `body`. -/
@[ext]
structure Envelope (P M : Type*) where
  /-- Sender process identity. -/
  src : P
  /-- Destination process identity. -/
  dest : P
  /-- Message payload. -/
  body : M
  deriving @[expose] DecidableEq

/-- Tag a `(dest, body)` pair emitted by `src` as an `Envelope`. -/
@[expose] def tagSender {P M : Type*} (src : P) : P × M → Envelope P M
  | (dest, body) => ⟨src, dest, body⟩

@[simp]
theorem tagSender_src {P M : Type*} (src : P) (pm : P × M) :
    (tagSender src pm).src = src := rfl

@[simp]
theorem tagSender_dest {P M : Type*} (src : P) (pm : P × M) :
    (tagSender src pm).dest = pm.1 := rfl

@[simp]
theorem tagSender_body {P M : Type*} (src : P) (pm : P × M) :
    (tagSender src pm).body = pm.2 := rfl

/-- Broadcast payload `m` to every process `q : P` (including the sender itself). -/
@[expose] def broadcastAll (P : Type*) {M : Type*} [Fintype P] (m : M) : Multiset (P × M) :=
  Finset.univ.val.map fun q => (q, m)

@[simp]
theorem card_broadcastAll {P M : Type*} [Fintype P] (m : M) :
    (broadcastAll P m).card = Fintype.card P := by
  simp [broadcastAll]

/-- Broadcasting `m` from `src` sends an envelope `⟨src, q, m⟩` to every recipient `q : P`. -/
theorem mem_broadcastAll_tag {P M : Type*} [Fintype P] (src q : P) (m : M) :
    ⟨src, q, m⟩ ∈ (broadcastAll P m).map (tagSender src) :=
  Multiset.mem_map.mpr ⟨(q, m), Multiset.mem_map.mpr ⟨q, Finset.mem_univ q, rfl⟩, rfl⟩

/-! ### Client operations, execution histories, and linearizability -/

/-- Client operation invoked on an emulated shared register. -/
inductive OpKind (V : Type*) where
  /-- Read the current value of the register. -/
  | read
  /-- Write value `v` to the register. -/
  | write (v : V)
  deriving @[expose] DecidableEq

/-- Whether an `OpKind` is a `read`. -/
@[expose] def OpKind.isRead {V : Type*} : OpKind V → Bool
  | .read => true
  | .write _ => false

/-- Completion response emitted by a process for its active client operation. -/
inductive OpResp (V : Type*) where
  /-- Complete an active `read` operation, returning `val`. -/
  | readRet (val : V)
  /-- Complete an active `write` operation. -/
  | writeAck
  deriving @[expose] DecidableEq

/-- Completion status of an invoked register operation in a global execution history. -/
inductive OpStatus (V : Type*) where
  /-- Operation has been invoked and has not yet completed. -/
  | pending
  /-- A `read` operation completed at transition step `respStep`, returning `val`. -/
  | doneRead (respStep : ℕ) (val : V)
  /-- A `write` operation completed at transition step `respStep`. -/
  | doneWrite (respStep : ℕ)
  deriving @[expose] DecidableEq

/-- Transition step at which an operation completed, or `none` if still pending. -/
@[expose] def OpStatus.respStep? {V : Type*} : OpStatus V → Option ℕ
  | .pending => none
  | .doneRead s _ => some s
  | .doneWrite s => some s

/-- Boolean check for whether an operation has completed. -/
@[expose] def OpStatus.isCompleted {V : Type*} (st : OpStatus V) : Bool :=
  st.respStep?.isSome

@[simp]
theorem OpStatus.isCompleted_pending {V : Type*} :
    (OpStatus.pending : OpStatus V).isCompleted = false := rfl

@[simp]
theorem OpStatus.isCompleted_doneRead {V : Type*} (s : ℕ) (v : V) :
    (OpStatus.doneRead s v).isCompleted = true := rfl

@[simp]
theorem OpStatus.isCompleted_doneWrite {V : Type*} (s : ℕ) :
    (OpStatus.doneWrite s : OpStatus V).isCompleted = true := rfl

/-- Record of an invoked client operation in a global execution history. -/
@[ext]
structure OpRecord (P V : Type*) where
  /-- Process that invoked the operation. -/
  caller : P
  /-- Operation invoked (`read` or `write v`). -/
  kind : OpKind V
  /-- Global non-stutter step counter when the operation was invoked. -/
  invStep : ℕ
  /-- Current completion status. -/
  status : OpStatus V
  deriving @[expose] DecidableEq

/-- Check whether an `OpRecord` is a valid participant in a linearization: either a completed
`read`, a completed `write`, or a pending `write`. -/
@[expose] def OpRecord.isEligible {P V : Type*} (rec : OpRecord P V) : Prop :=
  match rec.kind, rec.status with
  | .write _, .doneWrite _ => True
  | .write _, .pending => True
  | .read, .doneRead _ _ => True
  | _, _ => False

instance instDecidableIsEligible {P V : Type*} (rec : OpRecord P V) : Decidable rec.isEligible := by
  unfold OpRecord.isEligible
  cases rec.kind <;> cases rec.status <;> infer_instance

/-- Real-time strict precedence between operations `i` and `j` in `hist`: operation `i` completed at
some step `r` strictly before operation `j` was invoked (`r < hist[j].invStep`). -/
@[expose] def prec {P V : Type*} (hist : List (OpRecord P V)) (i j : ℕ) : Prop :=
  ∃ (hi : i < hist.length) (hj : j < hist.length) (r : ℕ),
    hist[i].status.respStep? = some r ∧ r < hist[j].invStep

instance instDecidablePrec {P V : Type*} (hist : List (OpRecord P V)) (i j : ℕ) :
    Decidable (prec hist i j) :=
  if hi : i < hist.length then
    if hj : j < hist.length then
      match h : hist[i].status.respStep? with
      | none => isFalse fun ⟨_, _, _, hr, _⟩ => by simp [h] at hr
      | some r =>
        decidable_of_iff (r < hist[j].invStep)
          ⟨fun hlt => ⟨hi, hj, r, h, hlt⟩,
           fun ⟨_, _, _, hr, hlt⟩ => by rw [h] at hr; cases hr; exact hlt⟩
    else isFalse fun ⟨_, hj', _⟩ => hj hj'
  else isFalse fun ⟨hi', _⟩ => hi hi'

/-- Every completed operation in a well-timed history satisfies `invStep ≤ respStep`, making
`prec hist` irreflexive. -/
theorem prec_irrefl {P V : Type*} {hist : List (OpRecord P V)}
    (hwf : ∀ i (hi : i < hist.length) r,
      hist[i].status.respStep? = some r → hist[i].invStep ≤ r)
    (i : ℕ) : ¬ prec hist i i := by
  rintro ⟨hi, _, r, hr, hlt⟩
  exact Nat.lt_irrefl r (lt_of_lt_of_le hlt (hwf i hi r hr))

/-- On any well-timed history (`invStep ≤ respStep` for completed operations), real-time precedence
`prec hist` is transitive. -/
theorem prec_trans {P V : Type*} {hist : List (OpRecord P V)}
    (hwf : ∀ i (hi : i < hist.length) r,
      hist[i].status.respStep? = some r → hist[i].invStep ≤ r)
    {i j k : ℕ} (hij : prec hist i j) (hjk : prec hist j k) : prec hist i k := by
  obtain ⟨hi, hj, ri, hri, hlt1⟩ := hij
  obtain ⟨_, hk, rj, hrj, hlt2⟩ := hjk
  exact ⟨hi, hk, ri, hri, lt_of_lt_of_le hlt1 ((hwf j hj rj hrj).trans (Nat.le_of_lt hlt2))⟩

/-- Sequential atomic read/write register validity along a list `seq` of operation indices starting
from current value `cur`: each `write v` (completed or pending) updates the register to `v`, and
each completed `read` returns the current register value `cur`. -/
@[expose] def seqValid {P V : Type*} (cur : V) (hist : List (OpRecord P V)) : List ℕ → Prop
  | [] => True
  | i :: rest =>
    ∃ hi : i < hist.length,
      match hist[i].kind, hist[i].status with
      | .write v, .doneWrite _ => seqValid v hist rest
      | .write v, .pending => seqValid v hist rest
      | .read, .doneRead _ r => r = cur ∧ seqValid cur hist rest
      | _, _ => False

instance instDecidableSeqValid {P V : Type*} [DecidableEq V] (cur : V)
    (hist : List (OpRecord P V)) : (seq : List ℕ) → Decidable (seqValid cur hist seq)
  | [] => isTrue trivial
  | i :: rest =>
    if hi : i < hist.length then
      match h1 : hist[i].kind, h2 : hist[i].status with
      | .write v, .doneWrite _ =>
        haveI := instDecidableSeqValid v hist rest
        decidable_of_iff (seqValid v hist rest)
          ⟨fun h => ⟨hi, by simp [h1, h2, h]⟩,
           fun ⟨_, h⟩ => by simpa [h1, h2] using h⟩
      | .write v, .pending =>
        haveI := instDecidableSeqValid v hist rest
        decidable_of_iff (seqValid v hist rest)
          ⟨fun h => ⟨hi, by simp [h1, h2, h]⟩,
           fun ⟨_, h⟩ => by simpa [h1, h2] using h⟩
      | .read, .doneRead _ r =>
        haveI := instDecidableSeqValid cur hist rest
        decidable_of_iff (r = cur ∧ seqValid cur hist rest)
          ⟨fun h => ⟨hi, by simp [h1, h2, h]⟩,
           fun ⟨_, h⟩ => by simpa [h1, h2] using h⟩
      | .write _, .doneRead _ _ =>
        isFalse fun ⟨_, h⟩ => by simp [h1, h2] at h
      | .read, .pending =>
        isFalse fun ⟨_, h⟩ => by simp [h1, h2] at h
      | .read, .doneWrite _ =>
        isFalse fun ⟨_, h⟩ => by simp [h1, h2] at h
    else
      isFalse fun ⟨hi', _⟩ => hi hi'

/-- Register value produced after sequentially executing a prefix `pref` of operation indices from
initial value `v₀`: the value written by the last `write` in `pref`, or `v₀` if `pref` contains no
`write`. -/
@[expose] def registerValAfter {P V : Type*} (v₀ : V) (hist : List (OpRecord P V))
    (pref : List ℕ) : V :=
  pref.foldl (fun cur i =>
    match hist[i]? with
    | some rec =>
      match rec.kind with
      | .write v => v
      | .read => cur
    | none => cur) v₀

@[simp]
theorem registerValAfter_nil {P V : Type*} (v₀ : V) (hist : List (OpRecord P V)) :
    registerValAfter v₀ hist [] = v₀ := rfl

@[simp]
theorem registerValAfter_cons {P V : Type*} (v₀ : V) (hist : List (OpRecord P V))
    (i : ℕ) (rest : List ℕ) :
    registerValAfter v₀ hist (i :: rest) =
      registerValAfter
        (match hist[i]? with
         | some rec => match rec.kind with | .write v => v | .read => v₀
         | none => v₀) hist rest := rfl

/-- Sequential register evaluation splits across list concatenation. -/
theorem registerValAfter_append {P V : Type*} (v₀ : V) (hist : List (OpRecord P V))
    (l₁ l₂ : List ℕ) :
    registerValAfter v₀ hist (l₁ ++ l₂) =
      registerValAfter (registerValAfter v₀ hist l₁) hist l₂ := by
  simp [registerValAfter, List.foldl_append]

private lemma seqValid_cons_iff {P V : Type*} {cur : V} {hist : List (OpRecord P V)}
    {j : ℕ} {rest : List ℕ} :
    seqValid cur hist (j :: rest) ↔
      ∃ hj : j < hist.length,
        hist[j].isEligible ∧
        (∀ s r, hist[j].status = .doneRead s r → r = cur) ∧
        seqValid (match hist[j].kind with | .write v => v | .read => cur) hist rest := by
  refine ⟨fun ⟨hj, hbody⟩ => ⟨hj, ?_⟩, fun ⟨hj, helig, hrd, hrest⟩ => ⟨hj, ?_⟩⟩
  · revert hbody
    cases hk : hist[j].kind <;> cases hs : hist[j].status <;>
      simp [OpRecord.isEligible, hk, hs]
  · revert helig hrest
    cases hk : hist[j].kind <;> cases hs : hist[j].status <;>
      simp only [OpRecord.isEligible, hk, hs] <;>
      first | exact False.elim | exact fun _ h => h | exact fun _ h => ⟨hrd _ _ hs, h⟩

private lemma seqValid_append {P V : Type*} (cur : V) (hist : List (OpRecord P V))
    (l₁ l₂ : List ℕ) (h₁ : seqValid cur hist l₁)
    (h₂ : seqValid (registerValAfter cur hist l₁) hist l₂) :
    seqValid cur hist (l₁ ++ l₂) := by
  induction l₁ generalizing cur with
  | nil => exact h₂
  | cons j rest ih =>
    rw [seqValid_cons_iff] at h₁
    obtain ⟨hj, helig, hrd, hrest⟩ := h₁
    exact (List.cons_append .. ▸ seqValid_cons_iff).mpr ⟨hj, helig, hrd,
      ih _ hrest (by simpa [registerValAfter_cons, List.getElem?_eq_getElem hj] using h₂)⟩

private lemma registerValAfter_append_hist {P V : Type*} (cur : V)
    (hist extra : List (OpRecord P V)) {seq : List ℕ}
    (hbound : ∀ i ∈ seq, i < hist.length) :
    registerValAfter cur (hist ++ extra) seq = registerValAfter cur hist seq := by
  induction seq generalizing cur with
  | nil => rfl
  | cons j rest ih =>
    have hj : j < hist.length := hbound j List.mem_cons_self
    have hj' : j < (hist ++ extra).length := lt_of_lt_of_le hj (by simp)
    simp only [registerValAfter_cons, List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem hj', List.getElem_append_left hj]
    exact ih _ fun i hi => hbound i (List.mem_cons_of_mem j hi)

private lemma seqValid_append_hist {P V : Type*} (cur : V)
    (hist extra : List (OpRecord P V)) {seq : List ℕ}
    (h : seqValid cur hist seq) : seqValid cur (hist ++ extra) seq := by
  induction seq generalizing cur with
  | nil => trivial
  | cons j rest ih =>
    rw [seqValid_cons_iff] at h ⊢
    obtain ⟨hj, helig, hrd, hrest⟩ := h
    refine ⟨lt_of_lt_of_le hj (by simp),
      by simpa [List.getElem_append_left hj] using helig,
      by simpa [List.getElem_append_left hj] using hrd,
      by simpa [List.getElem_append_left hj] using ih _ hrest⟩

/-- **Preceding-write characterization of `seqValid`:** a sequence `seq` satisfies `seqValid v₀ hist
seq` if and only if every index in `seq` is an in-bounds eligible operation (completed read,
completed write, or pending write) and every completed read at position `k` returns
`registerValAfter v₀ hist (seq.take k)` (the value written by the immediately preceding write in
`seq`, or `v₀` if no write precedes position `k`). -/
theorem seqValid_iff_registerValAfter {P V : Type*} (v₀ : V) (hist : List (OpRecord P V))
    (seq : List ℕ) :
    seqValid v₀ hist seq ↔
      (∀ i ∈ seq, ∃ hi : i < hist.length, hist[i].isEligible) ∧
      (∀ (k : ℕ) (hk : k < seq.length) (hi : seq[k] < hist.length) (s : ℕ) (r : V),
        hist[seq[k]].status = .doneRead s r →
        r = registerValAfter v₀ hist (seq.take k)) := by
  induction seq generalizing v₀ with
  | nil => simp [seqValid]
  | cons j rest ih =>
    rw [seqValid_cons_iff]
    constructor
    · rintro ⟨hj, helig, hrd0, hrest⟩
      obtain ⟨helig_rest, hrd_rest⟩ := (ih _).mp hrest
      refine ⟨fun i hi => ?_, fun k hk hi s r hst => ?_⟩
      · rcases List.mem_cons.mp hi with rfl | hm
        exacts [⟨hj, helig⟩, helig_rest i hm]
      · cases k with
        | zero => exact hrd0 s r hst
        | succ k' =>
          simpa [registerValAfter_cons, List.getElem?_eq_getElem hj] using
            hrd_rest k' (Nat.lt_of_succ_lt_succ hk) hi s r hst
    · rintro ⟨helig_all, hreads⟩
      obtain ⟨hj, helig⟩ := helig_all j List.mem_cons_self
      refine ⟨hj, helig, fun s r hst => hreads 0 (Nat.zero_lt_succ _) hj s r hst,
        (ih _).mpr ⟨fun i hi => helig_all i (List.mem_cons_of_mem j hi),
          fun k hk hi s r hst => ?_⟩⟩
      simpa [registerValAfter_cons, List.getElem?_eq_getElem hj] using
        hreads (k + 1) (Nat.succ_lt_succ hk) hi s r hst

/-- `IsLinearization v₀ hist seq` states that `seq` is a valid linearization of execution history
`hist` for an atomic read/write register initialized to `v₀`:

* `nodup`: no operation index appears twice in `seq`;
* `complete`: every completed operation in `hist` appears in `seq`;
* `respects_prec`: if `i, j ∈ seq` and `prec hist i j` (`i` completed strictly before `j` was
  invoked), then `i` precedes `j` in `seq` (`seq.idxOf i < seq.idxOf j`);
* `valid`: `seq` obeys sequential read/write register semantics from `v₀` (and contains only
  completed reads, completed writes, and optionally pending writes). -/
structure IsLinearization {P V : Type*} (v₀ : V) (hist : List (OpRecord P V))
    (seq : List ℕ) : Prop where
  /-- Each operation index occurs at most once. -/
  nodup : seq.Nodup
  /-- Every completed operation is included in the linearization. -/
  complete : ∀ (i : ℕ) (hi : i < hist.length), hist[i].status.isCompleted = true → i ∈ seq
  /-- Real-time precedence is preserved. -/
  respects_prec : ∀ i ∈ seq, ∀ j ∈ seq, prec hist i j → seq.idxOf i < seq.idxOf j
  /-- Sequential read/write register semantics hold from initial value `v₀`. -/
  valid : seqValid v₀ hist seq

instance instDecidableIsLinearization {P V : Type*} [DecidableEq V] (v₀ : V)
    (hist : List (OpRecord P V)) (seq : List ℕ) :
    Decidable (IsLinearization v₀ hist seq) :=
  decidable_of_iff
    (seq.Nodup ∧
      (∀ idx : Fin hist.length, hist[idx.val].status.isCompleted = true → idx.val ∈ seq) ∧
      (∀ i ∈ seq, ∀ j ∈ seq, prec hist i j → seq.idxOf i < seq.idxOf j) ∧
      seqValid v₀ hist seq)
    (by
      exact
        ⟨fun ⟨hnd, hcomp, hprec, hvalid⟩ =>
          ⟨hnd, fun i hi hc => hcomp ⟨i, hi⟩ hc, hprec, hvalid⟩,
         fun h =>
          ⟨h.nodup, fun idx hc => h.complete idx.val idx.isLt hc, h.respects_prec, h.valid⟩⟩)

/-- An execution history `hist` is *linearizable* (atomic) with initial value `v₀` if there exists
a valid linearization sequence `seq`. -/
@[expose] def Linearizable {P V : Type*} (v₀ : V) (hist : List (OpRecord P V)) : Prop :=
  ∃ seq : List ℕ, IsLinearization v₀ hist seq

/-- The empty execution history is trivially linearizable for every initial value `v₀`. -/
@[simp]
theorem linearizable_nil {P V : Type*} (v₀ : V) : Linearizable v₀ ([] : List (OpRecord P V)) :=
  ⟨[], IsLinearization.mk List.nodup_nil (fun _ hi => by cases hi) (fun _ hm => by cases hm)
    trivial⟩

/-- Insert index `k` at every position in `ys`. Marked `@[expose]` so `instDecidableLinearizable`
reduces completely under `decide` in downstream `module` clients. -/
@[expose] def insertAtAll (k : ℕ) : List ℕ → List (List ℕ)
  | [] => [[k]]
  | y :: ys => (k :: y :: ys) :: (insertAtAll k ys).map (y :: ·)

/-- Enumerate all duplicate-free sequences of indices strictly below `n`. -/
@[expose] def candidateSeqs : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 =>
    let prev := candidateSeqs n
    prev ++ prev.flatMap (insertAtAll n)

private lemma mem_insertAtAll (k : ℕ) (l₁ l₂ : List ℕ) :
    l₁ ++ k :: l₂ ∈ insertAtAll k (l₁ ++ l₂) := by
  induction l₁ with
  | nil => cases l₂ <;> exact List.mem_cons_self
  | cons y l₁ ih => exact List.mem_cons_of_mem _ (List.mem_map_of_mem ih)

private lemma mem_candidateSeqs {n : ℕ} {seq : List ℕ}
    (hnd : seq.Nodup) (hlt : ∀ i ∈ seq, i < n) : seq ∈ candidateSeqs n := by
  induction n generalizing seq with
  | zero =>
    cases seq with
    | nil => exact List.mem_singleton_self []
    | cons a _ => exact False.elim (Nat.not_lt_zero a (hlt a List.mem_cons_self))
  | succ n ih =>
    by_cases hn : n ∈ seq
    · obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hn
      obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp (List.perm_middle.nodup_iff.mp hnd)
      have hlt' : ∀ i ∈ l₁ ++ l₂, i < n := fun i hi =>
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (hlt i (by
          simp only [List.mem_append, List.mem_cons] at hi ⊢; tauto))) fun heq => hnot (heq ▸ hi)
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨l₁ ++ l₂, ih hnd' hlt', mem_insertAtAll n l₁ l₂⟩)
    · exact List.mem_append_left _ (ih hnd fun i hi =>
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (hlt i hi)) fun heq => hn (heq ▸ hi))

/-- Computable `Decidable` instance for `Linearizable v₀ hist` over finite histories when `V` has
decidable equality, obtained by checking `candidateSeqs hist.length`. -/
instance instDecidableLinearizable {P V : Type*} [DecidableEq V] (v₀ : V)
    (hist : List (OpRecord P V)) : Decidable (Linearizable v₀ hist) :=
  decidable_of_iff
    (∃ seq ∈ candidateSeqs hist.length, IsLinearization v₀ hist seq)
    (by
      exact ⟨fun ⟨seq, _, hlin⟩ => ⟨seq, hlin⟩,
        fun ⟨seq, hlin⟩ =>
          ⟨seq, mem_candidateSeqs hlin.nodup
            (fun i hi => (((seqValid_iff_registerValAfter v₀ hist seq).mp hlin.valid).1 i hi).1),
            hlin⟩⟩)

/-! ### Asynchronous message-passing protocol and LTS -/

/-- Local transition output emitted by a process upon a client invocation or message delivery. -/
@[ext]
structure StepOut (P M S V : Type*) where
  /-- Updated internal local state. -/
  nextState : S
  /-- Outgoing `(dest, body)` messages emitted onto the network. -/
  outgoing : Multiset (P × M)
  /-- Optional completion response for the process's currently pending operation. -/
  resp : Option (OpResp V)
  deriving @[expose] DecidableEq

/-- Active client operation currently pending at a process. -/
@[ext]
structure PendingOp (V : Type*) where
  /-- Index of this operation in the global execution `history`. -/
  opId : ℕ
  /-- Kind of operation (`read` or `write v`). -/
  kind : OpKind V
  deriving @[expose] DecidableEq

/-- Local configuration of a process: protocol state paired with at most one active operation. -/
@[ext]
structure ProcState (S V : Type*) where
  /-- Internal protocol state. -/
  state : S
  /-- Active client operation (`none` when the process is idle). -/
  pending : Option (PendingOp V)
  deriving @[expose] DecidableEq

/-- Global configuration of an asynchronous register-emulation network. -/
@[ext]
structure State (P S M V : Type*) where
  /-- Multiset of unordered point-to-point envelopes currently in transit. -/
  msgs : Multiset (Envelope P M)
  /-- Local state and active client status of every process. -/
  proc : P → ProcState S V
  /-- Chronological log of all client operations invoked so far. -/
  history : List (OpRecord P V)
  /-- Number of non-stutter transitions elapsed so far (used for `invStep` and `respStep`). -/
  step : ℕ

/-- Transition label for the asynchronous register-emulation LTS. -/
inductive Action (P M V : Type*) where
  /-- Idle process `caller` invokes client operation `kind` (`read` or `write v`). -/
  | invoke (caller : P) (kind : OpKind V)
  /-- Deliver an in-flight envelope `e` to `e.dest`. -/
  | deliver (e : Envelope P M)
  /-- Stuttering step leaving the global state unchanged. -/
  | stutter
  deriving @[expose] DecidableEq

/-- Deterministic asynchronous message-passing protocol emulating a shared register over `P`. -/
structure Protocol (P S M V : Type*) where
  /-- Initial internal state of process `p`. -/
  init : P → S
  /-- Initial outgoing messages `(dest, body)` emitted by process `p` at boot. -/
  initMsgs : P → Multiset (P × M) := fun _ => 0
  /-- Local transition when process `p` in state `st` invokes client operation `kind`. -/
  onInvoke : P → S → OpKind V → StepOut P M S V
  /-- Local transition when process `dest` in state `st` receives `body` from `src`. -/
  onRecv : P → S → P → M → StepOut P M S V

/-- Match an emitted `OpResp` against the active `OpKind` to form a completed `OpStatus` at `step`
(or `none` if no matching completion was emitted). -/
@[expose] def matchCompletion {V : Type*} (kind : OpKind V) (resp : Option (OpResp V))
    (step : ℕ) : Option (OpStatus V) :=
  match kind, resp with
  | .read, some (.readRet v) => some (.doneRead step v)
  | .write _, some .writeAck => some (.doneWrite step)
  | _, _ => none

/-- Updated `pending` field after invoking `kind` at `opId`. -/
@[expose] def invokePending {V : Type*} (opId : ℕ) (kind : OpKind V)
    (resp : Option (OpResp V)) (step : ℕ) : Option (PendingOp V) :=
  match matchCompletion kind resp step with
  | some _ => none
  | none => some ⟨opId, kind⟩

/-- Updated `pending` field after delivering a message with completion output `resp`. -/
@[expose] def deliverPending {V : Type*} (pend? : Option (PendingOp V))
    (resp : Option (OpResp V)) (step : ℕ) : Option (PendingOp V) :=
  match pend? with
  | none => none
  | some pend =>
    match matchCompletion pend.kind resp step with
    | none => some pend
    | some _ => none

/-- Updated `history` list after delivering a message with completion output `resp`. -/
@[expose] def deliverHistory {P V : Type*} (hist : List (OpRecord P V))
    (resp : Option (OpResp V)) (step : ℕ) : Option (PendingOp V) → List (OpRecord P V)
  | none => hist
  | some pend =>
    match matchCompletion pend.kind resp step, hist[pend.opId]? with
    | some stDone, some rec => hist.set pend.opId { rec with status := stDone }
    | _, _ => hist

@[simp]
theorem matchCompletion_none {V : Type*} (kind : OpKind V) (step : ℕ) :
    matchCompletion kind none step = none := by
  cases kind <;> rfl

@[simp]
theorem invokePending_none {V : Type*} (opId : ℕ) (kind : OpKind V) (step : ℕ) :
    invokePending opId kind none step = some ⟨opId, kind⟩ := by
  simp [invokePending]

@[simp]
theorem deliverPending_none {V : Type*} (pend? : Option (PendingOp V)) (step : ℕ) :
    deliverPending pend? none step = pend? := by
  cases pend? <;> simp [deliverPending]

@[simp]
theorem deliverHistory_none {P V : Type*} (hist : List (OpRecord P V)) (step : ℕ)
    (pend? : Option (PendingOp V)) :
    deliverHistory hist none step pend? = hist := by
  cases pend? <;> simp [deliverHistory]

@[simp]
theorem length_deliverHistory {P V : Type*} (hist : List (OpRecord P V))
    (resp : Option (OpResp V)) (step : ℕ) (pend? : Option (PendingOp V)) :
    (deliverHistory hist resp step pend?).length = hist.length := by
  cases pend? with
  | none => rfl
  | some pend => dsimp only [deliverHistory]; split <;> simp

private lemma respStep?_of_matchCompletion {V : Type*} {kind : OpKind V}
    {resp : Option (OpResp V)} {step : ℕ} {stDone : OpStatus V}
    (hm : matchCompletion kind resp step = some stDone) :
    stDone.respStep? = some step := by
  rcases kind with _ | _ <;> rcases resp with _ | (_ | _) <;> cases hm <;> rfl

/-- Delivering a response preserves `caller`, `kind`, and `invStep` at every index
`i < hist.length`, and any response timestamp in `deliverHistory` either was already present in
`hist` or equals `step`. -/
theorem deliverHistory_entry_preserves {P V : Type*} (hist : List (OpRecord P V))
    (resp : Option (OpResp V)) (step : ℕ) (pend? : Option (PendingOp V))
    {i : ℕ} (hi : i < hist.length)
    (hi' : i < (deliverHistory hist resp step pend?).length) :
    (deliverHistory hist resp step pend?)[i].caller = hist[i].caller ∧
    (deliverHistory hist resp step pend?)[i].kind = hist[i].kind ∧
    (deliverHistory hist resp step pend?)[i].invStep = hist[i].invStep ∧
    (∀ r, (deliverHistory hist resp step pend?)[i].status.respStep? = some r →
      hist[i].status.respStep? = some r ∨ r = step) := by
  by_cases h : (deliverHistory hist resp step pend?)[i] = hist[i]
  · rw [h]
    exact ⟨rfl, rfl, rfl, fun _ hr => Or.inl hr⟩
  · rcases pend? with _ | pend
    · exact absurd rfl h
    · cases hm : matchCompletion pend.kind resp step with
      | none => exact absurd (by simp only [deliverHistory, hm]) h
      | some stDone =>
        cases hrec : hist[pend.opId]? with
        | none => exact absurd (by simp only [deliverHistory, hm, hrec]) h
        | some rec =>
          obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.mp hrec
          obtain rfl : pend.opId = i := by_contra fun hip =>
            h (by simp only [deliverHistory, hm, hrec, List.getElem_set_ne hip])
          simp only [deliverHistory, hm, hrec, List.getElem_set_self, true_and]
          exact fun r hr =>
            Or.inr (Option.some.inj ((respStep?_of_matchCompletion hm).symm.trans hr)).symm

private lemma getElem?_deliverHistory_of_ne {P V : Type*} (hist : List (OpRecord P V))
    (resp : Option (OpResp V)) (step : ℕ) (pend? : Option (PendingOp V)) {i : ℕ}
    (hne : ∀ pend, pend? = some pend → pend.opId ≠ i) :
    (deliverHistory hist resp step pend?)[i]? = hist[i]? := by
  cases pend? with
  | none => rfl
  | some pend =>
    dsimp only [deliverHistory]
    split
    · exact List.getElem?_set_ne (hne pend rfl)
    · rfl

private lemma getElem_deliverHistory_of_ne {P V : Type*} (hist : List (OpRecord P V))
    (resp : Option (OpResp V)) (step : ℕ) (pend? : Option (PendingOp V))
    {i : ℕ} (hi : i < hist.length)
    (hne : ∀ pend, pend? = some pend → pend.opId ≠ i) :
    (deliverHistory hist resp step pend?)[i]'(by simpa using hi) = hist[i] := by
  have h := getElem?_deliverHistory_of_ne hist resp step pend? hne
  rw [List.getElem?_eq_getElem (by simpa using hi), List.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

namespace Protocol

variable {P S M V : Type*} [DecidableEq P] [DecidableEq M] (π : Protocol P S M V)

/-- Initial global state of `π`: all processes are idle in `π.init p`, `history` is empty, and
`step = 0`. -/
@[expose] def start [Fintype P] : State P S M V where
  msgs := Finset.univ.val.bind fun p => (π.initMsgs p).map (tagSender p)
  proc p := ⟨π.init p, none⟩
  history := []
  step := 0

/-- State transition when idle process `caller` invokes `kind`. -/
@[expose] def doInvoke (caller : P) (kind : OpKind V) (s : State P S M V) : State P S M V :=
  let out := π.onInvoke caller (s.proc caller).state kind
  let opId := s.history.length
  let st := (matchCompletion kind out.resp s.step).getD .pending
  let pend := invokePending opId kind out.resp s.step
  { msgs := s.msgs + out.outgoing.map (tagSender caller)
    proc := Function.update s.proc caller ⟨out.nextState, pend⟩
    history := s.history ++ [⟨caller, kind, s.step, st⟩]
    step := s.step + 1 }

/-- State transition when in-flight envelope `e` is delivered to `e.dest`. -/
@[expose] def doDeliver (e : Envelope P M) (s : State P S M V) : State P S M V :=
  let dest := e.dest
  let out := π.onRecv dest (s.proc dest).state e.src e.body
  { msgs := s.msgs.erase e + out.outgoing.map (tagSender dest)
    proc := Function.update s.proc dest
      ⟨out.nextState, deliverPending (s.proc dest).pending out.resp s.step⟩
    history := deliverHistory s.history out.resp s.step (s.proc dest).pending
    step := s.step + 1 }

omit [DecidableEq M] in
/-- Unfolding equation for `doInvoke` when `onInvoke` does not complete immediately (`resp = none`).
-/
theorem doInvoke_of_resp_eq_none {caller : P} {kind : OpKind V} {s : State P S M V}
    {nextSt : S} {outMsgs : Multiset (P × M)}
    (hout : π.onInvoke caller (s.proc caller).state kind = ⟨nextSt, outMsgs, none⟩) :
    π.doInvoke caller kind s =
      { msgs := s.msgs + outMsgs.map (tagSender caller)
        proc := Function.update s.proc caller ⟨nextSt, some ⟨s.history.length, kind⟩⟩
        history := s.history ++ [⟨caller, kind, s.step, .pending⟩]
        step := s.step + 1 } := by
  simp [doInvoke, hout]

/-- Unfolding equation for `doDeliver` when `onRecv` emits no completion response (`resp = none`).
-/
theorem doDeliver_of_resp_eq_none {e : Envelope P M} {s : State P S M V}
    {nextSt : S} {outMsgs : Multiset (P × M)}
    (hout : π.onRecv e.dest (s.proc e.dest).state e.src e.body = ⟨nextSt, outMsgs, none⟩) :
    π.doDeliver e s =
      { msgs := s.msgs.erase e + outMsgs.map (tagSender e.dest)
        proc := Function.update s.proc e.dest ⟨nextSt, (s.proc e.dest).pending⟩
        history := s.history
        step := s.step + 1 } := by
  simp [doDeliver, hout]

/-- Unfolding equation for `doDeliver` when `onRecv` completes `e.dest`'s pending operation. -/
theorem doDeliver_of_complete {e : Envelope P M} {s : State P S M V}
    {nextSt : S} {outMsgs : Multiset (P × M)} {resp : Option (OpResp V)}
    {pend : PendingOp V} {stDone : OpStatus V}
    (hout : π.onRecv e.dest (s.proc e.dest).state e.src e.body = ⟨nextSt, outMsgs, resp⟩)
    (hpend : (s.proc e.dest).pending = some pend)
    (hmatch : matchCompletion pend.kind resp s.step = some stDone)
    (hi : pend.opId < s.history.length) :
    π.doDeliver e s =
      { msgs := s.msgs.erase e + outMsgs.map (tagSender e.dest)
        proc := Function.update s.proc e.dest ⟨nextSt, none⟩
        history := s.history.set pend.opId { s.history[pend.opId] with status := stDone }
        step := s.step + 1 } := by
  simp [doDeliver, hout, hpend, deliverPending, deliverHistory, hmatch,
    List.getElem?_eq_getElem hi]

/-- Labelled transition system of `π`. -/
@[expose] def lts : LTS (State P S M V) (Action P M V) where
  Tr s a s' := match a with
    | .invoke caller kind => (s.proc caller).pending = none ∧ s' = π.doInvoke caller kind s
    | .deliver e => e ∈ s.msgs ∧ s' = π.doDeliver e s
    | .stutter => s' = s

/-- `π.Reachable s` means `s` is reachable from `π.start` under `π.lts`. -/
@[expose] def Reachable [Fintype P] (s : State P S M V) : Prop :=
  π.lts.CanReach π.start s

/-- The initial state `π.start` is reachable. -/
theorem reachable_start [Fintype P] : π.Reachable π.start :=
  LTS.CanReach.refl π.lts π.start

/-- Reachability from `π.start` composes with `π.lts.CanReach`. -/
theorem Reachable.trans [Fintype P] {π : Protocol P S M V} {s s' : State P S M V}
    (hs : π.Reachable s) (hreach : π.lts.CanReach s s') : π.Reachable s' := by
  obtain ⟨xl, hxl⟩ := hs
  obtain ⟨yl, hyl⟩ := hreach
  exact ⟨xl ++ yl, LTS.MTr.comp π.lts hxl hyl⟩

/-! ### Structural invariants of `history` and `msgs` -/

private lemma tr_history_length_le {s s' : State P S M V} {a : Action P M V}
    (htr : π.lts.Tr s a s') : s.history.length ≤ s'.history.length := by
  cases a with
  | stutter => exact htr ▸ le_rfl
  | _ => obtain ⟨_, rfl⟩ := htr; simp [doInvoke, doDeliver]

/-- Execution history length never decreases along a finite execution. -/
theorem mTr_history_length_le {s t : State P S M V} {xl : List (Action P M V)}
    (hmtr : π.lts.MTr s xl t) : s.history.length ≤ t.history.length := by
  induction hmtr with
  | refl => exact le_rfl
  | stepL htr _ ih => exact (π.tr_history_length_le htr).trans ih

private lemma tr_history_entry_preserves {s s' : State P S M V} {a : Action P M V}
    (htr : π.lts.Tr s a s') {i : ℕ} (hi : i < s.history.length)
    (hi' : i < s'.history.length) :
    s'.history[i].caller = s.history[i].caller ∧
    s'.history[i].kind = s.history[i].kind ∧
    s'.history[i].invStep = s.history[i].invStep := by
  cases a with
  | invoke caller kind =>
    obtain ⟨_, rfl⟩ := htr
    simp [doInvoke, List.getElem_append_left hi]
  | deliver e =>
    obtain ⟨_, rfl⟩ := htr
    obtain ⟨hc, hk, hv, _⟩ :=
      deliverHistory_entry_preserves s.history _ s.step (s.proc e.dest).pending hi hi'
    exact ⟨hc, hk, hv⟩
  | stutter =>
    obtain rfl := htr
    exact ⟨rfl, rfl, rfl⟩

/-- Every finite sequence of transitions preserves `caller`, `kind`, and `invStep` at every
already-invoked index `i < s.history.length`. -/
theorem mTr_history_entry_preserves {s t : State P S M V} {xl : List (Action P M V)}
    (hmtr : π.lts.MTr s xl t) {i : ℕ} (hi : i < s.history.length)
    (hit : i < t.history.length) :
    t.history[i].caller = s.history[i].caller ∧
    t.history[i].kind = s.history[i].kind ∧
    t.history[i].invStep = s.history[i].invStep := by
  induction hmtr with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | stepL htr _ ih =>
    have hi' := lt_of_lt_of_le hi (π.tr_history_length_le htr)
    obtain ⟨c1, k1, v1⟩ := ih hi' hit
    obtain ⟨c0, k0, v0⟩ := π.tr_history_entry_preserves htr hi hi'
    exact ⟨c1.trans c0, k1.trans k0, v1.trans v0⟩

/-- Completed entries in `history` never change across transitions. -/
theorem tr_history_completed_stable {s s' : State P S M V} {a : Action P M V}
    (htr : π.lts.Tr s a s') {i : ℕ} (hi : i < s.history.length)
    (hcomp : s.history[i].status.isCompleted = true)
    (hpend : ∀ p pend, (s.proc p).pending = some pend →
      ∃ hlt : pend.opId < s.history.length, s.history[pend.opId].status = .pending) :
    ∃ hi' : i < s'.history.length, s'.history[i] = s.history[i] := by
  refine ⟨lt_of_lt_of_le hi (π.tr_history_length_le htr), ?_⟩
  cases a with
  | invoke caller kind =>
    obtain ⟨_, rfl⟩ := htr
    simp [doInvoke, List.getElem_append_left hi]
  | deliver e =>
    obtain ⟨_, rfl⟩ := htr
    exact getElem_deliverHistory_of_ne s.history _ s.step (s.proc e.dest).pending hi
      fun pend hp heq => by
        obtain ⟨_, hppend⟩ := hpend e.dest pend hp
        subst heq
        rw [hppend] at hcomp
        cases hcomp
  | stutter =>
    obtain rfl := htr
    rfl

/-- An in-flight envelope `e` stays in `msgs` across any transition other than `.deliver e`. -/
theorem tr_notDelivered_mem {s s' : State P S M V} {a : Action P M V}
    {e : Envelope P M} (he : e ∈ s.msgs) (ha : a ≠ .deliver e)
    (htr : π.lts.Tr s a s') : e ∈ s'.msgs := by
  cases a with
  | invoke caller kind =>
    obtain ⟨_, rfl⟩ := htr
    exact Multiset.mem_add.mpr (Or.inl he)
  | deliver m =>
    obtain ⟨_, rfl⟩ := htr
    exact Multiset.mem_add.mpr
      (Or.inl ((Multiset.mem_erase_of_ne fun h => ha (congrArg Action.deliver h.symm)).mpr he))
  | stutter => exact htr ▸ he

private lemma mTr_notDelivered_mem {s t : State P S M V} {xl : List (Action P M V)}
    {e : Envelope P M} (h : π.lts.MTr s xl t) (he : e ∈ s.msgs)
    (hnot : .deliver e ∉ xl) : e ∈ t.msgs := by
  induction h with
  | refl => exact he
  | stepL htr _ ih =>
    exact ih (π.tr_notDelivered_mem he (fun hx => hnot (by simp [hx])) htr)
      fun hx => hnot (List.mem_cons_of_mem _ hx)

private lemma omega_notDelivered_mem {ss : ωSequence (State P S M V)}
    {xs : ωSequence (Action P M V)} (hexec : π.lts.OmegaExecution ss xs)
    {k : ℕ} {e : Envelope P M} (he : e ∈ (ss k).msgs)
    (hnot : ∀ j, k ≤ j → xs j ≠ .deliver e) :
    ∀ j, k ≤ j → e ∈ (ss j).msgs := by
  intro j hkj
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
  induction d with
  | zero => simpa using he
  | succ d ih =>
    exact π.tr_notDelivered_mem (ih (Nat.le_add_right k d))
      (hnot (k + d) (Nat.le_add_right k d)) (hexec (k + d))

/-! ### Fairness, admissible executions, and round-robin scheduler -/

omit [DecidableEq P] [DecidableEq M] in
/-- Fairness relative to static faulty set `F`: every in-flight envelope addressed to a non-faulty
process `e.dest ∉ F` is eventually delivered. -/
@[expose] def Fair (F : Finset P) (ss : ωSequence (State P S M V))
    (xs : ωSequence (Action P M V)) : Prop :=
  ∀ e : Envelope P M, e.dest ∉ F → ∀ k, e ∈ (ss k).msgs → ∃ j, k ≤ j ∧ xs j = .deliver e

/-- An admissible infinite execution of `π` relative to static faulty set `F`. -/
@[expose] def AdmissibleRun [Fintype P] (F : Finset P)
    (ss : ωSequence (State P S M V)) (xs : ωSequence (Action P M V)) : Prop :=
  ss 0 = π.start ∧ π.lts.OmegaExecution ss xs ∧ Fair F ss xs

/-- Every state along an `AdmissibleRun` is reachable from `π.start`. -/
theorem admissibleRun_reachable [Fintype P] {F : Finset P}
    {ss : ωSequence (State P S M V)} {xs : ωSequence (Action P M V)}
    (ha : π.AdmissibleRun F ss xs) (k : ℕ) : π.Reachable (ss k) :=
  ⟨xs.extract 0 k, ha.1 ▸ ha.2.1.extract_mTr (Nat.zero_le k)⟩

omit [DecidableEq P] [DecidableEq M] in
/-- Predicate for delivery/stutter actions that do not invoke new client operations and only
deliver to destinations outside `F`. -/
@[expose] def IsDrainAction (F : Finset P) : Action P M V → Prop
  | .invoke _ _ => False
  | .deliver e => e.dest ∉ F
  | .stutter => True

private def drainList (s : State P S M V) :
    List (Envelope P M) → List (Action P M V) × State P S M V
  | [] => ([], s)
  | e :: es =>
    let r := drainList (π.doDeliver e s) es
    (.deliver e :: r.1, r.2)

private lemma drainList_spec {F : Finset P} (s : State P S M V) (es : List (Envelope P M))
    (hle : Multiset.ofList es ≤ s.msgs) (hdest : ∀ e ∈ es, e.dest ∉ F) :
    π.lts.MTr s (π.drainList s es).1 (π.drainList s es).2 ∧
    (π.drainList s es).1 = es.map Action.deliver := by
  induction es generalizing s with
  | nil => exact ⟨LTS.MTr.refl, rfl⟩
  | cons e es ih =>
    have hcons : e ::ₘ Multiset.ofList es ≤ s.msgs := by simpa using hle
    have hle' : Multiset.ofList es ≤ (π.doDeliver e s).msgs :=
      le_trans (by simpa using Multiset.erase_le_erase e hcons) (Multiset.le_add_right _ _)
    obtain ⟨hmtr, hmap⟩ := ih (π.doDeliver e s) hle' fun x hx =>
      hdest x (List.mem_cons_of_mem e hx)
    exact ⟨.stepL ⟨Multiset.mem_of_le hle (by simp), rfl⟩ hmtr,
      by simp only [drainList, hmap, List.map_cons]⟩

private noncomputable def drainPhase (F : Finset P) (s : State P S M V) :
    List (Action P M V) × State P S M V :=
  let pending := s.msgs.filter (fun e => e.dest ∉ F)
  if pending = 0 then ([.stutter], s) else π.drainList s pending.toList

private lemma drainPhase_spec (F : Finset P) (s : State P S M V) :
    let res := π.drainPhase F s
    π.lts.MTr s res.1 res.2 ∧ 0 < res.1.length ∧
    (∀ a ∈ res.1, IsDrainAction F a) ∧
    (∀ e ∈ s.msgs, e.dest ∉ F → .deliver e ∈ res.1) := by
  dsimp only [drainPhase]
  set pending := s.msgs.filter (fun e => e.dest ∉ F)
  by_cases h0 : pending = 0
  · simp only [h0, ↓reduceIte, List.length_singleton, zero_lt_one, true_and,
      List.mem_singleton, forall_eq]
    exact ⟨LTS.MTr.single π.lts (show π.lts.Tr s Action.stutter s from rfl), trivial,
      fun e he hdest => absurd (show e ∈ pending from Multiset.mem_filter.mpr ⟨he, hdest⟩)
        (by simp [h0])⟩
  · simp only [h0, ↓reduceIte]
    have hdest : ∀ e ∈ pending.toList, e.dest ∉ F := fun e he =>
      (Multiset.mem_filter.mp (Multiset.mem_toList.mp he)).2
    obtain ⟨hmtr, hmap⟩ := π.drainList_spec s pending.toList
      (by simpa only [Multiset.coe_toList] using Multiset.filter_le _ _) hdest
    obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero h0
    refine ⟨hmtr, ?_, ?_, fun d hd hed => ?_⟩
    · simpa only [hmap, List.length_map] using List.length_pos_of_mem (Multiset.mem_toList.mpr he)
    · simpa only [hmap, List.forall_mem_map, IsDrainAction] using hdest
    · simp only [hmap, List.mem_map]
      exact ⟨d, Multiset.mem_toList.mpr (Multiset.mem_filter.mpr ⟨hd, hed⟩), rfl⟩

private noncomputable def drainSeq (F : Finset P) (s₀ : State P S M V) :
    ℕ → List (Action P M V) × State P S M V
  | 0 => ([], s₀)
  | k + 1 => π.drainPhase F (drainSeq F s₀ k).2

/-- Every state `s₀` extends to a fair infinite execution in which no new client operations are
invoked and no envelopes addressed to `F` are delivered (`IsDrainAction F`). -/
theorem exists_fair_omegaExecution (F : Finset P) (s₀ : State P S M V) :
    ∃ ss xs, ss 0 = s₀ ∧ π.lts.OmegaExecution ss xs ∧ Fair F ss xs ∧
      ∀ k, IsDrainAction F (xs k) := by
  let ts : ωSequence (State P S M V) := ωSequence.mk fun k => (π.drainSeq F s₀ k).2
  let xls : ωSequence (List (Action P M V)) := (ωSequence.mk fun k => (π.drainSeq F s₀ k).1).tail
  have hseg : ∀ k, π.lts.MTr (ts k) (xls k) (ts (k + 1)) ∧ 0 < (xls k).length ∧
      (∀ a ∈ xls k, IsDrainAction F a) ∧
      (∀ e ∈ (ts k).msgs, e.dest ∉ F → .deliver e ∈ xls k) := fun k => by
    simpa [ts, xls, drainSeq] using π.drainPhase_spec F (π.drainSeq F s₀ k).2
  have hpos : ∀ k, 0 < (xls k).length := fun k => (hseg k).2.1
  have : Inhabited (Action P M V) := ⟨.stutter⟩
  obtain ⟨ss, hexec, hts⟩ := LTS.OmegaExecution.flatten_mTr (fun k => (hseg k).1) hpos
  refine ⟨ss, xls.flatten, ?_, hexec, ?_, ?_⟩
  · simpa [cumLen_zero, ts, drainSeq] using hts 0
  · intro e hdest k he
    by_contra! hnot
    have hk_le : k ≤ xls.cumLen k := (cumLen_strictMono hpos).id_le k
    have hmem_cum : e ∈ (ts k).msgs :=
      hts k ▸ π.omega_notDelivered_mem hexec he hnot (xls.cumLen k) hk_le
    obtain ⟨i, hi, heq⟩ := List.getElem_of_mem ((hseg k).2.2.2 e hmem_cum hdest)
    exact hnot (xls.cumLen k + i) (hk_le.trans (Nat.le_add_right _ _))
      ((flatten_get_add xls hi hpos).trans heq)
  · rw [forall_flatten_iff hpos]
    exact fun k => List.forall_iff_forall_mem.mpr (hseg k).2.2.1

/-- Every reachable state occurs in an `AdmissibleRun F` whose suffix from step `k` onward
performs only `IsDrainAction F` steps. -/
theorem Reachable.exists_admissibleRun [Fintype P] {π : Protocol P S M V}
    (F : Finset P) {s : State P S M V} (hr : π.Reachable s) :
    ∃ ss xs k, π.AdmissibleRun F ss xs ∧ ss k = s ∧
      ∀ j, k ≤ j → IsDrainAction F (xs j) := by
  obtain ⟨xl, hxl⟩ := hr
  obtain ⟨ss', xs', h0, hexec, hfair, hdrain⟩ := π.exists_fair_omegaExecution F s
  obtain ⟨ss, hω, hstart, hat, hdrop⟩ := hexec.append hxl h0
  refine ⟨ss, xl ++ω xs', xl.length, ⟨hstart, hω, ?_⟩, hat, fun j hle => ?_⟩
  · intro e hdest k he
    by_cases hkl : k ≤ xl.length
    · by_cases hdel : .deliver e ∈ (xl ++ω xs').extract k xl.length
      · obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hdel
        have hi' : i < xl.length - k := by simpa [ωSequence.length_extract] using hi
        refine ⟨k + i, Nat.le_add_right k i, ?_⟩
        rw [← (xl ++ω xs').get_extract hi', hget]
      · have he_end : e ∈ (ss xl.length).msgs :=
          π.mTr_notDelivered_mem (hω.extract_mTr hkl) he hdel
        obtain ⟨j, _, hj⟩ := hfair e hdest 0 (by rw [← hdrop, get_drop, add_zero]; exact he_end)
        refine ⟨xl.length + j, hkl.trans (Nat.le_add_right _ _), ?_⟩
        simpa [get_append_right] using hj
    · obtain ⟨j, _, hj⟩ := hfair e hdest (k - xl.length)
        (by simpa [← hdrop, get_drop, Nat.add_sub_cancel' (Nat.le_of_not_le hkl)] using he)
      refine ⟨xl.length + j, by omega, ?_⟩
      simpa [get_append_right] using hj
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    simpa [get_append_right] using hdrain d

/-! ### Wait-free linearizable atomic register specification -/

/-- `π.ImplementsAtomicRegister v₀ t` means `π` emulates a wait-free linearizable (atomic)
multi-writer multi-reader shared register initialized to `v₀`, tolerating up to `t` crash faults
([AttiyaBarNoyDolev1995]):

* **linearizable** (safety / atomicity): every reachable execution history is linearizable from
  initial value `v₀`;
* **terminates** (wait-free liveness): in every fair execution with at most `t` crashed processes
  (`F.card ≤ t`), every operation invoked by a non-faulty process (`caller ∉ F`) eventually
  completes. -/
structure ImplementsAtomicRegister [Fintype P] (v₀ : V) (t : ℕ) : Prop where
  /-- Safety (atomicity): every reachable global state has a linearizable execution history. -/
  linearizable : ∀ s : State P S M V, π.Reachable s → Linearizable v₀ s.history
  /-- Wait-free liveness: every operation invoked by a non-faulty process eventually completes in
  every `t`-fault admissible execution. -/
  terminates : ∀ (F : Finset P), F.card ≤ t →
    ∀ (ss : ωSequence (State P S M V)) (xs : ωSequence (Action P M V)),
    π.AdmissibleRun F ss xs →
    ∀ (k i : ℕ) (hi : i < (ss k).history.length),
    (ss k).history[i].caller ∉ F →
    ∃ (j : ℕ) (hij : i < (ss j).history.length),
      k ≤ j ∧ (ss j).history[i].status.isCompleted = true

/-- Tolerating `t` crash faults implies tolerating at most `t' ≤ t` crash faults. -/
theorem ImplementsAtomicRegister.mono [Fintype P] {π : Protocol P S M V} {v₀ : V} {t t' : ℕ}
    (h : π.ImplementsAtomicRegister v₀ t) (ht : t' ≤ t) :
    π.ImplementsAtomicRegister v₀ t' where
  linearizable := h.linearizable
  terminates F hF := h.terminates F (hF.trans ht)

/-- Linearizability across all reachable states is equivalent to linearizability of every finite
prefix along all `t`-fault admissible infinite executions. -/
theorem linearizable_iff_admissible [Fintype P] (v₀ : V) (t : ℕ) :
    (∀ s : State P S M V, π.Reachable s → Linearizable v₀ s.history) ↔
    (∀ (F : Finset P), F.card ≤ t →
      ∀ (ss : ωSequence (State P S M V)) (xs : ωSequence (Action P M V)),
      π.AdmissibleRun F ss xs → ∀ k, Linearizable v₀ (ss k).history) := by
  constructor
  · intro h F _ ss xs ha k
    exact h (ss k) (π.admissibleRun_reachable ha k)
  · intro h s hr
    obtain ⟨ss, xs, k, ha, hsk, _⟩ := hr.exists_admissibleRun ∅
    exact hsk ▸ h ∅ (Nat.zero_le t) ss xs ha k

end Protocol

/-! ### Zero-message local register baseline (`Fintype.card P ≤ 1`) -/

/-- Single-process local register protocol: each process stores a local value initialized to `v₀`
and completes `read` and `write` invocations immediately in zero messages. When
`Fintype.card P ≤ 1`, no second process exists to observe a divergent copy, so this protocol
implements a wait-free linearizable register against any fault bound `t`. -/
@[expose] def localRegisterProtocol (P V : Type*) (v₀ : V) : Protocol P V PUnit V where
  init _ := v₀
  onInvoke _ cur kind := match kind with
    | .read => ⟨cur, 0, some (.readRet cur)⟩
    | .write v => ⟨v, 0, some .writeAck⟩
  onRecv _ cur _ _ := ⟨cur, 0, none⟩

private def localInv {P V : Type*} (v₀ : V) (s : State P V PUnit V) : Prop :=
  (∀ p : P, (s.proc p).pending = none) ∧
  (∀ (i : ℕ) (hi : i < s.history.length),
    s.history[i].status.isCompleted = true ∧
    s.history[i].status.respStep? = some s.history[i].invStep ∧
    s.history[i].invStep < s.step) ∧
  (∀ (i j : ℕ) (hij : i < j) (hj : j < s.history.length),
    (s.history[i]'(hij.trans hj)).invStep < s.history[j].invStep) ∧
  seqValid v₀ s.history (List.range s.history.length) ∧
  ∀ p : P, (s.proc p).state = registerValAfter v₀ s.history (List.range s.history.length)

private lemma localInv_start {P V : Type*} [Fintype P] (v₀ : V) :
    localInv v₀ (localRegisterProtocol P V v₀).start := by
  refine ⟨fun _ => rfl, ?_, ?_, trivial, fun _ => rfl⟩
  · intro _ hi; simp [Protocol.start] at hi
  · intro _ _ _ hj; simp [Protocol.start] at hj

private lemma localInv_snoc {P V : Type*} {s : State P V PUnit V}
    (hcomp : ∀ (i : ℕ) (hi : i < s.history.length),
      s.history[i].status.isCompleted = true ∧
      s.history[i].status.respStep? = some s.history[i].invStep ∧
      s.history[i].invStep < s.step)
    (hmono : ∀ (i j : ℕ) (hij : i < j) (hj : j < s.history.length),
      (s.history[i]'(hij.trans hj)).invStep < s.history[j].invStep)
    (rec' : OpRecord P V) (hrec_comp : rec'.status.isCompleted = true)
    (hrec_resp : rec'.status.respStep? = some s.step) (hrec_inv : rec'.invStep = s.step) :
    let hist' := s.history ++ [rec']
    (∀ (i : ℕ) (hi : i < hist'.length),
      hist'[i].status.isCompleted = true ∧
      hist'[i].status.respStep? = some hist'[i].invStep ∧
      hist'[i].invStep < s.step + 1) ∧
    (∀ (i j : ℕ) (hij : i < j) (hj : j < hist'.length),
      (hist'[i]'(hij.trans hj)).invStep < hist'[j].invStep) := by
  intro hist'
  refine ⟨fun i hi => ?_, fun i j hij hj => ?_⟩
  · by_cases hlt : i < s.history.length
    · simp only [hist', List.getElem_append_left hlt]
      exact ⟨(hcomp i hlt).1, (hcomp i hlt).2.1, Nat.lt_succ_of_lt (hcomp i hlt).2.2⟩
    · obtain rfl : i = s.history.length := by simp [hist'] at hi; omega
      simp only [hist', List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
      exact ⟨hrec_comp, hrec_resp.trans (congrArg some hrec_inv.symm), by omega⟩
  · by_cases hjl : j < s.history.length
    · simp only [hist', List.getElem_append_left (hij.trans hjl), List.getElem_append_left hjl]
      exact hmono i j hij hjl
    · obtain rfl : j = s.history.length := by simp [hist'] at hj; omega
      simp only [hist', List.getElem_append_left hij, List.getElem_append_right le_rfl,
        Nat.sub_self, List.getElem_singleton, hrec_inv]
      exact (hcomp i hij).2.2

private lemma localInv_tr {P V : Type*} [Fintype P] [DecidableEq P]
    (hcard : Fintype.card P ≤ 1) (v₀ : V) :
    (localRegisterProtocol P V v₀).lts.TrInv (localInv v₀) := by
  have hsub : Subsingleton P := Fintype.card_le_one_iff_subsingleton.mp hcard
  intro s a s' htr ⟨hpend, hcomp, hmono, hvalid, hstate⟩
  cases a with
  | stutter =>
    obtain rfl := htr
    exact ⟨hpend, hcomp, hmono, hvalid, hstate⟩
  | deliver e =>
    obtain ⟨_, rfl⟩ := htr
    rw [(localRegisterProtocol P V v₀).doDeliver_of_resp_eq_none rfl]
    have hproc_eq : Function.update s.proc e.dest
        ⟨(s.proc e.dest).state, (s.proc e.dest).pending⟩ = s.proc :=
      Function.update_eq_self e.dest s.proc
    refine ⟨fun p => hproc_eq.symm ▸ hpend p, fun i hi => ?_, hmono, hvalid,
      fun p => hproc_eq.symm ▸ hstate p⟩
    obtain ⟨hc, hr, hlt⟩ := hcomp i hi
    exact ⟨hc, hr, Nat.lt_succ_of_lt hlt⟩
  | invoke caller kind =>
    obtain ⟨_, rfl⟩ := htr
    let nextVal : V := match kind with
      | .read => (s.proc caller).state
      | .write v => v
    let stDone : OpStatus V := match kind with
      | .read => .doneRead s.step (s.proc caller).state
      | .write _ => .doneWrite s.step
    let rec' : OpRecord P V := ⟨caller, kind, s.step, stDone⟩
    have hhist : ((localRegisterProtocol P V v₀).doInvoke caller kind s).history =
        s.history ++ [rec'] := by cases kind <;> rfl
    have hproc : ((localRegisterProtocol P V v₀).doInvoke caller kind s).proc =
        Function.update s.proc caller ⟨nextVal, none⟩ := by cases kind <;> rfl
    obtain ⟨hcomp', hmono'⟩ := localInv_snoc hcomp hmono rec'
      (by cases kind <;> rfl) (by cases kind <;> rfl) rfl
    have hval_eq : registerValAfter v₀ (s.history ++ [rec']) (List.range s.history.length) =
        registerValAfter v₀ s.history (List.range s.history.length) :=
      registerValAfter_append_hist v₀ s.history [rec'] fun _ hx => List.mem_range.mp hx
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p
      rw [hproc, Subsingleton.elim p caller, Function.update_self]
    · change ∀ (i : ℕ)
          (hi : i < ((localRegisterProtocol P V v₀).doInvoke caller kind s).history.length),
        _ ∧ _ ∧ _ < s.step + 1
      simpa only [hhist] using hcomp'
    · simpa only [hhist] using hmono'
    · rw [hhist]
      simp only [List.length_append, List.length_singleton, List.range_succ]
      apply seqValid_append v₀ (s.history ++ [rec']) (List.range s.history.length)
        [s.history.length] (seqValid_append_hist v₀ s.history [rec'] hvalid)
      rw [hval_eq, ← hstate caller]
      refine ⟨by simp, ?_⟩
      cases kind <;> simp [rec', stDone, seqValid]
    · intro p
      rcases Subsingleton.elim p caller with rfl
      simp only [hproc, hhist, Function.update_self, List.length_append, List.length_singleton,
        List.range_succ, registerValAfter_append, hval_eq, ← hstate p]
      cases kind <;> simp [registerValAfter_cons, rec', nextVal]

/-- When `Fintype.card P ≤ 1`, `localRegisterProtocol` implements a wait-free linearizable atomic
register for *any* fault bound `t`. -/
theorem implementsAtomicRegister_local_of_card_le_one {P V : Type*} [Fintype P] [DecidableEq P]
    (hcard : Fintype.card P ≤ 1) (v₀ : V) (t : ℕ) :
    (localRegisterProtocol P V v₀).ImplementsAtomicRegister v₀ t where
  linearizable s hr := by
    obtain ⟨xl, hxl⟩ := hr
    obtain ⟨_, hcomp, hmono, hvalid, _⟩ :=
      LTS.mtrInv_of_trInv (localInv_tr hcard v₀) _ _ _ hxl (localInv_start v₀)
    refine ⟨List.range s.history.length, List.nodup_range, fun i hi _ => List.mem_range.mpr hi,
      ?_, hvalid⟩
    · intro i hi j hj ⟨hi_lt, hj_lt, r, hr_step, hlt⟩
      have hidx {k : ℕ} (hk : k < s.history.length) :
          (List.range s.history.length).idxOf k = k := by
        have hlen : k < (List.range s.history.length).length := by simpa using hk
        simpa [List.getElem_range hlen] using List.Nodup.idxOf_getElem List.nodup_range k hlen
      rw [hidx hi_lt, hidx hj_lt]
      obtain ⟨_, hr', _⟩ := hcomp i hi_lt
      cases hr'.symm.trans hr_step
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact hij
      · exact False.elim (Nat.lt_irrefl _ hlt)
      · exact False.elim (Nat.lt_asymm hlt (hmono j i hji hi_lt))
  terminates _ _ ss xs ha k i hi _ := by
    obtain ⟨xl, hxl⟩ := (localRegisterProtocol P V v₀).admissibleRun_reachable ha k
    have hinv := LTS.mtrInv_of_trInv (localInv_tr hcard v₀) _ _ _ hxl (localInv_start v₀)
    exact ⟨k, hi, le_rfl, (hinv.2.1 i hi).1⟩

end Cslib.Distributed.ABD
