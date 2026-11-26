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
import CslibFrontier.Tactic.FinsetCard
import Mathlib.Data.Multiset.Filter

/-!
# Asynchronous authenticated Byzantine message passing and reliable broadcast

This module models deterministic asynchronous point-to-point message passing with static Byzantine
faults and authenticated sender channels, following [Bracha1987] and [BrachaToueg1985]. It is the
asynchronous Byzantine counterpart to `Cslib.FLP` (asynchronous crash faults) and
`Cslib.Distributed.Byzantine` (synchronous Byzantine agreement).

A message on the network is an `Envelope P M` carrying its sender `src`, recipient `dest`, and
payload `body`. Given a distinguished broadcaster `dealer : P`, a `Protocol P S M V dealer` assigns:

* initial states `init` for non-dealer processes (independent of the dealer's input) and
  `initDealer` for `dealer` (depending on `input : Option V`),
* initial outgoing messages `initMsgs` for non-dealer processes and `initDealerMsgs` for `dealer`,
* deterministic transitions `next`, `send`, and `out` upon receiving a payload from `src`.

For a static set `F : Finset P` of faulty processes, `s.msgs : Multiset (Envelope P M)` holds all
in-flight messages sent by *correct* processes (`e.src ∉ F`). The labelled transition system
`π.lts F` allows three kinds of actions (`Action P M`):

* `Action.deliver e`: deliver an in-flight authentic envelope `e ∈ s.msgs` to a correct process
  `e.dest ∉ F`, erasing one copy of `e` from `s.msgs`.
* `Action.byzRecv src dest body`: let a faulty process `src ∈ F` deliver an arbitrary message
  `body` to a correct process `dest ∉ F`. Since transitions may fire in any order given the full
  global state, this covers adaptive/rushing adversaries, equivocation, replays, and
  silence/crashes.
* `Action.stutter`: a dummy stuttering step leaving the global state unchanged (following
  `Cslib.FLP`), so finite or quiescent runs always extend to infinite executions.

Every process's delivery field `out : Option V` is write-once: once a correct process decides
`some v`, later transitions leave `out` unchanged (`procDecided_stable`). Because point-to-point
channels are authenticated, no Byzantine action can forge a message whose `src ∉ F`
(`Reachable.msgs_src_notMem`).

An infinite execution is *fair* (`Fair F ss xs`) if every authentic in-flight message addressed to
a correct process is eventually delivered. `Protocol.exists_fair_omegaExecution` shows every
global state extends to a fair Byzantine-free infinite execution by draining the pending authentic
multiset round-by-round via `Cslib.LTS.OmegaExecution.flatten_mTr`.

`Protocol.SolvesReliableBroadcast t` specifies single-sender Byzantine reliable broadcast
(consistency/agreement, honest-sender integrity/no-spurious-delivery, validity, and totality)
against at most `t` faulty processes. `directProtocol` witnesses both the fault-free case (`t = 0`)
and every process set of size at most `2`.

## Main definitions

* `Cslib.Distributed.AsyncByzantine.Envelope`: authenticated point-to-point message envelope.
* `Cslib.Distributed.AsyncByzantine.ProcState`: local state paired with a write-once `Option V`
  delivery register.
* `Cslib.Distributed.AsyncByzantine.State`: global configuration (authentic in-flight multiset and
  process states).
* `Cslib.Distributed.AsyncByzantine.Action`: LTS transition label (`deliver`, `byzRecv`, `stutter`).
* `Cslib.Distributed.AsyncByzantine.broadcastAll`: multiset broadcasting one payload to every
  process in `P`.
* `Cslib.Distributed.AsyncByzantine.Protocol`: deterministic asynchronous protocol with
  distinguished broadcaster `dealer`.
* `Cslib.Distributed.AsyncByzantine.Protocol.lts`: LTS parameterized by the static faulty set `F`.
* `Cslib.Distributed.AsyncByzantine.Protocol.Fair`: eventual delivery of every authentic message to
  every correct process.
* `Cslib.Distributed.AsyncByzantine.Protocol.AdmissibleRun`: fair infinite execution starting from
  `start F input`.
* `Cslib.Distributed.AsyncByzantine.Protocol.traceSent`,
  `Cslib.Distributed.AsyncByzantine.Protocol.sentInTrace`: authentic messages emitted by correct
  processes along a finite execution trace.
* `Cslib.Distributed.AsyncByzantine.Protocol.SolvesReliableBroadcast`: Byzantine reliable broadcast
  specification against at most `t` faults.
* `Cslib.Distributed.AsyncByzantine.directProtocol`: direct single-hop broadcast protocol.

## Main results

* `Cslib.Distributed.AsyncByzantine.Protocol.procDecided_stable`: write-once delivery is monotone
  under reachability.
* `Cslib.Distributed.AsyncByzantine.Protocol.Reachable.msgs_src_notMem`: every in-flight message
  in a reachable state originates from a correct process.
* `Cslib.Distributed.AsyncByzantine.Protocol.mTr_notDelivered_mem`,
  `Cslib.Distributed.AsyncByzantine.Protocol.omega_notDelivered_mem`: undelivered in-flight
  messages remain in the network multiset.
* `Cslib.Distributed.AsyncByzantine.Protocol.card_msgs_add_traceSent`: exact message-conservation
  identity linking `traceSent`, remaining `msgs`, and completed deliveries.
* `Cslib.Distributed.AsyncByzantine.Protocol.exists_fair_omegaExecution`: any state extends to a
  fair Byzantine-free infinite execution.
* `Cslib.Distributed.AsyncByzantine.Protocol.Reachable.exists_admissibleRun`: every reachable
  state extends via an honest fair suffix to an admissible infinite execution.
* `Cslib.Distributed.AsyncByzantine.Protocol.consistency_iff_admissible`: equivalence between
  reachable-state and admissible-run consistency.
* `Cslib.Distributed.AsyncByzantine.solvesReliableBroadcast_direct_of_zero`: `directProtocol`
  solves reliable broadcast against `0` faults for every `P`.
* `Cslib.Distributed.AsyncByzantine.solvesReliableBroadcast_direct_of_card_le_two`: `directProtocol`
  solves reliable broadcast against any `t` faults when `Fintype.card P ≤ 2`.

## References

* [G. Bracha, *Asynchronous Byzantine agreement protocols*][Bracha1987]
* [G. Bracha, S. Toueg, *Asynchronous consensus and broadcast protocols*][BrachaToueg1985]
-/

public section

namespace Cslib.Distributed.AsyncByzantine

open Cslib Cslib.ωSequence

/-- An authenticated message envelope in transit from `src` to `dest` carrying payload `body`. -/
@[ext]
structure Envelope (P M : Type*) where
  /-- Sender process identity, authenticated by the point-to-point channel. -/
  src : P
  /-- Destination process identity. -/
  dest : P
  /-- Message payload. -/
  body : M
  deriving @[expose] DecidableEq

/-- Tag a `(dest, body)` pair emitted by sender `src` as an `Envelope`. -/
@[expose] def tagSender {P M : Type*} (src : P) (destBody : P × M) : Envelope P M :=
  ⟨src, destBody.1, destBody.2⟩

@[simp]
theorem tagSender_src {P M : Type*} (src : P) (destBody : P × M) :
    (tagSender src destBody).src = src := rfl

@[simp]
theorem tagSender_dest {P M : Type*} (src : P) (destBody : P × M) :
    (tagSender src destBody).dest = destBody.1 := rfl

@[simp]
theorem tagSender_body {P M : Type*} (src : P) (destBody : P × M) :
    (tagSender src destBody).body = destBody.2 := rfl

/-- Broadcast payload `m` to every process `q : P` (including the sender itself). -/
@[expose] def broadcastAll (P : Type*) {M : Type*} [Fintype P] (m : M) : Multiset (P × M) :=
  Finset.univ.val.map fun q => (q, m)

@[simp]
theorem card_broadcastAll {P M : Type*} [Fintype P] (m : M) :
    (broadcastAll P m).card = Fintype.card P := by
  simp [broadcastAll]

theorem mem_broadcastAll_tag {P M : Type*} [Fintype P] (src q : P) (m : M) :
    ⟨src, q, m⟩ ∈ (broadcastAll P m).map (tagSender src) :=
  Multiset.mem_map.mpr ⟨(q, m), Multiset.mem_map.mpr ⟨q, Finset.mem_univ q, rfl⟩, rfl⟩

/-- Local state of a process paired with its write-once delivery register `out`. -/
@[ext]
structure ProcState (S V : Type*) where
  /-- Internal local state. -/
  state : S
  /-- Delivered output value (`none` if no value has been delivered yet). -/
  out : Option V
  deriving @[expose] DecidableEq

/-- Global configuration of an asynchronous authenticated Byzantine network. -/
@[ext]
structure State (P S M V : Type*) where
  /-- Multiset of authentic in-flight messages (`src ∉ F`). Messages are unordered. -/
  msgs : Multiset (Envelope P M)
  /-- Local state of every process. Only entries for `p ∉ F` represent correct processes. -/
  proc : P → ProcState S V

/-- Process `p` has delivered value `v` in global state `s`. -/
abbrev State.ProcDecided {P S M V : Type*} (s : State P S M V) (p : P) (v : V) : Prop :=
  (s.proc p).out = some v

/-- Transition label for the asynchronous Byzantine LTS. -/
inductive Action (P M : Type*) where
  /-- Deliver an authentic in-flight envelope `e` to its correct recipient `e.dest`. -/
  | deliver (e : Envelope P M)
  /-- Deliver an arbitrary message `body` sent by a faulty process `src ∈ F` to a correct
  recipient `dest ∉ F`. -/
  | byzRecv (src dest : P) (body : M)
  /-- Stuttering step leaving the global state unchanged. -/
  | stutter
  deriving @[expose] DecidableEq

/-- Boolean predicate checking whether an action is an authentic delivery `.deliver _`. -/
@[expose] def Action.isDeliver {P M : Type*} : Action P M → Bool
  | .deliver _ => true
  | .byzRecv _ _ _ => false
  | .stutter => false

/-- `a.IsHonest` holds when `a` is not a Byzantine message injection. -/
@[expose] def Action.IsHonest {P M : Type*} : Action P M → Prop
  | .deliver _ => True
  | .byzRecv _ _ _ => False
  | .stutter => True

@[simp]
theorem Action.isHonest_deliver {P M : Type*} (e : Envelope P M) :
    (Action.deliver e).IsHonest := trivial

@[simp]
theorem Action.isHonest_stutter {P M : Type*} :
    (Action.stutter (P := P) (M := M)).IsHonest := trivial

@[simp]
theorem Action.not_isHonest_byzRecv {P M : Type*} (src dest : P) (body : M) :
    ¬ (Action.byzRecv src dest body).IsHonest := id

/-- A deterministic asynchronous authenticated message-passing protocol with a distinguished
broadcaster `dealer : P`.

Non-dealer initial states and messages cannot depend on the broadcaster's input `Option V`. When
a correct process `p` in local state `st` receives `body` from `src`, it moves to internal state
`next p st src body`, sends outgoing messages `send p st src body`, and optionally delivers
`out p st src body` if it has not already delivered a value. -/
structure Protocol (P S M V : Type*) (dealer : P) where
  /-- Initial internal state of a non-dealer process `p ≠ dealer`. -/
  init : P → S
  /-- Initial internal state of `dealer` given `input : Option V`. -/
  initDealer : Option V → S
  /-- Initial messages emitted by a non-dealer process `p ≠ dealer`. -/
  initMsgs : P → Multiset (P × M)
  /-- Initial messages emitted by `dealer` given `input : Option V`. -/
  initDealerMsgs : Option V → Multiset (P × M)
  /-- State update when process `dest` receives `body` from `src`. -/
  next : P → ProcState S V → P → M → S
  /-- Outgoing messages `(q, m)` emitted when process `dest` receives `body` from `src`. -/
  send : P → ProcState S V → P → M → Multiset (P × M)
  /-- Value delivered (`some v`) when process `dest` receives `body` from `src`. Write-once
  semantics are enforced by `recvCore`. -/
  out : P → ProcState S V → P → M → Option V

namespace Protocol

variable {P S M V : Type*} {dealer : P} [DecidableEq P] [DecidableEq M]
  (π : Protocol P S M V dealer)

/-- Initial internal state of process `p` given dealer input `input`. -/
@[expose] def initState (input : Option V) (p : P) : S :=
  if p = dealer then π.initDealer input else π.init p

/-- Initial outgoing `(dest, body)` multiset emitted by process `p` given dealer input `input`. -/
@[expose] def initSend (input : Option V) (p : P) : Multiset (P × M) :=
  if p = dealer then π.initDealerMsgs input else π.initMsgs p

/-- The initial global state for a static faulty set `F` and dealer input `input : Option V`.
Only correct processes (`p ∉ F`) contribute authentic messages to the initial network multiset;
faulty processes inject messages arbitrarily via `Action.byzRecv`. -/
@[expose] def start [Fintype P] (F : Finset P) (input : Option V) : State P S M V where
  msgs := Finset.univ.val.bind fun p =>
    if p ∈ F then 0 else (π.initSend input p).map (tagSender p)
  proc p := ⟨π.initState input p, none⟩

/-- Local state update shared by authentic and Byzantine message deliveries; once `out` becomes
`some v`, it never changes. -/
@[expose] def updateProc (dest : P) (src : P) (body : M) (st : ProcState S V) : ProcState S V :=
  ⟨π.next dest st src body, if st.out.isNone then π.out dest st src body else st.out⟩

/-- Core global transition shared by authentic delivery (`recvHonest`) and Byzantine injection
(`recvByz`), differing only in whether an envelope is erased from `s.msgs`. -/
@[expose] def recvCore (src dest : P) (body : M) (msgsBase : Multiset (Envelope P M))
    (s : State P S M V) : State P S M V where
  msgs := msgsBase + (π.send dest (s.proc dest) src body).map (tagSender dest)
  proc q := if q = dest then π.updateProc dest src body (s.proc dest) else s.proc q

/-- State resulting from delivering authentic in-flight envelope `e` to `e.dest`. -/
@[expose] def recvHonest (e : Envelope P M) (s : State P S M V) : State P S M V :=
  π.recvCore e.src e.dest e.body (s.msgs.erase e) s

/-- State resulting from delivering an adversary-injected message `(src, body)` to `dest`. -/
@[expose] def recvByz (src dest : P) (body : M) (s : State P S M V) : State P S M V :=
  π.recvCore src dest body s.msgs s

/-- Labelled transition system of `π` for a fixed static set `F` of Byzantine processes. -/
@[expose] def lts (F : Finset P) : LTS (State P S M V) (Action P M) where
  Tr s a s' := match a with
    | .deliver e => e ∈ s.msgs ∧ e.dest ∉ F ∧ s' = π.recvHonest e s
    | .byzRecv src dest body => src ∈ F ∧ dest ∉ F ∧ s' = π.recvByz src dest body s
    | .stutter => s' = s

/-- `π.Reachable F input s` means `s` is reachable from `π.start F input` under `π.lts F`. -/
@[expose] def Reachable [Fintype P] (F : Finset P) (input : Option V) (s : State P S M V) : Prop :=
  (π.lts F).CanReach (π.start F input) s

/-! ### Basic transition lemmas -/

theorem reachable_start [Fintype P] (F : Finset P) (input : Option V) :
    π.Reachable F input (π.start F input) :=
  LTS.CanReach.refl (π.lts F) (π.start F input)

theorem Reachable.trans [Fintype P] {π : Protocol P S M V dealer} {F : Finset P} {input : Option V}
    {s s' : State P S M V} (hs : π.Reachable F input s) (hreach : (π.lts F).CanReach s s') :
    π.Reachable F input s' := by
  obtain ⟨xl, hxl⟩ := hs
  obtain ⟨yl, hyl⟩ := hreach
  exact ⟨xl ++ yl, LTS.MTr.comp (π.lts F) hxl hyl⟩

omit [DecidableEq P] [DecidableEq M] in
theorem updateProc_out_eq_some {src dest : P} {body : M} {st : ProcState S V} {v : V}
    (hv : st.out = some v) : (π.updateProc dest src body st).out = some v := by
  simp only [updateProc, hv, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]

private lemma tr_procDecided_stable {F : Finset P} {s s' : State P S M V} {a : Action P M}
    {p : P} {v : V} (hd : s.ProcDecided p v) (htr : (π.lts F).Tr s a s') :
    s'.ProcDecided p v := by
  cases a with
  | stutter => obtain rfl := htr; exact hd
  | _ =>
    obtain ⟨_, _, rfl⟩ := htr
    simp only [State.ProcDecided, recvHonest, recvByz, recvCore]
    split_ifs with hp
    · subst hp; exact π.updateProc_out_eq_some hd
    · exact hd

/-- Once a process delivers `v`, its delivery register remains `some v` in every later state. -/
theorem procDecided_stable {F : Finset P} {s s' : State P S M V} {p : P} {v : V}
    (hd : s.ProcDecided p v) (hreach : (π.lts F).CanReach s s') : s'.ProcDecided p v := by
  obtain ⟨xl, hxl⟩ := hreach
  induction hxl with
  | refl => exact hd
  | stepL htr _ ih => exact ih (π.tr_procDecided_stable hd htr)

theorem omega_procDecided_stable {F : Finset P} {ss : ωSequence (State P S M V)}
    {xs : ωSequence (Action P M)} (he : (π.lts F).OmegaExecution ss xs)
    {k j : ℕ} (hkj : k ≤ j) {p : P} {v : V} (hd : (ss k).ProcDecided p v) :
    (ss j).ProcDecided p v :=
  π.procDecided_stable hd ⟨xs.extract k j, he.extract_mTr hkj⟩

omit [DecidableEq M] in
/-- Every envelope present in the initial multiset of `π.start F input` originates from a correct
process. -/
theorem start_msgs_src_notMem [Fintype P] (F : Finset P) (input : Option V)
    {e : Envelope P M} (he : e ∈ (π.start F input).msgs) : e.src ∉ F := by
  obtain ⟨p, -, hp⟩ := Multiset.mem_bind.mp he
  split_ifs at hp with hpF
  · simp at hp
  · obtain ⟨qm, _, rfl⟩ := Multiset.mem_map.mp hp
    exact hpF

private lemma tr_msgs_src_notMem {F : Finset P} {s s' : State P S M V} {a : Action P M}
    (hs : ∀ e ∈ s.msgs, e.src ∉ F) (htr : (π.lts F).Tr s a s') :
    ∀ e ∈ s'.msgs, e.src ∉ F := by
  intro e he
  cases a with
  | deliver m =>
    obtain ⟨_, hdest, rfl⟩ := htr
    simp only [recvHonest, recvCore, Multiset.mem_add, Multiset.mem_map] at he
    rcases he with he | ⟨qm, _, rfl⟩
    exacts [hs e (Multiset.mem_of_mem_erase he), hdest]
  | byzRecv src dest body =>
    obtain ⟨_, hdest, rfl⟩ := htr
    simp only [recvByz, recvCore, Multiset.mem_add, Multiset.mem_map] at he
    rcases he with he | ⟨qm, _, rfl⟩
    exacts [hs e he, hdest]
  | stutter => obtain rfl := htr; exact hs e he

/-- In any reachable global state, every envelope in `s.msgs` originates from a correct process. -/
theorem Reachable.msgs_src_notMem [Fintype P] {π : Protocol P S M V dealer}
    {F : Finset P} {input : Option V} {s : State P S M V} (hr : π.Reachable F input s)
    {e : Envelope P M} (he : e ∈ s.msgs) : e.src ∉ F := by
  obtain ⟨xl, hxl⟩ := hr
  exact LTS.mtrInv_of_trInv (lts := π.lts F) (fun _ _ _ htr hs => π.tr_msgs_src_notMem hs htr)
    _ _ _ hxl (fun _ => π.start_msgs_src_notMem F input) e he

/-- An in-flight message `e` stays in `msgs` across any transition other than `.deliver e`. -/
theorem tr_notDelivered_mem {F : Finset P} {s s' : State P S M V} {a : Action P M}
    {e : Envelope P M} (he : e ∈ s.msgs) (ha : a ≠ .deliver e)
    (htr : (π.lts F).Tr s a s') : e ∈ s'.msgs := by
  cases a with
  | deliver m =>
    obtain ⟨_, _, rfl⟩ := htr
    exact Multiset.mem_add.mpr (.inl ((Multiset.mem_erase_of_ne fun h => ha (by rw [h])).mpr he))
  | byzRecv src dest body => obtain ⟨_, _, rfl⟩ := htr; exact Multiset.mem_add.mpr (.inl he)
  | stutter => obtain rfl := htr; exact he

/-- An in-flight message `e` stays in `msgs` across any finite trace not containing `.deliver e`. -/
theorem mTr_notDelivered_mem {F : Finset P} {s t : State P S M V} {xl : List (Action P M)}
    {e : Envelope P M} (h : (π.lts F).MTr s xl t) (he : e ∈ s.msgs)
    (hnot : .deliver e ∉ xl) : e ∈ t.msgs := by
  induction h with
  | refl => exact he
  | stepL htr _ ih =>
    exact ih (π.tr_notDelivered_mem he (fun hx => hnot (by simp [hx])) htr)
      (hnot ∘ List.mem_cons_of_mem _)

/-- An in-flight message `e` stays in `msgs` across an infinite execution as long as `.deliver e`
never occurs. -/
theorem omega_notDelivered_mem {F : Finset P} {ss : ωSequence (State P S M V)}
    {xs : ωSequence (Action P M)} (hexec : (π.lts F).OmegaExecution ss xs)
    {k : ℕ} {e : Envelope P M} (he : e ∈ (ss k).msgs)
    (hnot : ∀ j, k ≤ j → xs j ≠ .deliver e) :
    ∀ j, k ≤ j → e ∈ (ss j).msgs := by
  intro j hkj
  induction j, hkj using Nat.le_induction with
  | base => exact he
  | succ j hkj ih => exact π.tr_notDelivered_mem ih (hnot j hkj) (hexec j)

omit [DecidableEq P] [DecidableEq M] in
/-- Fairness: every authentic in-flight envelope addressed to a correct process is eventually
delivered. -/
@[expose] def Fair (F : Finset P) (ss : ωSequence (State P S M V))
    (xs : ωSequence (Action P M)) : Prop :=
  ∀ e : Envelope P M, e.dest ∉ F → ∀ k, e ∈ (ss k).msgs → ∃ j, k ≤ j ∧ xs j = .deliver e

/-- An admissible infinite execution of `π` for static faulty set `F` and dealer input `input`. -/
@[expose] def AdmissibleRun [Fintype P] (F : Finset P) (input : Option V)
    (ss : ωSequence (State P S M V)) (xs : ωSequence (Action P M)) : Prop :=
  ss 0 = π.start F input ∧ (π.lts F).OmegaExecution ss xs ∧ Fair F ss xs

/-- Every state appearing in an admissible infinite execution is reachable from
`π.start F input`. -/
theorem admissibleRun_reachable [Fintype P] {F : Finset P} {input : Option V}
    {ss : ωSequence (State P S M V)} {xs : ωSequence (Action P M)}
    (ha : π.AdmissibleRun F input ss xs) (k : ℕ) : π.Reachable F input (ss k) :=
  ⟨xs.extract 0 k, ha.1 ▸ ha.2.1.extract_mTr (Nat.zero_le k)⟩

/-! ### Fair Byzantine-free scheduler -/

/-- Deliver a list of pending authentic envelopes in sequence from state `s`. -/
private def drainList (s : State P S M V) :
    List (Envelope P M) → List (Action P M) × State P S M V
  | [] => ([], s)
  | e :: es =>
    let r := drainList (π.recvHonest e s) es
    (.deliver e :: r.1, r.2)

private lemma drainList_spec {F : Finset P} (s : State P S M V) (es : List (Envelope P M))
    (hle : Multiset.ofList es ≤ s.msgs) (hdest : ∀ e ∈ es, e.dest ∉ F) :
    (π.lts F).MTr s (π.drainList s es).1 (π.drainList s es).2 ∧
    (π.drainList s es).1 = es.map Action.deliver := by
  induction es generalizing s with
  | nil =>
    exact ⟨LTS.MTr.refl, rfl⟩
  | cons e es ih =>
    have hes : Multiset.ofList es ≤ s.msgs.erase e := by
      simpa using Multiset.erase_le_erase e hle
    obtain ⟨hmtr, hmap⟩ := ih (π.recvHonest e s) (hes.trans (Multiset.le_add_right _ _))
      (fun x hx => hdest x (List.mem_cons_of_mem e hx))
    exact ⟨.stepL ⟨Multiset.mem_of_le hle (by simp), hdest e List.mem_cons_self, rfl⟩ hmtr,
      by simp only [drainList, hmap, List.map_cons]⟩

/-- One draining phase: deliver all envelopes currently in `s.msgs` addressed to `Fᶜ`, or stutter
if none are pending. -/
private noncomputable def drainPhase (F : Finset P) (s : State P S M V) :
    List (Action P M) × State P S M V :=
  let pending := s.msgs.filter (fun e => e.dest ∉ F)
  if pending = 0 then ([.stutter], s) else π.drainList s pending.toList

private lemma drainPhase_spec (F : Finset P) (s : State P S M V) :
    let res := π.drainPhase F s
    (π.lts F).MTr s res.1 res.2 ∧ 0 < res.1.length ∧
    (∀ a ∈ res.1, a.IsHonest) ∧
    (∀ e ∈ s.msgs, e.dest ∉ F → .deliver e ∈ res.1) := by
  dsimp only [drainPhase]
  set pending := s.msgs.filter (fun e => e.dest ∉ F)
  by_cases h0 : pending = 0
  · simp only [h0, ↓reduceIte, List.length_singleton, zero_lt_one, true_and]
    exact ⟨LTS.MTr.single (π.lts F) (show (π.lts F).Tr s Action.stutter s from rfl),
      fun a ha => by obtain rfl := List.mem_singleton.mp ha; trivial,
      fun e he hdest => (Multiset.filter_eq_nil.mp h0 e he hdest).elim⟩
  · simp only [h0, ↓reduceIte]
    obtain ⟨hmtr, hmap⟩ := π.drainList_spec s pending.toList
      (by rw [Multiset.coe_toList]; exact Multiset.filter_le _ _)
      (fun e he => (Multiset.mem_filter.mp (Multiset.mem_toList.mp he)).2)
    rw [hmap] at hmtr ⊢
    refine ⟨hmtr, ?_, fun a ha => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha; trivial,
      fun e he hed => List.mem_map.mpr
        ⟨e, Multiset.mem_toList.mpr (Multiset.mem_filter.mpr ⟨he, hed⟩), rfl⟩⟩
    obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero h0
    rw [List.length_map]; exact List.length_pos_of_mem (Multiset.mem_toList.mpr he)

private noncomputable def drainSeq (F : Finset P) (s₀ : State P S M V) :
    ℕ → List (Action P M) × State P S M V
  | 0 => ([], s₀)
  | k + 1 => π.drainPhase F (drainSeq F s₀ k).2

/-- Every global state `s₀` extends to a fair, Byzantine-free infinite execution of `π.lts F`.
All actions in the extension are either authentic deliveries `.deliver e` or `.stutter`. -/
theorem exists_fair_omegaExecution (F : Finset P) (s₀ : State P S M V) :
    ∃ ss xs, ss 0 = s₀ ∧ (π.lts F).OmegaExecution ss xs ∧ Fair F ss xs ∧
      ∀ k, (xs k).IsHonest := by
  let ts : ωSequence (State P S M V) := ωSequence.mk fun k => (π.drainSeq F s₀ k).2
  let xls : ωSequence (List (Action P M)) := (ωSequence.mk fun k => (π.drainSeq F s₀ k).1).tail
  have hseg (k : ℕ) : (π.lts F).MTr (ts k) (xls k) (ts (k + 1)) ∧ 0 < (xls k).length ∧
      (∀ a ∈ xls k, a.IsHonest) ∧ (∀ e ∈ (ts k).msgs, e.dest ∉ F → .deliver e ∈ xls k) := by
    simpa [ts, xls, drainSeq] using π.drainPhase_spec F (π.drainSeq F s₀ k).2
  have hpos : ∀ k, 0 < (xls k).length := fun k => (hseg k).2.1
  have : Inhabited (Action P M) := ⟨.stutter⟩
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
      (by rw [flatten_get_add xls hi hpos, heq])
  · rw [forall_flatten_iff hpos]
    exact fun k => List.forall_iff_forall_mem.mpr (hseg k).2.2.1

/-- Every initial state admits a fair, Byzantine-free infinite execution. -/
theorem exists_honest_admissibleRun [Fintype P] (F : Finset P) (input : Option V) :
    ∃ ss xs, π.AdmissibleRun F input ss xs ∧ ∀ k, (xs k).IsHonest := by
  obtain ⟨ss, xs, h0, hexec, hfair, hhon⟩ := π.exists_fair_omegaExecution F (π.start F input)
  exact ⟨ss, xs, ⟨h0, hexec, hfair⟩, hhon⟩

/-- Every reachable state occurs in some admissible infinite execution whose suffix from `k`
onward is Byzantine-free. -/
theorem Reachable.exists_admissibleRun [Fintype P] {π : Protocol P S M V dealer}
    {F : Finset P} {input : Option V} {s : State P S M V} (hr : π.Reachable F input s) :
    ∃ ss xs k, π.AdmissibleRun F input ss xs ∧ ss k = s ∧
      ∀ j, k ≤ j → (xs j).IsHonest := by
  obtain ⟨xl, hxl⟩ := hr
  obtain ⟨ss', xs', h0, hexec, hfair, hhon⟩ := π.exists_fair_omegaExecution F s
  obtain ⟨ss, hω, hstart, hat, hdrop⟩ := hexec.append hxl h0
  have hss' (n : ℕ) : ss (xl.length + n) = ss' n := by rw [← hdrop, get_drop]
  refine ⟨ss, xl ++ω xs', xl.length, ⟨hstart, hω, ?_⟩, hat, fun j hle => ?_⟩
  · intro e hdest k he
    by_cases hkl : k ≤ xl.length
    · by_cases hdel : .deliver e ∈ (xl ++ω xs').extract k xl.length
      · obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hdel
        have hi' : i < xl.length - k := by simpa [ωSequence.length_extract] using hi
        exact ⟨k + i, Nat.le_add_right k i, by rw [← (xl ++ω xs').get_extract hi', hget]⟩
      · obtain ⟨j, _, hj⟩ := hfair e hdest 0
          (hss' 0 ▸ π.mTr_notDelivered_mem (hω.extract_mTr hkl) he hdel)
        exact ⟨xl.length + j, by omega, by simpa [get_append_right] using hj⟩
    · obtain ⟨j, hkj, hj⟩ := hfair e hdest (k - xl.length)
        (by rwa [← hss', Nat.add_sub_cancel' (by omega)])
      exact ⟨xl.length + j, by omega, by simpa [get_append_right] using hj⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    simpa [get_append_right] using hhon d

/-! ### Authentic message-complexity accounting -/

/-- Total authentic envelopes emitted by correct processes along a finite trace `xl` starting at
state `s` (excluding messages already present in `s.msgs`). -/
@[expose] def traceSent (s : State P S M V) : List (Action P M) → ℕ
  | [] => 0
  | .deliver e :: xl =>
    (π.send e.dest (s.proc e.dest) e.src e.body).card + traceSent (π.recvHonest e s) xl
  | .byzRecv src dest body :: xl =>
    (π.send dest (s.proc dest) src body).card + traceSent (π.recvByz src dest body s) xl
  | .stutter :: xl => traceSent s xl

/-- Total authentic envelopes emitted by correct processes from the initial state through a finite
trace `xl` (initial messages in `(π.start F input).msgs` plus `π.traceSent`). -/
@[expose] def sentInTrace [Fintype P] (F : Finset P) (input : Option V) (xl : List (Action P M)) :
    ℕ :=
  (π.start F input).msgs.card + π.traceSent (π.start F input) xl

/-- **Exact message-conservation identity:** along any valid finite execution trace `xl` from `s₀`
to `s₁`, the initial in-flight envelopes plus newly emitted authentic envelopes equal the final
in-flight envelopes plus the authentic deliveries performed along `xl`. -/
theorem card_msgs_add_traceSent {F : Finset P} {s₀ s₁ : State P S M V} {xl : List (Action P M)}
    (hmtr : (π.lts F).MTr s₀ xl s₁) :
    s₀.msgs.card + π.traceSent s₀ xl = s₁.msgs.card + xl.countP Action.isDeliver := by
  induction hmtr with
  | refl => simp [traceSent]
  | @stepL s a s' xl' s₁ htr _ ih =>
    cases a with
    | deliver e =>
      obtain ⟨hmem, _, rfl⟩ := htr
      have := Multiset.card_pos_iff_exists_mem.mpr ⟨e, hmem⟩
      simp only [traceSent, recvHonest, recvCore, Multiset.card_add, Multiset.card_map,
        Multiset.card_erase_of_mem hmem, Nat.pred_eq_sub_one, List.countP_cons, Action.isDeliver,
        ↓reduceIte] at ih ⊢
      omega
    | byzRecv src dest body =>
      obtain ⟨_, _, rfl⟩ := htr
      simp only [traceSent, recvByz, recvCore, Multiset.card_add, Multiset.card_map,
        List.countP_cons, Action.isDeliver, Bool.false_eq_true, ↓reduceIte] at ih ⊢
      omega
    | stutter =>
      obtain rfl := htr
      simpa [traceSent, Action.isDeliver] using ih

/-! ### Reliable broadcast specification -/

/-- `π.SolvesReliableBroadcast t` means `π` implements single-sender asynchronous Byzantine
reliable broadcast from `dealer` tolerating up to `t` static Byzantine faults ([Bracha1987];
[BrachaToueg1985]):

* **consistency** (agreement): no two correct processes ever deliver different values, even if the
  dealer is faulty;
* **noSpurious** (honest-sender integrity): if the dealer is correct with input `input : Option V`,
  any value `v` delivered by a correct process must satisfy `input = some v` (in particular, if
  `input = none` the dealer never broadcasts and no correct process ever delivers);
* **validity**: if the dealer is correct with input `some v`, every correct process eventually
  delivers `v` in every fair execution;
* **totality**: in every fair execution (even if the dealer is faulty), if some correct process
  delivers `v`, then every correct process eventually delivers `v`.

No-duplication (at most one delivery per process) holds structurally from write-once `ProcState.out`
(`procDecided_stable`). -/
structure SolvesReliableBroadcast [Fintype P] (t : ℕ) : Prop where
  /-- Consistency (agreement): no two correct processes deliver different values in any reachable
  state. -/
  consistency : ∀ (F : Finset P), F.card ≤ t → ∀ (input : Option V) (s : State P S M V),
    π.Reachable F input s → ∀ i ∉ F, ∀ j ∉ F, ∀ v₁ v₂,
    s.ProcDecided i v₁ → s.ProcDecided j v₂ → v₁ = v₂
  /-- Integrity (no spurious delivery): if `dealer` is correct with input `input`, any value `v`
  delivered by a correct process matches `input = some v`. -/
  noSpurious : ∀ (F : Finset P), F.card ≤ t → dealer ∉ F →
    ∀ (input : Option V) (s : State P S M V),
    π.Reachable F input s → ∀ i ∉ F, ∀ v, s.ProcDecided i v → input = some v
  /-- Validity (liveness for an honest dealer): if `dealer` is correct with input `some v`, every
  correct process eventually delivers `v` in every admissible execution. -/
  validity : ∀ (F : Finset P), F.card ≤ t → dealer ∉ F →
    ∀ (v : V) (ss : ωSequence (State P S M V)) (xs : ωSequence (Action P M)),
    π.AdmissibleRun F (some v) ss xs → ∀ i ∉ F, ∃ k, (ss k).ProcDecided i v
  /-- Totality (liveness for a possibly faulty dealer): if any correct process delivers `v` in an
  admissible execution, then every correct process eventually delivers `v`. -/
  totality : ∀ (F : Finset P), F.card ≤ t → ∀ (input : Option V)
    (ss : ωSequence (State P S M V)) (xs : ωSequence (Action P M)),
    π.AdmissibleRun F input ss xs →
    ∀ i ∉ F, ∀ k v, (ss k).ProcDecided i v → ∀ j ∉ F, ∃ k', (ss k').ProcDecided j v

/-- Tolerating `t` faults implies tolerating at most `t' ≤ t` faults. -/
theorem SolvesReliableBroadcast.mono [Fintype P] {π : Protocol P S M V dealer} {t t' : ℕ}
    (h : π.SolvesReliableBroadcast t) (ht : t' ≤ t) : π.SolvesReliableBroadcast t' where
  consistency F hF := h.consistency F (hF.trans ht)
  noSpurious F hF := h.noSpurious F (hF.trans ht)
  validity F hF := h.validity F (hF.trans ht)
  totality F hF := h.totality F (hF.trans ht)

/-- Consistency across admissible infinite executions is equivalent to consistency across all
reachable finite states, because every reachable state extends to a fair infinite execution. -/
theorem consistency_iff_admissible [Fintype P] (t : ℕ) :
    (∀ (F : Finset P), F.card ≤ t → ∀ (input : Option V) (s : State P S M V),
      π.Reachable F input s → ∀ i ∉ F, ∀ j ∉ F, ∀ v₁ v₂,
      s.ProcDecided i v₁ → s.ProcDecided j v₂ → v₁ = v₂) ↔
    (∀ (F : Finset P), F.card ≤ t → ∀ (input : Option V)
      (ss : ωSequence (State P S M V)) (xs : ωSequence (Action P M)),
      π.AdmissibleRun F input ss xs →
      ∀ i ∉ F, ∀ j ∉ F, ∀ k₁ k₂ v₁ v₂,
      (ss k₁).ProcDecided i v₁ → (ss k₂).ProcDecided j v₂ → v₁ = v₂) := by
  constructor
  · intro h F hF input ss xs ha i hi j hj k₁ k₂ v₁ v₂ h₁ h₂
    let k := max k₁ k₂
    exact h F hF input (ss k) (π.admissibleRun_reachable ha k) i hi j hj v₁ v₂
      (π.omega_procDecided_stable ha.2.1 (le_max_left _ _) h₁)
      (π.omega_procDecided_stable ha.2.1 (le_max_right _ _) h₂)
  · intro h F hF input s hr i hi j hj v₁ v₂ h₁ h₂
    obtain ⟨ss, xs, k, ha, hsk, _⟩ := hr.exists_admissibleRun
    exact h F hF input ss xs ha i hi j hj k k v₁ v₂ (hsk.symm ▸ h₁) (hsk.symm ▸ h₂)

/-- Consistent broadcast fails across any run whose processes have already split. -/
theorem SolvesReliableBroadcast.consistency_admissible [Fintype P] {π : Protocol P S M V dealer}
    {t : ℕ} (h : π.SolvesReliableBroadcast t) {F : Finset P} (hF : F.card ≤ t)
    {input : Option V} {ss : ωSequence (State P S M V)} {xs : ωSequence (Action P M)}
    (ha : π.AdmissibleRun F input ss xs) {i j : P} (hi : i ∉ F) (hj : j ∉ F)
    {k₁ k₂ : ℕ} {v₁ v₂ : V} (h₁ : (ss k₁).ProcDecided i v₁) (h₂ : (ss k₂).ProcDecided j v₂) :
    v₁ = v₂ :=
  (π.consistency_iff_admissible t).mp h.consistency F hF input ss xs ha i hi j hj k₁ k₂ v₁ v₂ h₁ h₂

end Protocol

/-! ### Trivial direct broadcast (`t = 0` or `n ≤ 2`) -/

/-- The direct single-hop broadcast protocol: `dealer` sends its value `v` to every process
(including itself), and each process delivers the first message it receives directly from
`dealer`. This solves reliable broadcast when `t = 0` (on any process set) and against *any*
number of Byzantine faults when `Fintype.card P ≤ 2`. -/
@[expose] def directProtocol (P V : Type*) [Fintype P] [DecidableEq P] (dealer : P) :
    Protocol P PUnit V V dealer where
  init _ := .unit
  initDealer _ := .unit
  initMsgs _ := 0
  initDealerMsgs
    | none => 0
    | some v => broadcastAll P v
  next _ _ _ _ := .unit
  send _ _ _ _ := 0
  out _ _ src v := if src = dealer then some v else none

private def directInv {P V : Type*} {dealer : P} (F : Finset P) (input : Option V)
    (s : State P PUnit V V) : Prop :=
  (∀ e ∈ s.msgs, e.src = dealer ∧ input = some e.body) ∧
  (∀ i ∉ F, ∀ v, s.ProcDecided i v → input = some v)

private lemma directInv_start {P V : Type*} [Fintype P] [DecidableEq P] {dealer : P}
    (F : Finset P) (input : Option V) :
    directInv (dealer := dealer) F input ((directProtocol P V dealer).start F input) := by
  refine ⟨fun e he => ?_, fun i _ v hv => by simp [State.ProcDecided, Protocol.start] at hv⟩
  obtain ⟨p, -, hp⟩ := Multiset.mem_bind.mp he
  split_ifs at hp with hpF
  · simp at hp
  obtain ⟨⟨q, b⟩, hqb, rfl⟩ := Multiset.mem_map.mp hp
  simp only [Protocol.initSend, directProtocol] at hqb
  split_ifs at hqb with hpd
  · subst hpd
    cases input with
    | none => simp at hqb
    | some v => obtain ⟨_, _, ⟨⟩⟩ := Multiset.mem_map.mp hqb; exact ⟨rfl, rfl⟩
  · simp at hqb

private lemma directInv_tr {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {F : Finset P} (hd : dealer ∉ F) (input : Option V) :
    ((directProtocol P V dealer).lts F).TrInv (directInv (dealer := dealer) F input) := by
  intro s a s' htr ⟨hmsgs, hproc⟩
  cases a with
  | deliver e =>
    obtain ⟨hmem, hdest, rfl⟩ := htr
    refine ⟨fun e' he' => hmsgs e' (Multiset.mem_of_mem_erase
      (by simpa [Protocol.recvHonest, Protocol.recvCore, directProtocol] using he')),
      fun i hi v hv => ?_⟩
    simp only [State.ProcDecided, Protocol.recvHonest, Protocol.recvCore, Protocol.updateProc] at hv
    split_ifs at hv with hid hnone
    · simp only [directProtocol] at hv
      split_ifs at hv
      cases hv; exact (hmsgs e hmem).2
    · subst hid; exact hproc e.dest hdest v hv
    · exact hproc i hi v hv
  | byzRecv src dest body =>
    obtain ⟨hsrcF, hdest, rfl⟩ := htr
    have hne : src ≠ dealer := fun h => hd (h ▸ hsrcF)
    refine ⟨fun e' he' => hmsgs e'
      (by simpa [Protocol.recvByz, Protocol.recvCore, directProtocol] using he'),
      fun i hi v hv => ?_⟩
    simp only [State.ProcDecided, Protocol.recvByz, Protocol.recvCore, Protocol.updateProc] at hv
    split_ifs at hv with hid hnone
    · simp [directProtocol, hne] at hv
    · subst hid; exact hproc i hdest v hv
    · exact hproc i hi v hv
  | stutter => obtain rfl := htr; exact ⟨hmsgs, hproc⟩

private lemma direct_noSpurious {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {F : Finset P} (hd : dealer ∉ F) {input : Option V} {s : State P PUnit V V}
    (hr : (directProtocol P V dealer).Reachable F input s) {i : P} (hi : i ∉ F) {v : V}
    (hv : s.ProcDecided i v) : input = some v := by
  obtain ⟨xl, hxl⟩ := hr
  exact (LTS.mtrInv_of_trInv (directInv_tr hd input) _ _ _ hxl (directInv_start F input)).2
    i hi v hv

private lemma direct_validity {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {F : Finset P} (hd : dealer ∉ F) (v : V)
    {ss : ωSequence (State P PUnit V V)} {xs : ωSequence (Action P V)}
    (ha : (directProtocol P V dealer).AdmissibleRun F (some v) ss xs)
    {i : P} (hi : i ∉ F) : ∃ k, (ss k).ProcDecided i v := by
  let e : Envelope P V := ⟨dealer, i, v⟩
  have he0 : e ∈ (ss 0).msgs := by
    rw [ha.1]
    refine Multiset.mem_bind.mpr ⟨dealer, Finset.mem_univ _, ?_⟩
    simp only [hd, ↓reduceIte, Protocol.initSend, directProtocol]
    exact mem_broadcastAll_tag dealer i v
  obtain ⟨j, _, hj⟩ := ha.2.2 e hi 0 he0
  obtain ⟨_, _, hnext⟩ : ((directProtocol P V dealer).lts F).Tr (ss j) (.deliver e) (ss (j + 1)) :=
    hj ▸ ha.2.1 j
  refine ⟨j + 1, ?_⟩
  simp only [State.ProcDecided, hnext, Protocol.recvHonest, Protocol.recvCore, Protocol.updateProc,
    e, ↓reduceIte]
  cases hcur : ((ss j).proc i).out with
  | none => simp [directProtocol]
  | some v' =>
    simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    exact (direct_noSpurious hd ((directProtocol P V dealer).admissibleRun_reachable ha j)
      hi hcur).symm

private lemma eq_of_card_le_two_of_mem {P : Type*} [Fintype P]
    {F : Finset P} (hcard : Fintype.card P ≤ 2) {d i j : P}
    (hd : d ∈ F) (hi : i ∉ F) (hj : j ∉ F) : i = j := by
  finset_card

private lemma direct_honest_agreement {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {F : Finset P} (hd : dealer ∉ F) {input : Option V} {s : State P PUnit V V}
    (hr : (directProtocol P V dealer).Reachable F input s) {i j : P} (hi : i ∉ F) (hj : j ∉ F)
    {v₁ v₂ : V} (h₁ : s.ProcDecided i v₁) (h₂ : s.ProcDecided j v₂) : v₁ = v₂ :=
  Option.some.inj ((direct_noSpurious hd hr hi h₁).symm.trans (direct_noSpurious hd hr hj h₂))

private lemma direct_honest_totality {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {F : Finset P} (hd : dealer ∉ F) {input : Option V}
    {ss : ωSequence (State P PUnit V V)} {xs : ωSequence (Action P V)}
    (ha : (directProtocol P V dealer).AdmissibleRun F input ss xs)
    {i j : P} (hi : i ∉ F) (hj : j ∉ F) {k : ℕ} {v : V} (hv : (ss k).ProcDecided i v) :
    ∃ k', (ss k').ProcDecided j v := by
  have hinp := direct_noSpurious hd ((directProtocol P V dealer).admissibleRun_reachable ha k)
    hi hv
  subst hinp; exact direct_validity hd v ha hj

/-- Without faults (`t = 0`), `directProtocol` solves reliable broadcast on every finite `P`. -/
theorem solvesReliableBroadcast_direct_of_zero {P V : Type*} [Fintype P] [DecidableEq P]
    [DecidableEq V] (dealer : P) :
    (directProtocol P V dealer).SolvesReliableBroadcast 0 where
  consistency F hF _ _ hr _ hi _ hj _ _ h₁ h₂ := by
    obtain rfl := Finset.card_eq_zero.mp (Nat.le_zero.mp hF)
    exact direct_honest_agreement (Finset.notMem_empty dealer) hr hi hj h₁ h₂
  noSpurious _ _ hd _ _ hr _ hi _ hv := direct_noSpurious hd hr hi hv
  validity _ _ hd v _ _ ha _ hi := direct_validity hd v ha hi
  totality F hF _ _ _ ha _ hi _ _ hv _ hj := by
    obtain rfl := Finset.card_eq_zero.mp (Nat.le_zero.mp hF)
    exact direct_honest_totality (Finset.notMem_empty dealer) ha hi hj hv

/-- On at most two processes (`Fintype.card P ≤ 2`), `directProtocol` solves reliable broadcast
against *any* fault bound `t`: if `dealer` is faulty, at most one correct process remains, so both
consistency and totality are trivial. -/
theorem solvesReliableBroadcast_direct_of_card_le_two {P V : Type*} [Fintype P] [DecidableEq P]
    [DecidableEq V] (dealer : P) (hcard : Fintype.card P ≤ 2) (t : ℕ) :
    (directProtocol P V dealer).SolvesReliableBroadcast t where
  consistency F _ _ _ hr i hi j hj _ _ h₁ h₂ := by
    by_cases hd : dealer ∈ F
    · obtain rfl := eq_of_card_le_two_of_mem hcard hd hi hj
      exact Option.some.inj (h₁.symm.trans h₂)
    · exact direct_honest_agreement hd hr hi hj h₁ h₂
  noSpurious _ _ hd _ _ hr _ hi _ hv := direct_noSpurious hd hr hi hv
  validity _ _ hd v _ _ ha _ hi := direct_validity hd v ha hi
  totality F _ _ _ _ ha i hi k _ hv j hj := by
    by_cases hd : dealer ∈ F
    · obtain rfl := eq_of_card_le_two_of_mem hcard hd hi hj
      exact ⟨k, hv⟩
    · exact direct_honest_totality hd ha hi hj hv

end Cslib.Distributed.AsyncByzantine
