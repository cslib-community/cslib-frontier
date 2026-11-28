/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.AsyncByzantine.Basic
import CslibFrontier.Computability.Distributed.AsyncByzantine.Impossibility
import CslibFrontier.Tactic.FinsetCard
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Bracha's asynchronous Byzantine reliable broadcast (`n > 3t`)

This module formalizes the streamlined three-phase presentation of Bracha's asynchronous reliable
broadcast protocol (`brachaProtocol`, [Bracha1987]) and proves its correctness against up to `t`
static Byzantine faults whenever `3 * t < n`, where `n = Fintype.card P`. Combined with
`CslibFrontier.Computability.Distributed.AsyncByzantine.Impossibility` and `directProtocol`,
`exists_solvesReliableBroadcast_iff` gives the sharp threshold: for any nonempty value domain `V`,
deterministic asynchronous Byzantine reliable broadcast tolerating `t` faults exists **if and only
if** `n ≤ 2` or `3 * t < n`.

## Streamlined `echo` rule (difference from [Bracha1987] original rule)

In this formalization, a correct process sends `echo v` **only** upon receiving its first
`initial v` message directly from `dealer`. In some presentations of Bracha's original protocol,
a process also emits `echo v` upon receiving `echoThreshold n t` `echo v` or `t + 1` `ready v`
messages when it has not yet sent an `echo`. Omitting those echo-amplification branches yields the
same safety and liveness guarantees under `n > 3t` (because `ready` amplification and the
honest-echo quorum still force totality and consistency), keeps the exact `O(n²)` message bound
tighter, and avoids checking an extra transition rule; see the `brachaStep` specification below.

## The protocol

Every process maintains `BrachaState P V`: write-once fields recording the single `ECHO` and `READY`
values it has emitted (`sentEcho`, `sentReady : Option V`), and per-sender tables storing the
*first* `ECHO` and *first* `READY` received from each sender `j : P` (`echoFrom`,
`readyFrom : P → Option V`). Keeping only the first message per sender deduplicates Byzantine
replays and equivocations without requiring `[Fintype V]`.

For threshold `echoThreshold n t := (n + t) / 2 + 1 = ⌈(n + t + 1) / 2⌉`:

1. **Initial phase:** if `dealer` is correct with `input = some v`, it sends `initial v` to every
   process (including itself). Upon receiving its first `initial v` from `dealer`, a process sets
   `sentEcho := some v` and broadcasts `echo v` to all processes.
2. **Echo phase:** upon receiving the first `echo v` from `src`, record `echoFrom src := some v`.
   If at least `echoThreshold n t` distinct senders carry `echo v` and `sentReady` is `none`, set
   `sentReady := some v` and broadcast `ready v` to all processes.
3. **Ready phase:** upon receiving the first `ready v` from `src`, record `readyFrom src := some v`.
   - If at least `t + 1` distinct senders carry `ready v` and `sentReady` is `none`, set
     `sentReady := some v` and broadcast `ready v` to all processes (amplification).
   - If at least `2 * t + 1` distinct senders carry `ready v`, deliver `v`.

## Safety, liveness, and communication bound

Safety uses the *echo-quorum witness* invariant: whenever a correct process holds
`sentReady = some v`, there exists a quorum `S` with `echoThreshold n t ≤ S.card` every correct
member of which has `sentEcho = some v`. Two such quorums intersect in strictly more than `t`
processes (`echo_quorum_inter_notMem`), hence share a correct process; since each correct process
emits at most one `echo`, all correct `sentReady` values agree.

By exact telescoping over the counts of correct processes with `sentEcho.isSome` and
`sentReady.isSome`, `brachaSentInTrace_le` proves that along *every* finite execution trace—even
under arbitrary Byzantine message flooding—the total number of authentic envelopes emitted by
correct processes (`Protocol.sentInTrace`) is at most `n + 2 * (n - F.card) * n`.

## Main definitions

* `Cslib.Distributed.AsyncByzantine.echoThreshold`: quorum size `(n + t) / 2 + 1`.
* `Cslib.Distributed.AsyncByzantine.BrachaMsg`: message tag (`initial`, `echo`, `ready`).
* `Cslib.Distributed.AsyncByzantine.BrachaState`: local process state.
* `Cslib.Distributed.AsyncByzantine.BrachaStepResult`: return record of `brachaStep`.
* `Cslib.Distributed.AsyncByzantine.brachaStep`: unified local transition handler.
* `Cslib.Distributed.AsyncByzantine.brachaProtocol`: streamlined three-phase asynchronous reliable
  broadcast protocol.

## Main results

* `Cslib.Distributed.AsyncByzantine.echo_quorum_inter_notMem`: two echo quorums share a correct
  process.
* `Cslib.Distributed.AsyncByzantine.solvesReliableBroadcast_bracha`: correctness of
  `brachaProtocol` for `3 * t < Fintype.card P`.
* `Cslib.Distributed.AsyncByzantine.brachaSentInTrace_le`: exact `O(n²)` authentic communication
  bound `n + 2 * (n - F.card) * n` via `Protocol.sentInTrace`.
* `Cslib.Distributed.AsyncByzantine.exists_solvesReliableBroadcast_iff`: sharp threshold
  `Fintype.card P ≤ 2 ∨ 3 * t < Fintype.card P` for any nonempty `V`.

## References

* [G. Bracha, *Asynchronous Byzantine agreement protocols*][Bracha1987]
* [G. Bracha, S. Toueg, *Asynchronous consensus and broadcast protocols*][BrachaToueg1985]
-/

public section

namespace Cslib.Distributed.AsyncByzantine

open Cslib

/-! ### Threshold arithmetic and quorum intersection -/

/-- The Bracha echo-quorum threshold `⌈(n + t + 1) / 2⌉ = (n + t) / 2 + 1`. -/
@[expose] def echoThreshold (n t : ℕ) : ℕ := (n + t) / 2 + 1

/-- Any two echo quorums (of size at least `echoThreshold |P| t`) share a correct process
(`∉ F`) when `F.card ≤ t`. -/
theorem echo_quorum_inter_notMem {P : Type*} [Fintype P] [DecidableEq P]
    {F S₁ S₂ : Finset P} {t : ℕ} (hF : F.card ≤ t)
    (h₁ : echoThreshold (Fintype.card P) t ≤ S₁.card)
    (h₂ : echoThreshold (Fintype.card P) t ≤ S₂.card) :
    ∃ p ∈ S₁ ∩ S₂, p ∉ F := by
  finset_card [echoThreshold]

/-! ### Protocol definition -/

/-- Message payloads exchanged by Bracha's three-phase reliable broadcast protocol. -/
inductive BrachaMsg (V : Type*) where
  /-- Phase 1: original value sent by `dealer`. -/
  | initial (v : V)
  /-- Phase 2: echo confirmation of a value. -/
  | echo (v : V)
  /-- Phase 3: ready amplification/delivery confirmation of a value. -/
  | ready (v : V)
  deriving @[expose] DecidableEq

/-- Local internal state of a process running `brachaProtocol`. Retaining only the first message
per sender deduplicates Byzantine replays and equivocations without assuming `[Fintype V]`. -/
structure BrachaState (P V : Type*) where
  /-- The unique `echo` value emitted by this process, if any. -/
  sentEcho : Option V
  /-- The unique `ready` value emitted by this process, if any. -/
  sentReady : Option V
  /-- First `echo` value received from each sender `j : P`. -/
  echoFrom : P → Option V
  /-- First `ready` value received from each sender `j : P`. -/
  readyFrom : P → Option V

/-- Senders from whom `st` has recorded `echo v`. -/
@[expose] def echoSenders {P V : Type*} [Fintype P] [DecidableEq V]
    (st : BrachaState P V) (v : V) : Finset P :=
  Finset.univ.filter fun j => st.echoFrom j = some v

/-- Senders from whom `st` has recorded `ready v`. -/
@[expose] def readySenders {P V : Type*} [Fintype P] [DecidableEq V]
    (st : BrachaState P V) (v : V) : Finset P :=
  Finset.univ.filter fun j => st.readyFrom j = some v

/-- Output record of one local step of Bracha's protocol. -/
structure BrachaStepResult (P V : Type*) where
  /-- Updated local internal state. -/
  nextState : BrachaState P V
  /-- Outgoing `(dest, msg)` multiset emitted in this step. -/
  outgoing : Multiset (P × BrachaMsg V)
  /-- Value delivered (`some v`), if the delivery threshold `2t + 1` was reached. -/
  delivered : Option V

/-- Shared local transition handler for the streamlined three-phase `brachaProtocol`. Unlike
variants that also emit `echo v` after collecting enough `echo`/`ready` messages, this handler
emits `echo v` only upon receiving the first `initial v` from `dealer`. -/
@[expose] def brachaStep {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (dealer : P) (t : ℕ) (st : BrachaState P V) (src : P) :
    BrachaMsg V → BrachaStepResult P V
  | .initial v =>
    if src = dealer ∧ st.sentEcho.isNone then
      ⟨{ st with sentEcho := some v }, broadcastAll P (.echo v), none⟩
    else
      ⟨st, 0, none⟩
  | .echo v =>
    if (st.echoFrom src).isNone then
      let st' : BrachaState P V := { st with echoFrom := Function.update st.echoFrom src (some v) }
      if echoThreshold (Fintype.card P) t ≤ (echoSenders st' v).card ∧ st.sentReady.isNone then
        ⟨{ st' with sentReady := some v }, broadcastAll P (.ready v), none⟩
      else
        ⟨st', 0, none⟩
    else
      ⟨st, 0, none⟩
  | .ready v =>
    if (st.readyFrom src).isNone then
      let st' : BrachaState P V :=
        { st with readyFrom := Function.update st.readyFrom src (some v) }
      let cnt := (readySenders st' v).card
      let sendR := t + 1 ≤ cnt ∧ st.sentReady.isNone
      ⟨if sendR then { st' with sentReady := some v } else st',
       if sendR then broadcastAll P (.ready v) else 0,
       if 2 * t + 1 ≤ cnt then some v else none⟩
    else
      ⟨st, 0, none⟩

/-- Initial local state of a process running Bracha's protocol. -/
@[expose] def brachaInit (P V : Type*) : BrachaState P V where
  sentEcho := none
  sentReady := none
  echoFrom _ := none
  readyFrom _ := none

/-- Streamlined three-phase asynchronous Byzantine reliable broadcast protocol for sender `dealer`
and fault threshold `t` ([Bracha1987]). A correct process emits `echo v` only upon its first
`initial v` from `dealer` (without secondary echo amplification from `echo`/`ready` thresholds),
then emits `ready v` and delivers `v` via the standard `echoThreshold n t`, `t + 1`, and
`2 * t + 1` thresholds. -/
@[expose] def brachaProtocol (P V : Type*) [Fintype P] [DecidableEq P] [DecidableEq V]
    (dealer : P) (t : ℕ) : Protocol P (BrachaState P V) (BrachaMsg V) V dealer where
  init _ := brachaInit P V
  initDealer _ := brachaInit P V
  initMsgs _ := 0
  initDealerMsgs
    | none => 0
    | some v => broadcastAll P (.initial v)
  next _ st src m := (brachaStep dealer t st.state src m).nextState
  send _ st src m := (brachaStep dealer t st.state src m).outgoing
  out _ st src m := (brachaStep dealer t st.state src m).delivered

/-! ### Private specification lemmas for `brachaStep` -/

private lemma filter_optUpdate_ne {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {f : P → Option V} {src : P} {v w : V} (hne : v ≠ w) :
    (Finset.univ.filter fun j =>
      (if (f src).isNone then Function.update f src (some v) else f) j = some w) =
      Finset.univ.filter fun j => f j = some w := by
  split_ifs with hnone
  · ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j = src
    · subst hj; simp [Option.isNone_iff_eq_none.mp hnone, hne]
    · simp [Function.update_of_ne hj]
  · rfl

private lemma optUpdate_mono {P V : Type*} [DecidableEq P] {f : P → Option V} {src j : P} {u v : V}
    (h : f j = some u) :
    (if (f src).isNone then Function.update f src (some v) else f) j = some u := by
  split_ifs with hnone
  · by_cases hj : j = src
    · subst hj; simp [h] at hnone
    · simpa [Function.update_of_ne hj] using h
  · exact h

private lemma optUpdate_eq_some {P V : Type*} [DecidableEq P] {f : P → Option V} {src j : P}
    {w v : V} (h : (if (f src).isNone then Function.update f src (some w) else f) j = some v) :
    f j = some v ∨ (j = src ∧ w = v) := by
  split_ifs at h
  · by_cases hj : j = src
    · subst hj; simp only [Function.update_self, Option.some.injEq] at h; exact Or.inr ⟨rfl, h⟩
    · exact Or.inl (by rwa [Function.update_of_ne hj] at h)
  · exact Or.inl h

section BrachaStepSpecs

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
  {dealer : P} {t : ℕ} {st : BrachaState P V} {src : P} {body : BrachaMsg V}

/-- Every `brachaStep` emits either nothing (leaving `sentEcho` and `sentReady` unchanged), a fresh
`echo v` broadcast (transitioning `sentEcho` from `none` to `some v`), or a fresh `ready v`
broadcast (transitioning `sentReady` from `none` to `some v`). -/
private lemma brachaStep_outgoing_spec :
    let r := brachaStep dealer t st src body
    (r.outgoing = 0 ∧
      r.nextState.sentEcho = st.sentEcho ∧ r.nextState.sentReady = st.sentReady) ∨
    (∃ v, r.outgoing = broadcastAll P (.echo v) ∧
      st.sentEcho = none ∧ r.nextState.sentEcho = some v ∧
      r.nextState.sentReady = st.sentReady) ∨
    (∃ v, r.outgoing = broadcastAll P (.ready v) ∧
      st.sentReady = none ∧ r.nextState.sentReady = some v ∧
      r.nextState.sentEcho = st.sentEcho) := by
  cases body with
  | initial w =>
    dsimp only [brachaStep]; split_ifs with hc
    · exact Or.inr (Or.inl ⟨w, rfl, Option.isNone_iff_eq_none.mp hc.2, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl, rfl⟩
  | echo w =>
    dsimp only [brachaStep]; split_ifs with h1 h2
    · exact Or.inr (Or.inr ⟨w, rfl, Option.isNone_iff_eq_none.mp h2.2, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl, rfl⟩
  | ready w =>
    dsimp only [brachaStep]
    by_cases h1 : (st.readyFrom src).isNone = true
    · simp only [h1, ↓reduceIte]; split_ifs with h2
      · exact Or.inr (Or.inr ⟨w, rfl, Option.isNone_iff_eq_none.mp h2.2, rfl, rfl⟩)
      · exact Or.inl ⟨rfl, rfl, rfl⟩
    · simp [h1]

private lemma brachaStep_echoFrom_eq :
    (brachaStep dealer t st src body).nextState.echoFrom =
      match body with
      | .echo w =>
        if (st.echoFrom src).isNone then Function.update st.echoFrom src (some w) else st.echoFrom
      | _ => st.echoFrom := by
  cases body <;> dsimp only [brachaStep] <;> split_ifs <;> rfl

private lemma brachaStep_readyFrom_eq :
    (brachaStep dealer t st src body).nextState.readyFrom =
      match body with
      | .ready w =>
        if (st.readyFrom src).isNone then
          Function.update st.readyFrom src (some w)
        else st.readyFrom
      | _ => st.readyFrom := by
  cases body <;> dsimp only [brachaStep] <;> split_ifs <;> rfl

private lemma brachaStep_sentEcho_mono {v : V} (h : st.sentEcho = some v) :
    (brachaStep dealer t st src body).nextState.sentEcho = some v := by
  rcases brachaStep_outgoing_spec (dealer := dealer) (t := t) (st := st) (src := src)
      (body := body) with ⟨_, he, _⟩ | ⟨_, _, h0, _, _⟩ | ⟨_, _, _, _, he⟩
  · exact he.trans h
  · rw [h] at h0; cases h0
  · exact he.trans h

private lemma brachaStep_sentReady_mono {v : V} (h : st.sentReady = some v) :
    (brachaStep dealer t st src body).nextState.sentReady = some v := by
  rcases brachaStep_outgoing_spec (dealer := dealer) (t := t) (st := st) (src := src)
      (body := body) with ⟨_, _, hr⟩ | ⟨_, _, _, _, hr⟩ | ⟨_, _, h0, _, _⟩
  · exact hr.trans h
  · exact hr.trans h
  · rw [h] at h0; cases h0

private lemma brachaStep_echoFrom_mono {j : P} {v : V} (h : st.echoFrom j = some v) :
    (brachaStep dealer t st src body).nextState.echoFrom j = some v := by
  rw [brachaStep_echoFrom_eq]; cases body <;> first | exact optUpdate_mono h | exact h

private lemma brachaStep_readyFrom_mono {j : P} {v : V} (h : st.readyFrom j = some v) :
    (brachaStep dealer t st src body).nextState.readyFrom j = some v := by
  rw [brachaStep_readyFrom_eq]; cases body <;> first | exact optUpdate_mono h | exact h

private lemma brachaStep_echoSenders_card_eq {v : V} (h : body ≠ .echo v) :
    (echoSenders (brachaStep dealer t st src body).nextState v).card =
      (echoSenders st v).card := by
  simp only [echoSenders, brachaStep_echoFrom_eq]
  cases body with
  | echo _ => exact congrArg Finset.card (filter_optUpdate_ne fun hw => h (hw ▸ rfl))
  | _ => rfl

private lemma brachaStep_readySenders_card_eq {v : V} (h : body ≠ .ready v) :
    (readySenders (brachaStep dealer t st src body).nextState v).card =
      (readySenders st v).card := by
  simp only [readySenders, brachaStep_readyFrom_eq]
  cases body with
  | ready _ => exact congrArg Finset.card (filter_optUpdate_ne fun hw => h (hw ▸ rfl))
  | _ => rfl

private lemma brachaStep_sentReady_eq_some {v : V}
    (h : (brachaStep dealer t st src body).nextState.sentReady = some v) :
    st.sentReady = some v ∨
      echoThreshold (Fintype.card P) t ≤
        (echoSenders (brachaStep dealer t st src body).nextState v).card ∨
      t + 1 ≤ (readySenders (brachaStep dealer t st src body).nextState v).card := by
  cases body with
  | initial _ => dsimp only [brachaStep] at h; split_ifs at h <;> exact Or.inl h
  | echo _ =>
    dsimp only [brachaStep] at h ⊢; split_ifs at h with h1 h2
    · cases h; exact Or.inr (Or.inl (by simp only [h1, h2, ↓reduceIte]; exact h2.1))
    · exact Or.inl h
    · exact Or.inl h
  | ready _ =>
    dsimp only [brachaStep] at h ⊢
    by_cases h1 : (st.readyFrom src).isNone = true
    · simp only [h1, ↓reduceIte] at h ⊢; split_ifs at h with h2
      · cases h; exact Or.inr (Or.inr (by simp only [h2]; exact h2.1))
      · exact Or.inl h
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl h

private lemma brachaStep_echo_sat_none {v : V} (hsr : st.sentReady = none)
    (hcnt : echoThreshold (Fintype.card P) t ≤
      (echoSenders (brachaStep dealer t st src (.echo v)).nextState v).card) :
    echoThreshold (Fintype.card P) t ≤ (echoSenders st v).card ∨
      (brachaStep dealer t st src (.echo v)).nextState.sentReady = some v := by
  dsimp only [brachaStep] at hcnt ⊢
  by_cases h1 : (st.echoFrom src).isNone = true
  · simp only [h1, ↓reduceIte] at hcnt ⊢
    split_ifs at hcnt ⊢ with h2
    exacts [Or.inr rfl, absurd ⟨hcnt, by simp [hsr]⟩ h2]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hcnt; exact Or.inl hcnt

private lemma brachaStep_ready_sat_none {v : V} (hsr : st.sentReady = none)
    (hcnt : t + 1 ≤ (readySenders (brachaStep dealer t st src (.ready v)).nextState v).card) :
    t + 1 ≤ (readySenders st v).card ∨
      (brachaStep dealer t st src (.ready v)).nextState.sentReady = some v := by
  dsimp only [brachaStep] at hcnt ⊢
  by_cases h1 : (st.readyFrom src).isNone = true
  · simp only [h1, ↓reduceIte] at hcnt ⊢
    split_ifs at hcnt ⊢ with h2
    exacts [Or.inr rfl, absurd ⟨hcnt, by simp [hsr]⟩ h2]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hcnt; exact Or.inl hcnt

private lemma brachaStep_deliver_sat {v : V}
    (hcnt : 2 * t + 1 ≤ (readySenders (brachaStep dealer t st src (.ready v)).nextState v).card) :
    2 * t + 1 ≤ (readySenders st v).card ∨
      (brachaStep dealer t st src (.ready v)).delivered = some v := by
  dsimp only [brachaStep] at hcnt ⊢
  by_cases h1 : (st.readyFrom src).isNone = true
  · simp only [h1, ↓reduceIte] at hcnt ⊢
    have hcnt' : 2 * t + 1 ≤
        (readySenders { st with readyFrom := Function.update st.readyFrom src (some v) } v).card :=
      by split_ifs at hcnt <;> exact hcnt
    exact Or.inr (by simp [hcnt'])
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hcnt; exact Or.inl hcnt

end BrachaStepSpecs

/-! ### Global inductive invariant -/

/-- Global inductive invariant tracking authenticity, quorum witnesses, threshold triggers, and
in-flight liveness records for `brachaProtocol`. -/
private structure BrachaInv {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (dealer : P) (t : ℕ) (F : Finset P) (input : Option V)
    (s : State P (BrachaState P V) (BrachaMsg V) V) : Prop where
  srcNotF : ∀ e ∈ s.msgs, e.src ∉ F
  initMsg : ∀ e ∈ s.msgs, ∀ v, e.body = .initial v → e.src = dealer ∧ input = some v
  echoMsg : ∀ e ∈ s.msgs, ∀ v, e.body = .echo v → (s.proc e.src).state.sentEcho = some v
  readyMsg : ∀ e ∈ s.msgs, ∀ v, e.body = .ready v → (s.proc e.src).state.sentReady = some v
  echoDealer : dealer ∉ F → ∀ p ∉ F, ∀ v, (s.proc p).state.sentEcho = some v → input = some v
  echoSound : ∀ p ∉ F, ∀ j ∉ F, ∀ v,
    (s.proc p).state.echoFrom j = some v → (s.proc j).state.sentEcho = some v
  readySound : ∀ p ∉ F, ∀ j ∉ F, ∀ v,
    (s.proc p).state.readyFrom j = some v → (s.proc j).state.sentReady = some v
  readyWitness : ∀ p ∉ F, ∀ v, (s.proc p).state.sentReady = some v →
    ∃ S : Finset P, echoThreshold (Fintype.card P) t ≤ S.card ∧
      ∀ j ∈ S, j ∉ F → (s.proc j).state.sentEcho = some v
  outSound : ∀ p ∉ F, ∀ v, s.ProcDecided p v →
    2 * t + 1 ≤ (readySenders (s.proc p).state v).card
  echoSat : ∀ p ∉ F, ∀ v, echoThreshold (Fintype.card P) t ≤ (echoSenders (s.proc p).state v).card →
    (s.proc p).state.sentReady = some v
  readySat : ∀ p ∉ F, ∀ v, t + 1 ≤ (readySenders (s.proc p).state v).card →
    (s.proc p).state.sentReady = some v
  outSat : ∀ p ∉ F, ∀ v, 2 * t + 1 ≤ (readySenders (s.proc p).state v).card → s.ProcDecided p v
  initLive : dealer ∉ F → ∀ v, input = some v → ∀ q ∉ F,
    ⟨dealer, q, .initial v⟩ ∈ s.msgs ∨ (s.proc q).state.sentEcho = some v
  echoLive : ∀ p ∉ F, ∀ v, (s.proc p).state.sentEcho = some v → ∀ q ∉ F,
    ⟨p, q, .echo v⟩ ∈ s.msgs ∨ (s.proc q).state.echoFrom p = some v
  readyLive : ∀ p ∉ F, ∀ v, (s.proc p).state.sentReady = some v → ∀ q ∉ F,
    ⟨p, q, .ready v⟩ ∈ s.msgs ∨ (s.proc q).state.readyFrom p = some v

section BrachaInvariant

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
  {dealer : P} {t : ℕ} {F : Finset P} {input : Option V}

private lemma BrachaInv.witness_unique {s : State P (BrachaState P V) (BrachaMsg V) V}
    (hinv : BrachaInv dealer t F input s) (hF : F.card ≤ t)
    {S : Finset P} {u v : V} (hS : echoThreshold (Fintype.card P) t ≤ S.card)
    (hw : ∀ j ∈ S, j ∉ F → (s.proc j).state.sentEcho = some v)
    {p : P} (hp : p ∉ F) (hrp : (s.proc p).state.sentReady = some u) : v = u := by
  obtain ⟨S', hS', hw'⟩ := hinv.readyWitness p hp u hrp
  obtain ⟨k, hki, hkF⟩ := echo_quorum_inter_notMem hF hS hS'
  rw [Finset.mem_inter] at hki
  exact Option.some.inj ((hw k hki.1 hkF).symm.trans (hw' k hki.2 hkF))

private lemma BrachaInv.ready_unique {s : State P (BrachaState P V) (BrachaMsg V) V}
    (hinv : BrachaInv dealer t F input s) (hF : F.card ≤ t)
    {p q : P} (hp : p ∉ F) (hq : q ∉ F) {v₁ v₂ : V}
    (h₁ : (s.proc p).state.sentReady = some v₁) (h₂ : (s.proc q).state.sentReady = some v₂) :
    v₁ = v₂ :=
  let ⟨_, hS, hw⟩ := hinv.readyWitness p hp v₁ h₁
  hinv.witness_unique hF hS hw hq h₂

private lemma BrachaInv.out_has_honest_ready {s : State P (BrachaState P V) (BrachaMsg V) V}
    (hinv : BrachaInv dealer t F input s) (hF : F.card ≤ t)
    {p : P} (hp : p ∉ F) {v : V} (hv : s.ProcDecided p v) :
    ∃ k ∉ F, (s.proc k).state.sentReady = some v := by
  have hcnt := hinv.outSound p hp v hv
  obtain ⟨k, hkS, hkF⟩ : ∃ k ∈ readySenders (s.proc p).state v, k ∉ F := by finset_card
  simp only [readySenders, Finset.mem_filter, Finset.mem_univ, true_and] at hkS
  exact ⟨k, hkF, hinv.readySound p hp k hkF v hkS⟩

private lemma brachaInv_start (F : Finset P) (input : Option V) :
    BrachaInv dealer t F input ((brachaProtocol P V dealer t).start F input) := by
  have hmem : ∀ e ∈ ((brachaProtocol P V dealer t).start F input).msgs,
      ∃ v, e.src = dealer ∧ dealer ∉ F ∧ input = some v ∧ e.body = .initial v := by
    intro e he
    obtain ⟨p, -, hp⟩ := Multiset.mem_bind.mp he
    split_ifs at hp with hpF
    · simp at hp
    obtain ⟨⟨q, b⟩, hqb, rfl⟩ := Multiset.mem_map.mp hp
    simp only [Protocol.initSend, brachaProtocol] at hqb
    split_ifs at hqb with hpd
    · subst hpd
      cases input with
      | none => simp at hqb
      | some v => obtain ⟨_, _, ⟨⟩⟩ := Multiset.mem_map.mp hqb; exact ⟨v, rfl, hpF, rfl, rfl⟩
    · simp at hqb
  have hst : ∀ p, (((brachaProtocol P V dealer t).start F input).proc p).state = brachaInit P V :=
    fun _ => by simp [Protocol.start, Protocol.initState, brachaProtocol]
  have hthresh : 0 < echoThreshold (Fintype.card P) t := by simp [echoThreshold]
  refine
    { srcNotF := fun e he => let ⟨_, hs, hd, _, _⟩ := hmem e he; hs ▸ hd
      initMsg := fun e he v hb => by
        obtain ⟨_, hs, _, hinp, hbw⟩ := hmem e he; cases hbw.symm.trans hb; exact ⟨hs, hinp⟩
      echoMsg := fun e he v hb => by obtain ⟨_, _, _, _, hbw⟩ := hmem e he; cases hbw.symm.trans hb
      readyMsg := fun e he v hb => by obtain ⟨_, _, _, _, hbw⟩ := hmem e he; cases hbw.symm.trans hb
      echoDealer := fun _ p _ _ h => by simp [hst p, brachaInit] at h
      echoSound := fun p _ _ _ _ h => by simp [hst p, brachaInit] at h
      readySound := fun p _ _ _ _ h => by simp [hst p, brachaInit] at h
      readyWitness := fun p _ _ h => by simp [hst p, brachaInit] at h
      outSound := fun _ _ _ h => by simp [State.ProcDecided, Protocol.start] at h
      echoSat := fun p _ v hc => by simp [hst p, echoSenders, brachaInit] at hc; omega
      readySat := fun p _ v hc => by simp [hst p, readySenders, brachaInit] at hc
      outSat := fun p _ v hc => by simp [hst p, readySenders, brachaInit] at hc
      initLive := fun hd v hinp q _ => Or.inl (Multiset.mem_bind.mpr ⟨dealer, Finset.mem_univ _,
        by simpa [hd, hinp, Protocol.initSend, brachaProtocol] using
          mem_broadcastAll_tag dealer q (BrachaMsg.initial v)⟩)
      echoLive := fun p _ _ h => by simp [hst p, brachaInit] at h
      readyLive := fun p _ _ h => by simp [hst p, brachaInit] at h }

section RecvCore

variable {s : State P (BrachaState P V) (BrachaMsg V) V} {src dest : P} {body : BrachaMsg V}
  {mb : Multiset (Envelope P (BrachaMsg V))}

private lemma recvCore_state_mono {Q : BrachaState P V → Prop} {p : P}
    (hQ : ∀ st, Q st → Q (brachaStep dealer t st src body).nextState)
    (h : Q (s.proc p).state) :
    Q (((brachaProtocol P V dealer t).recvCore src dest body mb s).proc p).state := by
  dsimp only [Protocol.recvCore]
  split_ifs with hp
  · exact hp ▸ hQ _ h
  · exact h

private lemma recvCore_procDecided_mono {p : P} {v : V} (hv : s.ProcDecided p v) :
    ((brachaProtocol P V dealer t).recvCore src dest body mb s).ProcDecided p v := by
  dsimp only [State.ProcDecided, Protocol.recvCore]
  split_ifs with hp
  · subst hp; exact (brachaProtocol P V dealer t).updateProc_out_eq_some hv
  · exact hv

private lemma recvCore_sat_sentReady {p : P} {v : V} {k : ℕ}
    (cnt : BrachaState P V → V → ℕ) (msg : BrachaMsg V)
    (hprev : k ≤ cnt (s.proc p).state v → (s.proc p).state.sentReady = some v)
    (hcard_ne : body ≠ msg →
      cnt (brachaStep dealer t (s.proc dest).state src body).nextState v =
        cnt (s.proc dest).state v)
    (hnone : body = msg → (s.proc dest).state.sentReady = none →
      k ≤ cnt (brachaStep dealer t (s.proc dest).state src body).nextState v →
      k ≤ cnt (s.proc dest).state v ∨
        (brachaStep dealer t (s.proc dest).state src body).nextState.sentReady = some v)
    (hsome : ∀ u, (s.proc dest).state.sentReady = some u →
      k ≤ cnt (brachaStep dealer t (s.proc dest).state src body).nextState v → v = u)
    (hcnt : k ≤ cnt (((brachaProtocol P V dealer t).recvCore src dest body mb s).proc p).state v) :
    (((brachaProtocol P V dealer t).recvCore src dest body mb s).proc p).state.sentReady =
      some v := by
  by_cases hpd : p = dest
  · subst hpd
    simp only [Protocol.recvCore, Protocol.updateProc, brachaProtocol, ↓reduceIte] at hcnt ⊢
    by_cases hbm : body = msg
    · cases hsr : (s.proc p).state.sentReady with
      | none => exact (hnone hbm hsr hcnt).elim (fun h0 => brachaStep_sentReady_mono (hprev h0)) id
      | some u => obtain rfl := hsome u hsr hcnt; exact brachaStep_sentReady_mono hsr
    · rw [hcard_ne hbm] at hcnt; exact brachaStep_sentReady_mono (hprev hcnt)
  · simp only [Protocol.recvCore, hpd, ↓reduceIte] at hcnt ⊢; exact hprev hcnt

private lemma recvCore_live_keep {p q : P} {msg : BrachaMsg V} {v : V}
    {fld : BrachaState P V → Option V}
    (hprev : ⟨p, q, msg⟩ ∈ s.msgs ∨ fld (s.proc q).state = some v)
    (hdrop : ∀ e ∈ s.msgs, e ∉ mb → e = ⟨src, dest, body⟩)
    (hmono : ∀ st s₀ m, fld st = some v → fld (brachaStep dealer t st s₀ m).nextState = some v)
    (hnone : fld (s.proc q).state = none →
      fld (brachaStep dealer t (s.proc q).state p msg).nextState = some v)
    (hsome : ∀ u, fld (s.proc q).state = some u → u = v) :
    ⟨p, q, msg⟩ ∈ ((brachaProtocol P V dealer t).recvCore src dest body mb s).msgs ∨
      fld (((brachaProtocol P V dealer t).recvCore src dest body mb s).proc q).state = some v := by
  rcases hprev with hmem | hdone
  · by_cases hbase : ⟨p, q, msg⟩ ∈ mb
    · exact Or.inl (Multiset.mem_add.mpr (Or.inl hbase))
    · right
      obtain ⟨rfl, rfl, rfl⟩ := Envelope.mk.inj (hdrop _ hmem hbase)
      simp only [Protocol.recvCore, Protocol.updateProc, brachaProtocol, ↓reduceIte]
      cases hf : fld (s.proc q).state with
      | none => exact hnone hf
      | some u => obtain rfl := hsome u hf; exact hmono _ _ _ hf
  · exact Or.inr (recvCore_state_mono (Q := fun st => fld st = some v) (fun _ => hmono _ _ _) hdone)

private lemma recvCore_live_sent {p q : P} {v : V}
    (sent : BrachaState P V → Option V) (recv : BrachaState P V → P → Option V)
    (msg : V → BrachaMsg V)
    (hcur : sent (((brachaProtocol P V dealer t).recvCore src dest body mb s).proc p).state =
      some v)
    (hprev : sent (s.proc p).state = some v →
      ⟨p, q, msg v⟩ ∈ s.msgs ∨ recv (s.proc q).state p = some v)
    (hdrop : ∀ e ∈ s.msgs, e ∉ mb → e = ⟨src, dest, body⟩)
    (hmono : ∀ st s₀ m, recv st p = some v →
      recv (brachaStep dealer t st s₀ m).nextState p = some v)
    (hnone : recv (s.proc q).state p = none →
      recv (brachaStep dealer t (s.proc q).state p (msg v)).nextState p = some v)
    (hsound : ∀ u, recv (s.proc q).state p = some u → sent (s.proc p).state = some u)
    (hfresh : sent (brachaStep dealer t (s.proc dest).state src body).nextState = some v →
      sent (s.proc dest).state ≠ some v →
      (brachaStep dealer t (s.proc dest).state src body).outgoing = broadcastAll P (msg v)) :
    ⟨p, q, msg v⟩ ∈ ((brachaProtocol P V dealer t).recvCore src dest body mb s).msgs ∨
      recv (((brachaProtocol P V dealer t).recvCore src dest body mb s).proc q).state p =
        some v := by
  by_cases hold : sent (s.proc p).state = some v
  · exact recvCore_live_keep (fld := fun st => recv st p) (hprev hold) hdrop hmono hnone
      fun u hu => Option.some.inj ((hsound u hu).symm.trans hold)
  · have hpd : p = dest := by
      by_contra hc; simp only [Protocol.recvCore, hc, ↓reduceIte] at hcur; exact hold hcur
    subst hpd
    simp only [Protocol.recvCore, Protocol.updateProc, brachaProtocol, ↓reduceIte] at hcur
    exact Or.inl (Multiset.mem_add.mpr (Or.inr (by
      simpa [Protocol.recvCore, brachaProtocol, hfresh hcur hold] using
        mem_broadcastAll_tag p q (msg v))))

private lemma recvCore_readyWitness (hF : F.card ≤ t) (hinv : BrachaInv dealer t F input s)
    (hdest : dest ∉ F)
    (hES_pre : ∀ j ∉ F, ∀ v,
      (brachaStep dealer t (s.proc dest).state src body).nextState.echoFrom j = some v →
        (s.proc j).state.sentEcho = some v)
    (hRS_pre : ∀ j ∉ F, ∀ v,
      (brachaStep dealer t (s.proc dest).state src body).nextState.readyFrom j = some v →
        (s.proc j).state.sentReady = some v) :
    let s' := (brachaProtocol P V dealer t).recvCore src dest body mb s
    ∀ p ∉ F, ∀ v, (s'.proc p).state.sentReady = some v →
      ∃ S : Finset P, echoThreshold (Fintype.card P) t ≤ S.card ∧
        ∀ j ∈ S, j ∉ F → (s'.proc j).state.sentEcho = some v := by
  intro s' p hp v hv
  have lift : ∀ {S : Finset P}, echoThreshold (Fintype.card P) t ≤ S.card →
      (∀ j ∈ S, j ∉ F → (s.proc j).state.sentEcho = some v) →
      ∃ S' : Finset P, echoThreshold (Fintype.card P) t ≤ S'.card ∧
        ∀ j ∈ S', j ∉ F → (s'.proc j).state.sentEcho = some v := fun hS hw =>
    ⟨_, hS, fun j hj hjF => recvCore_state_mono (Q := fun st => st.sentEcho = some v)
      (fun _ => brachaStep_sentEcho_mono) (hw j hj hjF)⟩
  by_cases hpd : p = dest
  · subst hpd
    simp only [s', Protocol.recvCore, Protocol.updateProc, brachaProtocol, ↓reduceIte] at hv
    rcases brachaStep_sentReady_eq_some hv with h0 | hcnt | hcnt
    · obtain ⟨S, hS, hw⟩ := hinv.readyWitness p hdest v h0; exact lift hS hw
    · refine lift hcnt fun j hjS hjF => ?_
      simp only [echoSenders, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
      exact hES_pre j hjF v hjS
    · obtain ⟨k, hkS, hkF⟩ :
          ∃ k ∈ readySenders (brachaStep dealer t (s.proc p).state src body).nextState v,
            k ∉ F := by finset_card
      simp only [readySenders, Finset.mem_filter, Finset.mem_univ, true_and] at hkS
      obtain ⟨S, hS, hw⟩ := hinv.readyWitness k hkF v (hRS_pre k hkF v hkS)
      exact lift hS hw
  · simp only [s', Protocol.recvCore, hpd, ↓reduceIte] at hv
    obtain ⟨S, hS, hw⟩ := hinv.readyWitness p hp v hv; exact lift hS hw

private lemma recvCore_outSound (hinv : BrachaInv dealer t F input s) :
    let s' := (brachaProtocol P V dealer t).recvCore src dest body mb s
    ∀ p ∉ F, ∀ v, s'.ProcDecided p v → 2 * t + 1 ≤ (readySenders (s'.proc p).state v).card := by
  intro s' p hp v hv
  by_cases hpd : p = dest
  · subst hpd
    cases hprev : (s.proc p).out with
    | some u =>
      obtain rfl : u = v := Option.some.inj ((recvCore_procDecided_mono hprev).symm.trans hv)
      refine (hinv.outSound p hp u hprev).trans (Finset.card_le_card fun j hj => ?_)
      simp only [readySenders, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact recvCore_state_mono (Q := fun st => st.readyFrom j = some u)
        (fun _ => brachaStep_readyFrom_mono) hj
    | none =>
      have hdel : (brachaStep dealer t (s.proc p).state src body).delivered = some v := by
        simpa [s', State.ProcDecided, Protocol.recvCore, Protocol.updateProc, hprev,
          brachaProtocol] using hv
      simp only [s', Protocol.recvCore, Protocol.updateProc, brachaProtocol, ↓reduceIte]
      cases body with
      | initial _ | echo _ => dsimp only [brachaStep] at hdel; split_ifs at hdel
      | ready _ =>
        dsimp only [brachaStep] at hdel ⊢
        by_cases h1 : ((s.proc p).state.readyFrom src).isNone = true
        · simp only [h1, ↓reduceIte] at hdel ⊢; split_ifs at hdel with h2; cases hdel
          split_ifs <;> exact h2
        · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hdel; cases hdel
  · simp only [s', State.ProcDecided, Protocol.recvCore, hpd, ↓reduceIte] at hv ⊢
    exact hinv.outSound p hp v hv

private lemma recvCore_outSat (hF : F.card ≤ t) (hinv : BrachaInv dealer t F input s)
    (hRS_pre : ∀ j ∉ F, ∀ v,
      (brachaStep dealer t (s.proc dest).state src body).nextState.readyFrom j = some v →
        (s.proc j).state.sentReady = some v) :
    let s' := (brachaProtocol P V dealer t).recvCore src dest body mb s
    ∀ p ∉ F, ∀ v, 2 * t + 1 ≤ (readySenders (s'.proc p).state v).card → s'.ProcDecided p v := by
  intro s' p hp v hcnt
  by_cases hpd : p = dest
  · subst hpd
    simp only [s', Protocol.recvCore, Protocol.updateProc, brachaProtocol, ↓reduceIte] at hcnt
    cases hprev : (s.proc p).out with
    | some u =>
      obtain ⟨k₁, hk₁, hr₁⟩ := hinv.out_has_honest_ready hF hp hprev
      obtain ⟨k₂, hk₂S, hk₂F⟩ :
          ∃ k₂ ∈ readySenders (brachaStep dealer t (s.proc p).state src body).nextState v,
            k₂ ∉ F := by finset_card
      simp only [readySenders, Finset.mem_filter, Finset.mem_univ, true_and] at hk₂S
      obtain rfl := hinv.ready_unique hF hk₁ hk₂F hr₁ (hRS_pre k₂ hk₂F v hk₂S)
      exact recvCore_procDecided_mono hprev
    | none =>
      by_cases hbm : body = .ready v
      · subst hbm
        rcases brachaStep_deliver_sat hcnt with h0 | hdel
        · exact recvCore_procDecided_mono (hinv.outSat p hp v h0)
        · simpa [s', State.ProcDecided, Protocol.recvCore, Protocol.updateProc, hprev,
            brachaProtocol] using hdel
      · rw [brachaStep_readySenders_card_eq hbm] at hcnt
        exact recvCore_procDecided_mono (hinv.outSat p hp v hcnt)
  · simp only [s', State.ProcDecided, Protocol.recvCore, hpd, ↓reduceIte] at hcnt ⊢
    exact hinv.outSat p hp v hcnt

end RecvCore

private lemma brachaInv_recvCore (hF : F.card ≤ t)
    {s : State P (BrachaState P V) (BrachaMsg V) V} (hinv : BrachaInv dealer t F input s)
    {src dest : P} (hdest : dest ∉ F) {body : BrachaMsg V}
    {msgsBase : Multiset (Envelope P (BrachaMsg V))}
    (hle : msgsBase ≤ s.msgs)
    (hdrop : ∀ e ∈ s.msgs, e ∉ msgsBase → e = ⟨src, dest, body⟩)
    (hauth : src ∉ F →
      (∀ v, body = .initial v → src = dealer ∧ input = some v) ∧
      (∀ v, body = .echo v → (s.proc src).state.sentEcho = some v) ∧
      (∀ v, body = .ready v → (s.proc src).state.sentReady = some v)) :
    BrachaInv dealer t F input
      ((brachaProtocol P V dealer t).recvCore src dest body msgsBase s) := by
  let s' := (brachaProtocol P V dealer t).recvCore src dest body msgsBase s
  let res := brachaStep dealer t (s.proc dest).state src body
  have hst : (s'.proc dest).state = res.nextState := by
    simp [s', Protocol.recvCore, Protocol.updateProc, brachaProtocol, res]
  have hES_pre : ∀ j ∉ F, ∀ v, res.nextState.echoFrom j = some v →
      (s.proc j).state.sentEcho = some v := by
    intro j hj v hv
    dsimp only [res] at hv
    rw [brachaStep_echoFrom_eq] at hv
    cases body with
    | echo w =>
      exact (optUpdate_eq_some hv).elim (hinv.echoSound dest hdest j hj v) fun ⟨hjs, hw⟩ =>
        hjs ▸ hw ▸ (hauth (hjs ▸ hj)).2.1 w rfl
    | _ => exact hinv.echoSound dest hdest j hj v hv
  have hRS_pre : ∀ j ∉ F, ∀ v, res.nextState.readyFrom j = some v →
      (s.proc j).state.sentReady = some v := by
    intro j hj v hv
    dsimp only [res] at hv
    rw [brachaStep_readyFrom_eq] at hv
    cases body with
    | ready w =>
      exact (optUpdate_eq_some hv).elim (hinv.readySound dest hdest j hj v) fun ⟨hjs, hw⟩ =>
        hjs ▸ hw ▸ (hauth (hjs ▸ hj)).2.2 w rfl
    | _ => exact hinv.readySound dest hdest j hj v hv
  have hspec := brachaStep_outgoing_spec (dealer := dealer) (t := t) (st := (s.proc dest).state)
    (src := src) (body := body)
  have hmem_s' : ∀ e ∈ s'.msgs, e ∈ s.msgs ∨ (e.src = dest ∧
      ((∃ v, e.body = .echo v ∧ (s'.proc dest).state.sentEcho = some v) ∨
       (∃ v, e.body = .ready v ∧ (s'.proc dest).state.sentReady = some v))) := fun e he => by
    rcases Multiset.mem_add.mp he with he | he
    · exact Or.inl (Multiset.mem_of_le hle he)
    · obtain ⟨qm, hqm, rfl⟩ := Multiset.mem_map.mp he
      dsimp only [brachaProtocol] at hqm
      rcases hspec with ⟨h0, _⟩ | ⟨v, ho, _, hs, _⟩ | ⟨v, ho, _, hs, _⟩
      · simp [h0] at hqm
      · rw [ho] at hqm; obtain ⟨_, _, rfl⟩ := Multiset.mem_map.mp hqm
        exact Or.inr ⟨rfl, Or.inl ⟨v, rfl, hst ▸ hs⟩⟩
      · rw [ho] at hqm; obtain ⟨_, _, rfl⟩ := Multiset.mem_map.mp hqm
        exact Or.inr ⟨rfl, Or.inr ⟨v, rfl, hst ▸ hs⟩⟩
  refine
    { srcNotF := fun e he => (hmem_s' e he).elim (hinv.srcNotF e) fun ⟨hs, _⟩ => hs ▸ hdest
      initMsg := fun e he v hv => by
        rcases hmem_s' e he with he | ⟨_, ⟨_, hb, _⟩ | ⟨_, hb, _⟩⟩
        · exact hinv.initMsg e he v hv
        all_goals cases hv.symm.trans hb
      echoMsg := fun e he v hv => by
        rcases hmem_s' e he with he | ⟨rfl, ⟨_, hb, hs⟩ | ⟨_, hb, _⟩⟩
        · exact recvCore_state_mono (Q := fun st => st.sentEcho = some v)
            (fun _ => brachaStep_sentEcho_mono) (hinv.echoMsg e he v hv)
        · cases hv.symm.trans hb; exact hs
        · cases hv.symm.trans hb
      readyMsg := fun e he v hv => by
        rcases hmem_s' e he with he | ⟨rfl, ⟨_, hb, _⟩ | ⟨_, hb, hs⟩⟩
        · exact recvCore_state_mono (Q := fun st => st.sentReady = some v)
            (fun _ => brachaStep_sentReady_mono) (hinv.readyMsg e he v hv)
        · cases hv.symm.trans hb
        · cases hv.symm.trans hb; exact hs
      echoDealer := fun hd p hp v hv => by
        by_cases hpd : p = dest
        · subst hpd; rw [hst] at hv
          cases body with
          | initial w =>
            dsimp only [res, brachaStep] at hv; split_ifs at hv with hc
            · cases hv; exact ((hauth (hc.1 ▸ hd)).1 v rfl).2
            · exact hinv.echoDealer hd p hp v hv
          | echo _ | ready _ =>
            dsimp only [res, brachaStep] at hv
            split_ifs at hv <;> exact hinv.echoDealer hd p hp v hv
        · simp only [Protocol.recvCore, hpd, ↓reduceIte] at hv; exact hinv.echoDealer hd p hp v hv
      echoSound := fun p hp j hj v hv => recvCore_state_mono (Q := fun st => st.sentEcho = some v)
        (fun _ => brachaStep_sentEcho_mono) (by
          by_cases hpd : p = dest
          · subst hpd; exact hES_pre j hj v (hst ▸ hv)
          · simp only [Protocol.recvCore, hpd, ↓reduceIte] at hv
            exact hinv.echoSound p hp j hj v hv)
      readySound := fun p hp j hj v hv => recvCore_state_mono
        (Q := fun st => st.sentReady = some v) (fun _ => brachaStep_sentReady_mono) (by
          by_cases hpd : p = dest
          · subst hpd; exact hRS_pre j hj v (hst ▸ hv)
          · simp only [Protocol.recvCore, hpd, ↓reduceIte] at hv
            exact hinv.readySound p hp j hj v hv)
      readyWitness := recvCore_readyWitness hF hinv hdest hES_pre hRS_pre
      outSound := recvCore_outSound hinv
      echoSat := fun p hp v => recvCore_sat_sentReady (fun st v => (echoSenders st v).card)
        (.echo v) (hinv.echoSat p hp v) brachaStep_echoSenders_card_eq
        (fun hbm hsr hcnt => by rw [hbm] at hcnt ⊢; exact brachaStep_echo_sat_none hsr hcnt)
        (fun u hsr hcnt => hinv.witness_unique hF hcnt (fun j hj hjF => by
          simp only [echoSenders, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact hES_pre j hjF v hj) hdest hsr)
      readySat := fun p hp v => recvCore_sat_sentReady (fun st v => (readySenders st v).card)
        (.ready v) (hinv.readySat p hp v) brachaStep_readySenders_card_eq
        (fun hbm hsr hcnt => by rw [hbm] at hcnt ⊢; exact brachaStep_ready_sat_none hsr hcnt)
        (fun u hsr hcnt => by
          obtain ⟨k, hkS, hkF⟩ :
              ∃ k ∈ readySenders (brachaStep dealer t (s.proc dest).state src body).nextState v,
                k ∉ F := by finset_card
          simp only [readySenders, Finset.mem_filter, Finset.mem_univ, true_and] at hkS
          exact (hinv.ready_unique hF hdest hkF hsr (hRS_pre k hkF v hkS)).symm)
      outSat := recvCore_outSat hF hinv hRS_pre
      initLive := fun hd v hinp q hq =>
        recvCore_live_keep (fld := BrachaState.sentEcho) (hinv.initLive hd v hinp q hq) hdrop
          (fun _ _ _ => brachaStep_sentEcho_mono)
          (fun hse => by simp [brachaStep, hse])
          (fun u hse => Option.some.inj ((hinv.echoDealer hd q hq u hse).symm.trans hinp))
      echoLive := fun p hp v hv q hq => recvCore_live_sent BrachaState.sentEcho
        BrachaState.echoFrom .echo hv (fun h => hinv.echoLive p hp v h q hq) hdrop
        (fun _ _ _ => brachaStep_echoFrom_mono) (fun hef => by simp [brachaStep_echoFrom_eq, hef])
        (fun u => hinv.echoSound q hq p hp u) fun hnew hold =>
          hspec.elim (fun ⟨_, he, _⟩ => absurd (he.symm.trans hnew) hold) fun h =>
            h.elim (fun ⟨_, ho, _, he, _⟩ => by cases he.symm.trans hnew; exact ho)
              (fun ⟨_, _, _, _, he⟩ => absurd (he.symm.trans hnew) hold)
      readyLive := fun p hp v hv q hq => recvCore_live_sent BrachaState.sentReady
        BrachaState.readyFrom .ready hv (fun h => hinv.readyLive p hp v h q hq) hdrop
        (fun _ _ _ => brachaStep_readyFrom_mono)
        (fun hrf => by simp [brachaStep_readyFrom_eq, hrf])
        (fun u => hinv.readySound q hq p hp u) fun hnew hold =>
          hspec.elim (fun ⟨_, _, hr⟩ => absurd (hr.symm.trans hnew) hold) fun h =>
            h.elim (fun ⟨_, _, _, _, hr⟩ => absurd (hr.symm.trans hnew) hold)
              (fun ⟨_, ho, _, hr, _⟩ => by cases hr.symm.trans hnew; exact ho) }

private lemma brachaInv_tr (hF : F.card ≤ t) :
    ((brachaProtocol P V dealer t).lts F).TrInv (BrachaInv dealer t F input) := by
  intro s a s' htr hinv
  cases a with
  | deliver e =>
    obtain ⟨hmem, hdest, rfl⟩ := htr
    exact brachaInv_recvCore hF hinv hdest (Multiset.erase_le e s.msgs)
      (fun _ hm hne => by_contra fun hneq => hne ((Multiset.mem_erase_of_ne hneq).mpr hm))
      (fun _ => ⟨fun v => hinv.initMsg e hmem v, fun v => hinv.echoMsg e hmem v,
        fun v => hinv.readyMsg e hmem v⟩)
  | byzRecv src dest body =>
    obtain ⟨hsrcF, hdest, rfl⟩ := htr
    exact brachaInv_recvCore hF hinv hdest le_rfl (fun _ => absurd) (fun h => absurd hsrcF h)
  | stutter => obtain rfl := htr; exact hinv

private lemma brachaInv_reachable (hF : F.card ≤ t)
    {s : State P (BrachaState P V) (BrachaMsg V) V}
    (hr : (brachaProtocol P V dealer t).Reachable F input s) :
    BrachaInv dealer t F input s :=
  let ⟨_, hxl⟩ := hr
  LTS.mtrInv_of_trInv (brachaInv_tr hF) _ _ _ hxl (brachaInv_start F input)

private lemma brachaInv_run (hF : F.card ≤ t)
    {ss : ωSequence (State P (BrachaState P V) (BrachaMsg V) V)}
    {xs : ωSequence (Action P (BrachaMsg V))}
    (ha : (brachaProtocol P V dealer t).AdmissibleRun F input ss xs) (k : ℕ) :
    BrachaInv dealer t F input (ss k) :=
  brachaInv_reachable hF ((brachaProtocol P V dealer t).admissibleRun_reachable ha k)

end BrachaInvariant

/-! ### Liveness helpers and uniform stabilization -/

section Liveness

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
  {dealer : P} {t : ℕ} {F : Finset P} {input : Option V}
  {ss : ωSequence (State P (BrachaState P V) (BrachaMsg V) V)}
  {xs : ωSequence (Action P (BrachaMsg V))}

private lemma bracha_omega_proc_mono
    (hexec : ((brachaProtocol P V dealer t).lts F).OmegaExecution ss xs)
    (Q : BrachaState P V → Prop)
    (hQ : ∀ st src m, Q st → Q (brachaStep dealer t st src m).nextState)
    {k j : ℕ} (hkj : k ≤ j) {p : P} (h : Q ((ss k).proc p).state) :
    Q ((ss j).proc p).state := by
  induction j, hkj using Nat.le_induction with
  | base => exact h
  | succ j _ ih =>
    have htr := hexec j
    cases hact : xs j with
    | deliver _ | byzRecv _ _ _ =>
      rw [hact] at htr; obtain ⟨_, _, hnext⟩ := htr
      exact hnext ▸ recvCore_state_mono (fun _ => hQ _ _ _) ih
    | stutter => rw [hact] at htr; exact htr ▸ ih

/-- Shared fairness-step helper: if either `e ∈ (ss k).msgs` or `Q (ss k)` already holds, and
delivering `e` at step `j ≥ k` establishes `Q`, then `Q` holds at some step `j`. -/
private lemma eventual_of_mem_or (ha : (brachaProtocol P V dealer t).AdmissibleRun F input ss xs)
    {e : Envelope P (BrachaMsg V)} (hdest : e.dest ∉ F) {k : ℕ} {Q : BrachaState P V → Prop}
    (hor : e ∈ (ss k).msgs ∨ Q ((ss k).proc e.dest).state)
    (hstep : ∀ j, k ≤ j → BrachaInv dealer t F input (ss j) →
      Q (brachaStep dealer t ((ss j).proc e.dest).state e.src e.body).nextState)
    (hF : F.card ≤ t) :
    ∃ j, Q ((ss j).proc e.dest).state := by
  rcases hor with hmem | hdone
  · obtain ⟨j, hkj, hj⟩ := ha.2.2 e hdest k hmem
    obtain ⟨_, _, hnext⟩ := hj ▸ ha.2.1 j
    refine ⟨j + 1, ?_⟩
    simp only [hnext, Protocol.recvHonest, Protocol.recvCore, Protocol.updateProc, brachaProtocol,
      ↓reduceIte]
    exact hstep j hkj (brachaInv_run hF ha j)
  · exact ⟨k, hdone⟩

/-- Collect a uniform time `K` at which a monotone per-sender table (`echoFrom` or `readyFrom`)
records `some v` for every sender `r ∈ R`. -/
private lemma eventual_filter_card
    (hexec : ((brachaProtocol P V dealer t).lts F).OmegaExecution ss xs)
    (tbl : BrachaState P V → P → Option V)
    (hmono : ∀ st src m j v, tbl st j = some v →
      tbl (brachaStep dealer t st src m).nextState j = some v)
    (R : Finset P) (p : P) (v : V)
    (hev : ∀ r ∈ R, ∃ k, tbl ((ss k).proc p).state r = some v) :
    ∃ K, R.card ≤ (Finset.univ.filter fun r => tbl ((ss K).proc p).state r = some v).card := by
  let pick : R → ℕ := fun r => Classical.choose (hev r.1 r.2)
  refine ⟨R.attach.sup pick, Finset.card_le_card fun r hr => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact bracha_omega_proc_mono hexec (fun st => tbl st r = some v) (fun _ _ _ => hmono _ _ _ _ _)
    (Finset.le_sup (f := pick) (Finset.mem_attach R ⟨r, hr⟩)) (Classical.choose_spec (hev r hr))

private lemma eventual_readyFrom (hF : F.card ≤ t)
    (ha : (brachaProtocol P V dealer t).AdmissibleRun F input ss xs)
    {p q : P} (hp : p ∉ F) (hq : q ∉ F) {k : ℕ} {v : V}
    (hk : ((ss k).proc p).state.sentReady = some v) :
    ∃ j, ((ss j).proc q).state.readyFrom p = some v := by
  refine eventual_of_mem_or (Q := fun st => st.readyFrom p = some v) ha hq
    ((brachaInv_run hF ha k).readyLive p hp v hk q hq) (fun j hkj hinvj => ?_) hF
  cases hrf : ((ss j).proc q).state.readyFrom p with
  | none => simp [brachaStep_readyFrom_eq, hrf]
  | some u =>
    obtain rfl := Option.some.inj ((hinvj.readySound q hq p hp u hrf).symm.trans
      (bracha_omega_proc_mono ha.2.1 (fun st => st.sentReady = some v)
        (fun _ _ _ => brachaStep_sentReady_mono) hkj hk))
    exact brachaStep_readyFrom_mono hrf

private lemma eventual_deliver_of_all_ready (hnt : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    (ha : (brachaProtocol P V dealer t).AdmissibleRun F input ss xs)
    {v : V} (hready : ∀ p ∉ F, ∃ k, ((ss k).proc p).state.sentReady = some v)
    {q : P} (hq : q ∉ F) :
    ∃ k, (ss k).ProcDecided q v := by
  obtain ⟨K, hK⟩ := eventual_filter_card ha.2.1 BrachaState.readyFrom
    (fun _ _ _ _ _ => brachaStep_readyFrom_mono) (Finset.univ \ F) q v fun p hp => by
      obtain ⟨k, hk⟩ := hready p (Finset.mem_sdiff.mp hp).2
      exact eventual_readyFrom hF ha (Finset.mem_sdiff.mp hp).2 hq hk
  have hcard : 2 * t + 1 ≤ (Finset.univ \ F).card := by finset_card
  exact ⟨K, (brachaInv_run hF ha K).outSat q hq v (hcard.trans hK)⟩

end Liveness

/-! ### Correctness theorem (`n > 3t`) -/

/-- **Bracha's reliable broadcast correctness theorem** ([Bracha1987]). For any finite `P` with
`3 * t < Fintype.card P`, arbitrary value type `V` (no finiteness assumption on `V`), and any
broadcaster `dealer : P`, the streamlined three-phase protocol `brachaProtocol P V dealer t`
solves asynchronous Byzantine reliable broadcast against `t` static Byzantine faults. -/
theorem solvesReliableBroadcast_bracha {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {t : ℕ} (hnt : 3 * t < Fintype.card P) :
    (brachaProtocol P V dealer t).SolvesReliableBroadcast t where
  consistency F hF input s hr i hi j hj v₁ v₂ h₁ h₂ := by
    have hinv := brachaInv_reachable hF hr
    obtain ⟨k₁, hk₁, hr₁⟩ := hinv.out_has_honest_ready hF hi h₁
    obtain ⟨k₂, hk₂, hr₂⟩ := hinv.out_has_honest_ready hF hj h₂
    exact hinv.ready_unique hF hk₁ hk₂ hr₁ hr₂
  noSpurious F hF hd input s hr i hi v hv := by
    have hinv := brachaInv_reachable hF hr
    obtain ⟨k, hk, hrk⟩ := hinv.out_has_honest_ready hF hi hv
    obtain ⟨S, hS, hw⟩ := hinv.readyWitness k hk v hrk
    obtain ⟨j, hjS, hjF⟩ : ∃ j ∈ S, j ∉ F := by finset_card [echoThreshold]
    exact hinv.echoDealer hd j hjF v (hw j hjS hjF)
  validity F hF hd v ss xs ha q hq := by
    have hcard : echoThreshold (Fintype.card P) t ≤ (Finset.univ \ F).card := by
      finset_card [echoThreshold]
    have hevent_echo : ∀ r ∉ F, ∃ k, ((ss k).proc r).state.sentEcho = some v := fun r hr =>
      eventual_of_mem_or (Q := fun st => st.sentEcho = some v) ha hr
        ((brachaInv_run hF ha 0).initLive hd v rfl r hr) (fun j _ hinvj => by
          cases hse : ((ss j).proc r).state.sentEcho with
          | none => simp [brachaStep, hse]
          | some u =>
            cases hinvj.echoDealer hd r hr u hse; exact brachaStep_sentEcho_mono hse) hF
    refine eventual_deliver_of_all_ready hnt hF ha (fun p hp => ?_) hq
    obtain ⟨K, hK⟩ := eventual_filter_card ha.2.1 BrachaState.echoFrom
      (fun _ _ _ _ _ => brachaStep_echoFrom_mono) (Finset.univ \ F) p v fun r hr => by
        have hrF : r ∉ F := (Finset.mem_sdiff.mp hr).2
        obtain ⟨k, hk⟩ := hevent_echo r hrF
        refine eventual_of_mem_or (Q := fun st => st.echoFrom r = some v) ha hp
          ((brachaInv_run hF ha k).echoLive r hrF v hk p hp) (fun j _ hinvj => ?_) hF
        cases hef : ((ss j).proc p).state.echoFrom r with
        | none => simp [brachaStep_echoFrom_eq, hef]
        | some u =>
          cases hinvj.echoDealer hd r hrF u (hinvj.echoSound p hp r hrF u hef)
          exact brachaStep_echoFrom_mono hef
    exact ⟨K, (brachaInv_run hF ha K).echoSat p hp v (hcard.trans hK)⟩
  totality F hF input ss xs ha i hi k v hv q hq := by
    have hinvk := brachaInv_run hF ha k
    let R : Finset P := readySenders ((ss k).proc i).state v \ F
    have hcard : t + 1 ≤ R.card := by
      have := hinvk.outSound i hi v hv; finset_card
    refine eventual_deliver_of_all_ready hnt hF ha (fun p hp => ?_) hq
    obtain ⟨K, hK⟩ := eventual_filter_card ha.2.1 BrachaState.readyFrom
      (fun _ _ _ _ _ => brachaStep_readyFrom_mono) R p v fun r hr => by
        simp only [R, Finset.mem_sdiff, readySenders, Finset.mem_filter, Finset.mem_univ,
          true_and] at hr
        exact eventual_readyFrom hF ha hr.2 hp (hinvk.readySound i hi r hr.2 v hr.1)
    exact ⟨K, (brachaInv_run hF ha K).readySat p hp v (hcard.trans hK)⟩

/-! ### Exact `O(n²)` communication complexity -/

section Complexity

variable {P V : Type*} [Fintype P] [DecidableEq P]

private def sentFieldCount (F : Finset P) (field : BrachaState P V → Option V)
    (s : State P (BrachaState P V) (BrachaMsg V) V) : ℕ :=
  (Finset.univ.filter fun p => p ∉ F ∧ (field (s.proc p).state).isSome).card

private lemma sentFieldCount_congr (F : Finset P) (field : BrachaState P V → Option V)
    {s s' : State P (BrachaState P V) (BrachaMsg V) V} {dest : P}
    (hne : ∀ y ≠ dest, (s'.proc y).state = (s.proc y).state)
    (heq : (field (s'.proc dest).state).isSome = (field (s.proc dest).state).isSome) :
    sentFieldCount F field s' = sentFieldCount F field s := by
  unfold sentFieldCount; congr 1; ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hy : y = dest <;> simp [hy, heq, hne]

private lemma sentFieldCount_inc (F : Finset P) (field : BrachaState P V → Option V)
    {s s' : State P (BrachaState P V) (BrachaMsg V) V} {dest : P} (hdest : dest ∉ F)
    (hne : ∀ y ≠ dest, (s'.proc y).state = (s.proc y).state)
    (h0 : field (s.proc dest).state = none) (h1 : (field (s'.proc dest).state).isSome = true) :
    sentFieldCount F field s' = sentFieldCount F field s + 1 := by
  have heq : (Finset.univ.filter fun y => y ∉ F ∧ (field (s'.proc y).state).isSome = true) =
      insert dest (Finset.univ.filter fun y => y ∉ F ∧ (field (s.proc y).state).isSome = true) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hy : y = dest <;> simp [hy, hdest, h1, hne]
  unfold sentFieldCount; rw [heq, Finset.card_insert_of_notMem]; simp [h0]

private lemma brachaStep_sent_telescopes [DecidableEq V] (dealer : P) (t : ℕ) (F : Finset P)
    (s : State P (BrachaState P V) (BrachaMsg V) V) (src dest : P) (hdest : dest ∉ F)
    (body : BrachaMsg V) (msgsBase : Multiset (Envelope P (BrachaMsg V))) :
    let s' := (brachaProtocol P V dealer t).recvCore src dest body msgsBase s
    (brachaStep dealer t (s.proc dest).state src body).outgoing.card +
      Fintype.card P * (sentFieldCount F BrachaState.sentEcho s +
        sentFieldCount F BrachaState.sentReady s) =
      Fintype.card P * (sentFieldCount F BrachaState.sentEcho s' +
        sentFieldCount F BrachaState.sentReady s') := by
  intro s'
  have hne : ∀ y ≠ dest, (s'.proc y).state = (s.proc y).state := fun y hy => by
    simp [s', Protocol.recvCore, hy]
  have hst : (s'.proc dest).state =
      (brachaStep dealer t (s.proc dest).state src body).nextState := by
    simp [s', Protocol.recvCore, Protocol.updateProc, brachaProtocol]
  rcases brachaStep_outgoing_spec (dealer := dealer) (t := t) (st := (s.proc dest).state)
      (src := src) (body := body) with
    ⟨ho, hE, hR⟩ | ⟨_, ho, hE0, hE1, hR⟩ | ⟨_, ho, hR0, hR1, hE⟩
  · rw [ho, Multiset.card_zero, zero_add,
      sentFieldCount_congr F BrachaState.sentEcho hne (by rw [hst, hE]),
      sentFieldCount_congr F BrachaState.sentReady hne (by rw [hst, hR])]
  · rw [ho, card_broadcastAll,
      sentFieldCount_inc F BrachaState.sentEcho hdest hne hE0 (by rw [hst, hE1]; rfl),
      sentFieldCount_congr F BrachaState.sentReady hne (by rw [hst, hR]),
      Nat.add_right_comm, Nat.mul_succ, Nat.add_comm]
  · rw [ho, card_broadcastAll,
      sentFieldCount_congr F BrachaState.sentEcho hne (by rw [hst, hE]),
      sentFieldCount_inc F BrachaState.sentReady hdest hne hR0 (by rw [hst, hR1]; rfl),
      ← Nat.add_assoc, Nat.mul_succ, Nat.add_comm]

private lemma brachaTraceSent_eq [DecidableEq V] {dealer : P} {t : ℕ} {F : Finset P}
    {s₀ s₁ : State P (BrachaState P V) (BrachaMsg V) V} {xl : List (Action P (BrachaMsg V))}
    (hmtr : ((brachaProtocol P V dealer t).lts F).MTr s₀ xl s₁) :
    (brachaProtocol P V dealer t).traceSent s₀ xl +
        Fintype.card P * (sentFieldCount F BrachaState.sentEcho s₀ +
          sentFieldCount F BrachaState.sentReady s₀) =
      Fintype.card P * (sentFieldCount F BrachaState.sentEcho s₁ +
        sentFieldCount F BrachaState.sentReady s₁) := by
  induction hmtr with
  | refl => simp [Protocol.traceSent]
  | @stepL s a s' xl' s₁ htr _ ih =>
    cases a with
    | deliver e =>
      obtain ⟨_, hdest, rfl⟩ := htr
      have hstep := brachaStep_sent_telescopes dealer t F s e.src e.dest hdest e.body
        (s.msgs.erase e)
      simp only [Protocol.traceSent, brachaProtocol]
      rw [Nat.add_right_comm, show _ = _ from hstep, Nat.add_comm]; exact ih
    | byzRecv src dest body =>
      obtain ⟨_, hdest, rfl⟩ := htr
      have hstep := brachaStep_sent_telescopes dealer t F s src dest hdest body s.msgs
      simp only [Protocol.traceSent, brachaProtocol]
      rw [Nat.add_right_comm, show _ = _ from hstep, Nat.add_comm]; exact ih
    | stutter => obtain rfl := htr; exact ih

end Complexity

/-- **Exact message-complexity bound** for the streamlined `brachaProtocol`: across **any** finite
execution trace `xl` (independent of trace length, fault threshold `t`, or Byzantine flooding),
correct processes emit at most `n + 2 * (n - F.card) * n` authentic envelopes in total
(`initial` + `echo` + `ready`). -/
theorem brachaSentInTrace_le {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (dealer : P) (t : ℕ) (F : Finset P) (input : Option V)
    {s : State P (BrachaState P V) (BrachaMsg V) V} {xl : List (Action P (BrachaMsg V))}
    (hmtr : ((brachaProtocol P V dealer t).lts F).MTr
      ((brachaProtocol P V dealer t).start F input) xl s) :
    (brachaProtocol P V dealer t).sentInTrace F input xl ≤
      Fintype.card P + 2 * (Fintype.card P - F.card) * Fintype.card P := by
  have hinit_card : ((brachaProtocol P V dealer t).start F input).msgs.card ≤ Fintype.card P := by
    have hbind : ((brachaProtocol P V dealer t).start F input).msgs.card =
        Finset.univ.sum fun p =>
          (if p ∈ F then (0 : Multiset (Envelope P (BrachaMsg V)))
            else ((brachaProtocol P V dealer t).initSend input p).map (tagSender p)).card := by
      simp [Protocol.start, Multiset.card_bind]
    rw [hbind, Finset.sum_eq_single dealer
      (fun p _ hp => by simp [Protocol.initSend, brachaProtocol, hp])
      (fun h => absurd (Finset.mem_univ dealer) h)]
    by_cases hd : dealer ∈ F
    · simp [hd]
    · cases input <;> simp [hd, Protocol.initSend, brachaProtocol]
  have h0 : ∀ field, field (brachaInit P V) = none →
      sentFieldCount F field ((brachaProtocol P V dealer t).start F input) = 0 := fun field hf => by
    simp [sentFieldCount, Protocol.start, Protocol.initState, brachaProtocol, hf]
  have hsum := brachaTraceSent_eq hmtr
  rw [h0 _ rfl, h0 _ rfl, add_zero, mul_zero, add_zero] at hsum
  have hbound : ∀ field, sentFieldCount F field s ≤ Fintype.card P - F.card := fun field =>
    (Finset.card_le_card (t := Finset.univ \ F) fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp; simp [hp.1]).trans
      (by simp [Finset.card_sdiff])
  have hmul : Fintype.card P * (sentFieldCount F BrachaState.sentEcho s +
      sentFieldCount F BrachaState.sentReady s) ≤ 2 * (Fintype.card P - F.card) * Fintype.card P :=
    Nat.mul_comm (2 * (Fintype.card P - F.card)) _ ▸ Nat.mul_le_mul_left _
      (by have := hbound BrachaState.sentEcho; have := hbound BrachaState.sentReady; omega)
  simpa [Protocol.sentInTrace, hsum] using Nat.add_le_add hinit_card hmul

/-! ### Exact threshold characterization -/

/-- **Exact solvability threshold for asynchronous Byzantine reliable broadcast.**
For any finite process type `P` with distinguished broadcaster `dealer : P` and any **nonempty**
value domain `V` in the same universe (including a singleton such as `Unit`), a deterministic
asynchronous protocol solving reliable broadcast against `t` static Byzantine faults exists
**if and only if** `Fintype.card P ≤ 2` or `3 * t < Fintype.card P`.

- `3 * t < Fintype.card P`: witnessed by `brachaProtocol` (`solvesReliableBroadcast_bracha`,
  [Bracha1987]).
- `3 ≤ Fintype.card P ≤ 3 * t`: refuted by `Protocol.not_solvesReliableBroadcast`
  ([BrachaToueg1985]; [Bracha1987]).
- `Fintype.card P ≤ 2`: degenerate case where a faulty `dealer` leaves at most one correct
  process, witnessed by `directProtocol` (`solvesReliableBroadcast_direct_of_card_le_two`). -/
theorem exists_solvesReliableBroadcast_iff.{u} (P V : Type u) [Fintype P] [DecidableEq P]
    [Nonempty V] (dealer : P) (t : ℕ) :
    (∃ (S M : Type u) (_ : DecidableEq M) (π : Protocol P S M V dealer),
      π.SolvesReliableBroadcast t) ↔
      Fintype.card P ≤ 2 ∨ 3 * t < Fintype.card P := by
  classical
  constructor
  · rintro ⟨S, M, _, π, hsol⟩
    by_contra! h
    exact π.not_solvesReliableBroadcast (by omega) h.2 hsol
  · rintro (h2 | h3t)
    · exact ⟨PUnit.{u + 1}, V, inferInstance, directProtocol P V dealer,
        solvesReliableBroadcast_direct_of_card_le_two dealer h2 t⟩
    · exact ⟨BrachaState P V, BrachaMsg V, inferInstance, brachaProtocol P V dealer t,
        solvesReliableBroadcast_bracha h3t⟩

end Cslib.Distributed.AsyncByzantine
