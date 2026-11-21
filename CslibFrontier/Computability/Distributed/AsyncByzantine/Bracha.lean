/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.AsyncByzantine.Basic
import CslibFrontier.Computability.Distributed.AsyncByzantine.Impossibility
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

private lemma lt_two_mul_echoThreshold (n t : ℕ) : n + t < 2 * echoThreshold n t := by
  simp only [echoThreshold]; omega

private lemma echoThreshold_le_sub {n t : ℕ} (h : 3 * t < n) : echoThreshold n t ≤ n - t := by
  simp only [echoThreshold]; omega

private lemma lt_echoThreshold {n t : ℕ} (h : 3 * t < n) : t < echoThreshold n t := by
  simp only [echoThreshold]; omega

/-- Any two echo quorums (of size at least `echoThreshold |P| t`) share a correct process
(`∉ F`) when `F.card ≤ t`. -/
theorem echo_quorum_inter_notMem {P : Type*} [Fintype P] [DecidableEq P]
    {F S₁ S₂ : Finset P} {t : ℕ} (hF : F.card ≤ t)
    (h₁ : echoThreshold (Fintype.card P) t ≤ S₁.card)
    (h₂ : echoThreshold (Fintype.card P) t ≤ S₂.card) :
    ∃ p ∈ S₁ ∩ S₂, p ∉ F := by
  have hiu := Finset.card_union_add_card_inter S₁ S₂
  have hu : (S₁ ∪ S₂).card ≤ Fintype.card P := Finset.card_le_univ _
  have hlt := lt_two_mul_echoThreshold (Fintype.card P) t
  exact Finset.exists_mem_notMem_of_card_lt_card (by omega)

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

private lemma filter_update_ne {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {f : P → Option V} {src : P} {v w : V} (hnone : (f src).isNone = true) (hne : v ≠ w) :
    (Finset.univ.filter fun j => Function.update f src (some v) j = some w) =
      Finset.univ.filter fun j => f j = some w := by
  ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hj : j = src
  · subst hj
    simp only [Function.update_self, Option.some.injEq, hne, false_iff]
    cases h : f j <;> simp [h] at hnone ⊢
  · simp [Function.update_of_ne hj]

private lemma update_mono {P V : Type*} [DecidableEq P] {f : P → Option V} {src j : P} {u v : V}
    (hnone : (f src).isNone = true) (h : f j = some u) :
    Function.update f src (some v) j = some u := by
  by_cases hj : j = src
  · subst hj; simp [h] at hnone
  · simpa [Function.update_of_ne hj] using h

section BrachaStepSpecs

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
  {dealer : P} {t : ℕ} {st : BrachaState P V} {src : P} {body : BrachaMsg V}

private lemma brachaStep_sentEcho_mono {v : V} (h : st.sentEcho = some v) :
    (brachaStep dealer t st src body).nextState.sentEcho = some v := by
  cases body with
  | initial w => simp [brachaStep, h]
  | echo w => dsimp only [brachaStep]; split_ifs <;> exact h
  | ready w =>
    dsimp only [brachaStep]
    by_cases h1 : (st.readyFrom src).isNone = true <;> [simp only [h1, ↓reduceIte]; simp [h1, h]]
    split_ifs <;> exact h

private lemma brachaStep_sentReady_mono {v : V} (h : st.sentReady = some v) :
    (brachaStep dealer t st src body).nextState.sentReady = some v := by
  cases body with
  | initial w => dsimp only [brachaStep]; split_ifs <;> exact h
  | echo w => dsimp only [brachaStep]; split_ifs <;> simp_all
  | ready w =>
    dsimp only [brachaStep]
    by_cases h1 : (st.readyFrom src).isNone = true <;> [simp only [h1, ↓reduceIte]; simp [h1, h]]
    split_ifs with h2
    · simp [h] at h2
    · exact h

private lemma brachaStep_echoFrom_mono {j : P} {v : V} (h : st.echoFrom j = some v) :
    (brachaStep dealer t st src body).nextState.echoFrom j = some v := by
  cases body with
  | initial w => dsimp only [brachaStep]; split_ifs <;> exact h
  | echo w =>
    dsimp only [brachaStep]; split_ifs with h1 <;> first | exact update_mono h1 h | exact h
  | ready w =>
    dsimp only [brachaStep]
    by_cases h1 : (st.readyFrom src).isNone = true <;> [simp only [h1, ↓reduceIte]; simp [h1, h]]
    split_ifs <;> exact h

private lemma brachaStep_readyFrom_mono {j : P} {v : V} (h : st.readyFrom j = some v) :
    (brachaStep dealer t st src body).nextState.readyFrom j = some v := by
  cases body with
  | initial w => dsimp only [brachaStep]; split_ifs <;> exact h
  | echo w => dsimp only [brachaStep]; split_ifs <;> exact h
  | ready w =>
    dsimp only [brachaStep]
    by_cases h1 : (st.readyFrom src).isNone = true <;> [simp only [h1, ↓reduceIte]; simp [h1, h]]
    split_ifs <;> exact update_mono h1 h

private lemma brachaStep_sentEcho_eq_some {v : V}
    (h : (brachaStep dealer t st src body).nextState.sentEcho = some v) :
    st.sentEcho = some v ∨
      (body = .initial v ∧ src = dealer ∧ st.sentEcho = none ∧
        (brachaStep dealer t st src body).outgoing = broadcastAll P (.echo v)) := by
  cases body with
  | initial w =>
    dsimp only [brachaStep] at h ⊢; split_ifs at h with hc
    · cases h; exact Or.inr ⟨rfl, hc.1, Option.isNone_iff_eq_none.mp hc.2, by simp [hc]⟩
    · exact Or.inl h
  | echo w => dsimp only [brachaStep] at h; split_ifs at h <;> exact Or.inl h
  | ready w =>
    dsimp only [brachaStep] at h
    by_cases h1 : (st.readyFrom src).isNone = true
    · simp only [h1, ↓reduceIte] at h; split_ifs at h <;> exact Or.inl h
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl h

private lemma brachaStep_echoFrom_eq_some {j : P} {v : V}
    (h : (brachaStep dealer t st src body).nextState.echoFrom j = some v) :
    st.echoFrom j = some v ∨ (body = .echo v ∧ j = src ∧ (st.echoFrom src).isNone = true) := by
  cases body with
  | initial w => dsimp only [brachaStep] at h; split_ifs at h <;> exact Or.inl h
  | echo w =>
    dsimp only [brachaStep] at h
    by_cases h1 : (st.echoFrom src).isNone = true
    · simp only [h1, ↓reduceIte] at h
      have hupd : Function.update st.echoFrom src (some w) j = some v := by
        split_ifs at h <;> exact h
      by_cases hj : j = src
      · subst hj; rw [Function.update_self] at hupd; cases hupd; exact Or.inr ⟨rfl, rfl, h1⟩
      · rw [Function.update_of_ne hj] at hupd; exact Or.inl hupd
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl h
  | ready w =>
    dsimp only [brachaStep] at h
    by_cases h1 : (st.readyFrom src).isNone = true
    · simp only [h1, ↓reduceIte] at h; split_ifs at h <;> exact Or.inl h
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl h

private lemma brachaStep_readyFrom_eq_some {j : P} {v : V}
    (h : (brachaStep dealer t st src body).nextState.readyFrom j = some v) :
    st.readyFrom j = some v ∨ (body = .ready v ∧ j = src ∧ (st.readyFrom src).isNone = true) := by
  cases body with
  | initial w => dsimp only [brachaStep] at h; split_ifs at h <;> exact Or.inl h
  | echo w => dsimp only [brachaStep] at h; split_ifs at h <;> exact Or.inl h
  | ready w =>
    dsimp only [brachaStep] at h
    by_cases h1 : (st.readyFrom src).isNone = true
    · simp only [h1, ↓reduceIte] at h
      have hupd : Function.update st.readyFrom src (some w) j = some v := by
        split_ifs at h <;> exact h
      by_cases hj : j = src
      · subst hj; rw [Function.update_self] at hupd; cases hupd; exact Or.inr ⟨rfl, rfl, h1⟩
      · rw [Function.update_of_ne hj] at hupd; exact Or.inl hupd
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl h

private lemma brachaStep_sentReady_eq_some {v : V}
    (h : (brachaStep dealer t st src body).nextState.sentReady = some v) :
    st.sentReady = some v ∨
      (body = .echo v ∧ st.sentReady = none ∧
        echoThreshold (Fintype.card P) t ≤
          (echoSenders (brachaStep dealer t st src body).nextState v).card ∧
        (brachaStep dealer t st src body).outgoing = broadcastAll P (.ready v)) ∨
      (body = .ready v ∧ st.sentReady = none ∧
        t + 1 ≤ (readySenders (brachaStep dealer t st src body).nextState v).card ∧
        (brachaStep dealer t st src body).outgoing = broadcastAll P (.ready v)) := by
  cases body with
  | initial w => dsimp only [brachaStep] at h; split_ifs at h <;> exact Or.inl h
  | echo w =>
    dsimp only [brachaStep] at h ⊢
    by_cases h1 : (st.echoFrom src).isNone = true
    · simp only [h1, ↓reduceIte] at h ⊢
      split_ifs at h with h2
      · cases h; refine Or.inr (Or.inl ⟨rfl, Option.isNone_iff_eq_none.mp h2.2, ?_, by simp [h2]⟩)
        simp only [h2]; exact h2.1
      · exact Or.inl h
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl h
  | ready w =>
    dsimp only [brachaStep] at h ⊢
    by_cases h1 : (st.readyFrom src).isNone = true
    · simp only [h1, ↓reduceIte] at h ⊢
      split_ifs at h with h2
      · cases h; refine Or.inr (Or.inr ⟨rfl, Option.isNone_iff_eq_none.mp h2.2, ?_, by simp [h2]⟩)
        simp only [h2]; exact h2.1
      · exact Or.inl h
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h; exact Or.inl h

private lemma brachaStep_delivered_eq_some {v : V}
    (h : (brachaStep dealer t st src body).delivered = some v) :
    body = .ready v ∧
      2 * t + 1 ≤ (readySenders (brachaStep dealer t st src body).nextState v).card := by
  cases body with
  | initial w => dsimp only [brachaStep] at h; split_ifs at h
  | echo w => dsimp only [brachaStep] at h; split_ifs at h
  | ready w =>
    dsimp only [brachaStep] at h ⊢
    by_cases h1 : (st.readyFrom src).isNone = true
    · simp only [h1, ↓reduceIte] at h ⊢
      split_ifs at h with h2
      · cases h; refine ⟨rfl, ?_⟩
        change 2 * t + 1 ≤ (Finset.univ.filter _).card
        split_ifs <;> exact h2
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h; cases h

private lemma brachaStep_echoSenders_card_eq {v : V}
    (h : body ≠ .echo v) :
    (echoSenders (brachaStep dealer t st src body).nextState v).card =
      (echoSenders st v).card := by
  cases body with
  | initial w => dsimp only [brachaStep, echoSenders]; split_ifs <;> rfl
  | echo w =>
    have hne : w ≠ v := fun hw => h (hw ▸ rfl)
    by_cases h1 : (st.echoFrom src).isNone = true
    · have heq : (brachaStep dealer t st src (.echo w)).nextState.echoFrom =
          Function.update st.echoFrom src (some w) := by
        dsimp only [brachaStep]; simp only [h1, ↓reduceIte]; split_ifs <;> rfl
      simp only [echoSenders, heq]
      exact congrArg Finset.card (filter_update_ne h1 hne)
    · dsimp only [brachaStep, echoSenders]; simp only [h1, Bool.false_eq_true, ↓reduceIte]
  | ready w =>
    dsimp only [brachaStep, echoSenders]
    by_cases h1 : (st.readyFrom src).isNone = true
    · simp only [h1, ↓reduceIte]; split_ifs <;> rfl
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]

private lemma brachaStep_readySenders_card_eq {v : V}
    (h : body ≠ .ready v) :
    (readySenders (brachaStep dealer t st src body).nextState v).card =
      (readySenders st v).card := by
  cases body with
  | initial w => dsimp only [brachaStep, readySenders]; split_ifs <;> rfl
  | echo w => dsimp only [brachaStep, readySenders]; split_ifs <;> rfl
  | ready w =>
    have hne : w ≠ v := fun hw => h (hw ▸ rfl)
    by_cases h1 : (st.readyFrom src).isNone = true
    · have heq : (brachaStep dealer t st src (.ready w)).nextState.readyFrom =
          Function.update st.readyFrom src (some w) := by
        dsimp only [brachaStep]; simp only [h1, ↓reduceIte]; split_ifs <;> rfl
      simp only [readySenders, heq]
      exact congrArg Finset.card (filter_update_ne h1 hne)
    · dsimp only [brachaStep, readySenders]; simp only [h1, Bool.false_eq_true, ↓reduceIte]

private lemma brachaStep_echo_sat_none {v : V} (hsr : st.sentReady = none)
    (hcnt : echoThreshold (Fintype.card P) t ≤
      (echoSenders (brachaStep dealer t st src (.echo v)).nextState v).card) :
    echoThreshold (Fintype.card P) t ≤ (echoSenders st v).card ∨
      (brachaStep dealer t st src (.echo v)).nextState.sentReady = some v := by
  dsimp only [brachaStep] at hcnt ⊢
  by_cases h1 : (st.echoFrom src).isNone = true
  · simp only [h1, ↓reduceIte] at hcnt ⊢
    split_ifs with h2
    · exact Or.inr rfl
    · simp only [h2, ↓reduceIte] at hcnt
      exact absurd ⟨hcnt, by simp [hsr]⟩ h2
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hcnt; exact Or.inl hcnt

private lemma brachaStep_ready_sat_none {v : V} (hsr : st.sentReady = none)
    (hcnt : t + 1 ≤ (readySenders (brachaStep dealer t st src (.ready v)).nextState v).card) :
    t + 1 ≤ (readySenders st v).card ∨
      (brachaStep dealer t st src (.ready v)).nextState.sentReady = some v := by
  dsimp only [brachaStep] at hcnt ⊢
  by_cases h1 : (st.readyFrom src).isNone = true
  · simp only [h1, ↓reduceIte] at hcnt ⊢
    by_cases h2 : t + 1 ≤
        (readySenders { st with readyFrom := Function.update st.readyFrom src (some v) } v).card ∧
          st.sentReady.isNone = true
    · exact Or.inr (by simp [h2])
    · simp only [h2, ↓reduceIte] at hcnt
      exact absurd ⟨hcnt, by simp [hsr]⟩ h2
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

private lemma brachaStep_outgoing_mem {qm : P × BrachaMsg V}
    (h : qm ∈ (brachaStep dealer t st src body).outgoing) :
    (∃ v, qm.2 = .echo v ∧ (brachaStep dealer t st src body).nextState.sentEcho = some v) ∨
    (∃ v, qm.2 = .ready v ∧ (brachaStep dealer t st src body).nextState.sentReady = some v) := by
  cases body with
  | initial w =>
    dsimp only [brachaStep] at h ⊢; split_ifs at h with hc
    · obtain ⟨_, _, hq⟩ := Multiset.mem_map.mp h
      exact Or.inl ⟨w, congrArg Prod.snd hq.symm, by simp [hc]⟩
    · simp at h
  | echo w =>
    dsimp only [brachaStep] at h ⊢; split_ifs at h with h1 h2
    · obtain ⟨_, _, hq⟩ := Multiset.mem_map.mp h
      exact Or.inr ⟨w, congrArg Prod.snd hq.symm, by simp [h1, h2]⟩
    · simp at h
    · simp at h
  | ready w =>
    dsimp only [brachaStep] at h ⊢
    by_cases h1 : (st.readyFrom src).isNone = true
    · simp only [h1, ↓reduceIte] at h ⊢
      split_ifs at h with h2
      · obtain ⟨_, _, hq⟩ := Multiset.mem_map.mp h
        exact Or.inr ⟨w, congrArg Prod.snd hq.symm, by simp [h2]⟩
      · simp at h
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h; simp at h

private lemma brachaStep_outgoing_toggle :
    let r := brachaStep dealer t st src body
    (r.outgoing.card = 0 ∧
      r.nextState.sentEcho.isSome = st.sentEcho.isSome ∧
      r.nextState.sentReady.isSome = st.sentReady.isSome) ∨
    (r.outgoing.card = Fintype.card P ∧
      st.sentEcho = none ∧ r.nextState.sentEcho.isSome = true ∧
      r.nextState.sentReady.isSome = st.sentReady.isSome) ∨
    (r.outgoing.card = Fintype.card P ∧
      st.sentReady = none ∧ r.nextState.sentReady.isSome = true ∧
      r.nextState.sentEcho.isSome = st.sentEcho.isSome) := by
  cases body with
  | initial w =>
    dsimp only [brachaStep]; split_ifs with hc
    · exact Or.inr (Or.inl ⟨card_broadcastAll _, Option.isNone_iff_eq_none.mp hc.2, rfl, rfl⟩)
    · exact Or.inl ⟨Multiset.card_zero, rfl, rfl⟩
  | echo w =>
    dsimp only [brachaStep]; split_ifs with h1 h2
    · exact Or.inr (Or.inr ⟨card_broadcastAll _, Option.isNone_iff_eq_none.mp h2.2, rfl, rfl⟩)
    · exact Or.inl ⟨Multiset.card_zero, rfl, rfl⟩
    · exact Or.inl ⟨Multiset.card_zero, rfl, rfl⟩
  | ready w =>
    dsimp only [brachaStep]
    by_cases h1 : (st.readyFrom src).isNone = true
    · simp only [h1, ↓reduceIte]
      split_ifs with h2
      · exact Or.inr (Or.inr ⟨card_broadcastAll _, Option.isNone_iff_eq_none.mp h2.2, rfl, rfl⟩)
      · exact Or.inl ⟨Multiset.card_zero, rfl, rfl⟩
    · exact Or.inl ⟨by simp [h1], by simp [h1], by simp [h1]⟩

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

private lemma BrachaInv.witness_unique {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {t : ℕ} {F : Finset P} {input : Option V}
    {s : State P (BrachaState P V) (BrachaMsg V) V}
    (hinv : BrachaInv dealer t F input s) (hF : F.card ≤ t)
    {S : Finset P} {u v : V} (hS : echoThreshold (Fintype.card P) t ≤ S.card)
    (hw : ∀ j ∈ S, j ∉ F → (s.proc j).state.sentEcho = some v)
    {p : P} (hp : p ∉ F) (hrp : (s.proc p).state.sentReady = some u) : v = u := by
  obtain ⟨S', hS', hw'⟩ := hinv.readyWitness p hp u hrp
  obtain ⟨k, hki, hkF⟩ := echo_quorum_inter_notMem hF hS hS'
  rw [Finset.mem_inter] at hki
  exact Option.some.inj ((hw k hki.1 hkF).symm.trans (hw' k hki.2 hkF))

private lemma BrachaInv.ready_unique {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {t : ℕ} {F : Finset P} {input : Option V}
    {s : State P (BrachaState P V) (BrachaMsg V) V}
    (hinv : BrachaInv dealer t F input s) (hF : F.card ≤ t)
    {p q : P} (hp : p ∉ F) (hq : q ∉ F) {v₁ v₂ : V}
    (h₁ : (s.proc p).state.sentReady = some v₁) (h₂ : (s.proc q).state.sentReady = some v₂) :
    v₁ = v₂ := by
  obtain ⟨S, hS, hw⟩ := hinv.readyWitness p hp v₁ h₁
  exact hinv.witness_unique hF hS hw hq h₂

private lemma BrachaInv.out_has_honest_ready {P V : Type*} [Fintype P] [DecidableEq P]
    [DecidableEq V] {dealer : P} {t : ℕ} {F : Finset P} {input : Option V}
    {s : State P (BrachaState P V) (BrachaMsg V) V}
    (hinv : BrachaInv dealer t F input s) (hF : F.card ≤ t)
    {p : P} (hp : p ∉ F) {v : V} (hv : s.ProcDecided p v) :
    ∃ k ∉ F, (s.proc k).state.sentReady = some v := by
  have hcnt := hinv.outSound p hp v hv
  obtain ⟨k, hkS, hkF⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (lt_of_le_of_lt hF (lt_of_lt_of_le (by omega : t < 2 * t + 1) hcnt))
  simp only [readySenders, Finset.mem_filter, Finset.mem_univ, true_and] at hkS
  exact ⟨k, hkF, hinv.readySound p hp k hkF v hkS⟩

private lemma brachaInv_start {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {t : ℕ} (F : Finset P) (input : Option V) :
    BrachaInv dealer t F input ((brachaProtocol P V dealer t).start F input) := by
  have hmem_init : ∀ e ∈ ((brachaProtocol P V dealer t).start F input).msgs,
      ∃ v, e.src = dealer ∧ dealer ∉ F ∧ input = some v ∧ e.body = .initial v := by
    intro e he
    simp only [Protocol.start, Protocol.initSend, brachaProtocol, Multiset.mem_bind,
      Finset.mem_val, Finset.mem_univ, true_and] at he
    obtain ⟨p, hp⟩ := he
    by_cases hpF : p ∈ F
    · simp [hpF] at hp
    · by_cases hpd : p = dealer
      · subst hpd
        cases input with
        | none => simp [hpF] at hp
        | some v =>
          simp only [hpF, ↓reduceIte, broadcastAll, Multiset.mem_map] at hp
          obtain ⟨qm, ⟨q, _, rfl⟩, rfl⟩ := hp
          exact ⟨v, rfl, hpF, rfl, rfl⟩
      · simp [hpF, hpd] at hp
  have h0e : ∀ v : V, (echoSenders (brachaInit P V) v).card = 0 := fun _ => by
    simp [echoSenders, brachaInit]
  have h0r : ∀ v : V, (readySenders (brachaInit P V) v).card = 0 := fun _ => by
    simp [readySenders, brachaInit]
  have hthresh : 0 < echoThreshold (Fintype.card P) t := by simp [echoThreshold]
  refine
    { srcNotF := fun e he => by
        obtain ⟨_, hs, hd, _, _⟩ := hmem_init e he; rw [hs]; exact hd
      initMsg := fun e he v hb => by
        obtain ⟨w, hs, _, hinp, hbw⟩ := hmem_init e he
        rw [hbw] at hb; cases hb; exact ⟨hs, hinp⟩
      echoMsg := fun e he v hb => by
        obtain ⟨w, _, _, _, hbw⟩ := hmem_init e he; rw [hbw] at hb; cases hb
      readyMsg := fun e he v hb => by
        obtain ⟨w, _, _, _, hbw⟩ := hmem_init e he; rw [hbw] at hb; cases hb
      echoDealer := fun _ _ _ _ h => by simp [Protocol.start, Protocol.initState, brachaProtocol,
        brachaInit] at h
      echoSound := fun _ _ _ _ _ h => by simp [Protocol.start, Protocol.initState, brachaProtocol,
        brachaInit] at h
      readySound := fun _ _ _ _ _ h => by simp [Protocol.start, Protocol.initState, brachaProtocol,
        brachaInit] at h
      readyWitness := fun _ _ _ h => by simp [Protocol.start, Protocol.initState, brachaProtocol,
        brachaInit] at h
      outSound := fun _ _ _ h => by simp [State.ProcDecided, Protocol.start] at h
      echoSat := fun _ _ v hc => by
        have : (echoSenders (brachaInit P V) v).card = 0 := h0e v
        simp only [Protocol.start, Protocol.initState, brachaProtocol, ite_self] at hc
        omega
      readySat := fun _ _ v hc => by
        have : (readySenders (brachaInit P V) v).card = 0 := h0r v
        simp only [Protocol.start, Protocol.initState, brachaProtocol, ite_self] at hc
        omega
      outSat := fun _ _ v hc => by
        have : (readySenders (brachaInit P V) v).card = 0 := h0r v
        simp only [Protocol.start, Protocol.initState, brachaProtocol, ite_self] at hc
        omega
      initLive := fun hd v hinp q _ => Or.inl (by
        simp only [Protocol.start, Protocol.initSend, brachaProtocol, Multiset.mem_bind,
          Finset.mem_val, Finset.mem_univ, true_and]
        refine ⟨dealer, ?_⟩
        simp only [hd, ↓reduceIte, hinp]
        exact mem_broadcastAll_tag dealer q (BrachaMsg.initial v))
      echoLive := fun _ _ _ h => by simp [Protocol.start, Protocol.initState, brachaProtocol,
        brachaInit] at h
      readyLive := fun _ _ _ h => by simp [Protocol.start, Protocol.initState, brachaProtocol,
        brachaInit] at h }

private lemma brachaInv_recvCore {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {t : ℕ} {F : Finset P} {input : Option V} (hF : F.card ≤ t)
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
  let π := brachaProtocol P V dealer t
  let s' := π.recvCore src dest body msgsBase s
  let st := (s.proc dest).state
  let res := brachaStep dealer t st src body
  have hne : ∀ p ≠ dest, s'.proc p = s.proc p := fun p hp => by simp [s', Protocol.recvCore, hp]
  have hst : (s'.proc dest).state = res.nextState := by
    simp [s', Protocol.recvCore, Protocol.updateProc, π, brachaProtocol, res, st]
  have hse_mono : ∀ p v, (s.proc p).state.sentEcho = some v →
      (s'.proc p).state.sentEcho = some v := fun p v hv => by
    by_cases hp : p = dest
    · subst hp; rw [hst]; exact brachaStep_sentEcho_mono hv
    · rw [hne p hp]; exact hv
  have hsr_mono : ∀ p v, (s.proc p).state.sentReady = some v →
      (s'.proc p).state.sentReady = some v := fun p v hv => by
    by_cases hp : p = dest
    · subst hp; rw [hst]; exact brachaStep_sentReady_mono hv
    · rw [hne p hp]; exact hv
  have hef_mono : ∀ p j v, (s.proc p).state.echoFrom j = some v →
      (s'.proc p).state.echoFrom j = some v := fun p j v hv => by
    by_cases hp : p = dest
    · subst hp; rw [hst]; exact brachaStep_echoFrom_mono hv
    · rw [hne p hp]; exact hv
  have hrf_mono : ∀ p j v, (s.proc p).state.readyFrom j = some v →
      (s'.proc p).state.readyFrom j = some v := fun p j v hv => by
    by_cases hp : p = dest
    · subst hp; rw [hst]; exact brachaStep_readyFrom_mono hv
    · rw [hne p hp]; exact hv
  have hout_mono : ∀ p v, s.ProcDecided p v → s'.ProcDecided p v := fun p v hv => by
    by_cases hp : p = dest
    · subst hp; change (s'.proc p).out = some v
      simpa [s', Protocol.recvCore] using π.updateProc_out_eq_some hv
    · change (s'.proc p).out = some v; rw [hne p hp]; exact hv
  have hED : dealer ∉ F → ∀ p ∉ F, ∀ v,
      (s'.proc p).state.sentEcho = some v → input = some v := fun hd p hp v hv => by
    by_cases hpd : p = dest
    · subst hpd; rw [hst] at hv
      rcases brachaStep_sentEcho_eq_some hv with h0 | ⟨hb, hs, _, _⟩
      · exact hinv.echoDealer hd p hp v h0
      · subst hs; exact ((hauth hd).1 v hb).2
    · rw [hne p hpd] at hv; exact hinv.echoDealer hd p hp v hv
  have hES : ∀ p ∉ F, ∀ j ∉ F, ∀ v, (s'.proc p).state.echoFrom j = some v →
      (s'.proc j).state.sentEcho = some v := fun p hp j hj v hv => by
    by_cases hpd : p = dest
    · subst hpd; rw [hst] at hv
      rcases brachaStep_echoFrom_eq_some hv with h0 | ⟨hb, rfl, _⟩
      · exact hse_mono j v (hinv.echoSound p hp j hj v h0)
      · exact hse_mono j v ((hauth hj).2.1 v hb)
    · rw [hne p hpd] at hv; exact hse_mono j v (hinv.echoSound p hp j hj v hv)
  have hRS : ∀ p ∉ F, ∀ j ∉ F, ∀ v, (s'.proc p).state.readyFrom j = some v →
      (s'.proc j).state.sentReady = some v := fun p hp j hj v hv => by
    by_cases hpd : p = dest
    · subst hpd; rw [hst] at hv
      rcases brachaStep_readyFrom_eq_some hv with h0 | ⟨hb, rfl, _⟩
      · exact hsr_mono j v (hinv.readySound p hp j hj v h0)
      · exact hsr_mono j v ((hauth hj).2.2 v hb)
    · rw [hne p hpd] at hv; exact hsr_mono j v (hinv.readySound p hp j hj v hv)
  have hRW : ∀ p ∉ F, ∀ v, (s'.proc p).state.sentReady = some v →
      ∃ S : Finset P, echoThreshold (Fintype.card P) t ≤ S.card ∧
        ∀ j ∈ S, j ∉ F → (s'.proc j).state.sentEcho = some v := fun p hp v hv => by
    by_cases hpd : p = dest
    · subst hpd; rw [hst] at hv
      rcases brachaStep_sentReady_eq_some hv with h0 | ⟨_, _, hcnt, _⟩ | ⟨_, _, hcnt, _⟩
      · obtain ⟨S, hS, hw⟩ := hinv.readyWitness p hp v h0
        exact ⟨S, hS, fun j hjS hjF => hse_mono j v (hw j hjS hjF)⟩
      · refine ⟨echoSenders (s'.proc p).state v, by rwa [hst], fun j hjS hjF => ?_⟩
        simp only [echoSenders, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
        exact hES p hp j hjF v hjS
      · have hcnt' : t + 1 ≤ (readySenders (s'.proc p).state v).card := by rwa [hst]
        obtain ⟨k, hkS, hkF⟩ := Finset.exists_mem_notMem_of_card_lt_card
          (lt_of_le_of_lt hF (lt_of_lt_of_le (by omega : t < t + 1) hcnt'))
        simp only [readySenders, Finset.mem_filter, Finset.mem_univ, true_and] at hkS
        have hkr : (s.proc k).state.sentReady = some v := by
          rw [hst] at hkS
          rcases brachaStep_readyFrom_eq_some hkS with h0 | ⟨hb, rfl, _⟩
          · exact hinv.readySound p hp k hkF v h0
          · exact (hauth hkF).2.2 v hb
        obtain ⟨S, hS, hw⟩ := hinv.readyWitness k hkF v hkr
        exact ⟨S, hS, fun j hjS hjF => hse_mono j v (hw j hjS hjF)⟩
    · rw [hne p hpd] at hv
      obtain ⟨S, hS, hw⟩ := hinv.readyWitness p hp v hv
      exact ⟨S, hS, fun j hjS hjF => hse_mono j v (hw j hjS hjF)⟩
  have hmem_s' : ∀ e ∈ s'.msgs,
      e ∈ s.msgs ∨ (e.src = dest ∧
        ((∃ v, e.body = .echo v ∧ (s'.proc dest).state.sentEcho = some v) ∨
         (∃ v, e.body = .ready v ∧ (s'.proc dest).state.sentReady = some v))) := by
    intro e he
    rcases Multiset.mem_add.mp he with he | he
    · exact Or.inl (Multiset.mem_of_le hle he)
    · obtain ⟨qm, hqm, rfl⟩ := Multiset.mem_map.mp he
      rcases brachaStep_outgoing_mem hqm with ⟨v, hm, hs⟩ | ⟨v, hm, hs⟩
      · exact Or.inr ⟨rfl, Or.inl ⟨v, by simp [hm], hst ▸ hs⟩⟩
      · exact Or.inr ⟨rfl, Or.inr ⟨v, by simp [hm], hst ▸ hs⟩⟩
  refine
    { srcNotF := fun e he => by
        rcases hmem_s' e he with he | ⟨rfl, _⟩
        · exact hinv.srcNotF e he
        · exact hdest
      initMsg := fun e he v hv => by
        rcases hmem_s' e he with he | ⟨_, ⟨w, hb, _⟩ | ⟨w, hb, _⟩⟩
        · exact hinv.initMsg e he v hv
        · rw [hv] at hb; cases hb
        · rw [hv] at hb; cases hb
      echoMsg := fun e he v hv => by
        rcases hmem_s' e he with he | ⟨rfl, ⟨w, hb, hs⟩ | ⟨w, hb, _⟩⟩
        · exact hse_mono e.src v (hinv.echoMsg e he v hv)
        · rw [hv] at hb; cases hb; exact hs
        · rw [hv] at hb; cases hb
      readyMsg := fun e he v hv => by
        rcases hmem_s' e he with he | ⟨rfl, ⟨w, hb, _⟩ | ⟨w, hb, hs⟩⟩
        · exact hsr_mono e.src v (hinv.readyMsg e he v hv)
        · rw [hv] at hb; cases hb
        · rw [hv] at hb; cases hb; exact hs
      echoDealer := hED
      echoSound := hES
      readySound := hRS
      readyWitness := hRW
      outSound := fun p hp v hv => by
        by_cases hpd : p = dest
        · subst hpd
          cases hprev : (s.proc p).out with
          | some u =>
            obtain rfl : u = v := Option.some.inj ((hout_mono p u hprev).symm.trans hv)
            refine (hinv.outSound p hp u hprev).trans (Finset.card_le_card fun j hj => ?_)
            simp only [readySenders, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
            exact hrf_mono p j u hj
          | none =>
            have hdel : res.delivered = some v := by
              simpa [State.ProcDecided, s', Protocol.recvCore, Protocol.updateProc, hprev,
                π, brachaProtocol, res, st] using hv
            rw [hst]
            exact (brachaStep_delivered_eq_some hdel).2
        · change (s'.proc p).out = some v at hv
          rw [hne p hpd] at hv ⊢; exact hinv.outSound p hp v hv
      echoSat := fun p hp v hcnt => by
        by_cases hpd : p = dest
        · subst hpd; rw [hst] at hcnt ⊢
          by_cases hbm : body = .echo v
          · cases hsr : st.sentReady with
            | none =>
              subst hbm
              rcases brachaStep_echo_sat_none hsr hcnt with h0 | hnew
              · exact brachaStep_sentReady_mono (hinv.echoSat p hp v h0)
              · exact hnew
            | some u =>
              have hS : echoThreshold (Fintype.card P) t ≤
                  (echoSenders (s'.proc p).state v).card := by rwa [hst]
              have huw : v = u := by
                refine hinv.witness_unique hF hS (fun j hjS hjF => ?_) hp hsr
                simp only [echoSenders, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
                rw [hst] at hjS
                rcases brachaStep_echoFrom_eq_some hjS with h0 | ⟨hb, rfl, _⟩
                · exact hinv.echoSound p hp j hjF v h0
                · exact (hauth hjF).2.1 v hb
              subst huw; exact brachaStep_sentReady_mono hsr
          · rw [brachaStep_echoSenders_card_eq hbm] at hcnt
            exact brachaStep_sentReady_mono (hinv.echoSat p hp v hcnt)
        · rw [hne p hpd] at hcnt ⊢; exact hinv.echoSat p hp v hcnt
      readySat := fun p hp v hcnt => by
        by_cases hpd : p = dest
        · subst hpd; rw [hst] at hcnt ⊢
          by_cases hbm : body = .ready v
          · cases hsr : st.sentReady with
            | none =>
              subst hbm
              rcases brachaStep_ready_sat_none hsr hcnt with h0 | hnew
              · exact brachaStep_sentReady_mono (hinv.readySat p hp v h0)
              · exact hnew
            | some u =>
              obtain ⟨k, hkS, hkF⟩ := Finset.exists_mem_notMem_of_card_lt_card
                (lt_of_le_of_lt hF (lt_of_lt_of_le (by omega : t < t + 1) hcnt))
              simp only [readySenders, Finset.mem_filter, Finset.mem_univ, true_and] at hkS
              have hkr : (s.proc k).state.sentReady = some v := by
                rcases brachaStep_readyFrom_eq_some hkS with h0 | ⟨hb, rfl, _⟩
                · exact hinv.readySound p hp k hkF v h0
                · exact (hauth hkF).2.2 v hb
              obtain rfl := hinv.ready_unique hF hp hkF hsr hkr
              exact brachaStep_sentReady_mono hsr
          · rw [brachaStep_readySenders_card_eq hbm] at hcnt
            exact brachaStep_sentReady_mono (hinv.readySat p hp v hcnt)
        · rw [hne p hpd] at hcnt ⊢; exact hinv.readySat p hp v hcnt
      outSat := fun p hp v hcnt => by
        by_cases hpd : p = dest
        · subst hpd
          cases hprev : (s.proc p).out with
          | some u =>
            obtain ⟨k₁, hk₁, hr₁⟩ := hinv.out_has_honest_ready hF hp hprev
            obtain ⟨k₂, hk₂S, hk₂F⟩ := Finset.exists_mem_notMem_of_card_lt_card
              (lt_of_le_of_lt hF (lt_of_lt_of_le (by omega : t < 2 * t + 1) hcnt))
            simp only [readySenders, Finset.mem_filter, Finset.mem_univ, true_and] at hk₂S
            obtain ⟨S₁, hS₁, hw₁⟩ := hRW k₁ hk₁ u (hsr_mono k₁ u hr₁)
            obtain ⟨S₂, hS₂, hw₂⟩ := hRW k₂ hk₂F v (hRS p hp k₂ hk₂F v hk₂S)
            obtain ⟨k, hki, hkF⟩ := echo_quorum_inter_notMem hF hS₁ hS₂
            rw [Finset.mem_inter] at hki
            obtain rfl := Option.some.inj ((hw₁ k hki.1 hkF).symm.trans (hw₂ k hki.2 hkF))
            exact hout_mono p u hprev
          | none =>
            rw [hst] at hcnt
            by_cases hbm : body = .ready v
            · have hcnt' : 2 * t + 1 ≤
                  (readySenders (brachaStep dealer t st src (.ready v)).nextState v).card := by
                rwa [← hbm]
              rcases brachaStep_deliver_sat hcnt' with h0 | hdel
              · exact hout_mono p v (hinv.outSat p hp v h0)
              · change (s'.proc p).out = some v
                simpa [s', Protocol.recvCore, Protocol.updateProc, hprev, π, brachaProtocol,
                  hbm, st] using hdel
            · rw [brachaStep_readySenders_card_eq hbm] at hcnt
              exact hout_mono p v (hinv.outSat p hp v hcnt)
        · change (s'.proc p).out = some v
          rw [hne p hpd] at hcnt ⊢; exact hinv.outSat p hp v hcnt
      initLive := fun hd v hinp q hq => by
        rcases hinv.initLive hd v hinp q hq with hmem | hdone
        · by_cases hbase : ⟨dealer, q, .initial v⟩ ∈ msgsBase
          · exact Or.inl (Multiset.mem_add.mpr (Or.inl hbase))
          · right
            have heq := hdrop ⟨dealer, q, .initial v⟩ hmem hbase
            have hs1 : dealer = src := congrArg Envelope.src heq
            have hs2 : q = dest := congrArg Envelope.dest heq
            have hs3 : BrachaMsg.initial v = body := congrArg Envelope.body heq
            cases hse : (s.proc q).state.sentEcho with
            | none =>
              have hq' : (s'.proc q).state =
                  (brachaStep dealer t (s.proc q).state dealer (.initial v)).nextState := by
                rw [hs2, hst]; dsimp only [res, st]; rw [← hs1, ← hs3, ← hs2]
              rw [hq']; simp [brachaStep, hse]
            | some u =>
              have hu := hinv.echoDealer hd q hq u hse
              rw [hinp] at hu; cases hu; exact hse_mono q v hse
        · exact Or.inr (hse_mono q v hdone)
      echoLive := fun p hp v hv q hq => by
        by_cases hprev : (s.proc p).state.sentEcho = some v
        · rcases hinv.echoLive p hp v hprev q hq with hmem | hdone
          · by_cases hbase : ⟨p, q, .echo v⟩ ∈ msgsBase
            · exact Or.inl (Multiset.mem_add.mpr (Or.inl hbase))
            · right
              have heq := hdrop ⟨p, q, .echo v⟩ hmem hbase
              have hs1 : p = src := congrArg Envelope.src heq
              have hs2 : q = dest := congrArg Envelope.dest heq
              have hs3 : BrachaMsg.echo v = body := congrArg Envelope.body heq
              cases hef : (s.proc q).state.echoFrom p with
              | none =>
                have hq' : (s'.proc q).state =
                    (brachaStep dealer t (s.proc q).state p (.echo v)).nextState := by
                  rw [hs2, hst]; dsimp only [res, st]; rw [← hs1, ← hs3, ← hs2]
                rw [hq']; dsimp only [brachaStep]
                simp only [hef, Option.isNone_none, ↓reduceIte]; split_ifs <;> simp
              | some u =>
                have hu := hinv.echoSound q hq p hp u hef
                rw [hprev] at hu; cases hu; exact hef_mono q p v hef
          · exact Or.inr (hef_mono q p v hdone)
        · have hpd : p = dest := by by_contra hc; rw [hne p hc] at hv; exact hprev hv
          subst hpd; left
          refine Multiset.mem_add.mpr (Or.inr ?_)
          rw [hst] at hv
          rcases brachaStep_sentEcho_eq_some hv with h0 | ⟨_, _, _, hout⟩
          · exact absurd h0 hprev
          · change ⟨p, q, BrachaMsg.echo v⟩ ∈ res.outgoing.map (tagSender p)
            rw [hout]; exact mem_broadcastAll_tag p q (BrachaMsg.echo v)
      readyLive := fun p hp v hv q hq => by
        by_cases hprev : (s.proc p).state.sentReady = some v
        · rcases hinv.readyLive p hp v hprev q hq with hmem | hdone
          · by_cases hbase : ⟨p, q, .ready v⟩ ∈ msgsBase
            · exact Or.inl (Multiset.mem_add.mpr (Or.inl hbase))
            · right
              have heq := hdrop ⟨p, q, .ready v⟩ hmem hbase
              have hs1 : p = src := congrArg Envelope.src heq
              have hs2 : q = dest := congrArg Envelope.dest heq
              have hs3 : BrachaMsg.ready v = body := congrArg Envelope.body heq
              cases hrf : (s.proc q).state.readyFrom p with
              | none =>
                have hq' : (s'.proc q).state =
                    (brachaStep dealer t (s.proc q).state p (.ready v)).nextState := by
                  rw [hs2, hst]; dsimp only [res, st]; rw [← hs1, ← hs3, ← hs2]
                rw [hq']; dsimp only [brachaStep]
                simp only [hrf, Option.isNone_none, ↓reduceIte]; split_ifs <;> simp
              | some u =>
                have hu := hinv.readySound q hq p hp u hrf
                rw [hprev] at hu; cases hu; exact hrf_mono q p v hrf
          · exact Or.inr (hrf_mono q p v hdone)
        · have hpd : p = dest := by by_contra hc; rw [hne p hc] at hv; exact hprev hv
          subst hpd; left
          refine Multiset.mem_add.mpr (Or.inr ?_)
          rw [hst] at hv
          rcases brachaStep_sentReady_eq_some hv with h0 | ⟨_, _, _, hout⟩ | ⟨_, _, _, hout⟩
          · exact absurd h0 hprev
          · change ⟨p, q, BrachaMsg.ready v⟩ ∈ res.outgoing.map (tagSender p)
            rw [hout]; exact mem_broadcastAll_tag p q (BrachaMsg.ready v)
          · change ⟨p, q, BrachaMsg.ready v⟩ ∈ res.outgoing.map (tagSender p)
            rw [hout]; exact mem_broadcastAll_tag p q (BrachaMsg.ready v) }

private lemma brachaInv_tr {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {t : ℕ} {F : Finset P} {input : Option V} (hF : F.card ≤ t) :
    ((brachaProtocol P V dealer t).lts F).TrInv (BrachaInv dealer t F input) := by
  intro s a s' htr hinv
  cases a with
  | deliver e =>
    obtain ⟨hmem, hdest, rfl⟩ := htr
    exact brachaInv_recvCore hF hinv hdest (Multiset.erase_le e s.msgs)
      (fun m hm hne => by_contra fun hneq => hne ((Multiset.mem_erase_of_ne hneq).mpr hm))
      (fun _ => ⟨fun v hb => hinv.initMsg e hmem v hb, fun v hb => hinv.echoMsg e hmem v hb,
        fun v hb => hinv.readyMsg e hmem v hb⟩)
  | byzRecv src dest body =>
    obtain ⟨hsrcF, hdest, rfl⟩ := htr
    exact brachaInv_recvCore hF hinv hdest le_rfl (fun _ hm hne => absurd hm hne)
      (fun hnot => absurd hsrcF hnot)
  | stutter =>
    obtain rfl := htr; exact hinv

private lemma brachaInv_reachable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {t : ℕ} {F : Finset P} {input : Option V} (hF : F.card ≤ t)
    {s : State P (BrachaState P V) (BrachaMsg V) V}
    (hr : (brachaProtocol P V dealer t).Reachable F input s) :
    BrachaInv dealer t F input s := by
  obtain ⟨xl, hxl⟩ := hr
  exact LTS.mtrInv_of_trInv (brachaInv_tr hF) _ _ _ hxl (brachaInv_start F input)

/-! ### Liveness helpers and uniform stabilization -/

private lemma bracha_omega_proc_mono {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {t : ℕ} {F : Finset P}
    {ss : ωSequence (State P (BrachaState P V) (BrachaMsg V) V)}
    {xs : ωSequence (Action P (BrachaMsg V))}
    (hexec : ((brachaProtocol P V dealer t).lts F).OmegaExecution ss xs)
    (Q : BrachaState P V → Prop)
    (hQ : ∀ st src m, Q st → Q (brachaStep dealer t st src m).nextState)
    {k j : ℕ} (hkj : k ≤ j) {p : P} (h : Q ((ss k).proc p).state) :
    Q ((ss j).proc p).state := by
  have step_core : ∀ (s : State P (BrachaState P V) (BrachaMsg V) V)
      (src dest : P) (m : BrachaMsg V) (mb : Multiset (Envelope P (BrachaMsg V))),
      Q (s.proc p).state →
      Q (((brachaProtocol P V dealer t).recvCore src dest m mb s).proc p).state := by
    intro s src dest m mb hprev
    dsimp only [Protocol.recvCore]
    by_cases hp : p = dest
    · subst hp; simp only [↓reduceIte, Protocol.updateProc, brachaProtocol]; exact hQ _ _ _ hprev
    · simp only [hp, ↓reduceIte]; exact hprev
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
  induction d with
  | zero => simpa using h
  | succ d ih =>
    have hprev := ih (Nat.le_add_right k d)
    have htr := hexec (k + d)
    cases hact : xs (k + d) with
    | deliver e =>
      rw [hact] at htr; obtain ⟨_, _, hnext⟩ := htr
      rw [← Nat.add_assoc, hnext]; exact step_core _ _ _ _ _ hprev
    | byzRecv src dest body =>
      rw [hact] at htr; obtain ⟨_, _, hnext⟩ := htr
      rw [← Nat.add_assoc, hnext]; exact step_core _ _ _ _ _ hprev
    | stutter =>
      rw [hact] at htr; rw [← Nat.add_assoc]; exact htr ▸ hprev

private lemma exists_uniform_time {ι : Type*} (S : Finset ι) (Q : ι → ℕ → Prop)
    (hmono : ∀ x ∈ S, ∀ {k₁ k₂}, k₁ ≤ k₂ → Q x k₁ → Q x k₂)
    (hevent : ∀ x ∈ S, ∃ k, Q x k) :
    ∃ K : ℕ, ∀ x ∈ S, Q x K := by
  classical
  let pick : S → ℕ := fun x => Classical.choose (hevent x.1 x.2)
  refine ⟨S.attach.sup pick, fun x hx => ?_⟩
  exact hmono x hx (Finset.le_sup (f := pick) (Finset.mem_attach S ⟨x, hx⟩))
    (Classical.choose_spec (hevent x hx))

/-- Shared fairness-step helper: if either `e ∈ (ss k).msgs` or `Q (ss k)` already holds, and
delivering `e` establishes `Q`, then `Q` holds at some step `j`. -/
private lemma eventual_of_mem_or {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {t : ℕ} {F : Finset P} {input : Option V}
    {ss : ωSequence (State P (BrachaState P V) (BrachaMsg V) V)}
    {xs : ωSequence (Action P (BrachaMsg V))}
    (ha : (brachaProtocol P V dealer t).AdmissibleRun F input ss xs)
    {e : Envelope P (BrachaMsg V)} (hdest : e.dest ∉ F) {k : ℕ}
    {Q : BrachaState P V → Prop}
    (hor : e ∈ (ss k).msgs ∨ Q ((ss k).proc e.dest).state)
    (hstep : ∀ j, BrachaInv dealer t F input (ss j) →
      Q (brachaStep dealer t ((ss j).proc e.dest).state e.src e.body).nextState)
    (hF : F.card ≤ t) :
    ∃ j, Q ((ss j).proc e.dest).state := by
  rcases hor with hmem | hdone
  · obtain ⟨j, _, hj⟩ := ha.2.2 e hdest k hmem
    refine ⟨j + 1, ?_⟩
    have htr : ((brachaProtocol P V dealer t).lts F).Tr (ss j) (.deliver e) (ss (j + 1)) := by
      rw [← hj]; exact ha.2.1 j
    obtain ⟨_, _, hnext⟩ := htr
    rw [hnext]; simp only [Protocol.recvHonest, Protocol.recvCore, Protocol.updateProc,
      brachaProtocol, ↓reduceIte]
    exact hstep j (brachaInv_reachable hF ((brachaProtocol P V dealer t).admissibleRun_reachable
      ha j))
  · exact ⟨k, hdone⟩

private lemma eventual_readyFrom {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {t : ℕ} {F : Finset P} (hF : F.card ≤ t) {input : Option V}
    {ss : ωSequence (State P (BrachaState P V) (BrachaMsg V) V)}
    {xs : ωSequence (Action P (BrachaMsg V))}
    (ha : (brachaProtocol P V dealer t).AdmissibleRun F input ss xs)
    {p q : P} (hp : p ∉ F) (hq : q ∉ F) {k : ℕ} {v : V}
    (hk : ((ss k).proc p).state.sentReady = some v) :
    ∃ j, ((ss j).proc q).state.readyFrom p = some v := by
  have hinv := brachaInv_reachable hF ((brachaProtocol P V dealer t).admissibleRun_reachable ha k)
  refine eventual_of_mem_or (Q := fun st => st.readyFrom p = some v) ha hq
    (hinv.readyLive p hp v hk q hq) (fun j hinvj => ?_) hF
  cases hrf : ((ss j).proc q).state.readyFrom p with
  | none =>
    dsimp only [brachaStep]; simp only [hrf, Option.isNone_none, ↓reduceIte]
    split_ifs <;> simp
  | some u =>
    have hu := hinvj.readySound q hq p hp u hrf
    have hmax_u := bracha_omega_proc_mono ha.2.1 (fun st => st.sentReady = some u)
      (fun _ _ _ => brachaStep_sentReady_mono) (le_max_left j k) hu
    have hmax_v := bracha_omega_proc_mono ha.2.1 (fun st => st.sentReady = some v)
      (fun _ _ _ => brachaStep_sentReady_mono) (le_max_right j k) hk
    obtain rfl := Option.some.inj (hmax_u.symm.trans hmax_v)
    exact brachaStep_readyFrom_mono hrf

private lemma eventual_deliver_of_all_ready {P V : Type*} [Fintype P] [DecidableEq P]
    [DecidableEq V] {dealer : P} {t : ℕ} (hnt : 3 * t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t) {input : Option V}
    {ss : ωSequence (State P (BrachaState P V) (BrachaMsg V) V)}
    {xs : ωSequence (Action P (BrachaMsg V))}
    (ha : (brachaProtocol P V dealer t).AdmissibleRun F input ss xs)
    {v : V} (hready : ∀ p ∉ F, ∃ k, ((ss k).proc p).state.sentReady = some v)
    {q : P} (hq : q ∉ F) :
    ∃ k, (ss k).ProcDecided q v := by
  let R : Finset P := Finset.univ.filter fun p => p ∉ F
  have hevent : ∀ p ∈ R, ∃ k, ((ss k).proc q).state.readyFrom p = some v := by
    intro p hp
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨k, hk⟩ := hready p hp
    exact eventual_readyFrom hF ha hp hq hk
  obtain ⟨K, hK⟩ := exists_uniform_time R (fun p k => ((ss k).proc q).state.readyFrom p = some v)
    (fun p _ {_ _} hle h => bracha_omega_proc_mono ha.2.1 (fun st => st.readyFrom p = some v)
      (fun _ _ _ => brachaStep_readyFrom_mono) hle h)
    hevent
  have hinvK := brachaInv_reachable hF ((brachaProtocol P V dealer t).admissibleRun_reachable ha K)
  refine ⟨K, hinvK.outSat q hq v ?_⟩
  have hR_card : 2 * t + 1 ≤ R.card := by
    have hsub : R = Finset.univ \ F := by ext p; simp [R]
    rw [hsub]; simp [Finset.card_sdiff]; omega
  refine hR_card.trans (Finset.card_le_card fun p hp => ?_)
  simp only [readySenders, Finset.mem_filter, Finset.mem_univ, true_and]; exact hK p hp

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
    obtain ⟨j, hjS, hjF⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (lt_of_le_of_lt hF (lt_of_lt_of_le (lt_echoThreshold hnt) hS))
    exact hinv.echoDealer hd j hjF v (hw j hjS hjF)
  validity F hF hd v ss xs ha q hq := by
    let R : Finset P := Finset.univ.filter fun p => p ∉ F
    have hR_card : echoThreshold (Fintype.card P) t ≤ R.card := by
      have hsub : R = Finset.univ \ F := by ext p; simp [R]
      have := echoThreshold_le_sub hnt
      rw [hsub]; simp [Finset.card_sdiff]; omega
    have hevent_echo : ∀ r ∈ R, ∃ k, ((ss k).proc r).state.sentEcho = some v := by
      intro r hr
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      have hinv0 := brachaInv_reachable hF
        ((brachaProtocol P V dealer t).admissibleRun_reachable ha 0)
      refine eventual_of_mem_or (Q := fun st => st.sentEcho = some v) ha hr
        (hinv0.initLive hd v rfl r hr) (fun j hinvj => ?_) hF
      cases hse : ((ss j).proc r).state.sentEcho with
      | none => simp [brachaStep, hse]
      | some u =>
        have hu := hinvj.echoDealer hd r hr u hse
        cases hu; exact brachaStep_sentEcho_mono hse
    have hevent_ready : ∀ p ∉ F, ∃ k, ((ss k).proc p).state.sentReady = some v := by
      intro p hp
      have hev_from : ∀ r ∈ R, ∃ k, ((ss k).proc p).state.echoFrom r = some v := by
        intro r hr
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        obtain ⟨k, hk⟩ := hevent_echo r (by simp [R, hr])
        have hinvk := brachaInv_reachable hF
          ((brachaProtocol P V dealer t).admissibleRun_reachable ha k)
        refine eventual_of_mem_or (Q := fun st => st.echoFrom r = some v) ha hp
          (hinvk.echoLive r hr v hk p hp) (fun j hinvj => ?_) hF
        cases hef : ((ss j).proc p).state.echoFrom r with
        | none =>
          dsimp only [brachaStep]; simp only [hef, Option.isNone_none, ↓reduceIte]
          split_ifs <;> simp
        | some u =>
          have hu := hinvj.echoDealer hd r hr u (hinvj.echoSound p hp r hr u hef)
          cases hu; exact brachaStep_echoFrom_mono hef
      obtain ⟨K, hK⟩ := exists_uniform_time R (fun r k => ((ss k).proc p).state.echoFrom r = some v)
        (fun r _ {_ _} hle h => bracha_omega_proc_mono ha.2.1 (fun st => st.echoFrom r = some v)
          (fun _ _ _ => brachaStep_echoFrom_mono) hle h)
        hev_from
      have hinvK := brachaInv_reachable hF
        ((brachaProtocol P V dealer t).admissibleRun_reachable ha K)
      refine ⟨K, hinvK.echoSat p hp v (hR_card.trans (Finset.card_le_card fun r hr => ?_))⟩
      simp only [echoSenders, Finset.mem_filter, Finset.mem_univ, true_and]; exact hK r hr
    exact eventual_deliver_of_all_ready hnt hF ha hevent_ready hq
  totality F hF input ss xs ha i hi k v hv q hq := by
    have hinvk := brachaInv_reachable hF
      ((brachaProtocol P V dealer t).admissibleRun_reachable ha k)
    let R : Finset P := readySenders ((ss k).proc i).state v |>.filter fun r => r ∉ F
    have hR_card : t + 1 ≤ R.card := by
      have hsound := hinvk.outSound i hi v hv
      have hsplit : (readySenders ((ss k).proc i).state v).card ≤ R.card + F.card := by
        have hsub : readySenders ((ss k).proc i).state v ⊆ R ∪ F := fun r hr => by
          by_cases hrF : r ∈ F
          · exact Finset.mem_union_right _ hrF
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr, hrF⟩)
        exact (Finset.card_le_card hsub).trans (Finset.card_union_le R F)
      omega
    have hR_ready : ∀ r ∈ R, r ∉ F ∧ ((ss k).proc r).state.sentReady = some v := by
      intro r hr
      simp only [R, Finset.mem_filter, readySenders, Finset.mem_univ, true_and] at hr
      exact ⟨hr.2, hinvk.readySound i hi r hr.2 v hr.1⟩
    have hevent_ready : ∀ p ∉ F, ∃ k', ((ss k').proc p).state.sentReady = some v := by
      intro p hp
      have hev_from : ∀ r ∈ R, ∃ k', ((ss k').proc p).state.readyFrom r = some v := fun r hr =>
        let ⟨hrF, hrr⟩ := hR_ready r hr
        eventual_readyFrom hF ha hrF hp hrr
      obtain ⟨K, hK⟩ := exists_uniform_time R
        (fun r k' => ((ss k').proc p).state.readyFrom r = some v)
        (fun r _ {_ _} hle h => bracha_omega_proc_mono ha.2.1 (fun st => st.readyFrom r = some v)
          (fun _ _ _ => brachaStep_readyFrom_mono) hle h)
        hev_from
      have hinvK := brachaInv_reachable hF
        ((brachaProtocol P V dealer t).admissibleRun_reachable ha K)
      refine ⟨K, hinvK.readySat p hp v (hR_card.trans (Finset.card_le_card fun r hr => ?_))⟩
      simp only [readySenders, Finset.mem_filter, Finset.mem_univ, true_and]; exact hK r hr
    exact eventual_deliver_of_all_ready hnt hF ha hevent_ready hq

/-! ### Exact `O(n²)` communication complexity -/

private def sentFieldCount {P V : Type*} [Fintype P] [DecidableEq P] (F : Finset P)
    (field : BrachaState P V → Option V)
    (s : State P (BrachaState P V) (BrachaMsg V) V) : ℕ :=
  (Finset.univ.filter fun p => p ∉ F ∧ (field (s.proc p).state).isSome).card

private lemma sentFieldCount_congr {P V : Type*} [Fintype P] [DecidableEq P]
    (F : Finset P) (field : BrachaState P V → Option V)
    {s s' : State P (BrachaState P V) (BrachaMsg V) V} {dest : P}
    (hne : ∀ y ≠ dest, (s'.proc y).state = (s.proc y).state)
    (heq : (field (s'.proc dest).state).isSome = (field (s.proc dest).state).isSome) :
    sentFieldCount F field s' = sentFieldCount F field s := by
  unfold sentFieldCount; congr 1; ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hy : y = dest
  · subst hy; exact and_congr_right fun _ => by rw [heq]
  · exact and_congr_right fun _ => by rw [hne y hy]

private lemma sentFieldCount_inc {P V : Type*} [Fintype P] [DecidableEq P]
    (F : Finset P) (field : BrachaState P V → Option V)
    {s s' : State P (BrachaState P V) (BrachaMsg V) V} {dest : P} (hdest : dest ∉ F)
    (hne : ∀ y ≠ dest, (s'.proc y).state = (s.proc y).state)
    (h0 : field (s.proc dest).state = none)
    (h1 : (field (s'.proc dest).state).isSome = true) :
    sentFieldCount F field s' = sentFieldCount F field s + 1 := by
  have heq : (Finset.univ.filter fun y => y ∉ F ∧ (field (s'.proc y).state).isSome = true) =
      insert dest (Finset.univ.filter fun y => y ∉ F ∧ (field (s.proc y).state).isSome = true) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hy : y = dest
    · subst hy; simp [hdest, h1]
    · simp [hy, hne y hy]
  unfold sentFieldCount
  rw [heq, Finset.card_insert_of_notMem]
  simp [h0]

private lemma brachaStep_sent_telescopes {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (dealer : P) (t : ℕ) (F : Finset P)
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
  rcases brachaStep_outgoing_toggle (dealer := dealer) (t := t) (st := (s.proc dest).state)
      (src := src) (body := body) with
    ⟨hcard, hE, hR⟩ | ⟨hcard, hE0, hE1, hR⟩ | ⟨hcard, hR0, hR1, hE⟩
  · rw [hcard, zero_add,
      sentFieldCount_congr F BrachaState.sentEcho hne (hst ▸ hE),
      sentFieldCount_congr F BrachaState.sentReady hne (hst ▸ hR)]
  · rw [hcard,
      sentFieldCount_inc F BrachaState.sentEcho hdest hne hE0 (hst ▸ hE1),
      sentFieldCount_congr F BrachaState.sentReady hne (hst ▸ hR)]
    rw [Nat.add_right_comm, Nat.mul_succ, Nat.add_comm]
  · rw [hcard,
      sentFieldCount_congr F BrachaState.sentEcho hne (hst ▸ hE),
      sentFieldCount_inc F BrachaState.sentReady hdest hne hR0 (hst ▸ hR1)]
    rw [← Nat.add_assoc, Nat.mul_succ, Nat.add_comm]

private lemma brachaTraceSent_eq {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {dealer : P} {t : ℕ} {F : Finset P}
    {s₀ s₁ : State P (BrachaState P V) (BrachaMsg V) V}
    {xl : List (Action P (BrachaMsg V))}
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
      have hih : (brachaProtocol P V dealer t).traceSent
            ((brachaProtocol P V dealer t).recvHonest e s) xl' +
          Fintype.card P * (sentFieldCount F BrachaState.sentEcho
              ((brachaProtocol P V dealer t).recvHonest e s) +
            sentFieldCount F BrachaState.sentReady
              ((brachaProtocol P V dealer t).recvHonest e s)) =
          Fintype.card P * (sentFieldCount F BrachaState.sentEcho s₁ +
            sentFieldCount F BrachaState.sentReady s₁) := ih
      change _ + _ + _ = _
      rw [Nat.add_right_comm, hstep, Nat.add_comm]
      exact hih
    | byzRecv src dest body =>
      obtain ⟨_, hdest, rfl⟩ := htr
      have hstep := brachaStep_sent_telescopes dealer t F s src dest hdest body s.msgs
      simp only [Protocol.traceSent, brachaProtocol]
      change _ + _ + _ = _
      rw [Nat.add_right_comm, hstep, Nat.add_comm]
      exact ih
    | stutter =>
      obtain rfl := htr; exact ih

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
        Finset.univ.sum (fun p =>
          (if p ∈ F then (0 : Multiset (Envelope P (BrachaMsg V)))
            else ((brachaProtocol P V dealer t).initSend input p).map (tagSender p)).card) := by
      simp [Protocol.start, Multiset.card_bind]
    rw [hbind, Finset.sum_eq_single dealer
      (fun p _ hp => by simp [Protocol.initSend, brachaProtocol, hp])
      (fun h => absurd (Finset.mem_univ dealer) h)]
    by_cases hd : dealer ∈ F
    · simp [hd]
    · cases input with
      | none => simp [hd, Protocol.initSend, brachaProtocol]
      | some v => simp [hd, Protocol.initSend, brachaProtocol]
  have h0e : sentFieldCount F BrachaState.sentEcho
      ((brachaProtocol P V dealer t).start F input) = 0 := by
    simp [sentFieldCount, Protocol.start, Protocol.initState, brachaProtocol, brachaInit]
  have h0r : sentFieldCount F BrachaState.sentReady
      ((brachaProtocol P V dealer t).start F input) = 0 := by
    simp [sentFieldCount, Protocol.start, Protocol.initState, brachaProtocol, brachaInit]
  have hsum := brachaTraceSent_eq hmtr
  rw [h0e, h0r, add_zero, mul_zero, add_zero] at hsum
  have hbound : ∀ field, sentFieldCount F field s ≤ Fintype.card P - F.card := fun field => by
    have hsub : (Finset.univ.filter fun p => p ∉ F ∧ (field (s.proc p).state).isSome) ⊆
        Finset.univ \ F := fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp; simp [hp.1]
    exact (Finset.card_le_card hsub).trans (by simp [Finset.card_sdiff])
  have hadd : sentFieldCount F BrachaState.sentEcho s +
      sentFieldCount F BrachaState.sentReady s ≤ 2 * (Fintype.card P - F.card) := by
    have := hbound BrachaState.sentEcho; have := hbound BrachaState.sentReady; omega
  have hmul : Fintype.card P * (sentFieldCount F BrachaState.sentEcho s +
        sentFieldCount F BrachaState.sentReady s) ≤
      2 * (Fintype.card P - F.card) * Fintype.card P := by
    rw [Nat.mul_comm (2 * (Fintype.card P - F.card))]
    exact Nat.mul_le_mul_left _ hadd
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
