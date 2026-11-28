/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.CausalBroadcast.Causal
public import Cslib.Computability.Distributed.FLP.Impossibility
import Cslib.Computability.Distributed.FLP.FairScheduler
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Dedup

/-!
# One-Shot and Slot-Trace Total-Order Broadcast Steps and `Cslib.FLP` Reduction

This module formalizes one-shot initial-broadcast and discrete-time slot-trace steps toward #7297
for asynchronous crash-fault Total-Order (Atomic) Broadcast, its reductions to and from Consensus,
and its fault-tolerance contrast against single-group Causal Broadcast (after Hadzilacos and Toueg
[HadzilacosToueg1994], §§3.1, 3.4, 3.8–3.9, 7.1–7.2, and Chandra and Toueg [ChandraToueg1996], §§4,
7, 7.1).

1. **One-Shot Asynchronous Crash-Fault Broadcast Model (`TotalOrderBroadcastAlg`):**
   Models deterministic event-driven asynchronous broadcast algorithms over process set `P` in
   which each process receives one initial broadcast input `inp p : V` at `start`, with labelled
   transition system (`TotalOrderBroadcastAlg.lts`), schedule fairness (`BcastProcFair`,
   `BcastFairRun`), and crash count (`bcastNumProcFaulty`) aligned directly with
   `Cslib.FLP.Algorithm`. Defines one-shot `Validity`, `Integrity`, `Agreement`,
   `SolvesReliableBroadcast`, non-uniform `TotalOrder` ([HadzilacosToueg1994], §3.4, p. 13;
   [ChandraToueg1996], §7, p. 248), `UniformTotalOrder` ([HadzilacosToueg1994], §3.8, p. 15), and
   `SolvesTotalOrderBroadcast`.

2. **One-Shot Reduction to `Cslib.FLP` Consensus (`consensusOfTotalOrderBroadcast`) and
   `f ≥ 1` Impossibility Step (`not_exists_oneShotTotalOrderBroadcast_ge_one`):**
   Adapts any `f`-resilient one-shot `TotalOrderBroadcastAlg P M S Bool` into an `f`-resilient
   `Cslib.FLP.Algorithm P M S` (`consensusOfTotalOrderBroadcast_consensus`, after
   [HadzilacosToueg1994], §7.2.1, Figure 13 & Theorem 13, p. 58; [ChandraToueg1996], §7, p. 249) by
   deciding the payload of the first delivered message, and invokes
   `Cslib.FLP.Consensus.ge_one_not_exists` to rule out `f ≥ 1` crash-resilient
   `TotalOrderBroadcastAlg` for `2 ≤ Fintype.card P` and `[Nontrivial V]`
   (`not_exists_oneShotTotalOrderBroadcast_ge_one`).
   Paired with the `0`-fault deterministic sequencer `zeroFaultTotalOrderAlg`
   (`zeroFaultTotalOrderAlg_solves`), `exists_oneShotTotalOrderBroadcast_iff_eq_zero` characterizes
   one-shot solvability as `t = 0`.

3. **Abstract Slot-Trace Reduction Step from Consensus + Reliable Broadcast
   (`ConsensusSlotExec`, `totalOrderBroadcast_of_consensusSlotExec`):**
   Models the batch-delivery reduction of [ChandraToueg1996], §7.1 (Figure 7, Lemmas 7.1.2–7.1.5 &
   Theorem 7.1.6, pp. 249–252) and [HadzilacosToueg1994], §7.2.2 (Figure 14 & Theorem 14,
   pp. 60–63) over `[LinearOrder Msg]` (`canonicalBatch`, `runConsensusSlots`) at the abstract
   discrete-time (`t : ℕ`) subprotocol-execution level (`ConsensusSlotExec`), proving duplicate
   freedom, uniform integrity, uniform total order, agreement, and validity.

4. **Single-Group Causal vs. One-Shot Total-Order Fault-Tolerance Dichotomy Step
   (`causal_vs_oneShotTotalOrder_dichotomy`):**
   Contrasts `∀ t < Fintype.card P` solvability of `BSSSolvesAtomicMulticastCausalBroadcast` against
   `t = 0`-only solvability of one-shot `TotalOrderBroadcastAlg` for `2 ≤ Fintype.card P` and
   `[Nontrivial V]`.

## Model scope relative to primary sources

1. **Single initial broadcast per process in `TotalOrderBroadcastAlg`:** Following
   `Cslib.FLP.Algorithm`, each process `p : P` receives one initial broadcast input `inp p : V` at
   initialization (`TotalOrderBroadcastAlg.start`) rather than dynamic multi-shot `broadcast(m)`
   invocations; dynamic multi-shot `TotalOrderBroadcastAlg` remains open under #7297.
2. **Discrete-time modular subprotocol interface in `ConsensusSlotExec`:**
   `ConsensusSlotExec` and `totalOrderBroadcast_of_consensusSlotExec` work over an arbitrary
   multi-shot message type `Msg` with `[LinearOrder Msg]` and broadcast sets
   `correctBcast ⊆ bcast : Set Msg`, axiomatizing subprotocol execution traces (`rDelivered`,
   `decidedBatches`, `Proposed`, `faulty_eventually_halted`) rather than transforming executable
   network `Algorithm`s (and leaving failure-detector classes of [ChandraToueg1996] §§3, 5–6 out of
   scope).

## Main definitions

* `Cslib.Distributed.CausalBroadcast.BcastMsg`,
  `Cslib.Distributed.CausalBroadcast.NetEnvelope`,
  `Cslib.Distributed.CausalBroadcast.BcastEvent`,
  `Cslib.Distributed.CausalBroadcast.BcastProcState`,
  `Cslib.Distributed.CausalBroadcast.BcastState`: message, envelope, event, and state structures for
  one-shot asynchronous crash-fault broadcast algorithms.
* `Cslib.Distributed.CausalBroadcast.TotalOrderBroadcastAlg`: deterministic one-shot asynchronous
  broadcast algorithm and its `lts`, `AdmissibleRun`, `Validity`, `Integrity`, `Agreement`,
  `TotalOrder`, `UniformTotalOrder`, `SolvesReliableBroadcast`, and `SolvesTotalOrderBroadcast`
  predicates.
* `Cslib.Distributed.CausalBroadcast.consensusOfTotalOrderBroadcast`: `Cslib.FLP.Algorithm P M S`
  adapter reducing binary consensus to one-shot `TotalOrderBroadcastAlg`.
* `Cslib.Distributed.CausalBroadcast.zeroFaultTotalOrderAlg`: deterministic fixed-sequencer
  one-shot algorithm solving `0`-fault `SolvesTotalOrderBroadcast`.
* `Cslib.Distributed.CausalBroadcast.insertSorted`,
  `Cslib.Distributed.CausalBroadcast.canonicalBatch`,
  `Cslib.Distributed.CausalBroadcast.runConsensusSlots`: executable canonical `[LinearOrder Msg]`
  batch-delivery engine for sequential consensus slots.
* `Cslib.Distributed.CausalBroadcast.ConsensusSlotExec`: abstract discrete-time (`t : ℕ`) execution
  specification of sequential Consensus slots over Reliable Broadcast.

## Main results

* `Cslib.Distributed.CausalBroadcast.consensusOfTotalOrderBroadcast_consensus`: any `f`-resilient
  one-shot `TotalOrderBroadcastAlg` over `Bool` yields an `f`-resilient `Cslib.FLP.Algorithm`.
* `Cslib.Distributed.CausalBroadcast.uniformTotalOrder_of_solvesTotalOrderBroadcast`: for one-shot
  `TotalOrderBroadcastAlg`, non-uniform `SolvesTotalOrderBroadcast f` implies `UniformTotalOrder`
  across all reachable configurations.
* `Cslib.Distributed.CausalBroadcast.not_exists_oneShotTotalOrderBroadcast_ge_one`: impossibility
  step for `f ≥ 1` crash-resilient one-shot `TotalOrderBroadcastAlg` when `2 ≤ Fintype.card P` and
  `[Nontrivial V]`, proved via `Cslib.FLP.Consensus.ge_one_not_exists`.
* `Cslib.Distributed.CausalBroadcast.zeroFaultTotalOrderAlg_solves` and
  `Cslib.Distributed.CausalBroadcast.exists_oneShotTotalOrderBroadcast_iff_eq_zero`: `0`-fault
  one-shot sequencer solvability and exact `t = 0` characterization for `2 ≤ Fintype.card P`.
* `Cslib.Distributed.CausalBroadcast.canonicalBatch_ext` and
  `Cslib.Distributed.CausalBroadcast.runConsensusSlots_nodup`: canonical set-to-sequence batch
  uniqueness and duplicate-free multi-slot execution.
* `Cslib.Distributed.CausalBroadcast.totalOrderBroadcast_of_consensusSlotExec`: abstract slot-trace
  reduction step proving duplicate freedom, uniform integrity, uniform total order, agreement, and
  validity for any `ConsensusSlotExec`.
* `Cslib.Distributed.CausalBroadcast.causal_vs_oneShotTotalOrder_dichotomy`: fault-tolerance
  dichotomy step contrasting `∀ t < Fintype.card P` single-group atomic-multicast causal broadcast
  against `t = 0`-only one-shot total-order broadcast.

## References

* [K. Birman, A. Schiper, P. Stephenson, *Lightweight causal and atomic group
  multicast*][BirmanSchiperStephenson1991]
* [T. D. Chandra, S. Toueg, *Unreliable failure detectors for reliable distributed
  systems*][ChandraToueg1996]
* [V. Hadzilacos, S. Toueg, *A modular approach to fault-tolerant broadcasts and related
  problems*][HadzilacosToueg1994]
* [H. Völzer, *A constructive proof for FLP*][Volzer2004]
-/

public section

namespace Cslib.Distributed.CausalBroadcast

open Cslib Cslib.ωSequence Multiset Set

universe u v

/-! ### Part 1: Asynchronous Crash-Fault Total-Order Broadcast Model -/

/-- A broadcast message `(sender, payload)` initiated by `sender` with body `payload`. -/
@[ext]
structure BcastMsg (P V : Type*) where
  /-- Originating broadcaster process. -/
  sender : P
  /-- Broadcast message payload. -/
  payload : V
  deriving @[expose] DecidableEq

/-- An outgoing network message addressed to `dest` carrying protocol payload `body`. -/
@[ext]
structure NetEnvelope (P M : Type*) where
  /-- Recipient process identity. -/
  dest : P
  /-- Protocol message content. -/
  body : M
  deriving @[expose] DecidableEq

/-- An event delivered to `dest` in a `TotalOrderBroadcastAlg`: `Sum.inl v` delivers `dest`'s
initial broadcast input `v : V`, and `Sum.inr m` delivers an in-flight protocol message `m : M`. -/
@[ext]
structure BcastEvent (P M V : Type*) where
  /-- Recipient process identity. -/
  dest : P
  /-- Either initial broadcast value `Sum.inl v` or protocol message `Sum.inr m`. -/
  evt : V ⊕ M
  deriving @[expose] DecidableEq

/-- Per-process configuration in a `TotalOrderBroadcastAlg`, pairing internal protocol state `state`
with the append-only chronological list `delivered` of A-delivered broadcast messages. -/
@[ext]
structure BcastProcState (P S V : Type*) where
  /-- Internal protocol state of the process. -/
  state : S
  /-- Chronological sequence of broadcast messages delivered at this process so far. -/
  delivered : List (BcastMsg P V)
  deriving @[expose] DecidableEq

/-- Global network configuration of a `TotalOrderBroadcastAlg`: unordered multiset `msgs` of pending
events/messages in transit and per-process local states `proc`. -/
structure BcastState (P M S V : Type*) where
  /-- Unordered multiset of pending input triggers and in-flight network messages. -/
  msgs : Multiset (BcastEvent P M V)
  /-- Local state of each process. -/
  proc : P → BcastProcState P S V

/-- Specification of a deterministic asynchronous message-passing broadcast algorithm over process
set `P`, network message type `M`, local state type `S`, and broadcast payload type `V`.

Mirrors `Cslib.FLP.Algorithm`: protocol transitions depend only on the incoming `BcastEvent` and
the recipient's internal `state : S`, never on the specification log `delivered`. -/
structure TotalOrderBroadcastAlg (P M S V : Type*) where
  /-- Initial internal state of each process `p : P`. -/
  init : P → S
  /-- Updated internal state of `e.dest` upon receiving event `e`. -/
  next : BcastEvent P M V → S → S
  /-- Network messages emitted by `e.dest` upon receiving event `e`. -/
  send : BcastEvent P M V → S → Multiset (NetEnvelope P M)
  /-- Broadcast messages newly delivered to `e.dest` upon receiving event `e`. -/
  deliver : BcastEvent P M V → S → List (BcastMsg P V)

/-- Action label of `TotalOrderBroadcastAlg.lts`: `some e` processes event `e`, and `none` is a
stuttering step (matching `Cslib.FLP.Action`). -/
abbrev BcastAction (P M V : Type*) := Option (BcastEvent P M V)

namespace TotalOrderBroadcastAlg

section Model

variable {P M S V : Type*}

/-- Initial global configuration for input assignment `inp : P → V`: one initial trigger
`⟨p, Sum.inl (inp p)⟩` per process `p : P` and empty delivery logs. -/
@[expose]
def start [Fintype P] (π : TotalOrderBroadcastAlg P M S V) (inp : P → V) : BcastState P M S V where
  msgs := Multiset.map (fun p => ⟨p, Sum.inl (inp p)⟩) Finset.univ.val
  proc := fun p => ⟨π.init p, []⟩

/-- Global state transition when `e.dest` receives `e` in state `s`. -/
@[expose]
def recvEvent [DecidableEq P] [DecidableEq M] [DecidableEq V]
    (π : TotalOrderBroadcastAlg P M S V) (e : BcastEvent P M V) (s : BcastState P M S V) :
    BcastState P M S V :=
  let p := e.dest
  let st := (s.proc p).state
  { msgs := s.msgs.erase e + (π.send e st).map (fun env => ⟨env.dest, Sum.inr env.body⟩)
    proc := fun q =>
      if q = p then ⟨π.next e st, (s.proc p).delivered ++ π.deliver e st⟩
      else s.proc q }

/-- Labelled transition system of `π`, with stuttering step `none` matching
`Cslib.FLP.Algorithm`. -/
@[expose]
def lts [DecidableEq P] [DecidableEq M] [DecidableEq V]
    (π : TotalOrderBroadcastAlg P M S V) : LTS (BcastState P M S V) (BcastAction P M V) where
  Tr s act s' := match act with
    | some e => e ∈ s.msgs ∧ s' = π.recvEvent e s
    | none => s' = s

/-- Reachability from `π.start inp`. -/
@[expose]
def Reachable [Fintype P] [DecidableEq P] [DecidableEq M] [DecidableEq V]
    (π : TotalOrderBroadcastAlg P M S V) (inp : P → V) (s : BcastState P M S V) : Prop :=
  π.lts.CanReach (π.start inp) s

/-- Process `p` crashes (`BcastProcFaulty`) in `(ss, xs)` iff from some time `k` onward there is an
undelivered event addressed to `p` while `p` never processes another event (matching
`Cslib.FLP.ProcFaulty`). -/
@[expose]
def BcastProcFaulty (p : P) (ss : ωSequence (BcastState P M S V))
    (xs : ωSequence (BcastAction P M V)) : Prop :=
  ∃ k, (∃ e ∈ (ss k).msgs, e.dest = p) ∧ ∀ j, k ≤ j → ∀ e', xs j = some e' → e'.dest ≠ p

/-- Process `p` is fair/correct (`BcastProcFair`) in `(ss, xs)` iff every event in `msgs` addressed
to `p` is eventually processed by `p` (matching `Cslib.FLP.ProcFair`). -/
@[expose]
def BcastProcFair (p : P) (ss : ωSequence (BcastState P M S V))
    (xs : ωSequence (BcastAction P M V)) : Prop :=
  ∀ e, e.dest = p → ∀ k, e ∈ (ss k).msgs → ∃ j, k ≤ j ∧ xs j = some e

/-- An infinite run is fair iff every process is either crash-faulty or fair
(matching `Cslib.FLP.FairRun`). -/
@[expose]
def BcastFairRun (ss : ωSequence (BcastState P M S V))
    (xs : ωSequence (BcastAction P M V)) : Prop :=
  ∀ p, BcastProcFaulty p ss xs ∨ BcastProcFair p ss xs

/-- Number of crash-faulty processes in `(ss, xs)` (matching `Cslib.FLP.numProcFaulty`). -/
@[expose]
noncomputable def bcastNumProcFaulty (ss : ωSequence (BcastState P M S V))
    (xs : ωSequence (BcastAction P M V)) : ℕ :=
  {p | BcastProcFaulty p ss xs}.ncard

/-- An infinite execution `(ss, xs)` of `π` on input `inp` is `f`-admissible iff it starts at
`π.start inp`, follows `π.lts`, is fair, and has at most `f` crash-faulty processes
(matching `Cslib.FLP.Algorithm.AdmissibleRun`). -/
@[expose]
def AdmissibleRun [Fintype P] [DecidableEq P] [DecidableEq M] [DecidableEq V]
    (π : TotalOrderBroadcastAlg P M S V) (inp : P → V) (f : ℕ)
    (ss : ωSequence (BcastState P M S V)) (xs : ωSequence (BcastAction P M V)) : Prop :=
  ss 0 = π.start inp ∧ π.lts.OmegaExecution ss xs ∧
    BcastFairRun ss xs ∧ bcastNumProcFaulty ss xs ≤ f

/-- One-shot broadcast validity on `TotalOrderBroadcastAlg` (after [HadzilacosToueg1994], §3.1,
p. 10; [ChandraToueg1996], §4, p. 238): in every `f`-admissible run, every correct (`BcastProcFair`)
process `p` eventually delivers its own initial broadcast `⟨p, inp p⟩`. -/
@[expose]
def Validity [Fintype P] [DecidableEq P] [DecidableEq M] [DecidableEq V]
    (π : TotalOrderBroadcastAlg P M S V) (f : ℕ) : Prop :=
  ∀ inp ss xs, π.AdmissibleRun inp f ss xs →
    ∀ p, BcastProcFair p ss xs → ∃ k, ⟨p, inp p⟩ ∈ ((ss k).proc p).delivered

/-- One-shot broadcast integrity on `TotalOrderBroadcastAlg` (after [HadzilacosToueg1994], §3.1,
p. 10; [ChandraToueg1996], §4, p. 238): in every `f`-admissible run, every correct process delivers
each message at most once (`Nodup`), and every delivered message `m` equals the initial broadcast
`⟨m.sender, inp m.sender⟩` of its sender. -/
@[expose]
def Integrity [Fintype P] [DecidableEq P] [DecidableEq M] [DecidableEq V]
    (π : TotalOrderBroadcastAlg P M S V) (f : ℕ) : Prop :=
  ∀ inp ss xs, π.AdmissibleRun inp f ss xs →
    ∀ p, BcastProcFair p ss xs → ∀ k,
      ((ss k).proc p).delivered.Nodup ∧
        ∀ m ∈ ((ss k).proc p).delivered, m = ⟨m.sender, inp m.sender⟩

/-- One-shot broadcast agreement on `TotalOrderBroadcastAlg` (after [HadzilacosToueg1994], §3.1,
p. 10; [ChandraToueg1996], §4, p. 238): in every `f`-admissible run, if a correct process `p`
delivers `m`, then every correct process `q` eventually delivers `m`. -/
@[expose]
def Agreement [Fintype P] [DecidableEq P] [DecidableEq M] [DecidableEq V]
    (π : TotalOrderBroadcastAlg P M S V) (f : ℕ) : Prop :=
  ∀ inp ss xs, π.AdmissibleRun inp f ss xs →
    ∀ p q, BcastProcFair p ss xs → BcastProcFair q ss xs →
      ∀ m k, m ∈ ((ss k).proc p).delivered → ∃ k', m ∈ ((ss k').proc q).delivered

/-- Non-uniform total-order delivery on one-shot `TotalOrderBroadcastAlg` (after
[HadzilacosToueg1994], §3.4, p. 13; [ChandraToueg1996], §7, p. 248): in every `f`-admissible run, if
two correct processes `p` and `q` both deliver `m₁` and `m₂`, then `p` delivers `m₁` before `m₂` iff
`q` delivers `m₁` before `m₂`. -/
@[expose]
def TotalOrder [Fintype P] [DecidableEq P] [DecidableEq M] [DecidableEq V]
    (π : TotalOrderBroadcastAlg P M S V) (f : ℕ) : Prop :=
  ∀ inp ss xs, π.AdmissibleRun inp f ss xs →
    ∀ p q, BcastProcFair p ss xs → BcastProcFair q ss xs →
      ∀ m₁ m₂ k₁ k₂,
        m₁ ∈ ((ss k₁).proc p).delivered → m₂ ∈ ((ss k₁).proc p).delivered →
        m₁ ∈ ((ss k₂).proc q).delivered → m₂ ∈ ((ss k₂).proc q).delivered →
        (((ss k₁).proc p).delivered.idxOf m₁ < ((ss k₁).proc p).delivered.idxOf m₂ ↔
          ((ss k₂).proc q).delivered.idxOf m₁ < ((ss k₂).proc q).delivered.idxOf m₂)

/-- Uniform total-order delivery on one-shot `TotalOrderBroadcastAlg` (after [HadzilacosToueg1994],
§3.8, p. 15): in every reachable global configuration `s`, for any two processes `p` and `q`
(faulty or correct) that have both delivered `m₁` and `m₂`, `p` delivered `m₁` before `m₂` iff `q`
delivered `m₁` before `m₂`. -/
@[expose]
def UniformTotalOrder [Fintype P] [DecidableEq P] [DecidableEq M] [DecidableEq V]
    (π : TotalOrderBroadcastAlg P M S V) : Prop :=
  ∀ inp s, π.Reachable inp s →
    ∀ p q m₁ m₂,
      m₁ ∈ (s.proc p).delivered → m₂ ∈ (s.proc p).delivered →
      m₁ ∈ (s.proc q).delivered → m₂ ∈ (s.proc q).delivered →
      ((s.proc p).delivered.idxOf m₁ < (s.proc p).delivered.idxOf m₂ ↔
        (s.proc q).delivered.idxOf m₁ < (s.proc q).delivered.idxOf m₂)

/-- One-shot `f`-resilient reliable broadcast specification on `TotalOrderBroadcastAlg` (after
[HadzilacosToueg1994], §3.1). -/
@[expose]
def SolvesReliableBroadcast [Fintype P] [DecidableEq P] [DecidableEq M] [DecidableEq V]
    (π : TotalOrderBroadcastAlg P M S V) (f : ℕ) : Prop :=
  π.Validity f ∧ π.Integrity f ∧ π.Agreement f

/-- One-shot `f`-resilient total-order (atomic) broadcast specification on `TotalOrderBroadcastAlg`
(after [HadzilacosToueg1994], §3.4; [ChandraToueg1996], §7). -/
@[expose]
def SolvesTotalOrderBroadcast [Fintype P] [DecidableEq P] [DecidableEq M] [DecidableEq V]
    (π : TotalOrderBroadcastAlg P M S V) (f : ℕ) : Prop :=
  π.SolvesReliableBroadcast f ∧ π.TotalOrder f

private theorem tr_delivered_prefix [DecidableEq P] [DecidableEq M] [DecidableEq V]
    (π : TotalOrderBroadcastAlg P M S V) {s s' : BcastState P M S V} {act : BcastAction P M V}
    (htr : π.lts.Tr s act s') (p : P) :
    (s.proc p).delivered <+: (s'.proc p).delivered := by
  cases act with
  | none =>
    simp only [lts] at htr
    rw [htr]
  | some e =>
    rcases htr with ⟨_, rfl⟩
    simp only [recvEvent]
    by_cases hp : p = e.dest
    · subst hp; simp [List.prefix_append]
    · simp [hp]

private theorem mTr_delivered_prefix [DecidableEq P] [DecidableEq M] [DecidableEq V]
    (π : TotalOrderBroadcastAlg P M S V) {s s' : BcastState P M S V}
    {xl : List (BcastAction P M V)} (hmtr : π.lts.MTr s xl s') (p : P) :
    (s.proc p).delivered <+: (s'.proc p).delivered := by
  induction hmtr with
  | refl => exact List.prefix_refl _
  | stepL htr _ ih => exact (π.tr_delivered_prefix htr p).trans ih

end Model

end TotalOrderBroadcastAlg

/-! ### Part 2: Reduction 1 — Total-Order Broadcast → `Cslib.FLP` Consensus & Impossibility -/

section FLPReduction

variable {P M S : Type*}

/-- Convert a `BcastEvent P M Bool` into the isomorphic `Cslib.FLP.Message P M`. -/
private def bcastEventToFLP (e : BcastEvent P M Bool) : Cslib.FLP.Message P M :=
  ⟨e.dest, e.evt⟩

private theorem bcastEventToFLP_injective : Function.Injective (@bcastEventToFLP P M) := by
  intro a b h
  cases a; cases b
  cases h
  rfl

/-- One-shot initial-broadcast reduction adapter from `TotalOrderBroadcastAlg P M S Bool` to
`Cslib.FLP.Algorithm P M S` (toward #7297, after [HadzilacosToueg1994], §7.2.1, Figure 13, p. 58
and [ChandraToueg1996], §7, p. 249): each process `p` broadcasts its initial boolean input `inp p`
upon receiving `⟨p, Sum.inl (inp p)⟩` and decides the payload of the first message delivered in its
local delivery log (latched write-once by `Cslib.FLP.Algorithm.recvMsg`). -/
@[expose]
def consensusOfTotalOrderBroadcast (π : TotalOrderBroadcastAlg P M S Bool) :
    Cslib.FLP.Algorithm P M S where
  init := π.init
  next m ps := π.next ⟨m.dest, m.msg⟩ ps.state
  send m ps :=
    (π.send ⟨m.dest, m.msg⟩ ps.state).map (fun env => ⟨env.dest, Sum.inr env.body⟩)
  out m ps := ((π.deliver ⟨m.dest, m.msg⟩ ps.state).head?).map BcastMsg.payload

private def projFLPState (s : BcastState P M S Bool) : Cslib.FLP.State P M S where
  msgs := s.msgs.map bcastEventToFLP
  proc p := ⟨(s.proc p).state, ((s.proc p).delivered.head?).map BcastMsg.payload⟩

private theorem projFLPState_start [Fintype P] (π : TotalOrderBroadcastAlg P M S Bool)
    (inp : P → Bool) :
    projFLPState (π.start inp) = (consensusOfTotalOrderBroadcast π).start inp := by
  simp [projFLPState, TotalOrderBroadcastAlg.start, Cslib.FLP.Algorithm.start,
    consensusOfTotalOrderBroadcast, bcastEventToFLP, Function.comp_def]

private theorem projFLPState_recvEvent [DecidableEq P] [DecidableEq M]
    (π : TotalOrderBroadcastAlg P M S Bool)
    (e : BcastEvent P M Bool) (s : BcastState P M S Bool) :
    projFLPState (π.recvEvent e s) =
      (consensusOfTotalOrderBroadcast π).recvMsg (bcastEventToFLP e) (projFLPState s) := by
  have herase : (s.msgs.erase e).map bcastEventToFLP =
      (s.msgs.map bcastEventToFLP).erase (bcastEventToFLP e) :=
    Multiset.map_erase bcastEventToFLP bcastEventToFLP_injective e s.msgs
  rcases e with ⟨ed, eev⟩
  simp only [projFLPState, TotalOrderBroadcastAlg.recvEvent, Cslib.FLP.Algorithm.recvMsg,
    consensusOfTotalOrderBroadcast, bcastEventToFLP, Multiset.map_add,
    Multiset.map_map, Function.comp_def, herase]
  congr 1
  funext q
  by_cases hq : q = ed
  · subst hq
    simp only [↓reduceIte]
    congr 1
    have hhead : ∀ l₁ l₂ : List (BcastMsg P Bool),
        Option.map BcastMsg.payload (l₁ ++ l₂).head? =
          if (Option.map BcastMsg.payload l₁.head?).isNone = true then
            Option.map BcastMsg.payload l₂.head?
          else Option.map BcastMsg.payload l₁.head? :=
      fun l₁ _ => by cases l₁ <;> rfl
    exact hhead _ _
  · simp [hq]

private def bcastStepOpt [DecidableEq P] [DecidableEq M] (π : TotalOrderBroadcastAlg P M S Bool)
    (s : BcastState P M S Bool) : BcastAction P M Bool → BcastState P M S Bool
  | some e => π.recvEvent e s
  | none => s

private def liftBcastStates [DecidableEq P] [DecidableEq M]
    (π : TotalOrderBroadcastAlg P M S Bool)
    (s₀ : BcastState P M S Bool) (xs : ωSequence (Cslib.FLP.Action P M)) :
    ℕ → BcastState P M S Bool
  | 0 => s₀
  | k + 1 =>
    bcastStepOpt π (liftBcastStates π s₀ xs k) ((xs k).map fun m => ⟨m.dest, m.msg⟩)

private theorem liftBcastStates_sim [DecidableEq P] [DecidableEq M]
    (π : TotalOrderBroadcastAlg P M S Bool)
    {s₀ : BcastState P M S Bool} {ss : ωSequence (Cslib.FLP.State P M S)}
    {xs : ωSequence (Cslib.FLP.Action P M)}
    (h0 : ss 0 = projFLPState s₀)
    (he : (consensusOfTotalOrderBroadcast π).lts.OmegaExecution ss xs) :
    let ss_b : ωSequence (BcastState P M S Bool) := ωSequence.mk (liftBcastStates π s₀ xs)
    let xs_b : ωSequence (BcastAction P M Bool) := xs.map (Option.map fun m => ⟨m.dest, m.msg⟩)
    (∀ k, ss k = projFLPState (ss_b k)) ∧ π.lts.OmegaExecution ss_b xs_b := by
  intro ss_b xs_b
  have hproj : ∀ k, ss k = projFLPState (ss_b k) := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      have htr := he k
      cases hact : xs k with
      | none =>
        rw [hact] at htr
        have heq := Cslib.FLP.Algorithm.tr_none htr
        simpa [ss_b, liftBcastStates, bcastStepOpt, hact, ← heq] using ih
      | some m =>
        rw [hact] at htr
        rcases htr with ⟨_, hstep⟩
        have hm_b : bcastEventToFLP ⟨m.dest, m.msg⟩ = m := by cases m; rfl
        rw [hstep, ih]
        simpa [ss_b, liftBcastStates, bcastStepOpt, hact, hm_b] using
          (projFLPState_recvEvent π ⟨m.dest, m.msg⟩ (ss_b k)).symm
  refine ⟨hproj, fun k => ?_⟩
  have htr := he k
  cases hact : xs k with
  | none =>
    simp [xs_b, ss_b, ωSequence.get_map, hact, TotalOrderBroadcastAlg.lts, liftBcastStates,
      bcastStepOpt]
  | some m =>
    rw [hact] at htr
    rcases htr with ⟨hmem, _⟩
    rw [hproj k] at hmem
    simp only [projFLPState, Multiset.mem_map] at hmem
    obtain ⟨e, he_mem, he_eq⟩ := hmem
    have he_m : e = ⟨m.dest, m.msg⟩ := by
      rw [← he_eq]; cases e; rfl
    subst he_m
    have hxs_k : xs_b k = some ⟨m.dest, m.msg⟩ := by simp [xs_b, ωSequence.get_map, hact]
    rw [hxs_k]
    exact ⟨he_mem, by simp [ss_b, liftBcastStates, bcastStepOpt, hact]⟩

private theorem procFaulty_iff_bcastProcFaulty
    {ss : ωSequence (Cslib.FLP.State P M S)} {xs : ωSequence (Cslib.FLP.Action P M)}
    {ss_b : ωSequence (BcastState P M S Bool)}
    (hproj : ∀ k, ss k = projFLPState (ss_b k)) (p : P) :
    Cslib.FLP.ProcFaulty p ss xs ↔
      TotalOrderBroadcastAlg.BcastProcFaulty p ss_b
        (xs.map (Option.map fun m => ⟨m.dest, m.msg⟩)) := by
  constructor
  · rintro ⟨k, ⟨m, hm_mem, hm_dest⟩, hstop⟩
    rw [hproj k] at hm_mem
    simp only [projFLPState, Multiset.mem_map] at hm_mem
    obtain ⟨e, he_mem, rfl⟩ := hm_mem
    refine ⟨k, ⟨e, he_mem, hm_dest⟩, fun j hkj e' hxs => ?_⟩
    simp only [ωSequence.get_map, Option.map_eq_some_iff] at hxs
    obtain ⟨m', hxj, rfl⟩ := hxs
    exact hstop j hkj m' hxj
  · rintro ⟨k, ⟨e, he_mem, he_dest⟩, hstop⟩
    refine ⟨k, ⟨bcastEventToFLP e, ?_, he_dest⟩, fun j hkj m' hxj => ?_⟩
    · rw [hproj k]
      exact Multiset.mem_map_of_mem bcastEventToFLP he_mem
    · exact hstop j hkj ⟨m'.dest, m'.msg⟩ (by simp [ωSequence.get_map, hxj])

private theorem procFair_iff_bcastProcFair
    {ss : ωSequence (Cslib.FLP.State P M S)} {xs : ωSequence (Cslib.FLP.Action P M)}
    {ss_b : ωSequence (BcastState P M S Bool)}
    (hproj : ∀ k, ss k = projFLPState (ss_b k)) (p : P) :
    Cslib.FLP.ProcFair p ss xs ↔
      TotalOrderBroadcastAlg.BcastProcFair p ss_b
        (xs.map (Option.map fun m => ⟨m.dest, m.msg⟩)) := by
  constructor
  · intro hfair e he_dest k he_mem
    have hm_mem : bcastEventToFLP e ∈ (ss k).msgs := by
      rw [hproj k]
      exact Multiset.mem_map_of_mem bcastEventToFLP he_mem
    obtain ⟨j, hkj, hxj⟩ := hfair (bcastEventToFLP e) he_dest k hm_mem
    exact ⟨j, hkj, by simp [ωSequence.get_map, hxj, bcastEventToFLP]⟩
  · intro hfair m hm_dest k hm_mem
    rw [hproj k] at hm_mem
    simp only [projFLPState, Multiset.mem_map] at hm_mem
    obtain ⟨e, he_mem, rfl⟩ := hm_mem
    obtain ⟨j, hkj, hxj⟩ := hfair e hm_dest k he_mem
    simp only [ωSequence.get_map, Option.map_eq_some_iff] at hxj
    obtain ⟨m', hx, rfl⟩ := hxj
    exact ⟨j, hkj, hx⟩

private theorem exists_zero_fault_extension [Fintype P] [DecidableEq P] [DecidableEq M]
    (a : Cslib.FLP.Algorithm P M S)
    (inp : P → Bool) {s : Cslib.FLP.State P M S} (hr : a.Reachable inp s) :
    ∃ (K : ℕ) (ss : ωSequence (Cslib.FLP.State P M S)) (xs : ωSequence (Cslib.FLP.Action P M)),
      ss K = s ∧ a.AdmissibleRun inp 0 ss xs ∧ ∀ p, Cslib.FLP.ProcFair p ss xs := by
  obtain ⟨xl_pref, hmtr_pref⟩ := hr
  let d : Cslib.FLP.DeliverMsg P M S := fun st m => ([some m], a.recvMsg m st)
  have hd : a.FairDeliverMsg d Set.univ (fun _ => True) := by
    rintro st m ⟨hm_in, _, _⟩
    exact ⟨LTS.MTr.stepL (by exact ⟨hm_in, rfl⟩) LTS.MTr.refl, List.mem_singleton.mpr rfl, trivial⟩
  obtain ⟨ss_tail, he_tail, hs0_tail, _, _, _, hfair_tail⟩ :=
    Cslib.FLP.FairScheduler.fair_omegaExecution hd s trivial
  let xs_tail := (a.fairSegActions d Set.univ s).flatten
  obtain ⟨ss_full, he_full, hs0_full, hsK_full, hdrop_ss⟩ :=
    LTS.OmegaExecution.append hmtr_pref he_tail hs0_tail
  let xs_full := xl_pref ++ω xs_tail
  have hdrop_xs : xs_full.drop xl_pref.length = xs_tail := by
    simp [xs_full, ωSequence.drop_append_of_le_length]
  have hfair_full : ∀ p, Cslib.FLP.ProcFair p ss_full xs_full := by
    intro p
    rw [← Cslib.FLP.Algorithm.drop_procFair_iff he_full p xl_pref.length, hdrop_ss, hdrop_xs]
    exact hfair_tail p (Set.mem_univ p)
  exact ⟨xl_pref.length, ss_full, xs_full, hsK_full,
    Cslib.FLP.AdmissibleRun.fault_zero.mpr ⟨hs0_full, he_full, hfair_full⟩, hfair_full⟩

private theorem liftAdmissibleRun [Fintype P] [DecidableEq P] [DecidableEq M]
    (π : TotalOrderBroadcastAlg P M S Bool) {inp : P → Bool} {f : ℕ}
    {ss : ωSequence (Cslib.FLP.State P M S)} {xs : ωSequence (Cslib.FLP.Action P M)}
    (hadm : (consensusOfTotalOrderBroadcast π).AdmissibleRun inp f ss xs) :
    let ss_b : ωSequence (BcastState P M S Bool) :=
      ωSequence.mk (liftBcastStates π (π.start inp) xs)
    let xs_b : ωSequence (BcastAction P M Bool) := xs.map (Option.map fun m => ⟨m.dest, m.msg⟩)
    (∀ k, ss k = projFLPState (ss_b k)) ∧ π.AdmissibleRun inp f ss_b xs_b := by
  intro ss_b xs_b
  rcases hadm with ⟨hs0, he, hfair_run, hnum⟩
  obtain ⟨hproj, he_b⟩ :=
    liftBcastStates_sim π (hs0.trans (projFLPState_start π inp).symm) he
  refine ⟨hproj, rfl, he_b, fun q => ?_, ?_⟩
  · rcases hfair_run q with hfq | hfairq
    · exact Or.inl ((procFaulty_iff_bcastProcFaulty hproj q).mp hfq)
    · exact Or.inr ((procFair_iff_bcastProcFair hproj q).mp hfairq)
  · have hfault_eq : {q | TotalOrderBroadcastAlg.BcastProcFaulty q ss_b xs_b} =
        {q | Cslib.FLP.ProcFaulty q ss xs} := by
      ext q; exact (procFaulty_iff_bcastProcFaulty hproj q).symm
    simpa [TotalOrderBroadcastAlg.bcastNumProcFaulty, Cslib.FLP.numProcFaulty, hfault_eq] using hnum

/-- One-shot initial-broadcast reduction step from `TotalOrderBroadcastAlg` to binary Consensus in
`Cslib.FLP` (toward #7297, after [HadzilacosToueg1994], §7.2.1, Figure 13 & Theorem 13, p. 58 and
[ChandraToueg1996], §7, p. 249): for every fault bound `f : ℕ`, if `π` solves `f`-resilient
one-shot `SolvesTotalOrderBroadcast` over `Bool`, then `consensusOfTotalOrderBroadcast π` solves
`f`-resilient `Cslib.FLP.Algorithm.Consensus`. -/
theorem consensusOfTotalOrderBroadcast_consensus [Fintype P] [DecidableEq P] [DecidableEq M]
    {π : TotalOrderBroadcastAlg P M S Bool} {f : ℕ}
    (hπ : π.SolvesTotalOrderBroadcast f) :
    (consensusOfTotalOrderBroadcast π).Consensus f := by
  obtain ⟨⟨hval, hint, hagr⟩, htot⟩ := hπ
  let a := consensusOfTotalOrderBroadcast π
  refine ⟨?_, ?_⟩
  · intro inp s hr
    obtain ⟨K, ss, xs, hsK, hadm0, hfair_all⟩ := exists_zero_fault_extension a inp hr
    have hadmf : a.AdmissibleRun inp f ss xs :=
      Cslib.FLP.AdmissibleRun.fault_mono (Nat.zero_le f) hadm0
    obtain ⟨hproj, hadm_b⟩ := liftAdmissibleRun π hadmf
    set ss_b : ωSequence (BcastState P M S Bool) :=
      ωSequence.mk (liftBcastStates π (π.start inp) xs)
    set xs_b : ωSequence (BcastAction P M Bool) := xs.map (Option.map fun m => ⟨m.dest, m.msg⟩)
    have he_b : π.lts.OmegaExecution ss_b xs_b := hadm_b.2.1
    have hfair_b : ∀ p, TotalOrderBroadcastAlg.BcastProcFair p ss_b xs_b := fun p =>
      (procFair_iff_bcastProcFair hproj p).mp (hfair_all p)
    have hextract_head : ∀ p b, s.ProcDecided p b →
        ∃ d, ((ss_b K).proc p).delivered.head? = some d ∧ d.payload = b := by
      intro p b hdec
      rw [← hsK, hproj K] at hdec
      simp only [Cslib.FLP.State.ProcDecided, projFLPState, Option.map_eq_some_iff] at hdec
      exact hdec
    refine ⟨?_, ?_⟩
    · rintro b₁ b₂ ⟨⟨p₁, hp₁⟩, ⟨p₂, hp₂⟩⟩
      obtain ⟨d₁, hd₁_head, rfl⟩ := hextract_head p₁ b₁ hp₁
      obtain ⟨d₂, hd₂_head, rfl⟩ := hextract_head p₂ b₂ hp₂
      have hd₁_mem_K : d₁ ∈ ((ss_b K).proc p₁).delivered := List.mem_of_head? hd₁_head
      have hd₂_mem_K : d₂ ∈ ((ss_b K).proc p₂).delivered := List.mem_of_head? hd₂_head
      obtain ⟨K₁, hd₁_p₂⟩ :=
        hagr inp ss_b xs_b hadm_b p₁ p₂ (hfair_b p₁) (hfair_b p₂) d₁ K hd₁_mem_K
      obtain ⟨K₂, hd₂_p₁⟩ :=
        hagr inp ss_b xs_b hadm_b p₂ p₁ (hfair_b p₂) (hfair_b p₁) d₂ K hd₂_mem_K
      -- At a common later time `M_idx`, both logs start with their decided heads and contain
      -- both heads, so total order forces `d₁ = d₂`.
      let M_idx := max K (max K₁ K₂)
      have hpref : ∀ p k, k ≤ M_idx →
          ((ss_b k).proc p).delivered <+: ((ss_b M_idx).proc p).delivered :=
        fun p _ hk => π.mTr_delivered_prefix (he_b.extract_mTr hk) p
      have hhead : ∀ p d, ((ss_b K).proc p).delivered.head? = some d →
          ∃ l, ((ss_b M_idx).proc p).delivered = d :: l := fun p d h => by
        obtain ⟨t, ht⟩ := hpref p K (Nat.le_max_left _ _)
        obtain ⟨l, hl⟩ := List.head?_eq_some_iff.mp h
        exact ⟨l ++ t, by rw [← ht, hl, List.cons_append]⟩
      obtain ⟨l₁, hl₁⟩ := hhead p₁ d₁ hd₁_head
      obtain ⟨l₂, hl₂⟩ := hhead p₂ d₂ hd₂_head
      have hd₂_M₁ := (hpref p₁ K₂ (by omega)).subset hd₂_p₁
      have hd₁_M₂ := (hpref p₂ K₁ (by omega)).subset hd₁_p₂
      by_cases hdeq : d₁ = d₂
      · rw [hdeq]
      · have hord := htot inp ss_b xs_b hadm_b p₁ p₂ (hfair_b p₁) (hfair_b p₂)
          d₁ d₂ M_idx M_idx (by simp [hl₁]) hd₂_M₁ hd₁_M₂ (by simp [hl₂])
        rw [hl₁, hl₂] at hord
        simp [List.idxOf_cons_ne, hdeq, Ne.symm hdeq] at hord
    · rintro b ⟨p, hp⟩
      obtain ⟨d, hd_head, rfl⟩ := hextract_head p b hp
      have hd_mem : d ∈ ((ss_b K).proc p).delivered := List.mem_of_head? hd_head
      have hd_eq := (hint inp ss_b xs_b hadm_b p (hfair_b p) K).2 d hd_mem
      exact ⟨d.sender, (congrArg BcastMsg.payload hd_eq).symm⟩
  · intro inp ss xs hadm p
    rcases hadm.2.2.1 p with hfaulty | hfair
    · exact Or.inl hfaulty
    · right
      obtain ⟨hproj, hadm_b⟩ := liftAdmissibleRun π hadm
      set ss_b : ωSequence (BcastState P M S Bool) :=
        ωSequence.mk (liftBcastStates π (π.start inp) xs)
      set xs_b : ωSequence (BcastAction P M Bool) := xs.map (Option.map fun m => ⟨m.dest, m.msg⟩)
      have hfair_p : TotalOrderBroadcastAlg.BcastProcFair p ss_b xs_b :=
        (procFair_iff_bcastProcFair hproj p).mp hfair
      obtain ⟨k, hk_mem⟩ := hval inp ss_b xs_b hadm_b p hfair_p
      cases hl : ((ss_b k).proc p).delivered with
      | nil => simp [hl] at hk_mem
      | cons d₀ rest =>
        refine ⟨k, d₀.payload, ?_⟩
        rw [hproj k]
        change (((ss_b k).proc p).delivered.head?).map BcastMsg.payload = some d₀.payload
        simp [hl]

/-- Restrict a `TotalOrderBroadcastAlg P M S V` along two distinct values `v₀ ≠ v₁ : V` to obtain a
boolean `TotalOrderBroadcastAlg P M S Bool`. -/
private def comapBoolPayload {V : Type*} [DecidableEq V] (v₀ v₁ : V)
    (π : TotalOrderBroadcastAlg P M S V) : TotalOrderBroadcastAlg P M S Bool where
  init := π.init
  next e st := π.next ⟨e.dest, e.evt.map (fun b => if b then v₁ else v₀) id⟩ st
  send e st := π.send ⟨e.dest, e.evt.map (fun b => if b then v₁ else v₀) id⟩ st
  deliver e st :=
    (π.deliver ⟨e.dest, e.evt.map (fun b => if b then v₁ else v₀) id⟩ st).map
      (fun m => ⟨m.sender, decide (m.payload = v₁)⟩)

private theorem solvesTotalOrderBroadcast_comapBoolPayload [Fintype P]
    [DecidableEq P] [DecidableEq M]
    {V : Type*} [DecidableEq V] {v₀ v₁ : V} (hne : v₀ ≠ v₁)
    {π : TotalOrderBroadcastAlg P M S V} {f : ℕ}
    (hπ : π.SolvesTotalOrderBroadcast f) :
    (comapBoolPayload v₀ v₁ π).SolvesTotalOrderBroadcast f := by
  let enc : Bool → V := fun b => if b then v₁ else v₀
  let dec : V → Bool := fun v => decide (v = v₁)
  have hdec_enc : ∀ b, dec (enc b) = b := by
    intro b; cases b <;> simp [enc, dec, hne]
  let mapEvt : BcastEvent P M Bool → BcastEvent P M V :=
    fun e => ⟨e.dest, e.evt.map enc id⟩
  have hmapEvt_inj : Function.Injective mapEvt := by
    rintro ⟨d₁, e₁⟩ ⟨d₂, e₂⟩ h
    simp only [mapEvt, BcastEvent.mk.injEq] at h
    rw [h.1, Sum.map_injective.2 ⟨Function.LeftInverse.injective hdec_enc,
      Function.injective_id⟩ h.2]
  let mapMsg : BcastMsg P V → BcastMsg P Bool := fun m => ⟨m.sender, dec m.payload⟩
  let πB := comapBoolPayload v₀ v₁ π
  have hlift : ∀ inp ssB xsB, πB.AdmissibleRun inp f ssB xsB →
      ∃ ssV xsV, π.AdmissibleRun (enc ∘ inp) f ssV xsV ∧
        (∀ k p, ((ssB k).proc p).delivered = (((ssV k).proc p).delivered).map mapMsg) ∧
        (∀ p, TotalOrderBroadcastAlg.BcastProcFair p ssB xsB ↔
          TotalOrderBroadcastAlg.BcastProcFair p ssV xsV) := by
    intro inp ssB xsB hadmB
    rcases hadmB with ⟨hs0B, heB, hfairRunB, hnumB⟩
    let xsV : ωSequence (BcastAction P M V) := xsB.map (Option.map mapEvt)
    let stepV : BcastState P M S V → BcastAction P M V → BcastState P M S V :=
      fun s act => match act with | some e => π.recvEvent e s | none => s
    let mkStates : ℕ → BcastState P M S V :=
      Nat.rec (π.start (enc ∘ inp)) (fun k acc => stepV acc (xsV k))
    let ssV : ωSequence (BcastState P M S V) := ωSequence.mk mkStates
    have hssV_zero : ssV 0 = π.start (enc ∘ inp) := rfl
    have hssV_succ : ∀ k, ssV (k + 1) = stepV (ssV k) (xsV k) := fun _ => rfl
    have hsim : ∀ k, (ssV k).msgs = (ssB k).msgs.map mapEvt ∧
        ∀ p, ((ssB k).proc p).state = ((ssV k).proc p).state ∧
          ((ssB k).proc p).delivered = (((ssV k).proc p).delivered).map mapMsg := by
      intro k
      induction k with
      | zero =>
        rw [hs0B, hssV_zero]
        simp [TotalOrderBroadcastAlg.start, πB, comapBoolPayload, mapEvt, Function.comp_def]
      | succ k ih =>
        obtain ⟨hmsgs_k, hproc_k⟩ := ih
        have htrB := heB k
        cases hact : xsB k with
        | none =>
          rw [hact] at htrB
          simp only [TotalOrderBroadcastAlg.lts] at htrB
          have hxsV_k : xsV k = none := by simp [xsV, ωSequence.get_map, hact]
          rw [hssV_succ, hxsV_k, htrB]
          exact ⟨hmsgs_k, hproc_k⟩
        | some e =>
          rw [hact] at htrB
          rcases htrB with ⟨_, hstepB⟩
          have hxsV_k : xsV k = some (mapEvt e) := by simp [xsV, ωSequence.get_map, hact]
          rw [hssV_succ, hxsV_k, hstepB]
          simp only [stepV, TotalOrderBroadcastAlg.recvEvent, πB, comapBoolPayload]
          have herase : ((ssB k).msgs.erase e).map mapEvt =
              ((ssB k).msgs.map mapEvt).erase (mapEvt e) :=
            Multiset.map_erase mapEvt hmapEvt_inj e (ssB k).msgs
          have hst_eq : ((ssB k).proc e.dest).state = ((ssV k).proc e.dest).state :=
            (hproc_k e.dest).1
          refine ⟨?_, fun q => ?_⟩
          · rw [← hmsgs_k] at herase
            simp [Multiset.map_add, Multiset.map_map, Function.comp_def, herase, hst_eq, mapEvt,
              enc]
          · by_cases hq : q = e.dest
            · subst hq
              simp [hst_eq, (hproc_k e.dest).2, mapEvt, mapMsg, enc, dec]
            · simp [hq, mapEvt, hproc_k q]
    have hmemV : ∀ k e, mapEvt e ∈ (ssV k).msgs ↔ e ∈ (ssB k).msgs := fun k e => by
      rw [(hsim k).1]; exact Multiset.mem_map_of_injective hmapEvt_inj
    have hxsV : ∀ j e, xsV j = some (mapEvt e) ↔ xsB j = some e := fun j e => by
      simp [xsV, ωSequence.get_map, Option.map_eq_some_iff, hmapEvt_inj.eq_iff]
    have heV : π.lts.OmegaExecution ssV xsV := by
      intro k
      have htrB := heB k
      cases hact : xsB k with
      | none =>
        have hxsV_k : xsV k = none := by simp [xsV, ωSequence.get_map, hact]
        rw [hssV_succ, hxsV_k]
        rfl
      | some e =>
        rw [hact] at htrB
        rw [hssV_succ, (hxsV k e).2 hact]
        exact ⟨(hmemV k e).2 htrB.1, rfl⟩
    have hfair_iff : ∀ p, TotalOrderBroadcastAlg.BcastProcFair p ssB xsB ↔
        TotalOrderBroadcastAlg.BcastProcFair p ssV xsV := by
      refine fun p => ⟨fun hf eV heV_dest k heV_mem => ?_, fun hf eB heB_dest k heB_mem => ?_⟩
      · rw [(hsim k).1, Multiset.mem_map] at heV_mem
        obtain ⟨eB, heB_mem, rfl⟩ := heV_mem
        simpa only [hxsV] using hf eB heV_dest k heB_mem
      · simpa only [hxsV] using hf (mapEvt eB) heB_dest k ((hmemV k eB).2 heB_mem)
    have hfault_iff : ∀ p, TotalOrderBroadcastAlg.BcastProcFaulty p ssB xsB ↔
        TotalOrderBroadcastAlg.BcastProcFaulty p ssV xsV := by
      intro p
      constructor
      · rintro ⟨k, ⟨eB, heB_mem, heB_dest⟩, hstop⟩
        refine ⟨k, ⟨mapEvt eB, (hmemV k eB).2 heB_mem, heB_dest⟩, fun j hkj eV hxj => ?_⟩
        simp only [xsV, ωSequence.get_map, Option.map_eq_some_iff] at hxj
        obtain ⟨eB', hx, rfl⟩ := hxj
        exact hstop j hkj eB' hx
      · rintro ⟨k, ⟨eV, heV_mem, heV_dest⟩, hstop⟩
        rw [(hsim k).1, Multiset.mem_map] at heV_mem
        obtain ⟨eB, heB_mem, rfl⟩ := heV_mem
        exact ⟨k, ⟨eB, heB_mem, heV_dest⟩,
          fun j hkj eB' hxj => hstop j hkj (mapEvt eB') ((hxsV j eB').2 hxj)⟩
    have hadmV : π.AdmissibleRun (enc ∘ inp) f ssV xsV := by
      refine ⟨hssV_zero, heV, fun p => ?_, ?_⟩
      · rcases hfairRunB p with hf | hfair
        · exact Or.inl ((hfault_iff p).mp hf)
        · exact Or.inr ((hfair_iff p).mp hfair)
      · have hset : {p | TotalOrderBroadcastAlg.BcastProcFaulty p ssV xsV} =
            {p | TotalOrderBroadcastAlg.BcastProcFaulty p ssB xsB} := by
          ext p; exact (hfault_iff p).symm
        simpa [TotalOrderBroadcastAlg.bcastNumProcFaulty, hset] using hnumB
    exact ⟨ssV, xsV, hadmV, fun k p => ((hsim k).2 p).2, hfair_iff⟩
  obtain ⟨⟨hval, hint, hagr⟩, htot⟩ := hπ
  have hmapMsg_inj_on : ∀ (inp : P → Bool) {m₁ m₂ : BcastMsg P V},
      m₁ = ⟨m₁.sender, enc (inp m₁.sender)⟩ →
      m₂ = ⟨m₂.sender, enc (inp m₂.sender)⟩ →
      mapMsg m₁ = mapMsg m₂ → m₁ = m₂ := by
    intro inp m₁ m₂ hm₁ hm₂ heq
    have hs : m₁.sender = m₂.sender := congrArg (BcastMsg.sender (P := P) (V := Bool)) heq
    rw [hm₁, hm₂, hs]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro inp ssB xsB hadmB p hfairB
    obtain ⟨ssV, xsV, hadmV, hdel_eq, hfair_iff⟩ := hlift inp ssB xsB hadmB
    obtain ⟨k, hk⟩ := hval (enc ∘ inp) ssV xsV hadmV p ((hfair_iff p).mp hfairB)
    refine ⟨k, ?_⟩
    rw [hdel_eq k p, List.mem_map]
    exact ⟨⟨p, enc (inp p)⟩, hk, by simp [mapMsg, hdec_enc]⟩
  · intro inp ssB xsB hadmB p hfairB k
    obtain ⟨ssV, xsV, hadmV, hdel_eq, hfair_iff⟩ := hlift inp ssB xsB hadmB
    obtain ⟨hnodupV, hintV⟩ := hint (enc ∘ inp) ssV xsV hadmV p ((hfair_iff p).mp hfairB) k
    rw [hdel_eq k p]
    refine ⟨?_, ?_⟩
    · rw [List.nodup_map_iff_inj_on hnodupV]
      intro m₁ hm₁ m₂ hm₂ heq
      exact hmapMsg_inj_on inp (hintV m₁ hm₁) (hintV m₂ hm₂) heq
    · intro mB hmB
      rw [List.mem_map] at hmB
      obtain ⟨mV, hmV, rfl⟩ := hmB
      have hmV_eq := hintV mV hmV
      conv_lhs => rw [hmV_eq]
      simp [mapMsg, hdec_enc]
  · intro inp ssB xsB hadmB p q hfairP hfairQ mB k hmB
    obtain ⟨ssV, xsV, hadmV, hdel_eq, hfair_iff⟩ := hlift inp ssB xsB hadmB
    rw [hdel_eq k p, List.mem_map] at hmB
    obtain ⟨mV, hmV, rfl⟩ := hmB
    obtain ⟨k', hk'⟩ := hagr (enc ∘ inp) ssV xsV hadmV p q
      ((hfair_iff p).mp hfairP) ((hfair_iff q).mp hfairQ) mV k hmV
    refine ⟨k', ?_⟩
    rw [hdel_eq k' q, List.mem_map]
    exact ⟨mV, hk', rfl⟩
  · intro inp ssB xsB hadmB p q hfairP hfairQ m₁ m₂ k₁ k₂ hm₁P hm₂P hm₁Q hm₂Q
    obtain ⟨ssV, xsV, hadmV, hdel_eq, hfair_iff⟩ := hlift inp ssB xsB hadmB
    have hfairPV := (hfair_iff p).mp hfairP
    have hfairQV := (hfair_iff q).mp hfairQ
    obtain ⟨_, hintPV⟩ := hint (enc ∘ inp) ssV xsV hadmV p hfairPV k₁
    obtain ⟨_, hintQV⟩ := hint (enc ∘ inp) ssV xsV hadmV q hfairQV k₂
    rw [hdel_eq k₁ p] at hm₁P hm₂P ⊢
    rw [hdel_eq k₂ q] at hm₁Q hm₂Q ⊢
    rw [List.mem_map] at hm₁P hm₂P hm₁Q hm₂Q
    obtain ⟨u₁, hu₁P, rfl⟩ := hm₁P
    obtain ⟨u₂, hu₂P, rfl⟩ := hm₂P
    obtain ⟨w₁, hw₁Q, hw₁_eq⟩ := hm₁Q
    obtain ⟨w₂, hw₂Q, hw₂_eq⟩ := hm₂Q
    have hw₁_u₁ : w₁ = u₁ :=
      hmapMsg_inj_on inp (hintQV w₁ hw₁Q) (hintPV u₁ hu₁P) hw₁_eq
    have hw₂_u₂ : w₂ = u₂ :=
      hmapMsg_inj_on inp (hintQV w₂ hw₂Q) (hintPV u₂ hu₂P) hw₂_eq
    have hu₁Q : u₁ ∈ ((ssV k₂).proc q).delivered := hw₁_u₁ ▸ hw₁Q
    have hu₂Q : u₂ ∈ ((ssV k₂).proc q).delivered := hw₂_u₂ ▸ hw₂Q
    have hidx_map : ∀ (l : List (BcastMsg P V))
        (hl : ∀ m ∈ l, m = ⟨m.sender, enc (inp m.sender)⟩) (x : BcastMsg P V) (hx : x ∈ l),
        (l.map mapMsg).idxOf (mapMsg x) = l.idxOf x := by
      intro l hl x hx
      induction l with
      | nil => cases hx
      | cons hd tl ih =>
        by_cases hxeq : hd = x
        · subst hxeq; simp
        · have hmap_ne : mapMsg hd ≠ mapMsg x := fun hcontra =>
            hxeq (hmapMsg_inj_on inp (hl hd List.mem_cons_self) (hl x hx) hcontra)
          have htl_mem : x ∈ tl := List.mem_of_ne_of_mem (Ne.symm hxeq) hx
          rw [List.map_cons, List.idxOf_cons_ne _ hmap_ne, List.idxOf_cons_ne _ hxeq,
            ih (fun m hm => hl m (List.mem_cons_of_mem hd hm)) htl_mem]
    rw [hidx_map _ hintPV u₁ hu₁P, hidx_map _ hintPV u₂ hu₂P,
      hidx_map _ hintQV u₁ hu₁Q, hidx_map _ hintQV u₂ hu₂Q]
    exact htot (enc ∘ inp) ssV xsV hadmV p q hfairPV hfairQV u₁ u₂ k₁ k₂ hu₁P hu₂P hu₁Q hu₂Q

/-- One-shot initial-broadcast impossibility step for `f ≥ 1` crash faults (toward #7297, after
[HadzilacosToueg1994], §7.2.1, Corollary 2, p. 58 and [ChandraToueg1996], §7, observation (1),
p. 249): for any finite process set `P` with `2 ≤ Fintype.card P`, any nontrivial payload type `V`,
and any fault bound `1 ≤ f`, there is no deterministic asynchronous `f`-resilient one-shot
`TotalOrderBroadcastAlg`.

Proved by reducing binary Consensus to one-shot `TotalOrderBroadcastAlg` via
`consensusOfTotalOrderBroadcast` and applying `Cslib.FLP.Consensus.ge_one_not_exists` directly. -/
theorem not_exists_oneShotTotalOrderBroadcast_ge_one [Fintype P] [DecidableEq P] [DecidableEq M]
    {V : Type*} [DecidableEq V] [Nontrivial V]
    (hc : 2 ≤ Fintype.card P) {f : ℕ} (hf : 1 ≤ f) :
    ¬ ∃ π : TotalOrderBroadcastAlg P M S V, π.SolvesTotalOrderBroadcast f := by
  rintro ⟨π, hπ⟩
  obtain ⟨v₀, v₁, hne⟩ := exists_pair_ne V
  have hbool := solvesTotalOrderBroadcast_comapBoolPayload hne hπ
  have hcons := consensusOfTotalOrderBroadcast_consensus hbool
  exact Cslib.FLP.Consensus.ge_one_not_exists (P := P) (M := M) (S := S) hc hf ⟨_, hcons⟩

/-- One-shot initial-broadcast uniformity step via `Cslib.FLP.FairScheduler` (toward #7297): in
purely asynchronous crash-stop message passing, non-uniform `SolvesTotalOrderBroadcast f` on a
one-shot `TotalOrderBroadcastAlg` implies `UniformTotalOrder` on all reachable configurations,
because any finite reachable prefix extends to a `0`-fault admissible run in which every process is
`BcastProcFair`. -/
theorem uniformTotalOrder_of_solvesTotalOrderBroadcast [Fintype P] [DecidableEq P] [DecidableEq M]
    {V : Type*} [DecidableEq V] {π : TotalOrderBroadcastAlg P M S V} {f : ℕ}
    (hπ : π.SolvesTotalOrderBroadcast f) :
    π.UniformTotalOrder := by
  intro inp s ⟨xl, hmtr⟩ p q m₁ m₂ hm₁p hm₂p hm₁q hm₂q
  let aWrap : Cslib.FLP.Algorithm P (V ⊕ M) S :=
    { init := π.init
      next := fun m ps => match m.msg with
        | Sum.inl _ => ps.state
        | Sum.inr ev => π.next ⟨m.dest, ev⟩ ps.state
      send := fun m ps => match m.msg with
        | Sum.inl _ => 0
        | Sum.inr ev =>
          (π.send ⟨m.dest, ev⟩ ps.state).map (fun env => ⟨env.dest, Sum.inr (Sum.inr env.body)⟩)
      out := fun _ _ => none }
  let toWrapMsg : BcastEvent P M V → Cslib.FLP.Message P (V ⊕ M) :=
    fun e => ⟨e.dest, Sum.inr e.evt⟩
  let toWrapState : BcastState P M S V → Cslib.FLP.State P (V ⊕ M) S :=
    fun st => ⟨st.msgs.map toWrapMsg, fun r => ⟨(st.proc r).state, none⟩⟩
  have htoWrap_inj : Function.Injective toWrapMsg := by
    rintro ⟨d₁, e₁⟩ ⟨d₂, e₂⟩ h; cases h; rfl
  let d : Cslib.FLP.DeliverMsg P (V ⊕ M) S := fun st m => ([some m], aWrap.recvMsg m st)
  have hd : aWrap.FairDeliverMsg d Set.univ (fun _ => True) := by
    rintro st m ⟨hm_in, _, _⟩
    exact ⟨LTS.MTr.stepL (by exact ⟨hm_in, rfl⟩) LTS.MTr.refl, List.mem_singleton.mpr rfl, trivial⟩
  obtain ⟨ss_tail_w, he_tail_w, hs0_tail_w, _, _, _, hfair_tail_w⟩ :=
    Cslib.FLP.FairScheduler.fair_omegaExecution hd (toWrapState s) trivial
  let xs_tail_w := (aWrap.fairSegActions d Set.univ (toWrapState s)).flatten
  let unWrapAct : Cslib.FLP.Action P (V ⊕ M) → BcastAction P M V
    | some ⟨dest, Sum.inr ev⟩ => some ⟨dest, ev⟩
    | _ => none
  let stepTail : BcastState P M S V → BcastAction P M V → BcastState P M S V :=
    fun st act => match act with | some e => π.recvEvent e st | none => st
  let tailStates : ℕ → BcastState P M S V :=
    Nat.rec s (fun k acc => stepTail acc (unWrapAct (xs_tail_w k)))
  let ss_tail : ωSequence (BcastState P M S V) := ωSequence.mk tailStates
  let xs_tail : ωSequence (BcastAction P M V) := xs_tail_w.map unWrapAct
  have hss_tail_zero : ss_tail 0 = s := rfl
  have hss_tail_succ : ∀ k, ss_tail (k + 1) = stepTail (ss_tail k) (unWrapAct (xs_tail_w k)) :=
    fun _ => rfl
  have htail_sim : ∀ k, ss_tail_w k = toWrapState (ss_tail k) := by
    intro k
    induction k with
    | zero => exact hs0_tail_w
    | succ k ih =>
      have htr := he_tail_w k
      cases hact : xs_tail_w k with
      | none =>
        rw [hact] at htr
        have heq := Cslib.FLP.Algorithm.tr_none htr
        rw [← heq, hss_tail_succ, hact]
        exact ih
      | some mw =>
        rw [hact] at htr
        rcases htr with ⟨hmw_in, hstep⟩
        rw [ih] at hmw_in
        simp only [toWrapState, Multiset.mem_map] at hmw_in
        obtain ⟨e, _, rfl⟩ := hmw_in
        rw [hstep, ih, hss_tail_succ, hact]
        have herase : ((ss_tail k).msgs.erase e).map toWrapMsg =
            ((ss_tail k).msgs.map toWrapMsg).erase (toWrapMsg e) :=
          Multiset.map_erase toWrapMsg htoWrap_inj e (ss_tail k).msgs
        simp only [stepTail, toWrapMsg, unWrapAct, toWrapState,
          TotalOrderBroadcastAlg.recvEvent, Cslib.FLP.Algorithm.recvMsg, aWrap,
          Multiset.map_add, Multiset.map_map, Function.comp_def, herase]
        congr 1
        funext r
        by_cases hr : r = e.dest <;> simp [hr]
  have he_tail : π.lts.OmegaExecution ss_tail xs_tail := by
    intro k
    have htr := he_tail_w k
    cases hact : xs_tail_w k with
    | none =>
      have hxs_k : xs_tail k = none := by simp [xs_tail, ωSequence.get_map, hact, unWrapAct]
      rw [hxs_k, hss_tail_succ, hact]
      rfl
    | some mw =>
      rw [hact] at htr
      rcases htr with ⟨hmw_in, _⟩
      rw [htail_sim k] at hmw_in
      simp only [toWrapState, Multiset.mem_map] at hmw_in
      obtain ⟨e, he_in, rfl⟩ := hmw_in
      have hxs_k : xs_tail k = some e := by
        cases e; simp [xs_tail, ωSequence.get_map, hact, toWrapMsg, unWrapAct]
      rw [hxs_k, hss_tail_succ, hact]
      cases e
      exact ⟨he_in, rfl⟩
  obtain ⟨ss_full, he_full, hs0_full, hsK_full, hdrop_ss⟩ :=
    LTS.OmegaExecution.append hmtr he_tail hss_tail_zero
  let xs_full := xl ++ω xs_tail
  have hdrop_xs : xs_full.drop xl.length = xs_tail := by
    simp [xs_full, ωSequence.drop_append_of_le_length]
  have hfair_tail : ∀ r, TotalOrderBroadcastAlg.BcastProcFair r ss_tail xs_tail := by
    intro r e he_dest k he_mem
    have hmw_mem : toWrapMsg e ∈ (ss_tail_w k).msgs := by
      rw [htail_sim k]; exact Multiset.mem_map_of_mem toWrapMsg he_mem
    obtain ⟨j, hkj, hxj⟩ := hfair_tail_w r (Set.mem_univ r) (toWrapMsg e) he_dest k hmw_mem
    have hxj' : xs_tail_w j = some (toWrapMsg e) := hxj
    refine ⟨j, hkj, ?_⟩
    cases e
    simp [xs_tail, ωSequence.get_map, hxj', toWrapMsg, unWrapAct]
  have hmTr_notRcvd : ∀ {s₁ s₂ : BcastState P M S V} {acts : List (BcastAction P M V)}
      {e : BcastEvent P M V},
      π.lts.MTr s₁ acts s₂ → e ∈ s₁.msgs → some e ∉ acts → e ∈ s₂.msgs := by
    intro s₁ s₂ acts e hm hin hnot
    induction acts generalizing s₁ with
    | nil =>
      cases hm
      exact hin
    | cons act rest ih =>
      cases hm with
      | stepL htr hrest =>
        cases act with
        | none =>
          simp only [TotalOrderBroadcastAlg.lts] at htr
          subst htr
          exact ih hrest hin (fun h => hnot (List.mem_cons_of_mem none h))
        | some e' =>
          rcases htr with ⟨_, hstep⟩
          subst hstep
          have hne : e ≠ e' := fun heq => hnot (heq ▸ List.mem_cons_self)
          have hin' : e ∈ (π.recvEvent e' s₁).msgs :=
            Multiset.mem_add.mpr (Or.inl ((Multiset.mem_erase_of_ne hne).mpr hin))
          exact ih hrest hin' (fun h => hnot (List.mem_cons_of_mem _ h))
  have hfair_full : ∀ r, TotalOrderBroadcastAlg.BcastProcFair r ss_full xs_full := by
    -- Either `e` is processed before the tail starts, or it is still pending when the tail
    -- starts and the fair tail processes it.
    intro r e he_dest k he_mem
    let K := max k xl.length
    by_cases hin_pref : some e ∈ xs_full.extract k K
    · obtain ⟨idx, hidx, hget_idx⟩ := List.getElem_of_mem hin_pref
      have hidx_len : idx < K - k := by simpa [ωSequence.length_extract] using hidx
      exact ⟨k + idx, by omega, (ωSequence.get_extract hidx_len).symm.trans hget_idx⟩
    · have he_tail : e ∈ (ss_tail (K - xl.length)).msgs := by
        rw [← hdrop_ss, ωSequence.get_drop, Nat.add_sub_cancel' (le_max_right _ _)]
        exact hmTr_notRcvd (he_full.extract_mTr (le_max_left _ _)) he_mem hin_pref
      obtain ⟨j, hj, hxj⟩ := hfair_tail r e he_dest _ he_tail
      refine ⟨xl.length + j, by omega, ?_⟩
      have hget : (xs_full.drop xl.length) j = some e := by rwa [hdrop_xs]
      simpa [ωSequence.get_drop] using hget
  have hno_faulty : ∀ r, ¬ TotalOrderBroadcastAlg.BcastProcFaulty r ss_full xs_full := by
    rintro r ⟨k, ⟨e, he_in, he_dest⟩, hstop⟩
    obtain ⟨j, hkj, hxj⟩ := hfair_full r e he_dest k he_in
    exact hstop j hkj e hxj he_dest
  have hadm_full : π.AdmissibleRun inp f ss_full xs_full := by
    refine ⟨hs0_full, he_full, fun r => Or.inr (hfair_full r), ?_⟩
    have hempty : {r | TotalOrderBroadcastAlg.BcastProcFaulty r ss_full xs_full} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr hno_faulty
    simp [TotalOrderBroadcastAlg.bcastNumProcFaulty, hempty]
  rw [← hsK_full] at hm₁p hm₂p hm₁q hm₂q ⊢
  exact hπ.2 inp ss_full xs_full hadm_full p q (hfair_full p) (hfair_full q)
    m₁ m₂ xl.length xl.length hm₁p hm₂p hm₁q hm₂q

end FLPReduction

/-! ### Part 3: Zero-Fault Deterministic Sequencer Algorithm (`f = 0`) -/

section ZeroFaultSequencer

/-- Entry in a process's sequencer reorder buffer pairing sequence `slot` with `item`. -/
@[ext]
structure SlotEntry (P V : Type*) where
  /-- Assigned sequence number. -/
  slot : ℕ
  /-- Broadcast message assigned to `slot`. -/
  item : BcastMsg P V
  deriving @[expose] DecidableEq

/-- Result of draining consecutive available slots from a sequencer reorder buffer. -/
@[ext]
structure DrainResult (P V : Type*) where
  /-- Updated next-undelivered slot index. -/
  nextDeliver : ℕ
  /-- Broadcast messages newly drained in slot order. -/
  delivered : List (BcastMsg P V)
  deriving @[expose] DecidableEq

/-- Protocol message type of `zeroFaultTotalOrderAlg`: processes send `propose item` to the fixed
`leader`, and `leader` broadcasts `ordered slot item` to all processes. -/
inductive SeqMsg (P V : Type*) where
  /-- Process proposes its initial `BcastMsg` to `leader`. -/
  | propose (item : BcastMsg P V)
  /-- Sequencer `leader` assigns `slot` to `item` and broadcasts it to all processes. -/
  | ordered (slot : ℕ) (item : BcastMsg P V)
  deriving @[expose] DecidableEq

/-- Local state of each process in `zeroFaultTotalOrderAlg`. -/
@[ext]
structure SeqState (P V : Type*) where
  /-- Next sequence number to be assigned by `leader` (unused at non-leaders). -/
  nextSlot : ℕ
  /-- Next consecutive slot index this process is waiting to deliver. -/
  nextDeliver : ℕ
  /-- Buffer of received `SlotEntry` records from `leader`. -/
  buf : List (SlotEntry P V)
  deriving @[expose] DecidableEq

/-- Look up the first item assigned to `slot` in `buf`. -/
@[expose]
def lookupSlot {P V : Type*} : ℕ → List (SlotEntry P V) → Option (BcastMsg P V)
  | _, [] => none
  | slot, entry :: rest =>
    if entry.slot = slot then some entry.item else lookupSlot slot rest

/-- Drain consecutive slots `k, k + 1, …` available in `buf` for up to `fuel` steps. -/
@[expose]
def drainConsecutive {P V : Type*} : ℕ → ℕ → List (SlotEntry P V) → DrainResult P V
  | k, 0, _ => ⟨k, []⟩
  | k, fuel + 1, buf =>
    match lookupSlot k buf with
    | none => ⟨k, []⟩
    | some item =>
      let res := drainConsecutive (k + 1) fuel buf
      ⟨res.nextDeliver, item :: res.delivered⟩

/-- One-shot deterministic `0`-fault fixed-sequencer algorithm (`leader : P`) on
`TotalOrderBroadcastAlg` (toward #7297):
1. Upon receiving initial input `Sum.inl v` at `p`, `p` sends `SeqMsg.propose ⟨p, v⟩` to `leader`.
2. Upon receiving `SeqMsg.propose item` at `leader`, `leader` assigns `slot := st.nextSlot`,
   increments `nextSlot`, and sends `SeqMsg.ordered slot item` to every `q : P`.
3. Upon receiving `SeqMsg.ordered slot item` at `q`, `q` buffers `⟨slot, item⟩` and delivers all
   consecutive available slots starting at `st.nextDeliver`. -/
@[expose]
def zeroFaultTotalOrderAlg {P V : Type*} [Fintype P] [DecidableEq P] (leader : P) :
    TotalOrderBroadcastAlg P (SeqMsg P V) (SeqState P V) V where
  init _ := ⟨0, 0, []⟩
  next e st := match e.evt with
    | Sum.inl _ => st
    | Sum.inr (.propose _) =>
      if e.dest = leader then ⟨st.nextSlot + 1, st.nextDeliver, st.buf⟩ else st
    | Sum.inr (.ordered slot item) =>
      let buf' : List (SlotEntry P V) := ⟨slot, item⟩ :: st.buf
      let res := drainConsecutive st.nextDeliver (buf'.length + 1) buf'
      ⟨st.nextSlot, res.nextDeliver, buf'⟩
  send e st := match e.evt with
    | Sum.inl v => {⟨leader, .propose ⟨e.dest, v⟩⟩}
    | Sum.inr (.propose item) =>
      if e.dest = leader then
        Finset.univ.val.map (fun q => ⟨q, .ordered st.nextSlot item⟩)
      else 0
    | Sum.inr (.ordered _ _) => 0
  deliver e st := match e.evt with
    | Sum.inl _ => []
    | Sum.inr (.propose _) => []
    | Sum.inr (.ordered slot item) =>
      let buf' : List (SlotEntry P V) := ⟨slot, item⟩ :: st.buf
      (drainConsecutive st.nextDeliver (buf'.length + 1) buf').delivered

/-! ### Reorder-buffer drain lemmas -/

private theorem drainConsecutive_spec {P V : Type*} {log : List (BcastMsg P V)}
    {buf : List (SlotEntry P V)}
    (hbuf : ∀ entry ∈ buf, ∃ h : entry.slot < log.length, log[entry.slot] = entry.item) :
    ∀ k fuel, k ≤ log.length →
      let res := drainConsecutive k fuel buf
      res.nextDeliver ≤ log.length ∧
      log.take k ++ res.delivered = log.take res.nextDeliver ∧
      (lookupSlot res.nextDeliver buf = none ∨
        (res.nextDeliver = k + fuel ∧
          ∀ j, k ≤ j → j < k + fuel → (lookupSlot j buf).isSome)) := by
  have hlookup : ∀ s item, lookupSlot s buf = some item →
      ∃ h : s < log.length, log[s] = item := by
    intro s item hl
    induction buf with
    | nil => simp [lookupSlot] at hl
    | cons hd tl ih =>
      simp only [lookupSlot] at hl
      by_cases hs : hd.slot = s
      · simp only [hs, ↓reduceIte, Option.some.injEq] at hl
        subst hs hl
        exact hbuf hd List.mem_cons_self
      · simp only [hs, ↓reduceIte] at hl
        exact ih (fun e he => hbuf e (List.mem_cons_of_mem _ he)) hl
  intro k fuel hkle
  induction fuel generalizing k with
  | zero =>
    refine ⟨hkle, by simp [drainConsecutive], Or.inr ⟨by simp [drainConsecutive], ?_⟩⟩
    intro j hkj hjlt
    omega
  | succ fuel ih =>
    simp only [drainConsecutive]
    cases hl : lookupSlot k buf with
    | none =>
      exact ⟨hkle, by simp, Or.inl hl⟩
    | some item =>
      simp only
      obtain ⟨hk_lt, hlog_k⟩ := hlookup k item hl
      obtain ⟨hle', htake', hstop'⟩ := ih (k + 1) (by omega)
      refine ⟨hle', ?_, ?_⟩
      · have htake_succ : log.take (k + 1) = log.take k ++ [item] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hk_lt, Option.toList_some, hlog_k]
        calc log.take k ++ item :: (drainConsecutive (k + 1) fuel buf).delivered
            = (log.take k ++ [item]) ++ (drainConsecutive (k + 1) fuel buf).delivered := by simp
          _ = log.take (k + 1) ++ (drainConsecutive (k + 1) fuel buf).delivered := by
              rw [← htake_succ]
          _ = log.take (drainConsecutive (k + 1) fuel buf).nextDeliver := htake'
      · rcases hstop' with hnone | ⟨heq, hall⟩
        · exact Or.inl hnone
        · refine Or.inr ⟨by omega, fun j hkj hjlt => ?_⟩
          by_cases hjk : j = k
          · subst hjk; simp [hl]
          · exact hall j (by omega) (by omega)

private theorem drainConsecutive_stops_none {P V : Type*} {log : List (BcastMsg P V)}
    {buf : List (SlotEntry P V)}
    (hbuf : ∀ entry ∈ buf, ∃ h : entry.slot < log.length, log[entry.slot] = entry.item)
    {k : ℕ} (hkle : k ≤ log.length) :
    lookupSlot (drainConsecutive k (buf.length + 1) buf).nextDeliver buf = none := by
  obtain ⟨_, _, hstop⟩ := drainConsecutive_spec hbuf k (buf.length + 1) hkle
  rcases hstop with hnone | ⟨_, hall⟩
  · exact hnone
  · exfalso
    have hmem_slot : ∀ (l : List (SlotEntry P V)) (j : ℕ),
        (lookupSlot j l).isSome → j ∈ l.map SlotEntry.slot := by
      intro l j his
      induction l with
      | nil => simp [lookupSlot] at his
      | cons hd tl ih =>
        simp only [lookupSlot] at his
        by_cases hs : hd.slot = j
        · subst hs; simp
        · simp only [hs, ↓reduceIte] at his
          exact List.mem_cons_of_mem _ (ih his)
    let rng := (List.range (buf.length + 1)).map (fun i => k + i)
    have hnodup_rng : rng.Nodup :=
      List.Nodup.map (fun x y (h : k + x = k + y) => by omega) List.nodup_range
    have hsub : rng.toFinset ⊆ (buf.map SlotEntry.slot).toFinset := by
      intro j hj
      rw [List.mem_toFinset] at hj ⊢
      simp only [rng, List.mem_map, List.mem_range] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      exact hmem_slot buf (k + i) (hall (k + i) (by omega) (by omega))
    have hcard_le := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnodup_rng] at hcard_le
    have hlen_rng : rng.length = buf.length + 1 := by simp [rng]
    have hcard_buf : (buf.map SlotEntry.slot).toFinset.card ≤ buf.length := by
      simpa using List.toFinset_card_le (buf.map SlotEntry.slot)
    omega

private theorem lookupSlot_isSome_of_mem {P V : Type*} {slot : ℕ} {item : BcastMsg P V}
    {buf : List (SlotEntry P V)} (hmem : ⟨slot, item⟩ ∈ buf) :
    (lookupSlot slot buf).isSome := by
  induction buf with
  | nil => cases hmem
  | cons hd tl ih =>
    simp only [lookupSlot]
    by_cases hs : hd.slot = slot
    · simp [hs]
    · simp only [hs, ↓reduceIte]
      rcases List.mem_cons.mp hmem with rfl | htl
      · exact absurd rfl hs
      · exact ih htl

/-! ### Sequencer invariant and shadow log -/

/-- Global inductive invariant for `zeroFaultTotalOrderAlg leader` on input assignment `inp`,
relating a reachable global state `s` to the sequencer's shadow sequence log `log`. -/
private structure SeqInv {P V : Type*} [DecidableEq P] [DecidableEq V]
    (leader : P) (inp : P → V)
    (s : BcastState P (SeqMsg P V) (SeqState P V) V)
    (log : List (BcastMsg P V)) : Prop where
  /-- The sequencer's assigned log contains no duplicate broadcast messages. -/
  log_nodup : log.Nodup
  /-- Every assigned message in `log` carries the initial input of its sender. -/
  log_wf : ∀ item ∈ log, item = ⟨item.sender, inp item.sender⟩
  /-- The sequencer's `nextSlot` counter equals `log.length`. -/
  nextSlot_eq : (s.proc leader).state.nextSlot = log.length
  /-- Each process `p`'s single message resides in exactly one of: its initial input trigger, a
  pending `propose` to `leader`, or the assigned shadow `log`. -/
  msg_conservation : ∀ p : P,
    Multiset.count ⟨p, Sum.inl (inp p)⟩ s.msgs +
      Multiset.count ⟨leader, Sum.inr (.propose ⟨p, inp p⟩)⟩ s.msgs +
      (if ⟨p, inp p⟩ ∈ log then 1 else 0) = 1
  /-- Every in-flight event is an initial trigger, a `propose` addressed to `leader`, or a valid
  `ordered` assignment matching `log`. -/
  msgs_wf : ∀ e ∈ s.msgs,
    (∃ p, e = ⟨p, Sum.inl (inp p)⟩) ∨
    (∃ p, e = ⟨leader, Sum.inr (.propose ⟨p, inp p⟩)⟩) ∨
    (∃ q slot item, e = ⟨q, Sum.inr (.ordered slot item)⟩ ∧
      ∃ h : slot < log.length, log[slot] = item)
  /-- Every reorder-buffer entry at every process agrees with `log`. -/
  buf_wf : ∀ q, ∀ entry ∈ (s.proc q).state.buf,
    ∃ h : entry.slot < log.length, log[entry.slot] = entry.item
  /-- Each process's `nextDeliver` slot index does not exceed `log.length`. -/
  nextDeliver_le : ∀ q, (s.proc q).state.nextDeliver ≤ log.length
  /-- Each process's delivery log equals the drained prefix `log.take nextDeliver`. -/
  delivered_eq : ∀ q, (s.proc q).delivered = log.take (s.proc q).state.nextDeliver

/-- Advance the sequencer shadow log across one action: append `item` when `leader` processes a
`propose item` event, and leave `log` unchanged on all other events and stuttering steps. -/
private def seqStepLog {P V : Type*} [DecidableEq P] (leader : P)
    (log : List (BcastMsg P V)) : BcastAction P (SeqMsg P V) V → List (BcastMsg P V)
  | some ⟨dest, Sum.inr (.propose item)⟩ =>
    if dest = leader then log ++ [item] else log
  | _ => log

/-- Shadow sequence log accumulated after the first `k` actions of an infinite schedule `xs`. -/
private def seqRunLog {P V : Type*} [DecidableEq P] (leader : P)
    (xs : ωSequence (BcastAction P (SeqMsg P V) V)) : ℕ → List (BcastMsg P V) :=
  Nat.rec [] (fun k acc => seqStepLog leader acc (xs k))

/-- Dichotomy for `seqStepLog`: each action either leaves `log` unchanged or is a `propose`
delivered to `leader` that appends `propItem`. -/
private theorem seqStepLog_cases {P V : Type*} [DecidableEq P] (leader : P)
    (log : List (BcastMsg P V)) (act : BcastAction P (SeqMsg P V) V) :
    seqStepLog leader log act = log ∨
      ∃ propItem, act = some ⟨leader, Sum.inr (.propose propItem)⟩ ∧
        seqStepLog leader log act = log ++ [propItem] := by
  rcases act with _ | ⟨dest, _ | (propItem | _)⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · by_cases hdl : dest = leader
    · exact Or.inr ⟨propItem, hdl ▸ rfl, by simp [seqStepLog, hdl]⟩
    · exact Or.inl (by simp [seqStepLog, hdl])
  · exact Or.inl rfl

/-- The shadow sequence log grows only by appending along a schedule `xs`. -/
private theorem seqRunLog_prefix {P V : Type*} [DecidableEq P] (leader : P)
    (xs : ωSequence (BcastAction P (SeqMsg P V) V)) {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) :
    seqRunLog leader xs k₁ <+: seqRunLog leader xs k₂ := by
  obtain ⟨d, rfl⟩ : ∃ d, k₂ = k₁ + d := ⟨k₂ - k₁, by omega⟩
  induction d with
  | zero => exact List.prefix_refl _
  | succ d ih =>
    refine (ih (Nat.le_add_right k₁ d)).trans ?_
    change seqRunLog leader xs (k₁ + d) <+:
      seqStepLog leader (seqRunLog leader xs (k₁ + d)) (xs (k₁ + d))
    rcases seqStepLog_cases leader (seqRunLog leader xs (k₁ + d)) (xs (k₁ + d)) with
      heq | ⟨_, _, heq⟩ <;> rw [heq]
    exact List.prefix_append _ _

/-- Base case: `SeqInv` holds in the initial configuration `start inp` with an empty shadow log. -/
private theorem seqInv_start {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (leader : P) (inp : P → V) :
    SeqInv leader inp ((zeroFaultTotalOrderAlg (V := V) leader).start inp) [] where
  log_nodup := List.nodup_nil
  log_wf := by simp
  nextSlot_eq := rfl
  msg_conservation p := by
    have hcnt1 :
        Multiset.count ⟨p, Sum.inl (inp p)⟩
          ((zeroFaultTotalOrderAlg (V := V) leader).start inp).msgs = 1 := by
      simp only [TotalOrderBroadcastAlg.start]
      rw [Multiset.count_map_eq_count'
        (fun q : P => (⟨q, Sum.inl (inp q)⟩ : BcastEvent P (SeqMsg P V) V))
        Finset.univ.val (fun a b h => (BcastEvent.mk.inj h).1) p]
      exact Multiset.count_eq_one_of_mem Finset.univ.nodup
        (Finset.mem_def.mp (Finset.mem_univ p))
    have hcnt2 :
        Multiset.count ⟨leader, Sum.inr (.propose ⟨p, inp p⟩)⟩
          ((zeroFaultTotalOrderAlg (V := V) leader).start inp).msgs = 0 :=
      Multiset.count_eq_zero.mpr (by simp [TotalOrderBroadcastAlg.start])
    simp [hcnt1, hcnt2]
  msgs_wf e he := by
    simp only [TotalOrderBroadcastAlg.start, Multiset.mem_map] at he
    obtain ⟨p, _, rfl⟩ := he
    exact Or.inl ⟨p, rfl⟩
  buf_wf q entry hmem := by simp [TotalOrderBroadcastAlg.start, zeroFaultTotalOrderAlg] at hmem
  nextDeliver_le q := by simp [TotalOrderBroadcastAlg.start, zeroFaultTotalOrderAlg]
  delivered_eq q := by simp [TotalOrderBroadcastAlg.start, zeroFaultTotalOrderAlg]

/-! ### Per-action preservation of `SeqInv` -/

/-- Preservation of `SeqInv` when process `p₀` receives its initial input trigger `Sum.inl (inp p₀)`
and sends `propose ⟨p₀, inp p₀⟩` to `leader`. -/
private theorem seqInv_step_initInput {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {leader p₀ : P} {inp : P → V} {s : BcastState P (SeqMsg P V) (SeqState P V) V}
    {log : List (BcastMsg P V)} (hinv : SeqInv leader inp s log)
    (he_mem : ⟨p₀, Sum.inl (inp p₀)⟩ ∈ s.msgs) :
    SeqInv leader inp
      ((zeroFaultTotalOrderAlg (V := V) leader).recvEvent ⟨p₀, Sum.inl (inp p₀)⟩ s) log where
  log_nodup := hinv.log_nodup
  log_wf := hinv.log_wf
  nextSlot_eq := by
    by_cases h : leader = p₀ <;>
      simpa [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, h] using hinv.nextSlot_eq
  msg_conservation p := by
    have hc := hinv.msg_conservation p
    have hpos := Multiset.count_pos.mpr he_mem
    simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent,
      Multiset.map_singleton, Multiset.count_add, Multiset.count_singleton]
    by_cases hpp₀ : p = p₀
    · subst hpp₀
      rw [Multiset.count_erase_self, Multiset.count_erase_of_ne (by simp)]
      simp; omega
    · rw [Multiset.count_erase_of_ne (by simp [hpp₀]), Multiset.count_erase_of_ne (by simp)]
      simp [hpp₀]; omega
  msgs_wf e' he' := by
    simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent,
      Multiset.map_singleton, Multiset.mem_add, Multiset.mem_singleton] at he'
    rcases he' with he' | rfl
    · exact hinv.msgs_wf e' (Multiset.mem_of_mem_erase he')
    · exact Or.inr (Or.inl ⟨p₀, rfl⟩)
  buf_wf q entry hmem := by
    by_cases hq : q = p₀ <;>
      simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, hq,
        ↓reduceIte] at hmem <;>
      exact hinv.buf_wf _ entry hmem
  nextDeliver_le q := by
    by_cases hq : q = p₀ <;>
      simpa [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, hq]
        using hinv.nextDeliver_le q
  delivered_eq q := by
    by_cases hq : q = p₀ <;>
      simpa [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, hq]
        using hinv.delivered_eq q

/-- Preservation of `SeqInv` when `leader` receives `propose ⟨p₀, inp p₀⟩`, assigns it the next
sequence slot, broadcasts `.ordered` to every process, and appends it to the shadow log. -/
private theorem seqInv_step_propose {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {leader p₀ : P} {inp : P → V} {s : BcastState P (SeqMsg P V) (SeqState P V) V}
    {log : List (BcastMsg P V)} (hinv : SeqInv leader inp s log)
    (he_mem : ⟨leader, Sum.inr (.propose ⟨p₀, inp p₀⟩)⟩ ∈ s.msgs) :
    SeqInv leader inp
      ((zeroFaultTotalOrderAlg (V := V) leader).recvEvent
        ⟨leader, Sum.inr (.propose ⟨p₀, inp p₀⟩)⟩ s)
      (log ++ [⟨p₀, inp p₀⟩]) := by
  let newItem : BcastMsg P V := ⟨p₀, inp p₀⟩
  let log' := log ++ [newItem]
  have hnot_in_log : newItem ∉ log := by
    intro hin
    have hc := hinv.msg_conservation p₀
    have hpos : Multiset.count ⟨leader, Sum.inr (.propose newItem)⟩ s.msgs ≥ 1 :=
      Multiset.count_pos.mpr he_mem
    simp only [newItem, hin, ↓reduceIte] at hc hpos
    omega
  refine
    { log_nodup := by
        rw [List.nodup_append]
        refine ⟨hinv.log_nodup, List.nodup_singleton newItem, fun a ha b hb hab => ?_⟩
        simp only [List.mem_singleton] at hb
        rw [hab, hb] at ha
        exact hnot_in_log ha
      log_wf := fun it hit => by
        rcases List.mem_append.mp hit with hit | hit
        · exact hinv.log_wf it hit
        · simp only [List.mem_singleton] at hit; subst hit; rfl
      nextSlot_eq := by
        simp [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, hinv.nextSlot_eq]
      msg_conservation := fun p => by
        have hc := hinv.msg_conservation p
        have hpos := Multiset.count_pos.mpr he_mem
        simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, ↓reduceIte,
          Multiset.map_map, Function.comp_def, Multiset.count_add]
        rw [Multiset.count_eq_zero_of_notMem (s := Multiset.map _ _) (by simp),
          Multiset.count_eq_zero_of_notMem (s := Multiset.map _ _) (by simp)]
        by_cases hpp₀ : p = p₀
        · subst hpp₀
          rw [Multiset.count_erase_self, Multiset.count_erase_of_ne (by simp)]
          simp only [newItem, hnot_in_log, ↓reduceIte] at hc
          simp only [List.mem_append, List.mem_singleton, or_true, ↓reduceIte]
          omega
        · rw [Multiset.count_erase_of_ne (by simp),
            Multiset.count_erase_of_ne (by simp [hpp₀])]
          simpa [hpp₀] using hc
      msgs_wf := fun e' he' => by
        simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, ↓reduceIte,
          Multiset.map_map, Function.comp_def, Multiset.mem_add, Multiset.mem_map] at he'
        rcases he' with he' | ⟨q, _, rfl⟩
        · rcases hinv.msgs_wf e' (Multiset.mem_of_mem_erase he') with
            h1 | h2 | ⟨q, sl, it, rfl, hsl, hit⟩
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
          · refine Or.inr (Or.inr ⟨q, sl, it, rfl, ?_, ?_⟩)
            · simp only [List.length_append, List.length_singleton]; omega
            · simpa [List.getElem_append_left hsl] using hit
        · refine Or.inr (Or.inr ⟨q, (s.proc leader).state.nextSlot, newItem, rfl, ?_, ?_⟩)
          · simp [hinv.nextSlot_eq]
          · simp [newItem, hinv.nextSlot_eq]
      buf_wf := fun q entry hmem => by
        by_cases hq : q = leader <;>
          simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, hq,
            ↓reduceIte] at hmem <;>
          (obtain ⟨hsl, hit⟩ := hinv.buf_wf _ entry hmem;
           exact ⟨by simp only [List.length_append, List.length_singleton]; omega,
             by simpa [List.getElem_append_left hsl] using hit⟩)
      nextDeliver_le := fun q => by
        have hnd := hinv.nextDeliver_le q
        by_cases hq : q = leader <;>
          simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent,
            List.length_append, List.length_singleton, hq, ↓reduceIte] <;>
          (try subst hq) <;> omega
      delivered_eq := fun q => by
        by_cases hq : q = leader <;>
          simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, List.append_nil,
            hq, ↓reduceIte] <;>
          (try subst hq) <;>
          exact (hinv.delivered_eq _).trans
            (List.take_append_of_le_length (hinv.nextDeliver_le _)).symm }

/-- Preservation of `SeqInv` when process `q₀` receives `ordered slot item`, buffers it, and drains
consecutive available slots from `q₀.buf`. -/
private theorem seqInv_step_ordered {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {leader q₀ : P} {inp : P → V} {s : BcastState P (SeqMsg P V) (SeqState P V) V}
    {log : List (BcastMsg P V)} {slot : ℕ} {item : BcastMsg P V}
    (hinv : SeqInv leader inp s log) (hslot : slot < log.length) (hlog : log[slot] = item) :
    SeqInv leader inp
      ((zeroFaultTotalOrderAlg (V := V) leader).recvEvent
        ⟨q₀, Sum.inr (.ordered slot item)⟩ s) log := by
  let buf' : List (SlotEntry P V) := ⟨slot, item⟩ :: (s.proc q₀).state.buf
  have hbuf'_wf :
      ∀ entry ∈ buf', ∃ h : entry.slot < log.length, log[entry.slot] = entry.item := by
    intro entry hmem
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact ⟨hslot, hlog⟩
    · exact hinv.buf_wf q₀ entry htl
  obtain ⟨hres_le, hres_take, _⟩ :=
    drainConsecutive_spec hbuf'_wf (s.proc q₀).state.nextDeliver (buf'.length + 1)
      (hinv.nextDeliver_le q₀)
  refine
    { log_nodup := hinv.log_nodup
      log_wf := hinv.log_wf
      nextSlot_eq := by
        by_cases h : leader = q₀ <;>
          simpa [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, h]
            using hinv.nextSlot_eq
      msg_conservation := fun p => by
        simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent,
          Multiset.map_zero, add_zero]
        have hne1 : (⟨p, Sum.inl (inp p)⟩ : BcastEvent P (SeqMsg P V) V) ≠
            ⟨q₀, Sum.inr (.ordered slot item)⟩ := by simp
        have hne2 : (⟨leader, Sum.inr (.propose ⟨p, inp p⟩)⟩ : BcastEvent P (SeqMsg P V) V) ≠
            ⟨q₀, Sum.inr (.ordered slot item)⟩ := by simp
        rw [Multiset.count_erase_of_ne hne1, Multiset.count_erase_of_ne hne2]
        exact hinv.msg_conservation p
      msgs_wf := fun e' he' => by
        simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent,
          Multiset.map_zero, add_zero] at he'
        exact hinv.msgs_wf e' (Multiset.mem_of_mem_erase he')
      buf_wf := fun q entry hmem => by
        rcases eq_or_ne q q₀ with rfl | hqq₀
        · simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent,
            ↓reduceIte] at hmem
          exact hbuf'_wf entry hmem
        · simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, hqq₀,
            ↓reduceIte] at hmem
          exact hinv.buf_wf q entry hmem
      nextDeliver_le := fun q => by
        rcases eq_or_ne q q₀ with rfl | hqq₀
        · simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, ↓reduceIte]
          exact hres_le
        · simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, hqq₀, ↓reduceIte]
          exact hinv.nextDeliver_le q
      delivered_eq := fun q => by
        rcases eq_or_ne q q₀ with rfl | hqq₀
        · simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, ↓reduceIte]
          exact (hinv.delivered_eq q) ▸ hres_take
        · simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, hqq₀, ↓reduceIte]
          exact hinv.delivered_eq q }

/-- Single-step preservation of `SeqInv` along any transition of `zeroFaultTotalOrderAlg leader`. -/
private theorem seqInv_step {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {leader : P} {inp : P → V} {s s' : BcastState P (SeqMsg P V) (SeqState P V) V}
    {act : BcastAction P (SeqMsg P V) V} {log : List (BcastMsg P V)}
    (hinv : SeqInv leader inp s log)
    (htr : (zeroFaultTotalOrderAlg (V := V) leader).lts.Tr s act s') :
    SeqInv leader inp s' (seqStepLog leader log act) := by
  cases act with
  | none =>
    simp only [TotalOrderBroadcastAlg.lts] at htr
    subst htr
    exact hinv
  | some e =>
    rcases htr with ⟨he_mem, rfl⟩
    rcases hinv.msgs_wf e he_mem with
      ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, rfl, hslot_lt, hlog_s⟩
    · exact seqInv_step_initInput hinv he_mem
    · simpa [seqStepLog] using seqInv_step_propose hinv he_mem
    · exact seqInv_step_ordered hinv hslot_lt hlog_s

/-- `SeqInv` holds at every step `k` of an infinite execution starting at `start inp`. -/
private theorem seqInv_runLog {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {leader : P} {inp : P → V}
    {ss : ωSequence (BcastState P (SeqMsg P V) (SeqState P V) V)}
    {xs : ωSequence (BcastAction P (SeqMsg P V) V)}
    (hs0 : ss 0 = (zeroFaultTotalOrderAlg (V := V) leader).start inp)
    (he : (zeroFaultTotalOrderAlg (V := V) leader).lts.OmegaExecution ss xs) (k : ℕ) :
    SeqInv leader inp (ss k) (seqRunLog leader xs k) := by
  induction k with
  | zero => simpa [seqRunLog, ← hs0] using seqInv_start leader inp
  | succ k ih => exact seqInv_step ih (he k)

/-! ### Fairness, buffer monotonicity, and eventual slot delivery -/

/-- In any `0`-admissible run, the faulty set is empty, so every process is `BcastProcFair`. -/
private theorem bcastProcFair_of_admissibleZero {P M S V : Type*}
    [Fintype P] [DecidableEq P] [DecidableEq M] [DecidableEq V]
    {π : TotalOrderBroadcastAlg P M S V} {inp : P → V}
    {ss : ωSequence (BcastState P M S V)} {xs : ωSequence (BcastAction P M V)}
    (hadm : π.AdmissibleRun inp 0 ss xs) (r : P) :
    TotalOrderBroadcastAlg.BcastProcFair r ss xs := by
  rcases hadm with ⟨_, _, hfair_run, hnum⟩
  have hzero : {q | TotalOrderBroadcastAlg.BcastProcFaulty q ss xs} = ∅ :=
    (Set.ncard_eq_zero (s := {q | TotalOrderBroadcastAlg.BcastProcFaulty q ss xs})).mp
      (Nat.eq_zero_of_le_zero hnum)
  rcases hfair_run r with hfaulty | hfair
  · exact False.elim ((Set.eq_empty_iff_forall_notMem.mp hzero r) hfaulty)
  · exact hfair

/-- Each process's reorder buffer `buf` is monotone (append-only) along any execution of
`zeroFaultTotalOrderAlg leader`. -/
private theorem seqBuf_mono {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {leader : P} {ss : ωSequence (BcastState P (SeqMsg P V) (SeqState P V) V)}
    {xs : ωSequence (BcastAction P (SeqMsg P V) V)}
    (he : (zeroFaultTotalOrderAlg (V := V) leader).lts.OmegaExecution ss xs)
    {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) (q : P) (entry : SlotEntry P V)
    (hmem : entry ∈ ((ss k₁).proc q).state.buf) :
    entry ∈ ((ss k₂).proc q).state.buf := by
  obtain ⟨d, rfl⟩ : ∃ d, k₂ = k₁ + d := ⟨k₂ - k₁, by omega⟩
  induction d with
  | zero => exact hmem
  | succ d ih =>
    have hmem_d := ih (Nat.le_add_right k₁ d)
    have htr := he (k₁ + d)
    cases hact : xs (k₁ + d) with
    | none =>
      rw [hact] at htr
      simp only [TotalOrderBroadcastAlg.lts] at htr
      rwa [← Nat.add_assoc, htr]
    | some e =>
      rw [hact] at htr
      rcases htr with ⟨_, hstep⟩
      rw [← Nat.add_assoc, hstep]
      rcases e with ⟨dest, _ | (_ | ⟨_, _⟩)⟩
      · by_cases hqd : q = dest <;>
          simpa [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, hqd] using hmem_d
      · rcases eq_or_ne q dest with rfl | hqd
        · by_cases hdl : q = leader <;>
            simpa [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, hdl] using hmem_d
        · simpa [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, hqd] using hmem_d
      · rcases eq_or_ne q dest with rfl | hqe
        · simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, ↓reduceIte]
          exact List.mem_cons_of_mem _ hmem_d
        · simpa [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, hqe] using hmem_d

/-- Every slot `i` appearing in `seqRunLog leader xs N` had its `ordered` message enqueued to
process `q` at some earlier step `t < N`. -/
private theorem seqRunLog_ordered_sent {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {leader : P} {inp : P → V}
    {ss : ωSequence (BcastState P (SeqMsg P V) (SeqState P V) V)}
    {xs : ωSequence (BcastAction P (SeqMsg P V) V)}
    (hs0 : ss 0 = (zeroFaultTotalOrderAlg (V := V) leader).start inp)
    (he : (zeroFaultTotalOrderAlg (V := V) leader).lts.OmegaExecution ss xs)
    (q : P) (N i : ℕ) (hi : i < (seqRunLog leader xs N).length) :
    ∃ t < N, ⟨q, Sum.inr (.ordered i (seqRunLog leader xs N)[i])⟩ ∈ (ss (t + 1)).msgs := by
  induction N generalizing i with
  | zero => simp [seqRunLog] at hi
  | succ n ihn =>
    have hpref_n := seqRunLog_prefix leader xs (Nat.le_succ n)
    by_cases hin : i < (seqRunLog leader xs n).length
    · obtain ⟨t, ht_lt, hmsg⟩ := ihn i hin
      obtain ⟨_, htail⟩ := hpref_n
      have hget_eq : (seqRunLog leader xs (n + 1))[i] = (seqRunLog leader xs n)[i] := by
        simp only [← htail, List.getElem_append_left hin]
      exact ⟨t, by omega, hget_eq ▸ hmsg⟩
    · rcases seqStepLog_cases leader (seqRunLog leader xs n) (xs n) with
        heq | ⟨propItem, hact, hlog_succ⟩
      · change i < (seqStepLog leader (seqRunLog leader xs n) (xs n)).length at hi
        rw [heq] at hi; omega
      · have hlog_succ' : seqRunLog leader xs (n + 1) = seqRunLog leader xs n ++ [propItem] :=
          hlog_succ
        have hi_eq : i = (seqRunLog leader xs n).length := by
          rw [hlog_succ', List.length_append, List.length_singleton] at hi; omega
        subst hi_eq
        have hget_item : (seqRunLog leader xs (n + 1))[(seqRunLog leader xs n).length] = propItem :=
          by simp [hlog_succ']
        have htr_n := he n
        rw [hact] at htr_n
        rcases htr_n with ⟨_, hstep_n⟩
        have hns := (seqInv_runLog hs0 he n).nextSlot_eq
        refine ⟨n, Nat.lt_succ_self n, ?_⟩
        rw [hget_item, hstep_n]
        simp only [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent,
          ↓reduceIte, hns, Multiset.mem_add, Multiset.mem_map]
        exact Or.inr ⟨⟨q, .ordered (seqRunLog leader xs n).length propItem⟩,
          ⟨q, Finset.mem_def.mp (Finset.mem_univ q), rfl⟩, rfl⟩

/-- Core liveness helper: in any `0`-admissible run, every message assigned a slot
`m < (seqRunLog leader xs K).length` is eventually delivered at every process `q`. -/
private theorem zeroFaultTotalOrderAlg_eventually_delivers_slot
    {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {leader : P} {inp : P → V}
    {ss : ωSequence (BcastState P (SeqMsg P V) (SeqState P V) V)}
    {xs : ωSequence (BcastAction P (SeqMsg P V) V)}
    (hadm : (zeroFaultTotalOrderAlg (V := V) leader).AdmissibleRun inp 0 ss xs)
    (K m : ℕ) (hm : m < (seqRunLog leader xs K).length) (q : P) :
    ∃ k', (seqRunLog leader xs K)[m] ∈ ((ss k').proc q).delivered := by
  have hfair_q := bcastProcFair_of_admissibleZero hadm q
  rcases hadm with ⟨hs0, he, _, _⟩
  have hex_recv : ∀ i : Fin (m + 1),
      ∃ j, xs j =
          some ⟨q, Sum.inr (.ordered i.val ((seqRunLog leader xs K)[i.val]'(by omega)))⟩ := by
    intro i
    obtain ⟨t, _, hmsg⟩ := seqRunLog_ordered_sent hs0 he q K i.val (by omega)
    obtain ⟨j, _, hxj⟩ := hfair_q _ rfl (t + 1) hmsg
    exact ⟨j, hxj⟩
  choose jFn hjFn using hex_recv
  obtain ⟨iMax, _, hiMax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin (m + 1))) jFn Finset.univ_nonempty
  let jStar := jFn iMax
  have htr_star := he jStar
  rw [hjFn iMax] at htr_star
  rcases htr_star with ⟨_, hstep_star⟩
  have hinv_star := seqInv_runLog hs0 he jStar
  have hinv_next := seqInv_runLog hs0 he (jStar + 1)
  let itemMax := (seqRunLog leader xs K)[iMax.val]'(by omega)
  let bufStar : List (SlotEntry P V) := ⟨iMax.val, itemMax⟩ :: ((ss jStar).proc q).state.buf
  have hall_in_bufStar : ∀ i : Fin (m + 1), (lookupSlot i.val bufStar).isSome := by
    intro i
    have hij_le : jFn i ≤ jStar := hiMax i (Finset.mem_univ i)
    by_cases hlt : jFn i < jStar
    · have htr_i := he (jFn i)
      rw [hjFn i] at htr_i
      rcases htr_i with ⟨_, hstep_i⟩
      have hin_next : ⟨i.val, (seqRunLog leader xs K)[i.val]'(by omega)⟩ ∈
          ((ss (jFn i + 1)).proc q).state.buf := by
        rw [hstep_i]
        simp [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent]
      have hin_jStar := seqBuf_mono he (Nat.succ_le_of_lt hlt) q _ hin_next
      exact lookupSlot_isSome_of_mem (List.mem_cons_of_mem _ hin_jStar)
    · have hxs_eq : xs (jFn i) = xs jStar := congrArg xs (by omega : jFn i = jStar)
      rw [hjFn i, hjFn iMax] at hxs_eq
      simp only [Option.some.injEq, BcastEvent.mk.injEq, Sum.inr.injEq,
        SeqMsg.ordered.injEq] at hxs_eq
      have hi_eq : i = iMax := Fin.ext hxs_eq.2.1
      subst hi_eq
      exact lookupSlot_isSome_of_mem List.mem_cons_self
  have hbufStar_eq : ((ss (jStar + 1)).proc q).state.buf = bufStar := by
    rw [hstep_star]
    simp [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, bufStar, itemMax]
  have hstepLog_star : seqRunLog leader xs (jStar + 1) = seqRunLog leader xs jStar := by
    change seqStepLog leader (seqRunLog leader xs jStar) (xs jStar) = seqRunLog leader xs jStar
    rw [hjFn iMax]
    rfl
  have hbufStar_wf : ∀ entry ∈ bufStar,
      ∃ h : entry.slot < (seqRunLog leader xs jStar).length,
        (seqRunLog leader xs jStar)[entry.slot] = entry.item := by
    rw [← hstepLog_star, ← hbufStar_eq]
    exact hinv_next.buf_wf q
  have hnone_res := drainConsecutive_stops_none hbufStar_wf (hinv_star.nextDeliver_le q)
  let resNext := (drainConsecutive ((ss jStar).proc q).state.nextDeliver
    (bufStar.length + 1) bufStar).nextDeliver
  have hm_lt_res : m < resNext := by
    by_contra hge
    have hisSome := hall_in_bufStar ⟨resNext, by omega⟩
    change (lookupSlot resNext bufStar).isSome = true at hisSome
    rw [hnone_res] at hisSome
    cases hisSome
  have hnd_star1 : ((ss (jStar + 1)).proc q).state.nextDeliver = resNext := by
    rw [hstep_star]
    simp [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent, bufStar, itemMax, resNext]
  have hres_le_len : resNext ≤ (seqRunLog leader xs (jStar + 1)).length :=
    hnd_star1 ▸ hinv_next.nextDeliver_le q
  have hprefK := seqRunLog_prefix leader xs (Nat.le_max_left K (jStar + 1))
  have hprefJ := seqRunLog_prefix leader xs (Nat.le_max_right K (jStar + 1))
  have hm_lt_j : m < (seqRunLog leader xs (jStar + 1)).length := by omega
  have hget_eq : (seqRunLog leader xs K)[m] = (seqRunLog leader xs (jStar + 1))[m] :=
    (hprefK.getElem hm).trans (hprefJ.getElem hm_lt_j).symm
  refine ⟨jStar + 1, ?_⟩
  rw [hinv_next.delivered_eq q, hnd_star1, hget_eq]
  have htake_get :
      ((seqRunLog leader xs (jStar + 1)).take resNext)[m]'(by simp; omega) =
        (seqRunLog leader xs (jStar + 1))[m] :=
    List.getElem_take
  rw [← htake_get]
  exact List.getElem_mem _

/-! ### Broadcast specification properties for `zeroFaultTotalOrderAlg` -/

/-- One-shot `Validity` (`0` faults) for `zeroFaultTotalOrderAlg leader`. -/
private theorem zeroFaultTotalOrderAlg_validity
    {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V] (leader : P) :
    (zeroFaultTotalOrderAlg (V := V) leader).Validity 0 := by
  intro inp ss xs hadm p _
  have hfair_p := bcastProcFair_of_admissibleZero hadm p
  have hfair_l := bcastProcFair_of_admissibleZero hadm leader
  have hs0 := hadm.1
  have he := hadm.2.1
  have hin0 : (⟨p, Sum.inl (inp p)⟩ : BcastEvent P (SeqMsg P V) V) ∈ (ss 0).msgs := by
    rw [hs0]
    simp only [TotalOrderBroadcastAlg.start, Multiset.mem_map]
    exact ⟨p, Finset.mem_def.mp (Finset.mem_univ p), rfl⟩
  obtain ⟨j₁, _, hxj₁⟩ := hfair_p _ rfl 0 hin0
  have hprop_in :
      (⟨leader, Sum.inr (.propose ⟨p, inp p⟩)⟩ : BcastEvent P (SeqMsg P V) V) ∈
        (ss (j₁ + 1)).msgs := by
    have htr₁ := he j₁
    rw [hxj₁] at htr₁
    rcases htr₁ with ⟨_, hstep₁⟩
    rw [hstep₁]
    simp [zeroFaultTotalOrderAlg, TotalOrderBroadcastAlg.recvEvent]
  obtain ⟨j₂, _, hxj₂⟩ := hfair_l _ rfl (j₁ + 1) hprop_in
  have hlog_j₂ : seqRunLog leader xs (j₂ + 1) = seqRunLog leader xs j₂ ++ [⟨p, inp p⟩] := by
    change seqStepLog leader (seqRunLog leader xs j₂) (xs j₂) =
      seqRunLog leader xs j₂ ++ [⟨p, inp p⟩]
    rw [hxj₂]
    simp [seqStepLog]
  have hm_lt : (seqRunLog leader xs j₂).length < (seqRunLog leader xs (j₂ + 1)).length := by
    simp [hlog_j₂]
  have hget_m : (seqRunLog leader xs (j₂ + 1))[(seqRunLog leader xs j₂).length] = ⟨p, inp p⟩ := by
    simp [hlog_j₂]
  obtain ⟨k', hk'⟩ := zeroFaultTotalOrderAlg_eventually_delivers_slot hadm
    (j₂ + 1) (seqRunLog leader xs j₂).length hm_lt p
  exact ⟨k', hget_m ▸ hk'⟩

/-- One-shot `Integrity` (`0` faults) for `zeroFaultTotalOrderAlg leader`. -/
private theorem zeroFaultTotalOrderAlg_integrity
    {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V] (leader : P) :
    (zeroFaultTotalOrderAlg (V := V) leader).Integrity 0 := by
  rintro inp ss xs ⟨hs0, he, _, _⟩ p _ k
  have hinv_k := seqInv_runLog hs0 he k
  rw [hinv_k.delivered_eq p]
  exact ⟨hinv_k.log_nodup.take, fun m hm => hinv_k.log_wf m (List.mem_of_mem_take hm)⟩

/-- One-shot `Agreement` (`0` faults) for `zeroFaultTotalOrderAlg leader`. -/
private theorem zeroFaultTotalOrderAlg_agreement
    {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V] (leader : P) :
    (zeroFaultTotalOrderAlg (V := V) leader).Agreement 0 := by
  intro inp ss xs hadm p q _ _ m k hm
  rw [(seqInv_runLog hadm.1 hadm.2.1 k).delivered_eq p] at hm
  obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_take hm)
  exact zeroFaultTotalOrderAlg_eventually_delivers_slot hadm k idx hidx q

/-- Non-uniform `TotalOrder` (`0` faults) for `zeroFaultTotalOrderAlg leader`. -/
private theorem zeroFaultTotalOrderAlg_totalOrder
    {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V] (leader : P) :
    (zeroFaultTotalOrderAlg (V := V) leader).TotalOrder 0 := by
  rintro inp ss xs ⟨hs0, he, _, _⟩ p q _ _ m₁ m₂ k₁ k₂ hm₁p hm₂p hm₁q hm₂q
  have hpref_p : ((ss k₁).proc p).delivered <+: seqRunLog leader xs (max k₁ k₂) := by
    rw [(seqInv_runLog hs0 he k₁).delivered_eq p]
    exact (List.take_prefix _ _).trans (seqRunLog_prefix leader xs (Nat.le_max_left k₁ k₂))
  have hpref_q : ((ss k₂).proc q).delivered <+: seqRunLog leader xs (max k₁ k₂) := by
    rw [(seqInv_runLog hs0 he k₂).delivered_eq q]
    exact (List.take_prefix _ _).trans (seqRunLog_prefix leader xs (Nat.le_max_right k₁ k₂))
  rw [hpref_p.idxOf_eq_of_mem hm₁p, hpref_p.idxOf_eq_of_mem hm₂p,
    hpref_q.idxOf_eq_of_mem hm₁q, hpref_q.idxOf_eq_of_mem hm₂q]

/-- One-shot `0`-fault solvability step (toward #7297): `zeroFaultTotalOrderAlg leader` satisfies
`SolvesTotalOrderBroadcast 0` on any finite process set `P`. -/
theorem zeroFaultTotalOrderAlg_solves {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (leader : P) :
    (zeroFaultTotalOrderAlg (V := V) leader).SolvesTotalOrderBroadcast 0 :=
  ⟨⟨zeroFaultTotalOrderAlg_validity leader,
    zeroFaultTotalOrderAlg_integrity leader,
    zeroFaultTotalOrderAlg_agreement leader⟩,
   zeroFaultTotalOrderAlg_totalOrder leader⟩

/-- Exact `t = 0` crash-fault solvability characterization step for one-shot
`TotalOrderBroadcastAlg` (toward #7297): on any finite process set `P` with `2 ≤ Fintype.card P` and
any nontrivial payload type `V`, a deterministic asynchronous `t`-resilient one-shot
`TotalOrderBroadcastAlg` exists if and only if `t = 0`. -/
theorem exists_oneShotTotalOrderBroadcast_iff_eq_zero {P : Type u} {V : Type v}
    [Fintype P] [DecidableEq P] [DecidableEq V] [Nontrivial V]
    (hc : 2 ≤ Fintype.card P) (t : ℕ) :
    (∃ (M S : Type (max u v)) (_ : DecidableEq M) (π : TotalOrderBroadcastAlg P M S V),
      π.SolvesTotalOrderBroadcast t) ↔ t = 0 := by
  constructor
  · rintro ⟨M, S, hdecM, π, hπ⟩
    by_contra ht0
    exact not_exists_oneShotTotalOrderBroadcast_ge_one (M := M) (S := S) hc
      (Nat.pos_of_ne_zero ht0) ⟨π, hπ⟩
  · rintro rfl
    have hne : Nonempty P := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨leader⟩ := hne
    exact ⟨SeqMsg P V, SeqState P V, inferInstance, zeroFaultTotalOrderAlg leader,
      zeroFaultTotalOrderAlg_solves leader⟩

end ZeroFaultSequencer

/-! ### Part 4: Reduction 2 — Sequential Consensus Slots → Total-Order Broadcast -/

section ConsensusToTotalOrder

/-- Insert `x` into a strictly sorted list `ys` (with respect to `<`), omitting duplicates. -/
@[expose]
def insertSorted {Msg : Type*} [LinearOrder Msg] (x : Msg) : List Msg → List Msg
  | [] => [x]
  | y :: ys =>
    if x < y then x :: y :: ys
    else if x = y then y :: ys
    else y :: insertSorted x ys

/-- Given the list `alreadyDelivered` of previously A-delivered messages and a raw Consensus-decided
batch `rawBatch`, filter out already-delivered messages, deduplicate, and sort into canonical
strictly increasing `[LinearOrder Msg]` order ([ChandraToueg1996], §7.1, Figure 7, Task 3, p. 249;
[HadzilacosToueg1994], §7.2.2, Figure 14, p. 60). -/
@[expose]
def canonicalBatch {Msg : Type*} [LinearOrder Msg]
    (alreadyDelivered : List Msg) : List Msg → List Msg
  | [] => []
  | m :: ms =>
    let rest := canonicalBatch alreadyDelivered ms
    if m ∈ alreadyDelivered then rest else insertSorted m rest

/-- Fold a finite list of Consensus-decided batches into the resulting chronological A-delivery log,
appending `canonicalBatch acc batch` at each sequential slot. -/
@[expose]
def runConsensusSlots {Msg : Type*} [LinearOrder Msg] (batches : List (List Msg)) : List Msg :=
  batches.foldl (fun acc batch => acc ++ canonicalBatch acc batch) []

private theorem mem_insertSorted {Msg : Type*} [LinearOrder Msg] (x z : Msg) (l : List Msg) :
    z ∈ insertSorted x l ↔ z = x ∨ z ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    simp only [insertSorted]
    split_ifs with hlt heq
    · simp
    · subst heq
      simp only [List.mem_cons]
      tauto
    · simp only [List.mem_cons, ih]
      tauto

private theorem insertSorted_pairwise_lt {Msg : Type*} [LinearOrder Msg] (x : Msg)
    {l : List Msg} (hl : l.Pairwise (· < ·)) :
    (insertSorted x l).Pairwise (· < ·) := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨hy_lt, hys⟩ := hl
    simp only [insertSorted]
    split_ifs with hlt heq
    · rw [List.pairwise_cons]
      refine ⟨fun z hz => ?_, List.pairwise_cons.mpr ⟨hy_lt, hys⟩⟩
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact hlt
      · exact lt_trans hlt (hy_lt z hz')
    · exact List.pairwise_cons.mpr ⟨hy_lt, hys⟩
    · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      rw [List.pairwise_cons]
      refine ⟨fun z hz => ?_, ih hys⟩
      rcases (mem_insertSorted x z ys).mp hz with rfl | hz'
      · exact hyx
      · exact hy_lt z hz'

private theorem mem_canonicalBatch {Msg : Type*} [LinearOrder Msg]
    (deliv raw : List Msg) (m : Msg) :
    m ∈ canonicalBatch deliv raw ↔ m ∈ raw ∧ m ∉ deliv := by
  induction raw with
  | nil => simp [canonicalBatch]
  | cons hd tl ih =>
    simp only [canonicalBatch]
    split_ifs with hmem
    · simp only [ih, List.mem_cons]
      exact ⟨fun ⟨h1, h2⟩ => ⟨Or.inr h1, h2⟩,
        fun ⟨h1, h2⟩ => ⟨h1.resolve_left (fun heq => h2 (heq ▸ hmem)), h2⟩⟩
    · rw [mem_insertSorted, ih]
      simp only [List.mem_cons]
      exact ⟨fun h =>
          h.elim (fun heq => ⟨Or.inl heq, heq ▸ hmem⟩) (fun ⟨h1, h2⟩ => ⟨Or.inr h1, h2⟩),
        fun ⟨h1, h2⟩ => h1.elim Or.inl (fun htl => Or.inr ⟨htl, h2⟩)⟩

private theorem canonicalBatch_pairwise_lt {Msg : Type*} [LinearOrder Msg]
    (deliv raw : List Msg) :
    (canonicalBatch deliv raw).Pairwise (· < ·) := by
  induction raw with
  | nil => simp [canonicalBatch]
  | cons hd tl ih =>
    simp only [canonicalBatch]
    split_ifs
    · exact ih
    · exact insertSorted_pairwise_lt hd ih

/-- Extensionality of `canonicalBatch` on undelivered elements: two raw Consensus-decided batches
with the same undelivered elements produce the identical canonical sequence
`canonicalBatch deliv raw₁ = canonicalBatch deliv raw₂`, regardless of duplicates or internal list
ordering. -/
theorem canonicalBatch_ext {Msg : Type*} [LinearOrder Msg] {deliv raw₁ raw₂ : List Msg}
    (hext : ∀ m, (m ∈ raw₁ ∧ m ∉ deliv) ↔ (m ∈ raw₂ ∧ m ∉ deliv)) :
    canonicalBatch deliv raw₁ = canonicalBatch deliv raw₂ := by
  have h₁ := canonicalBatch_pairwise_lt deliv raw₁
  have h₂ := canonicalBatch_pairwise_lt deliv raw₂
  have hperm : (canonicalBatch deliv raw₁).Perm (canonicalBatch deliv raw₂) :=
    (List.perm_ext_iff_of_nodup (h₁.imp ne_of_lt) (h₂.imp ne_of_lt)).mpr fun m => by
      rw [mem_canonicalBatch, mem_canonicalBatch]
      exact hext m
  exact hperm.eq_of_pairwise (fun _ _ _ _ hab hba => absurd (lt_trans hab hba) (lt_irrefl _)) h₁ h₂

private theorem runConsensusSlots_append {Msg : Type*} [LinearOrder Msg]
    (b₁ b₂ : List (List Msg)) :
    runConsensusSlots (b₁ ++ b₂) =
      b₂.foldl (fun acc batch => acc ++ canonicalBatch acc batch) (runConsensusSlots b₁) :=
  List.foldl_append

/-- `runConsensusSlots batches` never delivers duplicate messages (`Nodup`). -/
theorem runConsensusSlots_nodup {Msg : Type*} [LinearOrder Msg] (batches : List (List Msg)) :
    (runConsensusSlots batches).Nodup := by
  induction batches using List.reverseRecOn with
  | nil => simp [runConsensusSlots]
  | append_singleton bs batch ih =>
    rw [runConsensusSlots_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [List.nodup_append]
    refine ⟨ih, (canonicalBatch_pairwise_lt _ batch).imp ne_of_lt, fun x hx y hy hxy => ?_⟩
    rw [← hxy] at hy
    exact ((mem_canonicalBatch _ batch x).mp hy).2 hx

private theorem mem_runConsensusSlots {Msg : Type*} [LinearOrder Msg]
    (batches : List (List Msg)) (m : Msg) :
    m ∈ runConsensusSlots batches ↔ ∃ batch ∈ batches, m ∈ batch := by
  induction batches using List.reverseRecOn with
  | nil => simp [runConsensusSlots]
  | append_singleton bs batch ih =>
    rw [runConsensusSlots_append]
    simp only [List.foldl_cons, List.foldl_nil, List.mem_append, mem_canonicalBatch,
      List.mem_singleton]
    constructor
    · rintro (hin_bs | ⟨hm, _⟩)
      · obtain ⟨b, hb, hm⟩ := ih.mp hin_bs
        exact ⟨b, Or.inl hb, hm⟩
      · exact ⟨batch, Or.inr rfl, hm⟩
    · rintro ⟨b, hb | rfl, hm⟩
      · exact Or.inl (ih.mpr ⟨b, hb, hm⟩)
      · by_cases hin : m ∈ runConsensusSlots bs
        · exact Or.inl hin
        · exact Or.inr ⟨hm, hin⟩

private theorem runConsensusSlots_prefix_of_prefix {Msg : Type*} [LinearOrder Msg]
    {b₁ b₂ : List (List Msg)} (hpref : b₁ <+: b₂) :
    runConsensusSlots b₁ <+: runConsensusSlots b₂ := by
  obtain ⟨tail, rfl⟩ := hpref
  rw [runConsensusSlots_append]
  generalize runConsensusSlots b₁ = acc
  induction tail generalizing acc with
  | nil => exact List.prefix_refl acc
  | cons batch rest ih =>
    simp only [List.foldl_cons]
    exact (List.prefix_append acc _).trans (ih _)

/-- Abstract discrete-time (`t : ℕ`) slot-execution specification step toward #7297 (after
[ChandraToueg1996], §7.1, Figure 7, pp. 249–252; [HadzilacosToueg1994], §7.2.2, Figure 14,
pp. 60–63) over finite process set `P`, static crash-fault set `F : Set P`, and message type `Msg`
equipped with `[LinearOrder Msg]`, axiomatizing the execution traces of an underlying Reliable
Broadcast and sequential per-slot Consensus instances (`k = 0, 1, …`).

Each process `p` maintains:
* `rDelivered p t : Finset Msg` — messages R-delivered by the underlying Reliable Broadcast up to
  time `t`;
* `decidedBatches p t : List (List Msg)` — raw Consensus batches sequentially decided by `p` in
  slots `0, 1, …, (decidedBatches p t).length - 1` up to time `t`, from which `p`'s chronological
  A-delivery log is computed by `aDelivered p t := runConsensusSlots (decidedBatches p t)`. -/
structure ConsensusSlotExec (P Msg : Type*) [LinearOrder Msg] (F : Set P) where
  /-- All messages submitted to Atomic Broadcast during the execution. -/
  bcast : Set Msg
  /-- Subset of `bcast` initiated by non-faulty (`∉ F`) broadcasters. -/
  correctBcast : Set Msg
  /-- Every message in `correctBcast` was submitted to `bcast`. -/
  correctBcast_sub : correctBcast ⊆ bcast
  /-- Local set `R_delivered_p` of Reliable-Broadcast-delivered messages at `p` at time `t`. -/
  rDelivered : P → ℕ → Finset Msg
  /-- Sequential Consensus batches `msgSet^0, …, msgSet^{k-1}` decided at `p` by time `t`. -/
  decidedBatches : P → ℕ → List (List Msg)
  /-- `Proposed p k t batch` holds when `p` executes `propose(k, batch)` at time `t`. -/
  Proposed : P → ℕ → ℕ → List Msg → Prop
  /-- `R_delivered_p` grows monotonically with time. -/
  rDelivered_mono : ∀ p {t₁ t₂}, t₁ ≤ t₂ → rDelivered p t₁ ⊆ rDelivered p t₂
  /-- Reliable Broadcast **Uniform Integrity**: every R-delivered message was broadcast. -/
  rb_integrity : ∀ p t m, m ∈ rDelivered p t → m ∈ bcast
  /-- Reliable Broadcast **Validity**: every message broadcast by a correct process is eventually
  R-delivered by every correct process `q ∉ F`. -/
  rb_validity : ∀ m ∈ correctBcast, ∀ q ∉ F, ∃ t, m ∈ rDelivered q t
  /-- Reliable Broadcast **Agreement**: every message R-delivered by a correct process `p ∉ F` is
  eventually R-delivered by every correct process `q ∉ F`. -/
  rb_agreement : ∀ p ∉ F, ∀ q ∉ F, ∀ m t, m ∈ rDelivered p t → ∃ t', m ∈ rDelivered q t'
  /-- Sequential slot decisions at each process only extend by appending new slots. -/
  decidedBatches_prefix : ∀ p {t₁ t₂}, t₁ ≤ t₂ → decidedBatches p t₁ <+: decidedBatches p t₂
  /-- Task 3 proposal rule ([ChandraToueg1996], Figure 7, p. 249): when `p` proposes `batch` in
  slot `k` at time `t`, `p` has completed slots `< k`, `batch` is nonempty, and `batch` consists of
  `R_delivered_p \ A_delivered_p`. -/
  propose_spec : ∀ p k t batch, Proposed p k t batch →
    (decidedBatches p t).length = k ∧ batch ≠ [] ∧
      ∀ m, m ∈ batch ↔ m ∈ rDelivered p t ∧ m ∉ runConsensusSlots (decidedBatches p t)
  /-- A process enters `decide(k, -)` only after executing `propose(k, -)` in Task 3. -/
  decide_requires_propose : ∀ p t k, k < (decidedBatches p t).length →
    ∃ t₀ ≤ t, ∃ batch, Proposed p k t₀ batch
  /-- Task 3 fairness at correct processes `p ∉ F`: whenever `p` is at slot `k` with an undelivered
  R-delivered message, `p` eventually executes `propose(k, -)`. -/
  task3_fair : ∀ p ∉ F, ∀ t k,
    (decidedBatches p t).length = k →
    (∃ m ∈ rDelivered p t, m ∉ runConsensusSlots (decidedBatches p t)) →
    ∃ t' batch, Proposed p k t' batch
  /-- Crash-stop bound on faulty proposers ([ChandraToueg1996], Lemma 7.1.4, p. 251): each faulty
  process `r ∈ F` crashes after finitely many steps and therefore proposes in only finitely many
  Consensus slots. -/
  faulty_eventually_halted : ∀ r ∈ F, ∃ K_r, ∀ k, K_r ≤ k → ∀ t batch, ¬ Proposed r k t batch
  /-- Consensus **Uniform Agreement** per slot `k`: any two processes that decide slot `k` decide
  extensionally equal message sets `msgSet^k`. -/
  cons_agreement : ∀ p q t₁ t₂ k (hk₁ : k < (decidedBatches p t₁).length)
    (hk₂ : k < (decidedBatches q t₂).length) m,
    m ∈ (decidedBatches p t₁)[k] ↔ m ∈ (decidedBatches q t₂)[k]
  /-- Consensus **Uniform Validity** per slot `k`: any decided batch in slot `k` was proposed by
  some process `r` in slot `k`. -/
  cons_validity : ∀ p t k (hk : k < (decidedBatches p t).length),
    ∃ r t_r batch, Proposed r k t_r batch ∧ ∀ m, m ∈ (decidedBatches p t)[k] ↔ m ∈ batch
  /-- Consensus **Termination** per slot `k`: if all correct processes `q ∉ F` propose in slot `k`,
  then all correct processes eventually decide slot `k`. -/
  cons_termination : ∀ k, (∀ q ∉ F, ∃ t batch, Proposed q k t batch) →
    ∀ q ∉ F, ∃ t, k < (decidedBatches q t).length

namespace ConsensusSlotExec

variable {P Msg : Type*} [LinearOrder Msg] {F : Set P}

/-- Chronological A-delivery log of process `p` at time `t` in `E`, obtained by running
`runConsensusSlots` on `E.decidedBatches p t`. -/
@[expose]
def aDelivered (E : ConsensusSlotExec P Msg F) (p : P) (t : ℕ) : List Msg :=
  runConsensusSlots (E.decidedBatches p t)

private theorem runConsensusSlots_eq_of_equiv {b₁ b₂ : List (List Msg)}
    (hlen : b₁.length = b₂.length)
    (hequiv : ∀ (k : ℕ) (hk₁ : k < b₁.length) (hk₂ : k < b₂.length),
      ∀ m, m ∈ b₁[k] ↔ m ∈ b₂[k]) :
    runConsensusSlots b₁ = runConsensusSlots b₂ := by
  suffices htake : ∀ n ≤ b₁.length,
      runConsensusSlots (b₁.take n) = runConsensusSlots (b₂.take n) by
    simpa [List.take_of_length_le (le_refl _), List.take_of_length_le (hlen.symm.le)]
      using htake b₁.length (le_refl _)
  intro n hn
  induction n with
  | zero => simp [runConsensusSlots]
  | succ n ih =>
    have hn_lt₁ : n < b₁.length := hn
    have hn_lt₂ : n < b₂.length := hlen ▸ hn
    have htake₁ : b₁.take (n + 1) = b₁.take n ++ [b₁[n]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hn_lt₁, Option.toList_some]
    have htake₂ : b₂.take (n + 1) = b₂.take n ++ [b₂[n]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hn_lt₂, Option.toList_some]
    rw [htake₁, htake₂, runConsensusSlots_append, runConsensusSlots_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have hprev := ih (Nat.le_of_lt hn)
    rw [hprev]
    congr 1
    exact canonicalBatch_ext (fun m => and_congr_left (fun _ => hequiv n hn_lt₁ hn_lt₂ m))

private theorem aDelivered_prefix_of_length_le (E : ConsensusSlotExec P Msg F)
    {p q : P} {t₁ t₂ : ℕ}
    (hle : (E.decidedBatches p t₁).length ≤ (E.decidedBatches q t₂).length) :
    E.aDelivered p t₁ <+: E.aDelivered q t₂ := by
  let n := (E.decidedBatches p t₁).length
  have heq : E.aDelivered p t₁ = runConsensusSlots ((E.decidedBatches q t₂).take n) := by
    apply runConsensusSlots_eq_of_equiv
    · simp [n, Nat.min_eq_left hle]
    · intro k hk₁ hk₂ m
      rw [List.getElem_take]
      exact E.cons_agreement p q t₁ t₂ k hk₁ (Nat.lt_of_lt_of_le hk₁ hle) m
  rw [heq]
  exact runConsensusSlots_prefix_of_prefix (List.take_prefix n (E.decidedBatches q t₂))

/-- **Lemma 7.1.2 of [ChandraToueg1996]** (pp. 250–251; Lemma 3 of [HadzilacosToueg1994],
pp. 61–62): if any correct process `p ∉ F` proposes in slot `k`, then every correct process `q ∉ F`
eventually proposes in slot `k` and eventually decides slot `k`. -/
private theorem ct_lemma_7_1_2 (E : ConsensusSlotExec P Msg F) :
    ∀ k, (∃ p ∉ F, ∃ t_p batch_p, E.Proposed p k t_p batch_p) →
      (∀ q ∉ F, ∃ t_q batch_q, E.Proposed q k t_q batch_q) ∧
      (∀ q ∉ F, ∃ t_d, k < (E.decidedBatches q t_d).length) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rintro ⟨p, hp, t_p, batch_p, hprop_p⟩
    have hall_prop : ∀ q ∉ F, ∃ t_q batch_q, E.Proposed q k t_q batch_q := by
      intro q hq
      obtain ⟨hlen_p, hne_p, hmem_p⟩ := E.propose_spec p k t_p batch_p hprop_p
      -- First, `q` reaches a time `t₁` with `k ≤ (E.decidedBatches q t₁).length`.
      have hex_t₁ : ∃ t₁, k ≤ (E.decidedBatches q t₁).length := by
        cases k with
        | zero => exact ⟨0, Nat.zero_le _⟩
        | succ k' =>
          have hk'_lt : k' < (E.decidedBatches p t_p).length := by omega
          obtain ⟨t₀, _, b₀, hp₀⟩ := E.decide_requires_propose p t_p k' hk'_lt
          obtain ⟨_, hdec_k'⟩ := ih k' (Nat.lt_succ_self k') ⟨p, hp, t₀, b₀, hp₀⟩
          obtain ⟨t₁, ht₁⟩ := hdec_k' q hq
          exact ⟨t₁, Nat.succ_le_of_lt ht₁⟩
      obtain ⟨t₁, ht₁⟩ := hex_t₁
      -- Pick a message `m₀ ∈ batch_p`; by RB-Agreement, `q` eventually R-delivers `m₀` at `t₂`.
      obtain ⟨m₀, hm₀_in⟩ := List.exists_mem_of_ne_nil batch_p hne_p
      obtain ⟨hm₀_r, hm₀_not_a⟩ := (hmem_p m₀).mp hm₀_in
      obtain ⟨t₂, hm₀_rq⟩ := E.rb_agreement p hp q hq m₀ t_p hm₀_r
      let T := max t₁ t₂
      have hlen_T : k ≤ (E.decidedBatches q T).length :=
        le_trans ht₁ (E.decidedBatches_prefix q (Nat.le_max_left t₁ t₂)).length_le
      by_cases hgt : k < (E.decidedBatches q T).length
      · obtain ⟨t₀, _, b₀, hp₀⟩ := E.decide_requires_propose q T k hgt
        exact ⟨t₀, b₀, hp₀⟩
      · have heq_k : (E.decidedBatches q T).length = k := by omega
        have ha_eq : runConsensusSlots (E.decidedBatches q T) =
            runConsensusSlots (E.decidedBatches p t_p) := by
          have h1 := E.aDelivered_prefix_of_length_le (p := q) (q := p) (t₁ := T) (t₂ := t_p)
            (by omega)
          have h2 := E.aDelivered_prefix_of_length_le (p := p) (q := q) (t₁ := t_p) (t₂ := T)
            (by omega)
          exact List.IsPrefix.eq_of_length h1 (le_antisymm h1.length_le h2.length_le)
        have hm₀_rT : m₀ ∈ E.rDelivered q T :=
          E.rDelivered_mono q (Nat.le_max_right t₁ t₂) hm₀_rq
        have hm₀_undeliv : m₀ ∉ runConsensusSlots (E.decidedBatches q T) :=
          ha_eq.symm ▸ hm₀_not_a
        exact E.task3_fair q hq T k heq_k ⟨m₀, hm₀_rT, hm₀_undeliv⟩
    exact ⟨hall_prop, E.cons_termination k hall_prop⟩

end ConsensusSlotExec

/-- Abstract discrete-time (`t : ℕ`) slot-trace reduction step from Reliable Broadcast and
sequential Consensus slot specifications (`ConsensusSlotExec`) to Total-Order Broadcast properties
(toward #7297, after [ChandraToueg1996], §7.1, Figure 7 & Theorem 7.1.6, pp. 249–252 and
[HadzilacosToueg1994], §7.2.2, Figure 14 & Theorem 14, pp. 60–63):

For any finite process set `P`, any crash-fault set `F : Set P`, and any `[LinearOrder Msg]`, every
abstract slot execution `E : ConsensusSlotExec P Msg F` satisfies:
1. **Uniform No Duplicates:** `(E.aDelivered p t).Nodup` for all `p : P` (faulty or correct);
2. **Uniform Integrity:** `m ∈ E.aDelivered p t → m ∈ E.bcast` for all `p : P`;
3. **Uniform Total Order:** for all `p, q : P` (faulty or correct) and `t₁, t₂ : ℕ`, if `m₁, m₂`
   have been A-delivered at both `(p, t₁)` and `(q, t₂)`, then `p` delivered `m₁` before `m₂` iff
   `q` delivered `m₁` before `m₂`;
4. **Agreement:** if `p ∉ F` A-delivers `m` at `t₁`, then every `q ∉ F` eventually A-delivers `m`;
5. **Validity:** for every `m ∈ E.correctBcast` and every `p ∉ F`, `p` eventually A-delivers `m`. -/
theorem totalOrderBroadcast_of_consensusSlotExec {P Msg : Type*} [Finite P] [LinearOrder Msg]
    {F : Set P} (E : ConsensusSlotExec P Msg F) :
    (∀ p t, (E.aDelivered p t).Nodup) ∧
    (∀ p t m, m ∈ E.aDelivered p t → m ∈ E.bcast) ∧
    (∀ p q t₁ t₂ m₁ m₂,
      m₁ ∈ E.aDelivered p t₁ → m₂ ∈ E.aDelivered p t₁ →
      m₁ ∈ E.aDelivered q t₂ → m₂ ∈ E.aDelivered q t₂ →
      ((E.aDelivered p t₁).idxOf m₁ < (E.aDelivered p t₁).idxOf m₂ ↔
        (E.aDelivered q t₂).idxOf m₁ < (E.aDelivered q t₂).idxOf m₂)) ∧
    (∀ p ∉ F, ∀ q ∉ F, ∀ m t₁, m ∈ E.aDelivered p t₁ → ∃ t₂, m ∈ E.aDelivered q t₂) ∧
    (∀ m ∈ E.correctBcast, ∀ p ∉ F, ∃ t, m ∈ E.aDelivered p t) := by
  have hutot : ∀ p q t₁ t₂ m₁ m₂,
      m₁ ∈ E.aDelivered p t₁ → m₂ ∈ E.aDelivered p t₁ →
      m₁ ∈ E.aDelivered q t₂ → m₂ ∈ E.aDelivered q t₂ →
      ((E.aDelivered p t₁).idxOf m₁ < (E.aDelivered p t₁).idxOf m₂ ↔
        (E.aDelivered q t₂).idxOf m₁ < (E.aDelivered q t₂).idxOf m₂) := by
    intro p q t₁ t₂ m₁ m₂ hm₁p hm₂p hm₁q hm₂q
    rcases le_total (E.decidedBatches p t₁).length (E.decidedBatches q t₂).length with hle | hge
    · have hpref := E.aDelivered_prefix_of_length_le hle
      rw [hpref.idxOf_eq_of_mem hm₁p, hpref.idxOf_eq_of_mem hm₂p]
    · have hpref := E.aDelivered_prefix_of_length_le hge
      rw [hpref.idxOf_eq_of_mem hm₁q, hpref.idxOf_eq_of_mem hm₂q]
  have hagr : ∀ p ∉ F, ∀ q ∉ F, ∀ m t₁, m ∈ E.aDelivered p t₁ → ∃ t₂, m ∈ E.aDelivered q t₂ := by
    intro p hp q hq m t₁ hm
    obtain ⟨batch, hbatch_mem, hm_in⟩ := (mem_runConsensusSlots _ m).mp hm
    obtain ⟨k, hk_lt, rfl⟩ := List.getElem_of_mem hbatch_mem
    obtain ⟨t₀, _, b₀, hp₀⟩ := E.decide_requires_propose p t₁ k hk_lt
    obtain ⟨_, hdec_k⟩ := E.ct_lemma_7_1_2 k ⟨p, hp, t₀, b₀, hp₀⟩
    obtain ⟨t₂, ht₂_lt⟩ := hdec_k q hq
    refine ⟨t₂, ?_⟩
    have hm_in_q_batch : m ∈ (E.decidedBatches q t₂)[k] :=
      (E.cons_agreement p q t₁ t₂ k hk_lt ht₂_lt m).mp hm_in
    exact (mem_runConsensusSlots _ m).mpr
      ⟨(E.decidedBatches q t₂)[k], List.getElem_mem _, hm_in_q_batch⟩
  refine ⟨fun p t => runConsensusSlots_nodup _, ?_, hutot, hagr, ?_⟩
  · intro p t m hm
    obtain ⟨batch, hbatch_mem, hm_in⟩ := (mem_runConsensusSlots _ m).mp hm
    obtain ⟨k, hk_lt, rfl⟩ := List.getElem_of_mem hbatch_mem
    obtain ⟨r, t_r, propBatch, hprop, hiff⟩ := E.cons_validity p t k hk_lt
    have hm_prop : m ∈ propBatch := (hiff m).mp hm_in
    have hm_rdeliv : m ∈ E.rDelivered r t_r :=
      (((E.propose_spec r k t_r propBatch hprop).2.2 m).mp hm_prop).1
    exact E.rb_integrity r t_r m hm_rdeliv
  · cases nonempty_fintype P
    intro m hm_cb p hp
    by_contra hnever_p
    push Not at hnever_p
    have hnever_all : ∀ q ∉ F, ∀ t, m ∉ E.aDelivered q t := by
      intro q hq t hm_q
      obtain ⟨t_p, hm_p⟩ := hagr q hq p hp m t hm_q
      exact hnever_p t_p hm_p
    have hex_tau : ∀ q : P, ∃ τ : ℕ, q ∉ F → m ∈ E.rDelivered q τ := by
      intro q
      by_cases hq : q ∉ F
      · obtain ⟨τ, hτ⟩ := E.rb_validity m hm_cb q hq
        exact ⟨τ, fun _ => hτ⟩
      · exact ⟨0, fun hc => absurd hc hq⟩
    choose tauFn htauFn using hex_tau
    have hex_kf :
        ∀ r : P, ∃ K_r : ℕ, r ∈ F → ∀ k, K_r ≤ k → ∀ t batch, ¬ E.Proposed r k t batch := by
      intro r
      by_cases hr : r ∈ F
      · obtain ⟨K_r, hK_r⟩ := E.faulty_eventually_halted r hr
        exact ⟨K_r, fun _ => hK_r⟩
      · exact ⟨0, fun hc => absurd hc hr⟩
    choose kFaultyFn hkFaultyFn using hex_kf
    let K_F : ℕ := Finset.univ.sup kFaultyFn
    let K_C : ℕ := Finset.univ.sup (fun q => (E.decidedBatches q (tauFn q)).length) + 1
    let K_star : ℕ := max K_F K_C
    have hp_reaches : ∀ n : ℕ, ∃ t, n ≤ (E.decidedBatches p t).length := by
      intro n
      induction n with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ k ihk =>
        obtain ⟨t_k, ht_k⟩ := ihk
        let T := max t_k (tauFn p)
        have hlen_T : k ≤ (E.decidedBatches p T).length :=
          le_trans ht_k (E.decidedBatches_prefix p (Nat.le_max_left _ _)).length_le
        by_cases hgt : k < (E.decidedBatches p T).length
        · exact ⟨T, Nat.succ_le_of_lt hgt⟩
        · have heq_k : (E.decidedBatches p T).length = k := by omega
          have hm_rT : m ∈ E.rDelivered p T :=
            E.rDelivered_mono p (Nat.le_max_right _ _) (htauFn p hp)
          have hm_not_aT : m ∉ runConsensusSlots (E.decidedBatches p T) := hnever_p T
          obtain ⟨t_prop, b_prop, hprop_k⟩ :=
            E.task3_fair p hp T k heq_k ⟨m, hm_rT, hm_not_aT⟩
          obtain ⟨_, hdec_k⟩ := E.ct_lemma_7_1_2 k ⟨p, hp, t_prop, b_prop, hprop_k⟩
          obtain ⟨t_next, ht_next⟩ := hdec_k p hp
          exact ⟨t_next, Nat.succ_le_of_lt ht_next⟩
    obtain ⟨t_star, ht_star⟩ := hp_reaches (K_star + 1)
    have hk_lt : K_star < (E.decidedBatches p t_star).length := by omega
    obtain ⟨r, t_r, batch_r, hprop_r, hiff_r⟩ := E.cons_validity p t_star K_star hk_lt
    have hr_not_F : r ∉ F := by
      intro hrF
      have hge_Kr : kFaultyFn r ≤ K_star :=
        le_trans (Finset.le_sup (f := kFaultyFn) (Finset.mem_univ r)) (Nat.le_max_left K_F K_C)
      exact hkFaultyFn r hrF K_star hge_Kr t_r batch_r hprop_r
    obtain ⟨hlen_r, _, hmem_r⟩ := E.propose_spec r K_star t_r batch_r hprop_r
    have hgt_tau_len : (E.decidedBatches r (tauFn r)).length < K_star := by
      have hle_sup : (E.decidedBatches r (tauFn r)).length ≤
          Finset.univ.sup (fun q => (E.decidedBatches q (tauFn q)).length) :=
        Finset.le_sup (f := fun q => (E.decidedBatches q (tauFn q)).length) (Finset.mem_univ r)
      have hKC_le : K_C ≤ K_star := Nat.le_max_right K_F K_C
      omega
    have htau_lt_tr : tauFn r < t_r := by
      by_contra hge
      have htr_le : t_r ≤ tauFn r := by omega
      have hlen_le := (E.decidedBatches_prefix r htr_le).length_le
      omega
    have hm_in_r : m ∈ E.rDelivered r t_r :=
      E.rDelivered_mono r (Nat.le_of_lt htau_lt_tr) (htauFn r hr_not_F)
    have hm_not_ar : m ∉ runConsensusSlots (E.decidedBatches r t_r) :=
      hnever_all r hr_not_F t_r
    have hm_in_batch : m ∈ batch_r := (hmem_r m).mpr ⟨hm_in_r, hm_not_ar⟩
    have hm_in_dec : m ∈ (E.decidedBatches p t_star)[K_star] := (hiff_r m).mpr hm_in_batch
    have hm_in_adeliv : m ∈ E.aDelivered p t_star :=
      (mem_runConsensusSlots _ m).mpr
        ⟨(E.decidedBatches p t_star)[K_star], List.getElem_mem _, hm_in_dec⟩
    exact hnever_p t_star hm_in_adeliv

end ConsensusToTotalOrder

/-! ### Part 5: Single-Group Causal vs. One-Shot Total-Order Fault-Tolerance Dichotomy Step -/

/-- Fault-tolerance dichotomy step between single-group atomic-multicast `CBCAST` and one-shot
`TotalOrderBroadcastAlg` (toward #7297, after [BirmanSchiperStephenson1991], §5.1;
[HadzilacosToueg1994], §3.3, §3.4 & Corollary 2; [ChandraToueg1996], §7):

Over any finite process set `P` with `2 ≤ Fintype.card P` and any nontrivial payload type `V`, for
every crash-fault threshold `t < Fintype.card P`:
1. Single-group atomic-multicast causal broadcast (`bssLTS`) is deterministically solvable for all
   `t < Fintype.card P`: for every fault set `F : Set P` with `F.ncard ≤ t`, non-faulty processes
   exist (`∃ q, q ∉ F`) and `bssLTS F` satisfies `BSSSolvesAtomicMulticastCausalBroadcast P V F`;
2. One-shot total-order broadcast (`TotalOrderBroadcastAlg`) is deterministically solvable iff
   `t = 0` (impossible for `t ≥ 1` by reduction to `Cslib.FLP`). -/
theorem causal_vs_oneShotTotalOrder_dichotomy {P : Type u} {V : Type v}
    [Fintype P] [DecidableEq P] [DecidableEq V] [Nontrivial V]
    (hc : 2 ≤ Fintype.card P) {t : ℕ} (ht : t < Fintype.card P) :
    (∀ F : Set P, F.ncard ≤ t →
      (∃ q : P, q ∉ F) ∧ BSSSolvesAtomicMulticastCausalBroadcast P V F) ∧
    ((∃ (M S : Type (max u v)) (_ : DecidableEq M) (π : TotalOrderBroadcastAlg P M S V),
        π.SolvesTotalOrderBroadcast t) ↔ t = 0) := by
  refine ⟨fun F hF => ⟨?_, bss_solves_atomicMulticast_causalBroadcast F⟩,
    exists_oneShotTotalOrderBroadcast_iff_eq_zero hc t⟩
  by_contra hall_in
  push Not at hall_in
  have hF_univ : F = Set.univ := Set.eq_univ_of_forall hall_in
  rw [hF_univ, Set.ncard_univ, Nat.card_eq_fintype_card] at hF
  omega

end Cslib.Distributed.CausalBroadcast
