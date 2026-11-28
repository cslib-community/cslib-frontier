/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ABD.Basic
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.WithBot
import CslibFrontier.Tactic.FinsetCard
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.SDiff

/-!
# Cardinality-quorum multi-writer atomic register emulation

This module formalizes `abdProtocol`, an independent cardinality-quorum point-to-point envelope
specialization **after** the two-phase multi-writer multi-reader (MWMR) construction of Lynch and
Shvartsman ([LynchShvartsman1997], §4.1–4.2 in the December 2, 1996 manuscript) and the majority
read write-back discipline of Attiya, Bar-Noy, and Dolev ([AttiyaBarNoyDolev1995], §4), as a step
toward full atomic-register emulation rather than the cited Theorem 4.5 or Theorem 4.9 endpoints:

* [LynchShvartsman1997] (§4.1–4.2, Theorem 4.5) parameterizes over separate fixed read and write
  quorum families, a quorum-acknowledged broadcast abstraction, and a per-processor client request
  queue, and Theorem 4.5 proves atomicity only (with conditional `4d` time and `8n` message bounds
  in §4.3 Theorem 4.6 and dynamic reconfiguration in §5).
* [AttiyaBarNoyDolev1995] (§4, Theorem 4.9, p. 134) emulates an unbounded single-writer
  multi-reader (SWMR) register over ping-pong channels using **one** communication phase for writes
  and **two** phases (query + write-back) for reads with `O(n)` message and `O(1)` time bounds,
  obtaining MWMR registers in §7 by composition (with bounded timestamps in §5 and dynamic links in
  §6).
* Here `abdProtocol` instead runs two uniform `(n - t)`-cardinality quorum phases over concrete
  unordered point-to-point envelopes (`Envelope`) with idle-only client invocations
  (`(s.proc caller).pending = none`) and lexicographic writer tags `Tag P := ℕ ×ₗ WithBot P`,
  proving both safety (`Reachable s → Linearizable v₀ s.history` in `abd_linearizable`) and a
  separate fair-crash liveness property (`abd_terminates` under `Protocol.Fair F`) without cost
  bounds:

* Each replica `p : P` stores `(repTag, repVal)` initialized to `(initTag P, v₀)` where
  `initTag P = toLex (0, ⊥)`, and updates its pair upon receiving `ABDMsg.store reqId inTag inVal`
  if and only if `repTag < inTag`.
* **`write v` by `caller`:** Phase 1 broadcasts `ABDMsg.query reqId` and collects `(rTag, rVal)`
  responses from `n - t` distinct replicas, choosing `chosenTag := nextWriteTag bestTag.seq caller`
  (`toLex (bestTag.seq + 1, ↑caller)`). Phase 2 broadcasts `ABDMsg.store reqId chosenTag v` and
  waits for `n - t` `ABDMsg.ack reqId` responses before returning.
* **`read` by `caller`:** Phase 1 queries `n - t` distinct replicas and picks `(bestTag, bestVal)`
  maximizing `tag` lexicographically. Phase 2 performs the **write-back** broadcast
  `ABDMsg.store reqId bestTag bestVal` and waits for `n - t` `ABDMsg.ack reqId` responses before
  returning `bestVal`.

For `2 * t < Fintype.card P`, any two quorums of size at least `n - t` intersect
(`quorum_inter_nonempty`), and replica tags never decrease (`tr_repTag_mono`). Consequently, every
operation invoked after a completed operation `a` observes a tag at least `a`'s Phase-2 tag
(strictly greater when the later operation is a `write`), and sorting all completed operations
together with Phase-2 pending writes by `(tag, isRead, opId)` yields an explicit valid
linearization (`abd_linearizable`). Against any static faulty set `F` of size at most `t`,
`n - F.card ≥ n - t` non-faulty replicas respond in each phase, establishing wait-free termination
(`abd_terminates`) and `implementsAtomicRegister_abd`.

## Main definitions

* `Cslib.Distributed.ABD.Tag`, `Cslib.Distributed.ABD.initTag`,
  `Cslib.Distributed.ABD.nextWriteTag`: lexicographic `(seq, writer)` version tags.
* `Cslib.Distributed.ABD.ABDMsg`, `Cslib.Distributed.ABD.ClientPhase`,
  `Cslib.Distributed.ABD.ABDState`: ABD messages and per-process replica/client state.
* `Cslib.Distributed.ABD.abdOnInvoke`, `Cslib.Distributed.ABD.abdOnRecv`,
  `Cslib.Distributed.ABD.abdProtocol`: two-phase fixed-`(n - t)`-quorum MWMR register emulation
  protocol.

## Main results

* `Cslib.Distributed.ABD.quorum_inter_nonempty`, `Cslib.Distributed.ABD.quorum_inter_notMem`:
  quorum intersection for `2 * t < Fintype.card P`.
* `Cslib.Distributed.ABD.tr_repTag_mono`, `Cslib.Distributed.ABD.mTr_repTag_mono`: replica tag
  monotonicity across transitions and finite executions.
* `Cslib.Distributed.ABD.abd_linearizable`: every reachable state of `abdProtocol` has a
  linearizable execution history when `2 * t < Fintype.card P`.
* `Cslib.Distributed.ABD.abd_terminates`: every operation invoked by a non-faulty process
  completes in every `t`-fault admissible run of `abdProtocol` when `2 * t < Fintype.card P`.
* `Cslib.Distributed.ABD.implementsAtomicRegister_abd`: `abdProtocol` implements a `t`-resilient
  wait-free linearizable atomic register when `2 * t < Fintype.card P`.

## References

* [H. Attiya, A. Bar-Noy, D. Dolev, *Sharing memory robustly in message-passing
  systems*][AttiyaBarNoyDolev1995]
* [N. A. Lynch, A. A. Shvartsman, *Robust emulation of shared memory using dynamic
  quorum-acknowledged broadcasts*][LynchShvartsman1997]
-/

public section

namespace Cslib.Distributed.ABD

open Cslib Cslib.ωSequence

/-! ### Lexicographic version tags -/

/-- Lexicographically ordered ABD version tag `(seq, writer)`, where `(0, ⊥)` marks the initial
register value `v₀` and `(seq + 1, ↑w)` marks a write by process `w : P`. -/
abbrev Tag (P : Type*) := ℕ ×ₗ WithBot P

/-- Sequence-number component of an ABD `Tag`. -/
@[expose] def Tag.seq {P : Type*} (τ : Tag P) : ℕ := (ofLex τ).1

/-- Optional writer component of an ABD `Tag` (`⊥` for the initial value, `↑w` for writer `w`). -/
@[expose] def Tag.writer {P : Type*} (τ : Tag P) : WithBot P := (ofLex τ).2

/-- Initial ABD tag `toLex (0, ⊥)` associated with the initial register value `v₀`. -/
@[expose] def initTag (P : Type*) : Tag P := toLex (0, ⊥)

/-- Fresh ABD tag `toLex (maxSeq + 1, ↑w)` chosen by writer `w` after observing maximum sequence
number `maxSeq` across its Phase-1 quorum. -/
@[expose] def nextWriteTag {P : Type*} (maxSeq : ℕ) (w : P) : Tag P :=
  toLex (maxSeq + 1, (w : WithBot P))

@[simp]
theorem initTag_seq (P : Type*) : (initTag P).seq = 0 := rfl

@[simp]
theorem initTag_writer (P : Type*) : (initTag P).writer = ⊥ := rfl

@[simp]
theorem nextWriteTag_seq {P : Type*} (s : ℕ) (w : P) : (nextWriteTag s w).seq = s + 1 := rfl

@[simp]
theorem nextWriteTag_writer {P : Type*} (s : ℕ) (w : P) :
    (nextWriteTag s w).writer = (w : WithBot P) := rfl

/-- `initTag P` (`(0, ⊥)`) is the least element of `Tag P`. -/
theorem initTag_le {P : Type*} [LinearOrder P] (τ : Tag P) : initTag P ≤ τ := by
  rw [initTag, ← toLex_ofLex τ, Prod.Lex.toLex_le_toLex]
  by_cases h : 0 < (ofLex τ).1
  · exact Or.inl h
  · exact Or.inr ⟨by omega, bot_le⟩

/-- Every write tag `nextWriteTag s w` strictly exceeds `initTag P`. -/
theorem initTag_lt_nextWriteTag {P : Type*} [LinearOrder P] (s : ℕ) (w : P) :
    initTag P < nextWriteTag s w :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inl (Nat.succ_pos s))

private lemma lt_nextWriteTag_of_seq_le {P : Type*} [LinearOrder P] {τ : Tag P} {s : ℕ}
    (h : τ.seq ≤ s) (w : P) : τ < nextWriteTag s w := by
  rw [← toLex_ofLex τ, nextWriteTag, Prod.Lex.toLex_lt_toLex]
  exact Or.inl (Nat.lt_succ_of_le h)

private lemma seq_le_of_le {P : Type*} [LinearOrder P] {τ₁ τ₂ : Tag P} (h : τ₁ ≤ τ₂) :
    τ₁.seq ≤ τ₂.seq := by
  rw [← toLex_ofLex τ₁, ← toLex_ofLex τ₂, Prod.Lex.toLex_le_toLex] at h
  rcases h with hlt | ⟨heq, _⟩
  · exact Nat.le_of_lt hlt
  · exact Nat.le_of_eq heq

/-! ### Quorum intersection -/

/-- **Quorum intersection:** when `2 * t < Fintype.card P`, any two subsets `Q₁, Q₂ : Finset P` of
cardinality at least `Fintype.card P - t` share at least one server. -/
theorem quorum_inter_nonempty {P : Type*} [Fintype P] [DecidableEq P] {t : ℕ}
    (h2t : 2 * t < Fintype.card P) {Q₁ Q₂ : Finset P}
    (hQ₁ : Fintype.card P - t ≤ Q₁.card) (hQ₂ : Fintype.card P - t ≤ Q₂.card) :
    (Q₁ ∩ Q₂).Nonempty := by
  finset_card

/-- When `Q₁` consists of non-faulty servers (`∀ q ∈ Q₁, q ∉ F`), any two `(n - t)`-quorums
intersect in a live server outside `F`. -/
theorem quorum_inter_notMem {P : Type*} [Fintype P] [DecidableEq P] {t : ℕ}
    (h2t : 2 * t < Fintype.card P) {F Q₁ Q₂ : Finset P}
    (hQ₁ : Fintype.card P - t ≤ Q₁.card) (hQ₂ : Fintype.card P - t ≤ Q₂.card)
    (hlive : ∀ q ∈ Q₁, q ∉ F) :
    ∃ q ∈ Q₁ ∩ Q₂, q ∉ F := by
  obtain ⟨q, hq⟩ := quorum_inter_nonempty h2t hQ₁ hQ₂
  exact ⟨q, hq, hlive q (Finset.mem_of_mem_inter_left hq)⟩

/-! ### ABD protocol messages, state, and transitions -/

/-- Network messages exchanged by the two-phase ABD register emulation protocol. -/
inductive ABDMsg (P V : Type*) where
  /-- Phase-1 query asking a replica for its current `(repTag, repVal)`. -/
  | query (reqId : ℕ)
  /-- Phase-1 reply reporting `(tag, val)` for `reqId`. -/
  | queryResp (reqId : ℕ) (tag : Tag P) (val : V)
  /-- Phase-2 command asking a replica to store `(tag, val)` if `tag` exceeds its current tag. -/
  | store (reqId : ℕ) (tag : Tag P) (val : V)
  /-- Phase-2 acknowledgment confirming processing of `store reqId`. -/
  | ack (reqId : ℕ)
  deriving @[expose] DecidableEq

/-- Client-side phase state of a process in the ABD protocol. -/
inductive ClientPhase (P V : Type*) where
  /-- No client operation is currently active. -/
  | idle
  /-- Phase 1: collecting `(tag, val)` replies from `n - t` distinct replicas. -/
  | phase1 (reqId : ℕ) (kind : OpKind V) (responses : Finset P) (bestTag : Tag P) (bestVal : V)
  /-- Phase 2: broadcasting `store(chosenTag, chosenVal)` (write or read write-back) and collecting
  `n - t` acknowledgments. -/
  | phase2 (reqId : ℕ) (kind : OpKind V) (chosenTag : Tag P) (chosenVal : V) (acks : Finset P)
  deriving @[expose] DecidableEq

/-- Local state of process `p : P` in the ABD protocol, combining its replica storage and its
client state machine. -/
@[ext]
structure ABDState (P V : Type*) where
  /-- Highest version tag stored at this replica. -/
  repTag : Tag P
  /-- Value associated with `repTag` at this replica. -/
  repVal : V
  /-- Counter generating fresh request nonces for this process's client invocations. -/
  nextReqId : ℕ
  /-- Active client phase (`.idle`, `.phase1`, or `.phase2`). -/
  phase : ClientPhase P V
  deriving @[expose] DecidableEq

/-- Initial local state of each ABD process. -/
@[expose] def abdInit (P : Type*) {V : Type*} (v₀ : V) : ABDState P V where
  repTag := initTag P
  repVal := v₀
  nextReqId := 0
  phase := .idle

/-- Client invocation handler for the ABD protocol: enter `.phase1` with a fresh `reqId` and
broadcast `.query reqId` to every replica. -/
@[expose] def abdOnInvoke {P V : Type*} [Fintype P] (v₀ : V) (_caller : P)
    (st : ABDState P V) (kind : OpKind V) : StepOut P (ABDMsg P V) (ABDState P V) V :=
  let reqId := st.nextReqId
  ⟨{ st with
      nextReqId := reqId + 1
      phase := .phase1 reqId kind ∅ (initTag P) v₀ },
   broadcastAll P (.query reqId),
   none⟩

/-- Message reception handler for the ABD protocol at recipient `dest` from sender `src`, using
quorum threshold `Fintype.card P - t`. -/
@[expose] def abdOnRecv {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder P] (t : ℕ)
    (dest : P) (st : ABDState P V) (src : P) (msg : ABDMsg P V) :
    StepOut P (ABDMsg P V) (ABDState P V) V :=
  let qSize := Fintype.card P - t
  match msg with
  | .query reqId =>
    ⟨st, {(src, .queryResp reqId st.repTag st.repVal)}, none⟩
  | .store reqId inTag inVal =>
    let st' := if st.repTag < inTag then { st with repTag := inTag, repVal := inVal } else st
    ⟨st', {(src, .ack reqId)}, none⟩
  | .queryResp rId rTag rVal =>
    match st.phase with
    | .phase1 reqId kind responses bestTag bestVal =>
      if rId = reqId then
        let responses' := insert src responses
        let bestTag' := if bestTag < rTag then rTag else bestTag
        let bestVal' := if bestTag < rTag then rVal else bestVal
        if qSize ≤ responses'.card then
          let chosenTag := match kind with
            | .write _ => nextWriteTag bestTag'.seq dest
            | .read => bestTag'
          let chosenVal := match kind with
            | .write v => v
            | .read => bestVal'
          ⟨{ st with phase := .phase2 reqId kind chosenTag chosenVal ∅ },
           broadcastAll P (.store reqId chosenTag chosenVal),
           none⟩
        else
          ⟨{ st with phase := .phase1 reqId kind responses' bestTag' bestVal' }, 0, none⟩
      else
        ⟨st, 0, none⟩
    | _ => ⟨st, 0, none⟩
  | .ack rId =>
    match st.phase with
    | .phase2 reqId kind chosenTag chosenVal acks =>
      if rId = reqId then
        let acks' := insert src acks
        if qSize ≤ acks'.card then
          let outResp := match kind with
            | .read => OpResp.readRet chosenVal
            | .write _ => OpResp.writeAck
          ⟨{ st with phase := .idle }, 0, some outResp⟩
        else
          ⟨{ st with phase := .phase2 reqId kind chosenTag chosenVal acks' }, 0, none⟩
      else
        ⟨st, 0, none⟩
    | _ => ⟨st, 0, none⟩

/-- Uniform two-phase `(n - t)`-cardinality quorum multi-writer multi-reader register protocol over
unordered envelopes with idle-only invocations, lexicographic `(seq, writer)` tags, and Phase-2
read write-back (an independent cardinality-quorum specialization **after**
[LynchShvartsman1997], §4.1 and [AttiyaBarNoyDolev1995], §4, replacing separate read/write quorum
families, broadcast primitives, and per-processor request queues with concrete envelope steps). -/
@[expose] def abdProtocol (P V : Type*) [Fintype P] [DecidableEq P] [LinearOrder P]
    (v₀ : V) (t : ℕ) : Protocol P (ABDState P V) (ABDMsg P V) V where
  init _ := abdInit P v₀
  onInvoke := abdOnInvoke v₀
  onRecv := abdOnRecv t

/-! ### Replica tag monotonicity -/

private lemma abdOnRecv_repTag_mono {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder P]
    (t : ℕ) (dest : P) (st : ABDState P V) (src : P) (msg : ABDMsg P V) :
    st.repTag ≤ (abdOnRecv t dest st src msg).nextState.repTag := by
  unfold abdOnRecv
  cases msg with
  | query _ => exact le_rfl
  | store _ inTag inVal =>
    dsimp only
    split_ifs with hlt
    · exact le_of_lt hlt
    · exact le_rfl
  | queryResp _ _ _ =>
    cases st.phase with
    | phase1 _ _ _ _ _ =>
      dsimp only
      split_ifs <;> exact le_rfl
    | _ => exact le_rfl
  | ack _ =>
    cases st.phase with
    | phase2 _ _ _ _ _ =>
      dsimp only
      split_ifs <;> exact le_rfl
    | _ => exact le_rfl

private lemma abdOnRecv_store_le_repTag {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder P]
    (t : ℕ) (dest : P) (st : ABDState P V) (src : P) (reqId : ℕ) (inTag : Tag P) (inVal : V) :
    inTag ≤ (abdOnRecv t dest st src (.store reqId inTag inVal)).nextState.repTag := by
  unfold abdOnRecv
  dsimp only
  split_ifs with hlt
  · exact le_rfl
  · exact le_of_not_gt hlt

/-- **Replica tag monotonicity (single transition):** no replica's stored `repTag` ever decreases
across any transition of `abdProtocol`. -/
theorem tr_repTag_mono {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder P] [DecidableEq V]
    {v₀ : V} {t : ℕ} {s s' : State P (ABDState P V) (ABDMsg P V) V}
    {a : Action P (ABDMsg P V) V} (htr : (abdProtocol P V v₀ t).lts.Tr s a s') (q : P) :
    (s.proc q).state.repTag ≤ (s'.proc q).state.repTag := by
  cases a with
  | invoke caller kind =>
    obtain ⟨_, rfl⟩ := htr
    simp only [Protocol.doInvoke, abdProtocol, abdOnInvoke]
    by_cases hq : q = caller
    · subst hq; simp
    · simp [hq]
  | deliver e =>
    obtain ⟨_, rfl⟩ := htr
    simp only [Protocol.doDeliver, abdProtocol]
    by_cases hq : q = e.dest
    · subst hq
      simp only [Function.update_self]
      exact abdOnRecv_repTag_mono t e.dest (s.proc e.dest).state e.src e.body
    · simp [hq]
  | stutter =>
    obtain rfl := htr
    exact le_rfl

/-- **Replica tag monotonicity (finite execution):** no replica's stored `repTag` ever decreases
along any finite execution of `abdProtocol`. -/
theorem mTr_repTag_mono {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder P] [DecidableEq V]
    {v₀ : V} {t : ℕ} {s s' : State P (ABDState P V) (ABDMsg P V) V}
    {xl : List (Action P (ABDMsg P V) V)}
    (hmtr : (abdProtocol P V v₀ t).lts.MTr s xl s') (q : P) :
    (s.proc q).state.repTag ≤ (s'.proc q).state.repTag := by
  induction hmtr with
  | refl => exact le_rfl
  | stepL htr _ ih => exact (tr_repTag_mono htr q).trans ih

/-! ### Global invariant for linearizability -/

section Invariant

/-- Relation witnessing that `(τ, v)` is either the initial pair `(initTag P, v₀)` or the tag and
value written by an operation `i` that has entered Phase 2. -/
private def TagValidVal {P V : Type*} (v₀ : V) (hist : List (OpRecord P V))
    (opTag : ℕ → Option (Tag P)) (τ : Tag P) (v : V) : Prop :=
  (τ = initTag P ∧ v = v₀) ∨
  ∃ (i : ℕ) (hi : i < hist.length), hist[i].kind = .write v ∧ opTag i = some τ

private lemma tagValidVal_mono {P V : Type*} {v₀ : V} {hist hist' : List (OpRecord P V)}
    {opTag opTag' : ℕ → Option (Tag P)}
    (hlen : hist.length ≤ hist'.length)
    (hpres : ∀ (i : ℕ) (hi : i < hist.length) (τ : Tag P),
      opTag i = some τ →
      (hist'[i]'(lt_of_lt_of_le hi hlen)).kind = hist[i].kind ∧ opTag' i = some τ)
    {τ : Tag P} {v : V} (hv : TagValidVal v₀ hist opTag τ v) :
    TagValidVal v₀ hist' opTag' τ v := by
  rcases hv with hinit | ⟨i, hi, hk, htag⟩
  · exact Or.inl hinit
  · obtain ⟨hk', htag'⟩ := hpres i hi τ htag
    exact Or.inr ⟨i, lt_of_lt_of_le hi hlen, hk'.trans hk, htag'⟩

/-- Equation-compiled synchronization predicate between `pending`, `phase`, `history`, and `opTag`
at process `p`. -/
private def ProcSync {P V : Type*} [Fintype P] [LinearOrder P] (t : ℕ)
    (hist : List (OpRecord P V)) (nextReqId : ℕ) (repTag : P → Tag P)
    (opTag : ℕ → Option (Tag P)) (p : P) :
    Option (PendingOp V) → ClientPhase P V → Prop
  | none, .idle => True
  | some pend, .phase1 reqId kind responses _ _ =>
    ∃ hi : pend.opId < hist.length,
      hist[pend.opId].caller = p ∧
      hist[pend.opId].kind = kind ∧
      pend.kind = kind ∧
      hist[pend.opId].status = .pending ∧
      opTag pend.opId = none ∧
      reqId < nextReqId ∧
      responses.card < Fintype.card P - t ∧
      ∀ j (hj : j < hist.length), j ≠ pend.opId → hist[j].caller = p →
        prec hist j pend.opId
  | some pend, .phase2 reqId kind chosenTag _ acks =>
    ∃ hi : pend.opId < hist.length,
      hist[pend.opId].caller = p ∧
      hist[pend.opId].kind = kind ∧
      pend.kind = kind ∧
      hist[pend.opId].status = .pending ∧
      opTag pend.opId = some chosenTag ∧
      reqId < nextReqId ∧
      acks.card < Fintype.card P - t ∧
      (∀ q ∈ acks, chosenTag ≤ repTag q) ∧
      ∀ j (hj : j < hist.length), j ≠ pend.opId → hist[j].caller = p →
        prec hist j pend.opId
  | _, _ => False

private lemma mem_map_tagSender_broadcastAll {P M : Type*} [Fintype P]
    {src : P} {m : M} {e : Envelope P M} :
    e ∈ (broadcastAll P m).map (tagSender src) ↔ e.src = src ∧ e.body = m := by
  constructor
  · simp only [broadcastAll, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
    rintro ⟨_, ⟨_, rfl⟩, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨hsrc, hbody⟩
    have he : e = ⟨src, e.dest, m⟩ := by ext <;> simp [hsrc, hbody]
    exact he ▸ mem_broadcastAll_tag src e.dest m

private lemma procSync_transport {P V : Type*} [Fintype P] [LinearOrder P] {t : ℕ}
    {hist hist' : List (OpRecord P V)} {nr₁ nr₂ : ℕ} {rt₁ rt₂ : P → Tag P}
    {opTag₁ opTag₂ : ℕ → Option (Tag P)} {p : P}
    {pend? : Option (PendingOp V)} {ph : ClientPhase P V}
    (hlen : hist.length ≤ hist'.length)
    (hnr : nr₁ ≤ nr₂) (hrt : ∀ q, rt₁ q ≤ rt₂ q)
    (hEntry : ∀ pend (hi : pend.opId < hist.length), pend? = some pend →
      hist[pend.opId].caller = p →
      (hist'[pend.opId]'(lt_of_lt_of_le hi hlen)).caller = p ∧
      (hist'[pend.opId]'(lt_of_lt_of_le hi hlen)).kind = hist[pend.opId].kind ∧
      (hist'[pend.opId]'(lt_of_lt_of_le hi hlen)).status = hist[pend.opId].status ∧
      opTag₂ pend.opId = opTag₁ pend.opId ∧
      ((∀ j (hj : j < hist.length), j ≠ pend.opId → hist[j].caller = p →
          prec hist j pend.opId) →
       ∀ j (hj : j < hist'.length), j ≠ pend.opId → hist'[j].caller = p →
          prec hist' j pend.opId))
    (hps : ProcSync t hist nr₁ rt₁ opTag₁ p pend? ph) :
    ProcSync t hist' nr₂ rt₂ opTag₂ p pend? ph := by
  cases pend? with
  | none => cases ph <;> exact hps
  | some pend =>
    cases ph with
    | idle => exact hps
    | phase1 _ _ _ _ _ =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hps
      obtain ⟨hc, hk, hs, htag, hpr⟩ := hEntry pend h1 rfl h2
      exact ⟨lt_of_lt_of_le h1 hlen, hc, hk.trans h3, h4, hs.trans h5,
        htag.trans h6, lt_of_lt_of_le h7 hnr, h8, hpr h9⟩
    | phase2 _ _ _ _ _ =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hps
      obtain ⟨hc, hk, hs, htag, hpr⟩ := hEntry pend h1 rfl h2
      exact ⟨lt_of_lt_of_le h1 hlen, hc, hk.trans h3, h4, hs.trans h5,
        htag.trans h6, lt_of_lt_of_le h7 hnr, h8, fun q hq => (h9 q hq).trans (hrt q),
        hpr h10⟩

/-- Equation-compiled well-formedness predicate for an in-flight envelope `e` with body `msg`. -/
private def MsgWF {P V : Type*} [LinearOrder P] (v₀ : V)
    (s : State P (ABDState P V) (ABDMsg P V) V) (opTag : ℕ → Option (Tag P))
    (src dest : P) : ABDMsg P V → Prop
  | .query reqId => reqId < (s.proc src).state.nextReqId
  | .queryResp reqId τ v =>
    reqId < (s.proc dest).state.nextReqId ∧ TagValidVal v₀ s.history opTag τ v
  | .store reqId τ v =>
    reqId < (s.proc src).state.nextReqId ∧ TagValidVal v₀ s.history opTag τ v ∧
    (∀ kind responses bt bv,
      (s.proc src).state.phase = .phase1 reqId kind responses bt bv → False) ∧
    (∀ kind cTag cVal acks,
      (s.proc src).state.phase = .phase2 reqId kind cTag cVal acks → τ = cTag ∧ v = cVal)
  | .ack reqId =>
    reqId < (s.proc dest).state.nextReqId ∧
    (∀ kind responses bt bv,
      (s.proc dest).state.phase = .phase1 reqId kind responses bt bv → False) ∧
    (∀ kind cTag cVal acks,
      (s.proc dest).state.phase = .phase2 reqId kind cTag cVal acks →
        cTag ≤ (s.proc src).state.repTag)

/-- Equation-compiled value-validity predicate for an active `ClientPhase`. -/
private def PhaseValValid {P V : Type*} (v₀ : V) (hist : List (OpRecord P V))
    (opTag : ℕ → Option (Tag P)) : ClientPhase P V → Prop
  | .idle => True
  | .phase1 _ _ _ bestTag bestVal => TagValidVal v₀ hist opTag bestTag bestVal
  | .phase2 _ _ chosenTag chosenVal _ => TagValidVal v₀ hist opTag chosenTag chosenVal

/-- Equation-compiled tag ordering between a preceding operation (`τ_a`) and a later operation of
kind `OpKind V` (`τ_b`). -/
private def PrecTagOrder {P V : Type*} [LinearOrder P] (τ_a τ_b : Tag P) : OpKind V → Prop
  | .write _ => τ_a < τ_b
  | .read => τ_a ≤ τ_b

private lemma phaseValValid_mono {P V : Type*} {v₀ : V} {hist hist' : List (OpRecord P V)}
    {opTag opTag' : ℕ → Option (Tag P)} (hlen : hist.length ≤ hist'.length)
    (hpres : ∀ (i : ℕ) (hi : i < hist.length) (τ : Tag P),
      opTag i = some τ →
      (hist'[i]'(lt_of_lt_of_le hi hlen)).kind = hist[i].kind ∧ opTag' i = some τ)
    {ph : ClientPhase P V} (hv : PhaseValValid v₀ hist opTag ph) :
    PhaseValValid v₀ hist' opTag' ph := by
  cases ph with
  | idle => trivial
  | phase1 _ _ _ _ _ => exact tagValidVal_mono hlen hpres hv
  | phase2 _ _ _ _ _ => exact tagValidVal_mono hlen hpres hv

/-- Global safety invariant for `abdProtocol P V v₀ t` equipped with witness map `opTag` assigning
each completed operation and each Phase-2 pending operation its Phase-2 version tag. -/
private structure ABDGood {P V : Type*} [Fintype P] [LinearOrder P] (v₀ : V) (t : ℕ)
    (s : State P (ABDState P V) (ABDMsg P V) V) (opTag : ℕ → Option (Tag P)) : Prop where
  /-- Outside `s.history.length`, `opTag` is `none`. -/
  tag_out : ∀ i, s.history.length ≤ i → opTag i = none
  /-- Step ordering and completion shape of all entries in `s.history`. -/
  hist_wf : ∀ (i : ℕ) (hi : i < s.history.length),
    s.history[i].invStep < s.step ∧
    (∀ r, s.history[i].status.respStep? = some r → s.history[i].invStep ≤ r ∧ r < s.step) ∧
    (∀ r v, s.history[i].status = .doneRead r v →
      s.history[i].kind = .read ∧ (opTag i).isSome = true) ∧
    (∀ r, s.history[i].status = .doneWrite r →
      (∃ w, s.history[i].kind = .write w) ∧ (opTag i).isSome = true) ∧
    (s.history[i].status = .pending →
      (s.proc s.history[i].caller).pending = some ⟨i, s.history[i].kind⟩)
  /-- Invocation steps strictly increase with history index. -/
  inv_mono : ∀ (i j : ℕ) (hij : i < j) (hj : j < s.history.length),
    (s.history[i]'(hij.trans hj)).invStep < s.history[j].invStep
  /-- Synchronization between `(s.proc p).pending`, `(s.proc p).state.phase`, `opTag`, and earlier
  operations of the same caller `p`. -/
  proc_sync : ∀ p : P,
    ProcSync t s.history (s.proc p).state.nextReqId (fun q => (s.proc q).state.repTag)
      opTag p (s.proc p).pending (s.proc p).state.phase
  /-- Request IDs and phase discipline for all in-flight envelopes. -/
  msg_wf : ∀ e ∈ s.msgs, MsgWF v₀ s opTag e.src e.dest e.body
  /-- Every write operation with an assigned tag has a `nextWriteTag` for its caller, and distinct
  writes never share a tag. -/
  write_unique :
    (∀ (i : ℕ) (hi : i < s.history.length) v τ,
      s.history[i].kind = .write v → opTag i = some τ →
      ∃ seq, τ = nextWriteTag seq s.history[i].caller) ∧
    (∀ (i j : ℕ) (hi : i < s.history.length) (hj : j < s.history.length) v₁ v₂ τ,
      s.history[i].kind = .write v₁ → s.history[j].kind = .write v₂ →
      opTag i = some τ → opTag j = some τ → i = j)
  /-- Value validity for replicas, active client phases, and completed reads. -/
  val_valid :
    (∀ q : P, TagValidVal v₀ s.history opTag (s.proc q).state.repTag (s.proc q).state.repVal) ∧
    (∀ p : P, PhaseValValid v₀ s.history opTag (s.proc p).state.phase) ∧
    (∀ (i : ℕ) (hi : i < s.history.length) step r τ,
      s.history[i].status = .doneRead step r → opTag i = some τ →
      TagValidVal v₀ s.history opTag τ r)
  /-- Every completed operation has written/written-back its tag to at least `n - t` replicas. -/
  completed_quorum : ∀ (a : ℕ) (ha : a < s.history.length) τ_a,
    s.history[a].status.isCompleted = true → opTag a = some τ_a →
    ∃ Q : Finset P, Fintype.card P - t ≤ Q.card ∧
      ∀ q ∈ Q, τ_a ≤ (s.proc q).state.repTag
  /-- Every active Phase-1 operation carries a live quorum witness from each operation `a` that
  completed before it was invoked. -/
  prec_phase1 : ∀ (p : P) pend reqId kind responses bestTag bestVal,
    (s.proc p).pending = some pend →
    (s.proc p).state.phase = .phase1 reqId kind responses bestTag bestVal →
    ∀ (a : ℕ) τ_a, prec s.history a pend.opId → opTag a = some τ_a →
    ∃ Q : Finset P, Fintype.card P - t ≤ Q.card ∧
      (∀ q ∈ Q, τ_a ≤ (s.proc q).state.repTag) ∧
      (∀ q ∈ Q, ∀ rTag rVal, ⟨q, p, .queryResp reqId rTag rVal⟩ ∈ s.msgs → τ_a ≤ rTag) ∧
      (∀ q ∈ Q, q ∈ responses → τ_a ≤ bestTag)
  /-- Real-time precedence translates to tag order for all operations with assigned tags. -/
  prec_tag : ∀ (a b : ℕ) (hb : b < s.history.length) τ_a τ_b,
    prec s.history a b → opTag a = some τ_a → opTag b = some τ_b →
    PrecTagOrder τ_a τ_b s.history[b].kind

private lemma abdGood_start {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder P]
    {v₀ : V} {t : ℕ} :
    ABDGood v₀ t (abdProtocol P V v₀ t).start (fun _ => none) where
  tag_out _ _ := rfl
  hist_wf _ hi := by simp [Protocol.start] at hi
  inv_mono _ _ _ hj := by simp [Protocol.start] at hj
  proc_sync _ := trivial
  msg_wf _ he := by simp [Protocol.start, abdProtocol] at he
  write_unique := ⟨fun _ hi => by simp [Protocol.start] at hi,
    fun _ _ hi => by simp [Protocol.start] at hi⟩
  val_valid := ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => trivial,
    fun _ hi => by simp [Protocol.start] at hi⟩
  completed_quorum _ ha := by simp [Protocol.start] at ha
  prec_phase1 _ _ _ _ _ _ _ hp := by simp [Protocol.start] at hp
  prec_tag _ _ hb := by simp [Protocol.start] at hb

private lemma abdGood_prec_append {P V : Type*} [Fintype P] [LinearOrder P]
    {s : State P (ABDState P V) (ABDMsg P V) V}
    {opTag : ℕ → Option (Tag P)} {v₀ : V} {t : ℕ} (hg : ABDGood v₀ t s opTag)
    (rec' : OpRecord P V) (hinv : rec'.invStep = s.step) (hstat : rec'.status = .pending) :
    (∀ i < s.history.length, ∀ j < s.history.length,
      prec (s.history ++ [rec']) i j ↔ prec s.history i j) ∧
    (∀ a, prec (s.history ++ [rec']) a s.history.length ↔
      ∃ ha : a < s.history.length, s.history[a].status.isCompleted = true) := by
  let hist' := s.history ++ [rec']
  have hlen : hist'.length = s.history.length + 1 := by simp [hist']
  refine ⟨?_, ?_⟩
  · intro i hi j hj
    have hi' : i < hist'.length := by omega
    have hj' : j < hist'.length := by omega
    constructor
    · rintro ⟨_, _, r, hr, hlt⟩
      exact ⟨hi, hj, r, by simpa [hist', List.getElem_append_left hi] using hr,
        by simpa [hist', List.getElem_append_left hj] using hlt⟩
    · rintro ⟨_, _, r, hr, hlt⟩
      exact ⟨hi', hj', r, by simpa [hist', List.getElem_append_left hi] using hr,
        by simpa [hist', List.getElem_append_left hj] using hlt⟩
  · intro a
    constructor
    · rintro ⟨ha', _, r, hr, _⟩
      have ha_len : a < s.history.length + 1 := hlen ▸ ha'
      by_cases ha : a < s.history.length
      · change (s.history ++ [rec'])[a].status.respStep? = some r at hr
        simp only [List.getElem_append_left ha] at hr
        exact ⟨ha, by simp [OpStatus.isCompleted, hr]⟩
      · obtain rfl : a = s.history.length := by omega
        change (s.history ++ [rec'])[s.history.length].status.respStep? = some r at hr
        simp [hstat, OpStatus.respStep?] at hr
    · rintro ⟨ha, hcomp⟩
      cases hrs : s.history[a].status.respStep? with
      | none => simp [OpStatus.isCompleted, hrs] at hcomp
      | some r =>
        have ha' : a < (s.history ++ [rec']).length := by simp; omega
        have hb' : s.history.length < (s.history ++ [rec']).length := by simp
        exact ⟨ha', hb', r, by simpa [List.getElem_append_left ha] using hrs,
          by simp [hinv, ((hg.hist_wf a ha).2.1 r hrs).2]⟩

private lemma abdGood_prec_complete {P V : Type*} [Fintype P] [LinearOrder P]
    {s : State P (ABDState P V) (ABDMsg P V) V}
    {opTag : ℕ → Option (Tag P)} {v₀ : V} {t : ℕ} (hg : ABDGood v₀ t s opTag)
    {k : ℕ} (hk : k < s.history.length) (hk_pend : s.history[k].status = .pending)
    (stDone : OpStatus V) (hst_resp : stDone.respStep? = some s.step) :
    let hist' := s.history.set k { s.history[k] with status := stDone }
    ∀ a b, prec hist' a b ↔ prec s.history a b := by
  intro hist' a b
  have hlen : hist'.length = s.history.length := List.length_set
  constructor
  · rintro ⟨ha', hb', r, hr, hlt⟩
    have ha : a < s.history.length := hlen ▸ ha'
    have hb : b < s.history.length := hlen ▸ hb'
    have hinv_b : hist'[b].invStep = s.history[b].invStep := by
      by_cases hbk : b = k
      · subst hbk; simp [hist']
      · simp [hist', List.getElem_set_ne (Ne.symm hbk)]
    rw [hinv_b] at hlt
    by_cases hak : a = k
    · subst hak
      simp only [hist', List.getElem_set_self, hst_resp, Option.some.injEq] at hr
      subst hr
      exact False.elim (Nat.lt_asymm hlt (hg.hist_wf b hb).1)
    · simp only [hist', List.getElem_set_ne (Ne.symm hak)] at hr
      exact ⟨ha, hb, r, hr, hlt⟩
  · rintro ⟨ha, hb, r, hr, hlt⟩
    have hak : a ≠ k := by
      intro heq; subst heq
      simp [hk_pend, OpStatus.respStep?] at hr
    refine ⟨hlen.symm ▸ ha, hlen.symm ▸ hb, r, ?_, ?_⟩
    · simpa [hist', List.getElem_set_ne (Ne.symm hak)] using hr
    · by_cases hbk : b = k
      · subst hbk; simpa [hist'] using hlt
      · simpa [hist', List.getElem_set_ne (Ne.symm hbk)] using hlt

private lemma ABDGood.lt_length_of_opTag_some {P V : Type*} [Fintype P] [LinearOrder P]
    {v₀ : V} {t : ℕ} {s : State P (ABDState P V) (ABDMsg P V) V}
    {opTag : ℕ → Option (Tag P)} (hg : ABDGood v₀ t s opTag)
    {i : ℕ} {τ : Tag P} (hτ : opTag i = some τ) : i < s.history.length := by
  by_contra hge
  simp [hg.tag_out i (Nat.le_of_not_lt hge)] at hτ

private lemma ABDGood.pending_info {P V : Type*} [Fintype P] [LinearOrder P]
    {v₀ : V} {t : ℕ} {s : State P (ABDState P V) (ABDMsg P V) V}
    {opTag : ℕ → Option (Tag P)} (hg : ABDGood v₀ t s opTag)
    {p : P} {pend : PendingOp V} (hp : (s.proc p).pending = some pend) :
    ∃ hi : pend.opId < s.history.length,
      s.history[pend.opId].caller = p ∧
      s.history[pend.opId].kind = pend.kind ∧
      s.history[pend.opId].status = .pending := by
  have hps := hg.proc_sync p
  rw [hp] at hps
  cases hph : (s.proc p).state.phase <;> rw [hph] at hps
  · exact False.elim hps
  · exact ⟨hps.1, hps.2.1, hps.2.2.1.trans hps.2.2.2.1.symm, hps.2.2.2.2.1⟩
  · exact ⟨hps.1, hps.2.1, hps.2.2.1.trans hps.2.2.2.1.symm, hps.2.2.2.2.1⟩

private lemma update_proc_repTag_le {P V : Type*} [DecidableEq P] [LinearOrder P]
    (proc : P → ProcState (ABDState P V) V) {actor : P}
    {nextSt : ABDState P V} {newPend : Option (PendingOp V)}
    (hle : (proc actor).state.repTag ≤ nextSt.repTag) (q : P) :
    (proc q).state.repTag ≤ (Function.update proc actor ⟨nextSt, newPend⟩ q).state.repTag := by
  by_cases hq : q = actor
  · subst hq; simpa using hle
  · simp [hq]

section StepProofs

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder P] [DecidableEq V]

omit [DecidableEq V] in
private lemma repTag_le_of_onRecv_eq {v₀ : V} {t : ℕ}
    {dest : P} {st nextSt : ABDState P V} {src : P} {body : ABDMsg P V}
    {outMsgs : Multiset (P × ABDMsg P V)} {resp : Option (OpResp V)}
    (hout : (abdProtocol P V v₀ t).onRecv dest st src body = ⟨nextSt, outMsgs, resp⟩) :
    st.repTag ≤ nextSt.repTag := by
  have hns : (abdOnRecv t dest st src body).nextState = nextSt := congrArg StepOut.nextState hout
  exact hns ▸ abdOnRecv_repTag_mono t dest st src body

omit [DecidableEq P] [DecidableEq V] in
private lemma prec_phase1_step_of_old {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag)
    {actor : P} {baseMsgs : Multiset (Envelope P (ABDMsg P V))}
    {outMsgs : Multiset (P × ABDMsg P V)}
    (hbase_sub : ∀ m ∈ baseMsgs, m ∈ s.msgs)
    (hout_qresp : ∀ dest' reqId rTag rVal,
      (dest', .queryResp reqId rTag rVal) ∈ outMsgs → (s.proc actor).state.repTag ≤ rTag)
    {p : P} {pnd : PendingOp V} {reqId : ℕ} {knd : OpKind V}
    {resp' : Finset P} {bt' : Tag P} {bv' : V}
    (hp1 : (s.proc p).pending = some pnd)
    (hp2 : (s.proc p).state.phase = .phase1 reqId knd resp' bt' bv')
    {a : ℕ} {τ_a : Tag P} (hpr : prec s.history a pnd.opId) (hτ_old : opTag a = some τ_a) :
    ∃ Q : Finset P, Fintype.card P - t ≤ Q.card ∧
      (∀ q ∈ Q, τ_a ≤ (s.proc q).state.repTag) ∧
      (∀ q ∈ Q, ∀ rTag rVal,
        ⟨q, p, .queryResp reqId rTag rVal⟩ ∈
          baseMsgs + outMsgs.map (tagSender actor) → τ_a ≤ rTag) ∧
      (∀ q ∈ Q, q ∈ resp' → τ_a ≤ bt') := by
  obtain ⟨Q, hQc, hQr, hQm, hQresp⟩ :=
    hg.prec_phase1 p pnd reqId knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_old
  refine ⟨Q, hQc, hQr, fun q hq rt rv hm => ?_, hQresp⟩
  rcases Multiset.mem_add.mp hm with hm_old | hm_new
  · exact hQm q hq rt rv (hbase_sub _ hm_old)
  · obtain ⟨⟨dest', body'⟩, hpm, heq⟩ := Multiset.mem_map.mp hm_new
    injection heq with hsrc _ hbody; subst hsrc hbody
    exact (hQr actor hq).trans (hout_qresp dest' reqId rt rv hpm)

omit [DecidableEq V] in
/-- Unified `ABDGood` transition frame lemma across client invocations, Phase-1/Phase-2 transitions,
completions, and replica deliveries at `actor`: discharges unchanged-client (`p ≠ actor`),
old-message, `inv_mono`, and existing-history-entry preservation once, leaving callers only the
transition-specific local obligation at `actor` and any newly added, newly tagged, or newly
completed history entry. -/
private lemma abdGood_step {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag opTag' : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag)
    {actor : P} {nextSt : ABDState P V} {newPend : Option (PendingOp V)}
    {baseMsgs : Multiset (Envelope P (ABDMsg P V))}
    {outMsgs : Multiset (P × ABDMsg P V)}
    {hist' : List (OpRecord P V)}
    (hrep_actor : (s.proc actor).state.repTag ≤ nextSt.repTag)
    (hlen : s.history.length ≤ hist'.length)
    (hlen_ub : hist'.length ≤ s.history.length + 1)
    (hmeta : ∀ (i : ℕ) (hi : i < s.history.length),
      (hist'[i]'(lt_of_lt_of_le hi hlen)).caller = (s.history[i]'hi).caller ∧
      (hist'[i]'(lt_of_lt_of_le hi hlen)).kind = (s.history[i]'hi).kind ∧
      (hist'[i]'(lt_of_lt_of_le hi hlen)).invStep = (s.history[i]'hi).invStep)
    (hother_entry : ∀ (i : ℕ) (hi : i < s.history.length), (s.history[i]'hi).caller ≠ actor →
      hist'[i]'(lt_of_lt_of_le hi hlen) = (s.history[i]'hi) ∧ opTag' i = opTag i)
    (hnew_entry : ∀ (j : ℕ) (hj : j < hist'.length), s.history.length ≤ j →
      (hist'[j]'hj) = ⟨actor, (hist'[j]'hj).kind, s.step, .pending⟩ ∧
        newPend = some ⟨j, (hist'[j]'hj).kind⟩)
    (hprec_old : ∀ i < s.history.length, ∀ j < s.history.length,
      prec hist' i j ↔ prec s.history i j)
    (htag_out : ∀ i, hist'.length ≤ i → opTag' i = none)
    (htag_lt : ∀ i τ, opTag' i = some τ → i < s.history.length)
    (htag_pres : ∀ i τ, opTag i = some τ → opTag' i = some τ)
    (htag_new_pending : ∀ (i : ℕ) (hi : i < s.history.length) τ,
      opTag i = none → opTag' i = some τ → (s.history[i]'hi).status = .pending)
    (hpnd_keep : ∀ (i : ℕ) (hi : i < s.history.length),
      (hist'[i]'(lt_of_lt_of_le hi hlen)).status = .pending →
      (s.proc actor).pending = some ⟨i, (s.history[i]'hi).kind⟩ →
      newPend = some ⟨i, (s.history[i]'hi).kind⟩)
    (hstatus_complete : ∀ (i : ℕ) (hi : i < s.history.length),
      hist'[i]'(lt_of_lt_of_le hi hlen) ≠ (s.history[i]'hi) →
      (opTag' i).isSome = true ∧
        ∃ resp, matchCompletion (s.history[i]'hi).kind resp s.step =
          some (hist'[i]'(lt_of_lt_of_le hi hlen)).status)
    (hbase_sub : ∀ m ∈ baseMsgs, m ∈ s.msgs)
    (hout_qresp : ∀ dest' reqId rTag rVal,
      (dest', .queryResp reqId rTag rVal) ∈ outMsgs → (s.proc actor).state.repTag ≤ rTag)
    (hps_actor : ProcSync t hist' nextSt.nextReqId
      (fun q => (Function.update s.proc actor ⟨nextSt, newPend⟩ q).state.repTag)
      opTag' actor newPend nextSt.phase)
    (hnext_actor : (s.proc actor).state.nextReqId ≤ nextSt.nextReqId)
    (hp1_actor : ∀ reqId, reqId < (s.proc actor).state.nextReqId →
      (∀ knd resp bt bv, (s.proc actor).state.phase = .phase1 reqId knd resp bt bv → False) →
      ∀ knd resp bt bv, nextSt.phase = .phase1 reqId knd resp bt bv → False)
    (hp2_actor : ∀ reqId, reqId < (s.proc actor).state.nextReqId →
      (∀ knd resp bt bv, (s.proc actor).state.phase = .phase1 reqId knd resp bt bv → False) →
      ∀ knd cTag cVal acks, nextSt.phase = .phase2 reqId knd cTag cVal acks →
        ∃ acks₀, (s.proc actor).state.phase = .phase2 reqId knd cTag cVal acks₀)
    (hout_wf : ∀ pm ∈ outMsgs,
      MsgWF v₀
        { msgs := baseMsgs + outMsgs.map (tagSender actor)
          proc := Function.update s.proc actor ⟨nextSt, newPend⟩
          history := hist'
          step := s.step + 1 }
        opTag' actor pm.1 pm.2)
    (hrep_val_actor : TagValidVal v₀ hist' opTag' nextSt.repTag nextSt.repVal)
    (hphase_val_actor : PhaseValValid v₀ hist' opTag' nextSt.phase)
    (hnew_write_tag : ∀ (i : ℕ) (hi : i < hist'.length) v τ,
      opTag i = none → opTag' i = some τ → (hist'[i]'hi).kind = .write v →
      (∃ seq, τ = nextWriteTag seq (hist'[i]'hi).caller) ∧
      (∀ (j : ℕ) (hj : j < s.history.length) vj,
        (s.history[j]'hj).kind = .write vj → opTag j ≠ some τ) ∧
      (∀ (j : ℕ) (_hj : j < hist'.length) τ',
        opTag j = none → opTag' j = some τ' → j = i))
    (hnew_read_val : ∀ (i : ℕ) (hi0 : i < s.history.length) stp r τ,
      (hist'[i]'(lt_of_lt_of_le hi0 hlen)).status = .doneRead stp r →
      (hist'[i]'(lt_of_lt_of_le hi0 hlen)).status ≠ (s.history[i]'hi0).status →
      opTag' i = some τ → TagValidVal v₀ hist' opTag' τ r)
    (hnew_comp_quorum : ∀ (a : ℕ) (ha0 : a < s.history.length) τ_a,
      (hist'[a]'(lt_of_lt_of_le ha0 hlen)).status.isCompleted = true →
      (s.history[a]'ha0).status.isCompleted ≠ true →
      opTag' a = some τ_a →
      ∃ Q : Finset P, Fintype.card P - t ≤ Q.card ∧ ∀ q ∈ Q, τ_a ≤ (s.proc q).state.repTag)
    (hp1_actor_prec : ∀ pend reqId knd resp' bt' bv',
      newPend = some pend →
      nextSt.phase = .phase1 reqId knd resp' bt' bv' →
      ∀ a τ_a, prec hist' a pend.opId → opTag' a = some τ_a →
      ∃ Q : Finset P, Fintype.card P - t ≤ Q.card ∧
        (∀ q ∈ Q, τ_a ≤ (s.proc q).state.repTag) ∧
        (∀ q ∈ Q, ∀ rTag rVal,
          ⟨q, actor, .queryResp reqId rTag rVal⟩ ∈
            baseMsgs + outMsgs.map (tagSender actor) → τ_a ≤ rTag) ∧
        (∀ q ∈ Q, q ∈ resp' → τ_a ≤ bt'))
    (hnew_prec_tag : ∀ (a b : ℕ) (hb : b < s.history.length) τ_a τ_b,
      prec s.history a b → opTag a = some τ_a → opTag b = none → opTag' b = some τ_b →
      PrecTagOrder τ_a τ_b (s.history[b]'hb).kind) :
    ABDGood v₀ t
      { msgs := baseMsgs + outMsgs.map (tagSender actor)
        proc := Function.update s.proc actor ⟨nextSt, newPend⟩
        history := hist'
        step := s.step + 1 } opTag' := by
  set proc' := Function.update s.proc actor ⟨nextSt, newPend⟩
  have hrep_le := update_proc_repTag_le s.proc (newPend := newPend) hrep_actor
  have hsome_pres : ∀ i, (opTag i).isSome = true → (opTag' i).isSome = true := by
    intro i hs
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
    exact Option.isSome_iff_exists.mpr ⟨τ, htag_pres i τ hτ⟩
  have htv_pres : ∀ (i : ℕ) (hi : i < s.history.length) τ,
      opTag i = some τ →
      (hist'[i]'(lt_of_lt_of_le hi hlen)).kind = s.history[i].kind ∧ opTag' i = some τ :=
    fun i hi τ hτ => ⟨(hmeta i hi).2.1, htag_pres i τ hτ⟩
  have htag_cases : ∀ i τ, opTag' i = some τ → opTag i = none ∨ opTag i = some τ := by
    intro i τ hτ
    cases ho : opTag i with
    | none => exact Or.inl rfl
    | some τ₀ => exact Or.inr (by rw [← htag_pres i τ₀ ho, hτ])
  have htag_of_not_pending : ∀ (i : ℕ) (hi : i < s.history.length) τ,
      s.history[i].status ≠ .pending → opTag' i = some τ → opTag i = some τ :=
    fun i hi τ hnp hτ' => (htag_cases i τ hτ').resolve_left fun ho =>
      hnp (htag_new_pending i hi τ ho hτ')
  refine
    { tag_out := htag_out
      hist_wf := fun i hi => by
        dsimp only at hi ⊢
        by_cases hi0 : i < s.history.length
        · by_cases hget : hist'[i] = s.history[i]
          · obtain ⟨h1, h2, h3, h4, h5⟩ := hg.hist_wf i hi0
            refine ⟨hget ▸ Nat.lt_succ_of_lt h1,
              fun r hr => ⟨hget ▸ (h2 r (hget ▸ hr)).1, Nat.lt_succ_of_lt (h2 r (hget ▸ hr)).2⟩,
              fun r v hr => ⟨hget ▸ (h3 r v (hget ▸ hr)).1, hsome_pres i (h3 r v (hget ▸ hr)).2⟩,
              fun r hr => ⟨hget ▸ (h4 r (hget ▸ hr)).1, hsome_pres i (h4 r (hget ▸ hr)).2⟩,
              fun hp => ?_⟩
            have hp0 := h5 (hget ▸ hp)
            by_cases hc : s.history[i].caller = actor
            · rw [hget, hc]; simp only [proc', Function.update_self]
              exact hpnd_keep i hi0 hp (hc ▸ hp0)
            · rw [hget]; simpa [proc', Function.update_of_ne hc] using hp0
          · obtain ⟨hsome_i, resp, hm⟩ := hstatus_complete i hi0 hget
            obtain ⟨h1, _⟩ := hg.hist_wf i hi0
            obtain ⟨_, hk_i, hinv_i⟩ := hmeta i hi0
            rw [hinv_i, hk_i]
            cases hki : s.history[i].kind <;> rcases resp with _ | (_ | _) <;>
              simp only [hki, matchCompletion, Option.some.injEq, reduceCtorEq] at hm <;>
              rw [← hm] <;>
              exact ⟨Nat.lt_succ_of_lt h1, by simp [OpStatus.respStep?, h1.le], by simp [hsome_i],
                by simp [hsome_i], by simp⟩
        · obtain ⟨hrec, hnp⟩ := hnew_entry i hi (Nat.le_of_not_lt hi0)
          have hcaller : hist'[i].caller = actor := congrArg OpRecord.caller hrec
          have hinv : hist'[i].invStep = s.step := congrArg OpRecord.invStep hrec
          have hst : hist'[i].status = .pending := congrArg OpRecord.status hrec
          rw [hinv, hst, hcaller]
          refine ⟨Nat.lt_succ_self _, by rintro _ ⟨⟩, by rintro _ _ ⟨⟩,
            by rintro _ ⟨⟩, fun _ => ?_⟩
          simp [proc', hnp]
      inv_mono := fun i j hij hj => by
        dsimp only at hj ⊢
        by_cases hjl : j < s.history.length
        · have hil := hij.trans hjl
          rw [(hmeta i hil).2.2, (hmeta j hjl).2.2]
          exact hg.inv_mono i j hij hjl
        · have hil : i < s.history.length := by omega
          rw [(hmeta i hil).2.2,
            congrArg OpRecord.invStep (hnew_entry j hj (Nat.le_of_not_lt hjl)).1]
          exact (hg.hist_wf i hil).1
      proc_sync := fun p => by
        change ProcSync t hist' (proc' p).state.nextReqId (fun q => (proc' q).state.repTag)
          opTag' p (proc' p).pending (proc' p).state.phase
        by_cases hp : p = actor
        · subst hp; simpa [proc'] using hps_actor
        · simp only [proc', Function.update_of_ne hp]
          refine procSync_transport hlen le_rfl hrep_le ?_ (hg.proc_sync p)
          intro pend hi _ hc
          obtain ⟨hget, htag_eq⟩ := hother_entry pend.opId hi (hc ▸ hp)
          refine ⟨hget ▸ hc, congrArg OpRecord.kind hget, congrArg OpRecord.status hget, htag_eq,
            fun hprev j hj hjne hjc => ?_⟩
          by_cases hjl : j < s.history.length
          · rw [(hmeta j hjl).1] at hjc
            exact (hprec_old j hjl pend.opId hi).mpr (hprev j hjl hjne hjc)
          · exact False.elim (hp (hjc.symm.trans
              (congrArg OpRecord.caller (hnew_entry j hj (Nat.le_of_not_lt hjl)).1)))
      msg_wf := fun m hm => by
        rcases Multiset.mem_add.mp hm with hm_old | hm_new
        · have hw := hg.msg_wf m (hbase_sub m hm_old)
          have hnext_le (p : P) : (s.proc p).state.nextReqId ≤ (proc' p).state.nextReqId := by
            rcases eq_or_ne p actor with rfl | hp
            · simpa [proc'] using hnext_actor
            · simp [proc', hp]
          have hp1_back (p : P) {rId : ℕ} (hreq : rId < (s.proc p).state.nextReqId)
              (hp1 : ∀ knd rp bt bv, (s.proc p).state.phase = .phase1 rId knd rp bt bv → False)
              (knd : OpKind V) (rp : Finset P) (bt : Tag P) (bv : V)
              (hph' : (proc' p).state.phase = .phase1 rId knd rp bt bv) : False := by
            rcases eq_or_ne p actor with rfl | hp
            · simp only [proc', Function.update_self] at hph'
              exact hp1_actor rId hreq hp1 knd rp bt bv hph'
            · simp only [proc', Function.update_of_ne hp] at hph'; exact hp1 knd rp bt bv hph'
          have hp2_back (p : P) {rId : ℕ} (hreq : rId < (s.proc p).state.nextReqId)
              (hp1 : ∀ knd rp bt bv, (s.proc p).state.phase = .phase1 rId knd rp bt bv → False)
              (knd : OpKind V) (cTag : Tag P) (cVal : V) (acks : Finset P)
              (hph' : (proc' p).state.phase = .phase2 rId knd cTag cVal acks) :
              ∃ acks₀, (s.proc p).state.phase = .phase2 rId knd cTag cVal acks₀ := by
            rcases eq_or_ne p actor with rfl | hp
            · simp only [proc', Function.update_self] at hph'
              exact hp2_actor rId hreq hp1 knd cTag cVal acks hph'
            · simp only [proc', Function.update_of_ne hp] at hph'; exact ⟨acks, hph'⟩
          rcases m with ⟨src, dest, reqId | ⟨reqId, τ, v⟩ | ⟨reqId, τ, v⟩ | reqId⟩
          · exact lt_of_lt_of_le hw (hnext_le src)
          · exact ⟨lt_of_lt_of_le hw.1 (hnext_le dest), tagValidVal_mono hlen htv_pres hw.2⟩
          · obtain ⟨hreq, htv, hp1, hp2⟩ := hw
            refine ⟨lt_of_lt_of_le hreq (hnext_le src), tagValidVal_mono hlen htv_pres htv,
              hp1_back src hreq hp1, fun knd cTag cVal acks hph' => ?_⟩
            obtain ⟨acks₀, hph₀⟩ := hp2_back src hreq hp1 knd cTag cVal acks hph'
            exact hp2 knd cTag cVal acks₀ hph₀
          · obtain ⟨hreq, hp1, hp2⟩ := hw
            refine ⟨lt_of_lt_of_le hreq (hnext_le dest), hp1_back dest hreq hp1,
              fun knd cTag cVal acks hph' => ?_⟩
            obtain ⟨acks₀, hph₀⟩ := hp2_back dest hreq hp1 knd cTag cVal acks hph'
            exact (hp2 knd cTag cVal acks₀ hph₀).trans (hrep_le src)
        · obtain ⟨pm, hpm, rfl⟩ := Multiset.mem_map.mp hm_new
          exact hout_wf pm hpm
      write_unique :=
        ⟨fun i hi v τ hk hτ => by
          dsimp only at hi hk ⊢
          rcases htag_cases i τ hτ with ho | ho
          · exact (hnew_write_tag i hi v τ ho hτ hk).1
          · have hi0 := hg.lt_length_of_opTag_some ho
            rw [(hmeta i hi0).2.1] at hk; rw [(hmeta i hi0).1]
            exact hg.write_unique.1 i hi0 v τ hk ho,
         fun i j hi hj v₁ v₂ τ hk₁ hk₂ hτ₁ hτ₂ => by
          dsimp only at hi hj hk₁ hk₂
          have hold : ∀ k (hk : k < hist'.length) v, hist'[k].kind = .write v → opTag k = some τ →
              ∃ hk0 : k < s.history.length, s.history[k].kind = .write v := fun k _ v hkk ho =>
            have hk0 := hg.lt_length_of_opTag_some ho; ⟨hk0, (hmeta k hk0).2.1 ▸ hkk⟩
          rcases htag_cases i τ hτ₁ with ho₁ | ho₁ <;> rcases htag_cases j τ hτ₂ with ho₂ | ho₂
          · exact ((hnew_write_tag i hi v₁ τ ho₁ hτ₁ hk₁).2.2 j hj τ ho₂ hτ₂).symm
          · obtain ⟨hj0, hk₂⟩ := hold j hj v₂ hk₂ ho₂
            exact absurd ho₂ ((hnew_write_tag i hi v₁ τ ho₁ hτ₁ hk₁).2.1 j hj0 v₂ hk₂)
          · obtain ⟨hi0, hk₁⟩ := hold i hi v₁ hk₁ ho₁
            exact absurd ho₁ ((hnew_write_tag j hj v₂ τ ho₂ hτ₂ hk₂).2.1 i hi0 v₁ hk₁)
          · obtain ⟨hi0, hk₁⟩ := hold i hi v₁ hk₁ ho₁
            obtain ⟨hj0, hk₂⟩ := hold j hj v₂ hk₂ ho₂
            exact hg.write_unique.2 i j hi0 hj0 v₁ v₂ τ hk₁ hk₂ ho₁ ho₂⟩
      val_valid :=
        ⟨fun q => by
          by_cases hqa : q = actor
          · subst hqa; simpa [proc'] using hrep_val_actor
          · simp only [proc', Function.update_of_ne hqa]
            exact tagValidVal_mono hlen htv_pres (hg.val_valid.1 q),
         fun p => by
          by_cases hp : p = actor
          · subst hp; simpa [proc'] using hphase_val_actor
          · simp only [proc', Function.update_of_ne hp]
            exact phaseValValid_mono hlen htv_pres (hg.val_valid.2.1 p),
         fun i _ stp r τ hst hτ => by
          dsimp only at hst ⊢
          have hi0 := htag_lt i τ hτ
          by_cases hst_eq : (hist'[i]'(lt_of_lt_of_le hi0 hlen)).status = s.history[i].status
          · have hst0 : s.history[i].status = .doneRead stp r := hst_eq.symm.trans hst
            have hτ0 := htag_of_not_pending i hi0 τ (by simp [hst0]) hτ
            exact tagValidVal_mono hlen htv_pres (hg.val_valid.2.2 i hi0 stp r τ hst0 hτ0)
          · exact hnew_read_val i hi0 stp r τ hst hst_eq hτ⟩
      completed_quorum := fun a _ τ_a hcomp hτ => by
        dsimp only at hcomp ⊢
        have ha0 := htag_lt a τ_a hτ
        by_cases hc0 : s.history[a].status.isCompleted = true
        · have hτ0 := htag_of_not_pending a ha0 τ_a (by intro hp; simp [hp] at hc0) hτ
          obtain ⟨Q, hQc, hQr⟩ := hg.completed_quorum a ha0 τ_a hc0 hτ0
          exact ⟨Q, hQc, fun q hq => (hQr q hq).trans (hrep_le q)⟩
        · obtain ⟨Q, hQc, hQr⟩ := hnew_comp_quorum a ha0 τ_a hcomp hc0 hτ
          exact ⟨Q, hQc, fun q hq => (hQr q hq).trans (hrep_le q)⟩
      prec_phase1 := fun p pnd reqId knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_a => by
        dsimp only at hp1 hp2 hpr ⊢
        by_cases hp : p = actor
        · subst hp
          simp only [proc', Function.update_self] at hp1 hp2
          obtain ⟨Q, hQc, hQr, hQm, hQresp⟩ :=
            hp1_actor_prec pnd reqId knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_a
          exact ⟨Q, hQc, fun q hq => (hQr q hq).trans (hrep_le q), hQm, hQresp⟩
        · simp only [proc', Function.update_of_ne hp] at hp1 hp2
          have ha0 := htag_lt a τ_a hτ_a
          obtain ⟨hpnd_lt, _⟩ := hg.pending_info hp1
          have hpr0 := (hprec_old a ha0 pnd.opId hpnd_lt).mp hpr
          have ⟨_, _, _, hrs, _⟩ := hpr0
          have hτ0 := htag_of_not_pending a ha0 τ_a
            (by intro hpend; simp [hpend, OpStatus.respStep?] at hrs) hτ_a
          obtain ⟨Q, hQc, hQr, hQm, hQresp⟩ :=
            prec_phase1_step_of_old hg hbase_sub hout_qresp hp1 hp2 hpr0 hτ0
          exact ⟨Q, hQc, fun q hq => (hQr q hq).trans (hrep_le q), hQm, hQresp⟩
      prec_tag := fun a b _ τ_a τ_b hpr hτ_a hτ_b => by
        dsimp only at hpr ⊢
        have ha0 := htag_lt a τ_a hτ_a
        have hb0 := htag_lt b τ_b hτ_b
        have hpr0 := (hprec_old a ha0 b hb0).mp hpr
        have ⟨_, _, _, hrs, _⟩ := hpr0
        have hτ_a0 := htag_of_not_pending a ha0 τ_a
          (by intro hpend; simp [hpend, OpStatus.respStep?] at hrs) hτ_a
        rw [(hmeta b hb0).2.1]
        rcases htag_cases b τ_b hτ_b with ho_b | ho_b
        · exact hnew_prec_tag a b hb0 τ_a τ_b hpr0 hτ_a0 ho_b hτ_b
        · exact hg.prec_tag a b hb0 τ_a τ_b hpr0 hτ_a0 ho_b }

/-- Specialization of `abdGood_step` to `resp = none` deliveries keeping `history` and `opTag`. -/
private lemma abdGood_deliver_same_opTag {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) {e : Envelope P (ABDMsg P V)}
    (nextSt : ABDState P V) (outMsgs : Multiset (P × ABDMsg P V))
    (hout : (abdProtocol P V v₀ t).onRecv e.dest (s.proc e.dest).state e.src e.body =
      ⟨nextSt, outMsgs, none⟩)
    (hout_qresp : ∀ d rId rt rv,
      (d, .queryResp rId rt rv) ∈ outMsgs → (s.proc e.dest).state.repTag ≤ rt)
    (hps_dest : ProcSync t s.history nextSt.nextReqId
      (fun q => (Function.update s.proc e.dest ⟨nextSt, (s.proc e.dest).pending⟩ q).state.repTag)
      opTag e.dest (s.proc e.dest).pending nextSt.phase)
    (hnext_dest : (s.proc e.dest).state.nextReqId ≤ nextSt.nextReqId)
    (hp1_dest : ∀ rId < (s.proc e.dest).state.nextReqId,
      (∀ knd resp bt bv, (s.proc e.dest).state.phase = .phase1 rId knd resp bt bv → False) →
      ∀ knd resp bt bv, nextSt.phase = .phase1 rId knd resp bt bv → False)
    (hp2_dest : ∀ rId < (s.proc e.dest).state.nextReqId,
      (∀ knd resp bt bv, (s.proc e.dest).state.phase = .phase1 rId knd resp bt bv → False) →
      ∀ knd cT cV acks, nextSt.phase = .phase2 rId knd cT cV acks →
        ∃ acks₀, (s.proc e.dest).state.phase = .phase2 rId knd cT cV acks₀)
    (hout_wf : ∀ pm ∈ outMsgs, MsgWF v₀
      ⟨s.msgs.erase e + outMsgs.map (tagSender e.dest),
        Function.update s.proc e.dest ⟨nextSt, (s.proc e.dest).pending⟩, s.history, s.step + 1⟩
      opTag e.dest pm.1 pm.2)
    (hrep_val_dest : TagValidVal v₀ s.history opTag nextSt.repTag nextSt.repVal)
    (hphase_val_dest : PhaseValValid v₀ s.history opTag nextSt.phase)
    (hp1_dest_prec : ∀ pend rId knd resp' bt' bv',
      (s.proc e.dest).pending = some pend → nextSt.phase = .phase1 rId knd resp' bt' bv' →
      ∀ a τ_a, prec s.history a pend.opId → opTag a = some τ_a →
      ∃ Q : Finset P, Fintype.card P - t ≤ Q.card ∧ (∀ q ∈ Q, τ_a ≤ (s.proc q).state.repTag) ∧
        (∀ q ∈ Q, ∀ rt rv,
          ⟨q, e.dest, .queryResp rId rt rv⟩ ∈ s.msgs.erase e + outMsgs.map (tagSender e.dest) →
            τ_a ≤ rt) ∧
        (∀ q ∈ Q, q ∈ resp' → τ_a ≤ bt')) :
    ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag := by
  rw [(abdProtocol P V v₀ t).doDeliver_of_resp_eq_none hout]
  exact abdGood_step (opTag' := opTag) (actor := e.dest) (nextSt := nextSt)
    (newPend := (s.proc e.dest).pending) (baseMsgs := s.msgs.erase e)
    (outMsgs := outMsgs) (hist' := s.history)
    hg (repTag_le_of_onRecv_eq hout) le_rfl (Nat.le_succ _)
    (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ _ => ⟨rfl, rfl⟩)
    (fun _ hj hge => absurd (lt_of_lt_of_le hj hge) (lt_irrefl _))
    (fun _ _ _ _ => Iff.rfl) hg.tag_out (fun _ _ => hg.lt_length_of_opTag_some)
    (fun _ _ h => h) (fun _ _ _ h0 h1 => nomatch h0.symm.trans h1)
    (fun _ _ _ h => h) (fun _ _ hne => False.elim (hne rfl))
    (fun _ => Multiset.mem_of_mem_erase) hout_qresp hps_dest hnext_dest hp1_dest hp2_dest
    hout_wf hrep_val_dest hphase_val_dest (fun _ _ _ _ h0 h1 => nomatch h0.symm.trans h1)
    (fun _ _ _ _ _ _ hne => False.elim (hne rfl)) (fun _ _ _ hc hne => False.elim (hne hc))
    hp1_dest_prec (fun _ _ _ _ _ _ _ h0 h1 => nomatch h0.symm.trans h1)

/-- Preservation of `ABDGood` for any delivery with `resp = none` that leaves `phase` and
`nextReqId` at `e.dest` unchanged (stale messages and replica `.query` / `.store` handlers). -/
private lemma abdGood_deliver_keep_phase {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) {e : Envelope P (ABDMsg P V)}
    (nextSt : ABDState P V) (outMsgs : Multiset (P × ABDMsg P V))
    (hout : (abdProtocol P V v₀ t).onRecv e.dest (s.proc e.dest).state e.src e.body =
      ⟨nextSt, outMsgs, none⟩)
    (hphase_eq : nextSt.phase = (s.proc e.dest).state.phase)
    (hnext_eq : nextSt.nextReqId = (s.proc e.dest).state.nextReqId)
    (hout_wf : ∀ pm ∈ outMsgs, MsgWF v₀
      ⟨s.msgs.erase e + outMsgs.map (tagSender e.dest),
        Function.update s.proc e.dest ⟨nextSt, (s.proc e.dest).pending⟩, s.history, s.step + 1⟩
      opTag e.dest pm.1 pm.2)
    (hout_qresp : ∀ d rId rt rv,
      (d, .queryResp rId rt rv) ∈ outMsgs → (s.proc e.dest).state.repTag ≤ rt)
    (hrep_val_dest : TagValidVal v₀ s.history opTag nextSt.repTag nextSt.repVal) :
    ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag := by
  exact abdGood_deliver_same_opTag hg nextSt outMsgs hout hout_qresp
    (hnext_eq.symm ▸ hphase_eq.symm ▸ procSync_transport le_rfl le_rfl
      (update_proc_repTag_le s.proc (repTag_le_of_onRecv_eq hout))
      (fun _ _ _ hc => ⟨hc, rfl, rfl, rfl, id⟩) (hg.proc_sync e.dest))
    hnext_eq.symm.le
    (fun _ _ hp1 knd resp bt bv hph => hp1 knd resp bt bv (hphase_eq.symm.trans hph))
    (fun _ _ _ _ _ _ acks hph => ⟨acks, hphase_eq.symm.trans hph⟩)
    hout_wf hrep_val_dest (hphase_eq ▸ hg.val_valid.2.1 e.dest)
    (fun _ _ _ _ _ _ hp1 hp2 _ _ hpr hτ =>
      prec_phase1_step_of_old hg (fun _ => Multiset.mem_of_mem_erase) hout_qresp
        hp1 (hphase_eq.symm.trans hp2) hpr hτ)

/-- Helper for a message delivery that leaves local states, `pending`, and `history` unchanged and
emits zero messages (stale or out-of-phase messages). -/
private lemma abdGood_deliver_noop {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) {e : Envelope P (ABDMsg P V)}
    (hnoop : abdOnRecv t e.dest (s.proc e.dest).state e.src e.body =
      ⟨(s.proc e.dest).state, 0, none⟩) :
    ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag := by
  exact abdGood_deliver_keep_phase hg (s.proc e.dest).state 0 hnoop rfl rfl (fun _ hm => nomatch hm)
    (fun _ _ _ _ hm => nomatch hm) (hg.val_valid.1 e.dest)

/-- Helper preserving `ABDGood` when a replica handles `.query` or `.store`. -/
private lemma abdGood_deliver_replica {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) {e : Envelope P (ABDMsg P V)} (he : e ∈ s.msgs)
    (hrep : (∃ reqId, e.body = .query reqId) ∨ (∃ reqId τ v, e.body = .store reqId τ v)) :
    ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag := by
  have he_wf := hg.msg_wf e he
  rcases hrep with ⟨reqId, hb⟩ | ⟨reqId, inTag, inVal, hb⟩
  · rw [hb] at he_wf
    dsimp only [MsgWF] at he_wf
    refine abdGood_deliver_keep_phase hg (s.proc e.dest).state
      {(e.src, .queryResp reqId (s.proc e.dest).state.repTag (s.proc e.dest).state.repVal)}
      (by simp [abdProtocol, hb, abdOnRecv]) rfl rfl ?_ ?_ (hg.val_valid.1 e.dest)
    · intro pm hpm
      rw [Multiset.mem_singleton] at hpm; subst hpm
      exact ⟨by rcases eq_or_ne e.src e.dest with hs | hs <;> [rw [hs]; skip] <;>
        simpa [hs] using he_wf, hg.val_valid.1 e.dest⟩
    · intro _ _ _ _ hm
      simp only [Multiset.mem_singleton, Prod.mk.injEq, ABDMsg.queryResp.injEq] at hm
      exact hm.2.2.1 ▸ le_rfl
  · rw [hb] at he_wf
    obtain ⟨hreq, htv, hp1, hp2⟩ := he_wf
    let nextSt := (abdOnRecv t e.dest (s.proc e.dest).state e.src e.body).nextState
    have hph_nr : nextSt.phase = (s.proc e.dest).state.phase ∧
        nextSt.nextReqId = (s.proc e.dest).state.nextReqId := by
      simp only [nextSt, hb, abdOnRecv]; split_ifs <;> exact ⟨rfl, rfl⟩
    have hsrc :
        let st' := (Function.update s.proc e.dest
          ⟨nextSt, (s.proc e.dest).pending⟩ e.src).state
        st'.phase = (s.proc e.src).state.phase ∧
          st'.nextReqId = (s.proc e.src).state.nextReqId := by
      dsimp only
      rcases eq_or_ne e.src e.dest with hs | hs
      · rw [hs, Function.update_self]; exact hph_nr
      · simp [hs]
    refine abdGood_deliver_keep_phase hg nextSt {(e.src, .ack reqId)}
      (by simp [abdProtocol, hb, abdOnRecv, nextSt]) hph_nr.1 hph_nr.2 ?_
      (fun _ _ _ _ hm => by simp at hm)
      (by simp only [nextSt, hb, abdOnRecv]; split_ifs <;> [exact htv; exact hg.val_valid.1 e.dest])
    intro pm hpm
    rw [Multiset.mem_singleton] at hpm; subst hpm
    refine ⟨hsrc.2.symm ▸ hreq,
      fun knd resp bt bv hph => hp1 knd resp bt bv (hsrc.1.symm.trans hph),
      fun knd cTag cVal acks hph => ?_⟩
    obtain ⟨hcT, _⟩ := hp2 knd cTag cVal acks (hsrc.1.symm.trans hph)
    simp only [Function.update_self, nextSt, hb]
    exact hcT ▸ abdOnRecv_store_le_repTag t e.dest (s.proc e.dest).state e.src reqId inTag inVal

omit [DecidableEq P] [DecidableEq V] in
private lemma pending_of_phase_ne_idle {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) (p : P) (hne : (s.proc p).state.phase ≠ .idle) :
    ∃ pend, (s.proc p).pending = some pend := by
  have hps := hg.proc_sync p
  cases hp : (s.proc p).pending with
  | none =>
    rw [hp] at hps
    cases hph : (s.proc p).state.phase <;> rw [hph] at hps hne
    exacts [absurd rfl hne, hps.elim, hps.elim]
  | some pend => exact ⟨pend, rfl⟩

/-- Phase-2 `(chosenTag, chosenVal)` selected by `dest` upon completing Phase 1 with `(bt, bv)`. -/
private def phase2Choice (dest : P) : OpKind V → Tag P → V → Tag P × V
  | .write v, bt, _ => (nextWriteTag bt.seq dest, v)
  | .read, bt, bv => (bt, bv)

omit [DecidableEq V] in
private lemma abdGood_invoke {v₀ : V} {t : ℕ} (h2t : 2 * t < Fintype.card P)
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) {caller : P} (kind : OpKind V)
    (hpend_none : (s.proc caller).pending = none) :
    ABDGood v₀ t ((abdProtocol P V v₀ t).doInvoke caller kind s) opTag := by
  let reqId := (s.proc caller).state.nextReqId
  let nextSt : ABDState P V :=
    { (s.proc caller).state with
      nextReqId := reqId + 1
      phase := .phase1 reqId kind ∅ (initTag P) v₀ }
  let outMsgs : Multiset (P × ABDMsg P V) := broadcastAll P (.query reqId)
  rw [(abdProtocol P V v₀ t).doInvoke_of_resp_eq_none
    (nextSt := nextSt) (outMsgs := outMsgs) rfl]
  let rec' : OpRecord P V := ⟨caller, kind, s.step, .pending⟩
  obtain ⟨hprec_old, hprec_to_new⟩ := abdGood_prec_append hg rec' rfl rfl
  have hq_pos : 0 < Fintype.card P - t := by omega
  refine abdGood_step (opTag' := opTag) (actor := caller) (nextSt := nextSt)
    (newPend := some ⟨s.history.length, kind⟩) (baseMsgs := s.msgs)
    (outMsgs := outMsgs) (hist' := s.history ++ [rec'])
    hg le_rfl (by simp) (by simp)
    (fun i hi => by simp [List.getElem_append_left hi])
    (fun i hi _ => ⟨List.getElem_append_left hi, rfl⟩)
    (fun j hj hge => by
      have hj_len : j < s.history.length + 1 := by simpa using hj
      obtain rfl : j = s.history.length := by omega
      simp [rec'])
    hprec_old (fun i hi => hg.tag_out i (le_trans (by simp) hi))
    (fun _ _ => hg.lt_length_of_opTag_some) (fun _ _ h => h)
    (fun _ _ _ h0 h1 => nomatch h0.symm.trans h1)
    (fun _ _ _ hp => by rw [hpend_none] at hp; cases hp)
    (fun i hi hne => False.elim (hne (List.getElem_append_left hi)))
    (fun _ hm => hm) (by simp [outMsgs, broadcastAll]) ?_ (Nat.le_succ _)
    (fun _ hreq _ _ _ _ _ hph' => by
      simp only [nextSt, ClientPhase.phase1.injEq] at hph'
      exact Nat.lt_irrefl _ (hph'.1 ▸ hreq))
    (fun _ _ _ _ _ _ _ h => nomatch h)
    (fun pm hpm => by
      simp only [outMsgs, broadcastAll, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
        true_and] at hpm
      obtain ⟨q, rfl⟩ := hpm; simp [MsgWF, nextSt, reqId])
    (tagValidVal_mono (by simp) (fun i hi _ hτ => ⟨by simp [List.getElem_append_left hi], hτ⟩)
      (hg.val_valid.1 caller))
    (Or.inl ⟨rfl, rfl⟩)
    (fun _ _ _ _ h0 h1 => nomatch h0.symm.trans h1)
    (fun i hi0 _ _ _ _ hne => False.elim (hne (by simp [List.getElem_append_left hi0])))
    (fun a ha0 _ hc hne => False.elim (hne (by simpa [List.getElem_append_left ha0] using hc)))
    ?_ (fun _ _ _ _ _ _ _ h0 h1 => nomatch h0.symm.trans h1)
  · refine ⟨by simp, by simp [rec'], by simp [rec'], rfl, by simp [rec'],
      hg.tag_out s.history.length le_rfl, Nat.lt_succ_self _, by simpa using hq_pos, ?_⟩
    intro j hj hjne hjc
    dsimp only at hjne
    have hj_len : j < s.history.length + 1 := by simpa using hj
    have hjl : j < s.history.length := by omega
    rw [List.getElem_append_left hjl] at hjc
    refine (hprec_to_new j).mpr ⟨hjl, ?_⟩
    cases hst : s.history[j].status with
    | doneRead _ _ | doneWrite _ => rfl
    | pending =>
      have hpnd := (hg.hist_wf j hjl).2.2.2.2 hst
      rw [hjc, hpend_none] at hpnd; cases hpnd
  · intro pend rId knd responses bt bv hp_pend hp_ph a τ_a hprec hτ_a
    simp only [nextSt, Option.some.injEq, ClientPhase.phase1.injEq] at hp_pend hp_ph
    subst hp_pend; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hp_ph
    obtain ⟨hal, hcomp_a⟩ := (hprec_to_new a).mp hprec
    obtain ⟨Q, hQcard, hQtag⟩ := hg.completed_quorum a hal τ_a hcomp_a hτ_a
    refine ⟨Q, hQcard, hQtag, fun q _ rTag rVal hmem => ?_, fun _ _ hm => nomatch hm⟩
    rcases Multiset.mem_add.mp hmem with hold | hnew
    · exact False.elim (Nat.lt_irrefl _ (hg.msg_wf _ hold).1)
    · obtain ⟨_, ⟨⟩⟩ := mem_map_tagSender_broadcastAll.mp hnew

/-- Phase-1 quorum transition (`.phase1 → .phase2`): assigns `chosenTag` at `pend.opId`, checks
write-tag freshness across same-caller writes, and converts `prec_phase1` into `prec_tag` via
`quorum_inter_nonempty`. -/
private lemma abdGood_phase1_to_phase2 {v₀ : V} {t : ℕ}
    (h2t : 2 * t < Fintype.card P) {s : State P (ABDState P V) (ABDMsg P V) V}
    {opTag : ℕ → Option (Tag P)} (hg : ABDGood v₀ t s opTag)
    {e : Envelope P (ABDMsg P V)} {rId : ℕ} {rTag : Tag P} {rVal : V}
    (hb : e.body = .queryResp rId rTag rVal)
    {pend : PendingOp V} (hp_dest : (s.proc e.dest).pending = some pend)
    {kind : OpKind V} {responses : Finset P} {bestTag : Tag P} {bestVal : V}
    (hph_dest : (s.proc e.dest).state.phase = .phase1 rId kind responses bestTag bestVal)
    (hquorum : Fintype.card P - t ≤ (insert e.src responses).card)
    (hbestVal' : TagValidVal v₀ s.history opTag
      (if bestTag < rTag then rTag else bestTag)
      (if bestTag < rTag then rVal else bestVal))
    (hresp'_le : ∀ {Q : Finset P} {τ_a : Tag P},
      (∀ q ∈ Q, ∀ rt rv, ⟨q, e.dest, .queryResp rId rt rv⟩ ∈ s.msgs → τ_a ≤ rt) →
      (∀ q ∈ Q, q ∈ responses → τ_a ≤ bestTag) →
      ∀ q ∈ Q, q ∈ insert e.src responses →
        τ_a ≤ (if bestTag < rTag then rTag else bestTag)) :
    ∃ opTag', ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag' := by
  have hps_dest := hg.proc_sync e.dest
  rw [hph_dest, hp_dest] at hps_dest
  obtain ⟨hi_pend, hc_pend, hk_pend, hpk_pend, hst_pend, htag_pend, hreq_lt, _,
    hprev_pend⟩ := hps_dest
  let bestTag' := if bestTag < rTag then rTag else bestTag
  let bestVal' := if bestTag < rTag then rVal else bestVal
  let cv := phase2Choice e.dest kind bestTag' bestVal'
  let chosenTag := cv.1
  let chosenVal := cv.2
  let opTag' := Function.update opTag pend.opId (some chosenTag)
  let nextSt : ABDState P V :=
    { (s.proc e.dest).state with phase := .phase2 rId kind chosenTag chosenVal ∅ }
  let outMsgs : Multiset (P × ABDMsg P V) := broadcastAll P (.store rId chosenTag chosenVal)
  have hq_pos : 0 < Fintype.card P - t := by omega
  have hout : (abdProtocol P V v₀ t).onRecv e.dest (s.proc e.dest).state e.src e.body =
      ⟨nextSt, outMsgs, none⟩ := by
    cases kind <;>
      simp [abdProtocol, hb, abdOnRecv, hph_dest, hquorum, bestTag', bestVal', cv, phase2Choice,
        chosenTag, chosenVal, nextSt, outMsgs]
  have htag_pres : ∀ i τ, opTag i = some τ → opTag' i = some τ := by
    intro i τ hτ
    have hip : i ≠ pend.opId := fun heq => by subst heq; rw [htag_pend] at hτ; cases hτ
    exact (Function.update_of_ne hip _ opTag).trans hτ
  have heq_pend_of_new : ∀ {i τ}, opTag i = none → opTag' i = some τ →
      i = pend.opId ∧ τ = chosenTag := by
    intro i τ h0 h1
    by_cases hip : i = pend.opId
    · subst hip; simp only [opTag', Function.update_self, Option.some.injEq] at h1
      exact ⟨rfl, h1.symm⟩
    · simp only [opTag', Function.update_of_ne hip, h0] at h1; cases h1
  have hprec_all_a : ∀ (a : ℕ) τ_a, prec s.history a pend.opId → opTag a = some τ_a →
      τ_a ≤ bestTag' := by
    intro a τ_a hprec hτ_a
    obtain ⟨Q, hQcard, _, hQmsg, hQresp⟩ :=
      hg.prec_phase1 e.dest pend rId kind responses bestTag bestVal hp_dest hph_dest a τ_a hprec
        hτ_a
    obtain ⟨q, hq_inter⟩ := quorum_inter_nonempty h2t hQcard hquorum
    obtain ⟨hqQ, hqR'⟩ := Finset.mem_inter.mp hq_inter
    exact hresp'_le hQmsg hQresp q hqQ hqR'
  have htv_pres : ∀ (i : ℕ) (hi : i < s.history.length) τ,
      opTag i = some τ → s.history[i].kind = s.history[i].kind ∧ opTag' i = some τ :=
    fun i _ τ hτ => ⟨rfl, htag_pres i τ hτ⟩
  have hchosen_valid : TagValidVal v₀ s.history opTag' chosenTag chosenVal := by
    cases kind with
    | read => exact tagValidVal_mono le_rfl htv_pres hbestVal'
    | write _ => exact Or.inr ⟨pend.opId, hi_pend, hk_pend, Function.update_self ..⟩
  refine ⟨opTag', ?_⟩
  rw [(abdProtocol P V v₀ t).doDeliver_of_resp_eq_none hout]
  refine abdGood_step (opTag' := opTag') (actor := e.dest) (nextSt := nextSt)
    (newPend := (s.proc e.dest).pending) (baseMsgs := s.msgs.erase e)
    (outMsgs := outMsgs) (hist' := s.history)
    hg le_rfl le_rfl (Nat.le_succ _)
    (fun _ _ => ⟨rfl, rfl, rfl⟩)
    (fun i _ hne => ⟨rfl, Function.update_of_ne (by rintro rfl; exact hne hc_pend) _ opTag⟩)
    (fun _ hj hge => absurd (lt_of_lt_of_le hj hge) (lt_irrefl _)) (fun _ _ _ _ => Iff.rfl)
    (fun i hi => (Function.update_of_ne (by omega) _ opTag).trans (hg.tag_out i hi))
    (fun i τ hτ => by
      by_cases hip : i = pend.opId
      · exact hip ▸ hi_pend
      · exact hg.lt_length_of_opTag_some ((Function.update_of_ne hip _ opTag).symm.trans hτ))
    htag_pres
    (fun _ _ _ h0 h1 => (heq_pend_of_new h0 h1).1 ▸ hst_pend)
    (fun _ _ _ h => h) (fun _ _ hne => False.elim (hne rfl))
    (fun _ => Multiset.mem_of_mem_erase) (by simp [outMsgs, broadcastAll]) ?_ le_rfl
    (fun _ _ _ _ _ _ _ h => nomatch h) ?_ ?_
    (tagValidVal_mono le_rfl htv_pres (hg.val_valid.1 e.dest)) hchosen_valid ?_
    (fun _ _ _ _ _ _ hne => False.elim (hne rfl))
    (fun _ _ _ hc hne => False.elim (hne hc))
    (fun _ _ _ _ _ _ _ h => nomatch h) ?_
  · rw [hp_dest]
    exact ⟨hi_pend, hc_pend, hk_pend, hpk_pend, hst_pend, Function.update_self .., hreq_lt,
      by simpa using hq_pos, fun _ hm => False.elim (Finset.notMem_empty _ hm), hprev_pend⟩
  · intro _ _ hp1 _ _ _ _ hph'
    simp only [nextSt, ClientPhase.phase2.injEq] at hph'
    exact False.elim (hp1 kind responses bestTag bestVal (hph'.1 ▸ hph_dest))
  · intro pm hpm
    simp only [outMsgs, broadcastAll, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
      true_and] at hpm
    obtain ⟨q, rfl⟩ := hpm
    dsimp only [MsgWF, nextSt]; rw [Function.update_self]
    refine ⟨hreq_lt, hchosen_valid, (fun _ _ _ _ h => nomatch h), fun _ _ _ _ hph => ?_⟩
    injection hph with _ _ hcT hcV _; exact ⟨hcT, hcV⟩
  · intro i _ v τ h0 h1 hk
    obtain ⟨rfl, rfl⟩ := heq_pend_of_new h0 h1
    have hkw_kind : kind = .write v := hk_pend.symm.trans hk
    have hc_eq : chosenTag = nextWriteTag bestTag'.seq e.dest := by
      simp [chosenTag, cv, phase2Choice, hkw_kind]
    refine ⟨⟨bestTag'.seq, hc_pend ▸ hc_eq⟩, fun k hk_lt vk hkw hτk => ?_,
      fun _ _ _ hj0 hj1 => (heq_pend_of_new hj0 hj1).1⟩
    have hkne : k ≠ pend.opId := fun heq => by subst heq; rw [htag_pend] at hτk; cases hτk
    obtain ⟨seq_k, hτk_eq⟩ := hg.write_unique.1 k hk_lt vk chosenTag hkw hτk
    have hwriter := congrArg Tag.writer (hτk_eq.symm.trans hc_eq)
    simp only [nextWriteTag_writer, WithBot.coe_inj] at hwriter
    have hle := hprec_all_a k chosenTag (hprev_pend k hk_lt hkne hwriter) hτk
    exact lt_irrefl chosenTag (hc_eq ▸ lt_nextWriteTag_of_seq_le (seq_le_of_le hle) e.dest)
  · intro a b _ τ_a τ_b hpr hτ_a hb0 hb1
    obtain ⟨rfl, rfl⟩ := heq_pend_of_new hb0 hb1
    have hle := hprec_all_a a τ_a hpr hτ_a
    rw [hk_pend]
    cases kind with
    | read => exact hle
    | write _ => exact lt_nextWriteTag_of_seq_le (seq_le_of_le hle) e.dest

/-- Helper preserving `ABDGood` when a client receives `.queryResp`. -/
private lemma abdGood_deliver_queryResp {v₀ : V} {t : ℕ}
    (h2t : 2 * t < Fintype.card P) {s : State P (ABDState P V) (ABDMsg P V) V}
    {opTag : ℕ → Option (Tag P)} (hg : ABDGood v₀ t s opTag)
    {e : Envelope P (ABDMsg P V)} (he : e ∈ s.msgs) {rId : ℕ} {rTag : Tag P} {rVal : V}
    (hb : e.body = .queryResp rId rTag rVal) :
    ∃ opTag', ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag' := by
  have he_wf := hg.msg_wf e he; rw [hb] at he_wf
  obtain ⟨_, hrTagVal⟩ := he_wf
  cases hph_dest : (s.proc e.dest).state.phase with
  | idle | phase2 _ _ _ _ _ =>
    exact ⟨opTag, abdGood_deliver_noop hg (by simp [hb, abdOnRecv, hph_dest])⟩
  | phase1 reqId kind responses bestTag bestVal =>
    by_cases hmatch : rId = reqId
    · subst hmatch
      obtain ⟨pend, hp_dest⟩ := pending_of_phase_ne_idle hg e.dest (by simp [hph_dest])
      let responses' := insert e.src responses
      let bestTag' := if bestTag < rTag then rTag else bestTag
      let bestVal' := if bestTag < rTag then rVal else bestVal
      have hbt_le : bestTag ≤ bestTag' := by
        dsimp only [bestTag']; split_ifs with hlt <;> [exact le_of_lt hlt; exact le_rfl]
      have hrTag_le : rTag ≤ bestTag' := by
        dsimp only [bestTag']; split_ifs with hlt <;> [exact le_rfl; exact le_of_not_gt hlt]
      have hbestVal' : TagValidVal v₀ s.history opTag bestTag' bestVal' := by
        dsimp only [bestTag', bestVal']
        split_ifs
        · exact hrTagVal
        · have hv := hg.val_valid.2.1 e.dest; rwa [hph_dest] at hv
      have hresp'_le : ∀ {Q : Finset P} {τ_a : Tag P},
          (∀ q ∈ Q, ∀ rt rv, ⟨q, e.dest, .queryResp rId rt rv⟩ ∈ s.msgs → τ_a ≤ rt) →
          (∀ q ∈ Q, q ∈ responses → τ_a ≤ bestTag) →
          ∀ q ∈ Q, q ∈ responses' → τ_a ≤ bestTag' := by
        intro Q τ_a hQm hQresp q hq hqR'
        rcases Finset.mem_insert.mp hqR' with rfl | hqR
        · have he_eq : (⟨e.src, e.dest, .queryResp rId rTag rVal⟩ :
              Envelope P (ABDMsg P V)) = e := by ext <;> simp [hb]
          exact (hQm e.src hq rTag rVal (he_eq ▸ he)).trans hrTag_le
        · exact (hQresp q hq hqR).trans hbt_le
      by_cases hquorum : Fintype.card P - t ≤ responses'.card
      · exact abdGood_phase1_to_phase2 h2t hg hb hp_dest hph_dest hquorum hbestVal' hresp'_le
      · have hps_dest := hg.proc_sync e.dest
        rw [hph_dest, hp_dest] at hps_dest
        obtain ⟨hi_pend, hc_pend, hk_pend, hpk_pend, hst_pend, htag_pend, hreq_lt, _,
          hprev_pend⟩ := hps_dest
        let nextSt : ABDState P V :=
          { (s.proc e.dest).state with phase := .phase1 rId kind responses' bestTag' bestVal' }
        have hout : (abdProtocol P V v₀ t).onRecv e.dest (s.proc e.dest).state e.src e.body =
            ⟨nextSt, 0, none⟩ := by
          simp [abdProtocol, hb, abdOnRecv, hph_dest, responses', bestTag', bestVal', hquorum,
            nextSt]
        refine ⟨opTag, abdGood_deliver_same_opTag hg nextSt 0 hout
          (fun _ _ _ _ hm => nomatch hm) ?_ le_rfl ?_
          (fun _ _ _ _ _ _ _ h => nomatch h) (fun _ hm => nomatch hm)
          (hg.val_valid.1 e.dest) hbestVal' ?_⟩
        · rw [hp_dest]
          exact ⟨hi_pend, hc_pend, hk_pend, hpk_pend, hst_pend, htag_pend, hreq_lt,
            Nat.lt_of_not_le hquorum, hprev_pend⟩
        · intro _ _ hp1 _ _ _ _ hph'
          simp only [nextSt, ClientPhase.phase1.injEq] at hph'
          exact hp1 kind responses bestTag bestVal (hph'.1 ▸ hph_dest)
        · intro pnd reqId' knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_a
          rw [hp_dest, Option.some.injEq] at hp1; subst hp1
          simp only [nextSt, ClientPhase.phase1.injEq] at hp2
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hp2
          obtain ⟨Q, hQc, hQr, hQm, hQresp⟩ :=
            hg.prec_phase1 e.dest pend rId kind responses bestTag bestVal hp_dest hph_dest
              a τ_a hpr hτ_a
          refine ⟨Q, hQc, hQr, fun q hq rt rv hm => ?_, hresp'_le hQm hQresp⟩
          simp only [Multiset.map_zero, add_zero] at hm
          exact hQm q hq rt rv (Multiset.mem_of_mem_erase hm)
    · exact ⟨opTag, abdGood_deliver_noop hg (by simp [hb, abdOnRecv, hph_dest, hmatch])⟩

/-- Phase-2 quorum completion (`.phase2 → .idle`): marks `pend.opId` completed in `history`,
records its acknowledged replica quorum in `completed_quorum`, and resets `e.dest` to `.idle`. -/
private lemma abdGood_phase2_complete {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) {e : Envelope P (ABDMsg P V)} {rId : ℕ}
    (hb : e.body = .ack rId)
    {pend : PendingOp V} (hp_dest : (s.proc e.dest).pending = some pend)
    {kind : OpKind V} {chosenTag : Tag P} {chosenVal : V} {acks : Finset P}
    (hph_dest : (s.proc e.dest).state.phase = .phase2 rId kind chosenTag chosenVal acks)
    (hquorum : Fintype.card P - t ≤ (insert e.src acks).card)
    (hacks'_le : ∀ q ∈ insert e.src acks, chosenTag ≤ (s.proc q).state.repTag)
    (hchosen_valid : TagValidVal v₀ s.history opTag chosenTag chosenVal) :
    ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag := by
  have hps_dest := hg.proc_sync e.dest
  rw [hph_dest, hp_dest] at hps_dest
  obtain ⟨hi_pend, hc_pend, hk_pend, hpk_pend, hst_pend, htag_pend, _, _, _, _⟩ := hps_dest
  let outResp := match kind with
    | .read => OpResp.readRet chosenVal
    | .write _ => OpResp.writeAck
  let stDone := match kind with
    | .read => OpStatus.doneRead s.step chosenVal
    | .write _ => OpStatus.doneWrite s.step
  let nextSt : ABDState P V := { (s.proc e.dest).state with phase := .idle }
  have hmatch_comp : matchCompletion pend.kind (some outResp) s.step = some stDone := by
    rw [hpk_pend]; cases kind <;> rfl
  have hout_step : (abdProtocol P V v₀ t).onRecv e.dest (s.proc e.dest).state e.src e.body =
      ⟨nextSt, 0, some outResp⟩ := by
    simp [abdProtocol, hb, abdOnRecv, hph_dest, hquorum, outResp, nextSt]
  rw [(abdProtocol P V v₀ t).doDeliver_of_complete hout_step hp_dest hmatch_comp hi_pend]
  set hist' := s.history.set pend.opId { s.history[pend.opId] with status := stDone }
  have hlen_eq : hist'.length = s.history.length := List.length_set
  have hmeta_eq : ∀ (i : ℕ) (hi : i < s.history.length),
      (hist'[i]'(hlen_eq.symm ▸ hi)).caller = s.history[i].caller ∧
      (hist'[i]'(hlen_eq.symm ▸ hi)).kind = s.history[i].kind ∧
      (hist'[i]'(hlen_eq.symm ▸ hi)).invStep = s.history[i].invStep := by
    intro i _
    by_cases hip : i = pend.opId
    · subst hip; simp [hist']
    · simp [hist', List.getElem_set_ne (Ne.symm hip)]
  have htv_pres : ∀ (j : ℕ) (hj : j < s.history.length) τ,
      opTag j = some τ →
      (hist'[j]'(hlen_eq.symm ▸ hj)).kind = s.history[j].kind ∧ opTag j = some τ :=
    fun j hj _ hτ' => ⟨(hmeta_eq j hj).2.1, hτ'⟩
  have hstDone_resp : stDone.respStep? = some s.step := by cases kind <;> rfl
  have hprec_eq := abdGood_prec_complete hg hi_pend hst_pend stDone hstDone_resp
  refine abdGood_step (opTag' := opTag) (actor := e.dest) (nextSt := nextSt)
    (newPend := none) (baseMsgs := s.msgs.erase e)
    (outMsgs := 0) (hist' := hist')
    hg le_rfl hlen_eq.symm.le (hlen_eq ▸ Nat.le_succ _) hmeta_eq
    (fun i _ hne => ⟨by
      have hip : pend.opId ≠ i := by rintro rfl; exact hne hc_pend
      simp [hist', List.getElem_set_ne hip], rfl⟩)
    (fun _ hj hge => absurd (lt_of_lt_of_le (hlen_eq ▸ hj) hge) (lt_irrefl _))
    (fun i _ j _ => hprec_eq i j)
    (hlen_eq ▸ hg.tag_out) (fun _ _ => hg.lt_length_of_opTag_some) (fun _ _ h => h)
    (fun _ _ _ h0 h1 => nomatch h0.symm.trans h1) ?_ ?_
    (fun _ => Multiset.mem_of_mem_erase) (fun _ _ _ _ hm => nomatch hm)
    trivial le_rfl (fun _ _ _ _ _ _ _ h => nomatch h) (fun _ _ _ _ _ _ _ h => nomatch h)
    (fun _ hm => nomatch hm) (tagValidVal_mono hlen_eq.symm.le htv_pres (hg.val_valid.1 e.dest))
    trivial (fun _ _ _ _ h0 h1 => nomatch h0.symm.trans h1) ?_ ?_
    (fun _ _ _ _ _ _ _ h => nomatch h)
    (fun _ _ _ _ _ _ _ h0 h1 => nomatch h0.symm.trans h1)
  · intro i _ hpend_i hp0
    rw [hp_dest, Option.some.injEq] at hp0
    have hip : pend.opId = i := congrArg PendingOp.opId hp0
    subst hip
    simp only [hist', List.getElem_set_self] at hpend_i
    dsimp only [stDone] at hpend_i
    cases kind <;> cases hpend_i
  · intro i _ hne
    have hip : i = pend.opId := by
      by_contra hne_i; exact hne (by simp [hist', List.getElem_set_ne (Ne.symm hne_i)])
    subst hip
    exact ⟨by simp [htag_pend], some outResp,
      by simpa [hist', hk_pend, ← hpk_pend] using hmatch_comp⟩
  · intro i _ stp r τ hst hne hτ
    have hip : i = pend.opId := by
      by_contra hne_i; exact hne (by simp [hist', List.getElem_set_ne (Ne.symm hne_i)])
    subst hip
    simp only [hist', List.getElem_set_self] at hst; dsimp only [stDone] at hst
    cases kind with
    | write _ => cases hst
    | read =>
      injection hst with _ hr_eq; subst hr_eq
      rw [htag_pend, Option.some.injEq] at hτ; subst hτ
      exact tagValidVal_mono hlen_eq.symm.le htv_pres hchosen_valid
  · intro a _ τ_a hcomp hne hτ
    have hap : a = pend.opId := by
      by_contra hne_a
      exact hne (by simpa [hist', List.getElem_set_ne (Ne.symm hne_a)] using hcomp)
    subst hap
    rw [htag_pend, Option.some.injEq] at hτ; subst hτ
    exact ⟨insert e.src acks, hquorum, hacks'_le⟩

/-- Helper preserving `ABDGood` when a client receives `.ack`. -/
private lemma abdGood_deliver_ack {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) {e : Envelope P (ABDMsg P V)} (he : e ∈ s.msgs)
    {rId : ℕ} (hb : e.body = .ack rId) :
    ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag := by
  cases hph_dest : (s.proc e.dest).state.phase with
  | idle | phase1 _ _ _ _ _ =>
    exact abdGood_deliver_noop hg (by simp [hb, abdOnRecv, hph_dest])
  | phase2 reqId kind chosenTag chosenVal acks =>
    by_cases hmatch : rId = reqId
    · subst hmatch
      obtain ⟨pend, hp_dest⟩ := pending_of_phase_ne_idle hg e.dest (by simp [hph_dest])
      have hps_dest := hg.proc_sync e.dest
      rw [hph_dest, hp_dest] at hps_dest
      obtain ⟨hi_pend, hc_pend, hk_pend, hpk_pend, hst_pend, htag_pend, hreq_lt, _,
        hacks_le, hprev_pend⟩ := hps_dest
      have he_wf := hg.msg_wf e he; rw [hb] at he_wf
      let acks' := insert e.src acks
      have hacks'_le : ∀ q ∈ acks', chosenTag ≤ (s.proc q).state.repTag := by
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq_old
        · exact he_wf.2.2 kind chosenTag chosenVal acks hph_dest
        · exact hacks_le q hq_old
      have hchosen_valid : TagValidVal v₀ s.history opTag chosenTag chosenVal := by
        have hv := hg.val_valid.2.1 e.dest; rwa [hph_dest] at hv
      by_cases hquorum : Fintype.card P - t ≤ acks'.card
      · exact abdGood_phase2_complete hg hb hp_dest hph_dest hquorum hacks'_le hchosen_valid
      · let nextSt : ABDState P V :=
          { (s.proc e.dest).state with phase := .phase2 rId kind chosenTag chosenVal acks' }
        have hout : (abdProtocol P V v₀ t).onRecv e.dest (s.proc e.dest).state e.src e.body =
            ⟨nextSt, 0, none⟩ := by
          simp [abdProtocol, hb, abdOnRecv, hph_dest, acks', hquorum, nextSt]
        refine abdGood_deliver_same_opTag hg nextSt 0 hout
          (fun _ _ _ _ hm => nomatch hm) ?_ le_rfl
          (fun _ _ _ _ _ _ _ h => nomatch h) ?_ (fun _ hm => nomatch hm)
          (hg.val_valid.1 e.dest) hchosen_valid (fun _ _ _ _ _ _ _ h => nomatch h)
        · rw [hp_dest]
          exact ⟨hi_pend, hc_pend, hk_pend, hpk_pend, hst_pend, htag_pend, hreq_lt,
            Nat.lt_of_not_le hquorum,
            fun q hq => (hacks'_le q hq).trans
              (update_proc_repTag_le s.proc (nextSt := nextSt) (newPend := some pend) le_rfl q),
            hprev_pend⟩
        · intro _ _ _ _ _ _ _ hph'
          simp only [nextSt, ClientPhase.phase2.injEq] at hph'
          obtain ⟨rfl, rfl, rfl, rfl, _⟩ := hph'
          exact ⟨acks, hph_dest⟩
    · exact abdGood_deliver_noop hg (by simp [hb, abdOnRecv, hph_dest, hmatch])

private lemma reachable_abdGood {v₀ : V} {t : ℕ} (h2t : 2 * t < Fintype.card P)
    {s : State P (ABDState P V) (ABDMsg P V) V} (hr : (abdProtocol P V v₀ t).Reachable s) :
    ∃ opTag, ABDGood v₀ t s opTag := by
  obtain ⟨xl, hxl⟩ := hr
  have hinv : (abdProtocol P V v₀ t).lts.TrInv (fun st => ∃ opTag, ABDGood v₀ t st opTag) := by
    rintro u a u' htr ⟨opTag, hg⟩
    cases a with
    | stutter => obtain rfl := htr; exact ⟨opTag, hg⟩
    | invoke caller kind =>
      obtain ⟨hp, rfl⟩ := htr
      exact ⟨opTag, abdGood_invoke h2t hg kind hp⟩
    | deliver e =>
      obtain ⟨he, rfl⟩ := htr
      cases hb : e.body with
      | query reqId =>
        exact ⟨opTag, abdGood_deliver_replica hg he (Or.inl ⟨reqId, hb⟩)⟩
      | store reqId τ v =>
        exact ⟨opTag, abdGood_deliver_replica hg he (Or.inr ⟨reqId, τ, v, hb⟩)⟩
      | queryResp rId rTag rVal =>
        exact abdGood_deliver_queryResp h2t hg he hb
      | ack rId =>
        exact ⟨opTag, abdGood_deliver_ack hg he hb⟩
  exact LTS.mtrInv_of_trInv hinv _ _ _ hxl ⟨fun _ => none, abdGood_start⟩

end StepProofs

/-! ### Explicit linearization order by `(tag, isRead, opId)` -/

/-- Lexicographic key `(tag, (isRead, opId))` ordering ABD operations: writes precede reads at the
same tag, and distinct reads at the same tag are ordered by invocation index `opId`. -/
private def abdLinKey {P V : Type*} (opTag : ℕ → Option (Tag P)) (hist : List (OpRecord P V))
    (i : ℕ) : Tag P ×ₗ Bool ×ₗ ℕ :=
  toLex ((opTag i).getD (initTag P),
    toLex ((hist[i]?.map (fun r => r.kind.isRead)).getD false, i))

private lemma abdLinKey_injective {P V : Type*} {opTag : ℕ → Option (Tag P)}
    {hist : List (OpRecord P V)} : Function.Injective (abdLinKey opTag hist) := by
  intro i j heq
  exact congrArg (fun x => (ofLex (ofLex x).2).2) heq

private lemma abdLinKey_lt_of_tag_lt {P V : Type*} [LinearOrder P]
    {opTag : ℕ → Option (Tag P)} {hist : List (OpRecord P V)}
    {i j : ℕ} {τ₁ τ₂ : Tag P} (h₁ : opTag i = some τ₁) (h₂ : opTag j = some τ₂)
    (hlt : τ₁ < τ₂) : abdLinKey opTag hist i < abdLinKey opTag hist j := by
  unfold abdLinKey
  rw [h₁, h₂, Option.getD_some, Option.getD_some, Prod.Lex.toLex_lt_toLex]
  exact Or.inl hlt

private lemma abdLinKey_write_lt_read {P V : Type*} [LinearOrder P]
    {opTag : ℕ → Option (Tag P)} {hist : List (OpRecord P V)}
    {w r : ℕ} (hw : w < hist.length) (hr : r < hist.length) {v : V}
    (hkw : hist[w].kind = .write v) (hkr : hist[r].kind = .read)
    {τ_w τ_r : Tag P} (h₁ : opTag w = some τ_w) (h₂ : opTag r = some τ_r)
    (hle : τ_w ≤ τ_r) : abdLinKey opTag hist w < abdLinKey opTag hist r := by
  rcases lt_or_eq_of_le hle with hlt | rfl
  · exact abdLinKey_lt_of_tag_lt h₁ h₂ hlt
  · unfold abdLinKey
    rw [h₁, h₂, List.getElem?_eq_getElem hw, List.getElem?_eq_getElem hr]
    simp only [Option.getD_some, Option.map_some, hkw, hkr, OpKind.isRead,
      Prod.Lex.toLex_lt_toLex, lt_self_iff_false, false_or, true_and]
    exact Or.inl (by decide)

private lemma registerValAfter_reads {P V : Type*} {cur : V} {hist : List (OpRecord P V)}
    {l : List ℕ} (hreads : ∀ x ∈ l, ∃ hx : x < hist.length, hist[x].kind = .read) :
    registerValAfter cur hist l = cur := by
  induction l generalizing cur with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hx, hkx⟩ := hreads x List.mem_cons_self
    simp only [registerValAfter_cons, List.getElem?_eq_getElem hx, hkx]
    exact ih fun y hy => hreads y (List.mem_cons_of_mem x hy)

private lemma pairwise_lt_index_of_key_lt {α β : Type*} [Preorder β] {key : α → β}
    {seq : List α} (hsorted : seq.Pairwise fun a b => key a < key b)
    {i j : ℕ} (hi : i < seq.length) (hj : j < seq.length)
    (hlt : key seq[i] < key seq[j]) : i < j := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact h
  · exact False.elim (lt_irrefl _ hlt)
  · exact False.elim (lt_asymm hlt (List.pairwise_iff_getElem.mp hsorted j i hj hi h))

private lemma abdLinKey_lt_of_prec {P V : Type*} [Fintype P] [LinearOrder P]
    {v₀ : V} {t : ℕ} {s : State P (ABDState P V) (ABDMsg P V) V}
    {opTag : ℕ → Option (Tag P)} (hg : ABDGood v₀ t s opTag)
    {a b : ℕ} {τ_a τ_b : Tag P} (hpr : prec s.history a b)
    (hτ_a : opTag a = some τ_a) (hτ_b : opTag b = some τ_b) :
    abdLinKey opTag s.history a < abdLinKey opTag s.history b := by
  obtain ⟨ha_lt, hb_lt, r, hr, hlt⟩ := hpr
  have hpt := hg.prec_tag a b hb_lt τ_a τ_b ⟨ha_lt, hb_lt, r, hr, hlt⟩ hτ_a hτ_b
  have hinv_lt : s.history[a].invStep < s.history[b].invStep :=
    lt_of_le_of_lt (((hg.hist_wf a ha_lt).2.1 r hr).1) hlt
  have hab_idx : a < b := by
    rcases lt_trichotomy a b with h | rfl | h
    · exact h
    · exact False.elim (Nat.lt_irrefl _ hinv_lt)
    · exact False.elim (Nat.lt_asymm hinv_lt (hg.inv_mono b a h ha_lt))
  cases hkb : s.history[b].kind with
  | write _ =>
    rw [hkb] at hpt
    exact abdLinKey_lt_of_tag_lt hτ_a hτ_b hpt
  | read =>
    rw [hkb] at hpt
    cases hka : s.history[a].kind with
    | write _ => exact abdLinKey_write_lt_read ha_lt hb_lt hka hkb hτ_a hτ_b hpt
    | read =>
      rcases lt_or_eq_of_le hpt with hlt_tag | rfl
      · exact abdLinKey_lt_of_tag_lt hτ_a hτ_b hlt_tag
      · unfold abdLinKey
        rw [hτ_a, hτ_b, List.getElem?_eq_getElem ha_lt, List.getElem?_eq_getElem hb_lt]
        simp only [Option.getD_some, Option.map_some, hka, hkb, OpKind.isRead,
          Prod.Lex.toLex_lt_toLex, lt_self_iff_false, false_or, true_and]
        exact hab_idx

/-- Independent cardinality-quorum envelope safety specialization (`abd_linearizable`), **after**
[LynchShvartsman1997], §4.1–4.2 (and not the cited Theorem 4.5 or [AttiyaBarNoyDolev1995]
Theorem 4.9 endpoint): when `2 * t < Fintype.card P`, every state `s` reachable under
`abdProtocol P V v₀ t` satisfies `Linearizable v₀ s.history`. Whereas [LynchShvartsman1997]
(§4.1–4.2, Theorem 4.5) proves atomicity over separate fixed read/write quorum families, a
broadcast abstraction, and a per-processor client request queue, this theorem proves
linearizability for Lean's concrete `(n - t)`-cardinality quorum envelope protocol with idle-only
client invocations. -/
theorem abd_linearizable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder P] [DecidableEq V]
    {t : ℕ} (h2t : 2 * t < Fintype.card P) (v₀ : V)
    {s : State P (ABDState P V) (ABDMsg P V) V}
    (hr : (abdProtocol P V v₀ t).Reachable s) : Linearizable v₀ s.history := by
  obtain ⟨opTag, hg⟩ := reachable_abdGood h2t hr
  let cand := (List.range s.history.length).filter fun i =>
    (opTag i).isSome && decide (∃ hi : i < s.history.length, s.history[i].isEligible)
  let leKey : ℕ → ℕ → Bool := fun i j =>
    decide (abdLinKey opTag s.history i ≤ abdLinKey opTag s.history j)
  let seq := cand.mergeSort leKey
  have hperm : seq.Perm cand := List.mergeSort_perm cand leKey
  have hnd : seq.Nodup := hperm.nodup_iff.mpr (List.Nodup.filter _ List.nodup_range)
  have hmem_seq : ∀ i, i ∈ seq ↔
      ∃ hi : i < s.history.length, (opTag i).isSome = true ∧ s.history[i].isEligible := by
    intro i
    rw [hperm.mem_iff]
    simp only [cand, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨hi, hsome, _, hel⟩ => ⟨hi, hsome, hel⟩,
      fun ⟨hi, hsome, hel⟩ => ⟨hi, hsome, hi, hel⟩⟩
  have hsorted_le : List.Pairwise (fun a b => leKey a b = true) seq :=
    List.pairwise_mergeSort
      (fun a b c hab hbc => by
        simp only [leKey, decide_eq_true_eq] at hab hbc ⊢; exact hab.trans hbc)
      (fun a b => by
        simp only [leKey, Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
      cand
  have hsorted : List.Pairwise
      (fun a b => abdLinKey opTag s.history a < abdLinKey opTag s.history b) seq := by
    have hnd_get := List.pairwise_iff_getElem.mp hnd
    rw [List.pairwise_iff_getElem] at hsorted_le ⊢
    intro i j hi hj hij
    have hle : abdLinKey opTag s.history seq[i] ≤ abdLinKey opTag s.history seq[j] := by
      simpa [leKey] using hsorted_le i j hi hj hij
    exact lt_of_le_of_ne hle fun heq => hnd_get i j hi hj hij (abdLinKey_injective heq)
  refine ⟨seq, hnd, ?_, ?_, ?_⟩
  · intro i hi hcomp
    rw [hmem_seq]
    obtain ⟨_, _, hdr, hdw, _⟩ := hg.hist_wf i hi
    cases hst : s.history[i].status with
    | pending => simp [hst] at hcomp
    | doneRead stp rv =>
      obtain ⟨hk, hsome⟩ := hdr stp rv hst
      exact ⟨hi, hsome, by simp [OpRecord.isEligible, hk, hst]⟩
    | doneWrite stp =>
      obtain ⟨⟨vw, hk⟩, hsome⟩ := hdw stp hst
      exact ⟨hi, hsome, by simp [OpRecord.isEligible, hk, hst]⟩
  · intro a ha b hb hpr
    obtain ⟨_, hsome_a, _⟩ := (hmem_seq a).mp ha
    obtain ⟨_, hsome_b, _⟩ := (hmem_seq b).mp hb
    obtain ⟨τ_a, hτ_a⟩ := Option.isSome_iff_exists.mp hsome_a
    obtain ⟨τ_b, hτ_b⟩ := Option.isSome_iff_exists.mp hsome_b
    have hia := List.idxOf_lt_length_of_mem ha
    have hib := List.idxOf_lt_length_of_mem hb
    exact pairwise_lt_index_of_key_lt hsorted hia hib
      (by simpa [List.getElem_idxOf] using abdLinKey_lt_of_prec hg hpr hτ_a hτ_b)
  · rw [seqValid_iff_registerValAfter]
    refine ⟨fun i hi => by obtain ⟨hlt, _, hel⟩ := (hmem_seq i).mp hi; exact ⟨hlt, hel⟩, ?_⟩
    intro k hk hi_k stp r_val hst_r
    obtain ⟨_, hsome_r, _⟩ := (hmem_seq seq[k]).mp (List.getElem_mem hk)
    obtain ⟨τ_r, hτ_r⟩ := Option.isSome_iff_exists.mp hsome_r
    have hkr : s.history[seq[k]].kind = .read := ((hg.hist_wf seq[k] hi_k).2.2.1 stp r_val hst_r).1
    have htv_r := hg.val_valid.2.2 seq[k] hi_k stp r_val τ_r hst_r hτ_r
    have hpref_lt : ∀ x ∈ seq.take k,
        abdLinKey opTag s.history x < abdLinKey opTag s.history seq[k] := by
      intro x hx
      obtain ⟨m, hm_len, rfl⟩ := List.getElem_of_mem hx
      have hmk : m < k := by rw [List.length_take] at hm_len; omega
      rw [List.getElem_take]
      exact (List.pairwise_iff_getElem.mp hsorted) m k (hmk.trans hk) hk hmk
    have hpref_write_le : ∀ w ∈ seq.take k, ∀ τ_w, opTag w = some τ_w → τ_w ≤ τ_r := by
      intro w hw_mem τ_w hτ_w
      by_contra hnot_le
      exact lt_asymm (hpref_lt w hw_mem) (abdLinKey_lt_of_tag_lt hτ_r hτ_w (lt_of_not_ge hnot_le))
    rcases htv_r with ⟨rfl, rfl⟩ | ⟨w, hw_lt, hkw, hτ_w⟩
    · symm
      refine registerValAfter_reads fun x hx => ?_
      obtain ⟨hx_lt, hsome_x, _⟩ := (hmem_seq x).mp (List.mem_of_mem_take hx)
      obtain ⟨τ_x, hτ_x⟩ := Option.isSome_iff_exists.mp hsome_x
      refine ⟨hx_lt, ?_⟩
      cases hkx : s.history[x].kind with
      | read => rfl
      | write vx =>
        obtain ⟨seq_x, hτ_eq⟩ := hg.write_unique.1 x hx_lt vx τ_x hkx hτ_x
        exact False.elim (not_lt_of_ge (hτ_eq ▸ hpref_write_le x hx τ_x hτ_x)
          (initTag_lt_nextWriteTag seq_x _))
    · have hw_elig : s.history[w].isEligible := by
        cases hsw : s.history[w].status with
        | pending | doneWrite _ => simp [OpRecord.isEligible, hkw, hsw]
        | doneRead sr vr =>
          have hkr_w := ((hg.hist_wf w hw_lt).2.2.1 sr vr hsw).1
          rw [hkw] at hkr_w; cases hkr_w
      have hw_seq : w ∈ seq := (hmem_seq w).mpr ⟨hw_lt, by simp [hτ_w], hw_elig⟩
      have hiw := List.idxOf_lt_length_of_mem hw_seq
      have hlt_k : seq.idxOf w < k :=
        pairwise_lt_index_of_key_lt hsorted hiw hk
          (by simpa [List.getElem_idxOf] using
            abdLinKey_write_lt_read hw_lt hi_k hkw hkr hτ_w hτ_r le_rfl)
      have htake_len : seq.idxOf w < (seq.take k).length := by rw [List.length_take]; omega
      have hw_in_take : w ∈ seq.take k := by
        have hget_take : (seq.take k)[seq.idxOf w] = w := by
          rw [List.getElem_take, List.getElem_idxOf hiw]
        exact hget_take ▸ List.getElem_mem htake_len
      obtain ⟨before, after, hsplit⟩ := List.append_of_mem hw_in_take
      have hafter_gt : ∀ x ∈ after, abdLinKey opTag s.history w < abdLinKey opTag s.history x :=
        (List.pairwise_append.mp (hsplit ▸ hsorted.take)).2.1 |> List.pairwise_cons.mp |>.1
      have hafter_reads : ∀ x ∈ after, ∃ hx : x < s.history.length, s.history[x].kind = .read := by
        intro x hx
        have hx_take : x ∈ seq.take k := by rw [hsplit]; simp [hx]
        obtain ⟨hx_lt, hsome_x, _⟩ := (hmem_seq x).mp (List.mem_of_mem_take hx_take)
        obtain ⟨τ_x, hτ_x⟩ := Option.isSome_iff_exists.mp hsome_x
        refine ⟨hx_lt, ?_⟩
        cases hkx : s.history[x].kind with
        | read => rfl
        | write vx =>
          rcases lt_or_eq_of_le (hpref_write_le x hx_take τ_x hτ_x) with hlt | rfl
          · exact False.elim (lt_asymm (hafter_gt x hx) (abdLinKey_lt_of_tag_lt hτ_x hτ_w hlt))
          · obtain rfl := hg.write_unique.2 x w hx_lt hw_lt vx r_val τ_x hkx hkw hτ_x hτ_w
            exact False.elim (lt_irrefl _ (hafter_gt x hx))
      rw [hsplit, registerValAfter_append, registerValAfter_cons, List.getElem?_eq_getElem hw_lt]
      dsimp only
      rw [hkw, registerValAfter_reads hafter_reads]

end Invariant

/-! ### Wait-free termination (`abd_terminates`) -/

section Liveness

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder P] [DecidableEq V]

omit [DecidableEq P] [LinearOrder P] [DecidableEq V] in
/-- Shared two-hop quorum progress argument: if at step `k₀` every live server `q ∉ F` has an
in-flight request `req q`, delivering `req q` emits a response satisfying `IsResp q`, and for all
`j ≥ k₀`, `coll j : Finset P` grows monotonically, stays strictly below `n - t`, and absorbs `q`
upon delivering any `IsResp q` envelope, then a contradiction ensues under fairness. -/
private lemma not_forall_stay_of_fair {t : ℕ} (_h2t : 2 * t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t)
    {ss : ωSequence (State P (ABDState P V) (ABDMsg P V) V)}
    {xs : ωSequence (Action P (ABDMsg P V) V)}
    (hfair : Protocol.Fair F ss xs)
    {c : P} (hc : c ∉ F) (k₀ : ℕ)
    (req : P → Envelope P (ABDMsg P V))
    (IsResp : P → Envelope P (ABDMsg P V) → Prop)
    (coll : ℕ → Finset P)
    (hreq_dest : ∀ q, (req q).dest = q)
    (hreq_init : ∀ q : P, req q ∈ (ss k₀).msgs)
    (hreq_emit : ∀ q j, k₀ ≤ j → xs j = .deliver (req q) →
      ∃ r, r ∈ (ss (j + 1)).msgs ∧ r.dest = c ∧ IsResp q r)
    (hcoll_mono : ∀ j, k₀ ≤ j → coll j ⊆ coll (j + 1))
    (hcoll_lt : ∀ j, k₀ ≤ j → (coll j).card < Fintype.card P - t)
    (hresp_absorb : ∀ q r j, k₀ ≤ j → xs j = .deliver r → IsResp q r → q ∈ coll (j + 1)) :
    False := by
  classical
  have hcoll_le : ∀ j₁ j₂, k₀ ≤ j₁ → j₁ ≤ j₂ → coll j₁ ⊆ coll j₂ := by
    intro j₁ j₂ hj₁ hle
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    induction d with
    | zero => exact Finset.Subset.refl _
    | succ d ih =>
      exact (ih (Nat.le_add_right j₁ d)).trans
        (hcoll_mono (j₁ + d) (hj₁.trans (Nat.le_add_right j₁ d)))
  have hex_q : ∀ q ∈ Finset.univ \ F, ∃ m, k₀ ≤ m ∧ q ∈ coll m := by
    intro q hq
    have hqF : q ∉ F := (Finset.mem_sdiff.mp hq).2
    obtain ⟨j₁, hj₁, hdel₁⟩ := hfair (req q) (by rwa [hreq_dest q]) k₀ (hreq_init q)
    obtain ⟨r, hr_mem, hr_dest, hr_is⟩ := hreq_emit q j₁ hj₁ hdel₁
    obtain ⟨j₂, hj₂, hdel₂⟩ := hfair r (by rwa [hr_dest]) (j₁ + 1) hr_mem
    have hk_j₂ : k₀ ≤ j₂ := hj₁.trans ((Nat.le_succ j₁).trans hj₂)
    exact ⟨j₂ + 1, Nat.le_succ_of_le hk_j₂, hresp_absorb q r j₂ hk_j₂ hdel₂ hr_is⟩
  choose stepOf hstep_ge hstep_mem using
    fun (q : {x // x ∈ Finset.univ \ F}) => hex_q q.val q.property
  let M := max k₀ (Finset.univ.sup stepOf)
  have hM_ge : k₀ ≤ M := le_max_left _ _
  have hsub : Finset.univ \ F ⊆ coll M := by
    intro q hq
    have hle_M : stepOf ⟨q, hq⟩ ≤ M :=
      (Finset.le_sup (f := stepOf) (Finset.mem_univ ⟨q, hq⟩)).trans (le_max_right _ _)
    exact hcoll_le _ M (hstep_ge ⟨q, hq⟩) hle_M (hstep_mem ⟨q, hq⟩)
  have := hcoll_lt M hM_ge
  finset_card

/-- Shared frame lemma for `c₀`'s client phase: while `c₀` has a pending operation, any transition
whose `.deliver` action at `c₀` preserves `.phase` (such as `.query`, `.store`, or mismatched
replies) leaves `c₀`'s `.phase` unchanged. -/
private lemma phase_eq_of_tr {v₀ : V} {t : ℕ}
    {u u' : State P (ABDState P V) (ABDMsg P V) V} {act : Action P (ABDMsg P V) V}
    (htr : (abdProtocol P V v₀ t).lts.Tr u act u')
    {c₀ : P} {pend : PendingOp V} (hp : (u.proc c₀).pending = some pend)
    (hrecv : ∀ src body, act = .deliver ⟨src, c₀, body⟩ →
      (abdOnRecv t c₀ (u.proc c₀).state src body).nextState.phase =
        (u.proc c₀).state.phase) :
    (u'.proc c₀).state.phase = (u.proc c₀).state.phase := by
  cases act with
  | stutter => obtain rfl := htr; rfl
  | invoke cm _ =>
    obtain ⟨hp_cm, rfl⟩ := htr
    have hne : c₀ ≠ cm := fun heq => by subst heq; rw [hp] at hp_cm; cases hp_cm
    simp [Protocol.doInvoke, Function.update_of_ne hne]
  | deliver e =>
    obtain ⟨_, rfl⟩ := htr
    by_cases hed : e.dest = c₀
    · subst hed
      simpa [Protocol.doDeliver, abdProtocol] using
        hrecv e.src e.body (congrArg Action.deliver (by ext <;> rfl))
    · simp [Protocol.doDeliver, Function.update_of_ne (Ne.symm hed)]

/-- In Phase 1, any transition other than delivering a matching `.queryResp reqId` to `c₀` leaves
`c₀`'s `.phase1` state unchanged (assuming `c₀` currently has a pending operation). -/
private lemma phase1_unchanged_of_not_queryResp {v₀ : V} {t : ℕ}
    {u u' : State P (ABDState P V) (ABDMsg P V) V} {act : Action P (ABDMsg P V) V}
    (htr : (abdProtocol P V v₀ t).lts.Tr u act u')
    {c₀ : P} {pend : PendingOp V} (hp : (u.proc c₀).pending = some pend)
    {reqId : ℕ} {kind : OpKind V} {resp : Finset P} {bt : Tag P} {bv : V}
    (hph : (u.proc c₀).state.phase = .phase1 reqId kind resp bt bv)
    (hnot : ¬ ∃ src rTag rVal, act = .deliver ⟨src, c₀, .queryResp reqId rTag rVal⟩) :
    (u'.proc c₀).state.phase = .phase1 reqId kind resp bt bv := by
  refine (phase_eq_of_tr htr hp fun src body hact => ?_).trans hph
  cases body with
  | query _ | ack _ => simp [abdOnRecv, hph]
  | store _ _ _ => dsimp only [abdOnRecv]; split_ifs <;> rfl
  | queryResp rId rt rv =>
    by_cases hr : rId = reqId
    · exact False.elim (hnot ⟨src, rt, rv, hr ▸ hact⟩)
    · simp [abdOnRecv, hph, hr]

/-- In Phase 2, any transition other than delivering a matching `.ack reqId` to `c₀` leaves `c₀`'s
`.phase2` state unchanged (assuming `c₀` currently has a pending operation). -/
private lemma phase2_unchanged_of_not_ack {v₀ : V} {t : ℕ}
    {u u' : State P (ABDState P V) (ABDMsg P V) V} {act : Action P (ABDMsg P V) V}
    (htr : (abdProtocol P V v₀ t).lts.Tr u act u')
    {c₀ : P} {pend : PendingOp V} (hp : (u.proc c₀).pending = some pend)
    {reqId : ℕ} {kind : OpKind V} {cTag : Tag P} {cVal : V} {acks : Finset P}
    (hph : (u.proc c₀).state.phase = .phase2 reqId kind cTag cVal acks)
    (hnot : ¬ ∃ src, act = .deliver ⟨src, c₀, .ack reqId⟩) :
    (u'.proc c₀).state.phase = .phase2 reqId kind cTag cVal acks := by
  refine (phase_eq_of_tr htr hp fun src body hact => ?_).trans hph
  cases body with
  | query _ | queryResp _ _ _ => simp [abdOnRecv, hph]
  | store _ _ _ => dsimp only [abdOnRecv]; split_ifs <;> rfl
  | ack rId =>
    by_cases hr : rId = reqId
    · exact False.elim (hnot ⟨src, hr ▸ hact⟩)
    · simp [abdOnRecv, hph, hr]

/-- Phase-1 liveness step: if non-faulty `c₀ ∉ F` enters `.phase1 reqId kind ∅ (initTag P) v₀` at
step `k₁` with all `.query reqId` envelopes in flight and remains `pending` forever from `k₁`,
fairness drives `c₀` into `.phase2 reqId kind cTag cVal ∅` at some step `k₂ ≥ k₁` with all
`.store reqId cTag cVal` envelopes in flight. -/
private lemma abd_phase1_eventually_phase2 {t : ℕ} (h2t : 2 * t < Fintype.card P) (v₀ : V)
    {F : Finset P} (hF : F.card ≤ t)
    {ss : ωSequence (State P (ABDState P V) (ABDMsg P V) V)}
    {xs : ωSequence (Action P (ABDMsg P V) V)}
    (hexec : (abdProtocol P V v₀ t).lts.OmegaExecution ss xs)
    (hfair : Protocol.Fair F ss xs)
    (hgood : ∀ k, ∃ opTag, ABDGood v₀ t (ss k) opTag)
    {c₀ : P} (hc₀ : c₀ ∉ F) {k₁ i reqId : ℕ} {kind : OpKind V}
    (hpend_c₀ : ∀ j, k₁ ≤ j → ((ss j).proc c₀).pending = some ⟨i, kind⟩)
    (hinit_ph : ((ss k₁).proc c₀).state.phase = .phase1 reqId kind ∅ (initTag P) v₀)
    (hinit_msgs : ∀ q : P, ⟨c₀, q, .query reqId⟩ ∈ (ss k₁).msgs) :
    ∃ k₂ cTag cVal, k₁ ≤ k₂ ∧
      ((ss k₂).proc c₀).state.phase = .phase2 reqId kind cTag cVal ∅ ∧
      ∀ q : P, ⟨c₀, q, .store reqId cTag cVal⟩ ∈ (ss k₂).msgs := by
  classical
  let p1Set (j : ℕ) : Finset P :=
    match ((ss j).proc c₀).state.phase with
    | .phase1 _ _ resp _ _ => resp
    | _ => ∅
  let IsP1 (j : ℕ) : Prop :=
    ∃ resp bt bv, ((ss j).proc c₀).state.phase = .phase1 reqId kind resp bt bv
  have hp1_step : ∀ j, k₁ ≤ j → IsP1 j →
      (IsP1 (j + 1) ∧ p1Set j ⊆ p1Set (j + 1)) ∨
      (∃ cTag cVal,
        ((ss (j + 1)).proc c₀).state.phase = .phase2 reqId kind cTag cVal ∅ ∧
        ∀ q : P, ⟨c₀, q, .store reqId cTag cVal⟩ ∈ (ss (j + 1)).msgs) := by
    intro j hj ⟨resp, bt, bv, hph⟩
    by_cases hqr : ∃ src rTag rVal, xs j = .deliver ⟨src, c₀, .queryResp reqId rTag rVal⟩
    · obtain ⟨src, rTag, rVal, hxs⟩ := hqr
      have htr_j := hexec j; rw [hxs] at htr_j; obtain ⟨_, heq⟩ := htr_j
      by_cases hq_card : Fintype.card P - t ≤ (insert src resp).card
      · right
        let cv := phase2Choice c₀ kind
          (if bt < rTag then rTag else bt) (if bt < rTag then rVal else bv)
        refine ⟨cv.1, cv.2, ?_, fun q => ?_⟩
        · cases kind <;>
            simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, hq_card, cv, phase2Choice]
        · cases kind <;>
          · simp only [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, ↓reduceIte,
              hq_card, cv, phase2Choice, Multiset.mem_add]
            exact Or.inr (mem_broadcastAll_tag c₀ q _)
      · left
        have hph' : ((ss (j + 1)).proc c₀).state.phase =
            .phase1 reqId kind (insert src resp)
              (if bt < rTag then rTag else bt) (if bt < rTag then rVal else bv) := by
          simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, hq_card]
        exact ⟨⟨insert src resp, _, _, hph'⟩, by simp [p1Set, hph, hph', Finset.subset_insert]⟩
    · have hph' := phase1_unchanged_of_not_queryResp (hexec j) (hpend_c₀ j hj) hph hqr
      exact Or.inl ⟨⟨resp, bt, bv, hph'⟩, by simp [p1Set, hph, hph']⟩
  have hex_gt : ∃ d, ¬ IsP1 (k₁ + d) := by
    by_contra! hall_d
    have hall_p1 : ∀ j, k₁ ≤ j → IsP1 j := fun j hj => by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj; exact hall_d d
    apply not_forall_stay_of_fair h2t hF hfair hc₀ k₁
      (fun q => ⟨c₀, q, .query reqId⟩)
      (fun q r => ∃ rt rv, r = ⟨q, c₀, .queryResp reqId rt rv⟩)
      p1Set (fun _ => rfl) hinit_msgs
    · intro q j _ hdel
      have htr_j := hexec j; rw [hdel] at htr_j; obtain ⟨_, heq⟩ := htr_j
      refine ⟨⟨q, c₀, .queryResp reqId ((ss j).proc q).state.repTag ((ss j).proc q).state.repVal⟩,
        ?_, rfl, _, _, rfl⟩
      simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, tagSender]
    · intro j hj
      rcases hp1_step j hj (hall_p1 j hj) with ⟨_, hsub⟩ | ⟨_, _, hph2, _⟩
      · exact hsub
      · obtain ⟨_, _, _, hph1⟩ := hall_p1 (j + 1) (Nat.le_succ_of_le hj)
        rw [hph2] at hph1; cases hph1
    · intro j hj
      obtain ⟨resp, bt, bv, hph⟩ := hall_p1 j hj
      obtain ⟨opTag, hg⟩ := hgood j
      have hps := hg.proc_sync c₀
      rw [hpend_c₀ j hj, hph] at hps
      simpa [p1Set, hph] using hps.2.2.2.2.2.2.2.1
    · rintro q r j hj hdel ⟨rt, rv, rfl⟩
      obtain ⟨resp, bt, bv, hph⟩ := hall_p1 j hj
      obtain ⟨_, _, _, hph1⟩ := hall_p1 (j + 1) (Nat.le_succ_of_le hj)
      have htr_j := hexec j; rw [hdel] at htr_j; obtain ⟨_, heq⟩ := htr_j
      by_cases hq_card : Fintype.card P - t ≤ (insert q resp).card
      · simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, hq_card] at hph1
      · simp [p1Set, heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, hq_card]
  let d₂ := Nat.find hex_gt
  have hd₂_not : ¬ IsP1 (k₁ + d₂) := Nat.find_spec hex_gt
  have hd₂_pos : 0 < d₂ :=
    Nat.pos_of_ne_zero fun hd0 => hd₂_not (hd0 ▸ ⟨∅, initTag P, v₀, hinit_ph⟩)
  have hd₂_prev : IsP1 (k₁ + (d₂ - 1)) := by
    by_contra hnot; exact Nat.find_min hex_gt (by omega) hnot
  have hk₂_eq : k₁ + (d₂ - 1) + 1 = k₁ + d₂ := by omega
  rcases hp1_step (k₁ + (d₂ - 1)) (Nat.le_add_right k₁ _) hd₂_prev with ⟨hp1', _⟩ | ⟨cT, cV, hp2⟩
  · exact False.elim (hd₂_not (hk₂_eq ▸ hp1'))
  · exact ⟨k₁ + d₂, cT, cV, Nat.le_add_right k₁ d₂, hk₂_eq ▸ hp2⟩

/-- Phase-2 liveness contradiction: non-faulty `c₀ ∉ F` cannot remain `pending` forever after
entering `.phase2 reqId kind cTag cVal ∅` with all `.store reqId cTag cVal` envelopes in flight. -/
private lemma abd_phase2_contradiction {t : ℕ} (h2t : 2 * t < Fintype.card P) (v₀ : V)
    {F : Finset P} (hF : F.card ≤ t)
    {ss : ωSequence (State P (ABDState P V) (ABDMsg P V) V)}
    {xs : ωSequence (Action P (ABDMsg P V) V)}
    (hexec : (abdProtocol P V v₀ t).lts.OmegaExecution ss xs)
    (hfair : Protocol.Fair F ss xs)
    (hgood : ∀ k, ∃ opTag, ABDGood v₀ t (ss k) opTag)
    {c₀ : P} (hc₀ : c₀ ∉ F) {k₂ i reqId : ℕ} {kind : OpKind V} {cTag : Tag P} {cVal : V}
    (hpend_c₀ : ∀ j, k₂ ≤ j → ((ss j).proc c₀).pending = some ⟨i, kind⟩)
    (hinit_ph : ((ss k₂).proc c₀).state.phase = .phase2 reqId kind cTag cVal ∅)
    (hinit_msgs : ∀ q : P, ⟨c₀, q, .store reqId cTag cVal⟩ ∈ (ss k₂).msgs) : False := by
  let p2Set (j : ℕ) : Finset P :=
    match ((ss j).proc c₀).state.phase with
    | .phase2 _ _ _ _ acks => acks
    | _ => ∅
  let IsP2 (j : ℕ) : Prop :=
    ∃ acks, ((ss j).proc c₀).state.phase = .phase2 reqId kind cTag cVal acks
  have hp2_not_quorum : ∀ j src acks, k₂ ≤ j →
      ((ss j).proc c₀).state.phase = .phase2 reqId kind cTag cVal acks →
      xs j = .deliver ⟨src, c₀, .ack reqId⟩ →
      ¬ Fintype.card P - t ≤ (insert src acks).card := by
    intro j src acks hj hph hxs hq_card
    have htr_j := hexec j; rw [hxs] at htr_j; obtain ⟨_, heq⟩ := htr_j
    have hp_next := hpend_c₀ (j + 1) (Nat.le_succ_of_le hj)
    have hp_cur := hpend_c₀ j hj
    simp only [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, ↓reduceIte,
      hq_card, Function.update_self, hp_cur, deliverPending] at hp_next
    cases kind <;> simp [matchCompletion] at hp_next
  have hp2_step : ∀ j, k₂ ≤ j → IsP2 j → IsP2 (j + 1) ∧ p2Set j ⊆ p2Set (j + 1) := by
    intro j hj ⟨acks, hph⟩
    by_cases hack : ∃ src, xs j = .deliver ⟨src, c₀, .ack reqId⟩
    · obtain ⟨src, hxs⟩ := hack
      have hq_card := hp2_not_quorum j src acks hj hph hxs
      have htr_j := hexec j; rw [hxs] at htr_j; obtain ⟨_, heq⟩ := htr_j
      have hph' : ((ss (j + 1)).proc c₀).state.phase =
          .phase2 reqId kind cTag cVal (insert src acks) := by
        simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, hq_card]
      exact ⟨⟨insert src acks, hph'⟩, by simp [p2Set, hph, hph', Finset.subset_insert]⟩
    · have hph' := phase2_unchanged_of_not_ack (hexec j) (hpend_c₀ j hj) hph hack
      exact ⟨⟨acks, hph'⟩, by simp [p2Set, hph, hph']⟩
  have hall_p2 : ∀ j, k₂ ≤ j → IsP2 j := fun j hj => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    induction d with
    | zero => exact ⟨∅, hinit_ph⟩
    | succ d ih => exact (hp2_step (k₂ + d) (Nat.le_add_right k₂ d) (ih (Nat.le_add_right k₂ d))).1
  apply not_forall_stay_of_fair h2t hF hfair hc₀ k₂
    (fun q => ⟨c₀, q, .store reqId cTag cVal⟩)
    (fun q r => r = ⟨q, c₀, .ack reqId⟩)
    p2Set (fun _ => rfl) hinit_msgs
  · intro q j _ hdel
    have htr_j := hexec j; rw [hdel] at htr_j; obtain ⟨_, heq⟩ := htr_j
    refine ⟨⟨q, c₀, .ack reqId⟩, ?_, rfl, rfl⟩
    simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, tagSender]
  · exact fun j hj => (hp2_step j hj (hall_p2 j hj)).2
  · intro j hj
    obtain ⟨acks, hph⟩ := hall_p2 j hj
    obtain ⟨opTag, hg⟩ := hgood j
    have hps := hg.proc_sync c₀
    rw [hpend_c₀ j hj, hph] at hps
    simpa [p2Set, hph] using hps.2.2.2.2.2.2.2.1
  · rintro q r j hj hdel rfl
    obtain ⟨acks, hph⟩ := hall_p2 j hj
    have hq_card := hp2_not_quorum j q acks hj hph hdel
    have htr_j := hexec j; rw [hdel] at htr_j; obtain ⟨_, heq⟩ := htr_j
    simp [p2Set, heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, hq_card]

/-- Fair-crash termination (`abd_terminates`) for the cardinality-quorum envelope protocol
`abdProtocol`: when `2 * t < Fintype.card P` and `F.card ≤ t`, every operation invoked by a
non-faulty process (`caller ∉ F`) eventually completes in every `Protocol.Fair F` execution (a
separate envelope-liveness property accompanying `abd_linearizable`, without message or time cost
bounds). -/
theorem abd_terminates {t : ℕ} (h2t : 2 * t < Fintype.card P) (v₀ : V)
    {F : Finset P} (hF : F.card ≤ t)
    {ss : ωSequence (State P (ABDState P V) (ABDMsg P V) V)}
    {xs : ωSequence (Action P (ABDMsg P V) V)}
    (ha : (abdProtocol P V v₀ t).AdmissibleRun F ss xs)
    (k₀ i : ℕ) (hi₀ : i < (ss k₀).history.length)
    (hc : (ss k₀).history[i].caller ∉ F) :
    ∃ (j : ℕ) (hij : i < (ss j).history.length),
      k₀ ≤ j ∧ (ss j).history[i].status.isCompleted = true := by
  let π := abdProtocol P V v₀ t
  obtain ⟨hstart, hexec, hfair⟩ := ha
  have hgood : ∀ k, ∃ opTag, ABDGood v₀ t (ss k) opTag :=
    fun k => reachable_abdGood h2t (π.admissibleRun_reachable ⟨hstart, hexec, hfair⟩ k)
  have hpend_wf : ∀ k p pend, ((ss k).proc p).pending = some pend →
      ∃ hlt : pend.opId < (ss k).history.length,
        (ss k).history[pend.opId].status = .pending := by
    intro k p pend hp
    obtain ⟨hlt, _, _, hst⟩ := (hgood k).choose_spec.pending_info hp
    exact ⟨hlt, hst⟩
  by_cases hdone₀ : (ss k₀).history[i].status.isCompleted = true
  · exact ⟨k₀, hi₀, le_rfl, hdone₀⟩
  by_contra! hnever
  have hnot_comp : ∀ j (hij : i < (ss j).history.length),
      (ss j).history[i].status = .pending := by
    intro j hij
    cases hst : (ss j).history[i].status with
    | pending => rfl
    | doneRead _ _ | doneWrite _ =>
      exfalso
      have hcj : (ss j).history[i].status.isCompleted = true := by simp [hst]
      have hstable : ∀ d, ∃ hm : i < (ss (j + d)).history.length,
          (ss (j + d)).history[i] = (ss j).history[i] := by
        intro d
        induction d with
        | zero => exact ⟨hij, rfl⟩
        | succ d ih =>
          obtain ⟨hmd, heqd⟩ := ih
          obtain ⟨hm', heq'⟩ := π.tr_history_completed_stable (hexec (j + d)) hmd
            (heqd ▸ hcj) (hpend_wf (j + d))
          exact ⟨hm', heq'.trans heqd⟩
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (le_max_right k₀ j)
      obtain ⟨hM, heqM⟩ := hstable d
      exact hnever (j + d) hM (hd ▸ le_max_left k₀ j) (heqM ▸ hcj)
  classical
  have hex_lt : ∃ k, i < (ss k).history.length := ⟨k₀, hi₀⟩
  let k₁ := Nat.find hex_lt
  have hk₁_lt : i < (ss k₁).history.length := Nat.find_spec hex_lt
  have hk₁_pos : 0 < k₁ := Nat.pos_of_ne_zero fun hk0 => by
    rw [hk0, hstart] at hk₁_lt; simp [Protocol.start] at hk₁_lt
  let k_inv := k₁ - 1
  have hk_succ : k_inv + 1 = k₁ := by omega
  have hnot_before : ¬ i < (ss k_inv).history.length := Nat.find_min hex_lt (by omega)
  have htr_inv := hexec k_inv; rw [hk_succ] at htr_inv
  obtain ⟨c₀, kind, hlen_kinv, hss_k₁⟩ : ∃ c₀ kind,
      (ss k_inv).history.length = i ∧ ss k₁ = π.doInvoke c₀ kind (ss k_inv) := by
    cases hxs : xs k_inv <;> rw [hxs] at htr_inv
    · obtain ⟨_, heq⟩ := htr_inv
      have hlen : (ss k₁).history.length = (ss k_inv).history.length + 1 := by
        simp [heq, Protocol.doInvoke]
      exact ⟨_, _, by omega, heq⟩
    · obtain ⟨_, heq⟩ := htr_inv
      exact False.elim (hnot_before (by simpa [heq, Protocol.doDeliver] using hk₁_lt))
    · exact False.elim (hnot_before (htr_inv ▸ hk₁_lt))
  have hck_const : ∀ j (hij : i < (ss j).history.length),
      (ss j).history[i].caller = c₀ ∧ (ss j).history[i].kind = kind := by
    intro j hij
    obtain ⟨hcj, hkj, _⟩ :=
      π.mTr_history_entry_preserves (hexec.extract_mTr (Nat.find_min' hex_lt hij)) hk₁_lt hij
    have hk₁_ck : (ss k₁).history[i].caller = c₀ ∧ (ss k₁).history[i].kind = kind := by
      simp [hss_k₁, Protocol.doInvoke, ← hlen_kinv]
    exact ⟨hcj.trans hk₁_ck.1, hkj.trans hk₁_ck.2⟩
  have hpend_c₀ : ∀ j, k₁ ≤ j → ((ss j).proc c₀).pending = some ⟨i, kind⟩ := by
    intro j hj
    have hij := lt_of_lt_of_le hk₁_lt (π.mTr_history_length_le (hexec.extract_mTr hj))
    obtain ⟨_, hg⟩ := hgood j
    obtain ⟨hcj, hkj⟩ := hck_const j hij
    simpa [hcj, hkj] using (hg.hist_wf i hij).2.2.2.2 (hnot_comp j hij)
  let reqId := ((ss k_inv).proc c₀).state.nextReqId
  obtain ⟨k₂, cTag, cVal, hk₁_k₂, hinit_p2_ph, hinit_p2_msgs⟩ :=
    abd_phase1_eventually_phase2 (reqId := reqId) h2t v₀ hF hexec hfair hgood
      ((hck_const k₀ hi₀).1 ▸ hc) hpend_c₀
      (by simp [π, hss_k₁, Protocol.doInvoke, abdProtocol, abdOnInvoke, reqId])
      (fun q => by
        simp only [π, hss_k₁, Protocol.doInvoke, abdProtocol, abdOnInvoke, Multiset.mem_add]
        exact Or.inr (mem_broadcastAll_tag c₀ q (ABDMsg.query reqId)))
  exact abd_phase2_contradiction h2t v₀ hF hexec hfair hgood ((hck_const k₀ hi₀).1 ▸ hc)
    (fun j hj => hpend_c₀ j (hk₁_k₂.trans hj)) hinit_p2_ph hinit_p2_msgs

end Liveness

/-- Combined safety and fair-crash termination (`implementsAtomicRegister_abd`) for the
cardinality-quorum envelope specialization **after** [LynchShvartsman1997], §4.1–4.2 (and not the
cited Theorem 4.5 or [AttiyaBarNoyDolev1995] Theorem 4.9 endpoint): when `2 * t < Fintype.card P`,
`abdProtocol P V v₀ t` satisfies `ImplementsAtomicRegister v₀ t` over concrete point-to-point
envelopes with `(n - t)`-cardinality quorums, idle-only invocations, and eventual delivery outside
`F` (pairing `abd_linearizable` with the separate liveness property `abd_terminates`, without
read/write quorum-family generality, per-processor request queues, or cost bounds). -/
theorem implementsAtomicRegister_abd {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder P]
    [DecidableEq V] {t : ℕ} (h2t : 2 * t < Fintype.card P) (v₀ : V) :
    (abdProtocol P V v₀ t).ImplementsAtomicRegister v₀ t where
  linearizable _ hr := abd_linearizable h2t v₀ hr
  terminates _ hF _ _ ha k₀ i hi₀ hc := abd_terminates h2t v₀ hF ha k₀ i hi₀ hc

end Cslib.Distributed.ABD
