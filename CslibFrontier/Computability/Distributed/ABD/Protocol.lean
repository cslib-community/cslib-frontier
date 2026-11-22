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
  have hcompl : (Finset.univ \ Q₁).card < Q₂.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ Q₁), Finset.card_univ]
    omega
  obtain ⟨q, hq₂, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcompl
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hnot
  exact ⟨q, Finset.mem_inter.mpr ⟨hnot, hq₂⟩⟩

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

private lemma procSync_mono {P V : Type*} [Fintype P] [LinearOrder P] {t : ℕ}
    {hist : List (OpRecord P V)} {nr₁ nr₂ : ℕ} {rt₁ rt₂ : P → Tag P}
    {opTag₁ opTag₂ : ℕ → Option (Tag P)} {p : P}
    {pend? : Option (PendingOp V)} {ph : ClientPhase P V}
    (hnr : nr₁ ≤ nr₂) (hrt : ∀ q, rt₁ q ≤ rt₂ q)
    (htag : ∀ pend, pend? = some pend → opTag₂ pend.opId = opTag₁ pend.opId)
    (hps : ProcSync t hist nr₁ rt₁ opTag₁ p pend? ph) :
    ProcSync t hist nr₂ rt₂ opTag₂ p pend? ph :=
  procSync_transport le_rfl hnr hrt
    (fun pend _ hp hc => ⟨hc, rfl, rfl, htag pend hp, id⟩) hps

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
    (∀ i, ¬ prec (s.history ++ [rec']) s.history.length i) ∧
    (∀ a, prec (s.history ++ [rec']) a s.history.length ↔
      ∃ ha : a < s.history.length, s.history[a].status.isCompleted = true) := by
  let hist' := s.history ++ [rec']
  have hlen : hist'.length = s.history.length + 1 := by simp [hist']
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj
    have hi' : i < hist'.length := by omega
    have hj' : j < hist'.length := by omega
    constructor
    · rintro ⟨_, _, r, hr, hlt⟩
      change (s.history ++ [rec'])[i].status.respStep? = some r at hr
      change r < (s.history ++ [rec'])[j].invStep at hlt
      simp only [List.getElem_append_left hi, List.getElem_append_left hj] at hr hlt
      exact ⟨hi, hj, r, hr, hlt⟩
    · rintro ⟨_, _, r, hr, hlt⟩
      refine ⟨hi', hj', r, ?_, ?_⟩
      · simpa [hist', List.getElem_append_left hi] using hr
      · simpa [hist', List.getElem_append_left hj] using hlt
  · intro i ⟨_, _, r, hr, _⟩
    change (s.history ++ [rec'])[s.history.length].status.respStep? = some r at hr
    simp [hstat, OpStatus.respStep?] at hr
  · intro a
    constructor
    · rintro ⟨ha', _, r, hr, _⟩
      have ha_len : a < s.history.length + 1 := hlen ▸ ha'
      by_cases ha : a < s.history.length
      · change (s.history ++ [rec'])[a].status.respStep? = some r at hr
        simp only [List.getElem_append_left ha] at hr
        exact ⟨ha, by simp [OpStatus.isCompleted, hr]⟩
      · have heq : a = s.history.length := by omega
        subst heq
        change (s.history ++ [rec'])[s.history.length].status.respStep? = some r at hr
        simp [hstat, OpStatus.respStep?] at hr
    · rintro ⟨ha, hcomp⟩
      have ha' : a < hist'.length := by omega
      have hb' : s.history.length < hist'.length := by omega
      cases hrs : s.history[a].status.respStep? with
      | none => simp [OpStatus.isCompleted, hrs] at hcomp
      | some r =>
        obtain ⟨_, hr_lt⟩ := (hg.hist_wf a ha).2.1 r hrs
        refine ⟨ha', hb', r, ?_, ?_⟩
        · simpa [hist', List.getElem_append_left ha] using hrs
        · simp [hist', hinv, hr_lt]

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

private lemma ABDGood.pending_opId_ne {P V : Type*} [Fintype P] [LinearOrder P]
    {v₀ : V} {t : ℕ} {s : State P (ABDState P V) (ABDMsg P V) V}
    {opTag : ℕ → Option (Tag P)} (hg : ABDGood v₀ t s opTag)
    {p q : P} (hpq : p ≠ q) {p₁ p₂ : PendingOp V}
    (hp : (s.proc p).pending = some p₁) (hq : (s.proc q).pending = some p₂) :
    p₁.opId ≠ p₂.opId := by
  obtain ⟨hi₁, hc₁, _⟩ := hg.pending_info hp
  obtain ⟨hi₂, hc₂, _⟩ := hg.pending_info hq
  intro heq
  have hget : s.history[p₁.opId]? = s.history[p₂.opId]? := by rw [heq]
  rw [List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂] at hget
  exact hpq (hc₁.symm.trans ((congrArg OpRecord.caller (Option.some.inj hget)).trans hc₂))

private lemma update_proc_repTag_le {P V : Type*} [DecidableEq P] [LinearOrder P]
    (proc : P → ProcState (ABDState P V) V) {actor : P}
    {nextSt : ABDState P V} {newPend : Option (PendingOp V)}
    (hle : (proc actor).state.repTag ≤ nextSt.repTag) (q : P) :
    (proc q).state.repTag ≤ (Function.update proc actor ⟨nextSt, newPend⟩ q).state.repTag := by
  by_cases hq : q = actor
  · subst hq; simpa using hle
  · simp [hq]

private lemma update_proc_repTag_eq {P V : Type*} [DecidableEq P]
    (proc : P → ProcState (ABDState P V) V) {actor : P}
    {nextSt : ABDState P V} {newPend : Option (PendingOp V)}
    (heq : nextSt.repTag = (proc actor).state.repTag) (q : P) :
    (Function.update proc actor ⟨nextSt, newPend⟩ q).state.repTag = (proc q).state.repTag := by
  by_cases hq : q = actor
  · subst hq; simpa using heq
  · simp [hq]

/-- Shared `MsgWF` preservation across any single-process update
`s'.proc = Function.update s.proc actor ⟨nextSt, newPend⟩`. -/
private lemma msgWF_transfer_update {P V : Type*} [DecidableEq P] [LinearOrder P] {v₀ : V}
    {s : State P (ABDState P V) (ABDMsg P V) V}
    {msgs' : Multiset (Envelope P (ABDMsg P V))} {hist' : List (OpRecord P V)} {step' : ℕ}
    {actor : P} {nextSt : ABDState P V} {newPend : Option (PendingOp V)}
    {opTag opTag' : ℕ → Option (Tag P)}
    (hlen : s.history.length ≤ hist'.length)
    (htag_pres : ∀ (i : ℕ) (hi : i < s.history.length) τ,
      opTag i = some τ →
      (hist'[i]'(lt_of_lt_of_le hi hlen)).kind = s.history[i].kind ∧ opTag' i = some τ)
    (hnext_actor : (s.proc actor).state.nextReqId ≤ nextSt.nextReqId)
    (hrep_actor : (s.proc actor).state.repTag ≤ nextSt.repTag)
    (hp1_actor : ∀ reqId, reqId < (s.proc actor).state.nextReqId →
      (∀ knd resp bt bv, (s.proc actor).state.phase = .phase1 reqId knd resp bt bv → False) →
      ∀ knd resp bt bv, nextSt.phase = .phase1 reqId knd resp bt bv → False)
    (hp2_actor : ∀ reqId, reqId < (s.proc actor).state.nextReqId →
      (∀ knd resp bt bv, (s.proc actor).state.phase = .phase1 reqId knd resp bt bv → False) →
      ∀ knd cTag cVal acks, nextSt.phase = .phase2 reqId knd cTag cVal acks →
        ∃ acks₀, (s.proc actor).state.phase = .phase2 reqId knd cTag cVal acks₀)
    {e : Envelope P (ABDMsg P V)} (hw : MsgWF v₀ s opTag e.src e.dest e.body) :
    MsgWF v₀
      { msgs := msgs'
        proc := Function.update s.proc actor ⟨nextSt, newPend⟩
        history := hist'
        step := step' }
      opTag' e.src e.dest e.body := by
  have hnext_le : ∀ p : P, (s.proc p).state.nextReqId ≤
      (Function.update s.proc actor ⟨nextSt, newPend⟩ p).state.nextReqId := by
    intro p; by_cases hp : p = actor <;> [subst hp; skip] <;> [simpa using hnext_actor; simp [hp]]
  have hrep_le := update_proc_repTag_le s.proc (newPend := newPend) hrep_actor
  have hp1_back : ∀ p reqId, reqId < (s.proc p).state.nextReqId →
      (∀ knd resp bt bv, (s.proc p).state.phase = .phase1 reqId knd resp bt bv → False) →
      ∀ knd resp bt bv,
        (Function.update s.proc actor ⟨nextSt, newPend⟩ p).state.phase =
          .phase1 reqId knd resp bt bv → False := by
    intro p reqId hreq hp1 knd resp bt bv hph'
    by_cases hp : p = actor
    · subst hp; simp only [Function.update_self] at hph'
      exact hp1_actor reqId hreq hp1 knd resp bt bv hph'
    · simp only [Function.update_of_ne hp] at hph'
      exact hp1 knd resp bt bv hph'
  have hp2_back : ∀ p reqId, reqId < (s.proc p).state.nextReqId →
      (∀ knd resp bt bv, (s.proc p).state.phase = .phase1 reqId knd resp bt bv → False) →
      ∀ knd cTag cVal acks,
        (Function.update s.proc actor ⟨nextSt, newPend⟩ p).state.phase =
          .phase2 reqId knd cTag cVal acks →
        ∃ acks₀, (s.proc p).state.phase = .phase2 reqId knd cTag cVal acks₀ := by
    intro p reqId hreq hp1 knd cTag cVal acks hph'
    by_cases hp : p = actor
    · subst hp; simp only [Function.update_self] at hph'
      exact hp2_actor reqId hreq hp1 knd cTag cVal acks hph'
    · simp only [Function.update_of_ne hp] at hph'
      exact ⟨acks, hph'⟩
  cases hb : e.body with
  | query reqId =>
    rw [hb] at hw; dsimp only [MsgWF] at hw ⊢
    exact lt_of_lt_of_le hw (hnext_le e.src)
  | queryResp reqId τ v =>
    rw [hb] at hw; dsimp only [MsgWF] at hw ⊢
    exact ⟨lt_of_lt_of_le hw.1 (hnext_le e.dest), tagValidVal_mono hlen htag_pres hw.2⟩
  | store reqId τ v =>
    rw [hb] at hw; dsimp only [MsgWF] at hw ⊢
    obtain ⟨hreq, htv, hp1, hp2⟩ := hw
    refine ⟨lt_of_lt_of_le hreq (hnext_le e.src), tagValidVal_mono hlen htag_pres htv,
      hp1_back e.src reqId hreq hp1, fun knd cTag cVal acks hph' => ?_⟩
    obtain ⟨acks₀, hph₀⟩ := hp2_back e.src reqId hreq hp1 knd cTag cVal acks hph'
    exact hp2 knd cTag cVal acks₀ hph₀
  | ack reqId =>
    rw [hb] at hw; dsimp only [MsgWF] at hw ⊢
    obtain ⟨hreq, hp1, hp2⟩ := hw
    refine ⟨lt_of_lt_of_le hreq (hnext_le e.dest), hp1_back e.dest reqId hreq hp1,
      fun knd cTag cVal acks hph' => ?_⟩
    obtain ⟨acks₀, hph₀⟩ := hp2_back e.dest reqId hreq hp1 knd cTag cVal acks hph'
    exact (hp2 knd cTag cVal acks₀ hph₀).trans (hrep_le e.src)

section StepProofs

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder P] [DecidableEq V]

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
  set proc' := Function.update s.proc caller ⟨nextSt, some ⟨s.history.length, kind⟩⟩
  have hrep_eq : ∀ q : P, (proc' q).state.repTag = (s.proc q).state.repTag :=
    update_proc_repTag_eq s.proc rfl
  obtain ⟨hprec_old, _, hprec_to_new⟩ := abdGood_prec_append hg rec' rfl rfl
  have hlen_le : s.history.length ≤ (s.history ++ [rec']).length := by simp
  have htag_pres : ∀ (i : ℕ) (hi : i < s.history.length) τ,
      opTag i = some τ →
      ((s.history ++ [rec'])[i]'(lt_of_lt_of_le hi hlen_le)).kind = s.history[i].kind ∧
        opTag i = some τ :=
    fun _ hi _ hτ => ⟨by simp [List.getElem_append_left hi], hτ⟩
  have hq_pos : 0 < Fintype.card P - t := by omega
  refine
    { tag_out := fun i hi => hg.tag_out i (le_trans (by simp) hi)
      hist_wf := fun i hi => by
        have hi_len : i < s.history.length + 1 := by simpa using hi
        by_cases hlt : i < s.history.length
        · simp only [List.getElem_append_left hlt]
          obtain ⟨hinv, hresp, hdr, hdw, hpnd⟩ := hg.hist_wf i hlt
          refine ⟨Nat.lt_succ_of_lt hinv,
            fun r hr => ⟨(hresp r hr).1, Nat.lt_succ_of_lt (hresp r hr).2⟩,
            hdr, hdw, fun hp => ?_⟩
          have hp' := hpnd hp
          have hne : s.history[i].caller ≠ caller := fun heq => by
            rw [heq, hpend_none] at hp'; cases hp'
          simpa [proc', Function.update_of_ne hne] using hp'
        · obtain rfl : i = s.history.length := by omega
          simp [proc', OpStatus.respStep?]
      inv_mono := fun i j hij hj => by
        have hj_len : j < s.history.length + 1 := by simpa using hj
        by_cases hjl : j < s.history.length
        · simp only [List.getElem_append_left (hij.trans hjl), List.getElem_append_left hjl]
          exact hg.inv_mono i j hij hjl
        · obtain rfl : j = s.history.length := by omega
          simp only [List.getElem_append_left hij, List.getElem_append_right le_rfl,
            Nat.sub_self, List.getElem_singleton]
          exact (hg.hist_wf i hij).1
      proc_sync := fun p => by
        change ProcSync t (s.history ++ [rec']) (proc' p).state.nextReqId
          (fun q => (proc' q).state.repTag) opTag p (proc' p).pending (proc' p).state.phase
        by_cases hp : p = caller
        · subst hp
          dsimp only [proc', nextSt]
          rw [Function.update_self]
          dsimp only [ProcSync]
          refine ⟨by simp, by simp [rec'], by simp [rec'], rfl, by simp [rec'],
            hg.tag_out s.history.length le_rfl, Nat.lt_succ_self _, by simpa using hq_pos, ?_⟩
          intro j hj hjne hjc
          have hj_len : j < s.history.length + 1 := by simpa using hj
          have hjl : j < s.history.length := by omega
          rw [List.getElem_append_left hjl] at hjc
          refine (hprec_to_new j).mpr ⟨hjl, ?_⟩
          cases hst : s.history[j].status with
          | doneRead _ _ | doneWrite _ => rfl
          | pending =>
            have hpnd := (hg.hist_wf j hjl).2.2.2.2 hst
            rw [hjc, hpend_none] at hpnd; cases hpnd
        · simp only [proc', Function.update_of_ne hp]
          refine procSync_transport hlen_le le_rfl (fun q => (hrep_eq q).symm.le) ?_
            (hg.proc_sync p)
          intro pend hi _ hc
          refine ⟨by simpa [List.getElem_append_left hi] using hc,
            by simp [List.getElem_append_left hi], by simp [List.getElem_append_left hi], rfl,
            fun hprev j hj hjne hjc => ?_⟩
          have hj_len : j < s.history.length + 1 := by simpa using hj
          by_cases hjl : j < s.history.length
          · rw [List.getElem_append_left hjl] at hjc
            exact (hprec_old j hjl _ hi).mpr (hprev j hjl hjne hjc)
          · obtain rfl : j = s.history.length := by omega
            simp only [List.getElem_append_right le_rfl, Nat.sub_self,
              List.getElem_singleton, rec'] at hjc
            exact False.elim (hp hjc.symm)
      msg_wf := fun e he => by
        rw [Multiset.mem_add] at he
        rcases he with he_old | he_new
        · refine msgWF_transfer_update (actor := caller) (nextSt := nextSt)
            (newPend := some ⟨s.history.length, kind⟩)
            hlen_le htag_pres (Nat.le_succ _) le_rfl ?_
            (fun _ _ _ _ _ _ _ h => nomatch h) (hg.msg_wf e he_old)
          intro rId hreq _ _ _ _ _ hph'
          simp only [nextSt, ClientPhase.phase1.injEq] at hph'
          exact Nat.lt_irrefl _ (hph'.1 ▸ hreq)
        · obtain ⟨rfl, hb⟩ := mem_map_tagSender_broadcastAll.mp he_new
          rw [hb]; simp [MsgWF, proc', nextSt, reqId]
      write_unique :=
        ⟨fun i _ v τ hk hτ => by
          have hil := hg.lt_length_of_opTag_some hτ
          simp only [List.getElem_append_left hil] at hk ⊢
          exact hg.write_unique.1 i hil v τ hk hτ,
         fun i j _ _ v₁ v₂ τ hk₁ hk₂ hτ₁ hτ₂ => by
          have hil := hg.lt_length_of_opTag_some hτ₁
          have hjl := hg.lt_length_of_opTag_some hτ₂
          simp only [List.getElem_append_left hil, List.getElem_append_left hjl] at hk₁ hk₂
          exact hg.write_unique.2 i j hil hjl v₁ v₂ τ hk₁ hk₂ hτ₁ hτ₂⟩
      val_valid :=
        ⟨fun q => by
          have hq := tagValidVal_mono hlen_le htag_pres (hg.val_valid.1 q)
          by_cases hqc : q = caller
          · subst hqc; simpa [proc', nextSt] using hq
          · simpa [proc', hqc] using hq,
         fun p => by
          by_cases hp : p = caller
          · subst hp
            simp only [proc', nextSt, Function.update_self, PhaseValValid]
            exact Or.inl ⟨rfl, rfl⟩
          · simp only [proc', Function.update_of_ne hp]
            exact phaseValValid_mono hlen_le htag_pres (hg.val_valid.2.1 p),
         fun i _ stp r τ hst hτ => by
          have hil := hg.lt_length_of_opTag_some hτ
          simp only [List.getElem_append_left hil] at hst
          exact tagValidVal_mono hlen_le htag_pres (hg.val_valid.2.2 i hil stp r τ hst hτ)⟩
      completed_quorum := fun a _ τ_a hcomp hτ => by
        have hal := hg.lt_length_of_opTag_some hτ
        simp only [List.getElem_append_left hal] at hcomp
        obtain ⟨Q, hQcard, hQtag⟩ := hg.completed_quorum a hal τ_a hcomp hτ
        exact ⟨Q, hQcard, fun q hq => (hrep_eq q).symm ▸ hQtag q hq⟩
      prec_phase1 := fun p pend rId knd responses bt bv hp_pend hp_ph a τ_a hprec hτ_a => by
        have hal := hg.lt_length_of_opTag_some hτ_a
        have hno_new_qr : ∀ {q p' rt rv},
            (⟨q, p', .queryResp rId rt rv⟩ : Envelope P (ABDMsg P V)) ∉
              outMsgs.map (tagSender caller) :=
          fun hnew => by obtain ⟨_, ⟨⟩⟩ := mem_map_tagSender_broadcastAll.mp hnew
        by_cases hp : p = caller
        · subst hp
          simp only [proc', nextSt, Function.update_self, Option.some.injEq,
            ClientPhase.phase1.injEq] at hp_pend hp_ph
          subst hp_pend; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hp_ph
          obtain ⟨_, hcomp_a⟩ := (hprec_to_new a).mp hprec
          obtain ⟨Q, hQcard, hQtag⟩ := hg.completed_quorum a hal τ_a hcomp_a hτ_a
          refine ⟨Q, hQcard, fun q hq => (hrep_eq q).symm ▸ hQtag q hq,
            fun q _ rTag rVal hmem => ?_, fun _ _ hm => nomatch hm⟩
          rcases Multiset.mem_add.mp hmem with hold | hnew
          · exact False.elim (Nat.lt_irrefl _ (hg.msg_wf _ hold).1)
          · exact False.elim (hno_new_qr hnew)
        · simp only [proc', Function.update_of_ne hp] at hp_pend hp_ph
          obtain ⟨hpend_lt, _⟩ := hg.pending_info hp_pend
          rw [hprec_old a hal pend.opId hpend_lt] at hprec
          obtain ⟨Q, hQcard, hQrep, hQmsg, hQresp⟩ :=
            hg.prec_phase1 p pend rId knd responses bt bv hp_pend hp_ph a τ_a hprec hτ_a
          refine ⟨Q, hQcard, fun q hq => (hrep_eq q).symm ▸ hQrep q hq,
            fun q hq rTag rVal hmem => ?_, hQresp⟩
          rcases Multiset.mem_add.mp hmem with hold | hnew
          · exact hQmsg q hq rTag rVal hold
          · exact False.elim (hno_new_qr hnew)
      prec_tag := fun a b _ τ_a τ_b hprec hτ_a hτ_b => by
        have hal := hg.lt_length_of_opTag_some hτ_a
        have hbl := hg.lt_length_of_opTag_some hτ_b
        rw [hprec_old a hal b hbl] at hprec
        simp only [List.getElem_append_left hbl]
        exact hg.prec_tag a b hbl τ_a τ_b hprec hτ_a hτ_b }

omit [DecidableEq V] in
private lemma repTag_le_of_onRecv_eq {v₀ : V} {t : ℕ}
    {dest : P} {st nextSt : ABDState P V} {src : P} {body : ABDMsg P V}
    {outMsgs : Multiset (P × ABDMsg P V)} {resp : Option (OpResp V)}
    (hout : (abdProtocol P V v₀ t).onRecv dest st src body = ⟨nextSt, outMsgs, resp⟩) :
    st.repTag ≤ nextSt.repTag := by
  have hns : (abdOnRecv t dest st src body).nextState = nextSt := congrArg StepOut.nextState hout
  exact hns ▸ abdOnRecv_repTag_mono t dest st src body

private lemma prec_phase1_deliver_step {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) {e : Envelope P (ABDMsg P V)}
    {nextSt : ABDState P V} {outMsgs : Multiset (P × ABDMsg P V)}
    (hrep_le : ∀ q : P, (s.proc q).state.repTag ≤
      (Function.update s.proc e.dest ⟨nextSt, (s.proc e.dest).pending⟩ q).state.repTag)
    (hout_qresp : ∀ dest' reqId rTag rVal,
      (dest', .queryResp reqId rTag rVal) ∈ outMsgs → (s.proc e.dest).state.repTag ≤ rTag)
    {p : P} {pnd : PendingOp V} {reqId : ℕ} {knd : OpKind V}
    {resp' : Finset P} {bt' : Tag P} {bv' : V}
    (hp1 : (s.proc p).pending = some pnd)
    (hp2 : (s.proc p).state.phase = .phase1 reqId knd resp' bt' bv')
    {a : ℕ} {τ_a : Tag P} (hpr : prec s.history a pnd.opId) (hτ_old : opTag a = some τ_a) :
    ∃ Q : Finset P, Fintype.card P - t ≤ Q.card ∧
      (∀ q ∈ Q, τ_a ≤
        (Function.update s.proc e.dest ⟨nextSt, (s.proc e.dest).pending⟩ q).state.repTag) ∧
      (∀ q ∈ Q, ∀ rTag rVal,
        ⟨q, p, .queryResp reqId rTag rVal⟩ ∈
          s.msgs.erase e + outMsgs.map (tagSender e.dest) → τ_a ≤ rTag) ∧
      (∀ q ∈ Q, q ∈ resp' → τ_a ≤ bt') := by
  obtain ⟨Q, hQc, hQr, hQm, hQresp⟩ :=
    hg.prec_phase1 p pnd reqId knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_old
  refine ⟨Q, hQc, fun q hq => (hQr q hq).trans (hrep_le q), ?_, hQresp⟩
  intro q hq rt rv hm
  rcases Multiset.mem_add.mp hm with hm_old | hm_new
  · exact hQm q hq rt rv (Multiset.mem_of_mem_erase hm_old)
  · obtain ⟨⟨dest', body'⟩, hpm, heq⟩ := Multiset.mem_map.mp hm_new
    injection heq with hsrc _ hbody; subst hsrc hbody
    exact (hQr e.dest hq).trans (hout_qresp dest' reqId rt rv hpm)

/-- Unified `ABDGood` preservation lemma for any message delivery whose local handler returns
`resp = none` (hence leaving `history` and `pending` unchanged). -/
private lemma abdGood_deliver_resp_none {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag opTag' : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) {e : Envelope P (ABDMsg P V)}
    {nextSt : ABDState P V} {outMsgs : Multiset (P × ABDMsg P V)}
    (hout : (abdProtocol P V v₀ t).onRecv e.dest (s.proc e.dest).state e.src e.body =
      ⟨nextSt, outMsgs, none⟩)
    (htag_out : ∀ i, s.history.length ≤ i → opTag' i = none)
    (htag_pres : ∀ i τ, opTag i = some τ → opTag' i = some τ)
    (hcomp_tag : ∀ (a : ℕ) (ha : a < s.history.length) τ_a,
      s.history[a].status.isCompleted = true → opTag' a = some τ_a → opTag a = some τ_a)
    (htag_other : ∀ p, p ≠ e.dest → ∀ pend, (s.proc p).pending = some pend →
      opTag' pend.opId = opTag pend.opId)
    (hps_dest : ProcSync t s.history nextSt.nextReqId
      (fun q => (Function.update s.proc e.dest ⟨nextSt, (s.proc e.dest).pending⟩ q).state.repTag)
      opTag' e.dest (s.proc e.dest).pending nextSt.phase)
    (hnext_dest : (s.proc e.dest).state.nextReqId ≤ nextSt.nextReqId)
    (hp1_dest : ∀ reqId, reqId < (s.proc e.dest).state.nextReqId →
      (∀ knd resp bt bv, (s.proc e.dest).state.phase = .phase1 reqId knd resp bt bv → False) →
      ∀ knd resp bt bv, nextSt.phase = .phase1 reqId knd resp bt bv → False)
    (hp2_dest : ∀ reqId, reqId < (s.proc e.dest).state.nextReqId →
      (∀ knd resp bt bv, (s.proc e.dest).state.phase = .phase1 reqId knd resp bt bv → False) →
      ∀ knd cTag cVal acks, nextSt.phase = .phase2 reqId knd cTag cVal acks →
        ∃ acks₀, (s.proc e.dest).state.phase = .phase2 reqId knd cTag cVal acks₀)
    (hout_wf : ∀ pm ∈ outMsgs,
      MsgWF v₀
        { msgs := s.msgs.erase e + outMsgs.map (tagSender e.dest)
          proc := Function.update s.proc e.dest ⟨nextSt, (s.proc e.dest).pending⟩
          history := s.history
          step := s.step + 1 }
        opTag' e.dest pm.1 pm.2)
    (hout_qresp : ∀ dest' reqId rTag rVal,
      (dest', .queryResp reqId rTag rVal) ∈ outMsgs → (s.proc e.dest).state.repTag ≤ rTag)
    (hwu :
      (∀ (i : ℕ) (hi : i < s.history.length) v τ,
        s.history[i].kind = .write v → opTag' i = some τ →
        ∃ seq, τ = nextWriteTag seq s.history[i].caller) ∧
      (∀ (i j : ℕ) (hi : i < s.history.length) (hj : j < s.history.length) v₁ v₂ τ,
        s.history[i].kind = .write v₁ → s.history[j].kind = .write v₂ →
        opTag' i = some τ → opTag' j = some τ → i = j))
    (hrep_val_dest : TagValidVal v₀ s.history opTag' nextSt.repTag nextSt.repVal)
    (hphase_val_dest : PhaseValValid v₀ s.history opTag' nextSt.phase)
    (hread_val : ∀ (i : ℕ) (hi : i < s.history.length) step r τ,
      s.history[i].status = .doneRead step r → opTag' i = some τ →
      TagValidVal v₀ s.history opTag' τ r)
    (hp1_dest_prec : ∀ pend reqId knd resp' bt' bv',
      (s.proc e.dest).pending = some pend →
      nextSt.phase = .phase1 reqId knd resp' bt' bv' →
      ∀ a τ_a, prec s.history a pend.opId → opTag a = some τ_a →
      ∃ Q : Finset P, Fintype.card P - t ≤ Q.card ∧
        (∀ q ∈ Q,
          τ_a ≤ (Function.update s.proc e.dest
            ⟨nextSt, (s.proc e.dest).pending⟩ q).state.repTag) ∧
        (∀ q ∈ Q, ∀ rTag rVal,
          ⟨q, e.dest, .queryResp reqId rTag rVal⟩ ∈
            s.msgs.erase e + outMsgs.map (tagSender e.dest) → τ_a ≤ rTag) ∧
        (∀ q ∈ Q, q ∈ resp' → τ_a ≤ bt'))
    (hprec_tag : ∀ (a b : ℕ) (hb : b < s.history.length) τ_a τ_b,
      prec s.history a b → opTag' a = some τ_a → opTag' b = some τ_b →
      PrecTagOrder τ_a τ_b s.history[b].kind) :
    ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag' := by
  rw [(abdProtocol P V v₀ t).doDeliver_of_resp_eq_none hout]
  set proc' := Function.update s.proc e.dest ⟨nextSt, (s.proc e.dest).pending⟩
  have hrep_dest := repTag_le_of_onRecv_eq hout
  have hrep_le := update_proc_repTag_le s.proc (newPend := (s.proc e.dest).pending) hrep_dest
  have hpend_eq : ∀ p : P, (proc' p).pending = (s.proc p).pending := by
    intro p; by_cases hp : p = e.dest <;> [subst hp; skip] <;> simp [proc', *]
  have hsome_pres : ∀ i, (opTag i).isSome = true → (opTag' i).isSome = true := by
    intro i hs
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs
    exact Option.isSome_iff_exists.mpr ⟨τ, htag_pres i τ hτ⟩
  have htv_pres : ∀ (i : ℕ) (hi : i < s.history.length) τ,
      opTag i = some τ → s.history[i].kind = s.history[i].kind ∧ opTag' i = some τ :=
    fun i _ τ hτ => ⟨rfl, htag_pres i τ hτ⟩
  refine
    { tag_out := htag_out
      hist_wf := fun i hi => by
        obtain ⟨h1, h2, h3, h4, h5⟩ := hg.hist_wf i hi
        exact ⟨Nat.lt_succ_of_lt h1,
          fun r hr => ⟨(h2 r hr).1, Nat.lt_succ_of_lt (h2 r hr).2⟩,
          fun r v hr => ⟨(h3 r v hr).1, hsome_pres i (h3 r v hr).2⟩,
          fun r hr => ⟨(h4 r hr).1, hsome_pres i (h4 r hr).2⟩,
          fun hp => (hpend_eq s.history[i].caller).trans (h5 hp)⟩
      inv_mono := hg.inv_mono
      proc_sync := fun p => by
        change ProcSync t s.history (proc' p).state.nextReqId (fun q => (proc' q).state.repTag)
          opTag' p (proc' p).pending (proc' p).state.phase
        by_cases hp : p = e.dest
        · subst hp; simpa [proc'] using hps_dest
        · simp only [proc', Function.update_of_ne hp]
          exact procSync_mono le_rfl hrep_le (htag_other p hp) (hg.proc_sync p)
      msg_wf := fun m hm => by
        rcases Multiset.mem_add.mp hm with hm_old | hm_new
        · exact msgWF_transfer_update le_rfl htv_pres hnext_dest hrep_dest hp1_dest hp2_dest
            (hg.msg_wf m (Multiset.mem_of_mem_erase hm_old))
        · obtain ⟨pm, hpm, rfl⟩ := Multiset.mem_map.mp hm_new
          exact hout_wf pm hpm
      write_unique := hwu
      val_valid :=
        ⟨fun q => by
          by_cases hqd : q = e.dest
          · subst hqd; simpa [proc'] using hrep_val_dest
          · simp only [proc', Function.update_of_ne hqd]
            exact tagValidVal_mono le_rfl htv_pres (hg.val_valid.1 q),
         fun p => by
          by_cases hp : p = e.dest
          · subst hp; simpa [proc'] using hphase_val_dest
          · simp only [proc', Function.update_of_ne hp]
            exact phaseValValid_mono le_rfl htv_pres (hg.val_valid.2.1 p),
         hread_val⟩
      completed_quorum := fun a ha τ_a hcomp hτ => by
        obtain ⟨Q, hQc, hQr⟩ := hg.completed_quorum a ha τ_a hcomp (hcomp_tag a ha τ_a hcomp hτ)
        exact ⟨Q, hQc, fun q hq => (hQr q hq).trans (hrep_le q)⟩
      prec_phase1 := fun p pnd reqId knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_a => by
        rw [hpend_eq p] at hp1
        have ⟨ha_lt, _, _, hr_step, _⟩ := hpr
        have ha_comp : s.history[a].status.isCompleted = true := by
          simp [OpStatus.isCompleted, hr_step]
        have hτ_old := hcomp_tag a ha_lt τ_a ha_comp hτ_a
        by_cases hp : p = e.dest
        · subst hp; simp only [proc', Function.update_self] at hp2
          exact hp1_dest_prec pnd reqId knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_old
        · simp only [proc', Function.update_of_ne hp] at hp2
          exact prec_phase1_deliver_step hg hrep_le hout_qresp hp1 hp2 hpr hτ_old
      prec_tag := hprec_tag }

/-- Specialization of `abdGood_deliver_resp_none` when `opTag` is unchanged (`opTag' = opTag`). -/
private lemma abdGood_deliver_same_opTag {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) {e : Envelope P (ABDMsg P V)}
    {nextSt : ABDState P V} {outMsgs : Multiset (P × ABDMsg P V)}
    (hout : (abdProtocol P V v₀ t).onRecv e.dest (s.proc e.dest).state e.src e.body =
      ⟨nextSt, outMsgs, none⟩)
    (hps_dest : ProcSync t s.history nextSt.nextReqId
      (fun q => (Function.update s.proc e.dest ⟨nextSt, (s.proc e.dest).pending⟩ q).state.repTag)
      opTag e.dest (s.proc e.dest).pending nextSt.phase)
    (hnext_dest : (s.proc e.dest).state.nextReqId ≤ nextSt.nextReqId)
    (hp1_dest : ∀ reqId, reqId < (s.proc e.dest).state.nextReqId →
      (∀ knd resp bt bv, (s.proc e.dest).state.phase = .phase1 reqId knd resp bt bv → False) →
      ∀ knd resp bt bv, nextSt.phase = .phase1 reqId knd resp bt bv → False)
    (hp2_dest : ∀ reqId, reqId < (s.proc e.dest).state.nextReqId →
      (∀ knd resp bt bv, (s.proc e.dest).state.phase = .phase1 reqId knd resp bt bv → False) →
      ∀ knd cTag cVal acks, nextSt.phase = .phase2 reqId knd cTag cVal acks →
        ∃ acks₀, (s.proc e.dest).state.phase = .phase2 reqId knd cTag cVal acks₀)
    (hout_wf : ∀ pm ∈ outMsgs,
      MsgWF v₀
        { msgs := s.msgs.erase e + outMsgs.map (tagSender e.dest)
          proc := Function.update s.proc e.dest ⟨nextSt, (s.proc e.dest).pending⟩
          history := s.history
          step := s.step + 1 }
        opTag e.dest pm.1 pm.2)
    (hout_qresp : ∀ dest' reqId rTag rVal,
      (dest', .queryResp reqId rTag rVal) ∈ outMsgs → (s.proc e.dest).state.repTag ≤ rTag)
    (hrep_val_dest : TagValidVal v₀ s.history opTag nextSt.repTag nextSt.repVal)
    (hphase_val_dest : PhaseValValid v₀ s.history opTag nextSt.phase)
    (hp1_dest_prec : ∀ pend reqId knd resp' bt' bv',
      (s.proc e.dest).pending = some pend →
      nextSt.phase = .phase1 reqId knd resp' bt' bv' →
      ∀ a τ_a, prec s.history a pend.opId → opTag a = some τ_a →
      ∃ Q : Finset P, Fintype.card P - t ≤ Q.card ∧
        (∀ q ∈ Q,
          τ_a ≤ (Function.update s.proc e.dest
            ⟨nextSt, (s.proc e.dest).pending⟩ q).state.repTag) ∧
        (∀ q ∈ Q, ∀ rTag rVal,
          ⟨q, e.dest, .queryResp reqId rTag rVal⟩ ∈
            s.msgs.erase e + outMsgs.map (tagSender e.dest) → τ_a ≤ rTag) ∧
        (∀ q ∈ Q, q ∈ resp' → τ_a ≤ bt')) :
    ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag :=
  abdGood_deliver_resp_none hg hout hg.tag_out (fun _ _ h => h) (fun _ _ _ _ h => h)
    (fun _ _ _ _ => rfl) hps_dest hnext_dest hp1_dest hp2_dest hout_wf hout_qresp
    hg.write_unique hrep_val_dest hphase_val_dest hg.val_valid.2.2 hp1_dest_prec hg.prec_tag

/-- Preservation of `ABDGood` for any delivery with `resp = none` that leaves `phase` and
`nextReqId` at `e.dest` unchanged (stale messages and replica `.query` / `.store` handlers). -/
private lemma abdGood_deliver_keep_phase {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) {e : Envelope P (ABDMsg P V)}
    {nextSt : ABDState P V} {outMsgs : Multiset (P × ABDMsg P V)}
    (hout : (abdProtocol P V v₀ t).onRecv e.dest (s.proc e.dest).state e.src e.body =
      ⟨nextSt, outMsgs, none⟩)
    (hphase_eq : nextSt.phase = (s.proc e.dest).state.phase)
    (hnext_eq : nextSt.nextReqId = (s.proc e.dest).state.nextReqId)
    (hout_wf : ∀ pm ∈ outMsgs,
      MsgWF v₀
        { msgs := s.msgs.erase e + outMsgs.map (tagSender e.dest)
          proc := Function.update s.proc e.dest ⟨nextSt, (s.proc e.dest).pending⟩
          history := s.history
          step := s.step + 1 }
        opTag e.dest pm.1 pm.2)
    (hout_qresp : ∀ dest' reqId rTag rVal,
      (dest', .queryResp reqId rTag rVal) ∈ outMsgs → (s.proc e.dest).state.repTag ≤ rTag)
    (hrep_val_dest : TagValidVal v₀ s.history opTag nextSt.repTag nextSt.repVal) :
    ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag := by
  have hrep_le := update_proc_repTag_le s.proc (newPend := (s.proc e.dest).pending)
    (repTag_le_of_onRecv_eq hout)
  exact abdGood_deliver_same_opTag hg hout
    (hnext_eq.symm ▸ hphase_eq.symm ▸ procSync_mono le_rfl hrep_le (fun _ _ => rfl)
      (hg.proc_sync e.dest))
    hnext_eq.symm.le
    (fun _ _ hp1 knd resp bt bv hph => hp1 knd resp bt bv (hphase_eq.symm.trans hph))
    (fun _ _ _ _ _ _ acks hph => ⟨acks, hphase_eq.symm.trans hph⟩)
    hout_wf hout_qresp hrep_val_dest (hphase_eq ▸ hg.val_valid.2.1 e.dest)
    fun _ _ _ _ _ _ hp1 hp2 _ _ hpr hτ =>
      prec_phase1_deliver_step hg hrep_le hout_qresp hp1 (hphase_eq.symm.trans hp2) hpr hτ

/-- Helper for a message delivery that leaves local states, `pending`, and `history` unchanged and
emits zero messages (stale or out-of-phase messages). -/
private lemma abdGood_deliver_noop {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) {e : Envelope P (ABDMsg P V)}
    (hnoop : abdOnRecv t e.dest (s.proc e.dest).state e.src e.body =
      ⟨(s.proc e.dest).state, 0, none⟩) :
    ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag :=
  abdGood_deliver_keep_phase hg hnoop rfl rfl (fun _ hm => nomatch hm)
    (fun _ _ _ _ hm => nomatch hm) (hg.val_valid.1 e.dest)

/-- Helper preserving `ABDGood` when a replica handles `.query` or `.store`. -/
private lemma abdGood_deliver_replica {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) {e : Envelope P (ABDMsg P V)} (he : e ∈ s.msgs)
    (hrep : (∃ reqId, e.body = .query reqId) ∨ (∃ reqId τ v, e.body = .store reqId τ v)) :
    ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag := by
  let out := abdOnRecv t e.dest (s.proc e.dest).state e.src e.body
  have hout_resp : out.resp = none := by
    rcases hrep with ⟨_, hb⟩ | ⟨_, _, _, hb⟩ <;> simp [out, hb, abdOnRecv]
  have hout : (abdProtocol P V v₀ t).onRecv e.dest (s.proc e.dest).state e.src e.body =
      ⟨out.nextState, out.outgoing, none⟩ := by
    change out = ⟨out.nextState, out.outgoing, none⟩; rw [← hout_resp]
  have hphase_eq : out.nextState.phase = (s.proc e.dest).state.phase := by
    rcases hrep with ⟨_, hb⟩ | ⟨_, _, _, hb⟩
    · simp [out, hb, abdOnRecv]
    · simp only [out, hb, abdOnRecv]; split_ifs <;> rfl
  have hnext_eq : out.nextState.nextReqId = (s.proc e.dest).state.nextReqId := by
    rcases hrep with ⟨_, hb⟩ | ⟨_, _, _, hb⟩
    · simp [out, hb, abdOnRecv]
    · simp only [out, hb, abdOnRecv]; split_ifs <;> rfl
  have hsrc_pair :
      let st' := (Function.update s.proc e.dest
        ⟨out.nextState, (s.proc e.dest).pending⟩ e.src).state
      st'.phase = (s.proc e.src).state.phase ∧
        st'.nextReqId = (s.proc e.src).state.nextReqId := by
    dsimp only
    by_cases hs : e.src = e.dest
    · rw [hs, Function.update_self]; exact ⟨hphase_eq, hnext_eq⟩
    · simp [hs]
  obtain ⟨hsrc_phase, hsrc_next⟩ := hsrc_pair
  refine abdGood_deliver_keep_phase hg hout hphase_eq hnext_eq ?_ ?_ ?_
  · intro pm hpm
    rcases hrep with ⟨reqId, hb⟩ | ⟨reqId, inTag, inVal, hb⟩
    · simp only [out, hb, abdOnRecv, Multiset.mem_singleton] at hpm
      subst hpm
      have he_wf := hg.msg_wf e he; rw [hb] at he_wf
      exact ⟨hsrc_next.symm ▸ he_wf, hg.val_valid.1 e.dest⟩
    · simp only [out, hb, abdOnRecv, Multiset.mem_singleton] at hpm
      subst hpm
      have he_wf := hg.msg_wf e he; rw [hb] at he_wf
      obtain ⟨hreq, _, hp1, hp2⟩ := he_wf
      refine ⟨hsrc_next.symm ▸ hreq,
        fun knd resp bt bv hph => hp1 knd resp bt bv (hsrc_phase.symm.trans hph),
        fun knd cTag cVal acks hph => ?_⟩
      obtain ⟨hcT, _⟩ := hp2 knd cTag cVal acks (hsrc_phase.symm.trans hph)
      rw [← hcT]
      simpa [out, hb] using
        abdOnRecv_store_le_repTag t e.dest (s.proc e.dest).state e.src reqId inTag inVal
  · intro dest' reqId rTag rVal hm
    rcases hrep with ⟨_, hb⟩ | ⟨_, _, _, hb⟩
    · simp only [out, hb, abdOnRecv, Multiset.mem_singleton, Prod.mk.injEq,
        ABDMsg.queryResp.injEq] at hm
      exact hm.2.2.1 ▸ le_rfl
    · simp [out, hb, abdOnRecv] at hm
  · rcases hrep with ⟨_, hb⟩ | ⟨_, inTag, inVal, hb⟩
    · simpa [out, hb, abdOnRecv] using hg.val_valid.1 e.dest
    · simp only [out, hb, abdOnRecv]
      split_ifs
      · have he_wf := hg.msg_wf e he; rw [hb] at he_wf; exact he_wf.2.1
      · exact hg.val_valid.1 e.dest

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
    · exact False.elim (hne rfl)
    · exact False.elim hps
    · exact False.elim hps
  | some pend => exact ⟨pend, rfl⟩

/-- Phase-2 `(chosenTag, chosenVal)` selected by `dest` upon completing Phase 1 with `(bt, bv)`. -/
private def phase2Choice (dest : P) : OpKind V → Tag P → V → Tag P × V
  | .write v, bt, _ => (nextWriteTag bt.seq dest, v)
  | .read, bt, bv => (bt, bv)

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
  have htv_pres : ∀ (i : ℕ) (hi : i < s.history.length) τ,
      opTag i = some τ → s.history[i].kind = s.history[i].kind ∧ opTag' i = some τ :=
    fun i _ τ hτ => ⟨rfl, htag_pres i τ hτ⟩
  have hprec_all_a : ∀ (a : ℕ) τ_a, prec s.history a pend.opId → opTag a = some τ_a →
      τ_a ≤ bestTag' := by
    intro a τ_a hprec hτ_a
    obtain ⟨Q, hQcard, _, hQmsg, hQresp⟩ :=
      hg.prec_phase1 e.dest pend rId kind responses bestTag bestVal hp_dest hph_dest a τ_a hprec
        hτ_a
    obtain ⟨q, hq_inter⟩ := quorum_inter_nonempty h2t hQcard hquorum
    obtain ⟨hqQ, hqR'⟩ := Finset.mem_inter.mp hq_inter
    exact hresp'_le hQmsg hQresp q hqQ hqR'
  have hchosen_valid : TagValidVal v₀ s.history opTag' chosenTag chosenVal := by
    cases kind with
    | read => exact tagValidVal_mono le_rfl htv_pres hbestVal'
    | write _ => exact Or.inr ⟨pend.opId, hi_pend, hk_pend, Function.update_self ..⟩
  refine ⟨opTag', abdGood_deliver_resp_none hg hout ?_ htag_pres ?_ ?_ ?_ le_rfl
    (fun _ _ _ _ _ _ _ h => nomatch h) ?_ ?_ ?_ ?_ ?_ hchosen_valid ?_
    (fun _ _ _ _ _ _ _ h => nomatch h) ?_⟩
  · intro i hi
    exact (Function.update_of_ne (by omega) _ opTag).trans (hg.tag_out i hi)
  · intro a _ τ_a hcomp hτ
    have hap : a ≠ pend.opId := fun heq => by subst heq; rw [hst_pend] at hcomp; cases hcomp
    simpa only [opTag', Function.update_of_ne hap] using hτ
  · exact fun p hp pnd hpnd =>
      Function.update_of_ne (hg.pending_opId_ne hp hpnd hp_dest) _ opTag
  · rw [hp_dest]
    dsimp only [nextSt, ProcSync]
    exact ⟨hi_pend, hc_pend, hk_pend, hpk_pend, hst_pend, Function.update_self .., hreq_lt,
      by simpa using hq_pos, fun _ hm => False.elim (Finset.notMem_empty _ hm), hprev_pend⟩
  · intro reqId' _ hp1 _ _ _ _ hph'
    simp only [nextSt, ClientPhase.phase2.injEq] at hph'
    exact False.elim (hp1 kind responses bestTag bestVal (hph'.1 ▸ hph_dest))
  · intro pm hpm
    simp only [outMsgs, broadcastAll, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
      true_and] at hpm
    obtain ⟨q, rfl⟩ := hpm
    dsimp only [MsgWF, nextSt]; rw [Function.update_self]
    refine ⟨hreq_lt, hchosen_valid, (fun _ _ _ _ h => nomatch h), fun _ _ _ _ hph => ?_⟩
    injection hph with _ _ hcT hcV _; exact ⟨hcT, hcV⟩
  · intro _ _ _ _ hm; simp [outMsgs, broadcastAll] at hm
  · have hfresh_write : ∀ k (hk : k < s.history.length) vk vw,
        kind = .write vw → k ≠ pend.opId →
        s.history[k].kind = .write vk → opTag k ≠ some chosenTag := by
      intro k hk vk vw hkw_kind hkne hkw hτk
      obtain ⟨seq_k, hτk_eq⟩ := hg.write_unique.1 k hk vk chosenTag hkw hτk
      have hc_eq : chosenTag = nextWriteTag bestTag'.seq e.dest := by
        simp [chosenTag, cv, phase2Choice, hkw_kind]
      have hwriter := congrArg Tag.writer (hτk_eq.symm.trans hc_eq)
      simp only [nextWriteTag_writer, WithBot.coe_inj] at hwriter
      have hle := hprec_all_a k chosenTag (hprev_pend k hk hkne hwriter) hτk
      exact lt_irrefl chosenTag (hc_eq ▸ lt_nextWriteTag_of_seq_le (seq_le_of_le hle) e.dest)
    refine ⟨fun i hi v τ hk hτ => ?_, fun i j hi hj v₁ v₂ τ hk₁ hk₂ hτ₁ hτ₂ => ?_⟩
    · by_cases hip : i = pend.opId
      · subst hip
        simp only [opTag', Function.update_self, Option.some.injEq] at hτ; subst hτ
        rw [hk_pend] at hk; cases hk
        exact ⟨bestTag'.seq, hc_pend ▸ rfl⟩
      · simp only [opTag', Function.update_of_ne hip] at hτ
        exact hg.write_unique.1 i hi v τ hk hτ
    · rcases eq_or_ne i pend.opId with rfl | hi_p <;>
        rcases eq_or_ne j pend.opId with rfl | hj_p
      · rfl
      · simp only [opTag', Function.update_self, Function.update_of_ne hj_p,
          Option.some.injEq] at hτ₁ hτ₂
        exact False.elim (hfresh_write j hj v₂ v₁ (hk_pend.symm.trans hk₁) hj_p hk₂ (hτ₁ ▸ hτ₂))
      · simp only [opTag', Function.update_self, Function.update_of_ne hi_p,
          Option.some.injEq] at hτ₁ hτ₂
        exact False.elim (hfresh_write i hi v₁ v₂ (hk_pend.symm.trans hk₂) hi_p hk₁ (hτ₂ ▸ hτ₁))
      · simp only [opTag', Function.update_of_ne hi_p, Function.update_of_ne hj_p] at hτ₁ hτ₂
        exact hg.write_unique.2 i j hi hj v₁ v₂ τ hk₁ hk₂ hτ₁ hτ₂
  · exact tagValidVal_mono le_rfl htv_pres (hg.val_valid.1 e.dest)
  · intro i hi stp r τ hst hτ
    have hip : i ≠ pend.opId := fun heq => by subst heq; rw [hst_pend] at hst; cases hst
    simp only [opTag', Function.update_of_ne hip] at hτ
    exact tagValidVal_mono le_rfl htv_pres (hg.val_valid.2.2 i hi stp r τ hst hτ)
  · intro a b hb τ_a τ_b hpr hτ_a hτ_b
    have hap : a ≠ pend.opId := fun heq => by
      subst heq; obtain ⟨_, _, _, hr, _⟩ := hpr; simp [hst_pend, OpStatus.respStep?] at hr
    simp only [opTag', Function.update_of_ne hap] at hτ_a
    by_cases hbp : b = pend.opId
    · subst hbp
      simp only [opTag', Function.update_self, Option.some.injEq] at hτ_b; subst hτ_b
      have hle := hprec_all_a a τ_a hpr hτ_a
      rw [hk_pend]
      cases kind with
      | read => exact hle
      | write _ => exact lt_nextWriteTag_of_seq_le (seq_le_of_le hle) e.dest
    · simp only [opTag', Function.update_of_ne hbp] at hτ_b
      exact hg.prec_tag a b hb τ_a τ_b hpr hτ_a hτ_b

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
        have hrep_same := update_proc_repTag_eq s.proc
          (nextSt := nextSt) (newPend := (s.proc e.dest).pending) rfl
        refine ⟨opTag, abdGood_deliver_same_opTag hg hout ?_ le_rfl ?_
          (fun _ _ _ _ _ _ _ h => nomatch h) (fun _ hm => nomatch hm)
          (fun _ _ _ _ hm => nomatch hm) (hg.val_valid.1 e.dest) hbestVal' ?_⟩
        · rw [hp_dest]
          exact ⟨hi_pend, hc_pend, hk_pend, hpk_pend, hst_pend, htag_pend, hreq_lt,
            Nat.lt_of_not_le hquorum, hprev_pend⟩
        · intro reqId' _ hp1 _ _ _ _ hph'
          simp only [nextSt, ClientPhase.phase1.injEq] at hph'
          exact hp1 kind responses bestTag bestVal (hph'.1 ▸ hph_dest)
        · intro pnd reqId' knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_a
          rw [hp_dest, Option.some.injEq] at hp1; subst hp1
          simp only [nextSt, ClientPhase.phase1.injEq] at hp2
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hp2
          obtain ⟨Q, hQc, hQr, hQm, hQresp⟩ :=
            hg.prec_phase1 e.dest pend rId kind responses bestTag bestVal hp_dest hph_dest
              a τ_a hpr hτ_a
          refine ⟨Q, hQc, fun q hq => (hrep_same q).symm ▸ hQr q hq,
            fun q hq rt rv hm => ?_, hresp'_le hQm hQresp⟩
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
  set proc' := Function.update s.proc e.dest ⟨nextSt, none⟩
  have hlen_eq : hist'.length = s.history.length := List.length_set
  have hrep_eq : ∀ q : P, (proc' q).state.repTag = (s.proc q).state.repTag :=
    update_proc_repTag_eq s.proc rfl
  have hmeta_eq : ∀ (i : ℕ) (hi : i < s.history.length),
      (hist'[i]'(hlen_eq.symm ▸ hi)).caller = s.history[i].caller ∧
      (hist'[i]'(hlen_eq.symm ▸ hi)).kind = s.history[i].kind ∧
      (hist'[i]'(hlen_eq.symm ▸ hi)).invStep = s.history[i].invStep := by
    intro i _
    by_cases hip : i = pend.opId
    · subst hip; simp [hist']
    · simp [hist', List.getElem_set_ne (Ne.symm hip)]
  have htv_to_new : ∀ {τ v},
      TagValidVal v₀ s.history opTag τ v → TagValidVal v₀ hist' opTag τ v :=
    tagValidVal_mono hlen_eq.symm.le fun i hi _ hτ' => ⟨(hmeta_eq i hi).2.1, hτ'⟩
  have hstDone_resp : stDone.respStep? = some s.step := by cases kind <;> rfl
  have hprec_eq := abdGood_prec_complete hg hi_pend hst_pend stDone hstDone_resp
  refine
    { tag_out := hlen_eq ▸ hg.tag_out
      hist_wf := fun i hi => by
        have hi0 : i < s.history.length := hlen_eq ▸ hi
        by_cases hip : i = pend.opId
        · subst hip
          obtain ⟨hinv, _⟩ := hg.hist_wf pend.opId hi0
          simp only [hist', List.getElem_set_self]
          refine ⟨Nat.lt_succ_of_lt hinv, fun r hr => ?_, fun r v hr => ?_,
            fun r hr => ?_, fun hp => ?_⟩
          · rw [hstDone_resp, Option.some.injEq] at hr; subst hr
            exact ⟨Nat.le_of_lt hinv, Nat.lt_succ_self _⟩
          · dsimp only [stDone] at hr
            cases kind <;> [exact ⟨hk_pend, by simp [htag_pend]⟩; cases hr]
          · dsimp only [stDone] at hr
            cases kind with
            | read => cases hr
            | write vw => exact ⟨⟨vw, hk_pend⟩, by simp [htag_pend]⟩
          · dsimp only [stDone] at hp; cases kind <;> cases hp
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hg.hist_wf i hi0
          have hget : hist'[i] = s.history[i] := by simp [hist', List.getElem_set_ne (Ne.symm hip)]
          rw [hget]
          refine ⟨Nat.lt_succ_of_lt h1,
            fun r hr => ⟨(h2 r hr).1, Nat.lt_succ_of_lt (h2 r hr).2⟩, h3, h4, fun hp => ?_⟩
          have hp0 := h5 hp
          have hne_c : s.history[i].caller ≠ e.dest := fun heq => by
            rw [heq, hp_dest, Option.some.injEq] at hp0
            exact hip (congrArg PendingOp.opId hp0).symm
          simpa [proc', Function.update_of_ne hne_c] using hp0
      inv_mono := fun i j hij hj => by
        have hj0 : j < s.history.length := hlen_eq ▸ hj
        rw [(hmeta_eq i (hij.trans hj0)).2.2, (hmeta_eq j hj0).2.2]
        exact hg.inv_mono i j hij hj0
      proc_sync := fun p => by
        change ProcSync t hist' (proc' p).state.nextReqId
          (fun q => (proc' q).state.repTag) opTag p (proc' p).pending (proc' p).state.phase
        by_cases hp : p = e.dest
        · subst hp; simp [proc', nextSt, ProcSync]
        · simp only [proc', Function.update_of_ne hp]
          refine procSync_transport hlen_eq.symm.le le_rfl (fun q => (hrep_eq q).symm.le) ?_
            (hg.proc_sync p)
          intro pnd h1 hpp hc
          have hne_id := hg.pending_opId_ne hp hpp hp_dest
          refine ⟨(hmeta_eq _ h1).1.trans hc, (hmeta_eq _ h1).2.1,
            by simp [hist', List.getElem_set_ne (Ne.symm hne_id)], rfl,
            fun hprev j hj hjne hjc => ?_⟩
          have hj0 : j < s.history.length := hlen_eq ▸ hj
          rw [(hmeta_eq j hj0).1] at hjc
          exact (hprec_eq j _).mpr (hprev j hj0 hjne hjc)
      msg_wf := fun m hm => by
        simp only [Multiset.map_zero, add_zero] at hm
        exact msgWF_transfer_update (actor := e.dest) (nextSt := nextSt) (newPend := none)
          hlen_eq.symm.le (fun i hi _ hτ => ⟨(hmeta_eq i hi).2.1, hτ⟩) le_rfl le_rfl
          (fun _ _ _ _ _ _ _ h => nomatch h) (fun _ _ _ _ _ _ _ h => nomatch h)
          (hg.msg_wf m (Multiset.mem_of_mem_erase hm))
      write_unique :=
        ⟨fun i hi v τ hk hτ => by
          have hi0 : i < s.history.length := hlen_eq ▸ hi
          rw [(hmeta_eq i hi0).2.1] at hk; rw [(hmeta_eq i hi0).1]
          exact hg.write_unique.1 i hi0 v τ hk hτ,
         fun i j hi hj v₁ v₂ τ hk₁ hk₂ hτ₁ hτ₂ => by
          have hi0 : i < s.history.length := hlen_eq ▸ hi
          have hj0 : j < s.history.length := hlen_eq ▸ hj
          rw [(hmeta_eq i hi0).2.1] at hk₁; rw [(hmeta_eq j hj0).2.1] at hk₂
          exact hg.write_unique.2 i j hi0 hj0 v₁ v₂ τ hk₁ hk₂ hτ₁ hτ₂⟩
      val_valid :=
        ⟨fun q => by
          have hq := htv_to_new (hg.val_valid.1 q)
          by_cases hqd : q = e.dest
          · subst hqd; simpa [proc', nextSt] using hq
          · simpa [proc', hqd] using hq,
         fun p => by
          by_cases hp : p = e.dest
          · subst hp; simp [proc', nextSt, PhaseValValid]
          · simp only [proc', Function.update_of_ne hp]
            exact phaseValValid_mono hlen_eq.symm.le
              (fun i hi _ hτ' => ⟨(hmeta_eq i hi).2.1, hτ'⟩) (hg.val_valid.2.1 p),
         fun i hi stp r τ hst hτ => by
          have hi0 : i < s.history.length := hlen_eq ▸ hi
          by_cases hip : i = pend.opId
          · subst hip
            simp only [hist', List.getElem_set_self] at hst; dsimp only [stDone] at hst
            cases kind with
            | write _ => cases hst
            | read =>
              injection hst with _ hr_eq; subst hr_eq
              rw [htag_pend, Option.some.injEq] at hτ; subst hτ
              exact htv_to_new hchosen_valid
          · simp only [hist', List.getElem_set_ne (Ne.symm hip)] at hst
            exact htv_to_new (hg.val_valid.2.2 i hi0 stp r τ hst hτ)⟩
      completed_quorum := fun a ha τ_a hcomp hτ => by
        have ha0 : a < s.history.length := hlen_eq ▸ ha
        by_cases hap : a = pend.opId
        · subst hap
          rw [htag_pend, Option.some.injEq] at hτ; subst hτ
          exact ⟨insert e.src acks, hquorum, fun q hq => (hrep_eq q).symm ▸ hacks'_le q hq⟩
        · simp only [hist', List.getElem_set_ne (Ne.symm hap)] at hcomp
          obtain ⟨Q, hQc, hQr⟩ := hg.completed_quorum a ha0 τ_a hcomp hτ
          exact ⟨Q, hQc, fun q hq => (hrep_eq q).symm ▸ hQr q hq⟩
      prec_phase1 := fun p pnd reqId' knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_a => by
        by_cases hp : p = e.dest
        · subst hp; simp [proc', nextSt] at hp2
        · simp only [proc', Function.update_of_ne hp] at hp1 hp2
          rw [hprec_eq] at hpr
          obtain ⟨Q, hQc, hQr, hQm, hQresp⟩ :=
            hg.prec_phase1 p pnd reqId' knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_a
          refine ⟨Q, hQc, fun q hq => (hrep_eq q).symm ▸ hQr q hq,
            fun q hq rt rv hm => ?_, hQresp⟩
          simp only [Multiset.map_zero, add_zero] at hm
          exact hQm q hq rt rv (Multiset.mem_of_mem_erase hm)
      prec_tag := fun a b hb τ_a τ_b hpr hτ_a hτ_b => by
        have hb0 : b < s.history.length := hlen_eq ▸ hb
        rw [hprec_eq] at hpr; rw [(hmeta_eq b hb0).2.1]
        exact hg.prec_tag a b hb0 τ_a τ_b hpr hτ_a hτ_b }

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
      · refine abdGood_deliver_same_opTag
          (nextSt := { (s.proc e.dest).state with
            phase := .phase2 rId kind chosenTag chosenVal acks' })
          (outMsgs := 0) hg
          (by simp [abdProtocol, hb, abdOnRecv, hph_dest, acks', hquorum]) ?_ le_rfl
          (fun _ _ _ _ _ _ _ h => nomatch h) ?_ (fun _ hm => nomatch hm)
          (fun _ _ _ _ hm => nomatch hm) (hg.val_valid.1 e.dest) hchosen_valid
          (fun _ _ _ _ _ _ _ h => nomatch h)
        · rw [hp_dest]
          exact ⟨hi_pend, hc_pend, hk_pend, hpk_pend, hst_pend, htag_pend, hreq_lt,
            Nat.lt_of_not_le hquorum,
            fun q hq => by
              by_cases hqd : q = e.dest
              · subst hqd; simpa using hacks'_le e.dest hq
              · simp only [Function.update_of_ne hqd]; exact hacks'_le q hq,
            hprev_pend⟩
        · intro _ _ _ _ _ _ _ hph'
          simp only [ClientPhase.phase2.injEq] at hph'
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
private lemma not_forall_stay_of_fair {t : ℕ} (h2t : 2 * t < Fintype.card P)
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
  choose stepOf hstep_ge hstep_mem using fun (q : {x // x ∈ Finset.univ \ F}) => hex_q q.1 q.2
  let M := max k₀ (Finset.univ.sup stepOf)
  have hM_ge : k₀ ≤ M := le_max_left _ _
  have hsub : Finset.univ \ F ⊆ coll M := by
    intro q hq
    have hle_M : stepOf ⟨q, hq⟩ ≤ M :=
      (Finset.le_sup (f := stepOf) (Finset.mem_univ ⟨q, hq⟩)).trans (le_max_right _ _)
    exact hcoll_le _ M (hstep_ge ⟨q, hq⟩) hle_M (hstep_mem ⟨q, hq⟩)
  have hlive_card : Fintype.card P - t ≤ (Finset.univ \ F).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ F), Finset.card_univ]
    omega
  have hcard_ge : Fintype.card P - t ≤ (coll M).card :=
    hlive_card.trans (Finset.card_le_card hsub)
  exact Nat.lt_irrefl _ (lt_of_le_of_lt hcard_ge (hcoll_lt M hM_ge))

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
  have hd₂_pos : 0 < d₂ := by
    by_contra h0
    have hd0 : d₂ = 0 := by omega
    exact hd₂_not (hd0 ▸ ⟨∅, initTag P, v₀, hinit_ph⟩)
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
    obtain ⟨_, hg⟩ := hgood k
    obtain ⟨hlt, _, _, hst⟩ := hg.pending_info hp
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
  have hk₁_pos : 0 < k₁ := by
    by_contra h0
    have hk0 : k₁ = 0 := by omega
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
