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

private lemma procSync_mono {P V : Type*} [Fintype P] [LinearOrder P] {t : ℕ}
    {hist : List (OpRecord P V)} {nr₁ nr₂ : ℕ} {rt₁ rt₂ : P → Tag P}
    {opTag₁ opTag₂ : ℕ → Option (Tag P)} {p : P}
    {pend? : Option (PendingOp V)} {ph : ClientPhase P V}
    (hnr : nr₁ ≤ nr₂) (hrt : ∀ q, rt₁ q ≤ rt₂ q)
    (htag : ∀ pend, pend? = some pend → opTag₂ pend.opId = opTag₁ pend.opId)
    (hps : ProcSync t hist nr₁ rt₁ opTag₁ p pend? ph) :
    ProcSync t hist nr₂ rt₂ opTag₂ p pend? ph := by
  cases pend? with
  | none =>
    cases ph <;> exact hps
  | some pend =>
    cases ph with
    | idle => exact hps
    | phase1 _ _ _ _ _ =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hps
      exact ⟨h1, h2, h3, h4, h5, (htag pend rfl).trans h6, lt_of_lt_of_le h7 hnr, h8, h9⟩
    | phase2 _ _ _ _ _ =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hps
      exact ⟨h1, h2, h3, h4, h5, (htag pend rfl).trans h6, lt_of_lt_of_le h7 hnr, h8,
        fun q hq => (h9 q hq).trans (hrt q), h10⟩

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

/-- Shared `MsgWF` preservation across any transition `s → s'` that increases `nextReqId` weakly,
increases `repTag` weakly, preserves `TagValidVal`, and preserves the `.phase1` / `.phase2`
constraints for existing request IDs. -/
private lemma msgWF_transfer {P V : Type*} [LinearOrder P] {v₀ : V}
    {s s' : State P (ABDState P V) (ABDMsg P V) V}
    {opTag opTag' : ℕ → Option (Tag P)}
    (hlen : s.history.length ≤ s'.history.length)
    (htag_pres : ∀ (i : ℕ) (hi : i < s.history.length) τ,
      opTag i = some τ →
      (s'.history[i]'(lt_of_lt_of_le hi hlen)).kind = s.history[i].kind ∧ opTag' i = some τ)
    (hnext_le : ∀ p : P, (s.proc p).state.nextReqId ≤ (s'.proc p).state.nextReqId)
    (hrep_le : ∀ p : P, (s.proc p).state.repTag ≤ (s'.proc p).state.repTag)
    (hp1_back : ∀ p reqId, reqId < (s.proc p).state.nextReqId →
      (∀ knd resp bt bv, (s.proc p).state.phase = .phase1 reqId knd resp bt bv → False) →
      ∀ knd resp bt bv, (s'.proc p).state.phase = .phase1 reqId knd resp bt bv → False)
    (hp2_back : ∀ p reqId, reqId < (s.proc p).state.nextReqId →
      (∀ knd resp bt bv, (s.proc p).state.phase = .phase1 reqId knd resp bt bv → False) →
      ∀ knd cTag cVal acks, (s'.proc p).state.phase = .phase2 reqId knd cTag cVal acks →
        ∃ acks₀, (s.proc p).state.phase = .phase2 reqId knd cTag cVal acks₀)
    {e : Envelope P (ABDMsg P V)} (hw : MsgWF v₀ s opTag e.src e.dest e.body) :
    MsgWF v₀ s' opTag' e.src e.dest e.body := by
  cases hb : e.body with
  | query reqId =>
    rw [hb] at hw
    dsimp only [MsgWF] at hw ⊢
    exact lt_of_lt_of_le hw (hnext_le e.src)
  | queryResp reqId τ v =>
    rw [hb] at hw
    dsimp only [MsgWF] at hw ⊢
    exact ⟨lt_of_lt_of_le hw.1 (hnext_le e.dest), tagValidVal_mono hlen htag_pres hw.2⟩
  | store reqId τ v =>
    rw [hb] at hw
    dsimp only [MsgWF] at hw ⊢
    obtain ⟨hreq, htv, hp1, hp2⟩ := hw
    refine ⟨lt_of_lt_of_le hreq (hnext_le e.src), tagValidVal_mono hlen htag_pres htv,
      hp1_back e.src reqId hreq hp1, ?_⟩
    intro knd cTag cVal acks hph'
    obtain ⟨acks₀, hph₀⟩ := hp2_back e.src reqId hreq hp1 knd cTag cVal acks hph'
    exact hp2 knd cTag cVal acks₀ hph₀
  | ack reqId =>
    rw [hb] at hw
    dsimp only [MsgWF] at hw ⊢
    obtain ⟨hreq, hp1, hp2⟩ := hw
    refine ⟨lt_of_lt_of_le hreq (hnext_le e.dest), hp1_back e.dest reqId hreq hp1, ?_⟩
    intro knd cTag cVal acks hph'
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
  have hout : (abdProtocol P V v₀ t).onInvoke caller (s.proc caller).state kind =
      ⟨nextSt, outMsgs, none⟩ := rfl
  rw [(abdProtocol P V v₀ t).doInvoke_of_resp_eq_none hout]
  let rec' : OpRecord P V := ⟨caller, kind, s.step, .pending⟩
  set proc' := Function.update s.proc caller ⟨nextSt, some ⟨s.history.length, kind⟩⟩
  have hrep_eq : ∀ q : P, (proc' q).state.repTag = (s.proc q).state.repTag := by
    intro q
    by_cases hq : q = caller
    · subst hq; simp [proc', nextSt]
    · simp [proc', hq]
  obtain ⟨hprec_old, _, hprec_to_new⟩ := abdGood_prec_append hg rec' rfl rfl
  have hlen_le : s.history.length ≤ (s.history ++ [rec']).length := by simp
  have htag_pres : ∀ (i : ℕ) (hi : i < s.history.length) τ,
      opTag i = some τ →
      ((s.history ++ [rec'])[i]'(lt_of_lt_of_le hi hlen_le)).kind = s.history[i].kind ∧
        opTag i = some τ := by
    intro i hi τ hτ
    exact ⟨by simp [List.getElem_append_left hi], hτ⟩
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
          have hne : s.history[i].caller ≠ caller := by
            intro heq; rw [heq, hpend_none] at hp'; cases hp'
          simpa [proc', Function.update_of_ne hne] using hp'
        · have heq : i = s.history.length := by omega
          subst heq
          simp [proc', OpStatus.respStep?]
      inv_mono := fun i j hij hj => by
        have hj_len : j < s.history.length + 1 := by simpa using hj
        by_cases hjl : j < s.history.length
        · have hil : i < s.history.length := hij.trans hjl
          simp only [List.getElem_append_left hil, List.getElem_append_left hjl]
          exact hg.inv_mono i j hij hjl
        · have heq : j = s.history.length := by omega
          subst heq
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
          rw [hprec_to_new]
          refine ⟨hjl, ?_⟩
          cases hst : s.history[j].status with
          | doneRead _ _ => rfl
          | doneWrite _ => rfl
          | pending =>
            have hpnd := (hg.hist_wf j hjl).2.2.2.2 hst
            rw [hjc, hpend_none] at hpnd; cases hpnd
        · simp only [proc', Function.update_of_ne hp]
          cases hpp : (s.proc p).pending <;> cases hph : (s.proc p).state.phase
          · trivial
          · have hps := hg.proc_sync p; rw [hpp, hph] at hps; exact hps
          · have hps := hg.proc_sync p; rw [hpp, hph] at hps; exact hps
          · have hps := hg.proc_sync p; rw [hpp, hph] at hps; exact hps
          · have hps := hg.proc_sync p; rw [hpp, hph] at hps
            obtain ⟨hi, hc, hk, hpk, hst, htag, hreq, hcard, hprev⟩ := hps
            refine ⟨lt_of_lt_of_le hi hlen_le, ?_, ?_, hpk, ?_, htag, hreq, hcard, ?_⟩
            · simpa [List.getElem_append_left hi] using hc
            · simpa [List.getElem_append_left hi] using hk
            · simpa [List.getElem_append_left hi] using hst
            · intro j hj hjne hjc
              have hj_len : j < s.history.length + 1 := by simpa using hj
              by_cases hjl : j < s.history.length
              · rw [List.getElem_append_left hjl] at hjc
                exact (hprec_old j hjl _ hi).mpr (hprev j hjl hjne hjc)
              · have heq : j = s.history.length := by omega
                subst heq
                simp only [List.getElem_append_right le_rfl, Nat.sub_self,
                  List.getElem_singleton, rec'] at hjc
                exact False.elim (hp hjc.symm)
          · have hps := hg.proc_sync p; rw [hpp, hph] at hps
            obtain ⟨hi, hc, hk, hpk, hst, htag, hreq, hcard, hacks, hprev⟩ := hps
            refine ⟨lt_of_lt_of_le hi hlen_le, ?_, ?_, hpk, ?_, htag, hreq, hcard,
              fun q hq => by
                by_cases hqc : q = caller
                · subst hqc; simpa [nextSt] using hacks q hq
                · simp only [Function.update_of_ne hqc]; exact hacks q hq,
              ?_⟩
            · simpa [List.getElem_append_left hi] using hc
            · simpa [List.getElem_append_left hi] using hk
            · simpa [List.getElem_append_left hi] using hst
            · intro j hj hjne hjc
              have hj_len : j < s.history.length + 1 := by simpa using hj
              by_cases hjl : j < s.history.length
              · rw [List.getElem_append_left hjl] at hjc
                exact (hprec_old j hjl _ hi).mpr (hprev j hjl hjne hjc)
              · have heq : j = s.history.length := by omega
                subst heq
                simp only [List.getElem_append_right le_rfl, Nat.sub_self,
                  List.getElem_singleton, rec'] at hjc
                exact False.elim (hp hjc.symm)
      msg_wf := fun e he => by
        rw [Multiset.mem_add] at he
        rcases he with he_old | he_new
        · refine msgWF_transfer
            (s' := { msgs := s.msgs + outMsgs.map (tagSender caller)
                     proc := proc'
                     history := s.history ++ [rec']
                     step := s.step + 1 })
            hlen_le htag_pres ?_ (fun q => (hrep_eq q).symm.le) ?_ ?_ (hg.msg_wf e he_old)
          · intro p
            by_cases hp : p = caller
            · subst hp; simp [proc', nextSt, reqId]
            · simp [proc', hp]
          · intro p rId hreq hp1 knd resp bt bv hph'
            by_cases hp : p = caller
            · subst hp
              simp only [proc', nextSt, Function.update_self, ClientPhase.phase1.injEq] at hph'
              exact Nat.lt_irrefl _ (hph'.1 ▸ hreq)
            · simp only [proc', Function.update_of_ne hp] at hph'
              exact hp1 knd resp bt bv hph'
          · intro p rId _ _ knd cTag cVal acks hph'
            by_cases hp : p = caller
            · subst hp; simp [proc', nextSt] at hph'
            · simp only [proc', Function.update_of_ne hp] at hph'
              exact ⟨acks, hph'⟩
        · simp only [outMsgs, broadcastAll, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
            true_and] at he_new
          obtain ⟨pm, ⟨q, rfl⟩, rfl⟩ := he_new
          simp [MsgWF, proc', nextSt, reqId]
      write_unique := by
        refine ⟨?_, ?_⟩
        · intro i _ v τ hk hτ
          have hil : i < s.history.length := by
            by_contra hge; rw [hg.tag_out i (Nat.le_of_not_lt hge)] at hτ; cases hτ
          simp only [List.getElem_append_left hil] at hk ⊢
          exact hg.write_unique.1 i hil v τ hk hτ
        · intro i j _ _ v₁ v₂ τ hk₁ hk₂ hτ₁ hτ₂
          have hil : i < s.history.length := by
            by_contra hge; rw [hg.tag_out i (Nat.le_of_not_lt hge)] at hτ₁; cases hτ₁
          have hjl : j < s.history.length := by
            by_contra hge; rw [hg.tag_out j (Nat.le_of_not_lt hge)] at hτ₂; cases hτ₂
          simp only [List.getElem_append_left hil, List.getElem_append_left hjl] at hk₁ hk₂
          exact hg.write_unique.2 i j hil hjl v₁ v₂ τ hk₁ hk₂ hτ₁ hτ₂
      val_valid := by
        refine ⟨?_, ?_, ?_⟩
        · intro q
          have hq := tagValidVal_mono hlen_le htag_pres (hg.val_valid.1 q)
          by_cases hqc : q = caller
          · subst hqc; simpa [proc', nextSt] using hq
          · simpa [proc', hqc] using hq
        · intro p
          by_cases hp : p = caller
          · subst hp
            simp only [proc', nextSt, Function.update_self, PhaseValValid]
            exact Or.inl ⟨rfl, rfl⟩
          · simp only [proc', Function.update_of_ne hp]
            exact phaseValValid_mono hlen_le htag_pres (hg.val_valid.2.1 p)
        · intro i _ stp r τ hst hτ
          have hil : i < s.history.length := by
            by_contra hge; rw [hg.tag_out i (Nat.le_of_not_lt hge)] at hτ; cases hτ
          simp only [List.getElem_append_left hil] at hst
          exact tagValidVal_mono hlen_le htag_pres (hg.val_valid.2.2 i hil stp r τ hst hτ)
      completed_quorum := fun a _ τ_a hcomp hτ => by
        have hal : a < s.history.length := by
          by_contra hge; rw [hg.tag_out a (Nat.le_of_not_lt hge)] at hτ; cases hτ
        simp only [List.getElem_append_left hal] at hcomp
        obtain ⟨Q, hQcard, hQtag⟩ := hg.completed_quorum a hal τ_a hcomp hτ
        exact ⟨Q, hQcard, fun q hq => by rw [hrep_eq q]; exact hQtag q hq⟩
      prec_phase1 := fun p pend rId knd responses bt bv hp_pend hp_ph a τ_a hprec hτ_a => by
        have hal : a < s.history.length := by
          by_contra hge; rw [hg.tag_out a (Nat.le_of_not_lt hge)] at hτ_a; cases hτ_a
        by_cases hp : p = caller
        · subst hp
          simp only [proc', nextSt, Function.update_self, Option.some.injEq,
            ClientPhase.phase1.injEq] at hp_pend hp_ph
          subst hp_pend
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hp_ph
          rw [hprec_to_new] at hprec
          obtain ⟨_, hcomp_a⟩ := hprec
          obtain ⟨Q, hQcard, hQtag⟩ := hg.completed_quorum a hal τ_a hcomp_a hτ_a
          refine ⟨Q, hQcard, fun q hq => by rw [hrep_eq q]; exact hQtag q hq, ?_,
            fun _ _ hm => nomatch hm⟩
          intro q _ rTag rVal hmem
          rw [Multiset.mem_add] at hmem
          rcases hmem with hold | hnew
          · have hm := hg.msg_wf _ hold
            exact False.elim (Nat.lt_irrefl _ hm.1)
          · simp only [outMsgs, broadcastAll, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
              true_and] at hnew
            obtain ⟨pm, ⟨_, rfl⟩, htag_eq⟩ := hnew
            cases htag_eq
        · simp only [proc', Function.update_of_ne hp] at hp_pend hp_ph
          have hps := hg.proc_sync p
          rw [hp_pend, hp_ph] at hps
          obtain ⟨hpend_lt, _⟩ := hps
          rw [hprec_old a hal pend.opId hpend_lt] at hprec
          obtain ⟨Q, hQcard, hQrep, hQmsg, hQresp⟩ :=
            hg.prec_phase1 p pend rId knd responses bt bv hp_pend hp_ph a τ_a hprec hτ_a
          refine ⟨Q, hQcard, fun q hq => by rw [hrep_eq q]; exact hQrep q hq, ?_, hQresp⟩
          intro q hq rTag rVal hmem
          rw [Multiset.mem_add] at hmem
          rcases hmem with hold | hnew
          · exact hQmsg q hq rTag rVal hold
          · simp only [outMsgs, broadcastAll, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
              true_and] at hnew
            obtain ⟨pm, ⟨_, rfl⟩, htag_eq⟩ := hnew
            cases htag_eq
      prec_tag := fun a b _ τ_a τ_b hprec hτ_a hτ_b => by
        have hal : a < s.history.length := by
          by_contra hge; rw [hg.tag_out a (Nat.le_of_not_lt hge)] at hτ_a; cases hτ_a
        have hbl : b < s.history.length := by
          by_contra hge; rw [hg.tag_out b (Nat.le_of_not_lt hge)] at hτ_b; cases hτ_b
        rw [hprec_old a hal b hbl] at hprec
        simp only [List.getElem_append_left hbl]
        exact hg.prec_tag a b hbl τ_a τ_b hprec hτ_a hτ_b }

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
  have hrep_dest : (s.proc e.dest).state.repTag ≤ nextSt.repTag := by
    have hm := abdOnRecv_repTag_mono t e.dest (s.proc e.dest).state e.src e.body
    have hns : (abdOnRecv t e.dest (s.proc e.dest).state e.src e.body).nextState = nextSt :=
      congrArg StepOut.nextState hout
    exact hns ▸ hm
  have hrep_le : ∀ q : P, (s.proc q).state.repTag ≤ (proc' q).state.repTag := by
    intro q
    by_cases hq : q = e.dest
    · subst hq; simpa [proc'] using hrep_dest
    · simp [proc', hq]
  have hpend_eq : ∀ p : P, (proc' p).pending = (s.proc p).pending := by
    intro p
    by_cases hp : p = e.dest
    · subst hp; simp [proc']
    · simp [proc', hp]
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
        rw [Multiset.mem_add] at hm
        rcases hm with hm_old | hm_new
        · refine msgWF_transfer (s := s)
            (s' := { msgs := s.msgs.erase e + outMsgs.map (tagSender e.dest)
                     proc := proc'
                     history := s.history
                     step := s.step + 1 })
            le_rfl htv_pres ?_ hrep_le ?_ ?_ (hg.msg_wf m (Multiset.mem_of_mem_erase hm_old))
          · intro p
            by_cases hp : p = e.dest
            · subst hp; simpa [proc'] using hnext_dest
            · simp [proc', hp]
          · intro p reqId hreq hp1 knd resp bt bv hph'
            by_cases hp : p = e.dest
            · subst hp
              simp only [proc', Function.update_self] at hph'
              exact hp1_dest reqId hreq hp1 knd resp bt bv hph'
            · simp only [proc', Function.update_of_ne hp] at hph'
              exact hp1 knd resp bt bv hph'
          · intro p reqId hreq hp1 knd cT cV acks hph'
            by_cases hp : p = e.dest
            · subst hp
              simp only [proc', Function.update_self] at hph'
              exact hp2_dest reqId hreq hp1 knd cT cV acks hph'
            · simp only [proc', Function.update_of_ne hp] at hph'
              exact ⟨acks, hph'⟩
        · rw [Multiset.mem_map] at hm_new
          obtain ⟨pm, hpm, rfl⟩ := hm_new
          exact hout_wf pm hpm
      write_unique := hwu
      val_valid := by
        refine ⟨?_, ?_, hread_val⟩
        · intro q
          by_cases hqd : q = e.dest
          · subst hqd; simpa [proc'] using hrep_val_dest
          · simp only [proc', Function.update_of_ne hqd]
            exact tagValidVal_mono le_rfl htv_pres (hg.val_valid.1 q)
        · intro p
          by_cases hp : p = e.dest
          · subst hp; simpa [proc'] using hphase_val_dest
          · simp only [proc', Function.update_of_ne hp]
            exact phaseValValid_mono le_rfl htv_pres (hg.val_valid.2.1 p)
      completed_quorum := fun a ha τ_a hcomp hτ => by
        obtain ⟨Q, hQc, hQr⟩ := hg.completed_quorum a ha τ_a hcomp (hcomp_tag a ha τ_a hcomp hτ)
        exact ⟨Q, hQc, fun q hq => (hQr q hq).trans (hrep_le q)⟩
      prec_phase1 := fun p pnd reqId knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_a => by
        rw [hpend_eq p] at hp1
        have ⟨ha_lt, _, r_step, hr_step, _⟩ := hpr
        have ha_comp : s.history[a].status.isCompleted = true := by
          simp [OpStatus.isCompleted, hr_step]
        have hτ_old := hcomp_tag a ha_lt τ_a ha_comp hτ_a
        by_cases hp : p = e.dest
        · subst hp
          simp only [proc', Function.update_self] at hp2
          exact hp1_dest_prec pnd reqId knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_old
        · simp only [proc', Function.update_of_ne hp] at hp2
          obtain ⟨Q, hQc, hQr, hQm, hQresp⟩ :=
            hg.prec_phase1 p pnd reqId knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_old
          refine ⟨Q, hQc, fun q hq => (hQr q hq).trans (hrep_le q), ?_, hQresp⟩
          intro q hq rt rv hm
          rw [Multiset.mem_add] at hm
          rcases hm with hm_old | hm_new
          · exact hQm q hq rt rv (Multiset.mem_of_mem_erase hm_old)
          · rw [Multiset.mem_map] at hm_new
            obtain ⟨⟨dest', body'⟩, hpm, heq⟩ := hm_new
            injection heq with hsrc hdest hbody
            subst hsrc hbody
            exact (hQr e.dest hq).trans (hout_qresp dest' reqId rt rv hpm)
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

/-- Helper for a message delivery that leaves local states, `pending`, and `history` unchanged and
emits zero messages (stale or out-of-phase messages). -/
private lemma abdGood_deliver_noop {v₀ : V} {t : ℕ}
    {s : State P (ABDState P V) (ABDMsg P V) V} {opTag : ℕ → Option (Tag P)}
    (hg : ABDGood v₀ t s opTag) {e : Envelope P (ABDMsg P V)}
    (hnoop : abdOnRecv t e.dest (s.proc e.dest).state e.src e.body =
      ⟨(s.proc e.dest).state, 0, none⟩) :
    ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag := by
  have hrep_same :
      (fun q => (Function.update s.proc e.dest
        ⟨(s.proc e.dest).state, (s.proc e.dest).pending⟩ q).state.repTag) =
      fun q => (s.proc q).state.repTag := by
    ext q; by_cases hq : q = e.dest <;> [subst hq; skip] <;> simp [*]
  refine abdGood_deliver_same_opTag hg hnoop (hrep_same ▸ hg.proc_sync e.dest) le_rfl
    (fun _ _ hp1 => hp1) (fun _ _ _ _ _ _ acks h => ⟨acks, h⟩)
    (fun _ hm => nomatch hm) (fun _ _ _ _ hm => nomatch hm)
    (hg.val_valid.1 e.dest) (hg.val_valid.2.1 e.dest) ?_
  intro pend reqId knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ
  obtain ⟨Q, hQc, hQr, hQm, hQresp⟩ :=
    hg.prec_phase1 e.dest pend reqId knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ
  refine ⟨Q, hQc, fun q hq => by simpa [hrep_same] using hQr q hq, ?_, hQresp⟩
  intro q hq rt rv hm
  simp only [Multiset.map_zero, add_zero] at hm
  exact hQm q hq rt rv (Multiset.mem_of_mem_erase hm)

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
    change out = ⟨out.nextState, out.outgoing, none⟩
    rw [← hout_resp]
  have hphase_eq : out.nextState.phase = (s.proc e.dest).state.phase := by
    rcases hrep with ⟨_, hb⟩ | ⟨_, _, _, hb⟩
    · simp [out, hb, abdOnRecv]
    · simp only [out, hb, abdOnRecv]; split_ifs <;> rfl
  have hnext_eq : out.nextState.nextReqId = (s.proc e.dest).state.nextReqId := by
    rcases hrep with ⟨_, hb⟩ | ⟨_, _, _, hb⟩
    · simp [out, hb, abdOnRecv]
    · simp only [out, hb, abdOnRecv]; split_ifs <;> rfl
  have hrep_le : ∀ q : P, (s.proc q).state.repTag ≤
      (Function.update s.proc e.dest ⟨out.nextState, (s.proc e.dest).pending⟩ q).state.repTag := by
    intro q
    by_cases hq : q = e.dest
    · subst hq
      simpa [out] using abdOnRecv_repTag_mono t e.dest (s.proc e.dest).state e.src e.body
    · simp [hq]
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
  have hout_qresp : ∀ dest' reqId rTag rVal,
      (dest', .queryResp reqId rTag rVal) ∈ out.outgoing →
      (s.proc e.dest).state.repTag ≤ rTag := by
    intro dest' reqId rTag rVal hm
    rcases hrep with ⟨qReq, hb⟩ | ⟨qReq, inTag, inVal, hb⟩
    · simp only [out, hb, abdOnRecv, Multiset.mem_singleton, Prod.mk.injEq,
        ABDMsg.queryResp.injEq] at hm
      exact hm.2.2.1 ▸ le_rfl
    · simp [out, hb, abdOnRecv] at hm
  refine abdGood_deliver_same_opTag hg hout
    (hnext_eq.symm ▸ hphase_eq.symm ▸ procSync_mono le_rfl hrep_le (fun _ _ => rfl)
      (hg.proc_sync e.dest))
    hnext_eq.symm.le
    (fun _ _ hp1 knd resp bt bv hph => hp1 knd resp bt bv (hphase_eq.symm.trans hph))
    (fun _ _ _ _ _ _ acks hph => ⟨acks, hphase_eq.symm.trans hph⟩)
    ?_ hout_qresp ?_ (hphase_eq ▸ hg.val_valid.2.1 e.dest) ?_
  · intro pm hpm
    rcases hrep with ⟨reqId, hb⟩ | ⟨reqId, inTag, inVal, hb⟩
    · simp only [out, hb, abdOnRecv, Multiset.mem_singleton] at hpm
      subst hpm
      have he_wf := hg.msg_wf e he
      rw [hb] at he_wf
      exact ⟨hsrc_next.symm ▸ he_wf, hg.val_valid.1 e.dest⟩
    · simp only [out, hb, abdOnRecv, Multiset.mem_singleton] at hpm
      subst hpm
      have he_wf := hg.msg_wf e he
      rw [hb] at he_wf
      obtain ⟨hreq, _, hp1, hp2⟩ := he_wf
      simp only [MsgWF]
      refine ⟨hsrc_next.symm ▸ hreq,
        fun knd resp bt bv hph => hp1 knd resp bt bv (hsrc_phase.symm.trans hph), ?_⟩
      intro knd cTag cVal acks hph
      obtain ⟨hcT, _⟩ := hp2 knd cTag cVal acks (hsrc_phase.symm.trans hph)
      rw [← hcT]
      simpa [out, hb] using
        abdOnRecv_store_le_repTag t e.dest (s.proc e.dest).state e.src reqId inTag inVal
  · rcases hrep with ⟨reqId, hb⟩ | ⟨reqId, inTag, inVal, hb⟩
    · simpa [out, hb, abdOnRecv] using hg.val_valid.1 e.dest
    · simp only [out, hb, abdOnRecv]
      split_ifs with hlt
      · have he_wf := hg.msg_wf e he
        rw [hb] at he_wf
        exact he_wf.2.1
      · exact hg.val_valid.1 e.dest
  · intro pend reqId knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ
    rw [hphase_eq] at hp2
    obtain ⟨Q, hQc, hQr, hQm, hQresp⟩ :=
      hg.prec_phase1 e.dest pend reqId knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ
    refine ⟨Q, hQc, fun q hq => (hQr q hq).trans (hrep_le q), ?_, hQresp⟩
    intro q hq rt rv hm
    rw [Multiset.mem_add] at hm
    rcases hm with hm_old | hm_new
    · exact hQm q hq rt rv (Multiset.mem_of_mem_erase hm_old)
    · rw [Multiset.mem_map] at hm_new
      obtain ⟨⟨dest', body'⟩, hpm, heq⟩ := hm_new
      injection heq with hsrc hdest hbody
      subst hsrc hbody
      exact (hQr e.dest hq).trans (hout_qresp dest' reqId rt rv hpm)

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

/-- Helper preserving `ABDGood` when a client receives `.queryResp`. -/
private lemma abdGood_deliver_queryResp {v₀ : V} {t : ℕ}
    (h2t : 2 * t < Fintype.card P) {s : State P (ABDState P V) (ABDMsg P V) V}
    {opTag : ℕ → Option (Tag P)} (hg : ABDGood v₀ t s opTag)
    {e : Envelope P (ABDMsg P V)} (he : e ∈ s.msgs) {rId : ℕ} {rTag : Tag P} {rVal : V}
    (hb : e.body = .queryResp rId rTag rVal) :
    ∃ opTag', ABDGood v₀ t ((abdProtocol P V v₀ t).doDeliver e s) opTag' := by
  have he_wf := hg.msg_wf e he
  rw [hb] at he_wf
  obtain ⟨_, hrTagVal⟩ := he_wf
  cases hph_dest : (s.proc e.dest).state.phase with
  | idle | phase2 _ _ _ _ _ =>
    exact ⟨opTag, abdGood_deliver_noop hg (by simp [hb, abdOnRecv, hph_dest])⟩
  | phase1 reqId kind responses bestTag bestVal =>
    by_cases hmatch : rId = reqId
    · subst hmatch
      obtain ⟨pend, hp_dest⟩ := pending_of_phase_ne_idle hg e.dest (by simp [hph_dest])
      have hps_dest := hg.proc_sync e.dest
      rw [hph_dest, hp_dest] at hps_dest
      obtain ⟨hi_pend, hc_pend, hk_pend, hpk_pend, hst_pend, htag_pend, hreq_lt, _,
        hprev_pend⟩ := hps_dest
      let responses' := insert e.src responses
      let bestTag' := if bestTag < rTag then rTag else bestTag
      let bestVal' := if bestTag < rTag then rVal else bestVal
      have hbt_le : bestTag ≤ bestTag' := by
        dsimp only [bestTag']; split_ifs with hlt <;> [exact le_of_lt hlt; exact le_rfl]
      have hrTag_le : rTag ≤ bestTag' := by
        dsimp only [bestTag']; split_ifs with hlt <;> [exact le_rfl; exact le_of_not_gt hlt]
      have hbestVal' : TagValidVal v₀ s.history opTag bestTag' bestVal' := by
        dsimp only [bestTag', bestVal']
        split_ifs with hlt
        · exact hrTagVal
        · have hv := hg.val_valid.2.1 e.dest
          rw [hph_dest] at hv; exact hv
      have hresp'_le : ∀ {Q : Finset P} {τ_a : Tag P},
          (∀ q ∈ Q, ∀ rt rv, ⟨q, e.dest, .queryResp rId rt rv⟩ ∈ s.msgs → τ_a ≤ rt) →
          (∀ q ∈ Q, q ∈ responses → τ_a ≤ bestTag) →
          ∀ q ∈ Q, q ∈ responses' → τ_a ≤ bestTag' := by
        intro Q τ_a hQm hQresp q hq hqR'
        rcases Finset.mem_insert.mp hqR' with rfl | hqR
        · have he_eq : (⟨e.src, e.dest, .queryResp rId rTag rVal⟩ :
              Envelope P (ABDMsg P V)) = e := by
            ext <;> simp [hb]
          exact (hQm e.src hq rTag rVal (he_eq ▸ he)).trans hrTag_le
        · exact (hQresp q hq hqR).trans hbt_le
      by_cases hquorum : Fintype.card P - t ≤ responses'.card
      · -- Transition `.phase1 → .phase2`
        let chosenTag := match kind with
          | .write _ => nextWriteTag bestTag'.seq e.dest
          | .read => bestTag'
        let chosenVal := match kind with
          | .write v => v
          | .read => bestVal'
        let opTag' := Function.update opTag pend.opId (some chosenTag)
        let nextSt : ABDState P V :=
          { (s.proc e.dest).state with phase := .phase2 rId kind chosenTag chosenVal ∅ }
        let outMsgs : Multiset (P × ABDMsg P V) :=
          broadcastAll P (.store rId chosenTag chosenVal)
        have hq_pos : 0 < Fintype.card P - t := by omega
        have hout : (abdProtocol P V v₀ t).onRecv e.dest (s.proc e.dest).state e.src e.body =
            ⟨nextSt, outMsgs, none⟩ := by
          simp [abdProtocol, hb, abdOnRecv, hph_dest, responses', bestTag', bestVal', hquorum,
            chosenTag, chosenVal, nextSt, outMsgs]
        have htag_pres : ∀ i τ, opTag i = some τ → opTag' i = some τ := by
          intro i τ hτ
          have hip : i ≠ pend.opId := by intro heq; subst heq; rw [htag_pend] at hτ; cases hτ
          exact (Function.update_of_ne hip _ opTag).trans hτ
        have hprec_all_a : ∀ (a : ℕ) τ_a, prec s.history a pend.opId → opTag a = some τ_a →
            τ_a ≤ bestTag' := by
          intro a τ_a hprec hτ_a
          obtain ⟨Q, hQcard, _, hQmsg, hQresp⟩ :=
            hg.prec_phase1 e.dest pend rId kind responses bestTag bestVal hp_dest hph_dest
              a τ_a hprec hτ_a
          obtain ⟨q, hq_inter⟩ := quorum_inter_nonempty h2t hQcard hquorum
          obtain ⟨hqQ, hqR'⟩ := Finset.mem_inter.mp hq_inter
          exact hresp'_le hQmsg hQresp q hqQ hqR'
        have hchosen_valid : TagValidVal v₀ s.history opTag' chosenTag chosenVal := by
          cases kind with
          | read =>
            exact tagValidVal_mono le_rfl (fun i _ τ hτ => ⟨rfl, htag_pres i τ hτ⟩) hbestVal'
          | write v => exact Or.inr ⟨pend.opId, hi_pend, hk_pend, Function.update_self ..⟩
        refine ⟨opTag', abdGood_deliver_resp_none hg hout ?_ htag_pres ?_ ?_ ?_ le_rfl
          (fun _ _ _ _ _ _ _ h => nomatch h) ?_ ?_ ?_ ?_ ?_ hchosen_valid ?_
          (fun _ _ _ _ _ _ _ h => nomatch h) ?_⟩
        · intro i hi
          have hip : i ≠ pend.opId := by omega
          simp only [opTag', Function.update_of_ne hip]
          exact hg.tag_out i hi
        · intro a _ τ_a hcomp hτ
          have hap : a ≠ pend.opId := by
            intro heq; subst heq; rw [hst_pend] at hcomp; cases hcomp
          simpa only [opTag', Function.update_of_ne hap] using hτ
        · intro p hp pnd hpnd
          have hps_p := hg.proc_sync p
          rw [hpnd] at hps_p
          have hpnd_caller : ∃ hlt : pnd.opId < s.history.length,
              s.history[pnd.opId].caller = p := by
            cases hph_p : (s.proc p).state.phase <;> rw [hph_p] at hps_p
            · exact False.elim hps_p
            · exact ⟨hps_p.1, hps_p.2.1⟩
            · exact ⟨hps_p.1, hps_p.2.1⟩
          obtain ⟨hlt_p, hc_p⟩ := hpnd_caller
          have hne_id : pnd.opId ≠ pend.opId := by
            intro heq
            have hget_eq : s.history[pnd.opId]? = s.history[pend.opId]? := by rw [heq]
            rw [List.getElem?_eq_getElem hlt_p, List.getElem?_eq_getElem hi_pend] at hget_eq
            exact hp (hc_p.symm.trans
              ((congrArg OpRecord.caller (Option.some.inj hget_eq)).trans hc_pend))
          exact Function.update_of_ne hne_id _ opTag
        · rw [hp_dest]
          dsimp only [nextSt, ProcSync]
          exact ⟨hi_pend, hc_pend, hk_pend, hpk_pend, hst_pend, Function.update_self ..,
            hreq_lt, by simpa using hq_pos,
            fun _ hm => False.elim (Finset.notMem_empty _ hm), hprev_pend⟩
        · intro reqId' _ hp1 knd cT cV _ hph'
          simp only [nextSt, ClientPhase.phase2.injEq] at hph'
          exact False.elim (hp1 kind responses bestTag bestVal (hph'.1 ▸ hph_dest))
        · intro pm hpm
          simp only [outMsgs, broadcastAll, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
            true_and] at hpm
          obtain ⟨q, rfl⟩ := hpm
          dsimp only [MsgWF, nextSt]
          rw [Function.update_self]
          dsimp only
          refine ⟨hreq_lt, hchosen_valid, (fun _ _ _ _ h => nomatch h), ?_⟩
          intro _ cT cV _ hph
          injection hph with _ _ hcT hcV _
          exact ⟨hcT, hcV⟩
        · intro dest' reqId' rt rv hm
          simp [outMsgs, broadcastAll] at hm
        · have hshape : ∀ (i : ℕ) (hi : i < s.history.length) v τ,
              s.history[i].kind = .write v → opTag' i = some τ →
              ∃ seq, τ = nextWriteTag seq s.history[i].caller := by
            intro i hi v τ hk hτ
            by_cases hip : i = pend.opId
            · subst hip
              simp only [opTag', Function.update_self, Option.some.injEq] at hτ
              subst hτ
              rw [hk_pend] at hk
              cases hk
              exact ⟨bestTag'.seq, hc_pend ▸ rfl⟩
            · simp only [opTag', Function.update_of_ne hip] at hτ
              exact hg.write_unique.1 i hi v τ hk hτ
          have hfresh_write : ∀ k (hk : k < s.history.length) vk vw,
              kind = .write vw → k ≠ pend.opId →
              s.history[k].kind = .write vk → opTag k ≠ some chosenTag := by
            intro k hk vk vw hkw_kind hkne hkw hτk
            obtain ⟨seq_k, hτk_eq⟩ := hg.write_unique.1 k hk vk chosenTag hkw hτk
            have hc_eq : chosenTag = nextWriteTag bestTag'.seq e.dest := by
              simp [chosenTag, hkw_kind]
            have hwriter := congrArg Tag.writer (hτk_eq.symm.trans hc_eq)
            simp only [nextWriteTag_writer, WithBot.coe_inj] at hwriter
            have hle := hprec_all_a k chosenTag (hprev_pend k hk hkne hwriter) hτk
            exact lt_irrefl chosenTag
              (hc_eq ▸ lt_nextWriteTag_of_seq_le (seq_le_of_le hle) e.dest)
          refine ⟨hshape, fun i j hi hj v₁ v₂ τ hk₁ hk₂ hτ₁ hτ₂ => ?_⟩
          by_cases hi_p : i = pend.opId
          · subst hi_p
            simp only [opTag', Function.update_self, Option.some.injEq] at hτ₁
            subst hτ₁
            by_cases hj_p : j = pend.opId
            · exact hj_p.symm
            · simp only [opTag', Function.update_of_ne hj_p] at hτ₂
              exact False.elim (hfresh_write j hj v₂ v₁ (hk_pend.symm.trans hk₁) hj_p hk₂ hτ₂)
          · by_cases hj_p : j = pend.opId
            · subst hj_p
              simp only [opTag', Function.update_self, Option.some.injEq] at hτ₂
              subst hτ₂
              simp only [opTag', Function.update_of_ne hi_p] at hτ₁
              exact False.elim (hfresh_write i hi v₁ v₂ (hk_pend.symm.trans hk₂) hi_p hk₁ hτ₁)
            · simp only [opTag', Function.update_of_ne hi_p] at hτ₁
              simp only [opTag', Function.update_of_ne hj_p] at hτ₂
              exact hg.write_unique.2 i j hi hj v₁ v₂ τ hk₁ hk₂ hτ₁ hτ₂
        · exact tagValidVal_mono le_rfl (fun i _ τ hτ => ⟨rfl, htag_pres i τ hτ⟩)
            (hg.val_valid.1 e.dest)
        · intro i hi stp r τ hst hτ
          have hip : i ≠ pend.opId := by
            intro heq; subst heq; rw [hst_pend] at hst; cases hst
          simp only [opTag', Function.update_of_ne hip] at hτ
          exact tagValidVal_mono le_rfl (fun j _ τ' hτ' => ⟨rfl, htag_pres j τ' hτ'⟩)
            (hg.val_valid.2.2 i hi stp r τ hst hτ)
        · intro a b hb τ_a τ_b hpr hτ_a hτ_b
          have hap : a ≠ pend.opId := by
            intro heq; subst heq
            obtain ⟨_, _, _, hr, _⟩ := hpr
            simp [hst_pend, OpStatus.respStep?] at hr
          simp only [opTag', Function.update_of_ne hap] at hτ_a
          by_cases hbp : b = pend.opId
          · subst hbp
            simp only [opTag', Function.update_self, Option.some.injEq] at hτ_b
            subst hτ_b
            have hle := hprec_all_a a τ_a hpr hτ_a
            rw [hk_pend]
            cases kind with
            | read => exact hle
            | write _ => exact lt_nextWriteTag_of_seq_le (seq_le_of_le hle) e.dest
          · simp only [opTag', Function.update_of_ne hbp] at hτ_b
            exact hg.prec_tag a b hb τ_a τ_b hpr hτ_a hτ_b
      · -- Stay in `.phase1` (`responses'.card < n - t`)
        let nextSt : ABDState P V :=
          { (s.proc e.dest).state with phase := .phase1 rId kind responses' bestTag' bestVal' }
        have hout : (abdProtocol P V v₀ t).onRecv e.dest (s.proc e.dest).state e.src e.body =
            ⟨nextSt, 0, none⟩ := by
          simp [abdProtocol, hb, abdOnRecv, hph_dest, responses', bestTag', bestVal', hquorum,
            nextSt]
        have hrep_same : ∀ q : P,
            (Function.update s.proc e.dest ⟨nextSt, (s.proc e.dest).pending⟩ q).state.repTag =
            (s.proc q).state.repTag := by
          intro q; by_cases hq : q = e.dest <;> [subst hq; skip] <;> simp [nextSt, *]
        refine ⟨opTag, abdGood_deliver_same_opTag hg hout ?_ le_rfl ?_
          (fun _ _ _ _ _ _ _ h => nomatch h) (fun _ hm => nomatch hm)
          (fun _ _ _ _ hm => nomatch hm) (hg.val_valid.1 e.dest) hbestVal' ?_⟩
        · rw [hp_dest]
          dsimp only [nextSt, ProcSync]
          exact ⟨hi_pend, hc_pend, hk_pend, hpk_pend, hst_pend, htag_pend, hreq_lt,
            Nat.lt_of_not_le hquorum, hprev_pend⟩
        · intro reqId' _ hp1 _ _ _ _ hph'
          simp only [nextSt, ClientPhase.phase1.injEq] at hph'
          exact hp1 kind responses bestTag bestVal (hph'.1 ▸ hph_dest)
        · intro pnd reqId' knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_a
          rw [hp_dest, Option.some.injEq] at hp1
          subst hp1
          simp only [nextSt, ClientPhase.phase1.injEq] at hp2
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hp2
          obtain ⟨Q, hQc, hQr, hQm, hQresp⟩ :=
            hg.prec_phase1 e.dest pend rId kind responses bestTag bestVal hp_dest hph_dest
              a τ_a hpr hτ_a
          refine ⟨Q, hQc, fun q hq => by rw [hrep_same q]; exact hQr q hq, ?_,
            hresp'_le hQm hQresp⟩
          intro q hq rt rv hm
          simp only [Multiset.map_zero, add_zero] at hm
          exact hQm q hq rt rv (Multiset.mem_of_mem_erase hm)
    · exact ⟨opTag, abdGood_deliver_noop hg (by simp [hb, abdOnRecv, hph_dest, hmatch])⟩

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
      have he_wf := hg.msg_wf e he
      rw [hb] at he_wf
      have hsrc_le : chosenTag ≤ (s.proc e.src).state.repTag :=
        he_wf.2.2 kind chosenTag chosenVal acks hph_dest
      let acks' := insert e.src acks
      have hacks'_le : ∀ q ∈ acks', chosenTag ≤ (s.proc q).state.repTag := by
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq_old
        · exact hsrc_le
        · exact hacks_le q hq_old
      have hchosen_valid : TagValidVal v₀ s.history opTag chosenTag chosenVal := by
        have hv := hg.val_valid.2.1 e.dest
        rw [hph_dest] at hv; exact hv
      by_cases hquorum : Fintype.card P - t ≤ acks'.card
      · -- Operation `pend.opId` completes!
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
          simp [abdProtocol, hb, abdOnRecv, hph_dest, acks', hquorum, outResp, nextSt]
        rw [(abdProtocol P V v₀ t).doDeliver_of_complete hout_step hp_dest hmatch_comp hi_pend]
        set hist' := s.history.set pend.opId { s.history[pend.opId] with status := stDone }
        set proc' := Function.update s.proc e.dest ⟨nextSt, none⟩
        have hlen_eq : hist'.length = s.history.length := List.length_set
        have hrep_eq : ∀ q : P, (proc' q).state.repTag = (s.proc q).state.repTag := by
          intro q; by_cases hq : q = e.dest <;> [subst hq; skip] <;> simp [proc', nextSt, *]
        have hkind_eq : ∀ (i : ℕ) (hi : i < s.history.length),
            (hist'[i]'(hlen_eq.symm ▸ hi)).kind = s.history[i].kind := by
          intro i _
          by_cases hip : i = pend.opId
          · subst hip; simp [hist']
          · simp [hist', List.getElem_set_ne (Ne.symm hip)]
        have hcaller_eq : ∀ (i : ℕ) (hi : i < s.history.length),
            (hist'[i]'(hlen_eq.symm ▸ hi)).caller = s.history[i].caller := by
          intro i _
          by_cases hip : i = pend.opId
          · subst hip; simp [hist']
          · simp [hist', List.getElem_set_ne (Ne.symm hip)]
        have hinv_eq : ∀ (i : ℕ) (hi : i < s.history.length),
            (hist'[i]'(hlen_eq.symm ▸ hi)).invStep = s.history[i].invStep := by
          intro i _
          by_cases hip : i = pend.opId
          · subst hip; simp [hist']
          · simp [hist', List.getElem_set_ne (Ne.symm hip)]
        have htv_to_new : ∀ {τ v},
            TagValidVal v₀ s.history opTag τ v → TagValidVal v₀ hist' opTag τ v :=
          tagValidVal_mono hlen_eq.symm.le fun i hi τ' hτ' => ⟨hkind_eq i hi, hτ'⟩
        have hstDone_resp : stDone.respStep? = some s.step := by cases kind <;> rfl
        have hprec_eq : ∀ a b, prec hist' a b ↔ prec s.history a b :=
          abdGood_prec_complete hg hi_pend hst_pend stDone hstDone_resp
        refine
          { tag_out := hlen_eq ▸ hg.tag_out
            hist_wf := fun i hi => by
              have hi0 : i < s.history.length := hlen_eq ▸ hi
              by_cases hip : i = pend.opId
              · subst hip
                obtain ⟨hinv, _⟩ := hg.hist_wf pend.opId hi0
                simp only [hist', List.getElem_set_self]
                refine ⟨Nat.lt_succ_of_lt hinv, ?_, ?_, ?_, ?_⟩
                · intro r hr
                  rw [hstDone_resp, Option.some.injEq] at hr
                  subst hr
                  exact ⟨Nat.le_of_lt hinv, Nat.lt_succ_self _⟩
                · intro r v hr
                  dsimp only [stDone] at hr
                  cases kind with
                  | write _ => cases hr
                  | read => exact ⟨hk_pend, by simp [htag_pend]⟩
                · intro r hr
                  dsimp only [stDone] at hr
                  cases kind with
                  | read => cases hr
                  | write vw => exact ⟨⟨vw, hk_pend⟩, by simp [htag_pend]⟩
                · intro hp
                  dsimp only [stDone] at hp
                  cases kind <;> cases hp
              · obtain ⟨h1, h2, h3, h4, h5⟩ := hg.hist_wf i hi0
                have hget : hist'[i] = s.history[i] := by
                  simp [hist', List.getElem_set_ne (Ne.symm hip)]
                rw [hget]
                refine ⟨Nat.lt_succ_of_lt h1,
                  fun r hr => ⟨(h2 r hr).1, Nat.lt_succ_of_lt (h2 r hr).2⟩,
                  h3, h4, fun hp => ?_⟩
                have hp0 := h5 hp
                have hne_c : s.history[i].caller ≠ e.dest := by
                  intro heq
                  rw [heq, hp_dest, Option.some.injEq] at hp0
                  exact hip (congrArg PendingOp.opId hp0).symm
                simpa [proc', Function.update_of_ne hne_c] using hp0
            inv_mono := fun i j hij hj => by
              have hj0 : j < s.history.length := hlen_eq ▸ hj
              have hi0 : i < s.history.length := hij.trans hj0
              rw [hinv_eq i hi0, hinv_eq j hj0]
              exact hg.inv_mono i j hij hj0
            proc_sync := fun p => by
              change ProcSync t hist' (proc' p).state.nextReqId
                (fun q => (proc' q).state.repTag) opTag p (proc' p).pending (proc' p).state.phase
              by_cases hp : p = e.dest
              · subst hp; simp [proc', nextSt, ProcSync]
              · simp only [proc', Function.update_of_ne hp]
                rcases hpp : (s.proc p).pending with _ | pnd <;>
                  cases hph_p : (s.proc p).state.phase
                · trivial
                · have hps := hg.proc_sync p; rw [hpp, hph_p] at hps; exact hps
                · have hps := hg.proc_sync p; rw [hpp, hph_p] at hps; exact hps
                · have hps := hg.proc_sync p; rw [hpp, hph_p] at hps; exact hps
                · have hps := hg.proc_sync p; rw [hpp, hph_p] at hps
                  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hps
                  have hne_id : pnd.opId ≠ pend.opId := by
                    intro heq
                    have hget_eq : s.history[pnd.opId]? = s.history[pend.opId]? := by rw [heq]
                    rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem hi_pend] at hget_eq
                    exact hp (h2.symm.trans
                      ((congrArg OpRecord.caller (Option.some.inj hget_eq)).trans hc_pend))
                  refine ⟨hlen_eq.symm ▸ h1, (hcaller_eq _ h1).trans h2,
                    (hkind_eq _ h1).trans h3, h4, ?_, h6, h7, h8, ?_⟩
                  · simpa [hist', List.getElem_set_ne (Ne.symm hne_id)] using h5
                  · intro j hj hjne hjc
                    have hj0 : j < s.history.length := hlen_eq ▸ hj
                    rw [hcaller_eq j hj0] at hjc
                    exact (hprec_eq j _).mpr (h9 j hj0 hjne hjc)
                · have hps := hg.proc_sync p; rw [hpp, hph_p] at hps
                  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hps
                  have hne_id : pnd.opId ≠ pend.opId := by
                    intro heq
                    have hget_eq : s.history[pnd.opId]? = s.history[pend.opId]? := by rw [heq]
                    rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem hi_pend] at hget_eq
                    exact hp (h2.symm.trans
                      ((congrArg OpRecord.caller (Option.some.inj hget_eq)).trans hc_pend))
                  refine ⟨hlen_eq.symm ▸ h1, (hcaller_eq _ h1).trans h2,
                    (hkind_eq _ h1).trans h3, h4, ?_, h6, h7, h8,
                    fun q hq => by
                      by_cases hqd : q = e.dest
                      · subst hqd; simpa [nextSt] using h9 e.dest hq
                      · simp only [Function.update_of_ne hqd]; exact h9 q hq,
                    ?_⟩
                  · simpa [hist', List.getElem_set_ne (Ne.symm hne_id)] using h5
                  · intro j hj hjne hjc
                    have hj0 : j < s.history.length := hlen_eq ▸ hj
                    rw [hcaller_eq j hj0] at hjc
                    exact (hprec_eq j _).mpr (h10 j hj0 hjne hjc)
            msg_wf := fun m hm => by
              simp only [Multiset.map_zero, add_zero] at hm
              refine msgWF_transfer (s := s)
                (s' := { msgs := s.msgs.erase e +
                           (0 : Multiset (P × ABDMsg P V)).map (tagSender e.dest)
                         proc := proc'
                         history := hist'
                         step := s.step + 1 })
                hlen_eq.symm.le (fun i hi τ hτ => ⟨hkind_eq i hi, hτ⟩)
                (fun p => ?_) (fun q => (hrep_eq q).symm.le) ?_ ?_
                (hg.msg_wf m (Multiset.mem_of_mem_erase hm))
              · by_cases hp : p = e.dest
                · subst hp; simp [proc', nextSt]
                · simp [proc', hp]
              · intro p reqId' _ hp1 knd resp bt bv hph'
                by_cases hp : p = e.dest
                · subst hp; simp [proc', nextSt] at hph'
                · simp only [proc', Function.update_of_ne hp] at hph'
                  exact hp1 knd resp bt bv hph'
              · intro p reqId' _ _ knd cT cV acks_m hph'
                by_cases hp : p = e.dest
                · subst hp; simp [proc', nextSt] at hph'
                · simp only [proc', Function.update_of_ne hp] at hph'
                  exact ⟨acks_m, hph'⟩
            write_unique := by
              refine ⟨?_, ?_⟩
              · intro i hi v τ hk hτ
                have hi0 : i < s.history.length := hlen_eq ▸ hi
                rw [hkind_eq i hi0] at hk
                rw [hcaller_eq i hi0]
                exact hg.write_unique.1 i hi0 v τ hk hτ
              · intro i j hi hj v₁ v₂ τ hk₁ hk₂ hτ₁ hτ₂
                have hi0 : i < s.history.length := hlen_eq ▸ hi
                have hj0 : j < s.history.length := hlen_eq ▸ hj
                rw [hkind_eq i hi0] at hk₁
                rw [hkind_eq j hj0] at hk₂
                exact hg.write_unique.2 i j hi0 hj0 v₁ v₂ τ hk₁ hk₂ hτ₁ hτ₂
            val_valid := by
              refine ⟨?_, ?_, ?_⟩
              · intro q
                have hq := htv_to_new (hg.val_valid.1 q)
                by_cases hqd : q = e.dest
                · subst hqd; simpa [proc', nextSt] using hq
                · simpa [proc', hqd] using hq
              · intro p
                by_cases hp : p = e.dest
                · subst hp; simp [proc', nextSt, PhaseValValid]
                · simp only [proc', Function.update_of_ne hp]
                  exact phaseValValid_mono hlen_eq.symm.le
                    (fun i hi τ' hτ' => ⟨hkind_eq i hi, hτ'⟩) (hg.val_valid.2.1 p)
              · intro i hi stp r τ hst hτ
                have hi0 : i < s.history.length := hlen_eq ▸ hi
                by_cases hip : i = pend.opId
                · subst hip
                  simp only [hist', List.getElem_set_self] at hst
                  dsimp only [stDone] at hst
                  cases kind with
                  | write _ => cases hst
                  | read =>
                    injection hst with _ hr_eq
                    subst hr_eq
                    rw [htag_pend, Option.some.injEq] at hτ
                    subst hτ
                    exact htv_to_new hchosen_valid
                · simp only [hist', List.getElem_set_ne (Ne.symm hip)] at hst
                  exact htv_to_new (hg.val_valid.2.2 i hi0 stp r τ hst hτ)
            completed_quorum := fun a ha τ_a hcomp hτ => by
              have ha0 : a < s.history.length := hlen_eq ▸ ha
              by_cases hap : a = pend.opId
              · subst hap
                rw [htag_pend, Option.some.injEq] at hτ
                subst hτ
                exact ⟨acks', hquorum, fun q hq => by rw [hrep_eq q]; exact hacks'_le q hq⟩
              · simp only [hist', List.getElem_set_ne (Ne.symm hap)] at hcomp
                obtain ⟨Q, hQc, hQr⟩ := hg.completed_quorum a ha0 τ_a hcomp hτ
                exact ⟨Q, hQc, fun q hq => by rw [hrep_eq q]; exact hQr q hq⟩
            prec_phase1 := fun p pnd reqId' knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_a => by
              by_cases hp : p = e.dest
              · subst hp; simp [proc', nextSt] at hp2
              · simp only [proc', Function.update_of_ne hp] at hp1 hp2
                rw [hprec_eq] at hpr
                obtain ⟨Q, hQc, hQr, hQm, hQresp⟩ :=
                  hg.prec_phase1 p pnd reqId' knd resp' bt' bv' hp1 hp2 a τ_a hpr hτ_a
                refine ⟨Q, hQc, fun q hq => by rw [hrep_eq q]; exact hQr q hq, ?_, hQresp⟩
                intro q hq rt rv hm
                simp only [Multiset.map_zero, add_zero] at hm
                exact hQm q hq rt rv (Multiset.mem_of_mem_erase hm)
            prec_tag := fun a b hb τ_a τ_b hpr hτ_a hτ_b => by
              have hb0 : b < s.history.length := hlen_eq ▸ hb
              rw [hprec_eq] at hpr
              rw [hkind_eq b hb0]
              exact hg.prec_tag a b hb0 τ_a τ_b hpr hτ_a hτ_b }
      · -- Stay in `.phase2` (`acks'.card < n - t`)
        refine abdGood_deliver_same_opTag
          (nextSt := { (s.proc e.dest).state with
            phase := .phase2 rId kind chosenTag chosenVal acks' })
          (outMsgs := 0) hg
          (by simp [abdProtocol, hb, abdOnRecv, hph_dest, acks', hquorum]) ?_ le_rfl
          (fun _ _ _ _ _ _ _ h => nomatch h) ?_ (fun _ hm => nomatch hm)
          (fun _ _ _ _ hm => nomatch hm) (hg.val_valid.1 e.dest) hchosen_valid
          (fun _ _ _ _ _ _ _ h => nomatch h)
        · rw [hp_dest]
          dsimp only [ProcSync]
          exact ⟨hi_pend, hc_pend, hk_pend, hpk_pend, hst_pend, htag_pend, hreq_lt,
            Nat.lt_of_not_le hquorum,
            fun q hq => by
              by_cases hqd : q = e.dest
              · subst hqd; simpa using hacks'_le e.dest hq
              · simp only [Function.update_of_ne hqd]; exact hacks'_le q hq,
            hprev_pend⟩
        · intro reqId' _ _ knd cT cV _ hph'
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
    refine ⟨hi, ?_⟩
    obtain ⟨_, _, hdr, hdw, _⟩ := hg.hist_wf i hi
    cases hst : s.history[i].status with
    | pending => simp [hst] at hcomp
    | doneRead stp rv =>
      obtain ⟨hk, hsome⟩ := hdr stp rv hst
      exact ⟨hsome, by simp [OpRecord.isEligible, hk, hst]⟩
    | doneWrite stp =>
      obtain ⟨⟨vw, hk⟩, hsome⟩ := hdw stp hst
      exact ⟨hsome, by simp [OpRecord.isEligible, hk, hst]⟩
  · intro a ha b hb hpr
    obtain ⟨ha_lt, hsome_a, _⟩ := (hmem_seq a).mp ha
    obtain ⟨hb_lt, hsome_b, _⟩ := (hmem_seq b).mp hb
    obtain ⟨τ_a, hτ_a⟩ := Option.isSome_iff_exists.mp hsome_a
    obtain ⟨τ_b, hτ_b⟩ := Option.isSome_iff_exists.mp hsome_b
    have hpt := hg.prec_tag a b hb_lt τ_a τ_b hpr hτ_a hτ_b
    have hab_idx : a < b := by
      obtain ⟨_, _, r, hr, hlt⟩ := hpr
      have hinv_le : s.history[a].invStep ≤ r := ((hg.hist_wf a ha_lt).2.1 r hr).1
      have hinv_lt : s.history[a].invStep < s.history[b].invStep := lt_of_le_of_lt hinv_le hlt
      rcases lt_trichotomy a b with h | rfl | h
      · exact h
      · exact False.elim (Nat.lt_irrefl _ hinv_lt)
      · exact False.elim (Nat.lt_asymm hinv_lt (hg.inv_mono b a h ha_lt))
    have hkey_lt : abdLinKey opTag s.history a < abdLinKey opTag s.history b := by
      cases hkb : s.history[b].kind with
      | write vw =>
        rw [hkb] at hpt
        exact abdLinKey_lt_of_tag_lt hτ_a hτ_b hpt
      | read =>
        rw [hkb] at hpt
        cases hka : s.history[a].kind with
        | write vw =>
          exact abdLinKey_write_lt_read ha_lt hb_lt hka hkb hτ_a hτ_b hpt
        | read =>
          rcases lt_or_eq_of_le hpt with hlt | rfl
          · exact abdLinKey_lt_of_tag_lt hτ_a hτ_b hlt
          · unfold abdLinKey
            rw [hτ_a, hτ_b, List.getElem?_eq_getElem ha_lt, List.getElem?_eq_getElem hb_lt]
            simp only [Option.getD_some, Option.map_some, hka, hkb, OpKind.isRead,
              Prod.Lex.toLex_lt_toLex, lt_self_iff_false, false_or, true_and]
            exact hab_idx
    have hia : seq.idxOf a < seq.length := List.idxOf_lt_length_of_mem ha
    have hib : seq.idxOf b < seq.length := List.idxOf_lt_length_of_mem hb
    have hga : seq[seq.idxOf a] = a := List.getElem_idxOf hia
    have hgb : seq[seq.idxOf b] = b := List.getElem_idxOf hib
    rcases lt_trichotomy (seq.idxOf a) (seq.idxOf b) with hlt | heq | hgt
    · exact hlt
    · have hget_eq : seq[seq.idxOf a]? = seq[seq.idxOf b]? := by rw [heq]
      rw [List.getElem?_eq_getElem hia, List.getElem?_eq_getElem hib] at hget_eq
      have hab_eq : a = b := hga.symm.trans ((Option.some.inj hget_eq).trans hgb)
      subst hab_eq
      exact False.elim (lt_irrefl _ hkey_lt)
    · have hrev := (List.pairwise_iff_getElem.mp hsorted) _ _ hib hia hgt
      rw [hgb, hga] at hrev
      exact False.elim (lt_asymm hkey_lt hrev)
  · rw [seqValid_iff_registerValAfter]
    refine ⟨fun i hi => by obtain ⟨hlt, _, hel⟩ := (hmem_seq i).mp hi; exact ⟨hlt, hel⟩, ?_⟩
    intro k hk hi_k stp r_val hst_r
    have hr_mem : seq[k] ∈ seq := List.getElem_mem hk
    obtain ⟨_, hsome_r, _⟩ := (hmem_seq seq[k]).mp hr_mem
    obtain ⟨τ_r, hτ_r⟩ := Option.isSome_iff_exists.mp hsome_r
    have hkr : s.history[seq[k]].kind = .read := ((hg.hist_wf seq[k] hi_k).2.2.1 stp r_val hst_r).1
    have htv_r : TagValidVal v₀ s.history opTag τ_r r_val :=
      hg.val_valid.2.2 seq[k] hi_k stp r_val τ_r hst_r hτ_r
    have hpref_lt : ∀ x ∈ seq.take k,
        abdLinKey opTag s.history x < abdLinKey opTag s.history seq[k] := by
      intro x hx
      obtain ⟨m, hm_len, rfl⟩ := List.getElem_of_mem hx
      have hmk : m < k := by rw [List.length_take] at hm_len; omega
      have hm_seq : m < seq.length := hmk.trans hk
      rw [List.getElem_take]
      exact (List.pairwise_iff_getElem.mp hsorted) m k hm_seq hk hmk
    have hpref_write_le : ∀ w ∈ seq.take k, ∀ hw : w < s.history.length, ∀ vw τ_w,
        s.history[w].kind = .write vw → opTag w = some τ_w → τ_w ≤ τ_r := by
      intro w hw_mem _ _ τ_w _ hτ_w
      have hklt := hpref_lt w hw_mem
      by_contra hnot_le
      exact lt_asymm hklt (abdLinKey_lt_of_tag_lt hτ_r hτ_w (lt_of_not_ge hnot_le))
    rcases htv_r with ⟨rfl, rfl⟩ | ⟨w, hw_lt, hkw, hτ_w⟩
    · symm
      apply registerValAfter_reads
      intro x hx
      have hx_seq : x ∈ seq := List.mem_of_mem_take hx
      obtain ⟨hx_lt, hsome_x, _⟩ := (hmem_seq x).mp hx_seq
      obtain ⟨τ_x, hτ_x⟩ := Option.isSome_iff_exists.mp hsome_x
      refine ⟨hx_lt, ?_⟩
      cases hkx : s.history[x].kind with
      | read => rfl
      | write vx =>
        have hle := hpref_write_le x hx hx_lt vx τ_x hkx hτ_x
        obtain ⟨seq_x, hτ_eq⟩ := hg.write_unique.1 x hx_lt vx τ_x hkx hτ_x
        rw [hτ_eq] at hle
        exact False.elim (not_lt_of_ge hle (initTag_lt_nextWriteTag seq_x _))
    · have hw_elig : s.history[w].isEligible := by
        cases hsw : s.history[w].status with
        | pending => simp [OpRecord.isEligible, hkw, hsw]
        | doneWrite _ => simp [OpRecord.isEligible, hkw, hsw]
        | doneRead sr vr =>
          have hkr_w := ((hg.hist_wf w hw_lt).2.2.1 sr vr hsw).1
          rw [hkw] at hkr_w; cases hkr_w
      have hw_seq : w ∈ seq := (hmem_seq w).mpr ⟨hw_lt, by simp [hτ_w], hw_elig⟩
      have hw_key_lt : abdLinKey opTag s.history w < abdLinKey opTag s.history seq[k] :=
        abdLinKey_write_lt_read hw_lt hi_k hkw hkr hτ_w hτ_r le_rfl
      have hw_in_take : w ∈ seq.take k := by
        have hiw : seq.idxOf w < seq.length := List.idxOf_lt_length_of_mem hw_seq
        have hgw : seq[seq.idxOf w] = w := List.getElem_idxOf hiw
        have hlt_k : seq.idxOf w < k := by
          rcases lt_trichotomy (seq.idxOf w) k with hlt | heq | hgt
          · exact hlt
          · have hget_eq : seq[seq.idxOf w]? = seq[k]? := by rw [heq]
            rw [List.getElem?_eq_getElem hiw, List.getElem?_eq_getElem hk] at hget_eq
            have hweq : w = seq[k] := hgw.symm.trans (Option.some.inj hget_eq)
            subst hweq; exact False.elim (lt_irrefl _ hw_key_lt)
          · have hrev := (List.pairwise_iff_getElem.mp hsorted) k (seq.idxOf w) hk hiw hgt
            rw [hgw] at hrev
            exact False.elim (lt_asymm hw_key_lt hrev)
        have htake_len : seq.idxOf w < (seq.take k).length := by
          rw [List.length_take]; omega
        have hget_take : (seq.take k)[seq.idxOf w] = w := by
          rw [List.getElem_take, hgw]
        exact hget_take ▸ List.getElem_mem htake_len
      obtain ⟨before, after, hsplit⟩ := List.append_of_mem hw_in_take
      have hsub_sorted : List.Pairwise
          (fun a b => abdLinKey opTag s.history a < abdLinKey opTag s.history b)
          (before ++ w :: after) := by
        rw [← hsplit]
        exact hsorted.take
      have hafter_gt : ∀ x ∈ after,
          abdLinKey opTag s.history w < abdLinKey opTag s.history x :=
        (List.pairwise_append.mp hsub_sorted).2.1 |> List.pairwise_cons.mp |>.1
      have hafter_reads : ∀ x ∈ after, ∃ hx : x < s.history.length, s.history[x].kind = .read := by
        intro x hx
        have hx_take : x ∈ seq.take k := by rw [hsplit]; simp [hx]
        have hx_seq : x ∈ seq := List.mem_of_mem_take hx_take
        obtain ⟨hx_lt, hsome_x, _⟩ := (hmem_seq x).mp hx_seq
        obtain ⟨τ_x, hτ_x⟩ := Option.isSome_iff_exists.mp hsome_x
        refine ⟨hx_lt, ?_⟩
        cases hkx : s.history[x].kind with
        | read => rfl
        | write vx =>
          have hle : τ_x ≤ τ_r := hpref_write_le x hx_take hx_lt vx τ_x hkx hτ_x
          rcases lt_or_eq_of_le hle with hlt | heq_tag
          · exact False.elim (lt_asymm (hafter_gt x hx) (abdLinKey_lt_of_tag_lt hτ_x hτ_w hlt))
          · subst heq_tag
            have hxeq : x = w := hg.write_unique.2 x w hx_lt hw_lt vx r_val τ_x hkx hkw hτ_x hτ_w
            subst hxeq
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
    obtain ⟨opTag, hg⟩ := hgood k
    have hps := hg.proc_sync p
    rw [hp] at hps
    cases hph : ((ss k).proc p).state.phase <;> rw [hph] at hps
    · exact False.elim hps
    · exact ⟨hps.1, hps.2.2.2.2.1⟩
    · exact ⟨hps.1, hps.2.2.2.2.1⟩
  have hlen_le : ∀ k₁ k₂, k₁ ≤ k₂ → (ss k₁).history.length ≤ (ss k₂).history.length :=
    fun k₁ k₂ hle => π.mTr_history_length_le (hexec.extract_mTr hle)
  by_cases hdone₀ : (ss k₀).history[i].status.isCompleted = true
  · exact ⟨k₀, hi₀, le_rfl, hdone₀⟩
  by_contra! hnever
  have hstable_comp : ∀ j (hij : i < (ss j).history.length),
      (ss j).history[i].status.isCompleted = true → False := by
    intro j hij hcj
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
    have hcM : (ss (j + d)).history[i].status.isCompleted = true := heqM ▸ hcj
    have hk₀_le : k₀ ≤ j + d := hd ▸ le_max_left k₀ j
    exact hnever (j + d) hM hk₀_le hcM
  have hnot_comp : ∀ j (hij : i < (ss j).history.length),
      (ss j).history[i].status = .pending := by
    intro j hij
    cases hst : (ss j).history[i].status with
    | pending => rfl
    | doneRead _ _ => exact False.elim (hstable_comp j hij (by simp [hst]))
    | doneWrite _ => exact False.elim (hstable_comp j hij (by simp [hst]))
  classical
  have hex_lt : ∃ k, i < (ss k).history.length := ⟨k₀, hi₀⟩
  let k₁ := Nat.find hex_lt
  have hk₁_lt : i < (ss k₁).history.length := Nat.find_spec hex_lt
  have hk₁_pos : 0 < k₁ := by
    by_contra h0
    have hk0 : k₁ = 0 := by omega
    rw [hk0, hstart] at hk₁_lt
    simp [Protocol.start] at hk₁_lt
  let k_inv := k₁ - 1
  have hk_succ : k_inv + 1 = k₁ := by omega
  have hnot_before : ¬ i < (ss k_inv).history.length := Nat.find_min hex_lt (by omega)
  have htr_inv := hexec k_inv
  rw [hk_succ] at htr_inv
  have hact_inv : ∃ c₀ kind, xs k_inv = .invoke c₀ kind ∧
      (ss k_inv).history.length = i ∧
      ((ss k_inv).proc c₀).pending = none ∧
      ss k₁ = π.doInvoke c₀ kind (ss k_inv) := by
    cases hxs : xs k_inv with
    | stutter =>
      rw [hxs] at htr_inv
      exact False.elim (hnot_before (htr_inv ▸ hk₁_lt))
    | deliver e =>
      rw [hxs] at htr_inv
      obtain ⟨_, heq⟩ := htr_inv
      have hlen : (ss k₁).history.length = (ss k_inv).history.length := by
        simp [heq, Protocol.doDeliver]
      exact False.elim (hnot_before (hlen ▸ hk₁_lt))
    | invoke c₀ kind =>
      rw [hxs] at htr_inv
      obtain ⟨hp0, heq⟩ := htr_inv
      have hlen : (ss k₁).history.length = (ss k_inv).history.length + 1 := by
        simp [heq, Protocol.doInvoke]
      exact ⟨c₀, kind, rfl, by omega, hp0, heq⟩
  obtain ⟨c₀, kind, _, hlen_kinv, _, hss_k₁⟩ := hact_inv
  have hck_const : ∀ j (hij : i < (ss j).history.length),
      (ss j).history[i].caller = c₀ ∧ (ss j).history[i].kind = kind := by
    intro j hij
    have hk₁_j : k₁ ≤ j := Nat.find_min' hex_lt hij
    obtain ⟨hcj, hkj, _⟩ :=
      π.mTr_history_entry_preserves (hexec.extract_mTr hk₁_j) hk₁_lt hij
    have hk₁_ck : (ss k₁).history[i].caller = c₀ ∧ (ss k₁).history[i].kind = kind := by
      simp [hss_k₁, Protocol.doInvoke, ← hlen_kinv]
    exact ⟨hcj.trans hk₁_ck.1, hkj.trans hk₁_ck.2⟩
  have hc₀_notF : c₀ ∉ F := (hck_const k₀ hi₀).1 ▸ hc
  have hpend_c₀ : ∀ j, k₁ ≤ j → ((ss j).proc c₀).pending = some ⟨i, kind⟩ := by
    intro j hj
    have hij : i < (ss j).history.length := lt_of_lt_of_le hk₁_lt (hlen_le k₁ j hj)
    obtain ⟨opTag, hg⟩ := hgood j
    have hp := (hg.hist_wf i hij).2.2.2.2 (hnot_comp j hij)
    obtain ⟨hcj, hkj⟩ := hck_const j hij
    simpa [hcj, hkj] using hp
  let reqId := ((ss k_inv).proc c₀).state.nextReqId
  have hinit_p1 : ((ss k₁).proc c₀).state.phase = .phase1 reqId kind ∅ (initTag P) v₀ ∧
      ∀ q : P, ⟨c₀, q, .query reqId⟩ ∈ (ss k₁).msgs := by
    refine ⟨?_, fun q => ?_⟩
    · simp [π, hss_k₁, Protocol.doInvoke, abdProtocol, abdOnInvoke, reqId]
    · simp only [π, hss_k₁, Protocol.doInvoke, abdProtocol, abdOnInvoke, Multiset.mem_add]
      exact Or.inr (mem_broadcastAll_tag c₀ q (ABDMsg.query reqId))
  have hstep_other : ∀ j, k₁ ≤ j → ∀ ph, ((ss j).proc c₀).state.phase = ph →
      (((ss (j + 1)).proc c₀).state.phase = ph ∧
        (∀ q rId rt rv, xs j ≠ .deliver ⟨q, c₀, .queryResp rId rt rv⟩) ∧
        (∀ q rId, xs j ≠ .deliver ⟨q, c₀, .ack rId⟩)) ∨
      (∃ q rId rt rv, xs j = .deliver ⟨q, c₀, .queryResp rId rt rv⟩) ∨
      (∃ q rId, xs j = .deliver ⟨q, c₀, .ack rId⟩) := by
    intro j hj ph hph
    have htr_j := hexec j
    cases hxs : xs j with
    | stutter =>
      rw [hxs] at htr_j
      have hss_eq : ss (j + 1) = ss j := htr_j
      exact Or.inl ⟨by simpa [hss_eq] using hph,
        (fun _ _ _ _ h => nomatch h), (fun _ _ h => nomatch h)⟩
    | invoke cm km =>
      rw [hxs] at htr_j; obtain ⟨hp_cm, heq⟩ := htr_j
      have hne : cm ≠ c₀ := by
        intro heq_c; subst heq_c; rw [hpend_c₀ j hj] at hp_cm; cases hp_cm
      exact Or.inl ⟨by simpa [heq, Protocol.doInvoke, Function.update_of_ne hne.symm] using hph,
        (fun _ _ _ _ h => nomatch h), (fun _ _ h => nomatch h)⟩
    | deliver e =>
      rw [hxs] at htr_j; obtain ⟨_, heq⟩ := htr_j
      by_cases hed : e.dest = c₀
      · cases hb : e.body with
        | query _ =>
          refine Or.inl ⟨by subst hed; simp [heq, Protocol.doDeliver, abdProtocol, hb, abdOnRecv,
            hph], ?_, ?_⟩
          · intro _ _ _ _ h; injection h with he_eq; rw [he_eq] at hb; cases hb
          · intro _ _ h; injection h with he_eq; rw [he_eq] at hb; cases hb
        | store _ inTag inVal =>
          refine Or.inl ⟨?_, ?_, ?_⟩
          · subst hed
            simp only [heq, Protocol.doDeliver, abdProtocol, hb, abdOnRecv, Function.update_self]
            split_ifs <;> exact hph
          · intro _ _ _ _ h; injection h with he_eq; rw [he_eq] at hb; cases hb
          · intro _ _ h; injection h with he_eq; rw [he_eq] at hb; cases hb
        | queryResp rId rt rv =>
          refine Or.inr (Or.inl ⟨e.src, rId, rt, rv, ?_⟩)
          congr 1; ext <;> simp [hed, hb]
        | ack rId =>
          refine Or.inr (Or.inr ⟨e.src, rId, ?_⟩)
          congr 1; ext <;> simp [hed, hb]
      · refine Or.inl ⟨by simpa [heq, Protocol.doDeliver, Function.update_of_ne (Ne.symm hed)]
          using hph, ?_, ?_⟩
        · intro _ _ _ _ h; injection h with he_eq
          exact False.elim (hed (congrArg Envelope.dest he_eq))
        · intro _ _ h; injection h with he_eq
          exact False.elim (hed (congrArg Envelope.dest he_eq))
  let p1Set (j : ℕ) : Finset P :=
    match ((ss j).proc c₀).state.phase with
    | .phase1 _ _ resp _ _ => resp
    | _ => ∅
  let IsP1 (j : ℕ) : Prop :=
    ∃ resp bt bv, ((ss j).proc c₀).state.phase = .phase1 reqId kind resp bt bv
  have hp1_step : ∀ j, k₁ ≤ j → IsP1 j →
      (IsP1 (j + 1) ∧ p1Set j ⊆ p1Set (j + 1) ∧
        (∀ q rTag rVal, xs j = .deliver ⟨q, c₀, .queryResp reqId rTag rVal⟩ →
          q ∈ p1Set (j + 1))) ∨
      (∃ cTag cVal,
        ((ss (j + 1)).proc c₀).state.phase = .phase2 reqId kind cTag cVal ∅ ∧
        ∀ q : P, ⟨c₀, q, .store reqId cTag cVal⟩ ∈ (ss (j + 1)).msgs) := by
    intro j hj ⟨resp, bt, bv, hph⟩
    rcases hstep_other j hj _ hph with
      ⟨hph', hno_qr, _⟩ | ⟨src, rId, rTag, rVal, hxs⟩ | ⟨src, rId, hxs⟩
    · exact Or.inl ⟨⟨resp, bt, bv, hph'⟩, by simp [p1Set, hph, hph'],
        fun q rt rv hdel => False.elim (hno_qr q reqId rt rv hdel)⟩
    · have htr_j := hexec j
      rw [hxs] at htr_j; obtain ⟨_, heq⟩ := htr_j
      by_cases hr : rId = reqId
      · subst hr
        by_cases hq_card : Fintype.card P - t ≤ (insert src resp).card
        · right
          let bt' := if bt < rTag then rTag else bt
          let bv' := if bt < rTag then rVal else bv
          let cTag := match kind with
            | .write _ => nextWriteTag bt'.seq c₀
            | .read => bt'
          let cVal := match kind with
            | .write v => v
            | .read => bv'
          refine ⟨cTag, cVal, ?_, fun q => ?_⟩
          · simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, hq_card, bt', bv',
              cTag, cVal]
          · simp only [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, ↓reduceIte,
              hq_card, Multiset.mem_add]
            exact Or.inr (mem_broadcastAll_tag c₀ q (ABDMsg.store reqId cTag cVal))
        · left
          let bt' := if bt < rTag then rTag else bt
          let bv' := if bt < rTag then rVal else bv
          have hph' : ((ss (j + 1)).proc c₀).state.phase =
              .phase1 reqId kind (insert src resp) bt' bv' := by
            simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, hq_card, bt', bv']
          refine ⟨⟨insert src resp, bt', bv', hph'⟩,
            by simp [p1Set, hph, hph', Finset.subset_insert], ?_⟩
          intro q rt rv hdel
          rw [hxs] at hdel
          injection hdel with he_eq
          have hsrc : src = q := congrArg Envelope.src he_eq
          subst hsrc
          simp [p1Set, hph']
      · have hph' : ((ss (j + 1)).proc c₀).state.phase = .phase1 reqId kind resp bt bv := by
          simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, hr]
        refine Or.inl ⟨⟨resp, bt, bv, hph'⟩, by simp [p1Set, hph, hph'], ?_⟩
        intro q rt rv hdel
        rw [hxs] at hdel
        injection hdel with he_eq
        have hbody := congrArg Envelope.body he_eq
        dsimp only at hbody
        injection hbody with hreq
        exact False.elim (hr hreq)
    · have htr_j := hexec j
      rw [hxs] at htr_j; obtain ⟨_, heq⟩ := htr_j
      have hph' : ((ss (j + 1)).proc c₀).state.phase = .phase1 reqId kind resp bt bv := by
        simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph]
      refine Or.inl ⟨⟨resp, bt, bv, hph'⟩, by simp [p1Set, hph, hph'], ?_⟩
      intro q rt rv hdel
      rw [hxs] at hdel
      injection hdel with he_eq
      have hbody := congrArg Envelope.body he_eq
      cases hbody
  have hex_exit_p1 : ∃ j, k₁ ≤ j ∧ ¬ IsP1 j := by
    by_contra! hall_p1
    apply not_forall_stay_of_fair h2t hF hfair hc₀_notF k₁
      (fun q => ⟨c₀, q, .query reqId⟩)
      (fun q r => ∃ rt rv, r = ⟨q, c₀, .queryResp reqId rt rv⟩)
      p1Set
      (fun _ => rfl)
      hinit_p1.2
    · intro q j _ hdel
      have htr_j := hexec j
      rw [hdel] at htr_j
      obtain ⟨_, heq⟩ := htr_j
      refine ⟨⟨q, c₀, .queryResp reqId ((ss j).proc q).state.repTag ((ss j).proc q).state.repVal⟩,
        ?_, rfl, _, _, rfl⟩
      simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, tagSender]
    · intro j hj
      rcases hp1_step j hj (hall_p1 j hj) with ⟨_, hsub, _⟩ | ⟨_, _, hph2, _⟩
      · exact hsub
      · obtain ⟨_, _, _, hph1⟩ := hall_p1 (j + 1) (Nat.le_succ_of_le hj)
        rw [hph2] at hph1; cases hph1
    · intro j hj
      obtain ⟨resp, bt, bv, hph⟩ := hall_p1 j hj
      obtain ⟨opTag, hg⟩ := hgood j
      have hps := hg.proc_sync c₀
      rw [hpend_c₀ j hj, hph] at hps
      simpa [p1Set, hph] using hps.2.2.2.2.2.2.2.1
    · intro q r j hj hdel ⟨rt, rv, hr_eq⟩
      subst hr_eq
      rcases hp1_step j hj (hall_p1 j hj) with ⟨_, _, habs⟩ | ⟨_, _, hph2, _⟩
      · exact habs q rt rv hdel
      · obtain ⟨_, _, _, hph1⟩ := hall_p1 (j + 1) (Nat.le_succ_of_le hj)
        rw [hph2] at hph1; cases hph1
  let hex_gt : ∃ d, ¬ IsP1 (k₁ + d) := by
    obtain ⟨j, hj, hnot⟩ := hex_exit_p1
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact ⟨d, hnot⟩
  let d₂ := Nat.find hex_gt
  have hd₂_not : ¬ IsP1 (k₁ + d₂) := Nat.find_spec hex_gt
  have hd₂_pos : 0 < d₂ := by
    by_contra h0
    have hd0 : d₂ = 0 := by omega
    exact hd₂_not (hd0 ▸ ⟨∅, initTag P, v₀, hinit_p1.1⟩)
  have hd₂_prev : IsP1 (k₁ + (d₂ - 1)) := by
    by_contra hnot
    exact Nat.find_min hex_gt (by omega) hnot
  have hk₂_eq : k₁ + (d₂ - 1) + 1 = k₁ + d₂ := by omega
  let k₂ := k₁ + d₂
  obtain ⟨cTag, cVal, hinit_p2_ph, hinit_p2_msgs⟩ :
      ∃ cTag cVal, ((ss k₂).proc c₀).state.phase = .phase2 reqId kind cTag cVal ∅ ∧
        ∀ q : P, ⟨c₀, q, .store reqId cTag cVal⟩ ∈ (ss k₂).msgs := by
    rcases hp1_step (k₁ + (d₂ - 1)) (Nat.le_add_right k₁ _) hd₂_prev with ⟨hp1', _⟩ | hp2
    · exact False.elim (hd₂_not (hk₂_eq ▸ hp1'))
    · simpa [k₂, hk₂_eq] using hp2
  let p2Set (j : ℕ) : Finset P :=
    match ((ss j).proc c₀).state.phase with
    | .phase2 _ _ _ _ acks => acks
    | _ => ∅
  let IsP2 (j : ℕ) : Prop :=
    ∃ acks, ((ss j).proc c₀).state.phase = .phase2 reqId kind cTag cVal acks
  have hp2_step : ∀ j, k₂ ≤ j → IsP2 j →
      IsP2 (j + 1) ∧ p2Set j ⊆ p2Set (j + 1) ∧
      ∀ q, xs j = .deliver ⟨q, c₀, .ack reqId⟩ → q ∈ p2Set (j + 1) := by
    intro j hj ⟨acks, hph⟩
    have hk₁_j : k₁ ≤ j := (Nat.le_add_right k₁ d₂).trans hj
    rcases hstep_other j hk₁_j _ hph with
      ⟨hph', _, hno_ack⟩ | ⟨src, rId, rt, rv, hxs⟩ | ⟨src, rId, hxs⟩
    · exact ⟨⟨acks, hph'⟩, by simp [p2Set, hph, hph'],
        fun q hdel => False.elim (hno_ack q reqId hdel)⟩
    · have htr_j := hexec j
      rw [hxs] at htr_j; obtain ⟨_, heq⟩ := htr_j
      have hph' : ((ss (j + 1)).proc c₀).state.phase = .phase2 reqId kind cTag cVal acks := by
        simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph]
      refine ⟨⟨acks, hph'⟩, by simp [p2Set, hph, hph'], ?_⟩
      intro q hdel
      rw [hxs] at hdel
      injection hdel with he_eq
      have hbody := congrArg Envelope.body he_eq
      cases hbody
    · have htr_j := hexec j
      rw [hxs] at htr_j; obtain ⟨_, heq⟩ := htr_j
      by_cases hr : rId = reqId
      · subst hr
        by_cases hq_card : Fintype.card P - t ≤ (insert src acks).card
        · exfalso
          have hp_next := hpend_c₀ (j + 1) (Nat.le_succ_of_le hk₁_j)
          have hp_cur := hpend_c₀ j hk₁_j
          simp only [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, ↓reduceIte,
            hq_card, Function.update_self, hp_cur, deliverPending] at hp_next
          cases kind <;> simp [matchCompletion] at hp_next
        · have hph' : ((ss (j + 1)).proc c₀).state.phase =
              .phase2 reqId kind cTag cVal (insert src acks) := by
            simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, hq_card]
          refine ⟨⟨insert src acks, hph'⟩,
            by simp [p2Set, hph, hph', Finset.subset_insert], ?_⟩
          intro q hdel
          rw [hxs] at hdel
          injection hdel with he_eq
          have hsrc : src = q := congrArg Envelope.src he_eq
          subst hsrc
          simp [p2Set, hph']
      · have hph' : ((ss (j + 1)).proc c₀).state.phase = .phase2 reqId kind cTag cVal acks := by
          simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, hph, hr]
        refine ⟨⟨acks, hph'⟩, by simp [p2Set, hph, hph'], ?_⟩
        intro q hdel
        rw [hxs] at hdel
        injection hdel with he_eq
        have hbody := congrArg Envelope.body he_eq
        dsimp only at hbody
        injection hbody with hreq
        exact False.elim (hr hreq)
  have hall_p2 : ∀ j, k₂ ≤ j → IsP2 j := by
    intro j hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    induction d with
    | zero => exact ⟨∅, hinit_p2_ph⟩
    | succ d ih => exact (hp2_step (k₂ + d) (Nat.le_add_right k₂ d) (ih (Nat.le_add_right k₂ d))).1
  apply not_forall_stay_of_fair h2t hF hfair hc₀_notF k₂
    (fun q => ⟨c₀, q, .store reqId cTag cVal⟩)
    (fun q r => r = ⟨q, c₀, .ack reqId⟩)
    p2Set
    (fun _ => rfl)
    hinit_p2_msgs
  · intro q j _ hdel
    have htr_j := hexec j
    rw [hdel] at htr_j
    obtain ⟨_, heq⟩ := htr_j
    refine ⟨⟨q, c₀, .ack reqId⟩, ?_, rfl, rfl⟩
    simp [heq, Protocol.doDeliver, abdProtocol, abdOnRecv, tagSender]
  · intro j hj
    exact (hp2_step j hj (hall_p2 j hj)).2.1
  · intro j hj
    obtain ⟨acks, hph⟩ := hall_p2 j hj
    obtain ⟨opTag, hg⟩ := hgood j
    have hk₁_j : k₁ ≤ j := (Nat.le_add_right k₁ d₂).trans hj
    have hps := hg.proc_sync c₀
    rw [hpend_c₀ j hk₁_j, hph] at hps
    simpa [p2Set, hph] using hps.2.2.2.2.2.2.2.1
  · intro q r j hj hdel hr_eq
    subst hr_eq
    exact (hp2_step j hj (hall_p2 j hj)).2.2 q hdel

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
