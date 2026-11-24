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
import CslibFrontier.Tactic.FinsetCard

/-!
# Asynchronous quorum protocol model and split-brain impossibility

Defines the deterministic crash-tolerant `AsyncQuorumProtocol` model and proves the original
disjoint-quorum partition impossibility (`not_synod_safe_of_disjoint_quorums`,
`not_safeSingleQuorum_of_card_le_two_mul`).

## Main definitions

* `Cslib.Distributed.Paxos.Packet`, `Cslib.Distributed.Paxos.NodeProcState`,
  `Cslib.Distributed.Paxos.NetState`, `Cslib.Distributed.Paxos.NetAction`,
  `Cslib.Distributed.Paxos.AsyncQuorumProtocol`: general asynchronous crash-tolerant message-passing
  protocol model for single-quorum progress analysis.

## Main results

* `Cslib.Distributed.Paxos.not_synod_safe_of_disjoint_quorums`: split-brain impossibility for any
  `AsyncQuorumProtocol` admitting progress on disjoint subsets `Q₁, Q₂`.
* `Cslib.Distributed.Paxos.not_safeSingleQuorum_of_card_le_two_mul`: impossibility of `t`-crash
  single-quorum progress when `2 ≤ Fintype.card P ≤ 2 * t`.
-/

public section

namespace Cslib.Distributed.Paxos

open Cslib

/-! ### Part 3: Disjoint-quorum split-brain impossibility -/

/-- A point-to-point network packet carrying `src`, `dest`, and `body`. -/
@[ext]
structure Packet (P M : Type*) where
  /-- Sender process identity. -/
  src : P
  /-- Recipient process identity. -/
  dest : P
  /-- Packet payload. -/
  body : M
  deriving @[expose] DecidableEq

/-- Local process state paired with a write-once consensus decision register `out`. -/
@[ext]
structure NodeProcState (S V : Type*) where
  /-- Internal protocol state. -/
  state : S
  /-- Write-once consensus output (`none` until decided). -/
  out : Option V
  deriving @[expose] DecidableEq

/-- Global configuration of an asynchronous message-passing consensus protocol. -/
@[ext]
structure NetState (P S M V : Type*) where
  /-- Sent network packets (subject to arbitrary reordering, duplication, and delay/partition). -/
  msgs : Finset (Packet P M)
  /-- Local state of each process. -/
  proc : P → NodeProcState S V

/-- Transition labels of an `AsyncQuorumProtocol`: spontaneous local steps, packet deliveries, and
stuttering. -/
inductive NetAction (P L M : Type*) where
  /-- Process `p` takes a local step with parameter `lbl`. -/
  | localStep (p : P) (lbl : L)
  /-- Packet `pkt` in the network is delivered to `pkt.dest`. -/
  | deliver (pkt : Packet P M)
  /-- Dummy stuttering step. -/
  | stutter
  deriving @[expose] DecidableEq

/-- Whether `act` touches only processes and channels internal to subset `Q`. -/
@[expose] def NetAction.InGroup {P L M : Type*} (Q : Finset P) : NetAction P L M → Prop
  | .localStep p _ => p ∈ Q
  | .deliver pkt => pkt.src ∈ Q ∧ pkt.dest ∈ Q
  | .stutter => True

/-- Output of a single local or receive step: updated state, outgoing `(dest, body)` pairs, and
optional decision candidate. -/
structure StepResult (P S M V : Type*) where
  /-- Updated internal node state. -/
  nextState : S
  /-- Outgoing `(dest, body)` pairs to be tagged with the executing node as `src`. -/
  outgoing : Finset (P × M)
  /-- Optional decision value (recorded only if `out` was `none`). -/
  decideVal : Option V

/-- General deterministic asynchronous crash-tolerant message-passing protocol over processes `P`,
local state `S`, local-step labels `L`, messages `M`, and value domain `V`. -/
structure AsyncQuorumProtocol (P S L M V : Type*) where
  /-- Initial local state of process `p` given its input `inp p : V`. -/
  init : P → V → S
  /-- Guard for spontaneous local step `(p, lbl)`. -/
  localEnabled : P → L → NodeProcState S V → Prop
  /-- Transition function for spontaneous local step `(p, lbl)`. -/
  onLocal : P → L → NodeProcState S V → StepResult P S M V
  /-- Transition function when `dest` receives `body` from `src`. -/
  onRecv : P → P → M → NodeProcState S V → StepResult P S M V

namespace AsyncQuorumProtocol

variable {P S L M V : Type*} [DecidableEq P] [DecidableEq M]
  (π : AsyncQuorumProtocol P S L M V)

/-- Initial network state for input assignment `inp : P → V`. -/
@[expose] def start (inp : P → V) : NetState P S M V where
  msgs := ∅
  proc p := { state := π.init p (inp p), out := none }

/-- Apply a `StepResult` emitted by process `p` to global state `s`. -/
@[expose] def applyResult (p : P) (res : StepResult P S M V) (s : NetState P S M V) :
    NetState P S M V where
  msgs := s.msgs ∪ res.outgoing.image fun db => ⟨p, db.1, db.2⟩
  proc q :=
    if q = p then
      { state := res.nextState
        out := if (s.proc p).out.isNone then res.decideVal else (s.proc p).out }
    else s.proc q

/-- Labelled transition system of `π`. -/
@[expose] def lts : LTS (NetState P S M V) (NetAction P L M) where
  Tr s act s' := match act with
    | .localStep p lbl =>
      π.localEnabled p lbl (s.proc p) ∧ s' = applyResult p (π.onLocal p lbl (s.proc p)) s
    | .deliver pkt =>
      pkt ∈ s.msgs ∧
        s' = applyResult pkt.dest (π.onRecv pkt.src pkt.dest pkt.body (s.proc pkt.dest)) s
    | .stutter => s' = s

/-- `π.Reachable inp s` holds when `s` is reachable from `π.start inp` in `π.lts`. -/
@[expose] def Reachable (inp : P → V) (s : NetState P S M V) : Prop :=
  π.lts.CanReach (π.start inp) s

/-- Consensus safety: in every reachable state, all decided values agree with one another and every
decided value equals some process's initial input. -/
@[expose] def SafeConsensus : Prop :=
  ∀ (inp : P → V) (s : NetState P S M V), π.Reachable inp s →
    (∀ p₁ p₂ v₁ v₂, (s.proc p₁).out = some v₁ → (s.proc p₂).out = some v₂ → v₁ = v₂) ∧
      (∀ p v, (s.proc p).out = some v → ∃ q, inp q = v)

/-- Single-quorum progress on subset `Q`: for every uniform input `fun _ => v`, there exists a
finite `Q`-internal execution (`InGroup Q`, i.e., with all nodes outside `Q` silent/crashed from the
start) in which some node `q ∈ Q` decides a value. -/
@[expose] def CanDecideIn (Q : Finset P) : Prop :=
  ∀ v : V, ∃ xl s,
    (∀ act ∈ xl, act.InGroup Q) ∧
    π.lts.MTr (π.start fun _ => v) xl s ∧
    ∃ q ∈ Q, ∃ w, (s.proc q).out = some w

/-- Partition simulation lemma: any `Q`-internal execution (`InGroup Q`) from `s₀` can be replayed
identically from any `u₀` that agrees with `s₀` on `Q`'s local states and contains `s₀`'s
`Q`-sourced packets, leaving all nodes outside `Q` and all non-`Q`-sourced packets untouched. -/
private lemma replay_group_mTr {Q : Finset P} {s₀ s₁ u₀ : NetState P S M V}
    {xl : List (NetAction P L M)}
    (hgroup : ∀ act ∈ xl, act.InGroup Q)
    (hmtr : π.lts.MTr s₀ xl s₁)
    (hproc₀ : ∀ p ∈ Q, u₀.proc p = s₀.proc p)
    (hmsgs₀ : ∀ pkt : Packet P M, pkt.src ∈ Q → pkt ∈ s₀.msgs → pkt ∈ u₀.msgs) :
    ∃ u₁, π.lts.MTr u₀ xl u₁ ∧
      (∀ p ∈ Q, u₁.proc p = s₁.proc p) ∧
      (∀ p ∉ Q, u₁.proc p = u₀.proc p) ∧
      (∀ pkt : Packet P M, pkt.src ∉ Q → (pkt ∈ u₁.msgs ↔ pkt ∈ u₀.msgs)) := by
  induction hmtr generalizing u₀ with
  | refl =>
    exact ⟨u₀, LTS.MTr.refl, hproc₀, fun _ _ => rfl, fun _ _ => Iff.rfl⟩
  | @stepL s act s' rest s_end htr _ ih =>
    have hactQ : act.InGroup Q := hgroup act List.mem_cons_self
    have hrestQ : ∀ a ∈ rest, a.InGroup Q := fun a ha => hgroup a (List.mem_cons_of_mem act ha)
    have happly : ∀ (p : P) (hpQ : p ∈ Q) (res : StepResult P S M V),
        u₀.proc p = s.proc p →
        let u' := applyResult p res u₀
        let s_next := applyResult p res s
        (∀ q ∈ Q, u'.proc q = s_next.proc q) ∧
          (∀ q ∉ Q, u'.proc q = u₀.proc q) ∧
          (∀ pkt : Packet P M, pkt.src ∈ Q → pkt ∈ s_next.msgs → pkt ∈ u'.msgs) ∧
          (∀ pkt : Packet P M, pkt.src ∉ Q → (pkt ∈ u'.msgs ↔ pkt ∈ u₀.msgs)) := by
      intro p hpQ res hp_eq
      refine ⟨fun q hqQ => ?_, fun q hq_not => ?_, fun pkt hsrc hm => ?_, fun pkt hsrc => ?_⟩
      · dsimp only [applyResult]
        by_cases hqp : q = p
        · subst hqp; simp only [↓reduceIte, hp_eq]
        · simp only [hqp, ↓reduceIte, hproc₀ q hqQ]
      · have hne : q ≠ p := fun h => hq_not (h ▸ hpQ)
        dsimp only [applyResult]
        simp only [hne, ↓reduceIte]
      · dsimp only [applyResult] at hm ⊢
        rcases Finset.mem_union.mp hm with hold | hnew
        · exact Finset.mem_union_left _ (hmsgs₀ pkt hsrc hold)
        · exact Finset.mem_union_right _ hnew
      · dsimp only [applyResult]
        refine ⟨fun hm => ?_, fun hm => Finset.mem_union_left _ hm⟩
        rcases Finset.mem_union.mp hm with hold | hnew
        · exact hold
        · obtain ⟨db, _, heq⟩ := Finset.mem_image.mp hnew
          have hsrc_eq : pkt.src = p := (congrArg Packet.src heq).symm
          exact absurd (hsrc_eq ▸ hpQ) hsrc
    cases act with
    | localStep p lbl =>
      obtain ⟨hen, rfl⟩ := htr
      have hp_eq := hproc₀ p hactQ
      let res := π.onLocal p lbl (s.proc p)
      let u' := applyResult p res u₀
      have htr_u : π.lts.Tr u₀ (.localStep p lbl) u' := by
        dsimp only [lts]
        rw [hp_eq]
        exact ⟨hen, rfl⟩
      obtain ⟨hp', hnp', hm', hnm'⟩ := happly p hactQ res hp_eq
      obtain ⟨u₁, hmtr₁, hp₁, hnp₁, hnm₁⟩ := ih hrestQ hp' hm'
      exact ⟨u₁, LTS.MTr.stepL htr_u hmtr₁, hp₁,
        fun q hq => (hnp₁ q hq).trans (hnp' q hq),
        fun pkt hpkt => (hnm₁ pkt hpkt).trans (hnm' pkt hpkt)⟩
    | deliver pkt =>
      obtain ⟨hpkt_mem, rfl⟩ := htr
      obtain ⟨hsrcQ, hdestQ⟩ := hactQ
      have hdest_eq := hproc₀ pkt.dest hdestQ
      let res := π.onRecv pkt.src pkt.dest pkt.body (s.proc pkt.dest)
      let u' := applyResult pkt.dest res u₀
      have htr_u : π.lts.Tr u₀ (.deliver pkt) u' := by
        dsimp only [lts]
        rw [hdest_eq]
        exact ⟨hmsgs₀ pkt hsrcQ hpkt_mem, rfl⟩
      obtain ⟨hp', hnp', hm', hnm'⟩ := happly pkt.dest hdestQ res hdest_eq
      obtain ⟨u₁, hmtr₁, hp₁, hnp₁, hnm₁⟩ := ih hrestQ hp' hm'
      exact ⟨u₁, LTS.MTr.stepL htr_u hmtr₁, hp₁,
        fun q hq => (hnp₁ q hq).trans (hnp' q hq),
        fun pkt' hpkt' => (hnm₁ pkt' hpkt').trans (hnm' pkt' hpkt')⟩
    | stutter =>
      obtain rfl := htr
      obtain ⟨u₁, hmtr₁, hp₁, hnp₁, hnm₁⟩ := ih hrestQ hproc₀ hmsgs₀
      exact ⟨u₁, LTS.MTr.stepL rfl hmtr₁, hp₁, hnp₁, hnm₁⟩


end AsyncQuorumProtocol

/-- Original asynchronous partition / split-brain impossibility over `AsyncQuorumProtocol`
(motivating the quorum-intersection condition `B2` of [Lamport1998] §§1.2, 2.1 and [Lamport2001]
§2.2, rather than formalizing a numbered theorem of those papers): over any nontrivial value domain
`[Nontrivial V]`, if subsets `Q₁, Q₂ : Finset P` are disjoint (`Disjoint Q₁ Q₂`), no deterministic
asynchronous message-passing protocol `π` can simultaneously guarantee `SafeConsensus` and
single-quorum progress (`CanDecideIn`) on both `Q₁` and `Q₂`. -/
theorem not_synod_safe_of_disjoint_quorums {P S L M V : Type*}
    [DecidableEq P] [DecidableEq M] [Nontrivial V]
    (π : AsyncQuorumProtocol P S L M V) {Q₁ Q₂ : Finset P} (hdisj : Disjoint Q₁ Q₂) :
    ¬ (π.SafeConsensus ∧ π.CanDecideIn Q₁ ∧ π.CanDecideIn Q₂) := by
  rintro ⟨hsafe, hdec₁, hdec₂⟩
  obtain ⟨v₁, v₂, hne⟩ := exists_pair_ne V
  obtain ⟨xl₁, s₁, hgrp₁, hmtr₁, q₁, hq₁, w₁, hout₁⟩ := hdec₁ v₁
  obtain ⟨xl₂, s₂, hgrp₂, hmtr₂, q₂, hq₂, w₂, hout₂⟩ := hdec₂ v₂
  -- Uniform validity forces `w₁ = v₁` and `w₂ = v₂`:
  have hw₁ : v₁ = w₁ := by
    obtain ⟨_, hval₁⟩ := hsafe (fun _ => v₁) s₁ ⟨xl₁, hmtr₁⟩
    obtain ⟨_, h_eq⟩ := hval₁ q₁ w₁ hout₁
    exact h_eq
  have hw₂ : v₂ = w₂ := by
    obtain ⟨_, hval₂⟩ := hsafe (fun _ => v₂) s₂ ⟨xl₂, hmtr₂⟩
    obtain ⟨_, h_eq⟩ := hval₂ q₂ w₂ hout₂
    exact h_eq
  subst hw₁ hw₂
  -- Replay `xl₁` then `xl₂` from hybrid input `inp p := if p ∈ Q₁ then v₁ else v₂`:
  let inp : P → V := fun p => if p ∈ Q₁ then v₁ else v₂
  obtain ⟨u₁, hmtr_u₁, hp₁, hnp₁, hnm₁⟩ :=
    π.replay_group_mTr hgrp₁ hmtr₁ (u₀ := π.start inp)
      (fun p hp => by simp only [AsyncQuorumProtocol.start, inp, hp, ↓reduceIte])
      (fun _ _ hm => absurd hm (Finset.notMem_empty _))
  obtain ⟨u₂, hmtr_u₂, hp₂, hnp₂, _⟩ :=
    π.replay_group_mTr hgrp₂ hmtr₂ (u₀ := u₁)
      (fun p hpQ₂ => by
        have hp_not_Q₁ : p ∉ Q₁ := Finset.disjoint_right.mp hdisj hpQ₂
        rw [hnp₁ p hp_not_Q₁]
        simp only [AsyncQuorumProtocol.start, inp, hp_not_Q₁, ↓reduceIte])
      (fun _ _ hm => absurd hm (Finset.notMem_empty _))
  have hreach_u₂ : π.Reachable inp u₂ :=
    ⟨xl₁ ++ xl₂, LTS.MTr.comp π.lts hmtr_u₁ hmtr_u₂⟩
  have hq₁_not_Q₂ : q₁ ∉ Q₂ := Finset.disjoint_left.mp hdisj hq₁
  have hu₂_q₁ : (u₂.proc q₁).out = some v₁ := by
    rw [hnp₂ q₁ hq₁_not_Q₂, hp₁ q₁ hq₁, hout₁]
  have hu₂_q₂ : (u₂.proc q₂).out = some v₂ := by
    rw [hp₂ q₂ hq₂, hout₂]
  have heq : v₁ = v₂ := (hsafe inp u₂ hreach_u₂).1 q₁ q₂ v₁ v₂ hu₂_q₁ hu₂_q₂
  exact hne heq

/-- Original split-brain impossibility corollary at `2 ≤ |P| ≤ 2t` over `AsyncQuorumProtocol`: over
any nontrivial value domain `[Nontrivial V]`, when `2 ≤ Fintype.card P ≤ 2 * t`, no
`AsyncQuorumProtocol` can guarantee `SafeConsensus` together with single-quorum progress on every
`(n - t)`-element subset (i.e., progress tolerating `t` process crashes). -/
theorem not_safeSingleQuorum_of_card_le_two_mul {P S L M V : Type*}
    [Fintype P] [DecidableEq P] [DecidableEq M] [Nontrivial V] {t : ℕ}
    (hcard₂ : 2 ≤ Fintype.card P) (hle : Fintype.card P ≤ 2 * t)
    (π : AsyncQuorumProtocol P S L M V) :
    ¬ (π.SafeConsensus ∧ ∀ Q : Finset P, Fintype.card P - t ≤ Q.card → π.CanDecideIn Q) := by
  rintro ⟨hsafe, hprog⟩
  obtain ⟨Q₁, _, hQ₁_card⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset P)) (n := Fintype.card P / 2)
      (by finset_card)
  exact not_synod_safe_of_disjoint_quorums π (Q₁ := Q₁) (Q₂ := Finset.univ \ Q₁)
    (by finset_card) ⟨hsafe, hprog Q₁ (by omega), hprog (Finset.univ \ Q₁) (by finset_card)⟩

end Cslib.Distributed.Paxos
