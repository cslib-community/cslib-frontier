/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Paxos.Basic
public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Mathlib.Order.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Order.Lemmas

/-!
# Crash-Stop Synod Livelock, Conditional Sole-Leader Step, and Split-Brain Impossibility

This module formalizes liveness and quorum-intersection results for the **crash-stop** Single-Decree
Synod model of `CslibFrontier.Computability.Distributed.Paxos.Basic` as intermediate steps towards
[Lamport1998] and [Lamport2001] (and **not** the crash-recovery or timeout-based leader-election
endpoints of those papers), together with an original asynchronous split-brain impossibility
theorem motivating quorum intersection:

1. **Duelling-Proposers Livelock (`exists_duelling_proposers_livelock`):** Crash-free livelock
   witness after the two-proposer scenario of [Lamport2001] §2.4 (and [Lamport1998] §2.4): on
   `Fin 3` acceptors (`t = 1` majority quorums) and `Fin 2` proposers with distinct inputs
   (`inputs 0 ≠ inputs 1`), an explicit crash-free, drop-free, stutter-free infinite execution
   alternates `Phase1a` prepares so each proposer's `Phase2a` accept request is preempted before
   `Phase2b` can fire, preventing any acceptor from voting and any learner from deciding.
2. **Conditional Sole-Leader Progress Step (`paxos_liveness_of_sole_leader_crashStop`):**
   Conditional crash-stop 4-phase progress step towards [Lamport2001] §2.4 and [Lamport1998] §2.1
   Theorem 2 / §2.4 (and **not** a complete leader-election or timeout-based liveness result): from
   any reachable crash-stop Synod state, assuming an already-selected live leader `p` prepares a
   ballot `b = ⟨r, p⟩` strictly exceeding all previously seen or promised ballots (`BallotsBelow`),
   no ballot strictly greater than `b` is subsequently prepared, and ballot-`b` packets among `p`,
   one live quorum `Q ∈ qs.quorums`, and a live learner `l` are delivered without loss, `l` learns
   a decree value across `1a → 1b → 2a → 2b` alongside arbitrary deliveries or drops of older
   ballots `< b` (`exists_sole_leader_execution_crashStop` constructs an explicit 4-phase
   execution). Leader election, NACK `nextBal[q]` ballot-bumping, persistent-storage crash
   recovery, and [Lamport1998] §2.4's real-time hourglass timeout bounds remain open.
3. **Disjoint-Quorum Split-Brain Impossibility (`not_synod_safe_of_disjoint_quorums`):** Original
   asynchronous partition / split-brain impossibility over `AsyncQuorumProtocol` (motivating the
   quorum-intersection condition `B2` of [Lamport1998] §§1.2, 2.1 and [Lamport2001] §2.2, rather
   than formalizing a numbered theorem of those papers): over `[Nontrivial V]`, no deterministic
   asynchronous message-passing protocol guarantees agreement and uniform validity while allowing
   independent single-quorum progress on disjoint subsets `Q₁, Q₂` (`Disjoint Q₁ Q₂`, in particular
   whenever `2 ≤ Fintype.card P ≤ 2 * t`). Conversely, crash-stop `synodQuorumProtocol` satisfies
   both safety and single-quorum progress for every `QuorumSystem P`
   (`synodQuorumProtocol_safeSingleQuorum_crashStop`).

## Main definitions

* `Cslib.Distributed.Paxos.majorityQuorumsFin3`: strict-majority quorum system on `Fin 3` (`t = 1`).
* `Cslib.Distributed.Paxos.Msg.ballot`, `Cslib.Distributed.Paxos.BallotsBelow`,
  `Cslib.Distributed.Paxos.LiveAndLossless`: ballot extractor, fresh-ballot dominance predicate, and
  live cohort / lossless ballot-delivery hypothesis for conditional sole-leader progress.
* `Cslib.Distributed.Paxos.Packet`, `Cslib.Distributed.Paxos.NodeProcState`,
  `Cslib.Distributed.Paxos.NetState`, `Cslib.Distributed.Paxos.NetAction`,
  `Cslib.Distributed.Paxos.AsyncQuorumProtocol`: general asynchronous crash-tolerant message-passing
  protocol model for single-quorum progress analysis.
* `Cslib.Distributed.Paxos.SynodNodeState`, `Cslib.Distributed.Paxos.synodQuorumProtocol`:
  co-located crash-stop Single-Decree Synod instantiated as an `AsyncQuorumProtocol`.

## Main results

* `Cslib.Distributed.Paxos.exists_duelling_proposers_livelock`: explicit crash-free non-terminating
  duelling-proposers execution on `Fin 3` acceptors and `Fin 2` proposers with distinct inputs.
* `Cslib.Distributed.Paxos.paxos_liveness_of_sole_leader_crashStop`: conditional crash-stop 4-phase
  learner termination step under a live sole leader at a fresh highest ballot.
* `Cslib.Distributed.Paxos.exists_sole_leader_execution_crashStop`: constructive 4-phase execution
  witness from any reachable crash-stop state (with `[Finite Acceptor]`).
* `Cslib.Distributed.Paxos.not_synod_safe_of_disjoint_quorums`: split-brain impossibility for any
  `AsyncQuorumProtocol` admitting progress on disjoint subsets `Q₁, Q₂`.
* `Cslib.Distributed.Paxos.not_safeSingleQuorum_of_card_le_two_mul`: impossibility of `t`-crash
  single-quorum progress when `2 ≤ Fintype.card P ≤ 2 * t`.
* `Cslib.Distributed.Paxos.synodQuorumProtocol_safeSingleQuorum_crashStop`: crash-stop step showing
  `synodQuorumProtocol qs` achieves `SafeConsensus` and `CanDecideIn Q` for every `Q ∈ qs.quorums`.

## References

* [L. Lamport, *The Part-Time Parliament*][Lamport1998]
* [L. Lamport, *Paxos Made Simple*][Lamport2001]
-/

public section

namespace Cslib.Distributed.Paxos

open Cslib Cslib.ωSequence

/-! ### Part 1: Duelling-proposers livelock on `Fin 3` -/

/-- Strict-majority quorum system on `Fin 3` tolerating `t = 1` acceptor crash (quorums of size at
least `2`). -/
@[expose] def majorityQuorumsFin3 : QuorumSystem (Fin 3) :=
  majorityQuorums (P := Fin 3) (t := 1) (by decide)

private def duellingInputs {V : Type*} (v₀ v₁ : V) : Fin 2 → V
  | 0 => v₀
  | 1 => v₁

private def duellingCycle {Learner V : Type*} (v₀ : V) (k : ℕ) :
    List (SynodAction (Fin 2) (Fin 3) Learner V) :=
  let b₀ : Ballot (Fin 2) := ⟨k, 0⟩
  let b₁ : Ballot (Fin 2) := ⟨k, 1⟩
  [ .prepare 0 k
  , .recvPhase1a 0 b₀
  , .recvPhase1a 1 b₀
  , .recvPhase1b 0 0 b₀ none
  , .recvPhase1b 0 1 b₀ none
  , .prepare 1 k
  , .recvPhase1a 0 b₁
  , .recvPhase1a 1 b₁
  , .recvPhase2a 0 b₀ v₀
  , .recvPhase1b 1 0 b₁ none
  , .recvPhase1b 1 1 b₁ none ]

private lemma fin3_singleton_zero_not_quorum :
    decide (∃ Q ∈ majorityQuorumsFin3.quorums, Q ⊆ ({0} : Finset (Fin 3))) = false := by
  decide

private lemma fin3_pair_zero_one_has_quorum :
    decide (∃ Q ∈ majorityQuorumsFin3.quorums, Q ⊆ ({0, 1} : Finset (Fin 3))) = true := by
  decide

private structure DuellingBoundary {Learner V : Type*} (v₀ v₁ : V) (k : ℕ)
    (s : SynodState (Fin 2) (Fin 3) Learner V) : Prop where
  p0_in : (s.proposers 0).input = v₀
  p0_live : (s.proposers 0).crashed = false
  p0_round : match (s.proposers 0).round with | none => True | some r => r < k
  p1_in : (s.proposers 1).input = v₁
  p1_live : (s.proposers 1).crashed = false
  p1_round : match (s.proposers 1).round with | none => True | some r => r < k
  a0_live : (s.acceptors 0).crashed = false
  a0_vote : (s.acceptors 0).maxVoted = none
  a0_bal : aboveMaxBal (s.acceptors 0).maxBal ⟨k, 0⟩ = true
  a1_live : (s.acceptors 1).crashed = false
  a1_vote : (s.acceptors 1).maxVoted = none
  a1_bal : aboveMaxBal (s.acceptors 1).maxBal ⟨k, 0⟩ = true
  a2_vote : (s.acceptors 2).maxVoted = none
  learners_empty : ∀ l, (s.learners l).learned = none

private lemma duellingBoundary_init {Learner V : Type*} (v₀ v₁ : V) :
    DuellingBoundary v₀ v₁ 0 (initState (Learner := Learner) (duellingInputs v₀ v₁)) where
  p0_in := rfl
  p0_live := rfl
  p0_round := trivial
  p1_in := rfl
  p1_live := rfl
  p1_round := trivial
  a0_live := rfl
  a0_vote := rfl
  a0_bal := rfl
  a1_live := rfl
  a1_vote := rfl
  a1_bal := rfl
  a2_vote := rfl
  learners_empty _ := rfl

private lemma duelling_prep_and_1a {Learner V : Type*} [DecidableEq Learner] [DecidableEq V]
    (p : Fin 2) (val : V) (k : ℕ) (u : SynodState (Fin 2) (Fin 3) Learner V)
    (hp_in : (u.proposers p).input = val)
    (hp_live : (u.proposers p).crashed = false)
    (hp_round : match (u.proposers p).round with | none => True | some r => r < k)
    (ha0_live : (u.acceptors 0).crashed = false)
    (ha0_vote : (u.acceptors 0).maxVoted = none)
    (ha0_bal : aboveMaxBal (u.acceptors 0).maxBal ⟨k, p⟩ = true)
    (ha1_live : (u.acceptors 1).crashed = false)
    (ha1_vote : (u.acceptors 1).maxVoted = none)
    (ha1_bal : aboveMaxBal (u.acceptors 1).maxBal ⟨k, p⟩ = true) :
    let acts : List (SynodAction (Fin 2) (Fin 3) Learner V) :=
      [.prepare p k, .recvPhase1a 0 ⟨k, p⟩, .recvPhase1a 1 ⟨k, p⟩]
    let u' := acts.foldl (synodStep majorityQuorumsFin3) u
    (synodLts majorityQuorumsFin3).MTr u acts u' ∧
      u'.proposers p =
        { input := val, round := some k, proposed := false, promised := ∅,
          maxVote := none, crashed := false } ∧
      (∀ q, q ≠ p → u'.proposers q = u.proposers q) ∧
      u'.acceptors 0 = { maxBal := some ⟨k, p⟩, maxVoted := none, crashed := false } ∧
      u'.acceptors 1 = { maxBal := some ⟨k, p⟩, maxVoted := none, crashed := false } ∧
      u'.acceptors 2 = u.acceptors 2 ∧
      u'.learners = u.learners ∧
      u.msgs ⊆ u'.msgs ∧
      Msg.phase1a ⟨k, p⟩ ∈ u'.msgs ∧
      Msg.phase1b 0 ⟨k, p⟩ none ∈ u'.msgs ∧
      Msg.phase1b 1 ⟨k, p⟩ none ∈ u'.msgs := by
  let b : Ballot (Fin 2) := ⟨k, p⟩
  set u1 := synodStep majorityQuorumsFin3 u (.prepare p k)
  have hu1_def : u1 =
      { u with
        msgs := insert (.phase1a b) u.msgs
        proposers := fun q => if q = p then
          { input := val, round := some k, proposed := false, promised := ∅,
            maxVote := none, crashed := false } else u.proposers q } := by
    dsimp only [u1, synodStep, synodStepCore]
    congr 1; funext q
    by_cases hqp : q = p <;> simp only [hqp, ↓reduceIte, hp_in, hp_live]
  set u2 := synodStep majorityQuorumsFin3 u1 (.recvPhase1a 0 b)
  have hu2_def : u2 =
      { u1 with
        msgs := insert (.phase1b 0 b none) u1.msgs
        acceptors := fun q => if q = 0 then
          { maxBal := some b, maxVoted := none, crashed := false } else u.acceptors q } := by
    dsimp only [u2, synodStep, synodStepCore]
    have hu1_acc : u1.acceptors = u.acceptors := by rw [hu1_def]
    rw [hu1_acc, ite_eq_left ha0_bal, ha0_vote]
    congr 1; funext q
    by_cases hq0 : q = 0 <;> simp only [hq0, ↓reduceIte, ha0_live]
  set u3 := synodStep majorityQuorumsFin3 u2 (.recvPhase1a 1 b)
  have hu3_def : u3 =
      { u2 with
        msgs := insert (.phase1b 1 b none) u2.msgs
        acceptors := fun q => if q = 1 then
          { maxBal := some b, maxVoted := none, crashed := false } else u2.acceptors q } := by
    dsimp only [u3, synodStep, synodStepCore]
    have hu2_a1 : u2.acceptors 1 = u.acceptors 1 := by rw [hu2_def]; rfl
    rw [hu2_a1, ite_eq_left ha1_bal, ha1_vote]
    congr 1; funext q
    by_cases hq1 : q = 1 <;> simp only [hq1, ↓reduceIte, ha1_live]
  have tr1 : (synodLts majorityQuorumsFin3).Tr u (.prepare p k) u1 := ⟨⟨hp_live, hp_round⟩, rfl⟩
  have tr2 : (synodLts majorityQuorumsFin3).Tr u1 (.recvPhase1a 0 b) u2 :=
    ⟨⟨ha0_live, by rw [hu1_def]; exact Finset.mem_insert_self _ _⟩, rfl⟩
  have tr3 : (synodLts majorityQuorumsFin3).Tr u2 (.recvPhase1a 1 b) u3 :=
    ⟨⟨by rw [hu2_def]; exact ha1_live,
      by rw [hu2_def, hu1_def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩, rfl⟩
  have hu3_eq : ([SynodAction.prepare p k, .recvPhase1a 0 b, .recvPhase1a 1 b] :
      List (SynodAction (Fin 2) (Fin 3) Learner V)).foldl (synodStep majorityQuorumsFin3) u = u3 :=
    rfl
  dsimp only []
  rw [hu3_eq]
  refine ⟨LTS.MTr.stepL tr1 (LTS.MTr.stepL tr2 (LTS.MTr.stepL tr3 LTS.MTr.refl)), ?_⟩
  rw [hu3_def, hu2_def, hu1_def]
  exact ⟨by simp only [↓reduceIte],
    fun q hqp => by simp only [hqp, ↓reduceIte],
    rfl, rfl, rfl, rfl,
    fun _ hm => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm)),
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
    Finset.mem_insert_self _ _⟩

private lemma duelling_recv_two_1b {Learner V : Type*} [DecidableEq Learner] [DecidableEq V]
    (p : Fin 2) (val : V) (k : ℕ) (u : SynodState (Fin 2) (Fin 3) Learner V)
    (hp : u.proposers p =
      { input := val, round := some k, proposed := false, promised := ∅,
        maxVote := none, crashed := false })
    (h1b0 : Msg.phase1b 0 ⟨k, p⟩ none ∈ u.msgs)
    (h1b1 : Msg.phase1b 1 ⟨k, p⟩ none ∈ u.msgs) :
    let acts : List (SynodAction (Fin 2) (Fin 3) Learner V) :=
      [.recvPhase1b p 0 ⟨k, p⟩ none, .recvPhase1b p 1 ⟨k, p⟩ none]
    let u' := acts.foldl (synodStep majorityQuorumsFin3) u
    (synodLts majorityQuorumsFin3).MTr u acts u' ∧
      ((u'.proposers p).input = val ∧ (u'.proposers p).crashed = false ∧
        (u'.proposers p).round = some k) ∧
      (∀ q, q ≠ p → u'.proposers q = u.proposers q) ∧
      u'.acceptors = u.acceptors ∧
      u'.learners = u.learners ∧
      u.msgs ⊆ u'.msgs ∧
      Msg.phase2a ⟨k, p⟩ val ∈ u'.msgs := by
  let b : Ballot (Fin 2) := ⟨k, p⟩
  have hins0 : insert (0 : Fin 3) (∅ : Finset (Fin 3)) = {0} := by decide
  have hins01 : insert (1 : Fin 3) ({0} : Finset (Fin 3)) = {0, 1} := by decide
  have hcond0 : b = ⟨k, p⟩ ∧ (0 : Fin 3) ∉ (∅ : Finset (Fin 3)) := ⟨rfl, Finset.notMem_empty 0⟩
  have hcond1 : b = ⟨k, p⟩ ∧ (1 : Fin 3) ∉ ({0} : Finset (Fin 3)) := ⟨rfl, by decide⟩
  set u1 := synodStep majorityQuorumsFin3 u (.recvPhase1b p 0 b none)
  have hu1_def : u1 =
      { u with
        proposers := fun q => if q = p then
          { input := val, round := some k, proposed := false, promised := {0},
            maxVote := none, crashed := false } else u.proposers q } := by
    dsimp only [u1, synodStep, synodStepCore]
    rw [hp]
    dsimp only [mergeVote]
    rw [ite_eq_left hcond0, hins0, fin3_singleton_zero_not_quorum]
    rfl
  set u2 := synodStep majorityQuorumsFin3 u1 (.recvPhase1b p 1 b none)
  have hu2_def : u2 =
      { u with
        msgs := insert (.phase2a b val) u.msgs
        proposers := fun q => if q = p then
          { input := val, round := some k, proposed := true, promised := {0, 1},
            maxVote := none, crashed := false } else u.proposers q } := by
    have hu1_p : u1.proposers p =
        { input := val, round := some k, proposed := false, promised := {0},
          maxVote := none, crashed := false } := by rw [hu1_def]; simp only [↓reduceIte]
    dsimp only [u2, synodStep, synodStepCore]
    rw [hu1_p]
    dsimp only [mergeVote]
    rw [ite_eq_left hcond1, hins01, fin3_pair_zero_one_has_quorum]
    simp only [Bool.not_false, Bool.true_and, ↓reduceIte, hu1_def]
    congr 1; funext q
    by_cases hqp : q = p <;> simp only [hqp, ↓reduceIte]
  have tr1 : (synodLts majorityQuorumsFin3).Tr u (.recvPhase1b p 0 b none) u1 :=
    ⟨⟨by rw [hp], h1b0⟩, rfl⟩
  have tr2 : (synodLts majorityQuorumsFin3).Tr u1 (.recvPhase1b p 1 b none) u2 :=
    ⟨⟨by rw [hu1_def]; simp only [↓reduceIte], by rw [hu1_def]; exact h1b1⟩, rfl⟩
  have hu2_eq : ([SynodAction.recvPhase1b p 0 b none, .recvPhase1b p 1 b none] :
      List (SynodAction (Fin 2) (Fin 3) Learner V)).foldl (synodStep majorityQuorumsFin3) u = u2 :=
    rfl
  dsimp only []
  rw [hu2_eq]
  refine ⟨LTS.MTr.stepL tr1 (LTS.MTr.stepL tr2 LTS.MTr.refl), ?_⟩
  rw [hu2_def]
  exact ⟨by dsimp only []; rw [ite_eq_left rfl]; exact ⟨rfl, rfl, rfl⟩,
    fun q hqp => ite_eq_right hqp,
    rfl, rfl, Finset.subset_insert _ _, Finset.mem_insert_self _ _⟩

private lemma duellingCycle_step {Learner V : Type*} [DecidableEq Learner] [DecidableEq V]
    (v₀ v₁ : V) (k : ℕ) (s : SynodState (Fin 2) (Fin 3) Learner V)
    (hb : DuellingBoundary v₀ v₁ k s) :
    let s' := (duellingCycle (Learner := Learner) v₀ k).foldl
      (synodStep majorityQuorumsFin3) s
    (synodLts majorityQuorumsFin3).MTr s (duellingCycle v₀ k) s' ∧
      DuellingBoundary v₀ v₁ (k + 1) s' ∧
      Msg.phase1a ⟨k, 0⟩ ∈ s'.msgs ∧
      Msg.phase1a ⟨k, 1⟩ ∈ s'.msgs ∧
      Msg.phase2a ⟨k, 0⟩ v₀ ∈ s'.msgs ∧
      Msg.phase2a ⟨k, 1⟩ v₁ ∈ s'.msgs := by
  let b₀ : Ballot (Fin 2) := ⟨k, 0⟩
  let b₁ : Ballot (Fin 2) := ⟨k, 1⟩
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hb₀₁ : aboveMaxBal (some b₀) b₁ = true := by
    simp only [aboveMaxBal, decide_eq_true_eq, Ballot.lt_iff, b₀, b₁]
    exact Or.inr ⟨trivial, by decide⟩
  have hallows_false : allowsVote (some b₁) b₀ = false := by
    simp only [allowsVote, decide_eq_false_iff_not, Ballot.le_iff, b₀, b₁]
    rintro (hlt | ⟨_, hle⟩)
    · exact Nat.lt_irrefl k hlt
    · exact absurd hle (by decide)
  have hb₁_next : aboveMaxBal (some b₁) ⟨k + 1, 0⟩ = true := by
    simp only [aboveMaxBal, decide_eq_true_eq, Ballot.lt_iff, b₁]
    exact Or.inl (Nat.lt_succ_self k)
  obtain ⟨mtr1, hs3_p0, hs3_po, hs3_a0, hs3_a1, hs3_a2, hs3_l, _, hs3_1a0, hs3_1b0, hs3_1b1⟩ :=
    duelling_prep_and_1a 0 v₀ k s hb.p0_in hb.p0_live hb.p0_round
      hb.a0_live hb.a0_vote hb.a0_bal hb.a1_live hb.a1_vote hb.a1_bal
  set s3 := ([SynodAction.prepare 0 k, .recvPhase1a 0 b₀, .recvPhase1a 1 b₀] :
    List (SynodAction (Fin 2) (Fin 3) Learner V)).foldl (synodStep majorityQuorumsFin3) s
  obtain ⟨mtr2, hs5_p0, hs5_po, hs5_acc, hs5_l, hs5_sub, hs5_2a0⟩ :=
    duelling_recv_two_1b 0 v₀ k s3 hs3_p0 hs3_1b0 hs3_1b1
  set s5 := ([SynodAction.recvPhase1b 0 0 b₀ none, .recvPhase1b 0 1 b₀ none] :
    List (SynodAction (Fin 2) (Fin 3) Learner V)).foldl (synodStep majorityQuorumsFin3) s3
  have hs5_p1 : s5.proposers 1 = s.proposers 1 := (hs5_po 1 h10).trans (hs3_po 1 h10)
  have hs5_a0 : s5.acceptors 0 = { maxBal := some b₀, maxVoted := none, crashed := false } := by
    rw [hs5_acc, hs3_a0]
  have hs5_a1 : s5.acceptors 1 = { maxBal := some b₀, maxVoted := none, crashed := false } := by
    rw [hs5_acc, hs3_a1]
  obtain ⟨mtr3, hs8_p1, hs8_po, hs8_a0, hs8_a1, hs8_a2, hs8_l, hs8_sub, hs8_1a1, hs8_1b0,
      hs8_1b1⟩ :=
    duelling_prep_and_1a 1 v₁ k s5
      (hs5_p1 ▸ hb.p1_in) (hs5_p1 ▸ hb.p1_live) (hs5_p1 ▸ hb.p1_round)
      (by rw [hs5_a0]) (by rw [hs5_a0]) (by rw [hs5_a0]; exact hb₀₁)
      (by rw [hs5_a1]) (by rw [hs5_a1]) (by rw [hs5_a1]; exact hb₀₁)
  set s8 := ([SynodAction.prepare 1 k, .recvPhase1a 0 b₁, .recvPhase1a 1 b₁] :
    List (SynodAction (Fin 2) (Fin 3) Learner V)).foldl (synodStep majorityQuorumsFin3) s5
  set s9 := synodStep majorityQuorumsFin3 s8 (.recvPhase2a 0 b₀ v₀)
  have tr9 : (synodLts majorityQuorumsFin3).Tr s8 (.recvPhase2a 0 b₀ v₀) s9 :=
    ⟨⟨by rw [hs8_a0], hs8_sub hs5_2a0⟩, rfl⟩
  have hs9_eq : s9 = s8 := by
    dsimp only [s9, synodStep, synodStepCore]
    rw [hs8_a0, hallows_false]
    rfl
  obtain ⟨mtr5, hs11_p1, hs11_po, hs11_acc, hs11_l, hs11_sub, hs11_2a1⟩ :=
    duelling_recv_two_1b 1 v₁ k s9 (hs9_eq ▸ hs8_p1) (hs9_eq ▸ hs8_1b0) (hs9_eq ▸ hs8_1b1)
  set s11 := ([SynodAction.recvPhase1b 1 0 b₁ none, .recvPhase1b 1 1 b₁ none] :
    List (SynodAction (Fin 2) (Fin 3) Learner V)).foldl (synodStep majorityQuorumsFin3) s9
  have hmTr : (synodLts majorityQuorumsFin3).MTr s (duellingCycle v₀ k) s11 := by
    have heq_acts : duellingCycle (Learner := Learner) v₀ k =
        [.prepare 0 k, .recvPhase1a 0 b₀, .recvPhase1a 1 b₀] ++
          [.recvPhase1b 0 0 b₀ none, .recvPhase1b 0 1 b₀ none] ++
          [.prepare 1 k, .recvPhase1a 0 b₁, .recvPhase1a 1 b₁] ++
          [.recvPhase2a 0 b₀ v₀] ++
          [.recvPhase1b 1 0 b₁ none, .recvPhase1b 1 1 b₁ none] := rfl
    rw [heq_acts]
    exact LTS.MTr.comp _
      (LTS.MTr.comp _
        (LTS.MTr.comp _ (LTS.MTr.comp _ mtr1 mtr2) mtr3)
        (LTS.MTr.single _ tr9))
      mtr5
  have hs11_p0 : s11.proposers 0 = s5.proposers 0 :=
    (hs11_po 0 h01).trans ((congrArg (fun u => u.proposers 0) hs9_eq).trans (hs8_po 0 h01))
  have hs11_acc8 : s11.acceptors = s8.acceptors :=
    hs11_acc.trans (congrArg SynodState.acceptors hs9_eq)
  have hs11_l0 : s11.learners = s.learners :=
    hs11_l.trans ((congrArg SynodState.learners hs9_eq).trans (hs8_l.trans (hs5_l.trans hs3_l)))
  have hs11_a2 : (s11.acceptors 2).maxVoted = none := by
    rw [hs11_acc8, hs8_a2, hs5_acc, hs3_a2]
    exact hb.a2_vote
  have hs11_eq : (duellingCycle (Learner := Learner) v₀ k).foldl
      (synodStep majorityQuorumsFin3) s = s11 := rfl
  dsimp only []
  rw [hs11_eq]
  refine ⟨hmTr, ?_,
    hs11_sub (hs9_eq ▸ hs8_sub (hs5_sub hs3_1a0)),
    hs11_sub (hs9_eq ▸ hs8_1a1),
    hs11_sub (hs9_eq ▸ hs8_sub hs5_2a0),
    hs11_2a1⟩
  exact
    { p0_in := hs11_p0 ▸ hs5_p0.1
      p0_live := hs11_p0 ▸ hs5_p0.2.1
      p0_round := by rw [hs11_p0, hs5_p0.2.2]; exact Nat.lt_succ_self k
      p1_in := hs11_p1.1
      p1_live := hs11_p1.2.1
      p1_round := by rw [hs11_p1.2.2]; exact Nat.lt_succ_self k
      a0_live := by rw [hs11_acc8, hs8_a0]
      a0_vote := by rw [hs11_acc8, hs8_a0]
      a0_bal := by rw [hs11_acc8, hs8_a0]; exact hb₁_next
      a1_live := by rw [hs11_acc8, hs8_a1]
      a1_vote := by rw [hs11_acc8, hs8_a1]
      a1_bal := by rw [hs11_acc8, hs8_a1]; exact hb₁_next
      a2_vote := hs11_a2
      learners_empty := fun l => by rw [hs11_l0]; exact hb.learners_empty l }

private def duellingStateSeq {Learner V : Type*} [DecidableEq Learner] [DecidableEq V]
    (v₀ v₁ : V) : ℕ → SynodState (Fin 2) (Fin 3) Learner V
  | 0 => initState (duellingInputs v₀ v₁)
  | k + 1 => (duellingCycle v₀ k).foldl
      (synodStep majorityQuorumsFin3) (duellingStateSeq v₀ v₁ k)

private lemma duellingStateSeq_inv {Learner V : Type*} [DecidableEq Learner] [DecidableEq V]
    (v₀ v₁ : V) (k : ℕ) :
    DuellingBoundary v₀ v₁ k (duellingStateSeq (Learner := Learner) v₀ v₁ k) := by
  induction k with
  | zero => exact duellingBoundary_init v₀ v₁
  | succ k ih => exact (duellingCycle_step v₀ v₁ k _ ih).2.1

private lemma mem_msgs_synodStep_of_mem {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    {qs : QuorumSystem Acceptor} {s : SynodState Proposer Acceptor Learner V}
    {act : SynodAction Proposer Acceptor Learner V} {m : Msg Proposer Acceptor V}
    (hm : m ∈ s.msgs) (hne : act ≠ .drop m) :
    m ∈ (synodStep qs s act).msgs := by
  cases act with
  | prepare _ _ => exact Finset.mem_insert_of_mem hm
  | recvPhase1a _ _ | recvPhase2a _ _ _ =>
    dsimp only [synodStep, synodStepCore]
    split_ifs
    · exact Finset.mem_insert_of_mem hm
    · exact hm
  | recvPhase1b p _ _ _ =>
    dsimp only [synodStep, synodStepCore]
    cases (s.proposers p).round with
    | none => exact hm
    | some _ =>
      dsimp only []
      split_ifs
      · exact Finset.mem_insert_of_mem hm
      · exact hm
      · exact hm
  | drop m' =>
    exact Finset.mem_erase.mpr ⟨fun heq => hne (heq ▸ rfl), hm⟩
  | _ => exact hm

private lemma mem_msgs_synodStep_cases {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    {qs : QuorumSystem Acceptor} {s : SynodState Proposer Acceptor Learner V}
    {act : SynodAction Proposer Acceptor Learner V} {m : Msg Proposer Acceptor V}
    (hm : m ∈ (synodStep qs s act).msgs) :
    m ∈ s.msgs ∨
      (∃ p r, act = .prepare p r ∧ m = .phase1a ⟨r, p⟩) ∨
      (∃ a b, act = .recvPhase1a a b ∧ aboveMaxBal (s.acceptors a).maxBal b = true ∧
        m = .phase1b a b (s.acceptors a).maxVoted) ∨
      (∃ p a b mv r val, act = .recvPhase1b p a b mv ∧ (s.proposers p).round = some r ∧
        b = ⟨r, p⟩ ∧ ((synodStep qs s act).proposers p).proposed = true ∧
        m = .phase2a ⟨r, p⟩ val) ∨
      (∃ a b v, act = .recvPhase2a a b v ∧ allowsVote (s.acceptors a).maxBal b = true ∧
        m = .phase2b a b v) := by
  cases act with
  | prepare p r =>
    rcases Finset.mem_insert.mp hm with rfl | hold
    · exact Or.inr (Or.inl ⟨p, r, rfl, rfl⟩)
    · exact Or.inl hold
  | recvPhase1a a b =>
    dsimp only [synodStep, synodStepCore] at hm
    split_ifs at hm with hab
    · rcases Finset.mem_insert.mp hm with rfl | hold
      · exact Or.inr (Or.inr (Or.inl ⟨a, b, rfl, hab, rfl⟩))
      · exact Or.inl hold
    · exact Or.inl hm
  | recvPhase1b p a b mv =>
    dsimp only [synodStep, synodStepCore] at hm ⊢
    cases hround : (s.proposers p).round with
    | none => rw [hround] at hm; exact Or.inl hm
    | some r =>
      rw [hround] at hm
      dsimp only [] at hm ⊢
      split_ifs at hm with hg hq
      · rcases Finset.mem_insert.mp hm with rfl | hold
        · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨p, a, b, mv, r, _, rfl, hround, hg.1, ?_, rfl⟩)))
          rw [ite_eq_left hg, ite_eq_left hq]
          simp only [↓reduceIte]
        · exact Or.inl hold
      · exact Or.inl hm
      · exact Or.inl hm
  | recvPhase2a a b v =>
    dsimp only [synodStep, synodStepCore] at hm
    split_ifs at hm with hal
    · rcases Finset.mem_insert.mp hm with rfl | hold
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, v, rfl, hal, rfl⟩)))
      · exact Or.inl hold
    · exact Or.inl hm
  | drop _ => exact Or.inl (Finset.mem_of_mem_erase hm)
  | _ => exact Or.inl hm

private lemma proposers_synodStep_cases {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    (qs : QuorumSystem Acceptor) (s : SynodState Proposer Acceptor Learner V)
    (act : SynodAction Proposer Acceptor Learner V) (p : Proposer) :
    (synodStep qs s act).proposers p = s.proposers p ∨
      (∃ r, act = .prepare p r ∧
        (synodStep qs s act).proposers p =
          { s.proposers p with
            round := some r, proposed := false, promised := ∅, maxVote := none }) ∨
      (∃ a b mv r val, act = .recvPhase1b p a b mv ∧ (s.proposers p).round = some r ∧
        b = ⟨r, p⟩ ∧ a ∉ (s.proposers p).promised ∧
        (!(s.proposers p).proposed &&
          decide (∃ Q ∈ qs.quorums, Q ⊆ insert a (s.proposers p).promised)) = true ∧
        (synodStep qs s act).proposers p =
          { s.proposers p with
            proposed := true
            promised := insert a (s.proposers p).promised
            maxVote := mergeVote (s.proposers p).maxVote mv } ∧
        Msg.phase2a ⟨r, p⟩ val ∈ (synodStep qs s act).msgs) ∨
      (∃ a b mv r, act = .recvPhase1b p a b mv ∧ (s.proposers p).round = some r ∧
        b = ⟨r, p⟩ ∧ a ∉ (s.proposers p).promised ∧
        ¬ ((!(s.proposers p).proposed &&
          decide (∃ Q ∈ qs.quorums, Q ⊆ insert a (s.proposers p).promised)) = true) ∧
        (synodStep qs s act).proposers p =
          { s.proposers p with
            promised := insert a (s.proposers p).promised
            maxVote := mergeVote (s.proposers p).maxVote mv }) ∨
      (act = .crashProposer p ∧
        (synodStep qs s act).proposers p = { s.proposers p with crashed := true }) := by
  cases act with
  | prepare q r =>
    dsimp only [synodStep, synodStepCore]
    rcases eq_or_ne p q with rfl | hpq
    · exact Or.inr (Or.inl ⟨r, rfl, ite_eq_left rfl⟩)
    · exact Or.inl (ite_eq_right hpq)
  | recvPhase1a _ _ | recvPhase2a _ _ _ =>
    dsimp only [synodStep, synodStepCore]
    split_ifs <;> exact Or.inl rfl
  | recvPhase1b q a b mv =>
    dsimp only [synodStep, synodStepCore]
    rcases eq_or_ne q p with rfl | hqp
    · cases hround : (s.proposers q).round with
      | none => exact Or.inl rfl
      | some r =>
        dsimp only []
        by_cases hg : b = ⟨r, q⟩ ∧ a ∉ (s.proposers q).promised
        · rw [ite_eq_left hg]
          by_cases hq_cond : (!(s.proposers q).proposed &&
              decide (∃ Q ∈ qs.quorums, Q ⊆ insert a (s.proposers q).promised)) = true
          · rw [ite_eq_left hq_cond]
            exact Or.inr (Or.inr (Or.inl
              ⟨a, b, mv, r, _, rfl, rfl, hg.1, hg.2, hq_cond, ite_eq_left rfl,
                Finset.mem_insert_self _ _⟩))
          · rw [ite_eq_right hq_cond]
            exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨a, b, mv, r, rfl, rfl, hg.1, hg.2, hq_cond, ite_eq_left rfl⟩)))
        · rw [ite_eq_right hg]; exact Or.inl rfl
    · cases (s.proposers q).round with
      | none => exact Or.inl rfl
      | some _ =>
        dsimp only []
        split_ifs
        · exact Or.inl (ite_eq_right (Ne.symm hqp))
        · exact Or.inl (ite_eq_right (Ne.symm hqp))
        · exact Or.inl rfl
  | crashProposer q =>
    dsimp only [synodStep, synodStepCore]
    rcases eq_or_ne p q with rfl | hpq
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ite_eq_left rfl⟩)))
    · exact Or.inl (ite_eq_right hpq)
  | _ => exact Or.inl rfl

private lemma acceptors_synodStep_cases {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    (qs : QuorumSystem Acceptor) (s : SynodState Proposer Acceptor Learner V)
    (act : SynodAction Proposer Acceptor Learner V) (a : Acceptor) :
    (synodStep qs s act).acceptors a = s.acceptors a ∨
      (∃ b, act = .recvPhase1a a b ∧ aboveMaxBal (s.acceptors a).maxBal b = true ∧
        (synodStep qs s act).acceptors a = { s.acceptors a with maxBal := some b } ∧
        Msg.phase1b a b (s.acceptors a).maxVoted ∈ (synodStep qs s act).msgs) ∨
      (∃ b v, act = .recvPhase2a a b v ∧ allowsVote (s.acceptors a).maxBal b = true ∧
        (synodStep qs s act).acceptors a =
          { s.acceptors a with maxBal := some b, maxVoted := some ⟨b, v⟩ }) ∨
      (act = .crashAcceptor a ∧
        (synodStep qs s act).acceptors a = { s.acceptors a with crashed := true }) := by
  cases act with
  | recvPhase1a a' b =>
    dsimp only [synodStep, synodStepCore]
    by_cases hab : aboveMaxBal (s.acceptors a').maxBal b = true
    · rw [ite_eq_left hab]
      rcases eq_or_ne a a' with rfl | haa
      · exact Or.inr (Or.inl ⟨b, rfl, hab, ite_eq_left rfl, Finset.mem_insert_self _ _⟩)
      · exact Or.inl (ite_eq_right haa)
    · rw [ite_eq_right hab]; exact Or.inl rfl
  | recvPhase1b q _ _ _ =>
    dsimp only [synodStep, synodStepCore]; cases (s.proposers q).round
    · exact Or.inl rfl
    · dsimp only []; split_ifs <;> exact Or.inl rfl
  | recvPhase2a a' b v =>
    dsimp only [synodStep, synodStepCore]
    by_cases hal : allowsVote (s.acceptors a').maxBal b = true
    · rw [ite_eq_left hal]
      rcases eq_or_ne a a' with rfl | haa
      · exact Or.inr (Or.inr (Or.inl ⟨b, v, rfl, hal, ite_eq_left rfl⟩))
      · exact Or.inl (ite_eq_right haa)
    · rw [ite_eq_right hal]; exact Or.inl rfl
  | crashAcceptor a' =>
    dsimp only [synodStep, synodStepCore]
    rcases eq_or_ne a a' with rfl | haa
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, ite_eq_left rfl⟩))
    · exact Or.inl (ite_eq_right haa)
  | _ => exact Or.inl rfl

private lemma learners_synodStep_cases {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    (qs : QuorumSystem Acceptor) (s : SynodState Proposer Acceptor Learner V)
    (act : SynodAction Proposer Acceptor Learner V) (l : Learner) :
    (synodStep qs s act).learners l = s.learners l ∨
      (∃ a b v, act = .recvPhase2b l a b v ∧
        (synodStep qs s act).learners l =
          { s.learners l with
            received := insert ⟨a, b, v⟩ (s.learners l).received
            learned :=
              if (s.learners l).learned.isNone &&
                  decide (∃ Q ∈ qs.quorums, ∀ a' ∈ Q,
                    ⟨a', b, v⟩ ∈ insert ⟨a, b, v⟩ (s.learners l).received) then
                some v
              else (s.learners l).learned }) ∨
      (act = .crashLearner l ∧
        (synodStep qs s act).learners l = { s.learners l with crashed := true }) := by
  cases act with
  | recvPhase1a _ _ | recvPhase2a _ _ _ =>
    dsimp only [synodStep, synodStepCore]; split_ifs <;> exact Or.inl rfl
  | recvPhase1b q _ _ _ =>
    dsimp only [synodStep, synodStepCore]; cases (s.proposers q).round
    · exact Or.inl rfl
    · dsimp only []; split_ifs <;> exact Or.inl rfl
  | recvPhase2b l₀ a b v =>
    dsimp only [synodStep, synodStepCore]
    rcases eq_or_ne l l₀ with rfl | hll
    · exact Or.inr (Or.inl ⟨a, b, v, rfl, ite_eq_left rfl⟩)
    · exact Or.inl (ite_eq_right hll)
  | crashLearner l₀ =>
    dsimp only [synodStep, synodStepCore]
    rcases eq_or_ne l l₀ with rfl | hll
    · exact Or.inr (Or.inr ⟨rfl, ite_eq_left rfl⟩)
    · exact Or.inl (ite_eq_right hll)
  | _ => exact Or.inl rfl

private lemma maxVoted_none_of_mTr {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    {qs : QuorumSystem Acceptor} {s₁ s₂ : SynodState Proposer Acceptor Learner V}
    {xl : List (SynodAction Proposer Acceptor Learner V)}
    (hmtr : (synodLts qs).MTr s₁ xl s₂) {a : Acceptor}
    (h₂ : (s₂.acceptors a).maxVoted = none) :
    (s₁.acceptors a).maxVoted = none := by
  have htr_inv : (synodLts qs (Proposer := Proposer) (Learner := Learner) (V := V)).TrInv
      (fun u => (u.acceptors a).maxVoted ≠ none) := by
    rintro u₁ act _ ⟨_, rfl⟩ hne
    rcases acceptors_synodStep_cases qs u₁ act a with heq | ⟨_, _, _, heq, _⟩ |
        ⟨_, _, _, _, heq⟩ | ⟨_, heq⟩ <;> rw [heq]
    · exact hne
    · exact hne
    · exact nofun
    · exact hne
  by_contra h₁
  exact LTS.mtrInv_of_trInv htr_inv _ _ _ hmtr h₁ h₂

private lemma learned_none_of_mTr {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    {qs : QuorumSystem Acceptor} {s₁ s₂ : SynodState Proposer Acceptor Learner V}
    {xl : List (SynodAction Proposer Acceptor Learner V)}
    (hmtr : (synodLts qs).MTr s₁ xl s₂) {l : Learner}
    (h₂ : (s₂.learners l).learned = none) :
    (s₁.learners l).learned = none := by
  have htr_inv : (synodLts qs (Proposer := Proposer) (Learner := Learner) (V := V)).TrInv
      (fun u => (u.learners l).learned ≠ none) := by
    rintro u₁ act _ ⟨_, rfl⟩ hne
    rcases learners_synodStep_cases qs u₁ act l with heq | ⟨_, _, _, _, heq⟩ | ⟨_, heq⟩ <;>
      rw [heq]
    · exact hne
    · cases hcur : (u₁.learners l).learned with
      | none => exact absurd hcur hne
      | some _ => exact nofun
    · exact hne
  by_contra h₁
  exact LTS.mtrInv_of_trInv htr_inv _ _ _ hmtr h₁ h₂

/-- Crash-free livelock witness after the two-proposer scenario of [Lamport2001] §2.4 and
[Lamport1998] §2.4 in the crash-stop Single-Decree Synod model (not a cited theorem endpoint): over
any nontrivial value domain `[Nontrivial V]`, `synodLts` on `Fin 3` acceptors
(`majorityQuorumsFin3`) and `Fin 2` proposers admits an explicit crash-free, drop-free,
stutter-free infinite execution with distinct proposer inputs (`inputs 0 ≠ inputs 1`) in which both
proposers prepare and propose in every round `k : ℕ`, yet alternating `Phase1a` prepares
perpetually preempt `Phase2b` so no acceptor ever votes and no learner ever decides. -/
theorem exists_duelling_proposers_livelock {Learner V : Type*}
    [DecidableEq Learner] [DecidableEq V] [Nontrivial V] :
    ∃ (inputs : Fin 2 → V) (ss : ωSequence (SynodState (Fin 2) (Fin 3) Learner V))
      (xs : ωSequence (SynodAction (Fin 2) (Fin 3) Learner V)),
      inputs 0 ≠ inputs 1 ∧
      ss 0 = initState inputs ∧
      (synodLts majorityQuorumsFin3).OmegaExecution ss xs ∧
      (∀ n, xs n ≠ .stutter ∧ (∀ m, xs n ≠ .drop m)) ∧
      (∀ k, ∃ n, Msg.phase1a ⟨k, 0⟩ ∈ (ss n).msgs ∧
        Msg.phase1a ⟨k, 1⟩ ∈ (ss n).msgs ∧
        Msg.phase2a ⟨k, 0⟩ (inputs 0) ∈ (ss n).msgs ∧
        Msg.phase2a ⟨k, 1⟩ (inputs 1) ∈ (ss n).msgs) ∧
      (∀ n a, ((ss n).acceptors a).maxVoted = none) ∧
      (∀ n l, ((ss n).learners l).learned = none) := by
  obtain ⟨v₀, v₁, hne⟩ := exists_pair_ne V
  let inputs := duellingInputs v₀ v₁
  let ts : ωSequence (SynodState (Fin 2) (Fin 3) Learner V) :=
    ωSequence.mk (duellingStateSeq v₀ v₁)
  let xls : ωSequence (List (SynodAction (Fin 2) (Fin 3) Learner V)) :=
    ωSequence.mk (duellingCycle v₀)
  have hstep : ∀ k,
      (synodLts majorityQuorumsFin3).MTr (ts k) (xls k) (ts (k + 1)) ∧
      Msg.phase1a ⟨k, 0⟩ ∈ (ts (k + 1)).msgs ∧
      Msg.phase1a ⟨k, 1⟩ ∈ (ts (k + 1)).msgs ∧
      Msg.phase2a ⟨k, 0⟩ v₀ ∈ (ts (k + 1)).msgs ∧
      Msg.phase2a ⟨k, 1⟩ v₁ ∈ (ts (k + 1)).msgs := by
    intro k
    have hc := duellingCycle_step (Learner := Learner) v₀ v₁ k (ts k)
      (duellingStateSeq_inv v₀ v₁ k)
    exact ⟨hc.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2⟩
  have hpos : ∀ k, 0 < (xls k).length := fun k => by
    simp only [xls, get_fun, duellingCycle, List.length_cons, List.length_nil]
    omega
  have : Inhabited (SynodAction (Fin 2) (Fin 3) Learner V) := ⟨.stutter⟩
  obtain ⟨ss, hexec, hts⟩ := LTS.OmegaExecution.flatten_mTr (fun k => (hstep k).1) hpos
  refine ⟨inputs, ss, xls.flatten, hne, ?_, hexec, ?_, ?_, ?_, ?_⟩
  · have h0 := hts 0
    simpa only [cumLen_zero, ts, get_fun, duellingStateSeq, inputs] using h0
  · refine (forall_flatten_iff hpos
      (fun act : SynodAction (Fin 2) (Fin 3) Learner V =>
        act ≠ .stutter ∧ ∀ m, act ≠ .drop m)).mpr ?_
    intro k
    apply List.forall_iff_forall_mem.mpr
    intro act hact
    simp only [xls, get_fun, duellingCycle, List.mem_cons, List.not_mem_nil, or_false] at hact
    rcases hact with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨nofun, nofun⟩
  · intro k
    refine ⟨xls.cumLen (k + 1), ?_⟩
    rw [hts (k + 1)]
    exact (hstep k).2
  · intro n a
    have hle : n ≤ xls.cumLen n := (cumLen_strictMono hpos).id_le n
    have hmtr := hexec.extract_mTr hle
    have hinv_cum := duellingStateSeq_inv (Learner := Learner) v₀ v₁ n
    have hnone_cum : ((ss (xls.cumLen n)).acceptors a).maxVoted = none := by
      rw [hts n]
      match a with
      | ⟨0, _⟩ => exact hinv_cum.a0_vote
      | ⟨1, _⟩ => exact hinv_cum.a1_vote
      | ⟨2, _⟩ => exact hinv_cum.a2_vote
    exact maxVoted_none_of_mTr hmtr hnone_cum
  · intro n l
    have hle : n ≤ xls.cumLen n := (cumLen_strictMono hpos).id_le n
    have hmtr := hexec.extract_mTr hle
    have hnone_cum : ((ss (xls.cumLen n)).learners l).learned = none := by
      rw [hts n]
      exact (duellingStateSeq_inv (Learner := Learner) v₀ v₁ n).learners_empty l
    exact learned_none_of_mTr hmtr hnone_cum

/-! ### Part 2: Single-distinguished-leader 4-phase liveness -/

/-- Extract the ballot number carried by any Synod packet. -/
@[expose] def Msg.ballot {Proposer Acceptor V : Type*} :
    Msg Proposer Acceptor V → Ballot Proposer
  | .phase1a b => b
  | .phase1b _ b _ => b
  | .phase2a b _ => b
  | .phase2b _ b _ => b

/-- Every ballot present in `s.msgs` or promised in any acceptor's `maxBal` is strictly below
`b`. -/
@[expose] def BallotsBelow {Proposer Acceptor Learner V : Type*} [LinearOrder Proposer]
    (s : SynodState Proposer Acceptor Learner V) (b : Ballot Proposer) : Prop :=
  (∀ m ∈ s.msgs, m.ballot < b) ∧
    ∀ a mb, (s.acceptors a).maxBal = some mb → mb < b

/-- Live cohort and lossless eventual delivery for ballot `b` among leader `p`, quorum `Q`, and
learner `l` along infinite execution `(ss, xs)`. -/
structure LiveAndLossless {Proposer Acceptor Learner V : Type*}
    (b : Ballot Proposer) (p : Proposer) (Q : Finset Acceptor) (l : Learner)
    (ss : ωSequence (SynodState Proposer Acceptor Learner V))
    (xs : ωSequence (SynodAction Proposer Acceptor Learner V)) : Prop where
  /-- Proposer `p` remains live throughout the execution. -/
  proposer_live : ∀ n, ((ss n).proposers p).crashed = false
  /-- Every acceptor in quorum `Q` remains live throughout the execution. -/
  quorum_live : ∀ a ∈ Q, ∀ n, ((ss n).acceptors a).crashed = false
  /-- Learner `l` remains live throughout the execution. -/
  learner_live : ∀ n, ((ss n).learners l).crashed = false
  /-- No packet carrying ballot `b` is dropped by the network. -/
  no_drop_ballot : ∀ n m, xs n = .drop m → m.ballot ≠ b
  /-- Fair Phase 1a delivery: `Phase1a(b)` is eventually delivered to every `a ∈ Q`. -/
  fair_phase1a : ∀ n, Msg.phase1a b ∈ (ss n).msgs →
    ∀ a ∈ Q, ∃ j, n ≤ j ∧ xs j = .recvPhase1a a b
  /-- Fair Phase 1b delivery: every `Phase1b(a, b, mv)` from `a ∈ Q` is eventually delivered to
  `p`. -/
  fair_phase1b : ∀ n a mv, a ∈ Q → Msg.phase1b a b mv ∈ (ss n).msgs →
    ∃ j, n ≤ j ∧ xs j = .recvPhase1b p a b mv
  /-- Fair Phase 2a delivery: `Phase2a(b, v)` is eventually delivered to every `a ∈ Q`. -/
  fair_phase2a : ∀ n v, Msg.phase2a b v ∈ (ss n).msgs →
    ∀ a ∈ Q, ∃ j, n ≤ j ∧ xs j = .recvPhase2a a b v
  /-- Fair Phase 2b delivery: every `Phase2b(a, b, v)` from `a ∈ Q` is eventually delivered to
  `l`. -/
  fair_phase2b : ∀ n a v, a ∈ Q → Msg.phase2b a b v ∈ (ss n).msgs →
    ∃ j, n ≤ j ∧ xs j = .recvPhase2b l a b v

section SoleLeader

variable {Proposer Acceptor Learner V : Type*}
  [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
  (qs : QuorumSystem Acceptor)

private lemma ballot_msg_persist {b : Ballot Proposer}
    {ss : ωSequence (SynodState Proposer Acceptor Learner V)}
    {xs : ωSequence (SynodAction Proposer Acceptor Learner V)}
    (hexec : (synodLts qs).OmegaExecution ss xs)
    (hnodrop : ∀ n m, xs n = .drop m → m.ballot ≠ b)
    {n j : ℕ} (hnj : n ≤ j) {m : Msg Proposer Acceptor V}
    (hm : m ∈ (ss n).msgs) (hbal : m.ballot = b) :
    m ∈ (ss j).msgs := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnj
  induction d with
  | zero => simpa only [Nat.add_zero] using hm
  | succ d ih =>
    rw [← Nat.add_assoc, (hexec (n + d)).2]
    exact mem_msgs_synodStep_of_mem (ih (Nat.le_add_right n d))
      (fun hact => hnodrop (n + d) m hact hbal)

private lemma ballot_ceiling_inv {b : Ballot Proposer}
    {ss : ωSequence (SynodState Proposer Acceptor Learner V)}
    {xs : ωSequence (SynodAction Proposer Acceptor Learner V)}
    (hexec : (synodLts qs).OmegaExecution ss xs)
    (hbelow : BallotsBelow (ss 0) b)
    (hno_higher : ∀ j q r', xs j = .prepare q r' → ⟨r', q⟩ ≤ b) :
    ∀ n, (∀ m ∈ (ss n).msgs, m.ballot ≤ b) ∧
      (∀ a mb, ((ss n).acceptors a).maxBal = some mb → mb ≤ b) := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun m hm => le_of_lt (hbelow.1 m hm),
      fun a mb hmb => le_of_lt (hbelow.2 a mb hmb)⟩
  | succ n ih =>
    obtain ⟨hen, hstep⟩ := hexec n
    rw [hstep]
    refine ⟨fun m hm => ?_, fun a mb hmb => ?_⟩
    · rcases mem_msgs_synodStep_cases hm with hold | ⟨q, r', hact, rfl⟩ |
          ⟨a, b', hact, _, rfl⟩ | ⟨q, a, b', mv, r_q, _, hact, _, hb_eq, _, rfl⟩ |
          ⟨a, b', v, hact, _, rfl⟩
      · exact ih.1 m hold
      · exact hno_higher n q r' hact
      · rw [hact] at hen; exact ih.1 (.phase1a b') hen.2
      · rw [hact] at hen; exact hb_eq ▸ ih.1 (.phase1b a b' mv) hen.2
      · rw [hact] at hen; exact ih.1 (.phase2a b' v) hen.2
    · rcases acceptors_synodStep_cases qs (ss n) (xs n) a with heq |
          ⟨b', hact, _, heq, _⟩ | ⟨b', v, hact, _, heq⟩ | ⟨_, heq⟩
      · rw [heq] at hmb; exact ih.2 a mb hmb
      · rw [heq] at hmb; injection hmb with h_eq
        rw [hact] at hen; exact h_eq ▸ ih.1 (.phase1a b') hen.2
      · rw [heq] at hmb; injection hmb with h_eq
        rw [hact] at hen; exact h_eq ▸ ih.1 (.phase2a b' v) hen.2
      · rw [heq] at hmb; exact ih.2 a mb hmb

private lemma sole_leader_round_inv {p : Proposer} {r : ℕ}
    {ss : ωSequence (SynodState Proposer Acceptor Learner V)}
    {xs : ωSequence (SynodAction Proposer Acceptor Learner V)}
    (hexec : (synodLts qs).OmegaExecution ss xs)
    (hprep₀ : xs 0 = .prepare p r)
    (hno_higher : ∀ j q r', xs j = .prepare q r' → ⟨r', q⟩ ≤ (⟨r, p⟩ : Ballot Proposer)) :
    ∀ n, 1 ≤ n → ((ss n).proposers p).round = some r ∧
      ∀ r', xs n ≠ .prepare p r' := by
  have hnot_prep : ∀ n, ((ss n).proposers p).round = some r → ∀ r', xs n ≠ .prepare p r' := by
    intro n hround r' hact
    obtain ⟨hen, _⟩ := hexec n
    rw [hact] at hen
    dsimp only [synodEnabled] at hen
    rw [hround] at hen
    have hle := (Ballot.le_iff _ _).mp (hno_higher n p r' hact)
    dsimp only at hle
    rcases hle with hlt | ⟨heq, _⟩ <;> omega
  have hround_all : ∀ k, ((ss (1 + k)).proposers p).round = some r := by
    intro k
    induction k with
    | zero =>
      rw [(hexec 0).2, hprep₀]
      dsimp only [synodStep, synodStepCore]
      simp only [↓reduceIte]
    | succ k ih =>
      have hidx : 1 + k + 1 = 1 + (k + 1) := by omega
      rw [← hidx, (hexec (1 + k)).2]
      rcases proposers_synodStep_cases qs (ss (1 + k)) (xs (1 + k)) p with heq |
          ⟨r', hact, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, heq, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, heq⟩ | ⟨_, heq⟩
      · rw [heq]; exact ih
      · exact absurd hact (hnot_prep (1 + k) ih r')
      · rw [heq]; exact ih
      · rw [heq]; exact ih
      · rw [heq]; exact ih
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact ⟨hround_all k, hnot_prep (1 + k) (hround_all k)⟩

private lemma promised_mono {p : Proposer} {r : ℕ}
    {ss : ωSequence (SynodState Proposer Acceptor Learner V)}
    {xs : ωSequence (SynodAction Proposer Acceptor Learner V)}
    (hexec : (synodLts qs).OmegaExecution ss xs)
    (hprep₀ : xs 0 = .prepare p r)
    (hno_higher : ∀ j q r', xs j = .prepare q r' → ⟨r', q⟩ ≤ (⟨r, p⟩ : Ballot Proposer))
    {n₁ n₂ : ℕ} (h₁ : 1 ≤ n₁) (hle : n₁ ≤ n₂) :
    ((ss n₁).proposers p).promised ⊆ ((ss n₂).proposers p).promised := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction d with
  | zero => exact Finset.Subset.rfl
  | succ d ih =>
    have hsub := ih (Nat.le_add_right n₁ d)
    have hno_prep := (sole_leader_round_inv qs hexec hprep₀ hno_higher (n₁ + d) (by omega)).2
    rw [← Nat.add_assoc, (hexec (n₁ + d)).2]
    rcases proposers_synodStep_cases qs (ss (n₁ + d)) (xs (n₁ + d)) p with heq |
        ⟨r', hact, _⟩ | ⟨a, _, _, _, _, _, _, _, _, _, heq, _⟩ |
        ⟨a, _, _, _, _, _, _, _, _, heq⟩ | ⟨_, heq⟩
    · rwa [heq]
    · exact absurd hact (hno_prep r')
    · rw [heq]; exact hsub.trans (Finset.subset_insert a _)
    · rw [heq]; exact hsub.trans (Finset.subset_insert a _)
    · rwa [heq]

private lemma learner_received_mono {l : Learner}
    {ss : ωSequence (SynodState Proposer Acceptor Learner V)}
    {xs : ωSequence (SynodAction Proposer Acceptor Learner V)}
    (hexec : (synodLts qs).OmegaExecution ss xs)
    {n₁ n₂ : ℕ} (hle : n₁ ≤ n₂) :
    ((ss n₁).learners l).received ⊆ ((ss n₂).learners l).received := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction d with
  | zero => exact Finset.Subset.rfl
  | succ d ih =>
    have hsub := ih (Nat.le_add_right n₁ d)
    rw [← Nat.add_assoc, (hexec (n₁ + d)).2]
    rcases learners_synodStep_cases qs (ss (n₁ + d)) (xs (n₁ + d)) l with heq |
        ⟨_, _, _, _, heq⟩ | ⟨_, heq⟩
    · rwa [heq]
    · rw [heq]; exact hsub.trans (Finset.subset_insert _ _)
    · rwa [heq]

/-- Conditional crash-stop 4-phase progress step towards [Lamport2001] §2.4 and [Lamport1998] §2.1
Theorem 2 / §2.4, and **not** the crash-recovery or timeout-based leader-election liveness result:
assuming an already-selected sole leader `p` (without modeling leader election, NACK `nextBal[q]`
ballot-bumping, persistent-storage crash recovery, or real-time timeout bounds), from any reachable
crash-stop Synod state `ss 0`, if live proposer `p` issues `prepare p r` at step `0` with ballot
`b = ⟨r, p⟩` strictly exceeding all ballots previously present or promised
(`BallotsBelow (ss 0) b`), no ballot strictly greater than `b` is subsequently prepared, and
ballot-`b` packets among `p`, one live quorum `Q ∈ qs.quorums`, and live learner `l` are delivered
without loss (`LiveAndLossless b p Q l ss xs`), then `l` eventually learns a decree value `v` at
ballot `b` (and `((ss k).learners l).learned = some v`). -/
theorem paxos_liveness_of_sole_leader_crashStop {inputs : Proposer → V}
    {ss : ωSequence (SynodState Proposer Acceptor Learner V)}
    {xs : ωSequence (SynodAction Proposer Acceptor Learner V)}
    (hr₀ : Reachable qs inputs (ss 0))
    (hexec : (synodLts qs).OmegaExecution ss xs)
    {p : Proposer} {r : ℕ} {Q : Finset Acceptor} {l : Learner}
    (hQ : Q ∈ qs.quorums)
    (hprep₀ : xs 0 = .prepare p r)
    (hbelow : BallotsBelow (ss 0) ⟨r, p⟩)
    (hno_higher : ∀ j q r', xs j = .prepare q r' → ⟨r', q⟩ ≤ (⟨r, p⟩ : Ballot Proposer))
    (hlive : LiveAndLossless ⟨r, p⟩ p Q l ss xs) :
    ∃ k v, (ss k).LearnedAt qs l ⟨r, p⟩ v ∧ ((ss k).learners l).learned = some v := by
  set b : Ballot Proposer := ⟨r, p⟩
  have hceil := ballot_ceiling_inv qs hexec hbelow hno_higher
  have hround_inv := sole_leader_round_inv qs hexec hprep₀ hno_higher
  have hs1_1a : Msg.phase1a b ∈ (ss 1).msgs := by
    rw [(hexec 0).2, hprep₀]; exact Finset.mem_insert_self _ _
  have ⟨hs1_prop_false, hs1_prom_empty⟩ :
      ((ss 1).proposers p).proposed = false ∧ ((ss 1).proposers p).promised = ∅ := by
    rw [(hexec 0).2, hprep₀]
    dsimp only [synodStep, synodStepCore]
    rw [ite_eq_left rfl]
    exact ⟨rfl, rfl⟩
  -- Phase 1a → 1b → 2a: prove `∃ n₂ ≥ 1, ∃ v, Msg.phase2a b v ∈ (ss n₂).msgs`.
  have hexists_2a : ∃ n₂ v, 1 ≤ n₂ ∧ Msg.phase2a b v ∈ (ss n₂).msgs := by
    by_cases hprop_ever : ∃ n, 1 ≤ n ∧ ((ss n).proposers p).proposed = true
    · obtain ⟨n_wit, hn_wit, htrue_wit⟩ := hprop_ever
      obtain ⟨d_wit, rfl⟩ := Nat.exists_eq_add_of_le hn_wit
      obtain ⟨d, hd_not, hd_true⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
        (p := fun d => ((ss (1 + d)).proposers p).proposed = true)
        (by simp only [Nat.add_zero, hs1_prop_false, Bool.false_eq_true, not_false_eq_true])
        ⟨d_wit, htrue_wit⟩
      set m := 1 + d
      have hm1 : 1 ≤ m := Nat.le_add_right 1 d
      have hm_false : ((ss m).proposers p).proposed = false := Bool.eq_false_iff.mpr hd_not
      have hm_true : ((ss (m + 1)).proposers p).proposed = true := by
        simpa only [m, Nat.add_assoc] using hd_true
      have ⟨hm_round, hm_noprep⟩ := hround_inv m hm1
      rw [(hexec m).2] at hm_true
      rcases proposers_synodStep_cases qs (ss m) (xs m) p with heq | ⟨r', hact, _⟩ |
          ⟨_, _, _, r_m, val, _, hr_m, _, _, _, _, h2a_mem⟩ |
          ⟨_, _, _, _, _, _, _, _, _, heq⟩ | ⟨_, heq⟩
      · exact absurd (heq.symm ▸ hm_true) (by rw [hm_false]; exact Bool.false_ne_true)
      · exact absurd hact (hm_noprep r')
      · have hr_eq : r_m = r := Option.some.inj (hr_m.symm.trans hm_round)
        subst hr_eq
        exact ⟨m + 1, val, by omega, (hexec m).2 ▸ h2a_mem⟩
      · rw [heq, hm_false] at hm_true; cases hm_true
      · rw [heq, hm_false] at hm_true; cases hm_true
    · -- Contradiction if `proposed` stays `false` for all `n ≥ 1`:
      have hprop_false : ∀ n, 1 ≤ n → ((ss n).proposers p).proposed = false := fun n hn =>
        Bool.eq_false_iff.mpr fun h => hprop_ever ⟨n, hn, h⟩
      have hno_2a : ∀ n v, Msg.phase2a b v ∉ (ss n).msgs := by
        intro n
        induction n with
        | zero => exact fun v hm => lt_irrefl b (hbelow.1 (.phase2a b v) hm)
        | succ n ih =>
          intro v hm
          rw [(hexec n).2] at hm
          rcases mem_msgs_synodStep_cases hm with hold | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ |
              ⟨q, _, _, _, r_q, _, hact, _, _, hprop_t, h⟩ | ⟨_, _, _, _, _, h⟩
          · exact ih v hold
          · cases h
          · cases h
          · injection h with hb_eq _
            have hqp : q = p := (congrArg Ballot.proposer hb_eq).symm
            subst hqp
            rcases eq_or_ne n 0 with rfl | hn0
            · rw [hprep₀] at hact; cases hact
            · have hp1 := hprop_false (n + 1) (by omega)
              rw [(hexec n).2, hprop_t] at hp1; cases hp1
          · cases h
      have hacc_1b : ∀ n a, ((ss n).acceptors a).maxBal = some b →
          ∃ j mv, Msg.phase1b a b mv ∈ (ss j).msgs := by
        intro n
        induction n with
        | zero => exact fun a hmb => False.elim (lt_irrefl b (hbelow.2 a b hmb))
        | succ n ih =>
          intro a hmb
          obtain ⟨hen, hstep⟩ := hexec n
          rw [hstep] at hmb
          rcases acceptors_synodStep_cases qs (ss n) (xs n) a with heq |
              ⟨b', _, _, heq, h1b⟩ | ⟨b', v, hact, _, heq⟩ | ⟨_, heq⟩
          · rw [heq] at hmb; exact ih a hmb
          · rw [heq] at hmb; injection hmb with hb_eq; subst hb_eq
            exact ⟨n + 1, _, hstep ▸ h1b⟩
          · rw [heq] at hmb; injection hmb with hb_eq; subst hb_eq
            rw [hact] at hen
            exact False.elim (hno_2a n v hen.2)
          · rw [heq] at hmb; exact ih a hmb
      have hQ_prom : ∀ a ∈ Q, ∃ n, 1 ≤ n ∧ a ∈ ((ss n).proposers p).promised := by
        intro a haQ
        obtain ⟨j₁, _, hj₁_act⟩ := hlive.fair_phase1a 1 hs1_1a a haQ
        have hex_1b : ∃ j_m mv, Msg.phase1b a b mv ∈ (ss j_m).msgs := by
          cases hab : aboveMaxBal ((ss j₁).acceptors a).maxBal b with
          | true =>
            refine ⟨j₁ + 1, ((ss j₁).acceptors a).maxVoted, ?_⟩
            rw [(hexec j₁).2, hj₁_act]
            dsimp only [synodStep, synodStepCore]
            rw [ite_eq_left hab]
            exact Finset.mem_insert_self _ _
          | false =>
            cases hmb_cur : ((ss j₁).acceptors a).maxBal with
            | none => rw [hmb_cur] at hab; cases hab
            | some mb =>
              rw [hmb_cur] at hab
              simp only [aboveMaxBal, decide_eq_false_iff_not, not_lt] at hab
              exact hacc_1b j₁ a (le_antisymm ((hceil j₁).2 a mb hmb_cur) hab ▸ hmb_cur)
        obtain ⟨j_m, mv, h1b_mem⟩ := hex_1b
        have h1b_at_max : Msg.phase1b a b mv ∈ (ss (max 1 j_m)).msgs :=
          ballot_msg_persist qs hexec hlive.no_drop_ballot (le_max_right 1 j_m) h1b_mem rfl
        obtain ⟨j₂, hj₂_ge, hj₂_act⟩ := hlive.fair_phase1b (max 1 j_m) a mv haQ h1b_at_max
        have hj₂_1 : 1 ≤ j₂ := (le_max_left 1 j_m).trans hj₂_ge
        refine ⟨j₂ + 1, by omega, ?_⟩
        by_cases ha_already : a ∈ ((ss j₂).proposers p).promised
        · exact promised_mono qs hexec hprep₀ hno_higher hj₂_1 (Nat.le_succ j₂) ha_already
        · rw [(hexec j₂).2, hj₂_act]
          dsimp only [synodStep, synodStepCore]
          rw [(hround_inv j₂ hj₂_1).1]
          dsimp only []
          rw [ite_eq_left ⟨rfl, ha_already⟩]
          split_ifs <;> simp only [↓reduceIte] <;> exact Finset.mem_insert_self _ _
      let stepOf : Acceptor → ℕ := fun a =>
        if h : a ∈ Q then Classical.choose (hQ_prom a h) else 1
      let N_all := max 1 (Q.sup stepOf)
      have hQ_sub_Nall : Q ⊆ ((ss N_all).proposers p).promised := by
        intro a haQ
        have hspec := Classical.choose_spec (hQ_prom a haQ)
        have hle_sup : Classical.choose (hQ_prom a haQ) ≤ Q.sup stepOf := by
          simpa only [stepOf, dite_eq_left haQ] using Finset.le_sup (f := stepOf) haQ
        exact promised_mono qs hexec hprep₀ hno_higher hspec.1
          (hle_sup.trans (le_max_right 1 _)) hspec.2
      have hnot_1 : ¬ (Q ⊆ ((ss 1).proposers p).promised) := by
        rw [hs1_prom_empty]
        obtain ⟨a₀, ha₀⟩ := qs.quorum_nonempty hQ
        exact fun hsub => Finset.notMem_empty a₀ (hsub ha₀)
      obtain ⟨d_all, hd_eq⟩ := Nat.exists_eq_add_of_le (le_max_left 1 (Q.sup stepOf))
      obtain ⟨d, hm_not_sub, hd_sub⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
        (p := fun d => Q ⊆ ((ss (1 + d)).proposers p).promised)
        (by simpa only [Nat.add_zero] using hnot_1)
        ⟨d_all, hd_eq ▸ hQ_sub_Nall⟩
      set m := 1 + d
      have hm1 : 1 ≤ m := Nat.le_add_right 1 d
      have hm_sub : Q ⊆ ((ss (m + 1)).proposers p).promised := by
        simpa only [m, Nat.add_assoc] using hd_sub
      have ⟨_, hm_noprep⟩ := hround_inv m hm1
      have hm_pfalse := hprop_false m hm1
      have hm_next_pfalse := hprop_false (m + 1) (by omega)
      rw [(hexec m).2] at hm_sub hm_next_pfalse
      rcases proposers_synodStep_cases qs (ss m) (xs m) p with heq | ⟨r', hact, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, heq, _⟩ |
          ⟨a, _, _, _, _, _, _, _, hq_not, heq⟩ | ⟨_, heq⟩
      · exact False.elim (hm_not_sub (heq ▸ hm_sub))
      · exact False.elim (hm_noprep r' hact)
      · rw [heq] at hm_next_pfalse; cases hm_next_pfalse
      · rw [heq] at hm_sub
        refine False.elim (hq_not ?_)
        rw [hm_pfalse]
        simp only [Bool.not_false, Bool.true_and, decide_eq_true_eq]
        exact ⟨Q, hQ, hm_sub⟩
      · rw [heq] at hm_sub
        exact False.elim (hm_not_sub hm_sub)
  -- Phase 2a → 2b → Learned at `l`:
  obtain ⟨n₂, v, _, h2a_mem⟩ := hexists_2a
  have hQ_recv : ∀ a ∈ Q, ∃ n, ⟨a, b, v⟩ ∈ ((ss n).learners l).received := by
    intro a haQ
    obtain ⟨j₃, _, hj₃_act⟩ := hlive.fair_phase2a n₂ v h2a_mem a haQ
    have hallows_j₃ : allowsVote ((ss j₃).acceptors a).maxBal b = true := by
      cases hmb : ((ss j₃).acceptors a).maxBal with
      | none => rfl
      | some mb =>
        simp only [allowsVote, decide_eq_true_eq]
        exact (hceil j₃).2 a mb hmb
    have h2b_mem : Msg.phase2b a b v ∈ (ss (j₃ + 1)).msgs := by
      rw [(hexec j₃).2, hj₃_act]
      dsimp only [synodStep, synodStepCore]
      rw [ite_eq_left hallows_j₃]
      exact Finset.mem_insert_self _ _
    obtain ⟨j₄, _, hj₄_act⟩ := hlive.fair_phase2b (j₃ + 1) a v haQ h2b_mem
    refine ⟨j₄ + 1, ?_⟩
    rw [(hexec j₄).2, hj₄_act]
    dsimp only [synodStep, synodStepCore]
    simp only [↓reduceIte]
    exact Finset.mem_insert_self _ _
  let recvStep : Acceptor → ℕ := fun a =>
    if h : a ∈ Q then Classical.choose (hQ_recv a h) else 0
  let k_final := Q.sup recvStep
  have hlearnedAt : (ss k_final).LearnedAt qs l b v := by
    refine ⟨Q, hQ, fun a haQ => ?_⟩
    have hle : Classical.choose (hQ_recv a haQ) ≤ k_final := by
      simpa only [recvStep, dite_eq_left haQ] using Finset.le_sup (f := recvStep) haQ
    exact learner_received_mono qs hexec hle (Classical.choose_spec (hQ_recv a haQ))
  have hr_final : Reachable qs inputs (ss k_final) :=
    hr₀.trans ⟨xs.extract 0 k_final, hexec.extract_mTr (Nat.zero_le k_final)⟩
  exact ⟨k_final, v, hlearnedAt, hr_final.learned_eq_some_iff.mpr ⟨b, hlearnedAt⟩⟩

/-! ### Constructive fair 4-phase execution from any reachable state -/

private noncomputable def soleLeaderMsgActs (b : Ballot Proposer) (p : Proposer)
    (Q : Finset Acceptor) (l : Learner) :
    Msg Proposer Acceptor V → List (SynodAction Proposer Acceptor Learner V)
  | .phase1a b' => if b' = b then Q.toList.map fun a => .recvPhase1a a b else []
  | .phase1b a b' mv => if b' = b ∧ a ∈ Q then [.recvPhase1b p a b mv] else []
  | .phase2a b' v => if b' = b then Q.toList.map fun a => .recvPhase2a a b v else []
  | .phase2b a b' v => if b' = b ∧ a ∈ Q then [.recvPhase2b l a b v] else []

private noncomputable def soleLeaderSweep (b : Ballot Proposer) (p : Proposer)
    (Q : Finset Acceptor) (l : Learner)
    (u : SynodState Proposer Acceptor Learner V) :
    List (SynodAction Proposer Acceptor Learner V) :=
  u.msgs.toList.flatMap (soleLeaderMsgActs b p Q l) ++ [.stutter]

omit [DecidableEq Learner] [DecidableEq V] in
private lemma soleLeaderSweep_pos (b : Ballot Proposer) (p : Proposer)
    (Q : Finset Acceptor) (l : Learner)
    (u : SynodState Proposer Acceptor Learner V) :
    0 < (soleLeaderSweep b p Q l u).length := by
  simp only [soleLeaderSweep, List.length_append, List.length_singleton]
  omega

omit [DecidableEq Learner] [DecidableEq V] in
private lemma mem_soleLeaderSweep_cases {b : Ballot Proposer} {p : Proposer}
    {Q : Finset Acceptor} {l : Learner}
    {u : SynodState Proposer Acceptor Learner V}
    {act : SynodAction Proposer Acceptor Learner V}
    (hmem : act ∈ soleLeaderSweep b p Q l u) :
    act = .stutter ∨
      (∃ a ∈ Q, Msg.phase1a b ∈ u.msgs ∧ act = .recvPhase1a a b) ∨
      (∃ a ∈ Q, ∃ mv, Msg.phase1b a b mv ∈ u.msgs ∧ act = .recvPhase1b p a b mv) ∨
      (∃ a ∈ Q, ∃ v, Msg.phase2a b v ∈ u.msgs ∧ act = .recvPhase2a a b v) ∨
      (∃ a ∈ Q, ∃ v, Msg.phase2b a b v ∈ u.msgs ∧ act = .recvPhase2b l a b v) := by
  simp only [soleLeaderSweep, soleLeaderMsgActs, List.mem_append, List.mem_singleton,
    List.mem_flatMap, Finset.mem_toList] at hmem
  rcases hmem with ⟨m, hm_msgs, hm_act⟩ | rfl
  · cases m with
    | phase1a b' =>
      dsimp only at hm_act
      split_ifs at hm_act with hb
      · subst hb
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm_act
        exact Or.inr (Or.inl ⟨a, Finset.mem_toList.mp ha, hm_msgs, rfl⟩)
      · cases hm_act
    | phase1b a b' mv =>
      dsimp only at hm_act
      split_ifs at hm_act with hba
      · obtain ⟨rfl, haQ⟩ := hba
        rw [List.mem_singleton] at hm_act
        exact Or.inr (Or.inr (Or.inl ⟨a, haQ, mv, hm_msgs, hm_act⟩))
      · cases hm_act
    | phase2a b' v =>
      dsimp only at hm_act
      split_ifs at hm_act with hb
      · subst hb
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm_act
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, Finset.mem_toList.mp ha, v, hm_msgs, rfl⟩)))
      · cases hm_act
    | phase2b a b' v =>
      dsimp only at hm_act
      split_ifs at hm_act with hba
      · obtain ⟨rfl, haQ⟩ := hba
        rw [List.mem_singleton] at hm_act
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, haQ, v, hm_msgs, hm_act⟩)))
      · cases hm_act
  · exact Or.inl rfl

private def IsSweepAct (act : SynodAction Proposer Acceptor Learner V) : Prop :=
  (∀ q r', act ≠ .prepare q r') ∧ (∀ m, act ≠ .drop m) ∧
    (∀ q, act ≠ .crashProposer q) ∧ (∀ a, act ≠ .crashAcceptor a) ∧
    (∀ l₀, act ≠ .crashLearner l₀)

omit [DecidableEq Learner] [DecidableEq V] in
private lemma isSweepAct_of_mem_soleLeaderSweep {b : Ballot Proposer} {p : Proposer}
    {Q : Finset Acceptor} {l : Learner} {u : SynodState Proposer Acceptor Learner V}
    {act : SynodAction Proposer Acceptor Learner V}
    (hmem : act ∈ soleLeaderSweep b p Q l u) : IsSweepAct act := by
  rcases mem_soleLeaderSweep_cases hmem with rfl | ⟨_, _, _, rfl⟩ |
      ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
    exact ⟨nofun, nofun, nofun, nofun, nofun⟩

private lemma synodStep_preserve_of_delivery {w : SynodState Proposer Acceptor Learner V}
    {act : SynodAction Proposer Acceptor Learner V}
    (hnodrop : ∀ m, act ≠ .drop m)
    (hnocp : ∀ q, act ≠ .crashProposer q)
    (hnoca : ∀ a, act ≠ .crashAcceptor a)
    (hnocl : ∀ l₀, act ≠ .crashLearner l₀) :
    let w' := synodStep qs w act
    w.msgs ⊆ w'.msgs ∧
      (∀ q, (w'.proposers q).crashed = (w.proposers q).crashed) ∧
      (∀ a, (w'.acceptors a).crashed = (w.acceptors a).crashed) ∧
      (∀ l₀, (w'.learners l₀).crashed = (w.learners l₀).crashed) := by
  refine ⟨fun m hm => mem_msgs_synodStep_of_mem hm (hnodrop m), fun q => ?_, fun a => ?_,
    fun l₀ => ?_⟩
  · rcases proposers_synodStep_cases qs w act q with heq | ⟨_, _, heq⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, heq, _⟩ | ⟨_, _, _, _, _, _, _, _, _, heq⟩ | ⟨hact, _⟩
    · rw [heq]
    · rw [heq]
    · rw [heq]
    · rw [heq]
    · exact absurd hact (hnocp q)
  · rcases acceptors_synodStep_cases qs w act a with heq | ⟨_, _, _, heq, _⟩ |
        ⟨_, _, _, _, heq⟩ | ⟨hact, _⟩
    · rw [heq]
    · rw [heq]
    · rw [heq]
    · exact absurd hact (hnoca a)
  · rcases learners_synodStep_cases qs w act l₀ with heq | ⟨_, _, _, _, heq⟩ | ⟨hact, _⟩
    · rw [heq]
    · rw [heq]
    · exact absurd hact (hnocl l₀)

private lemma soleLeaderSweep_mTr {b : Ballot Proposer} {p : Proposer}
    {Q : Finset Acceptor} {l : Learner}
    {u : SynodState Proposer Acceptor Learner V}
    (hp_live : (u.proposers p).crashed = false)
    (hQ_live : ∀ a ∈ Q, (u.acceptors a).crashed = false)
    (hl_live : (u.learners l).crashed = false) :
    let u' := (soleLeaderSweep b p Q l u).foldl (synodStep qs) u
    (synodLts qs).MTr u (soleLeaderSweep b p Q l u) u' ∧
      (u'.proposers p).crashed = false ∧
      (∀ a ∈ Q, (u'.acceptors a).crashed = false) ∧
      (u'.learners l).crashed = false := by
  have hloop : ∀ (acts : List (SynodAction Proposer Acceptor Learner V)),
      (∀ act ∈ acts, act ∈ soleLeaderSweep b p Q l u) →
      ∀ (w : SynodState Proposer Acceptor Learner V),
      u.msgs ⊆ w.msgs →
      (w.proposers p).crashed = false →
      (∀ a ∈ Q, (w.acceptors a).crashed = false) →
      (w.learners l).crashed = false →
      let w' := acts.foldl (synodStep qs) w
      (synodLts qs).MTr w acts w' ∧
        (w'.proposers p).crashed = false ∧
        (∀ a ∈ Q, (w'.acceptors a).crashed = false) ∧
        (w'.learners l).crashed = false := by
    intro acts hacts
    induction acts with
    | nil => exact fun _ _ hpw hQw hlw => ⟨LTS.MTr.refl, hpw, hQw, hlw⟩
    | cons act rest ih =>
      intro w hsub hpw hQw hlw
      have hmem := hacts act List.mem_cons_self
      have hen : synodEnabled w act := by
        rcases mem_soleLeaderSweep_cases hmem with rfl | ⟨a, haQ, hm, rfl⟩ |
            ⟨a, haQ, _, hm, rfl⟩ | ⟨a, haQ, _, hm, rfl⟩ | ⟨a, haQ, _, hm, rfl⟩
        · trivial
        · exact ⟨hQw a haQ, hsub hm⟩
        · exact ⟨hpw, hsub hm⟩
        · exact ⟨hQw a haQ, hsub hm⟩
        · exact ⟨hlw, hsub hm⟩
      have hsw := isSweepAct_of_mem_soleLeaderSweep hmem
      have hpres := synodStep_preserve_of_delivery (qs := qs) (w := w) (act := act)
        hsw.2.1 hsw.2.2.1 hsw.2.2.2.1 hsw.2.2.2.2
      obtain ⟨hmtr_r, hpw', hQw', hlw'⟩ := ih
        (fun x hx => hacts x (List.mem_cons_of_mem act hx))
        (synodStep qs w act) (hsub.trans hpres.1)
        ((hpres.2.1 p).trans hpw)
        (fun a haQ => (hpres.2.2.1 a).trans (hQw a haQ))
        ((hpres.2.2.2 l).trans hlw)
      exact ⟨LTS.MTr.stepL ⟨hen, rfl⟩ hmtr_r, hpw', hQw', hlw'⟩
  exact hloop (soleLeaderSweep b p Q l u) (fun _ h => h) u Finset.Subset.rfl
    hp_live hQ_live hl_live

private noncomputable def soleLeaderStateSeq (qs : QuorumSystem Acceptor) (b : Ballot Proposer)
    (p : Proposer) (Q : Finset Acceptor) (l : Learner)
    (s₁ : SynodState Proposer Acceptor Learner V) :
    ℕ → SynodState Proposer Acceptor Learner V
  | 0 => s₁
  | c + 1 => (soleLeaderSweep b p Q l (soleLeaderStateSeq qs b p Q l s₁ c)).foldl
      (synodStep qs) (soleLeaderStateSeq qs b p Q l s₁ c)

/-- Crash-stop constructive non-vacuity witness for `paxos_liveness_of_sole_leader_crashStop` (a
step towards [Lamport2001] §2.4 and [Lamport1998] §2.1 Theorem 2, not the crash-recovery cited
protocol): from any reachable crash-stop state `s₀` over `[Finite Acceptor]`, given live proposer
`p`, live quorum `Q ∈ qs.quorums`, and live learner `l`, there exists a fresh round `r` and a valid
infinite execution starting from `s₀` (preparing `⟨r, p⟩` at step `0` and then repeatedly sweeping
ballot-`b` deliveries across `p`, `Q`, and `l`) satisfying `LiveAndLossless` in which `l` learns a
value `v` at ballot `⟨r, p⟩`. -/
theorem exists_sole_leader_execution_crashStop [Finite Acceptor] {inputs : Proposer → V}
    {s₀ : SynodState Proposer Acceptor Learner V}
    (hr₀ : Reachable qs inputs s₀)
    {p : Proposer} {Q : Finset Acceptor} {l : Learner}
    (hQ : Q ∈ qs.quorums)
    (hp_live : (s₀.proposers p).crashed = false)
    (hQ_live : ∀ a ∈ Q, (s₀.acceptors a).crashed = false)
    (hl_live : (s₀.learners l).crashed = false) :
    ∃ (r : ℕ) (ss : ωSequence (SynodState Proposer Acceptor Learner V))
      (xs : ωSequence (SynodAction Proposer Acceptor Learner V)) (k : ℕ) (v : V),
      ss 0 = s₀ ∧
      (synodLts qs).OmegaExecution ss xs ∧
      xs 0 = .prepare p r ∧
      BallotsBelow (ss 0) ⟨r, p⟩ ∧
      (∀ j q r', xs j = .prepare q r' → ⟨r', q⟩ ≤ (⟨r, p⟩ : Ballot Proposer)) ∧
      LiveAndLossless ⟨r, p⟩ p Q l ss xs ∧
      (ss k).LearnedAt qs l ⟨r, p⟩ v ∧
      ((ss k).learners l).learned = some v := by
  let _ := Fintype.ofFinite Acceptor
  let msgBound := s₀.msgs.sup fun m => m.ballot.round + 1
  let accBound := (Finset.univ : Finset Acceptor).sup fun a =>
    match (s₀.acceptors a).maxBal with
    | none => 0
    | some mb => mb.round + 1
  let propBound := match (s₀.proposers p).round with
    | none => 0
    | some r₀ => r₀ + 1
  let r := max propBound (max msgBound accBound)
  let b : Ballot Proposer := ⟨r, p⟩
  have hbelow : BallotsBelow s₀ b := by
    refine ⟨fun m hm => (Ballot.lt_iff _ _).mpr (Or.inl ?_),
      fun a mb hmb => (Ballot.lt_iff _ _).mpr (Or.inl ?_)⟩
    · have hle1 := Finset.le_sup (f := fun m : Msg Proposer Acceptor V => m.ballot.round + 1) hm
      have hle2 : msgBound ≤ r := (le_max_left msgBound accBound).trans (le_max_right _ _)
      exact Nat.lt_of_succ_le (hle1.trans hle2)
    · have hle1 : mb.round + 1 ≤ accBound := by
        have hsup := Finset.le_sup (s := Finset.univ)
          (f := fun a' : Acceptor => match (s₀.acceptors a').maxBal with
            | none => 0 | some mb' => mb'.round + 1) (Finset.mem_univ a)
        simpa only [hmb] using hsup
      have hle2 : accBound ≤ r := (le_max_right msgBound accBound).trans (le_max_right _ _)
      exact Nat.lt_of_succ_le (hle1.trans hle2)
  have hp_round_ok : match (s₀.proposers p).round with | none => True | some r₀ => r₀ < r := by
    cases hpr : (s₀.proposers p).round with
    | none => trivial
    | some r₀ =>
      have hle : propBound ≤ r := le_max_left _ _
      simpa only [propBound, hpr, Nat.succ_le_iff] using hle
  let s₁ := synodStep qs s₀ (.prepare p r)
  have htr_prep : (synodLts qs).Tr s₀ (.prepare p r) s₁ := ⟨⟨hp_live, hp_round_ok⟩, rfl⟩
  let ts : ωSequence (SynodState Proposer Acceptor Learner V) :=
    ωSequence.mk (soleLeaderStateSeq qs b p Q l s₁)
  let xls : ωSequence (List (SynodAction Proposer Acceptor Learner V)) :=
    ωSequence.mk fun c => soleLeaderSweep b p Q l (ts c)
  have hts_live : ∀ c, ((ts c).proposers p).crashed = false ∧
      (∀ a ∈ Q, ((ts c).acceptors a).crashed = false) ∧
      ((ts c).learners l).crashed = false := by
    intro c
    induction c with
    | zero =>
      refine ⟨?_, hQ_live, hl_live⟩
      dsimp only [ts, get_fun, soleLeaderStateSeq, s₁, synodStep, synodStepCore]
      simp only [↓reduceIte, hp_live]
    | succ c ih => exact (soleLeaderSweep_mTr qs ih.1 ih.2.1 ih.2.2 (b := b)).2
  have hts_mtr : ∀ c, (synodLts qs).MTr (ts c) (xls c) (ts (c + 1)) :=
    fun c => (soleLeaderSweep_mTr qs (hts_live c).1 (hts_live c).2.1 (hts_live c).2.2).1
  have hpos : ∀ c, 0 < (xls c).length := fun c => soleLeaderSweep_pos b p Q l (ts c)
  have : Inhabited (SynodAction Proposer Acceptor Learner V) := ⟨.stutter⟩
  obtain ⟨ss_tail, hexec_tail, hcum⟩ := LTS.OmegaExecution.flatten_mTr hts_mtr hpos
  let ss := s₀ ::ω ss_tail
  let xs := (SynodAction.prepare p r) ::ω xls.flatten
  have hexec : (synodLts qs).OmegaExecution ss xs :=
    LTS.OmegaExecution.cons htr_prep hexec_tail
      (by simpa only [cumLen_zero, ts, get_fun, soleLeaderStateSeq] using hcum 0)
  have htail_ok : ∀ m, IsSweepAct (xs (m + 1)) :=
    (forall_flatten_iff hpos IsSweepAct).mpr fun _ =>
      List.forall_iff_forall_mem.mpr fun _ => isSweepAct_of_mem_soleLeaderSweep
  have hxs_nodel : ∀ n, (∀ m, xs n ≠ .drop m) ∧ (∀ q, xs n ≠ .crashProposer q) ∧
      (∀ a, xs n ≠ .crashAcceptor a) ∧ (∀ l₀, xs n ≠ .crashLearner l₀) := fun
    | 0 => ⟨nofun, nofun, nofun, nofun⟩
    | m + 1 => (htail_ok m).2
  have hno_higher : ∀ j q r', xs j = .prepare q r' → ⟨r', q⟩ ≤ b := by
    rintro (_ | m) q r' hj
    · injection hj with hq hr; subst hq hr; exact le_refl b
    · exact absurd hj ((htail_ok m).1 q r')
  have hss_inv : ∀ n, ((ss n).proposers p).crashed = false ∧
      (∀ a ∈ Q, ((ss n).acceptors a).crashed = false) ∧
      ((ss n).learners l).crashed = false := by
    intro n
    induction n with
    | zero => exact ⟨hp_live, hQ_live, hl_live⟩
    | succ n ih =>
      have hnd := hxs_nodel n
      have hpres := synodStep_preserve_of_delivery (qs := qs) (w := ss n) (act := xs n)
        hnd.1 hnd.2.1 hnd.2.2.1 hnd.2.2.2
      rw [(hexec n).2]
      exact ⟨(hpres.2.1 p).trans ih.1,
        fun a haQ => (hpres.2.2.1 a).trans (ih.2.1 a haQ),
        (hpres.2.2.2 l).trans ih.2.2⟩
  have hmsgs_mono : ∀ {n j}, n ≤ j → (ss n).msgs ⊆ (ss j).msgs := by
    intro n j hle
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    induction d with
    | zero => exact Finset.Subset.rfl
    | succ d ih =>
      rw [← Nat.add_assoc, (hexec (n + d)).2]
      exact fun m hm => mem_msgs_synodStep_of_mem (ih (Nat.le_add_right n d) hm)
        ((hxs_nodel (n + d)).1 m)
  have hex_fair : ∀ n (m : Msg Proposer Acceptor V)
      (act : SynodAction Proposer Acceptor Learner V),
      m ∈ (ss n).msgs → act ∈ soleLeaderMsgActs b p Q l m →
      ∃ j, n ≤ j ∧ xs j = act := by
    intro n m act hm hact_m
    have hts_m : m ∈ (ts n).msgs := by
      have hsub := hmsgs_mono (Nat.le_succ_of_le ((cumLen_strictMono hpos).id_le n))
      have hss_eq : ss (xls.cumLen n + 1) = ts n := hcum n
      exact (hss_eq ▸ hsub) hm
    have hmem : act ∈ soleLeaderSweep b p Q l (ts n) :=
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨m, Finset.mem_toList.mpr hts_m, hact_m⟩)
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
    have hn_le : n ≤ xls.cumLen n := (cumLen_strictMono hpos).id_le n
    exact ⟨(xls.cumLen n + i) + 1, by omega, (xls.flatten_get_add hi hpos).trans hget⟩
  have hlive : LiveAndLossless b p Q l ss xs :=
    { proposer_live := fun n => (hss_inv n).1
      quorum_live := fun a haQ n => (hss_inv n).2.1 a haQ
      learner_live := fun n => (hss_inv n).2.2
      no_drop_ballot := fun n m hm => absurd hm ((hxs_nodel n).1 m)
      fair_phase1a := fun n hm a haQ =>
        hex_fair n (.phase1a b) (.recvPhase1a a b) hm
          (by simp only [soleLeaderMsgActs, ↓reduceIte]
              exact List.mem_map_of_mem (Finset.mem_toList.mpr haQ))
      fair_phase1b := fun n a mv haQ hm =>
        hex_fair n (.phase1b a b mv) (.recvPhase1b p a b mv) hm
          (by simp only [soleLeaderMsgActs, true_and, haQ, ↓reduceIte, List.mem_singleton])
      fair_phase2a := fun n v hm a haQ =>
        hex_fair n (.phase2a b v) (.recvPhase2a a b v) hm
          (by simp only [soleLeaderMsgActs, ↓reduceIte]
              exact List.mem_map_of_mem (Finset.mem_toList.mpr haQ))
      fair_phase2b := fun n a v haQ hm =>
        hex_fair n (.phase2b a b v) (.recvPhase2b l a b v) hm
          (by simp only [soleLeaderMsgActs, true_and, haQ, ↓reduceIte, List.mem_singleton]) }
  obtain ⟨k, v, hlearnedAt, hlearned⟩ :=
    paxos_liveness_of_sole_leader_crashStop qs hr₀ hexec hQ rfl hbelow hno_higher hlive
  exact ⟨r, ss, xs, k, v, rfl, hexec, rfl, hbelow, hno_higher, hlive, hlearnedAt, hlearned⟩

end SoleLeader

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

private def deliverStep (s : NetState P S M V) (pkt : Packet P M) : NetState P S M V :=
  applyResult pkt.dest (π.onRecv pkt.src pkt.dest pkt.body (s.proc pkt.dest)) s

private lemma mTr_map_deliver {α : Type*} (f : α → Packet P M) {u : NetState P S M V}
    {as : List α} (hmem : ∀ a ∈ as, f a ∈ u.msgs) :
    let u' := as.foldl (fun w a => π.deliverStep w (f a)) u
    π.lts.MTr u (as.map fun a => .deliver (f a)) u' ∧ u.msgs ⊆ u'.msgs := by
  induction as generalizing u with
  | nil => exact ⟨LTS.MTr.refl, Finset.Subset.rfl⟩
  | cons a rest ih =>
    have htr : π.lts.Tr u (.deliver (f a)) (π.deliverStep u (f a)) :=
      ⟨hmem a List.mem_cons_self, rfl⟩
    have hsub1 : u.msgs ⊆ (π.deliverStep u (f a)).msgs := Finset.subset_union_left
    obtain ⟨hmtr_r, hsub_r⟩ := ih (fun x hx => hsub1 (hmem x (List.mem_cons_of_mem a hx)))
    exact ⟨LTS.MTr.stepL htr hmtr_r, hsub1.trans hsub_r⟩

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
  have hhalf_le : Fintype.card P / 2 ≤ (Finset.univ : Finset P).card := by
    rw [Finset.card_univ]; omega
  obtain ⟨Q₁, _, hQ₁_card⟩ := Finset.exists_subset_card_eq hhalf_le
  let Q₂ : Finset P := Finset.univ \ Q₁
  have hdisj : Disjoint Q₁ Q₂ := Finset.disjoint_sdiff
  have hQ₁_ge : Fintype.card P - t ≤ Q₁.card := by omega
  have hQ₂_ge : Fintype.card P - t ≤ Q₂.card := by
    have hcard₂_eq : Q₂.card = Fintype.card P - Q₁.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ Q₁), Finset.card_univ]
    omega
  exact not_synod_safe_of_disjoint_quorums π hdisj ⟨hsafe, hprog Q₁ hQ₁_ge, hprog Q₂ hQ₂_ge⟩

/-! ### Co-located Synod instantiated as an `AsyncQuorumProtocol` -/

/-- Co-located Single-Decree Synod node state when each process `p : P` plays proposer, acceptor,
and learner simultaneously. -/
@[ext]
structure SynodNodeState (P V : Type*) where
  /-- Co-located proposer state. -/
  prop : ProposerState P P V
  /-- Co-located acceptor state. -/
  acc : AcceptorState P V
  /-- Co-located learner state. -/
  learn : LearnerState P P V
  deriving @[expose] DecidableEq

/-- Co-located Single-Decree Synod protocol instantiated as an `AsyncQuorumProtocol` over a finite,
linearly ordered process set `P` and quorum system `qs : QuorumSystem P`. -/
@[expose] def synodQuorumProtocol {P V : Type*} [Fintype P] [LinearOrder P] [DecidableEq V]
    (qs : QuorumSystem P) :
    AsyncQuorumProtocol P (SynodNodeState P V) ℕ (Msg P P V) V where
  init _ v :=
    { prop := { input := v, round := none, proposed := false, promised := ∅, maxVote := none,
                crashed := false }
      acc := { maxBal := none, maxVoted := none, crashed := false }
      learn := { received := ∅, learned := none, crashed := false } }
  localEnabled _ r st :=
    st.state.prop.crashed = false ∧
      match st.state.prop.round with
      | none => True
      | some r₀ => r₀ < r
  onLocal p r st :=
    { nextState :=
        { st.state with
          prop := { st.state.prop with
            round := some r, proposed := false, promised := ∅, maxVote := none } }
      outgoing := Finset.univ.image fun q => (q, Msg.phase1a ⟨r, p⟩)
      decideVal := none }
  onRecv src dest body st :=
    match body with
    | .phase1a b =>
      if st.state.acc.crashed = false ∧ aboveMaxBal st.state.acc.maxBal b then
        { nextState := { st.state with acc := { st.state.acc with maxBal := some b } }
          outgoing := {(b.proposer, Msg.phase1b dest b st.state.acc.maxVoted)}
          decideVal := none }
      else { nextState := st.state, outgoing := ∅, decideVal := none }
    | .phase1b a b mv =>
      if st.state.prop.crashed = false ∧ src = a then
        match st.state.prop.round with
        | none => { nextState := st.state, outgoing := ∅, decideVal := none }
        | some r =>
          if b = ⟨r, dest⟩ ∧ a ∉ st.state.prop.promised then
            let promised' := insert a st.state.prop.promised
            let maxVote' := mergeVote st.state.prop.maxVote mv
            if !st.state.prop.proposed && decide (∃ Q ∈ qs.quorums, Q ⊆ promised') then
              let val := match maxVote' with
                | some vt => vt.value
                | none => st.state.prop.input
              { nextState :=
                  { st.state with
                    prop := { st.state.prop with
                      proposed := true, promised := promised', maxVote := maxVote' } }
                outgoing := Finset.univ.image fun q => (q, Msg.phase2a ⟨r, dest⟩ val)
                decideVal := none }
            else
              { nextState :=
                  { st.state with
                    prop := { st.state.prop with promised := promised', maxVote := maxVote' } }
                outgoing := ∅
                decideVal := none }
          else { nextState := st.state, outgoing := ∅, decideVal := none }
      else { nextState := st.state, outgoing := ∅, decideVal := none }
    | .phase2a b v =>
      if st.state.acc.crashed = false ∧ allowsVote st.state.acc.maxBal b then
        { nextState :=
            { st.state with
              acc := { st.state.acc with maxBal := some b, maxVoted := some ⟨b, v⟩ } }
          outgoing := Finset.univ.image fun q => (q, Msg.phase2b dest b v)
          decideVal := none }
      else { nextState := st.state, outgoing := ∅, decideVal := none }
    | .phase2b a b v =>
      if st.state.learn.crashed = false ∧ src = a then
        let received' := insert ⟨a, b, v⟩ st.state.learn.received
        let learned' :=
          if st.state.learn.learned.isNone &&
              decide (∃ Q ∈ qs.quorums, ∀ a' ∈ Q, ⟨a', b, v⟩ ∈ received') then
            some v
          else st.state.learn.learned
        { nextState :=
            { st.state with
              learn := { st.state.learn with received := received', learned := learned' } }
          outgoing := ∅
          decideVal := learned' }
      else { nextState := st.state, outgoing := ∅, decideVal := none }

private def netToSynod {P V : Type*} [DecidableEq P] [DecidableEq V]
    (s : NetState P (SynodNodeState P V) (Msg P P V) V) : SynodState P P P V where
  msgs := s.msgs.image Packet.body
  proposers p := (s.proc p).state.prop
  acceptors a := (s.proc a).state.acc
  learners l := (s.proc l).state.learn

private lemma union_image_broadcastPairs {P M : Type*} [Fintype P] [DecidableEq P] [DecidableEq M]
    (pkts : Finset (Packet P M)) (p : P) (m : M) :
    (pkts ∪ (Finset.univ.image fun q : P => (q, m)).image fun db => ⟨p, db.1, db.2⟩).image
        Packet.body =
      insert m (pkts.image Packet.body) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_union, Finset.mem_insert, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨pkt, hold | ⟨db, ⟨q, rfl⟩, rfl⟩, rfl⟩
    · exact Or.inr ⟨pkt, hold, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨pkt, hold, rfl⟩)
    · exact ⟨⟨p, p, x⟩, Or.inr ⟨(p, x), ⟨p, rfl⟩, rfl⟩, rfl⟩
    · exact ⟨pkt, Or.inl hold, rfl⟩

private lemma union_image_singleton_pair {P M : Type*} [DecidableEq P] [DecidableEq M]
    (pkts : Finset (Packet P M)) (p q : P) (m : M) :
    (pkts ∪ ({(q, m)} : Finset (P × M)).image fun db => ⟨p, db.1, db.2⟩).image Packet.body =
      insert m (pkts.image Packet.body) := by
  ext x
  simp only [Finset.image_singleton, Finset.mem_image, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_insert]
  constructor
  · rintro ⟨pkt, hold | rfl, rfl⟩
    · exact Or.inr ⟨pkt, hold, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨pkt, hold, rfl⟩)
    · exact ⟨⟨p, q, x⟩, Or.inr rfl, rfl⟩
    · exact ⟨pkt, Or.inl hold, rfl⟩

private lemma out_eq_after_nonlearn {V : Type*} (out learned : Option V)
    (h : out = learned) :
    (if out.isNone then none else out) = learned := by
  subst h
  cases out <;> rfl

private lemma out_preserved_of_nonlearn {P V : Type*} [DecidableEq P] [DecidableEq V]
    {s : NetState P (SynodNodeState P V) (Msg P P V) V}
    (hout : ∀ q, (s.proc q).out = (s.proc q).state.learn.learned)
    {dest : P} {nst : SynodNodeState P V} {out : Finset (P × Msg P P V)}
    (hl_eq : nst.learn.learned = (s.proc dest).state.learn.learned) :
    ∀ q, ((AsyncQuorumProtocol.applyResult dest
      { nextState := nst, outgoing := out, decideVal := none } s).proc q).out =
      ((AsyncQuorumProtocol.applyResult dest
        { nextState := nst, outgoing := out, decideVal := none }
          s).proc q).state.learn.learned := by
  intro q
  by_cases hqd : q = dest
  · subst hqd
    simp only [AsyncQuorumProtocol.applyResult, ↓reduceIte, hl_eq]
    exact out_eq_after_nonlearn _ _ (hout q)
  · simp only [AsyncQuorumProtocol.applyResult, hqd, ↓reduceIte]
    exact hout q

private lemma netToSynod_applyResult {P V : Type*} [DecidableEq P] [DecidableEq V]
    (s : NetState P (SynodNodeState P V) (Msg P P V) V)
    (dest : P) (res : StepResult P (SynodNodeState P V) (Msg P P V) V)
    (msgs' : Finset (Msg P P V))
    (hmsgs : (s.msgs ∪ res.outgoing.image fun db => ⟨dest, db.1, db.2⟩).image Packet.body =
      msgs') :
    netToSynod (AsyncQuorumProtocol.applyResult dest res s) =
      { msgs := msgs'
        proposers := fun x =>
          if x = dest then res.nextState.prop else (netToSynod s).proposers x
        acceptors := fun x =>
          if x = dest then res.nextState.acc else (netToSynod s).acceptors x
        learners := fun x =>
          if x = dest then res.nextState.learn else (netToSynod s).learners x } := by
  refine SynodState.ext hmsgs (funext fun x => ?_) (funext fun x => ?_) (funext fun x => ?_) <;>
    (dsimp only [netToSynod, AsyncQuorumProtocol.applyResult];
      by_cases hxd : x = dest <;> simp only [hxd, ↓reduceIte])

private lemma ite_self_field {P α : Type*} [DecidableEq P] (f : P → α) (dest : P) {val : α}
    (hval : val = f dest) :
    (fun x => if x = dest then val else f x) = f := by
  funext x; by_cases h : x = dest <;> simp only [h, ↓reduceIte, hval]

private lemma applyResult_noop_sim {P V : Type*} [DecidableEq P] [DecidableEq V]
    {s : NetState P (SynodNodeState P V) (Msg P P V) V}
    (hout : ∀ q, (s.proc q).out = (s.proc q).state.learn.learned) (dest : P) :
    let u := AsyncQuorumProtocol.applyResult dest
      { nextState := (s.proc dest).state, outgoing := ∅, decideVal := none } s
    (∀ q, (u.proc q).out = (u.proc q).state.learn.learned) ∧
      netToSynod u = netToSynod s := by
  refine ⟨out_preserved_of_nonlearn hout rfl, ?_⟩
  rw [netToSynod_applyResult s dest _ (netToSynod s).msgs
    (by simp only [netToSynod, Finset.image_empty, Finset.union_empty])]
  exact SynodState.ext rfl (ite_self_field _ dest rfl) (ite_self_field _ dest rfl)
    (ite_self_field _ dest rfl)

private lemma netToSynod_acc_update {P V : Type*} [DecidableEq P] [DecidableEq V]
    (s : NetState P (SynodNodeState P V) (Msg P P V) V)
    (dest : P) (ast : AcceptorState P V) (out : Finset (P × Msg P P V))
    (msgs' : Finset (Msg P P V))
    (hmsgs : (s.msgs ∪ out.image fun db => ⟨dest, db.1, db.2⟩).image Packet.body = msgs') :
    netToSynod (AsyncQuorumProtocol.applyResult dest
      { nextState := { (s.proc dest).state with acc := ast },
        outgoing := out, decideVal := none } s) =
      { (netToSynod s) with
        msgs := msgs'
        acceptors := fun x => if x = dest then ast else ((netToSynod s).acceptors x) } := by
  rw [netToSynod_applyResult s dest _ msgs' hmsgs]
  exact SynodState.ext rfl (ite_self_field _ dest rfl) rfl (ite_self_field _ dest rfl)

private lemma netToSynod_prop_update {P V : Type*} [DecidableEq P] [DecidableEq V]
    (s : NetState P (SynodNodeState P V) (Msg P P V) V)
    (dest : P) (pst : ProposerState P P V) (out : Finset (P × Msg P P V))
    (msgs' : Finset (Msg P P V))
    (hmsgs : (s.msgs ∪ out.image fun db => ⟨dest, db.1, db.2⟩).image Packet.body = msgs') :
    netToSynod (AsyncQuorumProtocol.applyResult dest
      { nextState := { (s.proc dest).state with prop := pst },
        outgoing := out, decideVal := none } s) =
      { (netToSynod s) with
        msgs := msgs'
        proposers := fun x => if x = dest then pst else ((netToSynod s).proposers x) } := by
  rw [netToSynod_applyResult s dest _ msgs' hmsgs]
  exact SynodState.ext rfl rfl (ite_self_field _ dest rfl) (ite_self_field _ dest rfl)

private lemma netToSynod_acc_recv_sim {P V : Type*} [LinearOrder P] [DecidableEq V]
    (qs : QuorumSystem P)
    (s : NetState P (SynodNodeState P V) (Msg P P V) V)
    (hout : ∀ q, (s.proc q).out = (s.proc q).state.learn.learned)
    (dest : P) (guard : Bool) (ast : AcceptorState P V) (out : Finset (P × Msg P P V))
    (emit : Msg P P V) (sact : SynodAction P P P V)
    (hen_live : (s.proc dest).state.acc.crashed = false → synodEnabled (netToSynod s) sact)
    (hstep_eq : synodStep qs (netToSynod s) sact =
      if guard then
        { (netToSynod s) with
          msgs := insert emit (netToSynod s).msgs
          acceptors := fun x => if x = dest then ast else (netToSynod s).acceptors x }
      else netToSynod s)
    (hmsgs : (s.msgs ∪ out.image fun db => ⟨dest, db.1, db.2⟩).image Packet.body =
      insert emit (netToSynod s).msgs) :
    let u := AsyncQuorumProtocol.applyResult dest
      (if (s.proc dest).state.acc.crashed = false ∧ guard = true then
        { nextState := { (s.proc dest).state with acc := ast }, outgoing := out, decideVal := none }
      else { nextState := (s.proc dest).state, outgoing := ∅, decideVal := none }) s
    (∀ q, (u.proc q).out = (u.proc q).state.learn.learned) ∧
      (netToSynod u = netToSynod s ∨
        ∃ sact', (synodLts qs).Tr (netToSynod s) sact' (netToSynod u)) := by
  by_cases hguard : (s.proc dest).state.acc.crashed = false ∧ guard = true
  · dsimp only []
    rw [ite_eq_left hguard]
    refine ⟨out_preserved_of_nonlearn hout rfl,
      Or.inr ⟨sact, ⟨hen_live hguard.1, ?_⟩⟩⟩
    rw [hstep_eq, ite_eq_left hguard.2]
    exact netToSynod_acc_update s dest ast out _ hmsgs
  · dsimp only []
    rw [ite_eq_right hguard]
    obtain ⟨ho, heq⟩ := applyResult_noop_sim hout dest
    by_cases hlive : (s.proc dest).state.acc.crashed = false
    · refine ⟨ho, Or.inr ⟨sact, ⟨hen_live hlive, ?_⟩⟩⟩
      rw [hstep_eq, ite_eq_right (fun hg => hguard ⟨hlive, hg⟩)]
      exact heq
    · exact ⟨ho, Or.inl heq⟩

private lemma netToSynod_step {P V : Type*} [Fintype P] [LinearOrder P] [DecidableEq V]
    (qs : QuorumSystem P)
    {s s' : NetState P (SynodNodeState P V) (Msg P P V) V}
    {act : NetAction P ℕ (Msg P P V)}
    (htr : (synodQuorumProtocol qs).lts.Tr s act s')
    (hout : ∀ q, (s.proc q).out = (s.proc q).state.learn.learned) :
    (∀ q, (s'.proc q).out = (s'.proc q).state.learn.learned) ∧
      (netToSynod s' = netToSynod s ∨
        ∃ sact, (synodLts qs).Tr (netToSynod s) sact (netToSynod s')) := by
  cases act with
  | localStep p r =>
    obtain ⟨hen, rfl⟩ := htr
    exact ⟨out_preserved_of_nonlearn hout rfl,
      Or.inr ⟨.prepare p r, ⟨hen,
        netToSynod_prop_update s p _ _ _ (union_image_broadcastPairs s.msgs p _)⟩⟩⟩
  | deliver pkt =>
    obtain ⟨hpkt_mem, rfl⟩ := htr
    have hbody_mem : pkt.body ∈ (netToSynod s).msgs :=
      Finset.mem_image.mpr ⟨pkt, hpkt_mem, rfl⟩
    rcases pkt with ⟨src, dest, body⟩
    cases body with
    | phase1a b =>
      exact netToSynod_acc_recv_sim qs s hout dest
        (aboveMaxBal (s.proc dest).state.acc.maxBal b)
        { (s.proc dest).state.acc with maxBal := some b }
        {(b.proposer, Msg.phase1b dest b (s.proc dest).state.acc.maxVoted)}
        (Msg.phase1b dest b (s.proc dest).state.acc.maxVoted)
        (.recvPhase1a dest b)
        (fun hlive => ⟨hlive, hbody_mem⟩) rfl
        (union_image_singleton_pair s.msgs dest b.proposer _)
    | phase1b a b mv =>
      dsimp only [synodQuorumProtocol]
      by_cases hguard : (s.proc dest).state.prop.crashed = false ∧ src = a
      · rw [ite_eq_left hguard]
        have hprop_ns : (netToSynod s).proposers dest = (s.proc dest).state.prop := rfl
        cases hround : (s.proc dest).state.prop.round with
        | none =>
          obtain ⟨ho, heq⟩ := applyResult_noop_sim hout dest
          refine ⟨ho, Or.inr ⟨.recvPhase1b dest a b mv, ⟨⟨hguard.1, hbody_mem⟩, ?_⟩⟩⟩
          dsimp only [synodStep, synodStepCore]
          rw [hprop_ns, hround]
          exact heq
        | some r =>
          dsimp only []
          by_cases hnew : b = ⟨r, dest⟩ ∧ a ∉ (s.proc dest).state.prop.promised
          · rw [ite_eq_left hnew]
            by_cases hq_cond : (!(s.proc dest).state.prop.proposed &&
                decide (∃ Q ∈ qs.quorums, Q ⊆ insert a (s.proc dest).state.prop.promised)) = true
            · rw [ite_eq_left hq_cond]
              refine ⟨out_preserved_of_nonlearn hout rfl,
                Or.inr ⟨.recvPhase1b dest a b mv, ⟨⟨hguard.1, hbody_mem⟩, ?_⟩⟩⟩
              dsimp only [synodStep, synodStepCore]
              rw [hprop_ns, hround]
              dsimp only []
              rw [ite_eq_left hnew, ite_eq_left hq_cond]
              exact netToSynod_prop_update s dest _ _ _
                (union_image_broadcastPairs s.msgs dest _)
            · rw [ite_eq_right hq_cond]
              refine ⟨out_preserved_of_nonlearn hout rfl,
                Or.inr ⟨.recvPhase1b dest a b mv, ⟨⟨hguard.1, hbody_mem⟩, ?_⟩⟩⟩
              dsimp only [synodStep, synodStepCore]
              rw [hprop_ns, hround]
              dsimp only []
              rw [ite_eq_left hnew, ite_eq_right hq_cond]
              exact netToSynod_prop_update s dest _ _ _
                (by simp only [netToSynod, Finset.image_empty, Finset.union_empty])
          · rw [ite_eq_right hnew]
            obtain ⟨ho, heq⟩ := applyResult_noop_sim hout dest
            refine ⟨ho, Or.inr ⟨.recvPhase1b dest a b mv, ⟨⟨hguard.1, hbody_mem⟩, ?_⟩⟩⟩
            dsimp only [synodStep, synodStepCore]
            rw [hprop_ns, hround]
            dsimp only []
            rw [ite_eq_right hnew]
            exact heq
      · rw [ite_eq_right hguard]
        obtain ⟨ho, heq⟩ := applyResult_noop_sim hout dest
        exact ⟨ho, Or.inl heq⟩
    | phase2a b v =>
      exact netToSynod_acc_recv_sim qs s hout dest
        (allowsVote (s.proc dest).state.acc.maxBal b)
        { (s.proc dest).state.acc with maxBal := some b, maxVoted := some ⟨b, v⟩ }
        (Finset.univ.image fun q => (q, Msg.phase2b dest b v))
        (Msg.phase2b dest b v)
        (.recvPhase2a dest b v)
        (fun hlive => ⟨hlive, hbody_mem⟩) rfl
        (union_image_broadcastPairs s.msgs dest _)
    | phase2b a b v =>
      dsimp only [synodQuorumProtocol]
      by_cases hguard : (s.proc dest).state.learn.crashed = false ∧ src = a
      · rw [ite_eq_left hguard]
        refine ⟨fun q => ?_, Or.inr ⟨.recvPhase2b dest a b v, ⟨⟨hguard.1, hbody_mem⟩, ?_⟩⟩⟩
        · dsimp only [AsyncQuorumProtocol.applyResult]
          rcases eq_or_ne q dest with rfl | hqd
          · simp only [↓reduceIte]; rw [hout q]; cases (s.proc q).state.learn.learned <;> rfl
          · simp only [hqd, ↓reduceIte]; exact hout q
        · rw [netToSynod_applyResult s dest _ (netToSynod s).msgs
            (by simp only [netToSynod, Finset.image_empty, Finset.union_empty])]
          refine SynodState.ext rfl (ite_self_field _ dest rfl) (ite_self_field _ dest rfl)
            (funext fun x => ?_)
          dsimp only [synodStep, synodStepCore, netToSynod]
          by_cases hxd : x = dest <;> simp only [hxd, ↓reduceIte]
          congr
      · rw [ite_eq_right hguard]
        obtain ⟨ho, heq⟩ := applyResult_noop_sim hout dest
        exact ⟨ho, Or.inl heq⟩
  | stutter =>
    obtain rfl := htr
    exact ⟨hout, Or.inl rfl⟩

private lemma netToSynod_reach {P V : Type*} [Fintype P] [LinearOrder P] [DecidableEq V]
    (qs : QuorumSystem P) {inp : P → V}
    {s : NetState P (SynodNodeState P V) (Msg P P V) V}
    (hreach : (synodQuorumProtocol qs).Reachable inp s) :
    Reachable qs inp (netToSynod s) ∧
      ∀ q, (s.proc q).out = ((netToSynod s).learners q).learned := by
  obtain ⟨xl, hmtr⟩ := hreach
  have hgen : ∀ {u u' : NetState P (SynodNodeState P V) (Msg P P V) V} {yl},
      (synodQuorumProtocol qs).lts.MTr u yl u' →
      Reachable qs inp (netToSynod u) →
      (∀ q, (u.proc q).out = (u.proc q).state.learn.learned) →
      Reachable qs inp (netToSynod u') ∧
        ∀ q, (u'.proc q).out = (u'.proc q).state.learn.learned := by
    intro u u' yl hm
    induction hm with
    | refl => exact fun hr ho => ⟨hr, ho⟩
    | stepL hstep _ ih =>
      intro hr ho
      obtain ⟨ho', hsim⟩ := netToSynod_step qs hstep ho
      rcases hsim with heq | ⟨sact, hstr⟩
      · exact ih (heq ▸ hr) ho'
      · exact ih (hr.trans ⟨[sact], LTS.MTr.single _ hstr⟩) ho'
  have hinit_eq : netToSynod ((synodQuorumProtocol qs).start inp) = initState inp := by
    refine SynodState.ext ?_ rfl rfl rfl
    simp only [netToSynod, AsyncQuorumProtocol.start, Finset.image_empty, initState]
  have hr₀ : Reachable qs inp (netToSynod ((synodQuorumProtocol qs).start inp)) := by
    rw [hinit_eq]
    exact ⟨[], LTS.MTr.refl⟩
  exact hgen hmtr hr₀ (fun _ => rfl)

private lemma deliver_fanout_acc {P V : Type*} [Fintype P] [LinearOrder P] [DecidableEq V]
    (qs : QuorumSystem P) (p₀ : P) (msg : Msg P P V)
    (acc₀ ast : AcceptorState P V) (reply : P → Msg P P V)
    (hrecv : ∀ (a : P) (st : NodeProcState (SynodNodeState P V) V),
      st.state.acc = acc₀ →
      ∃ out, (synodQuorumProtocol (V := V) qs).onRecv p₀ a msg st =
        { nextState := { st.state with acc := ast }, outgoing := out, decideVal := none } ∧
        (p₀, reply a) ∈ out)
    {as : List P} (hnodup : as.Nodup)
    {u : NetState P (SynodNodeState P V) (Msg P P V) V}
    (hall : ∀ x ∈ as, (⟨p₀, x, msg⟩ : Packet P (Msg P P V)) ∈ u.msgs ∧
      (u.proc x).state.acc = acc₀) :
    let π := synodQuorumProtocol (V := V) qs
    let u' := as.foldl (fun w a => π.deliverStep w ⟨p₀, a, msg⟩) u
    π.lts.MTr u (as.map fun a => .deliver ⟨p₀, a, msg⟩) u' ∧
      (∀ q, (u'.proc q).state.prop = (u.proc q).state.prop ∧
        (u'.proc q).state.learn = (u.proc q).state.learn) ∧
      (∀ x ∉ as, (u'.proc x).state.acc = (u.proc x).state.acc) ∧
      (∀ a ∈ as, (u'.proc a).state.acc = ast ∧
        (⟨a, p₀, reply a⟩ : Packet P (Msg P P V)) ∈ u'.msgs) := by
  let π := synodQuorumProtocol (V := V) qs
  have ⟨hmtr, _⟩ := π.mTr_map_deliver (fun a => ⟨p₀, a, msg⟩) (fun x hx => (hall x hx).1)
  refine ⟨hmtr, ?_⟩
  have hstate : ∀ (as : List P), as.Nodup →
      ∀ (u : NetState P (SynodNodeState P V) (Msg P P V) V),
      (∀ x ∈ as, (u.proc x).state.acc = acc₀) →
      let u' := as.foldl (fun w a => π.deliverStep w ⟨p₀, a, msg⟩) u
      (∀ q, (u'.proc q).state.prop = (u.proc q).state.prop ∧
        (u'.proc q).state.learn = (u.proc q).state.learn) ∧
      (∀ x ∉ as, (u'.proc x).state.acc = (u.proc x).state.acc) ∧
      (∀ a ∈ as, (u'.proc a).state.acc = ast ∧
        (⟨a, p₀, reply a⟩ : Packet P (Msg P P V)) ∈ u'.msgs) := by
    intro bs hnd
    induction bs with
    | nil =>
      exact fun _ _ => ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
    | cons a rest ih =>
      obtain ⟨ha_not, hnd_r⟩ := List.nodup_cons.mp hnd
      intro w hw
      obtain ⟨out, hon, hrep_mem⟩ := hrecv a (w.proc a) (hw a List.mem_cons_self)
      let w1 := π.deliverStep w ⟨p₀, a, msg⟩
      have hw1_pl : ∀ q, (w1.proc q).state.prop = (w.proc q).state.prop ∧
          (w1.proc q).state.learn = (w.proc q).state.learn := by
        intro q
        dsimp only [w1, AsyncQuorumProtocol.deliverStep, AsyncQuorumProtocol.applyResult]
        rw [hon]
        by_cases hqa : q = a <;> simp only [hqa, ↓reduceIte, and_self]
      have hw1_other : ∀ x, x ≠ a → (w1.proc x).state.acc = (w.proc x).state.acc := by
        intro x hxa
        dsimp only [w1, AsyncQuorumProtocol.deliverStep, AsyncQuorumProtocol.applyResult]
        simp only [hxa, ↓reduceIte]
      have hw1_a : (w1.proc a).state.acc = ast ∧
          (⟨a, p₀, reply a⟩ : Packet P (Msg P P V)) ∈ w1.msgs := by
        dsimp only [w1, AsyncQuorumProtocol.deliverStep, AsyncQuorumProtocol.applyResult]
        rw [hon, ite_eq_left rfl]
        exact ⟨rfl, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(p₀, reply a), hrep_mem, rfl⟩)⟩
      have hsub_r : ∀ (xs : List P) (z₀ : NetState P (SynodNodeState P V) (Msg P P V) V),
          z₀.msgs ⊆ (xs.foldl (fun z x => π.deliverStep z ⟨p₀, x, msg⟩) z₀).msgs := by
        intro xs
        induction xs with
        | nil => exact fun _ => Finset.Subset.rfl
        | cons x xs' ihx =>
          intro z₀
          exact Finset.subset_union_left.trans (ihx (π.deliverStep z₀ ⟨p₀, x, msg⟩))
      obtain ⟨hpl_r, hnot_r, hin_r⟩ := ih hnd_r w1 fun x hx =>
        (hw1_other x (fun h => ha_not (h ▸ hx))).trans (hw x (List.mem_cons_of_mem a hx))
      refine ⟨fun q => ⟨(hpl_r q).1.trans (hw1_pl q).1, (hpl_r q).2.trans (hw1_pl q).2⟩,
        fun x hx => (hnot_r x fun h => hx (List.mem_cons_of_mem a h)).trans
          (hw1_other x fun h => hx (h ▸ List.mem_cons_self)),
        fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx_r
      · exact ⟨(hnot_r x ha_not).trans hw1_a.1, hsub_r rest w1 hw1_a.2⟩
      · exact hin_r x hx_r
  exact hstate as hnodup u (fun x hx => (hall x hx).2)

/-- Crash-stop step for co-located `synodQuorumProtocol` (a crash-stop step towards [Lamport1998]
§2 and [Lamport2001] §2, not the crash-recovery cited protocol): for every quorum system
`qs : QuorumSystem P` over a finite, linearly ordered process set `P` (in particular
`majorityQuorums hmaj` whenever `2 * t < Fintype.card P`), `synodQuorumProtocol qs` satisfies both
`SafeConsensus` and single-quorum progress `CanDecideIn Q` on every quorum `Q ∈ qs.quorums`. -/
theorem synodQuorumProtocol_safeSingleQuorum_crashStop {P V : Type*} [Fintype P] [LinearOrder P]
    [DecidableEq V] (qs : QuorumSystem P) :
    (synodQuorumProtocol (V := V) qs).SafeConsensus ∧
      ∀ Q ∈ qs.quorums, (synodQuorumProtocol (V := V) qs).CanDecideIn Q := by
  let π := synodQuorumProtocol (V := V) qs
  refine ⟨?_, ?_⟩
  · intro inp s hreach
    obtain ⟨hr, hout⟩ := netToSynod_reach qs hreach
    refine ⟨fun p₁ p₂ v₁ v₂ h₁ h₂ => ?_, fun p v hpv => ?_⟩
    · rw [hout p₁] at h₁
      rw [hout p₂] at h₂
      obtain ⟨b₁, hl₁⟩ := hr.learned_eq_some_iff.mp h₁
      obtain ⟨b₂, hl₂⟩ := hr.learned_eq_some_iff.mp h₂
      exact paxos_agreement_crashStop qs hr hl₁ hl₂
    · rw [hout p] at hpv
      exact paxos_validity_crashStop qs hr hpv
  · intro Q₀ hQ₀ v
    obtain ⟨p₀, hp₀Q⟩ := qs.quorum_nonempty hQ₀
    let b : Ballot P := ⟨0, p₀⟩
    let qList := Q₀.toList
    let s₀ := π.start fun _ => v
    let act₀ : NetAction P ℕ (Msg P P V) := .localStep p₀ 0
    let s₁ := AsyncQuorumProtocol.applyResult p₀ (π.onLocal p₀ 0 (s₀.proc p₀)) s₀
    have htr₀ : π.lts.Tr s₀ act₀ s₁ := ⟨⟨rfl, trivial⟩, rfl⟩
    let propOf (S : Finset P) : ProposerState P P V :=
      { input := v
        round := some 0
        proposed := decide (∃ Q ∈ qs.quorums, Q ⊆ S)
        promised := S
        maxVote := none
        crashed := false }
    have hempty_no_q : decide (∃ Q ∈ qs.quorums, Q ⊆ (∅ : Finset P)) = false := by
      simp only [decide_eq_false_iff_not]
      rintro ⟨Q, hQ, hsub⟩
      obtain ⟨x, hx⟩ := qs.quorum_nonempty hQ
      exact Finset.notMem_empty x (hsub hx)
    have hs₁_prop : (s₁.proc p₀).state.prop = propOf ∅ := by
      dsimp only [s₁, AsyncQuorumProtocol.applyResult, π, synodQuorumProtocol, s₀,
        AsyncQuorumProtocol.start, propOf]
      rw [hempty_no_q, ite_eq_left rfl]
    have hs₁_learn : (s₁.proc p₀).state.learn.crashed = false := by
      dsimp only [s₁, AsyncQuorumProtocol.applyResult, π, synodQuorumProtocol, s₀,
        AsyncQuorumProtocol.start]
      simp only [↓reduceIte]
    have hs₁_as : ∀ x ∈ qList, (⟨p₀, x, Msg.phase1a b⟩ : Packet P (Msg P P V)) ∈ s₁.msgs ∧
        (s₁.proc x).state.acc = { maxBal := none, maxVoted := none, crashed := false } := by
      intro x _
      refine ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x, Msg.phase1a b),
        Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, rfl⟩), ?_⟩
      dsimp only [s₁, AsyncQuorumProtocol.applyResult, π, synodQuorumProtocol, s₀,
        AsyncQuorumProtocol.start]
      by_cases hxp : x = p₀ <;> simp only [hxp, ↓reduceIte]
    -- Phase 1a fanout across `qList`:
    obtain ⟨hmtr_1a, hs₂_pl, _, hs₂_in⟩ :=
      deliver_fanout_acc qs p₀ (.phase1a b)
        { maxBal := none, maxVoted := none, crashed := false }
        { maxBal := some b, maxVoted := none, crashed := false }
        (fun a => .phase1b a b none)
        (fun a st hacc => by
          refine ⟨{(b.proposer, .phase1b a b none)}, ?_, Finset.mem_singleton_self _⟩
          dsimp only [synodQuorumProtocol]
          rw [hacc]
          rfl)
        Q₀.nodup_toList hs₁_as
    set s₂ := qList.foldl (fun w a => π.deliverStep w ⟨p₀, a, .phase1a b⟩) s₁
    -- Phase 1b fan-in to `p₀` across `qList`:
    have hstep_1b : ∀ (u : NetState P (SynodNodeState P V) (Msg P P V) V) (S : Finset P) (a : P),
        (u.proc p₀).state.prop = propOf S →
        (decide (∃ Q ∈ qs.quorums, Q ⊆ S) = true →
          ∀ x : P, (⟨p₀, x, Msg.phase2a b v⟩ : Packet P (Msg P P V)) ∈ u.msgs) →
        let u1 := π.deliverStep u ⟨a, p₀, .phase1b a b none⟩
        (∀ x : P, (u1.proc x).state.acc = (u.proc x).state.acc ∧
          (u1.proc x).state.learn = (u.proc x).state.learn) ∧
        (u1.proc p₀).state.prop = propOf (insert a S) ∧
        (decide (∃ Q ∈ qs.quorums, Q ⊆ insert a S) = true →
          ∀ x : P, (⟨p₀, x, Msg.phase2a b v⟩ : Packet P (Msg P P V)) ∈ u1.msgs) := by
      intro u S a hpS h2a
      dsimp only [AsyncQuorumProtocol.deliverStep, AsyncQuorumProtocol.applyResult, π,
        synodQuorumProtocol]
      have hg : (u.proc p₀).state.prop.crashed = false ∧ a = a := ⟨by rw [hpS], rfl⟩
      rw [ite_eq_left hg, hpS]
      dsimp only [propOf, mergeVote]
      by_cases haS : a ∈ S
      · rw [ite_eq_right (fun h : b = ⟨0, p₀⟩ ∧ a ∉ S => h.2 haS), Finset.insert_eq_of_mem haS]
        exact ⟨fun x => by by_cases hx : x = p₀ <;> simp only [hx, ↓reduceIte, and_self],
          by rw [ite_eq_left rfl]; exact hpS,
          fun hq x => Finset.mem_union_left _ (h2a hq x)⟩
      · rw [ite_eq_left (⟨rfl, haS⟩ : b = ⟨0, p₀⟩ ∧ a ∉ S)]
        by_cases hqS : ∃ Q ∈ qs.quorums, Q ⊆ S
        · have hdS : decide (∃ Q ∈ qs.quorums, Q ⊆ S) = true := decide_eq_true hqS
          have hd_ins : decide (∃ Q ∈ qs.quorums, Q ⊆ insert a S) = true := by
            obtain ⟨Q, hQ, hsub⟩ := hqS
            exact decide_eq_true ⟨Q, hQ, hsub.trans (Finset.subset_insert a S)⟩
          simp only [hdS, hd_ins, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          exact ⟨fun x => by by_cases hx : x = p₀ <;> simp only [hx, ↓reduceIte, and_self],
            trivial, fun _ x => Finset.mem_union_left _ (h2a hdS x)⟩
        · have hdS : decide (∃ Q ∈ qs.quorums, Q ⊆ S) = false := decide_eq_false hqS
          by_cases hq_ins : ∃ Q ∈ qs.quorums, Q ⊆ insert a S
          · have hd_ins : decide (∃ Q ∈ qs.quorums, Q ⊆ insert a S) = true :=
              decide_eq_true hq_ins
            simp only [hdS, hd_ins, Bool.not_false, Bool.true_and, ↓reduceIte]
            exact ⟨fun x => by by_cases hx : x = p₀ <;> simp only [hx, ↓reduceIte, and_self],
              trivial,
              fun _ x => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x, .phase2a b v),
                Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, rfl⟩)⟩
          · have hd_ins : decide (∃ Q ∈ qs.quorums, Q ⊆ insert a S) = false :=
              decide_eq_false hq_ins
            simp only [hdS, hd_ins, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
            exact ⟨fun x => by by_cases hx : x = p₀ <;> simp only [hx, ↓reduceIte, and_self],
              trivial, nofun⟩
    have hloop_1b : ∀ (as : List P) (u : NetState P (SynodNodeState P V) (Msg P P V) V)
        (S : Finset P),
        (u.proc p₀).state.prop = propOf S →
        (decide (∃ Q ∈ qs.quorums, Q ⊆ S) = true →
          ∀ x : P, (⟨p₀, x, Msg.phase2a b v⟩ : Packet P (Msg P P V)) ∈ u.msgs) →
        let u' := as.foldl (fun w a => π.deliverStep w ⟨a, p₀, .phase1b a b none⟩) u
        let S' := as.foldl (fun acc a => insert a acc) S
        (∀ x : P, (u'.proc x).state.acc = (u.proc x).state.acc ∧
          (u'.proc x).state.learn = (u.proc x).state.learn) ∧
        S ⊆ S' ∧ (∀ a ∈ as, a ∈ S') ∧
        (decide (∃ Q ∈ qs.quorums, Q ⊆ S') = true →
          ∀ x : P, (⟨p₀, x, Msg.phase2a b v⟩ : Packet P (Msg P P V)) ∈ u'.msgs) := by
      intro as
      induction as with
      | nil =>
        exact fun _ _ _ h2a =>
          ⟨fun _ => ⟨rfl, rfl⟩, Finset.Subset.rfl, fun _ h => absurd h List.not_mem_nil, h2a⟩
      | cons a rest ih =>
        intro u S hpS h2a
        obtain ⟨hal1, hp1, h2a1⟩ := hstep_1b u S a hpS h2a
        obtain ⟨hal_r, hsub_r, hmem_r, h2a_r⟩ := ih _ (insert a S) hp1 h2a1
        refine ⟨fun x => ⟨(hal_r x).1.trans (hal1 x).1, (hal_r x).2.trans (hal1 x).2⟩,
          (Finset.subset_insert a S).trans hsub_r, fun x hx => ?_, h2a_r⟩
        rcases List.mem_cons.mp hx with rfl | hx_r
        · exact hsub_r (Finset.mem_insert_self x S)
        · exact hmem_r x hx_r
    have ⟨hmtr_1b, _⟩ := π.mTr_map_deliver (u := s₂) (fun a => ⟨a, p₀, .phase1b a b none⟩)
      (fun x hx => (hs₂_in x hx).2)
    obtain ⟨hs₃_al, _, hs₃_mem, hs₃_2a_imp⟩ := hloop_1b qList s₂ ∅
      ((hs₂_pl p₀).1.trans hs₁_prop) (by rw [hempty_no_q]; exact nofun)
    set s₃ := qList.foldl (fun w a => π.deliverStep w ⟨a, p₀, .phase1b a b none⟩) s₂
    have hs₃_2a_msgs : ∀ x : P, (⟨p₀, x, Msg.phase2a b v⟩ : Packet P (Msg P P V)) ∈ s₃.msgs :=
      hs₃_2a_imp (decide_eq_true ⟨Q₀, hQ₀, fun a haQ => hs₃_mem a (Finset.mem_toList.mpr haQ)⟩)
    -- Phase 2a fanout across `qList`:
    have hal_b : allowsVote (some b) b = true := by
      simp only [allowsVote, decide_eq_true_eq, le_refl]
    obtain ⟨hmtr_2a, hs₄_pl, _, hs₄_in⟩ :=
      deliver_fanout_acc qs p₀ (.phase2a b v)
        { maxBal := some b, maxVoted := none, crashed := false }
        { maxBal := some b, maxVoted := some ⟨b, v⟩, crashed := false }
        (fun a => .phase2b a b v)
        (fun a st hacc => by
          refine ⟨Finset.univ.image fun q => (q, .phase2b a b v), ?_,
            Finset.mem_image.mpr ⟨p₀, Finset.mem_univ p₀, rfl⟩⟩
          dsimp only [synodQuorumProtocol]
          rw [hacc, ite_eq_left ⟨rfl, hal_b⟩])
        Q₀.nodup_toList
        (fun x hx => ⟨hs₃_2a_msgs x, (hs₃_al x).1.trans (hs₂_in x hx).1⟩)
    set s₄ := qList.foldl (fun w a => π.deliverStep w ⟨p₀, a, .phase2a b v⟩) s₃
    have hs₄_learn : (s₄.proc p₀).state.learn.crashed = false := by
      rw [(hs₄_pl p₀).2, (hs₃_al p₀).2, (hs₂_pl p₀).2]
      exact hs₁_learn
    -- Phase 2b fan-in to `p₀` across `qList`:
    have ⟨hmtr_2b, _⟩ := π.mTr_map_deliver (u := s₄) (fun a => ⟨a, p₀, .phase2b a b v⟩)
      (fun x hx => (hs₄_in x hx).2)
    set s₅ := qList.foldl (fun w a => π.deliverStep w ⟨a, p₀, .phase2b a b v⟩) s₄
    have hs₅_recv : ∀ a ∈ qList, ⟨a, b, v⟩ ∈ (s₅.proc p₀).state.learn.received := by
      suffices h2b : ∀ (as : List P) (u : NetState P (SynodNodeState P V) (Msg P P V) V),
          (u.proc p₀).state.learn.crashed = false →
          let u' := as.foldl (fun w a => π.deliverStep w ⟨a, p₀, .phase2b a b v⟩) u
          (u.proc p₀).state.learn.received ⊆ (u'.proc p₀).state.learn.received ∧
            ∀ a ∈ as, ⟨a, b, v⟩ ∈ (u'.proc p₀).state.learn.received from
        (h2b qList s₄ hs₄_learn).2
      intro as
      induction as with
      | nil => exact fun _ _ => ⟨Finset.Subset.rfl, fun _ h => absurd h List.not_mem_nil⟩
      | cons a rest ih =>
        intro u hl
        let u1 := π.deliverStep u ⟨a, p₀, .phase2b a b v⟩
        have hstep_2b : (u1.proc p₀).state.learn.crashed = false ∧
            insert ⟨a, b, v⟩ (u.proc p₀).state.learn.received =
              (u1.proc p₀).state.learn.received := by
          dsimp only [u1, AsyncQuorumProtocol.deliverStep, AsyncQuorumProtocol.applyResult, π,
            synodQuorumProtocol]
          rw [ite_eq_left (⟨hl, rfl⟩ : (u.proc p₀).state.learn.crashed = false ∧ a = a)]
          simp only [↓reduceIte, hl, true_and]
        obtain ⟨hsub_r, hin_r⟩ := ih u1 hstep_2b.1
        have hsub_all : insert ⟨a, b, v⟩ (u.proc p₀).state.learn.received ⊆ _ :=
          hstep_2b.2 ▸ hsub_r
        refine ⟨(Finset.subset_insert _ _).trans hsub_all, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx_r
        · exact hsub_all (Finset.mem_insert_self _ _)
        · exact hin_r x hx_r
    let xl : List (NetAction P ℕ (Msg P P V)) :=
      [act₀] ++
        (qList.map fun a => .deliver ⟨p₀, a, Msg.phase1a b⟩) ++
        (qList.map fun a => .deliver ⟨a, p₀, Msg.phase1b a b none⟩) ++
        (qList.map fun a => .deliver ⟨p₀, a, Msg.phase2a b v⟩) ++
        (qList.map fun a => .deliver ⟨a, p₀, Msg.phase2b a b v⟩)
    have hmtr_all : π.lts.MTr s₀ xl s₅ :=
      LTS.MTr.comp π.lts
        (LTS.MTr.comp π.lts
          (LTS.MTr.comp π.lts
            (LTS.MTr.comp π.lts (LTS.MTr.single _ htr₀) hmtr_1a)
            hmtr_1b)
          hmtr_2a)
        hmtr_2b
    have hgroup : ∀ act ∈ xl, act.InGroup Q₀ := by
      intro act hact
      simp only [xl, qList, List.mem_append, List.mem_singleton, List.mem_map,
        Finset.mem_toList] at hact
      rcases hact with (((rfl | ⟨a, haQ, rfl⟩) | ⟨a, haQ, rfl⟩) | ⟨a, haQ, rfl⟩) | ⟨a, haQ, rfl⟩
      · exact hp₀Q
      · exact ⟨hp₀Q, haQ⟩
      · exact ⟨haQ, hp₀Q⟩
      · exact ⟨hp₀Q, haQ⟩
      · exact ⟨haQ, hp₀Q⟩
    obtain ⟨hr₅, hout₅⟩ := netToSynod_reach qs ⟨xl, hmtr_all⟩
    have hlearnedAt₅ : (netToSynod s₅).LearnedAt qs p₀ b v :=
      ⟨Q₀, hQ₀, fun a haQ => hs₅_recv a (Finset.mem_toList.mpr haQ)⟩
    have hout_eq : (s₅.proc p₀).out = some v := by
      rw [hout₅ p₀]
      exact hr₅.learned_eq_some_iff.mpr ⟨b, hlearnedAt₅⟩
    exact ⟨xl, s₅, hgroup, hmtr_all, p₀, hp₀Q, v, hout_eq⟩

end Cslib.Distributed.Paxos
