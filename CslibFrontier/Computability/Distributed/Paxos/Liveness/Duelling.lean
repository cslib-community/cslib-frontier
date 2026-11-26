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
import CslibFrontier.Computability.Distributed.Paxos.Liveness.StepFacts

/-!
# Crash-free duelling-proposers livelock on `Fin 3`

Constructs `exists_duelling_proposers_livelock` after the two-proposer scenario of [Lamport2001]
§2.4 and [Lamport1998] §2.4 in the crash-stop Single-Decree Synod model.

## Main definitions

* `Cslib.Distributed.Paxos.majorityQuorumsFin3`: strict-majority quorum system on `Fin 3` (`t = 1`).

## Main results

* `Cslib.Distributed.Paxos.exists_duelling_proposers_livelock`: explicit crash-free non-terminating
  duelling-proposers execution on `Fin 3` acceptors and `Fin 2` proposers with distinct inputs.
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
    decide (∃ Q ∈ majorityQuorumsFin3.prepareQuorums, Q ⊆ ({0} : Finset (Fin 3))) = false := by
  decide

private lemma fin3_pair_zero_one_has_quorum :
    decide (∃ Q ∈ majorityQuorumsFin3.prepareQuorums, Q ⊆ ({0, 1} : Finset (Fin 3))) = true := by
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
  intro acts u'
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
    rw [congrArg SynodState.acceptors hu1_def, ite_eq_left ha0_bal, ha0_vote]
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
  refine ⟨LTS.MTr.stepL tr1 (LTS.MTr.stepL tr2 (LTS.MTr.stepL tr3 LTS.MTr.refl)), ?_⟩
  rw [show u' = u3 from rfl, hu3_def, hu2_def, hu1_def]
  exact ⟨ite_eq_left rfl, fun q hqp => ite_eq_right hqp, rfl, rfl, rfl, rfl,
    fun _ hm => by simp [hm], by simp [b]⟩

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
  intro acts u'
  let b : Ballot (Fin 2) := ⟨k, p⟩
  have hins01 : insert (1 : Fin 3) ({0} : Finset (Fin 3)) = {0, 1} := by decide
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
    rw [ite_eq_left ⟨rfl, Finset.notMem_empty 0⟩, Finset.insert_empty,
      fin3_singleton_zero_not_quorum]
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
  refine ⟨LTS.MTr.stepL tr1 (LTS.MTr.stepL tr2 LTS.MTr.refl), ?_⟩
  rw [show u' = u2 from rfl, hu2_def]
  exact ⟨by simp only [↓reduceIte, and_self], fun q hqp => ite_eq_right hqp, rfl, rfl,
    Finset.subset_insert _ _, Finset.mem_insert_self _ _⟩

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
  have hb₀₁ : aboveMaxBal (some b₀) b₁ = true := by simp [aboveMaxBal, Ballot.lt_iff, b₀, b₁]
  have hallows_false : allowsVote (some b₁) b₀ = false := by
    simp [allowsVote, Ballot.le_iff, b₀, b₁]
  have hb₁_next : aboveMaxBal (some b₁) ⟨k + 1, 0⟩ = true := by
    simp [aboveMaxBal, Ballot.lt_iff, b₁]
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
  have hs5_a0 := (congrFun hs5_acc 0).trans hs3_a0
  have hs5_a1 := (congrFun hs5_acc 1).trans hs3_a1
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
    rw [hs8_a0, hallows_false]; rfl
  obtain ⟨mtr5, hs11_p1, hs11_po, hs11_acc, hs11_l, hs11_sub, hs11_2a1⟩ :=
    duelling_recv_two_1b 1 v₁ k s9 (hs9_eq ▸ hs8_p1) (hs9_eq ▸ hs8_1b0) (hs9_eq ▸ hs8_1b1)
  set s11 := ([SynodAction.recvPhase1b 1 0 b₁ none, .recvPhase1b 1 1 b₁ none] :
    List (SynodAction (Fin 2) (Fin 3) Learner V)).foldl (synodStep majorityQuorumsFin3) s9
  have hmTr : (synodLts majorityQuorumsFin3).MTr s (duellingCycle v₀ k) s11 :=
    LTS.MTr.comp _ mtr1 (LTS.MTr.comp _ mtr2
      (LTS.MTr.comp _ mtr3 (LTS.MTr.stepL tr9 mtr5)))
  have hs11_p0 : s11.proposers 0 = s5.proposers 0 :=
    (hs11_po 0 h01).trans ((congrArg (fun u => u.proposers 0) hs9_eq).trans (hs8_po 0 h01))
  have hs11_acc8 : s11.acceptors = s8.acceptors :=
    hs11_acc.trans (congrArg SynodState.acceptors hs9_eq)
  have hs11_l0 : s11.learners = s.learners :=
    hs11_l.trans ((congrArg SynodState.learners hs9_eq).trans (hs8_l.trans (hs5_l.trans hs3_l)))
  have hs11_eq : (duellingCycle (Learner := Learner) v₀ k).foldl
      (synodStep majorityQuorumsFin3) s = s11 := by
    simp only [duellingCycle, List.foldl_cons, List.foldl_nil]; rfl
  dsimp only []
  rw [hs11_eq]
  have hs11_sub8 : s8.msgs ⊆ s11.msgs := hs9_eq.subst (motive := (·.msgs ⊆ s11.msgs)) hs11_sub
  refine ⟨hmTr, ?_, hs11_sub8 (hs8_sub (hs5_sub hs3_1a0)), hs11_sub8 hs8_1a1,
    hs11_sub8 (hs8_sub hs5_2a0), hs11_2a1⟩
  exact
    { p0_in := (congrArg ProposerState.input hs11_p0).trans hs5_p0.1
      p0_live := (congrArg ProposerState.crashed hs11_p0).trans hs5_p0.2.1
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
      a2_vote := by rw [hs11_acc8, hs8_a2, hs5_acc, hs3_a2, hb.a2_vote]
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
  have hstep (k : ℕ) :=
    duellingCycle_step (Learner := Learner) v₀ v₁ k (ts k) (duellingStateSeq_inv v₀ v₁ k)
  have hpos (k : ℕ) : 0 < (xls k).length := by
    simp only [xls, get_fun, duellingCycle, List.length_cons, List.length_nil]; omega
  have : Inhabited (SynodAction (Fin 2) (Fin 3) Learner V) := ⟨.stutter⟩
  obtain ⟨ss, hexec, hts⟩ := LTS.OmegaExecution.flatten_mTr (fun k => (hstep k).1) hpos
  have hmtr n := hexec.extract_mTr ((cumLen_strictMono hpos).id_le n)
  refine ⟨inputs, ss, xls.flatten, hne, ?_, hexec, ?_,
    fun k => ⟨xls.cumLen (k + 1), (hts (k + 1)).symm ▸ (hstep k).2.2⟩, ?_, ?_⟩
  · simpa only [cumLen_zero, ts, get_fun, duellingStateSeq, inputs] using hts 0
  · refine (forall_flatten_iff hpos fun act => act ≠ .stutter ∧ ∀ m, act ≠ .drop m).mpr
      fun k => List.forall_iff_forall_mem.mpr fun act hact => ?_
    simp only [xls, get_fun, duellingCycle, List.mem_cons, List.not_mem_nil, or_false] at hact
    rcases hact with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨nofun, nofun⟩
  · intro n a
    have hinv := duellingStateSeq_inv (Learner := Learner) v₀ v₁ n
    exact maxVoted_none_of_mTr (hmtr n) ((hts n).symm ▸ match a with
      | ⟨0, _⟩ => hinv.a0_vote | ⟨1, _⟩ => hinv.a1_vote | ⟨2, _⟩ => hinv.a2_vote)
  · intro n l
    exact learned_none_of_mTr (hmtr n)
      (hts n ▸ (duellingStateSeq_inv (Learner := Learner) v₀ v₁ n).learners_empty l)

end Cslib.Distributed.Paxos
