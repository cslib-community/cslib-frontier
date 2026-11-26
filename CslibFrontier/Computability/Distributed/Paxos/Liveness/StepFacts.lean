/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Paxos.Basic

/-!
# Internal single-step and invariance lemmas for `synodStep`

Internal transition case analyses and backwards invariance helpers shared across `Duelling`,
`SoleLeaderInvariants`, `SoleLeader`, `SoleLeaderSweep`, and `SoleLeaderWitness`; never
re-exported through `Liveness`.

## Main results

* `Cslib.Distributed.Paxos.mem_msgs_synodStep_of_mem`,
  `Cslib.Distributed.Paxos.mem_msgs_synodStep_cases`: packet persistence and emission cases.
* `Cslib.Distributed.Paxos.proposers_synodStep_cases`,
  `Cslib.Distributed.Paxos.acceptors_synodStep_cases`,
  `Cslib.Distributed.Paxos.learners_synodStep_cases`: role-level single-step frame lemmas.
* `Cslib.Distributed.Paxos.maxVoted_none_of_mTr`,
  `Cslib.Distributed.Paxos.learned_none_of_mTr`: backwards invariance along finite traces.
-/

public section

namespace Cslib.Distributed.Paxos

open Cslib

/-- Packets not explicitly dropped persist across `synodStep`. -/
lemma mem_msgs_synodStep_of_mem {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    {qs : QuorumSystem Acceptor} {s : SynodState Proposer Acceptor Learner V}
    {act : SynodAction Proposer Acceptor Learner V} {m : Msg Proposer Acceptor V}
    (hm : m ∈ s.msgs) (hne : act ≠ .drop m) :
    m ∈ (synodStep qs s act).msgs := by
  cases act with
  | prepare _ _ => exact Finset.mem_insert_of_mem hm
  | recvPhase1a _ _ | recvPhase2a _ _ _ =>
    dsimp only [synodStep, synodStepCore]
    split_ifs <;> first | exact Finset.mem_insert_of_mem hm | exact hm
  | recvPhase1b p _ _ _ =>
    dsimp only [synodStep, synodStepCore]
    cases (s.proposers p).round <;> dsimp only [] <;>
      (repeat split) <;> first | exact Finset.mem_insert_of_mem hm | exact hm
  | drop _ => exact Finset.mem_erase.mpr ⟨fun heq => hne (heq ▸ rfl), hm⟩
  | _ => exact hm

/-- Case analysis on packets present after a single `synodStep`. -/
lemma mem_msgs_synodStep_cases {Proposer Acceptor Learner V : Type*}
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
          rw [ite_eq_left hg, ite_eq_left hq]; simp only [↓reduceIte]
        · exact Or.inl hold
      all_goals exact Or.inl hm
  | recvPhase2a a b v =>
    dsimp only [synodStep, synodStepCore] at hm
    split_ifs at hm with hal
    · rcases Finset.mem_insert.mp hm with rfl | hold
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, v, rfl, hal, rfl⟩)))
      · exact Or.inl hold
    · exact Or.inl hm
  | drop _ => exact Or.inl (Finset.mem_of_mem_erase hm)
  | _ => exact Or.inl hm

/-- Single-step case analysis on proposer state transitions under `synodStep`. -/
lemma proposers_synodStep_cases {Proposer Acceptor Learner V : Type*}
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
          decide (∃ Q ∈ qs.prepareQuorums, Q ⊆ insert a (s.proposers p).promised)) = true ∧
        (synodStep qs s act).proposers p =
          { s.proposers p with
            proposed := true
            promised := insert a (s.proposers p).promised
            maxVote := mergeVote (s.proposers p).maxVote mv } ∧
        Msg.phase2a ⟨r, p⟩ val ∈ (synodStep qs s act).msgs) ∨
      (∃ a b mv r, act = .recvPhase1b p a b mv ∧ (s.proposers p).round = some r ∧
        b = ⟨r, p⟩ ∧ a ∉ (s.proposers p).promised ∧
        ¬ ((!(s.proposers p).proposed &&
          decide (∃ Q ∈ qs.prepareQuorums, Q ⊆ insert a (s.proposers p).promised)) = true) ∧
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
    split <;> exact Or.inl rfl
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
              decide (∃ Q ∈ qs.prepareQuorums, Q ⊆ insert a (s.proposers q).promised)) = true
          · rw [ite_eq_left hq_cond]
            exact Or.inr (Or.inr (Or.inl
              ⟨a, b, mv, r, _, rfl, rfl, hg.1, hg.2, hq_cond, ite_eq_left rfl,
                Finset.mem_insert_self _ _⟩))
          · rw [ite_eq_right hq_cond]
            exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨a, b, mv, r, rfl, rfl, hg.1, hg.2, hq_cond, ite_eq_left rfl⟩)))
        · rw [ite_eq_right hg]; exact Or.inl rfl
    · cases (s.proposers q).round <;> dsimp only [] <;> (repeat split) <;>
        first | exact Or.inl (ite_eq_right (Ne.symm hqp)) | exact Or.inl rfl
  | crashProposer q =>
    dsimp only [synodStep, synodStepCore]
    rcases eq_or_ne p q with rfl | hpq
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ite_eq_left rfl⟩)))
    · exact Or.inl (ite_eq_right hpq)
  | _ => exact Or.inl rfl

/-- Single-step case analysis on acceptor state transitions under `synodStep`. -/
lemma acceptors_synodStep_cases {Proposer Acceptor Learner V : Type*}
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
  | recvPhase2a a' b v =>
    dsimp only [synodStep, synodStepCore]
    by_cases hal : allowsVote (s.acceptors a').maxBal b = true
    · rw [ite_eq_left hal]
      rcases eq_or_ne a a' with rfl | haa
      · exact Or.inr (Or.inr (Or.inl ⟨b, v, rfl, hal, ite_eq_left rfl⟩))
      · exact Or.inl (ite_eq_right haa)
    · rw [ite_eq_right hal]; exact Or.inl rfl
  | recvPhase1b q _ _ _ =>
    dsimp only [synodStep, synodStepCore]
    cases (s.proposers q).round <;> dsimp only [] <;> (repeat split) <;> exact Or.inl rfl
  | crashAcceptor a' =>
    dsimp only [synodStep, synodStepCore]
    rcases eq_or_ne a a' with rfl | haa
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, ite_eq_left rfl⟩))
    · exact Or.inl (ite_eq_right haa)
  | _ => exact Or.inl rfl

/-- Single-step case analysis on learner state transitions under `synodStep`. -/
lemma learners_synodStep_cases {Proposer Acceptor Learner V : Type*}
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
                  decide (∃ Q ∈ qs.acceptQuorums, ∀ a' ∈ Q,
                    ⟨a', b, v⟩ ∈ insert ⟨a, b, v⟩ (s.learners l).received) then
                some v
              else (s.learners l).learned }) ∨
      (act = .crashLearner l ∧
        (synodStep qs s act).learners l = { s.learners l with crashed := true }) := by
  cases act with
  | recvPhase1a _ _ | recvPhase2a _ _ _ =>
    dsimp only [synodStep, synodStepCore]
    split_ifs <;> exact Or.inl rfl
  | recvPhase2b l₀ a b v =>
    dsimp only [synodStep, synodStepCore]
    rcases eq_or_ne l l₀ with rfl | hll
    · exact Or.inr (Or.inl ⟨a, b, v, rfl, ite_eq_left rfl⟩)
    · exact Or.inl (ite_eq_right hll)
  | recvPhase1b q _ _ _ =>
    dsimp only [synodStep, synodStepCore]
    cases (s.proposers q).round <;> dsimp only [] <;> (repeat split) <;> exact Or.inl rfl
  | crashLearner l₀ =>
    dsimp only [synodStep, synodStepCore]
    rcases eq_or_ne l l₀ with rfl | hll
    · exact Or.inr (Or.inr ⟨rfl, ite_eq_left rfl⟩)
    · exact Or.inl (ite_eq_right hll)
  | _ => exact Or.inl rfl

/-- Backwards invariance of `maxVoted = none` along multi-step `synodLts` executions. -/
lemma maxVoted_none_of_mTr {Proposer Acceptor Learner V : Type*}
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
        ⟨_, _, _, _, heq⟩ | ⟨_, heq⟩ <;> rw [heq] <;> first | exact hne | exact nofun
  by_contra h₁
  exact LTS.mtrInv_of_trInv htr_inv _ _ _ hmtr h₁ h₂

/-- Backwards invariance of `learned = none` along multi-step `synodLts` executions. -/
lemma learned_none_of_mTr {Proposer Acceptor Learner V : Type*}
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
      rw [heq] <;> (try split) <;> first | exact hne | exact nofun
  by_contra h₁
  exact LTS.mtrInv_of_trInv htr_inv _ _ _ hmtr h₁ h₂

end Cslib.Distributed.Paxos
