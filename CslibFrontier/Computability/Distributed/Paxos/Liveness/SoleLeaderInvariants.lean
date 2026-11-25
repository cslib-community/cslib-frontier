/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Paxos.Liveness.SoleLeaderDefs
import CslibFrontier.Computability.Distributed.Paxos.Liveness.StepFacts

/-!
# Internal ballot-ceiling and monotonicity invariants for sole-leader liveness

Internal execution invariants used by `SoleLeader`; never re-exported through `Liveness`.

## Main results

* `Cslib.Distributed.Paxos.ballot_msg_persist`, `Cslib.Distributed.Paxos.ballot_ceiling_inv`,
  `Cslib.Distributed.Paxos.sole_leader_round_inv`, `Cslib.Distributed.Paxos.promised_mono`,
  `Cslib.Distributed.Paxos.learner_received_mono`: sole-leader execution invariants.
-/

public section

namespace Cslib.Distributed.Paxos

open Cslib Cslib.ωSequence

section SoleLeader

variable {Proposer Acceptor Learner V : Type*}
  [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
  (qs : QuorumSystem Acceptor)

/-- Any packet carrying ballot `b` persists as long as no packet of ballot `b` is dropped. -/
lemma ballot_msg_persist {b : Ballot Proposer}
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

/-- If all ballots initially and subsequently prepared are `≤ b`, then all in-flight and promised
ballots remain `≤ b`. -/
lemma ballot_ceiling_inv {b : Ballot Proposer}
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
      · exact ih.1 (.phase1a b') (hact ▸ hen).2
      · exact hb_eq ▸ ih.1 (.phase1b a b' mv) (hact ▸ hen).2
      · exact ih.1 (.phase2a b' v) (hact ▸ hen).2
    · rcases acceptors_synodStep_cases qs (ss n) (xs n) a with heq |
          ⟨b', hact, _, heq, _⟩ | ⟨b', v, hact, _, heq⟩ | ⟨_, heq⟩
      · rw [heq] at hmb
        exact ih.2 a mb hmb
      · rw [heq] at hmb
        exact Option.some.inj hmb ▸ ih.1 (.phase1a b') (hact ▸ hen).2
      · rw [heq] at hmb
        exact Option.some.inj hmb ▸ ih.1 (.phase2a b' v) (hact ▸ hen).2
      · rw [heq] at hmb
        exact ih.2 a mb hmb

/-- Once proposer `p` prepares round `r` cleanly with no higher ballot prepared, its round stays
`some r`. -/
lemma sole_leader_round_inv {p : Proposer} {r : ℕ}
    {ss : ωSequence (SynodState Proposer Acceptor Learner V)}
    {xs : ωSequence (SynodAction Proposer Acceptor Learner V)}
    (hexec : (synodLts qs).OmegaExecution ss xs)
    (hprep₀ : xs 0 = .prepare p r)
    (hno_higher : ∀ j q r', xs j = .prepare q r' → ⟨r', q⟩ ≤ (⟨r, p⟩ : Ballot Proposer)) :
    ∀ n, 1 ≤ n → ((ss n).proposers p).round = some r ∧
      ∀ r', xs n ≠ .prepare p r' := by
  have hnot_prep (n : ℕ) (hround : ((ss n).proposers p).round = some r) (r' : ℕ)
      (hact : xs n = .prepare p r') : False := by
    have hen := (hexec n).1
    rw [hact] at hen
    dsimp only [synodEnabled] at hen
    rw [hround] at hen
    have hle := (Ballot.le_iff _ _).mp (hno_higher n p r' hact)
    dsimp only at hle
    rcases hle with hlt | ⟨heq, _⟩ <;> omega
  have hround_all (k : ℕ) : ((ss (1 + k)).proposers p).round = some r := by
    induction k with
    | zero =>
      rw [(hexec 0).2, hprep₀]
      simp [synodStep, synodStepCore]
    | succ k ih =>
      rw [← Nat.add_assoc, (hexec (1 + k)).2]
      rcases proposers_synodStep_cases qs (ss (1 + k)) (xs (1 + k)) p with heq |
          ⟨r', hact, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, heq, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, heq⟩ | ⟨_, heq⟩
      · rwa [heq]
      · exact (hnot_prep (1 + k) ih r' hact).elim
      · rwa [heq]
      · rwa [heq]
      · rwa [heq]
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact ⟨hround_all k, hnot_prep (1 + k) (hround_all k)⟩

/-- Proposer `p`'s promised quorum set is monotone from step `1` onward while its round stays
`r`. -/
lemma promised_mono {p : Proposer} {r : ℕ}
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
    rw [← Nat.add_assoc, (hexec (n₁ + d)).2]
    rcases proposers_synodStep_cases qs (ss (n₁ + d)) (xs (n₁ + d)) p with heq |
        ⟨r', hact, _⟩ | ⟨a, _, _, _, _, _, _, _, _, _, heq, _⟩ |
        ⟨a, _, _, _, _, _, _, _, _, heq⟩ | ⟨_, heq⟩
    · rwa [heq]
    · exact absurd hact
        ((sole_leader_round_inv qs hexec hprep₀ hno_higher (n₁ + d) (by omega)).2 r')
    · rw [heq]; exact hsub.trans (Finset.subset_insert a _)
    · rw [heq]; exact hsub.trans (Finset.subset_insert a _)
    · rwa [heq]

/-- Learner `l`'s received Phase 2b vote set grows monotonically along any execution. -/
lemma learner_received_mono {l : Learner}
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


end SoleLeader

end Cslib.Distributed.Paxos
