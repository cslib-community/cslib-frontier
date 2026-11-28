/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Distributed.Paxos.Liveness

/-! Crash-stop Single-Decree Synod protocol step: strict-majority quorum checks on `Fin 3`
(`t = 1`), computable `decide`-checked execution
traces for (a) single-ballot consensus with packet loss, duplicate redelivery, and an acceptor
crash, (b) mid-flight ballot preemption `b₁ < b₂` where quorum intersection forces proposer `1` to
carry proposer `0`'s chosen value forward into `b₂`, and (c) a 2-round (22-step) finite prefix of
duelling proposers, together with instantiations of crash-stop safety (`paxos_agreement_crashStop`,
`paxos_validity_crashStop`, `phase2a_unique_of_ballot_crashStop`,
`chosenAt_implies_higher_phase2a_eq_crashStop`), infinite duelling-proposers livelock
(`exists_duelling_proposers_livelock`), conditional sole-leader progress
(`paxos_liveness_of_sole_leader_crashStop`, `exists_sole_leader_execution_crashStop`),
disjoint-quorum split-brain impossibility (`not_synod_safe_of_disjoint_quorums`,
`not_safeSingleQuorum_of_card_le_two_mul`), and `synodQuorumProtocol_safeCohort_crashStop`. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.Paxos

open Cslib Cslib.Distributed.Paxos

/-! ### Computable trace checker for `synodLts` -/

/-- Computable Boolean checker verifying that every action in `xl` is enabled along `synodStep`. -/
@[expose] public def validTrace {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    (qs : QuorumSystem Acceptor) (s : SynodState Proposer Acceptor Learner V) :
    List (SynodAction Proposer Acceptor Learner V) → Bool
  | [] => true
  | act :: rest => decide (synodEnabled s act) && validTrace qs (synodStep qs s act) rest

/-- Run a finite list of Synod actions from `s`. -/
@[expose] public def runTrace {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    (qs : QuorumSystem Acceptor) (s : SynodState Proposer Acceptor Learner V)
    (xl : List (SynodAction Proposer Acceptor Learner V)) :
    SynodState Proposer Acceptor Learner V :=
  xl.foldl (synodStep qs) s

public theorem mTr_of_validTrace {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    (qs : QuorumSystem Acceptor) (s : SynodState Proposer Acceptor Learner V)
    (xl : List (SynodAction Proposer Acceptor Learner V))
    (hv : validTrace qs s xl = true) :
    (synodLts qs).MTr s xl (runTrace qs s xl) := by
  induction xl generalizing s with
  | nil => exact LTS.MTr.refl
  | cons act rest ih =>
    simp only [validTrace, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact LTS.MTr.stepL ⟨hv.1, rfl⟩ (ih (synodStep qs s act) hv.2)

/-! ### Quorum checks on `Fin 3` (`t = 1`) -/

example : ({0, 1} : Finset (Fin 3)) ∈ majorityQuorumsFin3.prepareQuorums := by decide
example : ({1, 2} : Finset (Fin 3)) ∈ majorityQuorumsFin3.prepareQuorums := by decide
example : ({0, 2} : Finset (Fin 3)) ∈ majorityQuorumsFin3.prepareQuorums := by decide
example : ({0} : Finset (Fin 3)) ∉ majorityQuorumsFin3.prepareQuorums := by decide

example (Q : Finset (Fin 3)) (hQ : Q ∈ majorityQuorumsFin3.prepareQuorums) : Q.Nonempty :=
  majorityQuorumsFin3.prepareQuorum_nonempty hQ

/-! ### Trace (a): Clean 1-ballot consensus with crash, drop, and duplicate delivery -/

def trace1Inputs : Fin 2 → ℕ
  | 0 => 42
  | 1 => 99

def trace1Actions : List (SynodAction (Fin 2) (Fin 3) (Fin 2) ℕ) :=
  [ .crashAcceptor 2
  , .prepare 0 0
  , .recvPhase1a 0 ⟨0, 0⟩
  , .recvPhase1a 1 ⟨0, 0⟩
  , .recvPhase1b 0 0 ⟨0, 0⟩ none
  , .recvPhase1b 0 0 ⟨0, 0⟩ none  -- duplicate promise redelivery (idempotent)
  , .recvPhase1b 0 1 ⟨0, 0⟩ none  -- completes quorum `{0, 1}` → emits `Phase2a(⟨0, 0⟩, 42)`
  , .drop (.phase1a ⟨0, 0⟩)       -- network drops prepare packet
  , .recvPhase2a 0 ⟨0, 0⟩ 42
  , .recvPhase2a 1 ⟨0, 0⟩ 42
  , .recvPhase2b 0 0 ⟨0, 0⟩ 42
  , .recvPhase2b 0 1 ⟨0, 0⟩ 42
  , .recvPhase2b 1 1 ⟨0, 0⟩ 42
  , .recvPhase2b 1 0 ⟨0, 0⟩ 42 ]

def trace1End : SynodState (Fin 2) (Fin 3) (Fin 2) ℕ :=
  runTrace majorityQuorumsFin3 (initState trace1Inputs) trace1Actions

theorem trace1_valid :
    validTrace majorityQuorumsFin3
      (initState (Learner := Fin 2) trace1Inputs) trace1Actions = true := by
  decide

theorem trace1_learners_decide :
    (trace1End.learners 0).learned = some 42 ∧
      (trace1End.learners 1).learned = some 42 ∧
      (trace1End.acceptors 2).crashed = true ∧
      (trace1End.acceptors 2).maxVoted = none ∧
      Msg.phase1a ⟨0, 0⟩ ∉ trace1End.msgs := by
  decide

theorem trace1_reachable : Reachable majorityQuorumsFin3 trace1Inputs trace1End :=
  ⟨trace1Actions, mTr_of_validTrace _ _ _ trace1_valid⟩

example : ∃ p : Fin 2, trace1Inputs p = 42 :=
  paxos_validity_crashStop majorityQuorumsFin3 trace1_reachable trace1_learners_decide.1

/-! ### Trace (b): Preempted mid-flight ballot `b₁ < b₂` with quorum-intersection carry-over -/

def preemptInputs : Fin 2 → Bool
  | 0 => true
  | 1 => false

/-- Proposer `0` (`input = true`) gets `(b₁ = ⟨0, 0⟩, true)` accepted on `{0, 1}` and learned at
learner `0`. Before learner `1` hears `b₁`'s votes (which are dropped from `msgs`), proposer `1`
(`input = false`) prepares `b₂ = ⟨0, 1⟩ > b₁` on quorum `{1, 2}`: overlapping acceptor `1` reports
`some ⟨b₁, true⟩`, forcing proposer `1` to propose `(b₂, true)` instead of `false`, and learner `1`
learns `some true` at `b₂`. -/
def preemptActions : List (SynodAction (Fin 2) (Fin 3) (Fin 2) Bool) :=
  let b₁ : Ballot (Fin 2) := ⟨0, 0⟩
  let b₂ : Ballot (Fin 2) := ⟨0, 1⟩
  [ -- Ballot `b₁`: proposer `0` (`input = true`) reaches `ChosenAt` on `{0, 1}`
    .prepare 0 0
  , .recvPhase1a 0 b₁
  , .recvPhase1a 1 b₁
  , .recvPhase1b 0 0 b₁ none
  , .recvPhase1b 0 1 b₁ none
  , .recvPhase2a 0 b₁ true
  , .recvPhase2a 1 b₁ true
  , .recvPhase2b 0 0 b₁ true
  , .recvPhase2b 0 1 b₁ true
  -- Network drops `b₁`'s `Phase2b` packets before learner `1` receives them
  , .drop (.phase2b 0 b₁ true)
  , .drop (.phase2b 1 b₁ true)
  -- Ballot `b₂ > b₁`: proposer `1` (`input = false`) prepares across quorum `{1, 2}`
  , .prepare 1 0
  , .recvPhase1a 2 b₂
  , .recvPhase1a 1 b₂
  , .recvPhase1b 1 2 b₂ none
  , .recvPhase1b 1 1 b₂ (some ⟨b₁, true⟩)
  -- Stale `Phase2a(b₁, true)` arriving at acceptor `1` is rejected since `maxBal = some b₂ > b₁`
  , .recvPhase2a 1 b₁ true
  -- Quorum `{1, 2}` accepts `(b₂, true)` and learner `1` learns `true` at `b₂`
  , .recvPhase2a 1 b₂ true
  , .recvPhase2a 2 b₂ true
  , .recvPhase2b 1 1 b₂ true
  , .recvPhase2b 1 2 b₂ true ]

def preemptEnd : SynodState (Fin 2) (Fin 3) (Fin 2) Bool :=
  runTrace majorityQuorumsFin3 (initState preemptInputs) preemptActions

theorem preempt_valid :
    validTrace majorityQuorumsFin3
      (initState (Learner := Fin 2) preemptInputs) preemptActions = true := by
  decide

theorem preempt_carry_over_props :
    Msg.phase2a ⟨0, 1⟩ true ∈ preemptEnd.msgs ∧
      Msg.phase2a ⟨0, 1⟩ false ∉ preemptEnd.msgs ∧
      (preemptEnd.proposers 1).maxVote = some ⟨⟨0, 0⟩, true⟩ ∧
      (preemptEnd.learners 0).learned = some true ∧
      (preemptEnd.learners 1).learned = some true := by
  decide

theorem preempt_mtr :
    (synodLts majorityQuorumsFin3).MTr
      (initState preemptInputs) preemptActions preemptEnd :=
  mTr_of_validTrace _ _ _ preempt_valid

theorem preempt_reachable : Reachable majorityQuorumsFin3 preemptInputs preemptEnd :=
  ⟨preemptActions, preempt_mtr⟩

theorem preempt_b1_votes_emitted :
    Msg.phase2b 0 ⟨0, 0⟩ true ∈
      traceMsgs majorityQuorumsFin3 (initState (Learner := Fin 2) preemptInputs)
        preemptActions ∧
    Msg.phase2b 1 ⟨0, 0⟩ true ∈
      traceMsgs majorityQuorumsFin3 (initState (Learner := Fin 2) preemptInputs)
        preemptActions := by
  decide

/-- Exercise `phase2a_unique_of_ballot_crashStop`, `chosenAt_implies_higher_phase2a_eq_crashStop`,
and `paxos_agreement_crashStop` on the preempted trace. -/
example (v : Bool)
    (hm : Msg.phase2a ⟨0, 1⟩ v ∈
      traceMsgs majorityQuorumsFin3 (initState (Learner := Fin 2) preemptInputs) preemptActions) :
    v = true := by
  have hchosen : ChosenAt majorityQuorumsFin3
      (traceMsgs majorityQuorumsFin3 (initState (Learner := Fin 2) preemptInputs) preemptActions)
      ⟨0, 0⟩ true := by
    refine ⟨{0, 1}, by decide, fun a ha => ?_⟩
    rcases Finset.mem_insert.mp ha with rfl | ha1
    · exact preempt_b1_votes_emitted.1
    · rw [Finset.mem_singleton.mp ha1]
      exact preempt_b1_votes_emitted.2
  have hle : (⟨0, 0⟩ : Ballot (Fin 2)) ≤ ⟨0, 1⟩ := by decide
  have heq :=
    chosenAt_implies_higher_phase2a_eq_crashStop majorityQuorumsFin3 preempt_mtr hchosen hm hle
  have h2a_mem := mem_traceMsgs_of_mem_msgs majorityQuorumsFin3 preempt_mtr
    preempt_carry_over_props.1
  have _ : v = true := phase2a_unique_of_ballot_crashStop majorityQuorumsFin3 preempt_mtr hm h2a_mem
  exact heq

example :
    preemptEnd.LearnedAt majorityQuorumsFin3 0 ⟨0, 0⟩ true ∧
      preemptEnd.LearnedAt majorityQuorumsFin3 1 ⟨0, 1⟩ true := by
  refine ⟨⟨{0, 1}, by decide, fun a ha => ?_⟩, ⟨{1, 2}, by decide, fun a ha => ?_⟩⟩
  · rcases Finset.mem_insert.mp ha with rfl | ha1
    · decide
    · rw [Finset.mem_singleton.mp ha1]; decide
  · rcases Finset.mem_insert.mp ha with rfl | ha2
    · decide
    · rw [Finset.mem_singleton.mp ha2]; decide

/-! ### Trace (c): Finite 2-round prefix of duelling proposers -/

def testDuellingCycle (k : ℕ) : List (SynodAction (Fin 2) (Fin 3) Unit Bool) :=
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
  , .recvPhase2a 0 b₀ true
  , .recvPhase1b 1 0 b₁ none
  , .recvPhase1b 1 1 b₁ none ]

def duellingPrefixActions : List (SynodAction (Fin 2) (Fin 3) Unit Bool) :=
  testDuellingCycle 0 ++ testDuellingCycle 1

def duellingPrefixEnd : SynodState (Fin 2) (Fin 3) Unit Bool :=
  runTrace majorityQuorumsFin3 (initState preemptInputs) duellingPrefixActions

theorem duellingPrefix_valid :
    validTrace majorityQuorumsFin3
      (initState (Learner := Unit) preemptInputs) duellingPrefixActions = true := by
  decide

theorem duellingPrefix_no_decision :
    duellingPrefixActions.length = 22 ∧
      Msg.phase2a ⟨0, 0⟩ true ∈ duellingPrefixEnd.msgs ∧
      Msg.phase2a ⟨0, 1⟩ false ∈ duellingPrefixEnd.msgs ∧
      Msg.phase2a ⟨1, 0⟩ true ∈ duellingPrefixEnd.msgs ∧
      Msg.phase2a ⟨1, 1⟩ false ∈ duellingPrefixEnd.msgs ∧
      (duellingPrefixEnd.acceptors 0).maxBal = some ⟨1, 1⟩ ∧
      (duellingPrefixEnd.acceptors 0).maxVoted = none ∧
      (duellingPrefixEnd.acceptors 1).maxBal = some ⟨1, 1⟩ ∧
      (duellingPrefixEnd.acceptors 1).maxVoted = none ∧
      (duellingPrefixEnd.acceptors 2).maxVoted = none ∧
      (duellingPrefixEnd.learners ()).learned = none := by
  decide

/-! ### Infinite livelock, sole-leader liveness, and split-brain impossibility instantiations -/

-- Infinite duelling-proposers livelock on `Bool` and `ℕ`:
example :
    ∃ (inputs : Fin 2 → Bool) (ss : ωSequence (SynodState (Fin 2) (Fin 3) Unit Bool))
      (xs : ωSequence (SynodAction (Fin 2) (Fin 3) Unit Bool)),
      inputs 0 ≠ inputs 1 ∧
      ss 0 = initState inputs ∧
      (synodLts majorityQuorumsFin3).OmegaExecution ss xs ∧
      (∀ n, xs n ≠ .stutter ∧ (∀ m, xs n ≠ .drop m)) ∧
      (∀ k, ∃ n, Msg.phase1a ⟨k, 0⟩ ∈ (ss n).msgs ∧
        Msg.phase1a ⟨k, 1⟩ ∈ (ss n).msgs ∧
        Msg.phase2a ⟨k, 0⟩ (inputs 0) ∈ (ss n).msgs ∧
        Msg.phase2a ⟨k, 1⟩ (inputs 1) ∈ (ss n).msgs) ∧
      (∀ n a, ((ss n).acceptors a).maxVoted = none) ∧
      (∀ n l, ((ss n).learners l).learned = none) :=
  exists_duelling_proposers_livelock

example :
    ∃ (inputs : Fin 2 → ℕ) (ss : ωSequence (SynodState (Fin 2) (Fin 3) (Fin 2) ℕ))
      (xs : ωSequence (SynodAction (Fin 2) (Fin 3) (Fin 2) ℕ)),
      inputs 0 ≠ inputs 1 ∧
      ss 0 = initState inputs ∧
      (synodLts majorityQuorumsFin3).OmegaExecution ss xs ∧
      (∀ n, xs n ≠ .stutter ∧ (∀ m, xs n ≠ .drop m)) ∧
      (∀ k, ∃ n, Msg.phase1a ⟨k, 0⟩ ∈ (ss n).msgs ∧
        Msg.phase1a ⟨k, 1⟩ ∈ (ss n).msgs ∧
        Msg.phase2a ⟨k, 0⟩ (inputs 0) ∈ (ss n).msgs ∧
        Msg.phase2a ⟨k, 1⟩ (inputs 1) ∈ (ss n).msgs) ∧
      (∀ n a, ((ss n).acceptors a).maxVoted = none) ∧
      (∀ n l, ((ss n).learners l).learned = none) :=
  exists_duelling_proposers_livelock

-- Constructive sole-leader recovery directly from `duellingPrefixEnd`!
example :
    ∃ (r : ℕ) (ss : ωSequence (SynodState (Fin 2) (Fin 3) Unit Bool))
      (xs : ωSequence (SynodAction (Fin 2) (Fin 3) Unit Bool)) (k : ℕ) (v : Bool),
      ss 0 = duellingPrefixEnd ∧
      (synodLts majorityQuorumsFin3).OmegaExecution ss xs ∧
      xs 0 = .prepare 0 r ∧
      BallotsBelow (ss 0) ⟨r, 0⟩ ∧
      (∀ j q r', xs j = .prepare q r' → ⟨r', q⟩ ≤ (⟨r, 0⟩ : Ballot (Fin 2))) ∧
      LiveAndLossless ⟨r, 0⟩ 0 {0, 1} () ss xs ∧
      (ss k).LearnedAt majorityQuorumsFin3 () ⟨r, 0⟩ v ∧
      ((ss k).learners ()).learned = some v :=
  exists_sole_leader_execution_crashStop majorityQuorumsFin3
    ⟨duellingPrefixActions, mTr_of_validTrace _ _ _ duellingPrefix_valid⟩
    (by decide) (by decide) (by decide) (by decide)

-- Split-brain impossibility on disjoint subsets and for `2 ≤ |P| ≤ 2t`:
example {S L M : Type*} [DecidableEq M] (π : AsyncQuorumProtocol (Fin 4) S L M Bool) :
  ¬ (π.SafeConsensus ∧ π.CanDecideIn {0, 1} ∧ π.CanDecideIn {2, 3}) :=
  not_synod_safe_of_disjoint_quorums π (by decide)

example {S L M : Type*} [DecidableEq M] (π : AsyncQuorumProtocol (Fin 2) S L M Bool) :
    ¬ (π.SafeConsensus ∧ ∀ Q : Finset (Fin 2), 2 - 1 ≤ Q.card → π.CanDecideIn Q) :=
  not_safeSingleQuorum_of_card_le_two_mul (t := 1) (by simp) (by simp) π

example {S L M : Type*} [DecidableEq M] (π : AsyncQuorumProtocol (Fin 4) S L M ℕ) :
    ¬ (π.SafeConsensus ∧ ∀ Q : Finset (Fin 4), 4 - 2 ≤ Q.card → π.CanDecideIn Q) :=
  not_safeSingleQuorum_of_card_le_two_mul (t := 2) (by simp) (by simp) π

-- Crash-stop counterpart on strict-majority quorums (`Fin 3, t = 1` and `Fin 5, t = 2`):
example :
    (synodQuorumProtocol (V := Bool) majorityQuorumsFin3).SafeConsensus ∧
      ∀ Q ∈ majorityQuorumsFin3.prepareQuorums,
        (synodQuorumProtocol (V := Bool) majorityQuorumsFin3).CanDecideIn Q :=
  ⟨(synodQuorumProtocol_safeCohort_crashStop majorityQuorumsFin3).1, fun Q hQ =>
    (synodQuorumProtocol_safeCohort_crashStop majorityQuorumsFin3).2 Q
      ⟨⟨Q, hQ, Finset.Subset.rfl⟩, ⟨Q, hQ, Finset.Subset.rfl⟩⟩⟩

example :
    let qs := majorityQuorums (P := Fin 5) (t := 2) (by decide)
    (synodQuorumProtocol (V := ℕ) qs).SafeConsensus ∧
      ∀ Q ∈ qs.prepareQuorums, (synodQuorumProtocol (V := ℕ) qs).CanDecideIn Q :=
  ⟨(synodQuorumProtocol_safeCohort_crashStop _).1, fun Q hQ =>
    (synodQuorumProtocol_safeCohort_crashStop _).2 Q
      ⟨⟨Q, hQ, Finset.Subset.rfl⟩, ⟨Q, hQ, Finset.Subset.rfl⟩⟩⟩

end CslibFrontierTests.Distributed.Paxos
