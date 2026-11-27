/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.Paxos.Basic
import CslibFrontierTests.Computability.Distributed.Paxos

/-!
# Flexible Paxos client checks

Ordinary imports exercise separate prepare and accept quorum families. On four acceptors, three
promises suffice to prepare a ballot and two votes suffice to decide. A checked execution carries
an earlier decision from one accept pair to a disjoint accept pair, even after two acceptors crash
between the new ballot's prepare and accept phases. A grid instance allows disjoint quorums within
both phases while retaining cross-phase intersection.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.FlexiblePaxos

open Cslib Cslib.Distributed.Paxos
open CslibFrontierTests.Distributed.Paxos

private def fourQuorums : QuorumSystem (Fin 4) :=
  thresholdQuorums (qPrepare := 3) (qAccept := 2) (by decide) (by decide) (by decide)

example : ({0, 1, 2} : Finset (Fin 4)) ∈ fourQuorums.prepareQuorums ∧
    ({0, 1} : Finset (Fin 4)) ∉ fourQuorums.prepareQuorums ∧
    ({0, 1} : Finset (Fin 4)) ∈ fourQuorums.acceptQuorums ∧
    ({2, 3} : Finset (Fin 4)) ∈ fourQuorums.acceptQuorums ∧
    Disjoint ({0, 1} : Finset (Fin 4)) {2, 3} := by
  decide

private def inputs : Fin 2 → Bool
  | 0 => true
  | 1 => false

/-- The first ballot decides `true` on acceptors `{0, 1}`. The higher ballot prepares with
`{1, 2, 3}`, learns the earlier value from acceptor `1`, and decides on the disjoint pair `{2, 3}`
after both earlier voters crash. -/
private def actions : List (SynodAction (Fin 2) (Fin 4) (Fin 2) Bool) :=
  let b₀ : Ballot (Fin 2) := ⟨0, 0⟩
  let b₁ : Ballot (Fin 2) := ⟨0, 1⟩
  [ .prepare 0 0
  , .recvPhase1a 0 b₀
  , .recvPhase1a 1 b₀
  , .recvPhase1a 2 b₀
  , .recvPhase1b 0 0 b₀ none
  , .recvPhase1b 0 1 b₀ none
  , .recvPhase1b 0 2 b₀ none
  , .recvPhase2a 0 b₀ true
  , .recvPhase2a 1 b₀ true
  , .recvPhase2b 0 0 b₀ true
  , .recvPhase2b 0 1 b₀ true
  , .prepare 1 0
  , .recvPhase1a 1 b₁
  , .recvPhase1a 2 b₁
  , .recvPhase1a 3 b₁
  , .recvPhase1b 1 2 b₁ none
  , .recvPhase1b 1 3 b₁ none
  , .recvPhase1b 1 1 b₁ (some ⟨b₀, true⟩)
  , .crashAcceptor 0
  , .crashAcceptor 1
  , .recvPhase2a 2 b₁ true
  , .recvPhase2a 3 b₁ true
  , .recvPhase2b 1 2 b₁ true
  , .recvPhase2b 1 3 b₁ true ]

private def finalState : SynodState (Fin 2) (Fin 4) (Fin 2) Bool :=
  runTrace fourQuorums (initState inputs) actions

private theorem actions_valid :
    validTrace fourQuorums (initState (Learner := Fin 2) inputs) actions = true := by
  decide

private theorem finalState_reachable : Reachable fourQuorums inputs finalState :=
  ⟨actions, mTr_of_validTrace _ _ _ actions_valid⟩

example :
    (finalState.learners 0).learned = some true ∧
    (finalState.learners 1).learned = some true ∧
    (finalState.proposers 1).maxVote = some ⟨⟨0, 0⟩, true⟩ ∧
    Msg.phase2a ⟨0, 1⟩ true ∈ finalState.msgs ∧
    Msg.phase2a ⟨0, 1⟩ false ∉ finalState.msgs := by
  decide

-- Only two acceptors remain alive: they suffice to complete the prepared ballot, although no
-- prepare quorum remains available to start a fresh ballot.
example :
    (finalState.acceptors 0).crashed = true ∧
    (finalState.acceptors 1).crashed = true ∧
    (finalState.acceptors 2).crashed = false ∧
    (finalState.acceptors 3).crashed = false ∧
    (∀ Q ∈ fourQuorums.prepareQuorums, ∃ a ∈ Q, (finalState.acceptors a).crashed = true) ∧
    (∃ Q ∈ fourQuorums.acceptQuorums, ∀ a ∈ Q, (finalState.acceptors a).crashed = false) := by
  decide

-- Apply the exported safety theorem to the computed, reachable execution.
example {l₁ l₂ : Fin 2} {b₁ b₂ : Ballot (Fin 2)} {v₁ v₂ : Bool}
    (h₁ : finalState.LearnedAt fourQuorums l₁ b₁ v₁)
    (h₂ : finalState.LearnedAt fourQuorums l₂ b₂ v₂) : v₁ = v₂ :=
  paxos_agreement_crashStop fourQuorums finalState_reachable h₁ h₂

/-! ### A grid with disjoint prepare quorums and disjoint accept quorums -/

private def gridQuorums : QuorumSystem (Fin 4) where
  prepareQuorums := {{0, 1}, {2, 3}}
  acceptQuorums := {{0, 2}, {1, 3}}
  prepare_nonempty := by decide
  accept_nonempty := by decide
  inter_nonempty := by decide

example :
    ({0, 1} : Finset (Fin 4)) ∈ gridQuorums.prepareQuorums ∧
    ({2, 3} : Finset (Fin 4)) ∈ gridQuorums.prepareQuorums ∧
    Disjoint ({0, 1} : Finset (Fin 4)) {2, 3} ∧
    ({0, 2} : Finset (Fin 4)) ∈ gridQuorums.acceptQuorums ∧
    ({1, 3} : Finset (Fin 4)) ∈ gridQuorums.acceptQuorums ∧
    Disjoint ({0, 2} : Finset (Fin 4)) {1, 3} := by
  decide

-- A cohort that supports both phases can start from scratch. An accept quorum alone cannot.
example : gridQuorums.Supports {0, 1, 2} ∧ ¬ gridQuorums.Supports {0, 2} := by
  decide

-- At the excluded equality boundary, two cardinality-two sets can have no intersection.
example : ∃ Q₁ Q₂ : Finset (Fin 4),
    2 ≤ Q₁.card ∧ 2 ≤ Q₂.card ∧ Disjoint Q₁ Q₂ :=
  ⟨{0, 1}, {2, 3}, by decide, by decide, by decide⟩

example : ¬ ∃ qs : QuorumSystem (Fin 4),
    (∀ Q, Q ∈ qs.prepareQuorums ↔ 2 ≤ Q.card) ∧
    (∀ Q, Q ∈ qs.acceptQuorums ↔ 2 ≤ Q.card) := by
  rw [exists_thresholdQuorums_iff (by decide) (by decide)]
  decide

-- Four acceptors admit independent failure budgets of one in prepare and two in accept, but
-- no quorum system can tolerate every two-node failure separately in both phases.
example : ∃ qs : QuorumSystem (Fin 4),
    qs.AvailableFor {F | F.card ≤ 1} {F | F.card ≤ 2} :=
  (exists_availableFor_card_iff 1 2).mpr (by decide)

example : ¬ ∃ qs : QuorumSystem (Fin 4),
    qs.AvailableFor {F | F.card ≤ 2} {F | F.card ≤ 2} := by
  rw [exists_availableFor_card_iff]
  decide

end CslibFrontierTests.Distributed.FlexiblePaxos
