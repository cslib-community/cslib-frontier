/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Paxos.Basic
public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-!
# Ballot freshness and fairness predicates for sole-leader progress

Defines `Msg.ballot`, `BallotsBelow`, and `LiveAndLossless`, shared by conditional sole-leader
liveness, the constructive 4-phase witness, and clients of `Liveness`.

## Main definitions

* `Cslib.Distributed.Paxos.Msg.ballot`, `Cslib.Distributed.Paxos.BallotsBelow`,
  `Cslib.Distributed.Paxos.LiveAndLossless`: ballot extractor, fresh-ballot dominance predicate, and
  live cohort / lossless ballot-delivery hypothesis for conditional sole-leader progress.
-/

public section

namespace Cslib.Distributed.Paxos

open Cslib Cslib.ωSequence

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

/-- Live cohort and lossless eventual delivery for ballot `b` among leader `p`, cohort `Q`, and
learner `l` along infinite execution `(ss, xs)`. -/
structure LiveAndLossless {Proposer Acceptor Learner V : Type*}
    (b : Ballot Proposer) (p : Proposer) (Q : Finset Acceptor) (l : Learner)
    (ss : ωSequence (SynodState Proposer Acceptor Learner V))
    (xs : ωSequence (SynodAction Proposer Acceptor Learner V)) : Prop where
  /-- Proposer `p` remains live throughout the execution. -/
  proposer_live : ∀ n, ((ss n).proposers p).crashed = false
  /-- Every acceptor in cohort `Q` remains live throughout the execution. -/
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

end Cslib.Distributed.Paxos
