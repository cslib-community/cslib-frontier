/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Paxos.Liveness.Duelling
public import CslibFrontier.Computability.Distributed.Paxos.Liveness.SoleLeaderDefs
public import CslibFrontier.Computability.Distributed.Paxos.Liveness.SoleLeader
public import CslibFrontier.Computability.Distributed.Paxos.Liveness.SoleLeaderWitness
public import CslibFrontier.Computability.Distributed.Paxos.Liveness.AsyncQuorumProtocol
public import CslibFrontier.Computability.Distributed.Paxos.Liveness.SynodProtocol
public import CslibFrontier.Computability.Distributed.Paxos.Liveness.SynodProtocolCohort

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
   one live cohort `Q` containing a prepare and an accept quorum (`qs.Supports Q`), and a live
   learner `l` are delivered without loss, `l` learns
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
   both safety and progress in every cohort containing a quorum of each phase
   (`synodQuorumProtocol_safeCohort_crashStop`).

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
* `Cslib.Distributed.Paxos.paxos_liveness_from_phase2a_crashStop`: phase-2 progress using only
  an accept quorum after the proposal is sent, without requiring a live prepare quorum.
* `Cslib.Distributed.Paxos.paxos_liveness_of_sole_leader_crashStop`: conditional crash-stop 4-phase
  learner termination step under a live sole leader at a fresh highest ballot.
* `Cslib.Distributed.Paxos.exists_sole_leader_execution_crashStop`: constructive 4-phase execution
  witness from any reachable crash-stop state (with `[Finite Acceptor]`).
* `Cslib.Distributed.Paxos.not_synod_safe_of_disjoint_quorums`: split-brain impossibility for any
  `AsyncQuorumProtocol` admitting progress on disjoint subsets `Q₁, Q₂`.
* `Cslib.Distributed.Paxos.not_safeSingleQuorum_of_card_le_two_mul`: impossibility of `t`-crash
  single-quorum progress when `2 ≤ Fintype.card P ≤ 2 * t`.
* `Cslib.Distributed.Paxos.synodQuorumProtocol_safeCohort_crashStop`: crash-stop step showing
  `synodQuorumProtocol qs` achieves `SafeConsensus` and `CanDecideIn Q` whenever `qs.Supports Q`.

## References

* [L. Lamport, *The Part-Time Parliament*][Lamport1998]
* [L. Lamport, *Paxos Made Simple*][Lamport2001]
* [H. Howard, D. Malkhi, and A. Spiegelman, *Flexible Paxos*][HowardMalkhiSpiegelman2017]
-/
