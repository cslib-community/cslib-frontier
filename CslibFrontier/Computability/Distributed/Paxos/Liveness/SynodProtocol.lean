/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Paxos.Basic
public import CslibFrontier.Computability.Distributed.Paxos.Liveness.AsyncQuorumProtocol

/-!
# Co-located crash-stop Synod instantiated as `AsyncQuorumProtocol`

Instantiates Single-Decree Synod with co-located proposer, acceptor, and learner state per node
as `synodQuorumProtocol`.

## Main definitions

* `Cslib.Distributed.Paxos.SynodNodeState`, `Cslib.Distributed.Paxos.synodQuorumProtocol`:
  co-located crash-stop Single-Decree Synod instantiated as an `AsyncQuorumProtocol`.
-/

public section

namespace Cslib.Distributed.Paxos

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
            if !st.state.prop.proposed && decide (∃ Q ∈ qs.prepareQuorums, Q ⊆ promised') then
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
              decide (∃ Q ∈ qs.acceptQuorums, ∀ a' ∈ Q, ⟨a', b, v⟩ ∈ received') then
            some v
          else st.state.learn.learned
        { nextState :=
            { st.state with
              learn := { st.state.learn with received := received', learned := learned' } }
          outgoing := ∅
          decideVal := learned' }
      else { nextState := st.state, outgoing := ∅, decideVal := none }


end Cslib.Distributed.Paxos
