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
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Crash-Stop Single-Decree Synod Protocol Step

This module formalizes a **crash-stop intermediate step** towards Lamport's Single-Decree Synod
consensus protocol (§2 of [Lamport1998]; §2 of [Lamport2001]), and **not** the crash-recovery cited
results of those papers. Over abstract intersecting quorum systems (`QuorumSystem`), we model the
four Synod phases (`Phase1a`/`1b`/`2a`/`2b`) as a ghost-free asynchronous message-passing labelled
transition system (`Cslib.LTS`) allowing arbitrary message reordering, duplication, packet
loss/omission, and permanent **crash-stop** node failures (`crashed : Bool`).

**Step scope and model deviations:** In [Lamport1998] (§1.3, §2.3, Appendix A2 `Forget`) and
[Lamport2001] (§2.1, §2.5), nodes may fail by stopping and later restart using persistent stable
storage (`lastTried`, `maxBal`, `maxVoted`) while losing volatile per-round state; here crashes are
permanent (`crashed : Bool`), while `.prepare p r` resets per-round proposer fields (`proposed`,
`promised`, `maxVote`). Phase 2b uses [Lamport2001] §2.2's `mb ≤ b` voting guard (`allowsVote`,
updating `maxBal := some b`) rather than [Lamport1998] §2.3 step (4)'s `b = nextBal[q]`. Section 3
Multi-Paxos state-machine / ledger replication also remains open.

The protocol state (`SynodState`) is completely ghost-free: proposers, acceptors, and learners store
only the operational registers read by protocol transitions, and packet drops genuinely erase
messages from the live network buffer `msgs`. Safety invariants (the crash-stop `P2^c` / `B3`
quorum-witness condition on `Phase2a` proposals and `P1^a` promise–vote monotonicity) are proved
inductively over a non-dropping shadow execution (`traceMsgs`) and projected onto all reachable
states via network monotonicity.

## Main definitions

* `Cslib.Distributed.Paxos.QuorumSystem`: finite family of quorums over acceptors `P` that is
  nonempty and pairwise intersecting.
* `Cslib.Distributed.Paxos.majorityQuorums`: crash-tolerant strict-majority quorum system
  (`Fintype.card P - t ≤ Q.card` when `2 * t < Fintype.card P`).
* `Cslib.Distributed.Paxos.Ballot`: lexicographically ordered `(round, proposer)` ballot numbers
  uniquely owned by `proposer`.
* `Cslib.Distributed.Paxos.Vote`: `(ballot, value)` pair accepted in Phase 2b and reported in
  Phase 1b.
* `Cslib.Distributed.Paxos.Msg`: Synod protocol messages (`phase1a`, `phase1b`, `phase2a`,
  `phase2b`).
* `Cslib.Distributed.Paxos.ProposerState`, `Cslib.Distributed.Paxos.AcceptorState`,
  `Cslib.Distributed.Paxos.AcceptedVote`, `Cslib.Distributed.Paxos.LearnerState`,
  `Cslib.Distributed.Paxos.SynodState`: ghost-free local and global protocol states.
* `Cslib.Distributed.Paxos.initState`: initial global configuration for proposer input assignment
  `inputs`.
* `Cslib.Distributed.Paxos.SynodAction`, `Cslib.Distributed.Paxos.synodEnabled`,
  `Cslib.Distributed.Paxos.synodStep`, `Cslib.Distributed.Paxos.synodLts`: asynchronous crash-stop
  Synod transitions and `Cslib.LTS` semantics with reordering, duplication, `.drop`, `.crash*`, and
  `.stutter`.
* `Cslib.Distributed.Paxos.Reachable`, `Cslib.Distributed.Paxos.traceMsgs`: reachable states and
  packets emitted along an execution trace.
* `Cslib.Distributed.Paxos.ChosenAt`, `Cslib.Distributed.Paxos.SynodState.LearnedAt`: quorum
  acceptance in Phase 2b and quorum learning at a learner.

## Main results

* `Cslib.Distributed.Paxos.phase2a_unique_of_ballot_crashStop`: crash-stop step showing at most one
  value is ever proposed in `Phase2a` for any ballot `b`.
* `Cslib.Distributed.Paxos.chosenAt_implies_higher_phase2a_eq_crashStop`: crash-stop step for
  Lamport's inductive ballot-choice invariant—once a quorum has voted `(b, v)`, every
  `Phase2a(b', v')` emitted in the trace with `b ≤ b'` satisfies `v' = v`.
* `Cslib.Distributed.Paxos.paxos_agreement_crashStop`: crash-stop global learner agreement step
  across any two learners and any two ballots in any reachable state.
* `Cslib.Distributed.Paxos.paxos_validity_crashStop`: crash-stop nontriviality/validity step—any
  value learned by a learner in a reachable state equals some proposer's initial input.

## References

* [L. Lamport, *The Part-Time Parliament*][Lamport1998]
* [L. Lamport, *Paxos Made Simple*][Lamport2001]
-/

public section

namespace Cslib.Distributed.Paxos

open Cslib

/-! ### Quorum systems and strict-majority instantiation -/

/-- A quorum system over processes/acceptors `P`: a nonempty finite collection of subsets whose
members pairwise intersect ([Lamport1998]; [Lamport2001]). -/
structure QuorumSystem (P : Type*) [DecidableEq P] where
  /-- Finite family of quorum subsets of `P`. -/
  quorums : Finset (Finset P)
  /-- At least one quorum exists. -/
  nonempty : quorums.Nonempty
  /-- Every pair of quorums shares at least one member. -/
  inter_nonempty : ∀ Q₁ ∈ quorums, ∀ Q₂ ∈ quorums, (Q₁ ∩ Q₂).Nonempty

/-- Every quorum in a `QuorumSystem` is nonempty, by intersecting it with itself. -/
theorem QuorumSystem.quorum_nonempty {P : Type*} [DecidableEq P] (qs : QuorumSystem P)
    {Q : Finset P} (hQ : Q ∈ qs.quorums) : Q.Nonempty := by
  have hinter := qs.inter_nonempty Q hQ Q hQ
  simpa only [Finset.inter_self] using hinter

/-- Crash-tolerant strict-majority quorums over a finite acceptor set `P` when `2 * t < |P|`:
subsets of cardinality at least `|P| - t`. -/
@[expose] def majorityQuorums {P : Type*} [Fintype P] [DecidableEq P] {t : ℕ}
    (ht : 2 * t < Fintype.card P) : QuorumSystem P where
  quorums := Finset.univ.powerset.filter fun Q => Fintype.card P - t ≤ Q.card
  nonempty := ⟨Finset.univ, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), by simp only [Finset.card_univ]; omega⟩⟩
  inter_nonempty := by
    intro Q₁ h₁ Q₂ h₂
    have hcard₁ : Fintype.card P - t ≤ Q₁.card := (Finset.mem_filter.mp h₁).2
    have hcard₂ : Fintype.card P - t ≤ Q₂.card := (Finset.mem_filter.mp h₂).2
    have hunion : (Q₁ ∪ Q₂).card ≤ Fintype.card P := Finset.card_le_univ (Q₁ ∪ Q₂)
    have hsum := Finset.card_union_add_card_inter Q₁ Q₂
    exact Finset.card_pos.mp (by omega)

@[simp]
theorem mem_majorityQuorums_iff {P : Type*} [Fintype P] [DecidableEq P] {t : ℕ}
    (ht : 2 * t < Fintype.card P) (Q : Finset P) :
    Q ∈ (majorityQuorums ht).quorums ↔ Fintype.card P - t ≤ Q.card := by
  simp only [majorityQuorums, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]

/-! ### Proposer-owned ballots and protocol messages -/

/-- A ballot number `(round, proposer)` uniquely owned by `proposer`, ordered lexicographically
first by `round` and then by `proposer` ([Lamport1998]; [Lamport2001]). -/
@[ext]
structure Ballot (Proposer : Type*) where
  /-- Nonnegative round / sequence number. -/
  round : ℕ
  /-- Unique proposer owning this ballot. -/
  proposer : Proposer
  deriving @[expose] DecidableEq

/-- Order-embedding of `Ballot Proposer` into the lexicographic product `ℕ ×ₗ Proposer`. -/
@[expose] def Ballot.toLexProd {Proposer : Type*} (b : Ballot Proposer) : ℕ ×ₗ Proposer :=
  toLex (b.round, b.proposer)

instance instLinearOrderBallot {Proposer : Type*} [LinearOrder Proposer] :
    LinearOrder (Ballot Proposer) where
  le a b := a.toLexProd ≤ b.toLexProd
  lt a b := a.toLexProd < b.toLexProd
  le_refl a := le_refl a.toLexProd
  le_trans a b c := le_trans (a := a.toLexProd) (b := b.toLexProd) (c := c.toLexProd)
  lt_iff_le_not_ge a b := lt_iff_le_not_ge (a := a.toLexProd) (b := b.toLexProd)
  le_antisymm a b h₁ h₂ := by
    have h := Equiv.injective ofLex (le_antisymm h₁ h₂)
    cases a; cases b; cases h; rfl
  le_total a b := le_total a.toLexProd b.toLexProd
  max a b := if a.toLexProd ≤ b.toLexProd then b else a
  max_def a b := rfl
  min a b := if a.toLexProd ≤ b.toLexProd then a else b
  min_def a b := rfl
  compare a b := compare a.toLexProd b.toLexProd
  compare_eq_compareOfLessAndEq a b := by
    have heq : a.toLexProd = b.toLexProd ↔ a = b :=
      ⟨fun h => by have h' := Equiv.injective ofLex h; cases a; cases b; cases h'; rfl,
        congrArg Ballot.toLexProd⟩
    rw [LinearOrder.compare_eq_compareOfLessAndEq]
    change (if a.toLexProd < b.toLexProd then Ordering.lt
      else if a.toLexProd = b.toLexProd then Ordering.eq else Ordering.gt) =
      (if a.toLexProd < b.toLexProd then Ordering.lt
      else if a = b then Ordering.eq else Ordering.gt)
    simp only [heq]
  toDecidableLE a b := inferInstanceAs (Decidable (a.toLexProd ≤ b.toLexProd))
  toDecidableLT a b := inferInstanceAs (Decidable (a.toLexProd < b.toLexProd))
  toDecidableEq := inferInstance

@[simp]
theorem Ballot.lt_iff {Proposer : Type*} [LinearOrder Proposer] (a b : Ballot Proposer) :
    a < b ↔ a.round < b.round ∨ (a.round = b.round ∧ a.proposer < b.proposer) :=
  Prod.Lex.lt_iff (x := a.toLexProd) (y := b.toLexProd)

@[simp]
theorem Ballot.le_iff {Proposer : Type*} [LinearOrder Proposer] (a b : Ballot Proposer) :
    a ≤ b ↔ a.round < b.round ∨ (a.round = b.round ∧ a.proposer ≤ b.proposer) :=
  Prod.Lex.le_iff (x := a.toLexProd) (y := b.toLexProd)

/-- A vote `(ballot, value)` cast by an acceptor in Phase 2b and reported in Phase 1b. -/
@[ext]
structure Vote (Proposer V : Type*) where
  /-- Ballot at which the vote was cast. -/
  ballot : Ballot Proposer
  /-- Decree value accepted at `ballot`. -/
  value : V
  deriving @[expose] DecidableEq

/-- Network packets of Lamport's Single-Decree Synod protocol ([Lamport1998]; [Lamport2001]). -/
inductive Msg (Proposer Acceptor V : Type*) where
  /-- Phase 1a (`prepare`): proposer requests promises for ballot `b`. -/
  | phase1a (b : Ballot Proposer)
  /-- Phase 1b (`promise`): acceptor `a` promises not to vote in ballots `< b`, reporting its
  highest-numbered prior vote `maxVoted`. -/
  | phase1b (a : Acceptor) (b : Ballot Proposer) (maxVoted : Option (Vote Proposer V))
  /-- Phase 2a (`accept`): proposer of ballot `b` proposes decree value `v`. -/
  | phase2a (b : Ballot Proposer) (v : V)
  /-- Phase 2b (`accepted`): acceptor `a` casts its vote for `(b, v)`. -/
  | phase2b (a : Acceptor) (b : Ballot Proposer) (v : V)
  deriving @[expose] DecidableEq

/-! ### Ghost-free node and global protocol states -/

/-- Operational local state of a proposer (zero ghost history). -/
@[ext]
structure ProposerState (Proposer Acceptor V : Type*) where
  /-- Proposer's initial client input value. -/
  input : V
  /-- Active ballot round owned by this proposer (`none` before its first prepare). -/
  round : Option ℕ
  /-- Whether this proposer has already emitted `Phase2a` in its current `round`. -/
  proposed : Bool
  /-- Acceptors from which this proposer has received `Phase1b` for its current `round`. -/
  promised : Finset Acceptor
  /-- Highest-ballot vote reported among `promised` acceptors in the current `round`. -/
  maxVote : Option (Vote Proposer V)
  /-- Whether this proposer has crashed. -/
  crashed : Bool
  deriving @[expose] DecidableEq

/-- Operational local state of an acceptor (zero ghost history). -/
@[ext]
structure AcceptorState (Proposer V : Type*) where
  /-- Highest ballot promised in Phase 1b or voted in Phase 2b (`none` initially). -/
  maxBal : Option (Ballot Proposer)
  /-- Highest-ballot vote cast in Phase 2b (`none` before first vote). -/
  maxVoted : Option (Vote Proposer V)
  /-- Whether this acceptor has crashed. -/
  crashed : Bool
  deriving @[expose] DecidableEq

/-- A Phase 2b vote `(acceptor, ballot, value)` recorded by a learner. -/
@[ext]
structure AcceptedVote (Proposer Acceptor V : Type*) where
  /-- Acceptor that sent `Phase2b`. -/
  acceptor : Acceptor
  /-- Ballot number of the vote. -/
  ballot : Ballot Proposer
  /-- Accepted decree value. -/
  value : V
  deriving @[expose] DecidableEq

/-- Operational local state of a learner (zero ghost history). -/
@[ext]
structure LearnerState (Proposer Acceptor V : Type*) where
  /-- Phase 2b votes received so far by this learner. -/
  received : Finset (AcceptedVote Proposer Acceptor V)
  /-- Write-once learned decree value (`none` until a quorum of matching Phase 2b votes arrives). -/
  learned : Option V
  /-- Whether this learner has crashed. -/
  crashed : Bool
  deriving @[expose] DecidableEq

/-- Ghost-free global configuration of the Single-Decree Synod protocol: live network packet set
paired with local proposer, acceptor, and learner states. -/
@[ext]
structure SynodState (Proposer Acceptor Learner V : Type*) where
  /-- Currently in-flight packets on the asynchronous network (packets may be reordered,
  redelivered/duplicated, or erased by `.drop`). -/
  msgs : Finset (Msg Proposer Acceptor V)
  /-- Local state of each proposer. -/
  proposers : Proposer → ProposerState Proposer Acceptor V
  /-- Local state of each acceptor. -/
  acceptors : Acceptor → AcceptorState Proposer V
  /-- Local state of each learner. -/
  learners : Learner → LearnerState Proposer Acceptor V

/-- Initial global state for proposer input assignment `inputs`. -/
@[expose] def initState {Proposer Acceptor Learner V : Type*} (inputs : Proposer → V) :
    SynodState Proposer Acceptor Learner V where
  msgs := ∅
  proposers p :=
    { input := inputs p
      round := none
      proposed := false
      promised := ∅
      maxVote := none
      crashed := false }
  acceptors _ := { maxBal := none, maxVoted := none, crashed := false }
  learners _ := { received := ∅, learned := none, crashed := false }

/-! ### Asynchronous transitions and `Cslib.LTS` -/

/-- Transition labels of the asynchronous Synod LTS, covering all four Paxos phases plus packet
loss (`.drop`), crash-stop failures (`.crash*`), and stuttering (`.stutter`). -/
inductive SynodAction (Proposer Acceptor Learner V : Type*) where
  /-- Proposer `p` initiates Phase 1a at a fresh strictly higher round `r`. -/
  | prepare (p : Proposer) (r : ℕ)
  /-- Acceptor `a` processes `Phase1a(b)` from the network. -/
  | recvPhase1a (a : Acceptor) (b : Ballot Proposer)
  /-- Proposer `p` processes `Phase1b(a, b, mv)` from the network (and emits `Phase2a` upon
  completing a quorum of promises). -/
  | recvPhase1b (p : Proposer) (a : Acceptor) (b : Ballot Proposer)
      (mv : Option (Vote Proposer V))
  /-- Acceptor `a` processes `Phase2a(b, v)` from the network. -/
  | recvPhase2a (a : Acceptor) (b : Ballot Proposer) (v : V)
  /-- Learner `l` processes `Phase2b(a, b, v)` from the network. -/
  | recvPhase2b (l : Learner) (a : Acceptor) (b : Ballot Proposer) (v : V)
  /-- Network drops packet `m` from `msgs`. -/
  | drop (m : Msg Proposer Acceptor V)
  /-- Proposer `p` suffers a crash-stop failure. -/
  | crashProposer (p : Proposer)
  /-- Acceptor `a` suffers a crash-stop failure. -/
  | crashAcceptor (a : Acceptor)
  /-- Learner `l` suffers a crash-stop failure. -/
  | crashLearner (l : Learner)
  /-- Dummy stuttering step leaving the global state unchanged. -/
  | stutter
  deriving @[expose] DecidableEq

/-- Combine a proposer's running highest vote with a newly reported `Phase1b` vote. -/
@[expose] def mergeVote {Proposer V : Type*} [LinearOrder Proposer]
    (cur incoming : Option (Vote Proposer V)) : Option (Vote Proposer V) :=
  match cur, incoming with
  | none, mv => mv
  | some vt, none => some vt
  | some vt₁, some vt₂ => if vt₁.ballot < vt₂.ballot then some vt₂ else some vt₁

/-- Whether ballot `b` strictly exceeds an acceptor's `maxBal` (the Phase 1b promise condition). -/
@[expose] def aboveMaxBal {Proposer : Type*} [LinearOrder Proposer]
    (maxBal : Option (Ballot Proposer)) (b : Ballot Proposer) : Bool :=
  match maxBal with
  | none => true
  | some mb => decide (mb < b)

/-- Whether ballot `b` is at least an acceptor's `maxBal` (the Phase 2b voting condition). -/
@[expose] def allowsVote {Proposer : Type*} [LinearOrder Proposer]
    (maxBal : Option (Ballot Proposer)) (b : Ballot Proposer) : Bool :=
  match maxBal with
  | none => true
  | some mb => decide (mb ≤ b)

/-- Guard predicate specifying when `act` is enabled in state `s`. -/
@[expose] def synodEnabled {Proposer Acceptor Learner V : Type*}
    (s : SynodState Proposer Acceptor Learner V)
    (act : SynodAction Proposer Acceptor Learner V) : Prop :=
  match act with
  | .prepare p r =>
    (s.proposers p).crashed = false ∧
      match (s.proposers p).round with
      | none => True
      | some r₀ => r₀ < r
  | .recvPhase1a a b => (s.acceptors a).crashed = false ∧ Msg.phase1a b ∈ s.msgs
  | .recvPhase1b p a b mv => (s.proposers p).crashed = false ∧ Msg.phase1b a b mv ∈ s.msgs
  | .recvPhase2a a b v => (s.acceptors a).crashed = false ∧ Msg.phase2a b v ∈ s.msgs
  | .recvPhase2b l a b v => (s.learners l).crashed = false ∧ Msg.phase2b a b v ∈ s.msgs
  | .drop m => m ∈ s.msgs
  | .crashProposer _ => True
  | .crashAcceptor _ => True
  | .crashLearner _ => True
  | .stutter => True

instance instDecidableSynodEnabled {Proposer Acceptor Learner V : Type*}
    [DecidableEq Proposer] [DecidableEq Acceptor] [DecidableEq V]
    (s : SynodState Proposer Acceptor Learner V)
    (act : SynodAction Proposer Acceptor Learner V) :
    Decidable (synodEnabled s act) := by
  cases act <;> dsimp only [synodEnabled]
  case prepare p r => cases (s.proposers p).round <;> infer_instance
  all_goals infer_instance

/-- Shared transition kernel parameterized by whether `.drop` erases from `msgs`. -/
@[expose] def synodStepCore {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    (dropErases : Bool) (qs : QuorumSystem Acceptor)
    (s : SynodState Proposer Acceptor Learner V)
    (act : SynodAction Proposer Acceptor Learner V) :
    SynodState Proposer Acceptor Learner V :=
  match act with
  | .prepare p r =>
    let st := s.proposers p
    let pst' : ProposerState Proposer Acceptor V :=
      { st with round := some r, proposed := false, promised := ∅, maxVote := none }
    { s with
      msgs := insert (Msg.phase1a ⟨r, p⟩) s.msgs
      proposers := fun q => if q = p then pst' else s.proposers q }
  | .recvPhase1a a b =>
    let st := s.acceptors a
    if aboveMaxBal st.maxBal b then
      { s with
        msgs := insert (Msg.phase1b a b st.maxVoted) s.msgs
        acceptors := fun q => if q = a then { st with maxBal := some b } else s.acceptors q }
    else s
  | .recvPhase1b p a b mv =>
    let st := s.proposers p
    match st.round with
    | none => s
    | some r =>
      if b = ⟨r, p⟩ ∧ a ∉ st.promised then
        let promised' := insert a st.promised
        let maxVote' := mergeVote st.maxVote mv
        if !st.proposed && decide (∃ Q ∈ qs.quorums, Q ⊆ promised') then
          let val := match maxVote' with
            | some vt => vt.value
            | none => st.input
          let pst' : ProposerState Proposer Acceptor V :=
            { st with proposed := true, promised := promised', maxVote := maxVote' }
          { s with
            msgs := insert (Msg.phase2a ⟨r, p⟩ val) s.msgs
            proposers := fun q => if q = p then pst' else s.proposers q }
        else
          let pst' : ProposerState Proposer Acceptor V :=
            { st with promised := promised', maxVote := maxVote' }
          { s with proposers := fun q => if q = p then pst' else s.proposers q }
      else s
  | .recvPhase2a a b v =>
    let st := s.acceptors a
    if allowsVote st.maxBal b then
      let ast' : AcceptorState Proposer V :=
        { st with maxBal := some b, maxVoted := some ⟨b, v⟩ }
      { s with
        msgs := insert (Msg.phase2b a b v) s.msgs
        acceptors := fun q => if q = a then ast' else s.acceptors q }
    else s
  | .recvPhase2b l a b v =>
    let st := s.learners l
    let received' := insert ⟨a, b, v⟩ st.received
    let learned' :=
      if st.learned.isNone && decide (∃ Q ∈ qs.quorums, ∀ a' ∈ Q, ⟨a', b, v⟩ ∈ received') then
        some v
      else st.learned
    { s with
      learners := fun q =>
        if q = l then { st with received := received', learned := learned' } else s.learners q }
  | .drop m =>
    if dropErases then { s with msgs := s.msgs.erase m } else s
  | .crashProposer p =>
    { s with proposers := fun q => if q = p then { s.proposers p with crashed := true }
        else s.proposers q }
  | .crashAcceptor a =>
    { s with acceptors := fun q => if q = a then { s.acceptors a with crashed := true }
        else s.acceptors q }
  | .crashLearner l =>
    { s with learners := fun q => if q = l then { s.learners l with crashed := true }
        else s.learners q }
  | .stutter => s

/-- State transition function of the asynchronous Single-Decree Synod protocol. -/
@[expose] def synodStep {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    (qs : QuorumSystem Acceptor) (s : SynodState Proposer Acceptor Learner V)
    (act : SynodAction Proposer Acceptor Learner V) :
    SynodState Proposer Acceptor Learner V :=
  synodStepCore true qs s act

/-- Asynchronous labelled transition system (`Cslib.LTS`) of Lamport's Single-Decree Synod
protocol. -/
@[expose] def synodLts {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    (qs : QuorumSystem Acceptor) :
    LTS (SynodState Proposer Acceptor Learner V) (SynodAction Proposer Acceptor Learner V) where
  Tr s act s' := synodEnabled s act ∧ s' = synodStep qs s act

instance instDeterministicSynodLts {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    (qs : QuorumSystem Acceptor) :
    (synodLts qs (Proposer := Proposer) (Learner := Learner) (V := V)).Deterministic where
  deterministic _ _ _ _ h₁ h₂ := h₁.2.trans h₂.2.symm

/-- `Reachable qs inputs s` holds when `s` is reachable from `initState inputs` in `synodLts qs`. -/
@[expose] def Reachable {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    (qs : QuorumSystem Acceptor) (inputs : Proposer → V)
    (s : SynodState Proposer Acceptor Learner V) : Prop :=
  (synodLts qs).CanReach (initState inputs) s

/-- Initial state `initState inputs` is reachable. -/
theorem reachable_initState {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    (qs : QuorumSystem Acceptor) (inputs : Proposer → V) :
    Reachable qs inputs (initState (Learner := Learner) inputs) :=
  LTS.CanReach.refl (synodLts qs) (initState inputs)

/-- Transitivity of Synod reachability along multi-step transitions. -/
theorem Reachable.trans {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    {qs : QuorumSystem Acceptor} {inputs : Proposer → V}
    {s s' : SynodState Proposer Acceptor Learner V}
    (hs : Reachable qs inputs s) (hreach : (synodLts qs).CanReach s s') :
    Reachable qs inputs s' := by
  obtain ⟨xl, hxl⟩ := hs
  obtain ⟨yl, hyl⟩ := hreach
  exact ⟨xl ++ yl, LTS.MTr.comp (synodLts qs) hxl hyl⟩

/-- The cumulative finite set of packets emitted along execution trace `xl` from `s₀` (ignoring
`.drop` erasures). -/
@[expose] def traceMsgs {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    (qs : QuorumSystem Acceptor) (s₀ : SynodState Proposer Acceptor Learner V)
    (xl : List (SynodAction Proposer Acceptor Learner V)) :
    Finset (Msg Proposer Acceptor V) :=
  (xl.foldl (synodStepCore false qs) s₀).msgs

/-- Value `v` is *chosen at ballot `b`* relative to packet set `msgs` when every acceptor in some
quorum `Q ∈ qs.quorums` has emitted `Phase2b(a, b, v)`. -/
@[expose] def ChosenAt {Proposer Acceptor V : Type*} [DecidableEq Acceptor]
    (qs : QuorumSystem Acceptor) (msgs : Finset (Msg Proposer Acceptor V))
    (b : Ballot Proposer) (v : V) : Prop :=
  ∃ Q ∈ qs.quorums, ∀ a ∈ Q, Msg.phase2b a b v ∈ msgs

/-- Learner `l` has learned value `v` at ballot `b` in state `s` when `l` has received
`Phase2b(a, b, v)` from every acceptor in some quorum `Q ∈ qs.quorums`. -/
@[expose] def SynodState.LearnedAt {Proposer Acceptor Learner V : Type*} [DecidableEq Acceptor]
    (qs : QuorumSystem Acceptor) (s : SynodState Proposer Acceptor Learner V)
    (l : Learner) (b : Ballot Proposer) (v : V) : Prop :=
  ∃ Q ∈ qs.quorums, ∀ a ∈ Q, ⟨a, b, v⟩ ∈ (s.learners l).received

/-! ### Shadow non-dropping simulation -/

section Safety

variable {Proposer Acceptor Learner V : Type*}
  [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
  (qs : QuorumSystem Acceptor)

private def synodLtsNoDrop :
    LTS (SynodState Proposer Acceptor Learner V) (SynodAction Proposer Acceptor Learner V) where
  Tr s act s' := synodEnabled s act ∧ s' = synodStepCore false qs s act

omit [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V] in
private lemma enabled_mono_msgs {s₁ s₂ : SynodState Proposer Acceptor Learner V}
    {act : SynodAction Proposer Acceptor Learner V}
    (hen : synodEnabled s₁ act) (hsub : s₁.msgs ⊆ s₂.msgs)
    (hp : s₁.proposers = s₂.proposers) (ha : s₁.acceptors = s₂.acceptors)
    (hl : s₁.learners = s₂.learners) : synodEnabled s₂ act := by
  cases act <;> simp only [synodEnabled] at hen ⊢
  · rw [← hp]; exact hen
  · exact ⟨ha ▸ hen.1, hsub hen.2⟩
  · exact ⟨hp ▸ hen.1, hsub hen.2⟩
  · exact ⟨ha ▸ hen.1, hsub hen.2⟩
  · exact ⟨hl ▸ hen.1, hsub hen.2⟩
  · exact hsub hen

private lemma stepCore_sim {s₁ s₂ : SynodState Proposer Acceptor Learner V}
    (act : SynodAction Proposer Acceptor Learner V)
    (hsub : s₁.msgs ⊆ s₂.msgs)
    (hp : s₁.proposers = s₂.proposers) (ha : s₁.acceptors = s₂.acceptors)
    (hl : s₁.learners = s₂.learners) :
    (synodStep qs s₁ act).msgs ⊆ (synodStepCore false qs s₂ act).msgs ∧
      (synodStep qs s₁ act).proposers = (synodStepCore false qs s₂ act).proposers ∧
      (synodStep qs s₁ act).acceptors = (synodStepCore false qs s₂ act).acceptors ∧
      (synodStep qs s₁ act).learners = (synodStepCore false qs s₂ act).learners := by
  cases act <;> dsimp only [synodStep, synodStepCore]
  case prepare p r =>
    rw [hp, ha, hl]
    exact ⟨Finset.insert_subset_insert _ hsub, rfl, rfl, rfl⟩
  case recvPhase1a a b =>
    rw [ha]
    split_ifs
    · exact ⟨Finset.insert_subset_insert _ hsub, hp, rfl, hl⟩
    · exact ⟨hsub, hp, ha, hl⟩
  case recvPhase1b p a b mv =>
    rw [hp]
    cases (s₂.proposers p).round with
    | none => exact ⟨hsub, hp, ha, hl⟩
    | some r =>
      dsimp only []
      split_ifs
      · exact ⟨Finset.insert_subset_insert _ hsub, rfl, ha, hl⟩
      · exact ⟨hsub, rfl, ha, hl⟩
      · exact ⟨hsub, hp, ha, hl⟩
  case recvPhase2a a b v =>
    rw [ha]
    split_ifs
    · exact ⟨Finset.insert_subset_insert _ hsub, hp, rfl, hl⟩
    · exact ⟨hsub, hp, ha, hl⟩
  case recvPhase2b l a b v =>
    rw [hl]
    exact ⟨hsub, hp, ha, rfl⟩
  case drop m =>
    simp only [↓reduceIte, Bool.false_eq_true]
    exact ⟨(Finset.erase_subset m s₁.msgs).trans hsub, hp, ha, hl⟩
  case crashProposer p =>
    rw [hp]
    exact ⟨hsub, rfl, ha, hl⟩
  case crashAcceptor a =>
    rw [ha]
    exact ⟨hsub, hp, rfl, hl⟩
  case crashLearner l =>
    rw [hl]
    exact ⟨hsub, hp, ha, rfl⟩
  case stutter =>
    exact ⟨hsub, hp, ha, hl⟩

private lemma mTr_sim_noDrop {s₀ s : SynodState Proposer Acceptor Learner V}
    {xl : List (SynodAction Proposer Acceptor Learner V)}
    (hmtr : (synodLts qs).MTr s₀ xl s) :
    let s_nd := xl.foldl (synodStepCore false qs) s₀
    (synodLtsNoDrop qs).MTr s₀ xl s_nd ∧ s.msgs ⊆ s_nd.msgs ∧
      s.proposers = s_nd.proposers ∧ s.acceptors = s_nd.acceptors ∧
      s.learners = s_nd.learners := by
  have hgen : ∀ (u₀ : SynodState Proposer Acceptor Learner V),
      s₀.msgs ⊆ u₀.msgs → s₀.proposers = u₀.proposers → s₀.acceptors = u₀.acceptors →
      s₀.learners = u₀.learners →
      let s_nd := xl.foldl (synodStepCore false qs) u₀
      (synodLtsNoDrop qs).MTr u₀ xl s_nd ∧ s.msgs ⊆ s_nd.msgs ∧
        s.proposers = s_nd.proposers ∧ s.acceptors = s_nd.acceptors ∧
        s.learners = s_nd.learners := by
    induction hmtr with
    | refl =>
      intro u₀ hsub hp ha hl
      exact ⟨LTS.MTr.refl, hsub, hp, ha, hl⟩
    | @stepL s₁ act s₂ rest s₃ htr _ ih =>
      intro u₀ hsub hp ha hl
      obtain ⟨hen, rfl⟩ := htr
      have hen' := enabled_mono_msgs hen hsub hp ha hl
      have ⟨hsub', hp', ha', hl'⟩ := stepCore_sim qs act hsub hp ha hl
      obtain ⟨hmtr', hsub'', hp'', ha'', hl''⟩ :=
        ih (synodStepCore false qs u₀ act) hsub' hp' ha' hl'
      exact ⟨LTS.MTr.stepL ⟨hen', rfl⟩ hmtr', hsub'', hp'', ha'', hl''⟩
  exact hgen s₀ Finset.Subset.rfl rfl rfl rfl

/-- Every packet currently in `s.msgs` along a valid trace `xl` belongs to `traceMsgs qs s₀ xl`. -/
theorem mem_traceMsgs_of_mem_msgs {s₀ s : SynodState Proposer Acceptor Learner V}
    {xl : List (SynodAction Proposer Acceptor Learner V)}
    (hmtr : (synodLts qs).MTr s₀ xl s) {m : Msg Proposer Acceptor V} (hm : m ∈ s.msgs) :
    m ∈ traceMsgs qs s₀ xl :=
  (mTr_sim_noDrop qs hmtr).2.1 hm

/-! ### Global inductive invariant over `synodLtsNoDrop` -/

/-- Proposer promise-buffer predicate for active ballot `b`. -/
private def ProposerPromiseInv (msgs : Finset (Msg Proposer Acceptor V))
    (b : Ballot Proposer) (promised : Finset Acceptor)
    (maxVote : Option (Vote Proposer V)) : Prop :=
  match maxVote with
  | none => ∀ a ∈ promised, Msg.phase1b a b none ∈ msgs
  | some vt =>
    vt.ballot < b ∧ Msg.phase2a vt.ballot vt.value ∈ msgs ∧
      ∀ a ∈ promised, ∃ mv, Msg.phase1b a b mv ∈ msgs ∧
        ∀ vt', mv = some vt' → vt'.ballot ≤ vt.ballot

omit [DecidableEq Acceptor] [DecidableEq V] in
private lemma proposerPromiseInv_mono {m₁ m₂ : Finset (Msg Proposer Acceptor V)}
    (hsub : m₁ ⊆ m₂) {b : Ballot Proposer} {promised : Finset Acceptor}
    {maxVote : Option (Vote Proposer V)}
    (hp : ProposerPromiseInv m₁ b promised maxVote) :
    ProposerPromiseInv m₂ b promised maxVote := by
  cases maxVote with
  | none => exact fun a ha => hsub (hp a ha)
  | some vt =>
    exact ⟨hp.1, hsub hp.2.1, fun a ha =>
      let ⟨mv, hm, hb⟩ := hp.2.2 a ha
      ⟨mv, hsub hm, hb⟩⟩

/-- Lamport's condition P2c: every emitted `Phase2a(b, v)` is backed by a quorum `Q ∈ qs.quorums` of
`Phase1b` promises for `b`, either all carrying `none` or bounded by a prior vote `(vt.ballot, v)`
at `vt.ballot < b`. -/
private def Phase2aQuorumWitness (msgs : Finset (Msg Proposer Acceptor V))
    (b : Ballot Proposer) (v : V) : Prop :=
  ∃ Q ∈ qs.quorums,
    (∀ a ∈ Q, Msg.phase1b a b none ∈ msgs) ∨
      ∃ vt : Vote Proposer V, vt.value = v ∧ vt.ballot < b ∧
        Msg.phase2a vt.ballot vt.value ∈ msgs ∧
        ∀ a ∈ Q, ∃ mv, Msg.phase1b a b mv ∈ msgs ∧
          ∀ vt', mv = some vt' → vt'.ballot ≤ vt.ballot

omit [DecidableEq V] in
private lemma phase2aQuorumWitness_mono {m₁ m₂ : Finset (Msg Proposer Acceptor V)}
    (hsub : m₁ ⊆ m₂) {b : Ballot Proposer} {v : V}
    (hw : Phase2aQuorumWitness qs m₁ b v) : Phase2aQuorumWitness qs m₂ b v := by
  obtain ⟨Q, hQ, hcases⟩ := hw
  refine ⟨Q, hQ, ?_⟩
  rcases hcases with hnone | ⟨vt, hval, hlt, h2a, hall⟩
  · exact Or.inl fun a ha => hsub (hnone a ha)
  · exact Or.inr ⟨vt, hval, hlt, hsub h2a, fun a ha =>
      let ⟨mv, hm, hb⟩ := hall a ha
      ⟨mv, hsub hm, hb⟩⟩

/-- Combined single-state inductive invariant over the non-dropping network packet set and
ghost-free node states. -/
private structure SynodCoreInv (inputs : Proposer → V)
    (s : SynodState Proposer Acceptor Learner V) : Prop where
  /-- Proposer inputs remain equal to `inputs`. -/
  prop_input : ∀ p, (s.proposers p).input = inputs p
  /-- Any emitted `Phase2a(⟨r, p⟩, v)` lies strictly below `p`'s current round, or at `p`'s current
  round with `proposed = true`. -/
  prop_phase2a_round : ∀ r p v, Msg.phase2a ⟨r, p⟩ v ∈ s.msgs →
    ∃ r_cur, (s.proposers p).round = some r_cur ∧
      (r < r_cur ∨ (r = r_cur ∧ (s.proposers p).proposed = true))
  /-- Single-proposal per ballot: at most one value is ever proposed in `Phase2a` for ballot `b`. -/
  phase2a_unique : ∀ b v₁ v₂,
    Msg.phase2a b v₁ ∈ s.msgs → Msg.phase2a b v₂ ∈ s.msgs → v₁ = v₂
  /-- Validity of `Phase2a`: every proposed value equals some proposer's initial input. -/
  phase2a_valid : ∀ b v, Msg.phase2a b v ∈ s.msgs → ∃ p, inputs p = v
  /-- Active proposer promise invariant. -/
  prop_promises : ∀ p r, (s.proposers p).round = some r →
    ProposerPromiseInv s.msgs ⟨r, p⟩ (s.proposers p).promised (s.proposers p).maxVote
  /-- Lamport's condition P2c on every emitted `Phase2a(b, v)`. -/
  phase2a_witness : ∀ b v, Msg.phase2a b v ∈ s.msgs → Phase2aQuorumWitness qs s.msgs b v
  /-- Local acceptor state consistency: `maxVoted` is bounded by `maxBal` and backed by
  `Phase2a`. -/
  acc_local : ∀ a vt, (s.acceptors a).maxVoted = some vt →
    (∃ mb, (s.acceptors a).maxBal = some mb ∧ vt.ballot ≤ mb) ∧
      Msg.phase2a vt.ballot vt.value ∈ s.msgs
  /-- Emitted `Phase1b(a, b, mv)` implies `a.maxBal ≥ b` and any reported vote `vt` satisfies
  `vt.ballot < b` and is backed by `Phase2a`. -/
  phase1b_inv : ∀ a b mv, Msg.phase1b a b mv ∈ s.msgs →
    (∃ mb, (s.acceptors a).maxBal = some mb ∧ b ≤ mb) ∧
      ∀ vt, mv = some vt → vt.ballot < b ∧ Msg.phase2a vt.ballot vt.value ∈ s.msgs
  /-- Emitted `Phase2b(a, b, v)` implies `a.maxVoted` has ballot `≥ b` and `Phase2a(b, v)` was
  emitted. -/
  phase2b_inv : ∀ a b v, Msg.phase2b a b v ∈ s.msgs →
    (∃ vt, (s.acceptors a).maxVoted = some vt ∧ b ≤ vt.ballot) ∧ Msg.phase2a b v ∈ s.msgs
  /-- Lamport's promise–vote invariant: if acceptor `a` voted `(b₀, v₀)` and promised `b > b₀`, then
  `a`'s `Phase1b` for `b` reported a vote at ballot `≥ b₀`. -/
  promise_vote : ∀ a b₀ v₀ b mv,
    Msg.phase2b a b₀ v₀ ∈ s.msgs → Msg.phase1b a b mv ∈ s.msgs → b₀ < b →
    ∃ vt, mv = some vt ∧ b₀ ≤ vt.ballot
  /-- Learner received buffer contains only authentic `Phase2b` packets. -/
  learner_recv : ∀ l av, av ∈ (s.learners l).received →
    Msg.phase2b av.acceptor av.ballot av.value ∈ s.msgs

omit [DecidableEq Learner] [DecidableEq V] in
private lemma synodCoreInv_init (inputs : Proposer → V) :
    SynodCoreInv qs inputs (initState (Learner := Learner) inputs) where
  prop_input _ := rfl
  prop_phase2a_round _ _ _ hm := absurd hm (Finset.notMem_empty _)
  phase2a_unique _ _ _ hm := absurd hm (Finset.notMem_empty _)
  phase2a_valid _ _ hm := absurd hm (Finset.notMem_empty _)
  prop_promises _ _ hr := by simp only [initState] at hr; cases hr
  phase2a_witness _ _ hm := absurd hm (Finset.notMem_empty _)
  acc_local _ _ hv := by simp only [initState] at hv; cases hv
  phase1b_inv _ _ _ hm := absurd hm (Finset.notMem_empty _)
  phase2b_inv _ _ _ hm := absurd hm (Finset.notMem_empty _)
  promise_vote _ _ _ _ _ hm := absurd hm (Finset.notMem_empty _)
  learner_recv _ _ hm := absurd hm (Finset.notMem_empty _)

private lemma not_phase2a_of_insert {msgs : Finset (Msg Proposer Acceptor V)}
    {m : Msg Proposer Acceptor V} (hnot : ∀ b v, m ≠ Msg.phase2a b v)
    {b : Ballot Proposer} {v : V} (hm : Msg.phase2a b v ∈ insert m msgs) :
    Msg.phase2a b v ∈ msgs := by
  rcases Finset.mem_insert.mp hm with heq | hm'
  · exact absurd heq.symm (hnot b v)
  · exact hm'

omit [DecidableEq Learner] [DecidableEq V] in
private lemma mergeVote_promises_inv {inputs : Proposer → V}
    {s : SynodState Proposer Acceptor Learner V} (hinv : SynodCoreInv qs inputs s)
    {p : Proposer} {r : ℕ} (hround : (s.proposers p).round = some r)
    {a : Acceptor} {mv : Option (Vote Proposer V)}
    (h1b : Msg.phase1b a ⟨r, p⟩ mv ∈ s.msgs) :
    ProposerPromiseInv s.msgs ⟨r, p⟩
      (insert a (s.proposers p).promised) (mergeVote (s.proposers p).maxVote mv) := by
  have hcur := hinv.prop_promises p r hround
  have h1b_prop := (hinv.phase1b_inv a ⟨r, p⟩ mv h1b).2
  dsimp only [ProposerPromiseInv, mergeVote] at hcur ⊢
  cases hmv_cur : (s.proposers p).maxVote with
  | none =>
    rw [hmv_cur] at hcur
    cases mv with
    | none =>
      intro a' ha'
      rcases Finset.mem_insert.mp ha' with rfl | hold
      · exact h1b
      · exact hcur a' hold
    | some vt₂ =>
      obtain ⟨hvt₂_lt, hvt₂_2a⟩ := h1b_prop vt₂ rfl
      refine ⟨hvt₂_lt, hvt₂_2a, fun a' ha' => ?_⟩
      rcases Finset.mem_insert.mp ha' with rfl | hold
      · exact ⟨some vt₂, h1b, fun vt' h => by injection h with h'; subst h'; exact le_rfl⟩
      · exact ⟨none, hcur a' hold, fun _ h => by cases h⟩
  | some vt₁ =>
    rw [hmv_cur] at hcur
    obtain ⟨hvt₁_lt, hvt₁_2a, hall_cur⟩ := hcur
    cases mv with
    | none =>
      refine ⟨hvt₁_lt, hvt₁_2a, fun a' ha' => ?_⟩
      rcases Finset.mem_insert.mp ha' with rfl | hold
      · exact ⟨none, h1b, fun _ h => by cases h⟩
      · exact hall_cur a' hold
    | some vt₂ =>
      obtain ⟨hvt₂_lt, hvt₂_2a⟩ := h1b_prop vt₂ rfl
      dsimp only []
      split_ifs with hlt
      · refine ⟨hvt₂_lt, hvt₂_2a, fun a' ha' => ?_⟩
        rcases Finset.mem_insert.mp ha' with rfl | hold
        · exact ⟨some vt₂, h1b, fun vt' h => by injection h with h'; subst h'; exact le_rfl⟩
        · obtain ⟨mv', hm', hle'⟩ := hall_cur a' hold
          exact ⟨mv', hm', fun vt' h => (hle' vt' h).trans (le_of_lt hlt)⟩
      · have hle₂₁ : vt₂.ballot ≤ vt₁.ballot := not_lt.mp hlt
        refine ⟨hvt₁_lt, hvt₁_2a, fun a' ha' => ?_⟩
        rcases Finset.mem_insert.mp ha' with rfl | hold
        · exact ⟨some vt₂, h1b, fun vt' h => by injection h with h'; subst h'; exact hle₂₁⟩
        · exact hall_cur a' hold

private lemma synodCoreInv_tr (inputs : Proposer → V) :
    (synodLtsNoDrop qs (Learner := Learner)).TrInv (SynodCoreInv qs inputs) := by
  intro s act s' htr hinv
  cases act with
  | prepare p r =>
    obtain ⟨⟨_, hround_lt⟩, rfl⟩ := htr
    dsimp only [synodStepCore]
    have hnot2a : ∀ b v, (Msg.phase1a ⟨r, p⟩ : Msg Proposer Acceptor V) ≠ Msg.phase2a b v :=
      fun _ _ h => by cases h
    refine
      { prop_input := fun q => by
          dsimp only []
          split_ifs with hqp
          · subst hqp; exact hinv.prop_input q
          · exact hinv.prop_input q
        prop_phase2a_round := fun r' q v hm => by
          have hm' := not_phase2a_of_insert hnot2a hm
          obtain ⟨r_cur, hr_cur, hrel⟩ := hinv.prop_phase2a_round r' q v hm'
          dsimp only []
          split_ifs with hqp
          · subst hqp
            rw [hr_cur] at hround_lt
            refine ⟨r, rfl, Or.inl ?_⟩
            rcases hrel with hlt | ⟨rfl, _⟩ <;> omega
          · exact ⟨r_cur, hr_cur, hrel⟩
        phase2a_unique := fun b v₁ v₂ h₁ h₂ =>
          hinv.phase2a_unique b v₁ v₂
            (not_phase2a_of_insert hnot2a h₁) (not_phase2a_of_insert hnot2a h₂)
        phase2a_valid := fun b v hm =>
          hinv.phase2a_valid b v (not_phase2a_of_insert hnot2a hm)
        prop_promises := fun q r' hq => by
          dsimp only [] at hq ⊢
          split_ifs at hq ⊢ with hqp
          · subst hqp
            injection hq with hr_eq
            subst hr_eq
            exact fun a ha => absurd ha (Finset.notMem_empty _)
          · exact proposerPromiseInv_mono (Finset.subset_insert _ _)
              (hinv.prop_promises q r' hq)
        phase2a_witness := fun b v hm =>
          phase2aQuorumWitness_mono qs (Finset.subset_insert _ _)
            (hinv.phase2a_witness b v (not_phase2a_of_insert hnot2a hm))
        acc_local := fun a vt hvt =>
          let ⟨hmb, h2a⟩ := hinv.acc_local a vt hvt
          ⟨hmb, Finset.mem_insert_of_mem h2a⟩
        phase1b_inv := fun a b mv hm => by
          rcases Finset.mem_insert.mp hm with h | hm'
          · cases h
          · obtain ⟨hmb, hvt⟩ := hinv.phase1b_inv a b mv hm'
            exact ⟨hmb, fun vt hv =>
              ⟨(hvt vt hv).1, Finset.mem_insert_of_mem (hvt vt hv).2⟩⟩
        phase2b_inv := fun a b v hm => by
          rcases Finset.mem_insert.mp hm with h | hm'
          · cases h
          · obtain ⟨hvt, h2a⟩ := hinv.phase2b_inv a b v hm'
            exact ⟨hvt, Finset.mem_insert_of_mem h2a⟩
        promise_vote := fun a b₀ v₀ b mv h2b h1b hlt => by
          rcases Finset.mem_insert.mp h2b with h | h2b'
          · cases h
          · rcases Finset.mem_insert.mp h1b with h | h1b'
            · cases h
            · exact hinv.promise_vote a b₀ v₀ b mv h2b' h1b' hlt
        learner_recv := fun l av hav => Finset.mem_insert_of_mem (hinv.learner_recv l av hav) }
  | recvPhase1a a b =>
    obtain ⟨_, rfl⟩ := htr
    dsimp only [synodStepCore]
    split_ifs with habove
    · have hnot2a : ∀ b' v', Msg.phase1b a b (s.acceptors a).maxVoted ≠ Msg.phase2a b' v' :=
        fun _ _ h => by cases h
      have hvt_lt : ∀ vt, (s.acceptors a).maxVoted = some vt →
          vt.ballot < b ∧ Msg.phase2a vt.ballot vt.value ∈ s.msgs := by
        intro vt hvt
        obtain ⟨⟨mb, hmb, hle_mb⟩, h2a⟩ := hinv.acc_local a vt hvt
        simp only [aboveMaxBal, hmb, decide_eq_true_eq] at habove
        exact ⟨hle_mb.trans_lt habove, h2a⟩
      refine
        { prop_input := hinv.prop_input
          prop_phase2a_round := fun r' q v hm =>
            hinv.prop_phase2a_round r' q v (not_phase2a_of_insert hnot2a hm)
          phase2a_unique := fun b' v₁ v₂ h₁ h₂ =>
            hinv.phase2a_unique b' v₁ v₂
              (not_phase2a_of_insert hnot2a h₁) (not_phase2a_of_insert hnot2a h₂)
          phase2a_valid := fun b' v hm =>
            hinv.phase2a_valid b' v (not_phase2a_of_insert hnot2a hm)
          prop_promises := fun q r' hq =>
            proposerPromiseInv_mono (Finset.subset_insert _ _) (hinv.prop_promises q r' hq)
          phase2a_witness := fun b' v hm =>
            phase2aQuorumWitness_mono qs (Finset.subset_insert _ _)
              (hinv.phase2a_witness b' v (not_phase2a_of_insert hnot2a hm))
          acc_local := fun a' vt hvt => by
            dsimp only [] at hvt ⊢
            split_ifs at hvt ⊢ with haa
            · subst haa
              obtain ⟨hvt_b, h2a⟩ := hvt_lt vt hvt
              exact ⟨⟨b, rfl, le_of_lt hvt_b⟩, Finset.mem_insert_of_mem h2a⟩
            · obtain ⟨hmb, h2a⟩ := hinv.acc_local a' vt hvt
              exact ⟨hmb, Finset.mem_insert_of_mem h2a⟩
          phase1b_inv := fun a' b' mv hm => by
            dsimp only [] at hm ⊢
            rcases Finset.mem_insert.mp hm with h | hm'
            · injection h with ha_eq hb_eq hmv_eq
              subst ha_eq hb_eq hmv_eq
              simp only [↓reduceIte]
              exact ⟨⟨b', rfl, le_rfl⟩, fun vt hv =>
                ⟨(hvt_lt vt hv).1, Finset.mem_insert_of_mem (hvt_lt vt hv).2⟩⟩
            · obtain ⟨⟨mb, hmb, hle_mb⟩, hvt⟩ := hinv.phase1b_inv a' b' mv hm'
              refine ⟨?_, fun vt hv =>
                ⟨(hvt vt hv).1, Finset.mem_insert_of_mem (hvt vt hv).2⟩⟩
              split_ifs with haa
              · subst haa
                simp only [aboveMaxBal, hmb, decide_eq_true_eq] at habove
                exact ⟨b, rfl, hle_mb.trans (le_of_lt habove)⟩
              · exact ⟨mb, hmb, hle_mb⟩
          phase2b_inv := fun a' b' v hm => by
            dsimp only [] at hm ⊢
            rcases Finset.mem_insert.mp hm with h | hm'
            · cases h
            · obtain ⟨hvt, h2a⟩ := hinv.phase2b_inv a' b' v hm'
              refine ⟨?_, Finset.mem_insert_of_mem h2a⟩
              split_ifs with haa
              · subst haa; exact hvt
              · exact hvt
          promise_vote := fun a' b₀ v₀ b' mv h2b h1b hlt => by
            rcases Finset.mem_insert.mp h2b with h | h2b'
            · cases h
            · rcases Finset.mem_insert.mp h1b with h | h1b'
              · injection h with ha_eq hb_eq hmv_eq
                subst ha_eq hb_eq hmv_eq
                obtain ⟨⟨vt, hvt, hb₀_le⟩, _⟩ := hinv.phase2b_inv a' b₀ v₀ h2b'
                exact ⟨vt, hvt, hb₀_le⟩
              · exact hinv.promise_vote a' b₀ v₀ b' mv h2b' h1b' hlt
          learner_recv := fun l av hav => Finset.mem_insert_of_mem (hinv.learner_recv l av hav) }
    · exact hinv
  | recvPhase1b p a b mv =>
    obtain ⟨⟨_, h1b_mem⟩, rfl⟩ := htr
    dsimp only [synodStepCore]
    cases hround : (s.proposers p).round with
    | none => exact hinv
    | some r =>
      dsimp only []
      split_ifs with hguard hprop_q
      · obtain ⟨rfl, _⟩ := hguard
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hprop_q
        obtain ⟨hnot_prop, hq⟩ := hprop_q
        have hprom' := mergeVote_promises_inv qs hinv hround h1b_mem
        set maxVote' := mergeVote (s.proposers p).maxVote mv
        set val := match maxVote' with | some vt => vt.value | none => (s.proposers p).input
        have hval_valid : ∃ p₀, inputs p₀ = val := by
          cases hmv' : maxVote' with
          | none =>
            dsimp only [val]
            rw [hmv']
            exact ⟨p, (hinv.prop_input p).symm⟩
          | some vt =>
            dsimp only [val]
            rw [hmv']
            have hp_vt : ProposerPromiseInv s.msgs ⟨r, p⟩
                (insert a (s.proposers p).promised) (some vt) := hmv' ▸ hprom'
            exact hinv.phase2a_valid vt.ballot vt.value hp_vt.2.1
        have hno_prior_2a : ∀ v_old, Msg.phase2a ⟨r, p⟩ v_old ∉ s.msgs := by
          intro v_old hm_old
          obtain ⟨r_cur, hr_cur, hrel⟩ := hinv.prop_phase2a_round r p v_old hm_old
          rw [hround] at hr_cur
          injection hr_cur with hr_eq
          subst hr_eq
          rcases hrel with hlt | ⟨_, hp_true⟩
          · exact lt_irrefl r hlt
          · rw [hnot_prop] at hp_true
            exact Bool.false_ne_true hp_true
        have hwit_new : Phase2aQuorumWitness qs
            (insert (Msg.phase2a ⟨r, p⟩ val) s.msgs) ⟨r, p⟩ val := by
          obtain ⟨Q, hQ, hQsub⟩ := hq
          refine phase2aQuorumWitness_mono qs (Finset.subset_insert _ _) ⟨Q, hQ, ?_⟩
          cases hmv' : maxVote' with
          | none =>
            have hp_none : ProposerPromiseInv s.msgs ⟨r, p⟩
                (insert a (s.proposers p).promised) none := hmv' ▸ hprom'
            exact Or.inl fun a' ha' => hp_none a' (hQsub ha')
          | some vt =>
            dsimp only [val]
            rw [hmv']
            have hp_vt : ProposerPromiseInv s.msgs ⟨r, p⟩
                (insert a (s.proposers p).promised) (some vt) := hmv' ▸ hprom'
            exact Or.inr ⟨vt, rfl, hp_vt.1, hp_vt.2.1, fun a' ha' => hp_vt.2.2 a' (hQsub ha')⟩
        refine
          { prop_input := fun q => by
              dsimp only []
              split_ifs with hqp
              · subst hqp; exact hinv.prop_input q
              · exact hinv.prop_input q
            prop_phase2a_round := fun r' q v hm => by
              dsimp only [] at hm ⊢
              rcases Finset.mem_insert.mp hm with h | hm'
              · injection h with hb_eq hv_eq
                cases hb_eq
                subst hv_eq
                simp only [↓reduceIte]
                exact ⟨r, rfl, Or.inr ⟨rfl, trivial⟩⟩
              · obtain ⟨r_cur, hr_cur, hrel⟩ := hinv.prop_phase2a_round r' q v hm'
                split_ifs with hqp
                · subst hqp
                  rw [hround] at hr_cur
                  injection hr_cur with hr_eq
                  subst hr_eq
                  rcases hrel with hlt | ⟨rfl, _⟩
                  · exact ⟨r, rfl, Or.inl hlt⟩
                  · exact ⟨r', rfl, Or.inr ⟨rfl, rfl⟩⟩
                · exact ⟨r_cur, hr_cur, hrel⟩
            phase2a_unique := fun b' v₁ v₂ h₁ h₂ => by
              rcases Finset.mem_insert.mp h₁ with h₁_eq | h₁'
              · injection h₁_eq with hb₁ hv₁
                subst hb₁ hv₁
                rcases Finset.mem_insert.mp h₂ with h₂_eq | h₂'
                · injection h₂_eq with _ hv₂; exact hv₂.symm
                · exact absurd h₂' (hno_prior_2a v₂)
              · rcases Finset.mem_insert.mp h₂ with h₂_eq | h₂'
                · injection h₂_eq with hb₂ hv₂
                  subst hb₂ hv₂
                  exact absurd h₁' (hno_prior_2a v₁)
                · exact hinv.phase2a_unique b' v₁ v₂ h₁' h₂'
            phase2a_valid := fun b' v hm => by
              rcases Finset.mem_insert.mp hm with h | hm'
              · injection h with _ hv_eq; subst hv_eq; exact hval_valid
              · exact hinv.phase2a_valid b' v hm'
            prop_promises := fun q r' hq => by
              dsimp only [] at hq ⊢
              split_ifs at hq ⊢ with hqp
              · subst hqp
                injection hq with hr_eq
                subst hr_eq
                exact proposerPromiseInv_mono (Finset.subset_insert _ _) hprom'
              · exact proposerPromiseInv_mono (Finset.subset_insert _ _)
                  (hinv.prop_promises q r' hq)
            phase2a_witness := fun b' v hm => by
              rcases Finset.mem_insert.mp hm with h | hm'
              · injection h with hb_eq hv_eq
                subst hb_eq hv_eq
                exact hwit_new
              · exact phase2aQuorumWitness_mono qs (Finset.subset_insert _ _)
                  (hinv.phase2a_witness b' v hm')
            acc_local := fun a' vt hvt =>
              let ⟨hmb, h2a⟩ := hinv.acc_local a' vt hvt
              ⟨hmb, Finset.mem_insert_of_mem h2a⟩
            phase1b_inv := fun a' b' mv' hm => by
              rcases Finset.mem_insert.mp hm with h | hm'
              · cases h
              · obtain ⟨hmb, hvt⟩ := hinv.phase1b_inv a' b' mv' hm'
                exact ⟨hmb, fun vt hv =>
                  ⟨(hvt vt hv).1, Finset.mem_insert_of_mem (hvt vt hv).2⟩⟩
            phase2b_inv := fun a' b' v hm => by
              rcases Finset.mem_insert.mp hm with h | hm'
              · cases h
              · obtain ⟨hvt, h2a⟩ := hinv.phase2b_inv a' b' v hm'
                exact ⟨hvt, Finset.mem_insert_of_mem h2a⟩
            promise_vote := fun a' b₀ v₀ b' mv' h2b h1b hlt => by
              rcases Finset.mem_insert.mp h2b with h | h2b'
              · cases h
              · rcases Finset.mem_insert.mp h1b with h | h1b'
                · cases h
                · exact hinv.promise_vote a' b₀ v₀ b' mv' h2b' h1b' hlt
            learner_recv := fun l av hav => Finset.mem_insert_of_mem (hinv.learner_recv l av hav) }
      · obtain ⟨rfl, _⟩ := hguard
        have hprom' := mergeVote_promises_inv qs hinv hround h1b_mem
        refine
          { prop_input := fun q => by
              dsimp only []
              split_ifs with hqp
              · subst hqp; exact hinv.prop_input q
              · exact hinv.prop_input q
            prop_phase2a_round := fun r' q v hm => by
              obtain ⟨r_cur, hr_cur, hrel⟩ := hinv.prop_phase2a_round r' q v hm
              dsimp only []
              split_ifs with hqp
              · subst hqp
                rw [hround] at hr_cur
                injection hr_cur with hr_eq
                subst hr_eq
                exact ⟨r, rfl, hrel⟩
              · exact ⟨r_cur, hr_cur, hrel⟩
            phase2a_unique := hinv.phase2a_unique
            phase2a_valid := hinv.phase2a_valid
            prop_promises := fun q r' hq => by
              dsimp only [] at hq ⊢
              split_ifs at hq ⊢ with hqp
              · subst hqp
                injection hq with hr_eq
                subst hr_eq
                exact hprom'
              · exact hinv.prop_promises q r' hq
            phase2a_witness := hinv.phase2a_witness
            acc_local := hinv.acc_local
            phase1b_inv := hinv.phase1b_inv
            phase2b_inv := hinv.phase2b_inv
            promise_vote := hinv.promise_vote
            learner_recv := hinv.learner_recv }
      · exact hinv
  | recvPhase2a a b v =>
    obtain ⟨⟨_, h2a_mem⟩, rfl⟩ := htr
    dsimp only [synodStepCore]
    split_ifs with hallows
    · have hnot2a : ∀ b' v', (Msg.phase2b a b v : Msg Proposer Acceptor V) ≠ Msg.phase2a b' v' :=
        fun _ _ h => by cases h
      refine
        { prop_input := hinv.prop_input
          prop_phase2a_round := fun r' q v' hm =>
            hinv.prop_phase2a_round r' q v' (not_phase2a_of_insert hnot2a hm)
          phase2a_unique := fun b' v₁ v₂ h₁ h₂ =>
            hinv.phase2a_unique b' v₁ v₂
              (not_phase2a_of_insert hnot2a h₁) (not_phase2a_of_insert hnot2a h₂)
          phase2a_valid := fun b' v' hm =>
            hinv.phase2a_valid b' v' (not_phase2a_of_insert hnot2a hm)
          prop_promises := fun q r' hq =>
            proposerPromiseInv_mono (Finset.subset_insert _ _) (hinv.prop_promises q r' hq)
          phase2a_witness := fun b' v' hm =>
            phase2aQuorumWitness_mono qs (Finset.subset_insert _ _)
              (hinv.phase2a_witness b' v' (not_phase2a_of_insert hnot2a hm))
          acc_local := fun a' vt hvt => by
            dsimp only [] at hvt ⊢
            split_ifs at hvt ⊢ with haa
            · subst haa
              injection hvt with hvt_eq
              subst hvt_eq
              exact ⟨⟨b, rfl, le_rfl⟩, Finset.mem_insert_of_mem h2a_mem⟩
            · obtain ⟨hmb, h2a⟩ := hinv.acc_local a' vt hvt
              exact ⟨hmb, Finset.mem_insert_of_mem h2a⟩
          phase1b_inv := fun a' b' mv hm => by
            dsimp only [] at hm ⊢
            rcases Finset.mem_insert.mp hm with h | hm'
            · cases h
            · obtain ⟨⟨mb, hmb, hle_mb⟩, hvt⟩ := hinv.phase1b_inv a' b' mv hm'
              refine ⟨?_, fun vt hv =>
                ⟨(hvt vt hv).1, Finset.mem_insert_of_mem (hvt vt hv).2⟩⟩
              split_ifs with haa
              · subst haa
                simp only [allowsVote, hmb, decide_eq_true_eq] at hallows
                exact ⟨b, rfl, hle_mb.trans hallows⟩
              · exact ⟨mb, hmb, hle_mb⟩
          phase2b_inv := fun a' b' v' hm => by
            dsimp only [] at hm ⊢
            rcases Finset.mem_insert.mp hm with h | hm'
            · injection h with ha_eq hb_eq hv_eq
              subst ha_eq hb_eq hv_eq
              simp only [↓reduceIte]
              exact ⟨⟨⟨b', v'⟩, rfl, le_rfl⟩, Finset.mem_insert_of_mem h2a_mem⟩
            · obtain ⟨⟨vt, hvt, hb'_le⟩, h2a⟩ := hinv.phase2b_inv a' b' v' hm'
              refine ⟨?_, Finset.mem_insert_of_mem h2a⟩
              split_ifs with haa
              · subst haa
                obtain ⟨⟨mb, hmb, hvt_le_mb⟩, _⟩ := hinv.acc_local a' vt hvt
                simp only [allowsVote, hmb, decide_eq_true_eq] at hallows
                exact ⟨⟨b, v⟩, rfl, hb'_le.trans (hvt_le_mb.trans hallows)⟩
              · exact ⟨vt, hvt, hb'_le⟩
          promise_vote := fun a' b₀ v₀ b' mv h2b h1b hlt => by
            rcases Finset.mem_insert.mp h1b with h | h1b'
            · cases h
            · rcases Finset.mem_insert.mp h2b with h | h2b'
              · injection h with ha_eq hb₀_eq hv₀_eq
                subst ha_eq hb₀_eq hv₀_eq
                obtain ⟨⟨mb, hmb, hb'_le_mb⟩, _⟩ := hinv.phase1b_inv a' b' mv h1b'
                simp only [allowsVote, hmb, decide_eq_true_eq] at hallows
                exact absurd (hlt.trans_le (hb'_le_mb.trans hallows)) (lt_irrefl b₀)
              · exact hinv.promise_vote a' b₀ v₀ b' mv h2b' h1b' hlt
          learner_recv := fun l av hav => Finset.mem_insert_of_mem (hinv.learner_recv l av hav) }
    · exact hinv
  | recvPhase2b l a b v =>
    obtain ⟨⟨_, h2b_mem⟩, rfl⟩ := htr
    dsimp only [synodStepCore]
    refine
      { prop_input := hinv.prop_input
        prop_phase2a_round := hinv.prop_phase2a_round
        phase2a_unique := hinv.phase2a_unique
        phase2a_valid := hinv.phase2a_valid
        prop_promises := hinv.prop_promises
        phase2a_witness := hinv.phase2a_witness
        acc_local := hinv.acc_local
        phase1b_inv := hinv.phase1b_inv
        phase2b_inv := hinv.phase2b_inv
        promise_vote := hinv.promise_vote
        learner_recv := fun l' av hav => by
          by_cases hll : l' = l
          · subst hll
            simp only [↓reduceIte] at hav
            rcases Finset.mem_insert.mp hav with rfl | hold
            · exact h2b_mem
            · exact hinv.learner_recv l' av hold
          · simp only [hll, ↓reduceIte] at hav
            exact hinv.learner_recv l' av hav }
  | drop _ =>
    obtain ⟨_, rfl⟩ := htr
    exact hinv
  | crashProposer p =>
    obtain ⟨_, rfl⟩ := htr
    dsimp only [synodStepCore]
    refine
      { prop_input := fun q => by
          dsimp only []
          split_ifs with hqp
          · subst hqp; exact hinv.prop_input q
          · exact hinv.prop_input q
        prop_phase2a_round := fun r' q v hm => by
          dsimp only [] at hm ⊢
          split_ifs with hqp
          · subst hqp; exact hinv.prop_phase2a_round r' q v hm
          · exact hinv.prop_phase2a_round r' q v hm
        phase2a_unique := hinv.phase2a_unique
        phase2a_valid := hinv.phase2a_valid
        prop_promises := fun q r' hq => by
          dsimp only [] at hq ⊢
          split_ifs at hq ⊢ with hqp
          · subst hqp; exact hinv.prop_promises q r' hq
          · exact hinv.prop_promises q r' hq
        phase2a_witness := hinv.phase2a_witness
        acc_local := hinv.acc_local
        phase1b_inv := hinv.phase1b_inv
        phase2b_inv := hinv.phase2b_inv
        promise_vote := hinv.promise_vote
        learner_recv := hinv.learner_recv }
  | crashAcceptor a =>
    obtain ⟨_, rfl⟩ := htr
    dsimp only [synodStepCore]
    refine
      { prop_input := hinv.prop_input
        prop_phase2a_round := hinv.prop_phase2a_round
        phase2a_unique := hinv.phase2a_unique
        phase2a_valid := hinv.phase2a_valid
        prop_promises := hinv.prop_promises
        phase2a_witness := hinv.phase2a_witness
        acc_local := fun a' vt hvt => by
          dsimp only [] at hvt ⊢
          split_ifs at hvt ⊢ with haa
          · subst haa; exact hinv.acc_local a' vt hvt
          · exact hinv.acc_local a' vt hvt
        phase1b_inv := fun a' b' mv hm => by
          obtain ⟨hmb, hvt⟩ := hinv.phase1b_inv a' b' mv hm
          refine ⟨?_, hvt⟩
          dsimp only []
          split_ifs with haa
          · subst haa; exact hmb
          · exact hmb
        phase2b_inv := fun a' b' v hm => by
          obtain ⟨hvt, h2a⟩ := hinv.phase2b_inv a' b' v hm
          refine ⟨?_, h2a⟩
          dsimp only []
          split_ifs with haa
          · subst haa; exact hvt
          · exact hvt
        promise_vote := hinv.promise_vote
        learner_recv := hinv.learner_recv }
  | crashLearner l =>
    obtain ⟨_, rfl⟩ := htr
    dsimp only [synodStepCore]
    refine
      { prop_input := hinv.prop_input
        prop_phase2a_round := hinv.prop_phase2a_round
        phase2a_unique := hinv.phase2a_unique
        phase2a_valid := hinv.phase2a_valid
        prop_promises := hinv.prop_promises
        phase2a_witness := hinv.phase2a_witness
        acc_local := hinv.acc_local
        phase1b_inv := hinv.phase1b_inv
        phase2b_inv := hinv.phase2b_inv
        promise_vote := hinv.promise_vote
        learner_recv := fun l' av hav => by
          dsimp only [] at hav ⊢
          split_ifs at hav with hll
          · subst hll; exact hinv.learner_recv l' av hav
          · exact hinv.learner_recv l' av hav }
  | stutter =>
    obtain ⟨_, rfl⟩ := htr
    exact hinv

private lemma synodCoreInv_of_mTr {inputs : Proposer → V}
    {xl : List (SynodAction Proposer Acceptor Learner V)}
    {s : SynodState Proposer Acceptor Learner V}
    (hmtr : (synodLts qs).MTr (initState inputs) xl s) :
    SynodCoreInv qs inputs (xl.foldl (synodStepCore false qs) (initState inputs)) :=
  LTS.mtrInv_of_trInv (synodCoreInv_tr qs inputs) _ _ _
    (mTr_sim_noDrop qs hmtr).1 (synodCoreInv_init qs inputs)

/-! ### Main safety theorems -/

/-- Crash-stop helper step towards single-proposal per ballot in [Lamport1998] §2.1 (`B1`),
§2.2–§2.3 and [Lamport2001] §2.2, §2.5 (not the crash-recovery cited protocol): along any execution
trace of `synodLts`, at most one value is ever proposed in `Phase2a` for any given ballot `b`. -/
theorem phase2a_unique_of_ballot_crashStop {inputs : Proposer → V}
    {xl : List (SynodAction Proposer Acceptor Learner V)}
    {s : SynodState Proposer Acceptor Learner V}
    (hmtr : (synodLts qs).MTr (initState inputs) xl s)
    {b : Ballot Proposer} {v₁ v₂ : V}
    (h₁ : Msg.phase2a b v₁ ∈ traceMsgs qs (initState inputs) xl)
    (h₂ : Msg.phase2a b v₂ ∈ traceMsgs qs (initState inputs) xl) :
    v₁ = v₂ :=
  (synodCoreInv_of_mTr qs hmtr).phase2a_unique b v₁ v₂ h₁ h₂

private def isPhase2aBelow (b' : Ballot Proposer) : Msg Proposer Acceptor V → Bool
  | .phase2a b'' _ => decide (b'' < b')
  | _ => false

private def phase2aBelow (msgs : Finset (Msg Proposer Acceptor V))
    (b' : Ballot Proposer) : Finset (Msg Proposer Acceptor V) :=
  msgs.filter fun m => isPhase2aBelow b' m = true

omit [DecidableEq Acceptor] [DecidableEq V] in
private lemma phase2aBelow_card_lt {msgs : Finset (Msg Proposer Acceptor V)}
    {b₁ b₂ : Ballot Proposer} {v₁ : V} (hm₁ : Msg.phase2a b₁ v₁ ∈ msgs) (hlt : b₁ < b₂) :
    (phase2aBelow msgs b₁).card < (phase2aBelow msgs b₂).card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨Msg.phase2a b₁ v₁, ?_, ?_⟩
    · rw [phase2aBelow, Finset.mem_filter]
      exact ⟨hm₁, decide_eq_true hlt⟩
    · rw [phase2aBelow, Finset.mem_filter]
      intro h
      exact lt_irrefl b₁ (of_decide_eq_true h.2)
  · intro m hm
    rw [phase2aBelow, Finset.mem_filter] at hm ⊢
    refine ⟨hm.1, ?_⟩
    cases m with
    | phase2a b'' _ => exact decide_eq_true ((of_decide_eq_true hm.2).trans hlt)
    | _ => cases hm.2

/-- Crash-stop intermediate step towards the inductive ballot-choice invariant of [Lamport1998]
§2.1 (Lemma) and [Lamport2001] §2.2 (`P2^b`–`P2^c`), and **not** the crash-recovery cited result:
along any crash-stop `synodLts` execution, if a quorum `Q ∈ qs.quorums` has voted `(b, v)` in Phase
2b, then every `Phase2a(b', v')` emitted in the trace with `b ≤ b'` satisfies `v' = v`. -/
theorem chosenAt_implies_higher_phase2a_eq_crashStop {inputs : Proposer → V}
    {xl : List (SynodAction Proposer Acceptor Learner V)}
    {s : SynodState Proposer Acceptor Learner V}
    (hmtr : (synodLts qs).MTr (initState inputs) xl s)
    {b b' : Ballot Proposer} {v v' : V}
    (hchosen : ChosenAt qs (traceMsgs qs (initState inputs) xl) b v)
    (h2a : Msg.phase2a b' v' ∈ traceMsgs qs (initState inputs) xl)
    (hle : b ≤ b') :
    v' = v := by
  have hinv := synodCoreInv_of_mTr qs hmtr
  set msgs := traceMsgs qs (initState inputs) xl
  suffices hstrong : ∀ (n : ℕ) (b' : Ballot Proposer) (v' : V),
      (phase2aBelow msgs b').card = n →
      Msg.phase2a b' v' ∈ msgs → b ≤ b' → v' = v from
    hstrong (phase2aBelow msgs b').card b' v' rfl h2a hle
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro b' v' hcard h2a' hle'
    obtain ⟨Q₀, hQ₀, hall₀⟩ := hchosen
    rcases eq_or_lt_of_le hle' with rfl | hlt
    · obtain ⟨a₀, ha₀⟩ := qs.quorum_nonempty hQ₀
      have h2a₀ := (hinv.phase2b_inv a₀ b v (hall₀ a₀ ha₀)).2
      exact hinv.phase2a_unique b v' v h2a' h2a₀
    · obtain ⟨Q, hQ, hcases⟩ := hinv.phase2a_witness b' v' h2a'
      obtain ⟨a_star, ha_inter⟩ := qs.inter_nonempty Q₀ hQ₀ Q hQ
      have ha₀ : a_star ∈ Q₀ := (Finset.mem_inter.mp ha_inter).1
      have haQ : a_star ∈ Q := (Finset.mem_inter.mp ha_inter).2
      have h2b_star := hall₀ a_star ha₀
      rcases hcases with hnone | ⟨vt, rfl, hvt_lt, hvt_2a, hall_p⟩
      · have h1b_none := hnone a_star haQ
        obtain ⟨vt, hvt_eq, _⟩ := hinv.promise_vote a_star b v b' none h2b_star h1b_none hlt
        cases hvt_eq
      · obtain ⟨mv, h1b_star, hmv_le⟩ := hall_p a_star haQ
        obtain ⟨vt', hmv_eq, hb_le_vt'⟩ := hinv.promise_vote a_star b v b' mv h2b_star h1b_star hlt
        have hb_le_vt : b ≤ vt.ballot := hb_le_vt'.trans (hmv_le vt' hmv_eq)
        have hlt_card : (phase2aBelow msgs vt.ballot).card < n :=
          hcard ▸ phase2aBelow_card_lt hvt_2a hvt_lt
        exact ih _ hlt_card vt.ballot vt.value rfl hvt_2a hb_le_vt

/-- Crash-stop intermediate step towards Single-Decree Synod agreement in [Lamport1998] §2.1
(Theorem 1, Appendix A2) and [Lamport2001] §2.2 (`P2`), §2.3, and **not** the crash-recovery cited
result: in any reachable crash-stop Synod state, any two values `v₁, v₂` learned by any two
learners `l₁, l₂` at any two ballots `b₁, b₂` satisfy `v₁ = v₂`. -/
theorem paxos_agreement_crashStop {inputs : Proposer → V}
    {s : SynodState Proposer Acceptor Learner V}
    (hr : Reachable qs inputs s)
    {l₁ l₂ : Learner} {b₁ b₂ : Ballot Proposer} {v₁ v₂ : V}
    (h₁ : s.LearnedAt qs l₁ b₁ v₁)
    (h₂ : s.LearnedAt qs l₂ b₂ v₂) :
    v₁ = v₂ := by
  obtain ⟨xl, hmtr⟩ := hr
  have hinv := synodCoreInv_of_mTr qs hmtr
  have hl_eq := (mTr_sim_noDrop qs hmtr).2.2.2.2
  have hc₁ : ChosenAt qs (traceMsgs qs (initState inputs) xl) b₁ v₁ := by
    obtain ⟨Q₁, hQ₁, hall₁⟩ := h₁
    refine ⟨Q₁, hQ₁, fun a ha => hinv.learner_recv l₁ ⟨a, b₁, v₁⟩ ?_⟩
    rw [← hl_eq]
    exact hall₁ a ha
  have hc₂ : ChosenAt qs (traceMsgs qs (initState inputs) xl) b₂ v₂ := by
    obtain ⟨Q₂, hQ₂, hall₂⟩ := h₂
    refine ⟨Q₂, hQ₂, fun a ha => hinv.learner_recv l₂ ⟨a, b₂, v₂⟩ ?_⟩
    rw [← hl_eq]
    exact hall₂ a ha
  rcases le_total b₁ b₂ with hle | hle
  · obtain ⟨Q₂, hQ₂, hall₂⟩ := hc₂
    obtain ⟨a₂, ha₂⟩ := qs.quorum_nonempty hQ₂
    have h2a₂ := (hinv.phase2b_inv a₂ b₂ v₂ (hall₂ a₂ ha₂)).2
    exact (chosenAt_implies_higher_phase2a_eq_crashStop qs hmtr hc₁ h2a₂ hle).symm
  · obtain ⟨Q₁, hQ₁, hall₁⟩ := hc₁
    obtain ⟨a₁, ha₁⟩ := qs.quorum_nonempty hQ₁
    have h2a₁ := (hinv.phase2b_inv a₁ b₁ v₁ (hall₁ a₁ ha₁)).2
    exact chosenAt_implies_higher_phase2a_eq_crashStop qs hmtr hc₂ h2a₁ hle

private def LearnerRegInv (s : SynodState Proposer Acceptor Learner V) : Prop :=
  ∀ l : Learner,
    (∀ v, (s.learners l).learned = some v → ∃ b, s.LearnedAt qs l b v) ∧
      ((s.learners l).learned = none → ∀ b w, ¬ s.LearnedAt qs l b w)

omit [LinearOrder Proposer] [DecidableEq Learner] [DecidableEq V] in
private lemma learnerRegInv_init (inputs : Proposer → V) :
    LearnerRegInv qs (initState (Learner := Learner) inputs) := by
  intro l
  refine ⟨fun v hv => ?_, fun _ b w ⟨Q, hQ, hall⟩ => ?_⟩
  · simp only [initState] at hv; cases hv
  · obtain ⟨a, ha⟩ := qs.quorum_nonempty hQ
    exact Finset.notMem_empty _ (hall a ha)

private lemma learnerRegInv_tr :
    (synodLts qs (Proposer := Proposer) (Learner := Learner) (V := V)).TrInv
      (LearnerRegInv qs) := by
  intro s act s' htr hinv l
  cases act with
  | prepare _ _ => obtain ⟨_, rfl⟩ := htr; exact hinv l
  | recvPhase1a _ _ =>
    obtain ⟨_, rfl⟩ := htr
    dsimp only [synodStep, synodStepCore]
    split_ifs <;> exact hinv l
  | recvPhase1b p _ _ _ =>
    obtain ⟨_, rfl⟩ := htr
    dsimp only [synodStep, synodStepCore]
    cases (s.proposers p).round with
    | none => exact hinv l
    | some _ =>
      dsimp only []
      split_ifs <;> exact hinv l
  | recvPhase2a _ _ _ =>
    obtain ⟨_, rfl⟩ := htr
    dsimp only [synodStep, synodStepCore]
    split_ifs <;> exact hinv l
  | recvPhase2b l₀ a b v =>
    obtain ⟨_, rfl⟩ := htr
    dsimp only [synodStep, synodStepCore]
    by_cases hll : l = l₀
    · subst hll
      obtain ⟨hsome, hnone⟩ := hinv l
      simp only [SynodState.LearnedAt, ↓reduceIte]
      cases hcur : (s.learners l).learned with
      | some v₀ =>
        simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          Option.some.injEq]
        refine ⟨fun w hw => ?_, fun h => by cases h⟩
        subst hw
        obtain ⟨b₀, Q₀, hQ₀, hall₀⟩ := hsome v₀ hcur
        exact ⟨b₀, Q₀, hQ₀, fun a' ha' => Finset.mem_insert_of_mem (hall₀ a' ha')⟩
      | none =>
        simp only [Option.isNone_none, Bool.true_and]
        split_ifs with hq
        · simp only [decide_eq_true_eq] at hq
          simp only [Option.some.injEq]
          exact ⟨fun w hw => hw ▸ ⟨b, hq⟩, fun h => by cases h⟩
        · simp only [decide_eq_true_eq] at hq
          refine ⟨fun w hw => (by cases hw), fun _ b' w' ⟨Q, hQ, hall⟩ => ?_⟩
          by_cases hbw : b' = b ∧ w' = v
          · obtain ⟨rfl, rfl⟩ := hbw
            exact hq ⟨Q, hQ, hall⟩
          · refine hnone hcur b' w' ⟨Q, hQ, fun a' ha' => ?_⟩
            rcases Finset.mem_insert.mp (hall a' ha') with heq | hold
            · cases heq
              exact absurd ⟨rfl, rfl⟩ hbw
            · exact hold
    · simp only [SynodState.LearnedAt, hll, ↓reduceIte]
      exact hinv l
  | drop _ =>
    obtain ⟨_, rfl⟩ := htr
    exact hinv l
  | crashProposer _ => obtain ⟨_, rfl⟩ := htr; exact hinv l
  | crashAcceptor _ => obtain ⟨_, rfl⟩ := htr; exact hinv l
  | crashLearner l₀ =>
    obtain ⟨_, rfl⟩ := htr
    dsimp only [synodStep, synodStepCore]
    by_cases hll : l = l₀
    · subst hll
      simp only [SynodState.LearnedAt, ↓reduceIte]
      exact hinv l
    · simp only [SynodState.LearnedAt, hll, ↓reduceIte]
      exact hinv l
  | stutter => obtain ⟨_, rfl⟩ := htr; exact hinv l

/-- Crash-stop Synod learner-register characterization: in any reachable crash-stop Synod state,
learner `l`'s operational `learned` register holds `some v` if and only if `l` has learned `v` at
some ballot `b`. -/
theorem Reachable.learned_eq_some_iff {qs : QuorumSystem Acceptor} {inputs : Proposer → V}
    {s : SynodState Proposer Acceptor Learner V} (hr : Reachable qs inputs s)
    {l : Learner} {v : V} :
    (s.learners l).learned = some v ↔ ∃ b, s.LearnedAt qs l b v := by
  obtain ⟨xl, hmtr⟩ := hr
  have hreg :=
    (LTS.mtrInv_of_trInv (learnerRegInv_tr qs) _ _ _ hmtr (learnerRegInv_init qs inputs)) l
  refine ⟨hreg.1 v, fun ⟨b, hlearn⟩ => ?_⟩
  cases hcur : (s.learners l).learned with
  | none => exact absurd hlearn (hreg.2 hcur b v)
  | some v₀ =>
    obtain ⟨b₀, hlearn₀⟩ := hreg.1 v₀ hcur
    have heq : v₀ = v := paxos_agreement_crashStop qs ⟨xl, hmtr⟩ hlearn₀ hlearn
    exact heq ▸ rfl

/-- Crash-stop intermediate step towards Single-Decree Synod nontriviality/validity in
[Lamport1998] §1.2 and [Lamport2001] §2.1, and **not** the crash-recovery cited result: in any
reachable crash-stop Synod state, any value `v` learned by any learner `l` equals some proposer's
initial input. -/
theorem paxos_validity_crashStop {inputs : Proposer → V}
    {s : SynodState Proposer Acceptor Learner V}
    (hr : Reachable qs inputs s)
    {l : Learner} {v : V}
    (hl : (s.learners l).learned = some v) :
    ∃ p : Proposer, inputs p = v := by
  obtain ⟨b, Q, hQ, hall⟩ := hr.learned_eq_some_iff.mp hl
  obtain ⟨a, ha⟩ := qs.quorum_nonempty hQ
  obtain ⟨xl, hmtr⟩ := hr
  have hinv := synodCoreInv_of_mTr qs hmtr
  have hl_eq := (mTr_sim_noDrop qs hmtr).2.2.2.2
  have h2b : Msg.phase2b a b v ∈ traceMsgs qs (initState inputs) xl := by
    apply hinv.learner_recv l ⟨a, b, v⟩
    rw [← hl_eq]
    exact hall a ha
  exact hinv.phase2a_valid b v (hinv.phase2b_inv a b v h2b).2

end Safety

end Cslib.Distributed.Paxos
