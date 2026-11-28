/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Paxos.Quorums
public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Crash-Stop Single-Decree Synod Protocol Step

This module formalizes a **crash-stop intermediate step** towards Lamport's Single-Decree Synod
consensus protocol (§2 of [Lamport1998]; §2 of [Lamport2001]), and **not** the crash-recovery cited
results of those papers. Over separate prepare and accept quorum families (`QuorumSystem`) with
cross-phase intersection, we model the
four Synod phases (`Phase1a`/`1b`/`2a`/`2b`) as a ghost-free asynchronous message-passing labelled
transition system (`Cslib.LTS`) allowing arbitrary message reordering, duplication, packet
loss/omission, and permanent **crash-stop** node failures (`crashed : Bool`).

**Step scope and model deviations:** In [Lamport1998] (§1.3, §2.3, Appendix A2 `Forget`) and
[Lamport2001] (§2.1, §2.5), nodes may fail by stopping and later restart using persistent stable
storage (`lastTried`, `maxBal`, `maxVoted`) while losing volatile per-round state; here crashes are
permanent (`crashed : Bool`), while `.prepare p r` resets per-round proposer fields (`proposed`,
`promised`, `maxVote`). Phase 2b uses [Lamport2001] §2.2's `mb ≤ b` voting guard (`allowsVote`,
updating `maxBal := some b`) rather than [Lamport1998] §2.3 step (4)'s `b = nextBal[q]`. Section 3
Multi-Paxos state-machine / ledger replication also remains open under issue #7207. The quorum
generalization implements the cross-phase condition of [HowardMalkhiSpiegelman2017], §5 Eq. (3),
in this crash-stop kernel: prepare quorums need not intersect each other, and accept quorums need
not intersect each other. Only an earlier accept quorum and a later prepare quorum are intersected
in the agreement proof. This does not add persistent-storage recovery or dynamic reconfiguration.

The protocol state (`SynodState`) is completely ghost-free: proposers, acceptors, and learners store
only the operational registers read by protocol transitions, and packet drops genuinely erase
messages from the live network buffer `msgs`. Safety invariants (the crash-stop `P2^c` / `B3`
quorum-witness condition on `Phase2a` proposals and `P1^a` promise–vote monotonicity) are proved
inductively over a non-dropping shadow execution (`traceMsgs`) and projected onto all reachable
states via network monotonicity.

## Main definitions

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
* [H. Howard, D. Malkhi, and A. Spiegelman, *Flexible Paxos*][HowardMalkhiSpiegelman2017]
-/

public section

namespace Cslib.Distributed.Paxos

open Cslib

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
  le_antisymm a b h₁ h₂ := by cases a; cases b; cases Equiv.injective ofLex (le_antisymm h₁ h₂); rfl
  le_total a b := le_total a.toLexProd b.toLexProd
  max a b := if a.toLexProd ≤ b.toLexProd then b else a
  max_def a b := rfl
  min a b := if a.toLexProd ≤ b.toLexProd then a else b
  min_def a b := rfl
  compare a b := compare a.toLexProd b.toLexProd
  compare_eq_compareOfLessAndEq a b := by
    have heq : a.toLexProd = b.toLexProd ↔ a = b :=
      ⟨fun h => by cases a; cases b; cases Equiv.injective ofLex h; rfl, congrArg Ballot.toLexProd⟩
    rw [LinearOrder.compare_eq_compareOfLessAndEq]
    simp only [compareOfLessAndEq, heq]
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
        if !st.proposed && decide (∃ Q ∈ qs.prepareQuorums, Q ⊆ promised') then
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
      if st.learned.isNone && decide (∃ Q ∈ qs.acceptQuorums, ∀ a' ∈ Q, ⟨a', b, v⟩ ∈ received') then
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
    Reachable qs inputs s' :=
  hs.elim fun xl hxl => hreach.elim fun yl hyl => ⟨xl ++ yl, LTS.MTr.comp (synodLts qs) hxl hyl⟩

/-- The cumulative finite set of packets emitted along execution trace `xl` from `s₀` (ignoring
`.drop` erasures). -/
@[expose] def traceMsgs {Proposer Acceptor Learner V : Type*}
    [LinearOrder Proposer] [DecidableEq Acceptor] [DecidableEq Learner] [DecidableEq V]
    (qs : QuorumSystem Acceptor) (s₀ : SynodState Proposer Acceptor Learner V)
    (xl : List (SynodAction Proposer Acceptor Learner V)) :
    Finset (Msg Proposer Acceptor V) :=
  (xl.foldl (synodStepCore false qs) s₀).msgs

/-- Value `v` is *chosen at ballot `b`* relative to packet set `msgs` when every acceptor in some
quorum `Q ∈ qs.acceptQuorums` has emitted `Phase2b(a, b, v)`. -/
@[expose] def ChosenAt {Proposer Acceptor V : Type*} [DecidableEq Acceptor]
    (qs : QuorumSystem Acceptor) (msgs : Finset (Msg Proposer Acceptor V))
    (b : Ballot Proposer) (v : V) : Prop :=
  ∃ Q ∈ qs.acceptQuorums, ∀ a ∈ Q, Msg.phase2b a b v ∈ msgs

/-- Learner `l` has learned value `v` at ballot `b` in state `s` when `l` has received
`Phase2b(a, b, v)` from every acceptor in some quorum `Q ∈ qs.acceptQuorums`. -/
@[expose] def SynodState.LearnedAt {Proposer Acceptor Learner V : Type*} [DecidableEq Acceptor]
    (qs : QuorumSystem Acceptor) (s : SynodState Proposer Acceptor Learner V)
    (l : Learner) (b : Ballot Proposer) (v : V) : Prop :=
  ∃ Q ∈ qs.acceptQuorums, ∀ a ∈ Q, ⟨a, b, v⟩ ∈ (s.learners l).received

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
  rcases s₁, s₂ with ⟨⟨m₁, _, _, _⟩, ⟨m₂, _, _, _⟩⟩
  subst hp ha hl
  cases act <;> simp only [synodEnabled] at hen ⊢ <;>
    first | exact hen | exact ⟨hen.1, hsub hen.2⟩ | exact hsub hen

private lemma stepCore_sim {s₁ s₂ : SynodState Proposer Acceptor Learner V}
    (act : SynodAction Proposer Acceptor Learner V)
    (hsub : s₁.msgs ⊆ s₂.msgs)
    (hp : s₁.proposers = s₂.proposers) (ha : s₁.acceptors = s₂.acceptors)
    (hl : s₁.learners = s₂.learners) :
    (synodStep qs s₁ act).msgs ⊆ (synodStepCore false qs s₂ act).msgs ∧
      (synodStep qs s₁ act).proposers = (synodStepCore false qs s₂ act).proposers ∧
      (synodStep qs s₁ act).acceptors = (synodStepCore false qs s₂ act).acceptors ∧
      (synodStep qs s₁ act).learners = (synodStepCore false qs s₂ act).learners := by
  rcases s₁, s₂ with ⟨⟨m₁, _, _, _⟩, ⟨m₂, _, _, _⟩⟩
  subst hp ha hl
  cases act <;> dsimp only [synodStep, synodStepCore]
  case drop m => exact ⟨(Finset.erase_subset m _).trans hsub, rfl, rfl, rfl⟩
  all_goals (try split) <;> (try split_ifs) <;>
    exact ⟨by first | exact hsub | exact Finset.insert_subset_insert _ hsub, rfl, rfl, rfl⟩

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
    | refl => exact fun u₀ hsub hp ha hl => ⟨LTS.MTr.refl, hsub, hp, ha, hl⟩
    | @stepL s₁ act s₂ rest s₃ htr _ ih =>
      intro u₀ hsub hp ha hl
      obtain ⟨hen, rfl⟩ := htr
      have ⟨hsub', hp', ha', hl'⟩ := stepCore_sim qs act hsub hp ha hl
      obtain ⟨hmtr', h⟩ := ih (synodStepCore false qs u₀ act) hsub' hp' ha' hl'
      exact ⟨LTS.MTr.stepL ⟨enabled_mono_msgs hen hsub hp ha hl, rfl⟩ hmtr', h⟩
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

/-- Lamport's condition P2c: every emitted `Phase2a(b, v)` is backed by a prepare quorum
`Q ∈ qs.prepareQuorums` of
`Phase1b` promises for `b`, either all carrying `none` or bounded by a prior vote `(vt.ballot, v)`
at `vt.ballot < b`. -/
private def Phase2aQuorumWitness (msgs : Finset (Msg Proposer Acceptor V))
    (b : Ballot Proposer) (v : V) : Prop :=
  ∃ Q ∈ qs.prepareQuorums,
    (∀ a ∈ Q, Msg.phase1b a b none ∈ msgs) ∨
      ∃ vt : Vote Proposer V, vt.value = v ∧ vt.ballot < b ∧
        Msg.phase2a vt.ballot vt.value ∈ msgs ∧
        ∀ a ∈ Q, ∃ mv, Msg.phase1b a b mv ∈ msgs ∧
          ∀ vt', mv = some vt' → vt'.ballot ≤ vt.ballot

omit [DecidableEq V] in
private lemma phase2aQuorumWitness_mono {m₁ m₂ : Finset (Msg Proposer Acceptor V)}
    (hsub : m₁ ⊆ m₂) {b : Ballot Proposer} {v : V}
    (hw : Phase2aQuorumWitness qs m₁ b v) : Phase2aQuorumWitness qs m₂ b v := by
  obtain ⟨Q, hQ, hnone | ⟨vt, hval, hlt, h2a, hall⟩⟩ := hw
  · exact ⟨Q, hQ, Or.inl fun a ha => hsub (hnone a ha)⟩
  · exact ⟨Q, hQ, Or.inr ⟨vt, hval, hlt, hsub h2a, fun a ha =>
      let ⟨mv, hm, hb⟩ := hall a ha
      ⟨mv, hsub hm, hb⟩⟩⟩

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

omit [DecidableEq Learner] [DecidableEq V] in
private lemma mergeVote_promises_inv {inputs : Proposer → V}
    {s : SynodState Proposer Acceptor Learner V} (hinv : SynodCoreInv qs inputs s)
    {p : Proposer} {r : ℕ} (hround : (s.proposers p).round = some r)
    {a : Acceptor} {mv : Option (Vote Proposer V)}
    (h1b : Msg.phase1b a ⟨r, p⟩ mv ∈ s.msgs) :
    ProposerPromiseInv s.msgs ⟨r, p⟩
      (insert a (s.proposers p).promised) (mergeVote (s.proposers p).maxVote mv) := by
  have h1b_prop := (hinv.phase1b_inv a ⟨r, p⟩ mv h1b).2
  match (s.proposers p).maxVote, hinv.prop_promises p r hround with
  | none, hcur =>
    cases mv with
    | none => exact (Finset.forall_mem_insert _ _ _).2 ⟨h1b, hcur⟩
    | some vt₂ =>
      obtain ⟨hvt₂_lt, hvt₂_2a⟩ := h1b_prop vt₂ rfl
      exact ⟨hvt₂_lt, hvt₂_2a, (Finset.forall_mem_insert _ _ _).2
        ⟨⟨_, h1b, fun _ h => Option.some.inj h ▸ le_rfl⟩, fun a' ha' => ⟨none, hcur a' ha', nofun⟩⟩⟩
  | some vt₁, ⟨hvt₁_lt, hvt₁_2a, hall_cur⟩ =>
    cases mv with
    | none =>
      exact ⟨hvt₁_lt, hvt₁_2a, (Finset.forall_mem_insert _ _ _).2 ⟨⟨_, h1b, nofun⟩, hall_cur⟩⟩
    | some vt₂ =>
      obtain ⟨hvt₂_lt, hvt₂_2a⟩ := h1b_prop vt₂ rfl
      dsimp only [ProposerPromiseInv, mergeVote]
      split_ifs with hlt
      · refine ⟨hvt₂_lt, hvt₂_2a, (Finset.forall_mem_insert _ _ _).2
          ⟨⟨_, h1b, fun _ h => Option.some.inj h ▸ le_rfl⟩, fun a' ha' => ?_⟩⟩
        exact (hall_cur a' ha').imp fun _ ⟨hm', hle'⟩ => ⟨hm', fun v h => (hle' v h).trans hlt.le⟩
      · exact ⟨hvt₁_lt, hvt₁_2a, (Finset.forall_mem_insert _ _ _).2
          ⟨⟨_, h1b, fun _ h => Option.some.inj h ▸ not_lt.mp hlt⟩, hall_cur⟩⟩

omit [DecidableEq Learner] [DecidableEq V] in
private lemma SynodCoreInv.of_proposer_update {inputs : Proposer → V}
    {s : SynodState Proposer Acceptor Learner V} (hinv : SynodCoreInv qs inputs s)
    {p : Proposer} {pst' : ProposerState Proposer Acceptor V}
    {msgs' : Finset (Msg Proposer Acceptor V)}
    (hsub : s.msgs ⊆ msgs')
    (hno1b : ∀ a b mv, Msg.phase1b a b mv ∈ msgs' → Msg.phase1b a b mv ∈ s.msgs)
    (hno2b : ∀ a b v, Msg.phase2b a b v ∈ msgs' → Msg.phase2b a b v ∈ s.msgs)
    (hinp : pst'.input = (s.proposers p).input)
    (h2a_round : ∀ r' q v, Msg.phase2a ⟨r', q⟩ v ∈ msgs' →
      if q = p then
        ∃ r_cur, pst'.round = some r_cur ∧ (r' < r_cur ∨ (r' = r_cur ∧ pst'.proposed = true))
      else
        ∃ r_cur, (s.proposers q).round = some r_cur ∧
          (r' < r_cur ∨ (r' = r_cur ∧ (s.proposers q).proposed = true)))
    (h2a_unique : ∀ b v₁ v₂, Msg.phase2a b v₁ ∈ msgs' → Msg.phase2a b v₂ ∈ msgs' → v₁ = v₂)
    (h2a_valid : ∀ b v, Msg.phase2a b v ∈ msgs' → ∃ p₀, inputs p₀ = v)
    (hprom : ∀ r', pst'.round = some r' →
      ProposerPromiseInv msgs' ⟨r', p⟩ pst'.promised pst'.maxVote)
    (h2a_wit : ∀ b v, Msg.phase2a b v ∈ msgs' → Phase2aQuorumWitness qs msgs' b v) :
    SynodCoreInv qs inputs
      { s with
        msgs := msgs'
        proposers := fun q => if q = p then pst' else s.proposers q } where
  prop_input q := by by_cases hqp : q = p <;> simp [hqp, hinp, hinv.prop_input]
  prop_phase2a_round r' q v hm := by
    dsimp only []
    split_ifs <;> simpa [*] using h2a_round r' q v hm
  phase2a_unique := h2a_unique
  phase2a_valid := h2a_valid
  prop_promises q r' hq := by
    dsimp only [] at hq ⊢
    split_ifs at hq ⊢ with hqp
    exacts [hqp ▸ hprom r' hq, proposerPromiseInv_mono hsub (hinv.prop_promises q r' hq)]
  phase2a_witness := h2a_wit
  acc_local a vt hvt := (hinv.acc_local a vt hvt).imp_right fun h => hsub h
  phase1b_inv a b mv hm :=
    let ⟨hmb, hvt⟩ := hinv.phase1b_inv a b mv (hno1b a b mv hm)
    ⟨hmb, fun vt hv => (hvt vt hv).imp_right fun h => hsub h⟩
  phase2b_inv a b v hm := (hinv.phase2b_inv a b v (hno2b a b v hm)).imp_right fun h => hsub h
  promise_vote a b₀ v₀ b mv h2b h1b hlt :=
    hinv.promise_vote a b₀ v₀ b mv (hno2b a b₀ v₀ h2b) (hno1b a b mv h1b) hlt
  learner_recv l av hav := hsub (hinv.learner_recv l av hav)

omit [DecidableEq Learner] [DecidableEq V] in
private lemma SynodCoreInv.of_proposer_update_no2a {inputs : Proposer → V}
    {s : SynodState Proposer Acceptor Learner V} (hinv : SynodCoreInv qs inputs s)
    {p : Proposer} {pst' : ProposerState Proposer Acceptor V}
    {msgs' : Finset (Msg Proposer Acceptor V)}
    (hsub : s.msgs ⊆ msgs')
    (hno1b : ∀ a b mv, Msg.phase1b a b mv ∈ msgs' → Msg.phase1b a b mv ∈ s.msgs)
    (hno2b : ∀ a b v, Msg.phase2b a b v ∈ msgs' → Msg.phase2b a b v ∈ s.msgs)
    (hno2a : ∀ b v, Msg.phase2a b v ∈ msgs' → Msg.phase2a b v ∈ s.msgs)
    (hinp : pst'.input = (s.proposers p).input)
    (hround_p : ∀ r' r_cur, (s.proposers p).round = some r_cur →
      (r' < r_cur ∨ (r' = r_cur ∧ (s.proposers p).proposed = true)) →
      ∃ r_new, pst'.round = some r_new ∧ (r' < r_new ∨ (r' = r_new ∧ pst'.proposed = true)))
    (hprom : ∀ r', pst'.round = some r' →
      ProposerPromiseInv msgs' ⟨r', p⟩ pst'.promised pst'.maxVote) :
    SynodCoreInv qs inputs
      { s with
        msgs := msgs'
        proposers := fun q => if q = p then pst' else s.proposers q } :=
  hinv.of_proposer_update qs hsub hno1b hno2b hinp
    (fun r' q v hm => by
      obtain ⟨r_cur, hr_cur, hrel⟩ := hinv.prop_phase2a_round r' q v (hno2a ⟨r', q⟩ v hm)
      split_ifs with hqp
      · subst hqp; exact hround_p r' r_cur hr_cur hrel
      · exact ⟨r_cur, hr_cur, hrel⟩)
    (fun b v₁ v₂ h₁ h₂ => hinv.phase2a_unique b v₁ v₂ (hno2a b v₁ h₁) (hno2a b v₂ h₂))
    (fun b v hm => hinv.phase2a_valid b v (hno2a b v hm))
    hprom
    (fun b v hm => phase2aQuorumWitness_mono qs hsub (hinv.phase2a_witness b v (hno2a b v hm)))

omit [LinearOrder Proposer] [DecidableEq Learner] [DecidableEq V] in
private lemma acc_field_mono {α β : Type*} [Preorder β]
    (sel : AcceptorState Proposer V → Option α) (k : α → β)
    (acc : Acceptor → AcceptorState Proposer V) (a : Acceptor) (ast' : AcceptorState Proposer V)
    (hmono : ∀ x, sel (acc a) = some x → ∃ x', sel ast' = some x' ∧ k x ≤ k x')
    {a' : Acceptor} {b₀ : β} (h : ∃ x, sel (acc a') = some x ∧ b₀ ≤ k x) :
    ∃ x', sel (if a' = a then ast' else acc a') = some x' ∧ b₀ ≤ k x' := by
  obtain ⟨x, hx, hle⟩ := h
  split_ifs with ha
  · obtain ⟨x', hx', hxx'⟩ := hmono x (ha ▸ hx)
    exact ⟨x', hx', hle.trans hxx'⟩
  · exact ⟨x, hx, hle⟩

omit [DecidableEq Learner] [DecidableEq V] in
private lemma SynodCoreInv.of_acceptor_update {inputs : Proposer → V}
    {s : SynodState Proposer Acceptor Learner V} (hinv : SynodCoreInv qs inputs s)
    {a : Acceptor} {ast' : AcceptorState Proposer V}
    {msgs' : Finset (Msg Proposer Acceptor V)}
    (hsub : s.msgs ⊆ msgs')
    (hno2a : ∀ b v, Msg.phase2a b v ∈ msgs' → Msg.phase2a b v ∈ s.msgs)
    (hmb_mono : ∀ mb, (s.acceptors a).maxBal = some mb → ∃ mb', ast'.maxBal = some mb' ∧ mb ≤ mb')
    (hmv_mono : ∀ vt, (s.acceptors a).maxVoted = some vt →
      ∃ vt', ast'.maxVoted = some vt' ∧ vt.ballot ≤ vt'.ballot)
    (hacc_local : ∀ vt, ast'.maxVoted = some vt →
      (∃ mb, ast'.maxBal = some mb ∧ vt.ballot ≤ mb) ∧ Msg.phase2a vt.ballot vt.value ∈ s.msgs)
    (h1b_new : ∀ a' b' mv, Msg.phase1b a' b' mv ∈ msgs' →
      Msg.phase1b a' b' mv ∈ s.msgs ∨
        (a' = a ∧ (∃ mb, ast'.maxBal = some mb ∧ b' ≤ mb) ∧
          ∀ vt, mv = some vt → vt.ballot < b' ∧ Msg.phase2a vt.ballot vt.value ∈ s.msgs))
    (h2b_new : ∀ a' b' v, Msg.phase2b a' b' v ∈ msgs' →
      Msg.phase2b a' b' v ∈ s.msgs ∨
        (a' = a ∧ (∃ vt, ast'.maxVoted = some vt ∧ b' ≤ vt.ballot) ∧ Msg.phase2a b' v ∈ s.msgs))
    (hpv : ∀ a' b₀ v₀ b' mv,
      Msg.phase2b a' b₀ v₀ ∈ msgs' → Msg.phase1b a' b' mv ∈ msgs' → b₀ < b' →
      ∃ vt, mv = some vt ∧ b₀ ≤ vt.ballot) :
    SynodCoreInv qs inputs
      { s with
        msgs := msgs'
        acceptors := fun q => if q = a then ast' else s.acceptors q } where
  prop_input := hinv.prop_input
  prop_phase2a_round r' q v hm := hinv.prop_phase2a_round r' q v (hno2a ⟨r', q⟩ v hm)
  phase2a_unique b v₁ v₂ h₁ h₂ := hinv.phase2a_unique b v₁ v₂ (hno2a b v₁ h₁) (hno2a b v₂ h₂)
  phase2a_valid b v hm := hinv.phase2a_valid b v (hno2a b v hm)
  prop_promises q r' hq := proposerPromiseInv_mono hsub (hinv.prop_promises q r' hq)
  phase2a_witness b v hm :=
    phase2aQuorumWitness_mono qs hsub (hinv.phase2a_witness b v (hno2a b v hm))
  acc_local a' vt hvt := by
    dsimp only [] at hvt ⊢
    split_ifs at hvt ⊢
    exacts [(hacc_local vt hvt).imp_right fun h => hsub h,
      (hinv.acc_local a' vt hvt).imp_right fun h => hsub h]
  phase1b_inv a' b' mv hm := by
    rcases h1b_new a' b' mv hm with hold | ⟨rfl, hmb, hvt⟩
    · obtain ⟨hmb, hvt⟩ := hinv.phase1b_inv a' b' mv hold
      exact ⟨acc_field_mono AcceptorState.maxBal id s.acceptors a ast' hmb_mono hmb,
        fun vt hv => (hvt vt hv).imp_right fun h => hsub h⟩
    · exact ⟨by simpa only [↓reduceIte] using hmb,
        fun vt hv => (hvt vt hv).imp_right fun h => hsub h⟩
  phase2b_inv a' b' v hm := by
    rcases h2b_new a' b' v hm with hold | ⟨rfl, hvt, h2a⟩
    · obtain ⟨hvt, h2a⟩ := hinv.phase2b_inv a' b' v hold
      exact ⟨acc_field_mono AcceptorState.maxVoted Vote.ballot s.acceptors a ast' hmv_mono hvt,
        hsub h2a⟩
    · exact ⟨by simpa only [↓reduceIte] using hvt, hsub h2a⟩
  promise_vote := hpv
  learner_recv l av hav := hsub (hinv.learner_recv l av hav)

omit [DecidableEq V] in
private lemma SynodCoreInv.of_learner_update {inputs : Proposer → V}
    {s : SynodState Proposer Acceptor Learner V} (hinv : SynodCoreInv qs inputs s)
    {l : Learner} {lst' : LearnerState Proposer Acceptor V}
    (hrecv : ∀ av ∈ lst'.received, Msg.phase2b av.acceptor av.ballot av.value ∈ s.msgs) :
    SynodCoreInv qs inputs
      { s with learners := fun q => if q = l then lst' else s.learners q } :=
  { hinv with
    learner_recv := fun l' av hav => by
      dsimp only [] at hav
      split_ifs at hav
      exacts [hrecv av hav, hinv.learner_recv l' av hav] }

private lemma synodCoreInv_tr (inputs : Proposer → V) :
    (synodLtsNoDrop qs (Learner := Learner)).TrInv (SynodCoreInv qs inputs) := by
  rintro s act _ ⟨hen, rfl⟩ hinv
  cases act with
  | prepare p r =>
    dsimp only [synodStepCore]
    refine hinv.of_proposer_update_no2a qs (Finset.subset_insert _ _)
      (fun _ _ _ hm => Finset.mem_of_mem_insert_of_ne hm nofun)
      (fun _ _ _ hm => Finset.mem_of_mem_insert_of_ne hm nofun)
      (fun _ _ hm => Finset.mem_of_mem_insert_of_ne hm nofun) rfl
      (fun r' r_cur hr_cur hrel => ⟨r, rfl, Or.inl ?_⟩)
      (fun _ _ _ ha => absurd ha (Finset.notMem_empty _))
    have hround_lt := hr_cur ▸ hen.2
    rcases hrel with hlt | ⟨rfl, _⟩ <;> omega
  | recvPhase1a a b =>
    dsimp only [synodStepCore]
    split_ifs with habove
    · have hmb_lt : ∀ mb, (s.acceptors a).maxBal = some mb → mb < b := fun mb hmb => by
        simpa only [aboveMaxBal, hmb, decide_eq_true_eq] using habove
      have hvt_lt : ∀ vt, (s.acceptors a).maxVoted = some vt →
          vt.ballot < b ∧ Msg.phase2a vt.ballot vt.value ∈ s.msgs := fun vt hvt =>
        let ⟨⟨mb, hmb, hle_mb⟩, h2a⟩ := hinv.acc_local a vt hvt
        ⟨hle_mb.trans_lt (hmb_lt mb hmb), h2a⟩
      refine hinv.of_acceptor_update qs (Finset.subset_insert _ _)
        (fun _ _ hm => Finset.mem_of_mem_insert_of_ne hm nofun)
        (fun mb hmb => ⟨b, rfl, (hmb_lt mb hmb).le⟩)
        (fun vt hvt => ⟨vt, hvt, le_rfl⟩)
        (fun vt hvt => ⟨⟨b, rfl, (hvt_lt vt hvt).1.le⟩, (hvt_lt vt hvt).2⟩)
        (fun a' b' mv hm => (Finset.mem_insert.mp hm).symm.imp_right fun h => by
          cases h
          exact ⟨rfl, ⟨_, rfl, le_rfl⟩, hvt_lt⟩)
        (fun _ _ _ hm => Or.inl (Finset.mem_of_mem_insert_of_ne hm nofun))
        (fun a' b₀ v₀ b' mv h2b h1b hlt => ?_)
      have h2b' := Finset.mem_of_mem_insert_of_ne h2b nofun
      rcases Finset.mem_insert.mp h1b with h | h1b'
      · cases h
        exact (hinv.phase2b_inv _ _ _ h2b').1
      · exact hinv.promise_vote _ _ _ _ _ h2b' h1b' hlt
    · exact hinv
  | recvPhase1b p a b mv =>
    dsimp only [synodStepCore]
    cases hround : (s.proposers p).round with
    | none => exact hinv
    | some r =>
      dsimp only []
      split_ifs with hguard hprop_q
      · obtain ⟨rfl, _⟩ := hguard
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hprop_q
        obtain ⟨hnot_prop, Q, hQ, hQsub⟩ := hprop_q
        have hprom' := mergeVote_promises_inv qs hinv hround hen.2
        let val := match mergeVote (s.proposers p).maxVote mv with
          | some vt => vt.value | none => (s.proposers p).input
        have hno_prior_2a : ∀ v_old, Msg.phase2a ⟨r, p⟩ v_old ∉ s.msgs := fun v_old hm_old => by
          obtain ⟨r_cur, hr_cur, hrel⟩ := hinv.prop_phase2a_round r p v_old hm_old
          obtain rfl := Option.some.inj (hround.symm.trans hr_cur)
          exact hrel.elim (lt_irrefl _) fun h => Bool.false_ne_true (hnot_prop ▸ h.2)
        have ⟨hval_valid, hwit_s⟩ : (∃ p₀, inputs p₀ = val) ∧
            Phase2aQuorumWitness qs s.msgs ⟨r, p⟩ val := by
          dsimp only [val]
          exact match mergeVote (s.proposers p).maxVote mv, hprom' with
            | none, hprom' =>
              ⟨⟨p, (hinv.prop_input p).symm⟩, Q, hQ, Or.inl fun a' ha' => hprom' a' (hQsub ha')⟩
            | some vt, ⟨hlt, h2a, hall⟩ =>
              ⟨hinv.phase2a_valid _ _ h2a, Q, hQ,
                Or.inr ⟨vt, rfl, hlt, h2a, fun a' ha' => hall a' (hQsub ha')⟩⟩
        refine hinv.of_proposer_update qs (Finset.subset_insert _ _)
          (fun _ _ _ hm => Finset.mem_of_mem_insert_of_ne hm nofun)
          (fun _ _ _ hm => Finset.mem_of_mem_insert_of_ne hm nofun) rfl
          (fun r' q v hm => ?_)
          (fun b' v₁ v₂ h₁ h₂ => ?_)
          (fun b' v hm => ?_)
          (fun _ hr' => by
            cases hr'; exact proposerPromiseInv_mono (Finset.subset_insert _ _) hprom')
          (fun b' v hm => phase2aQuorumWitness_mono qs (Finset.subset_insert _ _) ?_)
        · rcases Finset.mem_insert.mp hm with h | hm'
          · cases h; simp
          · obtain ⟨r_cur, hr_cur, hrel⟩ := hinv.prop_phase2a_round r' q v hm'
            split_ifs with hqp
            · subst hqp
              obtain rfl := Option.some.inj (hround.symm.trans hr_cur)
              exact ⟨_, rfl, hrel.imp_right fun h => ⟨h.1, rfl⟩⟩
            · exact ⟨r_cur, hr_cur, hrel⟩
        · rcases Finset.mem_insert.mp h₁ with h | h₁' <;>
            rcases Finset.mem_insert.mp h₂ with h' | h₂'
          · cases h; cases h'; rfl
          · cases h; exact absurd h₂' (hno_prior_2a _)
          · cases h'; exact absurd h₁' (hno_prior_2a _)
          · exact hinv.phase2a_unique b' v₁ v₂ h₁' h₂'
        · exact (Finset.mem_insert.mp hm).elim
            (fun h => (Msg.phase2a.inj h).2.symm ▸ hval_valid) (hinv.phase2a_valid b' v)
        · exact (Finset.mem_insert.mp hm).elim
            (fun h => (Msg.phase2a.inj h).1.symm ▸ (Msg.phase2a.inj h).2.symm ▸ hwit_s)
            (hinv.phase2a_witness b' v)
      · obtain ⟨rfl, _⟩ := hguard
        exact hinv.of_proposer_update_no2a qs Finset.Subset.rfl
          (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ h => h) rfl
          (fun _ r_cur hr_cur hrel => ⟨r, rfl, Option.some.inj (hround.symm.trans hr_cur) ▸ hrel⟩)
          (fun _ hr' => Option.some.inj hr' ▸ mergeVote_promises_inv qs hinv hround hen.2)
      · exact hinv
  | recvPhase2a a b v =>
    dsimp only [synodStepCore]
    split_ifs with hallows
    · have hmb_le : ∀ mb, (s.acceptors a).maxBal = some mb → mb ≤ b := fun mb hmb => by
        simpa only [allowsVote, hmb, decide_eq_true_eq] using hallows
      refine hinv.of_acceptor_update qs (Finset.subset_insert _ _)
        (fun _ _ hm => Finset.mem_of_mem_insert_of_ne hm nofun)
        (fun mb hmb => ⟨b, rfl, hmb_le mb hmb⟩)
        (fun vt hvt =>
          let ⟨⟨mb, hmb, hvt_le⟩, _⟩ := hinv.acc_local a vt hvt
          ⟨⟨b, v⟩, rfl, hvt_le.trans (hmb_le mb hmb)⟩)
        (fun _ hvt => Option.some.inj hvt ▸ ⟨⟨b, rfl, le_rfl⟩, hen.2⟩)
        (fun _ _ _ hm => Or.inl (Finset.mem_of_mem_insert_of_ne hm nofun))
        (fun a' b' v' hm => (Finset.mem_insert.mp hm).symm.imp_right fun h => by
          cases h
          exact ⟨rfl, ⟨⟨_, _⟩, rfl, le_rfl⟩, hen.2⟩)
        (fun a' b₀ v₀ b' mv h2b h1b hlt => ?_)
      have h1b' := Finset.mem_of_mem_insert_of_ne h1b nofun
      rcases Finset.mem_insert.mp h2b with h | h2b'
      · cases h
        obtain ⟨⟨mb, hmb, hb'_le_mb⟩, _⟩ := hinv.phase1b_inv _ _ mv h1b'
        exact absurd (hlt.trans_le (hb'_le_mb.trans (hmb_le mb hmb))) (lt_irrefl _)
      · exact hinv.promise_vote a' b₀ v₀ b' mv h2b' h1b' hlt
    · exact hinv
  | recvPhase2b l a b v =>
    exact hinv.of_learner_update qs
      ((Finset.forall_mem_insert _ _ _).2 ⟨hen.2, hinv.learner_recv l⟩)
  | drop _ | stutter => exact hinv
  | crashProposer p =>
    exact hinv.of_proposer_update_no2a qs Finset.Subset.rfl
      (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ h => h) rfl
      (fun _ r_cur hr_cur hrel => ⟨r_cur, hr_cur, hrel⟩)
      (hinv.prop_promises p)
  | crashAcceptor a =>
    exact hinv.of_acceptor_update qs Finset.Subset.rfl (fun _ _ h => h)
      (fun mb hmb => ⟨mb, hmb, le_rfl⟩) (fun vt hvt => ⟨vt, hvt, le_rfl⟩)
      (hinv.acc_local a) (fun _ _ _ h => Or.inl h) (fun _ _ _ h => Or.inl h) hinv.promise_vote
  | crashLearner l =>
    exact hinv.of_learner_update qs (hinv.learner_recv l)

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
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun m hm => ?_).2
    ⟨Msg.phase2a b₁ v₁, Finset.mem_filter.2 ⟨hm₁, decide_eq_true hlt⟩,
      fun h => lt_irrefl b₁ (of_decide_eq_true (Finset.mem_filter.1 h).2)⟩)
  rw [phase2aBelow, Finset.mem_filter] at hm ⊢
  cases m <;>
    first | cases hm.2 | exact ⟨hm.1, decide_eq_true ((of_decide_eq_true hm.2).trans hlt)⟩

/-- Crash-stop intermediate step towards the inductive ballot-choice invariant of [Lamport1998]
§2.1 (Lemma) and [Lamport2001] §2.2 (`P2^b`–`P2^c`), and **not** the crash-recovery cited result:
along any crash-stop `synodLts` execution, if an accept quorum `Q ∈ qs.acceptQuorums` has voted
`(b, v)` in Phase 2b, then every `Phase2a(b', v')` emitted in the trace with `b ≤ b'`
satisfies `v' = v`. -/
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
  obtain ⟨Q₀, hQ₀, hall₀⟩ := hchosen
  refine fun n => Nat.strong_induction_on n fun n ih b' v' hcard h2a' hle' => ?_
  rcases eq_or_lt_of_le hle' with rfl | hlt
  · obtain ⟨a₀, ha₀⟩ := qs.acceptQuorum_nonempty hQ₀
    exact hinv.phase2a_unique b v' v h2a' (hinv.phase2b_inv a₀ b v (hall₀ a₀ ha₀)).2
  · obtain ⟨Q, hQ, hcases⟩ := hinv.phase2a_witness b' v' h2a'
    obtain ⟨a_star, haQ, ha₀⟩ := (qs.inter_nonempty Q hQ Q₀ hQ₀).imp fun _ => Finset.mem_inter.mp
    rcases hcases with hnone | ⟨vt, rfl, hvt_lt, hvt_2a, hall_p⟩
    · obtain ⟨_, ⟨⟩, _⟩ :=
        hinv.promise_vote a_star b v b' none (hall₀ a_star ha₀) (hnone a_star haQ) hlt
    · obtain ⟨mv, h1b_star, hmv_le⟩ := hall_p a_star haQ
      obtain ⟨vt', hmv_eq, hb_le_vt'⟩ :=
        hinv.promise_vote a_star b v b' mv (hall₀ a_star ha₀) h1b_star hlt
      exact ih _ (hcard ▸ phase2aBelow_card_lt hvt_2a hvt_lt) vt.ballot vt.value rfl hvt_2a
        (hb_le_vt'.trans (hmv_le vt' hmv_eq))

private lemma chosenAt_and_phase2a_of_learnedAt {inputs : Proposer → V}
    {xl : List (SynodAction Proposer Acceptor Learner V)}
    {s : SynodState Proposer Acceptor Learner V}
    (hmtr : (synodLts qs).MTr (initState inputs) xl s)
    {l : Learner} {b : Ballot Proposer} {v : V}
    (hl : s.LearnedAt qs l b v) :
    ChosenAt qs (traceMsgs qs (initState inputs) xl) b v ∧
      Msg.phase2a b v ∈ traceMsgs qs (initState inputs) xl := by
  have hinv := synodCoreInv_of_mTr qs hmtr
  have hl_eq := (mTr_sim_noDrop qs hmtr).2.2.2.2
  obtain ⟨Q, hQ, hall⟩ := hl
  have h2b : ∀ a ∈ Q, Msg.phase2b a b v ∈ traceMsgs qs (initState inputs) xl :=
    fun a ha => hinv.learner_recv l ⟨a, b, v⟩ (hl_eq ▸ hall a ha)
  obtain ⟨a₀, ha₀⟩ := qs.acceptQuorum_nonempty hQ
  exact ⟨⟨Q, hQ, h2b⟩, (hinv.phase2b_inv a₀ b v (h2b a₀ ha₀)).2⟩

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
  obtain ⟨hc₁, h2a₁⟩ := chosenAt_and_phase2a_of_learnedAt qs hmtr h₁
  obtain ⟨hc₂, h2a₂⟩ := chosenAt_and_phase2a_of_learnedAt qs hmtr h₂
  rcases le_total b₁ b₂ with hle | hle
  · exact (chosenAt_implies_higher_phase2a_eq_crashStop qs hmtr hc₁ h2a₂ hle).symm
  · exact chosenAt_implies_higher_phase2a_eq_crashStop qs hmtr hc₂ h2a₁ hle

private def LearnerRegInv (s : SynodState Proposer Acceptor Learner V) : Prop :=
  ∀ l : Learner,
    (∀ v, (s.learners l).learned = some v → ∃ b, s.LearnedAt qs l b v) ∧
      ((s.learners l).learned = none → ∀ b w, ¬ s.LearnedAt qs l b w)

omit [LinearOrder Proposer] [DecidableEq Learner] [DecidableEq V] in
private lemma learnerRegInv_init (inputs : Proposer → V) :
    LearnerRegInv qs (initState (Learner := Learner) inputs) := fun _ =>
  ⟨nofun, fun _ _ _ ⟨_, hQ, hall⟩ =>
    let ⟨a, ha⟩ := qs.acceptQuorum_nonempty hQ
    Finset.notMem_empty _ (hall a ha)⟩

private lemma learnerRegInv_tr :
    (synodLts qs (Proposer := Proposer) (Learner := Learner) (V := V)).TrInv
      (LearnerRegInv qs) := by
  rintro s act _ ⟨_, rfl⟩ hinv l
  cases act with
  | recvPhase1b p _ _ _ =>
    dsimp only [synodStep, synodStepCore]
    cases (s.proposers p).round <;> dsimp only [] <;> (try split_ifs) <;> exact hinv l
  | crashLearner l₀ =>
    by_cases hll : l = l₀ <;>
      simpa only [SynodState.LearnedAt, synodStep, synodStepCore, hll, ↓reduceIte] using hinv l
  | recvPhase2b l₀ a b v =>
    dsimp only [synodStep, synodStepCore]
    by_cases hll : l = l₀
    · subst hll
      obtain ⟨hsome, hnone⟩ := hinv l
      simp only [SynodState.LearnedAt, ↓reduceIte]
      cases hcur : (s.learners l).learned with
      | some v₀ =>
        obtain ⟨b₀, Q₀, hQ₀, hall₀⟩ := hsome v₀ hcur
        exact ⟨fun _ hw => Option.some.inj hw ▸
          ⟨b₀, Q₀, hQ₀, fun _ h => Finset.mem_insert_of_mem (hall₀ _ h)⟩, nofun⟩
      | none =>
        split_ifs with hq <;> simp only [Option.isNone_none, Bool.true_and, decide_eq_true_eq] at hq
        · exact ⟨fun _ hw => Option.some.inj hw ▸ ⟨b, hq⟩, nofun⟩
        · refine ⟨nofun, fun _ b' w' ⟨Q, hQ, hall⟩ => hnone hcur b' w' ⟨Q, hQ, fun a' ha' => ?_⟩⟩
          rcases Finset.mem_insert.mp (hall a' ha') with h | hold
          · cases h; exact absurd ⟨Q, hQ, hall⟩ hq
          · exact hold
    · simpa only [SynodState.LearnedAt, hll, ↓reduceIte] using hinv l
  | _ =>
    dsimp only [synodStep, synodStepCore]
    (try split_ifs) <;> exact hinv l

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
    exact congrArg some (paxos_agreement_crashStop qs ⟨xl, hmtr⟩ hlearn₀ hlearn)

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
  obtain ⟨b, hlearn⟩ := hr.learned_eq_some_iff.mp hl
  obtain ⟨xl, hmtr⟩ := hr
  exact (synodCoreInv_of_mTr qs hmtr).phase2a_valid b v
    (chosenAt_and_phase2a_of_learnedAt qs hmtr hlearn).2

end Safety

end Cslib.Distributed.Paxos
