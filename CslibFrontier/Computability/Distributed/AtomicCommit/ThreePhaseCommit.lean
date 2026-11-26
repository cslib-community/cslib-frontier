/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.AtomicCommit.TwoPhaseCommit
import Mathlib.Data.Multiset.Filter

/-!
# Global-Phase Three-Phase Commit and Partition-Cut Impossibility Steps

This module proves two intermediate steps toward non-blocking crash recovery and network-partition
impossibility (after [Skeen1981] and [SkeenStonebraker1983]), not the cited message-passing `3PC`
and crash-recovery endpoints (#7289):

1. **Global-phase FSA and survivor-polling Three-Phase Commit (`3PC`) step (after [Skeen1981],
   §§2–5, pp. 135–141):**
   Inserting the committable buffer state `.preCommitted` (`p_i`) between `.uncertain` (`w_i`) and
   `.committed` (`c_i`) ([Skeen1981], §4, Figure 6, p. 139; §5, Figure 7, p. 140) separates
   `.uncertain` operational sites from `.committed` sites. Unlike `TwoPCState` and `CommitProtocol`,
   `ThreePCState` and `threePCStep?` model centralized `3PC` at the global-phase FSA level via
   coordinator-directed phase-guarded single-site state updates (omitting in-flight message
   buffers), computes `backupPhase` by polling all operational survivors `alive` in one
   `electBackup` step (whereas [Skeen1981]'s Central Site Termination Protocol on p. 141 branches on
   the elected backup's own local state over messages), and is not yet instantiated as a
   `CommitProtocol` or extended with crash-recovery restarts or decentralized quorum `3PC` (#7289).
   Within this global-phase model we prove:
   * **Non-blocking state invariant step (`threePC_no_uncertain_and_committed_globalPhase`):** in
     every reachable configuration of `threePCLts`, if any operational site is `.init` or
     `.uncertain`, then no site (operational or crashed) has decided `.commit`.
   * **Safety and fault-free commit steps:** `threePC_decision_stable_globalPhase`,
     `threePC_agreement_globalPhase` (`AC1`), `threePC_abort_of_vote_no_globalPhase` (`AC2`), and
     `threePC_failureFree_commit_globalPhase` (`AC3`).
   * **Survivor termination steps (`threePCTerminate_mTr_globalPhase`,
     `threePC_nonblocking_termination_globalPhase`):** from every reachable configuration with
     `s.alive.Nonempty`, the operational survivors reach a unanimous decision via crash-free
     `threePCLts` steps without reviving any crashed site.

2. **Partition-cut impossibility step over `CommitProtocol` (after [SkeenStonebraker1983], §V-A,
   Theorem 4, p. 225, and Appendix Proof of Theorem 4, p. 227):**
   For asynchronous point-to-point message-passing protocols (`CommitProtocol` with `NormalStep`
   and group-informed `TimeoutStep`, without crash-recovery states, undeliverable-message
   notification, or a `3PC` instantiation; #7289) subject to cross-group message erasure `cutCfg`,
   no protocol satisfies `CommitProtocol.IsPartitionCutResilient G₁ G₂` for any nonempty disjoint
   groups `(G₁, G₂)` (`not_nonblocking_atomicCommit_of_partitionCut`). When `2 ≤ Fintype.card P`,
   such a simple bipartition (`G₁ ∪ G₂ = Finset.univ`) always exists
   (`not_exists_partitionCutResilient_atomicCommit`).

## Main definitions

* `Cslib.Distributed.AtomicCommit.ThreePCLocalState`: local states of `3PC` (`init`, `uncertain`,
  `preCommitted`, `committed`, `aborted`).
* `Cslib.Distributed.AtomicCommit.ThreePCLocalState.isCommittable`: committability predicate
  (`preCommitted` or `committed`).
* `Cslib.Distributed.AtomicCommit.ThreePCPhase`,
  `Cslib.Distributed.AtomicCommit.ThreePCState`,
  `Cslib.Distributed.AtomicCommit.ThreePCAction`: coordinator phases, global configurations, and
  transition labels of the global-phase `3PC` step.
* `Cslib.Distributed.AtomicCommit.backupPhase`,
  `Cslib.Distributed.AtomicCommit.threePCTerminate`: survivor-polling backup coordinator phase rule
  and termination map for the global-phase `3PC` step.
* `Cslib.Distributed.AtomicCommit.threePCStep?`,
  `Cslib.Distributed.AtomicCommit.threePCLts`,
  `Cslib.Distributed.AtomicCommit.ThreePCReachable`: operational `Cslib.LTS` semantics of the
  global-phase `3PC` step.
* `Cslib.Distributed.AtomicCommit.CommitEnvelope`,
  `Cslib.Distributed.AtomicCommit.CommitConfig`,
  `Cslib.Distributed.AtomicCommit.CommitProtocol`: asynchronous point-to-point commit protocol with
  group-informed partition-timeout steps.
* `Cslib.Distributed.AtomicCommit.PartitionState`,
  `Cslib.Distributed.AtomicCommit.PartitionAction`,
  `Cslib.Distributed.AtomicCommit.CommitProtocol.lts`,
  `Cslib.Distributed.AtomicCommit.CommitProtocol.IsPartitionCutResilient`: operational `cutCfg`
  partition `LTS` and partition-cut resilience predicate.

## Main results

* `Cslib.Distributed.AtomicCommit.threePC_decision_stable_globalPhase`: local decisions are
  irreversible in the global-phase `3PC` step.
* `Cslib.Distributed.AtomicCommit.threePC_no_uncertain_and_committed_globalPhase`: global-phase
  `3PC` step toward Skeen's non-blocking state invariant across normal and backup-recovery steps.
* `Cslib.Distributed.AtomicCommit.threePC_agreement_globalPhase`: global-phase `3PC` step toward
  `UniformAgreement` (`AC1`) across operational and crashed sites.
* `Cslib.Distributed.AtomicCommit.threePC_abort_of_vote_no_globalPhase`: global-phase `3PC` step
  toward `AbortValidity` (`AC2`).
* `Cslib.Distributed.AtomicCommit.threePC_failureFree_commit_globalPhase`: crash-free all-`yes`
  execution of the global-phase `3PC` model reaches `AllDecided _ .commit` (`AC3`).
* `Cslib.Distributed.AtomicCommit.threePCTerminate_mTr_globalPhase`: when `s.coord ∉ s.alive` and
  `b ∈ s.alive`, `threePCTerminate b s` is reached by a crash-free `threePCLts` execution and
  decides unanimously across `s.alive` in agreement with crashed sites.
* `Cslib.Distributed.AtomicCommit.threePC_nonblocking_termination_globalPhase`: every reachable
  `ThreePCState` with `s.alive.Nonempty` terminates among `s.alive` across recursive coordinator
  crashes in the global-phase `3PC` model.
* `Cslib.Distributed.AtomicCommit.cutCfg_comm`,
  `Cslib.Distributed.AtomicCommit.CommitProtocol.IsPartitionCutResilient.symm`: symmetry of
  `cutCfg` and `IsPartitionCutResilient` in `(G₁, G₂)`.
* `Cslib.Distributed.AtomicCommit.not_nonblocking_atomicCommit_of_partitionCut`: partition-cut
  impossibility step over `CommitProtocol` for any nonempty disjoint `(G₁, G₂)`.
* `Cslib.Distributed.AtomicCommit.not_exists_partitionCutResilient_atomicCommit`: for
  `2 ≤ Fintype.card P`, no `CommitProtocol` satisfies `IsPartitionCutResilient` across all simple
  two-way partitions.

## References

* [D. Skeen, *Nonblocking Commit Protocols*][Skeen1981]
* [D. Skeen, M. Stonebraker, *A Formal Model of Crash Recovery in a Distributed
  System*][SkeenStonebraker1983]
-/

public section

namespace Cslib.Distributed.AtomicCommit

open Cslib

/-! ### Part I: Global-phase Three-Phase Commit (`3PC`) step -/

/-- Local automaton states of Skeen's Three-Phase Commit ([Skeen1981], §4, Figure 6, p. 139;
§5, Figure 7, p. 140). -/
inductive ThreePCLocalState where
  /-- Initial state (`q_i`) prior to casting a vote. -/
  | init
  /-- Uncertain / wait state (`w_i`) after voting `.yes`, prior to receiving `PreCommit`. -/
  | uncertain
  /-- Buffer "prepare to commit" state (`p_i`), occupancy of which guarantees all sites voted
  `.yes` while still permitting coordinated abort if no survivor has committed. -/
  | preCommitted
  /-- Irreversible committed state (`c_i`). -/
  | committed
  /-- Irreversible aborted state (`a_i`). -/
  | aborted
  deriving @[expose] DecidableEq, Repr

/-- Decision recorded by a `ThreePCLocalState` (`none` in `.init`, `.uncertain`, and
`.preCommitted`). -/
@[expose] def ThreePCLocalState.decision : ThreePCLocalState → Option Decision
  | .committed => some .commit
  | .aborted => some .abort
  | .init | .uncertain | .preCommitted => none

/-- Skeen's committability predicate ([Skeen1981], §2, pp. 136–137): occupancy of `.preCommitted`
or `.committed` implies every site voted `.yes`. -/
@[expose] def ThreePCLocalState.isCommittable : ThreePCLocalState → Bool
  | .preCommitted | .committed => true
  | .init | .uncertain | .aborted => false

@[simp] theorem ThreePCLocalState.decision_committed :
    ThreePCLocalState.committed.decision = some .commit := rfl

@[simp] theorem ThreePCLocalState.decision_aborted :
    ThreePCLocalState.aborted.decision = some .abort := rfl

@[simp] theorem ThreePCLocalState.decision_init : ThreePCLocalState.init.decision = none := rfl

@[simp] theorem ThreePCLocalState.decision_uncertain :
    ThreePCLocalState.uncertain.decision = none := rfl

@[simp] theorem ThreePCLocalState.decision_preCommitted :
    ThreePCLocalState.preCommitted.decision = none := rfl

/-- A `ThreePCLocalState` decides `.commit` iff it is `.committed`. -/
theorem ThreePCLocalState.decision_eq_some_commit_iff {st : ThreePCLocalState} :
    st.decision = some .commit ↔ st = .committed := by
  cases st <;> simp [ThreePCLocalState.decision]

/-- A `ThreePCLocalState` decides `.abort` iff it is `.aborted`. -/
theorem ThreePCLocalState.decision_eq_some_abort_iff {st : ThreePCLocalState} :
    st.decision = some .abort ↔ st = .aborted := by
  cases st <;> simp [ThreePCLocalState.decision]

/-- Protocol phase directed by the active primary or backup coordinator in `3PC`. -/
inductive ThreePCPhase where
  /-- Phase 1: sites cast their initial `.yes` / `.no` votes. -/
  | collectingVotes
  /-- Phase 2 (or Phase 1 of backup failover when a survivor is `.preCommitted`): advancing
  operational `.uncertain` sites into `.preCommitted` before any site commits. -/
  | preCommitting
  /-- Phase 3: advancing operational `.preCommitted` sites into `.committed` once all operational
  sites are committable. -/
  | committing
  /-- Coordinated abort broadcast to undecided operational sites. -/
  | aborting
  deriving @[expose] DecidableEq, Repr

/-- Global configuration of Skeen's `3PC` in the fail-stop accurate-timeout model. -/
structure ThreePCState (P : Type*) where
  /-- Currently designated coordinator (primary initially; updated by `electBackup` on crash). -/
  coord : P
  /-- Active phase of `coord`. -/
  phase : ThreePCPhase
  /-- Operational (non-crashed) sites. -/
  alive : Finset P
  /-- Local state of each site (preserved permanently across crashes). -/
  localState : P → ThreePCLocalState

/-- Decision vector of a `ThreePCState` across all sites (operational or crashed). -/
@[expose] def ThreePCState.decision {P : Type*} (s : ThreePCState P) (p : P) : Option Decision :=
  (s.localState p).decision

/-- Initial global configuration of `3PC` with primary coordinator `coord`. -/
@[expose] def threePCStart (P : Type*) [Fintype P] (coord : P) : ThreePCState P where
  coord := coord
  phase := .collectingVotes
  alive := Finset.univ
  localState := fun _ => .init

/-- Survivor-polling backup coordinator phase rule for the global-phase `3PC` step (after
[Skeen1981], pp. 140–141, not the message-passing Central Site Termination Protocol; #7289): poll
the operational survivors `alive`:
* if any survivor is `.aborted`, enter `.aborting`;
* else if any survivor is `.committed`, enter `.committing`;
* else if any survivor is `.preCommitted`, enter `.preCommitting` (running the 2-step
  `PreCommit → Commit` round across `alive` before committing);
* otherwise all survivors are `.init` or `.uncertain`, so enter `.aborting`.

Unlike [Skeen1981]'s Central Site Termination Protocol on p. 141, which branches on the elected
backup coordinator's own local state and broadcasts that state over messages in Phase 1, this step
polls all survivors in `alive` directly (#7289). -/
@[expose] def backupPhase {P : Type*} (alive : Finset P) (st : P → ThreePCLocalState) :
    ThreePCPhase :=
  if ∃ p ∈ alive, st p = .aborted then .aborting
  else if ∃ p ∈ alive, st p = .committed then .committing
  else if ∃ p ∈ alive, st p = .preCommitted then .preCommitting
  else .aborting

/-- Closed-form post-failover configuration computed when surviving backup coordinator `b`
completes Skeen's termination protocol across `s.alive` without further crashes. -/
@[expose] def threePCTerminate {P : Type*} [DecidableEq P] (b : P) (s : ThreePCState P) :
    ThreePCState P :=
  match backupPhase s.alive s.localState with
  | .committing | .preCommitting =>
    { coord := b
      phase := .committing
      alive := s.alive
      localState := fun p => if p ∈ s.alive then .committed else s.localState p }
  | .collectingVotes | .aborting =>
    { coord := b
      phase := .aborting
      alive := s.alive
      localState := fun p => if p ∈ s.alive then .aborted else s.localState p }

/-- Transition labels of the `3PC` operational `LTS`. -/
inductive ThreePCAction (P : Type*) where
  /-- Operational site `p` casts `votes p` in Phase 1 (`.init → .uncertain | .aborted`). -/
  | castVote (p : P)
  /-- Primary coordinator enters Phase 2 (`.preCommitting`) once all sites in `P` are operational
  and `.uncertain`. -/
  | startPreCommit
  /-- Primary coordinator enters `.aborting` in Phase 1 upon any `.aborted` site or crash
  timeout. -/
  | primaryAbort
  /-- Active coordinator delivers `PreCommit` to operational `.uncertain` site `p`. -/
  | stepPreCommit (p : P)
  /-- Active coordinator advances `.preCommitting → .committing` once all operational sites are
  committable. -/
  | finishPreCommit
  /-- Active coordinator delivers `Commit` to operational `.preCommitted` site `p`. -/
  | stepCommit (p : P)
  /-- Active coordinator delivers `Abort` to operational undecided site `p`. -/
  | stepAbort (p : P)
  /-- Fail-stop crash of operational site `p`. -/
  | crash (p : P)
  /-- Surviving cohort `b ∈ alive` takes over as backup coordinator when `coord ∉ alive`. -/
  | electBackup (b : P)
  deriving @[expose] DecidableEq, Repr

/-- Whether a `ThreePCAction` involves no new site crashes. -/
@[expose] def ThreePCAction.isCrashFree {P : Type*} : ThreePCAction P → Bool
  | .crash _ => false
  | _ => true

/-- Partial transition function of Skeen's `3PC` with fail-stop crashes and backup coordinator
failover. -/
@[expose] def threePCStep? {P : Type*} [DecidableEq P] [Fintype P] (votes : P → Vote)
    (s : ThreePCState P) (act : ThreePCAction P) : Option (ThreePCState P) :=
  match act with
  | .castVote p =>
    if p ∈ s.alive ∧ s.phase = .collectingVotes ∧ s.localState p = .init then
      let nextSt : ThreePCLocalState := if votes p = .yes then .uncertain else .aborted
      some { s with localState := Function.update s.localState p nextSt }
    else none
  | .startPreCommit =>
    if s.coord ∈ s.alive ∧ s.phase = .collectingVotes ∧ s.alive = Finset.univ ∧
        ∀ q ∈ s.alive, s.localState q = .uncertain then
      some { s with
        phase := .preCommitting
        localState := Function.update s.localState s.coord .preCommitted }
    else none
  | .primaryAbort =>
    if s.coord ∈ s.alive ∧ s.phase = .collectingVotes ∧ ¬(s.localState s.coord).isCommittable ∧
        (s.alive ≠ Finset.univ ∨ ∃ q, s.localState q = .aborted) then
      some { s with
        phase := .aborting
        localState := Function.update s.localState s.coord .aborted }
    else none
  | .stepPreCommit p =>
    if s.coord ∈ s.alive ∧ p ∈ s.alive ∧ s.phase = .preCommitting ∧
        s.localState p = .uncertain then
      some { s with localState := Function.update s.localState p .preCommitted }
    else none
  | .finishPreCommit =>
    if s.coord ∈ s.alive ∧ s.phase = .preCommitting ∧ s.localState s.coord ≠ .aborted ∧
        ∀ q ∈ s.alive, (s.localState q).isCommittable = true then
      some { s with
        phase := .committing
        localState := Function.update s.localState s.coord .committed }
    else none
  | .stepCommit p =>
    if s.coord ∈ s.alive ∧ p ∈ s.alive ∧ s.phase = .committing ∧
        s.localState p = .preCommitted then
      some { s with localState := Function.update s.localState p .committed }
    else none
  | .stepAbort p =>
    if s.coord ∈ s.alive ∧ p ∈ s.alive ∧ s.phase = .aborting ∧
        (s.localState p = .init ∨ s.localState p = .uncertain) then
      some { s with localState := Function.update s.localState p .aborted }
    else none
  | .crash p =>
    if p ∈ s.alive then
      some { s with alive := s.alive.erase p }
    else none
  | .electBackup b =>
    if s.coord ∉ s.alive ∧ b ∈ s.alive then
      some { s with
        coord := b
        phase := backupPhase s.alive s.localState }
    else none

/-- Operational `Cslib.LTS` of the global-phase `3PC` step under fail-stop crashes and survivor
polling (after [Skeen1981], §§2–5, pp. 135–141; #7289). -/
@[expose] def threePCLts {P : Type*} [DecidableEq P] [Fintype P] (votes : P → Vote) :
    LTS (ThreePCState P) (ThreePCAction P) where
  Tr s a s' := threePCStep? votes s a = some s'

/-- Reachability of a `3PC` configuration from `threePCStart P coord₀` in the global-phase `3PC`
step. -/
@[expose] def ThreePCReachable {P : Type*} [DecidableEq P] [Fintype P] (coord₀ : P)
    (votes : P → Vote) (s : ThreePCState P) : Prop :=
  (threePCLts votes).CanReach (threePCStart P coord₀) s

/-! ### Global-phase state invariant, safety, and survivor termination steps -/

section ThreePCSafety

variable {P : Type*} [DecidableEq P] [Fintype P] {coord₀ : P} {votes : P → Vote}

private theorem threePC_canReach_trans {s₁ s₂ s₃ : ThreePCState P}
    (h₁ : (threePCLts votes).CanReach s₁ s₂) (h₂ : (threePCLts votes).CanReach s₂ s₃) :
    (threePCLts votes).CanReach s₁ s₃ := by
  exact h₁.elim fun _ hm₁ => h₂.elim fun _ hm₂ => ⟨_, hm₁.comp _ hm₂⟩

omit [Fintype P] in
private theorem threePC_decision_update {st : P → ThreePCLocalState} {q p : P}
    {newSt : ThreePCLocalState} {d : Decision}
    (hq : ∀ d', (st q).decision = some d' → newSt.decision = some d')
    (hd : (st p).decision = some d) :
    (Function.update st q newSt p).decision = some d := by
  by_cases hp : p = q
  · subst hp; rw [Function.update_self]; exact hq d hd
  · rwa [Function.update_of_ne hp]

private theorem step_threePC_decision_stable {s s' : ThreePCState P} {act : ThreePCAction P}
    (hstep : threePCStep? votes s act = some s') {p : P} {d : Decision}
    (hd : s.decision p = some d) : s'.decision p = some d := by
  cases act <;> dsimp only [threePCStep?] at hstep <;> split at hstep <;> cases hstep <;>
    dsimp only [ThreePCState.decision] at hd ⊢
  · rename_i q hg; exact threePC_decision_update (by simp [hg.2.2]) hd
  · rename_i hg; exact threePC_decision_update (by simp [hg.2.2.2 s.coord hg.1]) hd
  · rename_i hg
    exact threePC_decision_update
      (by have := hg.2.2.1; cases h : s.localState s.coord <;>
            simp_all [ThreePCLocalState.isCommittable]) hd
  · rename_i q hg; exact threePC_decision_update (by simp [hg.2.2.2]) hd
  · rename_i hg
    exact threePC_decision_update
      (by have := hg.2.2.1; cases h : s.localState s.coord <;> simp_all) hd
  · rename_i q hg; exact threePC_decision_update (by simp [hg.2.2.2]) hd
  · rename_i q hg
    exact threePC_decision_update (by rcases hg.2.2.2 with h | h <;> simp [h]) hd
  · exact hd
  · exact hd

/-- Global-phase FSA step toward [Skeen1981], §5 (pp. 140–141), not the cited message-passing `3PC`
result (#7289): local decisions are irreversible along all reachable transitions of `threePCLts`
(normal phase steps, crashes, and backup coordinator failovers). -/
theorem threePC_decision_stable_globalPhase {s s' : ThreePCState P}
    (hreach : (threePCLts votes).CanReach s s') {p : P} {d : Decision}
    (hd : s.decision p = some d) : s'.decision p = some d := by
  rcases hreach with ⟨tr, hmtr⟩
  exact (threePCLts votes).mtrInv_of_trInv
    (fun _ _ _ hstep hd' => step_threePC_decision_stable hstep hd') _ _ _ hmtr hd

/-- Inductive global invariant of Skeen's `3PC` across arbitrary single-site transitions, crashes,
and recursive backup coordinator elections. -/
private structure ThreePCInvariant (votes : P → Vote) (s : ThreePCState P) : Prop where
  noninit_votes : ∀ p, s.localState p ≠ .init → s.localState p = .aborted ∨ votes p = .yes
  committable_all_yes :
    (∃ p, (s.localState p).isCommittable = true) → ∀ q, votes q = .yes ∧ s.localState q ≠ .init
  aborted_disjoint_alive_committable :
    (∃ q, s.localState q = .aborted) → ∀ p ∈ s.alive, (s.localState p).isCommittable = false
  committed_disjoint_aborted :
    ∀ p q, s.localState p = .committed → s.localState q ≠ .aborted
  committed_imp_alive_committable :
    (∃ p, s.localState p = .committed) → ∀ q ∈ s.alive, (s.localState q).isCommittable = true
  phase_collecting :
    s.phase = .collectingVotes → ∀ p, (s.localState p).isCommittable = false
  phase_preCommitting :
    s.phase = .preCommitting →
      (∀ q, votes q = .yes ∧ s.localState q ≠ .init) ∧ (∀ q, s.localState q ≠ .aborted)
  phase_committing :
    s.phase = .committing →
      (∀ q, votes q = .yes ∧ s.localState q ≠ .init) ∧
      (∀ q, s.localState q ≠ .aborted) ∧
      (∀ q ∈ s.alive, (s.localState q).isCommittable = true)
  phase_aborting :
    s.phase = .aborting →
      (∀ q, s.localState q ≠ .committed) ∧
      (∀ q ∈ s.alive, (s.localState q).isCommittable = false)

omit [DecidableEq P] in
private theorem threePCInvariant_start (c : P) :
    ThreePCInvariant votes (threePCStart P c) where
  noninit_votes _ h := absurd rfl h
  committable_all_yes := fun ⟨_, hp⟩ => by
    simp [threePCStart, ThreePCLocalState.isCommittable] at hp
  aborted_disjoint_alive_committable _ _ _ := rfl
  committed_disjoint_aborted _ _ hp := by simp [threePCStart] at hp
  committed_imp_alive_committable := fun ⟨_, hp⟩ => by simp [threePCStart] at hp
  phase_collecting _ _ := rfl
  phase_preCommitting h := by simp [threePCStart] at h
  phase_committing h := by simp [threePCStart] at h
  phase_aborting h := by simp [threePCStart] at h

private theorem not_committed_of_not_committable {st : ThreePCLocalState}
    (h : st.isCommittable = false) : st ≠ .committed := by
  intro hc; subst hc; simp [ThreePCLocalState.isCommittable] at h

omit [Fintype P] in
private theorem functionUpdate_forall {f : P → ThreePCLocalState} (r : P) (v : ThreePCLocalState)
    (pred : ThreePCLocalState → Prop) (hv : pred v) (hf : ∀ q, pred (f q)) (q : P) :
    pred (Function.update f r v q) := by
  rw [Function.update_apply]; split_ifs; exacts [hv, hf q]

omit [Fintype P] in
private theorem threePCInvariant_set_preCommitted {s : ThreePCState P} (r : P) {ph : ThreePCPhase}
    (hph : ph = .preCommitting)
    (hyes : ∀ q, votes q = .yes) (hni : ∀ q, s.localState q ≠ .init)
    (hnab : ∀ q, s.localState q ≠ .aborted) (hncom : ∀ q, s.localState q ≠ .committed) :
    ThreePCInvariant votes
      { s with phase := ph, localState := Function.update s.localState r .preCommitted } :=
  have hnew_ni := functionUpdate_forall r .preCommitted (· ≠ .init) (by decide) hni
  have hnew_nab := functionUpdate_forall r .preCommitted (· ≠ .aborted) (by decide) hnab
  have hnew_ncom := functionUpdate_forall r .preCommitted (· ≠ .committed) (by decide) hncom
  { noninit_votes := fun p _ => Or.inr (hyes p)
    committable_all_yes := fun _ q => ⟨hyes q, hnew_ni q⟩
    aborted_disjoint_alive_committable := fun ⟨q, hq⟩ => False.elim (hnew_nab q hq)
    committed_disjoint_aborted := fun p _ hp => False.elim (hnew_ncom p hp)
    committed_imp_alive_committable := fun ⟨p, hp⟩ => False.elim (hnew_ncom p hp)
    phase_collecting := fun h => by cases hph.symm.trans h
    phase_preCommitting := fun _ => ⟨fun q => ⟨hyes q, hnew_ni q⟩, hnew_nab⟩
    phase_committing := fun h => by cases hph.symm.trans h
    phase_aborting := fun h => by cases hph.symm.trans h }

omit [Fintype P] in
private theorem threePCInvariant_set_committed {s : ThreePCState P} (r : P) {ph : ThreePCPhase}
    (hph : ph = .committing)
    (hyes_ni : ∀ q, votes q = .yes ∧ s.localState q ≠ .init)
    (hnab : ∀ q, s.localState q ≠ .aborted)
    (halive_c : ∀ q ∈ s.alive, (s.localState q).isCommittable = true) :
    ThreePCInvariant votes
      { s with phase := ph, localState := Function.update s.localState r .committed } := by
  subst hph
  have hnew_ni :=
    functionUpdate_forall r .committed (· ≠ .init) (by decide) (fun q => (hyes_ni q).2)
  have hnew_nab := functionUpdate_forall r .committed (· ≠ .aborted) (by decide) hnab
  have hnew_alive : ∀ q ∈ s.alive,
      (Function.update s.localState r .committed q).isCommittable = true := fun q hq => by
    rw [Function.update_apply]; split_ifs; exacts [rfl, halive_c q hq]
  exact
    { noninit_votes := fun p _ => Or.inr (hyes_ni p).1
      committable_all_yes := fun _ q => ⟨(hyes_ni q).1, hnew_ni q⟩
      aborted_disjoint_alive_committable := fun ⟨q, hq⟩ => False.elim (hnew_nab q hq)
      committed_disjoint_aborted := fun _ q _ => hnew_nab q
      committed_imp_alive_committable := fun _ q hq => hnew_alive q hq
      phase_collecting := fun h => by cases h
      phase_preCommitting := fun h => by cases h
      phase_committing := fun _ => ⟨fun q => ⟨(hyes_ni q).1, hnew_ni q⟩, hnew_nab, hnew_alive⟩
      phase_aborting := fun h => by cases h }

omit [DecidableEq P] [Fintype P] in
private theorem backupPhase_ne_collectingVotes (al : Finset P) (st : P → ThreePCLocalState) :
    backupPhase al st ≠ .collectingVotes := by
  unfold backupPhase; split_ifs <;> decide

omit [Fintype P] in
private theorem threePCInvariant_of_all_noncommittable {s : ThreePCState P}
    {ph : ThreePCPhase} (r : P) (v : ThreePCLocalState)
    (hinv : ThreePCInvariant votes s)
    (hph : ph = .collectingVotes ∨ ph = .aborting)
    (hv_nc : v.isCommittable = false)
    (hv_vote : v ≠ .init → v = .aborted ∨ votes r = .yes)
    (hno_comm : ∀ q, (s.localState q).isCommittable = false) :
    ThreePCInvariant votes
      { s with phase := ph, localState := Function.update s.localState r v } :=
  have hnew_nc := functionUpdate_forall r v (·.isCommittable = false) hv_nc hno_comm
  { noninit_votes := fun p hp => by
      dsimp only at hp ⊢
      by_cases hpr : p = r
      · subst hpr; rw [Function.update_self] at hp ⊢; exact hv_vote hp
      · rw [Function.update_of_ne hpr] at hp ⊢; exact hinv.noninit_votes p hp
    committable_all_yes := fun ⟨p, hp⟩ => by rw [hnew_nc p] at hp; cases hp
    aborted_disjoint_alive_committable := fun _ p _ => hnew_nc p
    committed_disjoint_aborted := fun p _ hp =>
      absurd hp (not_committed_of_not_committable (hnew_nc p))
    committed_imp_alive_committable := fun ⟨p, hp⟩ =>
      False.elim (not_committed_of_not_committable (hnew_nc p) hp)
    phase_collecting := fun _ p => hnew_nc p
    phase_preCommitting := fun h => by rcases hph with rfl | rfl <;> cases h
    phase_committing := fun h => by rcases hph with rfl | rfl <;> cases h
    phase_aborting := fun _ =>
      ⟨fun q => not_committed_of_not_committable (hnew_nc q), fun q _ => hnew_nc q⟩ }

private theorem threePCInvariant_step {s s' : ThreePCState P} {act : ThreePCAction P}
    (hinv : ThreePCInvariant votes s) (hstep : threePCStep? votes s act = some s') :
    ThreePCInvariant votes s' := by
  cases act <;> dsimp only [threePCStep?] at hstep <;> split at hstep <;> cases hstep
  case castVote.isTrue p₀ hg =>
    exact threePCInvariant_of_all_noncommittable (ph := s.phase) p₀ _ hinv (Or.inl hg.2.1)
      (by split <;> rfl) (fun _ => by cases hv : votes p₀ <;> simp)
      (hinv.phase_collecting hg.2.1)
  case startPreCommit.isTrue hg =>
    have hall_unc : ∀ q : P, s.localState q = .uncertain := fun q =>
      hg.2.2.2 q (hg.2.2.1.symm ▸ Finset.mem_univ q)
    exact threePCInvariant_set_preCommitted s.coord rfl
      (fun q => (hinv.noninit_votes q (by simp [hall_unc])).resolve_left (by simp [hall_unc]))
      (by simp [hall_unc]) (by simp [hall_unc]) (by simp [hall_unc])
  case primaryAbort.isTrue hg =>
    exact threePCInvariant_of_all_noncommittable s.coord .aborted hinv (Or.inr rfl)
      rfl (fun _ => Or.inl rfl) (hinv.phase_collecting hg.2.1)
  case stepPreCommit.isTrue p₀ hg =>
    obtain ⟨hyes_ni, hnab⟩ := hinv.phase_preCommitting hg.2.2.1
    have hno_com : ∀ r, s.localState r ≠ .committed := fun r hrc => by
      have hcomm := hinv.committed_imp_alive_committable ⟨r, hrc⟩ p₀ hg.2.1
      rw [hg.2.2.2] at hcomm; cases hcomm
    exact threePCInvariant_set_preCommitted (ph := s.phase) p₀ hg.2.2.1 (fun q => (hyes_ni q).1)
      (fun q => (hyes_ni q).2) hnab hno_com
  case finishPreCommit.isTrue hg =>
    obtain ⟨hyes_ni, hnab⟩ := hinv.phase_preCommitting hg.2.1
    exact threePCInvariant_set_committed s.coord rfl hyes_ni hnab hg.2.2.2
  case stepCommit.isTrue p₀ hg =>
    obtain ⟨hyes_ni, hnab, halive_c⟩ := hinv.phase_committing hg.2.2.1
    exact threePCInvariant_set_committed (ph := s.phase) p₀ hg.2.2.1 hyes_ni hnab halive_c
  case stepAbort.isTrue p₀ hg =>
    obtain ⟨hncom, halive_nc⟩ := hinv.phase_aborting hg.2.2.1
    have hnew_ncom := functionUpdate_forall p₀ .aborted (· ≠ .committed) (by decide) hncom
    have hnew_alive : ∀ q ∈ s.alive,
        (Function.update s.localState p₀ .aborted q).isCommittable = false := fun q hq => by
      rw [Function.update_apply]; split_ifs; exacts [rfl, halive_nc q hq]
    refine ⟨?_, ?_, fun _ q hq => hnew_alive q hq, fun p _ hp => False.elim (hnew_ncom p hp),
      fun ⟨p, hp⟩ => False.elim (hnew_ncom p hp),
      (fun h => by cases hg.2.2.1.symm.trans h),
      (fun h => by cases hg.2.2.1.symm.trans h),
      (fun h => by cases hg.2.2.1.symm.trans h),
      fun _ => ⟨hnew_ncom, hnew_alive⟩⟩
    · intro p hp; dsimp only at hp ⊢
      rw [Function.update_apply] at hp ⊢
      split_ifs at hp ⊢; exacts [Or.inl rfl, hinv.noninit_votes p hp]
    · rintro ⟨p, hp⟩ q; dsimp only at hp ⊢
      have hp_old : (s.localState p).isCommittable = true := by
        rw [Function.update_apply] at hp; split_ifs at hp; exacts [(by cases hp), hp]
      exact ⟨(hinv.committable_all_yes ⟨p, hp_old⟩ q).1,
        functionUpdate_forall p₀ .aborted (· ≠ .init) (by decide)
          (fun x => (hinv.committable_all_yes ⟨p, hp_old⟩ x).2) q⟩
  case crash.isTrue p₀ hg =>
    exact ⟨hinv.noninit_votes, hinv.committable_all_yes,
      fun hab q hq => hinv.aborted_disjoint_alive_committable hab q (Finset.mem_of_mem_erase hq),
      hinv.committed_disjoint_aborted,
      fun hcom q hq => hinv.committed_imp_alive_committable hcom q (Finset.mem_of_mem_erase hq),
      hinv.phase_collecting, hinv.phase_preCommitting,
      fun hph => let ⟨h1, h2, h3⟩ := hinv.phase_committing hph
        ⟨h1, h2, fun q hq => h3 q (Finset.mem_of_mem_erase hq)⟩,
      fun hph => let ⟨h1, h2⟩ := hinv.phase_aborting hph
        ⟨h1, fun q hq => h2 q (Finset.mem_of_mem_erase hq)⟩⟩
  case electBackup.isTrue b hg =>
    refine ⟨hinv.noninit_votes, hinv.committable_all_yes, hinv.aborted_disjoint_alive_committable,
      hinv.committed_disjoint_aborted, hinv.committed_imp_alive_committable,
      fun hph => absurd hph (backupPhase_ne_collectingVotes _ _), ?_, ?_, ?_⟩ <;>
      intro hph <;> unfold backupPhase at hph <;> split_ifs at hph with hab hcom hpre
    · obtain ⟨p, hp_al, hp_eq⟩ := hpre
      have hp_comm : (s.localState p).isCommittable = true := by rw [hp_eq]; rfl
      exact ⟨hinv.committable_all_yes ⟨p, hp_comm⟩, fun q hqa => by
        simpa [hp_comm] using hinv.aborted_disjoint_alive_committable ⟨q, hqa⟩ p hp_al⟩
    · obtain ⟨p, _, hp_eq⟩ := hcom
      exact ⟨hinv.committable_all_yes ⟨p, by rw [hp_eq]; rfl⟩,
        fun q => hinv.committed_disjoint_aborted p q hp_eq,
        hinv.committed_imp_alive_committable ⟨p, hp_eq⟩⟩
    · obtain ⟨p, _, hp_eq⟩ := hab
      exact ⟨fun q hqc => hinv.committed_disjoint_aborted q p hqc hp_eq,
        hinv.aborted_disjoint_alive_committable ⟨p, hp_eq⟩⟩
    · have halive_nc : ∀ q ∈ s.alive, (s.localState q).isCommittable = false := fun q hq => by
        cases hst : s.localState q <;>
          first | rfl | exact (hpre ⟨q, hq, hst⟩).elim | exact (hcom ⟨q, hq, hst⟩).elim
      refine ⟨fun q hqc => ?_, halive_nc⟩
      have hb_comm := hinv.committed_imp_alive_committable ⟨q, hqc⟩ b hg.2
      rw [halive_nc b hg.2] at hb_comm; cases hb_comm

private theorem threePCInvariant_of_reachable {s : ThreePCState P}
    (hreach : ThreePCReachable coord₀ votes s) : ThreePCInvariant votes s := by
  rcases hreach with ⟨tr, hmtr⟩
  exact (threePCLts votes).mtrInv_of_trInv
    (fun _ _ _ hstep hinv => threePCInvariant_step hinv hstep) _ _ _ hmtr
    (threePCInvariant_start coord₀)

/-- Global-phase FSA step toward [Skeen1981], §4, Theorem 1 (p. 138), not the cited message-passing
`3PC` result (#7289): in every reachable configuration of `threePCLts` (across single-site phase
steps, fail-stop crashes, and survivor-polling backup failovers), if any operational site is
`.init` or `.uncertain`, then no site—operational or crashed—has decided `.commit`. -/
theorem threePC_no_uncertain_and_committed_globalPhase {s : ThreePCState P}
    (hreach : ThreePCReachable coord₀ votes s)
    (hunc : ∃ q ∈ s.alive, s.localState q = .init ∨ s.localState q = .uncertain) :
    ∀ p, s.decision p ≠ some .commit := by
  have hinv := threePCInvariant_of_reachable hreach
  rcases hunc with ⟨q, hq_al, hq_st⟩
  intro p hp
  have hpc : s.localState p = .committed := ThreePCLocalState.decision_eq_some_commit_iff.mp hp
  have hcomm := hinv.committed_imp_alive_committable ⟨p, hpc⟩ q hq_al
  rcases hq_st with h | h <;> simp [h, ThreePCLocalState.isCommittable] at hcomm

/-- Global-phase FSA step toward [Skeen1981], §§4–5 (pp. 138–141), not the cited message-passing
`3PC` result (#7289): in every reachable configuration of `threePCLts`, all decided sites
(operational or crashed) satisfy `UniformAgreement` (`AC1`). -/
theorem threePC_agreement_globalPhase {s : ThreePCState P}
    (hreach : ThreePCReachable coord₀ votes s) :
    UniformAgreement s.decision := by
  have hinv := threePCInvariant_of_reachable hreach
  intro p q d₁ d₂ hp hq
  cases d₁ <;> cases d₂ <;>
    simp only [ThreePCState.decision, ThreePCLocalState.decision_eq_some_commit_iff,
      ThreePCLocalState.decision_eq_some_abort_iff] at hp hq
  exacts [rfl, (hinv.committed_disjoint_aborted p q hp hq).elim,
    (hinv.committed_disjoint_aborted q p hq hp).elim, rfl]

/-- Global-phase FSA step toward [Skeen1981], §§4–5 (pp. 138–141), not the cited message-passing
`3PC` result (#7289): if any site voted `.no`, no site decides `.commit` in any reachable
configuration of `threePCLts` (`AC2`). -/
theorem threePC_abort_of_vote_no_globalPhase {s : ThreePCState P}
    (hreach : ThreePCReachable coord₀ votes s) :
    AbortValidity votes s.decision := by
  have hinv := threePCInvariant_of_reachable hreach
  intro ⟨p, hp⟩ q hq
  have hcomm : (s.localState q).isCommittable = true := by
    rw [ThreePCLocalState.decision_eq_some_commit_iff.mp hq]; rfl
  simpa [hp] using (hinv.committable_all_yes ⟨q, hcomm⟩ p).1

/-! ### Crash-free batch execution helpers, `AC3`, and non-blocking backup termination -/

private def CrashFreeMTr (votes : P → Vote) (s₁ s₂ : ThreePCState P) : Prop :=
  ∃ tr, (∀ a ∈ tr, a.isCrashFree = true) ∧ (threePCLts votes).MTr s₁ tr s₂

private theorem CrashFreeMTr.refl (s : ThreePCState P) : CrashFreeMTr votes s s :=
  ⟨[], fun _ h => absurd h List.not_mem_nil, .refl⟩

private theorem CrashFreeMTr.step {s₁ s₂ s₃ : ThreePCState P} {a : ThreePCAction P}
    (ha : a.isCrashFree = true) (htr : threePCStep? votes s₁ a = some s₂)
    (hrest : CrashFreeMTr votes s₂ s₃) : CrashFreeMTr votes s₁ s₃ := by
  rcases hrest with ⟨tr, hcf, hmtr⟩
  exact ⟨a :: tr, List.forall_mem_cons.mpr ⟨ha, hcf⟩, .stepL htr hmtr⟩

private theorem CrashFreeMTr.trans {s₁ s₂ s₃ : ThreePCState P}
    (h₁ : CrashFreeMTr votes s₁ s₂) (h₂ : CrashFreeMTr votes s₂ s₃) :
    CrashFreeMTr votes s₁ s₃ := by
  rcases h₁ with ⟨tr₁, hcf₁, hm₁⟩
  rcases h₂ with ⟨tr₂, hcf₂, hm₂⟩
  exact ⟨tr₁ ++ tr₂, List.forall_mem_append.mpr ⟨hcf₁, hcf₂⟩, hm₁.comp _ hm₂⟩

private theorem CrashFreeMTr.invariant {s₁ s₂ : ThreePCState P} (h : CrashFreeMTr votes s₁ s₂)
    (hinv : ThreePCInvariant votes s₁) : ThreePCInvariant votes s₂ :=
  let ⟨_, _, hm⟩ := h
  (threePCLts votes).mtrInv_of_trInv (fun _ _ _ hstep hi => threePCInvariant_step hi hstep) _ _ _
    hm hinv

/-- Generic crash-free sweep applying `actOf q` to every site `q ∈ R ⊆ al` whose local state
satisfies `pred`, updating `R`'s local states to `target`. -/
private theorem crashFree_sweep {c : P} {ph : ThreePCPhase} {al : Finset P}
    {actOf : P → ThreePCAction P} {pred : ThreePCLocalState → Prop}
    {target : P → ThreePCLocalState} (hcf_act : ∀ p, (actOf p).isCrashFree = true)
    (hstep_of : ∀ (q : P) (st : P → ThreePCLocalState), q ∈ al → pred (st q) →
      threePCStep? votes { coord := c, phase := ph, alive := al, localState := st } (actOf q) =
        some { coord := c, phase := ph, alive := al,
               localState := Function.update st q (target q) }) :
    ∀ R : Finset P, R ⊆ al →
      ∀ st : P → ThreePCLocalState, (∀ r ∈ R, pred (st r)) →
        CrashFreeMTr votes
          { coord := c, phase := ph, alive := al, localState := st }
          { coord := c
            phase := ph
            alive := al
            localState := fun p => if p ∈ R then target p else st p } := by
  intro R
  induction R using Finset.induction_on with
  | empty => intro _ st _; simpa using CrashFreeMTr.refl (votes := votes) _
  | @insert q R hqR ih =>
    intro hsub st hst_R
    have hrest := ih (fun r hr => hsub (Finset.mem_insert_of_mem hr))
      (Function.update st q (target q)) fun r hr => by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hr hqR)]
        exact hst_R r (Finset.mem_insert_of_mem hr)
    have hloc_eq : (fun p => if p ∈ R then target p else Function.update st q (target q) p) =
        (fun p => if p ∈ insert q R then target p else st p) := by
      funext p; by_cases hpq : p = q <;> simp [hpq, hqR]
    rw [hloc_eq] at hrest
    exact CrashFreeMTr.step (hcf_act q) (hstep_of q st (hsub (Finset.mem_insert_self q R))
      (hst_R q (Finset.mem_insert_self q R))) hrest

/-- Sweep `{p ∈ s.alive | pred (s.localState p)}` when every operational site outside that filter
already equals `dst`, yielding unanimous `dst` across `s.alive`. -/
private theorem crashFree_sweep_alive_to {s : ThreePCState P} {ph : ThreePCPhase}
    {actOf : P → ThreePCAction P} {pred : ThreePCLocalState → Prop}
    {dst : ThreePCLocalState} (hph : s.phase = ph)
    (hcf_act : ∀ p, (actOf p).isCrashFree = true)
    (hstep_of : ∀ (q : P) (st : P → ThreePCLocalState), q ∈ s.alive → pred (st q) →
      threePCStep? votes { coord := s.coord, phase := ph, alive := s.alive, localState := st }
          (actOf q) =
        some { coord := s.coord, phase := ph, alive := s.alive,
               localState := Function.update st q dst })
    (halive_exhaust : ∀ p ∈ s.alive, ¬ pred (s.localState p) → s.localState p = dst) :
    CrashFreeMTr votes s
      { coord := s.coord
        phase := ph
        alive := s.alive
        localState := fun p => if p ∈ s.alive then dst else s.localState p } := by
  classical
  subst hph
  let R := s.alive.filter (fun p => pred (s.localState p))
  have hcf := crashFree_sweep (votes := votes) (target := fun _ => dst) hcf_act hstep_of R
    (Finset.filter_subset _ _) s.localState (fun _ hr => (Finset.mem_filter.mp hr).2)
  have hfinal_eq : (fun p => if p ∈ R then dst else s.localState p) =
      (fun p => if p ∈ s.alive then dst else s.localState p) := by
    funext p
    by_cases hpal : p ∈ s.alive
    · by_cases hp : pred (s.localState p)
      · simp [R, hpal, hp]
      · simp [R, hpal, halive_exhaust p hpal hp]
    · simp [R, hpal]
  rwa [hfinal_eq] at hcf

private theorem crashFree_castVotes (c : P) (al : Finset P) :
    ∀ R : Finset P, R ⊆ al →
      ∀ st : P → ThreePCLocalState, (∀ r ∈ R, st r = .init) →
        CrashFreeMTr votes
          { coord := c, phase := .collectingVotes, alive := al, localState := st }
          { coord := c
            phase := .collectingVotes
            alive := al
            localState := fun p =>
              if p ∈ R then (if votes p = .yes then .uncertain else .aborted) else st p } :=
  crashFree_sweep (pred := (· = .init)) (fun _ => rfl) fun q st hq_al hq_init => by
    rw [threePCStep?, ite_eq_left ⟨hq_al, rfl, hq_init⟩]

/-- Complete an active `.committing` phase (under `ThreePCInvariant`) into unanimous `.committed`
across `s.alive`. -/
private theorem crashFree_finish_from_committing {s : ThreePCState P}
    (hinv : ThreePCInvariant votes s) (hc : s.coord ∈ s.alive) (hph : s.phase = .committing) :
    CrashFreeMTr votes s
      { coord := s.coord
        phase := .committing
        alive := s.alive
        localState := fun p => if p ∈ s.alive then .committed else s.localState p } := by
  obtain ⟨_, _, halive_c⟩ := hinv.phase_committing hph
  refine crashFree_sweep_alive_to (actOf := .stepCommit) (pred := (· = .preCommitted)) hph
    (fun _ => rfl) (fun q st hq_al hq_pre => ?_) (fun p hpal hnpre => ?_)
  · rw [threePCStep?, ite_eq_left ⟨hc, hq_al, rfl, hq_pre⟩]
  · have hcomm_p := halive_c p hpal
    cases hstp : s.localState p <;>
      simp [hstp, ThreePCLocalState.isCommittable] at hcomm_p hnpre ⊢

/-- Complete an active `.aborting` phase (under `ThreePCInvariant`) into unanimous `.aborted`
across `s.alive`. -/
private theorem crashFree_finish_from_aborting {s : ThreePCState P}
    (hinv : ThreePCInvariant votes s) (hc : s.coord ∈ s.alive) (hph : s.phase = .aborting) :
    CrashFreeMTr votes s
      { coord := s.coord
        phase := .aborting
        alive := s.alive
        localState := fun p => if p ∈ s.alive then .aborted else s.localState p } := by
  obtain ⟨_, halive_nc⟩ := hinv.phase_aborting hph
  refine crashFree_sweep_alive_to (actOf := .stepAbort)
    (pred := fun st => st = .init ∨ st = .uncertain) hph (fun _ => rfl)
    (fun q st hq_al hq_iu => ?_) (fun p hpal hniu => ?_)
  · rw [threePCStep?, ite_eq_left ⟨hc, hq_al, rfl, hq_iu⟩]
  · have hnc := halive_nc p hpal
    cases hstp : s.localState p <;> simp [hstp, ThreePCLocalState.isCommittable] at hnc hniu ⊢

/-- Complete an active `.preCommitting` phase (under `ThreePCInvariant`) into unanimous `.committed`
across `s.alive` by sweeping `.uncertain` sites to `.preCommitted`, stepping `finishPreCommit`, and
completing Phase 3 via `crashFree_finish_from_committing`. -/
private theorem crashFree_finish_from_preCommitting {s : ThreePCState P}
    (hinv : ThreePCInvariant votes s) (hc : s.coord ∈ s.alive) (hph : s.phase = .preCommitting) :
    CrashFreeMTr votes s
      { coord := s.coord
        phase := .committing
        alive := s.alive
        localState := fun p => if p ∈ s.alive then .committed else s.localState p } := by
  obtain ⟨hyes_ni, hnab⟩ := hinv.phase_preCommitting hph
  let R₁ := s.alive.filter (fun p => s.localState p = .uncertain)
  have hs_eq : s = { s with phase := .preCommitting } := by cases s; simp_all
  have hcf₁ := crashFree_sweep (votes := votes) (actOf := .stepPreCommit)
    (pred := (· = .uncertain)) (target := fun _ => .preCommitted) (fun _ => rfl)
    (fun q st hq_al hq_unc => by rw [threePCStep?, ite_eq_left ⟨hc, hq_al, rfl, hq_unc⟩])
    R₁ (Finset.filter_subset _ _) s.localState (fun _ hr => (Finset.mem_filter.mp hr).2)
  rw [← hs_eq] at hcf₁
  let st₁ : P → ThreePCLocalState := fun p => if p ∈ R₁ then .preCommitted else s.localState p
  let s₁ : ThreePCState P :=
    { coord := s.coord, phase := .preCommitting, alive := s.alive, localState := st₁ }
  have hinv₁ : ThreePCInvariant votes s₁ := hcf₁.invariant hinv
  have halive_comm₁ : ∀ q ∈ s.alive, (st₁ q).isCommittable = true := fun q hq => by
    have h₁ := (hyes_ni q).2
    have h₂ := hnab q
    cases hstq : s.localState q <;>
      simp [st₁, R₁, hstq, hq, ThreePCLocalState.isCommittable] at h₁ h₂ ⊢
  let s₂ : ThreePCState P :=
    { coord := s.coord
      phase := .committing
      alive := s.alive
      localState := Function.update st₁ s.coord .committed }
  have hstep_fin : threePCStep? votes s₁ .finishPreCommit = some s₂ := by
    rw [threePCStep?,
      ite_eq_left ⟨hc, rfl, (hinv₁.phase_preCommitting rfl).2 s.coord, halive_comm₁⟩]
  have hinv₂ : ThreePCInvariant votes s₂ := threePCInvariant_step hinv₁ hstep_fin
  have hcf₂ := crashFree_finish_from_committing hinv₂ hc rfl
  have hfinal_eq : (fun p => if p ∈ s.alive then .committed else s₂.localState p) =
      (fun p => if p ∈ s.alive then .committed else s.localState p) := funext fun p => by
    by_cases hpal : p ∈ s.alive
    · simp [hpal]
    · simp [hpal, s₂, st₁, R₁, (ne_of_mem_of_not_mem hc hpal).symm]
  rw [hfinal_eq] at hcf₂
  exact hcf₁.trans (CrashFreeMTr.step rfl hstep_fin hcf₂)

/-- Global-phase FSA step toward [Skeen1981], §5, Figure 7 (p. 140), not the cited message-passing
`3PC` result (#7289): when all sites vote `.yes`, `threePCLts` admits a crash-free execution from
`threePCStart P coord₀` reaching `AllDecided s.decision .commit` with `s.alive = Finset.univ`
(`AC3`). -/
theorem threePC_failureFree_commit_globalPhase (coord₀ : P) (hyes : ∀ p, votes p = .yes) :
    ∃ tr s, (∀ a ∈ tr, a.isCrashFree = true) ∧
      (threePCLts votes).MTr (threePCStart P coord₀) tr s ∧
      AllDecided s.decision .commit ∧ s.alive = Finset.univ := by
  have hcf₁ := crashFree_castVotes (votes := votes) coord₀ Finset.univ Finset.univ
    (Finset.subset_univ _) (fun _ => .init) (fun _ _ => rfl)
  have hloc₁ : (fun p : P => if p ∈ (Finset.univ : Finset P) then
      (if votes p = .yes then ThreePCLocalState.uncertain else .aborted) else .init) =
      (fun _ => .uncertain) := funext fun p => by simp [hyes p]
  rw [hloc₁] at hcf₁
  let s₁ : ThreePCState P :=
    { coord := coord₀, phase := .collectingVotes, alive := Finset.univ,
      localState := fun _ => .uncertain }
  let s₂ : ThreePCState P :=
    { coord := coord₀, phase := .preCommitting, alive := Finset.univ,
      localState := Function.update (fun _ => .uncertain) coord₀ .preCommitted }
  have hstep_pre : threePCStep? votes s₁ .startPreCommit = some s₂ := by
    rw [threePCStep?, ite_eq_left ⟨Finset.mem_univ coord₀, rfl, rfl, fun _ _ => rfl⟩]
  have hinv₂ := threePCInvariant_step (hcf₁.invariant (threePCInvariant_start coord₀)) hstep_pre
  have hcf₂ := crashFree_finish_from_preCommitting hinv₂ (Finset.mem_univ coord₀) rfl
  obtain ⟨tr, hcf, hmtr⟩ := hcf₁.trans (CrashFreeMTr.step rfl hstep_pre hcf₂)
  exact ⟨tr, _, hcf, hmtr, fun p => by simp [ThreePCState.decision, s₂], rfl⟩

/-- Global-phase FSA and survivor-polling step toward [Skeen1981], pp. 140–141, not the cited
message-passing Central Site Termination Protocol result (#7289): from any reachable configuration
`s` with `s.coord ∉ s.alive` and `b ∈ s.alive`, electing `b` via `backupPhase` and sweeping
`s.alive` reaches `threePCTerminate b s` along a crash-free `threePCLts` trace, deciding
unanimously across `s.alive` while preserving `UniformAgreement` and `AbortValidity`. -/
theorem threePCTerminate_mTr_globalPhase {s : ThreePCState P}
    (hreach : ThreePCReachable coord₀ votes s) (hcrashed : s.coord ∉ s.alive) {b : P}
    (hb : b ∈ s.alive) :
    ∃ tr d, (∀ a ∈ tr, a.isCrashFree = true) ∧
      (threePCLts votes).MTr s tr (threePCTerminate b s) ∧
      OperationalDecided s.alive (threePCTerminate b s).decision d ∧
      UniformAgreement (threePCTerminate b s).decision ∧
      AbortValidity votes (threePCTerminate b s).decision := by
  let sB : ThreePCState P :=
    { s with coord := b, phase := backupPhase s.alive s.localState }
  have hstep_el : threePCStep? votes s (.electBackup b) = some sB := by
    rw [threePCStep?, ite_eq_left ⟨hcrashed, hb⟩]
  have hreachB : ThreePCReachable coord₀ votes sB :=
    threePC_canReach_trans hreach ⟨[.electBackup b], LTS.MTr.single _ hstep_el⟩
  have hinvB := threePCInvariant_of_reachable hreachB
  have hcf_tail : CrashFreeMTr votes sB (threePCTerminate b s) := by
    dsimp only [threePCTerminate]
    cases hph : backupPhase s.alive s.localState with
    | collectingVotes => exact absurd hph (backupPhase_ne_collectingVotes _ _)
    | committing => exact crashFree_finish_from_committing hinvB hb hph
    | preCommitting => exact crashFree_finish_from_preCommitting hinvB hb hph
    | aborting => exact crashFree_finish_from_aborting hinvB hb hph
  obtain ⟨tr, hcf, hmtr⟩ := CrashFreeMTr.step rfl hstep_el hcf_tail
  have hreach_fin : ThreePCReachable coord₀ votes (threePCTerminate b s) :=
    threePC_canReach_trans hreach ⟨tr, hmtr⟩
  obtain ⟨d, hdec⟩ : ∃ d, OperationalDecided s.alive (threePCTerminate b s).decision d := by
    dsimp only [threePCTerminate]
    cases backupPhase s.alive s.localState <;>
      exact ⟨_, fun p hp => by simp only [ThreePCState.decision, hp, ↓reduceIte]; rfl⟩
  exact ⟨tr, d, hcf, hmtr, hdec, threePC_agreement_globalPhase hreach_fin,
    threePC_abort_of_vote_no_globalPhase hreach_fin⟩

/-- A crash-free run from reachable `s` that keeps `s.alive` and decides `d` on it witnesses
survivor termination. -/
private theorem threePC_termination_of_crashFree {s s' : ThreePCState P}
    (hreach : ThreePCReachable coord₀ votes s) (hcf : CrashFreeMTr votes s s')
    (halive : s'.alive = s.alive) (d : Decision) (hdec : OperationalDecided s.alive s'.decision d) :
    ∃ tr s' d, (∀ a ∈ tr, a.isCrashFree = true) ∧ (threePCLts votes).MTr s tr s' ∧
      s'.alive = s.alive ∧ OperationalDecided s.alive s'.decision d ∧
      UniformAgreement s'.decision ∧ AbortValidity votes s'.decision :=
  let ⟨tr, hcf, hmtr⟩ := hcf
  have hreach' := threePC_canReach_trans hreach ⟨tr, hmtr⟩
  ⟨tr, s', d, hcf, hmtr, halive, hdec, threePC_agreement_globalPhase hreach',
    threePC_abort_of_vote_no_globalPhase hreach'⟩

/-- Global-phase FSA and survivor-polling step toward [Skeen1981], §§4–5 (pp. 138–141), not the
cited message-passing `3PC` result (#7289): from every reachable configuration `s` of `threePCLts`
(after arbitrary recursive primary and backup coordinator crashes) with `s.alive.Nonempty`, there
is a crash-free `threePCLts` execution among `s.alive` reaching unanimous survivor termination
satisfying `UniformAgreement` and `AbortValidity`. -/
theorem threePC_nonblocking_termination_globalPhase {s : ThreePCState P}
    (hreach : ThreePCReachable coord₀ votes s) (halive : s.alive.Nonempty) :
    ∃ tr s' d, (∀ a ∈ tr, a.isCrashFree = true) ∧
      (threePCLts votes).MTr s tr s' ∧
      s'.alive = s.alive ∧
      OperationalDecided s.alive s'.decision d ∧
      UniformAgreement s'.decision ∧
      AbortValidity votes s'.decision := by
  by_cases hc : s.coord ∈ s.alive
  · have hinv := threePCInvariant_of_reachable hreach
    cases hph : s.phase with
    | preCommitting =>
      exact threePC_termination_of_crashFree hreach
        (crashFree_finish_from_preCommitting hinv hc hph) rfl .commit
        fun p hp => by simp [ThreePCState.decision, hp]
    | committing =>
      exact threePC_termination_of_crashFree hreach (crashFree_finish_from_committing hinv hc hph)
        rfl .commit fun p hp => by simp [ThreePCState.decision, hp]
    | aborting =>
      exact threePC_termination_of_crashFree hreach (crashFree_finish_from_aborting hinv hc hph)
        rfl .abort fun p hp => by simp [ThreePCState.decision, hp]
    | collectingVotes =>
      let R₀ := s.alive.filter (fun p => s.localState p = .init)
      have hs_eq : s = { s with phase := .collectingVotes } := by cases s; simp_all
      have hcf₀ := crashFree_castVotes (votes := votes) s.coord s.alive R₀
        (Finset.filter_subset _ _) s.localState fun _ hr => (Finset.mem_filter.mp hr).2
      rw [← hs_eq] at hcf₀
      let st₁ : P → ThreePCLocalState := fun p =>
        if p ∈ R₀ then (if votes p = .yes then .uncertain else .aborted) else s.localState p
      let s₁ : ThreePCState P :=
        { coord := s.coord, phase := .collectingVotes, alive := s.alive, localState := st₁ }
      have hinv₁ : ThreePCInvariant votes s₁ := hcf₀.invariant hinv
      by_cases hall_ok : s.alive = Finset.univ ∧ ∀ q ∈ s.alive, st₁ q = .uncertain
      · let s₂ : ThreePCState P :=
          { coord := s.coord, phase := .preCommitting, alive := s.alive,
            localState := Function.update st₁ s.coord .preCommitted }
        have hstep_pre : threePCStep? votes s₁ .startPreCommit = some s₂ := by
          rw [threePCStep?, ite_eq_left ⟨hc, rfl, hall_ok.1, hall_ok.2⟩]
        exact threePC_termination_of_crashFree hreach (hcf₀.trans (CrashFreeMTr.step rfl hstep_pre
          (crashFree_finish_from_preCommitting (threePCInvariant_step hinv₁ hstep_pre) hc rfl)))
          rfl .commit fun p hp => by simp [ThreePCState.decision, s₂, hp]
      · have hab_guard : s.alive ≠ Finset.univ ∨ ∃ q, st₁ q = .aborted := by
          by_contra! h
          refine hall_ok ⟨h.1, fun q hq => ?_⟩
          have h₁ : (st₁ q).isCommittable = false := hinv₁.phase_collecting rfl q
          have h₂ : st₁ q ≠ .init := by
            by_cases hqR : q ∈ R₀ <;> simp only [st₁, hqR, ↓reduceIte]
            · split <;> decide
            · exact fun hi => hqR (Finset.mem_filter.mpr ⟨hq, hi⟩)
          have h₃ := h.2 q
          cases hst : st₁ q <;> simp [hst, ThreePCLocalState.isCommittable] at h₁ h₂ h₃ ⊢
        let s₂ : ThreePCState P :=
          { coord := s.coord, phase := .aborting, alive := s.alive,
            localState := Function.update st₁ s.coord .aborted }
        have hstep_ab : threePCStep? votes s₁ .primaryAbort = some s₂ := by
          have hc_nc : ¬(st₁ s.coord).isCommittable = true := by
            rw [hinv₁.phase_collecting rfl s.coord]; decide
          rw [threePCStep?, ite_eq_left ⟨hc, rfl, hc_nc, hab_guard⟩]
        exact threePC_termination_of_crashFree hreach (hcf₀.trans (CrashFreeMTr.step rfl hstep_ab
          (crashFree_finish_from_aborting (threePCInvariant_step hinv₁ hstep_ab) hc rfl)))
          rfl .abort fun p hp => by simp [ThreePCState.decision, s₂, hp]
  · obtain ⟨b, hb⟩ := halive
    obtain ⟨tr, d, hcf, hmtr, hdec, hagr, hval⟩ := threePCTerminate_mTr_globalPhase hreach hc hb
    refine ⟨tr, _, d, hcf, hmtr, ?_, hdec, hagr, hval⟩
    dsimp only [threePCTerminate]
    cases backupPhase s.alive s.localState <;> rfl

end ThreePCSafety

/-! ### Part II: Partition-cut impossibility step over `CommitProtocol` -/

/-- Point-to-point network message envelope from `src` to `dest` carrying `payload`. -/
@[ext]
structure CommitEnvelope (P M : Type*) where
  /-- Sender site. -/
  src : P
  /-- Recipient site. -/
  dest : P
  /-- Protocol message payload. -/
  payload : M
  deriving @[expose] DecidableEq, Repr

/-- Global configuration of an asynchronous message-passing commit protocol. -/
structure CommitConfig (P S M : Type*) where
  /-- Local state of each site. -/
  localState : P → S
  /-- Multiset of in-flight network envelopes. -/
  msgs : Multiset (CommitEnvelope P M)

/-- General asynchronous point-to-point atomic commit protocol over process set `P`, local state
type `S`, and message payload type `M` ([SkeenStonebraker1983], §§III and V, pp. 220–225).

The specification permits arbitrary (possibly infinite) state and message spaces, nondeterministic
local transitions, and partition-timeout transitions informed of the reachable group `G`. -/
structure CommitProtocol (P S M : Type*) where
  /-- Initial local state of site `p` given its own initial vote `v`. -/
  init : P → Vote → S
  /-- Irreversible decision readout of site `p` in local state `s`. -/
  decision : P → S → Option Decision
  /-- No site has decided in its initial state. -/
  init_undecided : ∀ p v, decision p (init p v) = none
  /-- Normal single-site step relation `NormalStep p s recv s' out`: site `p` in state `s`
  processes `recv` (`none` for a spontaneous step or `some e` for an incoming message) and moves to
  `s'` while emitting outgoing messages `out`. -/
  NormalStep : P → S → Option (CommitEnvelope P M) → S → Multiset (CommitEnvelope P M) → Prop
  /-- Partition-timeout step relation `TimeoutStep p G s s' out`: when isolated inside group `G`,
  site `p ∈ G` may take a timeout transition to `s'` and emit intra-group messages `out`. -/
  TimeoutStep : P → Finset P → S → S → Multiset (CommitEnvelope P M) → Prop
  /-- Decisions are write-once along normal transitions. -/
  normal_decision_stable :
    ∀ {p s recv s' out d}, NormalStep p s recv s' out → decision p s = some d →
      decision p s' = some d
  /-- Decisions are write-once along timeout transitions. -/
  timeout_decision_stable :
    ∀ {p G s s' out d}, TimeoutStep p G s s' out → decision p s = some d →
      decision p s' = some d

/-- Filter a message multiset to envelopes internal to a site group `G` (`src ∈ G ∧ dest ∈ G`). -/
@[expose] def intraMsgs {P M : Type*} [DecidableEq P] (G : Finset P)
    (ms : Multiset (CommitEnvelope P M)) : Multiset (CommitEnvelope P M) :=
  ms.filter (fun e => e.src ∈ G ∧ e.dest ∈ G)

/-- Erase cross-partition messages upon a partition into `(G₁, G₂)`, keeping intra-`G₁` and
intra-`G₂` messages while leaving all local states unchanged ([SkeenStonebraker1983], §V-A,
p. 225). -/
@[expose] def cutCfg {P S M : Type*} [DecidableEq P] (G₁ G₂ : Finset P)
    (cfg : CommitConfig P S M) : CommitConfig P S M where
  localState := cfg.localState
  msgs := intraMsgs G₁ cfg.msgs + intraMsgs G₂ cfg.msgs

/-- Cross-partition message erasure is symmetric in `(G₁, G₂)`. -/
theorem cutCfg_comm {P S M : Type*} [DecidableEq P] (G₁ G₂ : Finset P)
    (cfg : CommitConfig P S M) : cutCfg G₁ G₂ cfg = cutCfg G₂ G₁ cfg := by
  simp only [cutCfg, Multiset.add_comm]

/-- Global state of a `CommitProtocol` before (`partitioned = false`) and after
(`partitioned = true`) a two-group network partition. -/
structure PartitionState (P S M : Type*) where
  /-- Whether the network partition has occurred. -/
  partitioned : Bool
  /-- Underlying local states and in-flight message buffer. -/
  cfg : CommitConfig P S M

/-- Transition labels of the partitioned `CommitProtocol` `LTS`. -/
inductive PartitionAction (P M : Type*) where
  /-- Pre-partition single-site step by `p`. -/
  | normal (p : P) (recv : Option (CommitEnvelope P M))
  /-- Occurrence of the network partition `(G₁, G₂)` with loss of cross-group messages. -/
  | cutPartition
  /-- Post-partition intra-group step within `G₁` (`side = false`) or `G₂` (`side = true`). -/
  | groupStep (side : Bool) (p : P) (recv : Option (CommitEnvelope P M))
  deriving @[expose] DecidableEq, Repr

namespace CommitProtocol

variable {P S M : Type*} [DecidableEq P] [DecidableEq M]

/-- Decision vector of a `CommitConfig`. -/
@[expose] def configDecision (π : CommitProtocol P S M) (cfg : CommitConfig P S M) (p : P) :
    Option Decision :=
  π.decision p (cfg.localState p)

/-- Initial pre-partition configuration on vote profile `votes`. -/
@[expose] def initConfig (π : CommitProtocol P S M) (votes : P → Vote) : CommitConfig P S M where
  localState := fun p => π.init p (votes p)
  msgs := 0

/-- Initial `PartitionState` on vote profile `votes`. -/
@[expose] def start (π : CommitProtocol P S M) (votes : P → Vote) : PartitionState P S M where
  partitioned := false
  cfg := π.initConfig votes

/-- Single pre-partition step executed by site `p` on `CommitConfig`. -/
@[expose] def ConfigNormalStep (π : CommitProtocol P S M) (p : P)
    (recv : Option (CommitEnvelope P M)) (cfg cfg' : CommitConfig P S M) : Prop :=
  ∃ s' out,
    (∀ m ∈ out, m.src = p) ∧
    π.NormalStep p (cfg.localState p) recv s' out ∧
    match recv with
    | none =>
      cfg' = { localState := Function.update cfg.localState p s', msgs := cfg.msgs + out }
    | some e =>
      e ∈ cfg.msgs ∧ e.dest = p ∧
      cfg' = { localState := Function.update cfg.localState p s', msgs := cfg.msgs.erase e + out }

/-- Single isolated step executed by site `p ∈ G` during a partition isolating `G`: either an
intra-`G` normal transition or a `TimeoutStep p G` transition. -/
@[expose] def GroupStepOn (π : CommitProtocol P S M) (G : Finset P) (p : P)
    (recv : Option (CommitEnvelope P M)) (cfg cfg' : CommitConfig P S M) : Prop :=
  p ∈ G ∧
  ∃ s' out,
    (∀ m ∈ out, m.src = p) ∧
    match recv with
    | none =>
      (π.NormalStep p (cfg.localState p) none s' out ∨
        π.TimeoutStep p G (cfg.localState p) s' out) ∧
      cfg' = { localState := Function.update cfg.localState p s', msgs := cfg.msgs + out }
    | some e =>
      e ∈ cfg.msgs ∧ e.src ∈ G ∧ e.dest = p ∧
      π.NormalStep p (cfg.localState p) (some e) s' out ∧
      cfg' = { localState := Function.update cfg.localState p s', msgs := cfg.msgs.erase e + out }

/-- Reflexive-transitive closure of pre-partition `ConfigNormalStep` transitions. -/
inductive NormalSteps (π : CommitProtocol P S M) :
    CommitConfig P S M → CommitConfig P S M → Prop where
  | refl (cfg : CommitConfig P S M) : π.NormalSteps cfg cfg
  | tail {cfg₁ cfg₂ cfg₃ : CommitConfig P S M} {p : P} {recv : Option (CommitEnvelope P M)} :
    π.NormalSteps cfg₁ cfg₂ → π.ConfigNormalStep p recv cfg₂ cfg₃ → π.NormalSteps cfg₁ cfg₃

/-- Reflexive-transitive closure of isolated post-partition `GroupStepOn G` transitions. -/
inductive GroupSteps (π : CommitProtocol P S M) (G : Finset P) :
    CommitConfig P S M → CommitConfig P S M → Prop where
  | refl (cfg : CommitConfig P S M) : π.GroupSteps G cfg cfg
  | stepL {cfg₁ cfg₂ cfg₃ : CommitConfig P S M} {p : P} {recv : Option (CommitEnvelope P M)} :
    π.GroupStepOn G p recv cfg₁ cfg₂ → π.GroupSteps G cfg₂ cfg₃ → π.GroupSteps G cfg₁ cfg₃

/-- Operational `Cslib.LTS` of `π` subject to a two-group network partition `(G₁, G₂)`. -/
@[expose] def lts (π : CommitProtocol P S M) (G₁ G₂ : Finset P) :
    LTS (PartitionState P S M) (PartitionAction P M) where
  Tr s act s' :=
    match act with
    | .normal p recv =>
      s.partitioned = false ∧ s'.partitioned = false ∧ π.ConfigNormalStep p recv s.cfg s'.cfg
    | .cutPartition =>
      s.partitioned = false ∧ s' = { partitioned := true, cfg := cutCfg G₁ G₂ s.cfg }
    | .groupStep side p recv =>
      s.partitioned = true ∧ s'.partitioned = true ∧
      π.GroupStepOn (if side then G₂ else G₁) p recv s.cfg s'.cfg

/-- Partition-cut resilience predicate for `CommitProtocol` under cross-group message erasure
`cutCfg` (step after [SkeenStonebraker1983], §V-A, pp. 224–225, without crash-recovery states or a
`3PC` instantiation; #7289): protocol `π` satisfies partition-cut resilience on `(G₁, G₂)` if:
1. (`AC1`) every reachable state of `π.lts G₁ G₂` satisfies `UniformAgreement`,
2. (`AC2`) every reachable state of `π.lts G₁ G₂` satisfies `AbortValidity`,
3. (`AC3`) on all-`.yes` votes, a partition-free execution reaches `AllDecided _ .commit`,
4. (isolated termination) from every partition-free reachable state `cfg`, after `cutCfg G₁ G₂ cfg`
   erases cross-group messages, both `G₁` and `G₂` can independently reach decisions on all of
   their respective sites via isolated `GroupSteps`. -/
structure IsPartitionCutResilient (π : CommitProtocol P S M) (G₁ G₂ : Finset P) : Prop where
  /-- `AC1` Uniform Agreement across all reachable pre- and post-partition states. -/
  agreement : ∀ votes s, (π.lts G₁ G₂).CanReach (π.start votes) s →
    UniformAgreement (π.configDecision s.cfg)
  /-- `AC2` Abort Validity across all reachable pre- and post-partition states. -/
  abortValidity : ∀ votes s, (π.lts G₁ G₂).CanReach (π.start votes) s →
    AbortValidity votes (π.configDecision s.cfg)
  /-- `AC3` Commit Nontriviality on partition-free all-`.yes` runs. -/
  failureFreeCommit : ∃ cfg, π.NormalSteps (π.initConfig (fun _ => .yes)) cfg ∧
    AllDecided (π.configDecision cfg) .commit
  /-- Non-blocking independent termination of each isolated group `G₁` and `G₂`. -/
  nonblockingPartition : ∀ votes cfg, π.NormalSteps (π.initConfig votes) cfg →
    (∃ cfg₁, π.GroupSteps G₁ (cutCfg G₁ G₂ cfg) cfg₁ ∧
      ∀ p ∈ G₁, (π.decision p (cfg₁.localState p)).isSome = true) ∧
    (∃ cfg₂, π.GroupSteps G₂ (cutCfg G₁ G₂ cfg) cfg₂ ∧
      ∀ q ∈ G₂, (π.decision q (cfg₂.localState q)).isSome = true)

/-! #### Indistinguishability, commutation, and discrete-continuity crossing proof -/

private theorem partition_canReach_trans {π : CommitProtocol P S M} {G₁ G₂ : Finset P}
    {s₁ s₂ s₃ : PartitionState P S M}
    (h₁ : (π.lts G₁ G₂).CanReach s₁ s₂) (h₂ : (π.lts G₁ G₂).CanReach s₂ s₃) :
    (π.lts G₁ G₂).CanReach s₁ s₃ := by
  exact h₁.elim fun _ hm₁ => h₂.elim fun _ hm₂ => ⟨_, hm₁.comp _ hm₂⟩

private def GroupViewEq (G : Finset P) (c₁ c₂ : CommitConfig P S M) : Prop :=
  (∀ p ∈ G, c₁.localState p = c₂.localState p) ∧ intraMsgs G c₁.msgs = intraMsgs G c₂.msgs

omit [DecidableEq P] [DecidableEq M] in
private theorem GroupViewEq.refl [DecidableEq P] (G : Finset P) (c : CommitConfig P S M) :
    GroupViewEq G c c :=
  ⟨fun _ _ => rfl, rfl⟩

omit [DecidableEq P] [DecidableEq M] in
private theorem GroupViewEq.symm [DecidableEq P] {G : Finset P} {c₁ c₂ : CommitConfig P S M}
    (h : GroupViewEq G c₁ c₂) : GroupViewEq G c₂ c₁ :=
  ⟨fun p hp => (h.1 p hp).symm, h.2.symm⟩

omit [DecidableEq M] in
private theorem intraMsgs_add (G : Finset P) (a b : Multiset (CommitEnvelope P M)) :
    intraMsgs G (a + b) = intraMsgs G a + intraMsgs G b :=
  Multiset.filter_add _ _ _

private theorem intraMsgs_erase_of_pos {G : Finset P} {ms : Multiset (CommitEnvelope P M)}
    {e : CommitEnvelope P M} (he : e ∈ ms) (hG : e.src ∈ G ∧ e.dest ∈ G) :
    intraMsgs G (ms.erase e) = (intraMsgs G ms).erase e := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem he
  simp only [intraMsgs, Multiset.erase_cons_head]
  rw [Multiset.filter_cons_of_pos (p := fun d => d.src ∈ G ∧ d.dest ∈ G) t hG,
    Multiset.erase_cons_head]

private theorem intraMsgs_erase_of_neg {G : Finset P} {ms : Multiset (CommitEnvelope P M)}
    {e : CommitEnvelope P M} (he : e ∈ ms) (hG : ¬(e.src ∈ G ∧ e.dest ∈ G)) :
    intraMsgs G (ms.erase e) = intraMsgs G ms := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem he
  simp only [intraMsgs, Multiset.erase_cons_head]
  rw [Multiset.filter_cons_of_neg (p := fun d => d.src ∈ G ∧ d.dest ∈ G) t hG]

omit [DecidableEq M] in
private theorem intraMsgs_eq_zero_of_src_notMem {G : Finset P} {p : P} (hp : p ∉ G)
    {out : Multiset (CommitEnvelope P M)} (hout : ∀ m ∈ out, m.src = p) :
    intraMsgs G out = 0 := by
  rw [intraMsgs, Multiset.filter_eq_nil]
  intro m hm hmem
  exact hp (hout m hm ▸ hmem.1)

/-- Any step by a process `p ∉ G` leaves `G`'s local states and `intraMsgs G` completely
unchanged. -/
private theorem groupViewEq_of_step_outside {G : Finset P} {p : P} (hp : p ∉ G)
    {cfg : CommitConfig P S M} {s' : S} {out : Multiset (CommitEnvelope P M)}
    (hout : ∀ m ∈ out, m.src = p) :
    GroupViewEq G cfg
      { localState := Function.update cfg.localState p s', msgs := cfg.msgs + out } ∧
    ∀ {e : CommitEnvelope P M}, e ∈ cfg.msgs → e.dest = p →
      GroupViewEq G cfg
        { localState := Function.update cfg.localState p s', msgs := cfg.msgs.erase e + out } := by
  have hloc : ∀ q ∈ G, cfg.localState q = Function.update cfg.localState p s' q := fun q hq =>
    (Function.update_of_ne (ne_of_mem_of_not_mem hq hp) _ _).symm
  have hout0 : intraMsgs G out = 0 := intraMsgs_eq_zero_of_src_notMem hp hout
  refine ⟨⟨hloc, by simp only [intraMsgs_add, hout0, Multiset.add_zero]⟩,
    fun he hdest => ⟨hloc, ?_⟩⟩
  simp only [intraMsgs_add, hout0, Multiset.add_zero,
    intraMsgs_erase_of_neg he fun h => hp (hdest ▸ h.2)]

private theorem groupViewEq_of_normalStep_outside {π : CommitProtocol P S M} {G : Finset P}
    {p : P} (hp : p ∉ G) {recv : Option (CommitEnvelope P M)} {cfg cfg' : CommitConfig P S M}
    (hstep : π.ConfigNormalStep p recv cfg cfg') : GroupViewEq G cfg cfg' := by
  rcases hstep with ⟨s', out, hout, _, hrec⟩
  have ⟨hnone, hsome⟩ := groupViewEq_of_step_outside (cfg := cfg) (s' := s') hp hout
  rcases recv with _ | e
  · exact hrec ▸ hnone
  · exact hrec.2.2 ▸ hsome hrec.1 hrec.2.1

private theorem groupViewEq_of_groupStep_disjoint {π : CommitProtocol P S M} {G₁ G₂ : Finset P}
    (hdisj : Disjoint G₁ G₂) {p : P} {recv : Option (CommitEnvelope P M)}
    {cfg cfg' : CommitConfig P S M} (hstep : π.GroupStepOn G₁ p recv cfg cfg') :
    GroupViewEq G₂ cfg cfg' := by
  rcases hstep with ⟨hp₁, s', out, hout, hrec⟩
  have ⟨hnone, hsome⟩ :=
    groupViewEq_of_step_outside (cfg := cfg) (s' := s') (Finset.disjoint_left.mp hdisj hp₁) hout
  rcases recv with _ | e
  · exact hrec.2 ▸ hnone
  · exact hrec.2.2.2.2 ▸ hsome hrec.1 hrec.2.2.1

omit [DecidableEq M] in
private theorem groupViewEq_cutCfg_left (G₁ G₂ : Finset P) (hdisj : Disjoint G₁ G₂)
    (cfg : CommitConfig P S M) : GroupViewEq G₁ (cutCfg G₁ G₂ cfg) cfg := by
  refine ⟨fun _ _ => rfl, ?_⟩
  have h2 : intraMsgs G₁ (intraMsgs G₂ cfg.msgs) = 0 := Multiset.filter_eq_nil.mpr
    fun e he h => Finset.disjoint_left.mp hdisj h.1 (Multiset.mem_filter.mp he).2.1
  dsimp only [cutCfg]
  rw [intraMsgs_add, h2, Multiset.add_zero]
  simp only [intraMsgs, Multiset.filter_filter, and_self]

omit [DecidableEq M] in
private theorem groupViewEq_cutCfg_right (G₁ G₂ : Finset P) (hdisj : Disjoint G₁ G₂)
    (cfg : CommitConfig P S M) : GroupViewEq G₂ (cutCfg G₁ G₂ cfg) cfg := by
  rw [cutCfg_comm]
  exact groupViewEq_cutCfg_left G₂ G₁ hdisj.symm cfg

/-- Single-step simulation of `GroupStepOn G` across `GroupViewEq G`. -/
private theorem groupStepOn_congr {π : CommitProtocol P S M} {G : Finset P} {p : P}
    {recv : Option (CommitEnvelope P M)} {c₁ c₁' c₂ : CommitConfig P S M}
    (hstep : π.GroupStepOn G p recv c₁ c₁') (heq : GroupViewEq G c₁ c₂) :
    ∃ c₂', π.GroupStepOn G p recv c₂ c₂' ∧ GroupViewEq G c₁' c₂' := by
  rcases hstep with ⟨hpG, s', out, hout, hrec⟩
  have hloc_p : c₁.localState p = c₂.localState p := heq.1 p hpG
  have hloc' : ∀ q ∈ G,
      Function.update c₁.localState p s' q = Function.update c₂.localState p s' q := fun q hq => by
    simp only [Function.update_apply, heq.1 q hq]
  cases recv with
  | none =>
    rcases hrec with ⟨htr, rfl⟩
    rw [hloc_p] at htr
    refine ⟨{ localState := Function.update c₂.localState p s', msgs := c₂.msgs + out },
      ⟨hpG, s', out, hout, htr, rfl⟩, hloc', ?_⟩
    simp only [intraMsgs_add, heq.2]
  | some e =>
    rcases hrec with ⟨he₁, hsrcG, hdest, htr, rfl⟩
    rw [hloc_p] at htr
    have he₂ : e ∈ c₂.msgs := Multiset.mem_of_mem_filter
      (heq.2 ▸ Multiset.mem_filter.mpr ⟨he₁, hsrcG, hdest ▸ hpG⟩ : e ∈ intraMsgs G c₂.msgs)
    refine ⟨{ localState := Function.update c₂.localState p s', msgs := c₂.msgs.erase e + out },
      ⟨hpG, s', out, hout, he₂, hsrcG, hdest, htr, rfl⟩, hloc', ?_⟩
    simp only [intraMsgs_add, intraMsgs_erase_of_pos he₁ ⟨hsrcG, hdest ▸ hpG⟩,
      intraMsgs_erase_of_pos he₂ ⟨hsrcG, hdest ▸ hpG⟩, heq.2]

/-- Multi-step simulation of `GroupSteps G` across `GroupViewEq G`. -/
private theorem groupSteps_congr {π : CommitProtocol P S M} {G : Finset P}
    {c₁ c₁' c₂ : CommitConfig P S M} (hsteps : π.GroupSteps G c₁ c₁')
    (heq : GroupViewEq G c₁ c₂) :
    ∃ c₂', π.GroupSteps G c₂ c₂' ∧ GroupViewEq G c₁' c₂' := by
  induction hsteps generalizing c₂ with
  | refl => exact ⟨c₂, .refl c₂, heq⟩
  | stepL hstep _ ih =>
    obtain ⟨c₂_mid, hstep₂, heq_mid⟩ := groupStepOn_congr hstep heq
    obtain ⟨c₂', hsteps₂, heq'⟩ := ih heq_mid
    exact ⟨c₂', .stepL hstep₂ hsteps₂, heq'⟩

private theorem canReach_of_normalSteps {π : CommitProtocol P S M} {G₁ G₂ : Finset P}
    {c₁ c₂ : CommitConfig P S M} (h : π.NormalSteps c₁ c₂) :
    (π.lts G₁ G₂).CanReach ⟨false, c₁⟩ ⟨false, c₂⟩ := by
  induction h with
  | refl => exact LTS.CanReach.refl _ _
  | @tail _ _ p recv _ hstep ih =>
    exact partition_canReach_trans ih ⟨[.normal p recv], LTS.MTr.single _ ⟨rfl, rfl, hstep⟩⟩

private theorem canReach_of_groupSteps {π : CommitProtocol P S M} {G₁ G₂ : Finset P}
    (side : Bool) {c₁ c₂ : CommitConfig P S M}
    (h : π.GroupSteps (if side then G₂ else G₁) c₁ c₂) :
    (π.lts G₁ G₂).CanReach ⟨true, c₁⟩ ⟨true, c₂⟩ := by
  induction h with
  | refl => exact LTS.CanReach.refl _ _
  | @stepL _ _ _ p recv hstep _ ih =>
    exact partition_canReach_trans
      ⟨[.groupStep side p recv], LTS.MTr.single _ ⟨rfl, rfl, hstep⟩⟩ ih

private theorem groupSteps_preserve_outside {π : CommitProtocol P S M} {G₁ G₂ : Finset P}
    (hdisj : Disjoint G₁ G₂) {c₁ c₂ : CommitConfig P S M} (h : π.GroupSteps G₁ c₁ c₂) :
    GroupViewEq G₂ c₁ c₂ := by
  induction h with
  | refl => exact GroupViewEq.refl G₂ _
  | stepL hstep _ ih =>
    have h1 := groupViewEq_of_groupStep_disjoint hdisj hstep
    exact ⟨fun q hq => (h1.1 q hq).trans (ih.1 q hq), h1.2.trans ih.2⟩

private def CanGroupCommit (π : CommitProtocol P S M) (G : Finset P)
    (cfg : CommitConfig P S M) : Prop :=
  ∃ cfg', π.GroupSteps G cfg cfg' ∧ ∃ p ∈ G, π.decision p (cfg'.localState p) = some .commit

private theorem canGroupCommit_of_viewEq {π : CommitProtocol P S M} {G : Finset P}
    {c₁ c₂ : CommitConfig P S M} (heq : GroupViewEq G c₁ c₂) :
    CanGroupCommit π G c₁ → CanGroupCommit π G c₂ := by
  rintro ⟨c₁', hsteps₁, p, hpG, hdec⟩
  obtain ⟨c₂', hsteps₂, heq'⟩ := groupSteps_congr hsteps₁ heq
  exact ⟨c₂', hsteps₂, p, hpG, (heq'.1 p hpG) ▸ hdec⟩

private def swapPartitionSide : PartitionAction P M → PartitionAction P M
  | .normal p recv => .normal p recv
  | .cutPartition => .cutPartition
  | .groupStep side p recv => .groupStep (!side) p recv

private theorem canReach_swapGroups {π : CommitProtocol P S M} {G₁ G₂ : Finset P}
    {s₁ s₂ : PartitionState P S M} (h : (π.lts G₁ G₂).CanReach s₁ s₂) :
    (π.lts G₂ G₁).CanReach s₁ s₂ := by
  rcases h with ⟨tr, hmtr⟩
  induction hmtr with
  | refl => exact LTS.CanReach.refl _ _
  | @stepL s_a act s_b _ _ htr _ ih =>
    have htr' : (π.lts G₂ G₁).Tr s_a (swapPartitionSide act) s_b := by
      cases act with
      | normal p recv => exact htr
      | cutPartition =>
        dsimp only [lts, swapPartitionSide] at htr ⊢
        rw [cutCfg_comm G₂ G₁]
        exact htr
      | groupStep side p recv => cases side <;> exact htr
    exact partition_canReach_trans ⟨[swapPartitionSide act], LTS.MTr.single _ htr'⟩ ih

/-- `IsPartitionCutResilient` is symmetric in the two isolated groups `(G₁, G₂)`. -/
theorem IsPartitionCutResilient.symm {π : CommitProtocol P S M} {G₁ G₂ : Finset P}
    (h : π.IsPartitionCutResilient G₁ G₂) : π.IsPartitionCutResilient G₂ G₁ where
  agreement votes s hr := h.agreement votes s (canReach_swapGroups hr)
  abortValidity votes s hr := h.abortValidity votes s (canReach_swapGroups hr)
  failureFreeCommit := h.failureFreeCommit
  nonblockingPartition votes cfg hn := by
    rw [cutCfg_comm G₂ G₁]
    exact (h.nonblockingPartition votes cfg hn).symm

private theorem not_canGroupCommit_init_left {π : CommitProtocol P S M} {G₁ G₂ : Finset P}
    (hG₂ : G₂.Nonempty) (hdisj : Disjoint G₁ G₂) (hres : π.IsPartitionCutResilient G₁ G₂) :
    ¬ CanGroupCommit π G₁ (cutCfg G₁ G₂ (π.initConfig (fun _ => .yes))) := by
  rintro ⟨cfg₁, hsteps₁, p₁, hp₁, hdec₁⟩
  let votes₁ : P → Vote := fun r => if r ∈ G₁ then .yes else .no
  obtain ⟨q₀, hq₀⟩ := hG₂
  have hq₀_not : q₀ ∉ G₁ := Finset.disjoint_right.mp hdisj hq₀
  have hv_no : ∃ r, votes₁ r = .no := ⟨q₀, by simp [votes₁, hq₀_not]⟩
  have hview : GroupViewEq G₁ (cutCfg G₁ G₂ (π.initConfig (fun _ => .yes)))
      (cutCfg G₁ G₂ (π.initConfig votes₁)) := by
    refine ⟨fun p hp => ?_, rfl⟩
    simp [cutCfg, initConfig, votes₁, hp]
  obtain ⟨cfg₁', hsteps₁', heq'⟩ := groupSteps_congr hsteps₁ hview
  have hcut_tr : (π.lts G₁ G₂).Tr (π.start votes₁) .cutPartition
      ⟨true, cutCfg G₁ G₂ (π.initConfig votes₁)⟩ := ⟨rfl, rfl⟩
  have hreach : (π.lts G₁ G₂).CanReach (π.start votes₁) ⟨true, cfg₁'⟩ :=
    partition_canReach_trans ⟨[.cutPartition], LTS.MTr.single _ hcut_tr⟩
      (canReach_of_groupSteps (G₁ := G₁) (G₂ := G₂) false hsteps₁')
  have hdec₁' : π.configDecision cfg₁' p₁ = some .commit := by
    simpa [configDecision, ← heq'.1 p₁ hp₁] using hdec₁
  exact hres.abortValidity votes₁ ⟨true, cfg₁'⟩ hreach hv_no p₁ hdec₁'

/-- Core split-decision contradiction at the critical single-site step `c_prev →[pStar] c_next`
when `pStar ∉ G₂`: `G₂` sees the same view at `c_next` as at `c_prev` and must decide `.abort`,
while `G₁` can reach `.commit`, contradicting `UniformAgreement` (`AC1`). -/
private theorem contradiction_of_crossing_outside_right {π : CommitProtocol P S M}
    {G₁ G₂ : Finset P} (hG₂ : G₂.Nonempty) (hdisj : Disjoint G₁ G₂)
    (hres : π.IsPartitionCutResilient G₁ G₂)
    {c_prev c_next : CommitConfig P S M} {pStar : P} {recv : Option (CommitEnvelope P M)}
    (hnext_steps : π.NormalSteps (π.initConfig (fun _ => .yes)) c_next)
    (hstep_star : π.ConfigNormalStep pStar recv c_prev c_next)
    (hp_not₂ : pStar ∉ G₂)
    (hn₂ : ¬ CanGroupCommit π G₂ (cutCfg G₁ G₂ c_prev))
    (hnext_can : CanGroupCommit π G₁ (cutCfg G₁ G₂ c_next) ∨
      CanGroupCommit π G₂ (cutCfg G₁ G₂ c_next)) : False := by
  let allYes : P → Vote := fun _ => .yes
  have hview_step := groupViewEq_of_normalStep_outside hp_not₂ hstep_star
  have hview_cut₂ : GroupViewEq G₂ (cutCfg G₁ G₂ c_prev) (cutCfg G₁ G₂ c_next) := by
    have hc₁ := groupViewEq_cutCfg_right G₁ G₂ hdisj c_prev
    have hc₂ := (groupViewEq_cutCfg_right G₁ G₂ hdisj c_next).symm
    exact ⟨fun q hq => (hc₁.1 q hq).trans ((hview_step.1 q hq).trans (hc₂.1 q hq)),
      hc₁.2.trans (hview_step.2.trans hc₂.2)⟩
  have hn₂_next : ¬ CanGroupCommit π G₂ (cutCfg G₁ G₂ c_next) :=
    fun hc => hn₂ (canGroupCommit_of_viewEq hview_cut₂.symm hc)
  have hcan₁_next : CanGroupCommit π G₁ (cutCfg G₁ G₂ c_next) :=
    hnext_can.resolve_right hn₂_next
  rcases hcan₁_next with ⟨cfg₁, hsteps₁, u₁, hu₁, hcommit₁⟩
  obtain ⟨_, ⟨cfg₂, hsteps₂, hterm₂⟩⟩ := hres.nonblockingPartition allYes c_next hnext_steps
  obtain ⟨u₂, hu₂⟩ := hG₂
  obtain ⟨d₂, hd₂⟩ := Option.isSome_iff_exists.mp (hterm₂ u₂ hu₂)
  obtain rfl : d₂ = .abort := by
    cases d₂ <;> first | rfl | exact (hn₂_next ⟨cfg₂, hsteps₂, u₂, hu₂, hd₂⟩).elim
  have hpres₂ : GroupViewEq G₂ (cutCfg G₁ G₂ c_next) cfg₁ :=
    groupSteps_preserve_outside hdisj hsteps₁
  obtain ⟨cfg₁₂, hsteps₂', heq₂'⟩ := groupSteps_congr hsteps₂ hpres₂
  have hpres₁ : GroupViewEq G₁ cfg₁ cfg₁₂ :=
    groupSteps_preserve_outside hdisj.symm hsteps₂'
  have hcut_tr : (π.lts G₁ G₂).Tr ⟨false, c_next⟩ .cutPartition
      ⟨true, cutCfg G₁ G₂ c_next⟩ := ⟨rfl, rfl⟩
  have hreach₁₂ : (π.lts G₁ G₂).CanReach (π.start allYes) ⟨true, cfg₁₂⟩ :=
    partition_canReach_trans (canReach_of_normalSteps hnext_steps)
      (partition_canReach_trans ⟨[.cutPartition], LTS.MTr.single _ hcut_tr⟩
        (partition_canReach_trans
          (canReach_of_groupSteps (G₁ := G₁) (G₂ := G₂) false hsteps₁)
          (canReach_of_groupSteps (G₁ := G₁) (G₂ := G₂) true hsteps₂')))
  have hdec_u₁ : π.configDecision cfg₁₂ u₁ = some .commit := by
    simpa [configDecision, ← hpres₁.1 u₁ hu₁] using hcommit₁
  have hdec_u₂ : π.configDecision cfg₁₂ u₂ = some .abort := by
    simpa [configDecision, ← heq₂'.1 u₂ hu₂] using hd₂
  have := hres.agreement allYes ⟨true, cfg₁₂⟩ hreach₁₂ u₁ u₂ .commit .abort hdec_u₁ hdec_u₂
  cases this

end CommitProtocol

/-- Partition-cut step after [SkeenStonebraker1983], §V-A, Theorem 4 (p. 225) and Appendix Proof
of Theorem 4 (p. 227), not the cited crash-recovery endpoint (#7289): for any nonempty disjoint
groups `(G₁, G₂)`, no `CommitProtocol` (with cross-group message erasure `cutCfg` and without
crash-recovery states) satisfies `CommitProtocol.IsPartitionCutResilient G₁ G₂`. -/
theorem not_nonblocking_atomicCommit_of_partitionCut {P S M : Type*} [DecidableEq P] [DecidableEq M]
    {G₁ G₂ : Finset P} (hG₁ : G₁.Nonempty) (hG₂ : G₂.Nonempty) (hdisj : Disjoint G₁ G₂)
    (π : CommitProtocol P S M) :
    ¬ π.IsPartitionCutResilient G₁ G₂ := by
  intro hres
  let allYes : P → Vote := fun _ => .yes
  -- Step 1: At `initConfig allYes`, neither `G₁` nor `G₂` can reach `.commit` in isolation, by
  -- indistinguishability from an input where the opposite nonempty group voted `.no` (`AC2`).
  have hno_commit_init₁ : ¬ CommitProtocol.CanGroupCommit π G₁
      (cutCfg G₁ G₂ (π.initConfig allYes)) :=
    CommitProtocol.not_canGroupCommit_init_left hG₂ hdisj hres
  have hno_commit_init₂ : ¬ CommitProtocol.CanGroupCommit π G₂
      (cutCfg G₁ G₂ (π.initConfig allYes)) := by
    rw [cutCfg_comm G₁ G₂]
    exact CommitProtocol.not_canGroupCommit_init_left hG₁ hdisj.symm hres.symm
  -- Step 2: Walk the partition-free all-`.yes` commit execution (`AC3`) to find an adjacent
  -- single-site transition `c_prev →[p*] c_next` crossing from both-abort-only to some-can-commit.
  obtain ⟨cfg_m, hnorm_m, hcommit_m⟩ := hres.failureFreeCommit
  have ⟨u₁, hu₁⟩ := hG₁
  have hcan_m : CommitProtocol.CanGroupCommit π G₁ (cutCfg G₁ G₂ cfg_m) ∨
      CommitProtocol.CanGroupCommit π G₂ (cutCfg G₁ G₂ cfg_m) :=
    Or.inl ⟨cutCfg G₁ G₂ cfg_m, .refl _, u₁, hu₁, hcommit_m u₁⟩
  clear hcommit_m
  induction hnorm_m with
  | refl => exact hcan_m.elim hno_commit_init₁ hno_commit_init₂
  | @tail c_prev c_next pStar recv hprev hstep ih =>
    obtain ⟨hn₁, hn₂⟩ := not_or.mp ih
    have hnext_steps : π.NormalSteps (π.initConfig allYes) c_next := .tail hprev hstep
    -- Step 3: Because `Disjoint G₁ G₂`, `pStar ∉ G₂` or `pStar ∉ G₁`; apply the crossing lemma
    -- directly or symmetrically via `hres.symm`.
    by_cases hp₂ : pStar ∈ G₂
    · have hp_not₁ : pStar ∉ G₁ := Finset.disjoint_right.mp hdisj hp₂
      rw [cutCfg_comm G₁ G₂] at hn₁ hcan_m
      exact CommitProtocol.contradiction_of_crossing_outside_right hG₁ hdisj.symm hres.symm
        hnext_steps hstep hp_not₁ hn₁ hcan_m.symm
    · exact CommitProtocol.contradiction_of_crossing_outside_right hG₂ hdisj hres
        hnext_steps hstep hp₂ hn₂ hcan_m

/-- Partition-cut step after [SkeenStonebraker1983], §V-A, Theorem 4 (p. 225), not the cited
crash-recovery endpoint (#7289): on any process set with `2 ≤ Fintype.card P`, there exists a
simple two-way partition `(G₁, G₂)` (`G₁.Nonempty`, `G₂.Nonempty`, `Disjoint G₁ G₂`,
`G₁ ∪ G₂ = Finset.univ`), so no `CommitProtocol` satisfies `CommitProtocol.IsPartitionCutResilient`
across all simple two-way partitions. -/
theorem not_exists_partitionCutResilient_atomicCommit {P S M : Type*} [DecidableEq P]
    [DecidableEq M] [Fintype P] (hcard : 2 ≤ Fintype.card P) (π : CommitProtocol P S M) :
    ¬ (∀ G₁ G₂ : Finset P, G₁.Nonempty → G₂.Nonempty → Disjoint G₁ G₂ →
        G₁ ∪ G₂ = Finset.univ → π.IsPartitionCutResilient G₁ G₂) := by
  intro hall
  have hnt : Nontrivial P := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨p, q, hpq⟩ := hnt
  let G₁ : Finset P := {p}
  let G₂ : Finset P := Finset.univ.erase p
  have hG₁ : G₁.Nonempty := Finset.singleton_nonempty p
  have hG₂ : G₂.Nonempty := ⟨q, Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩⟩
  have hdisj : Disjoint G₁ G₂ := Finset.disjoint_singleton_left.mpr (Finset.notMem_erase p _)
  have hunion : G₁ ∪ G₂ = Finset.univ := by
    ext r; by_cases hrp : r = p <;> simp [G₁, G₂, hrp]
  exact not_nonblocking_atomicCommit_of_partitionCut hG₁ hG₂ hdisj π
    (hall G₁ G₂ hG₁ hG₂ hdisj hunion)

end Cslib.Distributed.AtomicCommit
