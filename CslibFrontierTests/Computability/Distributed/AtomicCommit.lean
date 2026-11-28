/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.AtomicCommit.ThreePhaseCommit

/-! Distributed atomic commitment step modules (`TwoPhaseCommit` and `ThreePhaseCommit`), checked
as a `module` client with ordinary imports:
1. `decide`-checked fail-stop `2PC` executions on `Fin 3` (all-`yes` commit, unilateral cohort-`no`
   abort, and 3-site coordinator-plus-cohort crash blocking witness with identical
   `TwoPCSurvivorView` on surviving `.uncertain` site `2`), plus an instantiation of
   `twoPC_no_safe_survivor_termination_failStop`.
2. `decide`-checked global-phase `3PC` executions on `Fin 3` (fault-free 3-phase commit, backup
   failover to `.abort` when primary `0` crashes in `.preCommitted` leaving `{1, 2}` in
   `.uncertain`, backup failover to `.commit` via the 2-step `PreCommit → Commit` round on mixed
   `.preCommitted`/`.uncertain` survivors, and recursive backup coordinator crash mid-failover),
   plus instantiations of `threePC_no_uncertain_and_committed_globalPhase`,
   `threePC_agreement_globalPhase`, and `threePC_nonblocking_termination_globalPhase`.
3. Concrete `Fin 3` split-brain failure when `3PC`'s fail-stop termination rule is invoked on two
   separate `.crash` branches modeling a false partition `({0, 1}, {2})`, plus instantiations of
   `IsPartitionCutResilient.symm`, `not_nonblocking_atomicCommit_of_partitionCut`, and
   `not_exists_partitionCutResilient_atomicCommit`. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.AtomicCommit

open Cslib Cslib.Distributed.AtomicCommit

/-! ### Local partial-step trace helpers for `decide` checks -/

private def execValid {State Label : Type*} (step? : State → Label → Option State) :
    State → List Label → Bool
  | _, [] => true
  | s, a :: as =>
    match step? s a with
    | some s' => execValid step? s' as
    | none => false

private def execState {State Label : Type*} (step? : State → Label → Option State) :
    State → List Label → State
  | s, [] => s
  | s, a :: as =>
    match step? s a with
    | some s' => execState step? s' as
    | none => s

private theorem mTr_execState_of_execValid {State Label : Type*}
    {step? : State → Label → Option State} {s : State} {tr : List Label}
    (hv : execValid step? s tr = true) :
    ({ Tr := fun s a s' => step? s a = some s' } : LTS State Label).MTr s tr
      (execState step? s tr) := by
  induction tr generalizing s with
  | nil => exact .refl
  | cons a as ih =>
    simp only [execValid, execState] at hv ⊢
    cases hstep : step? s a with
    | none => simp [hstep] at hv
    | some s' =>
      simp only [hstep] at hv
      exact .stepL hstep (ih hv)

private theorem canReach_execState_of_execValid {State Label : Type*}
    {step? : State → Label → Option State} {s : State} {tr : List Label}
    (hv : execValid step? s tr = true) :
    ({ Tr := fun s a s' => step? s a = some s' } : LTS State Label).CanReach s
      (execState step? s tr) :=
  ⟨tr, mTr_execState_of_execValid hv⟩

/-! ### 1. Fail-stop Two-Phase Commit (`2PC`) step on `Fin 3` -/

private def allYes3 : Fin 3 → Vote := fun _ => .yes

private def cohort1No : Fin 3 → Vote
  | 1 => .no
  | _ => .yes

private def tr2PCCommit : List (TwoPCAction (Fin 3)) :=
  [ .sendRequests,
    .recvRequest 1, .recvRequest 2,
    .recvVote 1 .yes, .recvVote 2 .yes,
    .coordCommit,
    .recvVerdict 1 .commit, .recvVerdict 2 .commit ]

example :
    let s := execState (twoPCStep? (0 : Fin 3) allYes3) (twoPCStart (Fin 3)) tr2PCCommit
    execValid (twoPCStep? (0 : Fin 3) allYes3) (twoPCStart (Fin 3)) tr2PCCommit = true ∧
    (tr2PCCommit.all TwoPCAction.isFaultFree) = true ∧
    TwoPCReachable (0 : Fin 3) allYes3 s ∧
    AllDecided s.decision .commit ∧
    s.alive = Finset.univ ∧
    s.msgs = 0 ∧
    UniformAgreement s.decision := by
  intro s
  have hv : execValid (twoPCStep? (0 : Fin 3) allYes3) (twoPCStart (Fin 3)) tr2PCCommit = true := by
    decide
  have hreach : TwoPCReachable (0 : Fin 3) allYes3 s := canReach_execState_of_execValid hv
  exact ⟨hv, by decide, hreach, by decide, by decide, by decide, twoPC_agreement_failStop hreach⟩

private def tr2PCAbort : List (TwoPCAction (Fin 3)) :=
  [ .sendRequests,
    .recvRequest 1, .recvRequest 2,
    .recvVote 1 .no,
    .coordAbort,
    .recvVerdict 2 .abort ]

example :
    let s := execState (twoPCStep? (0 : Fin 3) cohort1No) (twoPCStart (Fin 3)) tr2PCAbort
    execValid (twoPCStep? (0 : Fin 3) cohort1No) (twoPCStart (Fin 3)) tr2PCAbort = true ∧
    TwoPCReachable (0 : Fin 3) cohort1No s ∧
    AllDecided s.decision .abort ∧
    AbortValidity cohort1No s.decision := by
  intro s
  have hv :
      execValid (twoPCStep? (0 : Fin 3) cohort1No) (twoPCStart (Fin 3)) tr2PCAbort = true := by
    decide
  have hreach : TwoPCReachable (0 : Fin 3) cohort1No s := canReach_execState_of_execValid hv
  exact ⟨hv, hreach, by decide, twoPC_abort_of_vote_no_failStop hreach⟩

-- 3-site fail-stop `2PC` blocking witness (after [Skeen1981], §1, p. 134): coordinator `0` votes
-- `.yes` in both runs; cohort `2` votes `.yes` and survives alone in `.uncertain` with an empty
-- network; in `tr2PCBlockCohortNo` crashed cohort `1` voted `.no` and unilaterally aborted, whereas
-- in `tr2PCBlockCommit` crashed sites `0` and `1` both already decided `.commit`.
private def tr2PCBlockCohortNo : List (TwoPCAction (Fin 3)) :=
  [ .sendRequests,
    .recvRequest 1, .recvRequest 2,
    .dropMsg (.voteReply 1 .no), .dropMsg (.voteReply 2 .yes),
    .crash 0, .crash 1 ]

private def tr2PCBlockCommit : List (TwoPCAction (Fin 3)) :=
  [ .sendRequests,
    .recvRequest 1, .recvRequest 2,
    .recvVote 1 .yes, .recvVote 2 .yes,
    .coordCommit,
    .recvVerdict 1 .commit,
    .dropMsg (.verdict 2 .commit),
    .crash 0, .crash 1 ]

theorem twoPC_fin3_skeen_blocking_witness :
    let sA := execState (twoPCStep? (0 : Fin 3) cohort1No) (twoPCStart (Fin 3)) tr2PCBlockCohortNo
    let sC := execState (twoPCStep? (0 : Fin 3) allYes3) (twoPCStart (Fin 3)) tr2PCBlockCommit
    cohort1No 0 = .yes ∧
    TwoPCReachable (0 : Fin 3) cohort1No sA ∧
    TwoPCReachable (0 : Fin 3) allYes3 sC ∧
    sA.alive = {2} ∧ sC.alive = {2} ∧
    sA.localState 2 = .uncertain ∧ sC.localState 2 = .uncertain ∧
    sA.decision 1 = some .abort ∧
    sC.decision 0 = some .commit ∧ sC.decision 1 = some .commit ∧
    sA.survivorView 0 cohort1No = sC.survivorView 0 allYes3 := by
  intro sA sC
  have hvA : execValid (twoPCStep? (0 : Fin 3) cohort1No) (twoPCStart (Fin 3))
      tr2PCBlockCohortNo = true := by decide
  have hvC : execValid (twoPCStep? (0 : Fin 3) allYes3) (twoPCStart (Fin 3))
      tr2PCBlockCommit = true := by decide
  refine ⟨rfl, canReach_execState_of_execValid hvA, canReach_execState_of_execValid hvC,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  simp only [TwoPCState.survivorView, TwoPCSurvivorView.mk.injEq]
  refine ⟨by decide, ?_, ?_, by decide⟩
  · funext p; match p with | 0 => decide | 1 => decide | 2 => decide
  · funext p; match p with | 0 => decide | 1 => decide | 2 => decide

example (term : TwoPCSurvivorView (Fin 3) → Decision) :
    ∃ (votes : Fin 3 → Vote) (s : TwoPCState (Fin 3)),
      TwoPCReachable 0 votes s ∧ s.alive.Nonempty ∧
      ¬ UniformAgreement (fun p =>
        match s.decision p with
        | some d => some d
        | none => if p ∈ s.alive then some (term (s.survivorView 0 votes)) else none) :=
  twoPC_no_safe_survivor_termination_failStop (by decide) 0 term

/-! ### 2. Global-phase Three-Phase Commit (`3PC`) step on `Fin 3` -/

private def tr3PCCommit : List (ThreePCAction (Fin 3)) :=
  [ .castVote 0, .castVote 1, .castVote 2,
    .startPreCommit, .stepPreCommit 1, .stepPreCommit 2,
    .finishPreCommit, .stepCommit 1, .stepCommit 2 ]

example :
    let s := execState (threePCStep? allYes3) (threePCStart (Fin 3) 0) tr3PCCommit
    execValid (threePCStep? allYes3) (threePCStart (Fin 3) 0) tr3PCCommit = true ∧
    (tr3PCCommit.all ThreePCAction.isCrashFree) = true ∧
    ThreePCReachable 0 allYes3 s ∧
    AllDecided s.decision .commit ∧
    s.alive = Finset.univ := by
  intro s
  have hv : execValid (threePCStep? allYes3) (threePCStart (Fin 3) 0) tr3PCCommit = true := by
    decide
  exact ⟨hv, by decide, canReach_execState_of_execValid hv, by decide, by decide⟩

-- Failover Case A: Primary `0` enters `.preCommitted` and crashes before delivering `PreCommit` to
-- `{1, 2}`. All operational survivors `{1, 2}` are `.uncertain`, so backup `1` safely aborts
-- `{1, 2}` while crashed `0` stays in `.preCommitted` (`decision = none`), preserving `AC1`.
private def tr3PCCrashAllUncertain : List (ThreePCAction (Fin 3)) :=
  [ .castVote 0, .castVote 1, .castVote 2, .startPreCommit, .crash 0 ]

private def tr3PCFailoverAbort : List (ThreePCAction (Fin 3)) :=
  tr3PCCrashAllUncertain ++ [ .electBackup 1, .stepAbort 1, .stepAbort 2 ]

example :
    let sCrash := execState (threePCStep? allYes3) (threePCStart (Fin 3) 0) tr3PCCrashAllUncertain
    let sDone := execState (threePCStep? allYes3) (threePCStart (Fin 3) 0) tr3PCFailoverAbort
    execValid (threePCStep? allYes3) (threePCStart (Fin 3) 0) tr3PCFailoverAbort = true ∧
    sCrash.localState 0 = .preCommitted ∧
    sCrash.localState 1 = .uncertain ∧ sCrash.localState 2 = .uncertain ∧
    backupPhase sCrash.alive sCrash.localState = .aborting ∧
    (∀ q, sCrash.decision q ≠ some .commit) ∧
    sDone.alive = {1, 2} ∧
    OperationalDecided sDone.alive sDone.decision .abort ∧
    sDone.decision 0 = none ∧
    UniformAgreement sDone.decision ∧
    (∀ p, (threePCTerminate 1 sCrash).localState p = sDone.localState p) := by
  intro sCrash sDone
  have hvCrash : execValid (threePCStep? allYes3) (threePCStart (Fin 3) 0)
      tr3PCCrashAllUncertain = true := by decide
  have hvDone : execValid (threePCStep? allYes3) (threePCStart (Fin 3) 0)
      tr3PCFailoverAbort = true := by decide
  have hrCrash : ThreePCReachable 0 allYes3 sCrash := canReach_execState_of_execValid hvCrash
  have hrDone : ThreePCReachable 0 allYes3 sDone := canReach_execState_of_execValid hvDone
  have hnoCom : ∀ q, sCrash.decision q ≠ some .commit :=
    threePC_no_uncertain_and_committed_globalPhase hrCrash ⟨1, by decide, Or.inr (by decide)⟩
  exact ⟨hvDone, by decide, by decide, by decide, by decide, hnoCom, by decide,
    by decide, by decide, threePC_agreement_globalPhase hrDone, by decide⟩

-- Failover Case B: Primary `0` delivers `PreCommit` to `1` and crashes while `2` is still
-- `.uncertain`. Backup `2` polls `{1, 2}`, sees `1` is `.preCommitted`, and runs the 2-step
-- `PreCommit → Commit` round across `{1, 2}` to reach unanimous `.commit`.
private def tr3PCCrashMixed : List (ThreePCAction (Fin 3)) :=
  [ .castVote 0, .castVote 1, .castVote 2, .startPreCommit, .stepPreCommit 1, .crash 0 ]

private def tr3PCFailoverCommit : List (ThreePCAction (Fin 3)) :=
  tr3PCCrashMixed ++ [ .electBackup 2, .stepPreCommit 2, .finishPreCommit, .stepCommit 1 ]

example :
    let sCrash := execState (threePCStep? allYes3) (threePCStart (Fin 3) 0) tr3PCCrashMixed
    let sDone := execState (threePCStep? allYes3) (threePCStart (Fin 3) 0) tr3PCFailoverCommit
    execValid (threePCStep? allYes3) (threePCStart (Fin 3) 0) tr3PCFailoverCommit = true ∧
    sCrash.localState 1 = .preCommitted ∧ sCrash.localState 2 = .uncertain ∧
    backupPhase sCrash.alive sCrash.localState = .preCommitting ∧
    OperationalDecided sDone.alive sDone.decision .commit ∧
    UniformAgreement sDone.decision ∧
    (∀ p, (threePCTerminate 2 sCrash).localState p = sDone.localState p) := by
  intro sCrash sDone
  have hvDone : execValid (threePCStep? allYes3) (threePCStart (Fin 3) 0)
      tr3PCFailoverCommit = true := by decide
  have hrDone : ThreePCReachable 0 allYes3 sDone := canReach_execState_of_execValid hvDone
  exact ⟨hvDone, by decide, by decide, by decide, by decide,
    threePC_agreement_globalPhase hrDone, by decide⟩

-- Failover Case C: Recursive backup coordinator crash mid-failover (`0` crashes, backup `1`
-- advances `2` to `.preCommitted` and crashes before `finishPreCommit`, then sole survivor `2`
-- elects itself backup and completes `.commit`), plus
-- `threePC_nonblocking_termination_globalPhase`.
private def tr3PCRecursiveBackupCrash : List (ThreePCAction (Fin 3)) :=
  tr3PCCrashMixed ++ [ .electBackup 1, .stepPreCommit 2, .crash 1, .electBackup 2,
    .finishPreCommit ]

example :
    let sMid := execState (threePCStep? allYes3) (threePCStart (Fin 3) 0)
      (tr3PCCrashMixed ++ [ .electBackup 1, .stepPreCommit 2, .crash 1 ])
    let sFinal := execState (threePCStep? allYes3) (threePCStart (Fin 3) 0)
      tr3PCRecursiveBackupCrash
    execValid (threePCStep? allYes3) (threePCStart (Fin 3) 0) tr3PCRecursiveBackupCrash = true ∧
    sFinal.alive = {2} ∧
    sFinal.decision 2 = some .commit ∧
    UniformAgreement sFinal.decision ∧
    ∃ tr s' d, (∀ a ∈ tr, a.isCrashFree = true) ∧ (threePCLts allYes3).MTr sMid tr s' ∧
      s'.alive = sMid.alive ∧ OperationalDecided sMid.alive s'.decision d ∧
      UniformAgreement s'.decision ∧ AbortValidity allYes3 s'.decision := by
  intro sMid sFinal
  have hvMid : execValid (threePCStep? allYes3) (threePCStart (Fin 3) 0)
      (tr3PCCrashMixed ++ [ .electBackup 1, .stepPreCommit 2, .crash 1 ]) = true := by decide
  have hvFinal : execValid (threePCStep? allYes3) (threePCStart (Fin 3) 0)
      tr3PCRecursiveBackupCrash = true := by decide
  have hrMid : ThreePCReachable 0 allYes3 sMid := canReach_execState_of_execValid hvMid
  have hrFinal : ThreePCReachable 0 allYes3 sFinal := canReach_execState_of_execValid hvFinal
  exact ⟨hvFinal, by decide, by decide, threePC_agreement_globalPhase hrFinal,
    threePC_nonblocking_termination_globalPhase hrMid ⟨2, by decide⟩⟩

/-! ### 3. False-partition split-brain witness and partition-cut impossibility step -/

-- Concrete split-brain failure when `3PC`'s fail-stop termination rule is invoked on two separate
-- `.crash` branches modeling a false partition `G₁ = {0, 1}`, `G₂ = {2}` from reachable state
-- `sPre` (`0` and `1` in `.preCommitted`, `2` in `.uncertain`): `{0, 1}` treats `2` as crashed and
-- commits, while `{2}` treats `{0, 1}` as crashed and runs `threePCTerminate 2` to abort.
private def tr3PCPrePartition : List (ThreePCAction (Fin 3)) :=
  [ .castVote 0, .castVote 1, .castVote 2, .startPreCommit, .stepPreCommit 1 ]

private def tr3PCFalseCrashSide1 : List (ThreePCAction (Fin 3)) :=
  tr3PCPrePartition ++ [ .crash 2, .finishPreCommit, .stepCommit 1 ]

private def tr3PCFalseCrashSide2 : List (ThreePCAction (Fin 3)) :=
  tr3PCPrePartition ++ [ .crash 0, .crash 1, .electBackup 2, .stepAbort 2 ]

theorem threePC_split_brain_under_false_partition :
    let sSide1 := execState (threePCStep? allYes3) (threePCStart (Fin 3) 0) tr3PCFalseCrashSide1
    let sSide2 := execState (threePCStep? allYes3) (threePCStart (Fin 3) 0) tr3PCFalseCrashSide2
    let combinedDec : Fin 3 → Option Decision := fun p =>
      if p ∈ ({0, 1} : Finset (Fin 3)) then sSide1.decision p else sSide2.decision p
    execValid (threePCStep? allYes3) (threePCStart (Fin 3) 0) tr3PCFalseCrashSide1 = true ∧
    execValid (threePCStep? allYes3) (threePCStart (Fin 3) 0) tr3PCFalseCrashSide2 = true ∧
    combinedDec 0 = some .commit ∧
    combinedDec 1 = some .commit ∧
    combinedDec 2 = some .abort ∧
    ¬ UniformAgreement combinedDec := by
  intro sSide1 sSide2 combinedDec
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

-- Symmetry of `cutCfg` and `IsPartitionCutResilient`, plus partition-cut impossibility on
-- `Fin 3` (`G₁ = {0, 1}`, `G₂ = {2}`) and `Fin 2`.
example {S M : Type*} (G₁ G₂ : Finset (Fin 3)) (cfg : CommitConfig (Fin 3) S M) :
    cutCfg G₁ G₂ cfg = cutCfg G₂ G₁ cfg :=
  cutCfg_comm G₁ G₂ cfg

example {S M : Type*} [DecidableEq M] {π : CommitProtocol (Fin 3) S M}
    (h : π.IsPartitionCutResilient {0, 1} {2}) : π.IsPartitionCutResilient {2} {0, 1} :=
  h.symm

example {S M : Type*} [DecidableEq M] (π : CommitProtocol (Fin 3) S M) :
    ¬ π.IsPartitionCutResilient {0, 1} {2} :=
  not_nonblocking_atomicCommit_of_partitionCut ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide) π

example {S M : Type*} [DecidableEq M] (π : CommitProtocol (Fin 2) S M) :
    ¬ (∀ G₁ G₂ : Finset (Fin 2), G₁.Nonempty → G₂.Nonempty → Disjoint G₁ G₂ →
        G₁ ∪ G₂ = Finset.univ → π.IsPartitionCutResilient G₁ G₂) :=
  not_exists_partitionCutResilient_atomicCommit (by decide) π

end CslibFrontierTests.Distributed.AtomicCommit
