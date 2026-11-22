/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.MutualExclusion.Bakery
import CslibFrontier.Computability.Distributed.MutualExclusion.FilterLock

/-!
# Shared-Memory Mutual Exclusion Client Tests

Checked `module` client exercising `Cslib.Distributed.MutualExclusion` across three concrete
scenarios on `Fin 3`:
1. **Lamport's Bakery algorithm over safe registers:** concrete contention trace where overlapping
   safe reads during mid-writes and transient failure return the wild garbage value `999`, checking
   `bakery_mutualExclusion`, `bakery_cs_lt`, `bakery_doorway_lt`, `bakery_fcfs`, and
   `bakery_starvationFree`.
2. **Peterson's bounded-state `3`-process filter lock:** 3-thread contention trace driving threads
   `0, 1, 2` through waiting rooms `0` and `1`, verifying the level-capacity bounds `≤ 3, ≤ 2, ≤ 1`
   (`card_at_level_le`), `filterLock_mutualExclusion`, `filterLock_step_progress`, and
   `filterLock_exists_cs_execution`.
3. **Single-register `turn`-variable protocol failure & impossibility:** concrete covering-write
   execution putting two `Fin 3` processes into `.cs` simultaneously on 1 register, alongside
   instantiations of `not_deadlockFreeMutex_of_single_register`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Distributed.MutualExclusion

open Cslib
open Cslib.Distributed.MutualExclusion

/-! ## 1. Lamport's Bakery algorithm with wild garbage safe reads (`999`) -/

private def bakeryGarbageTrace : List (BakeryAction (Fin 3)) :=
  [ -- Thread 0 scans all 3 tickets and pauses mid-write on `number[0] := 1`:
    .enterDoorway 0, .finishChoosingTrue 0,
    .readTicket 0 0 0, .readTicket 0 1 0, .readTicket 0 2 0,
    .beginWriteNumber 0,
    -- While 0 is mid-write (`isWritingNumber 0 = true`), thread 1's overlapping safe read of
    -- `number[0]` nondeterministically observes the garbage value `999` and picks ticket `1000`:
    .enterDoorway 1, .finishChoosingTrue 1,
    .readTicket 1 0 999, .readTicket 1 1 0, .readTicket 1 2 0,
    .beginWriteNumber 1, .finishWriteNumber 1, .finishChoosingFalse 1,
    -- Thread 0 finishes writing `number[0] := 1` and `choosing[0] := false`:
    .finishWriteNumber 0, .finishChoosingFalse 0,
    -- Thread 1 polls `choosing[0] = false` and `number[0] = 1`, spinning at `L3`:
    .pollChoosing 1 false, .pollNumber 1 1,
    -- Thread 2 enters the doorway and crashes into `.failed`; thread 0's overlapping safe read of
    -- `number[2]` returns garbage `999` as well, and thread 0 enters `CS` safely:
    .enterDoorway 2, .fail 2,
    .pollChoosing 0 false, .pollNumber 0 1,
    .pollChoosing 0 false, .pollNumber 0 1000,
    .pollChoosing 0 false, .pollNumber 0 999 ]

private theorem bakeryGarbageTrace_isSome :
    (bakeryStepTrace? (BakeryState.init (Fin 3)) bakeryGarbageTrace).isSome = true := by
  decide

private def bakeryGarbageState : BakeryState (Fin 3) :=
  (bakeryStepTrace? (BakeryState.init (Fin 3)) bakeryGarbageTrace).get bakeryGarbageTrace_isSome

private theorem bakeryGarbageState_reachable : bakeryGarbageState.Reachable := by
  have hsome :
      bakeryStepTrace? (BakeryState.init (Fin 3)) bakeryGarbageTrace = some bakeryGarbageState :=
    Option.some_get bakeryGarbageTrace_isSome |>.symm
  exact BakeryState.Reachable.init.mTr (bakeryStepTrace?_eq_some_iff.mp hsome)

example :
    bakeryGarbageState.inCS 0 ∧
      bakeryGarbageState.inWaiting 1 ∧
      ¬ bakeryGarbageState.inCS 1 ∧
      ¬ bakeryGarbageState.inCS 2 ∧
      bakeryGarbageState.number 0 = 1 ∧
      bakeryGarbageState.number 1 = 1000 := by
  decide

example (q : Fin 3) (hq : bakeryGarbageState.inCS q) : q = 0 :=
  bakery_mutualExclusion bakeryGarbageState_reachable hq (by decide : bakeryGarbageState.inCS 0)

example : bakeryGarbageState.ticket 0 < bakeryGarbageState.ticket 1 :=
  bakery_cs_lt bakeryGarbageState_reachable
    (by decide : bakeryGarbageState.inCS 0)
    (BakeryState.inBakery_of_inWaiting (by decide : bakeryGarbageState.inWaiting 1))
    (by decide)

/-- Computable state-list builder for finite `bakeryLTS` executions. -/
private def bakeryExecStates (s : BakeryState (Fin 3)) :
    List (BakeryAction (Fin 3)) → Option (BakeryState (Fin 3) × List (BakeryState (Fin 3)))
  | [] => some (s, [s])
  | μ :: μs =>
    (bakeryStep? s μ).bind fun s' =>
      (bakeryExecStates s' μs).map fun (t, sl) => (t, s :: sl)

private theorem bakeryExecution_of_execStates {s t : BakeryState (Fin 3)}
    {μs : List (BakeryAction (Fin 3))} {sl : List (BakeryState (Fin 3))}
    (h : bakeryExecStates s μs = some (t, sl)) :
    (bakeryLTS (Fin 3)).Execution s μs t sl := by
  induction μs generalizing s sl with
  | nil =>
    simp only [bakeryExecStates, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact .refl s
  | cons μ μs ih =>
    simp only [bakeryExecStates, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨s', htr, ⟨t', sl'⟩, hex', heq⟩ := h
    injection heq with ht hsl
    subst ht; subst hsl
    exact .stepL htr (ih hex')

/-- Prefix where thread `1` finishes its doorway before thread `0` leaves `.remainder`. -/
private def fcfsDoorwayPrefix : List (BakeryAction (Fin 3)) :=
  [ .enterDoorway 1, .finishChoosingTrue 1,
    .readTicket 1 0 0, .readTicket 1 1 0, .readTicket 1 2 0,
    .beginWriteNumber 1, .finishWriteNumber 1, .finishChoosingFalse 1 ]

/-- Subsequent trace where thread `0` enters and completes its doorway after `1` is waiting. -/
private def fcfsLateArrival : List (BakeryAction (Fin 3)) :=
  [ .enterDoorway 0, .finishChoosingTrue 0,
    .readTicket 0 0 0, .readTicket 0 1 1, .readTicket 0 2 0,
    .beginWriteNumber 0, .finishWriteNumber 0, .finishChoosingFalse 0 ]

private theorem fcfs_s₁_isSome :
    (bakeryStepTrace? (BakeryState.init (Fin 3)) fcfsDoorwayPrefix).isSome = true := by
  decide

private def fcfs_s₁ : BakeryState (Fin 3) :=
  (bakeryStepTrace? (BakeryState.init (Fin 3)) fcfsDoorwayPrefix).get fcfs_s₁_isSome

private theorem fcfs_s₁_reachable : fcfs_s₁.Reachable :=
  BakeryState.Reachable.init.mTr
    (bakeryStepTrace?_eq_some_iff.mp (Option.some_get fcfs_s₁_isSome).symm)

private theorem fcfs_exec_isSome :
    (bakeryExecStates fcfs_s₁ fcfsLateArrival).isSome = true := by
  decide

private def fcfs_res : BakeryState (Fin 3) × List (BakeryState (Fin 3)) :=
  (bakeryExecStates fcfs_s₁ fcfsLateArrival).get fcfs_exec_isSome

private theorem fcfs_execution :
    (bakeryLTS (Fin 3)).Execution fcfs_s₁ fcfsLateArrival fcfs_res.1 fcfs_res.2 :=
  bakeryExecution_of_execStates (Option.some_get fcfs_exec_isSome).symm

-- Check Doorway Ordering (`bakery_doorway_lt`) and FCFS (`bakery_fcfs`): even though `0 < 1` as
-- process IDs, `1` completed its doorway first, so `ticket 1 < ticket 0` and `0` cannot enter CS!
example : fcfs_res.1.ticket 1 < fcfs_res.1.ticket 0 ∧ ¬ fcfs_res.1.inCS 0 :=
  ⟨bakery_doorway_lt fcfs_execution
      (by decide : ∀ s ∈ fcfs_res.2, s.inBakery 1)
      (by decide : fcfs_s₁.beforeDoorwayScan 0)
      (by decide : fcfs_res.1.inBakery 0),
    bakery_fcfs fcfs_s₁_reachable fcfs_execution
      (by decide : ∀ s ∈ fcfs_res.2, s.inWaiting 1)
      (by decide : fcfs_s₁.beforeDoorwayScan 0)⟩

-- Instantiate `bakery_starvationFree` on `Fin 3`.
example (ss : ωSequence (BakeryState (Fin 3))) (μs : ωSequence (BakeryAction (Fin 3)))
    (hr : (ss 0).Reachable) (hex : (bakeryLTS (Fin 3)).OmegaExecution ss μs)
    (hfair : BakeryState.WeakFair ss μs) (hbound : BakeryAction.NoFailAfter μs 0)
    (htry : (ss 0).isTrying 2) : ∃ k, (ss k).inCS 2 :=
  bakery_starvationFree hr hex hfair hbound (fun k => hbound k (Nat.zero_le k) 2) htry

/-! ## 2. Peterson's `3`-process Filter Lock contention trace (`≤ 3, ≤ 2, ≤ 1`) -/

private def filterRoom0Trace : List (FilterAction 3) :=
  [ .requestCS 0, .setLevel 0, .setVictim 0,
    .requestCS 1, .setLevel 1, .setVictim 1,
    .requestCS 2, .setLevel 2, .setVictim 2,
    .checkVictim 0, .checkVictim 1, .checkVictim 2 ]

private def filterRoom1Trace : List (FilterAction 3) :=
  [ .setLevel 0, .setVictim 0,
    .setLevel 1, .setVictim 1,
    .checkVictim 0, .checkVictim 1 ]

private def filterHandoffTrace : List (FilterAction 3) :=
  [ .exitCS 0, .checkLevel 1 0, .checkLevel 1 2 ]

private theorem filterStage1_isSome :
    (filterStepTrace? (FilterState.init 3) filterRoom0Trace).isSome = true := by
  decide

private def filterStage1 : FilterState 3 :=
  (filterStepTrace? (FilterState.init 3) filterRoom0Trace).get filterStage1_isSome

private theorem filterStage1_reachable : filterStage1.Reachable :=
  FilterState.Reachable.init.mTr
    (filterStepTrace?_eq_some_iff.mp (Option.some_get filterStage1_isSome).symm)

private theorem filterStage2_isSome :
    (filterStepTrace? filterStage1 filterRoom1Trace).isSome = true := by
  decide

private def filterStage2 : FilterState 3 :=
  (filterStepTrace? filterStage1 filterRoom1Trace).get filterStage2_isSome

private theorem filterStage2_reachable : filterStage2.Reachable :=
  filterStage1_reachable.mTr
    (filterStepTrace?_eq_some_iff.mp (Option.some_get filterStage2_isSome).symm)

private theorem filterStage3_isSome :
    (filterStepTrace? filterStage2 filterHandoffTrace).isSome = true := by
  decide

private def filterStage3 : FilterState 3 :=
  (filterStepTrace? filterStage2 filterHandoffTrace).get filterStage3_isSome

-- Concrete `decide` verification of level capacities `3 ≤ 3, 2 ≤ 2, 1 ≤ 1` and handoff into CS:
example :
    (filterStage1.atLevel 0).card = 3 ∧
      (filterStage1.atLevel 1).card = 2 ∧
      (filterStage1.atLevel 2).card = 0 ∧
      (filterStage2.atLevel 0).card = 3 ∧
      (filterStage2.atLevel 1).card = 2 ∧
      (filterStage2.atLevel 2).card = 1 ∧
      filterStage2.inCS 0 ∧
      ¬ filterStage2.inCS 1 ∧
      ¬ filterStage2.inCS 2 ∧
      filterStage3.inCS 1 := by
  decide

-- Theorem-level checks on `filterStage1` and `filterStage2`:
example :
    (filterStage2.atLevel 0).card ≤ 3 ∧
      (filterStage2.atLevel 1).card ≤ 2 ∧
      (filterStage2.atLevel 2).card ≤ 1 :=
  ⟨card_at_level_le filterStage2_reachable 0 (by decide),
    card_at_level_le filterStage2_reachable 1 (by decide),
    card_at_level_le filterStage2_reachable 2 (by decide)⟩

example (p : Fin 3) (hp : p ∈ filterStage2.atLevel 2) : 2 ≤ (filterStage2.level p).val :=
  atLevel_level_ge filterStage2_reachable hp

example (q : Fin 3) (hq : filterStage2.inCS q) : q = 0 :=
  filterLock_mutualExclusion filterStage2_reachable hq (by decide : filterStage2.inCS 0)

example :
    ∃ μ s', filterStage1.isTrying μ.actor ∧ (filterLock 3).Tr filterStage1 μ s' ∧
      filterStage1.potential < s'.potential :=
  filterLock_step_progress filterStage1_reachable
    ⟨0, by decide⟩ (by decide : ∀ p, ¬ filterStage1.inCS p)

example :
    ∃ μs s', (filterLock 3).MTr filterStage1 μs s' ∧
      (∀ μ ∈ μs, ∀ p, μ ≠ .requestCS p ∧ μ ≠ .exitCS p) ∧
      (∃ p, s'.inCS p) :=
  filterLock_exists_cs_execution filterStage1_reachable ⟨0, by decide⟩

/-! ## 3. Single-register `turn`-variable protocol failure trace & impossibility -/

private inductive TurnLocal where
  | rem
  | checkFree
  | writeTurn
  | confirmTurn
  | inCS
  | releaseTurn
  deriving @[expose] DecidableEq

/-- Classic naïve 1-register `turn` protocol on `Fin 3`: check `turn == none`, write
`turn := some p`, re-read `turn == some p`, and enter `CS`. -/
private def singleTurnProtocol : MutexProtocol (Fin 3) Unit (Option (Fin 3)) TurnLocal where
  initMem _ := none
  initLocal _ := .rem
  sectionOf _
    | .rem => .remainder
    | .checkFree | .writeTurn | .confirmTurn => .trying
    | .inCS => .cs
    | .releaseTurn => .exit
  enterTrying _ _ := .checkFree
  exitCS _ _ := .releaseTurn
  step p
    | .rem => .localStep .rem
    | .checkFree => .read () fun v => if v.isNone then .writeTurn else .checkFree
    | .writeTurn => .write () (some p) .confirmTurn
    | .confirmTurn => .read () fun v => if v = some p then .inCS else .checkFree
    | .inCS => .localStep .inCS
    | .releaseTurn => .write () none .rem
  init_remainder _ := rfl
  enterTrying_section _ _ _ := Or.inl rfl
  trying_step_section p st hst st' hnext := by
    cases st <;> simp only [reduceCtorEq] at hst <;> dsimp only [RegStep.NextState] at hnext
    · obtain ⟨v, rfl⟩ := hnext
      cases v <;> simp
    · subst hnext; exact Or.inl rfl
    · obtain ⟨v, rfl⟩ := hnext
      by_cases h : v = some p <;> simp [h]

/-- Covering-write trace: `0` reads `turn = none` and pauses poised to write `some 0`; `1` runs solo
into `CS`; `0`'s covering write overwrites `some 1` with `some 0`, letting `0` enter `CS` too! -/
private def turnFailureTrace : List (MutexAction (Fin 3)) :=
  [ .enter 0, .step 0,
    .enter 1, .step 1, .step 1, .step 1,
    .step 0, .step 0 ]

private theorem turnFailure_isSome :
    (singleTurnProtocol.stepTrace? singleTurnProtocol.initConfig turnFailureTrace).isSome = true :=
  by decide

private def turnFailureConfig : MutexConfig (Fin 3) Unit (Option (Fin 3)) TurnLocal :=
  (singleTurnProtocol.stepTrace? singleTurnProtocol.initConfig turnFailureTrace).get
    turnFailure_isSome

private theorem turnFailureConfig_reachable : singleTurnProtocol.Reachable turnFailureConfig :=
  (MutexProtocol.Reachable.init singleTurnProtocol).mTr
    ((singleTurnProtocol.stepTrace?_eq_some_iff).mp (Option.some_get turnFailure_isSome).symm)

-- Concrete `decide` check: both `0` and `1` are simultaneously in `CS`!
example :
    turnFailureConfig.inCS singleTurnProtocol 0 ∧
      turnFailureConfig.inCS singleTurnProtocol 1 := by
  decide

example : ¬ singleTurnProtocol.MutuallyExclusive := fun hme =>
  absurd
    (hme turnFailureConfig turnFailureConfig_reachable 0 1 (by decide) (by decide))
    (by decide)

-- General 1-register impossibility instantiated on `Fin 3` (`Unit`) and `Fin 2` (`Empty` / `Unit`):
example : ¬ singleTurnProtocol.DeadlockFreeMutex :=
  not_deadlockFreeMutex_of_single_register (by decide) (by decide) singleTurnProtocol

example {Val State : Type*} [DecidableEq Val]
    (π : MutexProtocol (Fin 2) Unit Val State) : ¬ π.DeadlockFreeMutex :=
  not_deadlockFreeMutex_of_single_register (by decide) (by decide) π

end CslibFrontierTests.Computability.Distributed.MutualExclusion
