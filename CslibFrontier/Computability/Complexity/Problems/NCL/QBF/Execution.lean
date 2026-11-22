/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Initial
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Enumeration

/-!
# Local execution protocols of the quantifiers

The quantifiers of [HearnDemaine2005, Figure 7 and Lemma 3, pages 6–7] execute a suffix through
their lower control wires. A ready configuration locks the chosen value, drives its literal
wire, and activates the suffix's try wire. Both directions of the suffix's satisfied wire are
legal in that configuration.

An existential quantifier prepares either value and passes the suffix's satisfied wire through.
A universal quantifier prepares false, records success by internal moves, lets the suffix reset,
changes to true while keeping the record set, and returns success after the second suffix call.
Each phase has an explicit checked list of reversals. Suffix calls and their reset paths are
supplied by the caller; this module proves the local gadget phases used in the chain induction.

## Main definitions

* `Cslib.Complexity.NCL.QBF.ExistsGadget.Execution.idle`,
  `Cslib.Complexity.NCL.QBF.ForallGadget.Execution.idle`: initial orientations after trying in.
* `Cslib.Complexity.NCL.QBF.ExistsGadget.Execution.ready`,
  `Cslib.Complexity.NCL.QBF.ForallGadget.Execution.ready`: locked configurations for suffix calls.
* `Cslib.Complexity.NCL.QBF.ForallGadget.Execution.success`: return after both branches.

## Main results

* `Cslib.Complexity.NCL.QBF.ExistsGadget.Execution.prepare_spec`:
  select either existential value.
* `Cslib.Complexity.NCL.QBF.ForallGadget.Execution.prepare_spec`:
  prepare a value with a clear record.
* `Cslib.Complexity.NCL.QBF.ForallGadget.Execution.record_false`: record the false branch.
* `Cslib.Complexity.NCL.QBF.ForallGadget.Execution.switch_true`: change value with the record set.
* `Cslib.Complexity.NCL.QBF.ForallGadget.Execution.finish`: return the second branch's success.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF

open Diagram Gate

namespace ExistsGadget.Execution

/-- The initial existential orientation with its incoming try wire activated. -/
@[expose]
def idle : Realization Gate.interp existsGadget [true, true] [true, false, false, false] where
  orient := fun e => [0, 1, 6].contains (existsGadget.num e)
  legal := by decide +kernel
  top_eq := by decide +kernel
  bot_eq := by decide +kernel

/-- The selected value is locked and its literal and outgoing try wires are active.
The satisfied wire passes through with direction `sat`. -/
@[expose] def ready (value sat : Bool) :
    Realization Gate.interp existsGadget [sat, true] [sat, true, value, !value] where
  orient := fun e => ([1, 2, 4, 10, 12] ++ (if value then [5, 7, 8] else [6, 9]) ++
    (if sat then [0] else [])).contains (existsGadget.num e)
  legal := by cases value <;> cases sat <;> decide +kernel
  top_eq := by cases value <;> cases sat <;> decide +kernel
  bot_eq := by cases value <;> cases sat <;> decide +kernel

@[simp] theorem ready_mem (value sat : Bool) : (ready value sat).orient mem = value := by
  cases value <;> cases sat <;> decide +kernel

/-- Activate the incoming try wire of the canonical initial configuration. -/
theorem activate : graph.StepOn (· = tryIn) Initial.existsInitial.orient idle.orient :=
  ⟨Initial.existsInitial.legal, idle.legal, tryIn, rfl, by decide +kernel⟩

/-- A suffix response changes exactly the common satisfied wire. -/
theorem ready_sat (value : Bool) :
    (ready value false).orient = reverse (ready value true).orient sat := by
  cases value <;> decide +kernel

private def numbered (n : Fin 13) : existsGadget.Edge := existsGadget.numEquiv.symm n

private def prepareMoves (value : Bool) : List existsGadget.Edge :=
  (if value then [2, 5, 7, 8, 6, 4, 10, 12] else [2, 4, 9, 10, 12]).map numbered

private theorem prepare_checked (value : Bool) :
    graph.Run (fun e => e ≠ sat ∧ e ≠ tryIn) idle.orient (prepareMoves value) ∧
      reverseAll idle.orient (prepareMoves value) = (ready value true).orient := by
  cases value <;> decide +kernel

/-- Select either value while keeping the incoming controls fixed. -/
theorem prepare (value : Bool) :
    graph.ReachableOn (fun e => e ≠ sat ∧ e ≠ tryIn) idle.orient (ready value true).orient := by
  obtain ⟨hrun, hend⟩ := prepare_checked value
  exact hend ▸ hrun.reachableOn

/-- Preparation reaches the requested assignment in the variable latch. -/
theorem prepare_spec (value : Bool) :
    graph.ReachableOn (fun e => e ≠ sat ∧ e ≠ tryIn) idle.orient (ready value true).orient ∧
      (ready value true).orient mem = value :=
  ⟨prepare value, ready_mem value true⟩

end ExistsGadget.Execution

namespace ForallGadget.Execution

/-- The initial universal orientation with its incoming try wire activated and record clear. -/
@[expose]
def idle : Realization Gate.interp forallGadget [true, true] [true, false, false, false] where
  orient := fun e => [0, 1, 2, 4, 7, 11, 26, 30, 31].contains (forallGadget.num e)
  legal := by decide +kernel
  top_eq := by decide +kernel
  bot_eq := by decide +kernel

/-- A locked variable and active suffix try, with the given record and suffix response.
The outer satisfied wire remains inactive. -/
@[expose] def ready (value recorded sat : Bool) :
    Realization Gate.interp forallGadget [true, true] [sat, true, value, !value] where
  orient := fun e => ([0, 1, 8, 9, 15, 17, 26, 30] ++ (if sat then [31] else []) ++
    (if recorded then [2, 3, 5, 6] else [2, 4, 7]) ++
    (if value then [10, 12, 13, 18, 22, 23] else [11, 14, 20, 24, 25])).contains
      (forallGadget.num e)
  legal := by cases value <;> cases recorded <;> cases sat <;> decide +kernel
  top_eq := by cases value <;> cases recorded <;> cases sat <;> decide +kernel
  bot_eq := by cases value <;> cases recorded <;> cases sat <;> decide +kernel

@[simp] theorem ready_mem (value recorded sat : Bool) : (ready value recorded sat).orient mem =
    value := by cases value <;> cases recorded <;> cases sat <;> decide +kernel

@[simp] theorem ready_recMem (value recorded sat : Bool) :
    (ready value recorded sat).orient recMem = recorded := by
  cases value <;> cases recorded <;> cases sat <;> decide +kernel

/-- The universal gadget returning success with its variable true and record set. -/
@[expose]
def success : Realization Gate.interp forallGadget [false, true] [false, true, true, false] where
  orient := fun e => [1, 2, 3, 5, 6, 8, 9, 10, 12, 13, 15, 17, 18, 22, 23, 27, 28, 30].contains
    (forallGadget.num e)
  legal := by decide +kernel
  top_eq := by decide +kernel
  bot_eq := by decide +kernel

/-- Activate the incoming try wire of the canonical initial configuration. -/
theorem activate : graph.StepOn (· = tryIn) Initial.forallInitial.orient idle.orient :=
  ⟨Initial.forallInitial.legal, idle.legal, tryIn, rfl, by decide +kernel⟩

/-- A suffix response changes exactly its satisfied wire at either value and record setting. -/
theorem ready_sat (value recorded : Bool) :
    (ready value recorded false).orient = reverse (ready value recorded true).orient satIn := by
  cases value <;> cases recorded <;> decide +kernel

private def numbered (n : Fin 32) : forallGadget.Edge := forallGadget.numEquiv.symm n

private def prepareMoves (value : Bool) : List forallGadget.Edge :=
  (if value then [8, 10, 12, 13, 11, 9, 15, 17, 18, 22, 23]
    else [8, 9, 14, 15, 17, 20, 24, 25]).map numbered

private theorem prepare_checked (value : Bool) :
    graph.Run (fun e => e ≠ satOut ∧ e ≠ tryIn ∧ e ≠ satIn ∧ e ≠ recMem)
      idle.orient (prepareMoves value) ∧
      reverseAll idle.orient (prepareMoves value) = (ready value false true).orient := by
  cases value <;> decide +kernel

/-- Prepare a value without changing the outer controls, suffix response, or clear record. -/
theorem prepare (value : Bool) :
    graph.ReachableOn (fun e => e ≠ satOut ∧ e ≠ tryIn ∧ e ≠ satIn ∧ e ≠ recMem)
      idle.orient (ready value false true).orient := by
  obtain ⟨hrun, hend⟩ := prepare_checked value
  exact hend ▸ hrun.reachableOn

/-- Preparation reaches the requested variable assignment while keeping the record clear. -/
theorem prepare_spec (value : Bool) :
    graph.ReachableOn (fun e => e ≠ satOut ∧ e ≠ tryIn ∧ e ≠ satIn ∧ e ≠ recMem)
      idle.orient (ready value false true).orient ∧
      (ready value false true).orient mem = value ∧
      (ready value false true).orient recMem = false :=
  ⟨prepare value, ready_mem value false true, ready_recMem value false true⟩

private def recordMoves : List forallGadget.Edge := [7, 30, 2, 3, 5, 6, 4, 2, 30].map numbered

private theorem record_checked : InnerRun Gate.interp forallGadget
    (ready false false false).orient recordMoves ∧
      reverseAll (ready false false false).orient recordMoves = (ready false true false).orient :=
  by decide +kernel

/-- Record success with the variable false, keeping every boundary direction fixed. -/
theorem record_false : InnerReach Gate.interp forallGadget
    (ready false false false).orient (ready false true false).orient := by
  obtain ⟨hrun, hend⟩ := record_checked
  exact hend ▸ hrun.innerReach

private def switchMoves : List forallGadget.Edge :=
  [17, 15, 9, 10, 12, 13, 18, 22, 23, 24, 25, 20, 14, 11, 9, 15, 17].map numbered

private theorem switch_checked :
    graph.Run (fun e => e ≠ satOut ∧ e ≠ tryIn ∧ e ≠ satIn ∧ e ≠ recMem)
      (ready false true true).orient switchMoves ∧
      reverseAll (ready false true true).orient switchMoves = (ready true true true).orient :=
  by decide +kernel

/-- After the suffix resets, change to true while keeping the false-branch record set. -/
theorem switch_true :
    graph.ReachableOn (fun e => e ≠ satOut ∧ e ≠ tryIn ∧ e ≠ satIn ∧ e ≠ recMem)
      (ready false true true).orient (ready true true true).orient := by
  obtain ⟨hrun, hend⟩ := switch_checked
  exact hend ▸ hrun.reachableOn

private def finishMoves : List forallGadget.Edge := [26, 27, 28, 0].map numbered

private theorem finish_checked :
    graph.Run (fun e => e ≠ tryIn ∧ ∀ j, e ≠ forallGadget.bottom j)
      (ready true true false).orient finishMoves ∧
      reverseAll (ready true true false).orient finishMoves = success.orient := by decide +kernel

/-- Return the true branch's success, keeping try-in and every suffix boundary wire fixed. -/
theorem finish : graph.ReachableOn (fun e => e ≠ tryIn ∧ ∀ j, e ≠ forallGadget.bottom j)
    (ready true true false).orient success.orient := by
  obtain ⟨hrun, hend⟩ := finish_checked
  exact hend ▸ hrun.reachableOn

end ForallGadget.Execution

end Cslib.Complexity.NCL.QBF
