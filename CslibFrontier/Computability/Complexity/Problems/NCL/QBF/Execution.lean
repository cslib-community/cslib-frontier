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

attribute [local instance] Diagram.decidableLegal

private def numRun (vs : List (Vertex ℕ)) (n : ℕ) : (ℕ → Bool) → List ℕ → (ℕ → Bool) → Bool
  | s, [], t => vs.all (·.Sat s) && (List.range n).all (fun i => s i == t i)
  | s, k :: ks, t => vs.all (·.Sat s) && numRun vs n (reverse s k) ks t

private theorem legal_of_numVertexList {a b : List Color} {D : Diagram Gate a b} {u : ℕ → Bool}
    (h : (numVertexList Gate.interp D).all (·.Sat u) = true) :
    (D.graph Gate.interp).Legal (u ∘ D.num) :=
  (forall_vertexList_iff D _).mp fun v hv => (Vertex.sat_map D.num v u).mp
    (of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hv)))

private theorem reachableOn_of_numRun {a b : List Color} {D : Diagram Gate a b}
    {p : D.Edge → Prop} [DecidablePred p] (u v : ℕ → Bool)
    (ks : List (Fin (a.length + D.innerCount)))
    (h : (ks.all (fun k => decide (p (D.numEquiv.symm k))) &&
      numRun (numVertexList Gate.interp D) (a.length + D.innerCount) u (ks.map Fin.val) v) =
        true) : (D.graph Gate.interp).ReachableOn p (u ∘ D.num) (v ∘ D.num) := by
  induction ks generalizing u with
  | nil =>
    simp only [List.all_nil, Bool.true_and, List.map_nil, numRun, Bool.and_eq_true,
      List.all_eq_true, List.mem_range, beq_iff_eq] at h
    exact (funext fun e => h.2 _ (D.numEquiv_val e ▸ (D.numEquiv e).isLt) :
      u ∘ D.num = v ∘ D.num) ▸ .refl
  | cons k ks ih =>
    simp only [List.all_cons, List.map_cons, numRun, Bool.and_eq_true, decide_eq_true_eq] at h
    have hrev : reverse (u ∘ D.num) (D.numEquiv.symm k) = reverse u k.val ∘ D.num := by
      simpa only [num_numEquiv_symm] using
        (reverse_comp_of_injective D.num_injective u (D.numEquiv.symm k)).symm
    have hs' : (D.graph Gate.interp).Legal (reverse u k.val ∘ D.num) := by
      cases ks <;> exact legal_of_numVertexList (Bool.and_eq_true _ _ |>.mp h.2.2).1
    exact .head ⟨legal_of_numVertexList h.2.1, hrev ▸ hs', _, h.1.1, hrev.symm⟩
      (hrev ▸ ih _ (Bool.and_eq_true _ _ |>.mpr ⟨h.1.2, h.2.2⟩))

namespace ExistsGadget.Execution

local notation "idleList" => ([0, 1, 6] : List ℕ)
local notation "readyList" v:arg s:arg => (([1, 2, 4, 10, 12] ++
  (if v then [5, 7, 8] else [6, 9]) ++ if s then [0] else []) : List ℕ)

/-- The initial existential orientation with its incoming try wire activated. -/
@[expose] def idle : Realization Gate.interp existsGadget [true, true]
    [true, false, false, false] where
  orient := fun e => (idleList).contains (existsGadget.num e)
  legal := by decide +kernel
  top_eq := by decide +kernel
  bot_eq := by decide +kernel

/-- The selected value is locked and its literal and outgoing try wires are active.
The satisfied wire passes through with direction `sat`. -/
@[expose] def ready (value sat : Bool) :
    Realization Gate.interp existsGadget [sat, true] [sat, true, value, !value] where
  orient := fun e => (readyList value sat).contains (existsGadget.num e)
  legal := by cases value <;> cases sat <;> decide +kernel
  top_eq := by cases value <;> cases sat <;> decide +kernel
  bot_eq := by cases value <;> cases sat <;> decide +kernel

@[simp] theorem ready_mem (value sat : Bool) : (ready value sat).orient mem = value := by
  cases value <;> cases sat <;> decide +kernel

/-- Activate the incoming try wire of the canonical initial configuration. -/
theorem activate : graph.StepOn (· = tryIn) Initial.existsInitial.orient idle.orient :=
  ⟨Initial.existsInitial.legal, idle.legal, tryIn, rfl, by decide +kernel⟩

/-- A suffix response changes exactly the common satisfied wire. -/
theorem ready_sat (value : Bool) : (ready value false).orient =
    reverse (ready value true).orient sat := by cases value <;> decide +kernel

/-- Select either value while keeping the incoming controls fixed. -/
theorem prepare (value : Bool) :
    graph.ReachableOn (fun e => e ≠ sat ∧ e ≠ tryIn) idle.orient (ready value true).orient :=
  reachableOn_of_numRun ((idleList).contains ·) ((readyList value true).contains ·)
    (if value then [2, 5, 7, 8, 6, 4, 10, 12] else [2, 4, 9, 10, 12])
    (by cases value <;> decide +kernel)

/-- Preparation reaches the requested assignment in the variable latch. -/
theorem prepare_spec (value : Bool) :
    graph.ReachableOn (fun e => e ≠ sat ∧ e ≠ tryIn) idle.orient (ready value true).orient ∧
      (ready value true).orient mem = value :=
  ⟨prepare value, ready_mem value true⟩

end ExistsGadget.Execution

namespace ForallGadget.Execution

local notation "idleList" => ([0, 1, 2, 4, 7, 11, 26, 30, 31] : List ℕ)
local notation "readyList" v:arg r:arg s:arg => (([0, 1, 8, 9, 15, 17, 26, 30] ++
  (if s then [31] else []) ++ (if r then [2, 3, 5, 6] else [2, 4, 7]) ++
  if v then [10, 12, 13, 18, 22, 23] else [11, 14, 20, 24, 25]) : List ℕ)
local notation "successList" =>
  ([1, 2, 3, 5, 6, 8, 9, 10, 12, 13, 15, 17, 18, 22, 23, 27, 28, 30] : List ℕ)

/-- The initial universal orientation with its incoming try wire activated and record clear. -/
@[expose]
def idle : Realization Gate.interp forallGadget [true, true] [true, false, false, false] where
  orient := fun e => (idleList).contains (forallGadget.num e)
  legal := by decide +kernel
  top_eq := by decide +kernel
  bot_eq := by decide +kernel

/-- A locked variable and active suffix try, with the given record and suffix response.
The outer satisfied wire remains inactive. -/
@[expose] def ready (value recorded sat : Bool) :
    Realization Gate.interp forallGadget [true, true] [sat, true, value, !value] where
  orient := fun e => (readyList value recorded sat).contains (forallGadget.num e)
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
  orient := fun e => (successList).contains (forallGadget.num e)
  legal := by decide +kernel
  top_eq := by decide +kernel
  bot_eq := by decide +kernel

/-- Activate the incoming try wire of the canonical initial configuration. -/
theorem activate : graph.StepOn (· = tryIn) Initial.forallInitial.orient idle.orient :=
  ⟨Initial.forallInitial.legal, idle.legal, tryIn, rfl, by decide +kernel⟩

/-- A suffix response changes exactly its satisfied wire at either value and record setting. -/
theorem ready_sat (value recorded : Bool) : (ready value recorded false).orient =
    reverse (ready value recorded true).orient satIn := by
  cases value <;> cases recorded <;> decide +kernel

/-- Prepare a value without changing the outer controls, suffix response, or clear record. -/
theorem prepare (value : Bool) :
    graph.ReachableOn (fun e => e ≠ satOut ∧ e ≠ tryIn ∧ e ≠ satIn ∧ e ≠ recMem)
      idle.orient (ready value false true).orient :=
  reachableOn_of_numRun ((idleList).contains ·) ((readyList value false true).contains ·)
    (if value then [8, 10, 12, 13, 11, 9, 15, 17, 18, 22, 23] else [8, 9, 14, 15, 17, 20, 24, 25])
    (by cases value <;> decide +kernel)

/-- Preparation reaches the requested variable assignment while keeping the record clear. -/
theorem prepare_spec (value : Bool) :
    graph.ReachableOn (fun e => e ≠ satOut ∧ e ≠ tryIn ∧ e ≠ satIn ∧ e ≠ recMem)
      idle.orient (ready value false true).orient ∧
      (ready value false true).orient mem = value ∧
      (ready value false true).orient recMem = false :=
  ⟨prepare value, ready_mem value false true, ready_recMem value false true⟩

/-- Record success with the variable false, keeping every boundary direction fixed. -/
theorem record_false : InnerReach Gate.interp forallGadget
    (ready false false false).orient (ready false true false).orient :=
  reachableOn_of_numRun ((readyList false false false).contains ·)
    ((readyList false true false).contains ·) [7, 30, 2, 3, 5, 6, 4, 2, 30] (by decide +kernel)

/-- After the suffix resets, change to true while keeping the false-branch record set. -/
theorem switch_true :
    graph.ReachableOn (fun e => e ≠ satOut ∧ e ≠ tryIn ∧ e ≠ satIn ∧ e ≠ recMem)
      (ready false true true).orient (ready true true true).orient :=
  reachableOn_of_numRun ((readyList false true true).contains ·)
    ((readyList true true true).contains ·)
    [17, 15, 9, 10, 12, 13, 18, 22, 23, 24, 25, 20, 14, 11, 9, 15, 17] (by decide +kernel)

/-- Return the true branch's success, keeping try-in and every suffix boundary wire fixed. -/
theorem finish : graph.ReachableOn (fun e => e ≠ tryIn ∧ ∀ j, e ≠ forallGadget.bottom j)
    (ready true true false).orient success.orient :=
  reachableOn_of_numRun ((readyList true true false).contains ·) ((successList).contains ·)
    [26, 27, 28, 0] (by decide +kernel)

end ForallGadget.Execution

end Cslib.Complexity.NCL.QBF
