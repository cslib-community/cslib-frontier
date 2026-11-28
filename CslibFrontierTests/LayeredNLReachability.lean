/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.LogSpace.LayeredReachability
import CslibFrontier.Computability.Complexity.Problems.STCON.Completeness

/-! Checked callers for empty paths, early arrival, rejection, and native NL witnesses. -/

namespace CslibFrontierTests.LayeredNLReachability

open Cslib.Complexity Cslib.Complexity.STCON
open Turing Turing.MultiTapeTM

private def emptyPath : STCONInstance where
  n := 1
  adj _ _ := false
  s := 0
  t := 0

/-- A zero-edge accepting path is retained even when the original graph has no edges. -/
example : Relation.ReflTransGen (layeredRelation emptyPath)
    (layeredStart emptyPath) (layeredTarget emptyPath) :=
  (layered_reachable_iff emptyPath).mpr Relation.ReflTransGen.refl

private def earlyArrival : STCONInstance where
  n := 4
  adj u v := u == 0 && v == 1
  s := 0
  t := 1

/-- Arrival after one original edge is padded to the fixed third layer. -/
example : Relation.ReflTransGen (layeredRelation earlyArrival)
    (layeredStart earlyArrival) (layeredTarget earlyArrival) := by
  apply (layered_reachable_iff earlyArrival).mpr
  exact Relation.ReflTransGen.single (show earlyArrival.adj earlyArrival.s earlyArrival.t = true
    from rfl)

private def rejected : STCONInstance where
  n := 2
  adj _ _ := false
  s := 0
  t := 1

/-- Waiting never creates a path between distinct unreachable original vertices. -/
example : ¬ Relation.ReflTransGen (layeredRelation rejected)
    (layeredStart rejected) (layeredTarget rejected) := by
  rw [layered_reachable_iff, mem_STCON,
    Relation.reflTransGen_iff_eq (fun _ => by simp [STCONInstance.Adj, rejected])]
  decide

/-- The general construction applies to the library's actual native NL decider for STCON,
not to a postulated graph family. Its one machine and exponent work for every instance. -/
example : ∃ (k : ℕ) (State : Type) (inst : Fintype State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
    letI := inst
    ∀ I, let J := configurationInstance ntm c (encSTCON I)
      Relation.ReflTransGen (layeredRelation J) (layeredStart J) (layeredTarget J) ↔ I ∈ STCON := by
  obtain ⟨k, State, inst, ntm, c, _, _, h⟩ := exists_layered_reachability_of_mem_NL STCON.mem_NL
  let : Fintype State := inst
  exact ⟨k, State, inst, ntm, c, fun I => (h I).1.symm⟩

/-- Nonconsecutive layers are rejected before any native transition-table lookup. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (B n : ℕ) :
    layeredEdgeQuery ntm ⟨B, n, 0, 0, 0, 0, none⟩ = false := by
  simp [layeredEdgeQuery]

/-- A caller resumes with the answer after three abstract steps: call entry, the actual
original-input read, and return. No copied input word or pre-read bit enters the request. -/
example {σ State : Type} {k : ℕ} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (M : QueryMachine σ) (request : σ → Option (LayeredQuery ⊕ Bool))
    (resume : σ → (LayeredQuery ⊕ Bool) → σ) (w : List Bool) (s : σ) (q : LayeredQuery)
    (hs : M.halted s = false) (hr : request s = some (.inl q)) :
    (M.withCalls (layeredCallback ntm) request resume).runFrom w (.inl s) 3 =
      .inl (resume s (.inr (layeredEdgeQuery ntm
        {q with symbol := w[layeredQueryIndex (k := k) q]?}))) := by
  have h := QueryMachine.withCalls_runFrom_call M (layeredCallback ntm) request resume w
    s (.inl q) 1 hs hr (by
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      rfl)
    (by rw [show 1 = 0 + 1 from rfl, layeredCallback_runFrom]; rfl)
  exact h.trans (congrArg (fun r => Sum.inl (resume s r))
    (layeredCallback_runFrom ntm w q 0))

end CslibFrontierTests.LayeredNLReachability
