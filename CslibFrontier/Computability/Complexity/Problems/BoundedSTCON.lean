/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Foundations.Relation.RelatesWithinSteps
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Length-bounded directed connectivity

A `BoundedSTCONInstance` consists of an adjacency-matrix connectivity instance and a binary
length bound. `BoundedSTCON` asks for a walk of at most that many arcs; allowing repeated
vertices does not change this question, since cycles can be removed.

This module proves the mathematical layered-graph construction for Exercise 5.19 of
[Goldreich2008] (January 2007 draft, printed p. 197). The machine certificate and NL membership
are in `BoundedSTCON/LogSpace` and `BoundedSTCON/Membership`.

## Main results

* `BoundedSTCONInstance.capped_iff`: capping the bound at the vertex count preserves the answer.
* `BoundedSTCONInstance.layered_mem_iff`: the layered graph is in `STCON` exactly when the
  original instance has a walk within its bound.
-/

public section

namespace Cslib.Complexity

/-- Directed connectivity with a bound on the number of arcs. -/
structure BoundedSTCONInstance where
  /-- The adjacency-matrix graph and its source and target, in the existing STCON format. -/
  graph : STCONInstance
  /-- The maximum number of arcs, encoded in binary. -/
  bound : ℕ

open Turing.MultiTapeTM in
/-- A framed `encSTCON` graph followed by the binary digits (`encNat`) of the length bound. -/
enc_structure encBoundedSTCON : BoundedSTCONInstance where
  graph : encSTCON,
  bound : encNat

/-- Instances admitting a directed source-to-target walk with at most `bound` arcs. -/
@[expose] def BoundedSTCON : Set BoundedSTCONInstance :=
  {I | Relation.RelatesWithinSteps I.graph.Adj I.graph.s I.graph.t I.bound}

namespace BoundedSTCONInstance

variable (I : BoundedSTCONInstance)

/-- The number of useful transitions: longer walks can have their cycles removed. -/
@[expose] def cap : ℕ := min I.bound I.graph.n

/-- Capping the binary bound at the vertex count preserves bounded reachability. -/
theorem capped_iff :
    Relation.RelatesWithinSteps I.graph.Adj I.graph.s I.graph.t I.cap ↔ I ∈ BoundedSTCON := by
  refine ⟨fun h => h.mono (Nat.min_le_left _ _), fun h => ?_⟩
  change Relation.RelatesWithinSteps I.graph.Adj I.graph.s I.graph.t I.bound at h
  by_cases hb : I.bound ≤ I.graph.n
  · simpa [cap, Nat.min_eq_left hb] using h
  · simpa [cap, Nat.min_eq_right (Nat.le_of_not_le hb)] using
      (Relation.reflTransGen_iff_relatesWithinSteps
        (r := I.graph.Adj) (a := I.graph.s) (b := I.graph.t)
        (N := I.graph.n) (by simp)).mp h.reflTransGen

/-- Number a vertex in a layer by `layer * n + vertex`. -/
@[expose] def node (layer : Fin (I.cap + 1)) (vertex : Fin I.graph.n) :
    Fin ((I.cap + 1) * I.graph.n) := finProdFinEquiv (layer, vertex)

/-- The directed layered instance: each arc advances one layer and follows an original arc
or stays at the same original vertex. -/
@[expose] def layered : STCONInstance where
  n := (I.cap + 1) * I.graph.n
  adj u v :=
    let a := finProdFinEquiv.symm u
    let b := finProdFinEquiv.symm v
    decide (b.1.val = a.1.val + 1) && (I.graph.adj a.2 b.2 || decide (a.2 = b.2))
  s := I.node ⟨0, by omega⟩ I.graph.s
  t := I.node ⟨I.cap, by omega⟩ I.graph.t

/-- The adjacency test in named layer and vertex coordinates. -/
theorem layered_adj_iff (i j : Fin (I.cap + 1)) (u v : Fin I.graph.n) :
    I.layered.Adj (I.node i u) (I.node j v) ↔
      j.val = i.val + 1 ∧ Relation.ReflGen I.graph.Adj u v := by
  simp only [STCONInstance.Adj, layered, node, Equiv.symm_apply_apply,
    Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  rw [Relation.reflGen_iff]
  tauto

private theorem project {x : Fin I.layered.n}
    (h : Relation.ReflTransGen I.layered.Adj I.layered.s x) :
    Relation.RelatesWithinSteps I.graph.Adj I.graph.s
      (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm x).1.val := by
  induction h with
  | refl => simp [layered, node]
  | @tail y z _ hyz ih =>
    have heq (w : Fin I.layered.n) :
        I.node (finProdFinEquiv.symm w).1 (finProdFinEquiv.symm w).2 = w :=
      Equiv.apply_symm_apply _ w
    rw [← heq y, ← heq z, I.layered_adj_iff] at hyz
    rw [hyz.1]
    exact Relation.RelatesWithinSteps.succ_iff.mpr ⟨_, ih, hyz.2⟩

private theorem lift {v : Fin I.graph.n} {k : ℕ}
    (h : Relation.RelatesInSteps (Relation.ReflGen I.graph.Adj) I.graph.s v k)
    (hk : k ≤ I.cap) :
    Relation.ReflTransGen I.layered.Adj I.layered.s (I.node ⟨k, by omega⟩ v) := by
  induction h with
  | refl => exact .refl
  | tail u v k _ huv ih =>
    exact (ih (by omega)).tail ((I.layered_adj_iff _ _ _ _).mpr ⟨rfl, huv⟩)

/-- The layered graph reaches its final-layer target exactly when the original graph has a
source-to-target walk within the given bound. Zero bounds and coinciding terminals are included. -/
theorem layered_mem_iff : I.layered ∈ STCON ↔ I ∈ BoundedSTCON := by
  rw [← I.capped_iff]
  constructor
  · intro h
    simpa [layered, node] using I.project h
  · intro h
    exact I.lift (Relation.relatesWithinSteps_iff_relatesInSteps_reflGen.mp h) le_rfl

end BoundedSTCONInstance

end Cslib.Complexity
