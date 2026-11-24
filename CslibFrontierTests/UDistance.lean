/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.UDistance.Completeness

set_option linter.privateModule false

open Cslib.Complexity Turing.MultiTapeTM

-- The record encoding keeps the undirected graph framed and the bound binary, the layout of
-- bounded directed connectivity on the directed graph.
example (I : UDistanceInstance) :
    encUDistance I = frame (encUSTCON I.graph) ++ encNat I.bound := rfl

example (I : UDistanceInstance) : encBoundedSTCON I.toBoundedSTCON = encUDistance I := rfl

-- The single edge: distance one, so at most one and at most two, exactly one but not exactly two
-- or zero.
example : (⟨USTCONInstance.edgeTwo, 1⟩ : UDistanceInstance) ∈ UDistanceEq :=
  SimpleGraph.edist_eq_one_iff_adj.mpr (by decide)

example : (⟨USTCONInstance.edgeTwo, 2⟩ : UDistanceInstance) ∈ UDistanceAtMost := by
  change (_ : ℕ∞) ≤ _
  rw [SimpleGraph.edist_eq_one_iff_adj.mpr (by decide)]
  decide

example : (⟨USTCONInstance.edgeTwo, 2⟩ : UDistanceInstance) ∉ UDistanceEq := by
  change ¬_ = _
  rw [SimpleGraph.edist_eq_one_iff_adj.mpr (by decide)]
  decide

example : (⟨USTCONInstance.edgeTwo, 0⟩ : UDistanceInstance) ∉ UDistanceAtMost := by
  change ¬(_ : ℕ∞) ≤ _
  rw [Nat.cast_zero, nonpos_iff_eq_zero, SimpleGraph.edist_eq_zero_iff]
  decide

-- Disconnected terminals have no distance: no bound, however large, is met.
example (K : ℕ) : (⟨USTCONInstance.emptyTwo, K⟩ : UDistanceInstance) ∉ UDistanceAtMost := by
  change ¬(_ : ℕ∞) ≤ _
  rw [SimpleGraph.edist_eq_top_of_not_reachable USTCONInstance.emptyTwo_notMem_USTCON]
  simp

-- The pendant target after `t` is never reached with zero arcs, so distance `0` is handled
-- without a separate case.
example (I : UDistanceInstance) (h : I.graph.s = I.graph.t) :
    I ∈ UDistanceEq ↔ I.bound = 0 := by
  change _ = _ ↔ _
  rw [h, SimpleGraph.edist_self]
  exact ⟨fun h => by exact_mod_cast h.symm, fun h => by simp [h]⟩

-- The layered hardness instance asks for distance `n`.
example (J : STCONInstance) : J.distanceInstance.bound = J.n := rfl

example : LogSpaceComplete NL encUDistance UDistanceAtMost := UDistanceAtMost.logSpaceComplete

example : LogSpaceComplete NL encUDistance UDistanceEq := UDistanceEq.logSpaceComplete
