/-
Copyright (c) 2026 Samuel Schlesinger, vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, vvauted
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.DisjointSet.Tarjan

/-!
# Worked inverse-Ackermann union-find step-bound examples

These kernel-checked examples exercise:

1. Empty (`n = 0`) and singleton (`n = 1`) edge cases under `tarjan_run_correct` and
   `tarjan_run_two_param`.
2. Balanced tree construction and repeated compressed queries on `Fin 4` against both
   `tarjanCharge` and `tarjan_run_two_param`.
3. Direct application of `tarjanAmortized` and `tarjanAmortizedAt` using `impl_rep`.
4. The dense linear step corollary `tarjan_run_linear_of_dense` when `n * Nat.log 2 n ≤ m`.
-/

public section

namespace CslibFrontierTests.TarjanUnionFind

open Cslib.DataStructure.DisjointSet
open Cslib.DataStructure.DisjointSet.UnionFind
open Cslib.DataStructure

example :
    (run (init 0) getNumComponents).value = 0 ∧
      total id (run (init 0) getNumComponents).traces ≤
        ((spec 0).clientHistory (Partition.discrete 0) getNumComponents).length *
          (5 * Nat.inverseAckermann 0 + 2) ∧
      (run (init 1) (union 0 0)).value = false ∧
      total id (run (init 1) (union 0 0)).traces ≤
        ((spec 1).clientHistory (Partition.discrete 1) (union 0 0)).length *
          (5 * Nat.inverseAckermannTwo 1 1 + 2) :=
  ⟨rfl, (tarjan_run_correct (n := 0) getNumComponents).2.2.2,
    rfl, (tarjan_run_two_param (n := 1) (union 0 0)).2.2⟩

def chainAndQueries : (spec 4).Client (Bool × Bool × Bool × Bool) := do
  let _ ← union 0 1
  let _ ← union 2 3
  let _ ← union 1 3
  let q₁ ← same 0 3
  let q₂ ← same 0 3
  let q₃ ← same 0 2
  let q₄ ← same 1 3
  pure (q₁, q₂, q₃, q₄)

-- Concrete trace total matches `Partition 4` semantics and satisfies `tarjan_run_correct`.
example :
    (run (init 4) chainAndQueries).value = (true, true, true, true) ∧
      total id (run (init 4) chainAndQueries).traces ≤
        ((spec 4).clientHistory (Partition.discrete 4) chainAndQueries).length *
          (5 * Nat.inverseAckermann 4 + 2) ∧
      total id (run (init 4) chainAndQueries).traces ≤
        ((spec 4).clientHistory (Partition.discrete 4) chainAndQueries).length *
          (5 * Nat.inverseAckermannTwo
            ((spec 4).clientHistory (Partition.discrete 4) chainAndQueries).length 4 + 2) :=
  ⟨rfl, (tarjan_run_correct chainAndQueries).2.2.2, (tarjan_run_two_param chainAndQueries).2.2⟩

-- Direct `Amortized.client` usage via `impl_rep` and `tarjanPotential_init`.
example :
    total id (run (init 4) chainAndQueries).traces +
        tarjanPotential 4 ((spec 4).clientState (Partition.discrete 4) chainAndQueries)
          (run (init 4) chainAndQueries).state ≤
      (spec 4).totalCost (tarjanCharge 4) (Partition.discrete 4)
        ((spec 4).clientHistory (Partition.discrete 4) chainAndQueries) := by
  have hr : (impl 4).rep (Partition.discrete 4) (init 4) := by
    rw [impl_rep]; exact rep_init 4
  have hv := (spec 4).validHistory_of_forall_valid (fun _ _ => trivial)
    (Partition.discrete 4) ((spec 4).clientHistory (Partition.discrete 4) chainAndQueries)
  have hc := (tarjanAmortized 4).client hr hv (Execution.executes_run step chainAndQueries (init 4))
  simpa only [tarjanPotential_init, Nat.add_zero] using hc

-- Adaptive client branching on `same` / `union` answers, bounded via `tarjan_run_two_param`.
def adaptiveClient : (spec 4).Client (Bool × ℕ) := do
  let _ ← union 0 1
  let merged ← union 2 3
  let samePair ← same 0 2
  if samePair then
    let _ ← same 1 3
    pure (merged, 0)
  else
    let _ ← union 1 3
    let c ← getNumComponents
    pure (merged, c)

example :
    (run (init 4) adaptiveClient).value = (true, 1) ∧
      ((spec 4).clientHistory (Partition.discrete 4) adaptiveClient).length = 5 ∧
      total id (run (init 4) adaptiveClient).traces ≤
        5 * (5 * Nat.inverseAckermannTwo 5 4 + 2) :=
  ⟨rfl, rfl, (tarjan_run_two_param adaptiveClient).2.2⟩

-- Dense client on `Fin 4` with `8 = 4 * Nat.log 2 4` operations satisfies strict `7 * m` bound.
def denseEightClient : (spec 4).Client ℕ := do
  let _ ← union 0 1
  let _ ← union 2 3
  let _ ← union 1 3
  let _ ← same 0 3
  let _ ← same 0 3
  let _ ← same 2 3
  let _ ← same 1 2
  getNumComponents

example :
    ((spec 4).clientHistory (Partition.discrete 4) denseEightClient).length = 8 ∧
      4 * Nat.log 2 4 ≤ ((spec 4).clientHistory (Partition.discrete 4) denseEightClient).length ∧
      total id (run (init 4) denseEightClient).traces ≤
        7 * ((spec 4).clientHistory (Partition.discrete 4) denseEightClient).length := by
  refine ⟨rfl, by decide, tarjan_run_linear_of_dense denseEightClient (by decide)⟩

example :
    total id (run (init 4) denseEightClient).traces +
        tarjanPotentialAt 3 4 ((spec 4).clientState (Partition.discrete 4) denseEightClient)
          (run (init 4) denseEightClient).state ≤
      (spec 4).totalCost (tarjanChargeAt 3 4) (Partition.discrete 4)
        ((spec 4).clientHistory (Partition.discrete 4) denseEightClient) +
        4 * (Nat.inverseAckermannAt 3 4 * 3) := by
  have hr : (impl 4).rep (Partition.discrete 4) (init 4) := by
    rw [impl_rep]; exact rep_init 4
  have hv := (spec 4).validHistory_of_forall_valid (fun _ _ => trivial)
    (Partition.discrete 4) ((spec 4).clientHistory (Partition.discrete 4) denseEightClient)
  have hc :=
    (tarjanAmortizedAt 3 4).client hr hv (Execution.executes_run step denseEightClient (init 4))
  simpa only [tarjanPotentialAt_init, max_eq_right (by decide : 1 ≤ 3)] using hc

end CslibFrontierTests.TarjanUnionFind
