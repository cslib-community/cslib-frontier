/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.UCONN
import CslibFrontier.Computability.Complexity.Problems.Bipartite.LogSpace

/-!
# Undirected connectivity tests

Goldreich, Theorem 5.6: connectivity of graphs encoded by adjacency matrices is in `L`
(`Cslib.Complexity.UCONN_mem_L`), through a logspace many-one reduction to undirected `s`–`t`
connectivity (`Cslib.Complexity.UCONN.logSpaceReducible_USTCON`).

The language is neither empty nor everything: the single edge is connected and two isolated
vertices are not. Following Goldreich's definition (a path between each pair of vertices), the
graph without vertices is connected. The copies in series of the single edge connect the source to
the target, and those of two isolated vertices do not
(`Cslib.Complexity.UCONN.chainInstance_mem_iff`); the number of vertices of the instance and the
numbering of the vertices of the copies are checked on small values.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.UCONN

open Cslib Cslib.Complexity Cslib.Complexity.UCONN

/-- The single edge `0 — 1`. -/
private def edge : UGraphInstance where
  n := 2
  adj a b := decide (a ≠ b)
  symm a b := by simp [ne_comm]
  loopless a := by simp

/-- Two isolated vertices. -/
private def isolated : UGraphInstance where
  n := 2
  adj _ _ := false
  symm _ _ := rfl
  loopless _ := rfl

private theorem edge_mem : edge ∈ UCONN := by
  have h : edge.graph.Adj ⟨0, by decide⟩ ⟨1, by decide⟩ := by
    change decide ((0 : Fin 2) ≠ 1) = true
    decide
  intro a b
  have hr : ∀ v : Fin edge.n, edge.graph.Reachable ⟨0, by decide⟩ v := fun v => by
    match v with
    | ⟨0, _⟩ => exact .rfl
    | ⟨1, _⟩ => exact h.reachable
  exact (hr a).symm.trans (hr b)

private theorem isolated_notMem : isolated ∉ UCONN := by
  intro h
  obtain ⟨p⟩ := h (0 : Fin 2) (1 : Fin 2)
  cases p with
  | cons hadj _ =>
    have := (UGraphInstance.graph_adj isolated).1 hadj
    contradiction

example : edge ∈ UCONN := edge_mem

example : isolated ∉ UCONN := isolated_notMem

/-- The graph without vertices is connected, as in Goldreich's definition. -/
example : Bipartite.empty ∈ UCONN := fun a => a.elim0

/-- The instance has `n² + 2` vertices: `6` for the single edge. -/
example : (chainInstance edge).n = 6 := rfl

/-- The vertex `x` of the copy `v` is `2 + v n + x`; it decodes back. -/
example : copyVertex 3 1 2 = 7 ∧ copy 3 7 = 1 ∧ vert 3 7 = 2 := by decide

/-- The single edge is connected, so the source reaches the target. -/
example : chainInstance edge ∈ USTCON := (chainInstance_mem_iff edge).2 edge_mem

/-- Two isolated vertices are not connected, so the source does not reach the target. -/
example : chainInstance isolated ∉ USTCON :=
  fun h => isolated_notMem ((chainInstance_mem_iff isolated).1 h)

/-- With no copies, the source and the target are joined directly. -/
example : chainInstance Bipartite.empty ∈ USTCON :=
  (chainInstance_mem_iff _).2 fun a => a.elim0

/-- **Goldreich's Theorem 5.6** on the matrix encoding. -/
example : UCONN ∈ L encUGraph := UCONN_mem_L

end CslibFrontierTests.UCONN
