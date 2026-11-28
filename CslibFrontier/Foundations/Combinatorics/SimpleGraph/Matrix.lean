/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Finite undirected adjacency matrices

`Cslib.Complexity.UGraphInstance` is a terminal-free symmetric loopless Boolean matrix,
including the empty matrix. Its `graph` accessor supplies the shared simple-graph interpretation
for connectivity and bipartiteness; `adjN` extends entries by zero outside the vertex range.
-/

@[expose] public section

namespace Cslib.Complexity

/-- An **undirected graph** on `Fin n`, given by its adjacency matrix, symmetric and with zero
diagonal. -/
structure UGraphInstance where
  /-- The number of vertices. -/
  n : ℕ
  /-- The adjacency matrix. -/
  adj : Fin n → Fin n → Bool
  /-- The matrix is symmetric. -/
  symm : ∀ a b, adj a b = adj b a
  /-- The diagonal is zero. -/
  loopless : ∀ a, adj a a = false

namespace UGraphInstance

variable (G : UGraphInstance)

/-- The simple graph of an instance. -/
def graph : SimpleGraph (Fin G.n) where
  Adj a b := G.adj a b = true
  symm.symm a b h := (G.symm b a).trans h
  loopless.irrefl a h := by simp [G.loopless] at h

@[simp]
theorem graph_adj {a b : Fin G.n} : G.graph.Adj a b ↔ G.adj a b = true :=
  Iff.rfl

/-- The entries of an instance on natural numbers, `false` outside the vertices. -/
def adjN (u v : ℕ) : Bool :=
  if h : u < G.n ∧ v < G.n then G.adj ⟨u, h.1⟩ ⟨v, h.2⟩ else false

theorem adjN_comm (u v : ℕ) : G.adjN u v = G.adjN v u := by
  unfold adjN
  by_cases h : u < G.n ∧ v < G.n
  · rw [dite_eq_left h, dite_eq_left ⟨h.2, h.1⟩]
    exact G.symm _ _
  · rw [dite_eq_right h, dite_eq_right fun h' => h ⟨h'.2, h'.1⟩]

end UGraphInstance

end Cslib.Complexity
