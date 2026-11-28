/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Cslib.Foundations.Relation.RelatesInSteps
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Walks of a simple graph as steps of its adjacency relation

A walk of length `n` from `u` to `v` in a simple graph is a chain of `n` steps of the adjacency
relation (`SimpleGraph.exists_walk_length_eq_iff_relatesInSteps`). Hence the extended distance
`SimpleGraph.edist` is at most `n` exactly when `v` is reached from `u` within `n` steps
(`SimpleGraph.edist_le_iff_relatesWithinSteps`). This connects Mathlib's graph metric to the
step-counted reachability `Relation.RelatesWithinSteps` that bounded connectivity uses.

## Main results

* `SimpleGraph.exists_walk_length_eq_iff_relatesInSteps`: walks of length `n` are chains of `n`
  adjacency steps.
* `SimpleGraph.edist_le_iff_relatesWithinSteps`: the distance is at most `n` exactly when there
  is a chain of at most `n` adjacency steps.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v : V} {n : ℕ}

/-- **Walks are chains of adjacency steps**: there is a walk of length `n` from `u` to `v`
exactly when `v` is reached from `u` in `n` steps of the adjacency relation. -/
theorem exists_walk_length_eq_iff_relatesInSteps :
    (∃ p : G.Walk u v, p.length = n) ↔ Relation.RelatesInSteps G.Adj u v n := by
  constructor
  · rintro ⟨p, rfl⟩
    induction p with
    | nil => exact .refl _
    | cons h _ ih => exact Relation.RelatesInSteps.head _ _ _ _ h ih
  · intro h
    induction h with
    | refl => exact ⟨.nil, rfl⟩
    | tail _ _ _ _ h ih =>
      obtain ⟨p, rfl⟩ := ih
      exact ⟨p.concat h, p.length_concat h⟩

/-- **The distance is at most `n`** exactly when `v` is reached from `u` within `n` steps of the
adjacency relation. -/
theorem edist_le_iff_relatesWithinSteps :
    G.edist u v ≤ n ↔ Relation.RelatesWithinSteps G.Adj u v n := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (ENat.natCast_ne_top n) h)
    refine ⟨p.length, ?_, exists_walk_length_eq_iff_relatesInSteps.mp ⟨p, rfl⟩⟩
    exact_mod_cast hp ▸ h
  · rintro ⟨m, hm, h⟩
    obtain ⟨p, rfl⟩ := exists_walk_length_eq_iff_relatesInSteps.mpr h
    exact (edist_le p).trans (by exact_mod_cast hm)

end SimpleGraph
