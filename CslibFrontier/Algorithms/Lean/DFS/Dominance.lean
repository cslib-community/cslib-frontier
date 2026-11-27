/-
Copyright (c) 2026 muanch18. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: muanch18
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.DFS.Basic
public import Mathlib.Data.List.Chain

/-!
# Block dominance by depth-first search

Block dominance asks whether every walk from the entry to a target visits a candidate block.
The executable query tests reachability after deleting the candidate's incident edges.

## Main definitions

* `Cslib.Algorithms.Lean.DFS.Dominates` expresses dominance over walks, including both endpoints.
* `Cslib.Algorithms.Lean.DFS.deleteVertex` removes the incident edges of a vertex.
* `Cslib.Algorithms.Lean.DFS.dominatesB` checks a single dominance query by depth-first search.

## Main results

* `Cslib.Algorithms.Lean.DFS.dominates_iff_not_reachable_delete` characterizes dominance by
  loss of reachability after deletion when the candidate differs from the entry.
* `Cslib.Algorithms.Lean.DFS.dominatesB_eq_true_iff` proves that the query agrees with the
  walk specification, including for unreachable targets.

## References

* [J. Zhao and S. Zdancewic, *Mechanized Verification of Computing Dominators for Formalizing
  Compilers*, Definition 1][ZhaoZdancewic2012]
-/

public section

namespace Cslib.Algorithms.Lean.DFS

variable {V : Type*} (adj : V → List V)

/-- Every walk from `entry` to `v` contains `d`, counting both endpoints. -/
@[expose] def Dominates (entry d v : V) : Prop :=
  ∀ tail : List V, (entry :: tail).IsChain (Edge adj) →
    (entry :: tail).getLast (by simp) = v → d ∈ entry :: tail

variable [DecidableEq V]

/-- Delete all incident edges of `d`, keeping the original vertex type. -/
@[expose] def deleteVertex (d u : V) : List V :=
  if u = d then [] else (adj u).filter (· != d)

private theorem chain_delete_iff (d u : V) (hu : u ≠ d) (tail : List V) :
    (u :: tail).IsChain (Edge (deleteVertex adj d)) ↔
      (u :: tail).IsChain (Edge adj) ∧ d ∉ tail := by
  induction tail generalizing u with
  | nil => simp
  | cons w tail ih =>
    by_cases hw : w = d
    · subst w
      simp [List.isChain_cons_cons, Edge, deleteVertex, hu]
    · rw [List.isChain_cons_cons, List.isChain_cons_cons, ih w hw]
      simp [Edge, deleteVertex, hu, hw, Ne.symm hw, and_assoc]

/-- Check dominance with one DFS, or immediately accept either endpoint. -/
@[expose] def dominatesB [Fintype V] (entry d v : V) : Bool :=
  if entry = d ∨ v = d then true else
    decide (v ∉ (dfs (deleteVertex adj d) (Fintype.card V) [entry]).visited)

variable {adj}

/-- A candidate distinct from the entry dominates exactly when its deletion destroys
reachability. This also covers targets already unreachable in the original graph. -/
theorem dominates_iff_not_reachable_delete {entry d v : V} (he : entry ≠ d) :
    Dominates adj entry d v ↔ ¬ Relation.ReflTransGen (Edge (deleteVertex adj d)) entry v := by
  constructor
  · intro h hr
    obtain ⟨tail, hc, hl⟩ := List.exists_isChain_cons_of_relationReflTransGen hr
    obtain ⟨hp, ha⟩ := (chain_delete_iff adj d entry he tail).mp hc
    exact ha ((List.mem_cons.mp (h tail hp hl)).resolve_left (Ne.symm he))
  · intro h tail hp hl
    by_contra ha
    exact h (List.relationReflTransGen_of_exists_isChain_cons tail
      ((chain_delete_iff adj d entry he tail).mpr
        ⟨hp, fun hm => ha (List.mem_cons_of_mem _ hm)⟩) hl)

/-- The executable query agrees with the all-walks specification on every target. -/
@[simp] theorem dominatesB_eq_true_iff [Fintype V] {entry d v : V} :
    dominatesB adj entry d v = true ↔ Dominates adj entry d v := by
  by_cases he : entry = d
  · subst d
    simp [dominatesB, Dominates]
  by_cases hv : v = d
  · subst v
    rw [dominatesB, ite_eq_left (Or.inr rfl), eq_self, true_iff]
    intro tail _ hl
    exact hl ▸ List.getLast_mem (l := entry :: tail) (by simp)
  · rw [dominates_iff_not_reachable_delete he]
    simp [dominatesB, he, hv, mem_dfs_visited_iff (adj := deleteVertex adj d) (le_refl _)]

end Cslib.Algorithms.Lean.DFS
