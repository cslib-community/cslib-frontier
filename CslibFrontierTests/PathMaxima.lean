/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.PathMaxima
import Mathlib.Tactic.FinCases

/-!
# Tests for path maxima in a forest

A checked instance where every hypothesis of `Cslib.Query.pathMaxima_eq_some_iff` and
`Cslib.Query.countQueries_pathMaxima_le` holds: the path `0 — 1 — 2` with edge `0` of weight `0`
and edge `1` of weight `1`. The answer to `(0, 2)` is edge `1`, and the answer to `(0, 0)` is
`none`. Parallel edges and self-loops are cycles, so the acyclicity hypothesis excludes them.
-/

public section

namespace Cslib.Query.PathMaximaTests

open Cslib.Multigraph

/-- Vertices joined by `S` stay on the same side of a cut that no edge of `S` crosses. -/
theorem not_joins_of_cut {V E : Type} {ends : E → Sym2 V} {S : Set E} (P : Set V) {u v : V}
    (hu : u ∈ P) (hv : v ∉ P) (h : ∀ e ∈ S, ∀ x y, ends e = s(x, y) → x ∈ P → y ∈ P) :
    ¬Joins ends S u v := fun hJ => by
  obtain ⟨e, he, hcut⟩ := hJ.exists_mem_edgeCut hu hv
  obtain ⟨x, y, hxy, hx, hy⟩ := Graph.mem_edgeCut_iff.1 hcut
  exact hy (h e he x y hxy hx)

/-- The path `0 — 1 — 2`. -/
def pathEnds : Fin 2 → Sym2 (Fin 3)
  | 0 => s(0, 1)
  | 1 => s(1, 2)

/-- The path is acyclic. -/
theorem isAcyclic_pathEnds : IsAcyclic pathEnds (Finset.univ : Finset (Fin 2)) := by
  have h01 : ¬Joins pathEnds ((Finset.univ : Finset (Fin 2)) \ {0} : Set (Fin 2)) 0 1 := by
    refine not_joins_of_cut {0} rfl (by decide) fun f hf x y hxy hx => ?_
    rw [Set.mem_singleton_iff] at hx
    subst hx
    fin_cases f
    · exact absurd hf (by simp)
    · simp only [pathEnds] at hxy
      rcases Sym2.eq_iff.1 hxy with ⟨h, -⟩ | ⟨-, h⟩ <;> exact absurd h (by decide)
  have h12 : ¬Joins pathEnds ((Finset.univ : Finset (Fin 2)) \ {1} : Set (Fin 2)) 1 2 := by
    refine not_joins_of_cut {2}ᶜ (by decide) (by simp) fun f hf x y hxy hx hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    fin_cases f
    · simp only [pathEnds] at hxy
      rcases Sym2.eq_iff.1 hxy with ⟨-, h⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
    · exact absurd hf (by simp)
  refine isAcyclic_iff.2 fun e _ a b hab => ?_
  fin_cases e
  · simp only [pathEnds] at hab
    rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h01
    · exact fun h => h01 h.symm
  · simp only [pathEnds] at hab
    rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h12
    · exact fun h => h12 h.symm

/-- The weights: edge `e` weighs `e`. -/
def pathWeight (e : Fin 2) : ℕ := e

/-- The heaviest edge on the path from `0` to `2` is edge `1`. -/
example : (pathMaxima pathEnds Finset.univ [(0, 2), (0, 0)]).eval
    (LEQuery.oracleOf fun a b => decide (pathWeight a ≤ pathWeight b)) 0 2 = some 1 := by
  rw [pathMaxima_eq_some_iff (w := pathWeight) (fun a b h => Fin.ext h) (fun _ _ => rfl)
    isAcyclic_pathEnds (by simp)]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · exact (Joins.of_mem (ends := pathEnds)
      (S := {g | g ∈ Finset.univ ∧ pathWeight g ≤ pathWeight 1}) (e := 0)
      ⟨Finset.mem_univ _, by decide⟩ rfl).trans
      (Joins.of_mem (ends := pathEnds) (e := 1) ⟨Finset.mem_univ _, le_rfl⟩ rfl)
  · refine not_joins_of_cut {0, 1} (by simp) (by decide) fun f hf x y hxy hx => ?_
    have : f = 0 := by
      obtain ⟨-, hf⟩ := hf
      fin_cases f
      · rfl
      · exact absurd hf (by decide)
    subst this
    simp only [pathEnds, Fin.isValue] at hxy
    rcases Sym2.eq_iff.1 hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- A query with equal ends has no answer. -/
example (f : Fin 2) : (pathMaxima pathEnds Finset.univ [(0, 2), (0, 0)]).eval
    (LEQuery.oracleOf fun a b => decide (pathWeight a ≤ pathWeight b)) 0 0 ≠ some f := by
  rw [Ne, pathMaxima_eq_some_iff (w := pathWeight) (fun a b h => Fin.ext h) (fun _ _ => rfl)
    isAcyclic_pathEnds (by simp)]
  exact fun ⟨_, _, h⟩ => h (Joins.refl _)

/-- Two queries on the path cost at most `16 * 2 + 5 * 2` comparisons. -/
example : (pathMaxima pathEnds Finset.univ [(0, 2), (0, 0)]).countQueries
    (LEQuery.oracleOf fun a b => decide (pathWeight a ≤ pathWeight b)) ≤ 42 :=
  countQueries_pathMaxima_le (w := pathWeight) (fun _ _ => rfl) isAcyclic_pathEnds _

/-- Parallel edges form a cycle, so the forest hypothesis excludes them. -/
example : ¬IsAcyclic (fun _ : Fin 2 => (s(0, 1) : Sym2 (Fin 2))) (Finset.univ : Finset (Fin 2)) :=
  fun h => isAcyclic_iff.1 h 0 (by simp) 0 1 rfl
    (Joins.of_mem (e := 1) (by simp) rfl)

/-- A self-loop is a cycle, so the forest hypothesis excludes it. -/
example : ¬IsAcyclic (fun _ : Fin 1 => (s(0, 0) : Sym2 (Fin 1))) (Finset.univ : Finset (Fin 1)) :=
  fun h => isAcyclic_iff.1 h 0 (by simp) 0 0 rfl (Joins.refl _)

end Cslib.Query.PathMaximaTests
