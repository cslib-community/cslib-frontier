/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.Planar.PathData
public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalPath
public import CslibFrontier.Logics.Propositional.CNF.Occurrence
import CslibFrontier.Foundations.Data.List.Range
import Mathlib.Data.List.GetD

/-!
# Canonical paths of the actual planarization compiler

The executable compiler uses the canonical unit paths of the existing CNF incidence graph.
These shared certificates serve both continuous geometry and logical wire correctness.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.paths_eq_unitPaths`, `.occurrencePath_eq_unitPath`:
  exact agreement with the canonical graph layout.
* `Cslib.Complexity.SAT.PlanarCompile.occurrence_index_lt`, `.incidenceGraph_edge_idxOf`: valid
  literal-incidence indices and the edges they select.
* `Cslib.Complexity.SAT.PlanarCompile.occurrencePath_endpoints`, `.occurrencePath_nodup`:
  actual endpoints and uniqueness of all listed points.
* `Cslib.Complexity.SAT.PlanarCompile.occurrencePath_unit`, `.occurrencePath_last_unit`:
  unit adjacency, including the final-literal lookups.
* `Cslib.Complexity.SAT.PlanarCompile.occurrencePath_ne_nil`, `.occurrencePath_length_ge_two`:
  paths contain a genuine unit step before the original clause center.

* `Cslib.Complexity.SAT.PlanarCompile.occurrencePaths_eq_paths`: indexed source occurrences
  select exactly the emitted canonical paths in their original order.

## References

These certificates refer to the original canonical path construction in the imported compiler.
-/

public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- The executable compiler uses exactly the canonical unit paths certified by the layout API. -/
theorem paths_eq_unitPaths (φ : CNF ℕ) : paths φ = (SAT.incidenceGraph φ).unitPaths := rfl

/-- Literal-occurrence indexing selects the same path in the compiler and canonical layout. -/
theorem occurrencePath_eq_unitPath (φ : CNF ℕ) (o : Occurrence ℕ) :
    occurrencePath φ o =
      (SAT.incidenceGraph φ).unitPath ((Cslib.Logic.PL.occurrences φ).idxOf o) := rfl

/-- Every actual occurrence indexes an existing incidence edge. -/
theorem occurrence_index_lt {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    (Cslib.Logic.PL.occurrences φ).idxOf o < (SAT.incidenceGraph φ).edges.length := by
  simpa only [SAT.incidenceGraph, List.length_map] using List.idxOf_lt_length_of_mem ho

/-- The incidence edge indexed by an actual occurrence joins its variable to its clause. -/
theorem incidenceGraph_edge_idxOf {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    (SAT.incidenceGraph φ).edges[(Cslib.Logic.PL.occurrences φ).idxOf o]'(occurrence_index_lt ho) =
      (φ.distinctVars.idxOf o.lit.1, φ.distinctVars.length + o.clause) := by
  simp only [SAT.incidenceGraph, List.getElem_map]
  rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem ho)]

/-- Every actual occurrence path is duplicate-free, without an extra supplied path witness. -/
theorem occurrencePath_nodup {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) : (occurrencePath φ o).Nodup := by
  rw [occurrencePath_eq_unitPath]
  exact Graph.unitPath_nodup _ (fun _ => SAT.incidenceGraph_endpoints)
    (fun _ => SAT.incidenceGraph_loopless) (occurrence_index_lt ho)

/-- Every consecutive step in the actual compiler path is a unit grid displacement. -/
theorem occurrencePath_unit {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) {e : Point × Point}
    (he : e ∈ (occurrencePath φ o).consecutivePairs) : Orthogonal.length e.1 e.2 = 1 := by
  rw [occurrencePath_eq_unitPath] at he
  exact Graph.unitPath_unit _ (fun _ => SAT.incidenceGraph_endpoints)
    (fun _ => SAT.incidenceGraph_loopless) (occurrence_index_lt ho) he

/-- Every actual selected path contains at least one point. -/
theorem occurrencePath_ne_nil {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) : occurrencePath φ o ≠ [] := by
  rw [occurrencePath_eq_unitPath]
  exact Graph.unitPath_ne_nil _ (fun _ => SAT.incidenceGraph_endpoints)
    (fun _ => SAT.incidenceGraph_loopless) (occurrence_index_lt ho)

/-- Actual occurrence paths start at the variable's source-grid center and end at their clause. -/
theorem occurrencePath_endpoints {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    (occurrencePath φ o).head? = some (Layout.center (φ.distinctVars.idxOf o.lit.1)) ∧
      (occurrencePath φ o).getLast? = some (Layout.center (φ.distinctVars.length + o.clause)) := by
  have hi := occurrence_index_lt ho
  have h := Graph.unitPath_endpoints (SAT.incidenceGraph φ)
    (fun _ => SAT.incidenceGraph_endpoints) (fun _ => SAT.incidenceGraph_loopless) hi
  have he := incidenceGraph_edge_idxOf ho
  have hb := he ▸ SAT.incidenceGraph_bipartite (List.getElem_mem hi)
  simp only [Graph.edgeEndpoint, Bool.false_eq_true, ↓reduceIte, List.getD_eq_getElem _ _ hi,
    he] at h
  change (occurrencePath φ o).head? =
      some (Layout.center ((List.range _).idxOf (φ.distinctVars.idxOf o.lit.1))) ∧
    (occurrencePath φ o).getLast? =
      some (Layout.center ((List.range _).idxOf (φ.distinctVars.length + o.clause))) at h
  rwa [List.idxOf_range_of_lt (by omega), List.idxOf_range_of_lt hb.2.2] at h

/-- Actual literal paths contain at least one unit step, so final-literal lookups are in range. -/
theorem occurrencePath_length_ge_two {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) : 2 ≤ (occurrencePath φ o).length := by
  have hend := occurrencePath_endpoints ho
  have hi : φ.distinctVars.idxOf o.lit.1 < φ.distinctVars.length :=
    List.idxOf_lt_length_of_mem
      (CNF.mem_distinctVars.mpr (Cslib.Logic.PL.variable_mem_of_mem_occurrences ho))
  rcases hr : occurrencePath φ o with _ | ⟨p, _ | ⟨q, r⟩⟩
  · exact absurd hr (occurrencePath_ne_nil ho)
  · simp only [hr, List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hend
    have hx := congrArg Prod.fst (hend.1.symm.trans hend.2)
    simp only [Layout.center] at hx
    omega
  · simp

/-- The last two actual unit-path points are adjacent, including with the compiler's defaults. -/
theorem occurrencePath_last_unit {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    let r := occurrencePath φ o
    Orthogonal.length (r.getD (r.length - 2) (0, 0)) (r.getLastD (0, 0)) = 1 := by
  dsimp only
  let r := occurrencePath φ o
  have hrlen : 2 ≤ r.length := occurrencePath_length_ge_two ho
  apply occurrencePath_unit ho (e := (r.getD (r.length - 2) (0, 0), r.getLastD (0, 0)))
  rw [List.consecutivePairs]
  have hk : r.length - 2 < (r.zip r.tail).length := by grind
  have hpair : (r.zip r.tail)[r.length - 2] =
      (r.getD (r.length - 2) (0, 0), r.getLastD (0, 0)) := by
    rw [List.getElem_zip]
    refine Prod.ext (List.getD_eq_getElem _ _ (by omega)).symm ?_
    rw [List.getElem_tail, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
    change r[r.length - 2 + 1] = r[r.length - 1]
    congr 1
    omega
  rw [← hpair]
  exact List.getElem_mem hk

/-- Enumerating source occurrences selects all actual paths in their original order. -/
theorem occurrencePaths_eq_paths (φ : CNF ℕ) :
    (Cslib.Logic.PL.occurrences φ).map (occurrencePath φ) = paths φ := by
  refine List.ext_getElem (by simp [paths, SAT.incidenceGraph]) fun i hi hj => ?_
  rw [List.getElem_map, occurrencePath,
    (Cslib.Logic.PL.occurrences_nodup φ).idxOf_getElem i (by simpa using hi),
    List.getD_eq_getElem _ _ hj]

/-- An actual occurrence selects a member of the canonical path list. -/
theorem occurrencePath_mem_paths {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) : occurrencePath φ o ∈ paths φ := by
  rw [← occurrencePaths_eq_paths]
  exact List.mem_map_of_mem ho

end Cslib.Complexity.SAT.PlanarCompile
