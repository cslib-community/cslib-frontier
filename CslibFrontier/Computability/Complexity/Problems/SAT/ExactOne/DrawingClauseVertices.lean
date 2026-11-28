/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.DrawingVertexBoxes
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# Distinct actual clause and variable vertices

The actual clause-position list follows the output formula. Certified inner profile vertices
are distinct, different boxes have different original clause owners, and original variable
centers cannot lie in any clause box.

## Main results

* `positiveClausePositions_nodup`: actual clause vertices have no repeated position.
* `positiveVariablePoint_ne_clause`: actual variables avoid every clause vertex.
* `positiveDrawing_positions_nodup`: all actual output graph vertices are distinct.

## References

These global vertex-separation proofs are original.
-/

public section

namespace Cslib.Complexity.SAT.ExactOne

open Graph.OrthogonalDrawing

open Cslib.Logic.PL Orthogonal

/-- The selected clause-position list has the exact actual profile clause length. -/
theorem clauseGeometry_clause_length (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) :
    (clauseGeometry φ d i c).clausePositions.length =
      (profileFormula (clauseProfile c)).length := by
  simpa only [clauseGeometry, collaredPrefixGeometry, profilePrefixGeometry,
    LocalGeometry.toPrefix, List.length_map] using profileGeometry_clause_length (clauseProfile c)

/-- A clause block lists precisely the translated local clause positions in order. -/
theorem positiveClauseBlock_positions (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) :
    ((positiveClauseBlock φ d i c).map fun pc => pc.point) =
      (clauseGeometry φ d i c).clausePositions.map (positiveBoxOrigin φ d i + ·) := by
  simp only [positiveClauseBlock, List.map_map, Function.comp_def]
  have he := congrArg (List.map (positiveBoxOrigin φ d i + ·))
    (List.map_getD_zipIdx (profileFormula (clauseProfile c))
      (clauseGeometry φ d i c).clausePositions (0, 0) (clauseGeometry_clause_length φ d i c))
  simpa only [List.map_map, Function.comp_def, LocalGeometry.clausePosition] using he

/-- Every actual local clause point lies in the common closed collar square. -/
theorem clauseGeometry_clause_bounds (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) {p : Point} (hp : p ∈ (clauseGeometry φ d i c).clausePositions) :
    InPositiveLocalBox p := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  apply collarPoint_in_positiveBox
  obtain ⟨j, rfl⟩ := List.get_of_mem hq
  simpa [LocalGeometry.clausePosition] using profile_prefix_clause_bounds (clauseProfile c) j

/-- A single actual clause box has distinct clause points. -/
theorem positiveClauseBlock_positions_nodup (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) :
    ((positiveClauseBlock φ d i c).map fun pc => pc.point).Nodup := by
  rw [positiveClauseBlock_positions]
  exact (((List.nodup_append.mp (profilePrefixGeometry_check (clauseProfile c)).1).2.1).map
    (collarPoint_injective _)).map fun _ _ => add_left_cancel

/-- A clause-box point identifies its original source-clause owner. -/
theorem positiveClauseBlock_positions_disjoint {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    {i j : ℕ} (hi : i < φ.length) (hj : j < φ.length) (hij : i ≠ j)
    (c c' : Clause ℕ) :
    List.Disjoint ((positiveClauseBlock φ d i c).map fun pc => pc.point)
      ((positiveClauseBlock φ d j c').map fun pc => pc.point) := by
  rw [positiveClauseBlock_positions, positiveClauseBlock_positions, List.disjoint_left]
  rintro p hpi hpj
  obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hpi
  obtain ⟨r, hr, hrp⟩ := List.mem_map.mp hpj
  exact hij <| Nat.add_left_cancel <| drawingPosition_injOn hd (sourceClause_declared φ hi)
    (sourceClause_declared φ hj) <| positiveBox_owner_injective
      (clauseGeometry_clause_bounds φ d i c hq) (clauseGeometry_clause_bounds φ d j c' hr)
      (hqp.trans hrp.symm)

/-- Every actual output clause has its own distinct displayed point. -/
theorem positiveClausePositions_nodup {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) :
    ((positivePlacedClauses φ d).map fun pc => pc.point).Nodup := by
  rw [positivePlacedClauses, List.map_flatMap]
  refine List.nodup_flatMap.mpr ⟨fun _ _ => positiveClauseBlock_positions_nodup _ _ _ _,
    List.pairwise_iff_getElem.mpr fun i j hi hj hij => ?_⟩
  have hi' : i < φ.length := by simpa only [List.length_zipIdx] using hi
  have hj' : j < φ.length := by simpa only [List.length_zipIdx] using hj
  simpa only [Function.onFun, List.getElem_zipIdx, Nat.zero_add] using
    positiveClauseBlock_positions_disjoint hd hi' hj' (Nat.ne_of_lt hij) φ[i] φ[j]

/-- Private local auxiliary points and actual local clause points are different. -/
theorem clauseGeometry_auxiliary_ne_clause (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) {v : CNF.PositiveExactOneCompile.Variable ℕ}
    (hv : v ∈ profileVariables (clauseProfile c)) (ha : ∀ n, v ≠ Sum.inl (Sum.inl n))
    {p : Point} (hp : p ∈ (clauseGeometry φ d i c).clausePositions) :
    (clauseGeometry φ d i c).variablePosition
      ((profileVariables (clauseProfile c)).idxOf v) ≠ p := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rw [clauseGeometry_auxiliary_point φ d i c hv ha]
  intro he
  have hidx := profileVariableIndex_lt (clauseProfile c) hv
  exact (List.nodup_append.mp (profilePrefixGeometry_check (clauseProfile c)).1).2.2 _
    (by rw [LocalGeometry.variablePosition, List.getD_eq_getElem _ _ hidx]
        exact List.getElem_mem hidx) _ hq (collarPoint_injective _ he)

/-- No actual source or private variable point coincides with an actual clause point. -/
theorem positiveVariablePoint_ne_clause {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    {v : CNF.PositiveExactOneCompile.Variable ℕ}
    (hv : v ∈ (CNF.PositiveExactOneCompile.rawFormula φ).vars) {p : Point}
    (hp : p ∈ (positivePlacedClauses φ d).map fun pc => pc.point) :
    positiveVariablePoint φ d v ≠ p := by
  obtain ⟨⟨c, i⟩, hc', hp⟩ := List.mem_flatMap.mp
    (by simpa only [positivePlacedClauses, List.map_flatMap] using hp)
  obtain ⟨q, hq, hqp⟩ := List.mem_map.mp (positiveClauseBlock_positions φ d i c ▸ hp)
  obtain ⟨hi, hci⟩ := List.mem_zipIdx' hc'
  obtain ⟨vp, hvp⟩ := positivePositionTable_covers φ d hv
  rw [positiveVariablePoint_of_mem φ d (positivePositionTable_keys_nodup φ d) hvp]
  intro he
  rcases List.mem_append.mp hvp with hsource | haux
  · obtain ⟨n, hn, hne⟩ := List.mem_map.mp hsource
    have hbox : InPositiveLocalBox positiveTranslation := by
      norm_num [InPositiveLocalBox, positiveTranslation, positiveRadius]
    have hlabels := drawingPosition_injOn hd
      (sourceVariable_declared φ (CNF.mem_distinctVars.mp hn)) (sourceClause_declared φ hi)
      (positiveBox_owner_injective hbox (clauseGeometry_clause_bounds φ d i c hq)
        ((congrArg Prod.snd hne).trans (he.trans hqp.symm)))
    have := List.idxOf_lt_length_of_mem hn
    omega
  · obtain ⟨c'', j, hcj, w, hw, hwa, _, hwp⟩ := positiveAuxiliaryPositions_origin φ d haux
    obtain ⟨hj, hcj'⟩ := List.mem_zipIdx' hcj
    have hplaced := hwp.symm.trans (he.trans hqp.symm)
    obtain rfl : j = i := Nat.add_left_cancel <| drawingPosition_injOn hd
      (sourceClause_declared φ hj) (sourceClause_declared φ hi) <|
      positiveBox_owner_injective (clauseGeometry_auxiliary_bounds φ d j c'' hw hwa)
        (clauseGeometry_clause_bounds φ d i c hq) hplaced
    obtain rfl : c'' = c := hcj'.trans hci.symm
    exact clauseGeometry_auxiliary_ne_clause φ d j c'' hw hwa hq (add_left_cancel hplaced)

/-- Every actual output graph vertex has a distinct displayed point. -/
theorem positiveDrawing_positions_nodup {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) :
    (positiveDrawing φ d).1.Nodup := by
  rw [positiveDrawing, List.nodup_append]
  refine ⟨positiveVariablePositions_nodup hd, positiveClausePositions_nodup hd, ?_⟩
  intro p hp q hq he
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
  exact positiveVariablePoint_ne_clause hd (CNF.mem_distinctVars.mp hv) hq he

end Cslib.Complexity.SAT.ExactOne
