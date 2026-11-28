/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.DrawingVertexGeometry
public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfilesPrefix
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# Separation of actual vertices in different clause boxes

The dilation separates the full closed boxes around distinct source vertices. Inside one box,
the certified profile and its common injective affine placement distinguish every actual
auxiliary and clause vertex. Inherited source-variable vertices stay at their shared centers.

## Main results

* `positiveVariablePoint_injective`: occurring output variables occupy distinct actual points.
* `positiveVariablePositions_nodup`: the actual variable-position prefix has no repetitions.

## References

These global placement and injectivity arguments are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Graph.OrthogonalDrawing

open Cslib.Logic.PL Orthogonal

/-- The common closed coordinate bounds of a local collared template. -/
def InPositiveLocalBox (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 540000 ∧ 0 ≤ p.2 ∧ p.2 ≤ 540000

/-- Affine placement sends every point of the side-180000 template square into the closed collar
box; `collarPoint_in_innerBox` gives the stronger inner-square bounds. -/
theorem collarPoint_in_positiveBox (reflected : Bool) {p : Point}
    (hp : 0 ≤ p.1 ∧ p.1 ≤ 180000 ∧ 0 ≤ p.2 ∧ p.2 ≤ 180000) :
    InPositiveLocalBox (collarPoint reflected p) := by
  have hb := collarPoint_in_innerBox reflected hp
  norm_num [inPointBox, realPoint] at hb
  have : (180000 : ℤ) ≤ (collarPoint reflected p).1 ∧ (collarPoint reflected p).1 ≤ 360000 ∧
      180000 ≤ (collarPoint reflected p).2 ∧ (collarPoint reflected p).2 ≤ 360000 := by
    exact_mod_cast hb
  unfold InPositiveLocalBox
  omega

/-- Every private actual variable lies in its own fixed collared box. -/
theorem clauseGeometry_auxiliary_bounds (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) {v : CNF.PositiveExactOneCompile.Variable ℕ}
    (hv : v ∈ profileVariables (clauseProfile c)) (ha : ∀ n, v ≠ Sum.inl (Sum.inl n)) :
    InPositiveLocalBox ((clauseGeometry φ d i c).variablePosition
      ((profileVariables (clauseProfile c)).idxOf v)) := by
  rw [clauseGeometry_auxiliary_point φ d i c hv ha]
  exact collarPoint_in_positiveBox _
    (profile_prefix_variable_bounds (clauseProfile c) ⟨_, profileVariableIndex_lt _ hv⟩)

/-- Equal placed points in closed local boxes determine the same integer source center. -/
theorem positiveBox_owner_injective {a b q r : Point} (hq : InPositiveLocalBox q)
    (hr : InPositiveLocalBox r) (he : positiveScale • a + q = positiveScale • b + r) : a = b := by
  rcases a, b, q, r with ⟨⟨ax, ay⟩, ⟨bx, by'⟩, ⟨qx, qy⟩, ⟨rx, ry⟩⟩
  simp only [positiveScale, Prod.smul_mk, Int.nsmul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq] at he
  simp only [InPositiveLocalBox] at hq hr
  exact Prod.ext (by omega) (by omega)

/-- A source clause's incidence-graph vertex is declared. -/
theorem sourceClause_declared (φ : CNF ℕ) {i : ℕ} (hi : i < φ.length) :
    φ.distinctVars.length + i ∈ (SAT.incidenceGraph φ).vertices := by
  simp only [SAT.incidenceGraph, List.mem_range]
  omega

/-- A used source variable's incidence-graph vertex is declared. -/
theorem sourceVariable_declared (φ : CNF ℕ) {v : ℕ} (hv : v ∈ φ.vars) :
    φ.distinctVars.idxOf v ∈ (SAT.incidenceGraph φ).vertices := by
  have hi := List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
  simp only [SAT.incidenceGraph, List.mem_range]
  omega

/-- Two private profile variables in one actual clause box have different points. -/
theorem clauseGeometry_auxiliary_injective (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) {v w : CNF.PositiveExactOneCompile.Variable ℕ}
    (hv : v ∈ profileVariables (clauseProfile c)) (hw : w ∈ profileVariables (clauseProfile c))
    (hva : ∀ n, v ≠ Sum.inl (Sum.inl n)) (hwa : ∀ n, w ≠ Sum.inl (Sum.inl n))
    (he : (clauseGeometry φ d i c).variablePosition ((profileVariables (clauseProfile c)).idxOf v) =
      (clauseGeometry φ d i c).variablePosition ((profileVariables (clauseProfile c)).idxOf w)) :
    v = w := by
  rw [clauseGeometry_auxiliary_point φ d i c hv hva,
    clauseGeometry_auxiliary_point φ d i c hw hwa] at he
  exact (List.idxOf_inj hv).mp (prefix_variablePoint_injective
    (profilePrefixGeometry_check (clauseProfile c)) (profileVariableIndex_lt _ hv)
    (profileVariableIndex_lt _ hw) (collarPoint_injective _ he))

/-- Equal points of two fresh-variable table entries have the same actual variable key. -/
theorem positiveAuxiliaryPositions_point_injective {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    {v w : CNF.PositiveExactOneCompile.Variable ℕ} {p q : Point}
    (hv : (v, p) ∈ positiveAuxiliaryPositions φ d)
    (hw : (w, q) ∈ positiveAuxiliaryPositions φ d) (he : p = q) : v = w := by
  obtain ⟨c, i, hci, a, ha, hauxa, hva, hpa⟩ := positiveAuxiliaryPositions_origin φ d hv
  obtain ⟨c', j, hcj, b, hb, hauxb, hwb, hqb⟩ := positiveAuxiliaryPositions_origin φ d hw
  obtain ⟨hi, hci'⟩ := List.mem_zipIdx' hci
  obtain ⟨hj, hcj'⟩ := List.mem_zipIdx' hcj
  have hplaced := hpa.symm.trans (he.trans hqb)
  obtain rfl : i = j := Nat.add_left_cancel (drawingPosition_injOn hd
    (sourceClause_declared φ hi) (sourceClause_declared φ hj)
    (positiveBox_owner_injective (clauseGeometry_auxiliary_bounds φ d i c ha hauxa)
      (clauseGeometry_auxiliary_bounds φ d j c' hb hauxb) hplaced))
  obtain rfl : c = c' := hci'.trans hcj'.symm
  rw [hva, hwb, clauseGeometry_auxiliary_injective φ d i c ha hb hauxa hauxb
    (add_left_cancel hplaced)]

/-- A shared source-variable point cannot coincide with any private clause-box point. -/
theorem positiveSourceAuxiliary_positions_disjoint {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    {v w : CNF.PositiveExactOneCompile.Variable ℕ} {p q : Point}
    (hv : (v, p) ∈ positiveSourcePositions φ d)
    (hw : (w, q) ∈ positiveAuxiliaryPositions φ d) : p ≠ q := by
  obtain ⟨n, hn, hv⟩ := List.mem_map.mp hv
  obtain ⟨c, i, hci, a, ha, hauxa, _, hqa⟩ := positiveAuxiliaryPositions_origin φ d hw
  intro he
  have hbox : InPositiveLocalBox positiveTranslation := by
    norm_num [InPositiveLocalBox, positiveTranslation, positiveRadius]
  have hlabels := drawingPosition_injOn hd
    (sourceVariable_declared φ (CNF.mem_distinctVars.mp hn))
    (sourceClause_declared φ (List.mem_zipIdx' hci).1)
    (positiveBox_owner_injective hbox (clauseGeometry_auxiliary_bounds φ d i c ha hauxa)
      ((congrArg Prod.snd hv).trans (he.trans hqa)))
  have := List.idxOf_lt_length_of_mem hn
  omega

/-- Shared source-position table entries are injective in their actual source-variable names. -/
theorem positiveSourcePositions_point_injective {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    {v w : CNF.PositiveExactOneCompile.Variable ℕ} {p q : Point}
    (hv : (v, p) ∈ positiveSourcePositions φ d)
    (hw : (w, q) ∈ positiveSourcePositions φ d) (he : p = q) : v = w := by
  obtain ⟨n, hn, hv⟩ := List.mem_map.mp hv
  obtain ⟨m, hm, hw⟩ := List.mem_map.mp hw
  have hcenters := nsmul_point_injective (by decide : positiveScale ≠ 0)
    (add_right_cancel ((congrArg Prod.snd hv).trans (he.trans (congrArg Prod.snd hw).symm)))
  obtain rfl : n = m := (List.idxOf_inj hn).mp (drawingPosition_injOn hd
    (sourceVariable_declared φ (CNF.mem_distinctVars.mp hn))
    (sourceVariable_declared φ (CNF.mem_distinctVars.mp hm)) hcenters)
  exact (congrArg Prod.fst hv).symm.trans (congrArg Prod.fst hw)

/-- The actual position-table map is injective on all its entries. -/
theorem positivePositionTable_point_injective {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    {v w : CNF.PositiveExactOneCompile.Variable ℕ} {p q : Point}
    (hv : (v, p) ∈ positivePositionTable φ d) (hw : (w, q) ∈ positivePositionTable φ d)
    (he : p = q) : v = w := by
  rcases List.mem_append.mp hv with hv | hv <;> rcases List.mem_append.mp hw with hw | hw
  · exact positiveSourcePositions_point_injective hd hv hw he
  · exact False.elim (positiveSourceAuxiliary_positions_disjoint hd hv hw he)
  · exact False.elim (positiveSourceAuxiliary_positions_disjoint hd hw hv he.symm)
  · exact positiveAuxiliaryPositions_point_injective hd hv hw he

/-- Distinct occurring output variables occupy distinct actual positions. -/
theorem positiveVariablePoint_injective {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    {v w : CNF.PositiveExactOneCompile.Variable ℕ}
    (hv : v ∈ (CNF.PositiveExactOneCompile.rawFormula φ).vars)
    (hw : w ∈ (CNF.PositiveExactOneCompile.rawFormula φ).vars)
    (he : positiveVariablePoint φ d v = positiveVariablePoint φ d w) : v = w := by
  obtain ⟨p, hp⟩ := positivePositionTable_covers φ d hv
  obtain ⟨q, hq⟩ := positivePositionTable_covers φ d hw
  have hkeys := positivePositionTable_keys_nodup φ d
  rw [positiveVariablePoint_of_mem φ d hkeys hp, positiveVariablePoint_of_mem φ d hkeys hq] at he
  exact positivePositionTable_point_injective hd hp hq he

/-- The actual variable-position prefix of the emitted drawing has no repetitions. -/
theorem positiveVariablePositions_nodup {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) :
    ((CNF.PositiveExactOneCompile.rawFormula φ).distinctVars.map
      (positiveVariablePoint φ d)).Nodup := by
  exact (CNF.nodup_distinctVars _).map_on fun _ hv _ hw =>
    positiveVariablePoint_injective hd (CNF.mem_distinctVars.mp hv) (CNF.mem_distinctVars.mp hw)

end Cslib.Complexity.SAT.ExactOne
