/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.DrawingData
public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.DrawingCounts
public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.DrawingClauseVertices
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Actual occurrence indices of the positive drawing

The local clause records are assembled in the output formula's order. The occurrence-indexed
view in this module retains precisely the emitted position and route lists.

## Main definitions

* `positiveFormulaDrawing`: the actual compiler indexed by actual output occurrences.

## Main results

* `positiveFormulaDrawing_drawing`: the indexed view equals the emitted drawing.

## References

The assembly and indexing proofs are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

/-- Index the emitted route lists by actual output clause and literal positions. -/
def positiveFormulaDrawing (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    FormulaDrawing (CNF.PositiveExactOneCompile.rawFormula φ) where
  variablePoint := positiveVariablePoint φ d
  clausePoints := (positivePlacedClauses φ d).map fun pc => pc.point
  incidenceRoute := fun o =>
    ((positivePlacedClauses φ d).getD o.clause ([], (0, 0), [])).routes.getD o.pos []

private theorem placed_occurrence_routes (pcs : List PositivePlacedClause)
    (hc : ∀ pc ∈ pcs, pc.routes.length = pc.clause.length) :
    ((Cslib.Logic.PL.occurrences (pcs.map Prod.fst)).map fun o =>
      (pcs.getD o.clause ([], (0, 0), [])).routes.getD o.pos []) =
        pcs.flatMap fun pc => pc.routes := by
  have hflat : pcs.flatMap (fun pc => pc.routes) = pcs.zipIdx.flatMap (fun pc => pc.1.routes) := by
    simpa only [List.flatMap_map, Function.comp_def] using
      (congrArg (List.flatMap (·.routes)) (List.zipIdx_map_fst (l := pcs) (i := 0))).symm
  rw [Cslib.Logic.PL.occurrences, List.zipIdx_map, hflat]
  simp only [List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  refine List.map_congr_left fun ⟨pc, i⟩ hi => ?_
  obtain ⟨hi', hpc⟩ := List.mem_zipIdx' hi
  change pc.1.zipIdx.map (fun x => (pcs.getD i ([], (0, 0), [])).routes.getD x.2 []) = _
  rw [(List.getD_eq_getElem _ _ hi').trans hpc.symm]
  exact List.map_getD_zipIdx pc.1 pc.2.2 [] (hc pc (List.fst_mem_of_mem_zipIdx hi))

/-- The occurrence-indexed view has exactly the compiler's actual position and route lists. -/
theorem positiveFormulaDrawing_drawing (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    (positiveFormulaDrawing φ d).drawing = positiveDrawing φ d := by
  refine Prod.ext rfl ?_
  change ((Cslib.Logic.PL.occurrences (CNF.PositiveExactOneCompile.rawFormula φ)).map fun o =>
    ((positivePlacedClauses φ d).getD o.clause ([], (0, 0), [])).routes.getD o.pos []) = _
  rw [← positivePlacedClauses_formula φ d]
  exact placed_occurrence_routes _ fun _ => positivePlacedClauses_route_count φ d

/-- Each actual output occurrence selects its literal and route in the same placed clause. -/
theorem positiveFormulaDrawing_occurrence (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    {o : Occurrence (CNF.PositiveExactOneCompile.Variable ℕ)}
    (ho : o ∈ Cslib.Logic.PL.occurrences (CNF.PositiveExactOneCompile.rawFormula φ)) :
    ∃ pc ∈ positivePlacedClauses φ d,
      pc.point = (positiveFormulaDrawing φ d).clausePoints.getD o.clause (0, 0) ∧
        (o.lit, (positiveFormulaDrawing φ d).incidenceRoute o) ∈ pc.clause.zip pc.routes := by
  obtain ⟨hi, hj, hl⟩ := Cslib.Logic.PL.mem_occurrences.mp ho
  have hip : o.clause < (positivePlacedClauses φ d).length := by
    have h := congrArg List.length (positivePlacedClauses_formula φ d)
    simp only [List.length_map] at h
    omega
  let pc := (positivePlacedClauses φ d)[o.clause]
  have hpc : pc ∈ positivePlacedClauses φ d := List.getElem_mem hip
  have hec : pc.clause = (CNF.PositiveExactOneCompile.rawFormula φ)[o.clause] := by
    have h := congrArg (fun cs => cs.getD o.clause []) (positivePlacedClauses_formula φ d)
    simpa only [List.getD_eq_getElem _ _ (show o.clause <
      ((positivePlacedClauses φ d).map Prod.fst).length by simpa using hip), List.getElem_map,
      List.getD_eq_getElem _ _ hi] using h
  have hjp : o.pos < pc.clause.length := hec ▸ hj
  have hjr : o.pos < pc.routes.length := (positivePlacedClauses_route_count φ d hpc).symm ▸ hjp
  refine ⟨pc, hpc, ?_, ?_⟩
  · change pc.point = ((positivePlacedClauses φ d).map (·.point)).getD o.clause (0, 0)
    rw [List.getD_eq_getElem _ _ (by simpa using hip), List.getElem_map]
  · change (o.lit, ((positivePlacedClauses φ d).getD o.clause ([], (0, 0), [])).routes.getD
        o.pos []) ∈ pc.clause.zip pc.routes
    rw [List.getD_eq_getElem _ _ hip, List.getD_eq_getElem _ _ hjr,
      show o.lit = pc.clause[o.pos] by grind, ← List.getElem_zip]
    exact List.getElem_mem (by simp only [List.length_zip]; omega)

/-- Geometry transformations retain the literal-to-variable index of every profile incidence. -/
theorem clauseGeometry_literal_indices (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) (j : Fin 22)
    {l : Literal (CNF.PositiveExactOneCompile.Variable ℕ)} {e : LocalIncidence}
    (he : (l, e) ∈ ((profileFormula (clauseProfile c)).getD j.val []).zip
      ((clauseGeometry φ d i c).incidenceRoutes.filter fun e => e.clauseIndex == j.val)) :
    e.variableIndex = (profileVariables (clauseProfile c)).idxOf l.1 := by
  simp only [clauseGeometry, collaredPrefixGeometry, profilePrefixGeometry,
    LocalGeometry.toPrefix, List.filter_map, List.map_map, Function.comp_def,
    List.zip_map_right] at he
  obtain ⟨⟨lit, old⟩, hold, hle⟩ := List.mem_map.mp he
  have hli : lit = l := congrArg Prod.fst hle
  exact (congrArg (fun a => a.2.2.1) hle).symm.trans
    (hli ▸ profileGeometry_literal_indices (clauseProfile c) j hold)

/-- A paired actual literal and route comes from its certified local incidence record. -/
theorem positiveClauseBlock_incidence (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) {pc : PositivePlacedClause}
    (hpc : pc ∈ positiveClauseBlock φ d i c)
    {l : Literal (CNF.PositiveExactOneCompile.Variable ℕ)} {r : Route}
    (hlr : (l, r) ∈ pc.clause.zip pc.routes) :
    ∃ e ∈ (clauseGeometry φ d i c).incidenceRoutes,
      r = positiveIncidenceRoute φ d i c e ∧
        pc.point = positiveBoxOrigin φ d i + (clauseGeometry φ d i c).clausePosition e.clauseIndex ∧
        l.1 = profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) c
          ((profileVariables (clauseProfile c)).getD e.variableIndex (.inl (.inl 0))) := by
  obtain ⟨⟨cl, j⟩, hj, rfl⟩ := List.mem_map.mp hpc
  change (l, r) ∈ (cl.relabel _).zip (List.map _ _) at hlr
  simp only [Clause.relabel, List.zip_map_left, List.zip_map_right, List.map_map,
    Function.comp_def] at hlr
  obtain ⟨⟨lit, e⟩, hle, hnames⟩ := List.mem_map.mp hlr
  have hparts := List.of_mem_zip hle
  obtain ⟨he1, he2⟩ := List.mem_filter.mp hparts.2
  obtain ⟨hjlt, hcl⟩ := List.mem_zipIdx' hj
  have hbound := profileFormula_length_le (clauseProfile c)
  have hidx := clauseGeometry_literal_indices φ d i c ⟨j, by omega⟩
    (((List.getD_eq_getElem _ _ hjlt).trans hcl.symm) ▸ hle)
  have hlvar : lit.1 ∈ profileVariables (clauseProfile c) :=
    CNF.mem_distinctVars.mpr
      (CNF.mem_vars.mpr ⟨cl, List.fst_mem_of_mem_zipIdx hj, lit.2, hparts.1⟩)
  refine ⟨e, he1, (congrArg Prod.snd hnames).symm,
    (beq_iff_eq.mp he2 : e.clauseIndex = j) ▸ rfl, ?_⟩
  rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_idxOf hlvar, Option.getD_some]
  exact (congrArg (fun a => a.1.1) hnames).symm

/-- Every actual output occurrence has a source-clause owner and a certified local route. -/
theorem positiveFormulaDrawing_incidence (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    {o : Occurrence (CNF.PositiveExactOneCompile.Variable ℕ)}
    (ho : o ∈ Cslib.Logic.PL.occurrences (CNF.PositiveExactOneCompile.rawFormula φ)) :
    ∃ (i : ℕ) (hi : i < φ.length) (e : LocalIncidence),
      e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes ∧
        (positiveFormulaDrawing φ d).incidenceRoute o = positiveIncidenceRoute φ d i φ[i] e ∧
        (positiveFormulaDrawing φ d).clausePoints.getD o.clause (0, 0) =
          positiveBoxOrigin φ d i + (clauseGeometry φ d i φ[i]).clausePosition e.clauseIndex ∧
        o.lit.1 = profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) φ[i]
          ((profileVariables (clauseProfile φ[i])).getD e.variableIndex (.inl (.inl 0))) := by
  obtain ⟨pc, hpc, hp, hlr⟩ := positiveFormulaDrawing_occurrence φ d ho
  obtain ⟨⟨c, i⟩, hci, hpc⟩ := List.mem_flatMap.mp hpc
  obtain ⟨hi, hc⟩ := List.mem_zipIdx' hci
  obtain ⟨e, he, hr, hpos, hvar⟩ := positiveClauseBlock_incidence φ d i φ[i] (hc ▸ hpc) hlr
  exact ⟨i, hi, e, he, hr, hp.symm.trans hpos, hvar⟩

end Cslib.Complexity.SAT.ExactOne
