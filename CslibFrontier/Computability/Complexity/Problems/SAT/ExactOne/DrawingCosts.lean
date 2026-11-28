/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.DrawingFits
public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.DrawingRoutes
public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.DrawingCounts
public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfilesPrefix
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Logics.Propositional.CNF.Occurrence
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Linarith

/-!
# Constant-factor costs of the actual positive drawing compiler

Costs are counted on the actual emitted route lists. The source-slot sequence of every fixed
profile contains each source occurrence once. Consequently inherited exteriors are charged
once, while every original clause receives only a fixed local route, segment and wire budget.

## Main results

* `clauseGeometry_local_costs`: fixed segment and wire budgets for the actual local replacements.
* `positiveDrawing_costs`: constant-factor actual vertex, route, segment and wire bounds.

## References

The exact finite-list accounting and cost estimates are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

private def sourceSlot (p : ClauseProfile) (e : LocalIncidence) : Option ℕ :=
  match (profileVariables p).getD e.variableIndex (.inl (.inl 0)) with
  | .inl (.inl j) => some j
  | _ => none

private theorem prefix_sourceSlots (p : ClauseProfile) :
    ((profilePrefixGeometry p).incidenceRoutes.filterMap (sourceSlot p)) =
      (profileSource p).zipIdx.map Prod.snd := by
  fin_cases p <;> decide +kernel

private theorem prefix_routes_grouped (p : ClauseProfile) :
    (profileFormula p).zipIdx.flatMap (fun a =>
      (profilePrefixGeometry p).incidenceRoutes.filter fun e => e.1 == a.2) =
        (profilePrefixGeometry p).incidenceRoutes := by
  fin_cases p <;> decide +kernel

private theorem clause_sourceSlots (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) :
    ((clauseGeometry φ d i c).incidenceRoutes.filterMap (sourceSlot (clauseProfile c))) =
      (profileSource (clauseProfile c)).zipIdx.map Prod.snd := by
  simp only [clauseGeometry, collaredPrefixGeometry, List.filterMap_map]
  exact prefix_sourceSlots (clauseProfile c)

private theorem clause_routes_grouped (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) :
    (profileFormula (clauseProfile c)).zipIdx.flatMap (fun a =>
      (clauseGeometry φ d i c).incidenceRoutes.filter fun e => e.1 == a.2) =
        (clauseGeometry φ d i c).incidenceRoutes := by
  let g := profilePrefixGeometry (clauseProfile c)
  let s := clausePorts φ d i
  let f (e : LocalIncidence) : LocalIncidence :=
    (e.clauseIndex, e.variableIndex, if e.variableIndex ∈ g.terminalVariables then
      collarPrefixRoute s (terminalIndex g e.variableIndex) e.route
      else collarRoute (collarReflected s) e.route)
  simpa only [clauseGeometry, collaredPrefixGeometry, List.map_flatMap, List.filter_map,
    Function.comp_def] using congrArg (List.map f) (prefix_routes_grouped (clauseProfile c))

private theorem sum_option_weights {A : Type*} (xs : List A) (slot : A → Option ℕ)
    (f : ℕ → ℕ) :
    (xs.map fun a => (slot a).elim 0 f).sum = ((xs.filterMap slot).map f).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : slot a <;> simp [h, ih]

private theorem clause_source_weight (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (i : ℕ) (c : Clause ℕ) (hw : c.length ≤ 3) (f : ℕ → ℕ) :
    ((clauseGeometry φ d i c).incidenceRoutes.map fun e =>
      (sourceSlot (clauseProfile c) e).elim 0 f).sum =
        (c.zipIdx.map fun a => f a.2).sum := by
  rw [sum_option_weights, clause_sourceSlots, List.zipIdx_map_snd, profileSource_length c hw,
    ← List.zipIdx_map_snd, List.map_map]
  rfl

private theorem positiveDrawing_weight (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    (weight : Route → ℕ) :
    (((positiveDrawing φ d).2).map weight).sum =
      (φ.zipIdx.map fun a => ((clauseGeometry φ d a.2 a.1).incidenceRoutes.map fun e =>
        weight (positiveIncidenceRoute φ d a.2 a.1 e)).sum).sum := by
  have hlocal (c : Clause ℕ) (i : ℕ) :
      (((positiveClauseBlock φ d i c).flatMap fun pc => pc.routes).map weight).sum =
        ((clauseGeometry φ d i c).incidenceRoutes.map fun e =>
          weight (positiveIncidenceRoute φ d i c e)).sum := by
    have he := congrArg (fun es => (es.map fun e =>
      weight (positiveIncidenceRoute φ d i c e)).sum) (clause_routes_grouped φ d i c)
    simpa only [positiveClauseBlock, PositivePlacedClause.routes, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def] using he
  change (((positivePlacedClauses φ d).flatMap fun pc => pc.routes).map weight).sum = _
  rw [positivePlacedClauses, List.flatMap_assoc, List.sum_map_flatMap]
  exact congrArg List.sum (List.map_congr_left fun a _ => hlocal a.1 a.2)

private theorem segmentCount_eq (r : Route) : r.consecutivePairs.length = r.length - 1 := by
  simp only [List.consecutivePairs, List.length_zip, List.length_tail]
  omega

/-- The actual collared local template has bounded total segment and Manhattan-wire costs.
The conservative collar allowance is charged once per local incidence. -/
theorem clauseGeometry_local_costs {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) (c : Clause ℕ) :
    (((clauseGeometry φ d i c).incidenceRoutes.map fun e => e.route.consecutivePairs.length).sum ≤
      575) ∧
      (((clauseGeometry φ d i c).incidenceRoutes.map fun e => wireLength e.route).sum ≤
        40252600) := by
  let p := clauseProfile c
  let g := profilePrefixGeometry p
  let s := clausePorts φ d i
  have hs := (clausePorts_spec hd hi).1
  have hg := profilePrefixGeometry_check p
  obtain ⟨hm0, hm1, hlen, hsc0, hwc, hm2⟩ := profilePrefixGeometry_costs p
  have hlocal (e : LocalIncidence) (he : e ∈ g.incidenceRoutes) :
      (profileCollarRoute p s e).consecutivePairs.length ≤
        e.route.consecutivePairs.length + 7 ∧
      wireLength (profileCollarRoute p s e) ≤ wireLength e.route + 600000 := by
    unfold profileCollarRoute
    split_ifs with ht
    · obtain ⟨h0, h1, h2, hend⟩ := LocalGeometry.prefix_incidence_endpoints hg he
      rw [profile_prefix_terminal_endpoint p e.variableIndex ht] at hend
      obtain ⟨hc1, hc2⟩ := collar_route_costs s hs (terminalIndex g e.variableIndex)
      rw [consecutivePairs_length_collarPrefixRoute hs hend,
        wireLength_collarPrefixRoute hs hend]
      exact ⟨Nat.add_le_add_left hc1 _, Nat.add_le_add_left hc2 _⟩
    · rw [consecutivePairs_length_collarRoute, wireLength_collarRoute]
      omega
  have hsc : ((g.incidenceRoutes.map fun e => e.route.consecutivePairs.length).sum) ≤ 113 := by
    simpa only [segmentCount_eq] using hsc0
  have hs' := List.sum_le_sum fun e he => (hlocal e he).1
  have hw' := List.sum_le_sum fun e he => (hlocal e he).2
  rw [List.sum_map_add, List.map_const', List.sum_replicate_nat] at hs' hw'
  dsimp only [g] at hs' hw' hsc
  simp only [clauseGeometry, collaredPrefixGeometry, List.map_map, Function.comp_def]
  exact ⟨hs'.trans (by omega), hw'.trans (by omega)⟩

private theorem positiveIncidenceRoute_weight {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) {e : LocalIncidence}
    (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes) (weight : Route → ℕ)
    (htranslate : ∀ v r, weight (translate v r) = weight r)
    (hjoin : ∀ {r₁ r₂ : Route} {q : Point}, r₁.getLast? = some q → r₂.head? = some q →
      weight (r₁ ++ r₂.tail) = weight r₁ + weight r₂) :
    weight (positiveIncidenceRoute φ d i φ[i] e) = weight e.route +
      (sourceSlot (clauseProfile φ[i]) e).elim 0
        (fun j => weight (positiveExterior φ d i j)) := by
  unfold positiveIncidenceRoute sourceSlot
  generalize hget :
    (profileVariables (clauseProfile φ[i])).getD e.variableIndex (.inl (.inl 0)) = v
  rcases v with (j | _) | _
  · obtain ⟨q, hlast, hhead⟩ := positiveIncidenceRoute_join_endpoints hd hi
      (profilePrefixGeometry_check _) he hget
    change weight (positiveStem φ d i e ++ (positiveExterior φ d i j).tail) =
      weight e.route + weight (positiveExterior φ d i j)
    rw [hjoin hlast hhead, positiveStem, htranslate]
  all_goals simp [htranslate]

private theorem sourceEdgeIndex_occurrence (φ : CNF ℕ) {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    sourceEdgeIndex φ o.clause o.pos = (Cslib.Logic.PL.occurrences φ).idxOf o := by
  obtain ⟨hi, hj, he⟩ := Cslib.Logic.PL.mem_occurrences.mp ho
  simp only [sourceEdgeIndex, sourceOccurrence, List.getD_eq_getElem _ _ hi,
    List.getD_eq_getElem _ _ hj, ← he]

private theorem source_edge_weight_sum {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) (weight : Route → ℕ) :
    (φ.zipIdx.map fun a => (a.1.zipIdx.map fun l =>
      weight (d.2.getD (sourceEdgeIndex φ a.2 l.2) [])).sum).sum = (d.2.map weight).sum := by
  have hlen : (Cslib.Logic.PL.occurrences φ).length = d.2.length := by
    simpa only [SAT.incidenceGraph, List.length_map] using hd.edgeCount.symm
  have hlist : ((Cslib.Logic.PL.occurrences φ).map fun o =>
      weight (d.2.getD ((Cslib.Logic.PL.occurrences φ).idxOf o) [])) = d.2.map weight := by
    refine List.ext_getElem (by simp only [List.length_map, hlen]) fun i hi hj => ?_
    simp only [List.length_map] at hi hj
    rw [List.getElem_map, (Cslib.Logic.PL.occurrences_nodup φ).idxOf_getElem i hi,
      List.getD_eq_getElem _ _ hj, List.getElem_map]
  calc
    _ = ((Cslib.Logic.PL.occurrences φ).map fun o =>
        weight (d.2.getD (sourceEdgeIndex φ o.clause o.pos) [])).sum := by
      rw [Cslib.Logic.PL.occurrences, List.sum_map_flatMap]
      simp only [List.map_map, Function.comp_def]
    _ = ((Cslib.Logic.PL.occurrences φ).map fun o =>
        weight (d.2.getD ((Cslib.Logic.PL.occurrences φ).idxOf o) [])).sum := by
      exact congrArg _ (List.map_congr_left fun _ ho => by rw [sourceEdgeIndex_occurrence φ ho])
    _ = _ := congrArg List.sum hlist

private theorem exterior_segment_sum {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) :
    (φ.zipIdx.map fun a => (a.1.zipIdx.map fun l =>
      (positiveExterior φ d a.2 l.2).consecutivePairs.length).sum).sum =
        Graph.drawingSegmentCount d := by
  simp only [positiveExterior, consecutivePairs_length_translate, exteriorRoute_segmentCount]
  exact source_edge_weight_sum hd (fun r : Route => r.consecutivePairs.length)

private theorem exterior_wire_sum_le {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) :
    (φ.zipIdx.map fun a => (a.1.zipIdx.map fun l =>
      wireLength (positiveExterior φ d a.2 l.2)).sum).sum ≤
        1080000 * Graph.drawingWireLength d := by
  calc
    _ ≤ (φ.zipIdx.map fun a => (a.1.zipIdx.map fun l =>
        1080000 * wireLength (d.2.getD (sourceEdgeIndex φ a.2 l.2) [])).sum).sum := by
      refine List.sum_le_sum fun ⟨c, i⟩ hci => ?_
      obtain ⟨hi, hc⟩ := List.mem_zipIdx' hci
      rw [hc]
      refine List.sum_le_sum fun ⟨l, j⟩ hlj => ?_
      have hj : j < φ[i].length := (List.mem_zipIdx' hlj).1
      have hw : wireLength (positiveExterior φ d i j) + positiveRadius =
          1080000 * wireLength (d.2.getD (sourceEdgeIndex φ i j) []) := by
        simpa only [positiveExterior, wireLength_translate, positiveScale] using
          exteriorRoute_wireLength hd (sourceEdgeIndex_lt φ hi hj)
            (by decide : positiveRadius < positiveScale)
      exact Nat.le.intro hw
    _ = 1080000 * (φ.zipIdx.map fun a => (a.1.zipIdx.map fun l =>
        wireLength (d.2.getD (sourceEdgeIndex φ a.2 l.2) [])).sum).sum := by
      simp only [List.sum_map_mul_left]
    _ = _ := by rw [source_edge_weight_sum hd]; rfl

/-- The actual route list has at most 507 incidences per original clause. -/
theorem positiveDrawing_routeCount (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    (positiveDrawing φ d).2.length ≤ 507 * φ.length := by
  rw [positiveDrawing_edgeCount, SAT.length_edges_incidenceGraph]
  exact CNF.PositiveExactOneCompile.length_vars_formula_le φ

/-- The actual vertex list has at most 676 vertices per original clause. -/
theorem positiveDrawing_vertexCount_le (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) :
    (positiveDrawing φ d).1.length ≤ 676 * φ.length := by
  rw [positiveDrawing_vertexCount, SAT.length_vertices_incidenceGraph]
  linarith [(CNF.PositiveExactOneCompile.formula φ).numVars_le_length_vars,
    CNF.PositiveExactOneCompile.length_vars_formula_le φ,
    CNF.PositiveExactOneCompile.length_formula_le φ]

private theorem positiveDrawing_weight_le {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    (hw : ∀ c ∈ φ, c.length ≤ 3) (weight : Route → ℕ) (C : ℕ)
    (htranslate : ∀ v r, weight (translate v r) = weight r)
    (hjoin : ∀ {r₁ r₂ : Route} {q : Point}, r₁.getLast? = some q → r₂.head? = some q →
      weight (r₁ ++ r₂.tail) = weight r₁ + weight r₂)
    (hloc : ∀ i (hi : i < φ.length),
      ((clauseGeometry φ d i φ[i]).incidenceRoutes.map fun e => weight e.route).sum ≤ C) :
    (((positiveDrawing φ d).2).map weight).sum ≤ C * φ.length +
      (φ.zipIdx.map fun a => (a.1.zipIdx.map fun l =>
        weight (positiveExterior φ d a.2 l.2)).sum).sum := by
  rw [positiveDrawing_weight]
  calc
    _ ≤ (φ.zipIdx.map fun a => C + (a.1.zipIdx.map fun l =>
        weight (positiveExterior φ d a.2 l.2)).sum).sum := by
      refine List.sum_le_sum fun ⟨c, i⟩ hci => ?_
      obtain ⟨hi, hc⟩ := List.mem_zipIdx' hci
      rw [hc, List.map_congr_left fun e he =>
          positiveIncidenceRoute_weight hd hi he weight htranslate hjoin,
        List.sum_map_add, clause_source_weight φ d i φ[i] (hw _ (List.getElem_mem hi))]
      exact Nat.add_le_add_right (hloc i hi) _
    _ = _ := by simp [List.sum_map_add, List.map_const', Nat.mul_comm]

/-- Each original source segment is retained once; every original clause contributes only
a fixed local segment allowance. -/
theorem positiveDrawing_segmentCount {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    (hw : ∀ c ∈ φ, c.length ≤ 3) :
    Graph.drawingSegmentCount (positiveDrawing φ d) ≤
      575 * φ.length + Graph.drawingSegmentCount d := by
  rw [Graph.drawingSegmentCount, ← exterior_segment_sum hd]
  exact positiveDrawing_weight_le hd hw (fun r => r.consecutivePairs.length) 575
    consecutivePairs_length_translate
    (fun hlast hhead => by rw [consecutivePairs_join hlast hhead, List.length_append])
    (fun i hi => (clauseGeometry_local_costs hd hi φ[i]).1)

/-- Each inherited source wire is charged once after the fixed dilation. The rest is a
constant local wire allowance per original clause. -/
theorem positiveDrawing_wireLength {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    (hw : ∀ c ∈ φ, c.length ≤ 3) :
    Graph.drawingWireLength (positiveDrawing φ d) ≤
      40252600 * φ.length + 1080000 * Graph.drawingWireLength d := by
  rw [Graph.drawingWireLength]
  exact (positiveDrawing_weight_le hd hw wireLength 40252600 wireLength_translate
    (fun hlast hhead => wireLength_join hlast hhead)
    (fun i hi => (clauseGeometry_local_costs hd hi φ[i]).2)).trans
    (Nat.add_le_add_left (exterior_wire_sum_le hd) _)

/-- All actual emitted drawing costs grow by only fixed factors. Inherited exterior incidences
are counted exactly once, independently of source variable repetitions. -/
theorem positiveDrawing_costs {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d)
    (hw : ∀ c ∈ φ, c.length ≤ 3) :
    (positiveDrawing φ d).1.length ≤ 676 * φ.length ∧
      (positiveDrawing φ d).2.length ≤ 507 * φ.length ∧
      Graph.drawingSegmentCount (positiveDrawing φ d) ≤
        575 * φ.length + Graph.drawingSegmentCount d ∧
      Graph.drawingWireLength (positiveDrawing φ d) ≤
        40252600 * φ.length + 1080000 * Graph.drawingWireLength d :=
  ⟨positiveDrawing_vertexCount_le φ d, positiveDrawing_routeCount φ d,
    positiveDrawing_segmentCount hd hw, positiveDrawing_wireLength hd hw⟩

end Cslib.Complexity.SAT.ExactOne
