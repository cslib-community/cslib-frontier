/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.Drawing
public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfilesCollar
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Constant-factor coordinate bounds for the actual positive drawing compiler

Every emitted vertex and route point is bounded on the actual drawing lists. The source drawing
is dilated by `positiveScale = 1080000`, and every local replacement lies in a side-`540000`
square. The source
axis translation and the endpoint cuts fit within the same constant margin. These bounds do
not require geometric validity of the input drawing.

## Main results

* `positiveDrawing_fits`: an input rectangle of width `W` and height `H` yields an actual output
  rectangle with sides `positiveScale * (W + 1)` and `positiveScale * (H + 1)`.

## References

The explicit coordinate and finite-output bounds are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Graph.OrthogonalDrawing

open Cslib.Logic.PL Orthogonal

private def Rect (W H : ℕ) (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ W ∧ 0 ≤ p.2 ∧ p.2 ≤ H

private theorem getD_property {A : Type*} (P : A → Prop) (xs : List A) (fallback : A)
    (hf : P fallback) (hxs : ∀ x ∈ xs, P x) (i : ℕ) : P (xs.getD i fallback) := by
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hxs _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (not_lt.mp hi)]
    exact hf

private theorem zero_rect (W H : ℕ) : Rect W H (0, 0) := by simp [Rect]

private theorem input_position_bounds {d : Graph.OrthogonalDrawing} {W H : ℕ}
    (hd : Graph.drawingFits d W H) (G : Graph) (v : ℕ) :
    Rect W H (Graph.drawingPosition G d v) :=
  getD_property _ d.1 (0, 0) (zero_rect W H) hd.1 _

private theorem collar_outer_bounds (side : Fin 4) :
    Rect 540000 540000 (collarOuterPort side) := by
  unfold Rect
  fin_cases side <;> decide +kernel

private theorem collar_points_bounds : ∀ (s : PortAssignment) (i : Fin 3),
    ∀ q ∈ (collarRoutes s).getD i [], Rect 540000 540000 q := by
  unfold Rect
  decide +kernel

private theorem collarPoint_bounds (reflected : Bool) {q : Point}
    (hq : Rect 180000 180000 q) : Rect 540000 540000 (collarPoint reflected q) := by
  cases reflected <;> dsimp [Rect, collarPoint, collarOffset, mirrorPoint] at * <;> omega

private theorem local_variable_bounds (p : ClauseProfile) (s : PortAssignment) (v : ℕ) :
    Rect 540000 540000
      ((collaredPrefixGeometry (profilePrefixGeometry p) s).variablePosition v) := by
  refine getD_property _ _ _ (zero_rect _ _) ?_ v
  intro _ hq
  obtain ⟨⟨a, _⟩, ha, rfl⟩ := List.mem_map.mp hq
  split_ifs
  · exact collar_outer_bounds _
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.fst_mem_of_mem_zipIdx ha)
    exact collarPoint_bounds _ (by
      simpa only [Rect, Nat.cast_ofNat, LocalGeometry.variablePosition,
        List.getD_eq_getElem _ _ hj] using profile_prefix_variable_bounds p ⟨j, hj⟩)

private theorem local_clause_bounds (p : ClauseProfile) (s : PortAssignment) (i : ℕ) :
    Rect 540000 540000 ((collaredPrefixGeometry (profilePrefixGeometry p) s).clausePosition i) := by
  refine getD_property _ _ _ (zero_rect _ _) ?_ i
  intro _ hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
  exact collarPoint_bounds _ (by
    simpa only [Rect, Nat.cast_ofNat, LocalGeometry.clausePosition,
      List.getD_eq_getElem _ _ hj] using profile_prefix_clause_bounds p ⟨j, hj⟩)

private theorem local_route_bounds (p : ClauseProfile) (s : PortAssignment)
    {e : LocalIncidence}
    (he : e ∈ (collaredPrefixGeometry (profilePrefixGeometry p) s).incidenceRoutes) :
    ∀ q ∈ e.route, Rect 540000 540000 q := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  dsimp only [LocalIncidence.route]
  split_ifs
  · intro q hq
    rw [collarPrefixRoute, List.mem_append] at hq
    rcases hq with hq | hq
    · exact collarRoute_points_bounds _ (profile_prefix_incidence_points_bounds p f hf) q hq
    · exact collar_points_bounds s _ q (List.mem_reverse.mp (List.mem_of_mem_tail hq))
  · exact collarRoute_points_bounds _ (profile_prefix_incidence_points_bounds p f hf)

private theorem placed_point_bounds {W H : ℕ} {a q : Point}
    (ha : Rect W H a) (hq : Rect 540000 540000 q) :
    Rect (positiveScale * (W + 1)) (positiveScale * (H + 1)) (positiveScale • a + q) := by
  dsimp [Rect, positiveScale, Prod.smul_mk, Int.nsmul_eq_mul] at *
  omega

private theorem translation_bounds : Rect 540000 540000 positiveTranslation := by
  unfold Rect
  decide +kernel

/-- Every point of the actual inherited exterior route fits the enlarged source rectangle. -/
theorem positiveExterior_points_fits {φ : CNF ℕ} {d : Graph.OrthogonalDrawing} {W H : ℕ}
    (hd : Graph.drawingFits d W H) (i j : ℕ) :
    ∀ q ∈ positiveExterior φ d i j,
      0 ≤ q.1 ∧ q.1 ≤ positiveScale * (W + 1) ∧
        0 ≤ q.2 ∧ q.2 ≤ positiveScale * (H + 1) := by
  have hr : ∀ q ∈ sourceRoute (SAT.incidenceGraph φ) d (sourceEdgeIndex φ i j), Rect W H q := by
    have hin := getD_property _ d.2 [] (by simp) hd.2 (sourceEdgeIndex φ i j)
    unfold sourceRoute
    split
    · exact hin
    · exact fun q hq => hin q (List.mem_reverse.mp hq)
  intro _ hq
  obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hq
  change q ∈ cutStart positiveScale positiveRadius
    (sourceRoute (SAT.incidenceGraph φ) d (sourceEdgeIndex φ i j)) at hq'
  match hsrc : sourceRoute (SAT.incidenceGraph φ) d (sourceEdgeIndex φ i j) with
  | [] => simp [hsrc, cutStart, dilateRoute] at hq'
  | [a] =>
    rw [hsrc] at hq' hr
    obtain rfl : q = positiveScale • a := by simpa [cutStart, dilateRoute] using hq'
    exact placed_point_bounds (hr a List.mem_cons_self) translation_bounds
  | a :: b :: r =>
    rw [hsrc] at hq' hr
    change q ∈ cutPoint positiveScale positiveRadius a b ::
      dilateRoute positiveScale (b :: r) at hq'
    rcases List.mem_cons.mp hq' with rfl | hq'
    · have hcut : Rect 540000 540000 (positiveRadius • direction a b + positiveTranslation) := by
        rcases direction_unit a b with h | h | h | h <;>
          rw [h] <;> norm_num [Rect, positiveRadius, positiveTranslation, Prod.smul_mk]
      rw [show cutPoint positiveScale positiveRadius a b + positiveTranslation =
          positiveScale • a + (positiveRadius • direction a b + positiveTranslation) by
        simp [cutPoint, add_assoc]]
      exact placed_point_bounds (hr a List.mem_cons_self) hcut
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq'
      exact placed_point_bounds (hr x (List.mem_cons_of_mem _ hx)) translation_bounds

private theorem actual_variablePoint_bounds {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    {W H : ℕ} (hd : Graph.drawingFits d W H) (v : CNF.PositiveExactOneCompile.Variable ℕ) :
    Rect (positiveScale * (W + 1)) (positiveScale * (H + 1)) (positiveVariablePoint φ d v) := by
  refine getD_property _ _ _ (zero_rect _ _) ?_ _
  intro _ hq
  obtain ⟨⟨_, q⟩, htable, rfl⟩ := List.mem_map.mp hq
  rcases List.mem_append.mp htable with hsource | haux
  · obtain ⟨_, _, he⟩ := List.mem_map.mp hsource
    exact congrArg Prod.snd he ▸ placed_point_bounds (input_position_bounds hd _ _)
      translation_bounds
  · obtain ⟨⟨c, _⟩, _, hentry⟩ := List.mem_flatMap.mp haux
    obtain ⟨⟨(_ | _) | _, _⟩, _, he⟩ := List.mem_filterMap.mp hentry
    · simp at he
    all_goals
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj he)
      exact placed_point_bounds (input_position_bounds hd _ _)
        (local_variable_bounds (clauseProfile c) _ _)

/-- The actual emitted drawing expands both source grid sides by only a fixed factor. This
holds for every finite input drawing, including malformed inputs handled by default lookups. -/
theorem positiveDrawing_fits (φ : CNF ℕ) {d : Graph.OrthogonalDrawing} {W H : ℕ}
    (hd : Graph.drawingFits d W H) :
    Graph.drawingFits (positiveDrawing φ d) (positiveScale * (W + 1))
      (positiveScale * (H + 1)) := by
  constructor
  · intro q hq
    rcases List.mem_append.mp hq with hv | hc
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
      exact actual_variablePoint_bounds hd v
    · obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hc
      obtain ⟨⟨c, _⟩, _, hpc⟩ := List.mem_flatMap.mp hpc
      obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp hpc
      exact placed_point_bounds (input_position_bounds hd _ _)
        (local_clause_bounds (clauseProfile c) _ _)
  · intro r hr q hq
    obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨⟨c, i⟩, _, hpc⟩ := List.mem_flatMap.mp hpc
    obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have hlocal : ∀ q ∈ translate (positiveBoxOrigin φ d i) e.route,
        Rect (positiveScale * (W + 1)) (positiveScale * (H + 1)) q := by
      intro _ h
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
      rw [add_comm x]
      exact placed_point_bounds (input_position_bounds hd _ _)
        (local_route_bounds (clauseProfile c) _ (List.mem_filter.mp he).1 x hx)
    unfold positiveIncidenceRoute at hq
    split at hq
    · rcases List.mem_append.mp hq with hq | hq
      · exact hlocal q hq
      · exact positiveExterior_points_fits hd _ _ q (List.mem_of_mem_tail hq)
    · exact hlocal q hq

end Cslib.Complexity.SAT.ExactOne
