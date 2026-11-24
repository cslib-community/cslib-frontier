/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary clients of actual crossing neighborhoods)

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.CrossingNeighborhoods
import CslibFrontierTests.RotationReferenceDrawing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
Both the library API and existing public test fixture are ordinarily imported.
No private library declaration is accessed. The fixture's loop, parallel
occurrences and isolate are retained. Two exact affine contacts exercise positive
radii, disjoint closed balls, vertex exclusion and nonincident-support exclusion.
-/

public section

namespace Cslib.Tests.RotationCrossingNeighborhoods

open Cslib.Polygonal Cslib.Complexity.Graph Cslib.Complexity.Graph.RotationRecognition

private abbrev input := RotationReferenceDrawing.input

private theorem valid_input : Valid input := validate_eq_true_iff input |>.mp (by decide +kernel)

private def edge (i : Fin 9) : Fin (subdivisionGraph input).edges.length :=
  ⟨i.val, by change i.val < 9; exact i.isLt⟩

private theorem fixture_point (v : ℕ) (hv : v < 9) :
    referencePoint input v = parabolaPoint (v : ℝ) := by
  have hord : referenceOrder input = [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide +kernel
  have h : ∀ i : Fin 9, referencePoint input i.val = parabolaPoint (i.val : ℝ) := by
    intro i
    unfold referencePoint
    rw [hord]
    fin_cases i <;> norm_num
  exact h ⟨v, hv⟩

private theorem fixture_contacts :
    (⟨3 / 2, 9 / 2⟩ : ℂ) ∈ openSegment ℝ ((referenceDrawing input).route (edge 0)).start
      ((referenceDrawing input).route (edge 0)).finish ∧
    (⟨3 / 2, 9 / 2⟩ : ℂ) ∈ openSegment ℝ ((referenceDrawing input).route (edge 5)).start
      ((referenceDrawing input).route (edge 5)).finish ∧
    (⟨2, 8⟩ : ℂ) ∈ openSegment ℝ ((referenceDrawing input).route (edge 2)).start
      ((referenceDrawing input).route (edge 2)).finish ∧
    (⟨2, 8⟩ : ℂ) ∈ openSegment ℝ ((referenceDrawing input).route (edge 5)).start
      ((referenceDrawing input).route (edge 5)).finish := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (⟨3 / 2, 9 / 2⟩ : ℂ) ∈ openSegment ℝ (referencePoint input 0)
      (referencePoint input 3)
    rw [fixture_point 0 (by decide), fixture_point 3 (by decide)]
    have h := lineMap_mem_openSegment ℝ (parabolaPoint 0) (parabolaPoint 3)
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioo 0 1)
    have heq : AffineMap.lineMap (parabolaPoint 0) (parabolaPoint 3) (1 / 2 : ℝ) =
        (⟨3 / 2, 9 / 2⟩ : ℂ) := by
      apply Complex.ext <;>
        norm_num [parabolaPoint, AffineMap.lineMap_apply_module, Complex.real_smul]
    simpa using heq ▸ h
  · change (⟨3 / 2, 9 / 2⟩ : ℂ) ∈ openSegment ℝ (referencePoint input 6)
      (referencePoint input 1)
    rw [fixture_point 6 (by decide), fixture_point 1 (by decide)]
    have h := lineMap_mem_openSegment ℝ (parabolaPoint 6) (parabolaPoint 1)
      (by norm_num : (9 / 10 : ℝ) ∈ Set.Ioo 0 1)
    have heq : AffineMap.lineMap (parabolaPoint 6) (parabolaPoint 1) (9 / 10 : ℝ) =
        (⟨3 / 2, 9 / 2⟩ : ℂ) := by
      apply Complex.ext <;>
        norm_num [parabolaPoint, AffineMap.lineMap_apply_module, Complex.real_smul]
    simpa using heq ▸ h
  · change (⟨2, 8⟩ : ℂ) ∈ openSegment ℝ (referencePoint input 4) (referencePoint input 0)
    rw [fixture_point 4 (by decide), fixture_point 0 (by decide)]
    have h := lineMap_mem_openSegment ℝ (parabolaPoint 4) (parabolaPoint 0)
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioo 0 1)
    have heq : AffineMap.lineMap (parabolaPoint 4) (parabolaPoint 0) (1 / 2 : ℝ) =
        (⟨2, 8⟩ : ℂ) := by
      apply Complex.ext <;>
        norm_num [parabolaPoint, AffineMap.lineMap_apply_module, Complex.real_smul]
    simpa using heq ▸ h
  · change (⟨2, 8⟩ : ℂ) ∈ openSegment ℝ (referencePoint input 6) (referencePoint input 1)
    rw [fixture_point 6 (by decide), fixture_point 1 (by decide)]
    have h := lineMap_mem_openSegment ℝ (parabolaPoint 6) (parabolaPoint 1)
      (by norm_num : (4 / 5 : ℝ) ∈ Set.Ioo 0 1)
    have heq : AffineMap.lineMap (parabolaPoint 6) (parabolaPoint 1) (4 / 5 : ℝ) =
        (⟨2, 8⟩ : ℂ) := by
      apply Complex.ext <;>
        norm_num [parabolaPoint, AffineMap.lineMap_apply_module, Complex.real_smul]
    simpa using heq ▸ h

private theorem first_center_not_middle_support :
    (⟨3 / 2, 9 / 2⟩ : ℂ) ∉ ((referenceDrawing input).route (edge 1)).support := by
  intro hz
  obtain ⟨i, t, ht, heq⟩ :=
    (((referenceDrawing input).route (edge 1)).mem_support_iff _).mp hz
  change (Route.line (referencePoint input 3) (referencePoint input 4)).eval i t =
    (⟨3 / 2, 9 / 2⟩ : ℂ) at heq
  have hline : AffineMap.lineMap (referencePoint input 3) (referencePoint input 4) t =
      (⟨3 / 2, 9 / 2⟩ : ℂ) :=
    (Route.eval_line _ _ i t).symm.trans heq
  rw [fixture_point 3 (by decide), fixture_point 4 (by decide)] at hline
  have hx := congrArg Complex.re hline
  norm_num [parabolaPoint, AffineMap.lineMap_apply_module, Complex.real_smul] at hx
  linarith [ht.1]

-- Both proposed centers have explicit affine contact proof terms above.
-- The disjointness conclusion concerns closed balls, and the isolate is still declared.
example : ∃ ρ : ℂ → ℝ,
    0 < ρ ⟨3 / 2, 9 / 2⟩ ∧ 0 < ρ ⟨2, 8⟩ ∧
    Disjoint (Metric.closedBall (⟨3 / 2, 9 / 2⟩ : ℂ) (ρ ⟨3 / 2, 9 / 2⟩))
      (Metric.closedBall (⟨2, 8⟩ : ℂ) (ρ ⟨2, 8⟩)) ∧
    (referenceDrawing input).vertex 2 ∉
      Metric.closedBall (⟨3 / 2, 9 / 2⟩ : ℂ) (ρ ⟨3 / 2, 9 / 2⟩) ∧
    Disjoint (Metric.closedBall (⟨3 / 2, 9 / 2⟩ : ℂ) (ρ ⟨3 / 2, 9 / 2⟩))
      ((referenceDrawing input).route (edge 1)).support := by
  let C : Set ℂ := {z | ∃ e f : Fin (subdivisionGraph input).edges.length, e ≠ f ∧
    z ∈ openSegment ℝ ((referenceDrawing input).route e).start
      ((referenceDrawing input).route e).finish ∧
    z ∈ openSegment ℝ ((referenceDrawing input).route f).start
      ((referenceDrawing input).route f).finish}
  have hp : (⟨3 / 2, 9 / 2⟩ : ℂ) ∈ C :=
    ⟨edge 0, edge 5, by decide +kernel, fixture_contacts.1, fixture_contacts.2.1⟩
  have hq : (⟨2, 8⟩ : ℂ) ∈ C :=
    ⟨edge 2, edge 5, by decide +kernel, fixture_contacts.2.2.1, fixture_contacts.2.2.2⟩
  have hpq : (⟨3 / 2, 9 / 2⟩ : ℂ) ≠ ⟨2, 8⟩ := by
    intro h
    have hx := congrArg Complex.re h
    norm_num at hx
  obtain ⟨_, ρ, hpos, hdisj, havoid⟩ := exists_reference_crossing_neighborhoods valid_input
  exact ⟨ρ, hpos _ hp, hpos _ hq, hdisj hp hq hpq,
    (havoid _ hp).1 2 (by decide +kernel),
    (havoid _ hp).2 (edge 1) first_center_not_middle_support⟩

-- Empty edges and a declared isolate give the actual empty crossing set, without a
-- nonempty-set or positive-cardinality premise on the neighborhood theorem.
theorem empty_reference_crossing_set :
    let I : FixedRotationInput := ⟨⟨[0], []⟩, [none]⟩
    let C : Set ℂ := {z | ∃ e f : Fin (subdivisionGraph I).edges.length, e ≠ f ∧
      z ∈ openSegment ℝ ((referenceDrawing I).route e).start
        ((referenceDrawing I).route e).finish ∧
      z ∈ openSegment ℝ ((referenceDrawing I).route f).start
        ((referenceDrawing I).route f).finish}
    C = ∅ ∧ C.Finite := by
  let I : FixedRotationInput := ⟨⟨[0], []⟩, [none]⟩
  have hI : Valid I := validate_eq_true_iff I |>.mp (by decide +kernel)
  refine ⟨?_, (exists_reference_crossing_neighborhoods hI).1⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨e, _, _, _, _⟩
  exact Fin.elim0 (show Fin 0 from e)

end Cslib.Tests.RotationCrossingNeighborhoods
