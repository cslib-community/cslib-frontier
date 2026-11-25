/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.RotationCertificate
public import CslibFrontier.Computability.PolyTime.Graph.RotationSystem
public import CslibFrontier.Computability.PolyTime.Graph.OrthogonalRoutes
import CslibFrontier.Computability.Geometry.Orthogonal.PointPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Native clockwise rotation computation from integer routes

The complete successor table is computed from the actual input graph and drawing in
polynomial time. Internal positions and cardinal ranks are unary; graph names, drawing
coordinates, and final certificate entries have their original binary encodings. The bound
holds on all raw input lists without geometric correctness or encoded-size premises.
-/

public section

namespace Cslib.Complexity.Graph.OrthogonalDrawing

open Cslib.Orthogonal Turing.MultiTapeTM

local instance : ListEncoding encPoint encRoute :=
  inferInstanceAs (ListEncoding encPoint (encList encPoint))

local instance : SizedListEncoding encPoint encRoute :=
  inferInstanceAs (SizedListEncoding encPoint (encList encPoint))

/-- Framed binary graph followed by its binary-coordinate drawing. -/
abbrev encDrawingInput := encPair encGraph encOrthogonalDrawing

/-- Framed graph/drawing input followed by a unary dart-list position. -/
abbrev encDrawingDart := encPair encDrawingInput encUnary

private theorem dartCount_polyTime :
    ComputableInPolyTime (fun p : Graph × OrthogonalDrawing => 2 * p.1.edges.length)
      encDrawingInput encUnary := by
  unfold encDrawingInput
  fun_prop

private theorem endpoint_polyTime :
    ComputableInPolyTime (fun p : Graph × ℕ => endpoint p.1 p.2)
      (encPair encGraph encUnary) encNat := by
  unfold endpoint
  fun_prop

private theorem dartOrigin_polyTime :
    ComputableInPolyTime (fun p : (Graph × OrthogonalDrawing) × ℕ =>
      drawingPosition p.1.1 p.1.2 (endpoint p.1.1 p.2)) encDrawingDart encPoint := by
  simpa only [Function.comp_def] using computableInPolyTime_drawingPosition.comp
    ((ComputableInPolyTime.fst encDrawingInput encUnary).prod
      (endpoint_polyTime.comp
        (((ComputableInPolyTime.fst encGraph encOrthogonalDrawing).comp
          (ComputableInPolyTime.fst encDrawingInput encUnary)).prod
            (ComputableInPolyTime.snd encDrawingInput encUnary))))

private theorem route_polyTime :
    ComputableInPolyTime (fun p : (Graph × OrthogonalDrawing) × ℕ =>
      (sourceRoute p.1.1 p.1.2 (p.2 / 2)).reverse) encDrawingDart encRoute := by
  apply ComputableInPolyTime.listReverseWithInput
  refine computableInPolyTime_sourceRoute.comp
    (g := fun p : (Graph × OrthogonalDrawing) × ℕ => (p.1, p.2 / 2)) ?_
  unfold encDrawingDart encDrawingInput encSourceIndex
  fun_prop

private theorem exitNeighbor_polyTime :
    ComputableInPolyTime (fun p : (Graph × OrthogonalDrawing) × ℕ =>
      exitNeighbor p.1.1 p.1.2 p.2) encDrawingDart encPoint := by
  have hr := route_polyTime
  unfold exitNeighbor
  apply ComputableInPolyTime.ite_decide
  · unfold encDrawingDart
    fun_prop
  · exact ComputableInPolyTime.listGetDWithInput hr (.const 1) (0, 0)
  · exact ComputableInPolyTime.listGetDWithInput hr (by fun_prop) (0, 0)

private theorem clockwiseRank_polyTime :
    ComputableInPolyTime (fun p : Point × Point => clockwiseRank p.1 p.2)
      (encPair encPoint encPoint) encUnary := by
  have := computableInPolyTime_direction
  unfold clockwiseRank
  fun_prop

private theorem dartRank_polyTime :
    ComputableInPolyTime (fun p : (Graph × OrthogonalDrawing) × ℕ =>
      dartRank p.1.1 p.1.2 p.2) encDrawingDart encUnary :=
  clockwiseRank_polyTime.comp (dartOrigin_polyTime.prod exitNeighbor_polyTime)

/-- Four scans of the actual dart list compute the candidate word on every raw input.
Coordinate magnitudes and vertex names do not determine any iteration count. -/
theorem computableInPolyTime_clockwiseCandidates :
    ComputableInPolyTime (fun p : (Graph × OrthogonalDrawing) × ℕ =>
      clockwiseCandidates p.1.1 p.1.2 p.2) encDrawingDart (encList encUnary) := by
  unfold clockwiseCandidates
  apply ComputableInPolyTime.flatMapWithInput (encA := encUnary)
    (ComputableInPolyTime.const (List.range 4))
  apply ComputableInPolyTime.filterWithInput (encA := encUnary)
    (ComputableInPolyTime.range.comp (dartCount_polyTime.comp
      ((ComputableInPolyTime.fst encDrawingInput encUnary).comp
        (ComputableInPolyTime.fst encDrawingDart encUnary))))
  let encStep := encPair encDrawingDart encUnary
  have hstepInput := ComputableInPolyTime.fst encStep encUnary
  have hdart := (ComputableInPolyTime.fst encDrawingDart encUnary).comp hstepInput
  have hinput := (ComputableInPolyTime.fst encDrawingInput encUnary).comp hdart
  have hi := (ComputableInPolyTime.snd encDrawingInput encUnary).comp hdart
  have hj := ComputableInPolyTime.snd encStep encUnary
  have hstep := (ComputableInPolyTime.snd encDrawingDart encUnary).comp hstepInput
  have hgraph := (ComputableInPolyTime.fst encGraph encOrthogonalDrawing).comp hinput
  have hei := endpoint_polyTime.comp (hgraph.prod hi)
  have hej := endpoint_polyTime.comp (hgraph.prod hj)
  have hri := dartRank_polyTime.comp (hinput.prod hi)
  have hrj := dartRank_polyTime.comp (hinput.prod hj)
  have hturn := ComputableInPolyTime.unary_mod'
    (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add' hri hstep)
      (ComputableInPolyTime.const 1)) (ComputableInPolyTime.const 4)
  have hvertex := hej.decide_eq' hei
  have hrank := hrj.decide_eq' hturn
  simpa only [Function.comp_def, Bool.decide_and] using
    ComputableInPolyTime.bool_and.comp (hvertex.prod hrank)

/-- The literal clockwise successor table is native polynomial time under the existing
binary certificate encoding, with no valid-input or drawing-provider hypothesis. -/
theorem computableInPolyTime_rotationCertificate :
    ComputableInPolyTime (fun p : Graph × OrthogonalDrawing => rotationCertificate p.1 p.2)
      encDrawingInput encRotationCertificate := by
  have hs : ComputableInPolyTime (fun p : (Graph × OrthogonalDrawing) × ℕ =>
      clockwiseSuccessor p.1.1 p.1.2 p.2) encDrawingDart encUnary := by
    unfold clockwiseSuccessor
    simp only [List.headD_eq_head?_getD]
    refine ComputableInPolyTime.optionGetDWithInput
      ((ComputableInPolyTime.head? encUnary).comp computableInPolyTime_clockwiseCandidates) ?_
    unfold encDrawingDart
    fun_prop
  refine encRotationCertificate_mk_polyTime ?_
  simpa only [Function.comp_def, List.map_id'] using
    ComputableInPolyTime.mapWithInput (f := fun _ n => n) (encB := encNat)
      (ComputableInPolyTime.mapWithInput (encA := encUnary)
        (ComputableInPolyTime.range.comp dartCount_polyTime) hs)
      (ComputableInPolyTime.unary_to_binary.comp
        (ComputableInPolyTime.snd encDrawingInput encUnary))

end Cslib.Complexity.Graph.OrthogonalDrawing
