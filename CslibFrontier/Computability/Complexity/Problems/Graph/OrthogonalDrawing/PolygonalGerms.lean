/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Polygonal
public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.CardinalOrder
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Germs
import CslibFrontier.Foundations.Data.List.ConsecutivePairs
import Mathlib.Data.List.GetD

/-!
# Actual end-segment germs and executed integer neighbours

The outgoing germ of the converted polygonal route is exactly the vector from the original
displayed vertex to the neighbour read by the native cardinal-successor computation.
Both ends of every indexed edge use the same shared route normalization. No chosen rotation
or geometric rank provider occurs in the statement.

This is original representation transport.
-/

public section

namespace Cslib.Complexity.Graph

open Cslib.Orthogonal OrthogonalDrawing

/-- The proof-side polygonal conversion and the native endpoint-neighbour lookup read
exactly the same actual segment vector, including independently reversed input routes. -/
theorem IsPlanarOrthogonalDrawing.germ_polygonalDrawing
    {G : Graph} {d : OrthogonalDrawing} (hd : IsPlanarOrthogonalDrawing G d) (a : Dart G) :
    hd.polygonalDrawing.germ a = complexPoint (exitNeighbor G d a.index) -
      complexPoint (drawingPosition G d a.vertex) := by
  rcases a with ⟨e, side⟩
  let r := (sourceRoute G d e).reverse
  have hlen : 2 ≤ r.length := by
    simpa only [r, List.length_reverse] using sourceRoute_length_ge_two hd e.isLt
  cases side
  · change complexPoint r[1] - complexPoint r[0] = _
    refine congrArg₂ (· - ·) (congrArg complexPoint ?_) (hd.polygonalDrawing.endpoint_eq e false)
    simpa only [exitNeighbor_index, Bool.false_eq_true, ↓reduceIte] using
      (List.getD_eq_getElem r (0, 0) (by omega : 1 < r.length)).symm
  · change complexPoint r[r.length - 2] - complexPoint r[r.length - 2 + 1] = _
    refine congrArg₂ (· - ·) (congrArg complexPoint ?_) (hd.polygonalDrawing.endpoint_eq e true)
    simpa only [exitNeighbor_index, ↓reduceIte] using
      (List.getD_eq_getElem r (0, 0) (by omega : r.length - 2 < r.length)).symm

/-- The native neighbour is joined to its displayed endpoint by an actual proper axis
segment. The last end uses orthogonality of the reversed route, preserving orientation. -/
theorem IsPlanarOrthogonalDrawing.axisAligned_exitNeighbor
    {G : Graph} {d : OrthogonalDrawing} (hd : IsPlanarOrthogonalDrawing G d) (a : Dart G) :
    AxisAligned (drawingPosition G d a.vertex) (exitNeighbor G d a.index) := by
  rcases a with ⟨e, side⟩
  let r := (sourceRoute G d e).reverse
  have hlen : 2 ≤ r.length := by
    simpa only [r, List.length_reverse] using sourceRoute_length_ge_two hd e.isLt
  have horth : IsOrthogonal r :=
    (isOrthogonal_reverse_iff _).mpr (sourceRoute_regular hd e.isLt).1
  rw [exitNeighbor_index]
  cases side
  · rw [← complexPoint_injective (hd.polygonalDrawing.endpoint_eq e false)]
    change AxisAligned r[0] (r.getD 1 (0, 0))
    rw [List.getD_eq_getElem r (0, 0) (by omega : 1 < r.length)]
    exact horth _ (List.getElem_mem_consecutivePairs r 0 (by omega))
  · rw [← complexPoint_injective (hd.polygonalDrawing.endpoint_eq e true)]
    change AxisAligned r[r.length - 2 + 1] (r.getD (r.length - 2) (0, 0))
    rw [List.getD_eq_getElem r (0, 0) (by omega : r.length - 2 < r.length)]
    have hp := ((isOrthogonal_reverse_iff r).mpr horth) _
      (List.getElem_mem_consecutivePairs r.reverse 0 (by simp only [List.length_reverse]; omega))
    simp only [List.getElem_reverse, Nat.sub_zero] at hp
    convert hp using 1
    congr 1
    omega

/-- The converted drawing's literal outgoing angle is exactly the rank read by the
native program; no rotation or idealized ray is supplied. -/
theorem IsPlanarOrthogonalDrawing.direction_polygonalDrawing
    {G : Graph} {d : OrthogonalDrawing} (hd : IsPlanarOrthogonalDrawing G d) (a : Dart G) :
    hd.polygonalDrawing.direction a =
      ((-(dartRank G d a.index : ℝ) * Real.pi / 2 : ℝ) : Real.Angle) := by
  change ((hd.polygonalDrawing.germ a).arg : Real.Angle) = _
  rw [hd.germ_polygonalDrawing]
  simpa only [dartRank, endpoint, Dart.vertex_index] using
    arg_eq_clockwiseRank (hd.axisAligned_exitNeighbor a)

end Cslib.Complexity.Graph
