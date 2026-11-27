/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Routes
public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Encoding
public import CslibFrontier.Computability.Geometry.Orthogonal.PointPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native normalization of supplied orthogonal incidence routes

These shared certificates compute graph positions, second-to-first route normalization and
cardinal exits on all raw inputs. Graph labels and signed coordinates keep their binary
encodings; edge positions use unary list indices. Existing point and route encodings,
framing, fallbacks and computed functions are unchanged.

The positive SAT drawing compiler and native clockwise-certificate computation consume
this common interface. No geometric validity premise funds a runtime bound.
-/

public section

namespace Cslib.Complexity.Graph.OrthogonalDrawing

open Cslib.Orthogonal Turing.MultiTapeTM

/-- Listed graphs retain binary vertex labels; edge positions use unary counters. -/
abbrev encSourceIndex : ((Graph × Graph.OrthogonalDrawing) × ℕ) ↪ List Bool :=
  encPair (encPair encGraph Graph.encOrthogonalDrawing) encUnary

local instance : ListEncoding encPoint encRoute :=
  inferInstanceAs (ListEncoding encPoint (encList encPoint))

local instance : SizedListEncoding encPoint encRoute :=
  inferInstanceAs (SizedListEncoding encPoint (encList encPoint))

attribute [local fun_prop] computableInPolyTime_direction

/-- Position lookup compares binary graph labels and scans only the declared vertex list. -/
@[fun_prop]
theorem computableInPolyTime_drawingPosition :
    ComputableInPolyTime
      (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
        Graph.drawingPosition p.1.1 p.1.2 p.2)
      (encPair (encPair encGraph Graph.encOrthogonalDrawing) encNat) encPoint := by
  unfold Graph.drawingPosition encGraph Graph.encOrthogonalDrawing encRoute
  fun_prop

/-- The second endpoint of an indexed source edge is computed without expanding labels. -/
@[fun_prop]
theorem computableInPolyTime_sourceStart :
    ComputableInPolyTime (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
      sourceStart p.1.1 p.1.2 p.2) encSourceIndex encPoint := by
  have hp : ComputableInPolyTime
      (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
        (p.1, (p.1.1.2.getD p.2 (0, 0)).2)) encSourceIndex
      (encPair (encPair encGraph Graph.encOrthogonalDrawing) encNat) := by fun_prop
  simpa only [Function.comp_def, sourceStart] using
    (computableInPolyTime_drawingPosition.comp hp)

/-- Reading and, when necessary, reversing an actual source route is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_sourceRoute :
    ComputableInPolyTime (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
      sourceRoute p.1.1 p.1.2 p.2) encSourceIndex encRoute := by
  have hs := computableInPolyTime_sourceStart
  have hr : ComputableInPolyTime
      (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ => p.1.2.2.getD p.2 [])
      encSourceIndex encRoute := by fun_prop
  have hhead := (ComputableInPolyTime.head? encPoint).comp hr
  have hsome := (ComputableInPolyTime.optionSome encPoint).comp hs
  exact ((hhead.decide_eq' hsome).ite_decide hr
    (ComputableInPolyTime.listReverseWithInput hr))

/-- The source exit direction needs only the first two listed route points. -/
@[fun_prop]
theorem computableInPolyTime_sourceDirection :
    ComputableInPolyTime (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
      sourceDirection p.1.1 p.1.2 p.2) encSourceIndex encPoint := by
  have hp : ComputableInPolyTime
      (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
        (sourceStart p.1.1 p.1.2 p.2,
          (sourceRoute p.1.1 p.1.2 p.2).getD 1 (0, 0)))
      encSourceIndex (encPair encPoint encPoint) := by fun_prop
  simpa only [Function.comp_def, sourceDirection] using
    (computableInPolyTime_direction.comp hp)

end Cslib.Complexity.Graph.OrthogonalDrawing
