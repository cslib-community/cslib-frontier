/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Parity
public import CslibFrontier.Computability.PolyTime.Graph.RotationSystem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Native frozen parity-query computation

Every certificate covers all raw inputs. Unary ranges are funded only by actual vertex/edge
list lengths. All supplied endpoint/dart labels use binary comparisons and saturating binary
lookup, including malformed huge indices. The concrete query composes the sparse compiler with
`XORSAT.computableInPolyTime_solve`; there is no solver, recognizer, growth or encoding provider
hypothesis.

## Main results

* `Cslib.Complexity.Graph.RotationRecognition.query_polyTime`: native all-raw algebraic query.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Turing.MultiTapeTM
open scoped RotationCertificate

attribute [fun_prop] encFixedRotationInput_graph_polyTime encFixedRotationInput_orders_polyTime
  encFixedRotationInput_mk_polyTime
attribute [local fun_prop] encFrame_vertexCount_polyTime encFrame_segments_polyTime
  encFrame_order_polyTime encFrame_mk_polyTime

/-- Binary-indexed endpoint fibers are computed from the actual edge count on all graphs. -/
theorem fiber_polyTime :
    ComputableInPolyTime (fun p : Graph × ℕ => fiber p.1 p.2)
      (encPair encGraph encNat) (encList encNat) := by
  unfold fiber
  apply ComputableInPolyTime.filterWithInput (encA := encNat) (by fun_prop)
  fun_prop

/-- Binary-indexed endpoint fibers of a computed graph and vertex are native polynomial-time. -/
@[fun_prop] theorem fiber_polyTime' {α : Type} {enc : α ↪ List Bool}
    {G : α → Graph} {v : α → ℕ}
    (hG : ComputableInPolyTime G enc encGraph)
    (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun x => fiber (G x) (v x)) enc (encList encNat) := by
  simpa only [Function.comp_def] using fiber_polyTime.comp (hG.prod hv)

/-- The dense/full-order validator has no raw well-formedness premise. -/
theorem validate_polyTime :
    ComputableInPolyTime validate encFixedRotationInput encBool := by
  unfold validate
  refine ((((by fun_prop : ComputableInPolyTime _ _ encBool).bool_and'
    (ComputableInPolyTime.allWithInput (by fun_prop)
      (ComputableInPolyTime.binary_lt' (by fun_prop) (by fun_prop)))).bool_and'
        (by fun_prop)).bool_and' ?_)
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  apply ComputableInPolyTime.optionElimWithInput (by fun_prop) (ComputableInPolyTime.const true)
  fun_prop

/-- Twice subdivision preserves list occurrence identity and is native on every raw input. -/
theorem subdivide_polyTime :
    ComputableInPolyTime subdivide encFixedRotationInput (encList encSegment) := by
  unfold subdivide encSegment
  apply ComputableInPolyTime.flatMapWithInput (by fun_prop)
  have ha : ComputableInPolyTime
      (fun p : FixedRotationInput × ((ℕ × ℕ) × ℕ) => p.1.graph.vertices.length + 2 * p.2.2)
      (encPair encFixedRotationInput (encPair (encPair encNat encNat) encUnary)) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hb : ComputableInPolyTime
      (fun p : FixedRotationInput × ((ℕ × ℕ) × ℕ) => p.1.graph.vertices.length + 2 * p.2.2 + 1)
      (encPair encFixedRotationInput (encPair (encPair encNat encNat) encUnary)) encNat :=
    ComputableInPolyTime.binary_add' ha (ComputableInPolyTime.const 1)
  fun_prop

private theorem centerBlocks_polyTime :
    ComputableInPolyTime centerBlocks encFixedRotationInput (encList encNat) := by
  unfold centerBlocks
  apply ComputableInPolyTime.flatMapWithInput (encA := encNat) (by fun_prop)
  exact ComputableInPolyTime.cons' (by fun_prop)
    (ComputableInPolyTime.mapWithInput (by fun_prop)
      (ComputableInPolyTime.binary_add' (by fun_prop) (by fun_prop)))

attribute [local fun_prop] centerBlocks_polyTime

/-- The full reference order is built from bounded list scans, including malformed words. -/
theorem referenceOrder_polyTime :
    ComputableInPolyTime referenceOrder encFixedRotationInput (encList encNat) := by
  unfold referenceOrder
  apply ComputableInPolyTime.listAppend' centerBlocks_polyTime
  apply ComputableInPolyTime.filterWithInput
  · apply ComputableInPolyTime.mapWithInput (encA := encNat) (by fun_prop)
    exact ComputableInPolyTime.binary_add' (by fun_prop) (by fun_prop)
  · exact ComputableInPolyTime.bool_not.comp (by fun_prop)

attribute [local fun_prop] subdivide_polyTime referenceOrder_polyTime

/-- Frame construction is native, with its unary stride funded by actual list lengths. -/
theorem frame_polyTime : ComputableInPolyTime frame encFixedRotationInput encFrame := by
  unfold frame subdivisionSize
  fun_prop

private theorem independent_polyTime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × (ℕ × ℕ) => independent p.1 p.2)
    (encPair (encPair encNat encNat) (encPair encNat encNat)) encBool := by
  unfold independent
  fun_prop

private theorem moveLabels_polyTime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × (Segment × (ℕ × ℕ)) => moveLabels p.1.1 p.1.2 p.2.1 p.2.2)
    (encPair (encPair encUnary encUnary) (encPair encSegment (encPair encNat encNat)))
    (encList encNat) := by
  unfold moveLabels moveLabel encSegment
  have hprod : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × (Segment × (ℕ × ℕ)) => p.1.2 * p.1.1)
      (encPair (encPair encUnary encUnary) (encPair encSegment (encPair encNat encNat))) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  exact ComputableInPolyTime.ite' (by fun_prop) (ComputableInPolyTime.const [])
    (ComputableInPolyTime.cons' (ComputableInPolyTime.binary_add' hprod (by fun_prop))
      (ComputableInPolyTime.cons' (ComputableInPolyTime.binary_add' hprod (by fun_prop))
        (ComputableInPolyTime.const [])))

private theorem moveLabels_polyTime' {α : Type} {enc : α ↪ List Bool}
    {n i : α → ℕ} {e : α → Segment} {f : α → ℕ × ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hi : ComputableInPolyTime i enc encUnary)
    (he : ComputableInPolyTime e enc encSegment)
    (hf : ComputableInPolyTime f enc (encPair encNat encNat)) :
    ComputableInPolyTime (fun x => moveLabels (n x) (i x) (e x) (f x)) enc (encList encNat) := by
  simpa only [Function.comp_def] using moveLabels_polyTime.comp ((hn.prod hi).prod (he.prod hf))

private theorem crossing_polyTime : ComputableInPolyTime
    (fun p : (List ℕ × (ℕ × ℕ)) × (ℕ × ℕ) => crossing p.1.1 p.1.2 p.2)
    (encPair (encPair (encList encNat) (encPair encNat encNat)) (encPair encNat encNat))
    encBool := by
  unfold crossing between
  fun_prop

private theorem crossing_polyTime' {α : Type} {enc : α ↪ List Bool}
    {order : α → List ℕ} {e f : α → ℕ × ℕ}
    (ho : ComputableInPolyTime order enc (encList encNat))
    (he : ComputableInPolyTime e enc (encPair encNat encNat))
    (hf : ComputableInPolyTime f enc (encPair encNat encNat)) :
    ComputableInPolyTime (fun x => crossing (order x) (e x) (f x)) enc encBool := by
  simpa only [Function.comp_def] using crossing_polyTime.comp ((ho.prod he).prod hf)

attribute [local fun_prop] independent_polyTime moveLabels_polyTime' crossing_polyTime'

private theorem row_polyTime :
    ComputableInPolyTime (fun p : (Frame × (Segment × ℕ)) × (Segment × ℕ) =>
      row p.1.1 p.1.2 p.2)
      (encPair (encPair encFrame (encPair encSegment encUnary)) (encPair encSegment encUnary))
      (encAffineEquation encNat) := by
  refine ComputableInPolyTime.of_enc_eq (encMid := encPair (encList encNat) encBool)
    (f := fun p : (Frame × (Segment × ℕ)) × (Segment × ℕ) =>
      ((row p.1.1 p.1.2 p.2).vars, (row p.1.1 p.1.2 p.2).rhs)) ?_ fun _ => rfl
  unfold row encSegment
  fun_prop

attribute [local fun_prop] row_polyTime

/-- Sparse row emission scans only segment occurrences, with width at most four. -/
theorem compileFrame_polyTime :
    ComputableInPolyTime compileFrame encFrame XORSAT.encoding := by
  unfold compileFrame XORSAT.encoding
  apply ComputableInPolyTime.flatMapWithInput (by fun_prop)
  apply ComputableInPolyTime.mapWithInput
  · apply ComputableInPolyTime.filterWithInput (by fun_prop)
    unfold encSegment
    fun_prop
  · exact row_polyTime

/-- The full graph/order-to-XOR compiler is an ordinary native polynomial-time function. -/
theorem compile_polyTime :
    ComputableInPolyTime compile encFixedRotationInput XORSAT.encoding :=
  compileFrame_polyTime.comp frame_polyTime

/-- Concrete all-raw native query. Invalid models reject, and every valid query actually calls
existing certified sparse Gaussian elimination. No topological criterion is used. -/
theorem query_polyTime : ComputableInPolyTime query encFixedRotationInput encBool :=
  validate_polyTime.bool_and' (XORSAT.computableInPolyTime_solve.comp compile_polyTime)

end Cslib.Complexity.Graph.RotationRecognition
