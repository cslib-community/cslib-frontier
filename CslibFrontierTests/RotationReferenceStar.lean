/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary clients of prescribed reference-star geometry)

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceStar
import Mathlib.Tactic.NormNum

/-! Ordinary clients retain both loop ends, parallel occurrences and a fixed isolated center.
The chosen degree-four word is neither binary-index order nor its reversal. -/

public section

namespace Cslib.Tests.RotationReferenceStar

open Cslib.Polygonal Cslib.Complexity.Graph Cslib.Complexity.Graph.RotationRecognition

/-- A prescribed star with one original loop, parallel occurrences and a fixed isolate. -/
@[expose] def input : FixedRotationInput :=
  ⟨⟨[0, 1, 2], [(0, 0), (0, 1), (0, 1)]⟩, [some [2, 1, 4, 0], none, some []]⟩

private theorem valid_input : Valid input := validate_eq_true_iff input |>.mp (by decide +kernel)

private def loopFirst : Dart input.graph := (⟨0, by decide⟩, false)
private def loopLast : Dart input.graph := (⟨0, by decide⟩, true)
private def parallelFirst : Dart input.graph := (⟨1, by decide⟩, false)
private def parallelSecond : Dart input.graph := (⟨2, by decide⟩, false)

-- The two loop ends select the first and last subdivision occurrences with unchanged end tags.
example : (subdivisionDart input loopFirst).1.val = 0 ∧
    (subdivisionDart input loopFirst).2 = false ∧
    (subdivisionDart input loopLast).1.val = 2 ∧
    (subdivisionDart input loopLast).2 = true := by
  decide +kernel

-- The literal word is reversed only in the leaf block, before the remaining centers/leaves.
private theorem reference_order : referenceOrder input = [0, 3, 7, 4, 5, 1, 2, 6, 8] := by
  decide +kernel

-- These are actual outgoing vectors at the two original ends of the same loop.
example : (referenceDrawing input).germ (subdivisionDart input loopFirst) = (⟨1, 1⟩ : ℂ) ∧
    (referenceDrawing input).germ (subdivisionDart input loopLast) = (⟨3, 9⟩ : ℂ) := by
  constructor <;>
    rw [referenceDrawing_subdivisionDart_germ] <;>
    simp only [referencePoint, reference_order] <;>
    apply Complex.ext <;>
    norm_num [parabolaPoint, input, loopFirst, loopLast, Dart.index, Dart.vertex,
      Cslib.Complexity.Graph.edgeEndpoint, List.idxOf_cons]

-- Position zero precedes position one clockwise, hence its real argument is larger.
example : ((referenceDrawing input).germ (subdivisionDart input loopLast)).arg <
    ((referenceDrawing input).germ (subdivisionDart input parallelFirst)).arg := by
  apply (referenceDrawing_fixedWord_arg_lt_iff valid_input
    (v := 0) (word := [2, 1, 4, 0]) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).mpr
  decide +kernel

-- Equal-dart comparison is included, without a distinctness premise.
example : ¬((referenceDrawing input).germ (subdivisionDart input loopLast)).arg <
    ((referenceDrawing input).germ (subdivisionDart input loopLast)).arg := by
  rw [referenceDrawing_fixedWord_arg_lt_iff valid_input
    (v := 0) (word := [2, 1, 4, 0]) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

-- Both outgoing loop rays are nonzero and have distinct geometric directions.
example : (referenceDrawing input).germ (subdivisionDart input loopLast) ≠ 0 ∧
    (referenceDrawing input).direction (subdivisionDart input loopFirst) ≠
      (referenceDrawing input).direction (subdivisionDart input loopLast) := by
  refine ⟨referenceDrawing_subdivisionDart_germ_ne_zero valid_input loopLast, ?_⟩
  intro h
  have heq := referenceDrawing_fixedWord_directions_injective valid_input
    (v := 0) (word := [2, 1, 4, 0]) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) h
  exact (show loopFirst ≠ loopLast by decide +kernel) heq

-- Clockwise follows the literal word; reversing the three directions is false.
example :
    sbtw ((referenceDrawing input).direction (subdivisionDart input parallelSecond))
      ((referenceDrawing input).direction (subdivisionDart input loopLast))
      ((referenceDrawing input).direction (subdivisionDart input parallelFirst)) ∧
    ¬sbtw ((referenceDrawing input).direction (subdivisionDart input parallelFirst))
      ((referenceDrawing input).direction (subdivisionDart input loopLast))
      ((referenceDrawing input).direction (subdivisionDart input parallelSecond)) := by
  have h := (referenceDrawing_fixedWord_clockwise_iff valid_input
    (v := 0) (word := [2, 1, 4, 0]) (by decide +kernel)
    (a := parallelFirst) (b := loopLast) (c := parallelSecond)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr (by decide +kernel)
  exact ⟨h, h.not_sbtw⟩

-- Degree one has a nonzero ray; the cyclic-triple API imposes no fictitious triple there.
example :
    let J : FixedRotationInput := ⟨⟨[0, 1], [(0, 1)]⟩, [some [0], some [1]]⟩
    (referenceDrawing J).germ (subdivisionDart J (⟨0, by decide⟩, false)) ≠ 0 := by
  dsimp only
  apply referenceDrawing_subdivisionDart_germ_ne_zero
  exact validate_eq_true_iff _ |>.mp (by decide +kernel)

end Cslib.Tests.RotationReferenceStar
