/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary clients of indexed reference crossings)

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceCrossings
import CslibFrontier.Foundations.Geometry.Polygonal.SlopeDetour
import Mathlib.Tactic.NormNum

/-!
Ordinary clients retain both loop ends, parallel/reversed occurrences and an isolate.
An actual independent reference crossing supplies unequal slopes, while the named
`parallel_reference_chords` client retains two distinct reference chords with equal slopes.
A finite subtype of actual routes through one interior point supplies the existing local
slope-detour construction without a supplied injectivity certificate.
-/

public section

namespace Cslib.Tests.RotationReferenceCrossings

open Cslib.Polygonal Cslib.Complexity.Graph Cslib.Complexity.Graph.RotationRecognition

private def input : FixedRotationInput :=
  ⟨⟨[0, 1, 2], [(0, 0), (0, 1), (0, 1)]⟩, List.replicate 3 none⟩

private theorem valid_input : Valid input := validate_eq_true_iff input |>.mp (by decide +kernel)

private def edge (i : Fin 9) : Fin (subdivisionGraph input).edges.length :=
  ⟨i.val, by change i.val < 9; exact i.isLt⟩

-- The moved raw lookup is available through ordinary imports and retains the middle flag.
example : (subdivide input)[4]? = some (((5, 6), false) : Segment) := by
  simpa [input] using subdivide_getElem? input ⟨1, by decide⟩ (1 : Fin 3)

-- The two ends of the original loop select different unordered segments.
example :
    (s(((subdivisionGraph input).edges[edge 0]).1,
      ((subdivisionGraph input).edges[edge 0]).2) : Sym2 ℕ) ≠
    s(((subdivisionGraph input).edges[edge 2]).1,
      ((subdivisionGraph input).edges[edge 2]).2) := by
  intro h
  have he := subdivisionGraph_edge_injective valid_input h
  have := congrArg Fin.val he
  norm_num [edge] at this

-- The original parallel occurrences also retain distinct fresh first segments.
example :
    (s(((subdivisionGraph input).edges[edge 3]).1,
      ((subdivisionGraph input).edges[edge 3]).2) : Sym2 ℕ) ≠
    s(((subdivisionGraph input).edges[edge 6]).1,
      ((subdivisionGraph input).edges[edge 6]).2) := by
  intro h
  have he := subdivisionGraph_edge_injective valid_input h
  have := congrArg Fin.val he
  norm_num [edge] at this

-- No vertex deletion is part of unordered edge injectivity: the original isolate remains.
example : 2 ∈ (subdivisionGraph input).vertices ∧
    ∀ e ∈ (subdivisionGraph input).edges, e.1 ≠ 2 ∧ e.2 ≠ 2 := by
  decide +kernel

-- A true rank crossing bit produces an actual common open point before slopes are compared.
example : ∃ z : ℂ,
    z ∈ openSegment ℝ ((referenceDrawing input).route (edge 0)).start
      ((referenceDrawing input).route (edge 0)).finish ∧
    z ∈ openSegment ℝ ((referenceDrawing input).route (edge 5)).start
      ((referenceDrawing input).route (edge 5)).finish ∧
    ((referenceDrawing input).route (edge 0)).start.re +
        ((referenceDrawing input).route (edge 0)).finish.re ≠
      ((referenceDrawing input).route (edge 5)).start.re +
        ((referenceDrawing input).route (edge 5)).finish.re := by
  obtain ⟨z, hz, _⟩ := (referenceDrawing_crossing_iff valid_input (edge 0) (edge 5)
    (by decide +kernel)).mp (by decide +kernel)
  refine ⟨z, hz.1, hz.2, ?_⟩
  exact referenceDrawing_slope_ne_of_interior_contact valid_input (edge 0) (edge 5)
    (by decide +kernel) hz.1 hz.2

/-- Equal slopes of distinct actual reference chords are permitted globally. The local
interior-contact theorem excludes a common open point for this parallel pair. -/
theorem parallel_reference_chords : ∃ I : FixedRotationInput, Valid I ∧
    ∃ e f : Fin (subdivisionGraph I).edges.length, e ≠ f ∧
      ((referenceDrawing I).route e).start.re + ((referenceDrawing I).route e).finish.re =
        ((referenceDrawing I).route f).start.re + ((referenceDrawing I).route f).finish.re ∧
      ¬∃ z : ℂ,
        z ∈ openSegment ℝ ((referenceDrawing I).route e).start
          ((referenceDrawing I).route e).finish ∧
        z ∈ openSegment ℝ ((referenceDrawing I).route f).start
          ((referenceDrawing I).route f).finish := by
  have hne : edge 1 ≠ edge 5 := by decide +kernel
  have hord : referenceOrder input = [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide +kernel
  have heq : ((referenceDrawing input).route (edge 1)).start.re +
      ((referenceDrawing input).route (edge 1)).finish.re =
      ((referenceDrawing input).route (edge 5)).start.re +
        ((referenceDrawing input).route (edge 5)).finish.re := by
    change ((referenceOrder input).idxOf 3 : ℝ) + (referenceOrder input).idxOf 4 =
      ((referenceOrder input).idxOf 6 : ℝ) + (referenceOrder input).idxOf 1
    rw [hord]
    norm_num
  refine ⟨input, valid_input, edge 1, edge 5, hne, heq, ?_⟩
  rintro ⟨z, hz, hz'⟩
  exact (referenceDrawing_slope_ne_of_interior_contact valid_input (edge 1) (edge 5)
    hne hz hz') heq

-- Reversed original occurrences also keep separate indexed subdivisions.
example :
    let I : FixedRotationInput := ⟨⟨[0, 1, 2], [(0, 1), (1, 0)]⟩, List.replicate 3 none⟩
    ∀ e f : Fin (subdivisionGraph I).edges.length,
      (s(((subdivisionGraph I).edges[e]).1, ((subdivisionGraph I).edges[e]).2) : Sym2 ℕ) =
        s(((subdivisionGraph I).edges[f]).1, ((subdivisionGraph I).edges[f]).2) → e = f := by
  dsimp only
  let I : FixedRotationInput := ⟨⟨[0, 1, 2], [(0, 1), (1, 0)]⟩, List.replicate 3 none⟩
  have hI : Valid I := validate_eq_true_iff I |>.mp (by decide +kernel)
  exact fun _ _ h => subdivisionGraph_edge_injective hI h

-- Empty edge data leave the declared isolated point and the empty actual edge-index type.
example :
    let I : FixedRotationInput := ⟨⟨[0], []⟩, [none]⟩
    Valid I ∧ (subdivisionGraph I).edges.length = 0 ∧
      0 ∈ (subdivisionGraph I).vertices := by
  exact ⟨validate_eq_true_iff _ |>.mp (by decide +kernel), rfl, by decide +kernel⟩

-- The finite subtype of actual routes through a point supplies local detours internally.
example (z : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    let X := {e : Fin (subdivisionGraph input).edges.length //
      z ∈ openSegment ℝ ((referenceDrawing input).route e).start
        ((referenceDrawing input).route e).finish}
    let s := fun e : X => ((referenceDrawing input).route e.val).start.re +
      ((referenceDrawing input).route e.val).finish.re
    ∃ d : X → ℝ, ∀ e, (Route.slopeDetour r (s e) (d e)).IsSimple := by
  classical
  dsimp only
  let X := {e : Fin (subdivisionGraph input).edges.length //
    z ∈ openSegment ℝ ((referenceDrawing input).route e).start
      ((referenceDrawing input).route e).finish}
  let s := fun e : X => ((referenceDrawing input).route e.val).start.re +
    ((referenceDrawing input).route e.val).finish.re
  have hs : Function.Injective s := by
    intro e f h
    apply Subtype.ext
    by_contra hne
    exact (referenceDrawing_slope_ne_of_interior_contact valid_input e.val f.val hne
      e.property f.property) h
  obtain ⟨d, h⟩ := exists_slopeDetour_separation s hs hr hε none
  refine ⟨d, fun e => ?_⟩
  simpa using (h.1 e).2.2.1

end Cslib.Tests.RotationReferenceCrossings
