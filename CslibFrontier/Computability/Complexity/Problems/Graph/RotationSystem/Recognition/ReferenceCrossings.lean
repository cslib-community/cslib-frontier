/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceDrawing
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.SubdivisionEdges
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.GetD
import Mathlib.Analysis.Convex.Segment

/-!
# Distinct slopes at actual reference crossings

Distinct indexed reference routes that share a strict-interior point have different
supporting slopes. Parallel reference chords are allowed globally. The endpoints are
the actual points of the existing drawing; validity supplies membership before ranks are
compared, and unordered subdivision-edge injectivity retains every original occurrence.

For a parabola chord the slope is the sum of its endpoint real coordinates. Restricting
this function to the finite subtype of routes through one interior point supplies the
injective slope input to `exists_slopeDetour_separation`. No public crossing-class object
or global regularization is introduced. Disjoint patches, ordered gluing, crossing parity,
placement and the Hanani–Tutte/query criterion remain tracked in
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Main results

* `Cslib.Complexity.Graph.RotationRecognition.referenceDrawing_open_inter_subsingleton`:
  distinct indexed reference routes have at most one common strict-interior point.

* `Cslib.Complexity.Graph.RotationRecognition.referenceDrawing_slope_ne_of_interior_contact`:
  actual common strict-interior contact forces unequal supporting slopes at distinct indices.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Polygonal

private theorem referenceDrawing_pair_properties {I : FixedRotationInput} (hI : Valid I)
    (e f : Fin (subdivisionGraph I).edges.length) (hef : e ≠ f) :
    (openSegment ℝ ((referenceDrawing I).route e).start ((referenceDrawing I).route e).finish ∩
      openSegment ℝ ((referenceDrawing I).route f).start
        ((referenceDrawing I).route f).finish).Subsingleton ∧
    (∀ z : ℂ,
      z ∈ openSegment ℝ ((referenceDrawing I).route e).start ((referenceDrawing I).route e).finish →
      z ∈ openSegment ℝ ((referenceDrawing I).route f).start ((referenceDrawing I).route f).finish →
      ((referenceDrawing I).route e).start.re + ((referenceDrawing I).route e).finish.re ≠
        ((referenceDrawing I).route f).start.re + ((referenceDrawing I).route f).finish.re) := by
  classical
  let a := Dart.vertex (e, false)
  let b := Dart.vertex (e, true)
  let c := Dart.vertex (f, false)
  let d := Dart.vertex (f, true)
  let r := fun v => ((referenceOrder I).idxOf v : ℝ)
  have he' := subdivision_endpoint_spec hI e
  have hf' := subdivision_endpoint_spec hI f
  have hab : r a ≠ r b :=
    Nat.cast_injective.ne ((List.idxOf_inj (he'.1 false)).not.mpr he'.2)
  have hcd : r c ≠ r d :=
    Nat.cast_injective.ne ((List.idxOf_inj (hf'.1 false)).not.mpr hf'.2)
  have hpair : (s(a, b) : Sym2 ℕ) ≠ s(c, d) := by
    intro h
    apply hef
    apply subdivisionGraph_edge_injective hI
    simpa only [a, b, c, d, Dart.vertex, Graph.edgeEndpoint, Bool.false_eq_true, Fin.getElem_fin,
      ↓reduceIte, List.getD_eq_getElem _ _ e.isLt, List.getD_eq_getElem _ _ f.isLt] using h
  have hout : ¬(c ∈ (s(a, b) : Sym2 ℕ) ∧ d ∈ (s(a, b) : Sym2 ℕ)) := by
    intro h
    exact hpair ((Sym2.mem_and_mem_iff hf'.2).mp h)
  change
    (openSegment ℝ (parabolaPoint (r a)) (parabolaPoint (r b)) ∩
      openSegment ℝ (parabolaPoint (r c)) (parabolaPoint (r d))).Subsingleton ∧
    (∀ z : ℂ, z ∈ openSegment ℝ (parabolaPoint (r a)) (parabolaPoint (r b)) →
      z ∈ openSegment ℝ (parabolaPoint (r c)) (parabolaPoint (r d)) → r a + r b ≠ r c + r d)
  by_cases hc : c ∈ (s(a, b) : Sym2 ℕ)
  · have hd : d ≠ a ∧ d ≠ b := by
      have hn : d ∉ (s(a, b) : Sym2 ℕ) := fun h => hout ⟨hc, h⟩
      simpa only [Sym2.mem_iff, not_or] using hn
    have had : r a ≠ r d :=
      Nat.cast_injective.ne ((List.idxOf_inj (he'.1 false)).not.mpr hd.1.symm)
    have hbd : r b ≠ r d :=
      Nat.cast_injective.ne ((List.idxOf_inj (he'.1 true)).not.mpr hd.2.symm)
    constructor
    · rw [openSegment_symm ℝ (parabolaPoint (r c)) (parabolaPoint (r d))]
      exact parabolaChord_inter_subsingleton hab hcd.symm had hbd
    · intro z he hf
      have hswap : z ∈ openSegment ℝ (parabolaPoint (r d)) (parabolaPoint (r c)) := by
        simpa only [openSegment_symm] using hf
      simpa only [add_comm (r d) (r c)] using
        parabolaChord_slope_ne_of_mem_inter hab hcd.symm had hbd he hswap
  · have hc' : c ≠ a ∧ c ≠ b := by simpa only [Sym2.mem_iff, not_or] using hc
    have hac : r a ≠ r c :=
      Nat.cast_injective.ne ((List.idxOf_inj (he'.1 false)).not.mpr hc'.1.symm)
    have hbc : r b ≠ r c :=
      Nat.cast_injective.ne ((List.idxOf_inj (he'.1 true)).not.mpr hc'.2.symm)
    exact ⟨parabolaChord_inter_subsingleton hab hcd hac hbc,
      fun z he hf => parabolaChord_slope_ne_of_mem_inter hab hcd hac hbc he hf⟩

/-- Two distinct actual reference edges have at most one common strict-interior point.
No independence or supplied endpoint/rank inequalities are assumed. -/
theorem referenceDrawing_open_inter_subsingleton {I : FixedRotationInput} (hI : Valid I)
    (e f : Fin (subdivisionGraph I).edges.length) (hef : e ≠ f) :
    (openSegment ℝ ((referenceDrawing I).route e).start ((referenceDrawing I).route e).finish ∩
      openSegment ℝ ((referenceDrawing I).route f).start
        ((referenceDrawing I).route f).finish).Subsingleton :=
  (referenceDrawing_pair_properties hI e f hef).1

/-- Distinct actual reference edges through a common strict-interior point have unequal
parabolic chord slopes. No independence or supplied endpoint/rank inequalities are assumed. -/
theorem referenceDrawing_slope_ne_of_interior_contact {I : FixedRotationInput} (hI : Valid I)
    (e f : Fin (subdivisionGraph I).edges.length) (hef : e ≠ f) {z : ℂ}
    (he : z ∈ openSegment ℝ ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish)
    (hf : z ∈ openSegment ℝ ((referenceDrawing I).route f).start
      ((referenceDrawing I).route f).finish) :
    ((referenceDrawing I).route e).start.re + ((referenceDrawing I).route e).finish.re ≠
      ((referenceDrawing I).route f).start.re + ((referenceDrawing I).route f).finish.re := by
  exact (referenceDrawing_pair_properties hI e f hef).2 z he hf

end Cslib.Complexity.Graph.RotationRecognition
