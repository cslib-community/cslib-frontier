/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RegularContacts
public import CslibFrontier.Foundations.Geometry.Polygonal.Germs
public import CslibFrontier.Foundations.Geometry.Polygonal.RayParityColors
import CslibFrontier.Foundations.Geometry.Polygonal.SegmentRays

/-!
# Distinct outgoing geometric rays in polygonal drawings

Distinct incident darts of a genuine polygonal embedding have distinct outgoing ray
directions. The proof constructs a small common point when the arguments are equal, then
uses the actual segment contact conditions. The same-edge case treats the two ends of a
loop using route simplicity. There is no degree bound or local-disk assumption.
Regular drawings with simple routes also have distinct outgoing directions, since
the open parts of distinct segments meet at most once.

## Main results

* `Cslib.Complexity.Graph.PolygonalDrawing.IsEmbedding.directions_injective`.
* `Cslib.Complexity.Graph.PolygonalDrawing.HasRegularContacts.directions_injective`.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal

/-- A polygonal embedding has different outgoing rays at distinct incident darts,
including the two ends of a loop. This follows from segment geometry, not from rotation data. -/
theorem IsEmbedding.directions_injective {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (a b : Dart G) (hv : a.vertex = b.vertex)
    (harg : D.direction a = D.direction b) : a = b := by
  by_contra hab
  have harg' : (D.germ a).arg = (D.germ b).arg := Complex.arg_coe_angle_eq_iff.mp harg
  obtain ⟨s, hs, t, ht, hst⟩ := exists_small_smul_eq_of_arg_eq
    (hD.germ_ne_zero a) (hD.germ_ne_zero b) harg' (by norm_num : (0 : ℝ) < 1 / 3)
  have hs' : s ∈ Set.Ioo 0 1 := ⟨hs.1, lt_trans hs.2 (by norm_num)⟩
  have ht' : t ∈ Set.Ioo 0 1 := ⟨ht.1, lt_trans ht.2 (by norm_num)⟩
  have hpoint :
      (D.route a.1).eval ((D.route a.1).endSegment a.2) (Route.endTime a.2 s) =
      (D.route b.1).eval ((D.route b.1).endSegment b.2) (Route.endTime b.2 t) := by
    rw [Route.eval_near_end, Route.eval_near_end, D.endpoint_eq, D.endpoint_eq]
    exact congrArg₂ (· + ·) (congrArg D.vertex hv) hst
  by_cases hedge : a.1 = b.1
  · rcases a with ⟨e, ba⟩
    rcases b with ⟨f, bb⟩
    change e = f at hedge
    subst f
    obtain heq | ⟨ha, -⟩ | ⟨ha, -⟩ := hD.simple e _ _ _ _
      (Route.endTime_mem ba ⟨hs'.1.le, hs'.2.le⟩)
      (Route.endTime_mem bb ⟨ht'.1.le, ht'.2.le⟩) hpoint
    · rw [Route.position_near_end, Route.position_near_end] at heq
      have hn : (1 : ℝ) ≤ (D.route e).segments := by
        exact_mod_cast Nat.le_add_left 1 (D.route e).bends
      cases ba <;> cases bb <;> simp only [Bool.false_eq_true, ↓reduceIte] at heq
      · exact hab rfl
      · linarith [hs.2, ht.2]
      · linarith [hs.2, ht.2]
      · exact hab rfl
    · exact (D.route e).not_atEnd_near_end ba false hs' ha
    · exact (D.route e).not_atEnd_near_end ba true hs' ha
  · obtain ⟨ba, _, ha, _, _⟩ := hD.edge_contacts a.1 b.1 hedge _ _ _ _
      (Route.endTime_mem a.2 ⟨hs'.1.le, hs'.2.le⟩)
      (Route.endTime_mem b.2 ⟨ht'.1.le, ht'.2.le⟩) hpoint
    exact (D.route a.1).not_atEnd_near_end a.2 ba hs' ha

/-- The segment-end occurrence corresponding to one actual graph dart. -/
@[expose] def segmentEnd {G : Graph} (D : PolygonalDrawing G) (d : Dart G) :
    D.SegmentIndex × Bool := (⟨d.1, (D.route d.1).endSegment d.2⟩, d.2)

/-- Distinct graph darts retain distinct indexed segment ends, including loop ends. -/
theorem segmentEnd_injective {G : Graph} (D : PolygonalDrawing G) :
    Function.Injective D.segmentEnd := by
  intro a b h
  exact congrArg (fun k : D.SegmentIndex × Bool => (k.1.1, k.2)) h

/-- The segment-end point of a dart is its actual named vertex. -/
theorem segmentEnd_endpoint {G : Graph} (D : PolygonalDrawing G) (d : Dart G) :
    rayEndpoint D.segmentStart D.segmentFinish (D.segmentEnd d) = D.vertex d.vertex := by
  rw [← D.endpoint_eq d.1 d.2]
  rcases d with ⟨e, tag⟩
  cases tag <;> simp [segmentEnd, rayEndpoint, segmentStart, segmentFinish,
    Route.endSegment, Route.endpoint, Route.start, Route.finish]

/-- The outgoing vector at a dart's segment end is its actual drawing germ. -/
theorem segmentEnd_vector {G : Graph} (D : PolygonalDrawing G) (d : Dart G) :
    rayEndVector D.segmentStart D.segmentFinish (D.segmentEnd d) = D.germ d := by
  rcases d with ⟨e, tag⟩
  cases tag <;> simp [segmentEnd, rayEndVector, segmentStart, segmentFinish,
    Route.endSegment, germ, Route.germ, Route.start, Route.finish]

/-- Distinct incident darts of a regular drawing with simple routes have distinct directions.
Equal directions would give two common points in the open parts of their end segments. -/
theorem HasRegularContacts.directions_injective {G : Graph} {D : PolygonalDrawing G}
    (hD : D.HasRegularContacts) (hsimple : ∀ e, (D.route e).IsSimple) (a b : Dart G)
    (hv : a.vertex = b.vertex) (harg : D.direction a = D.direction b) : a = b := by
  apply D.segmentEnd_injective
  apply rayEndVector_injective_of_open_inter_subsingleton D.segmentStart D.segmentFinish
    (fun i => (hsimple i.1).segment_ne i.2) hD.open_inter_subsingleton
  · rw [D.segmentEnd_endpoint, D.segmentEnd_endpoint, hv]
  · rw [D.segmentEnd_vector, D.segmentEnd_vector]
    have harg' : (D.germ a).arg = (D.germ b).arg := Complex.arg_coe_angle_eq_iff.mp harg
    have hsign : (D.germ a).im < 0 ↔ (D.germ b).im < 0 := by
      rw [← Complex.arg_neg_iff, ← Complex.arg_neg_iff, harg']
    by_cases h : (D.germ b).im < 0
    · simp only [turnArg, h, hsign.mpr h, harg', ↓reduceIte]
    · simp only [turnArg, h, mt hsign.mp h, harg', ↓reduceIte]

end Cslib.Complexity.Graph.PolygonalDrawing
