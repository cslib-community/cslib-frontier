/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary actual global reference regularization clients)

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceRegularization
import CslibFrontierTests.RotationReferencePatchAssembly
import CslibFrontierTests.RotationReferenceStar

/-!
Ordinary public clients consume the actual joint global theorem. The existing five-loop
fixture has a genuine nonvertex triple and multiple patches on an indexed route; the
source fixture and its checked coordinate proof are not reconstructed here. The newly
chosen contact coordinate is existential, not asserted to equal an old center.
-/

public section

namespace Cslib.Tests.RotationReferenceRegularization

open Cslib.Polygonal Cslib.Complexity.Graph Cslib.Complexity.Graph.RotationRecognition

-- A real old pair at the source triple has a new nonvertex common support point with
-- actual OPEN global segment parameters and nonzero actual segment determinant.
example :
    let I := RotationReferencePatchAssembly.tripleInput
    ∃ (A : ReferencePatchAssembly I)
      (e f : Fin (subdivisionGraph I).edges.length) (w : ℂ)
      (i : Fin (A.drawing.route e).segments) (j : Fin (A.drawing.route f).segments)
      (u v : ℝ),
      e ≠ f ∧ (∀ n ∈ (subdivisionGraph I).vertices, w ≠ A.drawing.vertex n) ∧
      u ∈ Set.Ioo 0 1 ∧ v ∈ Set.Ioo 0 1 ∧
      (A.drawing.route e).eval i u = w ∧ (A.drawing.route f).eval j v = w ∧
      let a := (A.drawing.route e).point i.succ - (A.drawing.route e).point i.castSucc
      let b := (A.drawing.route f).point j.succ - (A.drawing.route f).point j.castSucc
      a.re * b.im - a.im * b.re ≠ 0 := by
  obtain ⟨hI, e, f, g, hef, heg, hfg, he, hf, hg, hvertex⟩ :=
    RotationReferencePatchAssembly.source_has_nonvertex_triple
  obtain ⟨A, κ, hpairs, hno3⟩ := exists_reference_crossing_regularization hI
  have hw := (hpairs e f hef).1.1 ⟨he, hf⟩
  obtain ⟨i, j, u, v, hu, hv, hi, hj, hdet⟩ := (hpairs e f hef).2.2 _ hw
  exact ⟨A, e, f, κ e f ⟨9, 90⟩, i, j, u, v, hef, hw.2.2, hu, hv, hi, hj, hdet⟩

-- In particular the old THREE simultaneous incidences at (9,90) cannot ALL survive
-- in the new drawing. The point is known to avoid EVERY declared vertex, not just
-- the endpoints of these three selected routes.
example :
    let I := RotationReferencePatchAssembly.tripleInput
    ∃ (A : ReferencePatchAssembly I) (e f g : Fin (subdivisionGraph I).edges.length),
      e ≠ f ∧ e ≠ g ∧ f ≠ g ∧
      ¬((⟨9, 90⟩ : ℂ) ∈ (A.drawing.route e).support ∧
        (⟨9, 90⟩ : ℂ) ∈ (A.drawing.route f).support ∧
        (⟨9, 90⟩ : ℂ) ∈ (A.drawing.route g).support) := by
  obtain ⟨hI, e, f, g, hef, heg, hfg, he, hf, hg, hvertex⟩ :=
    RotationReferencePatchAssembly.source_has_nonvertex_triple
  obtain ⟨A, κ, hpairs, hno3⟩ := exists_reference_crossing_regularization hI
  refine ⟨A, e, f, g, hef, heg, hfg, ?_⟩
  rintro ⟨he', hf', hg'⟩
  exact hno3 e f g hef heg hfg _
    (by simpa only [A.vertex_eq] using hvertex) he' hf' hg'

-- Surjectivity covers an arbitrary new nonvertex pair contact: it comes from an
-- actual OLD common strict-interior point. This exercises the no-extra-contact half.
example {I : FixedRotationInput} (hI : Valid I) :
    ∃ A : ReferencePatchAssembly I, ∀ e f : Fin (subdivisionGraph I).edges.length,
      e ≠ f → ∀ w : ℂ, w ∈ (A.drawing.route e).support → w ∈ (A.drawing.route f).support →
      (∀ v ∈ (subdivisionGraph I).vertices, w ≠ A.drawing.vertex v) →
      ∃ z : ℂ, z ∈ openSegment ℝ ((referenceDrawing I).route e).start
          ((referenceDrawing I).route e).finish ∧
        z ∈ openSegment ℝ ((referenceDrawing I).route f).start
          ((referenceDrawing I).route f).finish := by
  obtain ⟨A, κ, hpairs, hno3⟩ := exists_reference_crossing_regularization hI
  refine ⟨A, ?_⟩
  intro e f hef w he hf hv
  obtain ⟨z, hz, _⟩ := (hpairs e f hef).1.2.2 ⟨he, hf, hv⟩
  exact ⟨z, hz.1, hz.2⟩

-- The public star input retains parallel occurrences, both loop ends, a decreasing
-- source orientation and a fixed isolate. Every frozen GLOBAL route is literal;
-- the outgoing vector property holds at BOTH end tags without a false extra sign.
example :
    let I := RotationReferenceStar.input
    ∃ A : ReferencePatchAssembly I,
      (∀ e : Fin (subdivisionGraph I).edges.length,
        ((subdivide I)[e.val]'(by
          simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true →
          A.drawing.route e = (referenceDrawing I).route e) ∧
      A.drawing.vertex 2 = (referenceDrawing I).vertex 2 ∧
      ∀ e b, ∃ c : ℝ, 0 < c ∧
        (A.drawing.route e).germ b = c • ((referenceDrawing I).route e).germ b := by
  let I := RotationReferenceStar.input
  have hI : Valid I := (validate_eq_true_iff I).mp (by decide +kernel)
  obtain ⟨A, κ, hpairs, hno3⟩ := exists_reference_crossing_regularization hI
  refine ⟨A, ?_, congrFun A.vertex_eq 2, A.germs⟩
  intro e he
  have hr := A.route_eq e
  dsimp only at hr
  rw [ite_eq_left he] at hr
  exact hr

-- Empty edges retain both isolates and introduce no requirement for a nonempty
-- crossing class. There is still no zero-segment Route representation.
example :
    let I : FixedRotationInput := ⟨⟨[0, 1], []⟩, [none, some []]⟩
    ∃ A : ReferencePatchAssembly I,
      A.drawing.vertex = (referenceDrawing I).vertex ∧
      ∀ e : Fin (subdivisionGraph I).edges.length,
        A.drawing.route e = (referenceDrawing I).route e := by
  let I : FixedRotationInput := ⟨⟨[0, 1], []⟩, [none, some []]⟩
  have hI : Valid I := (validate_eq_true_iff I).mp (by decide +kernel)
  obtain ⟨A, κ, hpairs, hno3⟩ := exists_reference_crossing_regularization hI
  exact ⟨A, A.vertex_eq, fun e => Fin.elim0 e⟩


-- A selected empty center list retains the actual original free route as well;
-- this tests the literal construction field, not only equality of supports.
example {I : FixedRotationInput} (hI : Valid I) :
    ∃ A : ReferencePatchAssembly I, ∀ e, A.centers e = [] →
      A.drawing.route e = (referenceDrawing I).route e := by
  obtain ⟨A, κ, hpairs, hno3⟩ := exists_reference_crossing_regularization hI
  refine ⟨A, ?_⟩
  intro e he
  simpa only [he, ite_self] using A.route_eq e

-- No3 must exclude declared vertices: this degree-four prescribed star STILL has
-- three distinct indexed supports through its declared center after regularization.
example :
    let I := RotationReferenceStar.input
    ∃ A : ReferencePatchAssembly I,
      A.drawing.vertex 0 ∈ (A.drawing.route ⟨0, by decide⟩).support ∧
      A.drawing.vertex 0 ∈ (A.drawing.route ⟨2, by decide⟩).support ∧
      A.drawing.vertex 0 ∈ (A.drawing.route ⟨3, by decide⟩).support := by
  let I := RotationReferenceStar.input
  have hI : Valid I := (validate_eq_true_iff I).mp (by decide +kernel)
  obtain ⟨A, κ, hpairs, hno3⟩ := exists_reference_crossing_regularization hI
  have hs (e : Fin (subdivisionGraph I).edges.length) (tag : Bool)
      (hv : Dart.vertex (e, tag) = 0) :
      A.drawing.vertex 0 ∈ (A.drawing.route e).support := by
    rw [← hv, ← A.drawing.endpoint_eq e tag]
    cases tag
    · simpa only [Route.eval, AffineMap.lineMap_apply_zero, Fin.castSucc_zero,
        Route.endpoint, Bool.false_eq_true, ↓reduceIte, Route.start] using
        (A.drawing.route e).at_mem_support 0
          (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    · simpa only [Route.eval, AffineMap.lineMap_apply_one, Fin.succ_last,
        Route.endpoint, ↓reduceIte, Route.finish] using
        (A.drawing.route e).at_mem_support (Fin.last (A.drawing.route e).bends)
          (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
  exact ⟨A, hs ⟨0, by decide⟩ false (by decide +kernel),
    hs ⟨2, by decide⟩ true (by decide +kernel), hs ⟨3, by decide⟩ false (by decide +kernel)⟩

end Cslib.Tests.RotationReferenceRegularization
