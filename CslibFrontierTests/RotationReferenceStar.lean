/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary clients of prescribed reference-star geometry)

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceSpokeEmbedding
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Bouquet
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SplitOrder
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.EmbeddingNecessity
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.RecoveryInvariants
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.SubdivisionContraction
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceRecut
import Mathlib.Tactic.FinCases
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

private def doubleLoop : FixedRotationInput :=
  ⟨⟨[0], [(0, 0), (0, 0)]⟩, [some [2, 3, 0, 1]]⟩

private def firstLoop : Fin doubleLoop.graph.edges.length := ⟨0, by decide⟩
private def secondLoop : Fin doubleLoop.graph.edges.length := ⟨1, by decide⟩

-- The word [2, 3, 0, 1] alternates the two pairs of cut ports.
example {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ D : PolygonalDrawing doubleLoop.graph,
      let port := D.cutPort ρ
      (openSegment ℝ (port (firstLoop, false)) (port (secondLoop, false)) ∩
        openSegment ℝ (port (firstLoop, true)) (port (secondLoop, true))).Nonempty := by
  have hI : Valid doubleLoop := (validate_eq_true_iff _).mp (by decide +kernel)
  let c : RotationCertificate := ⟨[1, 2, 3, 0]⟩
  have hrot : RotationCertificate.verifyRotation doubleLoop.graph c = true := by decide +kernel
  let r := RotationCertificate.decode doubleLoop.graph c hrot
  have hfix : Realizes doubleLoop r := verifyFixed_realizes hrot (by decide +kernel)
  have hloop : ∀ e : Fin doubleLoop.graph.edges.length,
      Dart.vertex (e, false) = Dart.vertex (e, true) := by decide +kernel
  have hw : doubleLoop.orders.getD 0 none = some [2, 3, 0, 1] := by decide +kernel
  refine ⟨PolygonalDrawing.bouquet r hloop, ?_⟩
  apply ((PolygonalDrawing.bouquet_realizes r hloop).cutPort_chords_inter_iff_alternates hρ
    (firstLoop, false) (secondLoop, false) (firstLoop, true) (secondLoop, true)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl).mpr
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl, rfl, rfl, ?_⟩
  rw [hfix.mem_rotationInterval_iff_fixedWord hI hw
    (a := (firstLoop, true)) (b := (firstLoop, false)) (c := (secondLoop, true))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hfix.mem_rotationInterval_iff_fixedWord hI hw
      (a := (firstLoop, true)) (b := (secondLoop, false)) (c := (secondLoop, true))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  decide +kernel

-- The fixed-order bouquet makes the query accept and preserves both ends of the first loop.
example :
    ∃ D : PolygonalDrawing doubleLoop.graph, D.IsEmbedding ∧
      query doubleLoop = true ∧
      sbtw (((D.cutPort 1 (secondLoop, false) - D.vertex 0).arg : ℝ) : Real.Angle)
        (((D.cutPort 1 (firstLoop, true) - D.vertex 0).arg : ℝ) : Real.Angle)
        (((D.cutPort 1 (firstLoop, false) - D.vertex 0).arg : ℝ) : Real.Angle) ∧
      (∃ T : {d : Dart doubleLoop.graph // d.vertex = 0} → Route,
        (∀ d, (T d).start = D.vertex 0 ∧ (T d).finish = D.cutPort 1 d.val ∧
          (((T d).germ false).arg : Real.Angle) =
            (referenceDrawing doubleLoop).direction (subdivisionDart doubleLoop d.val) ∧
          (T d).IsSimple ∧ (T d).support \ Metric.ball (D.vertex 0) 1 = {D.cutPort 1 d.val}) ∧
        Pairwise (fun d e => (T d).support ∩ (T e).support = {D.vertex 0})) ∧
      (∃ ρ > (0 : ℝ), ∃ E F : PolygonalDrawing (subdivisionGraph doubleLoop),
        F.IsEmbedding ∧ F.vertex = E.vertex ∧ F.vertex 0 = D.vertex 0 ∧
        (∀ e, (subdivisionEdgeIndex doubleLoop e).piece = 1 → F.route e = E.route e) ∧
        (∀ d : Dart doubleLoop.graph,
          F.vertex (subdivisionDart doubleLoop d).reverse.vertex = D.cutPort ρ d ∧
          F.direction (subdivisionDart doubleLoop d) =
            (referenceDrawing doubleLoop).direction (subdivisionDart doubleLoop d)) ∧
        ∃ A : PolygonalDrawing doubleLoop.graph, A.IsEmbedding ∧ A.vertex = F.vertex ∧
          (∀ i, (A.route i).support = ⋃ k : Fin 3,
            (F.route (⟨i, k⟩ : SubdivisionEdgeIndex doubleLoop).edge).support) ∧
          ∀ d : Dart doubleLoop.graph, A.germ d = F.germ (subdivisionDart doubleLoop d)) ∧
      (∃ H : PolygonalDrawing (subdivisionGraph doubleLoop), H.IsEmbedding ∧
        H.vertex 0 = referencePoint doubleLoop 0 ∧
        H.route (subdivisionDart doubleLoop (firstLoop, false)).1 =
          (referenceDrawing doubleLoop).route (subdivisionDart doubleLoop (firstLoop, false)).1 ∧
        H.route (subdivisionDart doubleLoop (firstLoop, true)).1 =
          (referenceDrawing doubleLoop).route (subdivisionDart doubleLoop (firstLoop, true)).1) ∧
      ∃ s ∈ Set.Ioo (0 : ℝ) 1, ∃ G : PolygonalDrawing (subdivisionGraph doubleLoop), G.IsEmbedding ∧
        G.vertex 0 = referencePoint doubleLoop 0 ∧
        let left := subdivisionDart doubleLoop (firstLoop, false)
        let right := subdivisionDart doubleLoop (firstLoop, true)
        let a := referencePoint doubleLoop 0
        let u := a + s • (referenceDrawing doubleLoop).germ left
        let v := a + s • (referenceDrawing doubleLoop).germ right
        G.vertex left.reverse.vertex = u ∧ G.vertex right.reverse.vertex = v ∧ u ≠ v ∧
          G.route left.1 = Route.line a u ∧ G.route right.1 = Route.line v a := by
  have hI : Valid doubleLoop := (validate_eq_true_iff _).mp (by decide +kernel)
  let c : RotationCertificate := ⟨[1, 2, 3, 0]⟩
  have hrot : RotationCertificate.verifyRotation doubleLoop.graph c = true := by decide +kernel
  let r := RotationCertificate.decode doubleLoop.graph c hrot
  have hfix : Realizes doubleLoop r := verifyFixed_realizes hrot (by decide +kernel)
  have hg : r.NumericalGenusZero :=
    (RotationCertificate.verifyEuler_eq_true_iff hrot).mp (by decide +kernel)
  have hloop : ∀ e : Fin doubleLoop.graph.edges.length,
      Dart.vertex (e, false) = Dart.vertex (e, true) := by decide +kernel
  let D := PolygonalDrawing.bouquet r hloop
  have hends : ∀ v ∈ doubleLoop.graph.incidenceVertices, v ∈ doubleLoop.graph.vertices := by
    intro v hv
    simpa [doubleLoop, incidenceVertices] using hv
  have hD : D.IsEmbedding := PolygonalDrawing.bouquet_isEmbedding r hends hg hloop
  have hw : doubleLoop.orders.getD 0 none = some [2, 3, 0, 1] := by decide +kernel
  refine ⟨D, hD, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact query_eq_true_of_rotation_embedding hI hD (PolygonalDrawing.bouquet_realizes r hloop) hfix
  · have a := cutPort_clockwise_iff_reference hI (PolygonalDrawing.bouquet_realizes r hloop)
      hfix zero_lt_one hw (a := (firstLoop, false)) (b := (firstLoop, true))
      (c := (secondLoop, false)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    apply a.mpr
    apply (referenceDrawing_fixedWord_clockwise_iff hI hw
      (a := (firstLoop, false)) (b := (firstLoop, true)) (c := (secondLoop, false))
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr
    decide +kernel
  · obtain ⟨T, hT, hpair⟩ := exists_reference_spokes_at_cutPorts hI hD
      (PolygonalDrawing.bouquet_realizes r hloop) hfix zero_lt_one hw
    refine ⟨T, ?_, hpair⟩
    intro d
    obtain ⟨hs, ht, ⟨a, ha, he⟩, hsim, hb⟩ := hT d
    refine ⟨hs, ht, ?_, hsim, hb⟩
    simp only [he, Complex.real_smul, Complex.arg_ofReal_mul ha _, PolygonalDrawing.direction]
  · obtain ⟨ε, hε, hall⟩ := exists_subdivision_embedding_with_reference_spokes hI hD
      (PolygonalDrawing.bouquet_realizes r hloop) hfix
    obtain ⟨E, F, _, hF, hvertices, hcenter, hports, hmiddle, _, hfixed⟩ :=
      hall (ε / 2) ⟨half_pos hε, half_lt_self hε⟩
    refine ⟨ε / 2, half_pos hε, E, F, hF, hvertices, hcenter 0 (by decide +kernel),
      hmiddle, ?_, ?_⟩
    · intro d
      have hd : (doubleLoop.orders.getD d.vertex none).isSome := by
        rcases d with ⟨e, b⟩
        fin_cases e <;> cases b <;> decide +kernel
      obtain ⟨a, ha, hger⟩ := hfixed d hd
      refine ⟨hports d, ?_⟩
      simp only [PolygonalDrawing.direction, hger, Complex.real_smul, Complex.arg_ofReal_mul ha _]
    · exact exists_contracted_subdivision_embedding hI hF
  · obtain ⟨H, hH, hcenters, hspokes⟩ :=
      exists_subdivision_embedding_with_frozen_reference_routes hI hD
        (PolygonalDrawing.bouquet_realizes r hloop) hfix
    exact ⟨H, hH, hcenters 0 (by decide +kernel),
      hspokes _ (by decide +kernel), hspokes _ (by decide +kernel)⟩
  · obtain ⟨ε, hε, hscale⟩ :=
      exists_subdivision_embedding_with_scaled_reference_spokes hI hD
        (PolygonalDrawing.bouquet_realizes r hloop) hfix
    have hs : ε / 2 ∈ Set.Ioo (0 : ℝ) ε := ⟨half_pos hε.1, half_lt_self hε.1⟩
    obtain ⟨G, hG, hposition, hspoke⟩ := hscale (ε / 2) hs
    obtain ⟨hleft, hl⟩ := hspoke (firstLoop, false) (by decide +kernel)
    obtain ⟨hright, hr⟩ := hspoke (firstLoop, true) (by decide +kernel)
    refine ⟨ε / 2, ⟨hs.1, hs.2.trans_le hε.2⟩, G, hG, hposition 0 (by decide +kernel),
      hleft, hright, ?_, hl, hr⟩
    have hn : G.vertex (subdivisionDart doubleLoop (firstLoop, false)).reverse.vertex ≠
        G.vertex (subdivisionDart doubleLoop (firstLoop, true)).reverse.vertex :=
      hG.vertex_ne (by decide +kernel) (by decide +kernel) (by decide +kernel)
    exact fun h => hn (hleft.trans (h.trans hright.symm))

end Cslib.Tests.RotationReferenceStar
