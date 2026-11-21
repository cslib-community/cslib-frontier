/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary clients of actual frozen-reference geometry)

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.FrozenReference
import CslibFrontier.Foundations.Geometry.Polygonal.LineEnds
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.CutTransport
import CslibFrontier.Foundations.Geometry.Polygonal.CutTransport
import Mathlib.Tactic.NormNum

/-! Ordinary clients keep both loop ends, parallel occurrences, unused fresh leaves, a fixed
isolate and degree-five stars. Contacts use arbitrary closed-interval parameters. The named
`all_free_frame` client checks the complete isolated-point frame when every edge is removed. -/

public section

namespace Cslib.Tests.RotationFrozenReference

open Cslib.Polygonal Cslib.Complexity.Graph Cslib.Complexity.Graph.RotationRecognition

private def input : FixedRotationInput :=
  ⟨⟨[0, 1, 2], [(0, 0), (0, 1), (0, 1)]⟩, [some [2, 1, 4, 0], none, some []]⟩

private theorem valid_input : Valid input := validate_eq_true_iff input |>.mp (by decide +kernel)

private theorem input_word : input.orders.getD 0 none = some [2, 1, 4, 0] := rfl

private def loopFirst : Dart input.graph := (⟨0, by decide⟩, false)
private def loopLast : Dart input.graph := (⟨0, by decide⟩, true)
private def parallelFirst : Dart input.graph := (⟨1, by decide⟩, false)
private def parallelSecond : Dart input.graph := (⟨2, by decide⟩, false)
private def firstFull : Fin (subdivisionGraph input).edges.length := ⟨0, by decide⟩
private def loopLastFull : Fin (subdivisionGraph input).edges.length := ⟨2, by decide⟩

-- The raw classifier has no Valid premise, even for a malformed declaration list.
example :
    let J : FixedRotationInput := ⟨⟨[], [(0, 0)]⟩, [some []]⟩
    ∃ d : Dart J.graph, (⟨2, by decide⟩ : Fin (subdivisionGraph J).edges.length) =
      (subdivisionDart J d).1 ∧ (J.orders.getD d.vertex none).isSome = true := by
  dsimp only
  let J : FixedRotationInput := ⟨⟨[], [(0, 0)]⟩, [some []]⟩
  exact (frozen_iff_exists_subdivisionDart J ⟨2, by decide⟩).mp (by decide +kernel)

-- The retained end still has the last-end tag and its own fresh neighbor, not the other loop end.
example :
    (frozenReferenceDart valid_input input_word loopLast (by decide +kernel)).2 = true ∧
    (frozenReferenceDart valid_input input_word loopLast (by decide +kernel)).vertex = 0 ∧
    (frozenReferenceDart valid_input input_word loopLast (by decide +kernel)).reverse.vertex =
      4 := by
  exact frozenReferenceDart_endpoints valid_input input_word loopLast (by decide +kernel)

-- The literal outgoing vector is retained, through the filtered route rather than a new fan.
example : (frozenReferenceDrawing input).germ
    (frozenReferenceDart valid_input input_word loopLast (by decide +kernel)) =
      referencePoint input 4 - referencePoint input 0 := by
  rw [frozenReferenceDrawing_germ_frozenReferenceDart, referenceDrawing_subdivisionDart_germ]
  rfl

-- These two frozen routes can meet only at their common center: first time0, last time1.
example {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : ((referenceDrawing input).route firstFull).eval 0 s =
      ((referenceDrawing input).route loopLastFull).eval 0 t) : s = 0 ∧ t = 1 := by
  obtain ⟨b, c, hb, hc, hv⟩ := referenceDrawing_frozen_edge_contacts valid_input
    firstFull loopLastFull (by decide +kernel) (by decide +kernel) (by decide +kernel)
    0 0 hs ht heq
  have hbs := (Route.atEnd_line_iff _ _ 0 s b).mp hb
  have hct := (Route.atEnd_line_iff _ _ 0 t c).mp hc
  cases b <;> cases c <;>
    norm_num [firstFull, loopLastFull, Dart.vertex, Cslib.Complexity.Graph.edgeEndpoint,
      subdivisionGraph, subdivide, input] at hv
  exact ⟨hbs, hct⟩

-- The unused target-side fresh point and the original fixed isolate remain declared and isolated.
example : 6 ∈ (frozenGraph input).vertices ∧ 2 ∈ (frozenGraph input).vertices ∧
    (∀ e ∈ (frozenGraph input).edges, e.1 ≠ 6 ∧ e.2 ≠ 6) ∧
    (frozenReferenceDrawing input).vertex 6 ≠ (frozenReferenceDrawing input).vertex 0 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact (frozenReferenceDrawing_isEmbedding valid_input).vertex_ne
    (by decide +kernel) (by decide +kernel) (by decide)

-- Clockwise order is preserved with the exact full word and reversed c,b,a angle convention.
example :
    sbtw ((frozenReferenceDrawing input).direction
      (frozenReferenceDart valid_input input_word parallelSecond (by decide +kernel)))
      ((frozenReferenceDrawing input).direction
        (frozenReferenceDart valid_input input_word loopLast (by decide +kernel)))
      ((frozenReferenceDrawing input).direction
        (frozenReferenceDart valid_input input_word parallelFirst (by decide +kernel))) ∧
    ¬sbtw ((frozenReferenceDrawing input).direction
      (frozenReferenceDart valid_input input_word parallelFirst (by decide +kernel)))
      ((frozenReferenceDrawing input).direction
        (frozenReferenceDart valid_input input_word loopLast (by decide +kernel)))
      ((frozenReferenceDrawing input).direction
        (frozenReferenceDart valid_input input_word parallelSecond (by decide +kernel))) := by
  have h := (frozenReferenceDrawing_fixedWord_clockwise_iff valid_input
    (v := 0) (word := [2, 1, 4, 0]) (by decide +kernel)
    (a := parallelFirst) (b := loopLast) (c := parallelSecond)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr (by decide +kernel)
  exact ⟨h, h.not_sbtw⟩

private def bothFixed : FixedRotationInput :=
  ⟨input.graph, [some [2, 1, 4, 0], some [5, 3], some []]⟩

private theorem valid_bothFixed : Valid bothFixed :=
  validate_eq_true_iff bothFixed |>.mp (by decide +kernel)

-- Two different center blocks cannot meet, including endpoints and both possible orientations.
example {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    ((referenceDrawing bothFixed).route ⟨0, by decide⟩).eval 0 s ≠
      ((referenceDrawing bothFixed).route ⟨5, by decide⟩).eval 0 t := by
  intro heq
  obtain ⟨b, c, _, _, hv⟩ := referenceDrawing_frozen_edge_contacts valid_bothFixed
    ⟨0, by decide⟩ ⟨5, by decide⟩ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) 0 0 hs ht heq
  cases b <;> cases c <;>
    norm_num [Dart.vertex, Cslib.Complexity.Graph.edgeEndpoint, subdivisionGraph, subdivide,
      bothFixed, input] at hv

-- The reference spoke on the left stays a positive horizontal distance from the right one.
example (z w : ℂ)
    (hz : z ∈ ((referenceDrawing bothFixed).route ⟨0, by decide⟩).support)
    (hw : w ∈ ((referenceDrawing bothFixed).route ⟨5, by decide⟩).support) :
    z.re + 1 / 4 < w.re := by
  let a : Dart bothFixed.graph := (⟨0, by decide⟩, false)
  let b : Dart bothFixed.graph := (⟨1, by decide⟩, true)
  obtain ⟨right, _, hsep, hstrip⟩ := exists_frozen_reference_strips valid_bothFixed
  have ha := hstrip a (by decide +kernel) z hz
  have hb := hstrip b (by decide +kernel) w hw
  have hgap := hsep a.vertex (by decide +kernel) b.vertex (by decide +kernel) (by decide +kernel)
  linarith only [ha.2, hb.1, hgap]

-- One map fixes both centers while halving both complete, oppositely oriented spokes.
example :
    ∃ F : ℂ → ℂ, Function.Injective F ∧
      F (referencePoint bothFixed 0) = referencePoint bothFixed 0 ∧
      F (referencePoint bothFixed 1) = referencePoint bothFixed 1 ∧
      (∀ z ∈ ((referenceDrawing bothFixed).route ⟨0, by decide⟩).support,
        F z = referencePoint bothFixed 0 + (1 / 2 : ℝ) • (z - referencePoint bothFixed 0)) ∧
      ∀ z ∈ ((referenceDrawing bothFixed).route ⟨5, by decide⟩).support,
        F z = referencePoint bothFixed 1 + (1 / 2 : ℝ) • (z - referencePoint bothFixed 1) := by
  let a : Dart bothFixed.graph := (⟨0, by decide⟩, false)
  let b : Dart bothFixed.graph := (⟨1, by decide⟩, true)
  obtain ⟨F, _, hcenter, hspoke, _⟩ :=
    exists_frozen_reference_compression valid_bothFixed (s := 1 / 2) (by constructor <;> norm_num)
  have ha : a.vertex = 0 := by decide +kernel
  have hb : b.vertex = 1 := by decide +kernel
  have hFa := hspoke a (by decide +kernel)
  have hFb := hspoke b (by decide +kernel)
  rw [ha] at hFa
  rw [hb] at hFb
  exact ⟨F, F.injective, hcenter 0 (by decide +kernel), hcenter 1 (by decide +kernel), hFa, hFb⟩

-- A vertical segment in the compressed plane needs no subdivision, even on a cut line.
example (z w : ℂ) (h : z.re = w.re) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    ∃ F : ℂ ≃ₜ ℂ, F (referencePoint bothFixed 0) = referencePoint bothFixed 0 ∧
      F.symm (AffineMap.lineMap z w t) = AffineMap.lineMap (F.symm z) (F.symm w) t := by
  obtain ⟨F, _, hcenter, _, hline⟩ :=
    exists_frozen_reference_compression valid_bothFixed (s := 1 / 2) (by constructor <;> norm_num)
  refine ⟨F, hcenter 0 (by decide +kernel), hline z w ?_ t ht⟩
  intro x _
  rw [h, min_self, max_self]
  exact fun hx => (not_lt_of_ge hx.1.le) hx.2

-- Each actual indexed piece in the compressed plane is transported by straight interpolation.
example (a b : ℂ) :
    ∃ (F : ℂ ≃ₜ ℂ) (cuts : Finset ℝ),
      let times := segmentCuts cuts a.re b.re
      ∀ (k : ℕ) (hk : k + 1 < times.length) (t : ℝ), t ∈ Set.Icc 0 1 →
        F.symm (AffineMap.lineMap a b (AffineMap.lineMap times[k] times[k + 1] t)) =
          AffineMap.lineMap (F.symm (AffineMap.lineMap a b times[k]))
            (F.symm (AffineMap.lineMap a b times[k + 1])) t := by
  obtain ⟨F, cuts, _, _, hline⟩ :=
    exists_frozen_reference_compression valid_bothFixed (s := 1 / 2) (by constructor <;> norm_num)
  refine ⟨F, cuts, fun k hk t ht => ?_⟩
  exact segmentCuts_map_lineMap cuts Complex.reCLM.toLinearMap.toAffineMap F.symm
    hline a b hk ht

-- The inverse transports complete simple routes, with all support points and both tagged ends.
example (p : Route) (hp : p.IsSimple) :
    ∃ (F : ℂ ≃ₜ ℂ) (q : Route),
      (∀ z ∈ ((referenceDrawing bothFixed).route ⟨0, by decide⟩).support,
        F z = referencePoint bothFixed 0 + (1 / 2 : ℝ) • (z - referencePoint bothFixed 0)) ∧
      q.IsSimple ∧ q.support = F.symm '' p.support ∧
        ∀ b : Bool, q.endpoint b = F.symm (p.endpoint b) := by
  obtain ⟨F, cuts, _, hspoke, hline⟩ :=
    exists_frozen_reference_compression valid_bothFixed (s := 1 / 2) (by constructor <;> norm_num)
  let coordinate : ℂ →ᵃ[ℝ] ℝ := Complex.reCLM.toLinearMap.toAffineMap
  let q := p.mapAtCuts cuts coordinate F.symm
  let a : Dart bothFixed.graph := (⟨0, by decide⟩, false)
  have ha : a.vertex = 0 := by decide +kernel
  have hFa := hspoke a (by decide +kernel)
  rw [ha] at hFa
  refine ⟨F, q, hFa, ?_, ?_, ?_⟩
  · exact Route.IsSimple.mapAtCuts (c := coordinate) hline hp F.symm.injective
  · exact Route.support_mapAtCuts (c := coordinate) hline p
  · exact Route.endpoint_mapAtCuts (c := coordinate) hline p

-- The same inverse map transports the entire frozen reference graph, including isolated vertices.
example :
    let D := frozenReferenceDrawing bothFixed
    ∃ (F : ℂ ≃ₜ ℂ) (E : PolygonalDrawing (frozenGraph bothFixed)),
      E.IsEmbedding ∧ (∀ v, E.vertex v = F.symm (D.vertex v)) ∧
        ∀ e, (E.route e).support = F.symm '' (D.route e).support := by
  obtain ⟨F, cuts, _, _, hline⟩ :=
    exists_frozen_reference_compression valid_bothFixed (s := 1 / 2) (by constructor <;> norm_num)
  let c : ℂ →ᵃ[ℝ] ℝ := Complex.reCLM.toLinearMap.toAffineMap
  let D := frozenReferenceDrawing bothFixed
  refine ⟨F, D.mapAtCuts (c := c) hline, ?_, fun _ => rfl, ?_⟩
  · exact (frozenReferenceDrawing_isEmbedding valid_bothFixed).mapAtCuts
      (c := c) hline F.symm.injective
  · exact fun e => Route.support_mapAtCuts (c := c) hline (D.route e)

/-- Removing every edge keeps the entire frame as distinct isolated points. -/
theorem all_free_frame :
    let J : FixedRotationInput := ⟨⟨[0, 1, 2], [(0, 1)]⟩, [none, none, none]⟩
    (frozenGraph J).edges = [] ∧ (frozenGraph J).vertices.length = 5 ∧
      (frozenReferenceDrawing J).IsEmbedding := by
  dsimp only
  exact ⟨by decide +kernel, by decide +kernel,
    frozenReferenceDrawing_isEmbedding (validate_eq_true_iff _ |>.mp (by decide +kernel))⟩

-- A degree-five star has five literal retained routes and all seventeen frame vertices.
example :
    let J : FixedRotationInput :=
      ⟨⟨List.range 7, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)]⟩,
        some [0, 2, 4, 6, 8] :: List.replicate 6 none⟩
    (frozenReferenceDrawing J).IsEmbedding ∧ (frozenGraph J).edges.length = 5 ∧
      (frozenGraph J).vertices.length = 17 := by
  dsimp only
  exact ⟨frozenReferenceDrawing_isEmbedding (validate_eq_true_iff _ |>.mp (by decide +kernel)),
    by decide +kernel, by decide +kernel⟩

end Cslib.Tests.RotationFrozenReference
