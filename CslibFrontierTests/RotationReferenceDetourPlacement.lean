/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary clients of actual local detour placement)

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceDetourPlacement
import CslibFrontierTests.RotationReferenceStar
import CslibFrontier.Foundations.Geometry.Polygonal.RouteInterior
import Mathlib.Tactic.NormNum

/-!
This ordinary client reuses the public fixed-star loop/parallel/isolate fixture. Its
reversed frozen loop-end route crosses the long free middle route; a second frozen
route has a different actual crossing with that free route. Local placed routes have
an actual transverse contact outside a third original frozen support. No private
fixture, reference construction, rank-injectivity or frozen-index proof is copied.
The third excluded support is an original nonincident route, not a claim that this
particular fixture has three members incident at one crossing center.
-/

public section

namespace Cslib.Tests.RotationReferenceDetourPlacement

open Cslib.Polygonal Cslib.Complexity.Graph Cslib.Complexity.Graph.RotationRecognition

private abbrev input := RotationReferenceStar.input
private abbrev D := referenceDrawing input
private abbrev E := Fin (subdivisionGraph input).edges.length

private def edge (i : Fin 9) : E := ⟨i.val, by change i.val < 9; exact i.isLt⟩

private theorem valid_input : Valid input := validate_eq_true_iff input |>.mp (by decide +kernel)

private theorem frozen (i : Fin 9) (hi : i = 0 ∨ i = 2 ∨ i = 3) :
    ((subdivide input)[(edge i).val]'(by
      simpa only [subdivisionGraph, List.length_map] using (edge i).isLt)).frozen = true := by
  rcases hi with rfl | rfl | rfl <;> decide +kernel

private theorem interior_of_open (e : E) {z : ℂ}
    (hz : z ∈ openSegment ℝ (D.route e).start (D.route e).finish) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, (D.route e).eval 0 t = z := by
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨t, ht, heq⟩ := hz
  exact ⟨t, ht, (Route.eval_line _ _ 0 t).trans heq⟩

private theorem frozen_open_disjoint (e f : E) (hef : e ≠ f)
    (he : ((subdivide input)[e.val]'(by simpa only [subdivisionGraph, List.length_map]
      using e.isLt)).frozen = true)
    (hf : ((subdivide input)[f.val]'(by simpa only [subdivisionGraph, List.length_map]
      using f.isLt)).frozen = true) {z : ℂ}
    (hz : z ∈ openSegment ℝ (D.route e).start (D.route e).finish) :
    z ∉ (D.route f).support := by
  intro hzf
  obtain ⟨t, ht, hez⟩ := interior_of_open e hz
  obtain ⟨i, u, hu, hfu⟩ := ((D.route f).mem_support_iff z).mp hzf
  obtain ⟨b, _, hb, _, _⟩ := referenceDrawing_frozen_edge_contacts valid_input e f hef he hf
    0 i ⟨ht.1.le, ht.2.le⟩ hu (hez.trans hfu.symm)
  exact (Route.not_atEnd_of_mem_Ioo _ 0 ht b) hb

/-- An actual decreasing-source frozen member has a literal cut line and a transverse
local pair contact outside a third original support, in a genuine multi-crossing fixture. -/
theorem frozen_reversed_local_cut : ∃ I : FixedRotationInput, Valid I ∧
    ∃ e f g h : Fin (subdivisionGraph I).edges.length,
      ((subdivide I)[e.val]'(by simpa only [subdivisionGraph, List.length_map]
        using e.isLt)).frozen = true ∧
      ((referenceDrawing I).route e).finish.re < ((referenceDrawing I).route e).start.re ∧
      ∃ z z' : ℂ, z ≠ z' ∧
        z ∈ openSegment ℝ ((referenceDrawing I).route e).start
          ((referenceDrawing I).route e).finish ∧
        z ∈ openSegment ℝ ((referenceDrawing I).route f).start
          ((referenceDrawing I).route f).finish ∧
        z' ∈ openSegment ℝ ((referenceDrawing I).route h).start
          ((referenceDrawing I).route h).finish ∧
        z' ∈ openSegment ℝ ((referenceDrawing I).route f).start
          ((referenceDrawing I).route f).finish ∧
        ∃ (ρ α β : ℝ) (p q : Route), 0 < ρ ∧ 0 < α ∧ α < β ∧ β < 1 ∧
          p = Route.line (AffineMap.lineMap ((referenceDrawing I).route e).start
              ((referenceDrawing I).route e).finish α)
            (AffineMap.lineMap ((referenceDrawing I).route e).start
              ((referenceDrawing I).route e).finish β) ∧
          p.IsSimple ∧ q.IsSimple ∧ p.support ⊆ Metric.ball z ρ ∧
          q.support ⊆ Metric.ball z ρ ∧
          ∃ w : ℂ, w ∈ p.support ∧ w ∈ q.support ∧
            w ∉ ((referenceDrawing I).route g).support ∧
            ∃ (i : Fin p.segments) (j : Fin q.segments) (u v : ℝ),
              u ∈ Set.Ioo 0 1 ∧ v ∈ Set.Ioo 0 1 ∧ p.eval i u = w ∧ q.eval j v = w ∧
              let a := p.point i.succ - p.point i.castSucc
              let b := q.point j.succ - q.point j.castSucc
              a.re * b.im - a.im * b.re ≠ 0 := by
  classical
  obtain ⟨z, hz, _⟩ := (referenceDrawing_crossing_iff valid_input (edge 2) (edge 7)
    (by decide +kernel)).mp (by decide +kernel)
  obtain ⟨z', hz', _⟩ := (referenceDrawing_crossing_iff valid_input (edge 3) (edge 7)
    (by decide +kernel)).mp (by decide +kernel)
  have he2 := frozen 2 (Or.inr (Or.inl rfl))
  have he3 := frozen 3 (Or.inr (Or.inr rfl))
  have he0 := frozen 0 (Or.inl rfl)
  have hzz : z ≠ z' := by
    intro heq
    have hnot := frozen_open_disjoint (edge 2) (edge 3) (by decide +kernel) he2 he3 hz.1
    apply hnot
    rw [heq]
    exact (Route.support_line (D.route (edge 3)).start (D.route (edge 3)).finish).symm ▸
      openSegment_subset_segment ℝ _ _ hz'.1
  have hdec : (D.route (edge 2)).finish.re < (D.route (edge 2)).start.re := by
    change ((referenceOrder input).idxOf 0 : ℝ) < ((referenceOrder input).idxOf 4 : ℝ)
    exact_mod_cast (show (referenceOrder input).idxOf 0 < (referenceOrder input).idxOf 4
      from by decide +kernel)
  have hzc : ∃ e f : E, e ≠ f ∧
      z ∈ openSegment ℝ (D.route e).start (D.route e).finish ∧
      z ∈ openSegment ℝ (D.route f).start (D.route f).finish :=
    ⟨edge 2, edge 7, by decide +kernel, hz.1, hz.2⟩
  obtain ⟨_, radius, hrad, _, hav⟩ := exists_reference_crossing_neighborhoods valid_input
  have hnot0 := frozen_open_disjoint (edge 2) (edge 0) (by decide +kernel) he2 he0 hz.1
  let ρ := radius z
  obtain ⟨r, hr, d, α, β, hcuts, hkeep, hpair, hcontact, _⟩ :=
    exists_reference_detour_placement valid_input hzc (hrad z hzc)
  let X := {e : E // z ∈ (D.route e).support}
  let ef : X := ⟨edge 2,
    (Route.support_line (D.route (edge 2)).start (D.route (edge 2)).finish).symm ▸
      openSegment_subset_segment ℝ _ _ hz.1⟩
  let ff : X := ⟨edge 7,
    (Route.support_line (D.route (edge 7)).start (D.route (edge 7)).finish).symm ▸
      openSegment_subset_segment ℝ _ _ hz.2⟩
  have hef : ef ≠ ff := by
    intro h
    have hval : edge 2 = edge 7 := congrArg Subtype.val h
    exact (by decide +kernel : edge 2 ≠ edge 7) hval
  obtain ⟨hαe, hαβe, hβe, _, _, hse, hbe⟩ := hcuts ef
  obtain ⟨_, _, _, _, _, hsf, hbf⟩ := hcuts ff
  obtain ⟨_, hline⟩ := hkeep ef he2
  obtain ⟨w, hw, _⟩ := hpair ef ff hef
  have hw0 : w ∉ (D.route (edge 0)).support := by
    intro h
    have hball := hbe hw.1
    have hclosed : w ∈ Metric.closedBall z (radius z) := Metric.ball_subset_closedBall hball
    exact Set.disjoint_left.mp ((hav z hzc).2 (edge 0) hnot0) hclosed h
  refine ⟨input, valid_input, edge 2, edge 7, edge 0, edge 3, he2, hdec,
    z, z', hzz, hz.1, hz.2, hz'.1, hz'.2, ρ, α ef, β ef, _, _,
    hrad z hzc, hαe, hαβe, hβe, hline, hse, hsf, hbe, hbf,
    w, hw.1, hw.2, hw0, ?_⟩
  exact hcontact ef ff hef w hw.1 hw.2

end Cslib.Tests.RotationReferenceDetourPlacement
