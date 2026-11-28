/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Restriction
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Basic
public import CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitOrder
import CslibFrontier.Foundations.Geometry.Polygonal.CircleChord

/-!
# Clockwise order of cut ports after moving their center

An interior fan to common-radius cut ports retains the exact clockwise order of the
original drawing. Both ends of a loop and all indexed parallel occurrences remain distinct.
The center can move anywhere in the open cut ball, without a semicircle restriction on
the old ports. For two pairs of distinct ports at one vertex, their joining chords
meet in their interiors exactly when the pairs alternate in the rotation.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

/-- A new fan center strictly inside the cut circle differs from every boundary port. -/
theorem IsEmbedding.cutPort_sub_ne_zero {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    {x : ℂ} (hx : x ∈ Metric.ball (D.vertex v) ρ) (d : Dart G) (hd : d.vertex = v) :
    D.cutPort ρ d - x ≠ 0 := by
  have hp : D.cutPort ρ d ∈ Metric.sphere (D.vertex v) ρ := by
    rw [Metric.mem_sphere, ← hd]
    exact hD.dist_cutPort hρ.le d
  intro heq
  have hmem : D.cutPort ρ d ∈ Metric.ball (D.vertex v) ρ :=
    (sub_eq_zero.mp heq).symm ▸ hx
  exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hp hmem

/-- Distinct retained darts still have distinct outgoing directions at any new interior
fan center, including the two separate ends of an old loop. -/
theorem IsEmbedding.cutPort_direction_injective {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    {x : ℂ} (hx : x ∈ Metric.ball (D.vertex v) ρ) (a b : Dart G)
    (ha : a.vertex = v) (hb : b.vertex = v)
    (heq : ((D.cutPort ρ a - x).arg : Real.Angle) =
      ((D.cutPort ρ b - x).arg : Real.Angle)) : a = b := by
  have hport (d : Dart G) (hd : d.vertex = v) :
      D.cutPort ρ d ∈ Metric.sphere (D.vertex v) ρ := by
    rw [Metric.mem_sphere, ← hd]
    exact hD.dist_cutPort hρ.le d
  exact hD.cutPort_injective hρ a b (ha.trans hb.symm)
    (Polygonal.arg_sub_injective_on_sphere hx (hport a ha) (hport b hb) heq)

private theorem Realizes.cutPort_mem_sphere {G : Graph} {D : PolygonalDrawing G}
    {r : RotationSystem G} (hR : D.Realizes r) {v : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (d : Dart G) (hd : d.vertex = v) :
    D.cutPort ρ d ∈ Metric.sphere (D.vertex v) ρ := by
  rw [Metric.mem_sphere, ← hd]
  exact D.dist_cutPort hρ d (hR.nonzero d)

private theorem Realizes.cutPort_ne {G : Graph} {D : PolygonalDrawing G}
    {r : RotationSystem G} (hR : D.Realizes r) {ρ : ℝ} (hρ : 0 < ρ) (d e : Dart G)
    (hv : d.vertex = e.vertex) (hne : d ≠ e) : D.cutPort ρ d ≠ D.cutPort ρ e :=
  fun heq => hne (hR.directions_injective d e hv
    (D.direction_eq_of_cutPort_eq hρ d e (hR.nonzero d) (hR.nonzero e) hv heq))

/-- Any interior fan center sees the literal clockwise order of the retained ports.
The cyclic order uses only the nonzero distinct outgoing directions of the drawing. -/
theorem Realizes.cutPort_clockwise {G : Graph} {D : PolygonalDrawing G}
    {r : RotationSystem G} (hR : D.Realizes r)
    (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {x : ℂ} (hx : x ∈ Metric.ball (D.vertex v) ρ)
    (a b c : Dart G) (ha : a.vertex = v) (hb : b.vertex = v) (hc : c.vertex = v)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw ((D.cutPort ρ c - x).arg : Real.Angle) ((D.cutPort ρ b - x).arg : Real.Angle)
      ((D.cutPort ρ a - x).arg : Real.Angle) ↔ b ∈ r.rotationInterval a c := by
  have horder := Polygonal.sbtw_arg_sub_iff_of_mem_ball hx (Metric.mem_ball_self hρ)
    (hR.cutPort_mem_sphere hρ.le c hc) (hR.cutPort_mem_sphere hρ.le b hb)
    (hR.cutPort_mem_sphere hρ.le a ha) (hR.cutPort_ne hρ c b (hc.trans hb.symm) hbc.symm)
    (hR.cutPort_ne hρ b a (hb.trans ha.symm) hab.symm)
    (hR.cutPort_ne hρ c a (hc.trans ha.symm) hac.symm)
  have harg (d : Dart G) (hd : d.vertex = v) :
      ((D.cutPort ρ d - D.vertex v).arg : Real.Angle) = D.direction d := by
    rw [← hd, D.arg_cutPort_sub hρ d (hR.nonzero d)]
    rfl
  rw [harg c hc, harg b hb, harg a ha] at horder
  exact horder.trans (hR.clockwise a b c (ha.trans hb.symm) (hb.trans hc.symm) hab hbc hac)

/-- At a shared vertex, joining two pairs of four distinct cut ports gives an interior
intersection exactly when those dart pairs alternate in the realized rotation. -/
theorem Realizes.cutPort_chords_inter_iff_alternates {G : Graph} {D : PolygonalDrawing G}
    {r : RotationSystem G} (hR : D.Realizes r) {ρ : ℝ} (hρ : 0 < ρ)
    (a b c d : Dart G)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d)
    (hv : a.vertex = b.vertex) (hw : c.vertex = d.vertex) (hc : a.vertex = c.vertex) :
    (openSegment ℝ (D.cutPort ρ a) (D.cutPort ρ b) ∩
      openSegment ℝ (D.cutPort ρ c) (D.cutPort ρ d)).Nonempty ↔ r.Alternates a b c d := by
  let p := D.cutPort ρ
  have hb := hv.symm.trans hc
  have hcross := Polygonal.circle_chord_inter_iff_alternates
    (hR.cutPort_mem_sphere hρ.le d hw.symm) (hR.cutPort_mem_sphere hρ.le c rfl)
    (hR.cutPort_mem_sphere hρ.le a hc) (hR.cutPort_mem_sphere hρ.le b hb)
    (hR.cutPort_ne hρ d c hw.symm hcd.symm) (hR.cutPort_ne hρ a b hv hab)
    (hR.cutPort_ne hρ d a (hw.symm.trans hc.symm) had.symm) (hR.cutPort_ne hρ a c hc hac)
    (hR.cutPort_ne hρ d b (hw.symm.trans hb.symm) hbd.symm) (hR.cutPort_ne hρ b c hb hbc)
  have hcenter := Metric.mem_ball_self (x := D.vertex c.vertex) hρ
  rw [Set.inter_comm, openSegment_symm ℝ (p d) (p c),
    hR.cutPort_clockwise c.vertex hρ hcenter c a d rfl hc hw.symm hac.symm had hcd,
    hR.cutPort_clockwise c.vertex hρ hcenter c b d rfl hb hw.symm hbc.symm hbd hcd,
    xor_iff_iff_not] at hcross
  exact hcross.trans
    ⟨fun h => ⟨hab, hcd, hac, had, hbc, hbd, hv, hw, hc, h⟩,
      fun ⟨_, _, _, _, _, _, _, _, _, h⟩ => h⟩

end Cslib.Complexity.Graph.PolygonalDrawing
