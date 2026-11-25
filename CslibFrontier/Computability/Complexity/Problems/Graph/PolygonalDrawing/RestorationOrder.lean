/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationGerms
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.SplitIntervals
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntervalOrder

/-!
# Exact clockwise order after actual nonloop restoration

Retained triples preserve literal cyclic order inside either source block. The selected
connector occupies its prescribed source insertion slot, including empty-tail cases.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal RotationSystem

private theorem target_vertex_of_eq_lastEdgeDart {G : Graph} {u v : ℕ} {side : Bool}
    {x : Dart (contractLastEdgeGraph G u v)}
    (hx : (contractionLift G u v x).vertex = (lastEdgeDart G u v side).vertex) :
    x.vertex = v := by
  apply (contractionLift_vertex_eq_iff G u v x).mpr
  cases side
  · exact Or.inl (by simpa only [vertex_lastEdgeDart, Bool.false_eq_true, ↓reduceIte] using hx)
  · exact Or.inr (by simpa only [vertex_lastEdgeDart, ↓reduceIte] using hx)

private theorem restoredVertex_lastEdgeDart {G : Graph} {u v : ℕ} (huv : u ≠ v)
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (a b : ℂ) (side : Bool) :
    D.restoredVertex a b (lastEdgeDart G u v side).vertex = if side then b else a := by
  cases side <;> simp [vertex_lastEdgeDart, restoredVertex, huv.symm]

/-- Retained triples preserve the exact source clockwise order at every vertex. -/
theorem Realizes.clockwise_restoration_retained {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    {D : PolygonalDrawing (contractLastEdgeGraph G u v)} (hD : D.IsEmbedding)
    (hR : D.Realizes (r.contractLastEdge huv)) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart (contractLastEdgeGraph G u v), d.vertex = v → 3 * ρ < ‖D.germ d‖)
    {a b : ℂ} (ha : a ∈ Metric.ball (D.vertex v) ρ) (hb : b ∈ Metric.ball (D.vertex v) ρ)
    (x y z : Dart (contractLastEdgeGraph G u v))
    (hxy : (contractionLift G u v x).vertex = (contractionLift G u v y).vertex)
    (hyz : (contractionLift G u v y).vertex = (contractionLift G u v z).vertex)
    (hneXY : x ≠ y) (hneYZ : y ≠ z) (hneXZ : x ≠ z) :
    sbtw ((D.restoration huv ρ a b).direction (contractionLift G u v z))
      ((D.restoration huv ρ a b).direction (contractionLift G u v y))
      ((D.restoration huv ρ a b).direction (contractionLift G u v x)) ↔
      contractionLift G u v y ∈ r.rotationInterval (contractionLift G u v x)
        (contractionLift G u v z) := by
  have htarget (x y : Dart (contractLastEdgeGraph G u v))
      (h : (contractionLift G u v x).vertex = (contractionLift G u v y).vertex) :
      x.vertex = y.vertex :=
    (vertex_contractionLift G u v x).symm.trans
      ((congrArg (Function.update id u v) h).trans (vertex_contractionLift G u v y))
  have htxy := htarget x y hxy
  have htyz := htarget y z hyz
  have hactive (side : Bool) (hxside : (contractionLift G u v x).vertex =
      (lastEdgeDart G u v side).vertex) :
      sbtw ((D.restoration huv ρ a b).direction (contractionLift G u v z))
        ((D.restoration huv ρ a b).direction (contractionLift G u v y))
        ((D.restoration huv ρ a b).direction (contractionLift G u v x)) ↔
        contractionLift G u v y ∈ r.rotationInterval (contractionLift G u v x)
          (contractionLift G u v z) := by
    have hyside := hxy.symm.trans hxside
    have hzside := hyz.symm.trans hyside
    have hx : x.vertex = v := target_vertex_of_eq_lastEdgeDart hxside
    have hy : y.vertex = v := htxy.symm.trans hx
    have hz : z.vertex = v := htyz.symm.trans hy
    have hball : (if side then b else a) ∈ Metric.ball (D.vertex v) ρ := by
      cases side <;> [exact ha; exact hb]
    simp only [direction, D.germ_restoration_lift_active huv ρ a b x hx,
      D.germ_restoration_lift_active huv ρ a b y hy, D.germ_restoration_lift_active huv ρ a b z hz,
      hxside, hyside, hzside, restoredVertex_lastEdgeDart huv D a b side]
    exact (hR.cutPort_clockwise v hρ hball x y z hx hy hz hneXY hneYZ hneXZ).trans
      (r.mem_rotationInterval_contractionLift_active huv ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ side
        hxside hyside hzside (fun h => hneXY (congrArg Subtype.val h))
        (fun h => hneYZ (congrArg Subtype.val h)) (fun h => hneXZ (congrArg Subtype.val h)))
  by_cases hxu : (contractionLift G u v x).vertex = u
  · exact hactive false
      (by simpa only [vertex_lastEdgeDart, Bool.false_eq_true, ↓reduceIte] using hxu)
  · by_cases hxv : (contractionLift G u v x).vertex = v
    · exact hactive true (by simpa only [vertex_lastEdgeDart, ↓reduceIte] using hxv)
    · have hx : x.vertex ≠ v := fun h =>
        ((contractionLift_vertex_eq_iff G u v x).mp h).elim hxu hxv
      have hy : y.vertex ≠ v := fun h => hx (htxy.trans h)
      have hz : z.vertex ≠ v := fun h => hy (htyz.trans h)
      rw [hD.direction_restoration_lift_inactive huv hρ hlen a b x hx,
        hD.direction_restoration_lift_inactive huv hρ hlen a b y hy,
        hD.direction_restoration_lift_inactive huv hρ hlen a b z hz]
      exact (hR.clockwise x y z htxy htyz hneXY hneYZ hneXZ).trans
        (r.mem_rotationInterval_contractionLift_of_ne huv x y z (htxy.trans htyz) hx)

/-- The selected connector occupies its exact original insertion slot. The retained
pair order is the internally constructed complementary fan gap, in either orientation. -/
theorem clockwise_restoration_selected {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (ρ : ℝ) (a b : ℂ)
    (horder : ∀ (side : Bool)
      (x y : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}),
      (contractionLift G u v x.val).vertex = (lastEdgeDart G u v side).vertex →
      (contractionLift G u v y.val).vertex = (lastEdgeDart G u v side).vertex → x ≠ y →
      (sbtw ((if side then a - b else b - a).arg : Real.Angle)
        ((D.cutPort ρ x.val - (if side then b else a)).arg : Real.Angle)
        ((D.cutPort ρ y.val - (if side then b else a)).arg : Real.Angle) ↔
      r.rotationDistance (lastEdgeDart G u v side) (contractionLift G u v y.val) <
        r.rotationDistance (lastEdgeDart G u v side) (contractionLift G u v x.val)))
    (side : Bool) (y z : Dart (contractLastEdgeGraph G u v))
    (hy : (contractionLift G u v y).vertex = (lastEdgeDart G u v side).vertex)
    (hz : (contractionLift G u v z).vertex = (lastEdgeDart G u v side).vertex)
    (hyz : y ≠ z) :
    sbtw ((D.restoration huv ρ a b).direction (contractionLift G u v z))
      ((D.restoration huv ρ a b).direction (contractionLift G u v y))
      ((D.restoration huv ρ a b).direction (lastEdgeDart G u v side)) ↔
      contractionLift G u v y ∈ r.rotationInterval (lastEdgeDart G u v side)
        (contractionLift G u v z) := by
  have hy' := target_vertex_of_eq_lastEdgeDart hy
  have hz' := target_vertex_of_eq_lastEdgeDart hz
  simp only [direction, D.germ_restoration_lift_active huv ρ a b y hy',
    D.germ_restoration_lift_active huv ρ a b z hz', hy, hz,
    restoredVertex_lastEdgeDart huv D a b side, D.germ_restoration_last]
  rw [sbtw_cyclic]
  exact (horder side ⟨z, hz'⟩ ⟨y, hy'⟩ hz hy
      (fun h => hyz (congrArg Subtype.val h).symm)).trans
    (r.mem_rotationInterval_iff_lt_distance _ _ _ hy.symm hz.symm
      (contractionLift_ne_lastEdgeDart G u v y side).symm
      (fun h => hyz (contractionLift_injective G u v h))
      (contractionLift_ne_lastEdgeDart G u v z side).symm).symm

/-- The actual restored drawing realizes the exact source rotation when its internally
constructed connector has the prescribed complementary gap order. -/
theorem Realizes.restoration {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    {D : PolygonalDrawing (contractLastEdgeGraph G u v)} (hD : D.IsEmbedding)
    (hR : D.Realizes (r.contractLastEdge huv)) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart (contractLastEdgeGraph G u v), d.vertex = v → 3 * ρ < ‖D.germ d‖)
    {a b : ℂ} (ha : a ∈ Metric.ball (D.vertex v) ρ) (hb : b ∈ Metric.ball (D.vertex v) ρ)
    (hnew : (D.restoration huv ρ a b).IsEmbedding)
    (horder : ∀ (side : Bool)
      (x y : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}),
      (contractionLift G u v x.val).vertex = (lastEdgeDart G u v side).vertex →
      (contractionLift G u v y.val).vertex = (lastEdgeDart G u v side).vertex → x ≠ y →
      (sbtw ((if side then a - b else b - a).arg : Real.Angle)
        ((D.cutPort ρ x.val - (if side then b else a)).arg : Real.Angle)
        ((D.cutPort ρ y.val - (if side then b else a)).arg : Real.Angle) ↔
      r.rotationDistance (lastEdgeDart G u v side) (contractionLift G u v y.val) <
        r.rotationDistance (lastEdgeDart G u v side) (contractionLift G u v x.val))) :
    (D.restoration huv ρ a b).Realizes r := by
  have hselected (side tag : Bool)
      (h : (lastEdgeDart G u v side).vertex = (lastEdgeDart G u v tag).vertex) :
      lastEdgeDart G u v side = lastEdgeDart G u v tag := by
    cases side <;> cases tag <;> simp [vertex_lastEdgeDart, huv, huv.symm] at h ⊢
  refine ⟨hnew.germ_ne_zero, hnew.directions_injective, ?_⟩
  intro x y z hxy hyz hneXY hneYZ hneXZ
  rcases contraction_dart_cases G u v x with ⟨x, rfl⟩ | ⟨side, rfl⟩
  · rcases contraction_dart_cases G u v y with ⟨y, rfl⟩ | ⟨side, rfl⟩
    · rcases contraction_dart_cases G u v z with ⟨z, rfl⟩ | ⟨side, rfl⟩
      · exact hR.clockwise_restoration_retained r huv hD hρ hlen ha hb x y z hxy hyz
          (fun h => hneXY (congrArg (contractionLift G u v) h))
          (fun h => hneYZ (congrArg (contractionLift G u v) h))
          (fun h => hneXZ (congrArg (contractionLift G u v) h))
      · have hmain := clockwise_restoration_selected r huv D ρ a b horder side x y
          (hxy.trans hyz) hyz (fun h => hneXY (congrArg (contractionLift G u v) h))
        have hcycle := (r.mem_rotationInterval_cyclic _ _ _ hxy hyz hneXY hneYZ hneXZ).trans
          (r.mem_rotationInterval_cyclic _ _ _ hyz (hxy.trans hyz).symm
            hneYZ hneXZ.symm hneXY.symm)
        exact sbtw_cyclic.symm.trans (hmain.trans hcycle.symm)
    · rcases contraction_dart_cases G u v z with ⟨z, rfl⟩ | ⟨tag, rfl⟩
      · have hmain := clockwise_restoration_selected r huv D ρ a b horder side z x
          hyz.symm hxy (fun h => hneXZ (congrArg (contractionLift G u v) h).symm)
        exact sbtw_cyclic.trans (hmain.trans
          (r.mem_rotationInterval_cyclic _ _ _ hxy hyz hneXY hneYZ hneXZ).symm)
      · exact False.elim (hneYZ (hselected side tag hyz))
  · rcases contraction_dart_cases G u v y with ⟨y, rfl⟩ | ⟨tag, rfl⟩
    · rcases contraction_dart_cases G u v z with ⟨z, rfl⟩ | ⟨tag, rfl⟩
      · exact clockwise_restoration_selected r huv D ρ a b horder side y z
          hxy.symm (hxy.trans hyz).symm
          (fun h => hneYZ (congrArg (contractionLift G u v) h))
      · exact False.elim (hneXZ (hselected side tag (hxy.trans hyz)))
    · exact False.elim (hneXY (hselected side tag hxy))

end Cslib.Complexity.Graph.PolygonalDrawing
