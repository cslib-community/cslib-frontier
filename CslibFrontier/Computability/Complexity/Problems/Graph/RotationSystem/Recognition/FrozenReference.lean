/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceStar
public import Mathlib.Topology.Homeomorph.Defs
import CslibFrontier.Foundations.Geometry.Polygonal.Germs
import CslibFrontier.Foundations.Geometry.Polygonal.LineEnds
import CslibFrontier.Foundations.Geometry.Polygonal.RouteInterior
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.GetD
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The actual frozen part of the reference drawing

Only stored frozen segments are retained, in their existing occurrence order. All subdivision
vertices remain declared, including unused leaves and isolated original centers. The retained
routes are literal routes of the reference drawing, with the same endpoint tags and germs.

Different center blocks have disjoint real-coordinate intervals. At one center, a contact
away from the center would identify two positive outgoing rays, contradicting the internally
proved fixed-word direction injectivity. Thus the frozen part is a genuine embedding although
the full reference drawing intentionally has crossings.

This concrete embedding supplies no ambient placement or isotopy, generic-position
regularization, move parity, Hanani–Tutte or query-completeness theorem; the unfinished
recognition and source-model objective is tracked in
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Main definitions

* `Cslib.Complexity.Graph.RotationRecognition.frozenReferenceDrawing`: literal retained routes
  on the existing spanning frozen graph. `frozenReferenceDrawing_vertex` gives its coordinates.
* `Cslib.Complexity.Graph.RotationRecognition.frozenReferenceDart`: the retained indexed end
  selected by a literal stored word. `frozenReferenceDart_endpoints` specifies its tag
  and neighbors.

## Main results

* `Cslib.Complexity.Graph.RotationRecognition.referenceDrawing_frozen_edge_contacts`: actual
  flagged indexed routes meet only at common original endpoints.
* `Cslib.Complexity.Graph.RotationRecognition.frozenReferenceDrawing_isEmbedding`: the
  actual frozen restriction is a genuine embedding with all frame vertices retained.

## Retained-end interface

* `Cslib.Complexity.Graph.RotationRecognition.frozenReferenceDrawing_germ_frozenReferenceDart`:
  retaining an original fixed end preserves its actual outgoing germ.
* `Cslib.Complexity.Graph.RotationRecognition.frozenReferenceDrawing_fixedWord_clockwise_iff`:
  the retained fixed ends have their literal prescribed clockwise order.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Polygonal
open scoped BigOperators

private abbrev centerBlock (I : FixedRotationInput) (v : ℕ) : List ℕ :=
  v :: ((fixedWord I v).reverse.map fun d => I.graph.vertices.length + d)

private theorem centerBlocks_pairwise {I : FixedRotationInput} (hI : Valid I) :
    (centerBlocks I).Pairwise
      (fun x y => (referenceOrder I).idxOf x < (referenceOrder I).idxOf y) := by
  have hn := (referenceOrder_enumerates hI).1
  have ho : (referenceOrder I).Pairwise
      (fun x y => (referenceOrder I).idxOf x < (referenceOrder I).idxOf y) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa only [hn.idxOf_getElem i hi, hn.idxOf_getElem j hj] using hij
  exact (List.pairwise_append.mp ho).1

private theorem centerBlock_mem_reference {I : FixedRotationInput} {v x : ℕ}
    (hv : v < I.graph.vertices.length) (hx : x ∈ centerBlock I v) :
    x ∈ referenceOrder I :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hv, hx⟩)

private theorem centerBlock_pairwise {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    (hv : v < I.graph.vertices.length) : (centerBlock I v).Pairwise
      (fun x y => (referenceOrder I).idxOf x < (referenceOrder I).idxOf y) := by
  exact (List.pairwise_flatMap.mp (centerBlocks_pairwise hI)).1 v (List.mem_range.mpr hv)

private theorem centerBlocks_separated {I : FixedRotationInput} (hI : Valid I) {u v x y : ℕ}
    (hu : u < I.graph.vertices.length) (hv : v < I.graph.vertices.length) (huv : u < v)
    (hx : x ∈ centerBlock I u) (hy : y ∈ centerBlock I v) :
    (referenceOrder I).idxOf x < (referenceOrder I).idxOf y := by
  have hp := (List.pairwise_flatMap.mp (centerBlocks_pairwise hI)).2
  have h := List.pairwise_iff_getElem.mp hp u v (by simpa using hu)
    (by simpa using hv) huv
  simp only [List.getElem_range] at h
  exact h x hx y hy

private theorem fixed_end_word {I : FixedRotationInput} (hI : Valid I) (d : Dart I.graph)
    (hd : (I.orders.getD d.vertex none).isSome = true) :
    ∃ word, I.orders.getD d.vertex none = some word ∧ d.index ∈ word := by
  cases hw : I.orders.getD d.vertex none with
  | none => simp only [hw, Option.isSome_none, Bool.false_eq_true] at hd
  | some word =>
    exact ⟨word, rfl, ((hI.2.2.2 d.vertex word hw).2 d.index).mpr (index_mem_fiber d)⟩

private theorem fixed_end_reference_spec {I : FixedRotationInput} (hI : Valid I)
    (d : Dart I.graph) (hd : (I.orders.getD d.vertex none).isSome = true) :
    d.vertex < I.graph.vertices.length ∧ d.vertex ∈ referenceOrder I ∧
      I.graph.vertices.length + d.index ∈ referenceOrder I ∧
      I.graph.vertices.length + d.index ∈ centerBlock I d.vertex ∧
      (referenceOrder I).idxOf d.vertex <
        (referenceOrder I).idxOf (I.graph.vertices.length + d.index) := by
  obtain ⟨word, hw, hm⟩ := fixed_end_word hI d hd
  have hv : d.vertex < I.graph.vertices.length := by
    by_contra hn
    have ho : I.orders.length ≤ d.vertex := by rw [hI.2.2.1]; omega
    rw [List.getD_eq_default _ _ ho] at hw
    contradiction
  have hleaf : I.graph.vertices.length + d.index ∈
      (fixedWord I d.vertex).reverse.map (fun k => I.graph.vertices.length + k) := by
    apply List.mem_map.mpr
    exact ⟨d.index, List.mem_reverse.mpr (by simpa only [fixedWord, hw, Option.getD_some] using hm),
      rfl⟩
  have hblock : I.graph.vertices.length + d.index ∈ centerBlock I d.vertex :=
    List.mem_cons_of_mem _ hleaf
  exact ⟨hv, centerBlock_mem_reference hv List.mem_cons_self,
    centerBlock_mem_reference hv hblock, hblock,
    (List.pairwise_cons.mp (centerBlock_pairwise hI hv)).1 _ hleaf⟩

private theorem eval_from_original_end (I : FixedRotationInput) (d : Dart I.graph)
    (i : Fin ((referenceDrawing I).route (subdivisionDart I d).1).segments) (t : ℝ) :
    ((referenceDrawing I).route (subdivisionDart I d).1).eval i t =
      (referenceDrawing I).vertex d.vertex + Route.endTime d.2 t •
        (referenceDrawing I).germ (subdivisionDart I d) := by
  let p := (referenceDrawing I).route (subdivisionDart I d).1
  have hi : i = p.endSegment d.2 := Subsingleton.elim (α := Fin 1) _ _
  have htt : Route.endTime d.2 (Route.endTime d.2 t) = t := by
    cases d.2 <;> simp only [Route.endTime, Bool.false_eq_true, ↓reduceIte]; ring
  rw [hi]
  calc
    _ = p.endpoint d.2 + Route.endTime d.2 t • p.germ d.2 := by
      simpa only [htt] using p.eval_near_end d.2 (Route.endTime d.2 t)
    _ = _ := by
      rw [(referenceDrawing I).endpoint_eq]
      change (referenceDrawing I).vertex (subdivisionDart I d).vertex +
        Route.endTime d.2 t • p.germ d.2 = _
      rw [(subdivisionDart_endpoints I d).1]
      rfl

private theorem at_original_end_of_outgoing_zero (I : FixedRotationInput) (d : Dart I.graph)
    (i : Fin ((referenceDrawing I).route (subdivisionDart I d).1).segments) {t : ℝ}
    (ht : Route.endTime d.2 t = 0) :
    ((referenceDrawing I).route (subdivisionDart I d).1).AtEnd i t d.2 := by
  apply (Route.atEnd_line_iff _ _ i t d.2).mpr
  cases hb : d.2 <;> simp only [Route.endTime, hb, Bool.false_eq_true, ↓reduceIte] at ht ⊢
  · exact ht
  · linarith only [ht]

private theorem eval_re_mem_original_interval {I : FixedRotationInput} (hI : Valid I)
    (d : Dart I.graph) (hd : (I.orders.getD d.vertex none).isSome = true)
    (i : Fin ((referenceDrawing I).route (subdivisionDart I d).1).segments)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (((referenceDrawing I).route (subdivisionDart I d).1).eval i t).re ∈
      Set.Icc ((referenceOrder I).idxOf d.vertex : ℝ)
        ((referenceOrder I).idxOf (I.graph.vertices.length + d.index) : ℝ) := by
  obtain ⟨_, _, _, _, hr⟩ := fixed_end_reference_spec hI d hd
  have hle : ((referenceOrder I).idxOf d.vertex : ℝ) ≤
      ((referenceOrder I).idxOf (I.graph.vertices.length + d.index) : ℝ) :=
    (Nat.cast_lt.mpr hr).le
  let σ := Route.endTime d.2 t
  let a := referencePoint I d.vertex
  let b := referencePoint I (I.graph.vertices.length + d.index)
  have heval : ((referenceDrawing I).route (subdivisionDart I d).1).eval i t =
      AffineMap.lineMap a b σ := by
    rw [eval_from_original_end, referenceDrawing_subdivisionDart_germ,
      AffineMap.lineMap_apply_module']
    exact add_comm _ _
  have hpoint := lineMap_mem_segment ℝ a b (Route.endTime_mem d.2 ht)
  let reMap : ℂ →ᵃ[ℝ] ℝ := Complex.reCLM.toLinearMap.toAffineMap
  have himage := image_segment ℝ reMap a b
  have hre : (AffineMap.lineMap a b σ).re ∈ segment ℝ a.re b.re :=
    himage ▸ Set.mem_image_of_mem reMap hpoint
  rw [heval]
  simpa only [a, b, referencePoint, parabolaPoint, segment_eq_Icc hle] using hre

/-- Every original center has a right bound strictly beyond its whole frozen star.
The bounds leave a positive gap before the next center, even when either center is
isolated. The support condition includes both orientations and all segment parameters. -/
theorem exists_frozen_reference_strips {I : FixedRotationInput} (hI : Valid I) :
    ∃ right : ℕ → ℝ,
      (∀ v ∈ I.graph.vertices, (referencePoint I v).re < right v) ∧
      (∀ u ∈ I.graph.vertices, ∀ v ∈ I.graph.vertices, u < v →
        right u + 1 / 4 < (referencePoint I v).re) ∧
      ∀ d : Dart I.graph, (I.orders.getD d.vertex none).isSome →
        ∀ z ∈ ((referenceDrawing I).route (subdivisionDart I d).1).support,
          z.re ∈ Set.Ico (referencePoint I d.vertex).re (right d.vertex) := by
  let right (v : ℕ) : ℝ := if v + 1 < I.graph.vertices.length then
    (referencePoint I (v + 1)).re - 1 / 2
    else (referenceOrder I).length
  have hname (v : ℕ) (hv : v ∈ I.graph.vertices) : v < I.graph.vertices.length := by
    rw [hI.1] at hv
    exact List.mem_range.mp hv
  have hbound (v x : ℕ) (hv : v < I.graph.vertices.length) (hx : x ∈ centerBlock I v) :
      (referencePoint I x).re < right v := by
    by_cases hn : v + 1 < I.graph.vertices.length
    · have hr := centerBlocks_separated hI hv hn (Nat.lt_succ_self v) hx List.mem_cons_self
      have hg : ((referenceOrder I).idxOf x : ℝ) + 1 ≤ (referenceOrder I).idxOf (v + 1) := by
        exact_mod_cast hr
      simp only [right, ite_eq_left hn, referencePoint, parabolaPoint]
      linarith only [hg]
    · simp only [right, ite_eq_right hn, referencePoint, parabolaPoint]
      exact Nat.cast_lt.mpr (List.idxOf_lt_length_of_mem (centerBlock_mem_reference hv hx))
  refine ⟨right, fun v hv => hbound v v (hname v hv) List.mem_cons_self, ?_, ?_⟩
  · intro u hu v hv huv
    have hn := (Nat.succ_le_of_lt huv).trans_lt (hname v hv)
    have hr : (referenceOrder I).idxOf (u + 1) ≤ (referenceOrder I).idxOf v := by
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt huv) with he | he
      · rw [show u + 1 = v from he]
      · exact (centerBlocks_separated hI hn (hname v hv) he
          List.mem_cons_self List.mem_cons_self).le
    simp only [right, ite_eq_left hn, referencePoint, parabolaPoint]
    have hr' := Nat.cast_le (α := ℝ) |>.mpr hr
    linarith only [hr']
  · intro d hd z hz
    obtain ⟨i, t, ht, rfl⟩ := (Route.mem_support_iff _ _).mp hz
    have h := eval_re_mem_original_interval hI d hd i ht
    obtain ⟨hv, _, _, hmem, _⟩ := fixed_end_reference_spec hI d hd
    exact ⟨h.1, h.2.trans_lt (hbound _ _ hv hmem)⟩

private noncomputable def stripRamp (a b c x : ℝ) : ℝ :=
  min (max 0 (x - a)) (max 0 (((b - a) / (c - b)) * (c - x)))

private theorem stripRamp_nonneg (a b c x : ℝ) : 0 ≤ stripRamp a b c x :=
  le_min (le_max_left _ _) (le_max_left _ _)

private theorem stripRamp_eq_zero {a b c x : ℝ} (hab : a < b) (hbc : b < c)
    (hx : x ∉ Set.Ioo a c) : stripRamp a b c x = 0 := by
  by_cases hax : a < x
  · have hcx : c ≤ x := le_of_not_gt fun h => hx ⟨hax, h⟩
    have hk := div_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr hbc.le)
    rw [stripRamp, max_eq_left (mul_nonpos_of_nonneg_of_nonpos hk (sub_nonpos.mpr hcx)),
      min_eq_right (le_max_left _ _)]
  · rw [stripRamp, max_eq_left (sub_nonpos.mpr (le_of_not_gt hax)),
      min_eq_left (le_max_left _ _)]

private theorem stripRamp_eq_sub {a b c x : ℝ} (hab : a < b) (hbc : b < c)
    (hx : x ∈ Set.Icc a b) : stripRamp a b c x = x - a := by
  have hk := div_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr hbc.le)
  have hb : ((b - a) / (c - b)) * (c - b) = b - a :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hbc.ne')
  have hle := mul_le_mul_of_nonneg_left (sub_le_sub_left hx.2 c) hk
  rw [stripRamp, max_eq_right (sub_nonneg.mpr hx.1)]
  apply min_eq_left
  exact (show x - a ≤ ((b - a) / (c - b)) * (c - x) by linarith only [hx.2, hb, hle]).trans
    (le_max_right _ _)

private theorem stripRamp_increment {a b c x y : ℝ} (hab : a < b) (hbc : b < c)
    (hxy : x ≤ y) : stripRamp a b c y ≤ stripRamp a b c x + (y - x) := by
  let k := (b - a) / (c - b)
  have hk : 0 ≤ k := div_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr hbc.le)
  have hdiff := sub_nonneg.mpr hxy
  have hRise : max 0 (y - a) ≤ max 0 (x - a) + (y - x) := by
    apply max_le
    · exact add_nonneg (le_max_left _ _) hdiff
    · have h := le_max_right (0 : ℝ) (x - a)
      linarith only [h]
  have hFall : max 0 (k * (c - y)) ≤ max 0 (k * (c - x)) :=
    max_le_max le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_left hxy c) hk)
  change min (max 0 (y - a)) (max 0 (k * (c - y))) ≤
    min (max 0 (x - a)) (max 0 (k * (c - x))) + (y - x)
  rcases le_total (max 0 (x - a)) (max 0 (k * (c - x))) with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans hRise
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (hFall.trans (le_add_of_nonneg_right hdiff))

private noncomputable def stripPlateau (a b x : ℝ) : ℝ :=
  min (max 0 (min 1 (8 * (x - a) + 1))) (max 0 (min 1 (8 * (b - x) + 1)))

private theorem stripPlateau_eq_zero {a b x : ℝ}
    (hx : x ∉ Set.Ioo (a - 1 / 8) (b + 1 / 8)) : stripPlateau a b x = 0 := by
  by_cases hax : a - 1 / 8 < x
  · have hbx : b + 1 / 8 ≤ x := le_of_not_gt fun h => hx ⟨hax, h⟩
    have h : 8 * (b - x) + 1 ≤ 0 := by linarith only [hbx]
    rw [stripPlateau, max_eq_left ((min_le_right _ _).trans h), min_eq_right (le_max_left _ _)]
  · have hax' := le_of_not_gt hax
    have h : 8 * (x - a) + 1 ≤ 0 := by linarith only [hax']
    rw [stripPlateau, max_eq_left ((min_le_right _ _).trans h), min_eq_left (le_max_left _ _)]

private theorem stripPlateau_eq_one {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    stripPlateau a b x = 1 := by
  have ha : 1 ≤ 8 * (x - a) + 1 := by linarith only [hx.1]
  have hb : 1 ≤ 8 * (b - x) + 1 := by linarith only [hx.2]
  rw [stripPlateau, min_eq_left ha, min_eq_left hb, max_eq_right zero_le_one, min_self]

private theorem interval_on_one_side {x y k : ℝ}
    (hk : k ∉ Set.Ioo (min x y) (max x y)) : max x y ≤ k ∨ k ≤ min x y := by
  by_cases h : max x y ≤ k
  · exact Or.inl h
  · exact Or.inr (le_of_not_gt fun h' => hk ⟨h', lt_of_not_ge h⟩)

private theorem stripRamp_eq_fall {a b c x : ℝ} (hab : a < b) (hbc : b < c)
    (hx : x ∈ Set.Icc b c) : stripRamp a b c x = ((b - a) / (c - b)) * (c - x) := by
  have hk := div_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr hbc.le)
  have hb : ((b - a) / (c - b)) * (c - b) = b - a :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hbc.ne')
  have hle := mul_le_mul_of_nonneg_left (sub_le_sub_left hx.1 c) hk
  rw [stripRamp, max_eq_right (mul_nonneg hk (sub_nonneg.mpr hx.2))]
  exact min_eq_right ((show ((b - a) / (c - b)) * (c - x) ≤ x - a by
    linarith only [hx.1, hb, hle]).trans (le_max_right _ _))

private theorem stripRamp_affine_on {a b c x y : ℝ} (hab : a < b) (hbc : b < c)
    (ha : a ∉ Set.Ioo (min x y) (max x y)) (hb : b ∉ Set.Ioo (min x y) (max x y))
    (hc : c ∉ Set.Ioo (min x y) (max x y)) :
    ∃ m d : ℝ, ∀ z ∈ Set.uIcc x y, stripRamp a b c z = m * z + d := by
  rcases interval_on_one_side ha with h | h
  · refine ⟨0, 0, fun z hz => ?_⟩
    simpa only [zero_mul, zero_add] using
      stripRamp_eq_zero hab hbc (Set.notMem_Ioo_of_le (hz.2.trans h))
  rcases interval_on_one_side hb with h' | h'
  · refine ⟨1, -a, fun z hz => ?_⟩
    simpa only [one_mul, sub_eq_add_neg] using
      stripRamp_eq_sub hab hbc ⟨h.trans hz.1, hz.2.trans h'⟩
  rcases interval_on_one_side hc with h'' | h''
  · refine ⟨-((b - a) / (c - b)), ((b - a) / (c - b)) * c, fun z hz => ?_⟩
    rw [stripRamp_eq_fall hab hbc ⟨h'.trans hz.1, hz.2.trans h''⟩]
    ring
  · refine ⟨0, 0, fun z hz => ?_⟩
    simpa only [zero_mul, zero_add] using
      stripRamp_eq_zero hab hbc (Set.notMem_Ioo_of_ge (h''.trans hz.1))

private theorem stripPlateau_affine_on {a b x y : ℝ} (hab : a ≤ b)
    (h₁ : a - 1 / 8 ∉ Set.Ioo (min x y) (max x y))
    (h₂ : a ∉ Set.Ioo (min x y) (max x y)) (h₃ : b ∉ Set.Ioo (min x y) (max x y))
    (h₄ : b + 1 / 8 ∉ Set.Ioo (min x y) (max x y)) :
    ∃ m d : ℝ, ∀ z ∈ Set.uIcc x y, stripPlateau a b z = m * z + d := by
  rcases interval_on_one_side h₁ with h | h
  · refine ⟨0, 0, fun z hz => ?_⟩
    simpa only [zero_mul, zero_add] using stripPlateau_eq_zero
      (a := a) (b := b) (Set.notMem_Ioo_of_le (hz.2.trans h))
  rcases interval_on_one_side h₂ with h' | h'
  · refine ⟨8, 1 - 8 * a, fun z hz => ?_⟩
    have hl : 0 ≤ 8 * (z - a) + 1 := by linarith only [h.trans hz.1]
    have hu : 8 * (z - a) + 1 ≤ 1 := by linarith only [hz.2.trans h']
    have hr : 1 ≤ 8 * (b - z) + 1 := by linarith only [(hz.2.trans h').trans hab]
    simp only [stripPlateau, min_eq_right hu, max_eq_right hl, min_eq_left hr,
      max_eq_right zero_le_one, min_eq_left hu]
    ring
  rcases interval_on_one_side h₃ with h'' | h''
  · refine ⟨0, 1, fun z hz => ?_⟩
    simpa only [zero_mul, zero_add] using stripPlateau_eq_one ⟨h'.trans hz.1, hz.2.trans h''⟩
  rcases interval_on_one_side h₄ with h''' | h'''
  · refine ⟨-8, 8 * b + 1, fun z hz => ?_⟩
    have hl : 0 ≤ 8 * (b - z) + 1 := by linarith only [hz.2.trans h''']
    have hu : 8 * (b - z) + 1 ≤ 1 := by linarith only [h''.trans hz.1]
    have hr : 1 ≤ 8 * (z - a) + 1 := by linarith only [hab.trans (h''.trans hz.1)]
    simp only [stripPlateau, max_eq_right hl, min_eq_left hr,
      max_eq_right zero_le_one, min_eq_right hu]
    ring
  · refine ⟨0, 0, fun z hz => ?_⟩
    simpa only [zero_mul, zero_add] using stripPlateau_eq_zero
      (a := a) (b := b) (Set.notMem_Ioo_of_ge (h'''.trans hz.1))

private theorem map_lineMap_of_affine_on {φ : ℝ → ℝ} {x y t : ℝ}
    (hφ : ∃ m d : ℝ, ∀ z ∈ Set.uIcc x y, φ z = m * z + d) (ht : t ∈ Set.Icc 0 1) :
    φ (AffineMap.lineMap x y t) = AffineMap.lineMap (φ x) (φ y) t := by
  obtain ⟨m, d, h⟩ := hφ
  have hp : AffineMap.lineMap x y t ∈ Set.uIcc x y := by
    rw [← segment_eq_uIcc]
    exact lineMap_mem_segment ℝ x y ht
  rw [h _ hp, h _ Set.left_mem_uIcc, h _ Set.right_mem_uIcc]
  simp only [AffineMap.lineMap_apply_ring]
  ring

private theorem sum_map_lineMap (V : Finset ℕ) (k : ℕ → ℝ → ℝ) (x y t : ℝ)
    (hk : ∀ v ∈ V, k v (AffineMap.lineMap x y t) = AffineMap.lineMap (k v x) (k v y) t) :
    (∑ v ∈ V, k v (AffineMap.lineMap x y t)) =
      AffineMap.lineMap (∑ v ∈ V, k v x) (∑ v ∈ V, k v y) t := by
  simp only [AffineMap.lineMap_apply_ring, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v hv => by
    simpa only [AffineMap.lineMap_apply_ring] using hk v hv

/-- A plane homeomorphism fixes all original reference centers and shrinks each full
frozen spoke about its center by the same positive factor. The supplied real coordinates
are the cut lines in the compressed plane. The inverse sends segments to straight segments
with the same parameter whenever no cut line lies strictly between the endpoint real
coordinates. Segments on a cut line and endpoints on a cut line are allowed. -/
theorem exists_frozen_reference_compression {I : FixedRotationInput} (hI : Valid I)
    {s : ℝ} (hs : s ∈ Set.Ioc 0 1) :
    ∃ (F : ℂ ≃ₜ ℂ) (cuts : Finset ℝ),
      (∀ v ∈ I.graph.vertices, F (referencePoint I v) = referencePoint I v) ∧
      (∀ d : Dart I.graph, (I.orders.getD d.vertex none).isSome →
        ∀ z ∈ ((referenceDrawing I).route (subdivisionDart I d).1).support,
          F z = referencePoint I d.vertex + s • (z - referencePoint I d.vertex)) ∧
      ∀ z w : ℂ, (∀ x ∈ cuts, x ∉ Set.Ioo (min z.re w.re) (max z.re w.re)) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          F.symm (AffineMap.lineMap z w t) = AffineMap.lineMap (F.symm z) (F.symm w) t := by
  classical
  obtain ⟨right, hright, hsep, hstrip⟩ := exists_frozen_reference_strips hI
  let V := I.graph.vertices.toFinset
  let a (v : ℕ) := (referencePoint I v).re
  let band (v : ℕ) := Set.Ioo (a v - 1 / 8) (right v + 1 / 8)
  let ramp (v : ℕ) := stripRamp (a v) (right v) (right v + 1 / 8)
  let offset (v : ℕ) (x : ℝ) := ((1 - s) * (referencePoint I v).im) *
    stripPlateau (a v) (right v) x
  have hmem {v : ℕ} : v ∈ V ↔ v ∈ I.graph.vertices := List.mem_toFinset
  have hgap (v : ℕ) : right v < right v + 1 / 8 := by linarith
  have hband {u v : ℕ} {x : ℝ} (hu : u ∈ V) (hv : v ∈ V) (hne : u ≠ v)
      (hxu : x ∈ band u) (hxv : x ∈ band v) : False := by
    rcases lt_or_gt_of_ne hne with h | h
    · linarith only [hsep u (hmem.mp hu) v (hmem.mp hv) h, hxu.2, hxv.1]
    · linarith only [hsep v (hmem.mp hv) u (hmem.mp hu) h, hxv.2, hxu.1]
  have hramp {v : ℕ} (hv : v ∈ V) {x : ℝ} (hx : x ∉ band v) : ramp v x = 0 :=
    stripRamp_eq_zero (hright v (hmem.mp hv)) (hgap v)
      (fun h => hx ⟨by linarith only [h.1], h.2⟩)
  have hoffset {v : ℕ} {x : ℝ} (hx : x ∉ band v) : offset v x = 0 := by
    simp only [offset, stripPlateau_eq_zero hx, mul_zero]
  have hsum (k : ℕ → ℝ → ℝ) (hzero : ∀ v ∈ V, ∀ x ∉ band v, k v x = 0)
      {v : ℕ} (hv : v ∈ V) {x : ℝ} (hx : x ∈ band v) :
      (∑ w ∈ V, k w x) = k v x := by
    apply Finset.sum_eq_single v
    · exact fun w hw hne => hzero w hw x (fun hxw => hband hw hv hne hxw hx)
    · exact fun h => (h hv).elim
  let f (x : ℝ) := x - (1 - s) * (∑ v ∈ V, ramp v x)
  let g (x : ℝ) := ∑ v ∈ V, offset v x
  have hfix (x : ℝ) (hx : ∀ v ∈ V, x ∉ band v) : f x = x := by
    have hz : (∑ v ∈ V, ramp v x) = 0 := Finset.sum_eq_zero fun v hv => hramp hv (hx v hv)
    simp only [f, hz, mul_zero, sub_zero]
  have hmono : StrictMono f := by
    intro x y hxy
    have hfx : f x ≤ x := sub_le_self _ (mul_nonneg (sub_nonneg.mpr hs.2)
      (Finset.sum_nonneg fun v _ => stripRamp_nonneg (a v) (right v) (right v + 1 / 8) x))
    by_cases hy : ∃ v ∈ V, y ∈ band v
    · obtain ⟨v, hv, hyv⟩ := hy
      have hy' : f y = y - (1 - s) * ramp v y := by
        simp only [f, hsum ramp (fun w hw _ hxw => hramp hw hxw) hv hyv]
      have hx' : f x ≤ x - (1 - s) * ramp v x := by
        by_cases hx : x ∈ band v
        · simp only [f, hsum ramp (fun w hw _ hxw => hramp hw hxw) hv hx]
          exact le_rfl
        · rwa [hramp hv hx, mul_zero, sub_zero]
      have hstep : ramp v y ≤ ramp v x + (y - x) :=
        stripRamp_increment (hright v (hmem.mp hv)) (hgap v) hxy.le
      have hmul := mul_le_mul_of_nonneg_left hstep (sub_nonneg.mpr hs.2)
      rw [hy']
      nlinarith only [hx', hmul, mul_pos hs.1 (sub_pos.mpr hxy)]
    · rw [hfix y (fun v hv h => hy ⟨v, hv, h⟩)]
      exact hfx.trans_lt hxy
  have hf : Continuous f :=
    continuous_id.sub (continuous_const.mul (continuous_finsetSum _ fun v _ => by
      unfold ramp stripRamp
      fun_prop))
  have hg : Continuous g := continuous_finsetSum _ fun v _ => by
    unfold offset stripPlateau
    fun_prop
  obtain ⟨lo, hlo⟩ := (V.image fun v => a v - 1 / 8).finite_toSet.bddBelow
  obtain ⟨hi, hhi⟩ := (V.image fun v => right v + 1 / 8).finite_toSet.bddAbove
  have hsurj : Function.Surjective f := by
    intro x
    have hfl : f (min lo x) = min lo x := hfix _ fun v hv hx =>
      not_lt_of_ge ((min_le_left lo x).trans (hlo (Finset.mem_image.mpr ⟨v, hv, rfl⟩))) hx.1
    have hfu : f (max hi x) = max hi x := hfix _ fun v hv hx =>
      not_lt_of_ge ((hhi (Finset.mem_image.mpr ⟨v, hv, rfl⟩)).trans (le_max_left hi x)) hx.2
    obtain ⟨y, _, hy⟩ := intermediate_value_Icc (min_le_right lo x |>.trans (le_max_right hi x))
      hf.continuousOn (show x ∈ Set.Icc (f (min lo x)) (f (max hi x)) by
        rw [hfl, hfu]; exact ⟨min_le_right lo x, le_max_right hi x⟩)
    exact ⟨y, hy⟩
  let e : ℝ ≃o ℝ := hmono.orderIsoOfSurjective f hsurj
  let F : ℂ ≃ₜ ℂ :=
    { toFun := fun z => ⟨f z.re, s * z.im + g z.re⟩
      invFun := fun z => ⟨e.symm z.re, (z.im - g (e.symm z.re)) / s⟩
      left_inv := by
        intro z
        have h : e.symm (f z.re) = z.re := e.symm_apply_apply _
        apply Complex.ext h
        change (s * z.im + g z.re - g (e.symm (f z.re))) / s = z.im
        rw [h]
        apply (div_eq_iff hs.1.ne').mpr
        ring
      right_inv := by
        intro z
        have h : f (e.symm z.re) = z.re := e.apply_symm_apply _
        apply Complex.ext h
        change s * ((z.im - g (e.symm z.re)) / s) + g (e.symm z.re) = z.im
        have hc := div_mul_cancel₀ (z.im - g (e.symm z.re)) hs.1.ne'
        linarith only [hc]
      continuous_toFun := by
        change Continuous (fun z : ℂ =>
          Complex.equivRealProdCLM.symm (f z.re, s * z.im + g z.re))
        exact Complex.equivRealProdCLM.symm.continuous.comp
          ((hf.comp Complex.continuous_re).prodMk
            ((continuous_const.mul Complex.continuous_im).add (hg.comp Complex.continuous_re)))
      continuous_invFun := by
        change Continuous (fun z : ℂ => Complex.equivRealProdCLM.symm
          (e.symm z.re, (z.im - g (e.symm z.re)) / s))
        have he := e.symm.continuous.comp Complex.continuous_re
        exact Complex.equivRealProdCLM.symm.continuous.comp
          (he.prodMk ((Complex.continuous_im.sub (hg.comp he)).div_const s)) }
  have hlocal {v : ℕ} (hv : v ∈ V) {z : ℂ} (hz : z.re ∈ Set.Icc (a v) (right v)) :
      F z = referencePoint I v + s • (z - referencePoint I v) := by
    have hz' : z.re ∈ band v := ⟨by linarith only [hz.1], by linarith only [hz.2]⟩
    have hre : f z.re = z.re - (1 - s) * (z.re - a v) := by
      simp only [f, hsum ramp (fun w hw _ hxw => hramp hw hxw) hv hz']
      have hexact : stripRamp (a v) (right v) (right v + 1 / 8) z.re = z.re - a v :=
        stripRamp_eq_sub (hright v (hmem.mp hv)) (hgap v) hz
      simp only [ramp, hexact]
    have him : g z.re = (1 - s) * (referencePoint I v).im := by
      simp only [g, hsum offset (fun _ _ _ h => hoffset h) hv hz']
      simp only [offset, stripPlateau_eq_one hz, mul_one]
    apply Complex.ext
    · change f z.re = (referencePoint I v + s • (z - referencePoint I v)).re
      rw [hre, Complex.add_re, Complex.smul_re, Complex.sub_re]
      change z.re - (1 - s) * (z.re - (referencePoint I v).re) = _
      ring
    · change s * z.im + g z.re = (referencePoint I v + s • (z - referencePoint I v)).im
      rw [him, Complex.add_im, Complex.smul_im, Complex.sub_im]
      ring
  let knots (v : ℕ) : Finset ℝ := {a v - 1 / 8, a v, right v, right v + 1 / 8}
  let levels := V.biUnion knots
  have hforward (z w : ℂ)
      (hcut : ∀ k ∈ levels, k ∉ Set.Ioo (min z.re w.re) (max z.re w.re))
      {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
      F (AffineMap.lineMap z w t) = AffineMap.lineMap (F z) (F w) t := by
    have hlocalCut {v : ℕ} (hv : v ∈ V) {k : ℝ} (hk : k ∈ knots v) :
        k ∉ Set.Ioo (min z.re w.re) (max z.re w.re) :=
      hcut k (Finset.mem_biUnion.mpr ⟨v, hv, hk⟩)
    have hR := sum_map_lineMap V ramp z.re w.re t (fun v hv => by
      have h : a v < right v := hright v (hmem.mp hv)
      exact map_lineMap_of_affine_on
        (stripRamp_affine_on h (hgap v) (hlocalCut hv (by simp [knots]))
          (hlocalCut hv (by simp [knots])) (hlocalCut hv (by simp [knots]))) ht)
    have hG : g (AffineMap.lineMap z.re w.re t) = AffineMap.lineMap (g z.re) (g w.re) t := by
      apply sum_map_lineMap
      intro v hv
      obtain ⟨m, d, h⟩ := stripPlateau_affine_on (a := a v) (b := right v)
        (x := z.re) (y := w.re) (hright v (hmem.mp hv)).le
        (hlocalCut hv (by simp [knots])) (hlocalCut hv (by simp [knots]))
        (hlocalCut hv (by simp [knots])) (hlocalCut hv (by simp [knots]))
      let c := (1 - s) * (referencePoint I v).im
      apply map_lineMap_of_affine_on (t := t) _ ht
      refine ⟨c * m, c * d, fun x hx => ?_⟩
      change c * stripPlateau (a v) (right v) x = _
      rw [h x hx]
      ring
    have hreal (p q : ℂ) : (AffineMap.lineMap p q t).re = AffineMap.lineMap p.re q.re t :=
      AffineMap.apply_lineMap Complex.reCLM.toLinearMap.toAffineMap p q t
    have himag (p q : ℂ) : (AffineMap.lineMap p q t).im = AffineMap.lineMap p.im q.im t :=
      AffineMap.apply_lineMap Complex.imCLM.toLinearMap.toAffineMap p q t
    apply Complex.ext
    · change f (AffineMap.lineMap z w t).re = (AffineMap.lineMap (F z) (F w) t).re
      rw [hreal, hreal]
      change f (AffineMap.lineMap z.re w.re t) = AffineMap.lineMap (f z.re) (f w.re) t
      simp only [f]
      rw [hR]
      simp only [AffineMap.lineMap_apply_ring]
      ring
    · change s * (AffineMap.lineMap z w t).im + g (AffineMap.lineMap z w t).re =
        (AffineMap.lineMap (F z) (F w) t).im
      rw [hreal, himag, himag, hG]
      change s * AffineMap.lineMap z.im w.im t + AffineMap.lineMap (g z.re) (g w.re) t =
        AffineMap.lineMap (s * z.im + g z.re) (s * w.im + g w.re) t
      simp only [AffineMap.lineMap_apply_ring]
      ring
  refine ⟨F, levels.image f, ?_, ?_, ?_⟩
  · intro v hv
    simpa only [sub_self, smul_zero, add_zero] using
      hlocal (z := referencePoint I v) (hmem.mpr hv) ⟨le_rfl, (hright v hv).le⟩
  · intro d hd z hz
    have hv : d.vertex ∈ V :=
      hmem.mpr (hI.1 ▸ List.mem_range.mpr (fixed_end_reference_spec hI d hd).1)
    have hz' := hstrip d hd z hz
    exact hlocal hv ⟨hz'.1, hz'.2.le⟩
  · intro z w hz t ht
    have hcut (k : ℝ) (hk : k ∈ levels) :
        k ∉ Set.Ioo (min (F.symm z).re (F.symm w).re) (max (F.symm z).re (F.symm w).re) := by
      intro h
      have hresz : f (F.symm z).re = z.re := congrArg Complex.re (F.apply_symm_apply z)
      have hresw : f (F.symm w).re = w.re := congrArg Complex.re (F.apply_symm_apply w)
      have hl := hmono h.1
      have hr := hmono h.2
      rw [hmono.monotone.map_min, hresz, hresw] at hl
      rw [hmono.monotone.map_max, hresz, hresw] at hr
      exact hz _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩) ⟨hl, hr⟩
    have h := hforward (F.symm z) (F.symm w) hcut ht
    rw [F.apply_symm_apply, F.apply_symm_apply] at h
    exact F.injective ((F.apply_symm_apply _).trans h.symm)

private theorem same_center_contacts {I : FixedRotationInput} (hI : Valid I)
    (a b : Dart I.graph) (ha : (I.orders.getD a.vertex none).isSome = true)
    (hv : a.vertex = b.vertex)
    (hab : (subdivisionDart I a).1 ≠ (subdivisionDart I b).1)
    (i : Fin ((referenceDrawing I).route (subdivisionDart I a).1).segments)
    (j : Fin ((referenceDrawing I).route (subdivisionDart I b).1).segments)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : ((referenceDrawing I).route (subdivisionDart I a).1).eval i s =
      ((referenceDrawing I).route (subdivisionDart I b).1).eval j t) :
    Route.endTime a.2 s = 0 ∧ Route.endTime b.2 t = 0 := by
  have hσ := Route.endTime_mem a.2 hs
  have hτ := Route.endTime_mem b.2 ht
  have hva := referenceDrawing_subdivisionDart_germ_ne_zero hI a
  have hvb := referenceDrawing_subdivisionDart_germ_ne_zero hI b
  rw [eval_from_original_end, eval_from_original_end, hv] at heq
  have hvec := add_left_cancel heq
  by_cases hzero : Route.endTime a.2 s = 0
  · refine ⟨hzero, ?_⟩
    rw [hzero, zero_smul] at hvec
    exact (smul_eq_zero.mp hvec.symm).resolve_right hvb
  have hσpos := lt_of_le_of_ne hσ.1 (Ne.symm hzero)
  have hτpos : 0 < Route.endTime b.2 t := by
    apply lt_of_le_of_ne hτ.1
    intro hzero'
    rw [← hzero', zero_smul] at hvec
    exact hzero ((smul_eq_zero.mp hvec).resolve_right hva)
  have harg := congrArg Complex.arg hvec
  simp only [Complex.real_smul, Complex.arg_ofReal_mul hσpos _,
    Complex.arg_ofReal_mul hτpos _] at harg
  obtain ⟨word, hw, ham⟩ := fixed_end_word hI a ha
  have hbm : b.index ∈ word :=
    ((hI.2.2.2 a.vertex word hw).2 b.index).mpr (by simpa only [hv] using index_mem_fiber b)
  have he := referenceDrawing_fixedWord_directions_injective hI hw ham hbm
    (congrArg (fun x : ℝ => (x : Real.Angle)) harg)
  exact (hab (congrArg (fun d => (subdivisionDart I d).1) he)).elim

private theorem separated_blocks_no_contact {I : FixedRotationInput} (hI : Valid I)
    (a b : Dart I.graph) (ha : (I.orders.getD a.vertex none).isSome = true)
    (hb : (I.orders.getD b.vertex none).isSome = true) (hab : a.vertex < b.vertex)
    (i : Fin ((referenceDrawing I).route (subdivisionDart I a).1).segments)
    (j : Fin ((referenceDrawing I).route (subdivisionDart I b).1).segments)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    ((referenceDrawing I).route (subdivisionDart I a).1).eval i s ≠
      ((referenceDrawing I).route (subdivisionDart I b).1).eval j t := by
  intro heq
  obtain ⟨right, _, hsep, hstrip⟩ := exists_frozen_reference_strips hI
  have haS := hstrip a ha _ ((referenceDrawing I).route _ |>.at_mem_support i hs)
  have hbS := hstrip b hb _ ((referenceDrawing I).route _ |>.at_mem_support j ht)
  have hdecl (d : Dart I.graph) (hd : (I.orders.getD d.vertex none).isSome) :
      d.vertex ∈ I.graph.vertices :=
    hI.1 ▸ List.mem_range.mpr (fixed_end_reference_spec hI d hd).1
  have hgap := hsep _ (hdecl a ha) _ (hdecl b hb) hab
  linarith only [haS.2, hbS.1, hgap, congrArg Complex.re heq]

/-- Distinct actual stored frozen routes meet only at a common named endpoint. The two
parameters range over the entire closed unit intervals, including endpoint-zero branches. -/
theorem referenceDrawing_frozen_edge_contacts {I : FixedRotationInput} (hI : Valid I)
    (e f : Fin (subdivisionGraph I).edges.length) (hef : e ≠ f)
    (he : ((subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true)
    (hf : ((subdivide I)[f.val]'(by
      simpa only [subdivisionGraph, List.length_map] using f.isLt)).frozen = true)
    (i : Fin ((referenceDrawing I).route e).segments)
    (j : Fin ((referenceDrawing I).route f).segments)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : ((referenceDrawing I).route e).eval i s =
      ((referenceDrawing I).route f).eval j t) :
    ∃ b c, ((referenceDrawing I).route e).AtEnd i s b ∧
      ((referenceDrawing I).route f).AtEnd j t c ∧ Dart.vertex (e, b) = Dart.vertex (f, c) := by
  obtain ⟨a, rfl, ha⟩ := (frozen_iff_exists_subdivisionDart I e).mp he
  obtain ⟨b, rfl, hb⟩ := (frozen_iff_exists_subdivisionDart I f).mp hf
  by_cases hv : a.vertex = b.vertex
  · obtain ⟨hσ, hτ⟩ := same_center_contacts hI a b ha hv hef i j hs ht heq
    exact ⟨a.2, b.2, at_original_end_of_outgoing_zero I a i hσ,
      at_original_end_of_outgoing_zero I b j hτ,
      ((subdivisionDart_endpoints I a).1.trans hv).trans
        (subdivisionDart_endpoints I b).1.symm⟩
  rcases lt_or_gt_of_ne hv with hab | hba
  · exact (separated_blocks_no_contact hI a b ha hb hab i j hs ht heq).elim
  · exact (separated_blocks_no_contact hI b a hb ha hba j i ht hs heq.symm).elim

private noncomputable def frozenIndexData (I : FixedRotationInput) :
    { f : Fin ((subdivide I).filter Segment.frozen).length ↪o Fin (subdivide I).length //
      ∀ i, ((subdivide I).filter Segment.frozen).get i = (subdivide I).get (f i) } := by
  have h := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
    (List.filter_sublist (p := Segment.frozen) (l := subdivide I))
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

private noncomputable def frozenIndex (I : FixedRotationInput)
    (e : Fin (frozenGraph I).edges.length) : Fin (subdivisionGraph I).edges.length := by
  let i : Fin ((subdivide I).filter Segment.frozen).length :=
    ⟨e.val, by simpa only [frozenGraph, List.length_map] using e.isLt⟩
  let j := (frozenIndexData I).val i
  exact ⟨j.val, by simpa only [subdivisionGraph, List.length_map] using j.isLt⟩

private theorem frozenIndex_get (I : FixedRotationInput)
    (e : Fin (frozenGraph I).edges.length) :
    ((subdivide I).filter Segment.frozen)[e.val]'(by
      simpa only [frozenGraph, List.length_map] using e.isLt) =
      (subdivide I)[(frozenIndex I e).val]'(by
        simpa only [subdivisionGraph, List.length_map] using (frozenIndex I e).isLt) := by
  exact (frozenIndexData I).property
    ⟨e.val, by simpa only [frozenGraph, List.length_map] using e.isLt⟩

private theorem frozenIndex_injective (I : FixedRotationInput) :
    Function.Injective (frozenIndex I) := by
  intro e f hef
  have hval := congrArg Fin.val hef
  have h := (frozenIndexData I).val.injective (Fin.ext hval)
  have hv : e.val = f.val := congrArg
    (fun i : Fin ((subdivide I).filter Segment.frozen).length => i.val) h
  exact Fin.ext hv

private theorem frozenIndex_flag (I : FixedRotationInput)
    (e : Fin (frozenGraph I).edges.length) :
    ((subdivide I)[(frozenIndex I e).val]'(by
      simpa only [subdivisionGraph, List.length_map] using
        (frozenIndex I e).isLt)).frozen = true := by
  have hm := List.getElem_mem (l := (subdivide I).filter Segment.frozen)
    (n := e.val) (by simpa only [frozenGraph, List.length_map] using e.isLt)
  exact (List.mem_filter.mp ((frozenIndex_get I e) ▸ hm)).2

private theorem frozenIndex_vertex (I : FixedRotationInput)
    (e : Fin (frozenGraph I).edges.length) (b : Bool) :
    Dart.vertex (frozenIndex I e, b) = Dart.vertex (e, b) := by
  have hends := congrArg Segment.endpoints (frozenIndex_get I e)
  have hedge : (subdivisionGraph I).edges[(frozenIndex I e).val] =
      (frozenGraph I).edges[e.val] := by
    simpa only [subdivisionGraph, frozenGraph, List.getElem_map] using hends.symm
  cases b <;>
    simp only [Dart.vertex, Graph.edgeEndpoint, Bool.false_eq_true, ↓reduceIte] <;>
    rw [List.getD_eq_getElem (subdivisionGraph I).edges (0, 0) (frozenIndex I e).isLt,
      List.getD_eq_getElem (frozenGraph I).edges (0, 0) e.isLt, hedge]

/-- The literal ordered restriction to stored frozen segments. The vertex function and full
frame declaration range are retained, including every isolated subdivision point. -/
noncomputable def frozenReferenceDrawing (I : FixedRotationInput) :
    PolygonalDrawing (frozenGraph I) where
  vertex := (referenceDrawing I).vertex
  route e := (referenceDrawing I).route (frozenIndex I e)
  endpoint_eq e b := ((referenceDrawing I).endpoint_eq _ _).trans
    (congrArg (referenceDrawing I).vertex (frozenIndex_vertex I e b))

/-- Every declared and undeclared name keeps precisely its existing reference coordinate. -/
@[simp] theorem frozenReferenceDrawing_vertex (I : FixedRotationInput) (v : ℕ) :
    (frozenReferenceDrawing I).vertex v = referencePoint I v := by
  simp only [frozenReferenceDrawing, referenceDrawing]

/-- Retaining only frozen indexed routes gives an actual embedding. All vertex-contact,
simplicity and pair-contact obligations are discharged internally from valid input. -/
theorem frozenReferenceDrawing_isEmbedding {I : FixedRotationInput} (hI : Valid I) :
    (frozenReferenceDrawing I).IsEmbedding where
  vertices_injective := referenceDrawing_vertices_injective hI
  simple e := referenceDrawing_simple hI (frozenIndex I e)
  vertex_contacts := by
    intro e i t ht v hv heq
    obtain ⟨b, hb, hvertex⟩ := referenceDrawing_vertex_contacts hI (frozenIndex I e) i ht hv heq
    exact ⟨b, hb, (frozenIndex_vertex I e b).symm.trans hvertex⟩
  edge_contacts := by
    intro e f hef i j s t hs ht heq
    obtain ⟨b, c, hb, hc, hvertex⟩ := referenceDrawing_frozen_edge_contacts hI
      (frozenIndex I e) (frozenIndex I f) (fun h => hef (frozenIndex_injective I h))
      (frozenIndex_flag I e) (frozenIndex_flag I f) i j hs ht heq
    exact ⟨b, c, hb, hc, (frozenIndex_vertex I e b).symm.trans
      (hvertex.trans (frozenIndex_vertex I f c))⟩

private theorem reference_routes_eq_of_segment_eq (I : FixedRotationInput)
    {e f : Fin (subdivisionGraph I).edges.length}
    (hseg : (subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt) =
      (subdivide I)[f.val]'(by
        simpa only [subdivisionGraph, List.length_map] using f.isLt)) :
    (referenceDrawing I).route e = (referenceDrawing I).route f := by
  have hends : (subdivisionGraph I).edges[e.val] = (subdivisionGraph I).edges[f.val] := by
    simpa only [subdivisionGraph, List.getElem_map] using congrArg Segment.endpoints hseg
  simp only [referenceDrawing, Dart.vertex, Graph.edgeEndpoint, Bool.false_eq_true, ↓reduceIte,
    List.getD_eq_getElem _ _ e.isLt, List.getD_eq_getElem _ _ f.isLt, hends]

private theorem frozen_segment_index_injective {I : FixedRotationInput} (hI : Valid I)
    {e f : Fin (subdivisionGraph I).edges.length}
    (he : ((subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true)
    (hf : ((subdivide I)[f.val]'(by
      simpa only [subdivisionGraph, List.length_map] using f.isLt)).frozen = true)
    (hseg : (subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt) =
      (subdivide I)[f.val]'(by
        simpa only [subdivisionGraph, List.length_map] using f.isLt)) : e = f := by
  by_contra hne
  have hroute := reference_routes_eq_of_segment_eq I hseg
  have hpoint : ((referenceDrawing I).route e).eval 0 (1 / 2) =
      ((referenceDrawing I).route f).eval 0 (1 / 2) := by rw [hroute]
  obtain ⟨b, _, hb, _, _⟩ := referenceDrawing_frozen_edge_contacts hI e f hne he hf
    0 0 (by constructor <;> norm_num) (by constructor <;> norm_num) hpoint
  exact Route.not_atEnd_of_mem_Ioo _ 0 (by constructor <;> norm_num) b hb

private theorem frozenIndex_covers {I : FixedRotationInput} (hI : Valid I)
    (e : Fin (subdivisionGraph I).edges.length)
    (he : ((subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true) :
    ∃ f, frozenIndex I f = e := by
  have heBound : e.val < (subdivide I).length := by
    simpa only [subdivisionGraph, List.length_map] using e.isLt
  have hm : (subdivide I)[e.val]'heBound ∈ (subdivide I).filter Segment.frozen :=
    List.mem_filter.mpr ⟨List.getElem_mem heBound, he⟩
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hm
  let f : Fin (frozenGraph I).edges.length :=
    ⟨j, by simpa only [frozenGraph, List.length_map] using hj⟩
  refine ⟨f, frozen_segment_index_injective hI (frozenIndex_flag I f) he ?_⟩
  exact (frozenIndex_get I f).symm.trans hget

private theorem fixed_of_word {I : FixedRotationInput} (hI : Valid I) {v : ℕ} {word : List ℕ}
    (hw : I.orders.getD v none = some word) {d : Dart I.graph} (hd : d.index ∈ word) :
    (I.orders.getD d.vertex none).isSome = true := by
  rw [fixedWord_dart_vertex hI hw hd, hw]
  rfl

/-- The actual retained indexed end selected by a literal complete stored word. Its source
fixedness and coverage by the filtered drawing are derived internally. -/
noncomputable def frozenReferenceDart {I : FixedRotationInput} (hI : Valid I)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    (d : Dart I.graph) (hd : d.index ∈ word) : Dart (frozenGraph I) :=
  (Classical.choose (frozenIndex_covers hI (subdivisionDart I d).1
    ((frozen_iff_exists_subdivisionDart I _).mpr ⟨d, rfl, fixed_of_word hI hw hd⟩)), d.2)

private theorem frozenReferenceDart_index {I : FixedRotationInput} (hI : Valid I)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    (d : Dart I.graph) (hd : d.index ∈ word) :
    frozenIndex I (frozenReferenceDart hI hw d hd).1 = (subdivisionDart I d).1 :=
  Classical.choose_spec (frozenIndex_covers hI (subdivisionDart I d).1
    ((frozen_iff_exists_subdivisionDart I _).mpr ⟨d, rfl, fixed_of_word hI hw hd⟩))

/-- Retention preserves the original occurrence's end tag, its center and its own leaf. -/
theorem frozenReferenceDart_endpoints {I : FixedRotationInput} (hI : Valid I)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    (d : Dart I.graph) (hd : d.index ∈ word) :
    (frozenReferenceDart hI hw d hd).2 = d.2 ∧
      (frozenReferenceDart hI hw d hd).vertex = d.vertex ∧
      (frozenReferenceDart hI hw d hd).reverse.vertex = I.graph.vertices.length + d.index := by
  have hindex := frozenReferenceDart_index hI hw d hd
  have hcenter := frozenIndex_vertex I (frozenReferenceDart hI hw d hd).1 d.2
  have hleaf := frozenIndex_vertex I (frozenReferenceDart hI hw d hd).1 (!d.2)
  rw [hindex] at hcenter hleaf
  exact ⟨rfl, hcenter.symm.trans (subdivisionDart_endpoints I d).1,
    hleaf.symm.trans (subdivisionDart_endpoints I d).2⟩

/-- Every retained original fixed end has exactly its old outgoing geometric vector. -/
theorem frozenReferenceDrawing_germ_frozenReferenceDart {I : FixedRotationInput} (hI : Valid I)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    (d : Dart I.graph) (hd : d.index ∈ word) :
    (frozenReferenceDrawing I).germ (frozenReferenceDart hI hw d hd) =
      (referenceDrawing I).germ (subdivisionDart I d) := by
  change ((referenceDrawing I).route
    (frozenIndex I (frozenReferenceDart hI hw d hd).1)).germ d.2 = _
  rw [frozenReferenceDart_index]
  rfl

/-- Restriction retains the complete literal prescribed clockwise order, expressed as the
reversed `c,b,a` angular triple. The fixed-end proofs are derived from the full stored word. -/
theorem frozenReferenceDrawing_fixedWord_clockwise_iff {I : FixedRotationInput} (hI : Valid I)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    {a b c : Dart I.graph} (ha : a.index ∈ word) (hb : b.index ∈ word) (hc : c.index ∈ word)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw ((frozenReferenceDrawing I).direction (frozenReferenceDart hI hw c hc))
      ((frozenReferenceDrawing I).direction (frozenReferenceDart hI hw b hb))
      ((frozenReferenceDrawing I).direction (frozenReferenceDart hI hw a ha)) ↔
        (word.idxOf a.index < word.idxOf b.index ∧ word.idxOf b.index < word.idxOf c.index) ∨
        (word.idxOf b.index < word.idxOf c.index ∧ word.idxOf c.index < word.idxOf a.index) ∨
        (word.idxOf c.index < word.idxOf a.index ∧ word.idxOf a.index < word.idxOf b.index) := by
  simp only [PolygonalDrawing.direction, frozenReferenceDrawing_germ_frozenReferenceDart]
  exact referenceDrawing_fixedWord_clockwise_iff hI hw ha hb hc hab hbc hac

end Cslib.Complexity.Graph.RotationRecognition
