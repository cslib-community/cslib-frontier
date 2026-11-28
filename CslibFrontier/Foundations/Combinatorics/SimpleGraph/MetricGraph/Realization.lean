/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/Realization.lean`)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Subdivision
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Maps
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

/-!
# Euclidean straight-edge realizations of metric graphs

This module constructs an isometric straight-edge realization of any finite connected metric graph
in `EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1))` after subdividing each edge into three
sub-segments. When all original edge weights are rational, every subdivided vertex has rational
coordinates.

## Main definitions

* `SimpleGraph.MetricGraph.realizationPoints`: the finite set of vertices together with two interior
  subdivision points on each original edge, dividing every edge into three sub-segments.
* `SimpleGraph.MetricGraph.realizationSubdivision`: the three-segment subdivision of `W`.
* `SimpleGraph.MetricGraph.realizationMap`: the straight-edge map from
  `MetricGraph (realizationSubdivision W)` into
  `EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1))`.
* `SimpleGraph.MetricGraph.realizationFromGraph`: the composed map from `MetricGraph W` into
  `EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1))`.
* `SimpleGraph.MetricGraph.realizationEuclideanGraph`: the weighted graph on `realizationPoints W`
  whose weights are the Euclidean distances between endpoints of `realizationMap`.

## Main results

* `SimpleGraph.MetricGraph.realizationMap_vertex`,
  `SimpleGraph.MetricGraph.realizationMap_edgePoint`:
  `realizationMap` maps every subdivided edge affinely onto the Euclidean straight line segment
  between its endpoints.
* `SimpleGraph.MetricGraph.realizationMap_edge_dist`,
  `SimpleGraph.MetricGraph.realizationMap_edgePoint_dist`: each subdivided edge is mapped
  isometrically onto its Euclidean segment.
* `SimpleGraph.MetricGraph.realizationMap_isClosedEmbedding`,
  `SimpleGraph.MetricGraph.realizationFromGraph_isClosedEmbedding`: closed topological embeddings
  into Euclidean space.
* `SimpleGraph.MetricGraph.realizationEuclideanEquiv`: isometric equivalence between
  `MetricGraph (realizationEuclideanGraph W)` and `MetricGraph W`.
* `SimpleGraph.MetricGraph.realizationMap_vertex_rational`: rational weights give rational vertex
  coordinates.

## References

* STOC 2027 submission 1056, Appendix C, Lemma C.2 (locator from Issue #4324 context; primary
  manuscript not inspected here).
-/

public section

open scoped unitInterval

namespace SimpleGraph

namespace MetricGraph

universe u

variable {V : Type u}

/-! ### Three-segment geometry and Euclidean vertex coordinates -/

open Classical in
private noncomputable def vertexEquiv [Finite V] : V ≃ Fin (Nat.card V) :=
  let : Fintype V := Fintype.ofFinite V
  Fintype.equivFinOfCardEq Fintype.card_eq_nat_card

open Classical in
private noncomputable def edgeEquiv [Finite V] (W : WeightedGraph V) :
    W.graph.edgeSet ≃ Fin (Nat.card W.graph.edgeSet) :=
  let : Fintype W.graph.edgeSet := Fintype.ofFinite _
  Fintype.equivFinOfCardEq Fintype.card_eq_nat_card

private theorem edge_weight_pos (W : WeightedGraph V) (e : W.graph.edgeSet) :
    0 < W.weight e.val := by
  simpa only [edgeDartOfSym2_edge] using W.dart_weight_pos (edgeDartOfSym2 e)

private noncomputable def minEdgeWeight [Finite V] (W : WeightedGraph V) : ℝ :=
  if h : 0 < Nat.card W.graph.edgeSet then
    ((Finset.univ : Finset (Fin (Nat.card W.graph.edgeSet))).image
      fun k => W.weight ((edgeEquiv W).symm k).val).min'
      (Finset.Nonempty.image ⟨⟨0, h⟩, Finset.mem_univ _⟩ _)
  else 1

private theorem exists_minEdgeWeight_eq_weight [Finite V] (W : WeightedGraph V)
    (hpos : 0 < Nat.card W.graph.edgeSet) :
    ∃ e : W.graph.edgeSet, minEdgeWeight W = W.weight e.val := by
  dsimp only [minEdgeWeight]
  split_ifs
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (Finset.min'_mem
    ((Finset.univ : Finset (Fin (Nat.card W.graph.edgeSet))).image
      fun k => W.weight ((edgeEquiv W).symm k).val)
    (Finset.Nonempty.image ⟨⟨0, hpos⟩, Finset.mem_univ _⟩ _))
  exact ⟨(edgeEquiv W).symm k, hk.symm⟩

private theorem minEdgeWeight_pos [Finite V] (W : WeightedGraph V) : 0 < minEdgeWeight W := by
  by_cases h : 0 < Nat.card W.graph.edgeSet
  · obtain ⟨e, he⟩ := exists_minEdgeWeight_eq_weight W h
    exact he ▸ edge_weight_pos W e
  · dsimp only [minEdgeWeight]
    split_ifs
    exact one_pos

private theorem minEdgeWeight_le [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    minEdgeWeight W ≤ W.weight e.val := by
  classical
  have hpos : 0 < Nat.card W.graph.edgeSet := Nat.card_pos_iff.mpr ⟨⟨e⟩, inferInstance⟩
  dsimp only [minEdgeWeight]
  split_ifs
  exact Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨edgeEquiv W e, Finset.mem_univ _, by rw [Equiv.symm_apply_apply]⟩)

private theorem minEdgeWeight_rational [Finite V] (W : WeightedGraph V)
    (hQ : ∀ e ∈ W.graph.edgeSet, ∃ q : ℚ, W.weight e = q) :
    ∃ q : ℚ, minEdgeWeight W = q := by
  by_cases h : 0 < Nat.card W.graph.edgeSet
  · obtain ⟨e, he⟩ := exists_minEdgeWeight_eq_weight W h
    exact he ▸ hQ e.val e.property
  · exact ⟨1, by dsimp only [minEdgeWeight]; split_ifs; exact Rat.cast_one.symm⟩

private noncomputable def vertexSpacing [Finite V] (W : WeightedGraph V) : ℝ :=
  minEdgeWeight W / (2 * ((Nat.card V : ℝ) + 1))

private theorem vertexSpacing_pos [Finite V] (W : WeightedGraph V) : 0 < vertexSpacing W :=
  div_pos (minEdgeWeight_pos W) (by positivity)

private theorem vertexSpacing_rational [Finite V] (W : WeightedGraph V)
    (hQ : ∀ e ∈ W.graph.edgeSet, ∃ q : ℚ, W.weight e = q) :
    ∃ q : ℚ, vertexSpacing W = q := by
  obtain ⟨q, hq⟩ := minEdgeWeight_rational W hQ
  exact ⟨q / (2 * (Nat.card V + 1 : ℚ)), by rw [vertexSpacing, hq]; push_cast; rfl⟩

private noncomputable def vertexPos [Finite V] (W : WeightedGraph V) (v : V) :
    EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1)) :=
  (vertexSpacing W * ((vertexEquiv v : ℕ) : ℝ)) • EuclideanSpace.single 0 (1 : ℝ)

private theorem vertexPos_apply_zero [Finite V] (W : WeightedGraph V) (v : V) :
    vertexPos W v 0 = vertexSpacing W * ((vertexEquiv v : ℕ) : ℝ) := by
  rw [vertexPos, PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul, mul_one]

private theorem vertexPos_apply_succ [Finite V] (W : WeightedGraph V) (v : V)
    (k : Fin (Nat.card W.graph.edgeSet)) :
    vertexPos W v k.succ = 0 := by
  rw [vertexPos, PiLp.smul_apply, PiLp.single_eq_of_ne 2 k.succ_ne_zero, smul_zero]

private theorem dist_vertexPos_eq [Finite V] (W : WeightedGraph V) (u v : V) :
    dist (vertexPos W u) (vertexPos W v) =
      vertexSpacing W * |((vertexEquiv u : ℕ) : ℝ) - (vertexEquiv v : ℕ)| := by
  rw [vertexPos, vertexPos, dist_eq_norm, ← sub_smul, norm_smul, PiLp.norm_single, norm_one,
    mul_one, ← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos (vertexSpacing_pos W)]

private theorem vertexPos_apply_zero_ne [Finite V] (W : WeightedGraph V) {u v : V}
    (hne : u ≠ v) : vertexPos W u 0 ≠ vertexPos W v 0 := by
  intro heq
  rw [vertexPos_apply_zero, vertexPos_apply_zero] at heq
  exact hne (vertexEquiv.injective (Fin.ext (by
    exact_mod_cast mul_left_cancel₀ (vertexSpacing_pos W).ne' heq)))

private noncomputable def edgeChordDist [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) : ℝ :=
  dist (vertexPos W (edgeDartOfSym2 e).fst) (vertexPos W (edgeDartOfSym2 e).snd)

private theorem edgeChordDist_pos [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    0 < edgeChordDist W e := by
  refine dist_pos.mpr fun h => vertexPos_apply_zero_ne W (edgeDartOfSym2 e).fst_ne_snd ?_
  exact congrArg (· 0) h

private theorem edgeChordDist_lt_weight [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    edgeChordDist W e < W.weight e.val := by
  rw [edgeChordDist, dist_vertexPos_eq]
  have hu := Nat.cast_lt (α := ℝ) |>.mpr (vertexEquiv (edgeDartOfSym2 e).fst).isLt
  have hv := Nat.cast_lt (α := ℝ) |>.mpr (vertexEquiv (edgeDartOfSym2 e).snd).isLt
  have habs : |((vertexEquiv (edgeDartOfSym2 e).fst : ℕ) : ℝ) -
      (vertexEquiv (edgeDartOfSym2 e).snd : ℕ)| < (Nat.card V : ℝ) + 1 :=
    abs_lt.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) (vertexEquiv (edgeDartOfSym2 e).fst : ℕ)],
      by linarith [Nat.cast_nonneg (α := ℝ) (vertexEquiv (edgeDartOfSym2 e).snd : ℕ)]⟩
  have hsp : vertexSpacing W * ((Nat.card V : ℝ) + 1) = minEdgeWeight W / 2 := by
    have hpos : (Nat.card V : ℝ) + 1 ≠ 0 := by positivity
    dsimp only [vertexSpacing]
    field_simp
  linarith [mul_lt_mul_of_pos_left habs (vertexSpacing_pos W), minEdgeWeight_pos W,
    minEdgeWeight_le W e]

private noncomputable def edgeLegHeight [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) : ℝ :=
  (W.weight e.val - edgeChordDist W e) / 2

private theorem edgeLegHeight_pos [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    0 < edgeLegHeight W e := by
  dsimp only [edgeLegHeight]
  linarith [edgeChordDist_lt_weight W e]

private theorem two_mul_legHeight_add_chord [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) :
    2 * edgeLegHeight W e + edgeChordDist W e = W.weight e.val := by
  dsimp only [edgeLegHeight]
  ring

private noncomputable def ratio1 [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    unitInterval :=
  ⟨edgeLegHeight W e / W.weight e.val,
    div_nonneg (edgeLegHeight_pos W e).le (edge_weight_pos W e).le,
    (div_le_one (edge_weight_pos W e)).mpr
      (by linarith [edgeLegHeight_pos W e, edgeChordDist_pos W e,
        two_mul_legHeight_add_chord W e])⟩

private noncomputable def ratio2 [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    unitInterval :=
  ⟨(edgeLegHeight W e + edgeChordDist W e) / W.weight e.val,
    div_nonneg (add_pos (edgeLegHeight_pos W e) (edgeChordDist_pos W e)).le
      (edge_weight_pos W e).le,
    (div_le_one (edge_weight_pos W e)).mpr
      (by linarith [edgeLegHeight_pos W e, two_mul_legHeight_add_chord W e])⟩

private theorem ratio1_mul_weight [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    (ratio1 W e : ℝ) * W.weight e.val = edgeLegHeight W e :=
  div_mul_cancel₀ _ (edge_weight_pos W e).ne'

private theorem ratio2_mul_weight [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    (ratio2 W e : ℝ) * W.weight e.val = edgeLegHeight W e + edgeChordDist W e :=
  div_mul_cancel₀ _ (edge_weight_pos W e).ne'

private theorem ratio1_pos [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    (0 : ℝ) < ratio1 W e :=
  div_pos (edgeLegHeight_pos W e) (edge_weight_pos W e)

private theorem ratio1_lt_ratio2 [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    (ratio1 W e : ℝ) < ratio2 W e :=
  div_lt_div_of_pos_right (by linarith [edgeChordDist_pos W e]) (edge_weight_pos W e)

private theorem ratio2_lt_one [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    (ratio2 W e : ℝ) < 1 :=
  (div_lt_one (edge_weight_pos W e)).mpr
    (by linarith [edgeLegHeight_pos W e, two_mul_legHeight_add_chord W e])

private noncomputable def bp1 [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    MetricGraph W :=
  edgePoint (edgeDartOfSym2 e) (ratio1 W e)

private noncomputable def bp2 [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    MetricGraph W :=
  edgePoint (edgeDartOfSym2 e) (ratio2 W e)

/-! ### Three-segment subdivision of `W` -/

open Classical in
/-- The finite set of original vertices together with two interior subdivision points per edge
(splitting every edge into three sub-segments). -/
noncomputable def realizationPoints [Finite V] (W : WeightedGraph V) :
    Finset (MetricGraph W) :=
  let : Fintype V := Fintype.ofFinite V
  let : Fintype W.graph.edgeSet := Fintype.ofFinite _
  Finset.univ.image vertex ∪
    Finset.univ.image (bp1 W) ∪
    Finset.univ.image (bp2 W)

theorem vertex_mem_realizationPoints [Finite V] (W : WeightedGraph V) (v : V) :
    vertex v ∈ realizationPoints W := by
  classical
  simp only [realizationPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl ⟨v, rfl⟩)

private theorem bp1_mem_realizationPoints [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) : bp1 W e ∈ realizationPoints W := by
  classical
  simp only [realizationPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inr ⟨e, rfl⟩)

private theorem bp2_mem_realizationPoints [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) : bp2 W e ∈ realizationPoints W := by
  classical
  simp only [realizationPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨e, rfl⟩

open Classical in
theorem realizationPoints_sdiff_card_le [Finite V] (W : WeightedGraph V) :
    let : Fintype V := Fintype.ofFinite V
    (realizationPoints W \ Finset.univ.image vertex).card ≤
      2 * Nat.card W.graph.edgeSet := by
  intro _
  let : Fintype W.graph.edgeSet := Fintype.ofFinite _
  have hsub : realizationPoints W \ Finset.univ.image vertex ⊆
      Finset.univ.image (bp1 W) ∪ Finset.univ.image (bp2 W) := fun q hq => by
    simp only [Finset.mem_sdiff, realizationPoints, Finset.mem_union] at hq ⊢
    tauto
  have himg : ∀ f : W.graph.edgeSet → MetricGraph W,
      (Finset.univ.image f).card ≤ Nat.card W.graph.edgeSet := fun f => by
    rw [← Fintype.card_eq_nat_card, ← Finset.card_univ]
    exact Finset.card_image_le
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (by linarith [himg (bp1 W), himg (bp2 W)]))

/-- The three-segment subdivision of `W` used for the Euclidean straight-edge realization. -/
noncomputable def realizationSubdivision [Finite V] (W : WeightedGraph V) :
    WeightedGraph { z : MetricGraph W // z ∈ realizationPoints W } :=
  subdivide W (realizationPoints W) (vertex_mem_realizationPoints W)

private theorem edgePoint_interior_ne_vertex (W : WeightedGraph V)
    {r : unitInterval} (hr0 : (0 : ℝ) < r) (hr1 : (r : ℝ) < 1)
    (e : W.graph.edgeSet) (v : V) : edgePoint (edgeDartOfSym2 e) r ≠ vertex v := by
  intro h
  rcases edgePoint_eq_vertex_iff.mp h with ⟨h0, _⟩ | ⟨h1, _⟩
  · exact hr0.ne' (congrArg Subtype.val h0)
  · exact hr1.ne (congrArg Subtype.val h1)

private theorem mem_realizationPoints_on_dart_iff [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) (u : unitInterval) :
    edgePoint (edgeDartOfSym2 e) u ∈ realizationPoints W ↔
      u = 0 ∨ u = ratio1 W e ∨ u = ratio2 W e ∨ u = 1 := by
  constructor
  · intro hu
    classical
    simp only [realizationPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hu
    rcases hu with (⟨v, hv⟩ | ⟨e', he'⟩) | ⟨e', he'⟩
    · rcases edgePoint_eq_vertex_iff.mp hv.symm with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr rfl))
    · obtain ⟨rfl, rfl⟩ := (edgePoint_edgeDartOfSym2_eq_iff_of_mem_Ioo
        (ratio1_pos W e') ((ratio1_lt_ratio2 W e').trans (ratio2_lt_one W e'))).mp he'.symm
      exact Or.inr (Or.inl rfl)
    · obtain ⟨rfl, rfl⟩ := (edgePoint_edgeDartOfSym2_eq_iff_of_mem_Ioo
        ((ratio1_pos W e').trans (ratio1_lt_ratio2 W e')) (ratio2_lt_one W e')).mp he'.symm
      exact Or.inr (Or.inr (Or.inl rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact edgePoint_zero _ ▸ vertex_mem_realizationPoints W _
    · exact bp1_mem_realizationPoints W e
    · exact bp2_mem_realizationPoints W e
    · exact edgePoint_one _ ▸ vertex_mem_realizationPoints W _

/-! ### Euclidean vertex placement and segment characterization -/

open Classical in
/-- Euclidean coordinates assigned to each vertex of `realizationSubdivision W`. -/
noncomputable def realizationVertexPos [Finite V] (W : WeightedGraph V)
    (x : { z : MetricGraph W // z ∈ realizationPoints W }) :
    EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1)) :=
  if hv : ∃ v : V, vertex v = x.val then
    vertexPos W (Classical.choose hv)
  else if h1 : ∃ e : W.graph.edgeSet, bp1 W e = x.val then
    let e := Classical.choose h1
    vertexPos W (edgeDartOfSym2 e).fst +
      (edgeLegHeight W e) • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ)
  else if h2 : ∃ e : W.graph.edgeSet, bp2 W e = x.val then
    let e := Classical.choose h2
    vertexPos W (edgeDartOfSym2 e).snd +
      (edgeLegHeight W e) • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ)
  else 0

private theorem realizationVertexPos_vertex [Finite V] (W : WeightedGraph V)
    {x : { z : MetricGraph W // z ∈ realizationPoints W }} {v : V} (hx : x.val = vertex v) :
    realizationVertexPos W x = vertexPos W v := by
  classical
  have hex : ∃ u : V, (vertex u : MetricGraph W) = x.val := ⟨v, hx.symm⟩
  dsimp only [realizationVertexPos]
  split_ifs
  exact congrArg (vertexPos W) (vertex_injective ((Classical.choose_spec hex).trans hx))

private theorem realizationVertexPos_bp1 [Finite V] (W : WeightedGraph V)
    {x : { z : MetricGraph W // z ∈ realizationPoints W }} {e : W.graph.edgeSet}
    (hx : x.val = bp1 W e) :
    realizationVertexPos W x =
      vertexPos W (edgeDartOfSym2 e).fst +
        (edgeLegHeight W e) • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ) := by
  classical
  obtain ⟨x, hx'⟩ := x
  obtain rfl : x = bp1 W e := hx
  have hnv : ¬ ∃ v : V, vertex v = bp1 W e := fun ⟨v, hv⟩ =>
    edgePoint_interior_ne_vertex W (ratio1_pos W e)
      ((ratio1_lt_ratio2 W e).trans (ratio2_lt_one W e)) e v hv.symm
  have hex : ∃ e' : W.graph.edgeSet, bp1 W e' = bp1 W e := ⟨e, rfl⟩
  dsimp only [realizationVertexPos]
  split_ifs
  have heq : Classical.choose hex = e := ((edgePoint_edgeDartOfSym2_eq_iff_of_mem_Ioo
    (ratio1_pos W e) ((ratio1_lt_ratio2 W e).trans (ratio2_lt_one W e))).mp
    (Classical.choose_spec hex)).1
  rw [heq]

private theorem realizationVertexPos_bp2 [Finite V] (W : WeightedGraph V)
    {x : { z : MetricGraph W // z ∈ realizationPoints W }} {e : W.graph.edgeSet}
    (hx : x.val = bp2 W e) :
    realizationVertexPos W x =
      vertexPos W (edgeDartOfSym2 e).snd +
        (edgeLegHeight W e) • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ) := by
  classical
  obtain ⟨x, hx'⟩ := x
  obtain rfl : x = bp2 W e := hx
  have hr2_pos : (0 : ℝ) < ratio2 W e := (ratio1_pos W e).trans (ratio1_lt_ratio2 W e)
  have hnv : ¬ ∃ v : V, vertex v = bp2 W e := fun ⟨v, hv⟩ =>
    edgePoint_interior_ne_vertex W hr2_pos (ratio2_lt_one W e) e v hv.symm
  have hn1 : ¬ ∃ e' : W.graph.edgeSet, bp1 W e' = bp2 W e := fun ⟨e', he'⟩ => by
    obtain ⟨rfl, hr⟩ := (edgePoint_edgeDartOfSym2_eq_iff_of_mem_Ioo
      hr2_pos (ratio2_lt_one W e)).mp he'
    exact (ratio1_lt_ratio2 W e').ne (congrArg Subtype.val hr)
  have hex : ∃ e' : W.graph.edgeSet, bp2 W e' = bp2 W e := ⟨e, rfl⟩
  dsimp only [realizationVertexPos]
  split_ifs
  have heq : Classical.choose hex = e := ((edgePoint_edgeDartOfSym2_eq_iff_of_mem_Ioo
    hr2_pos (ratio2_lt_one W e)).mp (Classical.choose_spec hex)).1
  rw [heq]

private def ForwardSubDart [Finite V] (W : WeightedGraph V)
    (a b : MetricGraph W) (w : ℝ) : Prop :=
  ∃ e : W.graph.edgeSet,
    (a = vertex (edgeDartOfSym2 e).fst ∧ b = bp1 W e ∧ w = edgeLegHeight W e) ∨
    (a = bp1 W e ∧ b = bp2 W e ∧ w = edgeChordDist W e) ∨
    (a = bp2 W e ∧ b = vertex (edgeDartOfSym2 e).snd ∧ w = edgeLegHeight W e)

private theorem forwardSubDart_of_edgePoint [Finite V] (W : WeightedGraph V)
    {e : W.graph.edgeSet} {s t : unitInterval} {a b : MetricGraph W}
    (hst : (s : ℝ) < t)
    (hs : edgePoint (edgeDartOfSym2 e) s = a) (ha : a ∈ realizationPoints W)
    (ht : edgePoint (edgeDartOfSym2 e) t = b) (hb : b ∈ realizationPoints W)
    (hno : ∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < t →
      edgePoint (edgeDartOfSym2 e) r ∉ realizationPoints W) :
    ForwardSubDart W a b (((t : ℝ) - s) * W.weight e.val) := by
  have hr1 := ratio1_pos W e
  have hr12 := ratio1_lt_ratio2 W e
  have hr2 := ratio2_lt_one W e
  have hmem_s := (mem_realizationPoints_on_dart_iff W e s).mp (hs.symm ▸ ha)
  have hmem_t := (mem_realizationPoints_on_dart_iff W e t).mp (ht.symm ▸ hb)
  have hmul : (ratio1 W e : ℝ) * W.weight e.val = edgeLegHeight W e ∧
      (ratio2 W e : ℝ) * W.weight e.val = edgeLegHeight W e + edgeChordDist W e :=
    ⟨ratio1_mul_weight W e, ratio2_mul_weight W e⟩
  -- The pairs with `t ≤ s` contradict `hst`, and those skipping a subdivision point contradict
  -- `hno`; the three consecutive pairs are the three sub-segments.
  rcases hmem_s with rfl | rfl | rfl | rfl <;> rcases hmem_t with rfl | rfl | rfl | rfl <;>
    (try simp only [Set.Icc.coe_zero, Set.Icc.coe_one] at hst hno ⊢) <;> try linarith
  · exact ⟨e, Or.inl ⟨hs.symm.trans (edgePoint_zero _), ht.symm, by linarith [hmul.1]⟩⟩
  · exact absurd (bp1_mem_realizationPoints W e) (hno (ratio1 W e) hr1 hr12)
  · exact absurd (bp1_mem_realizationPoints W e) (hno (ratio1 W e) hr1 (hr12.trans hr2))
  · exact ⟨e, Or.inr (Or.inl ⟨hs.symm, ht.symm, by linarith [hmul.1, hmul.2]⟩)⟩
  · exact absurd (bp2_mem_realizationPoints W e) (hno (ratio2 W e) hr12 hr2)
  · exact ⟨e, Or.inr (Or.inr ⟨hs.symm, ht.symm.trans (edgePoint_one _),
      by linarith [hmul.2, two_mul_legHeight_add_chord W e]⟩)⟩

private theorem classify_subDart [Finite V] (W : WeightedGraph V)
    (d' : (realizationSubdivision W).graph.Dart) :
    ForwardSubDart W d'.fst.val d'.snd.val ((realizationSubdivision W).weight d'.edge) ∨
    ForwardSubDart W d'.snd.val d'.fst.val ((realizationSubdivision W).weight d'.edge) := by
  obtain ⟨d, s, t, hst, hs, ht, hno, hw_eq, _⟩ :=
    subdivideEquiv_edgePoint (vertex_mem_realizationPoints W) d' 0
  let e : W.graph.edgeSet := ⟨d.edge, d.edge_mem⟩
  rcases (dart_edge_eq_iff d (edgeDartOfSym2 e)).mp (edgeDartOfSym2_edge e).symm with h | h
  · rw [show (realizationSubdivision W).weight d'.edge = ((t : ℝ) - s) * W.weight e.val from hw_eq]
    exact Or.inl (forwardSubDart_of_edgePoint W hst (h ▸ hs) d'.fst.property
      (h ▸ ht) d'.snd.property
      fun r h1 h2 => h ▸ hno r h1 h2)
  · have hw_symm : (realizationSubdivision W).weight d'.edge =
        ((unitInterval.symm s : ℝ) - unitInterval.symm t) * W.weight e.val := by
      rwa [unitInterval.coe_symm_eq, unitInterval.coe_symm_eq, sub_sub_sub_cancel_left]
    rw [hw_symm]
    refine Or.inr (forwardSubDart_of_edgePoint W
      (by simp only [unitInterval.coe_symm_eq]; linarith)
      ((edgePoint_symm' _ _).trans (h ▸ ht)) d'.snd.property
      ((edgePoint_symm' _ _).trans (h ▸ hs)) d'.fst.property fun r h1 h2 => ?_)
    simp only [unitInterval.coe_symm_eq] at h1 h2
    have hr := hno (unitInterval.symm r)
      (by simp only [unitInterval.coe_symm_eq]; linarith)
      (by simp only [unitInterval.coe_symm_eq]; linarith)
    rwa [h, edgePoint_symm] at hr

/-! ### Straight-edge realization map -/

/-- The straight-edge Euclidean map on `MetricGraph (realizationSubdivision W)` sending every
subdivided vertex to `realizationVertexPos W` and every subdivided edge onto a straight line
segment. -/
noncomputable def realizationMap [Finite V] (W : WeightedGraph V) :
    MetricGraph (realizationSubdivision W) →
      EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1)) :=
  lift (realizationVertexPos W)
    (fun d' r => (1 - (r : ℝ)) • realizationVertexPos W d'.fst +
      (r : ℝ) • realizationVertexPos W d'.snd)
    (fun d' => by rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, one_smul,
      zero_smul, add_zero])
    (fun d' => by rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self, zero_smul,
      zero_add, one_smul])
    (fun d' r => by
      change (1 - (1 - (r : ℝ))) • realizationVertexPos W d'.snd +
          (1 - (r : ℝ)) • realizationVertexPos W d'.fst = _
      rw [sub_sub_cancel]
      exact add_comm _ _)

@[simp]
theorem realizationMap_vertex [Finite V] (W : WeightedGraph V)
    (x : { z : MetricGraph W // z ∈ realizationPoints W }) :
    realizationMap W (vertex x) = realizationVertexPos W x :=
  lift_vertex _ _ _ _ _ x

theorem realizationMap_edgePoint [Finite V] (W : WeightedGraph V)
    (d' : (realizationSubdivision W).graph.Dart) (r : unitInterval) :
    realizationMap W (edgePoint d' r) =
      (1 - (r : ℝ)) • realizationMap W (vertex d'.fst) +
        (r : ℝ) • realizationMap W (vertex d'.snd) := by
  simp only [realizationMap, lift_vertex, lift_edgePoint]

theorem realizationMap_edge_dist [Finite V] (W : WeightedGraph V)
    (d' : (realizationSubdivision W).graph.Dart) :
    dist (realizationMap W (vertex d'.fst)) (realizationMap W (vertex d'.snd)) =
      (realizationSubdivision W).weight d'.edge := by
  have hleg : ∀ (x : EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1)))
      (e : W.graph.edgeSet),
      dist x (x + edgeLegHeight W e •
        EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ)) = edgeLegHeight W e := by
    intro x e
    rw [dist_self_add_right, norm_smul, Real.norm_of_nonneg (edgeLegHeight_pos W e).le,
      PiLp.norm_single, norm_one, mul_one]
  have hfwd : ∀ (a b : { z // z ∈ realizationPoints W }) {w : ℝ},
      ForwardSubDart W a.val b.val w →
        dist (realizationVertexPos W a) (realizationVertexPos W b) = w := by
    rintro a b w ⟨e, ⟨ha, hb, rfl⟩ | ⟨ha, hb, rfl⟩ | ⟨ha, hb, rfl⟩⟩
    · rw [realizationVertexPos_vertex W ha, realizationVertexPos_bp1 W hb]
      exact hleg _ e
    · rw [realizationVertexPos_bp1 W ha, realizationVertexPos_bp2 W hb, dist_add_right]
      rfl
    · rw [realizationVertexPos_bp2 W ha, realizationVertexPos_vertex W hb, dist_comm]
      exact hleg _ e
  rw [realizationMap_vertex, realizationMap_vertex]
  rcases classify_subDart W d' with h | h
  · exact hfwd _ _ h
  · exact (dist_comm _ _).trans (hfwd _ _ h)

theorem realizationMap_edgePoint_dist [Finite V] (W : WeightedGraph V)
    (d' : (realizationSubdivision W).graph.Dart) (r₁ r₂ : unitInterval) :
    dist (realizationMap W (edgePoint d' r₁)) (realizationMap W (edgePoint d' r₂)) =
      |(r₁ : ℝ) - r₂| * (realizationSubdivision W).weight d'.edge := by
  rw [realizationMap_edgePoint, realizationMap_edgePoint, ← AffineMap.lineMap_apply_module,
    ← AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module',
    AffineMap.lineMap_apply_module', dist_add_right, dist_eq_norm, ← sub_smul, norm_smul,
    Real.norm_eq_abs, ← dist_eq_norm', realizationMap_edge_dist]

theorem realizationMap_dist_le [Finite V] (W : WeightedGraph V)
    (p q : MetricGraph (realizationSubdivision W)) :
    dist (realizationMap W p) (realizationMap W q) ≤ dist p q :=
  dist_map_le_of_edgePoint_dist_le (realizationMap W)
    (fun d' r₁ r₂ => (realizationMap_edgePoint_dist W d' r₁ r₂).le) p q

theorem continuous_realizationMap [Finite V] (W : WeightedGraph V) :
    Continuous (realizationMap W) :=
  Metric.continuous_iff.mpr fun x ε hε =>
    ⟨ε, hε, fun {y} hy => (realizationMap_dist_le W y x).trans_lt hy⟩

/-! ### Injectivity, closed embedding, induced weighted graph, and rationality -/

private def OnEdgeTent [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) (u : unitInterval)
    (z : EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1))) : Prop :=
  let v₀ := vertexPos W (edgeDartOfSym2 e).fst
  let v₁ := vertexPos W (edgeDartOfSym2 e).snd
  let dir := EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ)
  let h := edgeLegHeight W e
  let w := W.weight e.val
  let τ := ((u : ℝ) * w - h) / edgeChordDist W e
  z = v₀ + ((u : ℝ) * w) • dir ∨
  z = ((1 - τ) • v₀ + τ • v₁) + h • dir ∨
  z = v₁ + ((1 - (u : ℝ)) * w) • dir

private theorem onEdgeTent_apply_succ_ne [Finite V] (W : WeightedGraph V)
    {e : W.graph.edgeSet} {u : unitInterval}
    {z : EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1))}
    (hz : OnEdgeTent W e u z) {k : Fin (Nat.card W.graph.edgeSet)} (hk : k ≠ edgeEquiv W e) :
    z k.succ = 0 := by
  have hne : k.succ ≠ (edgeEquiv W e).succ := Fin.succ_injective _ |>.ne hk
  rcases hz with rfl | rfl | rfl <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, vertexPos_apply_succ,
      PiLp.single_eq_of_ne 2 hne, mul_zero, add_zero]

private theorem onEdgeTent_apply_succ_pos [Finite V] (W : WeightedGraph V)
    {e : W.graph.edgeSet} {u : unitInterval} (hu0 : (0 : ℝ) < u) (hu1 : (u : ℝ) < 1)
    {z : EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1))} (hz : OnEdgeTent W e u z) :
    0 < z (Fin.succ (edgeEquiv W e)) := by
  rcases hz with rfl | rfl | rfl <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, vertexPos_apply_succ,
      PiLp.single_eq_same, mul_zero, mul_one, zero_add]
  · exact mul_pos hu0 (edge_weight_pos W e)
  · exact edgeLegHeight_pos W e
  · exact mul_pos (sub_pos.mpr hu1) (edge_weight_pos W e)

private theorem onEdgeTent_injective [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet)
    {u₁ u₂ : unitInterval} {z : EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1))}
    (h₁ : OnEdgeTent W e u₁ z) (h₂ : OnEdgeTent W e u₂ z) : u₁ = u₂ := by
  have hd := (edgeChordDist_pos W e).ne'
  have hsum := two_mul_legHeight_add_chord W e
  have hne01 := vertexPos_apply_zero_ne W (edgeDartOfSym2 e).fst_ne_snd
  let x₀ := vertexPos W (edgeDartOfSym2 e).fst 0
  let x₁ := vertexPos W (edgeDartOfSym2 e).snd 0
  let τ : unitInterval → ℝ := fun u =>
    ((u : ℝ) * W.weight e.val - edgeLegHeight W e) / edgeChordDist W e
  have haff : ∀ {α β : ℝ}, (1 - α) * x₀ + α * x₁ = (1 - β) * x₀ + β * x₁ → α = β :=
    fun {α β} h => sub_eq_zero.mp ((mul_eq_zero.mp
      (by linarith : (α - β) * (x₁ - x₀) = 0)).resolve_right (sub_ne_zero.mpr hne01.symm))
  have hcoord : ∀ {u}, OnEdgeTent W e u z →
      (z 0 = (1 - 0) * x₀ + 0 * x₁ ∧ z (edgeEquiv W e).succ = (u : ℝ) * W.weight e.val) ∨
      (z 0 = (1 - τ u) * x₀ + τ u * x₁ ∧ z (edgeEquiv W e).succ = edgeLegHeight W e) ∨
      (z 0 = (1 - 1) * x₀ + 1 * x₁ ∧ z (edgeEquiv W e).succ = (1 - (u : ℝ)) * W.weight e.val) := by
    intro u hu
    rcases hu with rfl | rfl | rfl <;>
      [left; (right; left); (right; right)] <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, vertexPos_apply_succ,
        PiLp.single_eq_of_ne 2 (Fin.succ_ne_zero _).symm, PiLp.single_eq_same,
        mul_zero, zero_mul, mul_one, one_mul, zero_add, add_zero, sub_zero, sub_self,
        and_self, x₀, x₁, τ]
  apply Subtype.ext
  apply mul_right_cancel₀ (edge_weight_pos W e).ne'
  -- In each of the nine cases, the first coordinates pin down the affine parameters and the
  -- edge coordinates then determine `u * w`, linearly once `τ` is cleared.
  rcases hcoord h₁ with ⟨h01, hy1⟩ | ⟨h01, hy1⟩ | ⟨h01, hy1⟩ <;>
    rcases hcoord h₂ with ⟨h02, hy2⟩ | ⟨h02, hy2⟩ | ⟨h02, hy2⟩ <;>
    have hα := haff (h01.symm.trans h02) <;>
    (try simp only [τ, eq_div_iff hd, div_eq_iff hd, div_mul_cancel₀ _ hd, zero_mul, one_mul]
      at hα) <;>
    linarith

private def RealizationClassified [Finite V] (W : WeightedGraph V)
    (p : MetricGraph (realizationSubdivision W)) : Prop :=
  let q := subdivideEquiv (vertex_mem_realizationPoints W) p
  (∃ v : V, q = vertex v ∧ realizationMap W p = vertexPos W v) ∨
  (∃ (e : W.graph.edgeSet) (u : unitInterval), (0 : ℝ) < u ∧ (u : ℝ) < 1 ∧
    q = edgePoint (edgeDartOfSym2 e) u ∧ OnEdgeTent W e u (realizationMap W p))

private theorem realizationMap_classify_vertex [Finite V] (W : WeightedGraph V)
    (x : { z : MetricGraph W // z ∈ realizationPoints W }) :
    RealizationClassified W (vertex x) := by
  classical
  have hx := x.property
  simp only [realizationPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and] at hx
  rcases hx with (⟨v, hv⟩ | ⟨e, he⟩) | ⟨e, he⟩
  · exact Or.inl ⟨v, (subdivideEquiv_vertex _ _).trans hv.symm,
      (realizationMap_vertex W _).trans (realizationVertexPos_vertex W hv.symm)⟩
  · refine Or.inr ⟨e, ratio1 W e, ratio1_pos W e,
      (ratio1_lt_ratio2 W e).trans (ratio2_lt_one W e), (subdivideEquiv_vertex _ _).trans he.symm,
      Or.inl ?_⟩
    rw [realizationMap_vertex, realizationVertexPos_bp1 W he.symm, ratio1_mul_weight]
  · refine Or.inr ⟨e, ratio2 W e, (ratio1_pos W e).trans (ratio1_lt_ratio2 W e),
      ratio2_lt_one W e, (subdivideEquiv_vertex _ _).trans he.symm, Or.inr (Or.inr ?_)⟩
    rw [realizationMap_vertex, realizationVertexPos_bp2 W he.symm]
    congr 2
    linarith [ratio2_mul_weight W e, two_mul_legHeight_add_chord W e]

private theorem realizationMap_classify [Finite V] (W : WeightedGraph V)
    (p : MetricGraph (realizationSubdivision W)) :
    RealizationClassified W p := by
  induction p using ind with
  | vertex x => exact realizationMap_classify_vertex W x
  | edgePoint d' r hr_pos hr_lt =>
    wlog hfwd : ForwardSubDart W d'.fst.val d'.snd.val ((realizationSubdivision W).weight d'.edge)
      generalizing d' r
    · rw [← edgePoint_symm d' r]
      exact this d'.symm (unitInterval.symm r)
        (by rw [unitInterval.coe_symm_eq]; linarith)
        (by rw [unitInterval.coe_symm_eq]; linarith)
        (by rw [Dart.edge_symm]; exact (classify_subDart W d').resolve_left hfwd)
    obtain ⟨d, s, t, hst, hs, ht, _, _, heq⟩ :=
      subdivideEquiv_edgePoint (vertex_mem_realizationPoints W) d' r
    -- Each forward sub-segment `[s₀, t₀]` of an original edge `e` lands on the matching piece of
    -- the tent over `e`, at the parameter `(1 - r) * s₀ + r * t₀`.
    have key : ∀ {e : W.graph.edgeSet} {s₀ t₀ : unitInterval},
        edgePoint (edgeDartOfSym2 e) s₀ = d'.fst.val →
        edgePoint (edgeDartOfSym2 e) t₀ = d'.snd.val →
        (s₀ : ℝ) < t₀ → (∀ u : unitInterval, (u : ℝ) = (1 - r) * s₀ + r * t₀ →
          OnEdgeTent W e u (realizationMap W (edgePoint d' r))) →
        RealizationClassified W (edgePoint d' r) := by
      intro e s₀ t₀ hs₀ ht₀ hst₀ htent
      obtain ⟨rfl, rfl, rfl⟩ :=
        subAdj_witness_eq hst hst₀ (hs.trans hs₀.symm) (ht.trans ht₀.symm)
      refine Or.inr ⟨_, _, ?_, ?_, heq, htent _ rfl⟩ <;> dsimp only <;>
        nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]
    have hz := realizationMap_edgePoint W d' r
    simp only [realizationMap_vertex] at hz
    rcases hfwd with ⟨e, ⟨ha, hb, _⟩ | ⟨ha, hb, _⟩ | ⟨ha, hb, _⟩⟩
    · refine key ((edgePoint_zero _).trans ha.symm) hb.symm (ratio1_pos W e)
        fun u hu => Or.inl ?_
      rw [realizationVertexPos_vertex W ha, realizationVertexPos_bp1 W hb] at hz
      rw [hz, hu, Set.Icc.coe_zero, mul_zero, zero_add, mul_assoc, ratio1_mul_weight]
      module
    · refine key ha.symm hb.symm (ratio1_lt_ratio2 W e) fun u hu => Or.inr (Or.inl ?_)
      rw [realizationVertexPos_bp1 W ha, realizationVertexPos_bp2 W hb] at hz
      have hnum : (u : ℝ) * W.weight e.val - edgeLegHeight W e = (r : ℝ) * edgeChordDist W e := by
        rw [hu]
        linear_combination (1 - (r : ℝ)) * ratio1_mul_weight W e + (r : ℝ) * ratio2_mul_weight W e
      rw [hz, hnum, mul_div_cancel_right₀ _ (edgeChordDist_pos W e).ne']
      module
    · refine key ha.symm ((edgePoint_one _).trans hb.symm) (ratio2_lt_one W e)
        fun u hu => Or.inr (Or.inr ?_)
      rw [realizationVertexPos_bp2 W ha, realizationVertexPos_vertex W hb] at hz
      have hmul : (1 - (u : ℝ)) * W.weight e.val = (1 - (r : ℝ)) * edgeLegHeight W e := by
        rw [hu, Set.Icc.coe_one]
        linear_combination -(1 - (r : ℝ)) * ratio2_mul_weight W e -
          (1 - (r : ℝ)) * two_mul_legHeight_add_chord W e
      rw [hz, hmul]
      module

theorem realizationMap_injective [Finite V] (W : WeightedGraph V) :
    Function.Injective (realizationMap W) := by
  intro p₁ p₂ hp
  have hvi : ∀ (v : V) (e : W.graph.edgeSet) (u : unitInterval),
      (0 : ℝ) < u → (u : ℝ) < 1 → OnEdgeTent W e u (vertexPos W v) → False := fun v e u h0 h1 ht =>
    (onEdgeTent_apply_succ_pos W h0 h1 ht).ne' (vertexPos_apply_succ W v _)
  apply (subdivideEquiv (vertex_mem_realizationPoints W)).injective
  rcases realizationMap_classify W p₁ with
    ⟨v₁, hq₁, hz₁⟩ | ⟨e₁, u₁, hu₁0, hu₁1, hq₁, ht₁⟩ <;>
    rcases realizationMap_classify W p₂ with
      ⟨v₂, hq₂, hz₂⟩ | ⟨e₂, u₂, hu₂0, hu₂1, hq₂, ht₂⟩
  · have h : vertexPos W v₁ 0 = vertexPos W v₂ 0 := congrArg (· 0) (hz₁.symm.trans (hp.trans hz₂))
    rw [hq₁, hq₂]
    by_contra hne
    exact vertexPos_apply_zero_ne W (fun hv => hne (congrArg vertex hv)) h
  · exact (hvi v₁ e₂ u₂ hu₂0 hu₂1 ((hz₁.symm.trans hp) ▸ ht₂)).elim
  · exact (hvi v₂ e₁ u₁ hu₁0 hu₁1 ((hz₂.symm.trans hp.symm) ▸ ht₁)).elim
  · have he : e₁ = e₂ := by
      by_contra hne
      have hzero := onEdgeTent_apply_succ_ne W ht₂ ((edgeEquiv W).injective.ne hne)
      exact (onEdgeTent_apply_succ_pos W hu₁0 hu₁1 ht₁).ne'
        ((congrArg (· (edgeEquiv W e₁).succ) hp).trans hzero)
    subst he
    rw [hq₁, hq₂, onEdgeTent_injective W e₁ ht₁ (hp ▸ ht₂)]

theorem realizationMap_isClosedEmbedding [Finite V] (W : WeightedGraph V) :
    Topology.IsClosedEmbedding (realizationMap W) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_realizationMap W) (realizationMap_injective W)
    fun _ hs => (hs.isCompact.image (continuous_realizationMap W)).isClosed

/-- The straight-edge Euclidean map on the original metric graph `MetricGraph W`, obtained by
precomposing `realizationMap W` with `(subdivideEquiv (vertex_mem_realizationPoints W)).symm`. -/
noncomputable def realizationFromGraph [Finite V] (W : WeightedGraph V) :
    MetricGraph W → EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1)) :=
  fun x => realizationMap W ((subdivideEquiv (vertex_mem_realizationPoints W)).symm x)

theorem realizationFromGraph_dist_le [Finite V] (W : WeightedGraph V) (x y : MetricGraph W) :
    dist (realizationFromGraph W x) (realizationFromGraph W y) ≤ dist x y :=
  (realizationMap_dist_le W _ _).trans_eq
    ((subdivideEquiv (vertex_mem_realizationPoints W)).symm.isometry.dist_eq x y)

theorem continuous_realizationFromGraph [Finite V] (W : WeightedGraph V) :
    Continuous (realizationFromGraph W) :=
  Metric.continuous_iff.mpr fun x ε hε =>
    ⟨ε, hε, fun {y} hy => (realizationFromGraph_dist_le W y x).trans_lt hy⟩

theorem realizationFromGraph_injective [Finite V] (W : WeightedGraph V) :
    Function.Injective (realizationFromGraph W) :=
  (realizationMap_injective W).comp
    (subdivideEquiv (vertex_mem_realizationPoints W)).symm.injective

theorem realizationFromGraph_isClosedEmbedding [Finite V] (W : WeightedGraph V) :
    Topology.IsClosedEmbedding (realizationFromGraph W) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_realizationFromGraph W) (realizationFromGraph_injective W)
    fun _ hs => (hs.isCompact.image (continuous_realizationFromGraph W)).isClosed

/-- The weighted graph induced by the Euclidean chord lengths of `realizationMap W` on the
subdivided vertex set `realizationPoints W`. -/
noncomputable def realizationEuclideanGraph [Finite V] (W : WeightedGraph V) :
    WeightedGraph { z : MetricGraph W // z ∈ realizationPoints W } where
  graph := (realizationSubdivision W).graph
  weight := Sym2.lift ⟨fun x y => dist (realizationMap W (vertex x)) (realizationMap W (vertex y)),
    fun _ _ => dist_comm _ _⟩
  weight_pos {x y} hadj := by
    let d' : (realizationSubdivision W).graph.Dart := ⟨(x, y), hadj⟩
    change 0 < dist (realizationMap W (vertex d'.fst)) (realizationMap W (vertex d'.snd))
    rw [realizationMap_edge_dist]
    exact (realizationSubdivision W).dart_weight_pos d'
  connected := (realizationSubdivision W).connected

theorem realizationEuclideanGraph_weight_eq [Finite V] (W : WeightedGraph V)
    {e : Sym2 { z : MetricGraph W // z ∈ realizationPoints W }}
    (he : e ∈ (realizationSubdivision W).graph.edgeSet) :
    (realizationEuclideanGraph W).weight e = (realizationSubdivision W).weight e := by
  let d' : (realizationEuclideanGraph W).graph.Dart := edgeDartOfSym2 ⟨e, he⟩
  have heq : d'.edge = e := edgeDartOfSym2_edge ⟨e, he⟩
  rw [← heq]
  exact realizationMap_edge_dist W d'

private noncomputable def realizationSubEquiv [Finite V] (W : WeightedGraph V) :
    MetricGraph (realizationEuclideanGraph W) ≃ᵢ MetricGraph (realizationSubdivision W) := by
  let f : MetricGraph (realizationEuclideanGraph W) → MetricGraph (realizationSubdivision W) :=
    lift (vertex (W := realizationSubdivision W))
      (fun d r => edgePoint (W := realizationSubdivision W) d r)
      (fun d => edgePoint_zero (W := realizationSubdivision W) d)
      (fun d => edgePoint_one (W := realizationSubdivision W) d)
      (fun d r => edgePoint_symm (W := realizationSubdivision W) d r)
  let g : MetricGraph (realizationSubdivision W) → MetricGraph (realizationEuclideanGraph W) :=
    lift (vertex (W := realizationEuclideanGraph W))
      (fun d r => edgePoint (W := realizationEuclideanGraph W) d r)
      (fun d => edgePoint_zero (W := realizationEuclideanGraph W) d)
      (fun d => edgePoint_one (W := realizationEuclideanGraph W) d)
      (fun d r => edgePoint_symm (W := realizationEuclideanGraph W) d r)
  have hf_v : ∀ v, f (vertex v) = vertex v := lift_vertex _ _ _ _ _
  have hf_e : ∀ (d : (realizationEuclideanGraph W).graph.Dart) r,
      f (edgePoint d r) = edgePoint (W := realizationSubdivision W) ⟨d.toProd, d.adj⟩ r :=
    lift_edgePoint _ _ _ _ _
  have hg_v : ∀ v, g (vertex v) = vertex v := lift_vertex _ _ _ _ _
  have hg_e : ∀ (d : (realizationSubdivision W).graph.Dart) r,
      g (edgePoint d r) = edgePoint (W := realizationEuclideanGraph W) ⟨d.toProd, d.adj⟩ r :=
    lift_edgePoint _ _ _ _ _
  have hfg : Function.RightInverse g f := fun x => by
    induction x using ind_simple with
    | vertex v => rw [hg_v, hf_v]
    | edgePoint d r => rw [hg_e, hf_e]
  have hgf : Function.LeftInverse g f := fun x => by
    induction x using ind_simple with
    | vertex v => rw [hf_v, hg_v]
    | edgePoint d r => rw [hf_e, hg_e]
  have hf_le : ∀ x y, dist (f x) (f y) ≤ dist x y :=
    dist_map_le_of_edgePoint_dist_le f fun d s t => by
      rw [hf_e, hf_e]
      refine (dist_edgePoint_self_le (W := realizationSubdivision W)
        ⟨d.toProd, d.adj⟩ s t).trans_eq ?_
      rw [mul_comm, realizationEuclideanGraph_weight_eq W d.edge_mem]
      rfl
  have hg_le : ∀ x y, dist (g x) (g y) ≤ dist x y :=
    dist_map_le_of_edgePoint_dist_le g fun d s t => by
      rw [hg_e, hg_e]
      refine (dist_edgePoint_self_le (W := realizationEuclideanGraph W)
        ⟨d.toProd, d.adj⟩ s t).trans_eq ?_
      rw [mul_comm,
        show (⟨d.toProd, d.adj⟩ : (realizationEuclideanGraph W).graph.Dart).edge = d.edge from
        rfl, realizationEuclideanGraph_weight_eq W d.edge_mem]
  exact IsometryEquiv.mk ⟨f, g, hgf, hfg⟩ (Isometry.of_dist_eq fun x y =>
    le_antisymm (hf_le x y) (by simpa only [hgf x, hgf y] using hg_le (f x) (f y)))

/-- The metric graph of the Euclidean chord-weighted subdivision is globally isometric to the
original metric graph `MetricGraph W`. -/
noncomputable def realizationEuclideanEquiv [Finite V] (W : WeightedGraph V) :
    MetricGraph (realizationEuclideanGraph W) ≃ᵢ MetricGraph W :=
  (realizationSubEquiv W).trans (subdivideEquiv (vertex_mem_realizationPoints W))

theorem realizationMap_vertex_rational [Finite V] (W : WeightedGraph V)
    (hQ : ∀ e ∈ W.graph.edgeSet, ∃ q : ℚ, W.weight e = q)
    (x : { z : MetricGraph W // z ∈ realizationPoints W })
    (i : Fin (Nat.card W.graph.edgeSet + 1)) :
    ∃ q : ℚ, realizationMap W (vertex x) i = q := by
  classical
  have hvp_rat : ∀ v : V, ∃ q : ℚ, vertexPos W v i = q := fun v => by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · obtain ⟨q, hq⟩ := vertexSpacing_rational W hQ
      exact ⟨q * (vertexEquiv v : ℕ), by rw [vertexPos_apply_zero, hq]; push_cast; rfl⟩
    · exact ⟨0, by rw [vertexPos_apply_succ, Rat.cast_zero]⟩
  have hh_rat : ∀ e : W.graph.edgeSet, ∃ q : ℚ, edgeLegHeight W e = q := fun e => by
    obtain ⟨qw, hqw⟩ := hQ e.val e.property
    obtain ⟨qs, hqs⟩ := vertexSpacing_rational W hQ
    refine ⟨(qw - qs * |((vertexEquiv (edgeDartOfSym2 e).fst : ℕ) : ℚ) -
      (vertexEquiv (edgeDartOfSym2 e).snd : ℕ)|) / 2, ?_⟩
    rw [edgeLegHeight, edgeChordDist, dist_vertexPos_eq, hqw, hqs]
    push_cast
    rfl
  have h_bp_rat : ∀ (v : V) (e : W.graph.edgeSet) (y : { z // z ∈ realizationPoints W }),
      realizationVertexPos W y =
        vertexPos W v +
          edgeLegHeight W e • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ) →
      ∃ q : ℚ, realizationMap W (vertex y) i = q := fun v e y hy => by
    obtain ⟨q1, hq1⟩ := hvp_rat v
    obtain ⟨qh, hqh⟩ := hh_rat e
    rw [realizationMap_vertex, hy, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    by_cases hi : i = Fin.succ (edgeEquiv W e)
    · subst hi
      exact ⟨q1 + qh, by rw [PiLp.single_eq_same, mul_one, hq1, hqh, Rat.cast_add]⟩
    · exact ⟨q1, by rw [PiLp.single_eq_of_ne 2 hi, mul_zero, add_zero, hq1]⟩
  have hx := x.property
  simp only [realizationPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and] at hx
  rcases hx with (⟨v, hv⟩ | ⟨e, he⟩) | ⟨e, he⟩
  · rw [realizationMap_vertex, realizationVertexPos_vertex W hv.symm]
    exact hvp_rat v
  · exact h_bp_rat (edgeDartOfSym2 e).fst e _ (realizationVertexPos_bp1 W he.symm)
  · exact h_bp_rat (edgeDartOfSym2 e).snd e _ (realizationVertexPos_bp2 W he.symm)

end MetricGraph

end SimpleGraph
