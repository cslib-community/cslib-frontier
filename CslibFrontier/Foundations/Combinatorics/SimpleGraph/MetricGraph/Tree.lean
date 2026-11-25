/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/Tree.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Geodesic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Maps
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.NearVertex
import Mathlib.Tactic.Linarith

/-!
# Tree metric graphs

When `W.graph.IsTree`, the continuous metric graph `MetricGraph W` is a metric tree (an `ℝ`-tree):
geodesics are uniquely determined, every metric interval `interval x y` is isometric to
`Set.Icc 0 (Dist.dist x y)`, every triple `x, y, z` has a unique metric median `treeMedian x y z`,
and branches at any base point `p` partition `{ q | q ≠ p }`.

## Main definitions

* `SimpleGraph.MetricGraph.edgeProj`: the `1`-Lipschitz projection of `MetricGraph W` onto the
  segment `[0, W.weight d.edge]` along a bridge dart `d`.
* `SimpleGraph.MetricGraph.treeMedian`: the unique point in
  `interval x y ∩ interval y z ∩ interval z x` for a tree metric graph.
* `SimpleGraph.MetricGraph.branch`: the branch `{ w | p ∉ interval q w }` of `MetricGraph W`
  pointing from `p` toward `q`.

## Main results

* `SimpleGraph.MetricGraph.vertexDist_adj`: adjacent vertices in a tree have `vertexDist` equal
  to their edge weight.
* `SimpleGraph.MetricGraph.eq_of_mem_interval_dist_eq`,
  `SimpleGraph.MetricGraph.IsGeodesic.eq_on`: uniqueness of shortest paths and geodesics in tree
  metric graphs.
* `SimpleGraph.MetricGraph.exists_treeMedian`, `SimpleGraph.MetricGraph.eq_treeMedian_of_mem`,
  `SimpleGraph.MetricGraph.dist_add_dist_eq_treeMedian`: existence, uniqueness, and shortest-path
  projection property of `treeMedian`.
* `SimpleGraph.MetricGraph.exists_isometry_interval`,
  `SimpleGraph.MetricGraph.interval_subset_union`: intervals are isometric to real segments, and
  `interval x z ⊆ interval x y ∪ interval y z`.
* `SimpleGraph.MetricGraph.mem_branch_iff_of_mem_interval`,
  `SimpleGraph.MetricGraph.mem_branch_vertex_iff_edgeProj_pos`: branch membership through a point
  between `z` and the base points, and branches at a vertex through bridge projections.
* `SimpleGraph.MetricGraph.branch_eq_of_mem`,
  `SimpleGraph.MetricGraph.branch_disjoint_of_mem_interval`,
  `SimpleGraph.MetricGraph.exists_stem_segment`: branch equivalence and unbranched stem geometry
  needed for strategyproof facility location on trees.
-/

public section

open scoped unitInterval

namespace SimpleGraph

namespace MetricGraph

universe u

variable {V : Type u} {W : WeightedGraph V}

/-! ### Bridge projections in tree metric graphs -/

section TreeProjection

private lemma bridge_deleteEdges (hT : W.graph.IsTree) (d : W.graph.Dart) :
    ¬ (W.graph.deleteEdges {d.edge}).Reachable d.fst d.snd := by
  have hb : W.graph.IsBridge d.edge :=
    isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic d.adj
  change ¬ (W.graph.deleteEdges {s(d.fst, d.snd)}).Reachable d.fst d.snd
  exact isBridge_iff.mp hb

private lemma walk_reachable_deleteEdges_or {G : SimpleGraph V} {u v a b : V}
    (p : G.Walk u v) :
    (G.deleteEdges {s(a, b)}).Reachable u v ∨
      ((G.deleteEdges {s(a, b)}).Reachable u a ∨ (G.deleteEdges {s(a, b)}).Reachable u b) := by
  induction p with
  | nil => exact Or.inl .rfl
  | @cons x y z hxy _ ih =>
    by_cases he : s(x, y) = s(a, b)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl .rfl)
      · exact Or.inr (Or.inr .rfl)
    · have hadj : (G.deleteEdges {s(a, b)}).Adj x y := ⟨hxy, by simp [he]⟩
      rcases ih with h | h | h
      · exact Or.inl (hadj.reachable.trans h)
      · exact Or.inr (Or.inl (hadj.reachable.trans h))
      · exact Or.inr (Or.inr (hadj.reachable.trans h))

private lemma reachable_deleteEdges_iff_not_reachable_snd (hT : W.graph.IsTree)
    (d : W.graph.Dart) (u : V) :
    (W.graph.deleteEdges {d.edge}).Reachable u d.fst ↔
      ¬ (W.graph.deleteEdges {d.edge}).Reachable u d.snd := by
  have hnot := bridge_deleteEdges hT d
  refine ⟨fun h1 h2 => hnot (h1.symm.trans h2), fun h => ?_⟩
  obtain ⟨p⟩ := W.connected u d.fst
  rcases walk_reachable_deleteEdges_or (a := d.fst) (b := d.snd) p with h1 | h1 | h2
  · exact h1
  · exact h1
  · exact False.elim (h h2)

private lemma reachable_deleteEdges_adj_iff (d d' : W.graph.Dart) (hne : d'.edge ≠ d.edge) :
    (W.graph.deleteEdges {d.edge}).Reachable d'.fst d.fst ↔
      (W.graph.deleteEdges {d.edge}).Reachable d'.snd d.fst := by
  have hadj : (W.graph.deleteEdges {d.edge}).Adj d'.fst d'.snd := ⟨d'.adj, by simp [hne]⟩
  exact ⟨fun h => hadj.symm.reachable.trans h, fun h => hadj.reachable.trans h⟩

private noncomputable def edgeProjVert (W : WeightedGraph V) (d : W.graph.Dart) (v : V) : ℝ :=
  @ite ℝ ((W.graph.deleteEdges {d.edge}).Reachable v d.fst) (Classical.propDecidable _)
    0 (W.weight d.edge)

private noncomputable def edgeProjEdge (W : WeightedGraph V) (d d' : W.graph.Dart)
    (t : unitInterval) : ℝ :=
  @ite ℝ (d' = d) (Classical.propDecidable _) ((t : ℝ) * W.weight d.edge)
    (@ite ℝ (d' = d.symm) (Classical.propDecidable _) ((1 - (t : ℝ)) * W.weight d.edge)
      (edgeProjVert W d d'.fst))

private lemma edgeProjVert_fst (W : WeightedGraph V) (d : W.graph.Dart) :
    edgeProjVert W d d.fst = 0 := by
  classical
  dsimp only [edgeProjVert]
  simp only [Reachable.refl, ↓reduceIte]

private lemma edgeProjVert_snd (hT : W.graph.IsTree) (d : W.graph.Dart) :
    edgeProjVert W d d.snd = W.weight d.edge := by
  classical
  have hns : ¬ (W.graph.deleteEdges {d.edge}).Reachable d.snd d.fst :=
    fun h => bridge_deleteEdges hT d h.symm
  dsimp only [edgeProjVert]
  simp only [hns, ↓reduceIte]

private lemma edgeProjEdge_eq_fst (W : WeightedGraph V) (d d' : W.graph.Dart)
    (h1 : d' = d) (t : unitInterval) :
    edgeProjEdge W d d' t = (t : ℝ) * W.weight d.edge := by
  classical
  dsimp only [edgeProjEdge]
  simp only [h1, ↓reduceIte]

private lemma edgeProjEdge_eq_symm (W : WeightedGraph V) (d d' : W.graph.Dart)
    (h2 : d' = d.symm) (t : unitInterval) :
    edgeProjEdge W d d' t = (1 - (t : ℝ)) * W.weight d.edge := by
  classical
  dsimp only [edgeProjEdge]
  rw [h2]
  simp only [d.symm_ne, ↓reduceIte]

private lemma edgeProjEdge_of_edge_ne (W : WeightedGraph V) {d d' : W.graph.Dart}
    (hne : d'.edge ≠ d.edge) (t : unitInterval) :
    edgeProjEdge W d d' t = edgeProjVert W d d'.fst := by
  classical
  have h1 : d' ≠ d := fun h => hne (h ▸ rfl)
  have h2 : d' ≠ d.symm := fun h => hne (by rw [h, Dart.edge_symm])
  dsimp only [edgeProjEdge]
  simp only [h1, h2, ↓reduceIte]

private lemma dart_eq_or_eq_symm_or_edge_ne (d' d : W.graph.Dart) :
    d = d' ∨ d.symm = d' ∨ d'.edge ≠ d.edge := by
  by_cases he : d'.edge = d.edge
  · rcases (dart_edge_eq_iff d' d).mp he with h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr he)

/-- The `1`-Lipschitz projection of a tree metric graph onto `[0, W.weight d.edge]` along dart `d`,
sending the `d.fst`-component of `G \ {d.edge}` to `0`, the `d.snd`-component to `W.weight d.edge`,
and mapping edge `d` affinely. -/
noncomputable def edgeProj (hT : W.graph.IsTree) (d : W.graph.Dart) : MetricGraph W → ℝ :=
  MetricGraph.lift (edgeProjVert W d) (edgeProjEdge W d)
    (fun d' => by
      rcases dart_eq_or_eq_symm_or_edge_ne d' d with rfl | rfl | hne
      · rw [edgeProjEdge_eq_fst W d d rfl 0, edgeProjVert_fst]
        simp
      · rw [edgeProjEdge_eq_symm W d d.symm rfl 0, Dart.fst_symm, edgeProjVert_snd hT]
        simp
      · exact edgeProjEdge_of_edge_ne W hne 0)
    (fun d' => by
      rcases dart_eq_or_eq_symm_or_edge_ne d' d with rfl | rfl | hne
      · rw [edgeProjEdge_eq_fst W d d rfl 1, edgeProjVert_snd hT]
        simp
      · rw [edgeProjEdge_eq_symm W d d.symm rfl 1]
        have hsnd : d.symm.snd = d.fst := rfl
        rw [hsnd, edgeProjVert_fst]
        simp
      · rw [edgeProjEdge_of_edge_ne W hne 1]
        classical
        dsimp only [edgeProjVert]
        simp only [reachable_deleteEdges_adj_iff d d' hne])
    (fun d' t => by
      rcases dart_eq_or_eq_symm_or_edge_ne d' d with rfl | rfl | hne
      · rw [edgeProjEdge_eq_symm W d d.symm rfl, edgeProjEdge_eq_fst W d d rfl,
          unitInterval.coe_symm_eq]
        ring
      · rw [edgeProjEdge_eq_fst W d d.symm.symm (Dart.symm_symm d),
          edgeProjEdge_eq_symm W d d.symm rfl, unitInterval.coe_symm_eq]
      · have hne_s : d'.symm.edge ≠ d.edge := by simpa only [Dart.edge_symm] using hne
        rw [edgeProjEdge_of_edge_ne W hne_s, edgeProjEdge_of_edge_ne W hne]
        classical
        dsimp only [edgeProjVert]
        rw [Dart.fst_symm]
        simp only [reachable_deleteEdges_adj_iff d d' hne])

private theorem edgeProj_vertex_priv (hT : W.graph.IsTree) (d : W.graph.Dart) (v : V) :
    edgeProj hT d (vertex v) = edgeProjVert W d v :=
  lift_vertex _ _ _ _ _ v

theorem edgeProj_vertex_eq_zero_iff (hT : W.graph.IsTree) (d : W.graph.Dart) (v : V) :
    edgeProj hT d (vertex v) = 0 ↔ (W.graph.deleteEdges {d.edge}).Reachable v d.fst := by
  classical
  rw [edgeProj_vertex_priv]
  dsimp only [edgeProjVert]
  split_ifs with h
  · simp [h]
  · simp [h, (W.dart_weight_pos d).ne']

theorem edgeProj_vertex_eq_weight_iff (hT : W.graph.IsTree) (d : W.graph.Dart) (v : V) :
    edgeProj hT d (vertex v) = W.weight d.edge ↔
      ¬ (W.graph.deleteEdges {d.edge}).Reachable v d.fst := by
  classical
  rw [edgeProj_vertex_priv]
  dsimp only [edgeProjVert]
  split_ifs with h
  · simp [h, (W.dart_weight_pos d).ne]
  · simp [h]

private lemma edgeProj_vertex_fst (hT : W.graph.IsTree) (d : W.graph.Dart) :
    edgeProj hT d (vertex d.fst) = 0 :=
  (edgeProj_vertex_eq_zero_iff hT d d.fst).mpr (.refl _)

private lemma edgeProj_vertex_snd (hT : W.graph.IsTree) (d : W.graph.Dart) :
    edgeProj hT d (vertex d.snd) = W.weight d.edge :=
  (edgeProj_vertex_eq_weight_iff hT d d.snd).mpr fun hr => bridge_deleteEdges hT d hr.symm

theorem edgeProj_edgePoint_self (hT : W.graph.IsTree) (d : W.graph.Dart) (t : unitInterval) :
    edgeProj hT d (edgePoint d t) = (t : ℝ) * W.weight d.edge := by
  rw [edgeProj, lift_edgePoint]
  exact edgeProjEdge_eq_fst W d d rfl t

theorem edgeProj_edgePoint_symm (hT : W.graph.IsTree) (d : W.graph.Dart) (t : unitInterval) :
    edgeProj hT d (edgePoint d.symm t) = (1 - (t : ℝ)) * W.weight d.edge := by
  rw [edgeProj, lift_edgePoint]
  exact edgeProjEdge_eq_symm W d d.symm rfl t

theorem edgeProj_edgePoint_of_edge_ne (hT : W.graph.IsTree) {d d' : W.graph.Dart}
    (hne : d'.edge ≠ d.edge) (t : unitInterval) :
    edgeProj hT d (edgePoint d' t) = edgeProj hT d (vertex d'.fst) := by
  rw [edgeProj, lift_edgePoint, edgeProjEdge_of_edge_ne W hne, lift_vertex]

/-- Every point's projection onto dart `d` is `0`, `W.weight d.edge`, or realized by a strictly
interior point along `d`. -/
lemma edgeProj_cases (hT : W.graph.IsTree) (d : W.graph.Dart) (x : MetricGraph W) :
    edgeProj hT d x = 0 ∨ edgeProj hT d x = W.weight d.edge ∨
      ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ x = edgePoint d t := by
  have hv : ∀ v : V, edgeProj hT d (vertex v) = 0 ∨ edgeProj hT d (vertex v) = W.weight d.edge := by
    intro v
    classical
    rw [edgeProj_vertex_priv]
    dsimp only [edgeProjVert]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  induction x using ind with
  | vertex v => exact (hv v).imp_right Or.inl
  | edgePoint d' t ht0 ht1 =>
    rcases dart_eq_or_eq_symm_or_edge_ne d' d with rfl | rfl | hne
    · exact Or.inr (Or.inr ⟨t, ht0, ht1, rfl⟩)
    · exact Or.inr (Or.inr ⟨unitInterval.symm t,
        by simp only [unitInterval.coe_symm_eq]; linarith,
        by simp only [unitInterval.coe_symm_eq]; linarith,
        (edgePoint_symm' d t).symm⟩)
    · rw [edgeProj_edgePoint_of_edge_ne hT hne]
      exact (hv d'.fst).imp_right Or.inl

theorem edgeProj_nonneg (hT : W.graph.IsTree) (d : W.graph.Dart) (x : MetricGraph W) :
    0 ≤ edgeProj hT d x := by
  rcases edgeProj_cases hT d x with h | h | ⟨t, ht0, _, rfl⟩
  · exact h.symm.le
  · exact h ▸ W.dart_weight_nonneg d
  · rw [edgeProj_edgePoint_self]
    exact mul_nonneg ht0.le (W.dart_weight_nonneg d)

theorem edgeProj_le_weight (hT : W.graph.IsTree) (d : W.graph.Dart) (x : MetricGraph W) :
    edgeProj hT d x ≤ W.weight d.edge := by
  rcases edgeProj_cases hT d x with h | h | ⟨t, _, ht1, rfl⟩
  · exact h ▸ W.dart_weight_nonneg d
  · exact h.le
  · rw [edgeProj_edgePoint_self]
    exact mul_le_of_le_one_left (W.dart_weight_nonneg d) ht1.le

theorem edgeProj_symm (hT : W.graph.IsTree) (d : W.graph.Dart) (x : MetricGraph W) :
    edgeProj hT d.symm x = W.weight d.edge - edgeProj hT d x := by
  have hv : ∀ v : V,
      edgeProj hT d.symm (vertex v) = W.weight d.edge - edgeProj hT d (vertex v) := by
    intro v
    classical
    rw [edgeProj_vertex_priv, edgeProj_vertex_priv]
    dsimp only [edgeProjVert]
    rw [Dart.edge_symm, Dart.fst_symm, reachable_deleteEdges_iff_not_reachable_snd hT d v]
    split_ifs <;> ring
  induction x using ind_simple with
  | vertex v => exact hv v
  | edgePoint d' t =>
    rcases dart_eq_or_eq_symm_or_edge_ne d' d with rfl | rfl | hne
    · conv_lhs => rw [← edgePoint_symm d t]
      rw [edgeProj_edgePoint_self, Dart.edge_symm, edgeProj_edgePoint_self,
        unitInterval.coe_symm_eq]
      ring
    · rw [edgeProj_edgePoint_symm, edgeProj_edgePoint_self, Dart.edge_symm]
      ring
    · rw [edgeProj_edgePoint_of_edge_ne hT (by simpa only [Dart.edge_symm] using hne),
        edgeProj_edgePoint_of_edge_ne hT hne]
      exact hv d'.fst

theorem abs_sub_edgeProj_le_dist [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    (x y : MetricGraph W) :
    |edgeProj hT d x - edgeProj hT d y| ≤ Dist.dist x y := by
  refine dist_map_le_of_edgePoint_dist_le (edgeProj hT d) (fun d' s t => ?_) x y
  rw [Real.dist_eq]
  by_cases hne : d'.edge = d.edge
  · rcases (dart_edge_eq_iff d' d).mp hne with hdd | hdd
    · subst d'
      rw [edgeProj_edgePoint_self, edgeProj_edgePoint_self, ← sub_mul, abs_mul,
        abs_of_nonneg (W.dart_weight_nonneg d)]
    · subst d'
      rw [edgeProj_edgePoint_symm, edgeProj_edgePoint_symm, Dart.edge_symm, ← sub_mul, abs_mul,
        abs_of_nonneg (W.dart_weight_nonneg d)]
      have heq : (1 - (s : ℝ)) - (1 - (t : ℝ)) = -((s : ℝ) - t) := by ring
      rw [heq, abs_neg]
  · rw [edgeProj_edgePoint_of_edge_ne hT hne, edgeProj_edgePoint_of_edge_ne hT hne,
      sub_self, abs_zero]
    exact mul_nonneg (abs_nonneg _) (W.dart_weight_nonneg d')

private lemma walkLength_split_cut {G : SimpleGraph V} (w : Sym2 V → ℝ)
    (S : Set V) {u v : V} (hu : u ∈ S) (hv : v ∉ S) (p : G.Walk u v) :
    ∃ a b : V, ∃ _ : G.Adj a b, a ∈ S ∧ b ∉ S ∧
      ∃ (p₁ : G.Walk u a) (p₂ : G.Walk b v),
        walkLength w p₁ + w s(a, b) + walkLength w p₂ = walkLength w p := by
  induction p with
  | nil => exact absurd hu hv
  | @cons x y z hadj q ih =>
    by_cases hy : y ∈ S
    · obtain ⟨a, b, hab, ha, hb, p₁, p₂, hsum⟩ := ih hy hv
      refine ⟨a, b, hab, ha, hb, Walk.cons hadj p₁, p₂, ?_⟩
      rw [walkLength_cons, walkLength_cons, ← hsum]
      ring
    · exact ⟨x, y, hadj, hu, hy, Walk.nil, q, by simp [walkLength_cons]⟩

theorem vertexDist_eq_of_deleteEdges_cut [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {u v : V} (hu : (W.graph.deleteEdges {d.edge}).Reachable u d.fst)
    (hv : ¬ (W.graph.deleteEdges {d.edge}).Reachable v d.fst) :
    vertexDist W.graph W.weight u v =
      vertexDist W.graph W.weight u d.fst + W.weight d.edge +
        vertexDist W.graph W.weight d.snd v := by
  have _ := hT
  refine le_antisymm ?_ ?_
  · have h1 := vertexDist_triangle W.weight_nonneg (W.connected u d.fst) (W.connected d.fst v)
    have h2 := vertexDist_triangle W.weight_nonneg (W.connected d.fst d.snd) (W.connected d.snd v)
    have h3 : vertexDist W.graph W.weight d.fst d.snd ≤ W.weight d.edge :=
      vertexDist_adj_le W.weight_nonneg d.adj
    linarith
  · obtain ⟨q, -, hq⟩ := exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected u v)
    obtain ⟨a, b, hab, ha, hb, p₁, p₂, hsum⟩ :=
      walkLength_split_cut W.weight
        {x | (W.graph.deleteEdges {d.edge}).Reachable x d.fst} hu hv q
    have he : s(a, b) = d.edge := by
      by_contra hne
      have hadj' : (W.graph.deleteEdges {d.edge}).Adj a b := ⟨hab, by simp [hne]⟩
      exact hb (hadj'.symm.reachable.trans ha)
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have h1 := vertexDist_le W.weight_nonneg p₁
      have h2 := vertexDist_le W.weight_nonneg p₂
      change walkLength W.weight p₁ + W.weight d.edge + walkLength W.weight p₂ =
        walkLength W.weight q at hsum
      linarith
    · exact absurd (Reachable.refl d.fst) hb

theorem vertexDist_adj [Finite V] (hT : W.graph.IsTree) {u v : V} (h : W.graph.Adj u v) :
    vertexDist W.graph W.weight u v = W.weight s(u, v) := by
  let d : W.graph.Dart := ⟨(u, v), h⟩
  have hcut := vertexDist_eq_of_deleteEdges_cut hT d (.refl u)
    (fun hrev => bridge_deleteEdges hT d hrev.symm)
  simpa [d, vertexDist_self W.weight_nonneg] using hcut

/-- In a tree, every path between two vertices is a shortest path. -/
theorem walkLength_eq_vertexDist_of_isPath [Finite V] (hT : W.graph.IsTree) {a b : V}
    (p : W.graph.Walk a b) (hp : p.IsPath) :
    walkLength W.weight p = vertexDist W.graph W.weight a b := by
  obtain ⟨q, hqp, hq⟩ := exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected a b)
  have heq : (⟨p, hp⟩ : W.graph.Path a b) = ⟨q, hqp⟩ :=
    (hT.isAcyclic.subsingleton_path a b).elim _ _
  exact (congrArg (fun x => walkLength W.weight x.1) heq).trans hq

/-- In a tree, the vertices of a path from `a` to `b` lie on the interval between `a` and `b`. -/
theorem vertex_mem_interval_of_mem_support [Finite V] (hT : W.graph.IsTree) {a b w : V}
    {p : W.graph.Walk a b} (hp : p.IsPath) (hw : w ∈ p.support) :
    (vertex w : MetricGraph W) ∈ interval (vertex a) (vertex b) := by
  classical
  have hlen : walkLength W.weight (p.takeUntil w hw) + walkLength W.weight (p.dropUntil w hw) =
      walkLength W.weight p := by
    rw [← walkLength_append, Walk.take_spec p hw]
  rw [mem_interval_iff, dist_vertex, dist_vertex, dist_vertex,
    ← walkLength_eq_vertexDist_of_isPath hT _ (hp.takeUntil hw),
    ← walkLength_eq_vertexDist_of_isPath hT _ (hp.dropUntil hw),
    ← walkLength_eq_vertexDist_of_isPath hT p hp, hlen]

theorem dist_edgePoint_edgePoint_same_eq [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    (s t : unitInterval) :
    Dist.dist (edgePoint d s : MetricGraph W) (edgePoint d t) =
      |(s : ℝ) - t| * W.weight d.edge := by
  rw [dist_edgePoint_eq_direct_of_vertexDist_eq (vertexDist_adj hT d.adj), mul_comm]

/-- An interior projection value along `d` is attained only at the matching edge point. -/
private lemma eq_edgePoint_of_edgeProj_eq (hT : W.graph.IsTree) {d : W.graph.Dart}
    {x : MetricGraph W} {t : unitInterval} (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (h : edgeProj hT d x = (t : ℝ) * W.weight d.edge) : x = edgePoint d t := by
  have hwpos := W.dart_weight_pos d
  rcases edgeProj_cases hT d x with h0 | hw | ⟨s, _, _, rfl⟩
  · nlinarith only [h, h0, ht0, hwpos]
  · nlinarith only [h, hw, ht1, hwpos]
  · rw [edgeProj_edgePoint_self] at h
    rw [Subtype.ext (mul_right_cancel₀ hwpos.ne' h)]

private lemma edgePoint_edgeProj_zero_decomp (hT : W.graph.IsTree) (d d' : W.graph.Dart)
    {s : unitInterval} (hs0 : 0 < (s : ℝ)) (hs1 : (s : ℝ) < 1)
    (hx : edgeProj hT d (edgePoint d' s) = 0) :
    d'.edge ≠ d.edge ∧
      (W.graph.deleteEdges {d.edge}).Reachable d'.fst d.fst ∧
      (W.graph.deleteEdges {d.edge}).Reachable d'.snd d.fst := by
  have hne : d'.edge ≠ d.edge := by
    intro he
    rcases (dart_edge_eq_iff d' d).mp he with rfl | rfl
    · rw [edgeProj_edgePoint_self] at hx
      exact absurd ((mul_eq_zero.mp hx).resolve_right (W.dart_weight_pos d').ne') hs0.ne'
    · rw [edgeProj_edgePoint_symm] at hx
      have : 1 - (s : ℝ) = 0 := (mul_eq_zero.mp hx).resolve_right (W.dart_weight_pos d).ne'
      linarith
  have hf : (W.graph.deleteEdges {d.edge}).Reachable d'.fst d.fst := by
    rw [edgeProj_edgePoint_of_edge_ne hT hne, edgeProj_vertex_eq_zero_iff] at hx
    exact hx
  exact ⟨hne, hf, (reachable_deleteEdges_adj_iff d d' hne).mp hf⟩

theorem dist_edgePoint_of_edgeProj_zero [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {x : MetricGraph W} (hx : edgeProj hT d x = 0) (t : unitInterval) :
    Dist.dist x (edgePoint d t) = Dist.dist x (vertex d.fst) + (t : ℝ) * W.weight d.edge := by
  have hns : ¬ (W.graph.deleteEdges {d.edge}).Reachable d.snd d.fst :=
    fun h => bridge_deleteEdges hT d h.symm
  have hcut : ∀ {u : V}, (W.graph.deleteEdges {d.edge}).Reachable u d.fst →
      vertexDist W.graph W.weight u d.snd = vertexDist W.graph W.weight u d.fst + W.weight d.edge :=
    fun hu => by simpa only [vertexDist_self W.weight_nonneg, add_zero] using
      vertexDist_eq_of_deleteEdges_cut hT d hu hns
  have ht1 : (t : ℝ) * W.weight d.edge ≤ W.weight d.edge + (1 - t) * W.weight d.edge := by
    nlinarith only [W.dart_weight_nonneg d, t.2.2]
  induction x using ind with
  | vertex u =>
    rw [dist_vertex_edgePoint, dist_vertex, hcut ((edgeProj_vertex_eq_zero_iff hT d u).mp hx)]
    exact min_eq_left (by linarith)
  | edgePoint d' s hs0 hs1 =>
    obtain ⟨hne, hf, hs⟩ := edgePoint_edgeProj_zero_decomp hT d d' hs0 hs1 hx
    rw [dist_edgePoint_edgePoint_of_edge_ne hne, dist_edgePoint_vertex, hcut hf, hcut hs]
    simp only [add_assoc, ← add_min, min_eq_left ht1]
    simp only [← add_assoc, ← min_add, vertexDist_comm d'.fst d.fst, vertexDist_comm d'.snd d.fst]

private lemma edgePoint_edgeProj_weight_decomp (hT : W.graph.IsTree) (d d' : W.graph.Dart)
    {s : unitInterval} (hs0 : 0 < (s : ℝ)) (hs1 : (s : ℝ) < 1)
    (hx : edgeProj hT d (edgePoint d' s) = W.weight d.edge) :
    d'.edge ≠ d.edge ∧
      ¬ (W.graph.deleteEdges {d.edge}).Reachable d'.fst d.fst ∧
      ¬ (W.graph.deleteEdges {d.edge}).Reachable d'.snd d.fst := by
  have hx' : edgeProj hT d.symm (edgePoint d' s) = 0 := by rw [edgeProj_symm, hx, sub_self]
  obtain ⟨hne, hf, hs⟩ := edgePoint_edgeProj_zero_decomp hT d.symm d' hs0 hs1 hx'
  rw [Dart.edge_symm] at hne hf hs
  exact ⟨hne, fun h => bridge_deleteEdges hT d (h.symm.trans hf),
    fun h => bridge_deleteEdges hT d (h.symm.trans hs)⟩

theorem dist_of_edgeProj_zero_eq_weight [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {x y : MetricGraph W} (hx : edgeProj hT d x = 0) (hy : edgeProj hT d y = W.weight d.edge) :
    Dist.dist x y =
      Dist.dist x (vertex d.fst) + W.weight d.edge + Dist.dist (vertex d.snd) y := by
  induction x using ind with
  | vertex u =>
    have hu := (edgeProj_vertex_eq_zero_iff hT d u).mp hx
    induction y using ind with
    | vertex v =>
      have hv := (edgeProj_vertex_eq_weight_iff hT d v).mp hy
      simpa only [dist_vertex] using vertexDist_eq_of_deleteEdges_cut hT d hu hv
    | edgePoint d₂ t ht0 ht1 =>
      obtain ⟨_, hf, hs⟩ := edgePoint_edgeProj_weight_decomp hT d d₂ ht0 ht1 hy
      rw [dist_vertex_edgePoint, dist_vertex, dist_vertex_edgePoint,
        vertexDist_eq_of_deleteEdges_cut hT d hu hf, vertexDist_eq_of_deleteEdges_cut hT d hu hs]
      simp only [add_assoc, ← add_min]
  | edgePoint d₁ s hs0 hs1 =>
    obtain ⟨_, hf₁, hs₁⟩ := edgePoint_edgeProj_zero_decomp hT d d₁ hs0 hs1 hx
    induction y using ind with
    | vertex v =>
      have hv := (edgeProj_vertex_eq_weight_iff hT d v).mp hy
      rw [dist_edgePoint_vertex, dist_edgePoint_vertex, dist_vertex,
        vertexDist_eq_of_deleteEdges_cut hT d hf₁ hv, vertexDist_eq_of_deleteEdges_cut hT d hs₁ hv,
        vertexDist_comm d₁.fst d.fst, vertexDist_comm d₁.snd d.fst]
      simp only [← add_assoc, ← min_add]
    | edgePoint d₂ t ht0 ht1 =>
      obtain ⟨_, hf₂, hs₂⟩ := edgePoint_edgeProj_weight_decomp hT d d₂ ht0 ht1 hy
      have hne₁₂ : d₁.edge ≠ d₂.edge := fun he => by
        rcases (dart_edge_eq_iff d₁ d₂).mp he with rfl | rfl
        · exact hf₂ hf₁
        · exact hs₂ hf₁
      rw [dist_edgePoint_edgePoint_of_edge_ne hne₁₂, dist_edgePoint_vertex, dist_vertex_edgePoint,
        vertexDist_eq_of_deleteEdges_cut hT d hf₁ hf₂,
        vertexDist_eq_of_deleteEdges_cut hT d hf₁ hs₂,
        vertexDist_eq_of_deleteEdges_cut hT d hs₁ hf₂,
        vertexDist_eq_of_deleteEdges_cut hT d hs₁ hs₂,
        vertexDist_comm d₁.fst d.fst, vertexDist_comm d₁.snd d.fst]
      simp only [add_assoc, ← add_min]
      simp only [← add_assoc, ← min_add]

theorem dist_edgePoint_of_edgeProj_weight [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {x : MetricGraph W} (hx : edgeProj hT d x = W.weight d.edge) (t : unitInterval) :
    Dist.dist x (edgePoint d t) =
      Dist.dist x (vertex d.snd) + (1 - (t : ℝ)) * W.weight d.edge := by
  have hx' : edgeProj hT d.symm x = 0 := by rw [edgeProj_symm, hx, sub_self]
  rw [← edgePoint_symm d t]
  simpa only [Dart.fst_symm, Dart.edge_symm, unitInterval.coe_symm_eq] using
    dist_edgePoint_of_edgeProj_zero hT d.symm hx' (unitInterval.symm t)

theorem vertex_fst_mem_interval_of_edgeProj [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {y z : MetricGraph W} (hy : edgeProj hT d y = 0) (hz : 0 < edgeProj hT d z) :
    vertex d.fst ∈ interval y z := by
  rw [mem_interval_iff]
  rcases edgeProj_cases hT d z with hz0 | hzw | ⟨sz, _, _, rfl⟩
  · linarith
  · have h1 := dist_of_edgeProj_zero_eq_weight hT d hy hzw
    have h2 := dist_edgePoint_of_edgeProj_weight hT d hzw 0
    simp only [edgePoint_zero, Set.Icc.coe_zero, sub_zero, one_mul] at h2
    rw [_root_.dist_comm (vertex d.fst) z, h2, h1, _root_.dist_comm z (vertex d.snd)]
    ring
  · have h1 := dist_edgePoint_of_edgeProj_zero hT d hy sz
    have h2 := dist_edgePoint_edgePoint_same_eq hT d 0 sz
    simp only [edgePoint_zero, Set.Icc.coe_zero, zero_sub, abs_neg,
      abs_of_nonneg sz.2.1] at h2
    rw [h1, h2]

theorem edgePoint_mem_interval_of_edgeProj_le [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {y z : MetricGraph W} {t : unitInterval} (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (hy : edgeProj hT d y ≤ (t : ℝ) * W.weight d.edge)
    (hz : (t : ℝ) * W.weight d.edge ≤ edgeProj hT d z) :
    edgePoint d t ∈ interval y z := by
  have hwpos := W.dart_weight_pos d
  rcases edgeProj_cases hT d y with hy0 | hyw | ⟨sy, _, _, rfl⟩
  · rcases edgeProj_cases hT d z with hz0 | hzw | ⟨sz, _, _, rfl⟩
    · nlinarith only [hz, hz0, ht0, hwpos]
    · rw [mem_interval_iff]
      have hxy := dist_of_edgeProj_zero_eq_weight hT d hy0 hzw
      have hy1 := dist_edgePoint_of_edgeProj_zero hT d hy0 t
      have hz1 := dist_edgePoint_of_edgeProj_weight hT d hzw t
      rw [_root_.dist_comm (edgePoint d t) z, hz1, hy1, hxy, _root_.dist_comm z (vertex d.snd)]
      ring
    · rw [edgeProj_edgePoint_self] at hz
      exact edgePoint_mem_interval_of_fst ((mul_le_mul_iff_left₀ hwpos).mp hz)
        (dist_edgePoint_of_edgeProj_zero hT d hy0 sz)
  · nlinarith only [hy, hyw, ht1, hwpos]
  · rw [edgeProj_edgePoint_self] at hy
    have hsy_le : (sy : ℝ) ≤ t := (mul_le_mul_iff_left₀ hwpos).mp hy
    rcases edgeProj_cases hT d z with hz0 | hzw | ⟨sz, _, _, rfl⟩
    · nlinarith only [hz, hz0, ht0, hwpos]
    · exact interval_comm z (edgePoint d sy) ▸
        edgePoint_mem_interval_of_snd hsy_le (dist_edgePoint_of_edgeProj_weight hT d hzw sy)
    · rw [edgeProj_edgePoint_self] at hz
      exact edgePoint_mem_interval_edgePoint_of_direct
        (dist_edgePoint_edgePoint_same_eq hT d sy sz)
        (Or.inl ⟨hsy_le, (mul_le_mul_iff_left₀ hwpos).mp hz⟩)

/-- In a tree, the zero set of a bridge projection is convex: it contains the interval between any
two of its points. -/
theorem edgeProj_eq_zero_of_mem_interval [Finite V] (hT : W.graph.IsTree) {d : W.graph.Dart}
    {p q z : MetricGraph W} (hp : edgeProj hT d p = 0) (hq : edgeProj hT d q = 0)
    (hz : z ∈ interval p q) : edgeProj hT d z = 0 := by
  by_contra hne
  have hpos : 0 < edgeProj hT d z := lt_of_le_of_ne (edgeProj_nonneg hT d z) (Ne.symm hne)
  have hm₁ := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d hp hpos)
  have hm₂ := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d hq hpos)
  have hz_mem := mem_interval_iff.mp hz
  have hd_pos : 0 < Dist.dist (vertex d.fst : MetricGraph W) z :=
    _root_.dist_pos.mpr fun heq => hne (heq ▸ edgeProj_vertex_fst hT d)
  linarith [_root_.dist_triangle p (vertex d.fst) q,
    _root_.dist_comm (vertex d.fst : MetricGraph W) z, _root_.dist_comm q z,
    _root_.dist_comm q (vertex d.fst)]

/-- In a tree, every point of an edge lies on the interval between the edge's endpoints. -/
theorem edgePoint_mem_interval_vertex [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    (t : unitInterval) : edgePoint d t ∈ interval (vertex d.fst) (vertex d.snd) := by
  rw [← edgePoint_zero d, ← edgePoint_one d]
  exact edgePoint_mem_interval_edgePoint_of_direct
    (dist_edgePoint_edgePoint_same_eq hT d 0 1) (Or.inl ⟨t.2.1, t.2.2⟩)

end TreeProjection

/-! ### Uniqueness of geodesics and metric intervals -/

section TreeGeodesic

private lemma dist_add_dist_gt_of_edgeProj_lt [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {x y z : MetricGraph W} (hzx : edgeProj hT d z < edgeProj hT d x)
    (hzy : edgeProj hT d z < edgeProj hT d y) :
    Dist.dist x y < Dist.dist x z + Dist.dist z y := by
  have hwpos := W.dart_weight_pos d
  let m := min (edgeProj hT d x) (edgeProj hT d y)
  have hzm : edgeProj hT d z < m := lt_min hzx hzy
  have hz0 : 0 ≤ edgeProj hT d z := edgeProj_nonneg hT d z
  have hmw : m ≤ W.weight d.edge := (min_le_left _ _).trans (edgeProj_le_weight hT d x)
  let c : ℝ := (edgeProj hT d z + m) / (2 * W.weight d.edge)
  have hc0 : 0 < c := div_pos (by linarith) (by linarith)
  have hc1 : c < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  let t : unitInterval := ⟨c, hc0.le, hc1.le⟩
  have htw : (t : ℝ) * W.weight d.edge = (edgeProj hT d z + m) / 2 := by
    change c * W.weight d.edge = _
    dsimp only [c]
    field_simp [hwpos.ne']
  have hzt : edgeProj hT d z < (t : ℝ) * W.weight d.edge := by linarith
  have hx_int := mem_interval_iff.mp
    (edgePoint_mem_interval_of_edgeProj_le hT d (y := z) (z := x) hc0 hc1 hzt.le
      (by linarith [min_le_left (edgeProj hT d x) (edgeProj hT d y)]))
  have hy_int := mem_interval_iff.mp
    (edgePoint_mem_interval_of_edgeProj_le hT d (y := z) (z := y) hc0 hc1 hzt.le
      (by linarith [min_le_right (edgeProj hT d x) (edgeProj hT d y)]))
  have hd_pos : 0 < Dist.dist z (edgePoint d t) :=
    _root_.dist_pos.mpr fun heq => hzt.ne (by rw [heq, edgeProj_edgePoint_self])
  linarith [_root_.dist_triangle x (edgePoint d t) y, _root_.dist_comm x z,
    _root_.dist_comm x (edgePoint d t)]

private lemma mem_interval_edgeProj_bounds [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {x y z : MetricGraph W} (hz : z ∈ interval x y)
    (hxy : edgeProj hT d x ≤ edgeProj hT d y) :
    edgeProj hT d x ≤ edgeProj hT d z ∧ edgeProj hT d z ≤ edgeProj hT d y := by
  have hxzy := mem_interval_iff.mp hz
  refine ⟨?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    exact (dist_add_dist_gt_of_edgeProj_lt hT d hlt (hlt.trans_le hxy)).ne hxzy.symm
  · by_contra hlt
    push Not at hlt
    refine (dist_add_dist_gt_of_edgeProj_lt hT d.symm ?_ ?_).ne hxzy.symm <;>
      rw [edgeProj_symm, edgeProj_symm] <;> linarith

private lemma dist_lt_of_edgeProj_lt [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {x y z₁ z₂ : MetricGraph W} (hz₁ : z₁ ∈ interval x y) (hz₂ : z₂ ∈ interval x y)
    (hxy : edgeProj hT d x ≤ edgeProj hT d y) (hlt : edgeProj hT d z₁ < edgeProj hT d z₂) :
    Dist.dist x z₁ < Dist.dist x z₂ := by
  have hb₁ := mem_interval_edgeProj_bounds hT d hz₁ hxy
  have h2_diff : edgeProj hT d z₂ - edgeProj hT d (vertex d.fst) ≤
      Dist.dist (vertex d.fst) z₂ := by
    rw [_root_.dist_comm]
    exact (le_abs_self _).trans (abs_sub_edgeProj_le_dist hT d z₂ (vertex d.fst))
  rw [edgeProj_vertex_fst, sub_zero] at h2_diff
  rcases edgeProj_cases hT d z₁ with h10 | h1w | ⟨s₁, hs10, hs11, rfl⟩
  · have hx0 : edgeProj hT d x = 0 :=
      le_antisymm (h10 ▸ hb₁.1) (edgeProj_nonneg hT d x)
    have hypos : 0 < edgeProj hT d y := by linarith [(mem_interval_edgeProj_bounds hT d hz₂ hxy).2]
    have hxy_f := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d hx0 hypos)
    have hzy_f := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d h10 hypos)
    have hxz₁_eq := mem_interval_iff.mp hz₁
    have hxz₂_f := mem_interval_iff.mp
      (vertex_fst_mem_interval_of_edgeProj hT d hx0 (z := z₂) (by linarith))
    linarith [_root_.dist_nonneg (x := z₁) (y := vertex d.fst)]
  · linarith [edgeProj_le_weight hT d z₂]
  · have hwpos := W.dart_weight_pos d
    have hs₁_eq := edgeProj_edgePoint_self hT d s₁
    rcases edgeProj_cases hT d x with hx0 | hxw | ⟨sx, _, _, rfl⟩
    · have hxz₁ := dist_edgePoint_of_edgeProj_zero hT d hx0 s₁
      have hxz₂_f := mem_interval_iff.mp
        (vertex_fst_mem_interval_of_edgeProj hT d hx0 (z := z₂) (by linarith [mul_pos hs10 hwpos]))
      linarith
    · nlinarith only [hb₁.1, hs₁_eq, hxw, hs11, hwpos]
    · have hsx_le : (sx : ℝ) ≤ s₁ := (mul_le_mul_iff_left₀ hwpos).mp
        (by simpa only [edgeProj_edgePoint_self] using hb₁.1)
      have hxz₁ := dist_edgePoint_edgePoint_same_eq hT d sx s₁
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hsx_le)] at hxz₁
      have h2 := (le_abs_self _).trans (abs_sub_edgeProj_le_dist hT d z₂ (edgePoint d sx))
      rw [edgeProj_edgePoint_self, _root_.dist_comm] at h2
      linarith

private lemma eq_of_forall_edgeProj_eq (hT : W.graph.IsTree) {z₁ z₂ : MetricGraph W}
    (h : ∀ d : W.graph.Dart, edgeProj hT d z₁ = edgeProj hT d z₂) : z₁ = z₂ := by
  induction z₁ using ind with
  | vertex u =>
    induction z₂ using ind with
    | vertex v =>
      by_contra hne
      obtain ⟨p, hp⟩ := (W.connected u v).exists_isPath
      have hnn : ¬ p.Nil := Walk.not_nil_of_ne fun huv => hne (huv ▸ rfl)
      let d : W.graph.Dart := p.firstDart hnn
      have htail_avoid : d.fst ∉ p.tail.support := by
        have hnodup := hp.support_nodup
        rw [← p.cons_tail_eq hnn, Walk.support_cons, List.nodup_cons] at hnodup
        exact hnodup.1
      have hdsnd : (W.graph.deleteEdges {d.edge}).Reachable d.snd v :=
        ⟨p.tail.toDeleteEdges {d.edge} fun e he hmem =>
          htail_avoid (p.tail.fst_mem_support_of_mem_edges (hmem ▸ he))⟩
      have h0 : edgeProj hT d (vertex u) = 0 := edgeProj_vertex_fst hT d
      have hw : edgeProj hT d (vertex v) = W.weight d.edge :=
        (edgeProj_vertex_eq_weight_iff hT d v).mpr fun hr =>
          bridge_deleteEdges hT d (hdsnd.trans hr).symm
      linarith [h d, W.dart_weight_pos d]
    | edgePoint d₂ t₂ ht0 ht1 =>
      exact eq_edgePoint_of_edgeProj_eq hT ht0 ht1 ((h d₂).trans (edgeProj_edgePoint_self hT d₂ t₂))
  | edgePoint d₁ t₁ ht10 ht11 =>
    exact (eq_edgePoint_of_edgeProj_eq hT ht10 ht11
      ((h d₁).symm.trans (edgeProj_edgePoint_self hT d₁ t₁))).symm

/-- In a tree metric graph, two points on `interval x y` at equal distance from `x` are equal. -/
theorem eq_of_mem_interval_dist_eq [Finite V] (hT : W.graph.IsTree) {x y z₁ z₂ : MetricGraph W}
    (hz₁ : z₁ ∈ interval x y) (hz₂ : z₂ ∈ interval x y) (hd : Dist.dist x z₁ = Dist.dist x z₂) :
    z₁ = z₂ := by
  refine eq_of_forall_edgeProj_eq hT fun d => ?_
  by_contra hne
  wlog hxy : edgeProj hT d x ≤ edgeProj hT d y generalizing x y
  · refine this (interval_comm x y ▸ hz₁) (interval_comm x y ▸ hz₂) ?_ (le_of_not_ge hxy)
    rw [_root_.dist_comm y z₁, _root_.dist_comm y z₂]
    linarith [mem_interval_iff.mp hz₁, mem_interval_iff.mp hz₂]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (dist_lt_of_edgeProj_lt hT d hz₁ hz₂ hxy hlt).ne hd
  · exact (dist_lt_of_edgeProj_lt hT d hz₂ hz₁ hxy hgt).ne hd.symm

/-- Geodesics between two points in a tree metric graph are unique on `[0, dist x y]`. -/
theorem IsGeodesic.eq_on [Finite V] (hT : W.graph.IsTree) {x y : MetricGraph W}
    {γ₁ γ₂ : ℝ → MetricGraph W} (h₁ : IsGeodesic x y γ₁) (h₂ : IsGeodesic x y γ₂)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (Dist.dist x y)) : γ₁ t = γ₂ t := by
  refine eq_of_mem_interval_dist_eq hT (h₁.mem_interval ht) (h₂.mem_interval ht) ?_
  calc Dist.dist x (γ₁ t) = Dist.dist (γ₁ 0) (γ₁ t) := by rw [h₁.map_zero]
    _ = |0 - t| := h₁.dist_eq ⟨le_rfl, _root_.dist_nonneg⟩ ht
    _ = Dist.dist (γ₂ 0) (γ₂ t) := (h₂.dist_eq ⟨le_rfl, _root_.dist_nonneg⟩ ht).symm
    _ = Dist.dist x (γ₂ t) := by rw [h₂.map_zero]

theorem interval_dist_eq_abs [Finite V] (hT : W.graph.IsTree) {x y z₁ z₂ : MetricGraph W}
    (hz₁ : z₁ ∈ interval x y) (hz₂ : z₂ ∈ interval x y) :
    Dist.dist z₁ z₂ = |Dist.dist x z₁ - Dist.dist x z₂| := by
  obtain ⟨γ, hγ⟩ := exists_isGeodesic x y
  obtain ⟨γ₁, hγ₁, h1⟩ := exists_isGeodesic_through_of_mem_interval hz₁
  obtain ⟨γ₂, hγ₂, h2⟩ := exists_isGeodesic_through_of_mem_interval hz₂
  have hmem1 : Dist.dist x z₁ ∈ Set.Icc 0 (Dist.dist x y) :=
    ⟨_root_.dist_nonneg,
      by linarith [mem_interval_iff.mp hz₁, _root_.dist_nonneg (x := z₁) (y := y)]⟩
  have hmem2 : Dist.dist x z₂ ∈ Set.Icc 0 (Dist.dist x y) :=
    ⟨_root_.dist_nonneg,
      by linarith [mem_interval_iff.mp hz₂, _root_.dist_nonneg (x := z₂) (y := y)]⟩
  conv_lhs =>
    rw [← h1, ← h2, hγ₁.eq_on hT hγ hmem1, hγ₂.eq_on hT hγ hmem2, hγ.dist_eq hmem1 hmem2]

theorem mem_interval_of_mem_interval_dist_le [Finite V] (hT : W.graph.IsTree)
    {x y z w : MetricGraph W} (hz : z ∈ interval x y) (hw : w ∈ interval x y)
    (hle : Dist.dist x z ≤ Dist.dist x w) : z ∈ interval x w := by
  rw [mem_interval_iff, interval_dist_eq_abs hT hz hw, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr hle)]
  ring

theorem interval_subset_of_mem [Finite V] (hT : W.graph.IsTree) {x y u v : MetricGraph W}
    (hu : u ∈ interval x y) (hv : v ∈ interval x y) : interval u v ⊆ interval x y := by
  wlog huv : Dist.dist x u ≤ Dist.dist x v generalizing u v
  · rw [interval_comm u v]
    exact this hv hu (le_of_not_ge huv)
  intro z hz
  have hu' : u ∈ interval x v := mem_interval_of_mem_interval_dist_le hT hu hv huv
  have hxz : z ∈ interval x v := by
    have e1 := mem_interval_iff.mp hz
    have e2 := mem_interval_iff.mp hu'
    rw [mem_interval_iff]
    linarith [_root_.dist_triangle x u z, _root_.dist_triangle x z v]
  exact mem_interval_trans_left hv hxz

theorem isClosed_interval [Finite V] (x y : MetricGraph W) :
    IsClosed (interval x y) :=
  isClosed_eq ((continuous_const.dist continuous_id).add (continuous_id.dist continuous_const))
    continuous_const

/-- In a tree metric graph, the interval between `a` and `b` is the image of an isometric
parametrization of `[0, dist a b]` from `a` to `b`. -/
theorem exists_isometry_interval [Finite V] (hT : W.graph.IsTree) (a b : MetricGraph W) :
    ∃ φ : Set.Icc (0 : ℝ) (Dist.dist a b) → MetricGraph W,
      Isometry φ ∧
      φ ⟨0, le_rfl, _root_.dist_nonneg⟩ = a ∧
      φ ⟨Dist.dist a b, _root_.dist_nonneg, le_rfl⟩ = b ∧
      Set.range φ = interval a b := by
  obtain ⟨γ, hγ⟩ := exists_isGeodesic a b
  refine ⟨fun t => γ t.1, hγ.isometry, hγ.map_zero, hγ.map_dist, Set.ext fun z => ?_⟩
  constructor
  · rintro ⟨t, rfl⟩
    exact hγ.mem_interval t.2
  · intro hz
    obtain ⟨γ', hγ', hgz⟩ := exists_isGeodesic_through_of_mem_interval hz
    have hmem : Dist.dist a z ∈ Set.Icc 0 (Dist.dist a b) :=
      ⟨_root_.dist_nonneg,
        by linarith [mem_interval_iff.mp hz, _root_.dist_nonneg (x := z) (y := b)]⟩
    exact ⟨⟨Dist.dist a z, hmem⟩, (hγ'.eq_on hT hγ hmem).symm.trans hgz⟩

end TreeGeodesic

/-! ### Tree medians and branch partitions -/

section TreeMedian

private lemma exists_edge_dart_of_ne {a b : MetricGraph W} (hab : a ≠ b) :
    Nonempty W.graph.Dart := by
  induction a using ind with
  | vertex u =>
    induction b using ind with
    | vertex v =>
      have huv : u ≠ v := fun h => hab (h ▸ rfl)
      obtain ⟨p⟩ := W.connected u v
      exact ⟨p.firstDart (Walk.not_nil_of_ne huv)⟩
    | edgePoint d _ _ _ => exact ⟨d⟩
  | edgePoint d _ _ _ => exact ⟨d⟩

/-- Every point at distance `r` strictly less than all edge weights from `vertex v` lies on
a dart starting at `v` at parameter `r / W.weight d.edge`. -/
theorem dist_vertex_mem_step_dart [Finite V] {v : V} {p : MetricGraph W} {r : ℝ}
    (hpos : 0 < r) (hr : Dist.dist (vertex v : MetricGraph W) p = r)
    (hmin : ∀ d : W.graph.Dart, r < W.weight d.edge) :
    ∃ (d : W.graph.Dart) (t : unitInterval),
      d.fst = v ∧ 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ p = edgePoint d t ∧
      (t : ℝ) * W.weight d.edge = r := by
  have hvd_ge : ∀ {u w : V}, u ≠ w → r < vertexDist W.graph W.weight u w := by
    intro u w huw
    obtain ⟨q, -, hq⟩ := exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected u w)
    cases q with
    | nil => exact absurd rfl huw
    | cons hadj q' =>
      have h1 := hmin ⟨(_, _), hadj⟩
      have h2 := walkLength_nonneg W.weight W.weight_nonneg q'
      rw [← hq, walkLength_cons]
      exact h1.trans_le (le_add_of_nonneg_right h2)
  rcases eq_vertex_or_edgePoint_of_dist_vertex_lt (v := v) (p := p)
      (fun u hu => by rw [hr, dist_vertex]; exact hvd_ge (Ne.symm hu)) with
    rfl | ⟨d, t, hfst, ht0, ht1, rfl, hd⟩
  · rw [_root_.dist_self] at hr
    linarith
  · exact ⟨d, t, hfst, ht0, ht1, rfl, hd.symm.trans hr⟩

private lemma vertex_step_dart_pos [Finite V] (hT : W.graph.IsTree) {v : V} {y : MetricGraph W}
    {r : ℝ} (hr_pos : 0 < r) (hr_le : r ≤ Dist.dist (vertex v : MetricGraph W) y)
    (hmin : ∀ d : W.graph.Dart, r < W.weight d.edge) :
    ∃ (d : W.graph.Dart) (t : unitInterval),
      d.fst = v ∧ 0 < (t : ℝ) ∧ edgePoint d t ∈ interval (vertex v) y ∧
      Dist.dist (vertex v : MetricGraph W) (edgePoint d t) = r ∧
      (t : ℝ) * W.weight d.edge = r ∧ 0 < edgeProj hT d y := by
  obtain ⟨p, hp_mem, hp_d, _⟩ := exists_mem_interval_dist_eq (vertex v) y ⟨hr_pos.le, hr_le⟩
  obtain ⟨d, t, hd_fst, ht0, _, rfl, htr⟩ := dist_vertex_mem_step_dart hr_pos hp_d hmin
  have hdv : edgeProj hT d (vertex v) = 0 := hd_fst ▸ edgeProj_vertex_fst hT d
  have hpos : 0 < edgeProj hT d y := by
    have h1 : 0 < edgeProj hT d (edgePoint d t) := by
      rw [edgeProj_edgePoint_self]
      exact mul_pos ht0 (W.dart_weight_pos d)
    exact h1.trans_le (mem_interval_edgeProj_bounds hT d hp_mem
      (by rw [hdv]; exact edgeProj_nonneg hT d y)).2
  exact ⟨d, t, hd_fst, ht0, hp_mem, hp_d, htr, hpos⟩

private lemma interval_of_no_common_step_vertex [Finite V] (hT : W.graph.IsTree)
    {v : V} {y z : MetricGraph W} (hvy : vertex v ≠ y) (hvz : vertex v ≠ z)
    (hno : ∀ p, 0 < Dist.dist (vertex v : MetricGraph W) p →
      p ∈ interval (vertex v) y → p ∈ interval (vertex v) z → False) :
    (vertex v : MetricGraph W) ∈ interval y z := by
  obtain ⟨d₀⟩ := exists_edge_dart_of_ne hvy
  obtain ⟨wmin, hwmin_pos, hwmin_le⟩ := exists_min_dart_weight (W := W) d₀
  let r : ℝ := min wmin (min (Dist.dist (vertex v) y) (Dist.dist (vertex v) z)) / 3
  have hdy_pos : 0 < Dist.dist (vertex v : MetricGraph W) y := _root_.dist_pos.mpr hvy
  have hdz_pos : 0 < Dist.dist (vertex v : MetricGraph W) z := _root_.dist_pos.mpr hvz
  have hr_pos : 0 < r := by dsimp only [r]; positivity
  have h3r : 3 * r = min wmin (min (Dist.dist (vertex v) y) (Dist.dist (vertex v) z)) := by
    dsimp only [r]; ring
  have hr_w : 3 * r ≤ wmin := h3r ▸ min_le_left _ _
  have hmin_yz : 3 * r ≤ min (Dist.dist (vertex v) y) (Dist.dist (vertex v) z) :=
    h3r ▸ min_le_right _ _
  have hr_lt_w : ∀ d : W.graph.Dart, r < W.weight d.edge := fun d => by linarith [hwmin_le d]
  obtain ⟨dy, ty, hdy_fst, _, hpy_mem, hpy_d, hty_r, hdy_y⟩ :=
    vertex_step_dart_pos hT (v := v) (y := y) hr_pos
      (by linarith [hmin_yz.trans (min_le_left _ _)]) hr_lt_w
  obtain ⟨dz, tz, hdz_fst, _, hpz_mem, hpz_d, htz_r, _⟩ :=
    vertex_step_dart_pos hT (v := v) (y := z) hr_pos
      (by linarith [hmin_yz.trans (min_le_right _ _)]) hr_lt_w
  by_cases he : dy.edge = dz.edge
  · obtain rfl : dy = dz := (dart_edge_eq_iff dy dz).mp he |>.resolve_right fun h =>
      dz.snd_ne_fst (by simpa only [h, Dart.fst_symm] using hdy_fst.trans hdz_fst.symm)
    obtain rfl : ty = tz :=
      Subtype.ext (mul_right_cancel₀ (W.dart_weight_pos dy).ne' (hty_r.trans htz_r.symm))
    exact (hno (edgePoint dy ty) (hpy_d ▸ hr_pos) hpy_mem hpz_mem).elim
  · have hpz0 : edgeProj hT dy (edgePoint dz tz) = 0 := by
      rw [edgeProj_edgePoint_of_edge_ne hT (Ne.symm he), hdz_fst, ← hdy_fst, edgeProj_vertex_fst]
    have hdy_z : edgeProj hT dy z = 0 := by
      by_contra hnz
      have hzpos := lt_of_le_of_ne (edgeProj_nonneg hT dy z) (Ne.symm hnz)
      have hv_mem := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT dy hpz0 hzpos)
      have hpz_eq := mem_interval_iff.mp hpz_mem
      rw [hdy_fst, _root_.dist_comm (edgePoint dz tz) (vertex v)] at hv_mem
      linarith
    exact hdy_fst ▸ interval_comm z y ▸ vertex_fst_mem_interval_of_edgeProj hT dy hdy_z hdy_y

private lemma interval_of_no_common_step_edgePoint [Finite V] (hT : W.graph.IsTree)
    {d : W.graph.Dart} {t : unitInterval} (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    {y z : MetricGraph W} (hmy : edgePoint d t ≠ y) (hmz : edgePoint d t ≠ z)
    (hno : ∀ p, 0 < Dist.dist (edgePoint d t) p →
      p ∈ interval (edgePoint d t) y → p ∈ interval (edgePoint d t) z → False) :
    edgePoint d t ∈ interval y z := by
  have hwpos := W.dart_weight_pos d
  have htw_pos : 0 < (t : ℝ) * W.weight d.edge := mul_pos ht0 hwpos
  have h1tw_pos : 0 < (1 - (t : ℝ)) * W.weight d.edge := mul_pos (sub_pos.mpr ht1) hwpos
  have hdy_pos : 0 < Dist.dist (edgePoint d t) y := _root_.dist_pos.mpr hmy
  have hdz_pos : 0 < Dist.dist (edgePoint d t) z := _root_.dist_pos.mpr hmz
  let r : ℝ := min (min ((t : ℝ) * W.weight d.edge) ((1 - (t : ℝ)) * W.weight d.edge))
    (min (Dist.dist (edgePoint d t) y) (Dist.dist (edgePoint d t) z)) / 3
  have hr_pos : 0 < r := by dsimp only [r]; positivity
  have h3r : 3 * r = min (min ((t : ℝ) * W.weight d.edge) ((1 - (t : ℝ)) * W.weight d.edge))
      (min (Dist.dist (edgePoint d t) y) (Dist.dist (edgePoint d t) z)) := by dsimp only [r]; ring
  have hlt_t : 3 * r ≤ min ((t : ℝ) * W.weight d.edge) ((1 - (t : ℝ)) * W.weight d.edge) :=
    h3r ▸ min_le_left _ _
  have hr_yz : 3 * r ≤ min (Dist.dist (edgePoint d t) y) (Dist.dist (edgePoint d t) z) :=
    h3r ▸ min_le_right _ _
  have hstep : ∀ w, 3 * r ≤ Dist.dist (edgePoint d t) w →
      ∃ s : unitInterval, edgePoint d s ∈ interval (edgePoint d t) w ∧
        |(s : ℝ) - t| * W.weight d.edge = r ∧
        ((s : ℝ) < t ∧ edgeProj hT d w ≤ (t : ℝ) * W.weight d.edge ∨
          (t : ℝ) < s ∧ (t : ℝ) * W.weight d.edge ≤ edgeProj hT d w) := by
    intro w hw_le
    obtain ⟨p, hp_mem, hp_d, _⟩ :=
      exists_mem_interval_dist_eq (edgePoint d t) w ⟨hr_pos.le, by linarith⟩
    have hsub := abs_sub_edgeProj_le_dist hT d (edgePoint d t) p
    rw [edgeProj_edgePoint_self, hp_d] at hsub
    have hbd := abs_le.mp hsub
    have hlo : 0 < edgeProj hT d p := by linarith [hlt_t.trans (min_le_left _ _)]
    have hhi : edgeProj hT d p < W.weight d.edge := by linarith [hlt_t.trans (min_le_right _ _)]
    obtain ⟨s, _, _, rfl⟩ := ((edgeProj_cases hT d p).resolve_left hlo.ne').resolve_left hhi.ne
    have hs_eq : |(s : ℝ) - t| * W.weight d.edge = r := by
      simpa only [abs_sub_comm] using (dist_edgePoint_edgePoint_same_eq hT d t s).symm.trans hp_d
    refine ⟨s, hp_mem, hs_eq, ?_⟩
    rcases lt_trichotomy (s : ℝ) t with hlt | heq | hgt
    · refine Or.inl ⟨hlt, le_of_not_gt fun hgt_w => ?_⟩
      have hb := mem_interval_edgeProj_bounds hT d hp_mem
        (by rw [edgeProj_edgePoint_self]; exact hgt_w.le)
      rw [edgeProj_edgePoint_self, edgeProj_edgePoint_self] at hb
      nlinarith only [hb.1, hlt, hwpos]
    · simp only [heq, sub_self, abs_zero, zero_mul] at hs_eq; linarith only [hr_pos, hs_eq]
    · refine Or.inr ⟨hgt, le_of_not_gt fun hlt_w => ?_⟩
      have hb := mem_interval_edgeProj_bounds hT d (interval_comm (edgePoint d t) w ▸ hp_mem)
        (by rw [edgeProj_edgePoint_self]; exact hlt_w.le)
      rw [edgeProj_edgePoint_self, edgeProj_edgePoint_self] at hb
      nlinarith only [hb.2, hgt, hwpos]
  obtain ⟨sy, hpy_mem, hsy_r, hside_y⟩ := hstep y (hr_yz.trans (min_le_left _ _))
  obtain ⟨sz, hpz_mem, hsz_r, hside_z⟩ := hstep z (hr_yz.trans (min_le_right _ _))
  have hne_s : sy ≠ sz := fun heq => hno (edgePoint d sy)
    (by rw [dist_edgePoint_edgePoint_same_eq hT, abs_sub_comm, hsy_r]; exact hr_pos)
    hpy_mem (heq ▸ hpz_mem)
  have hopp : (sy : ℝ) - t = -((sz : ℝ) - t) :=
    (abs_eq_abs.mp (mul_right_cancel₀ hwpos.ne' (hsy_r.trans hsz_r.symm))).resolve_left fun h =>
      hne_s (Subtype.ext (by linarith))
  rcases hside_y with ⟨hsy, hy⟩ | ⟨hsy, hy⟩ <;> rcases hside_z with ⟨hsz, hz⟩ | ⟨hsz, hz⟩
  · linarith
  · exact edgePoint_mem_interval_of_edgeProj_le hT d ht0 ht1 hy hz
  · exact interval_comm z y ▸ edgePoint_mem_interval_of_edgeProj_le hT d ht0 ht1 hz hy
  · linarith

/-- Every triple of points in a tree metric graph has a point lying on shortest paths between
all three pairs. -/
theorem exists_treeMedian [Finite V] (hT : W.graph.IsTree) (x y z : MetricGraph W) :
    ∃ m : MetricGraph W, m ∈ interval x y ∧ m ∈ interval y z ∧ m ∈ interval z x := by
  let S : Set (MetricGraph W) := interval x y ∩ interval x z
  obtain ⟨m, ⟨hm_xy, hm_xz⟩, hm_max⟩ :=
    ((isClosed_interval x y).inter (isClosed_interval x z)).isCompact.exists_isMaxOn
      ⟨x, left_mem_interval x y, left_mem_interval x z⟩
      (continuous_const.dist continuous_id).continuousOn
  refine ⟨m, hm_xy, ?_, interval_comm x z ▸ hm_xz⟩
  by_cases hmy : m = y; · exact hmy ▸ left_mem_interval y z
  by_cases hmz : m = z; · exact hmz ▸ right_mem_interval y z
  have hno : ∀ p, 0 < Dist.dist m p → p ∈ interval m y → p ∈ interval m z → False := by
    intro p hmp hpy hpz
    have extend : ∀ {a}, m ∈ interval x a → p ∈ interval m a → p ∈ interval x a :=
      fun {a} hm hp => interval_comm a x ▸
        mem_interval_trans_left (interval_comm x a ▸ hm) (interval_comm m a ▸ hp)
    have hpxy := extend hm_xy hpy
    have hle : Dist.dist x p ≤ Dist.dist x m := hm_max ⟨hpxy, extend hm_xz hpz⟩
    linarith [mem_interval_iff.mp hpxy, mem_interval_iff.mp hm_xy, mem_interval_iff.mp hpy]
  induction m using ind with
  | vertex v => exact interval_of_no_common_step_vertex hT hmy hmz hno
  | edgePoint d t ht0 ht1 => exact interval_of_no_common_step_edgePoint hT ht0 ht1 hmy hmz hno

/-- The unique metric median `treeMedian hT x y z` in a tree metric graph. -/
noncomputable def treeMedian [Finite V] (hT : W.graph.IsTree) (x y z : MetricGraph W) :
    MetricGraph W :=
  (exists_treeMedian hT x y z).choose

theorem treeMedian_mem_xy [Finite V] (hT : W.graph.IsTree) (x y z : MetricGraph W) :
    treeMedian hT x y z ∈ interval x y :=
  (exists_treeMedian hT x y z).choose_spec.1

theorem treeMedian_mem_yz [Finite V] (hT : W.graph.IsTree) (x y z : MetricGraph W) :
    treeMedian hT x y z ∈ interval y z :=
  (exists_treeMedian hT x y z).choose_spec.2.1

theorem treeMedian_mem_zx [Finite V] (hT : W.graph.IsTree) (x y z : MetricGraph W) :
    treeMedian hT x y z ∈ interval z x :=
  (exists_treeMedian hT x y z).choose_spec.2.2

theorem eq_treeMedian_of_mem [Finite V] (hT : W.graph.IsTree) {x y z m : MetricGraph W}
    (hxy : m ∈ interval x y) (hyz : m ∈ interval y z) (hzx : m ∈ interval z x) :
    m = treeMedian hT x y z := by
  refine eq_of_mem_interval_dist_eq hT hxy (treeMedian_mem_xy hT x y z) ?_
  have e1 := mem_interval_iff.mp hxy
  have e2 := mem_interval_iff.mp hyz
  have e3 := mem_interval_iff.mp hzx
  have m1 := mem_interval_iff.mp (treeMedian_mem_xy hT x y z)
  have m2 := mem_interval_iff.mp (treeMedian_mem_yz hT x y z)
  have m3 := mem_interval_iff.mp (treeMedian_mem_zx hT x y z)
  linarith [_root_.dist_comm z x, _root_.dist_comm z m, _root_.dist_comm m x,
    _root_.dist_comm m y, _root_.dist_comm z (treeMedian hT x y z),
    _root_.dist_comm (treeMedian hT x y z) x, _root_.dist_comm (treeMedian hT x y z) y]

theorem dist_add_dist_eq_treeMedian [Finite V] (hT : W.graph.IsTree) {x y z p : MetricGraph W}
    (hp : p ∈ interval x y) :
    Dist.dist z p = Dist.dist z (treeMedian hT x y z) + Dist.dist (treeMedian hT x y z) p := by
  let m := treeMedian hT x y z
  have hm_xy : m ∈ interval x y := treeMedian_mem_xy hT x y z
  have hm_yz : m ∈ interval y z := treeMedian_mem_yz hT x y z
  have hm_zx : m ∈ interval z x := treeMedian_mem_zx hT x y z
  rcases le_total (Dist.dist x p) (Dist.dist x m) with hle | hle
  · have hp_xm := mem_interval_iff.mp (mem_interval_of_mem_interval_dist_le hT hp hm_xy hle)
    have hm_zx' := mem_interval_iff.mp hm_zx
    linarith [_root_.dist_triangle z p x, _root_.dist_triangle z m p, _root_.dist_comm p x,
      _root_.dist_comm m x, _root_.dist_comm p m]
  · have hp_xy' := mem_interval_iff.mp hp
    have hm_xy' := mem_interval_iff.mp hm_xy
    have hm_xp := mem_interval_iff.mp (mem_interval_of_mem_interval_dist_le hT hm_xy hp hle)
    have hm_yz' := mem_interval_iff.mp hm_yz
    linarith [_root_.dist_triangle y p z, _root_.dist_triangle z m p, _root_.dist_comm y p,
      _root_.dist_comm p z, _root_.dist_comm y m, _root_.dist_comm m z, _root_.dist_comm y z]

/-- The median `treeMedian hT x y z` is the gate of `z` on `interval x y`: it lies between `z`
and every point of that interval. -/
theorem treeMedian_mem_interval_of_mem [Finite V] (hT : W.graph.IsTree) {x y p : MetricGraph W}
    (hp : p ∈ interval x y) (z : MetricGraph W) : treeMedian hT x y z ∈ interval z p :=
  mem_interval_iff.mpr (dist_add_dist_eq_treeMedian hT hp).symm

/-- In a tree metric graph, the interval from `x` to `z` is covered by the intervals from `x` to
`y` and from `y` to `z`. -/
theorem interval_subset_union [Finite V] (hT : W.graph.IsTree) (x y z : MetricGraph W) :
    interval x z ⊆ interval x y ∪ interval y z := by
  intro w hw
  have hm : treeMedian hT x y z ∈ interval x z := interval_comm z x ▸ treeMedian_mem_zx hT x y z
  rcases le_total (Dist.dist x w) (Dist.dist x (treeMedian hT x y z)) with hle | hle
  · exact Or.inl (interval_subset_of_mem hT (left_mem_interval x y) (treeMedian_mem_xy hT x y z)
      (mem_interval_of_mem_interval_dist_le hT hw hm hle))
  · exact Or.inr (interval_subset_of_mem hT (treeMedian_mem_yz hT x y z) (right_mem_interval y z)
      (mem_interval_trans_right hw (mem_interval_of_mem_interval_dist_le hT hm hw hle)))

/-- The branch of a tree metric graph at base point `p` in the direction of `q`:
`{ w | p ∉ interval q w }`. Equal to `∅` when `q = p`. -/
@[expose] def branch [Finite V] (p q : MetricGraph W) : Set (MetricGraph W) :=
  { w | p ∉ interval q w }

@[simp]
theorem notMem_branch_self [Finite V] (p q : MetricGraph W) : p ∉ branch p q := by
  simp [branch]

@[simp]
theorem branch_self [Finite V] (p : MetricGraph W) : branch p p = ∅ := by
  ext w
  simp [branch]

theorem mem_branch_self [Finite V] {p q : MetricGraph W} (hpq : q ≠ p) : q ∈ branch p q := by
  simp only [branch, Set.mem_ofPred_eq, interval_eq_singleton_self, Set.mem_singleton_iff]
  exact hpq.symm

theorem branch_symm [Finite V] {q₁ q₂ w : MetricGraph W} (hq : q₁ ≠ q₂)
    (hw : w ∉ branch q₁ q₂) : w ∈ branch q₂ q₁ := by
  simp only [branch, Set.mem_ofPred_eq, Classical.not_not] at hw ⊢
  intro hmem
  have e1 := mem_interval_iff.mp hw
  have e2 := mem_interval_iff.mp hmem
  have hd : Dist.dist q₂ q₁ = 0 := by
    linarith [_root_.dist_comm q₁ q₂, _root_.dist_comm q₁ w, _root_.dist_comm q₂ w]
  exact hq ((_root_.dist_eq_zero.mp hd).symm)

theorem branch_eq_of_mem [Finite V] (hT : W.graph.IsTree) {p q₁ q₂ : MetricGraph W}
    (hq : q₂ ∈ branch p q₁) : branch p q₂ = branch p q₁ := by
  have sub_of : ∀ {a b : MetricGraph W}, b ∈ branch p a → branch p b ⊆ branch p a := by
    intro a b hb w hw hwa
    let m₁ := treeMedian hT p a b
    let m₂ := treeMedian hT p b w
    have hcontra : ∀ m, m ≠ p → m ∈ interval p a → m ∈ interval p w → False := fun m hne ha' hw' =>
      by linarith [mem_interval_iff.mp ha', mem_interval_iff.mp hw', mem_interval_iff.mp hwa,
        _root_.dist_pos.mpr hne.symm, _root_.dist_triangle a m w,
        _root_.dist_comm a m, _root_.dist_comm p a, _root_.dist_comm p m]
    have hm1_pa := treeMedian_mem_xy hT p a b
    have hm1_pb := interval_comm b p ▸ treeMedian_mem_zx hT p a b
    have hm2_pb := treeMedian_mem_xy hT p b w
    have hm2_pw := interval_comm w p ▸ treeMedian_mem_zx hT p b w
    rcases le_total (Dist.dist p m₁) (Dist.dist p m₂) with hle | hle
    · exact hcontra m₁ (fun h => hb (h ▸ treeMedian_mem_yz hT p a b)) hm1_pa
        (mem_interval_trans_left hm2_pw (mem_interval_of_mem_interval_dist_le hT hm1_pb hm2_pb hle))
    · exact hcontra m₂ (fun h => hw (h ▸ treeMedian_mem_yz hT p b w))
        (mem_interval_trans_left hm1_pa (mem_interval_of_mem_interval_dist_le hT hm2_pb hm1_pb hle))
        hm2_pw
  exact Set.Subset.antisymm (sub_of hq) (sub_of (by rwa [branch, Set.mem_ofPred_eq, interval_comm]))

theorem branch_disjoint_of_mem_interval [Finite V] (hT : W.graph.IsTree)
    {p q₁ q₂ : MetricGraph W} (hp : p ∈ interval q₁ q₂) :
    Disjoint (branch p q₁) (branch p q₂) := by
  rw [Set.disjoint_left]
  intro w hw1 hw2
  by_cases h1 : q₁ = p
  · subst h1
    simp only [branch_self, Set.mem_empty_iff_false] at hw1
  · have hq1 : q₁ ∈ branch p q₂ := by
      rw [← branch_eq_of_mem hT hw2, branch_eq_of_mem hT hw1]
      exact mem_branch_self h1
    simp only [branch, Set.mem_ofPred_eq, interval_comm q₂ q₁] at hq1
    exact hq1 hp

/-- Two distinct branches at the same base point of a tree metric graph are disjoint. -/
theorem branch_disjoint_of_ne [Finite V] (hT : W.graph.IsTree) {y p q : MetricGraph W}
    (hpq : branch y p ≠ branch y q) : Disjoint (branch y p) (branch y q) :=
  Set.disjoint_left.mpr fun _ hwp hwq =>
    hpq ((branch_eq_of_mem hT hwp).symm.trans (branch_eq_of_mem hT hwq))

/-- Moving the base point toward `q` shrinks the branch toward `q`. -/
theorem branch_subset_branch_of_mem_interval [Finite V] {y p q : MetricGraph W}
    (hp : p ∈ interval y q) : branch p q ⊆ branch y q := by
  intro w hw
  by_contra hnot
  simp only [branch, Set.mem_ofPred_eq, Classical.not_not] at hnot hw
  have h1 := mem_interval_iff.mp hp
  have h2 := mem_interval_iff.mp hnot
  have hqpw : Dist.dist q p + Dist.dist p w ≤ Dist.dist q w := by
    have htri := _root_.dist_triangle p y w
    linarith [_root_.dist_comm q p, _root_.dist_comm q y, _root_.dist_comm q w,
      _root_.dist_comm p y, _root_.dist_comm y w]
  exact hw (mem_interval_iff.mpr (le_antisymm hqpw (_root_.dist_triangle q p w)))

/-- Every point other than `y` between `y` and a point of the branch at `y` toward `q` lies in
that branch. -/
theorem mem_branch_of_mem_interval [Finite V] (hT : W.graph.IsTree) {y b q z : MetricGraph W}
    (hb : b ∈ branch y q) (hz : z ∈ interval y b) (hzy : z ≠ y) : z ∈ branch y q := by
  rw [← branch_eq_of_mem hT hb]
  simp only [branch, Set.mem_ofPred_eq]
  intro hmem
  have h1 := mem_interval_iff.mp hz
  have h2 := mem_interval_iff.mp hmem
  have hd : Dist.dist y z = 0 := by
    linarith [_root_.dist_comm b y, _root_.dist_comm b z, _root_.dist_comm y z,
      _root_.dist_comm z b]
  exact hzy (_root_.dist_eq_zero.mp hd).symm

/-- A point `π` between `z` and both `p` and `q` lies in the branch at `p` toward `q` exactly
when `z` does. This is the branch property of gates (`IsConvex.mem_branch_gate_iff`) and of
medians. -/
theorem mem_branch_iff_of_mem_interval [Finite V] {p q z π : MetricGraph W}
    (hp : π ∈ interval z p) (hq : π ∈ interval z q) : z ∈ branch p q ↔ π ∈ branch p q := by
  have hzp := mem_interval_iff.mp hp
  have hzq := mem_interval_iff.mp hq
  simp only [branch, Set.mem_ofPred_eq, mem_interval_iff]
  constructor <;> intro h heq <;> apply h <;>
    linarith [_root_.dist_comm z p, _root_.dist_comm z q, _root_.dist_comm p π,
      _root_.dist_comm q π]

/-- The branch at a vertex `c` toward an adjacent vertex `w` is the set where the projection
along the dart `(c, w)` is positive. -/
theorem mem_branch_vertex_iff_edgeProj_pos [Finite V] (hT : W.graph.IsTree) {c w : V}
    (hadj : W.graph.Adj c w) (z : MetricGraph W) :
    z ∈ branch (vertex c) (vertex w) ↔ 0 < edgeProj hT ⟨(c, w), hadj⟩ z := by
  let d : W.graph.Dart := ⟨(c, w), hadj⟩
  change z ∈ branch (vertex d.fst) (vertex d.snd) ↔ 0 < edgeProj hT d z
  have hw_pos := W.dart_weight_pos d
  have hc0 : edgeProj hT d (vertex d.fst) = 0 := edgeProj_vertex_fst hT d
  have hw_proj : edgeProj hT d (vertex d.snd) = W.weight d.edge := edgeProj_vertex_snd hT d
  constructor
  · intro hz
    by_contra hle
    have h0 : edgeProj hT d z = 0 := le_antisymm (not_lt.mp hle) (edgeProj_nonneg hT d z)
    have hmem := vertex_fst_mem_interval_of_edgeProj hT d h0 (by rw [hw_proj]; exact hw_pos)
    exact hz (interval_comm z (vertex d.snd) ▸ hmem)
  · intro hpos
    simp only [branch, Set.mem_ofPred_eq, mem_interval_iff]
    exact fun hmem => (dist_add_dist_gt_of_edgeProj_lt hT d
      (by rw [hc0, hw_proj]; exact hw_pos) (by rwa [hc0])).ne hmem.symm

/-- At a vertex of a tree metric graph, the branches toward distinct neighbours are disjoint. -/
theorem disjoint_branch_vertex_of_adj [Finite V] (hT : W.graph.IsTree) {c w₁ w₂ : V}
    (hadj₁ : W.graph.Adj c w₁) (hadj₂ : W.graph.Adj c w₂) (hne : w₁ ≠ w₂) :
    Disjoint (branch (vertex c : MetricGraph W) (vertex w₁))
      (branch (vertex c : MetricGraph W) (vertex w₂)) := by
  refine branch_disjoint_of_ne hT fun heq => ?_
  have hw₁ : (vertex w₁ : MetricGraph W) ∈ branch (vertex c) (vertex w₂) :=
    heq ▸ mem_branch_self fun h => hadj₁.ne (vertex_injective (W := W) h.symm)
  rw [mem_branch_vertex_iff_edgeProj_pos hT hadj₂, ← not_le] at hw₁
  refine hw₁ (le_of_eq ((edgeProj_vertex_eq_zero_iff hT _ w₁).mpr ?_))
  refine SimpleGraph.Adj.reachable ⟨hadj₁.symm, fun h => ?_⟩
  rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp h.1) with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hadj₁.ne h1.symm
  · exact hne h1

private lemma edgeProj_gt_of_mem_branch_snd [Finite V] (hT : W.graph.IsTree) {d : W.graph.Dart}
    {t₀ : unitInterval} (ht₀1 : (t₀ : ℝ) < 1) {w : MetricGraph W}
    (hw : w ∈ branch (edgePoint d t₀) (vertex d.snd)) :
    (t₀ : ℝ) * W.weight d.edge < edgeProj hT d w := by
  by_contra hle
  push Not at hle
  have hv₀_proj := edgeProj_vertex_snd hT d
  rcases lt_or_eq_of_le t₀.2.1 with ht0 | ht0
  · exact hw (interval_comm w (vertex d.snd) ▸
      edgePoint_mem_interval_of_edgeProj_le hT d ht0 ht₀1 hle
        (hv₀_proj.symm ▸ mul_le_of_le_one_left (W.dart_weight_nonneg d) t₀.2.2))
  · obtain rfl : t₀ = 0 := Subtype.ext ht0.symm
    have hw0 : edgeProj hT d w = 0 := le_antisymm
      (by simpa only [Set.Icc.coe_zero, zero_mul] using hle) (edgeProj_nonneg hT d w)
    exact hw (by simpa only [edgePoint_zero] using interval_comm w (vertex d.snd) ▸
      vertex_fst_mem_interval_of_edgeProj hT d hw0 (hv₀_proj ▸ W.dart_weight_pos d))

private lemma exists_stem_segment_of_dart [Finite V] (hT : W.graph.IsTree)
    {d : W.graph.Dart} {t₀ : unitInterval} (ht₀1 : (t₀ : ℝ) < 1)
    {q : MetricGraph W} (hq_gt : (t₀ : ℝ) * W.weight d.edge < edgeProj hT d q) :
    ∃ v₀ ∈ branch (edgePoint d t₀) q, 0 < Dist.dist (edgePoint d t₀) v₀ ∧
      (∀ p ∈ interval (edgePoint d t₀) v₀, p ≠ edgePoint d t₀ →
        p ∈ branch (edgePoint d t₀) q) ∧
      (∀ w ∈ branch (edgePoint d t₀) q, ∀ p ∈ interval (edgePoint d t₀) v₀,
        Dist.dist (edgePoint d t₀) p ≤ Dist.dist (edgePoint d t₀) w →
          p ∈ interval (edgePoint d t₀) w) ∧
      (∃ r₀ > 0, r₀ ≤ Dist.dist (edgePoint d t₀) v₀ ∧
        ∀ p ∈ interval (edgePoint d t₀) v₀, 0 < Dist.dist (edgePoint d t₀) p →
          Dist.dist (edgePoint d t₀) p ≤ r₀ →
          ∀ z : MetricGraph W, Dist.dist p z ≤ Dist.dist (edgePoint d t₀) p →
            z ∈ interval (edgePoint d t₀) v₀ ∧
              Dist.dist (edgePoint d t₀) z ≤ 2 * Dist.dist (edgePoint d t₀) p) := by
  have hwpos := W.dart_weight_pos d
  have hy_proj := edgeProj_edgePoint_self hT d t₀
  have hv₀_proj := edgeProj_vertex_snd hT d
  have hdv_eq : Dist.dist (edgePoint d t₀) (vertex d.snd) = (1 - (t₀ : ℝ)) * W.weight d.edge := by
    have h := dist_edgePoint_edgePoint_same_eq hT d t₀ 1
    rw [edgePoint_one, Set.Icc.coe_one, abs_of_neg (sub_neg.mpr ht₀1)] at h
    linarith
  have hv₀_mem : (vertex d.snd : MetricGraph W) ∈ branch (edgePoint d t₀) q := by
    simp only [branch, Set.mem_ofPred_eq, mem_interval_iff]
    exact fun hmem => (dist_add_dist_gt_of_edgeProj_lt hT d (hy_proj ▸ hq_gt)
      (by rw [hy_proj, hv₀_proj]; nlinarith only [ht₀1, hwpos])).ne hmem.symm
  have hdv_pos : 0 < Dist.dist (edgePoint d t₀) (vertex d.snd) := by
    rw [hdv_eq]; exact mul_pos (sub_pos.mpr ht₀1) hwpos
  refine ⟨vertex d.snd, hv₀_mem, hdv_pos,
    fun p hp hpne => mem_branch_of_mem_interval hT hv₀_mem hp hpne, ?_, ?_⟩
  · intro w hw p hp hp_le
    have hw_gt := edgeProj_gt_of_mem_branch_snd hT ht₀1 (branch_eq_of_mem hT hv₀_mem ▸ hw)
    rcases eq_or_lt_of_le (edgeProj_le_weight hT d w) with hww | hww
    · have hsym_w : edgeProj hT d.symm w = 0 := by rw [edgeProj_symm, hww, sub_self]
      have hsym_y : 0 < edgeProj hT d.symm (edgePoint d t₀) := by
        rw [edgeProj_symm, hy_proj]; nlinarith only [ht₀1, hwpos]
      exact mem_interval_trans_left
        (interval_comm w _ ▸ Dart.fst_symm d ▸ vertex_fst_mem_interval_of_edgeProj hT d.symm
          hsym_w hsym_y) hp
    · obtain ⟨sw, _, _, rfl⟩ := ((edgeProj_cases hT d w).resolve_left
        ((mul_nonneg t₀.2.1 hwpos.le).trans_lt hw_gt).ne').resolve_left hww.ne
      have htw : (t₀ : ℝ) ≤ sw :=
        ((mul_lt_mul_iff_left₀ hwpos).mp (by rwa [edgeProj_edgePoint_self] at hw_gt)).le
      refine mem_interval_of_mem_interval_dist_le hT hp ?_ hp_le
      rw [← edgePoint_one d]
      exact edgePoint_mem_interval_edgePoint_of_direct
        (dist_edgePoint_edgePoint_same_eq hT d t₀ 1) (Or.inl ⟨htw, sw.2.2⟩)
  · refine ⟨(1 - (t₀ : ℝ)) * W.weight d.edge / 3, by linarith, by linarith,
      fun p hp hdp_pos hdp_le z hz => ?_⟩
    have hdz_le : Dist.dist (edgePoint d t₀) z ≤ 2 * Dist.dist (edgePoint d t₀) p :=
      (_root_.dist_triangle _ p z).trans (by linarith)
    have hp_gt := edgeProj_gt_of_mem_branch_snd hT ht₀1
      (mem_branch_of_mem_interval hT (mem_branch_self (_root_.dist_pos.mp hdv_pos).symm) hp
        (_root_.dist_pos.mp hdp_pos).symm)
    have hpy_sub := (le_abs_self _).trans (abs_sub_edgeProj_le_dist hT d p (edgePoint d t₀))
    rw [hy_proj, _root_.dist_comm] at hpy_sub
    rcases edgeProj_cases hT d p with h0 | hpw | ⟨sp, hs0, _, rfl⟩
    · linarith [mul_nonneg t₀.2.1 hwpos.le]
    · linarith
    have hp_sp := edgeProj_edgePoint_self hT d sp
    have hsp_ge : (t₀ : ℝ) ≤ sp := ((mul_lt_mul_iff_left₀ hwpos).mp (hp_sp ▸ hp_gt)).le
    have hdp_eq : Dist.dist (edgePoint d t₀) (edgePoint d sp) =
        ((sp : ℝ) - t₀) * W.weight d.edge := by
      rw [dist_edgePoint_edgePoint_same_eq hT d t₀ sp, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr hsp_ge)]
    have hzp := abs_le.mp ((abs_sub_edgeProj_le_dist hT d (edgePoint d sp) z).trans hz)
    rw [hp_sp, hdp_eq] at hzp
    refine ⟨?_, hdz_le⟩
    rcases edgeProj_cases hT d z with hz0 | hzw | ⟨sz, _, hsz1, rfl⟩
    · obtain rfl : t₀ = 0 := Subtype.ext (le_antisymm
        ((mul_le_mul_iff_left₀ hwpos).mp (by
          rw [hz0] at hzp; change _ ≤ (0 : ℝ) * _; linarith))
        t₀.2.1)
      have hm := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d hz0
        (by rw [hp_sp]; exact mul_pos hs0 hwpos))
      have hz_fst : z = vertex d.fst := _root_.dist_eq_zero.mp (le_antisymm (by
        rw [edgePoint_zero] at hz hdp_pos
        linarith [_root_.dist_comm (edgePoint d sp) z]) _root_.dist_nonneg)
      rw [edgePoint_zero, hz_fst]
      exact left_mem_interval _ _
    · linarith
    · have hge : (t₀ : ℝ) ≤ sz := (mul_le_mul_iff_left₀ hwpos).mp
        (by rw [edgeProj_edgePoint_self] at hzp; linarith)
      rw [← edgePoint_one d]
      exact edgePoint_mem_interval_edgePoint_of_direct
        (dist_edgePoint_edgePoint_same_eq hT d t₀ 1) (Or.inl ⟨hge, hsz1.le⟩)

/-- Every nonzero direction `q ≠ y` in a finite tree metric graph begins along a positive-length
unbranched segment `interval y v₀ ⊆ branch y q ∪ {y}` inside which small balls stay in the
segment. -/
theorem exists_stem_segment [Finite V] (hT : W.graph.IsTree) {y q : MetricGraph W} (hq : q ≠ y) :
    ∃ v₀ ∈ branch y q, 0 < Dist.dist y v₀ ∧
      (∀ p ∈ interval y v₀, p ≠ y → p ∈ branch y q) ∧
      (∀ w ∈ branch y q, ∀ p ∈ interval y v₀, Dist.dist y p ≤ Dist.dist y w → p ∈ interval y w) ∧
      (∃ r₀ > 0, r₀ ≤ Dist.dist y v₀ ∧
        ∀ p ∈ interval y v₀, 0 < Dist.dist y p → Dist.dist y p ≤ r₀ →
          ∀ z : MetricGraph W, Dist.dist p z ≤ Dist.dist y p →
            z ∈ interval y v₀ ∧ Dist.dist y z ≤ 2 * Dist.dist y p) := by
  induction y using ind with
  | vertex v =>
    obtain ⟨d₀⟩ := exists_edge_dart_of_ne hq.symm
    obtain ⟨wmin, hwmin_pos, hwmin_le⟩ := exists_min_dart_weight (W := W) d₀
    have hq_pos : 0 < Dist.dist (vertex v : MetricGraph W) q := _root_.dist_pos.mpr hq.symm
    let r : ℝ := min wmin (Dist.dist (vertex v) q) / 3
    have hr_pos : 0 < r := by dsimp only [r]; positivity
    have h3r : 3 * r = min wmin (Dist.dist (vertex v : MetricGraph W) q) := by dsimp only [r]; ring
    have hr_w : 3 * r ≤ wmin := h3r ▸ min_le_left _ _
    have hr_q : 3 * r ≤ Dist.dist (vertex v : MetricGraph W) q := h3r ▸ min_le_right _ _
    obtain ⟨d, _, hd_fst, _, _, _, _, hq_gt⟩ := vertex_step_dart_pos hT (v := v) (y := q) hr_pos
      (by linarith) (fun d => by linarith [hwmin_le d])
    subst hd_fst
    simpa only [edgePoint_zero] using
      exists_stem_segment_of_dart hT (t₀ := 0) zero_lt_one (by simpa only [Set.Icc.coe_zero,
        zero_mul] using hq_gt)
  | edgePoint d t ht0 ht1 =>
    have hq_ne : edgeProj hT d q ≠ (t : ℝ) * W.weight d.edge :=
      fun heq => hq (eq_edgePoint_of_edgeProj_eq hT ht0 ht1 heq)
    wlog hgt : (t : ℝ) * W.weight d.edge < edgeProj hT d q generalizing d t
    · rw [← edgePoint_symm d t]
      refine this d.symm (unitInterval.symm t)
        (by rw [unitInterval.coe_symm_eq]; linarith)
        (by rw [unitInterval.coe_symm_eq]; linarith)
        (by simpa only [edgePoint_symm] using hq) ?_ ?_
      all_goals rw [edgeProj_symm, unitInterval.coe_symm_eq, Dart.edge_symm]
      · exact fun heq => hq_ne (by linarith)
      · linarith [(lt_or_gt_of_ne hq_ne).resolve_right hgt]
    exact exists_stem_segment_of_dart hT ht1 hgt

end TreeMedian

end MetricGraph

end SimpleGraph
