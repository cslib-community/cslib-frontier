/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/Maps.lean`)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Non-expansive maps out of metric graphs

A map `f : MetricGraph W → α` from a finite metric graph into a pseudometric space is globally
`1`-Lipschitz as soon as it is `1`-Lipschitz along every individual edge segment.

## Main results

* `SimpleGraph.MetricGraph.dist_map_le_of_edgePoint_dist_le`:
  `dist (f p) (f q) ≤ dist p q` whenever
  `dist (f (edgePoint d s)) (f (edgePoint d t)) ≤ |(s : ℝ) - t| * W.weight d.edge` on every dart.
-/

public section

open scoped unitInterval

namespace SimpleGraph

namespace MetricGraph

variable {V : Type*} {α : Type*} [PseudoMetricSpace α]

/-- Any map from a finite metric graph into a pseudometric space that is `1`-Lipschitz along
every edge segment is globally `1`-Lipschitz (`dist (f p) (f q) ≤ dist p q`). -/
theorem dist_map_le_of_edgePoint_dist_le [Finite V] {W : WeightedGraph V}
    (f : MetricGraph W → α)
    (hdart : ∀ (d : W.graph.Dart) (s t : unitInterval),
      dist (f (edgePoint d s)) (f (edgePoint d t)) ≤ |(s : ℝ) - t| * W.weight d.edge)
    (p q : MetricGraph W) :
    dist (f p) (f q) ≤ dist p q := by
  have hend (d : W.graph.Dart) (r : unitInterval) :
      dist (f (edgePoint d r)) (f (vertex d.fst)) ≤ (r : ℝ) * W.weight d.edge ∧
      dist (f (edgePoint d r)) (f (vertex d.snd)) ≤ (1 - (r : ℝ)) * W.weight d.edge := by
    rw [← edgePoint_zero d, ← edgePoint_one d]
    refine ⟨(hdart d r 0).trans_eq ?_, (hdart d r 1).trans_eq ?_⟩
    · rw [Set.Icc.coe_zero, sub_zero, abs_of_nonneg r.property.1]
    · rw [Set.Icc.coe_one, abs_sub_comm, abs_of_nonneg (unitInterval.one_sub_nonneg r)]
  have hvertex (u v : V) :
      dist (f (vertex u)) (f (vertex v)) ≤ dist (vertex u : MetricGraph W) (vertex v) := by
    obtain ⟨w, -, hw⟩ := exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected u v)
    rw [dist_vertex, ← hw]
    clear hw
    induction w with
    | nil => simp
    | @cons u v x hadj w' ih =>
      have hstep := (hend ⟨(u, v), hadj⟩ 1).1
      rw [edgePoint_one, Set.Icc.coe_one, one_mul, dist_comm] at hstep
      rw [walkLength_cons]
      exact (dist_triangle _ (f (vertex v)) _).trans (add_le_add hstep ih)
  -- Through either endpoint of `d₁`, then on to `q`.
  have hvia (d₁ : W.graph.Dart) (r₁ : unitInterval) (q : MetricGraph W)
      (hq : ∀ x, dist (f (vertex x)) (f q) ≤ dist (vertex x : MetricGraph W) q) :
      dist (f (edgePoint d₁ r₁)) (f q) ≤
        min ((r₁ : ℝ) * W.weight d₁.edge + dist (vertex d₁.fst : MetricGraph W) q)
          ((1 - (r₁ : ℝ)) * W.weight d₁.edge + dist (vertex d₁.snd : MetricGraph W) q) := by
    obtain ⟨h0, h1⟩ := hend d₁ r₁
    refine le_min ?_ ?_ <;> linarith [hq d₁.fst, hq d₁.snd,
      dist_triangle (f (edgePoint d₁ r₁)) (f (vertex d₁.fst)) (f q),
      dist_triangle (f (edgePoint d₁ r₁)) (f (vertex d₁.snd)) (f q)]
  have hve (x : V) (q : MetricGraph W) :
      dist (f (vertex x)) (f q) ≤ dist (vertex x : MetricGraph W) q := by
    induction q using ind_simple with
    | vertex y => exact hvertex x y
    | edgePoint d r =>
      rw [dist_comm, dist_comm (vertex x : MetricGraph W)]
      refine (hvia d r _ fun y => hvertex y x).trans_eq ?_
      rw [dist_edgePoint_vertex, dist_vertex, dist_vertex]
  induction p using ind_simple with
  | vertex x => exact hve x q
  | edgePoint d₁ r₁ =>
    induction q using ind_simple with
    | vertex y =>
      rw [dist_comm, dist_comm (edgePoint d₁ r₁ : MetricGraph W)]
      exact hve y _
    | edgePoint d₂ r₂ =>
      by_cases he : d₁.edge = d₂.edge
      · obtain ⟨r, hr⟩ : ∃ r, (edgePoint d₂ r₂ : MetricGraph W) = edgePoint d₁ r := by
          rcases (dart_edge_eq_iff d₁ d₂).mp he with rfl | rfl
          exacts [⟨r₂, rfl⟩, ⟨unitInterval.symm r₂, (edgePoint_symm d₂ r₂).symm⟩]
        rw [hr, dist_edgePoint_edgePoint_same]
        refine le_min (hdart d₁ r₁ r) ((hvia d₁ r₁ _ (hve · _)).trans_eq ?_)
        rw [dist_vertex_edgePoint, dist_vertex_edgePoint]
        simp only [← min_add_add_left, add_assoc]
      · rw [dist_edgePoint_edgePoint_of_edge_ne he]
        refine (hvia d₁ r₁ _ (hve · _)).trans_eq ?_
        rw [dist_vertex_edgePoint, dist_vertex_edgePoint]
        simp only [← min_add_add_left, add_assoc]

end MetricGraph

end SimpleGraph
