/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Moves
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceRegularization
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.VertexPlacement
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.FrozenReferencePaths
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceRecut
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.SubdivisionEmbedding
import CslibFrontier.Foundations.Geometry.FiniteLineAvoidance
import CslibFrontier.Foundations.Geometry.Polygonal.ComplexMul
import CslibFrontier.Foundations.Geometry.Polygonal.RouteParity
import CslibFrontier.Foundations.Geometry.Polygonal.AttachmentParameters
import CslibFrontier.Foundations.Geometry.Polygonal.RouteIntersectionParity
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

/-!
# Embedding necessity for the fixed-rotation query

`query_eq_true_of_positioned_frozen_embedding` starts with an embedding at the reference
vertices with literal frozen routes. It constructs comparison routes, a common axis and
switch bits to derive the frozen independent-pair equations.
`query_eq_true_of_rotation_embedding` constructs that positioned subdivision from an
original polygonal embedding realizing the prescribed rotations.
When there are no frozen subdivision edges, `query_eq_true_of_unfrozen_embedding`
places the vertices at the reference points. `query_eq_true_of_unfrozen_original_embedding`
first constructs the embedding of the indexed subdivision.

Auxiliary two-piece routes have reciprocal closed-node exclusions for independent pairs,
even when the two original drawings overlap. A common complex multiplier makes all actual
pieces nonhorizontal. Indexed segment-pair events are identified with actual contacts
before the regularization bijection converts their parity to the reference rank bit.
Both loop ends, parallel occurrences, isolates and declared vertex stars are retained.

This is original finite polygonal geometry. Move realization, Hanani–Tutte and the
converse recognition direction remain open under
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Cslib.Polygonal

private def NodesAvoid (p q : Route) : Prop :=
  ∀ k : Fin (p.segments + 1), p.point k ∉ q.support

private def EndsApart {E : Type*} (c d : E → ℂ) (e f : E) : Prop :=
  c e ≠ c f ∧ c e ≠ d f ∧ d e ≠ c f ∧ d e ≠ d f

private theorem endsApart_symm {E : Type*} {c d : E → ℂ} {e f : E}
    (h : EndsApart c d e f) : EndsApart c d f e :=
  ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩

private noncomputable def nodeSet (p : Route) : Finset ℂ :=
  Finset.univ.image p.point

private theorem mem_nodeSet (p : Route) (k : Fin (p.segments + 1)) :
    p.point k ∈ nodeSet p := Finset.mem_image_of_mem _ (Finset.mem_univ _)

private noncomputable def segmentPairs (p : Route) : Finset (ℂ × ℂ) :=
  Finset.univ.image fun j : Fin p.segments => (p.point j.castSucc, p.point j.succ)

private theorem mem_segmentPairs (p : Route) (j : Fin p.segments) :
    (p.point j.castSucc, p.point j.succ) ∈ segmentPairs p :=
  Finset.mem_image_of_mem _ (Finset.mem_univ _)

private theorem avoid_segment_of_avoid_line {c p w : ℂ} (hp : p ≠ c)
    (hw : ∀ t : ℝ, AffineMap.lineMap c p t ≠ w) : p ∉ segment ℝ c w := by
  rw [segment_eq_image_lineMap]
  rintro ⟨t, _, heq⟩
  have ht : t ≠ 0 := fun hz => hp (by simpa [hz] using heq.symm)
  refine hw t⁻¹ ?_
  rw [← heq, AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ ht, AffineMap.lineMap_apply_one]

private def auxiliaryRoute (c d w : ℂ) : Route := (Route.line c w).append d

private theorem auxiliary_start (c d w : ℂ) : (auxiliaryRoute c d w).start = c := rfl

private theorem auxiliary_finish (c d w : ℂ) : (auxiliaryRoute c d w).finish = d := by
  exact Route.endpoint_append (Route.line c w) d true

private theorem auxiliary_nodes (c d w : ℂ) (k : Fin ((auxiliaryRoute c d w).segments + 1)) :
    (auxiliaryRoute c d w).point k = c ∨ (auxiliaryRoute c d w).point k = w ∨
      (auxiliaryRoute c d w).point k = d := by
  change Fin 3 at k
  fin_cases k
  exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]

private noncomputable def forbiddenPairs (c d : ℂ) (points : Finset ℂ)
    (segments : Finset (ℂ × ℂ)) : Finset (ℂ × ℂ) :=
  (segments ∪ points.image (fun p => (c, p)) ∪ points.image (fun p => (d, p)) ∪
    {(c, d)}).filter fun p => p.1 ≠ p.2

private theorem forbidden_segment {c d : ℂ} {points : Finset ℂ}
    {segments : Finset (ℂ × ℂ)} {a b : ℂ} (hab : a ≠ b) (h : (a, b) ∈ segments) :
    (a, b) ∈ forbiddenPairs c d points segments :=
  Finset.mem_filter.mpr
    ⟨Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)), hab⟩

private theorem forbidden_left {c d p : ℂ} {points : Finset ℂ}
    {segments : Finset (ℂ × ℂ)} (hp : p ∈ points) (hc : c ≠ p) :
    (c, p) ∈ forbiddenPairs c d points segments :=
  Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))), hc⟩

private theorem forbidden_right {c d p : ℂ} {points : Finset ℂ}
    {segments : Finset (ℂ × ℂ)} (hp : p ∈ points) (hd : d ≠ p) :
    (d, p) ∈ forbiddenPairs c d points segments :=
  Finset.mem_filter.mpr
    ⟨Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)), hd⟩

private theorem forbidden_ends {c d : ℂ} {points : Finset ℂ}
    {segments : Finset (ℂ × ℂ)} (hcd : c ≠ d) :
    (c, d) ∈ forbiddenPairs c d points segments :=
  Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_singleton_self _), hcd⟩

private theorem exists_auxiliary_apex (c d : ℂ) (hcd : c ≠ d)
    (points : Finset ℂ) (segments : Finset (ℂ × ℂ)) :
    ∃ w ∈ Metric.ball ((c + d) / 2) 1,
      (∀ p ∈ forbiddenPairs c d points segments, ∀ t : ℝ,
        AffineMap.lineMap p.1 p.2 t ≠ w) ∧ w ≠ c ∧ w ≠ d := by
  classical
  obtain ⟨w, hw, hlines⟩ := Cslib.exists_mem_ball_avoiding_lines
    (fun p : forbiddenPairs c d points segments => p.val.1) (fun p => p.val.2)
    (fun p => (Finset.mem_filter.mp p.property).2) ((c + d) / 2) one_pos
  exact ⟨w, hw, fun p hp => hlines ⟨p, hp⟩,
    fun h => hlines ⟨(c, d), forbidden_ends hcd⟩ 0 (by simpa using h.symm),
    fun h => hlines ⟨(c, d), forbidden_ends hcd⟩ 1 (by simpa using h.symm)⟩

private theorem auxiliary_segment_ne {c d w : ℂ} (hc : w ≠ c) (hd : w ≠ d)
    (j : Fin (auxiliaryRoute c d w).segments) :
    (auxiliaryRoute c d w).point j.castSucc ≠ (auxiliaryRoute c d w).point j.succ := by
  change Fin 2 at j
  fin_cases j
  exacts [hc.symm, hd]

private theorem auxiliary_avoids_point {c d w p : ℂ} {points : Finset ℂ}
    {segments : Finset (ℂ × ℂ)} (hp : p ∈ points) (hc : p ≠ c) (hd : p ≠ d)
    (hw : ∀ line ∈ forbiddenPairs c d points segments, ∀ t : ℝ,
      AffineMap.lineMap line.1 line.2 t ≠ w) :
    p ∉ (auxiliaryRoute c d w).support := by
  rw [auxiliaryRoute, Route.support_append, Route.support_line, Route.finish_line]
  rintro (h | h)
  · exact avoid_segment_of_avoid_line hc (hw (c, p) (forbidden_left hp hc.symm)) h
  · apply avoid_segment_of_avoid_line hd (hw (d, p) (forbidden_right hp hd.symm))
    simpa only [segment_symm] using h

private theorem auxiliary_reciprocal {c d w : ℂ} {points : Finset ℂ}
    {segments : Finset (ℂ × ℂ)} (q : Route)
    (hpoints : ∀ k : Fin (q.segments + 1), q.point k ∈ points)
    (hsegments : ∀ j : Fin q.segments,
      (q.point j.castSucc, q.point j.succ) ∈ segments)
    (hne : ∀ j : Fin q.segments, q.point j.castSucc ≠ q.point j.succ)
    (hc : c ∉ q.support) (hd : d ∉ q.support)
    (hw : ∀ line ∈ forbiddenPairs c d points segments, ∀ t : ℝ,
      AffineMap.lineMap line.1 line.2 t ≠ w) :
    NodesAvoid (auxiliaryRoute c d w) q ∧ NodesAvoid q (auxiliaryRoute c d w) := by
  have hnot : w ∉ q.support := fun hz => by
    obtain ⟨j, t, _, heq⟩ := (q.mem_support_iff w).mp hz
    exact hw _ (forbidden_segment (hne j) (hsegments j)) t heq
  refine ⟨fun k => ?_, fun k => auxiliary_avoids_point (hpoints k)
    (fun heq => hc (heq ▸ Route.point_mem_support q k))
    (fun heq => hd (heq ▸ Route.point_mem_support q k)) hw⟩
  rcases auxiliary_nodes c d w k with heq | heq | heq <;> rw [heq]
  exacts [hc, hnot, hd]

/-- Private finite construction state; no comparison family is supplied to the public
necessity result. Vertex avoidance includes isolates and every future edge endpoint. -/
private structure AuxiliaryOn {E : Type*} [Fintype E] [DecidableEq E]
    (c d : E → ℂ) (R : E × Bool → Route) (V : Finset ℂ) (s : Finset E) where
  apex : E → ℂ
  apex_ball : ∀ e ∈ s, apex e ∈ Metric.ball ((c e + d e) / 2) 1
  apex_ne : ∀ e ∈ s, apex e ≠ c e ∧ apex e ≠ d e
  vertices : ∀ e ∈ s, ∀ z ∈ V, z ≠ c e → z ≠ d e →
    z ∉ (auxiliaryRoute (c e) (d e) (apex e)).support
  old : ∀ e ∈ s, ∀ k : E × Bool, EndsApart c d e k.1 →
    NodesAvoid (auxiliaryRoute (c e) (d e) (apex e)) (R k) ∧
      NodesAvoid (R k) (auxiliaryRoute (c e) (d e) (apex e))
  pairs : ∀ e ∈ s, ∀ f ∈ s, EndsApart c d e f →
    NodesAvoid (auxiliaryRoute (c e) (d e) (apex e))
      (auxiliaryRoute (c f) (d f) (apex f))

private theorem auxiliaryOn_empty {E : Type*} [Fintype E] [DecidableEq E]
    (c d : E → ℂ) (R : E × Bool → Route) (V : Finset ℂ) :
    Nonempty (AuxiliaryOn c d R V ∅) := by
  refine ⟨⟨fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> simp

private theorem auxiliaryOn_insert {E : Type*} [Fintype E] [DecidableEq E]
    (c d : E → ℂ) (R : E × Bool → Route) (V : Finset ℂ)
    (hcV : ∀ e, c e ∈ V) (hdV : ∀ e, d e ∈ V) (hcd : ∀ e, c e ≠ d e)
    (hR : ∀ k, (R k).IsSimple)
    (hclean : ∀ e k, EndsApart c d e k.1 → c e ∉ (R k).support ∧ d e ∉ (R k).support)
    {s : Finset E} (A : AuxiliaryOn c d R V s) (e : E) (he : e ∉ s) :
    Nonempty (AuxiliaryOn c d R V (insert e s)) := by
  classical
  let H (f : E) := auxiliaryRoute (c f) (d f) (A.apex f)
  let points := (V ∪ Finset.univ.biUnion (fun k : E × Bool => nodeSet (R k))) ∪
    s.biUnion (fun f => nodeSet (H f))
  let segments := Finset.univ.biUnion (fun k : E × Bool => segmentPairs (R k)) ∪
    s.biUnion (fun f => segmentPairs (H f))
  obtain ⟨w, hwball, hw, hwc, hwd⟩ := exists_auxiliary_apex (c e) (d e) (hcd e)
    points segments
  have hV (z : ℂ) (hz : z ∈ V) : z ∈ points :=
    Finset.mem_union_left _ (Finset.mem_union_left _ hz)
  have hRnodes (k : E × Bool) (j : Fin ((R k).segments + 1)) : (R k).point j ∈ points :=
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, mem_nodeSet _ _⟩))
  have hRsegs (k : E × Bool) (j : Fin (R k).segments) :
      ((R k).point j.castSucc, (R k).point j.succ) ∈ segments :=
    Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨k, Finset.mem_univ _, mem_segmentPairs _ _⟩)
  have hHnodes (f : E) (hf : f ∈ s) (j : Fin ((H f).segments + 1)) :
      (H f).point j ∈ points :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨f, hf, mem_nodeSet _ _⟩)
  have hHsegs (f : E) (hf : f ∈ s) (j : Fin (H f).segments) :
      ((H f).point j.castSucc, (H f).point j.succ) ∈ segments :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨f, hf, mem_segmentPairs _ _⟩)
  have hnewR (k : E × Bool) (hind : EndsApart c d e k.1) :
      NodesAvoid (auxiliaryRoute (c e) (d e) w) (R k) ∧
        NodesAvoid (R k) (auxiliaryRoute (c e) (d e) w) :=
    auxiliary_reciprocal (R k) (hRnodes k) (hRsegs k)
      (fun j => (hR k).segment_ne j) (hclean e k hind).1 (hclean e k hind).2 hw
  have hnewH (f : E) (hf : f ∈ s) (hind : EndsApart c d e f) :
      NodesAvoid (auxiliaryRoute (c e) (d e) w) (H f) ∧
        NodesAvoid (H f) (auxiliaryRoute (c e) (d e) w) := by
    apply auxiliary_reciprocal (H f) (hHnodes f hf) (hHsegs f hf)
      (auxiliary_segment_ne (A.apex_ne f hf).1 (A.apex_ne f hf).2)
    · exact A.vertices f hf _ (hcV e) hind.1 hind.2.1
    · exact A.vertices f hf _ (hdV e) hind.2.2.1 hind.2.2.2
    · exact hw
  let apex := Function.update A.apex e w
  have hupe : apex e = w := Function.update_self ..
  have hupd (f : E) (hf : f ∈ s) : apex f = A.apex f :=
    Function.update_of_ne (fun (h : f = e) => he (h ▸ hf)) ..
  refine ⟨⟨apex, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> simp only [Finset.forall_mem_insert]
  · exact ⟨hupe ▸ hwball, fun f hf => hupd f hf ▸ A.apex_ball f hf⟩
  · exact ⟨hupe ▸ ⟨hwc, hwd⟩, fun f hf => hupd f hf ▸ A.apex_ne f hf⟩
  · exact ⟨fun z hz hzc hzd => hupe ▸ auxiliary_avoids_point (hV z hz) hzc hzd hw,
      fun f hf => hupd f hf ▸ A.vertices f hf⟩
  · exact ⟨fun k hind => hupe ▸ hnewR k hind, fun f hf => hupd f hf ▸ A.old f hf⟩
  · refine ⟨⟨fun hind => absurd rfl hind.1, fun g hg hind => ?_⟩,
      fun f hf => ⟨fun hind => ?_, fun g hg hind => ?_⟩⟩
    · rw [hupe, hupd g hg]; exact (hnewH g hg hind).1
    · rw [hupe, hupd f hf]; exact (hnewH f hf (endsApart_symm hind)).2
    · rw [hupd f hf, hupd g hg]; exact A.pairs f hf g hg hind

private theorem exists_auxiliaryOn {E : Type*} [Fintype E] [DecidableEq E]
    (c d : E → ℂ) (R : E × Bool → Route) (V : Finset ℂ)
    (hcV : ∀ e, c e ∈ V) (hdV : ∀ e, d e ∈ V) (hcd : ∀ e, c e ≠ d e)
    (hR : ∀ k, (R k).IsSimple)
    (hclean : ∀ e k, EndsApart c d e k.1 → c e ∉ (R k).support ∧ d e ∉ (R k).support) :
    Nonempty (AuxiliaryOn c d R V Finset.univ) := by
  suffices ∀ s : Finset E, Nonempty (AuxiliaryOn c d R V s) from this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => exact auxiliaryOn_empty c d R V
  | insert e s he ih =>
    exact ih.elim fun A => auxiliaryOn_insert c d R V hcV hdV hcd hR hclean A e he

private theorem nodesAvoid_mul {p q : Route} (h : NodesAvoid p q) {u : ℂ} (hu : u ≠ 0) :
    NodesAvoid (Route.mulComplex u p) (Route.mulComplex u q) := by
  intro k
  change u * p.point k ∉ (Route.mulComplex u q).support
  have hinj : Function.Injective (fun z => u * z) := fun _ _ => mul_left_cancel₀ hu
  simpa only [Route.support_mulComplex, hinj.mem_set_image] using h k

private def cycleStart (u : ℂ) (p q : Route) : Fin p.segments ⊕ Fin q.segments → ℂ :=
  Sum.elim (fun i => u * p.point i.castSucc) (fun i => u * q.point i.castSucc)

private def cycleFinish (u : ℂ) (p q : Route) : Fin p.segments ⊕ Fin q.segments → ℂ :=
  Sum.elim (fun i => u * p.point i.succ) (fun i => u * q.point i.succ)

private noncomputable def cycleRay (u : ℂ) (p q : Route) (z : ℂ) : Bool :=
  rayParity (cycleStart u p q) (cycleFinish u p q) (fun _ => true) (u * z)

private theorem cycleRay_eq (u : ℂ) (p q : Route) (z : ℂ) :
    cycleRay u p q z = p.rayParity u z + q.rayParity u z := by
  classical
  unfold cycleRay Route.rayParity
  dsimp only [cycleStart, cycleFinish, Sum.elim_inl, Sum.elim_inr, rayParity]
  exact Fintype.sum_sum_type _

private theorem cycle_even (u : ℂ) (p q : Route) (hs : p.start = q.start)
    (hf : p.finish = q.finish) (z : ℂ) :
    (∑ i : Fin p.segments ⊕ Fin q.segments,
      ((if cycleStart u p q i = z then (true : Bool) else 0) +
        (if cycleFinish u p q i = z then true else 0))) = false := by
  classical
  rw [Fintype.sum_sum_type]
  change (∑ i : Fin p.segments,
      ((if u * p.point i.castSucc = z then (true : Bool) else 0) +
        (if u * p.point i.succ = z then true else 0))) +
    (∑ i : Fin q.segments,
      ((if u * q.point i.castSucc = z then (true : Bool) else 0) +
        (if u * q.point i.succ = z then true else 0))) = false
  rw [Route.sum_segment_endpoint_incidence, Route.sum_segment_endpoint_incidence, hs, hf,
    BooleanRing.add_self]
  rfl

private theorem cycle_observe {p q r : Route} {u : ℂ} (hu : u ≠ 0)
    (hs : p.start = q.start) (hf : p.finish = q.finish)
    (hp : ∀ i : Fin p.segments, (u * p.point i.castSucc).im ≠ (u * p.point i.succ).im)
    (hq : ∀ i : Fin q.segments, (u * q.point i.castSucc).im ≠ (u * q.point i.succ).im)
    (hr : ∀ i : Fin r.segments, (u * r.point i.castSucc).im ≠ (u * r.point i.succ).im)
    (hpr : NodesAvoid p r) (hqr : NodesAvoid q r)
    (hrp : NodesAvoid r p) (hrq : NodesAvoid r q) :
    cycleRay u p q r.finish + cycleRay u p q r.start =
      p.intersectionParity r + q.intersectionParity r := by
  classical
  have hpr' := nodesAvoid_mul hpr hu
  have hqr' := nodesAvoid_mul hqr hu
  have hrp' := nodesAvoid_mul hrp hu
  have hrq' := nodesAvoid_mul hrq hu
  have h := Route.rayParity_endpoints_add_eq_sum_intersections
    (cycleStart u p q) (cycleFinish u p q) (fun _ => true) (Route.mulComplex u r)
    (by intro i; cases i with | inl i => exact hp i | inr i => exact hq i)
    hr
    (by
      intro k i _ hz
      cases i with
      | inl i => exact hrp' k (Set.mem_iUnion.mpr ⟨i, hz⟩)
      | inr i => exact hrq' k (Set.mem_iUnion.mpr ⟨i, hz⟩))
    (by
      intro i _
      cases i with
      | inl i => exact ⟨hpr' i.castSucc, hpr' i.succ⟩
      | inr i => exact ⟨hqr' i.castSucc, hqr' i.succ⟩)
    (cycle_even u p q hs hf)
  change cycleRay u p q r.finish + cycleRay u p q r.start =
    ∑ j : Fin r.segments, ∑ i : Fin p.segments ⊕ Fin q.segments,
      decide ((openSegment ℝ (cycleStart u p q i) (cycleFinish u p q i) ∩
        openSegment ℝ (u * r.point j.castSucc) (u * r.point j.succ)).Nonempty) at h
  simp only [Fintype.sum_sum_type, cycleStart, cycleFinish, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_add_distrib] at h
  refine h.trans ?_
  rw [← Route.intersectionParity_mulComplex p r hu, ← Route.intersectionParity_mulComplex q r hu]
  exact congrArg₂ (· + ·) Finset.sum_comm Finset.sum_comm

private theorem comparison_row {p q h k : Route} {u : ℂ} (hu : u ≠ 0)
    (hsp : p.start = h.start) (hfp : p.finish = h.finish)
    (hsq : q.start = k.start) (hfq : q.finish = k.finish)
    (hp : ∀ i : Fin p.segments, (u * p.point i.castSucc).im ≠ (u * p.point i.succ).im)
    (hq : ∀ i : Fin q.segments, (u * q.point i.castSucc).im ≠ (u * q.point i.succ).im)
    (hh : ∀ i : Fin h.segments, (u * h.point i.castSucc).im ≠ (u * h.point i.succ).im)
    (hk : ∀ i : Fin k.segments, (u * k.point i.castSucc).im ≠ (u * k.point i.succ).im)
    (hpq : NodesAvoid p q) (hqp : NodesAvoid q p)
    (hhq : NodesAvoid h q) (hqh : NodesAvoid q h)
    (hhk : NodesAvoid h k) (hkh : NodesAvoid k h) :
    Route.intersectionParity p q + Route.intersectionParity h k =
      cycleRay u p h q.start + cycleRay u p h q.finish +
        cycleRay u q k p.start + cycleRay u q k p.finish := by
  have h1 := cycle_observe hu hsp hfp hp hh hq hpq hhq hqp hqh
  have h2 := cycle_observe hu hsq hfq hq hk hh hqh hkh hhq hhk
  rw [← hsp, ← hfp, Route.intersectionParity_symm q h, Route.intersectionParity_symm k h] at h2
  have hsum := congrArg₂ (fun a b : Bool => a + b) h1 h2
  convert hsum.symm using 1 <;>
    abel_nf; simp only [two_zsmul, BooleanRing.add_self, add_zero]

private theorem exists_comparison_axis {E : Type*} [Finite E]
    (c d : E → ℂ) (P Q : E → Route) (V : Finset ℂ)
    (hcV : ∀ e, c e ∈ V) (hdV : ∀ e, d e ∈ V) (hcd : ∀ e, c e ≠ d e)
    (hP : ∀ e, (P e).IsSimple) (hQ : ∀ e, (Q e).IsSimple)
    (hPs : ∀ e, (P e).start = c e) (hPf : ∀ e, (P e).finish = d e)
    (hQs : ∀ e, (Q e).start = c e) (hQf : ∀ e, (Q e).finish = d e)
    (hPP : ∀ e f, EndsApart c d e f → NodesAvoid (P e) (P f))
    (hQQ : ∀ e f, EndsApart c d e f → NodesAvoid (Q e) (Q f)) :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ e f, EndsApart c d e f →
      cycleRay u (P e) (Q e) (c f) + cycleRay u (P e) (Q e) (d f) +
        cycleRay u (P f) (Q f) (c e) + cycleRay u (P f) (Q f) (d e) =
          Route.intersectionParity (P e) (P f) + Route.intersectionParity (Q e) (Q f) := by
  classical
  let _ := Fintype.ofFinite E
  let R (k : E × Bool) := if k.2 then Q k.1 else P k.1
  have hR : ∀ k : E × Bool, (R k).IsSimple := fun ⟨e, b⟩ => Bool.casesOn b (hP e) (hQ e)
  have hRs : ∀ k : E × Bool, (R k).start = c k.1 := fun ⟨e, b⟩ => Bool.casesOn b (hPs e) (hQs e)
  have hRf : ∀ k : E × Bool, (R k).finish = d k.1 := fun ⟨e, b⟩ => Bool.casesOn b (hPf e) (hQf e)
  have hRR (e f : E) (b : Bool) (hind : EndsApart c d e f) :
      NodesAvoid (R (e, b)) (R (f, b)) := Bool.casesOn b (hPP e f hind) (hQQ e f hind)
  have hclean (e : E) (k : E × Bool) (hind : EndsApart c d e k.1) :
      c e ∉ (R k).support ∧ d e ∉ (R k).support := by
    have hnodes := hRR e k.1 k.2 hind
    constructor
    · simpa only [← hRs (e, k.2), Route.start] using hnodes 0
    · simpa only [← hRf (e, k.2), Route.finish] using hnodes (Fin.last (R (e, k.2)).segments)
  obtain ⟨A⟩ := exists_auxiliaryOn c d R V hcV hdV hcd hR hclean
  let H (e : E) := auxiliaryRoute (c e) (d e) (A.apex e)
  let F : (E × Bool) ⊕ E → Route := Sum.elim R H
  have hne (k : (E × Bool) ⊕ E) (j : Fin (F k).segments) :
      (F k).point j.castSucc ≠ (F k).point j.succ := by
    cases k with
    | inl k => exact (hR k).segment_ne j
    | inr e =>
      exact auxiliary_segment_ne (A.apex_ne e (Finset.mem_univ _)).1
        (A.apex_ne e (Finset.mem_univ _)).2 j
  obtain ⟨u, hu, hheight⟩ := Route.exists_mul_im_ne_of_segments_ne F hne
  have hRH (e f : E) (b : Bool) (hind : EndsApart c d e f) :
      NodesAvoid (H e) (R (f, b)) ∧ NodesAvoid (R (f, b)) (H e) :=
    A.old e (Finset.mem_univ _) (f, b) hind
  have hHH (e f : E) (hind : EndsApart c d e f) : NodesAvoid (H e) (H f) :=
    A.pairs e (Finset.mem_univ _) f (Finset.mem_univ _) hind
  refine ⟨u, hu, fun e f hind => ?_⟩
  have hrev := endsApart_symm hind
  have hrow (b : Bool) := comparison_row hu
    ((hRs (e, b)).trans (auxiliary_start _ _ _).symm)
    ((hRf (e, b)).trans (auxiliary_finish _ _ _).symm)
    ((hRs (f, b)).trans (auxiliary_start _ _ _).symm)
    ((hRf (f, b)).trans (auxiliary_finish _ _ _).symm)
    (hheight (.inl (e, b))) (hheight (.inl (f, b)))
    (hheight (.inr e)) (hheight (.inr f))
    (hRR e f b hind) (hRR f e b hrev)
    (hRH e f b hind).1 (hRH e f b hind).2 (hHH e f hind) (hHH f e hrev)
  have hsum := congrArg₂ (· + ·)
    (by simpa only [R, Bool.false_eq_true, ↓reduceIte, hPs, hPf] using hrow false)
    (by simpa only [R, ↓reduceIte, hQs, hQf] using hrow true)
  simp only [cycleRay_eq] at hsum ⊢
  convert hsum.symm using 1 <;>
    abel_nf <;> simp only [two_zsmul, BooleanRing.add_self, add_zero]

private theorem open_index_unique {p : Route} (hp : p.IsSimple) (hopen : p.start ≠ p.finish)
    (i j : Fin p.segments) {s t : ℝ} (hs : s ∈ Set.Ioo 0 1) (ht : t ∈ Set.Ioo 0 1)
    (heq : p.eval i s = p.eval j t) : i = j := by
  have hpos := hp.position_eq_of_eval_eq hopen i j ⟨hs.1.le, hs.2.le⟩
    ⟨ht.1.le, ht.2.le⟩ heq
  dsimp only [Route.position] at hpos
  have hij : i.val < j.val + 1 := by exact_mod_cast (by linarith [hs.1, ht.2] : (i : ℝ) < j + 1)
  have hji : j.val < i.val + 1 := by exact_mod_cast (by linarith [ht.1, hs.2] : (j : ℝ) < i + 1)
  exact Fin.ext (by omega)

private theorem nodesAvoid_of_open_contacts {p q : Route} (hp : p.IsSimple)
    (hopen : p.start ≠ p.finish)
    (hcontacts : ∀ z ∈ p.support, z ∈ q.support →
      ∃ i : Fin p.segments, ∃ t ∈ Set.Ioo (0 : ℝ) 1, p.eval i t = z) :
    NodesAvoid p q := by
  have hno (n : ℕ) (i : Fin p.segments) (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
      (n : ℝ) ≠ p.position i t := by
    intro h
    dsimp only [Route.position] at h
    have h1 : i.val < n := by exact_mod_cast (show (i.val : ℝ) < n by linarith [ht.1])
    have h2 : n < i.val + 1 := by
      exact_mod_cast (show (n : ℝ) < (i.val : ℝ) + 1 by linarith [ht.2])
    omega
  intro k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · intro hq
    obtain ⟨i, t, ht, heq⟩ := hcontacts _ (Route.point_mem_support p _) hq
    have hpos := hp.position_eq_of_eval_eq hopen (Fin.last p.bends) i (by norm_num)
      ⟨ht.1.le, ht.2.le⟩ ((by simp [Route.eval] : p.eval (Fin.last p.bends) 1 = _).trans heq.symm)
    exact hno p.segments i t ht (by simpa [Route.position, Route.segments, Nat.cast_add] using hpos)
  · intro hq
    obtain ⟨i, t, ht, heq⟩ := hcontacts _ (Route.point_mem_support p _) hq
    have hpos := hp.position_eq_of_eval_eq hopen j i (by norm_num) ⟨ht.1.le, ht.2.le⟩
      ((by simp [Route.eval] : p.eval j 0 = _).trans heq.symm)
    exact hno j.val i t ht (by simpa only [Route.position, add_zero] using hpos)

private theorem endsApart_false_of_endpoint_eq {E : Type*} {c d : E → ℂ} {e f : E}
    (h : EndsApart c d e f) (a b : Bool)
    (heq : (if a then d e else c e) = if b then d f else c f) : False := by
  cases a <;> cases b
  exacts [h.1 heq, h.2.1 heq, h.2.2.1 heq, h.2.2.2 heq]

private theorem contact_away_of_vertex_contacts {G : Graph} (D : PolygonalDrawing G)
    (hvc : ∀ e (i : Fin (D.route e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      ∀ v ∈ G.vertices, (D.route e).eval i t = D.vertex v →
        ∃ b, (D.route e).AtEnd i t b ∧ Dart.vertex (e, b) = v)
    (c d : Fin G.edges.length → ℂ)
    (hs : ∀ e, (D.route e).start = c e) (hf : ∀ e, (D.route e).finish = d e)
    (e f : Fin G.edges.length) (hind : EndsApart c d e f) {z : ℂ}
    (he : z ∈ (D.route e).support) (hg : z ∈ (D.route f).support) :
    ∀ v ∈ G.vertices, z ≠ D.vertex v := by
  intro v hv hz
  obtain ⟨i, s, his, hez⟩ := ((D.route e).mem_support_iff z).mp he
  obtain ⟨j, t, hjt, hfz⟩ := ((D.route f).mem_support_iff z).mp hg
  obtain ⟨a, _, hav⟩ := hvc e i s his v hv (hez.trans hz)
  obtain ⟨b, _, hbv⟩ := hvc f j t hjt v hv (hfz.trans hz)
  apply endsApart_false_of_endpoint_eq hind a b
  have hend := (D.endpoint_eq e a).trans
    ((congrArg D.vertex (hav.trans hbv.symm)).trans (D.endpoint_eq f b).symm)
  simpa only [Route.endpoint, hs, hf] using hend

private theorem embedding_nodesAvoid {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (c d : Fin G.edges.length → ℂ)
    (hs : ∀ e, (D.route e).start = c e) (hf : ∀ e, (D.route e).finish = d e)
    (e f : Fin G.edges.length) (hind : EndsApart c d e f) :
    NodesAvoid (D.route e) (D.route f) := by
  have hef : e ≠ f := by intro h; subst f; exact hind.1 rfl
  intro k hz
  let z := (D.route e).point k
  obtain ⟨i, s, his, hez⟩ := ((D.route e).mem_support_iff z).mp (Route.point_mem_support _ _)
  obtain ⟨j, t, hjt, hfz⟩ := ((D.route f).mem_support_iff z).mp hz
  obtain ⟨a, b, _, _, hab⟩ := hD.edge_contacts e f hef i j s t his hjt
    (hez.trans hfz.symm)
  apply endsApart_false_of_endpoint_eq hind a b
  have hend := (D.endpoint_eq e a).trans
    ((congrArg D.vertex hab).trans (D.endpoint_eq f b).symm)
  simpa only [Route.endpoint, hs, hf] using hend

open Classical in
private theorem pairParity_eq_card_events (p q : Route) :
    Route.intersectionParity p q = (Fintype.card {ij : Fin p.segments × Fin q.segments //
      (openSegment ℝ (p.point ij.1.castSucc) (p.point ij.1.succ) ∩
        openSegment ℝ (q.point ij.2.castSucc) (q.point ij.2.succ)).Nonempty} : Bool) := by
  classical
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Fintype.sum_prod_type]
  unfold Route.intersectionParity
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (openSegment ℝ (p.point i.castSucc) (p.point i.succ) ∩
      openSegment ℝ (q.point j.castSucc) (q.point j.succ)).Nonempty <;>
    simp [h, ← Bool.one_eq_true, Bool.zero_eq_false]

open Classical in
private theorem event_contact_equiv (p q : Route) (T : Set ℂ)
    (hp : p.IsSimple) (hq : q.IsSimple) (hpo : p.start ≠ p.finish) (hqo : q.start ≠ q.finish)
    (hT : ∀ z, z ∈ T ↔ z ∈ p.support ∧ z ∈ q.support)
    (hsub : T.Subsingleton)
    (hopen : ∀ z ∈ T, ∃ (i : Fin p.segments) (j : Fin q.segments) (s t : ℝ),
      s ∈ Set.Ioo 0 1 ∧ t ∈ Set.Ioo 0 1 ∧ p.eval i s = z ∧ q.eval j t = z) :
    Nonempty ({ij : Fin p.segments × Fin q.segments //
      (openSegment ℝ (p.point ij.1.castSucc) (p.point ij.1.succ) ∩
        openSegment ℝ (q.point ij.2.castSucc) (q.point ij.2.succ)).Nonempty} ≃ T) := by
  classical
  let Event := {ij : Fin p.segments × Fin q.segments //
    (openSegment ℝ (p.point ij.1.castSucc) (p.point ij.1.succ) ∩
      openSegment ℝ (q.point ij.2.castSucc) (q.point ij.2.succ)).Nonempty}
  let point (a : Event) : ℂ := Classical.choose a.property
  have hpoint (a : Event) :
      point a ∈ openSegment ℝ (p.point a.val.1.castSucc) (p.point a.val.1.succ) ∧
      point a ∈ openSegment ℝ (q.point a.val.2.castSucc) (q.point a.val.2.succ) :=
    Classical.choose_spec a.property
  let toPoint (a : Event) : T := ⟨point a, (hT _).mpr
    ⟨Set.mem_iUnion.mpr ⟨a.val.1, openSegment_subset_segment ℝ _ _ (hpoint a).1⟩,
      Set.mem_iUnion.mpr ⟨a.val.2, openSegment_subset_segment ℝ _ _ (hpoint a).2⟩⟩⟩
  have hinj : Function.Injective toPoint := fun a b hab => by
    obtain ⟨⟨s, hs, hps⟩, ⟨t, ht, hqt⟩⟩ := by
      simpa only [openSegment_eq_image_lineMap, Set.mem_image] using hpoint a
    obtain ⟨⟨s', hs', hps'⟩, ⟨t', ht', hqt'⟩⟩ := by
      simpa only [openSegment_eq_image_lineMap, Set.mem_image] using hpoint b
    have hab' : point a = point b := congrArg Subtype.val hab
    exact Subtype.ext (Prod.ext
      (open_index_unique hp hpo _ _ hs hs' (hps.trans (hab'.trans hps'.symm)))
      (open_index_unique hq hqo _ _ ht ht' (hqt.trans (hab'.trans hqt'.symm))))
  have hsurj : Function.Surjective toPoint := fun z => by
    obtain ⟨i, j, s, t, hs, ht, hps, hqt⟩ := hopen z.val z.property
    let a : Event := ⟨(i, j), ⟨z.val,
      hps ▸ lineMap_mem_openSegment ℝ _ _ hs,
      hqt ▸ lineMap_mem_openSegment ℝ _ _ ht⟩⟩
    exact ⟨a, Subtype.ext (hsub (toPoint a).property z.property)⟩
  exact ⟨Equiv.ofBijective toPoint ⟨hinj, hsurj⟩⟩

open Classical in
private theorem pairParity_of_subsingleton_contacts (p q : Route) (T : Set ℂ)
    (hp : p.IsSimple) (hq : q.IsSimple) (hpo : p.start ≠ p.finish) (hqo : q.start ≠ q.finish)
    (hT : ∀ z, z ∈ T ↔ z ∈ p.support ∧ z ∈ q.support)
    (hsub : T.Subsingleton)
    (hopen : ∀ z ∈ T, ∃ (i : Fin p.segments) (j : Fin q.segments) (s t : ℝ),
      s ∈ Set.Ioo 0 1 ∧ t ∈ Set.Ioo 0 1 ∧ p.eval i s = z ∧ q.eval j t = z) :
    Route.intersectionParity p q = decide T.Nonempty := by
  classical
  let _ := hsub.finite.fintype
  obtain ⟨eqv⟩ := event_contact_equiv p q T hp hq hpo hqo hT hsub hopen
  rw [pairParity_eq_card_events, Fintype.card_congr eqv]
  by_cases ht : T.Nonempty
  · obtain ⟨z, hz⟩ := ht
    let _ : Unique T := ⟨⟨z, hz⟩, fun a => Subtype.ext (hsub a.property hz)⟩
    have ht' : T.Nonempty := ⟨z, hz⟩
    simp only [Fintype.card_unique, Nat.cast_one, ht', decide_true, Bool.one_eq_true]
  · let _ : IsEmpty T := ⟨fun a => ht ⟨a.val, a.property⟩⟩
    simp only [Fintype.card_eq_zero, Nat.cast_zero, ht, decide_false, Bool.zero_eq_false]

private theorem pairParity_embedding {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (c d : Fin G.edges.length → ℂ)
    (hs : ∀ e, (D.route e).start = c e) (hf : ∀ e, (D.route e).finish = d e)
    (e f : Fin G.edges.length) (hind : EndsApart c d e f) :
    Route.intersectionParity (D.route e) (D.route f) = 0 := by
  classical
  have hef : e ≠ f := fun h => by subst f; exact hind.1 rfl
  unfold Route.intersectionParity
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have hno : ¬(openSegment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) ∩
      openSegment ℝ ((D.route f).point j.castSucc) ((D.route f).point j.succ)).Nonempty := by
    rintro ⟨z, hp, hq⟩
    rw [openSegment_eq_image_lineMap] at hp hq
    obtain ⟨s, hs', he⟩ := hp
    obtain ⟨t, ht', hg⟩ := hq
    obtain ⟨a, b, _, _, hab⟩ := hD.edge_contacts e f hef i j s t
      ⟨hs'.1.le, hs'.2.le⟩ ⟨ht'.1.le, ht'.2.le⟩ (he.trans hg.symm)
    apply endsApart_false_of_endpoint_eq hind a b
    have hend := (D.endpoint_eq e a).trans
      ((congrArg D.vertex hab).trans (D.endpoint_eq f b).symm)
    simpa only [Route.endpoint, hs, hf] using hend
  simp only [hno, decide_false, Bool.zero_eq_false]

private theorem subdivision_end_declared {I : FixedRotationInput} (hI : Valid I)
    (e : Fin (subdivisionGraph I).edges.length) (b : Bool) :
    Dart.vertex (e, b) ∈ (subdivisionGraph I).vertices :=
  ((referenceOrder_enumerates hI).2 _).mp ((subdivision_endpoint_spec hI e).1 b)

private theorem reference_ends_apart {I : FixedRotationInput} (hI : Valid I)
    (e f : Fin (subdivisionGraph I).edges.length)
    (hind : independent ((subdivisionGraph I).edges[e])
      ((subdivisionGraph I).edges[f]) = true) :
    EndsApart (fun e => ((referenceDrawing I).route e).start)
      (fun e => ((referenceDrawing I).route e).finish) e f := by
  rw [Dart.edge_eq_vertices e, Dart.edge_eq_vertices f] at hind
  simp only [independent, Bool.and_eq_true, decide_eq_true_eq] at hind
  obtain ⟨⟨⟨h00, h01⟩, h10⟩, h11⟩ := hind
  have hn (a b : Bool) (h : Dart.vertex (e, a) ≠ Dart.vertex (f, b)) :
      (referenceDrawing I).vertex (Dart.vertex (e, a)) ≠
        (referenceDrawing I).vertex (Dart.vertex (f, b)) := by
    intro heq
    exact h (referenceDrawing_vertices_injective hI
      (subdivision_end_declared hI e a) (subdivision_end_declared hI f b) heq)
  exact ⟨hn false false h00, hn false true h01, hn true false h10, hn true true h11⟩

/-- A necessary algebraic condition for a supplied embedding already at the reference
vertices and LITERAL frozen routes. This does not place an arbitrary embedding, realize
moves, prove HT, or decide bare ordered planarity. Switch bits and comparison geometry
are constructed internally, with no caller-supplied parity or motion premise. -/
theorem query_eq_true_of_positioned_frozen_embedding {I : FixedRotationInput} (hI : Valid I)
    (D : PolygonalDrawing (subdivisionGraph I)) (hD : D.IsEmbedding)
    (hV : ∀ v ∈ (subdivisionGraph I).vertices,
      D.vertex v = (referenceDrawing I).vertex v)
    (hF : ∀ e : Fin (subdivisionGraph I).edges.length,
      ((subdivide I)[e.val]'(by
        simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true →
        D.route e = (referenceDrawing I).route e) : query I = true := by
  classical
  let G := subdivisionGraph I
  let E := Fin G.edges.length
  let ref := referenceDrawing I
  let c (e : E) := (ref.route e).start
  let d (e : E) := (ref.route e).finish
  obtain ⟨A, κ, hReg, _⟩ := exists_reference_crossing_regularization hI
  have hDs (e : E) : (D.route e).start = c e :=
    (D.endpoint_eq e false).trans (hV _ (subdivision_end_declared hI e false))
  have hDf (e : E) : (D.route e).finish = d e :=
    (D.endpoint_eq e true).trans (hV _ (subdivision_end_declared hI e true))
  have hAs (e : E) : (A.drawing.route e).start = c e :=
    (A.drawing.endpoint_eq e false).trans (congrFun A.vertex_eq _)
  have hAf (e : E) : (A.drawing.route e).finish = d e :=
    (A.drawing.endpoint_eq e true).trans (congrFun A.vertex_eq _)
  have hcd (e : E) : c e ≠ d e := by
    intro heq
    exact (subdivision_endpoint_spec hI e).2
      (referenceDrawing_vertices_injective hI (subdivision_end_declared hI e false)
        (subdivision_end_declared hI e true) heq)
  have haway (e f : E) (hind : EndsApart c d e f) (z : ℂ)
      (he : z ∈ (A.drawing.route e).support) (hf : z ∈ (A.drawing.route f).support) :
      ∀ v ∈ G.vertices, z ≠ A.drawing.vertex v :=
    contact_away_of_vertex_contacts A.drawing A.vertex_contacts c d hAs hAf e f hind he hf
  have hAproper (e f : E) (hind : EndsApart c d e f) :
      NodesAvoid (A.drawing.route e) (A.drawing.route f) := by
    have hef : e ≠ f := by intro h; subst f; exact hind.1 rfl
    apply nodesAvoid_of_open_contacts (A.simple e) (by rw [hAs, hAf]; exact hcd e)
    intro z he hf
    obtain ⟨i, j, s, t, hs, ht, heq, _, _⟩ :=
      (hReg e f hef).2.2 z ⟨he, hf, haway e f hind z he hf⟩
    exact ⟨i, s, hs, heq⟩
  let V := G.vertices.toFinset.image ref.vertex
  have hcV (e : E) : c e ∈ V :=
    Finset.mem_image.mpr ⟨_, List.mem_toFinset.mpr (subdivision_end_declared hI e false), rfl⟩
  have hdV (e : E) : d e ∈ V :=
    Finset.mem_image.mpr ⟨_, List.mem_toFinset.mpr (subdivision_end_declared hI e true), rfl⟩
  obtain ⟨u, hu, hswitch⟩ := exists_comparison_axis c d D.route A.drawing.route V
    hcV hdV hcd hD.simple A.simple hDs hDf hAs hAf
    (embedding_nodesAvoid hD c d hDs hDf) hAproper
  have hAcount (e f : E)
      (hind : independent (G.edges[e]) (G.edges[f]) = true) :
      Route.intersectionParity (A.drawing.route e) (A.drawing.route f) =
        crossing (referenceOrder I) (G.edges[e]) (G.edges[f]) := by
    have hap : EndsApart c d e f := reference_ends_apart hI e f hind
    have hef : e ≠ f := by intro h; subst f; exact hap.1 rfl
    let O := openSegment ℝ (c e) (d e) ∩ openSegment ℝ (c f) (d f)
    let T : Set ℂ := {z | z ∈ (A.drawing.route e).support ∧
      z ∈ (A.drawing.route f).support ∧ ∀ v ∈ G.vertices, z ≠ A.drawing.vertex v}
    have hb : Set.BijOn (κ e f) O T := (hReg e f hef).1
    have hO : O.Subsingleton := referenceDrawing_open_inter_subsingleton hI e f hef
    have hT : T.Subsingleton := fun z hz w hw => by
      obtain ⟨a, ha, rfl⟩ := hb.surjOn hz
      obtain ⟨b, hbb, rfl⟩ := hb.surjOn hw
      rw [hO ha hbb]
    have hTIff (z : ℂ) : z ∈ T ↔
        z ∈ (A.drawing.route e).support ∧ z ∈ (A.drawing.route f).support :=
      ⟨fun hz => ⟨hz.1, hz.2.1⟩, fun ⟨he, hf⟩ => ⟨he, hf, haway e f hap z he hf⟩⟩
    have hOpen (z : ℂ) (hz : z ∈ T) :
        ∃ (i : Fin (A.drawing.route e).segments) (j : Fin (A.drawing.route f).segments)
          (s t : ℝ), s ∈ Set.Ioo 0 1 ∧ t ∈ Set.Ioo 0 1 ∧
          (A.drawing.route e).eval i s = z ∧ (A.drawing.route f).eval j t = z := by
      obtain ⟨i, j, s, t, hs, ht, heq, hfq, _⟩ := (hReg e f hef).2.2 z hz
      exact ⟨i, j, s, t, hs, ht, heq, hfq⟩
    rw [pairParity_of_subsingleton_contacts _ _ T (A.simple e) (A.simple f)
      (by rw [hAs, hAf]; exact hcd e) (by rw [hAs, hAf]; exact hcd f) hTIff hT hOpen]
    have hcross := referenceDrawing_crossing_iff hI e f hind
    exact Bool.eq_iff_iff.2 (decide_eq_true_iff.trans ((hb.image_eq ▸ Set.image_nonempty).trans
      ⟨fun ⟨z, hz⟩ => hcross.2 ⟨z, hz, fun w hw => hO hw hz⟩,
        fun h => (hcross.1 h).imp fun _ => And.left⟩))
  let F := frame I
  let index (e : Fin F.segments.length) : E :=
    ⟨e.val, by simpa only [F, frame, G, subdivisionGraph, List.length_map] using e.isLt⟩
  let moves : Moves F := fun e v =>
    cycleRay u (D.route (index e)) (A.drawing.route (index e)) (ref.vertex v.val)
  have hfrozen : FrozenMoves F moves := by
    intro e v he
    have he' : ((subdivide I)[(index e).val]'(by
        simpa only [G, subdivisionGraph, List.length_map] using (index e).isLt)).frozen = true := by
      change ((subdivide I).getD e.val ((0, 0), false)).frozen = true at he
      rw [List.getD_eq_getElem _ _ (show e.val < (subdivide I).length from e.isLt)] at he
      exact he
    have hkeep := A.route_eq (index e)
    dsimp only at hkeep
    simp only [he', ↓reduceIte] at hkeep
    change cycleRay u (D.route (index e)) (A.drawing.route (index e)) (ref.vertex v.val) = false
    rw [hF (index e) he', hkeep, cycleRay_eq, BooleanRing.add_self]
    rfl
  have hvalue (x : Segment × ℕ) (hix : x.2 < F.segments.length)
      (hx : F.segments.getD x.2 ((0, 0), false) = x.1)
      (v : ℕ) (hv : v < F.vertexCount) :
      finiteMoveValue F moves x v = readMove F moves x.2 v := by
    by_cases hfixed : x.1.frozen = true
    · have hz := hfrozen ⟨x.2, hix⟩ ⟨v, hv⟩ (by simpa only [hx] using hfixed)
      simp only [finiteMoveValue, hfixed, ↓reduceIte, readMove, hix, hv, dite_true, hz]
    · have hfalse : x.1.frozen = false := Bool.eq_false_iff.mpr hfixed
      simp only [finiteMoveValue, hfalse, Bool.false_eq_true, ↓reduceIte]
  have hequations : MoveEquations F moves := by
    intro e he f hf _ hind
    obtain ⟨helt, heStored⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp he)
    obtain ⟨hflt, hfStored⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hf)
    have heget : F.segments.getD e.2 ((0, 0), false) = e.1 := by
      rw [List.getD_eq_getElem _ _ helt, heStored]
    have hfget : F.segments.getD f.2 ((0, 0), false) = f.1 := by
      rw [List.getD_eq_getElem _ _ hflt, hfStored]
    have hem : e.1 ∈ F.segments := heStored ▸ List.getElem_mem helt
    have hfm : f.1 ∈ F.segments := hfStored ▸ List.getElem_mem hflt
    have eb : e.1.source < F.vertexCount ∧ e.1.target < F.vertexCount :=
      boundedEndpoints_frame hI e.1 hem
    have fb : f.1.source < F.vertexCount ∧ f.1.target < F.vertexCount :=
      boundedEndpoints_frame hI f.1 hfm
    let ei := index ⟨e.2, helt⟩
    let fi := index ⟨f.2, hflt⟩
    have hends {x : Segment × ℕ} (hxlt : x.2 < F.segments.length)
        (hxS : F.segments[x.2] = x.1) :
        let xi := index ⟨x.2, hxlt⟩
        G.edges[xi] = x.1.endpoints ∧
          c xi = ref.vertex x.1.source ∧ d xi = ref.vertex x.1.target := by
      intro xi
      have hxE : G.edges[xi] = x.1.endpoints := by
        change ((subdivide I).map Segment.endpoints)[x.2]'
          (by simpa only [List.length_map, F, frame] using hxlt) = x.1.endpoints
        exact (List.getElem_map _).trans (congrArg Segment.endpoints hxS)
      have hv := (Dart.edge_eq_vertices xi).symm.trans hxE
      exact ⟨hxE, congrArg ref.vertex (congrArg Prod.fst hv),
        congrArg ref.vertex (congrArg Prod.snd hv)⟩
    obtain ⟨heEdge, hce, hde⟩ := hends helt heStored
    obtain ⟨hfEdge, hcf, hdf⟩ := hends hflt hfStored
    have hind' : independent (G.edges[ei]) (G.edges[fi]) = true := by
      rwa [heEdge, hfEdge]
    have hap : EndsApart c d ei fi := reference_ends_apart hI ei fi hind'
    have hrow := hswitch ei fi hap
    rw [pairParity_embedding hD c d hDs hDf ei fi hap, hAcount ei fi hind', zero_add,
      hce, hde, hcf, hdf, heEdge, hfEdge] at hrow
    rw [hvalue e helt heget f.1.source fb.1, hvalue e helt heget f.1.target fb.2,
      hvalue f hflt hfget e.1.source eb.1, hvalue f hflt hfget e.1.target eb.2]
    dsimp only [ei, fi] at hrow
    change _ = crossing (referenceOrder I) e.1.endpoints f.1.endpoints
    simpa only [readMove, helt, hflt, eb.1, eb.2, fb.1, fb.2, dite_true,
      moves, index, add_assoc] using hrow
  exact (query_eq_true_iff_exists_frozen_moves I).mpr ⟨hI, moves, hfrozen, hequations⟩

/-- An actual embedding of the twice-subdivided graph makes the query accept when no
subdivision edge is frozen. The reference vertex positions are attained internally. -/
theorem query_eq_true_of_unfrozen_embedding {I : FixedRotationInput} (hI : Valid I)
    (hF : (frozenGraph I).edges = [])
    (D : PolygonalDrawing (subdivisionGraph I)) (hD : D.IsEmbedding) : query I = true := by
  obtain ⟨E, hE, hV, _, _, _, _⟩ := hD.exists_vertex_placement
    (subdivisionGraph_endpoints_declared hI)
    (referenceDrawing I).vertex (referenceDrawing_vertices_injective hI)
  apply query_eq_true_of_positioned_frozen_embedding hI E hE hV
  intro e he
  let i : Fin (subdivide I).length :=
    ⟨e.val, by simpa only [subdivisionGraph, List.length_map] using e.isLt⟩
  have hem : (subdivide I)[i].endpoints ∈ (frozenGraph I).edges :=
    List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.getElem_mem _, he⟩, rfl⟩
  rw [hF] at hem
  exact (List.not_mem_nil hem).elim

/-- An actual embedding of the original listed graph makes the query accept when no
subdivision edge is frozen. The proof subdivides the indexed routes and places all
subdivision vertices at the reference points. -/
theorem query_eq_true_of_unfrozen_original_embedding {I : FixedRotationInput} (hI : Valid I)
    (hF : (frozenGraph I).edges = [])
    (D : PolygonalDrawing I.graph) (hD : D.IsEmbedding) : query I = true := by
  obtain ⟨E, hE, _⟩ := exists_subdivision_embedding hI D hD
  exact query_eq_true_of_unfrozen_embedding hI hF E hE

/-- An embedding of the original graph that realizes the prescribed rotations makes the
fixed-rotation query accept. The proof places all subdivision vertices and restores the
literal frozen routes before deriving the move equations. -/
theorem query_eq_true_of_rotation_embedding {I : FixedRotationInput} (hI : Valid I)
    {D : PolygonalDrawing I.graph} (hD : D.IsEmbedding) {r : RotationSystem I.graph}
    (hReal : D.Realizes r) (hfixed : Realizes I r) : query I = true := by
  obtain ⟨E, hE, hcenter, hfrozen⟩ :=
    exists_subdivision_embedding_with_frozen_reference_routes hI hD hReal hfixed
  have hspoke (d : Dart I.graph) (hd : (I.orders.getD d.vertex none).isSome) :
      E.route (subdivisionDart I d).1 = (referenceDrawing I).route (subdivisionDart I d).1 :=
    hfrozen _ ((frozen_iff_exists_subdivisionDart I _).mpr ⟨d, rfl, hd⟩)
  obtain ⟨F, hF, hpos, hroute⟩ := exists_subdivision_embedding_at_reference hI hE hcenter hspoke
  apply query_eq_true_of_positioned_frozen_embedding hI F hF hpos
  intro e he
  obtain ⟨d, rfl, hd⟩ := (frozen_iff_exists_subdivisionDart I e).mp he
  exact hroute d hd

end Cslib.Complexity.Graph.RotationRecognition
