/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceDetourPlacement
public import CslibFrontier.Foundations.Geometry.Polygonal.AttachmentParameters
public import CslibFrontier.Foundations.Geometry.Polygonal.CoordinateOrder
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Chain
import CslibFrontier.Foundations.Data.List.FlatMapPositions
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Assembling ordered patches of the actual reference drawing

The actual finite reference crossing set determines disjoint neighborhoods and local
source-oriented detours. On each original indexed route the complete center list is sorted
by its source cut parameters. Free routes use a literal finite append word; frozen routes
are retained as the original single segment, including when they pass through patches.
The resulting drawing retains vertices, endpoints and vertex contacts, has simple routes,
and preserves outgoing germs up to internally proved positive factors.

## Main results

* `ReferencePatchAssembly`: named data and properties tied to one constructed drawing.
* `exists_reference_patch_assembly`: internally selected neighborhoods, complete ordered
  patches and their actual global assembly, with exact all-real local/global parameter maps.
  A free local segment has index `3*q+1+j`; a frozen cut uses the original parameter
  `α+(β-α)*t`. Reversal takes the raw first piece to the last source-oriented local piece.

This is original finite coordinate geometry. The downstream
`exists_reference_crossing_regularization` in `ReferenceRegularization` constructs an
assembly with exact pair-contact correspondence, transverse contacts and no triple supports
away from declared vertices. Parity, frozen placement, Hanani–Tutte and query/source
recognition remain open under
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Polygonal

private theorem disjoint_reference_cuts (I : FixedRotationInput)
    (e : Fin (subdivisionGraph I).edges.length) {z w : ℂ} {ρ τ α β γ δ : ℝ}
    (hαβ : α ≤ β) (hγδ : γ ≤ δ)
    (hballs : Disjoint (Metric.closedBall z ρ) (Metric.closedBall w τ))
    (hα : AffineMap.lineMap ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish α ∈ Metric.ball z ρ)
    (hβ : AffineMap.lineMap ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish β ∈ Metric.ball z ρ)
    (hγ : AffineMap.lineMap ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish γ ∈ Metric.ball w τ)
    (hδ : AffineMap.lineMap ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish δ ∈ Metric.ball w τ) :
    Disjoint (Set.Icc α β) (Set.Icc γ δ) := by
  let f : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap ((referenceDrawing I).route e).start
    ((referenceDrawing I).route e).finish
  have hz : Set.Icc α β ⊆ f ⁻¹' Metric.ball z ρ := by
    simpa only [segment_eq_Icc hαβ] using
      (Convex.affine_preimage (𝕜 := ℝ) f (convex_ball z ρ)).segment_subset hα hβ
  have hw : Set.Icc γ δ ⊆ f ⁻¹' Metric.ball w τ := by
    simpa only [segment_eq_Icc hγδ] using
      (Convex.affine_preimage (𝕜 := ℝ) f (convex_ball w τ)).segment_subset hγ hδ
  exact Set.disjoint_left.mpr fun _ ht hu => Set.disjoint_left.mp hballs
    (Metric.ball_subset_closedBall (hz ht)) (Metric.ball_subset_closedBall (hw hu))

private theorem append_word_point_order {α : Type*} [Preorder α]
    (f : ℂ → α) (a b : ℂ) (nodes : List ℂ)
    (hword : (a :: b :: nodes).Pairwise (fun x y => f x < f y)) :
    StrictMono fun k => f ((nodes.foldl Route.append (Route.line a b)).point k) := by
  refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
  have h0 := Route.eval_foldl_append_line a b nodes i 0
  have h1 := Route.eval_foldl_append_line a b nodes i 1
  simp only [Route.eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at h0 h1
  simpa only [h0, h1] using (List.pairwise_iff_getElem.mp hword) _ _ _ _ (Nat.lt_succ_self _)


private theorem sorted_reference_cuts (I : FixedRotationInput)
    (e : Fin (subdivisionGraph I).edges.length) (C : Set ℂ) (hC : C.Finite)
    (ρ : ℂ → ℝ) (α β : C → ℝ)
    (hab : ∀ z, α z < β z)
    (hdisj : C.PairwiseDisjoint fun z => Metric.closedBall z (ρ z))
    (ha : ∀ z : C, AffineMap.lineMap ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish (α z) ∈ Metric.ball z.val (ρ z.val))
    (hb : ∀ z : C, AffineMap.lineMap ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish (β z) ∈ Metric.ball z.val (ρ z.val)) :
    ∃ L : List C, L.Nodup ∧ (∀ z : C, z ∈ L) ∧
      L.Pairwise (fun z w => β z < α w) := by
  classical
  let := hC.fintype
  have hcuts {z w : C} (hne : z ≠ w) :
      Disjoint (Set.Icc (α z) (β z)) (Set.Icc (α w) (β w)) :=
    disjoint_reference_cuts I e (hab z).le (hab w).le
      (hdisj z.property w.property (fun h => hne (Subtype.ext h)))
      (ha z) (hb z) (ha w) (hb w)
  have hinj : Function.Injective α := fun z w heq => by_contra fun hne =>
    Set.disjoint_left.mp (hcuts hne) ⟨le_rfl, (hab z).le⟩ (by rw [heq]; exact ⟨le_rfl, (hab w).le⟩)
  let : LinearOrder C := LinearOrder.lift' α hinj
  refine ⟨Finset.univ.sort, Finset.sort_nodup _ _,
    fun z => (Finset.mem_sort _).mpr (Finset.mem_univ z),
    (Finset.sortedLT_sort (Finset.univ : Finset C)).pairwise.imp fun {z w} hzw =>
      by_contra fun hn => Set.disjoint_left.mp (hcuts (ne_of_lt hzw))
        ⟨(show α z < α w from hzw).le, le_of_not_gt hn⟩ ⟨le_rfl, (hab w).le⟩⟩


private theorem append_word_support (a b : ℂ) (nodes : List ℂ) (S : Set ℂ)
    (hword : (a :: b :: nodes).IsChain (fun x y => segment ℝ x y ⊆ S)) :
    (nodes.foldl Route.append (Route.line a b)).support ⊆ S := by
  intro w hw
  obtain ⟨i, t, ht, heval⟩ := (Route.mem_support_iff _ w).mp hw
  have hi : i.val + 1 < (a :: b :: nodes).length := by
    have : i.val < 1 + nodes.length := Route.segments_foldl_append (Route.line a b) nodes ▸ i.isLt
    simp only [List.length_cons]; omega
  rw [← heval, Route.eval_foldl_append_line]
  exact (List.isChain_iff_getElem.mp hword i.val hi) (lineMap_mem_segment ℝ _ _ ht)


private theorem vertex_contacts_from_support {I : FixedRotationInput} (hI : Valid I)
    (e : Fin (subdivisionGraph I).edges.length) (C : Set ℂ) (ρ : ℂ → ℝ)
    (havoid : ∀ z ∈ C, ∀ v ∈ (subdivisionGraph I).vertices,
      (referenceDrawing I).vertex v ∉ Metric.ball z (ρ z))
    (q : Route) (hq : q.IsSimple)
    (hstart : q.start = ((referenceDrawing I).route e).start)
    (hfinish : q.finish = ((referenceDrawing I).route e).finish)
    (hsupport : q.support ⊆ ((referenceDrawing I).route e).support ∪
      ⋃ z ∈ C, Metric.ball z (ρ z)) :
    ∀ (i : Fin q.segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      ∀ v ∈ (subdivisionGraph I).vertices, q.eval i t = (referenceDrawing I).vertex v →
        ∃ b, q.AtEnd i t b ∧ Dart.vertex (e, b) = v := by
  have hopen : q.start ≠ q.finish := by
    rw [hstart, hfinish]
    exact (Route.isSimple_line_iff _ _).mp (referenceDrawing_simple hI e)
  intro i t ht v hv heq
  rcases hsupport (heq ▸ q.at_mem_support i ht) with hold | hball
  · obtain ⟨j, u, hu, huval⟩ := (Route.mem_support_iff _ _).mp hold
    obtain ⟨b, hb, hbv⟩ := referenceDrawing_vertex_contacts hI e j hu hv huval
    have hend : (referenceDrawing I).vertex v = q.endpoint b := by
      have hp := (Route.at_eq_endpoint _ j hu b hb).symm.trans huval
      cases b <;> simpa only [Route.endpoint, Bool.false_eq_true, ↓reduceIte, hstart, hfinish]
        using hp.symm
    refine ⟨b, ?_, hbv⟩
    cases b
    · have hp := hq.position_eq_of_eval_eq hopen i 0 ht ⟨le_rfl, zero_le_one⟩ (heq.trans (by
        simpa only [Route.endpoint, Bool.false_eq_true, ↓reduceIte, Route.eval,
          AffineMap.lineMap_apply_zero, Fin.castSucc_zero, Route.start] using hend))
      simpa only [Route.AtEnd, Route.position, Bool.false_eq_true, ↓reduceIte,
        Fin.val_zero, Nat.cast_zero, zero_add] using hp
    · have hp := hq.position_eq_of_eval_eq hopen i (Fin.last q.bends) ht ⟨zero_le_one, le_rfl⟩
        (heq.trans (by
          simpa only [Route.endpoint, ↓reduceIte, Route.eval, AffineMap.lineMap_apply_one,
            Fin.succ_last, Route.finish] using hend))
      simpa only [Route.AtEnd, Route.position, Route.segments, ↓reduceIte,
        Fin.val_last, Nat.cast_add, Nat.cast_one] using hp
  · obtain ⟨z, hz, hw⟩ := Set.mem_iUnion₂.mp hball
    exact (havoid z hz v hv hw).elim


private theorem free_local_pieces (r s d : ℝ) (z : ℂ) (flip : Bool) :
    let P := (if flip then (Route.slopeDetour r s d).reverse
      else Route.slopeDetour r s d).translate z
    (∀ t : ℝ, P.eval 0 t = AffineMap.lineMap P.start (z + (⟨0, d⟩ : ℂ)) t) ∧
    (∀ t : ℝ, P.eval 1 t = AffineMap.lineMap (z + (⟨0, d⟩ : ℂ)) P.finish t) := by
  cases flip <;> constructor <;> intro t <;> rfl

private theorem frozen_cut_parameter (a b : ℂ) (α β t : ℝ) :
    (Route.line (AffineMap.lineMap a b α) (AffineMap.lineMap a b β)).eval 0 t =
      (Route.line a b).eval 0 (α + (β - α) * t) := by
  rw [Route.eval_line, Route.eval_line, ← AffineMap.apply_lineMap]
  exact congrArg _ (by rw [AffineMap.lineMap_apply_ring']; ring)


private theorem chain_patch_word {ι : Type*} (L : List ι) (a b : ℂ)
    (left middle right : ι → ℂ) (R : ℂ → ℂ → Prop)
    (hab : R a b) (hfirst : ∀ z ∈ L, R a (left z))
    (hfinal : ∀ z ∈ L, R (right z) b)
    (hlocal : ∀ z ∈ L, R (left z) (middle z) ∧ R (middle z) (right z))
    (hbetween : L.Pairwise fun z w => R (right z) (left w)) :
    (a :: L.flatMap (fun z => [left z, middle z, right z]) ++ [b]).IsChain R := by
  induction L generalizing a with
  | nil => exact List.isChain_cons_cons.mpr ⟨hab, List.IsChain.singleton _⟩
  | cons z zs ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.isChain_cons_cons]
    refine ⟨hfirst z List.mem_cons_self, (hlocal z List.mem_cons_self).1,
      (hlocal z List.mem_cons_self).2, ih (right z) (hfinal z List.mem_cons_self)
        (fun w hw => (List.pairwise_cons.mp hbetween).1 w hw)
        (fun w hw => hfinal w (List.mem_cons_of_mem _ hw))
        (fun w hw => hlocal w (List.mem_cons_of_mem _ hw))
        (List.pairwise_cons.mp hbetween).2⟩


private def free_route {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (L : List ι) (left middle right : ι → ℂ) : Route :=
  match L with
  | [] => (referenceDrawing I).route e
  | z :: zs =>
      ([middle z, right z] ++ zs.flatMap (fun w => [left w, middle w, right w]) ++
        [((referenceDrawing I).route e).finish]).foldl Route.append
          (Route.line ((referenceDrawing I).route e).start (left z))

private theorem free_route_segments {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (L : List ι) (left middle right : ι → ℂ) :
    (free_route e L left middle right).segments = 3 * L.length + 1 := by
  cases L with
  | nil => rfl
  | cons z zs =>
    have hline : (Route.line ((referenceDrawing I).route e).start (left z)).segments = 1 := rfl
    simp [free_route, Route.segments_foldl_append, List.length_flatMap, hline,
      Nat.mul_comm, Nat.add_assoc, Nat.add_mul]
    omega

private theorem free_route_ends {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (L : List ι) (left middle right : ι → ℂ) :
    (free_route e L left middle right).start = ((referenceDrawing I).route e).start ∧
      (free_route e L left middle right).finish = ((referenceDrawing I).route e).finish := by
  cases L with
  | nil => exact ⟨rfl, rfl⟩
  | cons z zs =>
    refine ⟨?_, ?_⟩
    · have h0 := Route.eval_foldl_append_line ((referenceDrawing I).route e).start (left z)
        ([middle z, right z] ++ zs.flatMap (fun w => [left w, middle w, right w]) ++
          [((referenceDrawing I).route e).finish]) 0 0
      simp only [Route.eval, AffineMap.lineMap_apply_zero, Fin.castSucc_zero, Fin.val_zero,
        List.getElem_cons_zero] at h0
      exact h0
    · simp only [free_route, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact Route.endpoint_append _ _ true

private theorem free_route_simple {I : FixedRotationInput} (hI : Valid I)
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (L : List ι) (left middle right : ι → ℂ)
    (hword :
      (((referenceDrawing I).route e).start ::
        L.flatMap (fun z => [left z, middle z, right z]) ++
        [((referenceDrawing I).route e).finish]).Pairwise (fun x y => x.re < y.re) ∨
      (((referenceDrawing I).route e).start ::
        L.flatMap (fun z => [left z, middle z, right z]) ++
        [((referenceDrawing I).route e).finish]).Pairwise (fun x y => y.re < x.re)) :
    (free_route e L left middle right).IsSimple := by
  cases L with
  | nil => exact referenceDrawing_simple hI e
  | cons z zs =>
    let nodes := [middle z, right z] ++
      zs.flatMap (fun w => [left w, middle w, right w]) ++
        [((referenceDrawing I).route e).finish]
    rcases hword with hword | hword
    · exact Route.isSimple_of_strictMono_re <| append_word_point_order Complex.re _ _ nodes (by
        simpa only [nodes, List.flatMap_cons, List.cons_append, List.nil_append] using hword)
    · have hanti : StrictAnti fun k =>
          ((free_route e (z :: zs) left middle right).point k).re := fun _ _ hij =>
        neg_lt_neg_iff.mp <| append_word_point_order (fun w => -w.re) _ _ nodes
          (by simpa only [nodes, List.flatMap_cons, List.cons_append, List.nil_append] using
            hword.imp fun {_ _} => neg_lt_neg) hij
      simpa only [Route.reverse_reverse] using
        (Route.isSimple_of_strictMono_re
          (p := (free_route e (z :: zs) left middle right).reverse)
          fun _ _ hij => hanti (Fin.rev_lt_rev.mpr hij)).reverse

private theorem free_route_first_germ {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (z : ι) (zs : List ι) (left middle right : ι → ℂ) :
    (free_route e (z :: zs) left middle right).germ false =
      left z - ((referenceDrawing I).route e).start := by
  have heval (t : ℝ) : (free_route e (z :: zs) left middle right).eval 0 t =
      AffineMap.lineMap ((referenceDrawing I).route e).start (left z) t :=
    Route.eval_foldl_append_line _ _ _ 0 t
  simpa only [Route.eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    Route.germ, Route.start, Bool.false_eq_true, ↓reduceIte, Fin.castSucc_zero]
    using congrArg₂ (· - ·) (heval 1) (heval 0)

private theorem free_route_last_germ {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (L : List ι) (hne : L ≠ []) (left middle right : ι → ℂ) :
    (free_route e L left middle right).germ true =
      right (L.getLast hne) - ((referenceDrawing I).route e).finish := by
  let last := L.getLast hne
  have hsplit : L = L.dropLast ++ [last] := (List.dropLast_append_getLast hne).symm
  have hf (p : Route) (a : ℂ) : (p.append a).finish = a := Route.endpoint_append p a true
  conv_lhs => rw [hsplit]
  cases L.dropLast <;>
    simp only [free_route, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.nil_append, List.cons_append, List.append_assoc, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Route.germ_append, hf, ↓reduceIte] <;> rfl


private theorem word_order_from_cuts {ι : Type*} (L : List ι) (a b : ℂ)
    (left middle right : ι → ℂ) (α β : ι → ℝ) (ξ : ℂ → ℝ)
    (hab : ξ a < ξ b)
    (hproj : ∀ t : ℝ, ξ (AffineMap.lineMap a b t) = AffineMap.lineMap (ξ a) (ξ b) t)
    (hleft : ∀ z ∈ L, left z = AffineMap.lineMap a b (α z))
    (hright : ∀ z ∈ L, right z = AffineMap.lineMap a b (β z))
    (hα : ∀ z ∈ L, 0 < α z) (hβ : ∀ z ∈ L, β z < 1)
    (hlocal : ∀ z ∈ L, ξ (left z) < ξ (middle z) ∧ ξ (middle z) < ξ (right z))
    (hsorted : L.Pairwise fun z w => β z < α w) :
    (a :: L.flatMap (fun z => [left z, middle z, right z]) ++ [b]).Pairwise
      (fun x y => ξ x < ξ y) := by
  have hfirst (z) (hz : z ∈ L) : ξ a < ξ (left z) := by
    rw [hleft z hz, hproj]
    exact (left_lt_lineMap_iff_lt (hα z hz)).mpr hab
  have hfinal (z) (hz : z ∈ L) : ξ (right z) < ξ b := by
    rw [hright z hz, hproj]
    exact (lineMap_lt_right_iff_lt (hβ z hz)).mpr hab
  have hbetween : L.Pairwise fun z w => ξ (right z) < ξ (left w) :=
    List.pairwise_iff_getElem.mpr fun i j hi hj hij => by
      rw [hright _ (List.getElem_mem hi), hleft _ (List.getElem_mem hj), hproj, hproj]
      exact (lineMap_lt_lineMap_iff_of_lt' hab).mpr
        (List.pairwise_iff_getElem.mp hsorted i j hi hj hij)
  have hchain := chain_patch_word L a b left middle right
    (fun x y => ξ x < ξ y) hab hfirst hfinal hlocal hbetween
  rwa [← List.pairwise_map, ← List.isChain_iff_pairwise, List.isChain_map]


private theorem free_local_real_ends (r s d : ℝ) (z : ℂ) (flip : Bool) :
    let P := (if flip then (Route.slopeDetour r s d).reverse
      else Route.slopeDetour r s d).translate z
    P.start.re = z.re + (if flip then r else -r) ∧
      P.finish.re = z.re + (if flip then -r else r) := by
  cases flip <;> constructor <;> rfl


private theorem patch_node_get {ι : Type*} (L : List ι) (a b : ℂ)
    (left middle right : ι → ℂ) (q : Fin L.length) (j : Fin 3) :
    (a :: L.flatMap (fun z => [left z, middle z, right z]) ++ [b])[3 * q.val + 1 + j.val]? =
      some ([left L[q], middle L[q], right L[q]][j]) := by
  let emit := fun z => [left z, middle z, right z]
  have hj : j.val < (emit L[q.val]).length := by simpa only [emit, List.length_cons,
    List.length_nil] using j.isLt
  have hp : ((L.take q.val).flatMap emit).length = 3 * q.val := by
    simp [emit, List.length_flatMap, Nat.mul_comm]
  have hbound := List.flatMap_prefix_add_lt L emit q.isLt hj
  have hget := List.getElem_flatMap_prefix_add L emit q.isLt hj
  simp only [hp] at hbound hget
  have hindex : 3 * q.val + 1 + j.val = (3 * q.val + j.val) + 1 := by omega
  rw [List.cons_append, hindex, List.getElem?_cons_succ, List.getElem?_append_left hbound,
    List.getElem?_eq_getElem hbound, hget]
  rfl

private theorem free_route_eval_nodes {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (L : List ι) (left middle right : ι → ℂ)
    (i : Fin (free_route e L left middle right).segments) (t : ℝ) :
    ∃ a b : ℂ,
      (((referenceDrawing I).route e).start ::
        L.flatMap (fun z => [left z, middle z, right z]) ++
        [((referenceDrawing I).route e).finish])[i.val]? = some a ∧
      (((referenceDrawing I).route e).start ::
        L.flatMap (fun z => [left z, middle z, right z]) ++
        [((referenceDrawing I).route e).finish])[i.val + 1]? = some b ∧
      (free_route e L left middle right).eval i t = AffineMap.lineMap a b t := by
  cases L with
  | nil =>
    obtain rfl : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    exact ⟨_, _, rfl, rfl, Route.eval_line _ _ 0 t⟩
  | cons z zs =>
    let nodes := [middle z, right z] ++ zs.flatMap (fun w => [left w, middle w, right w]) ++
      [((referenceDrawing I).route e).finish]
    let word := ((referenceDrawing I).route e).start :: left z :: nodes
    have hi1 : i.val + 1 < word.length := by
      have hh := i.isLt
      simp [free_route_segments, word, nodes, List.length_flatMap] at hh ⊢
      omega
    refine ⟨word[i.val], word[i.val + 1], by simp [word, nodes], by simp [word, nodes],
      Route.eval_foldl_append_line _ _ nodes i t⟩


private theorem free_route_patch_eval {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (L : List ι) (left middle right : ι → ℂ) (q : Fin L.length) (j : Fin 2) :
    ∃ i : Fin (free_route e L left middle right).segments,
      i.val = 3 * q.val + 1 + j.val ∧ ∀ t : ℝ,
        (free_route e L left middle right).eval i t =
          AffineMap.lineMap ([left L[q], middle L[q], right L[q]][j.castSucc])
            ([left L[q], middle L[q], right L[q]][j.succ]) t := by
  let i : Fin (free_route e L left middle right).segments :=
    ⟨3 * q.val + 1 + j.val, by simp only [free_route_segments]; omega⟩
  refine ⟨i, rfl, fun t => ?_⟩
  obtain ⟨a, b, ha, hb, he⟩ := free_route_eval_nodes e L left middle right i t
  have hi1 : i.val + 1 = 3 * q.val + 1 + j.succ.val := by simp only [i, Fin.val_succ]; omega
  have hi0 : i.val = 3 * q.val + 1 + j.castSucc.val := rfl
  rw [hi0, patch_node_get L _ _ left middle right q j.castSucc] at ha
  rw [hi1, patch_node_get L _ _ left middle right q j.succ] at hb
  exact he.trans (congrArg₂ (fun x y => AffineMap.lineMap x y t)
    (Option.some.inj ha).symm (Option.some.inj hb).symm)

namespace ReferencePatchAssembly

/-- An indexed reference edge whose support contains the given actual crossing. -/
abbrev IncidentEdge (I : FixedRotationInput) (z : referenceCrossingPoints I) :=
  {e : Fin (subdivisionGraph I).edges.length // z.val ∈ ((referenceDrawing I).route e).support}

/-- An actual reference crossing lying on the specified indexed edge. -/
abbrev EdgeCenter (I : FixedRotationInput) (e : Fin (subdivisionGraph I).edges.length) :=
  {z : ℂ // z ∈ referenceCrossingPoints I ∧ z ∈ ((referenceDrawing I).route e).support}

end ReferencePatchAssembly

/-- One internally chosen reference patch assembly, with all data and properties tied to
its drawing. `exists_reference_patch_assembly` constructs it from `Valid I` alone.
Local contact facts do not assert global pair-contact regularization. -/
structure ReferencePatchAssembly (I : FixedRotationInput) where
  /-- Radius at each actual crossing center. -/
  radii : ℂ → ℝ
  /-- Shared horizontal extent of each local family. -/
  extent : referenceCrossingPoints I → ℝ
  /-- Internally chosen local detour heights. -/
  height : ∀ z : referenceCrossingPoints I, ReferencePatchAssembly.IncidentEdge I z → ℝ
  /-- Source parameter at the start of each cut. -/
  startParam : ∀ z : referenceCrossingPoints I, ReferencePatchAssembly.IncidentEdge I z → ℝ
  /-- Source parameter at the finish of each cut. -/
  finishParam : ∀ z : referenceCrossingPoints I, ReferencePatchAssembly.IncidentEdge I z → ℝ
  /-- Complete source-ordered center list for each indexed edge. -/
  centers : ∀ e, List (ReferencePatchAssembly.EdgeCenter I e)
  /-- Actual source-oriented local routes. -/
  patch : ∀ z : referenceCrossingPoints I, ReferencePatchAssembly.IncidentEdge I z → Route
  /-- Actual assembled polygonal drawing. -/
  drawing : PolygonalDrawing (subdivisionGraph I)
  /-- The full actual crossing set is finite. -/
  crossings_finite : (referenceCrossingPoints I).Finite
  /-- Every selected neighborhood radius is positive. -/
  radii_pos : ∀ z ∈ referenceCrossingPoints I, 0 < radii z
  /-- Distinct crossing neighborhoods have disjoint closed balls. -/
  balls_disjoint : (referenceCrossingPoints I).PairwiseDisjoint
    (fun z => Metric.closedBall z (radii z))
  /-- Each closed neighborhood excludes every declared vertex, including isolates. -/
  avoids_vertices : ∀ z ∈ referenceCrossingPoints I,
    ∀ v ∈ (subdivisionGraph I).vertices,
      (referenceDrawing I).vertex v ∉ Metric.closedBall z (radii z)
  /-- Each closed neighborhood excludes every nonincident original support. -/
  avoids_nonincident : ∀ z ∈ referenceCrossingPoints I,
    ∀ e : Fin (subdivisionGraph I).edges.length,
      z ∉ ((referenceDrawing I).route e).support →
      Disjoint (Metric.closedBall z (radii z)) ((referenceDrawing I).route e).support
  /-- Every local extent is positive. -/
  extent_pos : ∀ z, 0 < extent z
  /-- Local routes are precisely the translated, source-oriented existing detours. -/
  patch_eq : ∀ (z : referenceCrossingPoints I)
    (e : ReferencePatchAssembly.IncidentEdge I z),
    let D := referenceDrawing I
    let s := (D.route e.val).start.re + (D.route e.val).finish.re
    let frozen := ((subdivide I)[e.val.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.val.isLt)).frozen
    let raw := if frozen then
      Route.line ⟨-extent z, -extent z * s⟩ ⟨extent z, extent z * s⟩
      else Route.slopeDetour (extent z) s (height z e)
    patch z e = (if decide ((D.route e.val).finish.re < (D.route e.val).start.re)
      then raw.reverse else raw).translate z.val
  /-- Every cut has two strictly interior, source-ordered parameters. -/
  cut_bounds : ∀ z e, 0 < startParam z e ∧ startParam z e < finishParam z e ∧
    finishParam z e < 1
  /-- A local route starts at its original source cut point. -/
  patch_start : ∀ z e, (patch z e).start =
    AffineMap.lineMap (k := ℝ) ((referenceDrawing I).route e.val).start
      ((referenceDrawing I).route e.val).finish (startParam z e)
  /-- A local route finishes at its original source cut point. -/
  patch_finish : ∀ z e, (patch z e).finish =
    AffineMap.lineMap (k := ℝ) ((referenceDrawing I).route e.val).start
      ((referenceDrawing I).route e.val).finish (finishParam z e)
  /-- Every local route is simple as a continuum. -/
  patch_simple : ∀ z e, (patch z e).IsSimple
  /-- Every local support lies in its selected open ball. -/
  patch_support : ∀ z e, (patch z e).support ⊆ Metric.ball z.val (radii z.val)
  /-- Frozen members have zero detour height. -/
  frozen_height : ∀ (z : referenceCrossingPoints I)
    (e : ReferencePatchAssembly.IncidentEdge I z),
    ((subdivide I)[e.val.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.val.isLt)).frozen = true →
      height z e = 0
  /-- A frozen local member is literally its original one-segment cut. -/
  frozen_patch : ∀ (z : referenceCrossingPoints I)
    (e : ReferencePatchAssembly.IncidentEdge I z),
    ((subdivide I)[e.val.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.val.isLt)).frozen = true →
      patch z e = Route.line
        (AffineMap.lineMap (k := ℝ) ((referenceDrawing I).route e.val).start
          ((referenceDrawing I).route e.val).finish
          (startParam z e))
        (AffineMap.lineMap (k := ℝ) ((referenceDrawing I).route e.val).start
          ((referenceDrawing I).route e.val).finish
          (finishParam z e))
  /-- Distinct members of one local family have exactly one support contact. -/
  patch_pair_unique : ∀ z e f, e ≠ f →
    ∃! w : ℂ, w ∈ (patch z e).support ∧ w ∈ (patch z f).support
  /-- Every local pair contact has actual open parameters and nonzero determinant. -/
  patch_transverse : ∀ z e f, e ≠ f → ∀ w : ℂ,
    w ∈ (patch z e).support → w ∈ (patch z f).support →
      ∃ (i : Fin (patch z e).segments) (j : Fin (patch z f).segments) (u v : ℝ),
        u ∈ Set.Ioo 0 1 ∧ v ∈ Set.Ioo 0 1 ∧
        (patch z e).eval i u = w ∧ (patch z f).eval j v = w ∧
        let a := (patch z e).point i.succ - (patch z e).point i.castSucc
        let b := (patch z f).point j.succ - (patch z f).point j.castSucc
        a.re * b.im - a.im * b.re ≠ 0
  /-- No three distinct members of one local family share a support point. -/
  patch_no_triple : ∀ z e f g, e ≠ f → e ≠ g → f ≠ g → ∀ w : ℂ,
    w ∈ (patch z e).support → w ∈ (patch z f).support → w ∉ (patch z g).support
  /-- Each source-ordered center list has no duplicate occurrence. -/
  centers_nodup : ∀ e, (centers e).Nodup
  /-- Every actual crossing on an indexed edge occurs in its selected list. -/
  centers_complete : ∀ e (z : ReferencePatchAssembly.EdgeCenter I e), z ∈ centers e
  /-- Consecutive selected cuts are strictly separated in source order. -/
  centers_ordered : ∀ e, (centers e).Pairwise (fun z w =>
    finishParam ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩ <
      startParam ⟨w.val, w.property.1⟩ ⟨e, w.property.2⟩)
  /-- All declared vertex positions are unchanged. -/
  vertex_eq : drawing.vertex = (referenceDrawing I).vertex
  /-- The assembled route is the literal free append word or the original frozen route. -/
  route_eq :
    let H := subdivisionGraph I
    let D := referenceDrawing I
    let E := Fin H.edges.length
    let F : E → Bool := fun e => ((subdivide I)[e.val]'(by
      simpa only [H, subdivisionGraph, List.length_map] using e.isLt)).frozen
    let C : Set ℂ := referenceCrossingPoints I
    let X : C → Type := fun z => {e : E // z.val ∈ (D.route e).support}
    let Z : E → Type := fun e => {z : ℂ // z ∈ C ∧ z ∈ (D.route e).support}
    let site : ∀ e : E, Z e → C := fun _ z => ⟨z.val, z.property.1⟩
    let occurrence : ∀ (e : E) (z : Z e), X (site e z) := fun e z => ⟨e, z.property.2⟩
    let cutα : ∀ e : E, Z e → ℝ := fun e z => startParam (site e z) (occurrence e z)
    let cutβ : ∀ e : E, Z e → ℝ := fun e z => finishParam (site e z) (occurrence e z)
    let left : ∀ e : E, Z e → ℂ := fun e z =>
      AffineMap.lineMap (D.route e).start (D.route e).finish (cutα e z)
    let middle : ∀ e : E, Z e → ℂ := fun e z =>
      z.val + (⟨0, height (site e z) (occurrence e z)⟩ : ℂ)
    let right : ∀ e : E, Z e → ℂ := fun e z =>
      AffineMap.lineMap (D.route e).start (D.route e).finish (cutβ e z)
    ∀ e : E, drawing.route e = if F e then D.route e else
      List.casesOn (centers e) (D.route e) (fun z zs =>
        ([middle e z, right e z] ++ zs.flatMap (fun w => [left e w, middle e w, right e w]) ++
          [(D.route e).finish]).foldl Route.append (Route.line (D.route e).start (left e z)))
  /-- A free assembled route has exactly three segments per patch and one outer gap. -/
  segments_eq : ∀ e : Fin (subdivisionGraph I).edges.length,
    ((subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = false →
      (drawing.route e).segments = 3 * (centers e).length + 1
  /-- Every assembled route is simple as a continuum. -/
  simple : ∀ e, (drawing.route e).IsSimple
  /-- Every continuum contact with a declared vertex is the correct route end. -/
  vertex_contacts : ∀ e (i : Fin (drawing.route e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
    ∀ v ∈ (subdivisionGraph I).vertices, (drawing.route e).eval i t = drawing.vertex v →
      ∃ b, (drawing.route e).AtEnd i t b ∧ Dart.vertex (e, b) = v
  /-- Outgoing germs retain their directions with positive real factors. -/
  germs : ∀ e b, ∃ c : ℝ, 0 < c ∧
    (drawing.route e).germ b = c • ((referenceDrawing I).route e).germ b
  /-- Every selected local segment has its exact all-real global parameter map. -/
  patch_embedding : ∀ (e : Fin (subdivisionGraph I).edges.length) (q : Fin (centers e).length),
    let z := (centers e)[q]
    let p := patch ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩
    let frozen := ((subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen
    (frozen = false → ∀ j : Fin p.segments,
      ∃ i : Fin (drawing.route e).segments, i.val = 3 * q.val + 1 + j.val ∧
        ∀ t : ℝ, (drawing.route e).eval i t = p.eval j t) ∧
    (frozen = true → ∀ t : ℝ, (drawing.route e).eval 0
      (startParam ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩ +
        (finishParam ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩ -
          startParam ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩) * t) = p.eval 0 t)
  /-- The raw first detour piece maps to the source-oriented first or last local piece. -/
  raw_first_embedding : ∀ (e : Fin (subdivisionGraph I).edges.length),
    ((subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = false →
    ∀ q : Fin (centers e).length,
      let z := (centers e)[q]
      let site : referenceCrossingPoints I := ⟨z.val, z.property.1⟩
      let occurrence : ReferencePatchAssembly.IncidentEdge I site := ⟨e, z.property.2⟩
      let s := ((referenceDrawing I).route e).start.re + ((referenceDrawing I).route e).finish.re
      let raw := if ((subdivide I)[e.val]'(by
          simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen then
        Route.line ⟨-extent site, -extent site * s⟩ ⟨extent site, extent site * s⟩
        else Route.slopeDetour (extent site) s (height site occurrence)
      ∃ i : Fin (drawing.route e).segments,
        i.val = 3 * q.val +
          (if ((referenceDrawing I).route e).finish.re <
            ((referenceDrawing I).route e).start.re then 2 else 1) ∧
        ∀ t : ℝ, (drawing.route e).eval i
          (if ((referenceDrawing I).route e).finish.re <
            ((referenceDrawing I).route e).start.re then 1 - t else t) =
          z.val + raw.eval 0 t


private theorem free_route_word_support {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) {C : Set ℂ} {ρ : ℂ → ℝ}
    {ι : Type*} (site : ι → C) (L : List ι) (cutα cutβ : ι → ℝ)
    (left middle right : ι → ℂ)
    (hleft : ∀ z, left z = AffineMap.lineMap ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish (cutα z))
    (hright : ∀ z, right z = AffineMap.lineMap ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish (cutβ z))
    (hmargins : ∀ z, 0 < cutα z ∧ cutα z < cutβ z ∧ cutβ z < 1)
    (hleftBall : ∀ z, left z ∈ Metric.ball (site z).val (ρ (site z).val))
    (hmidBall : ∀ z, middle z ∈ Metric.ball (site z).val (ρ (site z).val))
    (hrightBall : ∀ z, right z ∈ Metric.ball (site z).val (ρ (site z).val))
    (hsorted : L.Pairwise fun z w => cutβ z < cutα w) :
    (free_route e L left middle right).support ⊆
      ((referenceDrawing I).route e).support ∪ ⋃ z ∈ C, Metric.ball z (ρ z) := by
  let D := referenceDrawing I
  let S := (D.route e).support ∪ ⋃ z ∈ C, Metric.ball z (ρ z)
  have hOld := (Route.support_line (D.route e).start (D.route e).finish).symm
  have hOldConvex : Convex ℝ (D.route e).support := hOld ▸ convex_segment _ _
  have hOldStart : (D.route e).start ∈ (D.route e).support := hOld ▸ left_mem_segment ℝ _ _
  have hOldFinish : (D.route e).finish ∈ (D.route e).support := hOld ▸ right_mem_segment ℝ _ _
  have hLeftOld (z : ι) : left z ∈ (D.route e).support := hleft z ▸ hOldConvex.lineMap_mem
    hOldStart hOldFinish ⟨(hmargins z).1.le, ((hmargins z).2.1.trans (hmargins z).2.2).le⟩
  have hRightOld (z : ι) : right z ∈ (D.route e).support := hright z ▸ hOldConvex.lineMap_mem
    hOldStart hOldFinish ⟨((hmargins z).1.trans (hmargins z).2.1).le, (hmargins z).2.2.le⟩
  have hold {x y : ℂ} (hx : x ∈ (D.route e).support) (hy : y ∈ (D.route e).support) :
      segment ℝ x y ⊆ S := (hOldConvex.segment_subset hx hy).trans Set.subset_union_left
  cases L with
  | nil => exact fun _ hw => Or.inl hw
  | cons z zs =>
    refine append_word_support _ _ _ S ?_
    have hchain := chain_patch_word (z :: zs) (D.route e).start (D.route e).finish
      left middle right (fun x y => segment ℝ x y ⊆ S) (hold hOldStart hOldFinish)
      (fun w _ => hold hOldStart (hLeftOld w)) (fun w _ => hold (hRightOld w) hOldFinish)
      (fun w _ => by
        have hballS : Metric.ball (site w).val (ρ (site w).val) ⊆ S :=
          fun _ hw => Or.inr (Set.mem_iUnion₂.mpr ⟨(site w).val, (site w).property, hw⟩)
        exact ⟨((convex_ball _ _).segment_subset (hleftBall w) (hmidBall w)).trans hballS,
          ((convex_ball _ _).segment_subset (hmidBall w) (hrightBall w)).trans hballS⟩)
      (hsorted.imp fun {w u} _ => hold (hRightOld w) (hLeftOld u))
    simpa only [List.flatMap_cons, List.cons_append, List.nil_append] using hchain

private theorem free_route_isSimple_of_cuts {I : FixedRotationInput} (hI : Valid I)
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (L : List ι) (cutα cutβ r s d : ι → ℝ) (zpt : ι → ℂ)
    (left middle right : ι → ℂ) (P : ι → Route)
    (hP : ∀ z, P z = (if decide (((referenceDrawing I).route e).finish.re <
        ((referenceDrawing I).route e).start.re)
      then (Route.slopeDetour (r z) (s z) (d z)).reverse
      else Route.slopeDetour (r z) (s z) (d z)).translate (zpt z))
    (hs : ∀ z, (P z).start = left z) (hf : ∀ z, (P z).finish = right z)
    (hleft : ∀ z, left z = AffineMap.lineMap ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish (cutα z))
    (hright : ∀ z, right z = AffineMap.lineMap ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish (cutβ z))
    (hmargins : ∀ z, 0 < cutα z ∧ cutα z < cutβ z ∧ cutβ z < 1)
    (hr : ∀ z, 0 < r z) (hmidRe : ∀ z, (middle z).re = (zpt z).re)
    (hsorted : L.Pairwise fun z w => cutβ z < cutα w) :
    (free_route e L left middle right).IsSimple := by
  let D := referenceDrawing I
  have hne : (D.route e).start.re ≠ (D.route e).finish.re :=
    (parabolaPoint_injective.eq_iff.not).mp
      ((Route.isSimple_line_iff _ _).mp (referenceDrawing_simple hI e))
  have hends (z : ι) :
      (left z).re = (zpt z).re + (if (D.route e).finish.re < (D.route e).start.re
        then r z else -r z) ∧
      (right z).re = (zpt z).re + (if (D.route e).finish.re < (D.route e).start.re
        then -r z else r z) := by
    have hx := free_local_real_ends (r z) (s z) (d z) (zpt z)
      (decide ((D.route e).finish.re < (D.route e).start.re))
    dsimp only at hx
    rw [← hP z, hs z, hf z] at hx
    by_cases hd : (D.route e).finish.re < (D.route e).start.re <;>
      simpa only [D, hd, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] using hx
  refine free_route_simple hI e L left middle right <| (lt_or_gt_of_ne hne).elim
    (fun hab => .inl (word_order_from_cuts L (D.route e).start (D.route e).finish left middle
      right cutα cutβ Complex.re hab
      (fun t => Complex.reCLM.toLinearMap.toAffineMap.apply_lineMap _ _ t)
      (fun z _ => hleft z) (fun z _ => hright z)
      (fun z _ => (hmargins z).1) (fun z _ => (hmargins z).2.2) (fun z _ => ?_) hsorted))
    (fun hba => .inr ((word_order_from_cuts L (D.route e).start (D.route e).finish left middle
      right cutα cutβ (fun w => -w.re) (neg_lt_neg hba)
      (fun t => (-Complex.reCLM).toLinearMap.toAffineMap.apply_lineMap _ _ t)
      (fun z _ => hleft z) (fun z _ => hright z)
      (fun z _ => (hmargins z).1) (fun z _ => (hmargins z).2.2) (fun z _ => ?_) hsorted).imp
      (fun {_ _} => neg_lt_neg_iff.mp)))
  all_goals
    obtain ⟨hl, hr'⟩ := hends z
    rw [hmidRe]
    split_ifs at hl hr' <;> constructor <;> linarith [hr z]

private theorem assembled_route_germs {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) (frozen : Bool) {ι : Type*}
    (L : List ι) (cutα cutβ : ι → ℝ) (left middle right : ι → ℂ)
    (hleft : ∀ z, left z = AffineMap.lineMap ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish (cutα z))
    (hright : ∀ z, right z = AffineMap.lineMap ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish (cutβ z))
    (hmargins : ∀ z, 0 < cutα z ∧ cutα z < cutβ z ∧ cutβ z < 1) (tag : Bool) :
    let Q := if frozen then (referenceDrawing I).route e else free_route e L left middle right
    ∃ c : ℝ, 0 < c ∧ Q.germ tag = c • ((referenceDrawing I).route e).germ tag := by
  cases frozen
  · cases L with
    | nil =>
      exact ⟨1, zero_lt_one, by simp only [Bool.false_eq_true, ↓reduceIte, free_route, one_smul]⟩
    | cons z zs =>
      cases tag
      · refine ⟨cutα z, (hmargins z).1, ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte, free_route_first_germ, hleft z]
        exact AffineMap.lineMap_vsub_left (k := ℝ)
          ((referenceDrawing I).route e).start ((referenceDrawing I).route e).finish (cutα z)
      · let last := (z :: zs).getLast (by simp)
        refine ⟨1 - cutβ last, sub_pos.mpr (hmargins last).2.2, ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [free_route_last_germ e (z :: zs) (by simp), hright last]
        exact AffineMap.lineMap_vsub_right (k := ℝ)
          ((referenceDrawing I).route e).start ((referenceDrawing I).route e).finish (cutβ last)
  · exact ⟨1, zero_lt_one, by simp only [↓reduceIte, one_smul]⟩

private theorem assembled_patch_embedding {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) (frozen : Bool) {ι : Type*}
    (L : List ι) (cutα cutβ : ι → ℝ) (left middle right : ι → ℂ) (P : ι → Route)
    (hseg : frozen = false → ∀ z, (P z).segments = 2)
    (hpieces : frozen = false → ∀ z,
      (∀ t : ℝ, (P z).eval 0 t = AffineMap.lineMap (left z) (middle z) t) ∧
      (∀ t : ℝ, (P z).eval 1 t = AffineMap.lineMap (middle z) (right z) t))
    (hkeep : frozen = true → ∀ z, P z = Route.line
      (AffineMap.lineMap ((referenceDrawing I).route e).start
        ((referenceDrawing I).route e).finish (cutα z))
      (AffineMap.lineMap ((referenceDrawing I).route e).start
        ((referenceDrawing I).route e).finish (cutβ z)))
    (q : Fin L.length) :
    let z := L[q]
    (frozen = false → ∀ j : Fin (P z).segments,
      ∃ i : Fin (if frozen then (referenceDrawing I).route e
          else free_route e L left middle right).segments,
        i.val = 3 * q.val + 1 + j.val ∧
        ∀ t : ℝ, (if frozen then (referenceDrawing I).route e
          else free_route e L left middle right).eval i t = (P z).eval j t) ∧
    (frozen = true → ∀ t : ℝ,
      (if frozen then (referenceDrawing I).route e
        else free_route e L left middle right).eval 0 (cutα z + (cutβ z - cutα z) * t) =
        (P z).eval 0 t) := by
  let z := L[q]
  cases frozen
  · refine ⟨fun _ j => ?_, nofun⟩
    change ∃ i : Fin (free_route e L left middle right).segments,
      i.val = 3 * q.val + 1 + j.val ∧
      ∀ t : ℝ, (free_route e L left middle right).eval i t = (P z).eval j t
    obtain ⟨i, hi, hieval⟩ :=
      free_route_patch_eval e L left middle right q ⟨j.val, hseg rfl z ▸ j.isLt⟩
    refine ⟨i, hi, fun t => (hieval t).trans ?_⟩
    obtain ⟨_ | _ | k, hj⟩ := j
    · exact ((hpieces rfl z).1 t).symm
    · have hj1 : (⟨1, hj⟩ : Fin (P z).segments) = 1 :=
        Fin.ext (by change 1 = 1 % (P z).segments; rw [hseg rfl z])
      exact ((congrArg (fun k => (P z).eval k t) hj1).trans ((hpieces rfl z).2 t)).symm
    · have := hseg rfl L[q]; omega
  · refine ⟨nofun, fun _ t => ?_⟩
    change ((referenceDrawing I).route e).eval 0 (cutα z + (cutβ z - cutα z) * t) =
      (P z).eval 0 t
    rw [hkeep rfl z]
    exact (frozen_cut_parameter _ _ (cutα z) (cutβ z) t).symm

private theorem free_raw_first_embedding {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (L : List ι) (left middle right : ι → ℂ) (raw P : ι → Route) (zpt : ι → ℂ)
    (hraw_seg : ∀ z, (raw z).segments = 2)
    (hP : ∀ z, P z = (if decide (((referenceDrawing I).route e).finish.re <
        ((referenceDrawing I).route e).start.re)
      then (raw z).reverse else raw z).translate (zpt z))
    (hpieces : ∀ z,
      (∀ t : ℝ, (P z).eval 0 t = AffineMap.lineMap (left z) (middle z) t) ∧
      (∀ t : ℝ, (P z).eval 1 t = AffineMap.lineMap (middle z) (right z) t))
    (q : Fin L.length) :
    let z := L[q]
    ∃ i : Fin (free_route e L left middle right).segments,
      i.val = 3 * q.val +
        (if ((referenceDrawing I).route e).finish.re <
          ((referenceDrawing I).route e).start.re then 2 else 1) ∧
      ∀ t : ℝ, (free_route e L left middle right).eval i
        (if ((referenceDrawing I).route e).finish.re <
          ((referenceDrawing I).route e).start.re then 1 - t else t) =
        zpt z + (raw z).eval 0 t := by
  let z := L[q]
  by_cases hd : ((referenceDrawing I).route e).finish.re <
      ((referenceDrawing I).route e).start.re
  · obtain ⟨i, hi, hieval⟩ := free_route_patch_eval e L left middle right q 1
    refine ⟨i, by simp only [hd, ↓reduceIte, Fin.val_one] at *; omega, fun t => ?_⟩
    simp only [hd, ↓reduceIte]
    refine ((hieval (1 - t)).trans ((hpieces z).2 (1 - t)).symm).trans ?_
    have hp := hP z
    rw [ite_eq_left (decide_eq_true hd)] at hp
    generalize P z = Pz at hp ⊢
    subst hp
    have hrev : (1 : Fin (raw z).reverse.segments).rev = 0 :=
      Fin.ext (by
        simp only [Fin.val_rev, Fin.val_zero]
        change (raw z).segments - (1 % (raw z).segments + 1) = 0
        rw [hraw_seg z])
    change ((raw z).reverse.translate (zpt z)).eval (1 : Fin (raw z).reverse.segments) (1 - t) = _
    rw [Route.eval_translate, Route.eval_reverse, hrev, sub_sub_cancel]
    rfl
  · obtain ⟨i, hi, hieval⟩ := free_route_patch_eval e L left middle right q 0
    refine ⟨i, by simpa only [hd, ↓reduceIte, Fin.val_zero, add_zero] using hi, fun t => ?_⟩
    simp only [hd, ↓reduceIte]
    refine ((hieval t).trans ((hpieces z).1 t).symm).trans ?_
    have hp := hP z
    rw [ite_eq_right (Bool.eq_false_iff.mp (decide_eq_false hd))] at hp
    generalize P z = Pz at hp ⊢
    subst hp
    exact Route.eval_translate (raw z) (zpt z) 0 t

/-- Construct one complete named-field reference patch assembly from `Valid I` alone.
All selected data and proofs refer to its single drawing. A global assembly with exact
pair-contact correspondence, transverse contacts and no triples away from declared vertices
is provided by `exists_reference_crossing_regularization` in `ReferenceRegularization`.
Parity, placement, Hanani–Tutte and recognition remain open. -/
theorem exists_reference_patch_assembly {I : FixedRotationInput} (hI : Valid I) :
    Nonempty (ReferencePatchAssembly I) := by
  classical
  let H := subdivisionGraph I
  let D := referenceDrawing I
  let E := Fin H.edges.length
  let F : E → Bool := fun e => ((subdivide I)[e.val]'(by
    simpa only [H, subdivisionGraph, List.length_map] using e.isLt)).frozen
  let C : Set ℂ := referenceCrossingPoints I
  let X : C → Type := fun z => {e : E // z.val ∈ (D.route e).support}
  let Z : E → Type := fun e => {z : ℂ // z ∈ C ∧ z ∈ (D.route e).support}
  obtain ⟨hC, ρ, hρ, hballs, hexclude⟩ := exists_reference_crossing_neighborhoods hI
  choose r hr d α β hcuts hkeep hpair htrans hno3 using
    fun z : C => exists_reference_detour_placement hI z.property (hρ z.val z.property)
  let s : ∀ z : C, X z → ℝ := fun _ e => (D.route e.val).start.re + (D.route e.val).finish.re
  let R : ∀ z : C, X z → Route := fun z e => if F e.val then
    Route.line ⟨-r z, -r z * s z e⟩ ⟨r z, r z * s z e⟩
    else Route.slopeDetour (r z) (s z e) (d z e)
  let P : ∀ z : C, X z → Route := fun z e =>
    (if decide ((D.route e.val).finish.re < (D.route e.val).start.re)
      then (R z e).reverse else R z e).translate z.val
  change ∀ (z : C) (e : X z), 0 < α z e ∧ α z e < β z e ∧ β z e < 1 ∧
    (P z e).start = AffineMap.lineMap (D.route e.val).start (D.route e.val).finish (α z e) ∧
    (P z e).finish = AffineMap.lineMap (D.route e.val).start (D.route e.val).finish (β z e) ∧
    (P z e).IsSimple ∧ (P z e).support ⊆ Metric.ball z.val (ρ z.val) at hcuts
  change ∀ (z : C) (e : X z), F e.val = true → d z e = 0 ∧
    P z e = Route.line
      (AffineMap.lineMap (D.route e.val).start (D.route e.val).finish (α z e))
      (AffineMap.lineMap (D.route e.val).start (D.route e.val).finish (β z e)) at hkeep
  let site : ∀ e : E, Z e → C := fun _ z => ⟨z.val, z.property.1⟩
  let occurrence : ∀ (e : E) (z : Z e), X (site e z) := fun e z => ⟨e, z.property.2⟩
  let cutα : ∀ e : E, Z e → ℝ := fun e z => α (site e z) (occurrence e z)
  let cutβ : ∀ e : E, Z e → ℝ := fun e z => β (site e z) (occurrence e z)
  let left : ∀ e : E, Z e → ℂ := fun e z =>
    AffineMap.lineMap (D.route e).start (D.route e).finish (cutα e z)
  let middle : ∀ e : E, Z e → ℂ := fun e z =>
    z.val + (⟨0, d (site e z) (occurrence e z)⟩ : ℂ)
  let right : ∀ e : E, Z e → ℂ := fun e z =>
    AffineMap.lineMap (D.route e).start (D.route e).finish (cutβ e z)
  have hmargins (e : E) (z : Z e) : 0 < cutα e z ∧ cutα e z < cutβ e z ∧ cutβ e z < 1 :=
    ⟨(hcuts (site e z) (occurrence e z)).1, (hcuts (site e z) (occurrence e z)).2.1,
      (hcuts (site e z) (occurrence e z)).2.2.1⟩
  have hαball (e : E) (z : Z e) : left e z ∈ Metric.ball z.val (ρ z.val) := by
    obtain ⟨_, _, _, hs, _, _, hball⟩ := hcuts (site e z) (occurrence e z)
    rw [Route.start] at hs
    simpa only [Route.eval, AffineMap.lineMap_apply_zero, Fin.castSucc_zero, hs]
      using hball ((P (site e z) (occurrence e z)).at_mem_support 0 ⟨le_rfl, zero_le_one⟩)
  have hβball (e : E) (z : Z e) : right e z ∈ Metric.ball z.val (ρ z.val) := by
    obtain ⟨_, _, _, _, hf, _, hball⟩ := hcuts (site e z) (occurrence e z)
    rw [Route.finish] at hf
    simpa only [Route.eval, AffineMap.lineMap_apply_one, Fin.succ_last, hf]
      using hball ((P (site e z) (occurrence e z)).at_mem_support
        (Fin.last (P (site e z) (occurrence e z)).bends) ⟨zero_le_one, le_rfl⟩)
  have hordered (e : E) : ∃ L : List (Z e), L.Nodup ∧ (∀ z : Z e, z ∈ L) ∧
      L.Pairwise (fun z w => cutβ e z < cutα e w) :=
    sorted_reference_cuts I e {z : ℂ | z ∈ C ∧ z ∈ (D.route e).support}
      (hC.subset fun _ hz => hz.1) ρ (cutα e) (cutβ e)
      (fun z => (hmargins e z).2.1) (fun _ hz _ hw hzw => hballs hz.1 hw.1 hzw)
      (hαball e) (hβball e)
  choose L hnd hmem hsorted using hordered
  have hfree (e : E) (he : F e = false) (z : Z e) :
      P (site e z) (occurrence e z) =
        (if decide ((D.route e).finish.re < (D.route e).start.re) then
          (Route.slopeDetour (r (site e z)) (s (site e z) (occurrence e z))
            (d (site e z) (occurrence e z))).reverse else
          Route.slopeDetour (r (site e z)) (s (site e z) (occurrence e z))
            (d (site e z) (occurrence e z))).translate z.val := by
    simp only [P, R, occurrence, he, Bool.false_eq_true, ↓reduceIte]; rfl
  have hpieces (e : E) (he : F e = false) (z : Z e) :
      (∀ t : ℝ, (P (site e z) (occurrence e z)).eval 0 t =
        AffineMap.lineMap (left e z) (middle e z) t) ∧
      (∀ t : ℝ, (P (site e z) (occurrence e z)).eval 1 t =
        AffineMap.lineMap (middle e z) (right e z) t) := by
    obtain ⟨_, _, _, hs, hf, _, _⟩ := hcuts (site e z) (occurrence e z)
    have hp := free_local_pieces (r (site e z)) (s (site e z) (occurrence e z))
      (d (site e z) (occurrence e z)) z.val (decide ((D.route e).finish.re < (D.route e).start.re))
    rw [← hfree e he z] at hp
    change (P (site e z) (occurrence e z)).start = left e z at hs
    change (P (site e z) (occurrence e z)).finish = right e z at hf
    simpa only [hs, hf] using hp
  have hmiddle_ball (e : E) (he : F e = false) (z : Z e) :
      middle e z ∈ Metric.ball z.val (ρ z.val) := by
    obtain ⟨_, _, _, _, _, _, hball⟩ := hcuts (site e z) (occurrence e z)
    have hw := hball ((P (site e z) (occurrence e z)).at_mem_support 0 ⟨zero_le_one, le_rfl⟩)
    simpa only [(hpieces e he z).1 1, AffineMap.lineMap_apply_one] using hw
  let Q : E → Route := fun e => if F e then D.route e else
    free_route e (L e) (left e) (middle e) (right e)
  have hends (e : E) : (Q e).start = (D.route e).start ∧ (Q e).finish = (D.route e).finish := by
    cases hf : F e
    · simpa only [Q, hf, Bool.false_eq_true, ↓reduceIte]
        using free_route_ends e (L e) (left e) (middle e) (right e)
    · simp [Q, hf]
  have hsimple (e : E) : (Q e).IsSimple := by
    cases hf : F e
    · simp only [Q, hf, Bool.false_eq_true, ↓reduceIte]
      exact free_route_isSimple_of_cuts hI e (L e) (cutα e) (cutβ e)
        (fun z => r (site e z)) (fun z => s (site e z) (occurrence e z))
        (fun z => d (site e z) (occurrence e z)) (fun z => z.val)
        (left e) (middle e) (right e) (fun z => P (site e z) (occurrence e z))
        (hfree e hf) (fun z => (hcuts (site e z) (occurrence e z)).2.2.2.1)
        (fun z => (hcuts (site e z) (occurrence e z)).2.2.2.2.1)
        (fun _ => rfl) (fun _ => rfl) (hmargins e) (fun z => hr (site e z))
        (fun _ => by simp only [middle, Complex.add_re, add_zero]) (hsorted e)
    · simp only [Q, hf, ↓reduceIte]
      exact referenceDrawing_simple hI e
  have hsupport (e : E) :
      (Q e).support ⊆ (D.route e).support ∪ ⋃ z ∈ C, Metric.ball z (ρ z) := by
    cases hf : F e
    · simpa only [Q, hf, Bool.false_eq_true, ↓reduceIte] using
        free_route_word_support e (site e) (L e) (cutα e) (cutβ e) (left e) (middle e) (right e)
          (fun _ => rfl) (fun _ => rfl) (hmargins e) (hαball e) (hmiddle_ball e hf) (hβball e)
          (hsorted e)
    · exact fun _ hw => Or.inl (by simpa only [Q, hf, ↓reduceIte] using hw)
  let D' : PolygonalDrawing H :=
    ⟨D.vertex, Q, fun e tag => by
      cases tag <;> simp only [Route.endpoint, Bool.false_eq_true, ↓reduceIte,
        (hends e).1, (hends e).2, ← D.endpoint_eq]⟩
  have hsegfree (e : E) (he : F e = false) (z : Z e) :
      (P (site e z) (occurrence e z)).segments = 2 := by
    rw [hfree e he z]
    cases decide ((D.route e).finish.re < (D.route e).start.re) <;> rfl
  have hlocal_embed (e : E) (q : Fin (L e).length) :=
    assembled_patch_embedding e (F e) (L e) (cutα e) (cutβ e) (left e) (middle e) (right e)
      (fun z => P (site e z) (occurrence e z)) (hsegfree e) (hpieces e)
      (fun he z => (hkeep (site e z) (occurrence e z) he).2) q
  refine ⟨{
    radii := ρ
    extent := r
    height := d
    startParam := α
    finishParam := β
    centers := L
    patch := P
    drawing := D'
    crossings_finite := hC
    radii_pos := hρ
    balls_disjoint := hballs
    avoids_vertices := fun z hz => (hexclude z hz).1
    avoids_nonincident := fun z hz => (hexclude z hz).2
    extent_pos := hr
    patch_eq := fun _ _ => rfl
    cut_bounds := fun z e => ⟨(hcuts z e).1, (hcuts z e).2.1, (hcuts z e).2.2.1⟩
    patch_start := fun z e => (hcuts z e).2.2.2.1
    patch_finish := fun z e => (hcuts z e).2.2.2.2.1
    patch_simple := fun z e => (hcuts z e).2.2.2.2.2.1
    patch_support := fun z e => (hcuts z e).2.2.2.2.2.2
    frozen_height := fun z e hf => (hkeep z e hf).1
    frozen_patch := fun z e hf => (hkeep z e hf).2
    patch_pair_unique := hpair
    patch_transverse := htrans
    patch_no_triple := hno3
    centers_nodup := hnd
    centers_complete := hmem
    centers_ordered := hsorted
    vertex_eq := rfl
    route_eq := ?_
    segments_eq := fun e he => by
      simpa only [D', Q, F, he, Bool.false_eq_true, ↓reduceIte] using
        free_route_segments e (L e) (left e) (middle e) (right e)
    simple := hsimple
    vertex_contacts := fun e => vertex_contacts_from_support hI e C ρ
      (fun z hz v hv hw => (hexclude z hz).1 v hv (Metric.ball_subset_closedBall hw))
      (Q e) (hsimple e) (hends e).1 (hends e).2 (hsupport e)
    germs := fun e tag => assembled_route_germs e (F e) (L e) (cutα e) (cutβ e)
      (left e) (middle e) (right e) (fun _ => rfl) (fun _ => rfl) (hmargins e) tag
    patch_embedding := hlocal_embed
    raw_first_embedding := fun e he q => by
      have hFe : F e = false := he
      have hraw_seg (z : Z e) : (R (site e z) (occurrence e z)).segments = 2 := by
        simp only [R, occurrence, hFe, Bool.false_eq_true, ↓reduceIte]; rfl
      dsimp only [D', Q]
      generalize F e = b at hFe ⊢
      subst hFe
      exact free_raw_first_embedding e (L e) (left e) (middle e) (right e)
        (fun z => R (site e z) (occurrence e z)) (fun z => P (site e z) (occurrence e z))
        (fun z => z.val) hraw_seg (fun _ => rfl) (hpieces e he) q }⟩
  dsimp only
  intro e
  cases hf : F e <;> cases hL : L e <;>
    simp only [D', Q, free_route, F, D, site, occurrence, cutα, cutβ, left, middle,
      right, hf, hL, Bool.false_eq_true, ↓reduceIte]; rfl


end Cslib.Complexity.Graph.RotationRecognition
