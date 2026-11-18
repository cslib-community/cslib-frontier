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
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain
import CslibFrontier.Foundations.Data.List.FlatMapPositions
import Mathlib.Order.Basic
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.Foundations.Geometry.Polygonal.LineEnds

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

This is original finite coordinate geometry. Global exclusion of extra pair contacts,
pair-contact correspondence and no triples away from declared vertices remain open under
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
  apply Set.disjoint_left.mpr
  intro t ht hu
  exact Set.disjoint_left.mp hballs
    (Metric.ball_subset_closedBall (hz ht)) (Metric.ball_subset_closedBall (hw hu))

private theorem append_word_point_order {α : Type*} [Preorder α]
    (f : ℂ → α) (a b : ℂ) (nodes : List ℂ)
    (hword : (a :: b :: nodes).Pairwise (fun x y => f x < f y)) :
    StrictMono fun k => f ((nodes.foldl Route.append (Route.line a b)).point k) := by
  have hab : f a < f b := by
    exact (List.pairwise_iff_getElem.mp hword) 0 1 (by simp) (by simp) (by decide)
  have hnext (q : Fin nodes.length) :
      f ((b :: nodes)[q.castSucc]) < f (nodes[q]) := by
    have h := (List.pairwise_iff_getElem.mp hword.tail) q.val (q.val + 1)
      (by simp) (by simp) (by omega)
    simpa only [List.tail_cons, Fin.getElem_fin, Fin.val_castSucc, List.getElem_cons_succ] using h
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have h0 := Route.foldl_append_eval_cases (Route.line a b) nodes i 0
  have h1 := Route.foldl_append_eval_cases (Route.line a b) nodes i 1
  have heval : f ((nodes.foldl Route.append (Route.line a b)).eval i 0) <
      f ((nodes.foldl Route.append (Route.line a b)).eval i 1) := by
    rcases h0 with ⟨j, hj, he0, _⟩ | ⟨q, hq, he0, _⟩ <;>
      rcases h1 with ⟨k, hk, he1, _⟩ | ⟨r, hr, he1, _⟩
    · have hj0 : j = 0 := by
        apply Fin.ext
        change j.val = 0
        have h := j.isLt
        change j.val < 1 at h
        omega
      have hk0 : k = 0 := by
        apply Fin.ext
        change k.val = 0
        have h := k.isLt
        change k.val < 1 at h
        omega
      subst j
      subst k
      rw [he0, he1, Route.eval_line, Route.eval_line,
        AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
      exact hab
    · have hj0 : j.val = 0 := by have h := j.isLt; change j.val < 1 at h; omega
      change i.val = 1 + r.val at hr
      omega
    · have hk0 : k.val = 0 := by have h := k.isLt; change k.val < 1 at h; omega
      change i.val = 1 + q.val at hq
      omega
    · have hqr : q = r := by
        apply Fin.ext
        change i.val = 1 + q.val at hq
        change i.val = 1 + r.val at hr
        omega
      subst r
      rw [he0, he1, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
      simpa only [Route.finish_line] using hnext q
  simpa only [Route.eval, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] using heval


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
  have hcuts (z w : C) (hne : z ≠ w) :
      Disjoint (Set.Icc (α z) (β z)) (Set.Icc (α w) (β w)) := by
    apply disjoint_reference_cuts I e (hab z).le (hab w).le
      (hdisj z.property w.property (fun h => hne (Subtype.ext h)))
      (ha z) (hb z) (ha w) (hb w)
  have hinj : Function.Injective α := by
    intro z w heq
    by_contra hne
    have hw : α z ∈ Set.Icc (α w) (β w) := by
      rw [heq]
      exact ⟨le_rfl, (hab w).le⟩
    exact Set.disjoint_left.mp (hcuts z w hne) ⟨le_rfl, (hab z).le⟩ hw
  let : LinearOrder C := LinearOrder.lift' α hinj
  let L : List C := Finset.univ.sort
  refine ⟨L, Finset.sort_nodup _ _, fun z => ?_, ?_⟩
  · exact (Finset.mem_sort _).mpr (Finset.mem_univ z)
  · apply (Finset.sortedLT_sort (Finset.univ : Finset C)).pairwise.imp
    intro z w hzw
    have hlt : α z < α w := hzw
    by_contra hn
    have hne : z ≠ w := ne_of_lt hzw
    exact Set.disjoint_left.mp (hcuts z w hne)
      ⟨hlt.le, le_of_not_gt hn⟩ ⟨le_rfl, (hab w).le⟩


private theorem append_word_support (a b : ℂ) (nodes : List ℂ) (S : Set ℂ)
    (hword : (a :: b :: nodes).IsChain (fun x y => segment ℝ x y ⊆ S)) :
    (nodes.foldl Route.append (Route.line a b)).support ⊆ S := by
  intro w hw
  obtain ⟨i, t, ht, heval⟩ := (Route.mem_support_iff _ w).mp hw
  have hi : i.val + 1 < (a :: b :: nodes).length := by
    have hh := i.isLt
    simp only [Route.segments_foldl_append] at hh
    change i.val < 1 + nodes.length at hh
    simp only [List.length_cons]
    omega
  have hpiece := (List.isChain_iff_getElem.mp hword) i.val hi
  apply hpiece
  rw [← heval, Route.eval_foldl_append_line]
  exact lineMap_mem_segment ℝ _ _ ht

private theorem first_germ_after_word (a b : ℂ) (nodes : List ℂ) :
    (nodes.foldl Route.append (Route.line a b)).germ false = b - a := by
  have heval (t : ℝ) : (nodes.foldl Route.append (Route.line a b)).eval 0 t =
      AffineMap.lineMap a b t := by
    rw [Route.eval_foldl_append_line]
    rfl
  have h0 := heval 0
  have h1 := heval 1
  simpa only [Route.eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    Route.germ, Route.start, Bool.false_eq_true, ↓reduceIte, Fin.castSucc_zero]
    using congrArg₂ (· - ·) h1 h0


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
  have hw := hsupport (q.at_mem_support i ht)
  rw [heq] at hw
  rcases hw with hold | hball
  · obtain ⟨j, u, hu, huval⟩ := (Route.mem_support_iff _ _).mp hold
    obtain ⟨b, hb, hbv⟩ := referenceDrawing_vertex_contacts hI e j hu hv huval
    have hendpoint : (referenceDrawing I).vertex v = q.endpoint b := by
      have hp := (Route.at_eq_endpoint _ j hu b hb).symm.trans huval
      cases b
      · simpa only [Route.endpoint, Bool.false_eq_true, ↓reduceIte, hstart] using hp.symm
      · simpa only [Route.endpoint, ↓reduceIte, hfinish] using hp.symm
    refine ⟨b, ?_, hbv⟩
    cases b
    · have hzero : q.eval 0 0 = q.start := by
        simp only [Route.eval, AffineMap.lineMap_apply_zero, Fin.castSucc_zero, Route.start]
      have hp := hq.position_eq_of_eval_eq hopen i 0 ht ⟨le_rfl, zero_le_one⟩
        (heq.trans (hendpoint.trans hzero.symm))
      simpa only [Route.AtEnd, Route.position, Bool.false_eq_true, ↓reduceIte,
        Fin.val_zero, Nat.cast_zero, zero_add] using hp
    · have hone : q.eval (Fin.last q.bends) 1 = q.finish := by
        simp only [Route.eval, AffineMap.lineMap_apply_one, Fin.succ_last, Route.finish]
      have hp := hq.position_eq_of_eval_eq hopen i (Fin.last q.bends)
        ht ⟨zero_le_one, le_rfl⟩ (heq.trans (hendpoint.trans hone.symm))
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

private theorem eval_retained_after_word (p : Route) (nodes : List ℂ)
    (j : Fin p.segments)
    (i : Fin (nodes.foldl Route.append p).segments) (hi : i.val = j.val) (t : ℝ) :
    (nodes.foldl Route.append p).eval i t = p.eval j t := by
  rcases Route.foldl_append_eval_cases p nodes i t with
    ⟨k, hk, heval, _⟩ | ⟨q, hq, _, _⟩
  · have hkj : k = j := Fin.ext (hk.symm.trans hi)
    simpa only [hkj] using heval
  · have hj := j.isLt
    omega

private theorem frozen_cut_parameter (a b : ℂ) (α β t : ℝ) :
    (Route.line (AffineMap.lineMap a b α) (AffineMap.lineMap a b β)).eval 0 t =
      (Route.line a b).eval 0 (α + (β - α) * t) := by
  rw [Route.eval_line, Route.eval_line, ← AffineMap.apply_lineMap]
  congr 1
  rw [AffineMap.lineMap_apply_ring']
  ring


private theorem chain_patch_word {ι : Type*} (L : List ι) (a b : ℂ)
    (left middle right : ι → ℂ) (R : ℂ → ℂ → Prop)
    (hab : R a b) (hfirst : ∀ z ∈ L, R a (left z))
    (hfinal : ∀ z ∈ L, R (right z) b)
    (hlocal : ∀ z ∈ L, R (left z) (middle z) ∧ R (middle z) (right z))
    (hbetween : L.Pairwise fun z w => R (right z) (left w)) :
    (a :: L.flatMap (fun z => [left z, middle z, right z]) ++ [b]).IsChain R := by
  let blocks := [a] :: L.map (fun z => [left z, middle z, right z]) ++ [[b]]
  have hempty : [] ∉ blocks := by simp [blocks]
  have hinternal : ∀ block ∈ blocks, block.IsChain R := by
    intro block hblock
    simp only [blocks, List.mem_cons, List.mem_append, List.mem_map,
      List.not_mem_nil, or_false] at hblock
    rcases hblock with (rfl | ⟨z, hz, rfl⟩) | rfl
    · exact List.IsChain.singleton _
    · simpa only [List.isChain_cons_cons, List.IsChain.singleton, and_true] using hlocal z hz
    · exact List.IsChain.singleton _
  let G := fun xs ys : List ℂ => ∀ x ∈ xs.getLast?, ∀ y ∈ ys.head?, R x y
  have hmap : (L.map (fun z => [left z, middle z, right z])).Pairwise G := by
    apply List.pairwise_map.mpr
    exact hbetween.imp (by intro z w h; simpa [G] using h)
  have houter : blocks.Pairwise G := by
    apply List.pairwise_cons.mpr
    constructor
    · intro block hblock
      rcases List.mem_append.mp hblock with hblock | hblock
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hblock
        simpa [G] using hfirst z hz
      · rcases List.mem_singleton.mp hblock with rfl
        simpa [G] using hab
    · apply List.pairwise_append.mpr
      refine ⟨hmap, by simp, ?_⟩
      intro xs hxs ys hys
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hxs
      rcases List.mem_singleton.mp hys with rfl
      simpa [G] using hfinal z hz
  have hblocks : blocks.IsChain G := houter.isChain
  have hflat := (List.isChain_flatten hempty).mpr ⟨hinternal, hblocks⟩
  simpa only [List.flatten_nil, blocks, List.flatten_cons, List.flatten_append, ← List.flatMap_def,
    List.flatten_singleton, List.singleton_append] using hflat

private theorem start_after_word (p : Route) (nodes : List ℂ) :
    (nodes.foldl Route.append p).start = p.start := by
  have h := eval_retained_after_word p nodes 0 0 rfl 0
  simpa only [Route.eval, AffineMap.lineMap_apply_zero, Fin.castSucc_zero,
    Route.start] using h


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
    simp [free_route, Route.segments_foldl_append, List.length_flatMap,
      Route.line, Nat.mul_comm, Nat.add_assoc, Nat.add_mul]
    omega

private theorem free_route_ends {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (L : List ι) (left middle right : ι → ℂ) :
    (free_route e L left middle right).start = ((referenceDrawing I).route e).start ∧
      (free_route e L left middle right).finish = ((referenceDrawing I).route e).finish := by
  cases L with
  | nil => exact ⟨rfl, rfl⟩
  | cons z zs =>
    constructor
    · exact (start_after_word _ _).trans (Route.start_line _ _)
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
    · apply Route.isSimple_of_strictMono_re
      exact append_word_point_order Complex.re _ _ nodes (by
        simpa only [nodes, List.flatMap_cons, List.cons_append, List.nil_append] using hword)
    · have hmono : StrictMono fun k =>
          -((free_route e (z :: zs) left middle right).point k).re :=
        append_word_point_order (fun w => -w.re) _ _ nodes (by
          simpa only [nodes, List.flatMap_cons, List.cons_append, List.nil_append] using
            hword.imp (by intro x y h; exact neg_lt_neg h))
      have hanti : StrictAnti fun k =>
          ((free_route e (z :: zs) left middle right).point k).re := by
        intro i j hij
        exact neg_lt_neg_iff.mp (hmono hij)
      have hrev : StrictMono fun k =>
          ((free_route e (z :: zs) left middle right).reverse.point k).re := by
        intro i j hij
        exact hanti (Fin.rev_lt_rev.mpr hij)
      have hs := Route.isSimple_of_strictMono_re hrev
      simpa only [Route.reverse_reverse] using hs.reverse

private theorem free_route_support {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (L : List ι) (left middle right : ι → ℂ) (S : Set ℂ)
    (hold : ((referenceDrawing I).route e).support ⊆ S)
    (hword : (((referenceDrawing I).route e).start ::
      L.flatMap (fun z => [left z, middle z, right z]) ++
      [((referenceDrawing I).route e).finish]).IsChain (fun x y => segment ℝ x y ⊆ S)) :
    (free_route e L left middle right).support ⊆ S := by
  cases L with
  | nil => exact hold
  | cons z zs =>
    apply append_word_support
    simpa only [List.flatMap_cons, List.cons_append, List.nil_append] using hword


private theorem free_route_first_germ {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (z : ι) (zs : List ι) (left middle right : ι → ℂ) :
    (free_route e (z :: zs) left middle right).germ false =
      left z - ((referenceDrawing I).route e).start :=
  first_germ_after_word _ _ _

private theorem free_route_last_germ {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (L : List ι) (hne : L ≠ []) (left middle right : ι → ℂ) :
    (free_route e L left middle right).germ true =
      right (L.getLast hne) - ((referenceDrawing I).route e).finish := by
  let last := L.getLast hne
  have hsplit : L = L.dropLast ++ [last] := (List.dropLast_append_getLast hne).symm
  have hf (p : Route) (a : ℂ) : (p.append a).finish = a := Route.endpoint_append p a true
  cases hpre : L.dropLast with
  | nil =>
    have hL : L = [last] := by simpa only [hpre, List.nil_append] using hsplit
    conv_lhs => rw [hL]
    simp only [free_route, List.flatMap_nil, List.nil_append, List.cons_append, List.foldl_cons,
      List.foldl_nil, Route.germ_append, hf, ↓reduceIte]
    rfl
  | cons z zs =>
    have hL : L = z :: (zs ++ [last]) := by simpa only [hpre, List.cons_append] using hsplit
    conv_lhs => rw [hL]
    simp only [free_route, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.nil_append, List.append_assoc, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Route.germ_append, hf, ↓reduceIte]
    rfl


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
  have hbetween : L.Pairwise fun z w => ξ (right z) < ξ (left w) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hz := List.getElem_mem hi
    have hw := List.getElem_mem hj
    have hzw := (List.pairwise_iff_getElem.mp hsorted) i j hi hj hij
    rw [hright _ hz, hleft _ hw, hproj, hproj]
    exact (lineMap_lt_lineMap_iff_of_lt' hab).mpr hzw
  have hchain := chain_patch_word L a b left middle right
    (fun x y => ξ x < ξ y) hab hfirst hfinal hlocal hbetween
  have hreal : ((a :: L.flatMap (fun z => [left z, middle z, right z]) ++ [b]).map ξ).IsChain
      (· < ·) := by
    simpa only [List.isChain_map] using hchain
  have hpair := (List.isChain_iff_pairwise).mp hreal
  simpa only [List.pairwise_map] using hpair


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
    have hi : i = 0 := by
        apply Fin.ext
        change i.val = 0
        have h := i.isLt
        change i.val < 1 at h
        omega
    subst i
    exact ⟨_, _, rfl, rfl, Route.eval_line _ _ 0 t⟩
  | cons z zs =>
    let nodes := [middle z, right z] ++ zs.flatMap (fun w => [left w, middle w, right w]) ++
      [((referenceDrawing I).route e).finish]
    let word := ((referenceDrawing I).route e).start :: left z :: nodes
    have hi : i.val < word.length := by
      have hh := i.isLt
      simp only [free_route_segments] at hh
      simp only [word, nodes, List.length_cons, List.length_append, List.length_flatMap]
      simp only [List.length_cons] at hh
      simp at *; omega
    have hi1 : i.val + 1 < word.length := by
      have hh := i.isLt
      simp only [free_route_segments] at hh
      simp [word, nodes, List.length_flatMap] at *; omega
    refine ⟨word[i.val], word[i.val + 1], ?_, ?_, ?_⟩
    · simpa only [word, nodes, List.flatMap_cons, List.cons_append, List.nil_append]
        using (List.getElem?_eq_getElem hi)
    · simpa only [word, nodes, List.flatMap_cons, List.cons_append, List.nil_append]
        using (List.getElem?_eq_getElem hi1)
    · exact Route.eval_foldl_append_line _ _ nodes i t


private theorem free_route_patch_eval {I : FixedRotationInput}
    (e : Fin (subdivisionGraph I).edges.length) {ι : Type*}
    (L : List ι) (left middle right : ι → ℂ) (q : Fin L.length) (j : Fin 2) :
    ∃ i : Fin (free_route e L left middle right).segments,
      i.val = 3 * q.val + 1 + j.val ∧ ∀ t : ℝ,
        (free_route e L left middle right).eval i t =
          AffineMap.lineMap ([left L[q], middle L[q], right L[q]][j.castSucc])
            ([left L[q], middle L[q], right L[q]][j.succ]) t := by
  let i : Fin (free_route e L left middle right).segments :=
    ⟨3 * q.val + 1 + j.val, by
      simp only [free_route_segments]
      have hq := q.isLt
      have hj := j.isLt
      omega⟩
  refine ⟨i, rfl, ?_⟩
  intro t
  obtain ⟨a, b, ha, hb, he⟩ := free_route_eval_nodes e L left middle right i t
  have hleft := patch_node_get L ((referenceDrawing I).route e).start
    ((referenceDrawing I).route e).finish left middle right q j.castSucc
  have hright := patch_node_get L ((referenceDrawing I).route e).start
    ((referenceDrawing I).route e).finish left middle right q j.succ
  rw [show i.val = 3 * q.val + 1 + j.castSucc.val from rfl, hleft] at ha
  rw [show i.val + 1 = 3 * q.val + 1 + j.succ.val by
      dsimp only [i]
      simp only [Fin.val_succ]
      omega,
    hright] at hb
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


/-- Construct one complete named-field reference patch assembly from `Valid I` alone.
All selected data and proofs refer to its single drawing; global contact regularization
and the HT criterion remain open. -/
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
  have hlocal (z : C) := exists_reference_detour_placement hI z.property (hρ z.val z.property)
  choose r hr d α β hcuts hkeep hpair htrans hno3 using hlocal
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
  have hmargins (e : E) (z : Z e) :
      0 < cutα e z ∧ cutα e z < cutβ e z ∧ cutβ e z < 1 := by
    obtain ⟨ha, hab, hb, _, _, _, _⟩ := hcuts (site e z) (occurrence e z)
    exact ⟨ha, hab, hb⟩
  have hαball (e : E) (z : Z e) : left e z ∈ Metric.ball z.val (ρ z.val) := by
    obtain ⟨_, _, _, hs, _, _, hball⟩ := hcuts (site e z) (occurrence e z)
    have hw := hball ((P (site e z) (occurrence e z)).at_mem_support 0
      (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩))
    change (P (site e z) (occurrence e z)).eval 0 0 ∈ Metric.ball z.val (ρ z.val) at hw
    rw [Route.eval, AffineMap.lineMap_apply_zero] at hw
    change (P (site e z) (occurrence e z)).start ∈ Metric.ball z.val (ρ z.val) at hw
    simpa only [hs] using hw
  have hβball (e : E) (z : Z e) : right e z ∈ Metric.ball z.val (ρ z.val) := by
    obtain ⟨_, _, _, _, hf, _, hball⟩ := hcuts (site e z) (occurrence e z)
    have hw := hball ((P (site e z) (occurrence e z)).at_mem_support
      (Fin.last (P (site e z) (occurrence e z)).bends)
      (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩))
    change (P (site e z) (occurrence e z)).eval (Fin.last _ ) 1 ∈ Metric.ball z.val (ρ z.val) at hw
    rw [Route.eval, AffineMap.lineMap_apply_one, Fin.succ_last] at hw
    change (P (site e z) (occurrence e z)).finish ∈ Metric.ball z.val (ρ z.val) at hw
    simpa only [hf] using hw
  have hordered (e : E) : ∃ L : List (Z e), L.Nodup ∧ (∀ z : Z e, z ∈ L) ∧
      L.Pairwise (fun z w => cutβ e z < cutα e w) := by
    have hCe : {z : ℂ | z ∈ C ∧ z ∈ (D.route e).support}.Finite :=
      hC.subset fun _ hz => hz.1
    apply sorted_reference_cuts I e _ hCe ρ (cutα e) (cutβ e)
      (fun z => (hmargins e z).2.1) ?_ (hαball e) (hβball e)
    intro z hz w hw hzw
    exact hballs hz.1 hw.1 hzw
  choose L hnd hmem hsorted using hordered
  have hfree (e : E) (he : F e = false) (z : Z e) :
      P (site e z) (occurrence e z) =
        (if decide ((D.route e).finish.re < (D.route e).start.re) then
          (Route.slopeDetour (r (site e z)) (s (site e z) (occurrence e z))
            (d (site e z) (occurrence e z))).reverse else
          Route.slopeDetour (r (site e z)) (s (site e z) (occurrence e z))
            (d (site e z) (occurrence e z))).translate z.val := by
    simp only [P, R, occurrence, he, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hpieces (e : E) (he : F e = false) (z : Z e) :
      (∀ t : ℝ, (P (site e z) (occurrence e z)).eval 0 t =
        AffineMap.lineMap (left e z) (middle e z) t) ∧
      (∀ t : ℝ, (P (site e z) (occurrence e z)).eval 1 t =
        AffineMap.lineMap (middle e z) (right e z) t) := by
    obtain ⟨_, _, _, hs, hf, _, _⟩ := hcuts (site e z) (occurrence e z)
    have hp := free_local_pieces (r (site e z)) (s (site e z) (occurrence e z))
      (d (site e z) (occurrence e z)) z.val
      (decide ((D.route e).finish.re < (D.route e).start.re))
    rw [← hfree e he z] at hp
    change (P (site e z) (occurrence e z)).start = left e z at hs
    change (P (site e z) (occurrence e z)).finish = right e z at hf
    simpa only [hs, hf] using hp
  have hmiddle_ball (e : E) (he : F e = false) (z : Z e) :
      middle e z ∈ Metric.ball z.val (ρ z.val) := by
    obtain ⟨_, _, _, _, _, _, hball⟩ := hcuts (site e z) (occurrence e z)
    have hw := hball ((P (site e z) (occurrence e z)).at_mem_support 0
      (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩))
    rw [(hpieces e he z).1 1, AffineMap.lineMap_apply_one] at hw
    exact hw
  let S : E → Set ℂ := fun e => (D.route e).support ∪ ⋃ z ∈ C, Metric.ball z (ρ z)
  have hOldConvex (e : E) : Convex ℝ (D.route e).support := by
    exact (Route.support_line (D.route e).start (D.route e).finish).symm ▸
      convex_segment _ _
  have hOldStart (e : E) : (D.route e).start ∈ (D.route e).support :=
    (Route.support_line (D.route e).start (D.route e).finish).symm ▸ left_mem_segment ℝ _ _
  have hOldFinish (e : E) : (D.route e).finish ∈ (D.route e).support :=
    (Route.support_line (D.route e).start (D.route e).finish).symm ▸ right_mem_segment ℝ _ _
  have hLeftOld (e : E) (z : Z e) : left e z ∈ (D.route e).support := by
    exact (hOldConvex e).lineMap_mem (hOldStart e) (hOldFinish e)
      ⟨(hmargins e z).1.le, ((hmargins e z).2.1.trans (hmargins e z).2.2).le⟩
  have hRightOld (e : E) (z : Z e) : right e z ∈ (D.route e).support := by
    exact (hOldConvex e).lineMap_mem (hOldStart e) (hOldFinish e)
      ⟨((hmargins e z).1.trans (hmargins e z).2.1).le, (hmargins e z).2.2.le⟩
  have hWordS (e : E) (he : F e = false) :
      ((D.route e).start :: (L e).flatMap (fun z => [left e z, middle e z, right e z]) ++
        [(D.route e).finish]).IsChain (fun x y => segment ℝ x y ⊆ S e) := by
    have hold (x y : ℂ) (hx : x ∈ (D.route e).support) (hy : y ∈ (D.route e).support) :
        segment ℝ x y ⊆ S e :=
      ((hOldConvex e).segment_subset hx hy).trans (fun _ h => Or.inl h)
    apply chain_patch_word (L e) (D.route e).start (D.route e).finish
      (left e) (middle e) (right e) (fun x y => segment ℝ x y ⊆ S e)
      (hold _ _ (hOldStart e) (hOldFinish e))
      (fun z _ => hold _ _ (hOldStart e) (hLeftOld e z))
      (fun z _ => hold _ _ (hRightOld e z) (hOldFinish e))
    · intro z _
      have hballS : Metric.ball z.val (ρ z.val) ⊆ S e := fun _ hw =>
        Or.inr (Set.mem_iUnion₂.mpr ⟨z.val, z.property.1, hw⟩)
      exact ⟨((convex_ball z.val (ρ z.val)).segment_subset
          (hαball e z) (hmiddle_ball e he z)).trans hballS,
        ((convex_ball z.val (ρ z.val)).segment_subset
          (hmiddle_ball e he z) (hβball e z)).trans hballS⟩
    · exact (hsorted e).imp (by intro z w _; exact hold _ _ (hRightOld e z) (hLeftOld e w))
  have hCoords (e : E) (he : F e = false) (z : Z e) :
      (left e z).re = z.val.re +
        (if (D.route e).finish.re < (D.route e).start.re then r (site e z) else -r (site e z)) ∧
      (right e z).re = z.val.re +
        (if (D.route e).finish.re < (D.route e).start.re then -r (site e z) else r (site e z)) := by
    obtain ⟨_, _, _, hs, hf, _, _⟩ := hcuts (site e z) (occurrence e z)
    have hx := free_local_real_ends (r (site e z)) (s (site e z) (occurrence e z))
      (d (site e z) (occurrence e z)) z.val
      (decide ((D.route e).finish.re < (D.route e).start.re))
    rw [← hfree e he z] at hx
    change (P (site e z) (occurrence e z)).start = left e z at hs
    change (P (site e z) (occurrence e z)).finish = right e z at hf
    by_cases hd : (D.route e).finish.re < (D.route e).start.re <;>
      simpa only [hs, hf, hd, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] using hx
  have hMiddleRe (e : E) (z : Z e) : (middle e z).re = z.val.re := by
    simp only [middle, Complex.add_re, add_zero]
  have hWordOrder (e : E) (he : F e = false) :
      ((D.route e).start :: (L e).flatMap (fun z => [left e z, middle e z, right e z]) ++
        [(D.route e).finish]).Pairwise (fun x y => x.re < y.re) ∨
      ((D.route e).start :: (L e).flatMap (fun z => [left e z, middle e z, right e z]) ++
        [(D.route e).finish]).Pairwise (fun x y => y.re < x.re) := by
    have hne : (D.route e).start.re ≠ (D.route e).finish.re :=
      (parabolaPoint_injective.eq_iff.not).mp
        ((Route.isSimple_line_iff _ _).mp (referenceDrawing_simple hI e))
    rcases lt_or_gt_of_ne hne with hab | hba
    · left
      apply word_order_from_cuts (L e) (D.route e).start (D.route e).finish
        (left e) (middle e) (right e) (cutα e) (cutβ e) Complex.re hab
        (fun t => Complex.reCLM.toLinearMap.toAffineMap.apply_lineMap _ _ t)
        (fun _ _ => rfl) (fun _ _ => rfl)
        (fun z _ => (hmargins e z).1) (fun z _ => (hmargins e z).2.2) ?_ (hsorted e)
      intro z _
      have hx := hCoords e he z
      have hrz := hr (site e z)
      simp only [ite_eq_right (not_lt_of_ge hab.le)] at hx
      rw [hMiddleRe]
      constructor <;> linarith [hx.1, hx.2]
    · right
      have hneg := word_order_from_cuts (L e) (D.route e).start (D.route e).finish
        (left e) (middle e) (right e) (cutα e) (cutβ e) (fun w => -w.re)
        (neg_lt_neg hba)
        (fun t => (-Complex.reCLM).toLinearMap.toAffineMap.apply_lineMap _ _ t)
        (fun _ _ => rfl) (fun _ _ => rfl)
        (fun z _ => (hmargins e z).1) (fun z _ => (hmargins e z).2.2)
        (fun z _ => by
          have hx := hCoords e he z
          have hrz := hr (site e z)
          simp only [ite_eq_left hba] at hx
          rw [hMiddleRe]
          constructor <;> linarith [hx.1, hx.2]) (hsorted e)
      exact hneg.imp (by intro x y h; exact neg_lt_neg_iff.mp h)
  let Q : E → Route := fun e => if F e then D.route e else
    free_route e (L e) (left e) (middle e) (right e)
  have hends (e : E) : (Q e).start = (D.route e).start ∧ (Q e).finish = (D.route e).finish := by
    cases hf : F e
    · simp only [Q, hf, Bool.false_eq_true, ↓reduceIte]
      exact free_route_ends e (L e) (left e) (middle e) (right e)
    · simp [Q, hf]
  have hsimple (e : E) : (Q e).IsSimple := by
    cases hf : F e
    · simp only [Q, hf, Bool.false_eq_true, ↓reduceIte]
      exact free_route_simple hI e (L e) (left e) (middle e) (right e) (hWordOrder e hf)
    · simp only [Q, hf, ↓reduceIte]
      exact referenceDrawing_simple hI e
  have hsupport (e : E) : (Q e).support ⊆ S e := by
    cases hf : F e
    · simp only [Q, hf, Bool.false_eq_true, ↓reduceIte]
      exact free_route_support e (L e) (left e) (middle e) (right e) (S e)
        (fun _ hw => Or.inl hw) (hWordS e hf)
    · simp only [Q, hf, ↓reduceIte]
      exact fun _ hw => Or.inl hw
  have hvertices (e : E) := vertex_contacts_from_support hI e C ρ
    (fun z hz v hv hw => (hexclude z hz).1 v hv (Metric.ball_subset_closedBall hw))
    (Q e) (hsimple e) (hends e).1 (hends e).2 (hsupport e)
  let D' : PolygonalDrawing H :=
    ⟨D.vertex, Q, fun e tag => by
      cases tag
      · exact (hends e).1.trans (D.endpoint_eq e false)
      · exact (hends e).2.trans (D.endpoint_eq e true)⟩
  have hgerms (e : E) (tag : Bool) :
      ∃ c : ℝ, 0 < c ∧ (Q e).germ tag = c • (D.route e).germ tag := by
    cases hf : F e
    · cases hL : L e with
      | nil =>
        refine ⟨1, zero_lt_one, ?_⟩
        simp only [Q, hf, Bool.false_eq_true, ↓reduceIte, hL, free_route, one_smul]
        rfl
      | cons z zs =>
        cases tag
        · refine ⟨cutα e z, (hmargins e z).1, ?_⟩
          simp only [Q, hf, Bool.false_eq_true, ↓reduceIte, hL, free_route_first_germ]
          change AffineMap.lineMap (D.route e).start (D.route e).finish (cutα e z) -
            (D.route e).start = cutα e z • ((D.route e).finish - (D.route e).start)
          exact AffineMap.lineMap_vsub_left (k := ℝ) (D.route e).start (D.route e).finish _
        · let last := (z :: zs).getLast (by simp)
          refine ⟨1 - cutβ e last, sub_pos.mpr (hmargins e last).2.2, ?_⟩
          simp only [Q, hf, Bool.false_eq_true, ↓reduceIte, hL]
          rw [free_route_last_germ e (z :: zs) (by simp)]
          change AffineMap.lineMap (D.route e).start (D.route e).finish (cutβ e last) -
            (D.route e).finish = (1 - cutβ e last) • ((D.route e).start - (D.route e).finish)
          exact AffineMap.lineMap_vsub_right (k := ℝ) (D.route e).start (D.route e).finish _
    · refine ⟨1, zero_lt_one, ?_⟩
      simp only [Q, hf, ↓reduceIte, one_smul]
  have hsegfree (e : E) (he : F e = false) (z : Z e) :
      (P (site e z) (occurrence e z)).segments = 2 := by
    rw [hfree e he z]
    cases hflip : decide ((D.route e).finish.re < (D.route e).start.re) <;> rfl
  have hlocal_embed (e : E) (q : Fin (L e).length) :
      let z := (L e)[q]
      let p := P (site e z) (occurrence e z)
      (F e = false → ∀ j : Fin p.segments,
        ∃ i : Fin (Q e).segments, i.val = 3 * q.val + 1 + j.val ∧
          ∀ t : ℝ, (Q e).eval i t = p.eval j t) ∧
      (F e = true → ∀ t : ℝ,
        (Q e).eval 0 (cutα e z + (cutβ e z - cutα e z) * t) = p.eval 0 t) := by
    let z := (L e)[q]
    constructor
    · intro he j
      let j' : Fin 2 := ⟨j.val, hsegfree e he z ▸ j.isLt⟩
      obtain ⟨i, hi, hieval⟩ := free_route_patch_eval e (L e)
        (left e) (middle e) (right e) q j'
      have hQ : Q e = free_route e (L e) (left e) (middle e) (right e) := by
        simp only [Q, he, Bool.false_eq_true, ↓reduceIte]
      rw [hQ]
      refine ⟨i, hi, ?_⟩
      intro t
      rw [hieval]
      have hj : j.val = j'.val := rfl
      have hp := hpieces e he z
      have hjlt : j'.val < 2 := j'.isLt
      rcases (show j'.val = 0 ∨ j'.val = 1 by omega) with hj0 | hj1
      · have hj0' : j = 0 := Fin.ext (hj.trans hj0)
        have hj0'' : j' = 0 := Fin.ext hj0
        rw [hj0', hj0'']
        exact (hp.1 t).symm
      · have hj1' : j = 1 := Fin.ext (by
          calc
            j.val = 1 := hj.trans hj1
            _ = (1 : Fin (P (site e z) (occurrence e z)).segments).val := by
              change 1 = 1 % _
              rw [hsegfree e he z])
        have hj1'' : j' = 1 := Fin.ext hj1
        rw [hj1', hj1'']
        exact (hp.2 t).symm
    · intro he t
      have hQ : Q e = D.route e := by simp only [Q, he, ↓reduceIte]
      obtain ⟨_, hp⟩ := hkeep (site e z) (occurrence e z) he
      rw [hQ]
      change (D.route e).eval 0 _ = (P (site e z) (occurrence e z)).eval 0 t
      rw [hp]
      exact (frozen_cut_parameter (D.route e).start (D.route e).finish
        (cutα e z) (cutβ e z) t).symm
  have hraw_embed (e : E) (he : F e = false) (q : Fin (L e).length) :
      let z := (L e)[q]
      let raw := R (site e z) (occurrence e z)
      ∃ i : Fin (Q e).segments,
        i.val = 3 * q.val +
          (if (D.route e).finish.re < (D.route e).start.re then 2 else 1) ∧
        ∀ t : ℝ,
          (Q e).eval i (if (D.route e).finish.re < (D.route e).start.re then 1 - t else t) =
            z.val + raw.eval 0 t := by
    let z := (L e)[q]
    by_cases hd : (D.route e).finish.re < (D.route e).start.re
    · have hp : P (site e z) (occurrence e z) =
          (R (site e z) (occurrence e z)).reverse.translate z.val := by
        dsimp only [P, occurrence, site]
        rw [ite_eq_left (by simpa only [decide_eq_true_eq] using hd)]
      have hn : (R (site e z) (occurrence e z)).segments = 2 := by
        dsimp only [R, occurrence]
        rw [ite_eq_right (by simp only [he, Bool.false_eq_true, not_false_eq_true])]
        rfl
      let j : Fin (P (site e z) (occurrence e z)).segments :=
        ⟨1, by rw [hsegfree e he z]; decide⟩
      obtain ⟨i, hi, hieval⟩ := (hlocal_embed e q).1 he j
      refine ⟨i, by simpa only [hd, ↓reduceIte, j] using hi, ?_⟩
      intro t
      rw [ite_eq_left hd, hieval]
      -- Keep the segment binder while transporting the route equality: its bound
      -- depends on the route, whereas the numerical segment value stays one.
      have hEval : ∀ k : Fin (P (site e z) (occurrence e z)).segments,
          k.val = 1 → (P (site e z) (occurrence e z)).eval k (1 - t) =
            z.val + (R (site e z) (occurrence e z)).eval 0 t := by
        rw [hp]
        intro k hk
        change Fin ((R (site e z) (occurrence e z)).bends + 1) at k
        rw [Route.eval_translate (R (site e z) (occurrence e z)).reverse z.val k (1 - t),
          Route.eval_reverse (R (site e z) (occurrence e z)) k (1 - t)]
        have hkrev : k.rev = 0 := by
          apply Fin.ext
          simp only [Fin.val_rev, Fin.val_zero]
          have hn' : (R (site e z) (occurrence e z)).bends + 1 = 2 := hn
          omega
        exact (congrArg (fun l : Fin ((R (site e z) (occurrence e z)).bends + 1) =>
          z.val + (R (site e z) (occurrence e z)).eval l (1 - (1 - t))) hkrev).trans
            (congrArg (fun u : ℝ => z.val + (R (site e z) (occurrence e z)).eval 0 u)
              (sub_sub_cancel 1 t))
      exact hEval j rfl
    · have hp : P (site e z) (occurrence e z) =
          (R (site e z) (occurrence e z)).translate z.val := by
        dsimp only [P, occurrence, site]
        rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hd)]
      let j : Fin (P (site e z) (occurrence e z)).segments := 0
      obtain ⟨i, hi, hieval⟩ := (hlocal_embed e q).1 he j
      refine ⟨i, by simpa only [hd, ↓reduceIte, j, Fin.val_zero, Nat.add_zero] using hi, ?_⟩
      intro t
      rw [ite_eq_right hd, hieval]
      have hEval : ∀ k : Fin (P (site e z) (occurrence e z)).segments,
          k.val = 0 → (P (site e z) (occurrence e z)).eval k t =
            z.val + (R (site e z) (occurrence e z)).eval 0 t := by
        rw [hp]
        intro k hk
        have hkzero : k = 0 := Fin.ext hk
        subst k
        exact Route.eval_translate _ _ _ _
      exact hEval j rfl
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
    cut_bounds := ?_
    patch_start := ?_
    patch_finish := ?_
    patch_simple := ?_
    patch_support := ?_
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
    segments_eq := ?_
    simple := hsimple
    vertex_contacts := hvertices
    germs := hgerms
    patch_embedding := hlocal_embed
    raw_first_embedding := hraw_embed }⟩
  · intro z e
    obtain ⟨ha, hab, hb, _⟩ := hcuts z e
    exact ⟨ha, hab, hb⟩
  · intro z e
    obtain ⟨_, _, _, hs, _⟩ := hcuts z e
    exact hs
  · intro z e
    obtain ⟨_, _, _, _, hf, _⟩ := hcuts z e
    exact hf
  · intro z e
    obtain ⟨_, _, _, _, _, hs, _⟩ := hcuts z e
    exact hs
  · intro z e
    obtain ⟨_, _, _, _, _, _, hb⟩ := hcuts z e
    exact hb
  · dsimp only
    intro e
    cases hf : F e <;> cases hL : L e <;>
      dsimp only [F] at hf <;>
      simp only [D', Q, free_route, F, D, site, occurrence, cutα, cutβ, left, middle,
        right, hf, hL, Bool.false_eq_true, ↓reduceIte]; rfl
  · intro e he
    change F e = false at he
    change (Q e).segments = _
    simp only [Q, he, Bool.false_eq_true, ↓reduceIte]
    exact free_route_segments e (L e) (left e) (middle e) (right e)


end Cslib.Complexity.Graph.RotationRecognition
