/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.SegmentCuts
import CslibFrontier.Foundations.Geometry.Polygonal.AttachmentParameters
import CslibFrontier.Foundations.Geometry.Polygonal.CoordinateOrder
import CslibFrontier.Foundations.Geometry.Polygonal.Germs
import CslibFrontier.Foundations.Data.List.ConsecutivePairs
import CslibFrontier.Foundations.Data.List.FlatMapPositions
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polygonal route images across coordinate cuts

Split each indexed source segment at a finite set of levels of an affine coordinate, keep
the samples in source order, and join the mapped samples. When interpolation is preserved
between levels, the resulting route has exactly the image support and has the same tagged
endpoints under the map. An injective map preserves simplicity, including closed routes.
The construction and its indexed proofs are shared by plateau shear and inverse strip
compression.
-/

public section

namespace Cslib.Polygonal.Route

open scoped BigOperators

private noncomputable abbrev cuts (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (a b : ℂ) : List ℝ :=
  segmentCuts S (c a) (c b)

private theorem cuts_length_bounds (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (a b : ℂ) :
    2 ≤ (cuts S c a b).length ∧ (cuts S c a b).length ≤ S.card + 2 := by
  have h := segmentInteriorCuts_card_le S (c a) (c b)
  simp only [cuts, segmentCuts_length_eq]
  omega

private noncomputable def sourceBlock (p : Route) (S : Finset ℝ)
    (c : ℂ →ᵃ[ℝ] ℝ) (i : Fin p.segments) :
    List (Fin p.segments × ℝ) :=
  (cuts S c (p.point i.castSucc) (p.point i.succ)).dropLast.map fun t => (i, t)

private noncomputable def sourceSamples (p : Route) (S : Finset ℝ)
    (c : ℂ →ᵃ[ℝ] ℝ) : List (Fin p.segments × ℝ) :=
  ((List.finRange p.segments).flatMap (sourceBlock p S c)) ++
      [(Fin.last p.bends, 1)]

private def sourcePosition {p : Route} (x : Fin p.segments × ℝ) : ℝ :=
  (x.1.val : ℝ) + x.2

private theorem sourceSamples_ordered (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) :
    (sourceSamples p S c).Pairwise (fun a b => sourcePosition a < sourcePosition b) := by
  rw [sourceSamples, List.pairwise_append]
  refine ⟨?_, by simp, ?_⟩
  · rw [List.pairwise_flatMap]
    constructor
    · intro i _
      apply List.pairwise_map.mpr
      exact (((segmentCuts_sorted S (c (p.point i.castSucc))
        (c (p.point i.succ))).pairwise).sublist (List.dropLast_sublist _)).imp
        fun hab => by dsimp [sourcePosition]; linarith
    · apply (List.sortedLT_finRange p.segments).pairwise.imp
      intro i j hij x hx y hy
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
      have hstep : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
      dsimp [sourcePosition]
      linarith [segmentCuts_dropLast_bounds hs, segmentCuts_dropLast_bounds ht]
  · rintro x hx _ hy
    obtain ⟨i, _, ht⟩ := List.mem_flatMap.mp hx
    obtain ⟨t, hcut, rfl⟩ := List.mem_map.mp ht
    obtain rfl := List.mem_singleton.mp hy
    have hi : i.val ≤ p.bends := by have := i.isLt; dsimp [Route.segments] at *; omega
    have ht' := segmentCuts_dropLast_bounds hcut
    dsimp [sourcePosition]
    cast_linarith [hi]

private theorem sourceBlock_length (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (i : Fin p.segments) :
    1 ≤ (sourceBlock p S c i).length ∧ (sourceBlock p S c i).length ≤ S.card + 1 := by
  have hc := cuts_length_bounds S c (p.point i.castSucc) (p.point i.succ)
  simp only [sourceBlock, List.length_map, List.length_dropLast]
  omega

private theorem sourceBlock_ne_nil (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (i : Fin p.segments) :
    sourceBlock p S c i ≠ [] :=
  List.ne_nil_of_length_pos (sourceBlock_length p S c i).1

private theorem sourceBlock_head (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (i : Fin p.segments) :
    (sourceBlock p S c i).head (sourceBlock_ne_nil p S c i) = (i, 0) := by
  simp only [List.head_eq_getElem, sourceBlock, List.getElem_map, List.getElem_dropLast,
    (segmentCuts_first_last S (c (p.point i.castSucc)) (c (p.point i.succ))).1]

private theorem sourceBlock_last (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (i : Fin p.segments) :
    (sourceBlock p S c i).getLast (sourceBlock_ne_nil p S c i) =
      (i, (cuts S c (p.point i.castSucc) (p.point i.succ))[
        (cuts S c (p.point i.castSucc) (p.point i.succ)).length - 2]'(by
          have := cuts_length_bounds S c (p.point i.castSucc) (p.point i.succ); omega)) := by
  simp only [List.getLast_eq_getElem, sourceBlock, List.length_map, List.length_dropLast,
    List.getElem_map, List.getElem_dropLast, Nat.sub_sub]

private theorem sourceSamples_length_eq_sum (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) :
    (sourceSamples p S c).length =
      (∑ i : Fin p.segments, (sourceBlock p S c i).length) + 1 := by
  simp only [sourceSamples, List.length_append, List.length_singleton, List.length_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

private theorem sourceSamples_length (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) :
    p.segments + 1 ≤ (sourceSamples p S c).length ∧
      (sourceSamples p S c).length ≤ (S.card + 1) * p.segments + 1 := by
  have hlo := Finset.card_nsmul_le_sum Finset.univ _ 1 fun i _ => (sourceBlock_length p S c i).1
  have hhi := Finset.sum_le_card_nsmul Finset.univ _ _ fun i _ => (sourceBlock_length p S c i).2
  simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.mul_comm p.segments] at hlo hhi
  rw [sourceSamples_length_eq_sum]
  omega

private theorem sourceSamples_nontrivial (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) :
    ∃ x y rest, sourceSamples p S c = x :: y :: rest := by
  have hn := (sourceSamples_length p S c).1
  match h : sourceSamples p S c with
  | [] | [_] => simp [h, Route.segments] at hn
  | x :: y :: rest => exact ⟨x, y, rest, rfl⟩

private theorem sourceSamples_ends (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) :
    (sourceSamples p S c)[0]'(by have := sourceSamples_length p S c; omega) = (0, 0) ∧
      (sourceSamples p S c)[(sourceSamples p S c).length - 1]'(by
        have := sourceSamples_length p S c; omega) = (Fin.last p.bends, 1) := by
  have hfin : List.finRange p.segments ≠ [] := by simp [Route.segments]
  have hsource : sourceSamples p S c ≠ [] := by simp [sourceSamples]
  constructor
  · rw [← List.head_eq_getElem hsource]
    change (((List.finRange p.segments).flatMap (sourceBlock p S c)) ++
        [(Fin.last p.bends,1)]).head (by simp) = (0,0)
    rw [List.head_append_of_ne_nil (List.flatMap_ne_nil hfin fun i _ => sourceBlock_ne_nil p S c i),
      List.head_flatMap hfin (fun i _ => sourceBlock_ne_nil p S c i), sourceBlock_head]
    congr 1
    exact Fin.ext (by simp [List.head_eq_getElem])
  · rw [← List.getLast_eq_getElem hsource]
    exact List.getLast_append_of_ne_nil (by simp) (List.cons_ne_nil _ _)

-- The two source descriptions at a shared old knot are retained; only their geometric
-- endpoint equality is used. No lookup by geometric point value occurs here.
private theorem final_cut_endpoint (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (a b : ℂ) :
    (cuts S c a b)[(cuts S c a b).length - 2 + 1]'(by
      have hlen := cuts_length_bounds S c a b
      omega) = 1 := by
  have hlen := cuts_length_bounds S c a b
  have hidx : (cuts S c a b).length - 2 + 1 = (cuts S c a b).length - 1 := by omega
  simpa only [hidx] using (segmentCuts_first_last S (c a) (c b)).2

private theorem sourceSamples_adjacent (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ)
    {x y : Fin p.segments × ℝ} (hxy : (x, y) ∈ (sourceSamples p S c).consecutivePairs) :
    ∃ (i : Fin p.segments) (k : ℕ)
      (hk : k + 1 < (cuts S c (p.point i.castSucc) (p.point i.succ)).length),
      p.eval x.1 x.2 = p.eval i (cuts S c (p.point i.castSucc) (p.point i.succ))[k] ∧
      p.eval y.1 y.2 = p.eval i (cuts S c (p.point i.castSucc) (p.point i.succ))[k + 1] ∧
      sourcePosition x = p.position i (cuts S c (p.point i.castSucc) (p.point i.succ))[k] ∧
      sourcePosition y = p.position i (cuts S c (p.point i.castSucc) (p.point i.succ))[k + 1] := by
  let L := List.finRange p.segments
  let f := sourceBlock p S c
  have hL : L ≠ [] := by simp [L, Route.segments]
  have hf (i : Fin p.segments) : f i ≠ [] := sourceBlock_ne_nil p S c i
  have hflat := List.flatMap_ne_nil hL (fun i _ => hf i)
  rw [sourceSamples, List.consecutivePairs_append hflat (List.cons_ne_nil _ _)] at hxy
  rcases List.mem_append.mp hxy with hxy | hxy
  · rcases (List.mem_consecutivePairs_flatMap hL hf).mp hxy with
      ⟨i, _, hxy⟩ | ⟨⟨i, j⟩, hij, hx, hy⟩
    · obtain ⟨k, hk, hx, hy⟩ := List.mem_consecutivePairs_iff_exists_getElem.mp hxy
      simp only [f, sourceBlock, List.length_map, List.length_dropLast, List.getElem_map,
        List.getElem_dropLast] at hk hx hy
      subst hx hy
      exact ⟨i, k, by omega, rfl, rfl, rfl, rfl⟩
    · obtain ⟨k, hk, hi, hj⟩ := List.mem_consecutivePairs_iff_exists_getElem.mp hij
      have hji : j.val = i.val + 1 := by simp [← hi, ← hj, L]
      obtain rfl := hx.trans (sourceBlock_last p S c i)
      obtain rfl := hy.trans (sourceBlock_head p S c j)
      let C := cuts S c (p.point i.castSucc) (p.point i.succ)
      have hlen := cuts_length_bounds S c (p.point i.castSucc) (p.point i.succ)
      have hend := final_cut_endpoint S c (p.point i.castSucc) (p.point i.succ)
      refine ⟨i, C.length - 2, by dsimp [C]; omega, rfl, ?_, rfl, ?_⟩
      · simp only [C, hend, Route.eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
          (Fin.ext hji : j.castSucc = i.succ)]
      · simp only [C, hend, sourcePosition, Route.position, hji, Nat.cast_add, Nat.cast_one]
        ring
  · rcases List.mem_cons.mp hxy with heq | hempty
    · have hlast : L.getLast hL = Fin.last p.bends :=
        Fin.ext (by simp [List.getLast_eq_getElem, L, Route.segments])
      have hx : x = (f (Fin.last p.bends)).getLast (hf _) := by
        simpa only [List.getLast_flatMap hL (fun i _ => hf i), hlast] using congrArg Prod.fst heq
      have hy : y = (Fin.last p.bends, 1) := by
        simpa only [List.head_cons] using congrArg Prod.snd heq
      rw [sourceBlock_last] at hx
      subst hx hy
      let i := Fin.last p.bends
      let C := cuts S c (p.point i.castSucc) (p.point i.succ)
      have hlen := cuts_length_bounds S c (p.point i.castSucc) (p.point i.succ)
      have hend := final_cut_endpoint S c (p.point i.castSucc) (p.point i.succ)
      refine ⟨i, C.length - 2, by dsimp [C]; omega, rfl, ?_, rfl, ?_⟩
      · rw [hend]
      · rw [hend]
        simp [sourcePosition, Route.position, i]
    · simp only [List.consecutivePairs_singleton, List.not_mem_nil] at hempty

/-- Join the mapped samples in source order after splitting each indexed segment at its cuts. -/
noncomputable def mapAtCuts (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (F : ℂ → ℂ) : Route :=
  match sourceSamples p S c with
  | x :: y :: rest =>
      (rest.map fun z => F (p.eval z.1 z.2)).foldl Route.append
        (Route.line (F (p.eval x.1 x.2))
          (F (p.eval y.1 y.2)))
  | _ => p

private theorem mapAtCuts_segments (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (F : ℂ → ℂ) :
    (mapAtCuts p S c F).segments = (sourceSamples p S c).length - 1 := by
  obtain ⟨x,y,rest,hw⟩ := sourceSamples_nontrivial p S c
  simp only [mapAtCuts, hw, Route.segments_foldl_append, Route.segments, Route.line,
    List.length_map, List.length_cons]
  omega

/-- Each old indexed segment contributes one piece plus the number of its strict cuts. -/
theorem segments_mapAtCuts_eq (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (F : ℂ → ℂ) :
    (p.mapAtCuts S c F).segments = ∑ i : Fin p.segments,
      (1 + (segmentInteriorCuts S (c (p.point i.castSucc)) (c (p.point i.succ))).card) := by
  rw [mapAtCuts_segments, sourceSamples_length_eq_sum, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sourceBlock, List.length_map, List.length_dropLast, cuts, segmentCuts_length_eq]
  omega

/-- Each old indexed segment contributes at least one piece and at most one more than the
number of supplied levels. -/
theorem segments_mapAtCuts (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (F : ℂ → ℂ) :
    p.segments ≤ (p.mapAtCuts S c F).segments ∧
    (p.mapAtCuts S c F).segments ≤ (S.card + 1) * p.segments := by
  rw [mapAtCuts_segments]
  have h := sourceSamples_length p S c
  omega

private theorem mapAtCuts_nodeCount (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (F : ℂ → ℂ) :
    (mapAtCuts p S c F).bends + 2 = (sourceSamples p S c).length := by
  have hseg := mapAtCuts_segments p S c F
  have hlen := sourceSamples_length p S c
  dsimp only [Route.segments] at hseg
  omega

-- A scalar auxiliary route, not the geometric image route, records old chain positions.
-- Its strict real order is the existing CoordinateOrder caller that permits arbitrary loops.
private noncomputable def parameterRoute (p : Route) (S : Finset ℝ)
    (c : ℂ →ᵃ[ℝ] ℝ) (F : ℂ → ℂ) : Route where
  bends := (mapAtCuts p S c F).bends
  point := fun i => (sourcePosition ((sourceSamples p S c)[i.val]'(by
    rw [← mapAtCuts_nodeCount p S c F]
    exact i.isLt)) : ℝ)

private theorem parameterRoute_ordered (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (F : ℂ → ℂ) :
    StrictMono fun i => ((parameterRoute p S c F).point i).re := by
  intro i j hij
  have hm := List.pairwise_iff_get.mp (sourceSamples_ordered p S c)
  exact hm _ _ (show (⟨i.val, by rw [← mapAtCuts_nodeCount p S c F]; exact i.isLt⟩ :
    Fin (sourceSamples p S c).length) < ⟨j.val, by
      rw [← mapAtCuts_nodeCount p S c F]; exact j.isLt⟩ from hij)

private theorem parameterRoute_ends (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (F : ℂ → ℂ) :
    (parameterRoute p S c F).start = 0 ∧
      (parameterRoute p S c F).finish = (p.segments : ℝ) := by
  have he := sourceSamples_ends p S c
  constructor
  · simp only [parameterRoute, Route.start, Fin.val_zero, he.1, sourcePosition,
      Nat.cast_zero, zero_add, Complex.ofReal_zero]
  · simp only [parameterRoute, Route.finish, Fin.val_last, mapAtCuts_segments p S c F, he.2,
      sourcePosition, Route.segments, Nat.cast_add, Nat.cast_one]

private theorem mapAtCuts_adjacent (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (F : ℂ → ℂ)
    (i : Fin (mapAtCuts p S c F).segments) :
    let W := sourceSamples p S c
    let x := W[i.val]'(by
      have hi := i.isLt
      have hseg := mapAtCuts_segments p S c F
      change _ < (sourceSamples p S c).length
      omega)
    let y := W[i.val + 1]'(by
      have hi := i.isLt
      have hseg := mapAtCuts_segments p S c F
      change _ < (sourceSamples p S c).length
      omega)
    (∀ t : ℝ, (mapAtCuts p S c F).eval i t =
      AffineMap.lineMap (F (p.eval x.1 x.2))
        (F (p.eval y.1 y.2)) t) ∧
    (∀ t : ℝ, ((parameterRoute p S c F).eval i t).re =
      AffineMap.lineMap (sourcePosition x) (sourcePosition y) t) := by
  obtain ⟨x, y, rest, hw⟩ := sourceSamples_nontrivial p S c
  dsimp only
  refine ⟨fun t => ?_, fun t => ?_⟩
  · let imageSample : Fin p.segments × ℝ → ℂ := fun z => F (p.eval z.1 z.2)
    have hraw : mapAtCuts p S c F = (rest.map imageSample).foldl Route.append
        (Route.line (imageSample x) (imageSample y)) := by simp [mapAtCuts, hw, imageSample]
    have hev (r : Route) (hr : mapAtCuts p S c F = r) :
        (mapAtCuts p S c F).eval i t = r.eval ⟨i.val, hr ▸ i.isLt⟩ t := by
      subst hr
      rfl
    have hword : imageSample x :: imageSample y :: rest.map imageSample =
        (x :: y :: rest).map imageSample := rfl
    rw [hev _ hraw]
    simpa only [hword, ← hw, List.getElem_map, imageSample] using
      Route.eval_foldl_append_line (imageSample x) (imageSample y)
        (rest.map imageSample) ⟨i.val, hraw ▸ i.isLt⟩ t
  · have hi := i.isLt
    have hseg := mapAtCuts_segments p S c F
    change (AffineMap.lineMap ((sourcePosition ((sourceSamples p S c)[i.val])) : ℂ)
        ((sourcePosition ((sourceSamples p S c)[i.val + 1])) : ℂ) t).re = _
    simp only [AffineMap.lineMap_apply_module', Complex.add_re, Complex.smul_re,
      Complex.sub_re, Complex.ofReal_re]


private theorem lineMap_mem_unit {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (ht : t ∈ Set.Icc 0 1) : AffineMap.lineMap a b t ∈ Set.Icc 0 1 :=
  (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).lineMap_mem ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ ht

section Interpolation

variable {S : Finset ℝ} {c : ℂ →ᵃ[ℝ] ℝ} {F : ℂ → ℂ}
  (hF : ∀ a b : ℂ,
    (∀ y ∈ S, y ∉ Set.Ioo (min (c a) (c b)) (max (c a) (c b))) →
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      F (AffineMap.lineMap a b t) = AffineMap.lineMap (F a) (F b) t)

include hF in
private theorem mapAtCuts_parameter (p : Route)
    (i : Fin (mapAtCuts p S c F).segments) :
    ∃ (j : Fin p.segments) (α β : ℝ),
      0 ≤ α ∧ α < β ∧ β ≤ 1 ∧
      (∀ y ∈ S, ¬(min (c (p.eval j α)) (c (p.eval j β)) < y ∧
        y < max (c (p.eval j α)) (c (p.eval j β)))) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        (mapAtCuts p S c F).eval i t =
          F (p.eval j (AffineMap.lineMap α β t))) ∧
      (∀ t : ℝ, ((parameterRoute p S c F).eval i t).re =
        p.position j (AffineMap.lineMap α β t)) := by
  have hidx : i.val + 1 < (sourceSamples p S c).length := by
    have := i.isLt
    have hseg := mapAtCuts_segments p S c F
    omega
  obtain ⟨heval, hpos⟩ := mapAtCuts_adjacent p S c F i
  obtain ⟨j, k, hk, hx, hy, hxp, hyp⟩ := sourceSamples_adjacent p S c
    (List.getElem_mem_consecutivePairs (sourceSamples p S c) i.val hidx)
  let C := cuts S c (p.point j.castSucc) (p.point j.succ)
  have hkC : k + 1 < C.length := hk
  have hα := segmentCuts_mem_Icc (List.getElem_mem (by omega : k < C.length))
  have hβ := segmentCuts_mem_Icc (List.getElem_mem hk)
  have hαβ : C[k] < C[k + 1] := (segmentCuts_sorted S _ _).strictMono_get
    (show (⟨k, by omega⟩ : Fin C.length) < ⟨k + 1, hk⟩ from Nat.lt_succ_self k)
  refine ⟨j, C[k], C[k + 1], hα.1, hαβ, hβ.2, segmentCuts_adjacent_no_level S c hk,
    fun t ht => ?_, fun t => ?_⟩
  · rw [heval, hx, hy]
    exact (segmentCuts_map_lineMap S c F hF _ _ hk ht).symm
  · rw [hpos, hxp, hyp]
    change AffineMap.lineMap ((j.val : ℝ) + C[k]) ((j.val : ℝ) + C[k + 1]) t =
      (j.val : ℝ) + AffineMap.lineMap C[k] C[k + 1] t
    simp only [AffineMap.lineMap_apply_ring']
    ring

private theorem parameterRoute_real (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (F : ℂ → ℂ)
    (i : Fin (mapAtCuts p S c F).segments) (t : ℝ) :
    (parameterRoute p S c F).eval i t =
      (((parameterRoute p S c F).eval i t).re : ℝ) :=
  Complex.ext (by simp)
    (by simp [Route.eval, parameterRoute, AffineMap.lineMap_apply_module'])

private theorem parameterRoute_open (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (F : ℂ → ℂ) :
    (parameterRoute p S c F).start ≠ (parameterRoute p S c F).finish := by
  rw [(parameterRoute_ends p S c F).1, (parameterRoute_ends p S c F).2]
  exact_mod_cast (Nat.zero_lt_succ p.bends).ne

private theorem mapAtCuts_atEnd (p : Route) (S : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (F : ℂ → ℂ)
    (i : Fin (mapAtCuts p S c F).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) (b : Bool) :
    (mapAtCuts p S c F).AtEnd i t b ↔
      ((parameterRoute p S c F).eval i t).re = if b then (p.segments : ℝ) else 0 := by
  let q := parameterRoute p S c F
  have hq := Route.isSimple_of_strictMono_re (parameterRoute_ordered p S c F)
  have hend (b : Bool) : q.endpoint b = (if b then (p.segments : ℝ) else 0 : ℝ) := by
    cases b <;> simp only [q, Route.endpoint, Bool.false_eq_true, ↓reduceIte,
      (parameterRoute_ends p S c F).1, (parameterRoute_ends p S c F).2, Complex.ofReal_zero]
  constructor
  · intro he
    have he' : q.AtEnd i t b := he
    rw [q.at_eq_endpoint i ht b he', hend]
    simp
  · intro he
    have hc : q.eval i t = q.endpoint b := by
      rw [parameterRoute_real p S c F i t, he, hend]
    cases b
    · have hz : q.eval 0 0 = q.endpoint false := by simp [Route.eval, Route.endpoint, Route.start]
      have hp := hq.position_eq_of_eval_eq (parameterRoute_open p S c F) i 0 ht
        (by constructor <;> norm_num) (hc.trans hz.symm)
      simpa only [Route.AtEnd, Bool.false_eq_true, ↓reduceIte, Route.position,
        Fin.val_zero, Nat.cast_zero, add_zero] using hp
    · have hz : q.eval (Fin.last q.bends) 1 = q.endpoint true := by
        simp [Route.eval, Route.endpoint, Route.finish, Route.segments]
      have hp := hq.position_eq_of_eval_eq (parameterRoute_open p S c F) i (Fin.last q.bends) ht
        (by constructor <;> norm_num) (hc.trans hz.symm)
      simpa only [q, parameterRoute, Route.AtEnd, ↓reduceIte, Route.position, Fin.val_last,
        Route.segments,
        Nat.cast_add, Nat.cast_one] using hp

include hF in
/-- Each indexed image piece comes from one strictly positive source parameter interval.
No level lies strictly between that interval's endpoint coordinates. Evaluation and both
tagged ends agree with the source evaluation on closed parameters, including for loops. -/
theorem eval_mapAtCuts (p : Route) (i : Fin (p.mapAtCuts S c F).segments) :
    ∃ (j : Fin p.segments) (α β : ℝ), 0 ≤ α ∧ α < β ∧ β ≤ 1 ∧
      (∀ y ∈ S, y ∉ Set.Ioo (min (c (p.eval j α)) (c (p.eval j β)))
        (max (c (p.eval j α)) (c (p.eval j β)))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (p.mapAtCuts S c F).eval i t = F (p.eval j (AffineMap.lineMap α β t)) ∧
        ∀ b : Bool, (p.mapAtCuts S c F).AtEnd i t b ↔
          p.AtEnd j (AffineMap.lineMap α β t) b := by
  obtain ⟨j, α, β, ha, hab, hb, hn, he, hp⟩ := mapAtCuts_parameter hF p i
  refine ⟨j, α, β, ha, hab, hb, hn, fun t ht => ⟨he t ht, fun b => ?_⟩⟩
  rw [mapAtCuts_atEnd p S c F i ht b, hp]; rfl

include hF in
/-- Injectivity and cutwise interpolation preserve the simplicity of the original route. -/
protected theorem IsSimple.mapAtCuts {p : Route} (hp : p.IsSimple)
    (hInjective : Function.Injective F) : (mapAtCuts p S c F).IsSimple := by
  intro i j s t hs ht heq
  obtain ⟨k, α, β, hα, hαβ, hβ, _hlevels, hi, hip⟩ := mapAtCuts_parameter hF p i
  obtain ⟨l, γ, δ, hγ, hγδ, hδ, _hlevels, hj, hjp⟩ := mapAtCuts_parameter hF p j
  have hs' := lineMap_mem_unit hα hαβ.le hβ hs
  have ht' := lineMap_mem_unit hγ hγδ.le hδ ht
  have he := hInjective ((hi s hs).symm.trans (heq.trans (hj t ht)))
  rcases hp k l _ _ hs' ht' he with he | ⟨he₀, he₁⟩ | ⟨he₁, he₀⟩
  · left
    have hc : (parameterRoute p S c F).eval i s = (parameterRoute p S c F).eval j t := by
      rw [parameterRoute_real p S c F i s, parameterRoute_real p S c F j t, hip, hjp, he]
    exact (Route.isSimple_of_strictMono_re (parameterRoute_ordered p S c F)).position_eq_of_eval_eq
      (parameterRoute_open p S c F) i j hs ht hc
  · exact .inr <| .inl ⟨(mapAtCuts_atEnd p S c F i hs false).mpr ((hip s).trans he₀),
      (mapAtCuts_atEnd p S c F j ht true).mpr ((hjp t).trans he₁)⟩
  · exact .inr <| .inr ⟨(mapAtCuts_atEnd p S c F i hs true).mpr ((hip s).trans he₁),
      (mapAtCuts_atEnd p S c F j ht false).mpr ((hjp t).trans he₀)⟩

include hF in
/-- The two tagged endpoints are the images of their corresponding source endpoints. -/
theorem endpoint_mapAtCuts (p : Route) (b : Bool) :
    (mapAtCuts p S c F).endpoint b = F (p.endpoint b) := by
  let i : Fin (mapAtCuts p S c F).segments := if b then Fin.last (mapAtCuts p S c F).bends else 0
  let t : ℝ := if b then 1 else 0
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by cases b <;> constructor <;> norm_num [t]
  have he : (mapAtCuts p S c F).AtEnd i t b := by
    cases b <;> simp [Route.AtEnd, Route.position, i, t, Route.segments]
  obtain ⟨j, α, β, hα, hαβ, hβ, _hlevels, hj, hjp⟩ := mapAtCuts_parameter hF p i
  have hu := lineMap_mem_unit hα hαβ.le hβ ht
  have hje : p.AtEnd j (AffineMap.lineMap α β t) b :=
    (hjp t).symm.trans ((mapAtCuts_atEnd p S c F i ht b).mp he)
  rw [← (mapAtCuts p S c F).at_eq_endpoint i ht b he, hj t ht,
    p.at_eq_endpoint j hu b hje]

private theorem sourceSamples_piece (p : Route) (S : Finset ℝ)
    (c : ℂ →ᵃ[ℝ] ℝ) (j : Fin p.segments) {k : ℕ}
    (hk : k + 1 < (cuts S c (p.point j.castSucc) (p.point j.succ)).length) :
    ∃ (q : ℕ) (hq : q + 1 < (sourceSamples p S c).length),
      (sourceSamples p S c)[q] = (j, (cuts S c (p.point j.castSucc) (p.point j.succ))[k]) ∧
      p.eval ((sourceSamples p S c)[q + 1]).1 ((sourceSamples p S c)[q + 1]).2 =
        p.eval j (cuts S c (p.point j.castSucc) (p.point j.succ))[k + 1] := by
  let L := List.finRange p.segments
  let f := sourceBlock p S c
  let C := cuts S c (p.point j.castSucc) (p.point j.succ)
  have hdef : sourceSamples p S c = L.flatMap f ++ [(Fin.last p.bends,1)] := rfl
  have hLlen : L.length = p.segments := List.length_finRange
  let prefLen := ((L.take j.val).flatMap f).length
  have hj : j.val < L.length := by simpa only [L, List.length_finRange] using j.isLt
  have hget : L[j.val] = j := by simp [L]
  have hkf : k < (f L[j.val]).length := by
    simp only [hget, f, sourceBlock, List.length_map, List.length_dropLast]
    omega
  have hq0 := List.flatMap_prefix_add_lt L f hj hkf
  have hq : prefLen + k + 1 < (sourceSamples p S c).length := by
    rw [hdef, List.length_append, List.length_singleton]
    change prefLen+k < (L.flatMap f).length at hq0
    omega
  refine ⟨prefLen + k, hq, ?_, ?_⟩
  · refine (List.getElem_append_left (bs := [(Fin.last p.bends, 1)]) hq0).trans ?_
    simp only [List.getElem_flatMap_prefix_add L f hj hkf, hget, f, sourceBlock, List.getElem_map,
      List.getElem_dropLast]
  · by_cases hnext : k + 1 < (f j).length
    · have hq1 := List.flatMap_prefix_add_lt L f hj (hget.symm ▸ hnext)
      have hget1 : (sourceSamples p S c)[prefLen + k + 1] = (f j)[k + 1] :=
        (List.getElem_append_left (bs := [(Fin.last p.bends, 1)]) hq1).trans
          (by simpa only [prefLen, Nat.add_assoc, hget] using
            List.getElem_flatMap_prefix_add L f hj (hget.symm ▸ hnext))
      simp only [hget1, f, sourceBlock, List.getElem_map, List.getElem_dropLast]
    · have hkLast : k + 1 = (f j).length := by
        simp only [f, sourceBlock, List.length_map, List.length_dropLast] at hnext ⊢; omega
      have hfinish : C[k + 1] = 1 := by
        have hlen := cuts_length_bounds S c (p.point j.castSucc) (p.point j.succ)
        have hkLast' : k + 1 = C.length - 1 := by simpa only
          [f, sourceBlock, List.length_map, List.length_dropLast] using hkLast
        simp only [hkLast']
        exact (segmentCuts_first_last S (c (p.point j.castSucc)) (c (p.point j.succ))).2
      have hpref : ((L.take (j.val + 1)).flatMap f).length = prefLen + (f j).length := by
        rw [List.take_succ_eq_append_getElem hj, List.flatMap_append,
          List.flatMap_singleton, List.length_append, hget]
      by_cases hjnext : j.val + 1 < p.segments
      · let j' : Fin p.segments := ⟨j.val + 1, hjnext⟩
        have hj' : j'.val < L.length := by dsimp [j']; omega
        have hhead : L[j'.val] = j' := by simp [L, j']
        have hz : 0 < (f L[j'.val]).length := hhead.symm ▸ (sourceBlock_length p S c j').1
        have hflat := List.flatMap_prefix_add_lt L f hj' hz
        have hq1 : prefLen + k + 1 = ((L.take j'.val).flatMap f).length + 0 := by
          simp only [j', hpref, add_zero]; omega
        have hqlem : (sourceSamples p S c)[prefLen + k + 1] =
            (f j')[0]'(by rw [← hhead]; exact hz) := by
          have helem' : (sourceSamples p S c)[((L.take j'.val).flatMap f).length + 0] =
              (f L[j'.val])[0] :=
            (List.getElem_append_left (bs := [(Fin.last p.bends, 1)]) hflat).trans
              (List.getElem_flatMap_prefix_add L f hj' hz)
          simpa only [← hq1, hhead] using helem'
        have hzero : (f j')[0]'(by rw [← hhead]; exact hz) = (j', 0) := by
          simpa only [List.head_eq_getElem] using sourceBlock_head p S c j'
        rw [hqlem, hzero, hfinish]
        simp only [Route.eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
        congr 1
      · have hjlast : j = Fin.last p.bends := Fin.ext <| by
          have := j.isLt
          simp only [Route.segments, Fin.val_last] at this hjnext ⊢; omega
        have hjlen : j.val + 1 = L.length := by rw [hjlast, Fin.val_last, hLlen]
        rw [hjlen, List.take_length] at hpref
        have hqlem : (sourceSamples p S c)[prefLen + k + 1] = (Fin.last p.bends, 1) :=
          List.getElem_concat_length (l := L.flatMap f) (by omega) _
        rw [hqlem]
        change p.eval (Fin.last p.bends) 1 = p.eval j C[k+1]
        rw [hfinish, hjlast]

include hF in
private theorem mapAtCuts_contains (p : Route)
    (j : Fin p.segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    F (p.eval j t) ∈ (mapAtCuts p S c F).support := by
  obtain ⟨k, hk, hlo, hhi⟩ := segmentCuts_cover (levels := S)
    (a := c (p.point j.castSucc)) (b := c (p.point j.succ)) ht
  let C := cuts S c (p.point j.castSucc) (p.point j.succ)
  have hkC : k + 1 < C.length := hk
  have hstep : C[k] < C[k + 1] := (segmentCuts_sorted S _ _).strictMono_get
    (show (⟨k, by omega⟩ : Fin C.length) < ⟨k + 1, hk⟩ from Nat.lt_succ_self k)
  let u := (t - C[k]) / (C[k + 1] - C[k])
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg (sub_nonneg.mpr hlo) (sub_pos.mpr hstep).le,
    (div_le_iff₀ (sub_pos.mpr hstep)).mpr (by linarith)⟩
  have huval : AffineMap.lineMap C[k] C[k + 1] u = t := by
    rw [AffineMap.lineMap_apply_ring']
    dsimp [u]
    field_simp [sub_ne_zero.mpr (ne_of_gt hstep)]; ring
  obtain ⟨q, hq, hfirst, hlast⟩ := sourceSamples_piece p S c j hk
  have hq' : q < (mapAtCuts p S c F).segments := by rw [mapAtCuts_segments]; omega
  have heval := (mapAtCuts_adjacent p S c F ⟨q, hq'⟩).1 u
  rw [hfirst, hlast] at heval
  have he : (mapAtCuts p S c F).eval ⟨q, hq'⟩ u = F (p.eval j t) := by
    rw [heval]
    change AffineMap.lineMap (F (p.eval j C[k]))
      (F (p.eval j C[k+1])) u = _
    exact (segmentCuts_map_lineMap S c F hF _ _ hk hu).symm.trans
      (congrArg (fun t => F (p.eval j t)) huval)
  exact he ▸ (mapAtCuts p S c F).at_mem_support ⟨q, hq'⟩ hu

include hF in
/-- The complete support is the image of the original support, including all cut points. -/
theorem support_mapAtCuts (p : Route) :
    (mapAtCuts p S c F).support = F '' p.support := by
  refine Set.ext fun z => ⟨fun hz => ?_, ?_⟩
  · obtain ⟨i, t, ht, heq⟩ := ((mapAtCuts p S c F).mem_support_iff z).mp hz
    obtain ⟨j, α, β, hα, hαβ, hβ, _, hj, _⟩ := mapAtCuts_parameter hF p i
    exact ⟨_, p.at_mem_support j (lineMap_mem_unit hα hαβ.le hβ ht), (hj t ht).symm.trans heq⟩
  · rintro ⟨_, hw, rfl⟩
    obtain ⟨j, t, ht, rfl⟩ := (p.mem_support_iff _).mp hw
    exact mapAtCuts_contains hF p j ht

end Interpolation
end Cslib.Polygonal.Route
