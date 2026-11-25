/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Neighborhood
public import CslibFrontier.Foundations.Geometry.Polygonal.Route
public import CslibFrontier.Foundations.Geometry.Polygonal.RouteIntersectionParity
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import CslibFrontier.Foundations.Geometry.Polygonal.CircleChord
import CslibFrontier.Foundations.Geometry.Polygonal.Concatenate
import CslibFrontier.Foundations.Geometry.Polygonal.Germs
import CslibFrontier.Foundations.Geometry.Polygonal.Reverse
import CslibFrontier.Foundations.Geometry.Polygonal.RouteIntersectionCutEnds
import CslibFrontier.Foundations.Geometry.Polygonal.Trisection
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.AffineSpace.Midpoint

/-!
# Splicing out an isolated crossing of a polygonal route

Cut the two crossing segments at the boundary of their disk. Reverse the intervening
portion and join the two entry points and the two exit points, so the result is one
route. Its exterior support, outer endpoints and outgoing directions are preserved,
and its support in the disk is exactly two disjoint chords without interior crossings.
The splice preserves intersection parity against any route avoiding the disk.
Every strict-interior crossing of the spliced route was already a crossing outside the disk.
-/

public section

namespace Cslib.Polygonal.Route

private def intervalSupport (p : Route) (i j : Fin p.segments) (s t : ℝ) : Set ℂ :=
  {w | ∃ k : Fin p.segments, k ∈ Set.Icc i j ∧ ∃ u : ℝ,
    u ∈ Set.Icc (if k = i then s else 0) (if k = j then t else 1) ∧ p.eval k u = w}

private theorem intersectionParity_eq_sum_lines (p r : Route) :
    p.intersectionParity r = ∑ k : Fin p.segments,
      (line (p.eval k 0) (p.eval k 1)).intersectionParity r := by
  classical
  simp only [eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
  unfold intersectionParity
  apply Finset.sum_congr rfl
  intro k _
  change _ = ∑ l : Fin 1, _
  rw [Fin.sum_univ_one]
  rfl

open Classical in
private noncomputable def intervalParity (p : Route) (i j : Fin p.segments) (s t : ℝ)
    (r : Route) : Bool :=
  ∑ k : Fin p.segments, if k ∈ Set.Icc i j then
    (line (p.eval k (if k = i then s else 0))
      (p.eval k (if k = j then t else 1))).intersectionParity r else 0

private theorem exists_pos_smul_germ_of_end_eval (q p : Route) (b : Bool) {lo hi : ℝ}
    (hlt : lo < hi) (hb : if b then hi = 1 else lo = 0)
    (he : ∀ u, q.eval (q.endSegment b) u =
      p.eval (p.endSegment b) (AffineMap.lineMap lo hi u)) :
    ∃ c : ℝ, 0 < c ∧ q.germ b = c • p.germ b := by
  refine ⟨hi - lo, sub_pos.mpr hlt, ?_⟩
  have htime (u : ℝ) : AffineMap.lineMap lo hi (endTime b u) = endTime b ((hi - lo) * u) := by
    cases b <;> simp only [endTime, Bool.false_eq_true, ↓reduceIte,
      AffineMap.lineMap_apply_module', smul_eq_mul] at hb ⊢ <;> rw [hb] <;> ring
  have h₀ := he (endTime b 0)
  have h₁ := he (endTime b 1)
  simp only [htime, eval_near_end, mul_zero, zero_smul, add_zero] at h₀
  simp only [htime, eval_near_end, mul_one, one_smul, h₀] at h₁
  exact add_left_cancel h₁

private theorem exists_route_support_between (p : Route) (i j : Fin p.segments) (hij : i ≤ j)
    {s t : ℝ} (hs : s ∈ Set.Ico 0 1) (ht : t ∈ Set.Ioc 0 1) (hst : i = j → s < t) :
    ∃ q : Route, q.start = p.eval i s ∧ q.finish = p.eval j t ∧
      q.support = intervalSupport p i j s t ∧
      (∀ r : Route, q.intersectionParity r = intervalParity p i j s t r) ∧
      (i = 0 → s = 0 → ∃ c : ℝ, 0 < c ∧ q.germ false = c • p.germ false) ∧
      (j = Fin.last p.bends → t = 1 → ∃ c : ℝ, 0 < c ∧ q.germ true = c • p.germ true) ∧
      ∃ e : Fin q.segments ≃o Set.Icc i j, ∀ k {u : ℝ}, u ∈ Set.Ioo 0 1 →
        ∃ v ∈ Set.Ioo (if (e k).val = i then s else 0) (if (e k).val = j then t else 1),
          v ∈ Set.Ioo 0 1 ∧ q.eval k u = p.eval (e k).val v := by
  obtain ⟨q, e, hstart, hfinish, hspec⟩ := p.exists_subroute_between i j hij hs ht hst
  have hparity (r : Route) : q.intersectionParity r = intervalParity p i j s t r := by
    classical
    let contribution (k : Fin p.segments) :=
      (line (p.eval k (if k = i then s else 0))
        (p.eval k (if k = j then t else 1))).intersectionParity r
    rw [intersectionParity_eq_sum_lines q r]
    change _ = ∑ k : Fin p.segments, if k ∈ Set.Icc i j then contribution k else 0
    rw [← Finset.sum_filter]
    rw [Finset.sum_subtype (p := (· ∈ Set.Icc i j))
      (Finset.univ.filter (· ∈ Set.Icc i j)) (fun k => by simp) contribution]
    refine Fintype.sum_equiv e.toEquiv _ _ fun k => ?_
    change (line (q.eval k 0) (q.eval k 1)).intersectionParity r = contribution (e k).val
    obtain ⟨_, _, _, he⟩ := hspec k
    simp only [contribution, he, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
  have hgerm_start (hi : i = 0) (hs₀ : s = 0) :
      ∃ c : ℝ, 0 < c ∧ q.germ false = c • p.germ false := by
    let first : Set.Icc i j := ⟨i, le_rfl, hij⟩
    have hfirst := e.monotone (Fin.zero_le (e.symm first))
    rw [e.apply_symm_apply] at hfirst
    have hi' : (e 0).val = i := le_antisymm hfirst (e 0).property.1
    obtain ⟨_, hlt, _, he⟩ := hspec 0
    simp only [hi', ↓reduceIte] at hlt he
    apply exists_pos_smul_germ_of_end_eval q p false hlt hs₀
    simpa only [endSegment, Bool.false_eq_true, ↓reduceIte, hi] using he
  have hgerm_finish (hj : j = Fin.last p.bends) (ht₁ : t = 1) :
      ∃ c : ℝ, 0 < c ∧ q.germ true = c • p.germ true := by
    let last : Set.Icc i j := ⟨j, hij, le_rfl⟩
    have hlast := e.monotone (Fin.le_last (e.symm last))
    rw [e.apply_symm_apply] at hlast
    have hj' : (e (Fin.last q.bends)).val = j :=
      le_antisymm (e (Fin.last q.bends)).property.2 hlast
    obtain ⟨_, hlt, _, he⟩ := hspec (Fin.last q.bends)
    simp only [hj', ↓reduceIte] at hlt he
    apply exists_pos_smul_germ_of_end_eval q p true hlt ht₁
    simpa only [endSegment, ↓reduceIte, hj] using he
  refine ⟨q, hstart, hfinish, ?_, hparity, hgerm_start, hgerm_finish, e, ?_⟩
  · ext w
    rw [q.mem_support_iff]
    constructor
    · rintro ⟨k, u, hu, hwu⟩
      obtain ⟨_, hlt, _, he⟩ := hspec k
      let a := if (e k).val = i then s else 0
      let b := if (e k).val = j then t else 1
      have huv : AffineMap.lineMap a b u ∈ Set.Icc a b := by
        rw [← segment_eq_Icc hlt.le]
        exact lineMap_mem_segment ℝ a b hu
      exact ⟨(e k).val, (e k).property, _, huv, (he u).symm.trans hwu⟩
    · rintro ⟨k, hk, u, hu, hwu⟩
      let l := e.symm ⟨k, hk⟩
      have hel : (e l).val = k := congrArg Subtype.val (e.apply_symm_apply ⟨k, hk⟩)
      obtain ⟨_, hlt, _, he⟩ := hspec l
      rw [← hel] at hu hwu
      have hu' : u ∈ segment ℝ (if (e l).val = i then s else 0)
          (if (e l).val = j then t else 1) := by
        rw [segment_eq_Icc hlt.le]
        exact hu
      rw [segment_eq_image_lineMap] at hu'
      obtain ⟨v, hv, rfl⟩ := hu'
      exact ⟨l, v, hv, (he v).trans hwu⟩
  · intro k u hu
    obtain ⟨hl, hlt, hh, he⟩ := hspec k
    let lo := if (e k).val = i then s else 0
    let hi := if (e k).val = j then t else 1
    have hv : AffineMap.lineMap lo hi u ∈ Set.Ioo lo hi := by
      rw [← openSegment_eq_Ioo hlt]
      exact lineMap_mem_openSegment ℝ lo hi hu
    exact ⟨_, hv, ⟨hl.trans_lt hv.1, hv.2.trans_le hh⟩, he u⟩

private theorem intervalSupport_subset (p : Route) (i j : Fin p.segments) {s t : ℝ}
    (hs : 0 ≤ s) (ht : t ≤ 1) : intervalSupport p i j s t ⊆ p.support := by
  rintro _ ⟨k, _, u, hu, rfl⟩
  have hlo : 0 ≤ (if k = i then s else 0) := by split_ifs <;> first | assumption | exact le_rfl
  have hhi : (if k = j then t else 1) ≤ 1 := by split_ifs <;> first | assumption | exact le_rfl
  exact p.at_mem_support k ⟨hlo.trans hu.1, hu.2.trans hhi⟩

private theorem intersectionParity_eq_zero_of_disjoint {p r : Route}
    (h : Disjoint p.support r.support) : p.intersectionParity r = 0 := by
  classical
  unfold intersectionParity
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  change decide _ = false
  apply decide_eq_false
  rintro ⟨z, hi, hj⟩
  exact Set.disjoint_left.mp h
    (Set.mem_iUnion.mpr ⟨i, openSegment_subset_segment ℝ _ _ hi⟩)
    (Set.mem_iUnion.mpr ⟨j, openSegment_subset_segment ℝ _ _ hj⟩)

private theorem intervalParity_splice (p : Route) {i j : Fin p.segments} (hij : i < j)
    (r : Route) {li ui lj uj : ℝ} (hli : 0 < li) (hi : li < ui) (hui : ui < 1)
    (hlj : 0 < lj) (hj : lj < uj) (huj : uj < 1)
    (hcuti : Disjoint (segment ℝ (p.eval i li) (p.eval i ui)) r.support)
    (hcutj : Disjoint (segment ℝ (p.eval j lj) (p.eval j uj)) r.support) :
    intervalParity p 0 i 0 li r + intervalParity p i j ui lj r +
      intervalParity p j (Fin.last p.bends) uj 1 r = p.intersectionParity r := by
  classical
  rw [intersectionParity_eq_sum_lines p r]
  unfold intervalParity
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Set.mem_Icc, Fin.zero_le, Fin.le_last, true_and, and_true, ite_self]
  rcases lt_trichotomy k i with hki | rfl | hik
  · have hkj := hki.trans hij
    simp [hki.le, hki.ne, hki.not_ge, hkj.not_ge]
  · simpa only [le_rfl, hij.le, hij.not_ge, hij.ne, and_self, true_and, ↓reduceIte,
      and_false, add_zero, eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
      using (intersectionParity_line_split_of_disjoint hli hi hui hcuti).symm
  · rcases lt_trichotomy k j with hkj | rfl | hjk
    · simp [hik.le, hik.ne', hik.not_ge, hkj.le, hkj.ne, hkj.not_ge]
    · simpa only [le_rfl, hij.le, hij.not_ge, hij.ne', and_self, and_true, ↓reduceIte,
        zero_add, eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
        using (intersectionParity_line_split_of_disjoint hlj hj huj hcutj).symm
    · have hik' := hij.trans hjk
      simp [hjk.le, hjk.ne', hjk.not_ge, hik'.not_ge]

/-- Replace an isolated double crossing by two disjoint chords joined to the original
route portions. The resulting route has the same outer endpoints and exterior support.
Inside the disk its support is precisely the two chords, and neither contains the center.
Its indexed intersection parity against every route disjoint from the disk is preserved.
Both outgoing germs are positive multiples of their originals. Every pair of distinct segments
meeting in their open interiors gives an original crossing point outside the closed disk. -/
theorem exists_splice_of_isolated_crossing (p : Route) (i j : Fin p.segments) (hij : i < j)
    {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hzi : z ∈ openSegment ℝ (p.point i.castSucc) (p.point i.succ))
    (hzj : z ∈ openSegment ℝ (p.point j.castSucc) (p.point j.succ))
    (hpair : (segment ℝ (p.point i.castSucc) (p.point i.succ) ∩
      segment ℝ (p.point j.castSucc) (p.point j.succ)).Subsingleton)
    (hends : ∀ k, p.point k ∉ Metric.closedBall z ρ)
    (honly : ∀ k : Fin p.segments, k ≠ i → k ≠ j →
      Disjoint (segment ℝ (p.point k.castSucc) (p.point k.succ)) (Metric.closedBall z ρ)) :
    ∃ q : Route, q.start = p.start ∧ q.finish = p.finish ∧ z ∉ q.support ∧
      q.support \ Metric.closedBall z ρ = p.support \ Metric.closedBall z ρ ∧
      (∀ r : Route, Disjoint (Metric.closedBall z ρ) r.support →
        q.intersectionParity r = p.intersectionParity r) ∧
      (∀ b : Bool, ∃ c : ℝ, 0 < c ∧ q.germ b = c • p.germ b) ∧
      openSegmentCrossings (fun k : Fin q.segments => q.point k.castSucc)
        (fun k => q.point k.succ) ⊆
        openSegmentCrossings (fun k : Fin p.segments => p.point k.castSucc)
          (fun k => p.point k.succ) \ Metric.closedBall z ρ ∧
      ∃ li ui lj uj : ℝ, 0 < li ∧ li < ui ∧ ui < 1 ∧ 0 < lj ∧ lj < uj ∧ uj < 1 ∧
        p.eval i li ∈ Metric.sphere z ρ ∧ p.eval i ui ∈ Metric.sphere z ρ ∧
        p.eval j lj ∈ Metric.sphere z ρ ∧ p.eval j uj ∈ Metric.sphere z ρ ∧
        q.support ∩ Metric.closedBall z ρ =
          segment ℝ (p.eval i li) (p.eval j lj) ∪ segment ℝ (p.eval i ui) (p.eval j uj) ∧
        Disjoint (segment ℝ (p.eval i li) (p.eval j lj))
          (segment ℝ (p.eval i ui) (p.eval j uj)) := by
  classical
  obtain ⟨li, ui, hli, hi₀, hui, hiBall, hiSphere, hiMid⟩ :=
    exists_closedBall_lineMap_cuts hρ hzi (hends i.castSucc) (hends i.succ)
  obtain ⟨lj, uj, hlj, hj₀, huj, hjBall, hjSphere, hjMid⟩ :=
    exists_closedBall_lineMap_cuts hρ hzj (hends j.castSucc) (hends j.succ)
  let B := Metric.closedBall z ρ
  let a := p.eval i li
  let b := p.eval i ui
  let c := p.eval j lj
  let d := p.eval j uj
  have ha : a ∈ Metric.sphere z ρ := (hiSphere li).mpr (Or.inl rfl)
  have hb : b ∈ Metric.sphere z ρ := (hiSphere ui).mpr (Or.inr rfl)
  have hc : c ∈ Metric.sphere z ρ := (hjSphere lj).mpr (Or.inl rfl)
  have hd : d ∈ Metric.sphere z ρ := (hjSphere uj).mpr (Or.inr rfl)
  have hcb : c ≠ b := by
    intro h
    have hb' : b ∈ segment ℝ (p.point i.castSucc) (p.point i.succ) :=
      lineMap_mem_segment ℝ _ _ ⟨(hli.trans hi₀).le, hui.le⟩
    have hc' : c ∈ segment ℝ (p.point j.castSucc) (p.point j.succ) :=
      lineMap_mem_segment ℝ _ _ ⟨hlj.le, (hj₀.trans huj).le⟩
    have he : c = z := hpair ⟨h.symm ▸ hb', hc'⟩
      ⟨openSegment_subset_segment ℝ _ _ hzi, openSegment_subset_segment ℝ _ _ hzj⟩
    exact hρ.ne' ((Metric.mem_sphere.mp hc).symm.trans (he.symm ▸ dist_self z))
  have hdisjoint : Disjoint (segment ℝ a c) (segment ℝ b d) :=
    disjoint_segments_of_antipodal_pairs ha hc hcb hiMid hjMid
  let jlast : Fin p.segments := Fin.last p.bends
  obtain ⟨A, hA₀, hA₁, hA, hAp, hAg, _, eA, hAt⟩ :=
    exists_route_support_between p 0 i (Fin.zero_le i)
    (s := 0) (t := li) ⟨le_rfl, zero_lt_one⟩ ⟨hli, (hi₀.trans hui).le⟩ (fun _ => hli)
  obtain ⟨M, hM₀, hM₁, hM, hMp, _, _, eM, hMt⟩ := exists_route_support_between p i j hij.le
    (s := ui) (t := lj) ⟨(hli.trans hi₀).le, hui⟩ ⟨hlj, (hj₀.trans huj).le⟩
    (fun h => (hij.ne h).elim)
  obtain ⟨S, hS₀, hS₁, hS, hSp, _, hSg, eS, hSt⟩ :=
    exists_route_support_between p j jlast (Fin.le_last j)
    (s := uj) (t := 1) ⟨(hlj.trans hj₀).le, huj⟩ ⟨zero_lt_one, le_rfl⟩ (fun _ => huj)
  let L := line a c
  let R := line b d
  have hjoinL : A.finish = L.start := hA₁
  have hjoinM : (A.concat L).finish = M.reverse.start := by
    change (A.concat L).endpoint true = M.reverse.endpoint false
    rw [endpoint_concat A L hjoinL, endpoint_reverse]
    exact hM₁.symm
  have hjoinR : ((A.concat L).concat M.reverse).finish = R.start := by
    change ((A.concat L).concat M.reverse).endpoint true = R.start
    rw [endpoint_concat (A.concat L) M.reverse hjoinM, endpoint_reverse]
    exact hM₀
  have hjoinS : (((A.concat L).concat M.reverse).concat R).finish = S.start := by
    change (((A.concat L).concat M.reverse).concat R).endpoint true = S.start
    rw [endpoint_concat _ R hjoinR]
    exact hS₀.symm
  let q := (((A.concat L).concat M.reverse).concat R).concat S
  have hstart : q.start = p.start := by
    change ((((A.concat L).concat M.reverse).concat R).concat S).endpoint false = _
    simp only [endpoint_concat _ S hjoinS, endpoint_concat _ R hjoinR,
      endpoint_concat _ M.reverse hjoinM, endpoint_concat A L hjoinL, Bool.false_eq_true,
      ↓reduceIte]
    simpa only [endpoint, Bool.false_eq_true, ↓reduceIte, eval, AffineMap.lineMap_apply_zero,
      Fin.castSucc_zero, start] using hA₀
  have hfinish : q.finish = p.finish := by
    change ((((A.concat L).concat M.reverse).concat R).concat S).endpoint true = _
    rw [endpoint_concat _ S hjoinS]
    simpa only [endpoint, ↓reduceIte, eval, jlast, AffineMap.lineMap_apply_one, Fin.succ_last,
      finish] using hS₁
  let E := A.support ∪ M.support ∪ S.support
  let N := segment ℝ a c ∪ segment ℝ b d
  have hcenter : z ∉ N := by
    let f := AffineEquiv.pointReflection ℝ z
    have hfb : f a = b := midpoint_eq_iff.mp hiMid
    have hfd : f c = d := midpoint_eq_iff.mp hjMid
    have hfz : f z = z := AffineEquiv.pointReflection_self ℝ z
    have hreflect : f.toAffineMap '' segment ℝ a c = segment ℝ b d := by
      rw [image_segment, AffineEquiv.coe_toAffineMap, hfb, hfd]
    rintro (h | h)
    · exact Set.disjoint_left.mp hdisjoint h (hreflect ▸ ⟨z, h, hfz⟩)
    · have himg := h
      rw [← hreflect] at himg
      obtain ⟨w, hw, he⟩ := himg
      have hwz : w = z := f.injective (he.trans hfz.symm)
      exact Set.disjoint_left.mp hdisjoint (hwz ▸ hw) h
  have hq : q.support = E ∪ N := by
    dsimp only [q]
    rw [support_concat _ _ hjoinS, support_concat _ _ hjoinR, support_concat _ _ hjoinM,
      support_concat _ _ hjoinL, support_reverse]
    simp only [L, R, E, N, support_line]
    ac_rfl
  have hNew : N ⊆ B := Set.union_subset
    ((convex_closedBall z ρ).segment_subset (Metric.sphere_subset_closedBall ha)
      (Metric.sphere_subset_closedBall hc))
    ((convex_closedBall z ρ).segment_subset (Metric.sphere_subset_closedBall hb)
      (Metric.sphere_subset_closedBall hd))
  have hE : E ⊆ p.support := by
    dsimp only [E]
    rw [hA, hM, hS]
    exact Set.union_subset (Set.union_subset (intervalSupport_subset p 0 i le_rfl
      (hi₀.trans hui).le) (intervalSupport_subset p i j (hli.trans hi₀).le
        (hj₀.trans huj).le)) (intervalSupport_subset p j jlast (hlj.trans hj₀).le le_rfl)
  have cover : p.support \ B ⊆ E := by
    rintro w ⟨hw, hout⟩
    obtain ⟨k, u, hu, rfl⟩ := (p.mem_support_iff w).mp hw
    have intoA (hk : k ≤ i) (ht : k = i → u ≤ li) : p.eval k u ∈ E := by
      refine Or.inl (Or.inl ?_)
      rw [hA]
      refine ⟨k, ⟨Fin.zero_le k, hk⟩, u, ?_, rfl⟩
      simp only [ite_self]
      exact ⟨hu.1, by split_ifs with h; exacts [ht h, hu.2]⟩
    have intoM (hki : i ≤ k) (hkj : k ≤ j) (hlo : k = i → ui ≤ u)
        (hhi : k = j → u ≤ lj) : p.eval k u ∈ E := by
      refine Or.inl (Or.inr ?_)
      rw [hM]
      exact ⟨k, ⟨hki, hkj⟩, u, ⟨by split_ifs with h; exacts [hlo h, hu.1],
        by split_ifs with h; exacts [hhi h, hu.2]⟩, rfl⟩
    have intoS (hk : j ≤ k) (ht : k = j → uj ≤ u) : p.eval k u ∈ E := by
      apply Or.inr
      rw [hS]
      refine ⟨k, ⟨hk, Fin.le_last k⟩, u, ?_, rfl⟩
      simp only [ite_self]
      exact ⟨by split_ifs with h; exacts [ht h, hu.1], hu.2⟩
    rcases lt_trichotomy k i with hki | rfl | hik
    · exact intoA hki.le (fun h => (hki.ne h).elim)
    · by_cases h : u ≤ li
      · exact intoA le_rfl (fun _ => h)
      · have hu' : ui ≤ u := le_of_not_ge (fun h' =>
          hout ((hiBall u).mpr ⟨le_of_lt (lt_of_not_ge h), h'⟩))
        exact intoM le_rfl hij.le (fun _ => hu') (fun h => (hij.ne h).elim)
    · rcases lt_trichotomy k j with hkj | rfl | hjk
      · exact intoM hik.le hkj.le (fun h => (hik.ne' h).elim) (fun h => (hkj.ne h).elim)
      · by_cases h : u ≤ lj
        · exact intoM hij.le le_rfl (fun h => (hij.ne' h).elim) (fun _ => h)
        · have hu' : uj ≤ u := le_of_not_ge (fun h' =>
            hout ((hjBall u).mpr ⟨le_of_lt (lt_of_not_ge h), h'⟩))
          exact intoS le_rfl (fun _ => hu')
      · exact intoS hjk.le (fun h => (hjk.ne' h).elim)
  have hother (k : Fin p.segments) (u : ℝ) (hu : u ∈ Set.Icc 0 1)
      (hki : k ≠ i) (hkj : k ≠ j) (hw : p.eval k u ∈ B) : False :=
    Set.disjoint_left.mp (honly k hki hkj) (lineMap_mem_segment ℝ _ _ hu) hw
  have hretained (k : Fin p.segments) (u : ℝ) (hu : u ∈ Set.Icc 0 1)
      (hki : k = i → u < li ∨ ui < u) (hkj : k = j → u < lj ∨ uj < u) :
      p.eval k u ∉ B := by
    intro hw
    by_cases hi : k = i
    · have hu' := (hiBall u).mp (hi ▸ hw)
      exact (hki hi).elim (fun h => h.not_ge hu'.1) (fun h => h.not_ge hu'.2)
    by_cases hj : k = j
    · have hu' := (hjBall u).mp (hj ▸ hw)
      exact (hkj hj).elim (fun h => h.not_ge hu'.1) (fun h => h.not_ge hu'.2)
    exact hother k u hu hi hj hw
  let inPrefix (k : Fin p.segments) (v : ℝ) := k ∈ Set.Icc 0 i ∧ (k = i → v < li)
  let inMiddle (k : Fin p.segments) (v : ℝ) := k ∈ Set.Icc i j ∧ (k = j → v < lj)
  -- The cut parameters distinguish the two retained pieces of either cut segment.
  let indexAt (k : Fin p.segments) (v : ℝ) : ℕ :=
    if hp : inPrefix k v then (eA.symm ⟨k, hp.1⟩).val
    else if hm : inMiddle k v then (A.concat L).segments + (eM.symm ⟨k, hm.1⟩).rev.val
    else if hs : k ∈ Set.Icc j jlast then
      (((A.concat L).concat M.reverse).concat R).segments + (eS.symm ⟨k, hs⟩).val
    else 0
  have hAtrace (k : Fin A.segments) {u : ℝ} (hu : u ∈ Set.Ioo 0 1) :
      ∃ v ∈ Set.Ioo 0 1, indexAt (eA k).val v = k.val ∧
        A.eval k u = p.eval (eA k).val v ∧ A.eval k u ∉ B := by
    obtain ⟨v, hv, hv₀, he⟩ := hAt k hu
    have hbefore (hi : (eA k).val = i) : v < li := by simpa only [hi, ↓reduceIte] using hv.2
    have hp : inPrefix (eA k).val v := ⟨(eA k).property, hbefore⟩
    refine ⟨v, hv₀, ?_, he, ?_⟩
    · simp only [indexAt, dite_eq_left hp,
        show (⟨(eA k).val, hp.1⟩ : Set.Icc 0 i) = eA k from rfl, eA.symm_apply_apply]
    rw [he]
    apply hretained _ _ (Set.Ioo_subset_Icc_self hv₀)
    · exact fun hi => Or.inl (hbefore hi)
    · intro hj
      exact (hij.not_ge (hj ▸ (eA k).property.2)).elim
  have hMtrace (k : Fin M.reverse.segments) {u : ℝ} (hu : u ∈ Set.Ioo 0 1) :
      ∃ v ∈ Set.Ioo 0 1, indexAt (eM k.rev).val v = (A.concat L).segments + k.val ∧
        M.reverse.eval k u = p.eval (eM k.rev).val v ∧ M.reverse.eval k u ∉ B := by
    have hu' : 1 - u ∈ Set.Ioo 0 1 := ⟨sub_pos.mpr hu.2, sub_lt_self _ hu.1⟩
    obtain ⟨v, hv, hv₀, he⟩ := hMt k.rev hu'
    have hafter (hi : (eM k.rev).val = i) : ui < v := by
      simpa only [hi, ↓reduceIte] using hv.1
    have hbefore (hj : (eM k.rev).val = j) : v < lj := by
      simpa only [hj, ↓reduceIte] using hv.2
    have hp : ¬ inPrefix (eM k.rev).val v := by
      rintro ⟨⟨_, hle⟩, hb⟩
      have hi := le_antisymm hle (eM k.rev).property.1
      exact (hi₀.trans (hafter hi)).not_gt (hb hi)
    have hm : inMiddle (eM k.rev).val v := ⟨(eM k.rev).property, hbefore⟩
    have he' := (eval_reverse M k u).trans he
    refine ⟨v, hv₀, ?_, he', ?_⟩
    · simp only [indexAt, dite_eq_right hp, dite_eq_left hm,
        show (⟨(eM k.rev).val, hm.1⟩ : Set.Icc i j) = eM k.rev from rfl]
      rw [eM.symm_apply_apply k.rev]
      exact congrArg (fun l : Fin M.segments => (A.concat L).segments + l.val) (Fin.rev_rev k)
    rw [he']
    exact hretained _ _ (Set.Ioo_subset_Icc_self hv₀) (fun h => Or.inr (hafter h))
      (fun h => Or.inl (hbefore h))
  have hStrace (k : Fin S.segments) {u : ℝ} (hu : u ∈ Set.Ioo 0 1) :
      ∃ v ∈ Set.Ioo 0 1,
        indexAt (eS k).val v = (((A.concat L).concat M.reverse).concat R).segments + k.val ∧
        S.eval k u = p.eval (eS k).val v ∧ S.eval k u ∉ B := by
    obtain ⟨v, hv, hv₀, he⟩ := hSt k hu
    have hafter (hj : (eS k).val = j) : uj < v := by simpa only [hj, ↓reduceIte] using hv.1
    have hp : ¬ inPrefix (eS k).val v := by
      rintro ⟨⟨_, hle⟩, _⟩
      exact hij.not_ge ((eS k).property.1.trans hle)
    have hm : ¬ inMiddle (eS k).val v := by
      rintro ⟨⟨_, hle⟩, hb⟩
      have hj := le_antisymm hle (eS k).property.1
      exact (hj₀.trans (hafter hj)).not_gt (hb hj)
    refine ⟨v, hv₀, ?_, he, ?_⟩
    · simp only [indexAt, dite_eq_right hp, dite_eq_right hm, dite_eq_left (eS k).property,
        show (⟨(eS k).val, (eS k).property⟩ : Set.Icc j jlast) = eS k from rfl,
        eS.symm_apply_apply]
    rw [he]
    apply hretained _ _ (Set.Ioo_subset_Icc_self hv₀)
    · intro hi
      exact (hij.not_ge (hi ▸ (eS k).property.1)).elim
    · exact fun hj => Or.inr (hafter hj)
  have hlocation (k : Fin q.segments) {u : ℝ} (hu : u ∈ Set.Ioo 0 1) :
      (∃ l : Fin p.segments, ∃ v ∈ Set.Ioo 0 1, indexAt l v = k.val ∧
        q.eval k u = p.eval l v ∧ q.eval k u ∉ B) ∨
      (k.val = A.segments ∧ q.eval k u ∈ segment ℝ a c) ∨
      (k.val = ((A.concat L).concat M.reverse).segments ∧ q.eval k u ∈ segment ℝ b d) := by
    rcases concat_eval_cases _ S hjoinS k u with ⟨k₄, h₄, he₄⟩ | ⟨kS, hS, heS⟩
    · rcases concat_eval_cases _ R hjoinR k₄ u with ⟨k₃, h₃, he₃⟩ | ⟨kR, hR, heR⟩
      · rcases concat_eval_cases _ M.reverse hjoinM k₃ u with ⟨k₂, h₂, he₂⟩ | ⟨kM, hM, heM⟩
        · rcases concat_eval_cases A L hjoinL k₂ u with ⟨kA, hkA, heA⟩ | ⟨kL, hL, heL⟩
          · obtain ⟨v, hv, hidx, he, hw⟩ := hAtrace kA hu
            have hval := he₄.trans (he₃.trans (he₂.trans heA))
            exact Or.inl ⟨_, v, hv, hidx.trans (h₄.trans (h₃.trans (h₂.trans hkA))).symm,
              hval.trans he, hval.symm ▸ hw⟩
          · apply Or.inr ∘ Or.inl
            refine ⟨h₄.trans (h₃.trans (h₂.trans ?_)), ?_⟩
            · simpa only [show kL.val = 0 from Nat.lt_one_iff.mp kL.isLt, add_zero] using hL
            · rw [he₄, he₃, he₂, heL, eval_line]
              exact lineMap_mem_segment ℝ _ _ (Set.Ioo_subset_Icc_self hu)
        · obtain ⟨v, hv, hidx, he, hw⟩ := hMtrace kM hu
          have hval := he₄.trans (he₃.trans heM)
          exact Or.inl ⟨_, v, hv, hidx.trans (h₄.trans (h₃.trans hM)).symm,
            hval.trans he, hval.symm ▸ hw⟩
      · apply Or.inr ∘ Or.inr
        refine ⟨h₄.trans ?_, ?_⟩
        · simpa only [show kR.val = 0 from Nat.lt_one_iff.mp kR.isLt, add_zero] using hR
        · rw [he₄, heR, eval_line]
          exact lineMap_mem_segment ℝ _ _ (Set.Ioo_subset_Icc_self hu)
    · obtain ⟨v, hv, hidx, he, hw⟩ := hStrace kS hu
      exact Or.inl ⟨_, v, hv, hidx.trans hS.symm, heS.trans he, heS.symm ▸ hw⟩
  have hcut_injective (k : Fin p.segments)
      (hz : z ∈ openSegment ℝ (p.point k.castSucc) (p.point k.succ)) :
      Function.Injective (p.eval k) := by
    apply AffineMap.lineMap_injective ℝ
    intro he
    have hz' := openSegment_subset_segment ℝ _ _ hz
    rw [he, segment_same, Set.mem_singleton_iff] at hz'
    exact hends k.succ (hz' ▸ Metric.mem_closedBall_self hρ.le)
  have hindexAt (k : Fin p.segments) {u v : ℝ} (he : p.eval k u = p.eval k v) :
      indexAt k u = indexAt k v := by
    by_cases hi : k = i
    · subst k
      rw [hcut_injective i hzi he]
    by_cases hj : k = j
    · subst k
      rw [hcut_injective j hzj he]
    simp [indexAt, inPrefix, inMiddle, hi, hj]
  have hCross : openSegmentCrossings (fun k : Fin q.segments => q.point k.castSucc)
      (fun k => q.point k.succ) ⊆ openSegmentCrossings
        (fun k : Fin p.segments => p.point k.castSucc) (fun k => p.point k.succ) \ B := by
    rintro w ⟨k, l, hkl, hk, hl⟩
    rw [openSegment_eq_image_lineMap] at hk hl
    obtain ⟨u, hu, he⟩ := hk
    obtain ⟨v, hv, he'⟩ := hl
    change q.eval k u = w at he
    change q.eval l v = w at he'
    have hk := hlocation k hu
    have hl := hlocation l hv
    rw [he] at hk
    rw [he'] at hl
    have hw : w ∉ B := by
      intro hw
      rcases hk.resolve_left (by rintro ⟨_, _, _, _, _, h⟩; exact h hw) with hk | hk <;>
        rcases hl.resolve_left (by rintro ⟨_, _, _, _, _, h⟩; exact h hw) with hl | hl
      · exact hkl (Fin.ext (hk.1.trans hl.1.symm))
      · exact Set.disjoint_left.mp hdisjoint hk.2 hl.2
      · exact Set.disjoint_left.mp hdisjoint hl.2 hk.2
      · exact hkl (Fin.ext (hk.1.trans hl.1.symm))
    have hnotChord (n : ℕ) : ¬ ((n = A.segments ∧ w ∈ segment ℝ a c) ∨
        (n = ((A.concat L).concat M.reverse).segments ∧ w ∈ segment ℝ b d)) :=
      fun h => hw (hNew (h.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)))
    obtain ⟨k', u', hu', hidx, he₁, _⟩ := hk.resolve_right (hnotChord k.val)
    obtain ⟨l', v', hv', hidx', he₂, _⟩ := hl.resolve_right (hnotChord l.val)
    have hne : k' ≠ l' := by
      rintro rfl
      exact hkl (Fin.ext (hidx.symm.trans ((hindexAt k' (he₁.symm.trans he₂)).trans hidx')))
    refine ⟨⟨k', l', hne, ?_, ?_⟩, hw⟩
    · exact he₁.symm ▸ lineMap_mem_openSegment ℝ _ _ hu'
    · exact he₂.symm ▸ lineMap_mem_openSegment ℝ _ _ hv'
  have hInside : E ∩ B ⊆ N := by
    rintro w ⟨(hA' | hM') | hS', hw⟩
    · rw [hA] at hA'
      obtain ⟨k, hk, u, hu, rfl⟩ := hA'
      by_cases hki : k = i
      · subst k
        have h : u = li := le_antisymm (by simpa using hu.2) ((hiBall u).mp hw).1
        subst u
        exact Or.inl (left_mem_segment ℝ a c)
      · exact (hother k u ⟨by simpa only [ite_self] using hu.1,
          by simpa only [ite_eq_right hki] using hu.2⟩ hki ((hk.2.trans_lt hij).ne) hw).elim
    · rw [hM] at hM'
      obtain ⟨k, _, u, hu, rfl⟩ := hM'
      by_cases hki : k = i
      · subst k
        have h : u = ui := le_antisymm ((hiBall u).mp hw).2 (by simpa using hu.1)
        subst u
        exact Or.inr (left_mem_segment ℝ b d)
      · by_cases hkj : k = j
        · subst k
          have h : u = lj := le_antisymm (by simpa using hu.2) ((hjBall u).mp hw).1
          subst u
          exact Or.inl (right_mem_segment ℝ a c)
        · exact (hother k u ⟨by simpa only [ite_eq_right hki] using hu.1,
            by simpa only [ite_eq_right hkj] using hu.2⟩ hki hkj hw).elim
    · rw [hS] at hS'
      obtain ⟨k, hk, u, hu, rfl⟩ := hS'
      by_cases hkj : k = j
      · subst k
        have h : u = uj := le_antisymm ((hjBall u).mp hw).2 (by simpa using hu.1)
        subst u
        exact Or.inr (right_mem_segment ℝ b d)
      · exact (hother k u ⟨by simpa only [ite_eq_right hkj] using hu.1,
          by simpa only [ite_self] using hu.2⟩ (hij.trans_le hk.1).ne' hkj hw).elim
  have hDisk : q.support ∩ B = N := by
    rw [hq]
    ext w
    exact ⟨fun hw => hw.1.elim (fun he => hInside ⟨he, hw.2⟩) id,
      fun hw => ⟨Or.inr hw, hNew hw⟩⟩
  have hNoCenter : z ∉ q.support := by
    intro hz
    have hzB : z ∈ q.support ∩ B := ⟨hz, Metric.mem_closedBall_self hρ.le⟩
    rw [hDisk] at hzB
    exact hcenter hzB
  refine ⟨q, hstart, hfinish, hNoCenter, ?_, ?_, ?_, hCross, li, ui, lj, uj,
    hli, hi₀, hui, hlj, hj₀, huj, ha, hb, hc, hd, hDisk, hdisjoint⟩
  · change q.support \ B = p.support \ B
    rw [hq]
    ext w
    exact ⟨fun hw => ⟨hE (hw.1.resolve_right (fun hn => hw.2 (hNew hn))), hw.2⟩,
      fun hw => ⟨Or.inl (cover hw), hw.2⟩⟩
  · intro r hr
    have hL : Disjoint L.support r.support := hr.mono_left (by
      rw [support_line]
      exact fun _ hw => hNew (Or.inl hw))
    have hR : Disjoint R.support r.support := hr.mono_left (by
      rw [support_line]
      exact fun _ hw => hNew (Or.inr hw))
    have hcuti := hr.mono_left ((convex_closedBall z ρ).segment_subset
      (Metric.sphere_subset_closedBall ha) (Metric.sphere_subset_closedBall hb))
    have hcutj := hr.mono_left ((convex_closedBall z ρ).segment_subset
      (Metric.sphere_subset_closedBall hc) (Metric.sphere_subset_closedBall hd))
    simpa only [q, intersectionParity_concat_left _ _ _ hjoinS,
      intersectionParity_concat_left _ _ _ hjoinR, intersectionParity_concat_left _ _ _ hjoinM,
      intersectionParity_concat_left _ _ _ hjoinL, intersectionParity_reverse_left,
      intersectionParity_eq_zero_of_disjoint hL, intersectionParity_eq_zero_of_disjoint hR,
      add_zero, hAp, hMp, hSp] using
      intervalParity_splice p hij r hli hi₀ hui hlj hj₀ huj hcuti hcutj
  · intro side
    simp only [q, germ_concat _ _ hjoinS, germ_concat _ _ hjoinR, germ_concat _ _ hjoinM,
      germ_concat _ _ hjoinL]
    cases side
    · simpa only [Bool.false_eq_true, ↓reduceIte] using hAg rfl rfl
    · simpa only [↓reduceIte] using hSg rfl rfl

end Cslib.Polygonal.Route
