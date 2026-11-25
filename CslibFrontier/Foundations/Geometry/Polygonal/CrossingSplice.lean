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
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import CslibFrontier.Foundations.Geometry.Polygonal.CircleChord
import CslibFrontier.Foundations.Geometry.Polygonal.Concatenate
import CslibFrontier.Foundations.Geometry.Polygonal.Germs
import CslibFrontier.Foundations.Geometry.Polygonal.Reverse
import CslibFrontier.Foundations.Geometry.Polygonal.RouteIntersectionCutEnds
import CslibFrontier.Foundations.Geometry.Polygonal.Trisection
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
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
  refine Finset.sum_congr rfl fun k _ => ?_
  change _ = ∑ l : Fin 1, _
  rw [Fin.sum_univ_one]; rfl

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

private abbrev IntervalEvaluation (p q : Route) {i j : Fin p.segments} (s t : ℝ)
    (e : Fin q.segments ≃o Set.Icc i j) : Prop :=
  ∀ k, let lo := if (e k).val = i then s else 0
       let hi := if (e k).val = j then t else 1
       0 ≤ lo ∧ lo < hi ∧ hi ≤ 1 ∧ ∀ u : ℝ,
         q.eval k u = p.eval (e k).val (AffineMap.lineMap lo hi u)

private theorem interval_eval_injective {p q : Route} {i j : Fin p.segments} {s t : ℝ}
    {e : Fin q.segments ≃o Set.Icc i j} (hspec : IntervalEvaluation p q s t e)
    (hp : ∀ k : Fin p.segments, p.point k.castSucc ≠ p.point k.succ)
    (k : Fin q.segments) : Function.Injective (q.eval k) := by
  obtain ⟨_, hlt, _, he⟩ := hspec k
  intro u v h
  rw [he u, he v] at h
  exact AffineMap.lineMap_injective ℝ hlt.ne (AffineMap.lineMap_injective ℝ (hp _) h)

private theorem affineSpan_eq_of_reparam {p q : Route} {k : Fin q.segments}
    {l : Fin p.segments} {f : ℝ → ℝ} (hf : f 0 ≠ f 1)
    (he : ∀ u, q.eval k u = p.eval l (f u)) :
    affineSpan ℝ ({q.point k.castSucc, q.point k.succ} : Set ℂ) =
      affineSpan ℝ ({p.point l.castSucc, p.point l.succ} : Set ℂ) := by
  have h₀ := he 0
  have h₁ := he 1
  simp only [eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at h₀ h₁
  rw [h₀, h₁]
  by_cases hp : p.point l.castSucc = p.point l.succ
  · simp only [hp, AffineMap.lineMap_same_apply]
  · exact affineSpan_pair_eq_of_mem_of_mem_of_ne
      (AffineMap.lineMap_mem_affineSpan_pair _ _ _) (AffineMap.lineMap_mem_affineSpan_pair _ _ _)
      ((AffineMap.lineMap_injective ℝ hp).ne hf)

private theorem exists_parameter_at_point (p : Route) (a : Fin (p.segments + 1)) :
    ∃ (k : Fin p.segments) (u : ℝ), u ∈ Set.Icc 0 1 ∧ u ∉ Set.Ioo 0 1 ∧
      p.eval k u = p.point a ∧ p.position k u = (a.val : ℝ) := by
  refine Fin.lastCases ?_ (fun k => ?_) a
  · refine ⟨Fin.last p.bends, 1, ⟨zero_le_one, le_rfl⟩, fun h => (lt_irrefl _ h.2), ?_, ?_⟩
    · simp only [eval, AffineMap.lineMap_apply_one, Fin.succ_last]
    · simp only [position, Fin.val_last, segments, Nat.cast_add, Nat.cast_one]
  · exact ⟨k, 0, ⟨le_rfl, zero_le_one⟩, fun h => lt_irrefl _ h.1,
      AffineMap.lineMap_apply_zero _ _, add_zero _⟩

private theorem exists_point_at_end_parameter {p : Route} (k : Fin p.segments) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) (hopen : u ∉ Set.Ioo 0 1) :
    ∃ a : Fin (p.segments + 1), p.eval k u = p.point a ∧ p.position k u = (a.val : ℝ) := by
  have he : u ∈ ({0, 1} : Set ℝ) :=
    Set.Icc_sdiff_Ioo_same (show (0 : ℝ) ≤ 1 from zero_le_one) ▸ ⟨hu, hopen⟩
  rcases Set.mem_insert_iff.mp he with rfl | he
  · exact ⟨k.castSucc, AffineMap.lineMap_apply_zero _ _, add_zero _⟩
  · rw [Set.mem_singleton_iff] at he
    subst u
    exact ⟨k.succ, AffineMap.lineMap_apply_one _ _, by simp only [position, Fin.val_succ,
      Nat.cast_add, Nat.cast_one]⟩

private theorem position_ne_nat_of_mem_Ioo {p : Route} (k : Fin p.segments) {u : ℝ}
    (hu : u ∈ Set.Ioo 0 1) (n : ℕ) : p.position k u ≠ (n : ℝ) := by
  intro he
  dsimp only [position] at he
  have hlo : k.val < n := mod_cast (by linarith [hu.1] : (k.val : ℝ) < n)
  have hhi : n < k.val + 1 := mod_cast (by linarith [hu.2] : (n : ℝ) < k.val + 1)
  omega

private noncomputable abbrev intervalTime {p q : Route} {i j : Fin p.segments} (s t : ℝ)
    (e : Fin q.segments ≃o Set.Icc i j) (k : Fin q.segments) (u : ℝ) : ℝ :=
  AffineMap.lineMap (if (e k).val = i then s else 0) (if (e k).val = j then t else 1) u

private abbrev IntervalPositions (p q : Route) {i j : Fin p.segments} (s t : ℝ)
    (e : Fin q.segments ≃o Set.Icc i j) : Prop :=
  ∀ (k l : Fin q.segments) {u v : ℝ}, u ∈ Set.Icc 0 1 → v ∈ Set.Icc 0 1 →
    p.position (e k).val (intervalTime s t e k u) =
      p.position (e l).val (intervalTime s t e l v) → q.position k u = q.position l v

private theorem interval_source_position_bounds {p : Route} {i j : Fin p.segments} {s t v : ℝ}
    (hi : s ≤ 1) (hj : 0 ≤ t) (k : Set.Icc i j) (hv₀ : v ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (if k.val = i then s else 0) (if k.val = j then t else 1)) :
    p.position k.val v ∈ Set.Icc (p.position i s) (p.position j t) := by
  constructor
  · by_cases h : k.val = i
    · simpa only [position, h, add_le_add_iff_left, ↓reduceIte] using hv.1
    · have hstep : (i.val : ℝ) + 1 ≤ k.val.val :=
        mod_cast lt_of_le_of_ne k.property.1 (Ne.symm h)
      dsimp only [position]
      linarith only [hi, hv₀.1, hstep]
  · by_cases h : k.val = j
    · simpa only [position, h, add_le_add_iff_left, ↓reduceIte] using hv.2
    · have hstep : (k.val.val : ℝ) + 1 ≤ j.val := mod_cast lt_of_le_of_ne k.property.2 h
      dsimp only [position]
      linarith only [hj, hv₀.2, hstep]

private theorem interval_first {n : ℕ} {i j : Fin n} (hij : i ≤ j) {m : ℕ}
    (e : Fin (m + 1) ≃o Set.Icc i j) : (e 0).val = i := by
  let first : Set.Icc i j := ⟨i, le_rfl, hij⟩
  have h := e.monotone (Fin.zero_le (e.symm first))
  rw [e.apply_symm_apply] at h
  exact le_antisymm h (e 0).property.1

private theorem interval_last {n : ℕ} {i j : Fin n} (hij : i ≤ j) {m : ℕ}
    (e : Fin (m + 1) ≃o Set.Icc i j) : (e (Fin.last m)).val = j := by
  let last : Set.Icc i j := ⟨j, hij, le_rfl⟩
  have h := e.monotone (Fin.le_last (e.symm last))
  rw [e.apply_symm_apply] at h
  exact le_antisymm (e (Fin.last m)).property.2 h

private theorem interval_open_eval {p q : Route} {i j : Fin p.segments} {s t : ℝ}
    {e : Fin q.segments ≃o Set.Icc i j} (hspec : IntervalEvaluation p q s t e)
    (k : Fin q.segments) {u : ℝ} (hu : u ∈ Set.Ioo 0 1) :
    ∃ v ∈ Set.Ioo (if (e k).val = i then s else 0) (if (e k).val = j then t else 1),
      v ∈ Set.Ioo 0 1 ∧ q.eval k u = p.eval (e k).val v ∧ v = intervalTime s t e k u := by
  obtain ⟨hl, hlt, hh, he⟩ := hspec k
  let lo := if (e k).val = i then s else 0
  let hi := if (e k).val = j then t else 1
  have hv : AffineMap.lineMap lo hi u ∈ Set.Ioo lo hi := by
    rw [← openSegment_eq_Ioo hlt]
    exact lineMap_mem_openSegment ℝ lo hi hu
  exact ⟨_, hv, ⟨hl.trans_lt hv.1, hv.2.trans_le hh⟩, he u, rfl⟩

private theorem interval_exterior_interior_iff {p q : Route} {i j : Fin p.segments} {s t : ℝ}
    {e : Fin q.segments ≃o Set.Icc i j} (hspec : IntervalEvaluation p q s t e)
    {B : Set ℂ} (hstart : s = 0 ∨ p.eval i s ∈ B) (hfinish : t = 1 ∨ p.eval j t ∈ B)
    (k : Fin q.segments) {u v : ℝ} (hu : u ∈ Set.Icc 0 1)
    (htime : v = intervalTime s t e k u) (hout : p.eval (e k).val v ∉ B) :
    u ∈ Set.Ioo 0 1 ↔ v ∈ Set.Ioo 0 1 := by
  constructor
  · intro hu'
    obtain ⟨w, _, hw, _, hwtime⟩ := interval_open_eval hspec k hu'
    exact (hwtime.trans htime.symm) ▸ hw
  · intro hv
    have hzero (h : u = 0) : v = 0 := by
      have he := htime
      simp only [intervalTime, h, AffineMap.lineMap_apply_zero] at he
      split_ifs at he with hk
      · exact hstart.elim (he.trans ·) fun hs => (hout (by simpa only [hk, he] using hs)).elim
      · exact he
    have hone (h : u = 1) : v = 1 := by
      have he := htime
      simp only [intervalTime, h, AffineMap.lineMap_apply_one] at he
      split_ifs at he with hk
      · exact hfinish.elim (he.trans ·) fun ht => (hout (by simpa only [hk, he] using ht)).elim
      · exact he
    exact ⟨lt_of_le_of_ne hu.1 (fun h => hv.1.ne' (hzero h.symm)),
      lt_of_le_of_ne hu.2 (fun h => hv.2.ne (hone h))⟩

private theorem interval_closed_eval {p q : Route} {i j : Fin p.segments} {s t : ℝ}
    (hij : i ≤ j) {e : Fin q.segments ≃o Set.Icc i j} (hspec : IntervalEvaluation p q s t e)
    (k : Fin q.segments) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    ∃ v ∈ Set.Icc (if (e k).val = i then s else 0) (if (e k).val = j then t else 1),
      v ∈ Set.Icc 0 1 ∧ q.eval k u = p.eval (e k).val v ∧
      ((e k).val = i → v = s → q.position k u = 0) ∧
      ((e k).val = j → v = t → q.position k u = q.segments) ∧
      v = intervalTime s t e k u := by
  obtain ⟨hl, hlt, hh, he⟩ := hspec k
  let lo := if (e k).val = i then s else 0
  let hi := if (e k).val = j then t else 1
  let v := AffineMap.lineMap lo hi u
  have hv : v ∈ Set.Icc lo hi := by
    rw [← segment_eq_Icc hlt.le]
    exact lineMap_mem_segment ℝ lo hi hu
  have hinj := AffineMap.lineMap_injective ℝ (show lo ≠ hi from hlt.ne)
  refine ⟨v, hv, ⟨hl.trans hv.1, hv.2.trans hh⟩, he u, ?_, ?_, rfl⟩
  · intro hk heq
    have hk₀ : k = 0 := e.injective (Subtype.ext (hk.trans (interval_first hij e).symm))
    have hu₀ : u = 0 := hinj (by
      rw [AffineMap.lineMap_apply_zero]
      simpa only [v, lo, hk, ↓reduceIte] using heq)
    simp [position, hk₀, hu₀]
  · intro hk heq
    have hk₁ : k = Fin.last q.bends :=
      e.injective (Subtype.ext (hk.trans (interval_last hij e).symm))
    have hu₁ : u = 1 := hinj (by
      rw [AffineMap.lineMap_apply_one]
      simpa only [v, hi, hk, ↓reduceIte] using heq)
    simp [position, hk₁, hu₁, segments]

private theorem exists_route_support_between (p : Route) (i j : Fin p.segments) (hij : i ≤ j)
    {s t : ℝ} (hs : s ∈ Set.Ico 0 1) (ht : t ∈ Set.Ioc 0 1) (hst : i = j → s < t) :
    ∃ q : Route, q.start = p.eval i s ∧ q.finish = p.eval j t ∧
      q.support = intervalSupport p i j s t ∧
      (∀ r : Route, q.intersectionParity r = intervalParity p i j s t r) ∧
      (i = 0 → s = 0 → ∃ c : ℝ, 0 < c ∧ q.germ false = c • p.germ false) ∧
      (j = Fin.last p.bends → t = 1 → ∃ c : ℝ, 0 < c ∧ q.germ true = c • p.germ true) ∧
      ∃ e : Fin q.segments ≃o Set.Icc i j,
        IntervalEvaluation p q s t e ∧ IntervalPositions p q s t e := by
  obtain ⟨q, e, hstart, hfinish, hspec, hpositions⟩ := p.exists_subroute_between i j hij hs ht hst
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
    have hi' := interval_first hij e
    obtain ⟨_, hlt, _, he⟩ := hspec 0
    simp only [hi', ↓reduceIte] at hlt he
    apply exists_pos_smul_germ_of_end_eval q p false hlt hs₀
    simpa only [endSegment, Bool.false_eq_true, ↓reduceIte, hi] using he
  have hgerm_finish (hj : j = Fin.last p.bends) (ht₁ : t = 1) :
      ∃ c : ℝ, 0 < c ∧ q.germ true = c • p.germ true := by
    have hj' := interval_last hij e
    obtain ⟨_, hlt, _, he⟩ := hspec (Fin.last q.bends)
    simp only [hj', ↓reduceIte] at hlt he
    apply exists_pos_smul_germ_of_end_eval q p true hlt ht₁
    simpa only [endSegment, ↓reduceIte, hj] using he
  refine ⟨q, hstart, hfinish, ?_, hparity, hgerm_start, hgerm_finish, e, hspec, hpositions⟩
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
      rw [← hel, ← segment_eq_Icc hlt.le, segment_eq_image_lineMap] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      rw [← hel] at hwu
      exact ⟨l, v, hv, (he v).trans hwu⟩

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
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => decide_eq_false ?_
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
meeting in their open interiors gives an original crossing point outside the closed disk.
At each exterior point, the open segments through the point embed into the original
open segments through that point, preserving their supporting affine spans.
Inside the disk, equal evaluations have equal positions along the spliced route, including
at the four cut endpoints. Outside the disk, a point reached at distinct positions of the
splice is also reached at distinct original positions, with each visit preserving whether
it is in the interior of its segment. Individual exterior visits also retain their endpoint
or interior status. Distinct listed points, exclusion of listed points from open segments, and
nondegeneracy of segments are each preserved if they hold for the original route. -/
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
      (∀ (k l : Fin q.segments) {s t : ℝ}, s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
        q.eval k s ∈ Metric.closedBall z ρ → q.eval k s = q.eval l t →
          q.position k s = q.position l t) ∧
      (∀ (k l : Fin q.segments) {s t : ℝ}, s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
        q.eval k s ∉ Metric.closedBall z ρ → q.eval k s = q.eval l t →
        q.position k s ≠ q.position l t →
        ∃ (a b : Fin p.segments) (u v : ℝ), u ∈ Set.Icc 0 1 ∧ v ∈ Set.Icc 0 1 ∧
          p.eval a u = q.eval k s ∧ p.eval b v = q.eval l t ∧ p.position a u ≠ p.position b v ∧
          (s ∈ Set.Ioo 0 1 ↔ u ∈ Set.Ioo 0 1) ∧ (t ∈ Set.Ioo 0 1 ↔ v ∈ Set.Ioo 0 1)) ∧
      ((∀ k : Fin p.segments, p.point k.castSucc ≠ p.point k.succ) →
        ∀ k : Fin q.segments, q.point k.castSucc ≠ q.point k.succ) ∧
      (∀ (k : Fin q.segments) {s : ℝ}, s ∈ Set.Icc 0 1 → q.eval k s ∉ Metric.closedBall z ρ →
        ∃ (a : Fin p.segments) (u : ℝ), u ∈ Set.Icc 0 1 ∧ p.eval a u = q.eval k s ∧
          (s ∈ Set.Ioo 0 1 ↔ u ∈ Set.Ioo 0 1)) ∧
      (Function.Injective p.point → Function.Injective q.point) ∧
      ((∀ (a : Fin (p.segments + 1)) (k : Fin p.segments),
        p.point a ∉ openSegment ℝ (p.point k.castSucc) (p.point k.succ)) →
        ∀ (a : Fin (q.segments + 1)) (k : Fin q.segments),
          q.point a ∉ openSegment ℝ (q.point k.castSucc) (q.point k.succ)) ∧
      (∀ w ∉ Metric.closedBall z ρ,
        ∃ f : {k : Fin q.segments // w ∈ openSegment ℝ (q.point k.castSucc) (q.point k.succ)} ↪
            {k : Fin p.segments // w ∈ openSegment ℝ (p.point k.castSucc) (p.point k.succ)},
          ∀ k, affineSpan ℝ ({q.point k.val.castSucc, q.point k.val.succ} : Set ℂ) =
            affineSpan ℝ ({p.point (f k).val.castSucc, p.point (f k).val.succ} : Set ℂ)) ∧
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
  have hport_ne {u v : ℝ} (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
      (hsphere : p.eval i u ∈ Metric.sphere z ρ) : p.eval i u ≠ p.eval j v := by
    intro h
    have hmem₁ : p.eval i u ∈ segment ℝ (p.point i.castSucc) (p.point i.succ) :=
      lineMap_mem_segment ℝ _ _ hu
    have hmem₂ : p.eval j v ∈ segment ℝ (p.point j.castSucc) (p.point j.succ) :=
      lineMap_mem_segment ℝ _ _ hv
    have he : p.eval i u = z := hpair ⟨hmem₁, h.symm ▸ hmem₂⟩
      ⟨openSegment_subset_segment ℝ _ _ hzi, openSegment_subset_segment ℝ _ _ hzj⟩
    exact hρ.ne' ((Metric.mem_sphere.mp hsphere).symm.trans (he.symm ▸ dist_self z))
  have hli' : li ∈ Set.Icc 0 1 := ⟨hli.le, (hi₀.trans hui).le⟩
  have hui' : ui ∈ Set.Icc 0 1 := ⟨(hli.trans hi₀).le, hui.le⟩
  have hlj' : lj ∈ Set.Icc 0 1 := ⟨hlj.le, (hj₀.trans huj).le⟩
  have huj' : uj ∈ Set.Icc 0 1 := ⟨(hlj.trans hj₀).le, huj.le⟩
  have hdisjoint : Disjoint (segment ℝ a c) (segment ℝ b d) :=
    disjoint_segments_of_antipodal_pairs ha hc (hport_ne hui' hlj' hb).symm hiMid hjMid
  let jlast : Fin p.segments := Fin.last p.bends
  obtain ⟨A, hA₀, hA₁, hA, hAp, hAg, _, eA, hAt, hApos⟩ :=
    exists_route_support_between p 0 i (Fin.zero_le i)
    (s := 0) (t := li) ⟨le_rfl, zero_lt_one⟩ ⟨hli, (hi₀.trans hui).le⟩ (fun _ => hli)
  obtain ⟨M, hM₀, hM₁, hM, hMp, _, _, eM, hMt, hMpos⟩ := exists_route_support_between p i j hij.le
    (s := ui) (t := lj) ⟨(hli.trans hi₀).le, hui⟩ ⟨hlj, (hj₀.trans huj).le⟩
    (fun h => (hij.ne h).elim)
  obtain ⟨S, hS₀, hS₁, hS, hSp, _, hSg, eS, hSt, hSpos⟩ :=
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
    · obtain ⟨w, hw, he⟩ := hreflect ▸ h
      exact Set.disjoint_left.mp hdisjoint (f.injective (he.trans hfz.symm) ▸ hw) h
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
    obtain ⟨v, hv, hv₀, he, _⟩ := interval_open_eval hAt k hu
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
    have hu' := Set.Ioo.one_sub_mem hu
    obtain ⟨v, hv, hv₀, he, _⟩ := interval_open_eval hMt k.rev hu'
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
    obtain ⟨v, hv, hv₀, he, _⟩ := interval_open_eval hSt k hu
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
  have hparts (k : Fin q.segments) :
      (∃ l : Fin A.segments, k.val = l.val ∧ ∀ u, q.eval k u = A.eval l u) ∨
      (k.val = A.segments ∧ ∀ u, q.eval k u = AffineMap.lineMap a c u) ∨
      (∃ l : Fin M.reverse.segments, k.val = (A.concat L).segments + l.val ∧
        ∀ u, q.eval k u = M.reverse.eval l u) ∨
      (k.val = ((A.concat L).concat M.reverse).segments ∧
        ∀ u, q.eval k u = AffineMap.lineMap b d u) ∨
      (∃ l : Fin S.segments, k.val = (((A.concat L).concat M.reverse).concat R).segments + l.val ∧
        ∀ u, q.eval k u = S.eval l u) := by
    rcases concat_eval_cases _ S hjoinS k with ⟨k₄, h₄, he₄⟩ | ⟨kS, hS, heS⟩
    · rcases concat_eval_cases _ R hjoinR k₄ with ⟨k₃, h₃, he₃⟩ | ⟨kR, hR, heR⟩
      · rcases concat_eval_cases _ M.reverse hjoinM k₃ with ⟨k₂, h₂, he₂⟩ | ⟨kM, hM, heM⟩
        · rcases concat_eval_cases A L hjoinL k₂ with ⟨kA, hkA, heA⟩ | ⟨kL, hL, heL⟩
          · exact Or.inl ⟨kA, h₄.trans (h₃.trans (h₂.trans hkA)),
              fun u => (he₄ u).trans ((he₃ u).trans ((he₂ u).trans (heA u)))⟩
          · refine Or.inr (Or.inl ⟨h₄.trans (h₃.trans (h₂.trans ?_)), ?_⟩)
            · simpa only [show kL.val = 0 from Nat.lt_one_iff.mp kL.isLt, add_zero] using hL
            · intro u
              rw [he₄, he₃, he₂, heL, eval_line]
        · exact Or.inr (Or.inr (Or.inl ⟨kM, h₄.trans (h₃.trans hM),
            fun u => (he₄ u).trans ((he₃ u).trans (heM u))⟩))
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨h₄.trans ?_, ?_⟩)))
        · simpa only [show kR.val = 0 from Nat.lt_one_iff.mp kR.isLt, add_zero] using hR
        · intro u
          rw [he₄, heR, eval_line]
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨kS, hS, heS⟩)))
  have hnondeg (hp : ∀ k : Fin p.segments, p.point k.castSucc ≠ p.point k.succ)
      (k : Fin q.segments) : q.point k.castSucc ≠ q.point k.succ := by
    have hinj : Function.Injective (q.eval k) := by
      intro u v heq
      rcases hparts k with ⟨l, _, he⟩ | ⟨_, he⟩ | ⟨l, _, he⟩ | ⟨_, he⟩ | ⟨l, _, he⟩ <;>
        rw [he u, he v] at heq
      · exact interval_eval_injective hAt hp l heq
      · exact AffineMap.lineMap_injective ℝ (hport_ne hli' hlj' ha) heq
      · rw [eval_reverse, eval_reverse] at heq
        have h := interval_eval_injective hMt hp l.rev heq
        linarith only [h]
      · exact AffineMap.lineMap_injective ℝ (hport_ne hui' huj' hb) heq
      · exact interval_eval_injective hSt hp l heq
    intro he
    have he' : q.eval k 0 = q.eval k 1 := by
      simpa only [eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using he
    exact zero_ne_one (hinj he')
  let segmentLine (P : Route) (k : Fin P.segments) :=
    affineSpan ℝ ({P.point k.castSucc, P.point k.succ} : Set ℂ)
  have hlocation (k : Fin q.segments) {u : ℝ} (hu : u ∈ Set.Ioo 0 1) :
      (∃ l : Fin p.segments, ∃ v ∈ Set.Ioo 0 1, indexAt l v = k.val ∧
        q.eval k u = p.eval l v ∧ q.eval k u ∉ B ∧ segmentLine q k = segmentLine p l) ∨
      (k.val = A.segments ∧ q.eval k u ∈ segment ℝ a c) ∨
      (k.val = ((A.concat L).concat M.reverse).segments ∧ q.eval k u ∈ segment ℝ b d) := by
    rcases hparts k with ⟨kA, hk, hval⟩ | ⟨hk, hval⟩ | ⟨kM, hk, hval⟩ |
      ⟨hk, hval⟩ | ⟨kS, hk, hval⟩
    · obtain ⟨v, hv, hidx, he, hw⟩ := hAtrace kA hu
      obtain ⟨_, hlt, _, hEval⟩ := hAt kA
      exact Or.inl ⟨_, v, hv, hidx.trans hk.symm, (hval u).trans he, (hval u).symm ▸ hw,
        affineSpan_eq_of_reparam ((AffineMap.lineMap_injective ℝ hlt.ne).ne zero_ne_one)
          (fun t => (hval t).trans (hEval t))⟩
    · exact Or.inr (Or.inl
        ⟨hk, (hval u).symm ▸ lineMap_mem_segment ℝ _ _ (Set.Ioo_subset_Icc_self hu)⟩)
    · obtain ⟨v, hv, hidx, he, hw⟩ := hMtrace kM hu
      obtain ⟨_, hlt, _, hEval⟩ := hMt kM.rev
      have hrev : (1 : ℝ) - 0 ≠ 1 - 1 := by norm_num
      exact Or.inl ⟨_, v, hv, hidx.trans hk.symm, (hval u).trans he, (hval u).symm ▸ hw,
        affineSpan_eq_of_reparam (f := fun t => intervalTime ui lj eM kM.rev (1 - t))
          (fun h => hrev (AffineMap.lineMap_injective ℝ hlt.ne h))
          (fun t => (hval t).trans ((eval_reverse M kM t).trans (hEval (1 - t))))⟩
    · exact Or.inr (Or.inr
        ⟨hk, (hval u).symm ▸ lineMap_mem_segment ℝ _ _ (Set.Ioo_subset_Icc_self hu)⟩)
    · obtain ⟨v, hv, hidx, he, hw⟩ := hStrace kS hu
      obtain ⟨_, hlt, _, hEval⟩ := hSt kS
      exact Or.inl ⟨_, v, hv, hidx.trans hk.symm, (hval u).trans he, (hval u).symm ▸ hw,
        affineSpan_eq_of_reparam ((AffineMap.lineMap_injective ℝ hlt.ne).ne zero_ne_one)
          (fun t => (hval t).trans (hEval t))⟩
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
  let through (P : Route) (w : ℂ) :=
    {k : Fin P.segments // w ∈ openSegment ℝ (P.point k.castSucc) (P.point k.succ)}
  have hthrough (w : ℂ) (k : through q w) :
      (∃ l : through p w, ∃ v, p.eval l.val v = w ∧ indexAt l.val v = k.val ∧
        w ∉ B ∧ segmentLine q k.val = segmentLine p l.val) ∨
        ((k.val : ℕ) = A.segments ∧ w ∈ segment ℝ a c) ∨
        ((k.val : ℕ) = ((A.concat L).concat M.reverse).segments ∧ w ∈ segment ℝ b d) := by
    have ht := k.property
    rw [openSegment_eq_image_lineMap] at ht
    obtain ⟨u, hu, he⟩ := ht
    change q.eval k.val u = w at he
    rcases hlocation k.val hu with ⟨l, v, hv, hi, hvEq, hout, hline⟩ | hc | hd
    · have hw : p.eval l v = w := hvEq.symm.trans he
      exact Or.inl ⟨⟨l, hw ▸ lineMap_mem_openSegment ℝ _ _ hv⟩, v, hw, hi, he ▸ hout, hline⟩
    · exact Or.inr (Or.inl ⟨hc.1, he ▸ hc.2⟩)
    · exact Or.inr (Or.inr ⟨hd.1, he ▸ hd.2⟩)
  have hexterior_open (w : ℂ) (hw : w ∉ B) :
      ∃ f : through q w ↪ through p w, ∀ k, segmentLine q k.val = segmentLine p (f k).val := by
    have ht (k : through q w) :
        ∃ l : through p w, ∃ v, p.eval l.val v = w ∧ indexAt l.val v = k.val ∧
          w ∉ B ∧ segmentLine q k.val = segmentLine p l.val :=
      (hthrough w k).resolve_right (fun h => hw (hNew (h.elim
        (fun h => Or.inl h.2) (fun h => Or.inr h.2))))
    choose f v he hi _ hline using ht
    refine ⟨⟨f, ?_⟩, hline⟩
    intro k l hkl
    have hf := congrArg Subtype.val hkl
    have he' : p.eval (f k).val (v k) = p.eval (f k).val (v l) := by
      rw [he k, hf, he l]
    apply Subtype.ext
    apply Fin.ext
    calc
      _ = indexAt (f k).val (v k) := (hi k).symm
      _ = indexAt (f k).val (v l) := hindexAt (f k).val he'
      _ = _ := by rw [hf, hi l]
  have hCross : openSegmentCrossings (fun k : Fin q.segments => q.point k.castSucc)
      (fun k => q.point k.succ) ⊆ openSegmentCrossings
        (fun k : Fin p.segments => p.point k.castSucc) (fun k => p.point k.succ) \ B := by
    rintro w ⟨k, l, hkl, hk, hl⟩
    let k' : through q w := ⟨k, hk⟩
    let l' : through q w := ⟨l, hl⟩
    have hkl' : k' ≠ l' := fun h => hkl (congrArg Subtype.val h)
    have hw : w ∉ B := by
      intro hw
      have chord (m : through q w) :
          ((m.val : ℕ) = A.segments ∧ w ∈ segment ℝ a c) ∨
            ((m.val : ℕ) = ((A.concat L).concat M.reverse).segments ∧ w ∈ segment ℝ b d) :=
        (hthrough w m).resolve_left (by rintro ⟨_, _, _, _, hout, _⟩; exact hout hw)
      rcases chord k' with hk | hk <;> rcases chord l' with hl | hl
      · exact hkl (Fin.ext (hk.1.trans hl.1.symm))
      · exact Set.disjoint_left.mp hdisjoint hk.2 hl.2
      · exact Set.disjoint_left.mp hdisjoint hl.2 hk.2
      · exact hkl (Fin.ext (hk.1.trans hl.1.symm))
    obtain ⟨f, _⟩ := hexterior_open w hw
    exact ⟨⟨(f k').val, (f l').val, fun h => hkl' (f.injective (Subtype.ext h)),
      (f k').property, (f l').property⟩, hw⟩
  have hshift (P : Route) (k : Fin q.segments) (l : Fin P.segments) {n : ℕ}
      (hk : k.val = n + l.val) (u : ℝ) : q.position k u = (n : ℝ) + P.position l u := by
    simp only [position, hk, Nat.cast_add]
    ring
  let aSource (l : Fin A.segments) (u : ℝ) := p.position (eA l).val (intervalTime 0 li eA l u)
  let mSource (l : Fin M.segments) (u : ℝ) := p.position (eM l).val (intervalTime ui lj eM l u)
  let sSource (l : Fin S.segments) (u : ℝ) := p.position (eS l).val (intervalTime uj 1 eS l u)
  let reversePosition (x : ℝ) := ((A.concat L).segments : ℝ) + (M.segments - x)
  let suffixPosition (x : ℝ) := ((((A.concat L).concat M.reverse).concat R).segments : ℝ) + x
  let lifts (P : Route) (source : Fin P.segments → ℝ → ℝ) (orient : ℝ → ℝ) (x y : ℝ) : Prop :=
    ∃ l u, u ∈ Set.Icc (0 : ℝ) 1 ∧ source l u = x ∧ orient (P.position l u) = y
  let retained (x y : ℝ) : Prop :=
    (x ≤ p.position i li ∧ lifts A aSource id x y) ∨
    (p.position i ui ≤ x ∧ x ≤ p.position j lj ∧ lifts M mSource reversePosition x y) ∨
    (p.position j uj ≤ x ∧ lifts S sSource suffixPosition x y)
  have hExterior (k : Fin q.segments) {u : ℝ} (hu : u ∈ Set.Icc 0 1) (hw : q.eval k u ∉ B) :
      ∃ (r : Fin p.segments) (v : ℝ), v ∈ Set.Icc 0 1 ∧ p.eval r v = q.eval k u ∧
        (u ∈ Set.Ioo 0 1 ↔ v ∈ Set.Ioo 0 1) ∧
        retained (p.position r v) (q.position k u) := by
    rcases hparts k with ⟨l, hk, he⟩ | ⟨_, he⟩ | ⟨l, hk, he⟩ | ⟨_, he⟩ | ⟨l, hk, he⟩ <;>
      specialize he u
    · obtain ⟨v, hv, hv₀, hvEq, _, _, ht⟩ := interval_closed_eval (Fin.zero_le i) hAt l hu
      have h := interval_source_position_bounds zero_le_one hli.le (eA l) hv₀ hv
      have hclass := interval_exterior_interior_iff hAt (Or.inl rfl)
        (Or.inr (Metric.sphere_subset_closedBall ha)) l hu ht (he.trans hvEq ▸ hw)
      refine ⟨_, v, hv₀, (he.trans hvEq).symm, hclass, Or.inl ⟨h.2, l, u, hu, ?_, ?_⟩⟩
      · exact congrArg (p.position (eA l).val) ht.symm
      · simp only [id_eq, position, hk]
    · exact (hw (hNew (Or.inl (he.symm ▸ lineMap_mem_segment ℝ _ _ hu)))).elim
    · have hu' := Set.Icc.one_sub_mem hu
      obtain ⟨v, hv, hv₀, hvEq, _, _, ht⟩ := interval_closed_eval hij.le hMt l.rev hu'
      have h := interval_source_position_bounds hui.le hlj.le (eM l.rev) hv₀ hv
      have hev := he.trans ((eval_reverse M l u).trans hvEq)
      have hclass := interval_exterior_interior_iff hMt
        (Or.inr (Metric.sphere_subset_closedBall hb)) (Or.inr (Metric.sphere_subset_closedBall hc))
        l.rev hu' ht (hev ▸ hw)
      refine ⟨_, v, hv₀, hev.symm, Set.Ioo.mem_iff_one_sub_mem.trans hclass,
        Or.inr (Or.inl ⟨h.1, h.2, l.rev, 1 - u, hu', ?_, ?_⟩)⟩
      · exact congrArg (p.position (eM l.rev).val) ht.symm
      · rw [hshift M.reverse k l hk u, position_reverse]
    · exact (hw (hNew (Or.inr (he.symm ▸ lineMap_mem_segment ℝ _ _ hu)))).elim
    · obtain ⟨v, hv, hv₀, hvEq, _, _, ht⟩ := interval_closed_eval (Fin.le_last j) hSt l hu
      have h := interval_source_position_bounds huj.le zero_le_one (eS l) hv₀ hv
      have hclass := interval_exterior_interior_iff hSt
        (Or.inr (Metric.sphere_subset_closedBall hd)) (Or.inl rfl) l hu ht (he.trans hvEq ▸ hw)
      refine ⟨_, v, hv₀, (he.trans hvEq).symm, hclass, Or.inr (Or.inr ⟨h.1, l, u, hu, ?_, ?_⟩)⟩
      · exact congrArg (p.position (eS l).val) ht.symm
      · exact (hshift S k l hk u).symm
  have hlift (P : Route) (source : Fin P.segments → ℝ → ℝ) (orient : ℝ → ℝ)
      (hpos : ∀ (k l : Fin P.segments) {u v : ℝ}, u ∈ Set.Icc 0 1 → v ∈ Set.Icc 0 1 →
        source k u = source l v → P.position k u = P.position l v)
      {x y y' : ℝ} (hy : lifts P source orient x y) (hy' : lifts P source orient x y') :
      y = y' := by
    obtain ⟨k, u, hu, hx, hy⟩ := hy
    obtain ⟨l, v, hv, hx', hy'⟩ := hy'
    rw [← hy, ← hy', hpos k l hu hv (hx.trans hx'.symm)]
  have hretained_unique {x y y' : ℝ} (hy : retained x y) (hy' : retained x y') : y = y' := by
    have hiGap : p.position i li < p.position i ui := add_lt_add_right hi₀ _
    have hjGap : p.position j lj < p.position j uj := add_lt_add_right hj₀ _
    have hspan : p.position i ui ≤ p.position j lj := by
      have hstep : (i.val : ℝ) + 1 ≤ j.val := by
        exact_mod_cast (show i.val < j.val from hij)
      dsimp only [position]
      linarith only [hui, hlj, hstep]
    rcases hy with ⟨ha, hy⟩ | ⟨hm₀, hm₁, hy⟩ | ⟨hs, hy⟩ <;>
      rcases hy' with ⟨ha', hy'⟩ | ⟨hm₀', hm₁', hy'⟩ | ⟨hs', hy'⟩
    · exact hlift A aSource id hApos hy hy'
    · exact (hiGap.not_ge (hm₀'.trans ha)).elim
    · linarith only [ha, hs', hiGap, hspan, hjGap]
    · exact (hiGap.not_ge (hm₀.trans ha')).elim
    · exact hlift M mSource reversePosition hMpos hy hy'
    · exact (hjGap.not_ge (hs'.trans hm₁)).elim
    · linarith only [ha', hs, hiGap, hspan, hjGap]
    · exact (hjGap.not_ge (hs.trans hm₁')).elim
    · exact hlift S sSource suffixPosition hSpos hy hy'
  have hExteriorContact (k l : Fin q.segments) {s t : ℝ} (hs : s ∈ Set.Icc 0 1)
      (ht : t ∈ Set.Icc 0 1) (hw : q.eval k s ∉ B) (he : q.eval k s = q.eval l t)
      (hpos : q.position k s ≠ q.position l t) :
      ∃ (a b : Fin p.segments) (u v : ℝ), u ∈ Set.Icc 0 1 ∧ v ∈ Set.Icc 0 1 ∧
        p.eval a u = q.eval k s ∧ p.eval b v = q.eval l t ∧ p.position a u ≠ p.position b v ∧
        (s ∈ Set.Ioo 0 1 ↔ u ∈ Set.Ioo 0 1) ∧ (t ∈ Set.Ioo 0 1 ↔ v ∈ Set.Ioo 0 1) := by
    obtain ⟨a, u, hu, ha, hia, hLiftA⟩ := hExterior k hs hw
    obtain ⟨b, v, hv, hb, hib, hLiftB⟩ := hExterior l ht (he ▸ hw)
    refine ⟨a, b, u, v, hu, hv, ha, hb, ?_, hia, hib⟩
    intro heq
    exact hpos (hretained_unique hLiftA (heq.symm ▸ hLiftB))
  let rOffset := ((A.concat L).concat M.reverse).segments
  have hcontact (k : Fin q.segments) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
      (hw : q.eval k u ∈ B) :
      (∃ v ∈ Set.Icc (0 : ℝ) 1, q.eval k u = AffineMap.lineMap a c v ∧
        q.position k u = (A.segments : ℝ) + v) ∨
      (∃ v ∈ Set.Icc (0 : ℝ) 1, q.eval k u = AffineMap.lineMap b d v ∧
        q.position k u = (rOffset : ℝ) + v) := by
    rcases hparts k with ⟨l, hk, hp⟩ | ⟨hk, hp⟩ | ⟨l, hk, hp⟩ | ⟨hk, hp⟩ | ⟨l, hk, hp⟩ <;>
      specialize hp u
    · obtain ⟨v, hv, hv₀, he, _, hfinish, _⟩ := interval_closed_eval (Fin.zero_le i) hAt l hu
      have hw' : p.eval (eA l).val v ∈ B := (hp.trans he) ▸ hw
      by_cases hi : (eA l).val = i
      · have hcut : v = li := le_antisymm (by simpa only [hi, ↓reduceIte] using hv.2)
          ((hiBall v).mp (hi ▸ hw')).1
        refine Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩
        · rw [hp, he, hi, hcut, AffineMap.lineMap_apply_zero]
        · simpa only [position, hk, add_zero] using hfinish hi hcut
      · exact (hother _ _ hv₀ hi (((eA l).property.2.trans_lt hij).ne) hw').elim
    · exact Or.inl ⟨u, hu, hp, by simp only [position, hk]⟩
    · obtain ⟨v, hv, hv₀, he, hfirst, hfinish, _⟩ :=
        interval_closed_eval hij.le hMt l.rev (Set.Icc.one_sub_mem hu)
      have heval := hp.trans ((eval_reverse M l u).trans he)
      have hw' : p.eval (eM l.rev).val v ∈ B := heval ▸ hw
      have hpos := hshift M.reverse k l hk u
      rw [position_reverse] at hpos
      by_cases hi : (eM l.rev).val = i
      · have hcut : v = ui := le_antisymm ((hiBall v).mp (hi ▸ hw')).2
          (by simpa only [hi, ↓reduceIte] using hv.1)
        refine Or.inr ⟨0, ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩
        · rw [heval, hi, hcut, AffineMap.lineMap_apply_zero]
        · rw [hpos, hfirst hi hcut]
          simp [rOffset, Nat.cast_add, reverse]
      · by_cases hj : (eM l.rev).val = j
        · have hcut : v = lj := le_antisymm (by simpa only [hj, ↓reduceIte] using hv.2)
            ((hjBall v).mp (hj ▸ hw')).1
          refine Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, ?_, ?_⟩
          · rw [heval, hj, hcut, AffineMap.lineMap_apply_one]
          · rw [hpos, hfinish hj hcut]
            simp [Nat.cast_add, show L.segments = 1 from rfl]
        · exact (hother _ _ hv₀ hi hj hw').elim
    · exact Or.inr ⟨u, hu, hp, by simp only [position, rOffset, hk]⟩
    · obtain ⟨v, hv, hv₀, he, hfirst, _, _⟩ := interval_closed_eval (Fin.le_last j) hSt l hu
      have hw' : p.eval (eS l).val v ∈ B := (hp.trans he) ▸ hw
      by_cases hj : (eS l).val = j
      · have hcut : v = uj := le_antisymm ((hjBall v).mp (hj ▸ hw')).2
          (by simpa only [hj, ↓reduceIte] using hv.1)
        refine Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, ?_, ?_⟩
        · rw [hp, he, hj, hcut, AffineMap.lineMap_apply_one]
        · rw [hshift S k l hk u, hfirst hj hcut]
          simp [rOffset, Nat.cast_add, show R.segments = 1 from rfl]
      · exact (hother _ _ hv₀ (hij.trans_le (eS l).property.1).ne' hj hw').elim
  have hpositions (k l : Fin q.segments) {s t : ℝ} (hs : s ∈ Set.Icc 0 1)
      (ht : t ∈ Set.Icc 0 1) (hw : q.eval k s ∈ B) (he : q.eval k s = q.eval l t) :
      q.position k s = q.position l t := by
    rcases hcontact k hs hw with ⟨x, hx, hx₁, hx₂⟩ | ⟨x, hx, hx₁, hx₂⟩ <;>
      rcases hcontact l ht (he ▸ hw) with ⟨y, hy, hy₁, hy₂⟩ | ⟨y, hy, hy₁, hy₂⟩
    · have hxy := AffineMap.lineMap_injective ℝ (hport_ne hli' hlj' ha)
        (hx₁.symm.trans (he.trans hy₁))
      rw [hx₂, hy₂, hxy]
    · exact (Set.disjoint_left.mp hdisjoint
        (hx₁.symm ▸ lineMap_mem_segment ℝ _ _ hx)
        (he.symm ▸ hy₁.symm ▸ lineMap_mem_segment ℝ _ _ hy)).elim
    · exact (Set.disjoint_left.mp hdisjoint
        (he.symm ▸ hy₁.symm ▸ lineMap_mem_segment ℝ _ _ hy)
        (hx₁.symm ▸ lineMap_mem_segment ℝ _ _ hx)).elim
    · have hxy := AffineMap.lineMap_injective ℝ (hport_ne hui' huj' hb)
        (hx₁.symm.trans (he.trans hy₁))
      rw [hx₂, hy₂, hxy]
  have hExteriorVisit (k : Fin q.segments) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
      (hw : q.eval k u ∉ B) :
      ∃ (a : Fin p.segments) (v : ℝ), v ∈ Set.Icc 0 1 ∧ p.eval a v = q.eval k u ∧
        (u ∈ Set.Ioo 0 1 ↔ v ∈ Set.Ioo 0 1) := by
    obtain ⟨a, v, hv, he, hi, _⟩ := hExterior k hu hw
    exact ⟨a, v, hv, he, hi⟩
  have hPoints (hp : Function.Injective p.point) : Function.Injective q.point := by
    intro a b he
    obtain ⟨k, s, hs, hsb, hqa, hsa⟩ := exists_parameter_at_point q a
    obtain ⟨l, t, ht, htb, hqb, htbPos⟩ := exists_parameter_at_point q b
    have hqt := hqa.trans (he.trans hqb.symm)
    by_contra hab
    have hpos : q.position k s ≠ q.position l t := by
      rw [hsa, htbPos]
      exact fun h => hab (Fin.ext (by exact_mod_cast h))
    have hw : q.eval k s ∉ B := fun h => hpos (hpositions k l hs ht h hqt)
    obtain ⟨i, j, u, v, hu, hv, hi, hj, hne, hsU, htV⟩ :=
      hExteriorContact k l hs ht hw hqt hpos
    obtain ⟨a', hpa, huPos⟩ := exists_point_at_end_parameter i hu (fun h => hsb (hsU.mpr h))
    obtain ⟨b', hpb, hvPos⟩ := exists_point_at_end_parameter j hv (fun h => htb (htV.mpr h))
    have hab' := hp (hpa.symm.trans (hi.trans (hqt.trans (hj.symm.trans hpb))))
    apply hne
    rw [huPos, hvPos, hab']
  have hAvoid (hp : ∀ (a : Fin (p.segments + 1)) (k : Fin p.segments),
      p.point a ∉ openSegment ℝ (p.point k.castSucc) (p.point k.succ))
      (a : Fin (q.segments + 1)) (l : Fin q.segments) :
      q.point a ∉ openSegment ℝ (q.point l.castSucc) (q.point l.succ) := by
    intro he
    rw [openSegment_eq_image_lineMap] at he
    obtain ⟨t, ht, hqb⟩ := he
    obtain ⟨k, s, hs, hsb, hqa, hsa⟩ := exists_parameter_at_point q a
    have hqt : q.eval k s = q.eval l t := hqa.trans hqb.symm
    have hpos : q.position k s ≠ q.position l t := by
      rw [hsa]
      exact (position_ne_nat_of_mem_Ioo l ht a.val).symm
    have ht' := Set.Ioo_subset_Icc_self ht
    have hw : q.eval k s ∉ B := fun h => hpos (hpositions k l hs ht' h hqt)
    obtain ⟨i, j, u, v, hu, _, hi, hj, _, hsU, htV⟩ :=
      hExteriorContact k l hs ht' hw hqt hpos
    obtain ⟨a', hpa, _⟩ := exists_point_at_end_parameter i hu (fun h => hsb (hsU.mpr h))
    apply hp a' j
    rw [← hpa, hi, hqt, ← hj]
    exact lineMap_mem_openSegment ℝ _ _ (htV.mp ht)
  have hDisk : q.support ∩ B = N := by
    ext w
    constructor
    · rintro ⟨hw, hdisk⟩
      obtain ⟨k, u, hu, rfl⟩ := (q.mem_support_iff w).mp hw
      rcases hcontact k hu hdisk with ⟨v, hv, he, _⟩ | ⟨v, hv, he, _⟩
      · exact Or.inl (he.symm ▸ lineMap_mem_segment ℝ _ _ hv)
      · exact Or.inr (he.symm ▸ lineMap_mem_segment ℝ _ _ hv)
    · intro hw
      exact ⟨hq.symm ▸ Or.inr hw, hNew hw⟩
  have hNoCenter : z ∉ q.support := fun hz =>
    hcenter (hDisk ▸ ⟨hz, Metric.mem_closedBall_self (x := z) hρ.le⟩)
  refine ⟨q, hstart, hfinish, hNoCenter, ?_, ?_, ?_, hCross, hpositions, hExteriorContact, hnondeg,
    hExteriorVisit, hPoints, hAvoid, hexterior_open, li, ui, lj, uj,
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
