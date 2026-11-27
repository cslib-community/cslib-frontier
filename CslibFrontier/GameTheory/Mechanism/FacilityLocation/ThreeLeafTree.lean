/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.PhantomMedian
public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Tree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Anonymous 3-agent strategyproof facility location on 3-leaved metric trees

Symmetric path-distance (`FacilityLocation`) specialization after [SchummerVohra2007],
Exercise 10.5 (p. 265), building on [SchummerVohra2002], Theorem 1: this module does not prove the
ordinal tree-single-peaked preference characterization posed in Exercise 10.5 (which remains open
under #7789), and instead characterizes all deterministic, strategy-proof, surjective, anonymous
`3`-agent facility-location mechanisms under symmetric path-distance utilities on a `3`-leaved tree
metric graph (`Tripod W`, `W.graph.IsTree`).

A `Tripod W` decomposes `MetricGraph W` into three closed legs `interval center (leaf r)`
(`r : Fin 3`) meeting pairwise only at `center`, with `leaf r ≠ center`. Every anonymous,
strategy-proof, surjective `3`-agent facility-location mechanism on `MetricGraph W` is uniquely
determined by a `ThreeLeafScheme T` assigning to each leg `r` two threshold distances
`0 ≤ low r ≤ high r ≤ dist center (leaf r)` subject to the center-exclusivity condition
`r ≠ s → 0 < low r → high s = 0`. Equivalently, every such scheme falls into one of two families
(`ThreeLeafScheme.dichotomy`):

1. **Two-phantom single-leg rules** (`∃ r, 0 < low r`, forcing `low s = high s = 0` for `s ≠ r`):
   two phantom voters lie on leg `r` at distances `low r ≤ high r` from `center`.
2. **Three-leg-cap rules** (`∀ r, low r = 0`): each leg `r` has an independent majority cap
   `high r ∈ [0, dist center (leaf r)]`, where any two agents on leg `r` pull the outcome toward
   `leaf r` up to distance `high r` (and beyond `high r` unanimity of all three agents is needed).
   When all three caps `high 0, high 1, high 2` are positive (for example the pure 2-of-3 majority
   rule `high r = dist center (leaf r)`), the rule has three nonzero caps and cannot be realized
   by placing only two phantom voters in the tree.

## Main definitions

* `Cslib.GameTheory.FacilityLocation.Tripod`: a 3-leaved tree decomposition of `MetricGraph W`.
* `Cslib.GameTheory.FacilityLocation.ThreeLeafScheme`: the `(low, high)` leg-threshold
  parameterization of anonymous 3-agent facility-location rules on a `Tripod`.
* `Cslib.GameTheory.FacilityLocation.ThreeLeafScheme.toTreeEMVS`: the `TreeEMVS W (Fin 3)` induced
  by a `ThreeLeafScheme`.
* `Cslib.GameTheory.FacilityLocation.ThreeLeafScheme.eval`: evaluation map of a `ThreeLeafScheme`.

## Main results

* `Cslib.GameTheory.FacilityLocation.ThreeLeafScheme.dichotomy`: every `ThreeLeafScheme` is either
  a single-leg two-phantom scheme or a three-leg-cap scheme.
* `Cslib.GameTheory.FacilityLocation.ThreeLeafScheme.eval_isGroupStrategyProof`,
  `ThreeLeafScheme.eval_surjective`, `ThreeLeafScheme.eval_isAnonymous`: every `ThreeLeafScheme`
  defines a strongly group strategy-proof, surjective, anonymous 3-agent facility-location
  mechanism.
* `Cslib.GameTheory.FacilityLocation.isStrategyProof_surjective_anonymous_iff_threeLeafScheme`:
  symmetric path-distance (`FacilityLocation`) specialization after [SchummerVohra2007],
  Exercise 10.5 (p. 265), via [SchummerVohra2002], Theorem 1: on a 3-leaved metric tree,
  deterministic strategy-proof, surjective, anonymous 3-agent facility-location mechanisms coincide
  with `ThreeLeafScheme.eval`.

## References

* [J. Schummer and R. V. Vohra, *Strategy-proof Location on a Network*][SchummerVohra2002]
* [J. Schummer and R. V. Vohra, *Mechanism Design without Money*][SchummerVohra2007]
-/

public section

open SimpleGraph SimpleGraph.MetricGraph

namespace Cslib.GameTheory.FacilityLocation

/-- A **3-leaved tree** (tripod) decomposition of a metric graph `MetricGraph W`: a center
`center` and three leaves `leaf : Fin 3 → MetricGraph W` strictly distinct from `center` such that
the three closed legs `interval center (leaf r)` cover `MetricGraph W` and meet pairwise only at
`center` (after [SchummerVohra2007], Exercise 10.5, p. 265). -/
structure Tripod {V : Type*} (W : WeightedGraph V) [Finite V] where
  /-- The unique degree-3 junction (center) of the 3-leaved tree. -/
  center : MetricGraph W
  /-- The three leaves of the tree. -/
  leaf : Fin 3 → MetricGraph W
  /-- Every leaf is distinct from the center. -/
  leaf_ne_center : ∀ r, leaf r ≠ center
  /-- Every point of the tree lies on at least one leg `interval center (leaf r)`. -/
  cover : ∀ x : MetricGraph W, ∃ r : Fin 3, x ∈ interval center (leaf r)
  /-- Any two distinct legs intersect only at `center`. -/
  inter_eq : ∀ {r s : Fin 3}, r ≠ s →
    interval center (leaf r) ∩ interval center (leaf s) = {center}

/-- Symmetric path-distance parameterization of anonymous, strategy-proof, surjective `3`-agent
facility-location rules on a 3-leaved metric tree `T` (after [SchummerVohra2007], Exercise 10.5,
p. 265, and [SchummerVohra2002], Theorem 1; the ordinal tree-single-peaked preference domain of
Exercise 10.5 remains open under #7789). -/
structure ThreeLeafScheme {V : Type*} {W : WeightedGraph V} [Finite V] (T : Tripod W) where
  /-- Distance along leg `r` where the outward 1-agent winning threshold ends. -/
  low : Fin 3 → ℝ
  /-- Distance along leg `r` where the outward 2-agent winning threshold ends. -/
  high : Fin 3 → ℝ
  /-- `low r ≥ 0` on every leg. -/
  low_nonneg : ∀ r, 0 ≤ low r
  /-- `low r ≤ high r` on every leg. -/
  low_le_high : ∀ r, low r ≤ high r
  /-- `high r` does not exceed the length of leg `r`. -/
  high_le_dist : ∀ r, high r ≤ dist T.center (T.leaf r)
  /-- Exclusivity at the center: if `0 < low r`, then `high s = 0` on both other legs `s ≠ r`. -/
  exclusive_legs : ∀ {r s : Fin 3}, r ≠ s → 0 < low r → high s = 0

section TripodGeometry

variable {V : Type*} [Finite V] {W : WeightedGraph V} {T : Tripod W}

private lemma mem_inter_eq_center {r s : Fin 3} (hrs : r ≠ s) {x : MetricGraph W}
    (hr : x ∈ interval T.center (T.leaf r)) (hs : x ∈ interval T.center (T.leaf s)) :
    x = T.center :=
  Set.mem_singleton_iff.mp (T.inter_eq hrs ▸ ⟨hr, hs⟩)

private lemma leg_unique_of_ne_center {r s : Fin 3} {x : MetricGraph W} (hx : x ≠ T.center)
    (hr : x ∈ interval T.center (T.leaf r)) (hs : x ∈ interval T.center (T.leaf s)) :
    r = s := by
  exact by_contra fun hrs => hx (mem_inter_eq_center hrs hr hs)

private lemma center_mem_interval_of_ne_leg (hT : W.graph.IsTree) {r s : Fin 3} (hrs : r ≠ s)
    {x y : MetricGraph W}
    (hx : x ∈ interval T.center (T.leaf r)) (hy : y ∈ interval T.center (T.leaf s)) :
    T.center ∈ interval x y := by
  have hmr : treeMedian hT T.center x y ∈ interval T.center (T.leaf r) :=
    interval_subset_of_mem hT (left_mem_interval _ _) hx (treeMedian_mem_xy hT T.center x y)
  have hms : treeMedian hT T.center x y ∈ interval T.center (T.leaf s) :=
    interval_subset_of_mem hT (left_mem_interval _ _) hy
      (interval_comm y T.center ▸ treeMedian_mem_zx hT T.center x y)
  exact mem_inter_eq_center hrs hmr hms ▸ treeMedian_mem_yz hT T.center x y

private lemma mem_branch_center_leaf_iff (hT : W.graph.IsTree) (r : Fin 3) (x : MetricGraph W) :
    x ∈ branch T.center (T.leaf r) ↔ x ∈ interval T.center (T.leaf r) ∧ x ≠ T.center := by
  refine ⟨fun hx => ?_, fun ⟨hx, hxc⟩ hc => ?_⟩
  · obtain ⟨s, hs⟩ := T.cover x
    rcases eq_or_ne r s with rfl | hrs
    · exact ⟨hs, fun h => notMem_branch_self T.center (T.leaf r) (h ▸ hx)⟩
    · exact (hx (center_mem_interval_of_ne_leg hT hrs (right_mem_interval _ _) hs)).elim
  · rw [mem_interval_iff, _root_.dist_comm x (T.leaf r)] at hx
    rw [mem_interval_iff, _root_.dist_comm (T.leaf r) T.center] at hc
    linarith [dist_pos.mpr hxc.symm, dist_triangle (T.leaf r) T.center x]

private lemma mem_branch_outward_iff (hT : W.graph.IsTree) {r : Fin 3} {y : MetricGraph W}
    (hy : y ∈ interval T.center (T.leaf r)) (_hyl : y ≠ T.leaf r) (x : MetricGraph W) :
    x ∈ branch y (T.leaf r) ↔
      x ∈ interval T.center (T.leaf r) ∧ dist T.center y < dist T.center x := by
  refine ⟨fun hx => ?_, fun ⟨hx, hlt⟩ hy_lx => ?_⟩
  · obtain ⟨s, hs⟩ := T.cover x
    rcases eq_or_ne r s with rfl | hrs
    · refine ⟨hs, lt_of_not_ge fun hdx => hx ?_⟩
      have hx_cy := mem_interval_of_mem_interval_dist_le hT hs hy hdx
      rw [interval_comm, mem_interval_iff]
      rw [mem_interval_iff] at hx_cy hy hs
      linarith
    · have hc_lx := center_mem_interval_of_ne_leg hT hrs (right_mem_interval _ _) hs
      exact (hx (interval_subset_of_mem hT (left_mem_interval _ _) hc_lx
        (interval_comm T.center (T.leaf r) ▸ hy))).elim
  · have hy_cx := mem_interval_of_mem_interval_dist_le hT hy hx hlt.le
    rw [mem_interval_iff] at hy hx hy_cx
    rw [mem_interval_iff, _root_.dist_comm (T.leaf r) y, _root_.dist_comm (T.leaf r) x] at hy_lx
    linarith

private lemma mem_branch_inward_iff (hT : W.graph.IsTree) {r : Fin 3} {y : MetricGraph W}
    (hy : y ∈ interval T.center (T.leaf r)) (hyc : y ≠ T.center) (x : MetricGraph W) :
    x ∈ branch y T.center ↔
      x ≠ y ∧ ¬ (x ∈ interval T.center (T.leaf r) ∧ dist T.center y < dist T.center x) := by
  refine ⟨fun hx => ⟨fun h => notMem_branch_self y T.center (h ▸ hx), fun ⟨hxr, hlt⟩ =>
    hx (mem_interval_of_mem_interval_dist_le hT hy hxr hlt.le)⟩, fun ⟨hxy, hnot⟩ hy_cx => ?_⟩
  obtain ⟨s, hs⟩ := T.cover x
  rcases eq_or_ne r s with rfl | hrs
  · have hle : dist T.center x ≤ dist T.center y := le_of_not_gt fun hgt => hnot ⟨hs, hgt⟩
    rw [mem_interval_iff] at hy_cx
    exact hxy (eq_of_mem_interval_dist_eq hT hs hy
      (le_antisymm hle (by linarith [dist_nonneg (x := y) (y := x)])))
  · have hc_yx := center_mem_interval_of_ne_leg hT hrs hy hs
    rw [mem_interval_iff] at hy_cx
    rw [mem_interval_iff, _root_.dist_comm y T.center] at hc_yx
    linarith [dist_pos.mpr hyc.symm]

private lemma branch_eq_outward_or_inward (hT : W.graph.IsTree) {r : Fin 3} {y q : MetricGraph W}
    (hy : y ∈ interval T.center (T.leaf r)) (hyc : y ≠ T.center) (hqy : q ≠ y) :
    (y ≠ T.leaf r ∧ branch y q = branch y (T.leaf r)) ∨ branch y q = branch y T.center := by
  by_cases h : q ∈ interval T.center (T.leaf r) ∧ dist T.center y < dist T.center q
  · have hyl : y ≠ T.leaf r := fun e => by
      linarith [mem_interval_iff.mp h.1, dist_nonneg (x := q) (y := T.leaf r),
        congrArg (dist T.center) e, h.2]
    exact Or.inl ⟨hyl, branch_eq_of_mem hT ((mem_branch_outward_iff hT hy hyl q).mpr h)⟩
  · exact Or.inr (branch_eq_of_mem hT ((mem_branch_inward_iff hT hy hyc q).mpr ⟨hqy, h⟩))

private lemma branch_center_eq_leaf (hT : W.graph.IsTree) {q : MetricGraph W} (hqc : q ≠ T.center) :
    ∃ r : Fin 3, branch T.center q = branch T.center (T.leaf r) :=
  let ⟨r, hr⟩ := T.cover q
  ⟨r, branch_eq_of_mem hT ((mem_branch_center_leaf_iff hT r q).mpr ⟨hr, hqc⟩)⟩

private lemma branch_center_ne_of_ne (hT : W.graph.IsTree) {r s : Fin 3} (hrs : r ≠ s) :
    branch T.center (T.leaf r) ≠ branch T.center (T.leaf s) := fun heq =>
  T.leaf_ne_center r (mem_inter_eq_center hrs (right_mem_interval _ _)
    ((mem_branch_center_leaf_iff hT s (T.leaf r)).mp
      (heq ▸ mem_branch_self (T.leaf_ne_center r))).1)

private lemma branch_outward_ne_inward (hT : W.graph.IsTree) {r : Fin 3} {y : MetricGraph W}
    (hy : y ∈ interval T.center (T.leaf r)) (hyc : y ≠ T.center) (hyl : y ≠ T.leaf r) :
    branch y (T.leaf r) ≠ branch y T.center := fun heq => by
  have hnot := ((mem_branch_inward_iff hT hy hyc (T.leaf r)).mp (heq ▸ mem_branch_self hyl.symm)).2
  rw [mem_interval_iff] at hy
  exact hnot ⟨right_mem_interval _ _, by linarith [dist_pos.mpr hyl]⟩

private lemma exists_point_on_leg_dist (hT : W.graph.IsTree) (r : Fin 3) {d : ℝ}
    (hd0 : 0 ≤ d) (hd : d ≤ dist T.center (T.leaf r)) :
    ∃ p ∈ interval T.center (T.leaf r), dist T.center p = d := by
  obtain ⟨φ, hφ_iso, hφ0, _, hφ_range⟩ := exists_isometry_interval hT T.center (T.leaf r)
  let dPt : Set.Icc (0 : ℝ) (dist T.center (T.leaf r)) := ⟨d, hd0, hd⟩
  refine ⟨φ dPt, hφ_range ▸ Set.mem_range_self dPt, ?_⟩
  rw [← hφ0, hφ_iso.dist_eq, Subtype.dist_eq, Real.dist_eq]
  simpa only [zero_sub, abs_neg] using abs_of_nonneg hd0

end TripodGeometry

/-! ### `ThreeLeafScheme` to `TreeEMVS` -/

namespace ThreeLeafScheme

variable {V : Type*} [Finite V] {W : WeightedGraph V} {T : Tripod W}

/-- Outward winning predicate at distance `d` along leg `r` for coalition `S`. -/
private def outwardWin (P : ThreeLeafScheme T) (r : Fin 3) (d : ℝ) (S : Finset (Fin 3)) : Prop :=
  (d < P.low r ∧ 1 ≤ S.card) ∨ (d < P.high r ∧ 2 ≤ S.card) ∨ 3 ≤ S.card

/-- Inward winning predicate at distance `d` along leg `r` for coalition `S`. -/
private def inwardWin (P : ThreeLeafScheme T) (r : Fin 3) (d : ℝ) (S : Finset (Fin 3)) : Prop :=
  (P.high r < d ∧ 1 ≤ S.card) ∨ (P.low r < d ∧ 2 ≤ S.card) ∨ 3 ≤ S.card

/-- **Dichotomy** for `ThreeLeafScheme` (after [SchummerVohra2007], Exercise 10.5, p. 265): every
`ThreeLeafScheme` on a 3-leaved tree has either positive `low` on one leg `r` with zero `low` and
`high` on both other legs (single-leg two-phantom parameters) or `low = 0` on all three legs
(three-leg-cap parameters). -/
theorem dichotomy (P : ThreeLeafScheme T) :
    (∃ r : Fin 3, 0 < P.low r ∧ ∀ s : Fin 3, s ≠ r → P.low s = 0 ∧ P.high s = 0) ∨
      (∀ r : Fin 3, P.low r = 0) := by
  by_cases h : ∃ r : Fin 3, 0 < P.low r
  · obtain ⟨r, hr⟩ := h
    refine Or.inl ⟨r, hr, fun s hsr => ?_⟩
    have hhigh : P.high s = 0 := P.exclusive_legs hsr.symm hr
    exact ⟨le_antisymm ((P.low_le_high s).trans_eq hhigh) (P.low_nonneg s), hhigh⟩
  · push Not at h
    exact Or.inr fun r => le_antisymm (h r) (P.low_nonneg r)

private lemma high_nonneg (P : ThreeLeafScheme T) (r : Fin 3) : 0 ≤ P.high r :=
  (P.low_nonneg r).trans (P.low_le_high r)

private lemma low_eq_zero_of_high_pos (P : ThreeLeafScheme T) {r s : Fin 3} (hrs : r ≠ s)
    (hpos : 0 < P.high r) : P.low s = 0 :=
  le_antisymm (le_of_not_gt fun hls => hpos.ne' (P.exclusive_legs hrs.symm hls)) (P.low_nonneg s)

/-- The `TreeEMVS W (Fin 3)` induced by a `ThreeLeafScheme T`. -/
noncomputable def toTreeEMVS (hT : W.graph.IsTree) (P : ThreeLeafScheme T) :
    TreeEMVS W (Fin 3) where
  win y q S :=
    (∃ r : Fin 3, y ∈ interval T.center (T.leaf r) ∧ y ≠ T.leaf r ∧
      q ∈ branch y (T.leaf r) ∧ P.outwardWin r (dist T.center y) S) ∨
    (∃ r : Fin 3, y ∈ interval T.center (T.leaf r) ∧ y ≠ T.center ∧
      q ∈ branch y T.center ∧ P.inwardWin r (dist T.center y) S)
  branch_eq {y q₁ q₂} hq1 hq2 hbr := by
    funext S
    apply propext
    constructor
    · rintro (⟨r, hy, hyl, hq, hw⟩ | ⟨r, hy, hyc, hq, hw⟩)
      · left
        have h1 : branch y q₁ = branch y (T.leaf r) := branch_eq_of_mem hT hq
        exact ⟨r, hy, hyl, (hbr.symm.trans h1) ▸ mem_branch_self hq2, hw⟩
      · right
        have h1 : branch y q₁ = branch y T.center := branch_eq_of_mem hT hq
        exact ⟨r, hy, hyc, (hbr.symm.trans h1) ▸ mem_branch_self hq2, hw⟩
    · rintro (⟨r, hy, hyl, hq, hw⟩ | ⟨r, hy, hyc, hq, hw⟩)
      · left
        have h2 : branch y q₂ = branch y (T.leaf r) := branch_eq_of_mem hT hq
        exact ⟨r, hy, hyl, (hbr.trans h2) ▸ mem_branch_self hq1, hw⟩
      · right
        have h2 : branch y q₂ = branch y T.center := branch_eq_of_mem hT hq
        exact ⟨r, hy, hyc, (hbr.trans h2) ▸ mem_branch_self hq1, hw⟩
  empty_false _ := by
    rintro (⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩)
    · rcases h with ⟨_, h⟩ | ⟨_, h⟩ | h <;> simp at h
    · rcases h with ⟨_, h⟩ | ⟨_, h⟩ | h <;> simp at h
  univ_true {y q} hqy := by
    obtain ⟨r, hy⟩ := T.cover y
    by_cases hyc : y = T.center
    · subst hyc
      obtain ⟨s, hs⟩ := branch_center_eq_leaf hT hqy
      left
      refine ⟨s, left_mem_interval _ _, (T.leaf_ne_center s).symm,
        hs ▸ mem_branch_self hqy, Or.inr (Or.inr (by decide))⟩
    · rcases branch_eq_outward_or_inward hT hy hyc hqy with ⟨hyl, hbr⟩ | hbr
      · left
        exact ⟨r, hy, hyl, hbr ▸ mem_branch_self hqy, Or.inr (Or.inr (by decide))⟩
      · right
        exact ⟨r, hy, hyc, hbr ▸ mem_branch_self hqy, Or.inr (Or.inr (by decide))⟩
  mono _ hST := by
    have hcard := Finset.card_le_card hST
    rintro (⟨r, hy, hyl, hq, hw⟩ | ⟨r, hy, hyc, hq, hw⟩)
    · left
      refine ⟨r, hy, hyl, hq, ?_⟩
      rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
      · exact Or.inl ⟨h1, h2.trans hcard⟩
      · exact Or.inr (Or.inl ⟨h1, h2.trans hcard⟩)
      · exact Or.inr (Or.inr (h.trans hcard))
    · right
      refine ⟨r, hy, hyc, hq, ?_⟩
      rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
      · exact Or.inl ⟨h1, h2.trans hcard⟩
      · exact Or.inr (Or.inl ⟨h1, h2.trans hcard⟩)
      · exact Or.inr (Or.inr (h.trans hcard))
  nesting {y₁ q₁ y₂ q₂ S} hq1 hq2 hsub := by
    rintro (⟨r₂, hy₂, hyl₂, hq₂_mem, hw₂⟩ | ⟨r₂, hy₂, hyc₂, hq₂_mem, hw₂⟩)
    · have hbr2 : branch y₂ q₂ = branch y₂ (T.leaf r₂) := branch_eq_of_mem hT hq₂_mem
      rw [hbr2] at hsub
      have hlr2_mem : T.leaf r₂ ∈ branch y₁ q₁ := hsub (mem_branch_self hyl₂.symm)
      have hbr1 : branch y₁ q₁ = branch y₁ (T.leaf r₂) := (branch_eq_of_mem hT hlr2_mem).symm
      obtain ⟨r₁, hy₁⟩ := T.cover y₁
      by_cases hy1_eq : y₁ = T.center
      · subst hy1_eq
        left
        refine ⟨r₂, left_mem_interval _ _, (T.leaf_ne_center r₂).symm,
          hbr1 ▸ mem_branch_self hq1, ?_⟩
        rw [_root_.dist_self]
        have hd2 : 0 ≤ dist T.center y₂ := dist_nonneg
        rcases hw₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
        · exact Or.inl ⟨hd2.trans_lt h1, h2⟩
        · exact Or.inr (Or.inl ⟨hd2.trans_lt h1, h2⟩)
        · exact Or.inr (Or.inr h)
      · by_cases hr12 : r₁ = r₂
        · subst hr12
          have hyl1 : y₁ ≠ T.leaf r₁ := fun h =>
            notMem_branch_self y₁ q₁ (h ▸ hlr2_mem)
          have hdy : dist T.center y₁ ≤ dist T.center y₂ := by
            by_contra hgt
            have hlt : dist T.center y₂ < dist T.center y₁ := lt_of_not_ge hgt
            have hy1_in : y₁ ∈ branch y₂ (T.leaf r₁) :=
              (mem_branch_outward_iff hT hy₂ hyl₂ y₁).mpr ⟨hy₁, hlt⟩
            exact notMem_branch_self y₁ q₁ (hsub hy1_in)
          left
          refine ⟨r₁, hy₁, hyl1, hbr1 ▸ mem_branch_self hq1, ?_⟩
          rcases hw₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
          · exact Or.inl ⟨hdy.trans_lt h1, h2⟩
          · exact Or.inr (Or.inl ⟨hdy.trans_lt h1, h2⟩)
          · exact Or.inr (Or.inr h)
        · have hlr2_inward : T.leaf r₂ ∈ branch y₁ T.center := by
            refine (mem_branch_inward_iff hT hy₁ hy1_eq (T.leaf r₂)).mpr
              ⟨fun h => T.leaf_ne_center r₂
                (mem_inter_eq_center hr12 (h ▸ hy₁) (right_mem_interval _ _)), ?_⟩
            rintro ⟨hlr_on_r1, _⟩
            exact T.leaf_ne_center r₂ (mem_inter_eq_center hr12 hlr_on_r1 (right_mem_interval _ _))
          have hbr1_in : branch y₁ q₁ = branch y₁ T.center := by
            rw [hbr1]
            exact branch_eq_of_mem hT hlr2_inward
          have hd1_pos : 0 < dist T.center y₁ := dist_pos.mpr (Ne.symm hy1_eq)
          have hd2_nonneg : 0 ≤ dist T.center y₂ := dist_nonneg
          right
          refine ⟨r₁, hy₁, hy1_eq, hbr1_in ▸ mem_branch_self hq1, ?_⟩
          rcases hw₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
          · have hlow2 : 0 < P.low r₂ := hd2_nonneg.trans_lt h1
            have hhigh1 : P.high r₁ = 0 := P.exclusive_legs (Ne.symm hr12) hlow2
            exact Or.inl ⟨hhigh1 ▸ hd1_pos, h2⟩
          · have hhigh2 : 0 < P.high r₂ := hd2_nonneg.trans_lt h1
            have hlow1 : P.low r₁ = 0 := P.low_eq_zero_of_high_pos (Ne.symm hr12) hhigh2
            exact Or.inr (Or.inl ⟨hlow1 ▸ hd1_pos, h2⟩)
          · exact Or.inr (Or.inr h)
    · have hbr2 : branch y₂ q₂ = branch y₂ T.center := branch_eq_of_mem hT hq₂_mem
      rw [hbr2] at hsub
      have hc_mem : T.center ∈ branch y₁ q₁ := hsub (mem_branch_self hyc₂.symm)
      have hy1c : y₁ ≠ T.center := fun h => notMem_branch_self y₁ q₁ (h ▸ hc_mem)
      obtain ⟨r₁, hy₁⟩ := T.cover y₁
      have hbr1_in : branch y₁ q₁ = branch y₁ T.center := (branch_eq_of_mem hT hc_mem).symm
      by_cases hr12 : r₁ = r₂
      · subst hr12
        have hdy : dist T.center y₂ ≤ dist T.center y₁ := by
          by_contra hlt
          have hy1_in : y₁ ∈ branch y₂ T.center :=
            (mem_branch_inward_iff hT hy₂ hyc₂ y₁).mpr
              ⟨fun h => by subst h; exact hlt le_rfl,
                fun h => not_lt_of_ge (le_of_lt (lt_of_not_ge hlt)) h.2⟩
          exact notMem_branch_self y₁ q₁ (hsub hy1_in)
        right
        refine ⟨r₁, hy₁, hy1c, hbr1_in ▸ mem_branch_self hq1, ?_⟩
        rcases hw₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1.trans_le hdy, h2⟩
        · exact Or.inr (Or.inl ⟨h1.trans_le hdy, h2⟩)
        · exact Or.inr (Or.inr h)
      · exfalso
        have hy1_in : y₁ ∈ branch y₂ T.center :=
          (mem_branch_inward_iff hT hy₂ hyc₂ y₁).mpr
            ⟨fun h => hy1c (mem_inter_eq_center hr12 hy₁ (h ▸ hy₂)),
              fun h => hy1c (mem_inter_eq_center hr12 hy₁ h.1)⟩
        exact notMem_branch_self y₁ q₁ (hsub hy1_in)
  duality {y₁ y₂ S} h12 hnot := by
    have hcard_c : Sᶜ.card = 3 - S.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    have hSle : S.card ≤ 3 := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ S
    obtain ⟨r₁, hy₁⟩ := T.cover y₁
    obtain ⟨r₂, hy₂⟩ := T.cover y₂
    by_cases hy1c : y₁ = T.center
    · subst hy1c
      have hy2c : y₂ ≠ T.center := h12.symm
      have hy2_br : y₂ ∈ branch T.center (T.leaf r₂) :=
        (mem_branch_center_leaf_iff hT r₂ y₂).mpr ⟨hy₂, hy2c⟩
      have hnot_out : ¬ P.outwardWin r₂ 0 S := fun hw =>
        hnot (Or.inl ⟨r₂, left_mem_interval _ _, (T.leaf_ne_center r₂).symm, hy2_br,
          by simpa only [_root_.dist_self] using hw⟩)
      have hd2_pos : 0 < dist T.center y₂ := dist_pos.mpr hy2c.symm
      right
      refine ⟨r₂, hy₂, hy2c, mem_branch_self hy2c.symm, ?_⟩
      by_cases h0 : S.card = 0
      · exact Or.inr (Or.inr (by omega))
      · by_cases h1 : S.card = 1
        · have hle : P.low r₂ ≤ 0 := by
            by_contra hgt
            exact hnot_out (Or.inl ⟨lt_of_not_ge hgt, by omega⟩)
          exact Or.inr (Or.inl ⟨hle.trans_lt hd2_pos, by omega⟩)
        · by_cases h2 : S.card = 2
          · have hle : P.high r₂ ≤ 0 := by
              by_contra hgt
              exact hnot_out (Or.inr (Or.inl ⟨lt_of_not_ge hgt, by omega⟩))
            exact Or.inl ⟨hle.trans_lt hd2_pos, by omega⟩
          · exfalso; exact hnot_out (Or.inr (Or.inr (by omega)))
    · by_cases hy2c : y₂ = T.center
      · subst hy2c
        have hnot_in : ¬ P.inwardWin r₁ (dist T.center y₁) S := fun hw =>
          hnot (Or.inr ⟨r₁, hy₁, hy1c, mem_branch_self (Ne.symm hy1c), hw⟩)
        have hy1_br : y₁ ∈ branch T.center (T.leaf r₁) :=
          (mem_branch_center_leaf_iff hT r₁ y₁).mpr ⟨hy₁, hy1c⟩
        have hd1_pos : 0 < dist T.center y₁ := dist_pos.mpr (Ne.symm hy1c)
        left
        refine ⟨r₁, left_mem_interval _ _, (T.leaf_ne_center r₁).symm, hy1_br, ?_⟩
        rw [_root_.dist_self]
        by_cases h0 : S.card = 0
        · exact Or.inr (Or.inr (by omega))
        · by_cases h1 : S.card = 1
          · have hle : dist T.center y₁ ≤ P.high r₁ := by
              by_contra hgt
              exact hnot_in (Or.inl ⟨lt_of_not_ge hgt, by omega⟩)
            exact Or.inr (Or.inl ⟨hd1_pos.trans_le hle, by omega⟩)
          · by_cases h2 : S.card = 2
            · have hle : dist T.center y₁ ≤ P.low r₁ := by
                by_contra hgt
                exact hnot_in (Or.inr (Or.inl ⟨lt_of_not_ge hgt, by omega⟩))
              exact Or.inl ⟨hd1_pos.trans_le hle, by omega⟩
            · exfalso; exact hnot_in (Or.inr (Or.inr (by omega)))
      · by_cases hr12 : r₁ = r₂
        · subst hr12
          rcases lt_or_gt_of_ne (fun h => h12 (eq_of_mem_interval_dist_eq hT hy₁ hy₂ h)) with
            hlt | hgt
          · have hyl1 : y₁ ≠ T.leaf r₁ := by
              rintro rfl
              have hle : dist T.center y₂ ≤ dist T.center (T.leaf r₁) := by
                rw [mem_interval_iff] at hy₂; linarith [dist_nonneg (x := y₂) (y := T.leaf r₁)]
              linarith
            have hy2_out : y₂ ∈ branch y₁ (T.leaf r₁) :=
              (mem_branch_outward_iff hT hy₁ hyl1 y₂).mpr ⟨hy₂, hlt⟩
            have hy1_in : y₁ ∈ branch y₂ T.center :=
              (mem_branch_inward_iff hT hy₂ hy2c y₁).mpr ⟨h12, fun h => hlt.not_gt h.2⟩
            have hnot_out : ¬ P.outwardWin r₁ (dist T.center y₁) S := fun hw =>
              hnot (Or.inl ⟨r₁, hy₁, hyl1, hy2_out, hw⟩)
            right
            refine ⟨r₁, hy₂, hy2c, hy1_in, ?_⟩
            by_cases h0 : S.card = 0
            · exact Or.inr (Or.inr (by omega))
            · by_cases h1 : S.card = 1
              · have hle : P.low r₁ ≤ dist T.center y₁ := by
                  by_contra h; exact hnot_out (Or.inl ⟨lt_of_not_ge h, by omega⟩)
                exact Or.inr (Or.inl ⟨hle.trans_lt hlt, by omega⟩)
              · by_cases h2 : S.card = 2
                · have hle : P.high r₁ ≤ dist T.center y₁ := by
                    by_contra h; exact hnot_out (Or.inr (Or.inl ⟨lt_of_not_ge h, by omega⟩))
                  exact Or.inl ⟨hle.trans_lt hlt, by omega⟩
                · exfalso; exact hnot_out (Or.inr (Or.inr (by omega)))
          · have hyl2 : y₂ ≠ T.leaf r₁ := by
              rintro rfl
              have hle : dist T.center y₁ ≤ dist T.center (T.leaf r₁) := by
                rw [mem_interval_iff] at hy₁; linarith [dist_nonneg (x := y₁) (y := T.leaf r₁)]
              linarith
            have hy1_out : y₁ ∈ branch y₂ (T.leaf r₁) :=
              (mem_branch_outward_iff hT hy₂ hyl2 y₁).mpr ⟨hy₁, hgt⟩
            have hy2_in : y₂ ∈ branch y₁ T.center :=
              (mem_branch_inward_iff hT hy₁ hy1c y₂).mpr ⟨h12.symm, fun h => hgt.not_gt h.2⟩
            have hnot_in : ¬ P.inwardWin r₁ (dist T.center y₁) S := fun hw =>
              hnot (Or.inr ⟨r₁, hy₁, hy1c, hy2_in, hw⟩)
            left
            refine ⟨r₁, hy₂, hyl2, hy1_out, ?_⟩
            by_cases h0 : S.card = 0
            · exact Or.inr (Or.inr (by omega))
            · by_cases h1 : S.card = 1
              · have hle : dist T.center y₁ ≤ P.high r₁ := by
                  by_contra h; exact hnot_in (Or.inl ⟨lt_of_not_ge h, by omega⟩)
                exact Or.inr (Or.inl ⟨hgt.trans_le hle, by omega⟩)
              · by_cases h2 : S.card = 2
                · have hle : dist T.center y₁ ≤ P.low r₁ := by
                    by_contra h; exact hnot_in (Or.inr (Or.inl ⟨lt_of_not_ge h, by omega⟩))
                  exact Or.inl ⟨hgt.trans_le hle, by omega⟩
                · exfalso; exact hnot_in (Or.inr (Or.inr (by omega)))
        · have hy2_in : y₂ ∈ branch y₁ T.center :=
            (mem_branch_inward_iff hT hy₁ hy1c y₂).mpr
              ⟨h12.symm, fun h => hy2c (mem_inter_eq_center hr12 h.1 hy₂)⟩
          have hy1_in : y₁ ∈ branch y₂ T.center :=
            (mem_branch_inward_iff hT hy₂ hy2c y₁).mpr
              ⟨h12, fun h => hy1c (mem_inter_eq_center hr12 hy₁ h.1)⟩
          have hnot_in : ¬ P.inwardWin r₁ (dist T.center y₁) S := fun hw =>
            hnot (Or.inr ⟨r₁, hy₁, hy1c, hy2_in, hw⟩)
          have hd1_pos : 0 < dist T.center y₁ := dist_pos.mpr (Ne.symm hy1c)
          have hd2_pos : 0 < dist T.center y₂ := dist_pos.mpr (Ne.symm hy2c)
          right
          refine ⟨r₂, hy₂, hy2c, hy1_in, ?_⟩
          by_cases h0 : S.card = 0
          · exact Or.inr (Or.inr (by omega))
          · by_cases h1 : S.card = 1
            · have hle : dist T.center y₁ ≤ P.high r₁ := by
                by_contra h; exact hnot_in (Or.inl ⟨lt_of_not_ge h, by omega⟩)
              have hlow2 : P.low r₂ = 0 := P.low_eq_zero_of_high_pos hr12 (hd1_pos.trans_le hle)
              exact Or.inr (Or.inl ⟨hlow2 ▸ hd2_pos, by omega⟩)
            · by_cases h2 : S.card = 2
              · have hle : dist T.center y₁ ≤ P.low r₁ := by
                  by_contra h; exact hnot_in (Or.inr (Or.inl ⟨lt_of_not_ge h, by omega⟩))
                have hhigh2 : P.high r₂ = 0 := P.exclusive_legs hr12 (hd1_pos.trans_le hle)
                exact Or.inl ⟨hhigh2 ▸ hd2_pos, by omega⟩
              · exfalso; exact hnot_in (Or.inr (Or.inr (by omega)))
  exclusive {y q₁ q₂ S} hq1 hq2 hbr := by
    have hcard_c : Sᶜ.card = 3 - S.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    have hSle : S.card ≤ 3 := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ S
    rintro ⟨hw1, hw2⟩
    rcases hw1 with ⟨r₁, hy₁, hyl₁, hq1_m, h1⟩ | ⟨r₁, hy₁, hyc₁, hq1_m, h1⟩ <;>
    rcases hw2 with ⟨r₂, hy₂, hyl₂, hq2_m, h2⟩ | ⟨r₂, hy₂, hyc₂, hq2_m, h2⟩
    · have hbr1 : branch y q₁ = branch y (T.leaf r₁) := branch_eq_of_mem hT hq1_m
      have hbr2 : branch y q₂ = branch y (T.leaf r₂) := branch_eq_of_mem hT hq2_m
      have hr12 : r₁ ≠ r₂ := fun h => hbr (by rw [hbr1, hbr2, h])
      have hyc : y = T.center := mem_inter_eq_center hr12 hy₁ hy₂
      subst hyc
      rw [_root_.dist_self] at h1 h2
      rcases h1 with ⟨hl1, hc1⟩ | ⟨hh1, hc1⟩ | hc1 <;>
      rcases h2 with ⟨hl2, hc2⟩ | ⟨hh2, hc2⟩ | hc2
      · linarith [P.exclusive_legs hr12 hl1, P.low_le_high r₂]
      · linarith [P.exclusive_legs hr12 hl1]
      · omega
      · linarith [P.exclusive_legs hr12.symm hl2]
      · omega
      · omega
      · omega
      · omega
      · omega
    · have hr12 : r₁ = r₂ := leg_unique_of_ne_center hyc₂ hy₁ hy₂
      subst hr12
      rcases h1 with ⟨hl1, hc1⟩ | ⟨hh1, hc1⟩ | hc1 <;>
      rcases h2 with ⟨hh2, hc2⟩ | ⟨hl2, hc2⟩ | hc2 <;>
        first | omega | linarith [P.low_le_high r₁]
    · have hr12 : r₁ = r₂ := leg_unique_of_ne_center hyc₁ hy₁ hy₂
      subst hr12
      rcases h1 with ⟨hh1, hc1⟩ | ⟨hl1, hc1⟩ | hc1 <;>
      rcases h2 with ⟨hl2, hc2⟩ | ⟨hh2, hc2⟩ | hc2 <;>
        first | omega | linarith [P.low_le_high r₁]
    · have hbr1 : branch y q₁ = branch y T.center := branch_eq_of_mem hT hq1_m
      have hbr2 : branch y q₂ = branch y T.center := branch_eq_of_mem hT hq2_m
      exact hbr (hbr1.trans hbr2.symm)
  open_interior {y q S} hqy hw := by
    classical
    rcases hw with ⟨r, hy, hyl, hq_m, h⟩ | ⟨r, hy, hyc, hq_m, h⟩
    · have hq_info := (mem_branch_outward_iff hT hy hyl q).mp hq_m
      have hdyq : dist T.center y < dist T.center q := hq_info.2
      have hd_le_l : dist T.center q ≤ dist T.center (T.leaf r) := by
        have hm := hq_info.1
        rw [mem_interval_iff] at hm
        linarith [dist_nonneg (x := q) (y := T.leaf r)]
      have htarget : ∃ t : ℝ, dist T.center y < t ∧ t < dist T.center q ∧
          P.outwardWin r t S := by
        rcases h with ⟨hl, hc⟩ | ⟨hh, hc⟩ | hc
        · refine ⟨(dist T.center y + min (dist T.center q) (P.low r)) / 2, ?_, ?_,
            Or.inl ⟨?_, hc⟩⟩
          · linarith [lt_min hdyq hl]
          · linarith [min_le_left (dist T.center q) (P.low r), lt_min hdyq hl]
          · linarith [min_le_right (dist T.center q) (P.low r), lt_min hdyq hl]
        · refine ⟨(dist T.center y + min (dist T.center q) (P.high r)) / 2, ?_, ?_,
            Or.inr (Or.inl ⟨?_, hc⟩)⟩
          · linarith [lt_min hdyq hh]
          · linarith [min_le_left (dist T.center q) (P.high r), lt_min hdyq hh]
          · linarith [min_le_right (dist T.center q) (P.high r), lt_min hdyq hh]
        · exact ⟨(dist T.center y + dist T.center q) / 2, by linarith, by linarith,
            Or.inr (Or.inr hc)⟩
      obtain ⟨t, hyt, htq, hwt⟩ := htarget
      obtain ⟨p, hp_leg, hdp⟩ := exists_point_on_leg_dist hT r (dist_nonneg.trans hyt.le)
        (htq.le.trans hd_le_l)
      have hpy : p ≠ y := fun heq => by rw [heq] at hdp; linarith
      have hpq : p ≠ q := fun heq => by rw [heq] at hdp; linarith
      have hpl : p ≠ T.leaf r := fun heq => by rw [heq] at hdp; linarith
      have hp_int : p ∈ interval y q := by
        rw [mem_interval_iff, interval_dist_eq_abs hT hy hp_leg,
          interval_dist_eq_abs hT hp_leg hq_info.1, interval_dist_eq_abs hT hy hq_info.1, hdp]
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        ring
      have hq_br : q ∈ branch p (T.leaf r) :=
        (mem_branch_outward_iff hT hp_leg hpl q).mpr ⟨hq_info.1, hdp ▸ htq⟩
      exact ⟨p, hp_int, hpy, hpq, Or.inl ⟨r, hp_leg, hpl, hq_br, hdp ▸ hwt⟩⟩
    · have hdy_pos : 0 < dist T.center y := dist_pos.mpr (Ne.symm hyc)
      have hq_info := (mem_branch_inward_iff hT hy hyc q).mp hq_m
      let d₀ : ℝ := if q ∈ interval T.center (T.leaf r) then dist T.center q else 0
      have hd0_lt : d₀ < dist T.center y := by
        dsimp only [d₀]
        split_ifs with hqr
        · by_contra hge
          have hle : dist T.center y ≤ dist T.center q := le_of_not_gt hge
          rcases hle.eq_or_lt with heq | hlt
          · exact hq_info.1 (eq_of_mem_interval_dist_eq hT hqr hy heq.symm)
          · exact hq_info.2 ⟨hqr, hlt⟩
        · exact hdy_pos
      have hd0_nonneg : 0 ≤ d₀ := by
        dsimp only [d₀]
        split_ifs
        · exact dist_nonneg
        · exact le_rfl
      have htarget : ∃ t : ℝ, d₀ < t ∧ t < dist T.center y ∧ P.inwardWin r t S := by
        rcases h with ⟨hh, hc⟩ | ⟨hl, hc⟩ | hc
        · refine ⟨(max d₀ (P.high r) + dist T.center y) / 2, ?_, ?_, Or.inl ⟨?_, hc⟩⟩
          · linarith [le_max_left d₀ (P.high r), max_lt hd0_lt hh]
          · linarith [max_lt hd0_lt hh]
          · linarith [le_max_right d₀ (P.high r), max_lt hd0_lt hh]
        · refine ⟨(max d₀ (P.low r) + dist T.center y) / 2, ?_, ?_, Or.inr (Or.inl ⟨?_, hc⟩)⟩
          · linarith [le_max_left d₀ (P.low r), max_lt hd0_lt hl]
          · linarith [max_lt hd0_lt hl]
          · linarith [le_max_right d₀ (P.low r), max_lt hd0_lt hl]
        · exact ⟨(d₀ + dist T.center y) / 2, by linarith, by linarith, Or.inr (Or.inr hc)⟩
      obtain ⟨t, hd0t, hty, hwt⟩ := htarget
      have hy_le : dist T.center y ≤ dist T.center (T.leaf r) := by
        rw [mem_interval_iff] at hy; linarith [dist_nonneg (x := y) (y := T.leaf r)]
      obtain ⟨p, hp_leg, hdp⟩ := exists_point_on_leg_dist hT r (hd0_nonneg.trans hd0t.le)
        (hty.le.trans hy_le)
      have hpy : p ≠ y := fun heq => by rw [heq] at hdp; linarith
      have hpc : p ≠ T.center := fun heq => by rw [heq, _root_.dist_self] at hdp; linarith
      have hpq : p ≠ q := by
        rintro rfl
        have hqr : p ∈ interval T.center (T.leaf r) := hp_leg
        simp only [d₀, hqr, ↓reduceIte] at hd0t
        linarith
      have hp_int : p ∈ interval y q := by
        by_cases hqr : q ∈ interval T.center (T.leaf r)
        · simp only [d₀, hqr, ↓reduceIte] at hd0t
          rw [mem_interval_iff, interval_dist_eq_abs hT hy hp_leg,
            interval_dist_eq_abs hT hp_leg hqr, interval_dist_eq_abs hT hy hqr, hdp]
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          ring
        · obtain ⟨s, hs⟩ := T.cover q
          have hrs : r ≠ s := fun h => hqr (h ▸ hs)
          have hc_yq : T.center ∈ interval y q := center_mem_interval_of_ne_leg hT hrs hy hs
          have hp_yc : p ∈ interval y T.center := by
            rw [interval_comm]
            exact mem_interval_of_mem_interval_dist_le hT hp_leg hy (hdp ▸ hty.le)
          exact interval_subset_of_mem hT (left_mem_interval _ _) hc_yq hp_yc
      have hq_br : q ∈ branch p T.center := by
        refine (mem_branch_inward_iff hT hp_leg hpc q).mpr ⟨hpq.symm, ?_⟩
        rintro ⟨hqr, hlt⟩
        simp only [d₀, hqr, ↓reduceIte] at hd0t
        linarith
      exact ⟨p, hp_int, hpy, hpq, Or.inr ⟨r, hp_leg, hpc, hq_br, hdp ▸ hwt⟩⟩

/-- Evaluates a `ThreeLeafScheme` via its induced `TreeEMVS`. -/
noncomputable def eval [Nonempty V] (hT : W.graph.IsTree) (P : ThreeLeafScheme T)
    (x : Fin 3 → MetricGraph W) : MetricGraph W :=
  (P.toTreeEMVS hT).eval hT x

theorem eval_isGroupStrategyProof [Nonempty V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) (P : ThreeLeafScheme T) :
    (Mechanism.deterministic (P.eval hT)).IsGroupStrategyProof :=
  (P.toTreeEMVS hT).eval_isGroupStrategyProof hT

theorem eval_isStrategyProof [Nonempty V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) (P : ThreeLeafScheme T) :
    (Mechanism.deterministic (P.eval hT)).IsStrategyProof :=
  (P.eval_isGroupStrategyProof hT).isStrategyProof

theorem eval_surjective [Nonempty V] (hT : W.graph.IsTree) (P : ThreeLeafScheme T) :
    Function.Surjective (P.eval hT) :=
  (P.toTreeEMVS hT).eval_surjective hT

theorem eval_isAnonymous [Nonempty V] (hT : W.graph.IsTree) (P : ThreeLeafScheme T) :
    IsAnonymous (P.eval hT) := by
  intro σ x
  rw [eval, eval]
  refine ((P.toTreeEMVS hT).eval_eq_iff hT (x ∘ σ) ((P.toTreeEMVS hT).eval hT x)).mpr
    fun q hq S hS hw => ?_
  have hS' (i : Fin 3) :
      i ∈ S.map σ.toEmbedding ↔ x i ∈ branch ((P.toTreeEMVS hT).eval hT x) q := by
    simp only [Finset.mem_map, Equiv.coe_toEmbedding]
    exact ⟨fun ⟨j, hj, h⟩ => h ▸ (hS j).mp hj, fun hi =>
      ⟨σ.symm i, (hS (σ.symm i)).mpr (by simpa using hi), σ.apply_symm_apply i⟩⟩
  refine (((P.toTreeEMVS hT).eval_eq_iff hT x ((P.toTreeEMVS hT).eval hT x)).mp rfl)
    q hq (S.map σ.toEmbedding) hS' ?_
  rcases hw with ⟨r, hy, hyl, hqm, h⟩ | ⟨r, hy, hyc, hqm, h⟩
  · exact Or.inl ⟨r, hy, hyl, hqm, by simpa only [outwardWin, Finset.card_map] using h⟩
  · exact Or.inr ⟨r, hy, hyc, hqm, by simpa only [inwardWin, Finset.card_map] using h⟩

end ThreeLeafScheme

/-! ### Symmetric path-distance characterization on 3-leaved metric trees -/

section Characterization

variable {V : Type*} [Finite V] {W : WeightedGraph V} {T : Tripod W}

private lemma eval_twoVal_mem_branch_iff [Nonempty V] (hT : W.graph.IsTree)
    (E : TreeEMVS W (Fin 3)) {y q : MetricGraph W} (hqy : q ≠ y) (S : Finset (Fin 3)) :
    E.eval hT (fun i => if i ∈ S then q else y) ∈ branch y q ↔ E.win y q S := by
  let x : Fin 3 → MetricGraph W := fun i => if i ∈ S then q else y
  have hx_iff (i : Fin 3) : i ∈ S ↔ x i ∈ branch y q := by
    by_cases hi : i ∈ S <;> simp [x, hi, mem_branch_self hqy, notMem_branch_self]
  refine ⟨fun hmem => by_contra fun hnot => ?_, fun hw => by_contra fun hnot => ?_⟩
  · have heq : E.eval hT x = y := (E.eval_eq_iff hT x y).mpr fun q' hq' T' hT' hw' => by
      by_cases hbr : branch y q' = branch y q
      · exact hnot (E.branch_eq hq' hqy hbr ▸
          Finset.ext (fun i => (hT' i).trans (hbr ▸ (hx_iff i).symm)) ▸ hw')
      · refine E.empty_false hq' (Finset.eq_empty_of_forall_notMem (fun i hi => ?_) ▸ hw')
        have hx_in := (hT' i).mp hi
        by_cases hiS : i ∈ S <;> simp only [x, hiS, ↓reduceIte] at hx_in
        · exact Set.disjoint_left.mp (branch_disjoint_of_ne hT hbr) hx_in (mem_branch_self hqy)
        · exact notMem_branch_self y q' hx_in
    exact notMem_branch_self y q (Eq.mp (congrArg (· ∈ branch y q) heq) hmem)
  · set z := E.eval hT x
    have hEq := (E.eval_eq_iff hT x z).mp rfl
    have hzy : z ≠ y := fun h => (h ▸ hEq) q hqy S hx_iff hw
    have hy_qz : y ∈ interval q z := Classical.not_not.mp hnot
    have hq_in : q ∈ branch z y := fun hz_yq => by
      rw [mem_interval_iff, _root_.dist_comm q y, _root_.dist_comm q z] at hy_qz
      linarith [mem_interval_iff.mp hz_yq, dist_pos.mpr hzy.symm]
    refine hEq y hzy.symm Finset.univ (fun i => ?_) (E.univ_true hzy.symm)
    by_cases hi : i ∈ S <;> simp [x, hi, hq_in, mem_branch_self hzy.symm]

private lemma win_congr_card_of_isAnonymous [Nonempty V] (hT : W.graph.IsTree)
    (E : TreeEMVS W (Fin 3)) (hanon : IsAnonymous (E.eval hT))
    {y q : MetricGraph W} (hqy : q ≠ y) {S₁ S₂ : Finset (Fin 3)} (hcard : S₁.card = S₂.card) :
    E.win y q S₁ ↔ E.win y q S₂ := by
  rw [← eval_twoVal_mem_branch_iff hT E hqy S₁, ← eval_twoVal_mem_branch_iff hT E hqy S₂,
    hanon.apply_ite_eq_of_card_eq hcard]

/-- Symmetric path-distance (`FacilityLocation`) specialization after [SchummerVohra2007],
Exercise 10.5 (p. 265), not the full ordinal tree-single-peaked characterization of that exercise
(which remains open under #7789): building on [SchummerVohra2002], Theorem 1
(`isStrategyProof_and_surjective_iff_exists_treeEMVS`), on a 3-leaved tree metric graph `T`
(`W.graph.IsTree`), a deterministic `3`-agent facility-location mechanism under symmetric
path-distance utilities is strategy-proof, surjective, and anonymous if and only if it is the
evaluation map of a `ThreeLeafScheme T`. -/
theorem isStrategyProof_surjective_anonymous_iff_threeLeafScheme [Nonempty V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hT : W.graph.IsTree) (T : Tripod W) (f : (Fin 3 → MetricGraph W) → MetricGraph W) :
    ((Mechanism.deterministic f).IsStrategyProof ∧ Function.Surjective f ∧ IsAnonymous f) ↔
      ∃ P : ThreeLeafScheme T, f = P.eval hT := by
  refine ⟨?_, fun ⟨P, hP⟩ => hP ▸ ⟨P.eval_isStrategyProof hT, P.eval_surjective hT,
    P.eval_isAnonymous hT⟩⟩
  rintro ⟨hf_sp, hf_onto, hf_anon⟩
  obtain ⟨E, rfl⟩ :=
    (isStrategyProof_and_surjective_iff_exists_treeEMVS hT f).mp ⟨hf_sp, hf_onto⟩
  let thrSet (S : Finset (Fin 3)) (r : Fin 3) : Set ℝ :=
    {0} ∪ {d | ∃ y ∈ interval T.center (T.leaf r),
      y ≠ T.leaf r ∧ dist T.center y = d ∧ E.win y (T.leaf r) S}
  have hleg_le {r : Fin 3} {y : MetricGraph W} (hy : y ∈ interval T.center (T.leaf r)) :
      dist T.center y ≤ dist T.center (T.leaf r) := by
    linarith [mem_interval_iff.mp hy, dist_nonneg (x := y) (y := T.leaf r)]
  have hthr_bdd (S : Finset (Fin 3)) (r : Fin 3) : BddAbove (thrSet S r) :=
    ⟨dist T.center (T.leaf r), fun _ h => h.elim (fun e => e ▸ dist_nonneg)
      fun ⟨_, hy, _, e, _⟩ => e ▸ hleg_le hy⟩
  have hthr_ne (S : Finset (Fin 3)) (r : Fin 3) : (thrSet S r).Nonempty := ⟨0, Or.inl rfl⟩
  let low (r : Fin 3) : ℝ := sSup (thrSet {0} r)
  let high (r : Fin 3) : ℝ := sSup (thrSet {0, 1} r)
  have hthr_iff (S : Finset (Fin 3)) (r : Fin 3) {y : MetricGraph W}
      (hy : y ∈ interval T.center (T.leaf r)) (hyl : y ≠ T.leaf r) :
      E.win y (T.leaf r) S ↔ dist T.center y < sSup (thrSet S r) := by
    refine ⟨fun hw => ?_, fun hlt => ?_⟩
    · obtain ⟨p, hp_int, hpy, hpl, hwp⟩ := E.open_interior hyl.symm hw
      have hp_leg : p ∈ interval T.center (T.leaf r) :=
        interval_subset_of_mem hT hy (right_mem_interval _ _) hp_int
      have hlt : dist T.center y < dist T.center p := by
        linarith [mem_interval_iff.mp hy, mem_interval_iff.mp hp_int,
          mem_interval_iff.mp hp_leg, dist_pos.mpr hpy.symm]
      exact hlt.trans_le (le_csSup (hthr_bdd S r) (Or.inr ⟨p, hp_leg, hpl, rfl, hwp⟩))
    · obtain ⟨d, rfl | ⟨p, hp_leg, hpl, rfl, hwp⟩, hyd⟩ :=
        (lt_csSup_iff (hthr_bdd S r) (hthr_ne S r)).mp hlt
      · linarith [dist_nonneg (x := T.center) (y := y)]
      · refine E.nesting hyl.symm hpl.symm (fun x hx => ?_) hwp
        obtain ⟨hxr, hlt'⟩ := (mem_branch_outward_iff hT hp_leg hpl x).mp hx
        exact (mem_branch_outward_iff hT hy hyl x).mpr ⟨hxr, hyd.trans hlt'⟩
  have hlow_iff (r : Fin 3) {y : MetricGraph W} := hthr_iff {0} r (y := y)
  have hhigh_iff (r : Fin 3) {y : MetricGraph W} := hthr_iff {0, 1} r (y := y)
  let P : ThreeLeafScheme T :=
    { low := low
      high := high
      low_nonneg := fun r => le_csSup (hthr_bdd {0} r) (Or.inl rfl)
      low_le_high := fun r => csSup_le (hthr_ne {0} r) fun _ hd =>
        le_csSup (hthr_bdd {0, 1} r) (hd.imp id fun ⟨y, hy, hyl, e, hw⟩ =>
          ⟨y, hy, hyl, e, E.mono hyl.symm (by decide) hw⟩)
      high_le_dist := fun r => csSup_le (hthr_ne {0, 1} r) fun _ hd =>
        hd.elim (fun e => e ▸ dist_nonneg) fun ⟨_, hy, _, e, _⟩ => e ▸ hleg_le hy
      exclusive_legs := fun {r s} hrs hlr => by_contra fun hne => by
        have hhs : 0 < high s :=
          lt_of_le_of_ne (le_csSup (hthr_bdd {0, 1} s) (Or.inl rfl)) (Ne.symm hne)
        have hw1 : E.win T.center (T.leaf r) {0} :=
          (hlow_iff r (left_mem_interval _ _) (T.leaf_ne_center r).symm).mpr
            (by simpa only [_root_.dist_self] using hlr)
        have hw2 : E.win T.center (T.leaf s) ({0}ᶜ : Finset (Fin 3)) :=
          (win_congr_card_of_isAnonymous hT E hf_anon (T.leaf_ne_center s) (by decide)).mp
            ((hhigh_iff s (left_mem_interval _ _) (T.leaf_ne_center s).symm).mpr
              (by simpa only [_root_.dist_self] using hhs))
        exact E.exclusive (T.leaf_ne_center r) (T.leaf_ne_center s)
          (branch_center_ne_of_ne hT hrs) ⟨hw1, hw2⟩ }
  have hin_iff (S S' : Finset (Fin 3)) (thr : Fin 3 → ℝ)
      (hcard : Sᶜ.card = S'.card) (hthr0 : ∀ r, 0 ≤ thr r)
      (hout_iff : ∀ r {y : MetricGraph W}, y ∈ interval T.center (T.leaf r) → y ≠ T.leaf r →
        (E.win y (T.leaf r) S' ↔ dist T.center y < thr r))
      (r : Fin 3) {y : MetricGraph W} (hy : y ∈ interval T.center (T.leaf r))
      (hyc : y ≠ T.center) :
      E.win y T.center S ↔ thr r < dist T.center y := by
    refine ⟨fun hw => ?_, fun hlt => ?_⟩
    · obtain ⟨p, hp_int, hpy, hpc, hwp⟩ := E.open_interior hyc.symm hw
      rw [interval_comm] at hp_int
      have hp_leg := interval_subset_of_mem hT (left_mem_interval _ _) hy hp_int
      have hdp_lt : dist T.center p < dist T.center y := by
        linarith [mem_interval_iff.mp hp_int, dist_pos.mpr hpy]
      have hpl : p ≠ T.leaf r := fun h => hdp_lt.not_ge (h ▸ hleg_le hy)
      have hle : thr r ≤ dist T.center p := le_of_not_gt fun hlt =>
        E.exclusive hpc.symm hpl.symm (branch_outward_ne_inward hT hp_leg hpc hpl).symm
          ⟨hwp, (win_congr_card_of_isAnonymous hT E hf_anon hpl.symm hcard.symm).mp
            ((hout_iff r hp_leg hpl).mpr hlt)⟩
      exact hle.trans_lt hdp_lt
    · obtain ⟨p, hp_leg, hdp⟩ :=
        exists_point_on_leg_dist (T := T) (d := (thr r + dist T.center y) / 2) hT r
          (by linarith [hthr0 r])
          (by linarith [hleg_le hy])
      have hpy : p ≠ y := fun h => by linarith [congrArg (dist T.center) h]
      have hpl : p ≠ T.leaf r := fun h => by linarith [congrArg (dist T.center) h, hleg_le hy]
      have hbr_py : branch p y = branch p (T.leaf r) :=
        branch_eq_of_mem hT ((mem_branch_outward_iff hT hp_leg hpl y).mpr ⟨hy, by linarith⟩)
      have hnot_py : ¬ E.win p y Sᶜ := fun hw => by
        rw [E.branch_eq hpy.symm hpl.symm hbr_py] at hw
        linarith [((hout_iff r hp_leg hpl).mp
          ((win_congr_card_of_isAnonymous hT E hf_anon hpl.symm hcard).mp hw)).le]
      have hbr_yp : branch y p = branch y T.center :=
        branch_eq_of_mem hT ((mem_branch_inward_iff hT hy hyc p).mpr
          ⟨hpy, fun h => by linarith [h.2]⟩)
      simpa only [compl_compl, ← E.branch_eq hpy hyc.symm hbr_yp] using E.duality hpy hnot_py
  have hwin_eq (y q : MetricGraph W) (hqy : q ≠ y) (S : Finset (Fin 3)) :
      E.win y q S ↔ (P.toTreeEMVS hT).win y q S := by
    have hSle : S.card ≤ 3 := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
    have hwin_card (q₀ : MetricGraph W) (hq₀ : q₀ ≠ y) {P₁ P₂ : Prop}
        (h12 : P₁ → P₂) (hP₁ : E.win y q₀ {0} ↔ P₁) (hP₂ : E.win y q₀ {0, 1} ↔ P₂) :
        E.win y q₀ S ↔ (P₁ ∧ 1 ≤ S.card) ∨ (P₂ ∧ 2 ≤ S.card) ∨ 3 ≤ S.card := by
      rcases (by omega : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3) with
        h0 | h1 | h2 | h3
      · rw [Finset.card_eq_zero.mp h0]
        exact iff_of_false (E.empty_false hq₀) (by rintro (⟨_, h⟩ | ⟨_, h⟩ | h) <;> simp at h)
      · rw [win_congr_card_of_isAnonymous hT E hf_anon hq₀ (S₂ := {0}) (by simp [h1]), hP₁]
        exact ⟨fun h => .inl ⟨h, by omega⟩, fun h => h.elim And.left fun _ => by omega⟩
      · rw [win_congr_card_of_isAnonymous hT E hf_anon hq₀ (S₂ := {0, 1}) (by simp [h2]), hP₂]
        exact ⟨fun h => .inr (.inl ⟨h, by omega⟩),
          fun h => h.elim (h12 ∘ And.left) fun h => h.elim And.left fun _ => by omega⟩
      · rw [Finset.eq_univ_of_card S (by simpa using h3)]
        exact iff_of_true (E.univ_true hq₀) (Or.inr (Or.inr (by decide)))
    have hwin_out (r : Fin 3) (hy : y ∈ interval T.center (T.leaf r)) (hyl : y ≠ T.leaf r) :
        E.win y (T.leaf r) S ↔ P.outwardWin r (dist T.center y) S :=
      hwin_card (T.leaf r) hyl.symm (fun h => h.trans_le (P.low_le_high r))
        (hlow_iff r hy hyl) (hhigh_iff r hy hyl)
    have hwin_in (r : Fin 3) (hy : y ∈ interval T.center (T.leaf r)) (hyc : y ≠ T.center) :
        E.win y T.center S ↔ P.inwardWin r (dist T.center y) S :=
      hwin_card T.center hyc.symm (fun h => (P.low_le_high r).trans_lt h)
        (hin_iff {0} {0, 1} high (by decide) P.high_nonneg hhigh_iff r hy hyc)
        (hin_iff {0, 1} {0} low (by decide) P.low_nonneg hlow_iff r hy hyc)
    obtain ⟨r, hy⟩ := T.cover y
    by_cases hyc : y = T.center
    · subst hyc
      obtain ⟨s, hbr⟩ := branch_center_eq_leaf hT hqy
      rw [E.branch_eq hqy (T.leaf_ne_center s) hbr,
        (P.toTreeEMVS hT).branch_eq hqy (T.leaf_ne_center s) hbr,
        hwin_out s (left_mem_interval _ _) (T.leaf_ne_center s).symm]
      refine ⟨fun hw => Or.inl ⟨s, left_mem_interval _ _, (T.leaf_ne_center s).symm,
        mem_branch_self (T.leaf_ne_center s), hw⟩, ?_⟩
      rintro (⟨s', _, _, hqm, hw⟩ | ⟨_, _, hne, _, _⟩)
      · exact by_contra (fun hne => branch_center_ne_of_ne hT hne (branch_eq_of_mem hT hqm)) ▸ hw
      · exact absurd rfl hne
    · rcases branch_eq_outward_or_inward hT hy hyc hqy with ⟨hyl, hbr⟩ | hbr
      · rw [E.branch_eq hqy hyl.symm hbr, (P.toTreeEMVS hT).branch_eq hqy hyl.symm hbr,
          hwin_out r hy hyl]
        refine ⟨fun hw => Or.inl ⟨r, hy, hyl, mem_branch_self hyl.symm, hw⟩, ?_⟩
        rintro (⟨r', hy', _, _, hw⟩ | ⟨r', hy', _, hqm, _⟩)
        · exact leg_unique_of_ne_center hyc hy hy' ▸ hw
        · obtain rfl := leg_unique_of_ne_center hyc hy hy'
          exact absurd (branch_eq_of_mem hT hqm) (branch_outward_ne_inward hT hy hyc hyl)
      · rw [E.branch_eq hqy (Ne.symm hyc) hbr, (P.toTreeEMVS hT).branch_eq hqy (Ne.symm hyc) hbr,
          hwin_in r hy hyc]
        refine ⟨fun hw => Or.inr ⟨r, hy, hyc, mem_branch_self (Ne.symm hyc), hw⟩, ?_⟩
        rintro (⟨r', hy', hyl', hqm, _⟩ | ⟨r', hy', _, _, hw⟩)
        · obtain rfl := leg_unique_of_ne_center hyc hy hy'
          exact absurd (branch_eq_of_mem hT hqm).symm (branch_outward_ne_inward hT hy hyc hyl')
        · exact leg_unique_of_ne_center hyc hy hy' ▸ hw
  refine ⟨P, funext fun x => ?_⟩
  rw [ThreeLeafScheme.eval]
  exact (((P.toTreeEMVS hT).eval_eq_iff hT x (E.eval hT x)).mpr fun q hq S hS hw =>
    ((E.eval_eq_iff hT x (E.eval hT x)).mp rfl) q hq S hS ((hwin_eq _ q hq S).mpr hw)).symm

end Characterization

end Cslib.GameTheory.FacilityLocation
