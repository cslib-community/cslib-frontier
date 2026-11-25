/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.SOA
public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.VCDimension
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Nat
import CslibFrontier.MachineLearning.PACLearning.VCDimension
import Mathlib.Data.Fintype.Card

/-!
# Thresholds: VC dimension one, unbounded Littlestone dimension

On any linear order `α`, the threshold concept `thresholdConcept θ : α → Bool` labels `x` with
`true` iff `x < θ`, and `thresholdClass α` is the class of all such thresholds:

* no two points are shattered, since a threshold labelling the larger point `true` labels the
  smaller one `true` too (`not_setShatters_thresholdClass`), so `vcDim (thresholdClass α) = 1`
  whenever `α` is nontrivial (`vcDim_thresholdClass`);
* any `2 ^ k` strictly ordered thresholds admit a complete `k`-mistake tree by binary search on the
  midpoint (`hasMistakeTree_thresholdConcept_orderEmb`), so every infinite linear order — including
  `ℕ`, `ℚ`, and `ℝ` — has `littlestoneDim (thresholdClass α) = ⊤` (`littlestoneDim_thresholdClass`);
* on a dense linear order such as `ℚ`, even the thresholds restricted to an arbitrarily small
  nonempty open interval `(lo, hi)` admit complete mistake trees of every height
  (`hasMistakeTree_thresholdConcept_Ioo`).

On `ℕ`, the finite prefix `thresholdClassUpTo N` (`θ ≤ N`) gives the quantitative finite gap
[Littlestone1988, §3, Example 3]: VC dimension `1` (`vcDim_thresholdClassUpTo`) and Littlestone
dimension `⌊log₂ (N + 1)⌋` (`littlestoneDim_thresholdClassUpTo`), so `2 ^ n` thresholds have optimal
mistake bound `n` (`optimalMistakeBound_thresholdClassUpTo_pow`). Meanwhile `thresholdClass α` is
realizable-PAC learnable via a size-`1` sample compression scheme (`isPACLearnable_thresholdClass`
in `CslibFrontier/MachineLearning/PACLearning/Compression/Thresholds.lean`), separating PAC
learnability from online mistake-bound learnability.

Littlestone's Example 3 uses the instance space `{1, …, 2 ^ n - 1}` and the thresholds
`f_j(x) = 1` iff `x < j` for `j ∈ {1, …, 2 ^ n}`. For `thresholdClassUpTo`, the instance space is
all of `ℕ` and `θ ∈ {0, …, 2 ^ n - 1}`; the instances `x ≥ N` add nothing since every threshold in
`thresholdClassUpTo N` labels them `false`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.thresholdConcept`: the threshold `x < θ` on a
  linear order.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.thresholdClass`: all thresholds on a linear
  order `α`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.thresholdClassUpTo`: the thresholds `θ ≤ N` on
  `ℕ`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.vcDim_thresholdClass`:
  `vcDim (thresholdClass α) = 1` for every nontrivial linear order `α`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim_thresholdClass`:
  `littlestoneDim (thresholdClass α) = ⊤` for every infinite linear order `α` (such as `ℕ` or `ℚ`).
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.hasMistakeTree_thresholdConcept_Ioo`: on a
  dense linear order, thresholds in `(lo, hi)` (`lo < hi`) have mistake trees of every height.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim_thresholdClassUpTo`:
  `littlestoneDim (thresholdClassUpTo N) = ⌊log₂ (N + 1)⌋`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.optimalMistakeBound_thresholdClassUpTo_pow`:
  [Littlestone1988, §3, Example 3], `2 ^ n` thresholds have optimal mistake bound `n`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.vcDim_thresholdClassUpTo`: VC dimension `1`
  for `N ≥ 1`.

## References

* [N. Littlestone, *Learning quickly when irrelevant attributes abound: a new linear-threshold
  algorithm*][Littlestone1988]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

open PACLearning (ConceptClass SetShatters vcDim evcDim)

section LinearOrder

variable {α : Type*} [LinearOrder α]

/-- The threshold concept on a linear order: `x` is labelled `true` iff `x < θ`. -/
def thresholdConcept (θ : α) : α → Bool := fun x => decide (x < θ)

/-- The class of all threshold concepts `x ↦ decide (x < θ)` on a linear order `α`. -/
def thresholdClass (α : Type*) [LinearOrder α] : ConceptClass α Bool :=
  Set.range thresholdConcept

@[simp] theorem thresholdConcept_apply (θ x : α) : thresholdConcept θ x = decide (x < θ) := by
  rw [thresholdConcept]

theorem mem_thresholdClass {c : α → Bool} :
    c ∈ thresholdClass α ↔ ∃ θ : α, thresholdConcept θ = c := by
  simp [thresholdClass]

@[simp] theorem thresholdConcept_mem_thresholdClass (θ : α) :
    thresholdConcept θ ∈ thresholdClass α :=
  ⟨θ, rfl⟩

/-- Binary search along any order-embedded chain of `2 ^ k` thresholds gives a complete `k`-mistake
tree. -/
theorem hasMistakeTree_thresholdConcept_orderEmb (k : ℕ) (e : Fin (2 ^ k) ↪o α) :
    HasMistakeTree k (thresholdConcept '' Set.range e) := by
  induction k with
  | zero => exact ⟨_, _, ⟨⟨0, Nat.one_le_two_pow⟩, rfl⟩, rfl⟩
  | succ k ih =>
    have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    refine hasMistakeTree_succ_bool.mpr ⟨e ⟨2 ^ k - 1, by rw [pow_succ]; omega⟩, fun y => ?_⟩
    cases y
    · refine (ih (OrderEmbedding.ofStrictMono
        (fun i => e ⟨i.1, by rw [pow_succ]; omega⟩) fun _ _ h => e.strictMono h)).mono ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      have hi : i.1 < 2 ^ (k + 1) := by have := i.2; rw [pow_succ]; omega
      refine mem_versionSpace_singleton.mpr ⟨⟨e ⟨i.1, hi⟩, ⟨⟨i.1, hi⟩, rfl⟩, rfl⟩, ?_⟩
      simp only [thresholdConcept_apply, decide_eq_false_iff_not, not_lt]
      exact e.le_iff_le.mpr (Fin.mk_le_mk.mpr (by have := i.2; omega))
    · refine (ih (OrderEmbedding.ofStrictMono
        (fun i => e ⟨2 ^ k + i.1, by rw [pow_succ]; omega⟩) fun _ _ h =>
          e.strictMono (Nat.add_lt_add_left h _))).mono ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      have hi : 2 ^ k + i.1 < 2 ^ (k + 1) := by have := i.2; rw [pow_succ]; omega
      refine mem_versionSpace_singleton.mpr ⟨⟨e ⟨2 ^ k + i.1, hi⟩, ⟨⟨2 ^ k + i.1, hi⟩, rfl⟩, rfl⟩,
        ?_⟩
      simp only [thresholdConcept_apply, decide_eq_true_eq]
      exact e.lt_iff_lt.mpr (Fin.mk_lt_mk.mpr (by omega))

/-- Every infinite linear order (for instance `ℕ`, `ℚ`, or `ℝ`) has thresholds of infinite
Littlestone dimension: no deterministic online learner has a finite mistake bound. -/
theorem littlestoneDim_thresholdClass [Infinite α] : littlestoneDim (thresholdClass α) = ⊤ := by
  refine ENat.eq_top_iff_forall_ge.mpr fun k => ?_
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α (2 ^ k)
  refine le_littlestoneDim_of_hasMistakeTree
    ((hasMistakeTree_thresholdConcept_orderEmb k (s.orderEmbOfFin hs)).mono ?_)
  exact (Set.image_mono (Set.subset_univ _)).trans (by simp [thresholdClass])

/-- On a dense linear order (such as `ℚ`), the thresholds strictly inside `(lo, hi)` (`lo < hi`)
admit complete mistake trees of every height via midpoint bisection. -/
theorem hasMistakeTree_thresholdConcept_Ioo [DenselyOrdered α] (k : ℕ) {lo hi : α}
    (h : lo < hi) : HasMistakeTree k (thresholdConcept '' Set.Ioo lo hi) := by
  induction k generalizing lo hi with
  | zero =>
    obtain ⟨m, hm⟩ := exists_between h
    exact ⟨_, m, hm, rfl⟩
  | succ k ih =>
    obtain ⟨m, hlo, hhi⟩ := exists_between h
    refine hasMistakeTree_succ_bool.mpr ⟨m, fun y => ?_⟩
    cases y
    · refine (ih hlo).mono ?_
      rintro _ ⟨θ, ⟨h1, h2⟩, rfl⟩
      exact mem_versionSpace_singleton.mpr ⟨⟨θ, ⟨h1, h2.trans hhi⟩, rfl⟩, by simpa using h2.le⟩
    · refine (ih hhi).mono ?_
      rintro _ ⟨θ, ⟨h1, h2⟩, rfl⟩
      exact mem_versionSpace_singleton.mpr ⟨⟨θ, ⟨hlo.trans h1, h2⟩, rfl⟩, by simpa using h1⟩

/-- No two points of a linear order are shattered by thresholds. -/
theorem not_setShatters_thresholdClass {W : Finset α} (hW : 1 < W.card) :
    ¬ SetShatters (thresholdClass α) (W : Set α) := by
  intro hsh
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hW
  wlog hlt : a < b generalizing a b
  · exact this b hb a ha hab.symm (hab.lt_or_gt.resolve_left hlt)
  obtain ⟨_, ⟨θ, rfl⟩, hc⟩ := hsh {b} (by simpa using hb)
  have hbθ : b < θ := by
    simpa using (hc ▸ rfl : b ∈ thresholdConcept θ ⁻¹' {true} ∩ (W : Set α)).1
  have ha' : a ∉ thresholdConcept θ ⁻¹' {true} ∩ (W : Set α) := by
    rw [hc]
    simpa using hab
  exact ha' ⟨by simpa using hlt.trans hbθ, ha⟩

/-- A subclass of `thresholdClass α` that shatters a singleton has VC dimension `1`. -/
theorem vcDim_eq_one_of_subset_thresholdClass {C : ConceptClass α Bool}
    (hC : C ⊆ thresholdClass α) (x : α) (hx : SetShatters C ({x} : Set α)) : vcDim C = 1 := by
  have hub : ∀ n ∈ {n : ℕ | ∃ W : Finset α, W.card = n ∧ SetShatters C (W : Set α)}, n ≤ 1 := by
    rintro n ⟨W, rfl, hW⟩
    exact not_lt.mp fun h => not_setShatters_thresholdClass h (hW.superset hC)
  refine le_antisymm (csSup_le' hub) ?_
  simpa using (show SetShatters C (({x} : Finset α) : Set α) by simpa using hx).card_le_vcDim
    ⟨1, hub⟩

/-- On every nontrivial linear order `α`, the class of all thresholds has VC dimension `1`. -/
theorem vcDim_thresholdClass [Nontrivial α] : vcDim (thresholdClass α) = 1 := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have hlt : min a b < max a b := min_lt_max.mpr hab
  refine vcDim_eq_one_of_subset_thresholdClass subset_rfl (min a b) fun W' hW' => ?_
  rcases Set.subset_singleton_iff_eq.mp hW' with rfl | rfl
  · exact ⟨thresholdConcept (min a b), ⟨min a b, rfl⟩, by ext z; simp⟩
  · exact ⟨thresholdConcept (max a b), ⟨max a b, rfl⟩, by ext z; simp [hlt]⟩

end LinearOrder

/-! ### Finite prefixes on `ℕ` -/

/-- The threshold concepts on `ℕ` with `θ ≤ N`. -/
def thresholdClassUpTo (N : ℕ) : ConceptClass ℕ Bool := thresholdConcept '' Set.Iic N

theorem mem_thresholdClassUpTo {N : ℕ} {c : ℕ → Bool} :
    c ∈ thresholdClassUpTo N ↔ ∃ θ ≤ N, thresholdConcept θ = c := by
  simp [thresholdClassUpTo]

theorem thresholdConcept_injective : Function.Injective (thresholdConcept (α := ℕ)) := by
  intro a b hab
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := congrFun hab a; simp [h] at this
  · have := congrFun hab b; simp [h] at this

theorem thresholdClassUpTo_subset_thresholdClass (N : ℕ) :
    thresholdClassUpTo N ⊆ thresholdClass ℕ :=
  Set.image_subset_range _ _

/-- Binary search on `ℕ`: the thresholds `θ ∈ [lo, lo + 2 ^ k - 1]` have a complete `k`-mistake
tree. -/
theorem hasMistakeTree_thresholdConcept_Icc (k lo : ℕ) :
    HasMistakeTree k (thresholdConcept '' Set.Icc lo (lo + 2 ^ k - 1)) := by
  let e : Fin (2 ^ k) ↪o ℕ :=
    OrderEmbedding.ofStrictMono (fun i : Fin (2 ^ k) => lo + i.1) fun _ _ h =>
      Nat.add_lt_add_left h lo
  refine (hasMistakeTree_thresholdConcept_orderEmb k e).mono ?_
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨lo + i.1, ⟨Nat.le_add_right lo i.1, by have := i.2; omega⟩, rfl⟩

/-- The thresholds `θ ≤ N` on `ℕ` have Littlestone dimension `⌊log₂ (N + 1)⌋`. -/
theorem littlestoneDim_thresholdClassUpTo (N : ℕ) :
    littlestoneDim (thresholdClassUpTo N) = Nat.log 2 (N + 1) := by
  classical
  apply le_antisymm
  · have hC : thresholdClassUpTo N =
        ((Finset.Iic N).image thresholdConcept : Set (ℕ → Bool)) := by
      simp [thresholdClassUpTo]
    rw [hC]
    exact (littlestoneDim_le_log_card _).trans
      (by exact_mod_cast Nat.log_mono_right (Finset.card_image_le.trans (by simp)))
  · refine le_littlestoneDim_of_hasMistakeTree ((hasMistakeTree_thresholdConcept_Icc _ 0).mono ?_)
    rintro _ ⟨θ, ⟨-, h2⟩, rfl⟩
    have := Nat.pow_log_le_self 2 (Nat.add_one_ne_zero N)
    exact ⟨θ, by simp only [Set.mem_Iic]; omega, rfl⟩

/-- [Littlestone1988, §3, Example 3]: the `2 ^ n` thresholds `θ < 2 ^ n` have optimal mistake
bound `n`. -/
theorem optimalMistakeBound_thresholdClassUpTo_pow (n : ℕ) :
    optimalMistakeBound (thresholdClassUpTo (2 ^ n - 1)) = n := by
  rw [optimalMistakeBound_eq_littlestoneDim, littlestoneDim_thresholdClassUpTo,
    Nat.sub_add_cancel Nat.one_le_two_pow, Nat.log_pow (by norm_num)]

theorem setShatters_singleton_thresholdClassUpTo {N x : ℕ} (hx : x < N) :
    SetShatters (thresholdClassUpTo N) ({x} : Set ℕ) := by
  intro W' hW'
  rcases Set.subset_singleton_iff_eq.mp hW' with rfl | rfl
  · refine ⟨thresholdConcept 0, ⟨0, by simp, rfl⟩, ?_⟩
    ext
    simp
  · refine ⟨thresholdConcept (x + 1), ⟨x + 1, by simp only [Set.mem_Iic]; omega, rfl⟩, ?_⟩
    ext
    simp

/-- For `N ≥ 1`, the thresholds `θ ≤ N` have VC dimension `1`. -/
theorem vcDim_thresholdClassUpTo {N : ℕ} (hN : 1 ≤ N) : vcDim (thresholdClassUpTo N) = 1 :=
  vcDim_eq_one_of_subset_thresholdClass (thresholdClassUpTo_subset_thresholdClass N) 0
    (setShatters_singleton_thresholdClassUpTo hN)

end Cslib.MachineLearning.OnlineLearning.MistakeBound
