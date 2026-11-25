/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
import CslibFrontier.Foundations.Data.List.OrderStatistic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Multiset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Order statistics and medians of finite families

Defines rank-`k` order statistics (`Fintype.IsOrderStatistic`, `Fintype.orderStatistic`), lower
median `x_((n - 1) / 2)` (`Fintype.lowerMedian`), and upper median `x_(n / 2)`
(`Fintype.upperMedian`) for finite families `x : ι → α`, bridging to `List.IsOrderStatistic` and
proving that any median minimizes `∑ i, |x i - y|` over `ℝ`.

## Main definitions

* `Fintype.IsOrderStatistic`: `y` is the `k`-th order statistic (0-indexed) of `x : ι → α`.
* `Fintype.orderStatistic`: the `k`-th order statistic of `x : ι → α` (clamped at `|ι| - 1`).
* `Fintype.lowerMedian`, `Fintype.upperMedian`: the lower and upper medians of `x : ι → α`.

## Main results

* `Fintype.IsOrderStatistic.unique`, `Fintype.orderStatistic_isOrderStatistic`,
  `Fintype.orderStatistic_eq_of_isOrderStatistic`, `Fintype.orderStatistic_fin_eq_mergeSort`,
  `Fintype.lt_orderStatistic_iff`, `Fintype.orderStatistic_comp_equiv`:
  uniqueness, rank and threshold characterizations, merge-sort correspondence, and permutation
  invariance.
* `Fintype.sum_abs_sub_le_of_median_counts`, `Fintype.sum_abs_sub_lowerMedian_le`,
  `Fintype.sum_abs_sub_upperMedian_le`: on `ℝ`, any point with at most `|ι| / 2` elements strictly
  on each side (and in particular `lowerMedian x` and `upperMedian x`) minimizes `∑ i, |x i - y|`.
-/

public section

namespace Fintype

open Finset
open scoped BigOperators

section OrderStatistic

open Classical in
/-- `y` is the `k`-th order statistic (0-indexed) of the profile `x : ι → α`: `y` lies in the
image of `x`, at most `k` indices satisfy `x i < y`, and strictly more than `k` satisfy
`x i ≤ y`. -/
@[expose] def IsOrderStatistic {ι α : Type*} [Fintype ι] [LinearOrder α] (x : ι → α)
    (k : ℕ) (y : α) : Prop :=
  (∃ i : ι, x i = y) ∧
    (Finset.univ.filter fun i => x i < y).card ≤ k ∧
    k < (Finset.univ.filter fun i => x i ≤ y).card

open Classical in
/-- The `k`-th order statistic (0-indexed) of `x : ι → α`, clamped to `Fintype.card ι - 1` when
`k ≥ Fintype.card ι`. -/
noncomputable def orderStatistic {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α]
    (x : ι → α) (k : ℕ) : α :=
  ((Finset.univ.val.map x).sort (· ≤ ·))[min k (Fintype.card ι - 1)]'(by
    rw [Multiset.length_sort, Multiset.card_map, Finset.card_val, Finset.card_univ]
    exact Nat.lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt Fintype.card_pos zero_lt_one))

/-- The lower median `x_((n - 1) / 2)` of a nonempty finite family `x`. -/
noncomputable def lowerMedian {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α]
    (x : ι → α) : α :=
  orderStatistic x ((Fintype.card ι - 1) / 2)

/-- The upper median `x_(n / 2)` of a nonempty finite family `x`. -/
noncomputable def upperMedian {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α]
    (x : ι → α) : α :=
  orderStatistic x (Fintype.card ι / 2)

theorem lowerMedian_def {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α] (x : ι → α) :
    lowerMedian x = orderStatistic x ((Fintype.card ι - 1) / 2) := by
  unfold lowerMedian
  rfl

theorem upperMedian_def {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α] (x : ι → α) :
    upperMedian x = orderStatistic x (Fintype.card ι / 2) := by
  unfold upperMedian
  rfl

theorem orderStatistic_eq_min {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α]
    (x : ι → α) (k : ℕ) :
    orderStatistic x k = orderStatistic x (min k (Fintype.card ι - 1)) := by
  simp only [orderStatistic, min_assoc, min_self]

section Lemmas

open Classical in
private theorem countP_sorted_eq_card_filter {ι α : Type*} [Fintype ι] [LinearOrder α]
    (x : ι → α) (p : α → Bool) :
    ((Finset.univ.val.map x).sort (· ≤ ·)).countP p =
      (Finset.univ.filter fun i => p (x i)).card := by
  have hp : p = fun a => decide (p a = true) := funext fun a => by cases p a <;> rfl
  rw [hp, ← Multiset.coe_countP, Multiset.sort_eq, Multiset.countP_map, ← Finset.filter_val]
  simp only [Bool.decide_eq_true]
  rfl

open Classical in
private theorem isOrderStatistic_iff_list {ι α : Type*} [Fintype ι] [LinearOrder α]
    {x : ι → α} {k : ℕ} {y : α} :
    IsOrderStatistic x k y ↔
      ((Finset.univ.val.map x).sort (· ≤ ·)).IsOrderStatistic (· ≤ ·) k y := by
  set s := (Finset.univ.val.map x).sort (· ≤ ·)
  have hmem : (∃ i : ι, x i = y) ↔ y ∈ s := by
    rw [Multiset.mem_sort, Multiset.mem_map]
    simp only [Finset.mem_val, Finset.mem_univ, true_and]
  have hlt : (Finset.univ.filter fun i => x i < y).card = s.countP (fun a => ¬ y ≤ a) := by
    rw [countP_sorted_eq_card_filter x (fun a => decide (¬ y ≤ a))]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, not_le]
  have hle : (Finset.univ.filter fun i => x i ≤ y).card = s.countP (fun a => a ≤ y) := by
    rw [countP_sorted_eq_card_filter x (fun a => decide (a ≤ y))]
    simp only [decide_eq_true_eq]
  rw [IsOrderStatistic, hmem, hlt, hle]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩, fun h => ⟨h.mem, h.countP_lt_le, h.lt_countP_le⟩⟩

variable {ι α : Type*} [Fintype ι] [LinearOrder α]

theorem IsOrderStatistic.unique {x : ι → α} {k : ℕ} {y y' : α}
    (h : IsOrderStatistic x k y) (h' : IsOrderStatistic x k y') : y = y' :=
  (isOrderStatistic_iff_list.1 h).unique (isOrderStatistic_iff_list.1 h')

theorem orderStatistic_isOrderStatistic [Nonempty ι] (x : ι → α) {k : ℕ}
    (hk : k < Fintype.card ι) : IsOrderStatistic x k (orderStatistic x k) := by
  classical
  rw [isOrderStatistic_iff_list]
  have hlen : k < ((Finset.univ.val.map x).sort (· ≤ ·)).length := by
    rw [Multiset.length_sort, Multiset.card_map, Finset.card_val, Finset.card_univ]
    exact hk
  have hmin : min k (Fintype.card ι - 1) = k := min_eq_left (Nat.le_pred_of_lt hk)
  have hlist := List.isOrderStatistic_getElem_of_perm (List.Perm.refl _)
    (Multiset.pairwise_sort _ _) hlen
  simpa only [orderStatistic, hmin] using hlist

theorem orderStatistic_eq_of_isOrderStatistic [Nonempty ι] {x : ι → α} {k : ℕ}
    (hk : k < Fintype.card ι) {y : α} (h : IsOrderStatistic x k y) :
    orderStatistic x k = y :=
  (orderStatistic_isOrderStatistic x hk).unique h

theorem orderStatistic_fin_eq_mergeSort {n : ℕ} (x : Fin (n + 1) → α) {k : ℕ} (hk : k < n + 1) :
    (List.ofFn x).mergeSort[k]? = some (orderStatistic x k) := by
  classical
  rw [← List.isOrderStatistic_iff_mergeSort]
  have hlist := isOrderStatistic_iff_list.1
    (orderStatistic_isOrderStatistic x (by simpa only [Fintype.card_fin] using hk))
  have hperm : (List.ofFn x).Perm ((Finset.univ.val.map x).sort (· ≤ ·)) := by
    rw [← Multiset.coe_eq_coe, Multiset.sort_eq, Fin.univ_def, List.ofFn_eq_map]
    rfl
  exact ⟨hperm.symm.subset hlist.mem, hperm.countP_eq _ ▸ hlist.countP_lt_le,
    hperm.countP_eq _ ▸ hlist.lt_countP_le⟩

/-- Threshold characterization of the `k`-th order statistic: `t < orderStatistic x k` if and only
if at most `k` indices satisfy `x i ≤ t`. -/
theorem lt_orderStatistic_iff [Nonempty ι] (x : ι → α) {k : ℕ} (hk : k < Fintype.card ι) (t : α) :
    t < orderStatistic x k ↔ (Finset.univ.filter fun i => x i ≤ t).card ≤ k := by
  classical
  have hos := orderStatistic_isOrderStatistic x hk
  refine ⟨fun ht => (Finset.card_le_card fun i hi => Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2.trans_lt ht⟩).trans hos.2.1,
    fun hcard => not_le.mp fun hle => not_lt_of_ge hcard (hos.2.2.trans_le
      (Finset.card_le_card fun i hi => Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2.trans hle⟩))⟩

/-- Reindexing a family along an equivalence preserves every order statistic. -/
theorem orderStatistic_comp_equiv {ι' : Type*} [Fintype ι'] [Nonempty ι] [Nonempty ι']
    (e : ι' ≃ ι) (x : ι → α) (k : ℕ) :
    orderStatistic (x ∘ e) k = orderStatistic x k := by
  classical
  rw [orderStatistic_eq_min, orderStatistic_eq_min x, Fintype.card_congr e]
  set k' := min k (Fintype.card ι - 1)
  have hk' : k' < Fintype.card ι :=
    Nat.lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt Fintype.card_pos zero_lt_one)
  have hk'_ι' : k' < Fintype.card ι' := by rwa [Fintype.card_congr e]
  refine orderStatistic_eq_of_isOrderStatistic hk'_ι' ?_
  have hos := orderStatistic_isOrderStatistic x hk'
  have hcard : ∀ (p : α → Prop) [DecidablePred p],
      (Finset.univ.filter fun c : ι' => p ((x ∘ e) c)).card =
        (Finset.univ.filter fun i : ι => p (x i)).card := fun p _ =>
    Finset.card_bij (fun c _ => e c)
      (fun c hc => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2⟩)
      (fun _ _ _ _ h => e.injective h)
      (fun i hi => ⟨e.symm i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
          (Finset.mem_filter.mp hi).2⟩, e.apply_symm_apply i⟩)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hos.1
    exact ⟨e.symm i, by simp only [Function.comp_apply, Equiv.apply_symm_apply, hi]⟩
  · rw [hcard (· < orderStatistic x k')]
    exact hos.2.1
  · rw [hcard (· ≤ orderStatistic x k')]
    exact hos.2.2

end Lemmas

end OrderStatistic

section RealMedian

/-- Any point `y : ℝ` having at most `|ι| / 2` points strictly to its left and at most `|ι| / 2`
points strictly to its right minimizes `∑ i, |x i - y|`. -/
theorem sum_abs_sub_le_of_median_counts {ι : Type*} [Fintype ι] {x : ι → ℝ} {y : ℝ}
    (hlt : 2 * (Finset.univ.filter fun i => x i < y).card ≤ Fintype.card ι)
    (hgt : 2 * (Finset.univ.filter fun i => y < x i).card ≤ Fintype.card ι) (z : ℝ) :
    ∑ i, |x i - y| ≤ ∑ i, |x i - z| := by
  classical
  have aux : ∀ {x : ι → ℝ} {y z : ℝ},
      2 * (Finset.univ.filter fun i => x i < y).card ≤ Fintype.card ι → z ≤ y →
      ∑ i, |x i - y| ≤ ∑ i, |x i - z| := by
    intro x y z hlt' hzy
    set L := Finset.univ.filter fun i => x i < y
    set R := Finset.univ.filter fun i => ¬ x i < y
    have hcard : L.card + R.card = Fintype.card ι := by
      simpa only [Finset.card_univ] using
        Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun i => x i < y)
    have hLR : (L.card : ℝ) ≤ R.card := Nat.cast_le.2 (by omega)
    have hL : ∑ i ∈ L, |x i - y| ≤ ∑ i ∈ L, |x i - z| + (L.card : ℝ) * (y - z) :=
      (Finset.sum_le_sum fun i _ => by
        simpa only [abs_of_nonpos (sub_nonpos.2 hzy), neg_sub] using abs_sub_le (x i) z y).trans_eq
        (by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul])
    have hR : ∑ i ∈ R, |x i - y| = ∑ i ∈ R, |x i - z| - (R.card : ℝ) * (y - z) := by
      have hcongr : ∑ i ∈ R, |x i - y| = ∑ i ∈ R, (|x i - z| - (y - z)) :=
        Finset.sum_congr rfl fun i hi => by
          have hxi := not_lt.1 (Finset.mem_filter.1 hi).2
          rw [abs_of_nonneg (sub_nonneg.2 hxi), abs_of_nonneg (sub_nonneg.2 (hzy.trans hxi))]
          ring
      rw [hcongr, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have hsplit_y := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => x i < y)
      (fun i => |x i - y|)
    have hsplit_z := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => x i < y)
      (fun i => |x i - z|)
    linarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hLR) (sub_nonneg.2 hzy)]
  rcases le_total z y with hzy | hyz
  · exact aux hlt hzy
  · have hneg := aux (x := fun i => -x i) (y := -y) (z := -z)
      (by simpa only [neg_lt_neg_iff] using hgt) (neg_le_neg hyz)
    simpa only [neg_sub_neg, abs_sub_comm] using hneg

private theorem sum_abs_sub_orderStatistic_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) {k : ℕ} (hk : k < Fintype.card ι) (hle : 2 * k ≤ Fintype.card ι)
    (hge : Fintype.card ι ≤ 2 * (k + 1)) (z : ℝ) :
    ∑ i, |x i - orderStatistic x k| ≤ ∑ i, |x i - z| := by
  classical
  have hos := orderStatistic_isOrderStatistic x hk
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun i => x i ≤ orderStatistic x k)
  have hgt_eq : (Finset.univ.filter fun i => orderStatistic x k < x i) =
      Finset.univ.filter fun i => ¬ x i ≤ orderStatistic x k := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  rw [Finset.card_univ, ← hgt_eq] at hsplit
  refine sum_abs_sub_le_of_median_counts ?_ ?_ z
  · have := hos.2.1; omega
  · have := hos.2.2; omega

/-- The lower median minimizes `∑ i, |x i - y|` over `ℝ`. -/
theorem sum_abs_sub_lowerMedian_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (z : ℝ) :
    ∑ i, |x i - lowerMedian x| ≤ ∑ i, |x i - z| := by
  have hk : (Fintype.card ι - 1) / 2 < Fintype.card ι :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ 2) (Nat.sub_lt Fintype.card_pos zero_lt_one)
  have hpos := Fintype.card_pos (α := ι)
  exact sum_abs_sub_orderStatistic_le x hk (by omega) (by omega) z

/-- The upper median minimizes `∑ i, |x i - y|` over `ℝ`. -/
theorem sum_abs_sub_upperMedian_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (z : ℝ) :
    ∑ i, |x i - upperMedian x| ≤ ∑ i, |x i - z| := by
  have hk : Fintype.card ι / 2 < Fintype.card ι :=
    Nat.div_lt_self Fintype.card_pos (by decide)
  exact sum_abs_sub_orderStatistic_le x hk (by omega) (by omega) z

end RealMedian

end Fintype
