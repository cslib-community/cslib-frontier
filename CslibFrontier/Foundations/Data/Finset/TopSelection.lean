/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate (Mathlib, finite selection and rounding)

public import CslibFrontier.Init
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

/-!
# Selecting largest coordinates and rounding an approximate indicator

`List.selectLargest` sorts a finite list by decreasing weight and keeps its first `k` entries.
It is executable when its weights have a decidable linear order, including integer weights.

The rounding theorem bounds the number of missed coordinates when selecting a set of the
correct cardinality by largest score. If the scores are close to a scaled indicator in squared
Euclidean distance, the selected set has small symmetric difference from its support. The proof
pairs each missed coordinate with an incorrectly selected coordinate.
-/

public section

namespace List

variable {α β : Type*} [DecidableEq α] [LinearOrder β]

/-- Sort by decreasing weight and select the first `k` entries, breaking ties by the order
chosen by merge sort. A duplicate-free input yields `min k xs.length` selected elements. -/
@[expose] def selectLargest (weight : α → β) (k : ℕ) (xs : List α) : Finset α :=
  ((xs.mergeSort fun a b => decide (weight b ≤ weight a)).take k).toFinset

/-- On a duplicate-free input, selection has the expected cardinality. -/
theorem card_selectLargest (weight : α → β) (k : ℕ) {xs : List α} (hxs : xs.Nodup) :
    (selectLargest weight k xs).card = min k xs.length := by
  have hsorted : (xs.mergeSort fun a b => decide (weight b ≤ weight a)).Nodup :=
    (List.mergeSort_perm xs _).nodup_iff.mpr hxs
  rw [selectLargest, List.toFinset_card_of_nodup (hsorted.take (i := k)), List.length_take,
    List.length_mergeSort]

/-- Every selected weight is at least every omitted weight from the input list. -/
theorem weight_le_of_notMem_selectLargest (weight : α → β) (k : ℕ) (xs : List α)
    {i j : α} (hi : i ∈ xs) (hinot : i ∉ selectLargest weight k xs)
    (hj : j ∈ selectLargest weight k xs) : weight i ≤ weight j := by
  let ys := xs.mergeSort fun a b => decide (weight b ≤ weight a)
  have hsorted : ys.Pairwise (fun a b => weight b ≤ weight a) := by
    simpa only [ys, decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun a b => decide (weight b ≤ weight a))
        (fun a b c h₁ h₂ =>
          decide_eq_true (le_trans (of_decide_eq_true h₂) (of_decide_eq_true h₁)))
        (fun a b => by rcases le_total (weight b) (weight a) with h | h <;> simp [h]) xs
  have hiys : i ∈ ys := by simpa only [ys, List.mem_mergeSort] using hi
  have hinot' : i ∉ ys.take k := by simpa only [selectLargest, List.mem_toFinset] using hinot
  have hj' : j ∈ ys.take k := by simpa only [selectLargest, List.mem_toFinset] using hj
  have hidrop : i ∈ ys.drop k := by
    have hi' : i ∈ ys.take k ++ ys.drop k := by simpa only [List.take_append_drop] using hiys
    exact (List.mem_append.mp hi').resolve_left hinot'
  exact hsorted.rel_of_mem_take_of_mem_drop hj' hidrop

end List

namespace Finset

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rounding a real score vector by its largest coordinates. If `S` and `T` have the same
cardinality and the scores on `T` dominate those outside `T`, the squared error from the
scaled indicator of `S` controls the number of missed elements. This statement also covers
negative scores; the indicator height `a` is nonnegative. -/
theorem card_sdiff_mul_sq_le_sum_sq (S T : Finset ι) (x : ι → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hcard : S.card = T.card)
    (horder : ∀ i ∉ T, ∀ j ∈ T, x i ≤ x j) :
    ((S \ T).card : ℝ) * a ^ 2 ≤
      2 * ∑ i, (x i - if i ∈ S then a else 0) ^ 2 := by
  let A := S \ T
  let B := T \ S
  let error : ι → ℝ := fun i => (x i - if i ∈ S then a else 0) ^ 2
  have hAB : A.card = B.card := Finset.card_sdiff_comm hcard
  let e : A ≃ B := Fintype.equivOfCardEq (by simpa using hAB)
  have hpair (i : A) : a ^ 2 ≤ 2 * (error i + error (e i)) := by
    obtain ⟨hiS, hiT⟩ := Finset.mem_sdiff.mp i.property
    obtain ⟨hjT, hjS⟩ := Finset.mem_sdiff.mp (e i).property
    have hle := horder i hiT (e i) hjT
    have hprod := mul_nonneg ha (sub_nonneg.mpr hle)
    dsimp only [error]
    simp only [hiS, hjS, ite_true, ite_false, sub_zero]
    nlinarith [sq_nonneg (x i + x (e i) - a), sq_nonneg (x i - x (e i))]
  have hdisj : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hsum : (∑ i ∈ A, error i) + (∑ i ∈ B, error i) ≤ ∑ i, error i := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ =>
      sq_nonneg _
  calc
    ((S \ T).card : ℝ) * a ^ 2 = ∑ _i : A, a ^ 2 := by simp [A]
    _ ≤ ∑ i : A, 2 * (error i + error (e i)) := Finset.sum_le_sum fun i _ => hpair i
    _ = 2 * ((∑ i ∈ A, error i) + (∑ i ∈ B, error i)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib,
        e.sum_comp (fun j : B => error j), Finset.sum_coe_sort, Finset.sum_coe_sort]
    _ ≤ 2 * ∑ i, error i := mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- A squared error of at most `1 / 32` from a normalized indicator suffices for the
one-sixteenth overlap bound used in clique recovery. The normalization equation separates
this finite rounding argument from the construction of a unit indicator vector. -/
theorem sixteen_mul_card_sdiff_le_of_sum_sq_le (S T : Finset ι) (x : ι → ℝ)
    {a : ℝ} {k : ℕ} (ha : 0 ≤ a) (hscale : (k : ℝ) * a ^ 2 = 1)
    (hcard : S.card = T.card) (horder : ∀ i ∉ T, ∀ j ∈ T, x i ≤ x j)
    (herror : ∑ i, (x i - if i ∈ S then a else 0) ^ 2 ≤ 1 / 32) :
    16 * (S \ T).card ≤ k := by
  have hround := card_sdiff_mul_sq_le_sum_sq S T x ha hcard horder
  have hbound : ((S \ T).card : ℝ) * a ^ 2 ≤ 1 / 16 := by linarith
  have hscaled : ((S \ T).card : ℝ) ≤ (k : ℝ) * (1 / 16) := by
    calc
      ((S \ T).card : ℝ) = (k : ℝ) * (((S \ T).card : ℝ) * a ^ 2) := by
        rw [mul_left_comm, hscale, mul_one]
      _ ≤ (k : ℝ) * (1 / 16) :=
        mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg k)
  have hreal : (16 : ℝ) * (S \ T).card ≤ k := by linarith
  exact_mod_cast hreal

end Finset
