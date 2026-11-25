/-
Copyright (c) 2026 Samuel Schlesinger, Shengye Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Shengye Tao
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Prod

/-!
# Counting overlaps of Boolean supports

For fixed support x, a column is determined by its subsets inside and outside x.
Grouping each part by cardinality gives the exact finite tail used in the
Walsh–Hadamard construction of Alman–Williams, §3, arXiv:1611.05558.
`Cslib.card_off_band_row` counts columns for one row and `Cslib.card_off_band_pair` counts
ordered pairs.
-/

public section

namespace Cslib

open Finset

/-- Group a weight-dependent sum over all subsets by size. -/
private theorem sum_by_size {α : Type*} (x : Finset α) (f : ℕ → ℕ) :
    ∑ s ∈ x.powerset, f s.card = ∑ j ∈ range (x.card + 1), x.card.choose j * f j := by
  rw [sum_powerset]
  simp [sum_powersetCard, nsmul_eq_mul]

/-- Split a Boolean column into its supports inside and outside a fixed row. -/
private theorem sum_split {n : ℕ} (x : Finset (Fin n)) (f : ℕ → ℕ → ℕ) :
    ∑ y : Finset (Fin n), f (x ∩ y).card y.card =
      ∑ s ∈ x.powerset, ∑ q ∈ xᶜ.powerset, f s.card (s.card + q.card) := by
  classical
  rw [← sum_product']
  refine sum_nbij' (fun y => (x ∩ y, xᶜ ∩ y)) (fun p => p.1 ∪ p.2) ?_ (by simp) ?_ ?_ ?_
  · simp
  · intro y _
    ext i; by_cases h : i ∈ x <;> simp [h]
  · rintro ⟨s,q⟩ h
    obtain ⟨hs,hq⟩ : s ⊆ x ∧ q ⊆ xᶜ := by simpa using h
    apply Prod.ext
    · change x ∩ (s ∪ q) = s
      ext i; simp only [mem_inter, mem_union]; grind [mem_compl]
    · change xᶜ ∩ (s ∪ q) = q
      ext i; simp only [mem_inter, mem_union]; grind [mem_compl]
  · intro y _
    have hd : Disjoint (x ∩ y) (xᶜ ∩ y) :=
      disjoint_compl_right.mono inter_subset_left inter_subset_left
    have hu : (x ∩ y) ∪ (xᶜ ∩ y) = y := by ext i; by_cases h : i ∈ x <;> simp [h]
    rw [← card_union_of_disjoint hd, hu]

/-- Count central-weight columns whose overlap with a given row misses the interpolation band. -/
theorem card_off_band_row (n lo hi k t : ℕ) (x : Finset (Fin n)) :
    (univ.filter fun y : Finset (Fin n) => lo ≤ y.card ∧ y.card ≤ hi ∧
      ((x ∩ y).card < k ∨ k + t ≤ (x ∩ y).card)).card =
    let a := x.card
    ∑ j ∈ Finset.range (a + 1), ∑ b ∈ Finset.range (n - a + 1),
      if lo ≤ j + b ∧ j + b ≤ hi ∧ (j < k ∨ k + t ≤ j)
      then a.choose j * (n - a).choose b else 0 := by
  classical
  let f (j w : ℕ) := if lo ≤ w ∧ w ≤ hi ∧ (j < k ∨ k + t ≤ j) then 1 else 0
  calc
    _ = ∑ y : Finset (Fin n), f (x ∩ y).card y.card := by simp [f]
    _ = _ := sum_split x f
    _ = _ := by
      rw [sum_by_size x (fun j => ∑ q ∈ xᶜ.powerset, f j (j + q.card))]
      apply sum_congr rfl
      intro j _
      rw [sum_by_size xᶜ (fun b => f j (j + b)), card_compl, Fintype.card_fin, mul_sum]
      apply sum_congr rfl
      intro b _
      simp [f, mul_ite]

/-- Count ordered off-band pairs whose row and column both have central weight. -/
theorem card_off_band_pair (n lo hi k t : ℕ) :
    (univ.filter fun p : Finset (Fin n) × Finset (Fin n) =>
      lo ≤ p.1.card ∧ p.1.card ≤ hi ∧ lo ≤ p.2.card ∧ p.2.card ≤ hi ∧
      ((p.1 ∩ p.2).card < k ∨ k + t ≤ (p.1 ∩ p.2).card)).card =
    ∑ a ∈ range (n + 1), if lo ≤ a ∧ a ≤ hi then
      n.choose a * (∑ j ∈ range (a + 1), ∑ b ∈ range (n - a + 1),
        if lo ≤ j + b ∧ j + b ≤ hi ∧ (j < k ∨ k + t ≤ j)
        then a.choose j * (n - a).choose b else 0)
    else 0 := by
  classical
  let row (a : ℕ) := ∑ j ∈ Finset.range (a + 1), ∑ b ∈ Finset.range (n - a + 1),
      if lo ≤ j + b ∧ j + b ≤ hi ∧ (j < k ∨ k + t ≤ j)
      then a.choose j * (n - a).choose b else 0
  let weight (a : ℕ) := if lo ≤ a ∧ a ≤ hi then row a else 0
  calc
    _ = ∑ x : Finset (Fin n), ∑ y : Finset (Fin n),
        (if lo ≤ x.card ∧ x.card ≤ hi ∧ lo ≤ y.card ∧ y.card ≤ hi ∧
          ((x ∩ y).card < k ∨ k + t ≤ (x ∩ y).card) then 1 else 0) := by
      rw [← sum_product']
      simp
    _ = ∑ x : Finset (Fin n), weight x.card := by
      apply sum_congr rfl
      intro x _
      by_cases h : lo ≤ x.card ∧ x.card ≤ hi
      · simpa [weight, h, h.1, h.2, row, ← sum_filter] using card_off_band_row n lo hi k t x
      · by_cases l : lo ≤ x.card
        · have u : ¬x.card ≤ hi := fun hu => h ⟨l, hu⟩
          simp [weight, l, u]
        · simp [weight, l]
    _ = _ := by
      have h := sum_by_size (univ : Finset (Fin n)) weight
      simpa [weight, row, mul_ite] using h

end Cslib
