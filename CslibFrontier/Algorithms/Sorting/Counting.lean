/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Stable counting-sort positions

## Main definitions

* `CountingSort.position`: stable scatter position of an original occurrence.

## Main results

* `CountingSort.count_lt_succ`: the prefix-sum update used by a native counting pass.
* `CountingSort.sum_count_eq_count_lt`: the bucket counts below `T` sum to the prefix count.
* `CountingSort.position_injective`: every original position has a distinct destination.
* `CountingSort.position_bijective`: scatter destinations form a permutation of the input.
* `CountingSort.scatter_span_image`: an actual scattered array's bucket span has exactly
  the values whose original keys select that bucket.

These finite counting identities are original supporting mathematics for the native router.
They reuse Mathlib's `Nat.count` and its prefix-count APIs directly; only the stable-scatter
construction and cross-bucket theory are added. They assert no program or execution cost.
-/

@[expose] public section

namespace Cslib.Algorithms.CountingSort

open Finset

/-- The stable destination of original position `i` in an input of length `n`. -/
def position (key : ℕ → ℕ) (n i : ℕ) : ℕ :=
  Nat.count (fun k => key k < key i) n + Nat.count (fun k => key k = key i) i

/-- Larger keys start no earlier. -/
private theorem offset_mono (key : ℕ → ℕ) (n : ℕ) {b c : ℕ} (h : b ≤ c) :
    Nat.count (fun k => key k < b) n ≤ Nat.count (fun k => key k < c) n :=
  Nat.count_mono_left fun _ _ hk => hk.trans_le h

/-- One prefix-sum step appends exactly the current bucket's cardinality. -/
theorem count_lt_succ (key : ℕ → ℕ) (n b : ℕ) :
    Nat.count (fun k => key k < b + 1) n =
      Nat.count (fun k => key k < b) n + Nat.count (fun k => key k = b) n := by
  simp only [Nat.count_eq_card_filter_range, Nat.lt_succ_iff_lt_or_eq, filter_or]
  exact card_union_of_disjoint (disjoint_filter.mpr fun _ _ => ne_of_lt)

/-- The bucket counts below `T` sum to the number of positions whose key is below `T`. -/
theorem sum_count_eq_count_lt (key : ℕ → ℕ) (n T : ℕ) :
    ∑ b ∈ range T, Nat.count (fun i => key i = b) n = Nat.count (fun i => key i < T) n := by
  induction T with
  | zero => simp
  | succ T ih => rw [sum_range_succ, ih, count_lt_succ]

/-- Each occurrence lands before the next bucket, and after its own bucket's start. -/
theorem position_mem (key : ℕ → ℕ) {n i : ℕ} (hi : i < n) :
    Nat.count (fun k => key k < key i) n ≤ position key n i ∧
      position key n i < Nat.count (fun k => key k < key i + 1) n := by
  have := Nat.count_strict_mono (p := fun j => key j = key i) rfl hi
  rw [count_lt_succ]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ‹_› _⟩

/-- Stable scatter destinations are valid original-length indices. -/
theorem position_lt (key : ℕ → ℕ) {n i : ℕ} (hi : i < n) : position key n i < n :=
  (position_mem key hi).2.trans_le (Nat.count_le _)

/-- Original order is retained inside a bucket. -/
theorem position_lt_same (key : ℕ → ℕ) (n : ℕ) {i j : ℕ} (hij : i < j)
    (hkey : key i = key j) : position key n i < position key n j := by
  have := Nat.count_strict_mono (p := fun j => key j = key i) rfl hij
  simp only [position, hkey] at *
  omega

/-- Every position in a smaller bucket precedes every position in a larger bucket. -/
theorem position_lt_key (key : ℕ → ℕ) {n i j : ℕ} (hi : i < n)
    (hkey : key i < key j) : position key n i < position key n j :=
  ((position_mem key hi).2.trans_le
    (offset_mono key n (Nat.succ_le_of_lt hkey))).trans_le (Nat.le_add_right _ _)

/-- Distinct original positions never overwrite one another during stable scatter. -/
theorem position_injective (key : ℕ → ℕ) (n : ℕ) :
    Function.Injective (fun i : Fin n => position key n i.val) := by
  intro i j he
  change position key n i.val = position key n j.val at he
  rcases lt_trichotomy (key i) (key j) with hk | hk | hk
  · have := position_lt_key key i.isLt hk
    omega
  · rcases lt_trichotomy i.val j.val with hij | hij | hij
    · have := position_lt_same key n hij hk
      omega
    · exact Fin.ext hij
    · have := position_lt_same key n hij hk.symm
      omega
  · have := position_lt_key key j.isLt hk
    omega

/-- All original occurrences, including equal keys, are a permutation of the output cells. -/
theorem position_bijective (key : ℕ → ℕ) (n : ℕ) :
    Function.Bijective (fun i : Fin n =>
      (⟨position key n i.val, position_lt key i.isLt⟩ : Fin n)) := by
  have hi : Function.Injective (fun i : Fin n =>
      (⟨position key n i.val, position_lt key i.isLt⟩ : Fin n)) :=
    fun i j h => position_injective key n (congrArg (fun j : Fin n => j.val) h)
  exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- A stable destination belongs to a bucket's half-open span exactly when its key is that
bucket. Equal values or repeated original requests do not change the interval criterion. -/
theorem position_mem_iff (key : ℕ → ℕ) {n i : ℕ} (hi : i < n) (b : ℕ) :
    (Nat.count (fun k => key k < b) n ≤ position key n i ∧
      position key n i < Nat.count (fun k => key k < b + 1) n) ↔
      key i = b := by
  refine ⟨fun h => ?_, fun h => h ▸ position_mem key hi⟩
  rcases lt_trichotomy (key i) b with hb | rfl | hb
  · have := (position_mem key hi).2.trans_le (offset_mono key n (Nat.succ_le_of_lt hb))
    omega
  · rfl
  · have : Nat.count (fun k => key k < b + 1) n ≤ position key n i :=
      (offset_mono key n (Nat.succ_le_of_lt hb)).trans (position_mem key hi).1
    omega

/-- A memory array satisfying the stable-scatter equations has precisely the original
values selected by each bucket. No sorted list or permutation certificate is a premise. -/
theorem scatter_span_image {α : Type*} [DecidableEq α] (key : ℕ → ℕ) (n b : ℕ)
    (stored values : ℕ → α) (h : ∀ i < n, stored (position key n i) = values i) :
    (Ico (Nat.count (fun k => key k < b) n) (Nat.count (fun k => key k < b + 1) n)).image stored =
      ((range n).filter fun i => key i = b).image values := by
  ext v
  simp only [mem_image, mem_Ico, mem_filter, mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨i, hi⟩ := (position_bijective key n).surjective ⟨j, hj.2.trans_le (Nat.count_le _)⟩
    have hpos : position key n i.val = j := congrArg Fin.val hi
    exact ⟨i.val, ⟨i.isLt, (position_mem_iff key i.isLt b).mp (hpos ▸ hj)⟩,
      (h i.val i.isLt).symm.trans (congrArg stored hpos)⟩
  · rintro ⟨i, ⟨hlt, hik⟩, rfl⟩
    exact ⟨position key n i, (position_mem_iff key hlt b).mpr hik, h i hlt⟩

end Cslib.Algorithms.CountingSort
