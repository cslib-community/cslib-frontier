/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Basic

/-!
# Segmented propagation of Boolean sources

Each position contributes a source bit. A true link carries the previous value forward;
a false link starts a new segment. The value of a prefix is true precisely when it contains
a true source connected to the end by uninterrupted true links. The link at the source itself
is irrelevant, including the first link.

## Main definitions

* `Cslib.BitString.propagate`: the source/link recurrence, initialized with false.
* `Cslib.BitString.keyLinks`: link adjacent equal keys.

## Main results

* `Cslib.BitString.propagate_eq_true_iff`: characterization by a connected true source.
* `Cslib.BitString.propagate_sorted_eq_true_iff`: on sorted keys, the output is the OR of
  the sources in the equal-key run ending at the last processed record.

## References

* Adapted from MassProduction/Nonuniform/{Propagation,SortedPropagation}.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.BitString

/-- The propagated value after processing a prefix, starting with false. -/
def propagate (source link : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | count + 1 => source count || (link count && propagate source link count)

/-- Propagation depends only on the source and link bits in its processed prefix. -/
theorem propagate_congr {source source' link link' : ℕ → Bool} (count : ℕ)
    (hs : ∀ i, i < count → source i = source' i)
    (hl : ∀ i, i < count → link i = link' i) :
    propagate source link count = propagate source' link' count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [propagate, propagate, hs count (by lia), hl count (by lia),
      ih (fun i hi => hs i (by lia)) (fun i hi => hl i (by lia))]

/-- A true value has a true source connected to the end by uninterrupted true links. -/
theorem propagate_eq_true_iff (source link : ℕ → Bool) (count : ℕ) :
    propagate source link count = true ↔
      ∃ start, start < count ∧ source start = true ∧
        ∀ index, start < index → index < count → link index = true := by
  induction count with
  | zero => simp [propagate]
  | succ count ih =>
    simp only [propagate, Bool.or_eq_true, Bool.and_eq_true, ih]
    refine ⟨?_, fun ⟨s, hs, hst, hl⟩ => ?_⟩
    · rintro (last | ⟨linked, s, hs, hst, hl⟩)
      · refine ⟨count, by omega, last, fun _ lo hi => ?_⟩
        omega
      · refine ⟨s, by omega, hst, fun idx lo hi => ?_⟩
        exact if h : idx = count then h ▸ linked else hl idx lo (by omega)
    · by_cases h : s = count
      · exact Or.inl (h ▸ hst)
      · refine Or.inr ⟨hl count (by omega) (by omega), s, by omega, hst, fun i lo hi => ?_⟩
        exact hl i lo (by omega)

/-- Adjacent records are linked precisely when their keys agree; the first link is false. -/
def keyLinks {κ : Type*} [DecidableEq κ] (key : ℕ → κ) (index : ℕ) : Bool :=
  if index = 0 then false else decide (key (index - 1) = key index)

/-- In a sorted prefix, propagation reports exactly the true sources having the last key.
The prefix may be empty. No uniqueness of sources or keys is required, and no order is
required beyond the prefix. The explicit equality instance retains the caller's executable
equality test when it differs from the one inherited from the order. -/
theorem propagate_sorted_eq_true_iff {κ : Type*} [LinearOrder κ] [DecidableEq κ]
    (key : ℕ → κ) (source : ℕ → Bool) (count : ℕ)
    (sorted : MonotoneOn key (Set.Iio count)) :
    propagate source (keyLinks key) count = true ↔
      ∃ start, start < count ∧ source start = true ∧ key start = key (count - 1) := by
  rw [propagate_eq_true_iff]
  refine ⟨?_, fun ⟨s, hs, hst, hkey⟩ => ⟨s, hs, hst, fun idx lo hi => ?_⟩⟩
  · rintro ⟨s, hs, hst, hl⟩
    have conn : ∀ idx, s ≤ idx → idx < count → key s = key idx := fun idx hle => by
      induction idx, hle using Nat.le_induction with
      | base => exact fun _ => rfl
      | succ idx _ ih =>
        intro hb
        have hadj : key idx = key (idx + 1) := by
          simpa [keyLinks] using hl (idx + 1) (by omega) hb
        exact (ih (by omega)).trans hadj
    exact ⟨s, hs, hst, conn (count - 1) (by omega) (by omega)⟩
  · have hnz : idx ≠ 0 := by omega
    simp only [keyLinks, ite_eq_right hnz, decide_eq_true_eq]
    have hprev : idx - 1 < count := by omega
    have hlast : count - 1 < count := by omega
    have hle1 : key (idx - 1) ≤ key idx := sorted hprev hi (by omega)
    have hle2 : key idx ≤ key (count - 1) := sorted hi hlast (by omega)
    have hle3 : key s ≤ key (idx - 1) := sorted hs hprev (by omega)
    exact le_antisymm hle1 (hle2.trans (hkey.symm.le.trans hle3))

end Cslib.BitString
