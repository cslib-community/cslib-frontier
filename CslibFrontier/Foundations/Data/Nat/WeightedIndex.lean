/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Selecting a column by its natural weight

The columns of a row receive consecutive intervals of natural labels, of lengths given by their
weights. Subtracting each weight from the remaining label finds the column containing it. A label
outside every interval returns the row width. This also handles zero weights and empty rows.

## Main definitions

* `Cslib.scanWeightedRow` selects the column containing a natural label.

## Main results

* `Cslib.scanWeightedRow_spec` bounds the returned column and its prefix weight.
* `Cslib.scanWeightedRow_eq_iff` characterizes each real column by its half-open interval.
-/

public section

namespace Cslib

open Finset

/-- The column containing `label` in the consecutive intervals of lengths `weight 0` through
`weight (n - 1)`, or `n` when all intervals have been exhausted. -/
@[expose] def scanWeightedRow : (n : ℕ) → (ℕ → ℕ) → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, weight, label =>
    if label < weight 0 then 0
    else scanWeightedRow n (fun i => weight (i + 1)) (label - weight 0) + 1

/-- The returned column is at most the width. Its prefix weight fits the label, and if this is
a real column its interval reaches strictly beyond the label. -/
theorem scanWeightedRow_spec (n : ℕ) (weight : ℕ → ℕ) (label : ℕ) :
    let j := scanWeightedRow n weight label
    j ≤ n ∧ ∑ i ∈ range j, weight i ≤ label ∧
      (j < n → label < ∑ i ∈ range (j + 1), weight i) := by
  induction n generalizing label weight with
  | zero => simp [scanWeightedRow]
  | succ n ih =>
    simp only [scanWeightedRow]
    split_ifs with h
    · simp [h]
    · obtain ⟨hle, hp, hq⟩ := ih (fun i => weight (i + 1)) (label - weight 0)
      refine ⟨Nat.succ_le_succ hle, ?_, fun hj => ?_⟩
      · rw [sum_range_succ']
        omega
      · have := hq (Nat.lt_of_succ_lt_succ hj)
        rw [sum_range_succ']
        omega

/-- A label selects column `j < n` exactly on the half-open interval starting at the prefix
weight of the first `j` columns. -/
theorem scanWeightedRow_eq_iff {n j : ℕ} (hj : j < n) (weight : ℕ → ℕ) (label : ℕ) :
    scanWeightedRow n weight label = j ↔
      (∑ i ∈ range j, weight i) ≤ label ∧ label < (∑ i ∈ range j, weight i) + weight j := by
  let dest := scanWeightedRow n weight label
  obtain ⟨hle, hlo, hhi⟩ := scanWeightedRow_spec n weight label
  change dest ≤ n at hle
  change (∑ i ∈ range dest, weight i) ≤ label at hlo
  change dest < n → label < (∑ i ∈ range (dest + 1), weight i) at hhi
  change dest = j ↔ _
  rw [← sum_range_succ]
  constructor
  · rintro rfl
    exact ⟨hlo, hhi hj⟩
  · rintro ⟨ha, hb⟩
    have hmono : Monotone fun k => ∑ i ∈ range k, weight i :=
      fun _ _ h => sum_mono_set _ (range_mono h)
    rcases lt_trichotomy dest j with h | h | h
    · exact False.elim ((hhi (h.trans hj)).not_ge ((hmono h).trans ha))
    · exact h
    · exact False.elim (hb.not_ge ((hmono h).trans hlo))

end Cslib
