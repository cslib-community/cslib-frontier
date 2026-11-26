/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Finset.KthLargest

/-!
# Upper truncation of zero-padded order statistics

Capping every value at a nonnegative threshold caps the positive-order `k`-th largest value
at the same threshold. Nonnegativity of the cap preserves the zero padding. Input values may
be negative, and the retained cardinality may be smaller than the requested rank.

## Main results

* `Finset.kthLargest_min`: upper truncation commutes with the padded order statistic.
-/

public section

namespace Finset

variable {α R : Type*} [LinearOrder R] [Zero R] {s : Finset α} {k : ℕ} {f : α → R} {t : R}

/-- An upper cap that preserves zero commutes with every positive-order padded rank. -/
theorem kthLargest_min (hk : 0 < k) (ht : 0 ≤ t) :
    kthLargest k s (fun x => min t (f x)) = min t (kthLargest k s f) := by
  classical
  refine le_antisymm (le_min (kthLargest_le ht fun _ _ => min_le_left _ _)
    (not_lt.mp fun hlt => ?_)) ?_
  · refine lt_irrefl (kthLargest k s f) ((lt_kthLargest_iff hk kthLargest_nonneg).mpr
      (((lt_kthLargest_iff hk kthLargest_nonneg).mp hlt).trans (card_le_card fun x hx => ?_)))
    exact mem_filter.mpr ⟨(mem_filter.mp hx).1, (mem_filter.mp hx).2.trans_le (min_le_right _ _)⟩
  · rcases le_or_gt (min t (kthLargest k s f)) 0 with hzero | hpos
    · exact hzero.trans kthLargest_nonneg
    exact (le_kthLargest_iff hk hpos).mpr
      (((le_kthLargest_iff hk hpos).mp (min_le_right _ _)).trans (card_le_card fun x hx =>
        mem_filter.mpr ⟨(mem_filter.mp hx).1, le_min (min_le_left _ _) (mem_filter.mp hx).2⟩))

end Finset
