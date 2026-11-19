/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Real.Basic

/-!
# Zero in an open real segment

`Cslib.zero_mem_openSegment_iff_xor_pos` characterizes zero between two nonzero
real endpoints by their opposite signs. The original scalar proof is shared by
parabola-chord intersections and straight-observation parity.
-/

public section

namespace Cslib

/-- Zero belongs to the open segment between nonzero real endpoints exactly when
precisely one endpoint is positive. Equal nonzero endpoints are included. -/
theorem zero_mem_openSegment_iff_xor_pos {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    0 ∈ openSegment ℝ u v ↔ Xor (0 < u) (0 < v) := by
  have ordered {s t : ℝ} (hst : s ≤ t) (hs : s ≠ 0) :
      0 ∈ openSegment ℝ s t ↔ Xor (0 < s) (0 < t) := by
    by_cases he : s = t
    · subst t
      simp [openSegment_same, Xor, hs.symm]
    · rw [openSegment_eq_Ioo (lt_of_le_of_ne hst he)]
      constructor
      · intro h
        exact Or.inr ⟨h.2, not_lt_of_ge h.1.le⟩
      · rintro (⟨h, hnot⟩ | ⟨h, hnot⟩)
        · exact False.elim (hnot (h.trans_le hst))
        · exact ⟨lt_of_le_of_ne (le_of_not_gt hnot) hs, h⟩
  rcases le_total u v with huv | huv
  · exact ordered huv hu
  · rw [openSegment_symm, xor_comm (0 < u) (0 < v)]
    exact ordered huv hv

end Cslib
