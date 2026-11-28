/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.TSP.Symmetric
import Mathlib.Tactic.IntervalCases

/-! Checked instances of the symmetric traveling salesperson problem of Arora–Barak, Example 2.2
(`Cslib.Complexity.SymTSP`): a three-city triangle with distances `1, 2, 3` (the lower triangle
`[[], [1], [2, 3]]`) has a tour of length `6` and none shorter, so it is a yes-instance with budget
`6` and a no-instance with budget `5`; and the full matrix written by `SymTSP.toTSP` is symmetric
with zero diagonal. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SymmetricTSP

open Cslib.Complexity

example : SymTSP.toMatrix [[], [1], [2, 3]] = [[0, 1, 2], [1, 0, 3], [2, 3, 0]] := by decide

example : (⟨[[], [1], [2, 3]], 6⟩ : SymTSPInstance) ∈ SymTSP :=
  ⟨[0, 1, 2], List.Perm.refl _, by decide⟩

example : (⟨[[], [1], [2, 3]], 5⟩ : SymTSPInstance) ∉ SymTSP := by
  rintro ⟨p, hp, hle⟩
  -- Every tour of a triangle uses all three edges.
  have h : SymTSP.tourLength [[], [1], [2, 3]] p = 6 := by
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c, p = [a, b, c] := by
      match p, hp.length_eq with
      | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
    have ha : a < 3 := List.mem_range.1 (hp.subset (by simp))
    have hb : b < 3 := List.mem_range.1 (hp.subset (by simp))
    have hc : c < 3 := List.mem_range.1 (hp.subset (by simp))
    have hnd := hp.nodup_iff.2 List.nodup_range
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    interval_cases a <;> interval_cases b <;> interval_cases c <;> first | omega | decide
  change SymTSP.tourLength [[], [1], [2, 3]] p ≤ 5 at hle
  omega

example : NPComplete encSymTSP SymTSP := SymTSP_npComplete

end CslibFrontierTests.SymmetricTSP
