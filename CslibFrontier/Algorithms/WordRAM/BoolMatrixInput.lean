/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Defs
import Mathlib.Tactic.Linarith

/-!
# Flat row-major Boolean matrix input bounds

Shared `InputFits` helper for Word-RAM programs whose input list is `[n]` followed by the
row-major `n × n` `0`/`1` adjacency matrix of a Boolean relation `adj : Fin n → Fin n → Bool`.
-/

public section

namespace Cslib.Algorithms.WordRAM

open Cslib.WordRAM

/-- A row-major Boolean matrix encoding
`n :: flatMap (fun u => ofFn (fun v => if adj u v then 1 else 0))` satisfies `InputFits w`
whenever `w` fits `n * n + 1`, `n`, and `1`. -/
theorem inputFits_boolMatrix {n B w : ℕ} (adj : Fin n → Fin n → Bool) (hw : Fits w B)
    (hlen_le : n * n + 1 ≤ B) (hn_le : n ≤ B) (h1_le : 1 ≤ B) :
    InputFits w (n :: (List.finRange n).flatMap fun u =>
      List.ofFn fun v => if adj u v then 1 else 0) := by
  refine ⟨hw.of_le (by simp [List.length_flatMap]; omega), fun x hx => ?_⟩
  simp only [List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and, List.mem_ofFn] at hx
  rcases hx with rfl | ⟨_, _, rfl⟩
  · exact hw.of_le hn_le
  · split_ifs
    · exact hw.of_le h1_le
    · exact fits_zero w

end Cslib.Algorithms.WordRAM
