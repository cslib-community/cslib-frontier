/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.BinPacking.HarmonicLimit
import Mathlib.Tactic.NormNum

/-!
# Harmonic_k: examples

These kernel-checked examples (using no `native_decide`) exercise
`CslibFrontier.Algorithms.Lean.BinPacking.Harmonic` and
`CslibFrontier.Algorithms.Lean.BinPacking.HarmonicLimit`:

1. The classes at their boundaries: with `k = 3` and `C = 24`, sizes `12` and `13` are of classes
   `2` and `1`, and sizes `8` and `9` of classes `3` and `2`.
2. The packing rule. Items of class `2` go two to a bin. An item of class `k` does not join a bin
   of another class even when it fits, and goes into the most recently opened bin of class `k`,
   as in Next Fit, not into the first bin with room, as in First Fit.
3. A run of Harmonic_3 on four copies of `[13, 9, 1, 1]` with `C = 24`. The optimum is `4` bins,
   one per copy; Harmonic_3 uses `7 = T₃ * 4` bins, so it attains the ratio `T₃ = 7/4` on this
   input. The bounds `length_run_harmonicPacker_le` and
   `length_run_harmonicPacker_le_harmonicLimit` instantiated on it.
4. Lee and Lee's constants `T₂, …, T₇` and `T₁₂`, Sylvester's numbers, and `T∞ ≤ T₃`.
-/

public section

namespace CslibFrontierTests.BinPackingHarmonic

open Cslib.Algorithms.Lean.BinPacking

/-! ### 1. Classes -/

example : (harmonicClass 3 24 12, harmonicClass 3 24 13) = (2, 1) := by decide
example : (harmonicClass 3 24 8, harmonicClass 3 24 9) = (3, 2) := by decide
/-- An item of size `0` is of class `k`. -/
example : harmonicClass 3 24 0 = 3 := by decide

/-! ### 2. The packing rule -/

/-- Items of class `2` (sizes in `(4, 6]` for `C = 12`) go two to a bin. -/
example : (harmonicPacker 3 12).run [5, 6, 5] = [[5, 6], [5]] := by decide

/-- An item of class `3` does not join a bin of class `2`, though it fits. -/
example : (harmonicPacker 3 12).run [5, 5, 1] = [[5, 5], [1]] := by decide

/-- Items of class `k` are packed by Next Fit: the `4` joins the bin of the `5`, the last bin of
class `k`, not the earlier bin `[3, 3]` with room for it. -/
example : (harmonicPacker 2 10).run [3, 3, 5, 4] = [[3, 3], [5, 4]] := by decide

/-- First Fit puts the `4` into the first bin. -/
example : (firstFitPacker 10).run [3, 3, 5, 4] = [[3, 3, 4], [5]] := by
  rw [run_firstFitPacker]; decide

/-! ### 3. A run of Harmonic_3 -/

/-- Four copies of an item of each of the classes `1` and `2` and two items of class `3`. -/
abbrev items : List ℕ := [13, 9, 1, 1, 13, 9, 1, 1, 13, 9, 1, 1, 13, 9, 1, 1]

example : (harmonicPacker 3 24).run items =
    [[13], [9, 9], [1, 1, 1, 1, 1, 1, 1, 1], [13], [13], [9, 9], [13]] := by decide

example : ((harmonicPacker 3 24).run items).length = 7 := by decide

/-- An optimal packing: one full bin per copy. -/
theorem isPacking_opt : IsPacking 24 items (List.replicate 4 [13, 9, 1, 1]) :=
  ⟨by decide, by decide⟩

/-- No packing of the items uses fewer than `4` bins, as they fill `4` bins exactly. -/
example (Q : List (List ℕ)) (hQ : IsPacking 24 items Q) : 4 ≤ Q.length := by
  have := hQ.sum_le_mul_length
  simp only [items, List.sum_cons, List.sum_nil] at this
  omega

example : harmonicRatio 3 = 7 / 4 := by norm_num [harmonicRatio, harmonicTail, sylvester]

/-- The bound `T₃ * OPT + 3` on this input. -/
example : (((harmonicPacker 3 24).run items).length : ℚ) ≤ harmonicRatio 3 * 4 + 3 := by
  have := length_run_harmonicPacker_le (k := 3) (by norm_num) isPacking_opt
  simpa only [List.length_replicate, Nat.cast_ofNat] using this

/-- The bound `(T∞ + 1/6) * OPT + 3` on this input. -/
example : (((harmonicPacker 3 24).run items).length : ℝ) ≤
    (harmonicLimit + 1 / (3 * (3 - 1))) * 4 + 3 := by
  have := length_run_harmonicPacker_le_harmonicLimit (k := 3) (by norm_num) isPacking_opt
  simpa only [List.length_replicate, Nat.cast_ofNat] using this

/-! ### 4. Lee and Lee's constants -/

example : harmonicRatio 2 = 2 := by norm_num [harmonicRatio, harmonicTail, sylvester]
example : harmonicRatio 4 = 31 / 18 := by norm_num [harmonicRatio, harmonicTail, sylvester]
example : harmonicRatio 5 = 41 / 24 := by norm_num [harmonicRatio, harmonicTail, sylvester]
example : harmonicRatio 6 = 17 / 10 := by norm_num [harmonicRatio, harmonicTail, sylvester]
example : harmonicRatio 7 = 61 / 36 := by norm_num [harmonicRatio, harmonicTail, sylvester]
example : harmonicRatio 12 = 391 / 231 := by norm_num [harmonicRatio, harmonicTail, sylvester]

example : (List.range 5).map sylvester = [2, 3, 7, 43, 1807] := by decide

/-- `T∞ ≤ T₃ = 7/4`. -/
example : harmonicLimit ≤ 7 / 4 := by
  have h := harmonicLimit_le_harmonicRatio (k := 3) (by norm_num)
  rw [show harmonicRatio 3 = 7 / 4 by norm_num [harmonicRatio, harmonicTail, sylvester]] at h
  norm_num at h
  exact h

end CslibFrontierTests.BinPackingHarmonic
