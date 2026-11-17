/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.BitString
import CslibFrontier.Foundations.Data.BitString.WordsOfLength
import CslibFrontier.Probability.Guessing.Leakage

/-!
# Guessing bounds for uniform bit strings

Bounds the probability of guessing a uniform `n`-bit word from a `d`-bit hint, specializing
`Cslib.Probability.PMF.tsum_mul_apply_le_card_mul` to `BitString.uniformList`.

## Main results

* `Cslib.Probability.PMF.tsum_uniformList_mul_apply_le`: guessing a uniform `n`-bit word `w` from a
  `d`-bit hint `hint w` succeeds with probability at most `(2 : ℝ≥0∞) ^ d * (1 / 2 ^ n)`.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

/-- Guessing a uniform `n`-bit word `w` from a `d`-bit hint `hint w` succeeds with probability at
most `2 ^ d / 2 ^ n` in `ℝ≥0∞`. -/
theorem tsum_uniformList_mul_apply_le {n d : ℕ} (hint : List Bool → List Bool)
    (hhint : ∀ w : List Bool, w.length = n → (hint w).length = d)
    (guess : List Bool → PMF (List Bool)) :
    ∑' w, BitString.uniformList n w * guess (hint w) w ≤ (2 : ℝ≥0∞) ^ d * (1 / 2 ^ n) := by
  let hint' (w : List Bool) : List Bool := if w.length = n then hint w else List.replicate d false
  have hsum :
      ∑' w, BitString.uniformList n w * guess (hint w) w =
        ∑' w, BitString.uniformList n w * guess (hint' w) w := by
    refine tsum_congr fun w => ?_
    by_cases hw : BitString.uniformList n w = 0
    · simp [hw]
    · have hmem : w ∈ (BitString.uniformList n).support := hw
      simp only [hint', BitString.length_of_mem_support_uniformList hmem, ↓reduceIte]
  rw [hsum]
  refine (PMF.tsum_mul_apply_le_card_mul (BitString.uniformList n)
    (BitString.uniformList_apply_le n) hint' (BitString.wordsOfLength d) (fun w => ?_)
    guess).trans ?_
  · dsimp only [hint']
    split_ifs with hw
    · exact BitString.mem_wordsOfLength.mpr (hhint w hw)
    · exact BitString.mem_wordsOfLength.mpr List.length_replicate
  · gcongr
    exact_mod_cast (BitString.card_wordsOfLength d).le

end Cslib.Probability.PMF
