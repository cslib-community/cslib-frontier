/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.GreedyDesignSize

/-! Checked instance of the size half of Arora–Barak, Lemma 16.18: with `d = 10`, `n = 11` and
`ℓ = 122 > 10 · 11² / 10`, the greedy algorithm gives a `(122, 11, 10)`-design with
`⌈2 ^ (10 / 10)⌉ = 2` blocks. -/

set_option linter.privateModule false

namespace CslibFrontierTests.GreedyDesignSize

open Cslib.Crypto.PRG.NisanWigderson

/-- The hypotheses of Lemma 16.18 at `d = 10`, `n = 11`, `ℓ = 122`. -/
example : 10 * 11 ^ 2 < 122 * 10 := by norm_num

/-- The greedy `(122, 11, 10)`-design with `⌈2 ^ (10 / 10)⌉` blocks. -/
noncomputable example : Design 122 11 10 ⌈(2 : ℝ) ^ ((10 : ℕ) / 10 : ℝ)⌉₊ :=
  Design.greedy 122 11 10 _ (natCeil_rpow_le_length_greedyMasks (by norm_num) (by norm_num))

/-- The design has two blocks. -/
example : ⌈(2 : ℝ) ^ ((10 : ℕ) / 10 : ℝ)⌉₊ = 2 := by norm_num

end CslibFrontierTests.GreedyDesignSize
