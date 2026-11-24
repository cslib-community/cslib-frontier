/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Data.Code.RandomLinear

/-! Checked clients of Goldreich, Proposition E.1 (draft `r6.pdf`): the eventual form of the
source, and a satisfiable instance of its hypotheses. -/

set_option linter.privateModule false

namespace CslibFrontierTests.GoldreichRandomLinearCode

open Cslib.Code Real Filter

/-- The eventual form in the source: if `(E.1)` holds for all large `k`, then for all large `k` a
random `k`-by-`n(k)` generating matrix gives distance `d(k)` with probability above
`1 - 2^(-t(k))`. -/
example (n d t : ℕ → ℕ)
    (h : ∀ᶠ k in atTop, 2 * d k ≤ n k ∧
      (k + t k : ℝ) ≤ n k * (1 - binEntropy (d k / n k) / log 2)) :
    ∀ᶠ k in atTop, 1 - (1 / 2 : ℝ) ^ t k <
      (Finset.card {G : Matrix (Fin k) (Fin (n k)) (ZMod 2) |
          ∀ x y, x ≠ y → d k ≤ hammingDist (Matrix.vecMul x G) (Matrix.vecMul y G)}) /
        Fintype.card (Matrix (Fin k) (Fin (n k)) (ZMod 2)) :=
  h.mono fun _ hk => one_sub_inv_two_pow_lt_card_filter_le_hammingDist hk.1 hk.2

/-- The hypotheses are satisfiable: distance `0` at length `k + t`, where `H₂(0) = 0`. -/
example (k t : ℕ) : 1 - (1 / 2 : ℝ) ^ t <
    (Finset.card {G : Matrix (Fin k) (Fin (k + t)) (ZMod 2) |
        ∀ x y, x ≠ y → 0 ≤ hammingDist (Matrix.vecMul x G) (Matrix.vecMul y G)}) /
      Fintype.card (Matrix (Fin k) (Fin (k + t)) (ZMod 2)) :=
  one_sub_inv_two_pow_lt_card_filter_le_hammingDist (by omega) (by simp)

end CslibFrontierTests.GoldreichRandomLinearCode
