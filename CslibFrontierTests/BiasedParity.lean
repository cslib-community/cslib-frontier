/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.BooleanAnalysis.Noise
import Mathlib.Tactic.NormNum

/-! # Checked clients for Arora–Barak, Exercise 17.1 (corrected)

The parity of the first `k` of `n` biased bits, as in the exercise, and the text's bound
`1/2 + (1 - 2δ)^k` for `0 ≤ δ ≤ 1/2`. -/

set_option linter.privateModule false

open Finset Cslib Cslib.BitString

/-- The exercise's setting: `X_1, …, X_n` independent with `Pr[X_i = 1] = 1 - δ`, and the parity of
`k` of them (the coordinates in `S`). -/
example (n k : ℕ) (S : Finset (Fin n)) (hS : #S = k) (δ : ℝ) :
    bernoulliAverage (1 - δ) (fun x : Fin n → Bool => if parityOn S x then 1 else 0) =
      1 / 2 - (2 * δ - 1) ^ k / 2 := by
  rw [bernoulliAverage_parityOn, hS]

/-- The bound the text uses, for `0 ≤ δ ≤ 1/2`. -/
example (k : ℕ) (δ : ℝ) (hδ : δ ≤ 1 / 2) :
    bernoulliAverage (1 - δ) (fun x : Fin k → Bool => if parityOn univ x then 1 else 0) ≤
      1 / 2 + (1 - 2 * δ) ^ k := by
  have h := parityOn_bernoulliAverage_le δ (univ : Finset (Fin k))
  rw [card_univ, Fintype.card_fin] at h
  have : (0 : ℝ) ≤ (1 - 2 * δ) ^ k := pow_nonneg (by linarith) k
  linarith
