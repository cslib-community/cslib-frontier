/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.ExponentialDesign

/-! Checked client of Goldreich Exercise 8.19: the exponential-time set system for `γ = 1 / 4`,
and the explicit system `expDesign 2` at `k = 41 = 10 · 2² + 1`, where `t = 1`: two sets of
`2` elements of `[41]` sharing at most `1`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.ExponentialDesign

open Cslib.Crypto.PRG.NisanWigderson Finset Turing.MultiTapeTM

example : ∃ (S : ℕ × ℕ → List Bool) (ℓ m : ℕ → ℕ) (δ c : ℝ) (k₀ : ℕ),
    Cslib.Complexity.ComputableInExpTime S (encPair encUnary encNat) encBits (fun p => p.1) δ ∧
    (∀ k i, i < ℓ k → (S (k, i)).length = k ∧ #(maskBlock k (S (k, i))) = m k) ∧
    (∀ k i j, i < ℓ k → j < ℓ k → i ≠ j →
      (#(maskBlock k (S (k, i)) ∩ maskBlock k (S (k, j))) : ℝ) ≤ 1 / 4 * m k) ∧
    0 < c ∧ ∀ k ≥ k₀, c * k ≤ m k ∧ (2 : ℝ) ^ (c * k) ≤ ℓ k :=
  exists_computableInExpTime_design (by norm_num)

example : #(maskBlock 41 (expDesign 2 41 3)) = 2 :=
  card_maskBlock_expDesign le_rfl le_rfl (by norm_num)

example : #(maskBlock 41 (expDesign 2 41 0) ∩ maskBlock 41 (expDesign 2 41 3)) ≤ 1 :=
  card_maskBlock_inter_expDesign_le le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num)

end CslibFrontierTests.ExponentialDesign
