/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Primitives.PRG.ReadOnceBias

/-! [Goldreich2007DraftR4], Exercises 8.37, 8.38 and 8.25(2). Exercise 8.37 and its corollaries in
the printed form for `ε`-bias generators `G : {0,1}^k → {0,1}^ℓ`; the corrected Exercises 8.38
(`2ε`-bias) and 8.25(2) (`ε < 1/2`); and the refutation of the printed versions of the latter two
by the generator `σ ↦ σσ`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SmallBiasStretch

open Cslib.BitString Cslib.Crypto.PRG Cslib.Probability
open scoped NNReal

-- Exercise 8.37, Corollary 1, for `k`-bit seeds: `ℓ(k) < 2^k`.
example {k ℓ : ℕ} {G : (Fin k → Bool) → Fin ℓ → Bool} {ε : ℝ} (hε : ε < 1)
    (hG : IsSmallBias ε ((PMF.uniformOfFintype (Fin k → Bool)).map G)) : ℓ < 2 ^ k := by
  simpa using card_lt_card_of_isSmallBias hε hG

-- With `d = k`, the bound `∑_{i=1}^d C(k,i)` of Exercise 8.37 is `2^k - 1`, Corollary 1.
example (k : ℕ) : ∑ i ∈ Finset.Icc 1 k, k.choose i = 2 ^ k - 1 := by
  rw [← Nat.sum_range_choose, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp [Finset.Ico_add_one_right_eq_Icc]

-- The identity on `k` bits is a `0`-bias generator, so it is not a counterexample to
-- Corollary 2, which needs `ℓ > k`.
example (k : ℕ) : IsSmallBias 0 ((PMF.uniformOfFintype (Fin k → Bool)).map id) := by
  rw [PMF.map_id]
  exact isSmallBias_uniformOfFintype

-- Exercise 8.38 as printed is false.
example : ¬ ∀ (k ℓ s : ℕ) (G : Generator (Fin k → Bool) (Fin ℓ → Bool)) (ε : ℝ≥0), 1 ≤ s →
    G.Secure (IsReadOnceTest (2 ^ s)) ε → IsSmallBias ε G.outputDist := by
  intro h
  obtain ⟨G, hG, hbias⟩ := exists_secure_not_isSmallBias
  exact hbias (by exact_mod_cast h 1 _ 1 G (1 / 2) le_rfl fun A _ => hG A trivial)

-- Exercise 8.25(2) as printed is false.
example : ¬ ∀ (k ℓ s : ℕ) (G : Generator (Fin k → Bool) (Fin ℓ → Bool)) (ε : ℝ≥0), 1 ≤ s →
    (ε : ℝ) < 1 → G.Secure (IsReadOnceTest (2 ^ s)) ε → ℓ < 2 ^ k := by
  intro h
  obtain ⟨G, hG, -⟩ := exists_secure_not_isSmallBias
  exact lt_irrefl _ (h 1 _ 1 G (1 / 2) le_rfl (by norm_num) fun A _ => hG A trivial)

-- The corrected Exercise 8.25(2): `(s, ε)`-pseudorandom with `s ≥ 1`, `ε < 1/2` gives
-- `ℓ(k) < 2^k`; for example, error `1/4` against two-state programs.
example {k ℓ : ℕ} (G : Generator (Fin k → Bool) (Fin ℓ → Bool))
    (hG : G.Secure (IsReadOnceTest (2 ^ 1)) (1 / 4)) : ℓ < 2 ^ k :=
  hG.lt_two_pow le_rfl (by norm_num)

end CslibFrontierTests.SmallBiasStretch
