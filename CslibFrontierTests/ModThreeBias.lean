/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Primitives.PRG.ModThreeBias

/-! [Goldreich2007DraftR4], Exercise 8.39: the uniform distribution on the words of weight
divisible by three has exponentially small bias, yet a read-once automaton with three states
distinguishes it from uniform. -/

set_option linter.privateModule false

namespace CslibFrontierTests.ModThreeBias

open Cslib.BitString Cslib.Crypto.PRG Finset
open scoped NNReal

-- The words of four bits of weight divisible by three: weight `0` (one word) and weight `3`
-- (four words).
example : #(modThreeWords 4) = 5 := by decide

-- A `1/1000`-biased distribution on `58` bits that is not `(2, 0.666)`-pseudorandom: small bias,
-- even very small, does not give space-bounded pseudorandomness, the converse of Exercise 8.38.
example : IsSmallBias (1 / 1000) (modThreeGenerator 58).outputDist ∧
    ¬ (modThreeGenerator 58).Secure (IsReadOnceTest (2 ^ 2)) (666 / 1000) := by
  refine ⟨(isSmallBias_modThreeGenerator 58).mono ?_, not_secure_modThreeGenerator (by norm_num)⟩
  rw [show (58 : ℕ) = 2 * 29 from rfl, pow_mul, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

-- At length `10` the gap of the three-state test is already within `1/1000` of `2/3`: the
-- distribution is not even `(2, 1997/3000)`-pseudorandom, `1997/3000 = 2/3 - 1/1000` (width
-- written as `4`).
example : ¬ (modThreeGenerator 10).Secure (IsReadOnceTest 4) (1997 / 3000) := by
  intro h
  have h1 := h _ (isReadOnceTest_modThreeTest 10)
  have h2 := two_div_three_sub_le_advantage_modThreeTest 10
  have h3 : ((1997 / 3000 : ℝ≥0) : ℝ) = 1997 / 3000 := by
    rw [NNReal.coe_div]
    norm_num
  rw [h3] at h1
  norm_num at h2
  linarith

-- Counting ones modulo `m` at chosen positions is a read-once test: here, modulo `5` at the even
-- positions of an `8`-bit word, with `8` states.
example : IsReadOnceTest 8 (fun x : Fin 8 → Bool =>
    PMF.pure (decide (#{i ∈ ({0, 2, 4, 6} : Finset (Fin 8)) | x i = true} % 5 = 2))) :=
  isReadOnceTest_countMod (by norm_num) (by norm_num) _ 2

end CslibFrontierTests.ModThreeBias
