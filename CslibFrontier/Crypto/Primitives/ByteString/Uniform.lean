/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.ByteString
public import CslibFrontier.Probability.PMF.UniformPoint

/-!
# Uniform sampling of fixed-length byte strings

An observation which is true at most once on an `n`-byte space succeeds with probability
at most `2^(-8n)` on a uniformly random string.
-/

public section

namespace Cslib.Crypto.FixedBytes
open Cslib.Probability
open scoped ENNReal

/-- There are `2^(8n)` strings of exactly `n` bytes. -/
theorem card (n : ℕ) : Fintype.card (FixedBytes n) = 2 ^ (8 * n) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]

/-- A test accepting at most one uniform byte string has success at most `2^(-8n)`. -/
theorem uniform_test_le {n : ℕ} {win : FixedBytes n → Bool}
    (unique : {x | win x = true}.Subsingleton) :
    ((PMF.uniformOfFintype (FixedBytes n)).map win) true ≤ (2 ^ (8 * n) : ℝ≥0∞)⁻¹ := by
  simpa only [PMF.map, Function.comp_def, FixedBytes.card, Nat.cast_pow, Nat.cast_ofNat] using
    PMF.uniformOfFintype_bind_pure_apply_true_le unique

end Cslib.Crypto.FixedBytes
