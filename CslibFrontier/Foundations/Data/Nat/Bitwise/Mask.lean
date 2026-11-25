/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Lean core, beside `Nat.and_lt_two_pow` in
-- `Init/Data/Nat/Bitwise/Lemmas.lean`)

public import CslibFrontier.Init

/-!
# Low-bit masks

Masking a natural number with `2 ^ n - 1` keeps its low `n` bits, so the result is below `2 ^ n`
(`Nat.and_two_pow_sub_one_lt`). Core's `Nat.and_two_pow_sub_one_eq_mod` identifies the masked
value with `a % 2 ^ n`; this is the bound callers use to show a masked field fits in `n` bits.
-/

public section

namespace Nat

/-- Masking with `2 ^ n - 1` gives a value below `2 ^ n`. -/
theorem and_two_pow_sub_one_lt (a n : ℕ) : a &&& (2 ^ n - 1) < 2 ^ n :=
  Nat.and_lt_two_pow a (Nat.sub_lt (Nat.two_pow_pos n) Nat.one_pos)

end Nat
