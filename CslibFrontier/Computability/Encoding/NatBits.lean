/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Encoding.Basic
public import Mathlib.Data.Nat.Bits

/-!
# Binary encoding and natural-number digits

The shared binary encoding uses Mathlib's `Num` implementation. `encNat_eq_bits` lets
arithmetic clients use the `Nat.bits` equations without choosing another encoding.
-/

public section

namespace Cslib.Encoding

private theorem encodePosNum_eq_bits (n : PosNum) :
    Computability.encodePosNum n = (n : ℕ).bits := by
  induction n with
  | one => rfl
  | bit0 n ih =>
    rw [PosNum.cast_bit0, ← two_mul, Nat.bit0_bits _ (Nat.ne_of_gt n.to_nat_pos)]
    exact congrArg (false :: ·) ih
  | bit1 n ih =>
    rw [PosNum.cast_bit1, ← two_mul, Nat.bit1_bits]
    exact congrArg (true :: ·) ih

/-- Mathlib's binary encoding and `Nat.bits` give exactly the same little-endian word. -/
theorem encNat_eq_bits (n : ℕ) : encNat n = n.bits := by
  have h : ∀ k : Num, Computability.encodeNum k = (k : ℕ).bits := by
    intro k
    cases k with
    | zero => rfl
    | pos k => exact encodePosNum_eq_bits k
  exact (h (n : Num)).trans (congrArg Nat.bits (Num.to_of_nat n))

end Cslib.Encoding
