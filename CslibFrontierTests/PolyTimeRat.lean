/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import Mathlib.Tactic.FailIfNoProgress

/-!
# Polynomial-time rational arithmetic and natural-number casts

Concrete encodings, `fun_prop` composition checks for binary natural casts into `ℚ`, unary natural
casts into `ℤ`, rational field operations, unary powers, comparisons, floor, and the boundary check
that `rat_pow` rejects binary-encoded exponents.
-/

namespace CslibFrontierTests.PolyTimeRat

open Turing MultiTapeTM ComputableInPolyTime

/-! ### Concrete codes and normalized values -/

example : encRat (0 : ℚ) = encPair encIntBin encNat (0, 1) := rfl
example : encRat (-3 / 2 : ℚ) = encPair encIntBin encNat (-3, 2) := by decide +kernel
example : Rat.divInt (-6) 0 = 0 ∧ ((-3 / 2 : ℚ) ^ 3).num = -27 ∧
    ((-3 / 2 : ℚ) ^ 3).den = 8 ∧ (-3 / 2 : ℚ).floor = -2 := by
  decide +kernel

/-! ### Composed `fun_prop` certificates -/

-- Binary natural casts into `ℚ` and unary powers compose with field operations.
example : ComputableInPolyTime
    (fun p : ℕ × ℚ => (p.1 : ℚ) ^ 2 * p.2 - ((p.1 + 1 : ℕ) : ℚ)⁻¹)
    (encPair encNat encRat) encRat := by
  fun_prop

-- Runtime unary exponents on `ℚ` compose with `Rat.floor` and unary casts into `ℤ`.
example : ComputableInPolyTime
    (fun p : ℕ × ℚ => (p.2 ^ (2 * p.1 + 1)).floor + (p.1 : ℤ))
    (encPair encUnary encRat) encIntBin := by
  fun_prop

-- Numerator, denominator, zero/order/equality tests, and `Rat.divInt` compose cleanly.
example : ComputableInPolyTime
    (fun p : ℤ × ℚ =>
      decide (Rat.divInt (-p.1) (p.2.den : ℤ) ≤ p.2 ^ 2) &&
        !decide (p.2 = 0) && decide ((p.2.num.natAbs : ℚ) = p.2 * (p.2.den : ℚ)))
    (encPair encIntBin encRat) encBool := by
  fun_prop

/-! ### Boundary check: binary exponents are not accepted by `rat_pow` -/

-- A binary exponent `k` on `encNat` can double output length `k` times and must fail `fun_prop`.
example : True := by
  fail_if_success
    exact (by fun_prop :
      ComputableInPolyTime (fun p : ℚ × ℕ => p.1 ^ p.2) (encPair encRat encNat) encRat)
  trivial

end CslibFrontierTests.PolyTimeRat
