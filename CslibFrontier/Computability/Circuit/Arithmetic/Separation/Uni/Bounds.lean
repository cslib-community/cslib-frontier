/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.LenU
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Top
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The universal automaton: bounds for the time

The number of steps of the universal machine on a plain instance (`Uni.runLength`), and bounds
for the length `Uni.tU` of the tapes of the automaton that simulates a machine: it is monotone
and at most quadratic in the number of bits of an address. The bounds
`(m * n).size ≤ m.size + n.size` and `n.size ≤ lg n` that the source proves here are
`Nat.size_mul_le` and `Nat.size_le_log_two_add_one`.

## Main definitions

* `Uni.runLength`.

## Main results

* `Uni.natCast_runLength`: the bound of `Uni.sumTo_universalMachine` is `Uni.runLength`.
* `Uni.tU_mono`, `Uni.tU_le`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition I.1 (the count of the steps in its proof), module `Nc.Uni.Bounds`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

/-- The number of steps of the universal machine on a `τ`-plain instance of size `s`. -/
@[expose] def runLength (supp : Finset (List Bool)) (τ s : ℕ) : ℕ :=
  3 * s + (40 + 2 * nameLength supp) * τ + 10

theorem natCast_runLength (supp : Finset (List Bool)) (τ s : ℕ) :
    (runLength supp τ s : ℤ) = 3 * s + codeCost supp * τ + 10 := by
  simp [runLength, codeCost]

theorem tU_mono {b T T' L L' : ℕ} (hT : T ≤ T') (hL : L ≤ L') : tU b T L ≤ tU b T' L' := by
  unfold tU
  gcongr

theorem tU_le (b T L : ℕ) : tU b T L ≤ (50 + b) * ((T + 1) * (L + 1) ^ 2) := by
  unfold tU
  nlinarith [Nat.zero_le (T * L ^ 2), Nat.zero_le (b * T), Nat.zero_le (b * (T * L)),
    Nat.zero_le (b * L ^ 2), Nat.zero_le (b * (T * L ^ 2))]

end Cslib.Circuits.Arithmetic.Separation.Uni
