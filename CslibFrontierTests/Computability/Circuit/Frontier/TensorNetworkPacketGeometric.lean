/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.PacketGeometric

/-!
# Tests for finite geometric packet inverses

The geometric expansion covers precision zero and one, an empty kernel grid, and the cross ratio
with denominator `1 + 4 ζ`. Concrete coefficient lists at precision three check that the geometric
sum agrees with the existing inverse for `3 + 2 U`, and that an even constant cannot be inverted
by the same identity.
-/

public section

namespace CslibFrontierTests.TensorNetworkPacketGeometric

open Cslib Cslib.Circuits.Frontier.NativePacket GaloisRingArith Finset

-- Precision zero: the sum has no terms, including when the inverse's raw list is not reduced.
example (fl : List ℕ) : val 0 fl (inv 0 fl (intConst 0 fl 3)) = 0 := by
  have h : val 0 fl (intConst 0 fl 3) = 1 + 2 * (1 : Ring 0 fl) := by
    rw [val_intConst]
    norm_num
  simpa using val_inv_eq_sum_pow _ h

-- Precision one: the entire inverse of every `3 + 2 ζ` has value one.
example (ζ : List ℕ) : val 1 [1, 1] (inv 1 [1, 1] (linFactor 1 [1, 1] 3 1 ζ)) = 1 := by
  obtain ⟨w, hw⟩ := exists_val_linFactor_eq (p := 1) (fl := [1, 1])
    (u := 3) (by decide) (k := 1) (by decide) ζ
  simpa using val_inv_eq_sum_pow _ hw

-- In an empty grid the denominator is one, so the sum is just its constant term.
example (fl : List ℕ) : val 3 fl (kernelUnitList 3 fl 0) = 1 := by
  rw [val_kernelUnitList_eq_sum_pow]
  norm_num [kernelUnitDen, gridList, val_prodList]

-- Modulo eight and `U² + U + 1`, the inverse of `3 + 2 U` is `7 + 2 U`.
example : inv 3 [1, 1] [3, 2] = [7, 2] := by decide
example : sumList 3 [1, 1] ((List.range 3).map fun j =>
    pow 3 [1, 1] (sub 3 [1, 1] (one [1, 1]) [3, 2]) j) = [7, 2] := by decide

-- The expansion also works with a variable denominator: `2/(1 + 4 ζ)` modulo eight.
example (ζ : List ℕ) :
    val 3 [1, 1] (crossRatioList 3 [1, 1] 1 0 1 0 ζ) =
      2 * (1 + (1 - val 3 [1, 1] (linFactor 3 [1, 1] 1 2 ζ)) +
        (1 - val 3 [1, 1] (linFactor 3 [1, 1] 1 2 ζ)) ^ 2) := by
  have h := val_crossRatioList_eq_sum_pow (p := 3) (fl := [1, 1])
    (a := 1) (i := 0) (by decide) (t := 1) (d₀ := 0) (by decide) ζ
  simpa [sum_range_succ, twoVal, twoValAux] using h

-- An even denominator is outside the hypothesis: multiplying by its three-term geometric sum
-- gives `2` modulo eight, not the unit.
example : mul 3 [1, 1] [2, 0]
    (sumList 3 [1, 1] ((List.range 3).map fun j =>
      pow 3 [1, 1] (sub 3 [1, 1] (one [1, 1]) [2, 0]) j)) = [2, 0] := by decide

end CslibFrontierTests.TensorNetworkPacketGeometric
