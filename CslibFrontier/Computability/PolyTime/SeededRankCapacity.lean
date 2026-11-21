/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Checking a rank against twice the average label-class occupancy

Two alphabet-64 labels of length `a` give `2 ^ (12 * a)` possible pair labels. For `N`
edges the admissible class size is the integer part of twice the average occupancy.
Right-shifting the binary expansion of `2 * N` gives this threshold directly. The native
shift drops at most the number of digits of its left operand.
-/

public section

namespace Cslib.SeededRankCapacity

open Turing.MultiTapeTM ComputableInPolyTime

/-- Shared edge count and label length, together with one guessed class rank. -/
structure Input where
  /-- Number of genuine graph edges, encoded in binary. -/
  edges : ℕ
  /-- Length of one alphabet-64 label, encoded in unary. -/
  labelLength : ℕ
  /-- Rank of an edge within its class, encoded in binary. -/
  rank : ℕ

/-- Binary edge count, unary label length and binary rank. -/
enc_structure encInput : Input where edges : encNat, labelLength : encUnary, rank : encNat

/-- The exact threshold for the class size. -/
@[expose] def capacity (p : Input) : ℕ := (2 * p.edges) >>> (12 * p.labelLength)

/-- Check whether this rank is strictly below the class-size threshold. -/
@[expose] def fits (p : Input) : Bool := decide (p.rank + 1 ≤ capacity p)

/-- The shift computes the integer part of the twice-average occupancy. -/
theorem capacity_eq_div (p : Input) : capacity p = 2 * p.edges / 64 ^ (2 * p.labelLength) := by
  have h : 64 ^ (2 * p.labelLength) = 2 ^ (12 * p.labelLength) := by
    rw [show 64 = 2 ^ 6 by decide, ← pow_mul, ← Nat.mul_assoc]
  rw [capacity, Nat.shiftRight_eq_div_pow, h]

/-- Acceptance is precisely the multiplicative rank condition for a balanced seed. -/
theorem fits_eq_true_iff (p : Input) :
    fits p = true ↔ (p.rank + 1) * 64 ^ (2 * p.labelLength) ≤ 2 * p.edges := by
  rw [fits, decide_eq_true_eq, capacity_eq_div]
  exact Nat.le_div_iff_mul_le (by positivity)

/-- A rank guessed with `w` bits has an input charge linear in `w`, unary label length
and the binary edge count. -/
theorem length_encInput_le (p : Input) {w : ℕ} (hr : p.rank < 2 ^ w) :
    (encInput p).length ≤ 2 * p.edges.size + 2 * p.labelLength + w + 2 := by
  have hw : p.rank.size ≤ w := Nat.size_le.mpr hr
  simp [encInput_apply, encInputFields, encPair_apply, encNat_apply, Nat.size_eq_bits_len]
  omega

/-- The rank comparison runs in polynomial time on the short fields. Its denominator is
represented by a shift count throughout the computation. -/
theorem computableInPolyTime_fits : ComputableInPolyTime fits encInput encBool :=
  binary_le' (binary_add' encInput_rank_deg.computableInPolyTime (const 1))
    (binary_shiftRight' (binary_mul' (const 2) encInput_edges_deg.computableInPolyTime)
      (binary_mul' (const 12) (unary_to_binary.comp encInput_labelLength_deg.computableInPolyTime)))

end Cslib.SeededRankCapacity
