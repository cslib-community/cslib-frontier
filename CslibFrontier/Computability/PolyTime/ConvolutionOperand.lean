/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Addressing one input bit of a convolution

A terminal partial-product query uses row and shift indices from the two carry-save trees.
The router computes one operand's coefficient and bit from binary indices. Padding and the
zero carry word have no operand requests.
-/

public section
namespace Cslib.ConvolutionOperand

open Turing.MultiTapeTM ComputableInPolyTime

/-- Metadata for one requested bit at the bottom of a multiplication tree in a convolution. -/
structure Input where
  /-- Number of coefficients in each operand. -/
  degree : ℕ
  /-- Precision of each coefficient. -/
  precision : ℕ
  /-- Ordinary convolution coefficient before trinomial reduction. -/
  diagonal : ℕ
  /-- First operand's selected coefficient. -/
  row : ℕ
  /-- Shift of the partial product. -/
  shift : ℕ
  /-- Bit position in the partial product. -/
  bit : ℕ
  /-- The carry word of a partial product is identically zero. -/
  carry : Bool
  /-- Select the second operand when true. -/
  right : Bool

/-- All indices are binary. -/
enc_structure encInput : Input where
  degree : encNat, precision : encNat, diagonal : encNat, row : encNat, shift : encNat,
  bit : encNat, carry : encBool, right : encBool

/-- A partial-product term exists only on a real diagonal and at a valid shift. -/
@[expose] def active (p : Input) : Bool :=
  !p.carry && decide (p.row < p.degree) && decide (p.row ≤ p.diagonal) &&
    decide (p.diagonal - p.row < p.degree) && decide (p.bit < p.precision) &&
    decide (p.shift ≤ p.bit)

/-- The selected coefficient and bit, with no request for a padding or zero leaf. -/
@[expose] def run (p : Input) : Option (ℕ × ℕ) :=
  if active p then some (if p.right then (p.diagonal - p.row, p.shift)
    else (p.row, p.bit - p.shift)) else none

/-- The native router charges polynomial time only in the binary indices. -/
theorem computableInPolyTime_run :
    ComputableInPolyTime run encInput (encOption (encPair encNat encNat)) := by
  have hd := encInput_degree_deg.computableInPolyTime
  have hw := encInput_precision_deg.computableInPolyTime
  have hk := encInput_diagonal_deg.computableInPolyTime
  have hj := encInput_row_deg.computableInPolyTime
  have hs := encInput_shift_deg.computableInPolyTime
  have hi := encInput_bit_deg.computableInPolyTime
  have hc := encInput_carry_deg.computableInPolyTime
  have hr := encInput_right_deg.computableInPolyTime
  have hsub := binary_sub' hk hj
  have hg := bool_and.comp ((bool_not.comp hc).prod (binary_lt' hj hd))
  have hdiag := bool_and.comp (hg.prod (binary_le' hj hk))
  have hsecond := bool_and.comp (hdiag.prod (binary_lt' hsub hd))
  have hbit := bool_and.comp (hsecond.prod (binary_lt' hi hw))
  have hactive := bool_and.comp (hbit.prod (binary_le' hs hi))
  exact ite' hactive ((optionSome _).comp
    (ite' hr (hsub.prod hs) (hj.prod (binary_sub' hi hs)))) (const none)

/-- Every genuine request names a coefficient and bit in the chosen operand. -/
theorem run_bounds {p : Input} {j i : ℕ} (h : run p = some (j, i)) :
    j < p.degree ∧ i < p.precision := by
  unfold run at h
  split at h <;> simp_all only [active, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, Option.some.injEq, reduceCtorEq]
  split at h <;> simp_all <;> omega

end Cslib.ConvolutionOperand
