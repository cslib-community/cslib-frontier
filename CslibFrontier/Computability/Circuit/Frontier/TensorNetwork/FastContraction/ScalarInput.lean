/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SparseProduct
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Mathlib.Data.Int.Bitwise
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import Mathlib.Data.List.GetD
import Init.Data.BitVec.Lemmas

/-!
# Binary queries for scalar contraction-ring inputs

A signed integer followed by a binary shift describes the scalar `n * 2 ^ shift` without
constructing that integer or its residue at the requested precision. Its only possibly nonzero
representative coefficient is coefficient zero. Below the precision, its bits are the shifted
two's-complement bits of `n`; all other coefficients and bits are zero.

The native algorithm reads a binary index in the sign-magnitude encoding of `n`. Lookup caps the
index at the magnitude's encoded length before traversing that word. In particular, none of the
precision, shift or bit index is expanded to unary, and `2 ^ precision` is never constructed.
The same request handles integer constants and powers of two.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.FastContraction.ScalarInput

open Polynomial GaloisRingArith Turing.MultiTapeTM ComputableInPolyTime

/-- An integer scalar has only its constant representative coefficient, including precision zero.
The statement is total in the coefficient index. -/
theorem representative_intCast_coeff (m p coefficient : ℕ) (n : ℤ) :
    (representative m p (n : Ring p (modulus m))).coeff coefficient =
      if coefficient = 0 then (n : ZMod (2 ^ p)) else 0 := by
  have hpos : 0 < (modulus m).length := by rw [length_modulus]; positivity
  have hnat (a : ℕ) :
      (representative m p (a : Ring p (modulus m))).coeff coefficient =
        if coefficient = 0 then (a : ZMod (2 ^ p)) else 0 := by
    rw [← val_singleton (p := p) (fl := modulus m) a, representative,
      coeff_modByMonicHom_val]
    cases coefficient <;> simp [hpos]
  cases n with
  | ofNat a => simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using hnat a
  | negSucc a =>
    simp only [Int.cast_negSucc, representative, map_neg, coeff_neg]
    change -(representative m p ((a + 1 : ℕ) : Ring p (modulus m))).coeff coefficient = _
    rw [hnat]
    split_ifs <;> simp

private theorem getLsbD_ofInt (n : ℤ) (p bit : ℕ) :
    (BitVec.ofInt p n).getLsbD bit = (decide (bit < p) && n.testBit bit) := by
  cases n with
  | ofNat a => simp [BitVec.getLsbD_ofNat, Int.testBit]
  | negSucc a =>
    rw [BitVec.ofInt_negSucc_eq_not_ofNat, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
    by_cases h : bit < p <;> simp [h, Int.testBit]

private theorem ofInt_mul_twoPow (n : ℤ) (p shift : ℕ) :
    BitVec.ofInt p (n * 2 ^ shift) = BitVec.ofInt p n <<< shift := by
  rw [BitVec.ofInt_mul, BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  have hpow : (2 ^ shift : ℤ) = ((2 ^ shift : ℕ) : ℤ) := by norm_cast
  rw [hpow, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp

/-- The coefficient bit of an actual shifted integer scalar in the contraction ring. The guard
also specifies every out-of-range coefficient and bit, with no positivity assumptions. -/
theorem representative_shiftedInt_bit (m p shift coefficient bit : ℕ) (n : ℤ) :
    ((representative m p ((n : Ring p (modulus m)) * 2 ^ shift)).coeff coefficient).val.testBit
        bit =
      (decide (coefficient = 0 ∧ bit < p ∧ shift ≤ bit) && n.testBit (bit - shift)) := by
  have hcast : (n : Ring p (modulus m)) * 2 ^ shift = ((n * 2 ^ shift : ℤ) : Ring p (modulus m)) :=
    by push_cast; rfl
  rw [hcast, representative_intCast_coeff]
  by_cases hc : coefficient = 0
  · simp only [hc, ↓reduceIte, true_and]
    have hval (a : ℤ) : (a : ZMod (2 ^ p)).val = (BitVec.ofInt p a).toNat := by
      have h := congrArg Int.toNat (ZMod.val_intCast (n := 2 ^ p) a)
      simpa only [Int.toNat_natCast, BitVec.toNat_ofInt] using h
    rw [hval, BitVec.testBit_toNat, ofInt_mul_twoPow, BitVec.getLsbD_shiftLeft,
      getLsbD_ofInt]
    by_cases hb : bit < p <;> by_cases hs : shift ≤ bit
    · have hsub : bit - shift < p := by omega
      simp [hb, hs, hsub, Nat.not_lt.mpr hs]
    · simp [hb, hs, Nat.lt_of_not_ge hs]
    · simp [hb]
    · simp [hb]
  · simp [hc]

/-- A signed scalar, binary shift, precision and output coordinate, followed by the asserted bit.
The scale does not occur: scalar coordinates are independent of the contraction modulus. -/
structure Input where
  /-- The sign-magnitude integer before shifting. -/
  integer : ℤ
  /-- The binary power-of-two shift. -/
  shift : ℕ
  /-- The binary coefficient precision. -/
  precision : ℕ
  /-- The requested representative coefficient. -/
  coefficient : ℕ
  /-- The requested bit in that coefficient. -/
  bit : ℕ
  /-- The claimed value of the selected bit. -/
  claim : Bool

/-- All unbounded numeric fields are binary; the last field is one raw Boolean. -/
enc_structure encInput : Input where
  integer : encIntBin, shift : encNat, precision : encNat, coefficient : encNat,
  bit : encNat, claim : encBool

/-- Read a scalar bit without constructing either the shifted scalar or the precision modulus. -/
def run (q : Input) : Bool :=
  decide (q.coefficient = 0 ∧ q.bit < q.precision ∧ q.shift ≤ q.bit) &&
    q.integer.testBit (q.bit - q.shift)

/-- The executable bit agrees with the canonical coefficient of the actual contraction ring. -/
theorem run_eq_representative_bit (m : ℕ) (q : Input) :
    run q = ((representative m q.precision
      ((q.integer : Ring q.precision (modulus m)) * 2 ^ q.shift)).coeff q.coefficient).val.testBit
        q.bit :=
  (representative_shiftedInt_bit m q.precision q.shift q.coefficient q.bit q.integer).symm

private theorem nat_testBit_binary {α : Type} {enc : α ↪ List Bool} {n i : α → ℕ}
    (hn : ComputableInPolyTime n enc encNat) (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun a => (n a).testBit (i a)) enc encBool := by
  exact (listGetD_binary (encL := encBits) false (natBits.comp hn) hi).of_enc_eq fun _ => by
    simp only [Nat.testBit_eq_inth, ← List.getD_default_eq_getI]
    rfl

private theorem int_testBit_binary {α : Type} {enc : α ↪ List Bool} {n : α → ℤ} {i : α → ℕ}
    (hn : ComputableInPolyTime n enc encIntBin) (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun a => (n a).testBit (i a)) enc encBool := by
  have hmag := intBin_natAbs.comp hn
  have h := ite (intBin_isNeg.comp hn)
    (bool_not.comp (nat_testBit_binary (binary_sub' hmag (const 1)) hi))
    (nat_testBit_binary hmag hi)
  refine h.of_enc_eq fun a => congrArg encBool ?_
  cases hnval : n a <;> simp [hnval, Int.testBit]

/-- One native machine reads a scalar bit in polynomial time in the binary request length.
Even an arbitrarily large precision or index is charged only through its binary encoding. -/
theorem computableInPolyTime_run : ComputableInPolyTime run encInput encBool := by
  have hb := encInput_bit_deg.computableInPolyTime
  have hs := encInput_shift_deg.computableInPolyTime
  have hguard := decide_and (decide_eq' encInput_coefficient_deg.computableInPolyTime (const 0))
    (decide_and (binary_lt' hb encInput_precision_deg.computableInPolyTime)
      (binary_le.comp (hs.prod hb)))
  exact bool_and' hguard (int_testBit_binary encInput_integer_deg.computableInPolyTime
    (binary_sub' hb hs))

/-- Check the supplied positive or negative claim about the selected scalar bit. -/
def accept (q : Input) : Bool := decide (run q = q.claim)

/-- Checking either polarity has the same polynomial binary-input bound. -/
theorem computableInPolyTime_accept : ComputableInPolyTime accept encInput encBool :=
  decide_eq' computableInPolyTime_run encInput_claim_deg.computableInPolyTime

end Cslib.Circuits.Frontier.FastContraction.ScalarInput
