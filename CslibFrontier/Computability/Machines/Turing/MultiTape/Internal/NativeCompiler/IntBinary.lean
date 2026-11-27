/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryAddition
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySubtraction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Comparison
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Conditional
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Nat
import Mathlib.Tactic.Linarith
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Tactic.EncLen

/-!
# Named native signed-binary arithmetic

This module retains actual finite machines for arithmetic on canonical sign-magnitude binary
integers. Natural addition and comparison package the existing direct zip transducers. Natural
subtraction retains the existing `BinarySub.subStep` borrow round as a raw zip transducer, then
uses the retained reverse/drop-false/reverse canonicalizer; underflow is selected to canonical
zero by the retained conditional machine. Signed operations assemble those natural machines with
the standard pair projections and conditionals, so their `NativeCompiler` fields expose the exact
machine, control encoding, time, independent workspace, description and static description length.

Inputs are typed values and hence use canonical `encNat` and `encIntBin` words. The constituent
raw transducers are total: missing zip digits are read as `false`, and raw subtraction underflow is
discarded by the explicit comparison branch rather than being assigned a noncanonical integer.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.natAdd`, `.natSub`, `.natLtBool`, `.natLeBool`:
  retained binary-natural arithmetic used by the signed constructions.
* `Turing.MultiTapeTM.Internal.NativeCompiler.intBinNatAbs`, `.intBinIsNegBool`,
  `.intBinIsPosBool`, `.intBinSignMagnitude`: retained magnitude and sign operations.
* `Turing.MultiTapeTM.Internal.NativeCompiler.intBinAdd`, `.intBinSub`, `.intBinLtBool`,
  `.intBinLeBool`: retained signed-binary arithmetic and comparison.

## Main results

Each compiler's correctness for every canonical input is its `computes` field. The module adds:

* `Turing.MultiTapeTM.Internal.NativeCompiler.intBinAdd_time_le`, `.intBinSub_time_le`,
  `.intBinLtBool_time_le`, `.intBinLeBool_time_le` and the corresponding lemmas for the natural
  and sign operations: linear bounds on the exact clock of each retained machine.

The asymptotic `ComputableInPolyTime` facts for these operations already exist in the plain
calculus (`ComputableInPolyTime.intBin_add`, `.binary_add`, …); these lemmas give the same
asymptotics for the retained machines without restating them.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

private theorem length_encTest (bit : Bool) :
    (encTest bit).length = if bit then 1 else 0 := by
  cases bit <;> rfl

private theorem natBinaryZip_time_le (input : ℕ × ℕ) :
    2 * (3 * (encPair encNat encNat input).length + 1) +
        3 * ((encNat input.1).length + 2) + 2 * 1 + 4 ≤
      20 * ((encPair encNat encNat input).length + 1) := by
  have := length_le_encPair_left encNat encNat input
  omega

/-- Binary-natural addition through the existing carry zip transducer. -/
@[expose] def natAdd :
    NativeCompiler (fun input : ℕ × ℕ => input.1 + input.2)
      (encPair encNat encNat) encNat :=
  ofZipTransducer encNat encNat encNat NatAdd.zipTransducer Universal.eBit fun input => by
    rw [NatAdd.run_zipTransducer]
    simpa only [NatAdd.zipTransducer, encNat_apply, Bool.toNat_false, Nat.add_zero] using
      NatAdd.addBits_bits false input.1 input.2

/-- Construction-derived linear clock bound for the retained `natAdd` machine. -/
theorem natAdd_time_le (input : ℕ × ℕ) :
    natAdd.time input ≤ 20 * ((encPair encNat encNat input).length + 1) := by
  change 2 * (3 * (encPair encNat encNat input).length + 1) +
      3 * ((encNat input.1).length + 2) + 2 * 1 + 4 ≤
    20 * ((encPair encNat encNat input).length + 1)
  exact natBinaryZip_time_le input

/-- Strict binary-natural comparison through the existing comparison zip transducer. -/
@[expose] def natLtBool :
    NativeCompiler (fun input : ℕ × ℕ => decide (input.1 < input.2))
      (encPair encNat encNat) encBool :=
  ofZipTransducer encNat encNat encBool (BinaryCompare.zipTransducer false)
    Universal.eBit fun input => by
      rw [BinaryCompare.run_zipTransducer]
      simp [BinaryCompare.zipTransducer, encNat_apply, encBool_apply, ofBits]

/-- Construction-derived linear clock bound for the retained `natLtBool` machine. -/
theorem natLtBool_time_le (input : ℕ × ℕ) :
    natLtBool.time input ≤ 20 * ((encPair encNat encNat input).length + 1) := by
  change 2 * (3 * (encPair encNat encNat input).length + 1) +
      3 * ((encNat input.1).length + 2) + 2 * 1 + 4 ≤
    20 * ((encPair encNat encNat input).length + 1)
  exact natBinaryZip_time_le input

/-- Non-strict binary-natural comparison through the same zip transducer, initialized to true. -/
@[expose] def natLeBool :
    NativeCompiler (fun input : ℕ × ℕ => decide (input.1 ≤ input.2))
      (encPair encNat encNat) encBool :=
  ofZipTransducer encNat encNat encBool (BinaryCompare.zipTransducer true)
    Universal.eBit fun input => by
      rw [BinaryCompare.run_zipTransducer]
      simp [BinaryCompare.zipTransducer, encNat_apply, encBool_apply, ofBits,
        Nat.le_iff_lt_or_eq]

/-- Construction-derived linear clock bound for the retained `natLeBool` machine. -/
theorem natLeBool_time_le (input : ℕ × ℕ) :
    natLeBool.time input ≤ 20 * ((encPair encNat encNat input).length + 1) := by
  change 2 * (3 * (encPair encNat encNat input).length + 1) +
      3 * ((encNat input.1).length + 2) + 2 * 1 + 4 ≤
    20 * ((encPair encNat encNat input).length + 1)
  exact natBinaryZip_time_le input

/-- Truncated binary-natural subtraction. The retained machine first compares the operands; an
underflow emits canonical zero, while the non-underflow branch runs the existing borrow round and
canonicalizes the resulting little-endian word. -/
@[expose] def natSub :
    NativeCompiler (fun input : ℕ × ℕ => input.1 - input.2)
      (encPair encNat encNat) encNat := by
  let raw : NativeCompiler
      (fun input : ℕ × ℕ => BinarySub.zipTransducer.run false input.1.bits input.2.bits)
      (encPair encNat encNat) encBits :=
    ofZipTransducer encNat encNat encBits BinarySub.zipTransducer Universal.eBit fun input => by
      simp only [BinarySub.zipTransducer, encNat_apply, encBits_apply]
  let less := boolToTest.comp natLtBool
  let zero := const (encPair encNat encNat) encNat 0
  let difference := bitsToNat.comp raw
  exact (ite less zero difference).ofOutputEq fun input => by
    apply congrArg encNat
    by_cases h : input.1 < input.2
    · simp [h, Nat.le_of_lt h]
    · simp only [h, decide_false, id_eq, Bool.false_eq_true, ↓reduceIte]
      rw [BinarySub.ofBits_run_zipTransducer_of_le input.1.bits input.2.bits]
      · simp only [ofBits, Nat.foldr_bit_bits]
      · simpa only [ofBits, Nat.foldr_bit_bits] using Nat.le_of_not_gt h

/-- The magnitude of a canonical signed-binary integer, by dropping its first sign bit. -/
@[expose] def intBinNatAbs :
    NativeCompiler Int.natAbs encIntBin encNat :=
  (tailDecoder.ofInputEq encIntBin fun _ => rfl).ofOutputEq fun integer => by
    simp only [encIntBin_apply, List.tail_cons, encNat_apply, encBits_apply]

/-- Construction-derived linear clock bound for the retained `intBinNatAbs` machine. -/
theorem intBinNatAbs_time_le (integer : ℤ) :
    intBinNatAbs.time integer ≤ 10 * ((encIntBin integer).length + 1) := by
  change 4 * (encIntBin integer).length + 8 ≤ 10 * ((encIntBin integer).length + 1)
  omega

/-- The sign bit of a canonical signed-binary integer, with `true` exactly for negative values. -/
@[expose] def intBinIsNegBool :
    NativeCompiler (fun integer : ℤ => decide (integer < 0)) encIntBin encBool :=
  (boolDecoder.ofInputEq encIntBin fun _ => rfl).ofOutputEq fun integer => by
    simp only [encIntBin_apply, List.headD_cons]

/-- Construction-derived linear clock bound for the retained `intBinIsNegBool` machine. -/
theorem intBinIsNegBool_time_le (integer : ℤ) :
    intBinIsNegBool.time integer ≤ 10 * ((encIntBin integer).length + 1) := by
  change 4 * (encIntBin integer).length + 8 ≤ 10 * ((encIntBin integer).length + 1)
  omega

/-- Assemble a canonical signed-binary integer from a sign and binary magnitude. A negative sign
on zero is cleared by an explicit retained zero-test branch. -/
@[expose] def intBinSignMagnitude :
    NativeCompiler (fun input : Bool × ℕ => if input.1 then -(input.2 : ℤ) else input.2)
      (encPair encBool encNat) encIntBin := by
  let sign := first encBool encNat
  let magnitude := second encBool encNat
  let signWord : NativeCompiler (fun input : Bool × ℕ => [input.1])
      (encPair encBool encNat) encBits :=
    sign.ofOutputEq fun _ => rfl
  let magnitudeWord : NativeCompiler (fun input : Bool × ℕ => input.2.bits)
      (encPair encBool encNat) encBits :=
    magnitude.ofOutputEq fun _ => rfl
  let raw := signWord.append magnitudeWord
  let zero := boolToTest.comp (natIsZeroBool.comp magnitude)
  let canonical := ite zero (const (encPair encBool encNat) encBits [false]) raw
  exact canonical.ofOutputEq fun input => by
    rcases input with ⟨sign, magnitude⟩
    cases sign <;> by_cases h : magnitude = 0
    · subst magnitude
      rfl
    · simp [h, encIntBin_apply]
    · subst magnitude
      rfl
    · simp [h, encIntBin_apply, Nat.pos_iff_ne_zero]

/-- Construction-derived linear clock bound for the retained `intBinSignMagnitude` machine. -/
theorem intBinSignMagnitude_time_le (input : Bool × ℕ) :
    intBinSignMagnitude.time input ≤ 1000000 * ((encPair encBool encNat input).length + 1) := by
  dsimp [intBinSignMagnitude, ofOutputEq, ite, comp, pair, append, first, second,
    boolToTest, natIsZeroBool, encodeFrame, ofTransducer, const]
  simp only [length_encTest]
  split_ifs <;> omega

/-- Test strict positivity of a signed-binary integer. The retained conditionals reject a negative
sign and canonical zero and accept every remaining canonical input. -/
@[expose] def intBinIsPosBool :
    NativeCompiler (fun integer : ℤ => decide (0 < integer)) encIntBin encBool := by
  let negative := boolToTest.comp intBinIsNegBool
  let zero := boolToTest.comp (natIsZeroBool.comp intBinNatAbs)
  let falseCompiler := const encIntBin encBool false
  let trueCompiler := const encIntBin encBool true
  exact (ite negative falseCompiler (ite zero falseCompiler trueCompiler)).ofOutputEq
    fun integer => by
      apply congrArg encBool
      rcases lt_trichotomy integer 0 with h | rfl | h
      · simp [h, h.le]
      · simp
      · simp [h, h.le, h.ne']

/-- Construction-derived linear clock bound for the retained `intBinIsPosBool` machine. -/
theorem intBinIsPosBool_time_le (integer : ℤ) :
    intBinIsPosBool.time integer ≤ 1000000 * ((encIntBin integer).length + 1) := by
  dsimp [intBinIsPosBool, ofOutputEq, ite, comp, boolToTest, intBinIsNegBool,
    intBinNatAbs, natIsZeroBool, ofInputEq, boolDecoder, tailDecoder, ofTransducer, const]
  simp only [length_encTest]
  split_ifs <;> omega

/-- Addition of canonical signed-binary integers. Equal signs add magnitudes; unequal signs compare
the magnitudes, subtract the smaller from the larger, and retain the larger magnitude's sign. -/
@[expose] def intBinAdd :
    NativeCompiler (fun input : ℤ × ℤ => input.1 + input.2)
      (encPair encIntBin encIntBin) encIntBin := by
  let left := first encIntBin encIntBin
  let right := second encIntBin encIntBin
  let leftSign := intBinIsNegBool.comp left
  let rightSign := intBinIsNegBool.comp right
  let leftMagnitude := intBinNatAbs.comp left
  let rightMagnitude := intBinNatAbs.comp right
  let sameSign := wordEqTest encBool |>.comp (leftSign.pair rightSign)
  let sameMagnitude := natAdd.comp (leftMagnitude.pair rightMagnitude)
  let same := intBinSignMagnitude.comp (leftSign.pair sameMagnitude)
  let rightLeLeft := boolToTest.comp (natLeBool.comp (rightMagnitude.pair leftMagnitude))
  let leftDifference := natSub.comp (leftMagnitude.pair rightMagnitude)
  let rightDifference := natSub.comp (rightMagnitude.pair leftMagnitude)
  let different := ite rightLeLeft
    (intBinSignMagnitude.comp (leftSign.pair leftDifference))
    (intBinSignMagnitude.comp (rightSign.pair rightDifference))
  exact (ite sameSign same different).ofOutputEq fun input => by
    apply congrArg encIntBin
    rcases input with ⟨left, right⟩
    by_cases hleft : left < 0 <;> by_cases hright : right < 0 <;>
      simp only [hleft, hright, decide_true, decide_false, Bool.false_eq_true,
        decide_eq_true_eq, id_eq, encBool_apply, ↓reduceIte] <;> (try split_ifs) <;> lia

/-- Construction-derived linear clock bound for the retained `intBinAdd` machine. -/
theorem intBinAdd_time_le (input : ℤ × ℤ) :
    intBinAdd.time input ≤
      100000000 * ((encPair encIntBin encIntBin input).length + 1) := by
  have hleft := length_le_encPair_left encIntBin encIntBin input
  have hright := length_le_encPair_right encIntBin encIntBin input
  have hsum := Nat.size_add_le input.1.natAbs input.2.natAbs
  have hleftSub : (input.1.natAbs - input.2.natAbs).size ≤ input.1.natAbs.size :=
    Nat.size_le_size (Nat.sub_le input.1.natAbs input.2.natAbs)
  have hrightSub : (input.2.natAbs - input.1.natAbs).size ≤ input.2.natAbs.size :=
    Nat.size_le_size (Nat.sub_le input.2.natAbs input.1.natAbs)
  have hrawLeft := BinarySub.length_run_zipTransducer
    false input.1.natAbs.bits input.2.natAbs.bits
  have hrawRight := BinarySub.length_run_zipTransducer
    false input.2.natAbs.bits input.1.natAbs.bits
  have hdropLeft := List.length_dropWhile_le (!·)
    (BinarySub.zipTransducer.run false input.1.natAbs.bits input.2.natAbs.bits).reverse
  have hdropRight := List.length_dropWhile_le (!·)
    (BinarySub.zipTransducer.run false input.2.natAbs.bits input.1.natAbs.bits).reverse
  dsimp [intBinAdd, intBinSignMagnitude, natAdd, natSub, natLeBool, intBinIsNegBool,
    intBinNatAbs, ofOutputEq, ofInputEq, ite, comp, pair, append, first, second,
    boolToTest, natIsZeroBool, bitsToNat, natLtBool, wordEqTest, wordEqBool,
    ofZipTransducer, boolDecoder, tailDecoder, encodeFrame, ofTransducer, const]
  simp only [length_encTest]
  split_ifs <;>
    simp [encIntBin_apply, Nat.size_eq_bits_len, List.length_reverse,
      hrawLeft, hrawRight]
      at hleft hright hsum hleftSub hrightSub hdropLeft hdropRight ⊢ <;>
    omega

/-- Subtraction of canonical signed-binary integers, by retained negation of the second operand
followed by the retained signed addition machine. -/
@[expose] def intBinSub :
    NativeCompiler (fun input : ℤ × ℤ => input.1 - input.2)
      (encPair encIntBin encIntBin) encIntBin := by
  let boolNot : NativeCompiler Bool.not encBool encBool :=
    (ite boolToTest (const encBool encBool false) (const encBool encBool true)).ofOutputEq
      fun bit => by cases bit <;> rfl
  let neg : NativeCompiler (fun integer : ℤ => -integer) encIntBin encIntBin :=
    (intBinSignMagnitude.comp ((boolNot.comp intBinIsNegBool).pair intBinNatAbs)).ofOutputEq
      fun integer => by
        apply congrArg encIntBin
        by_cases h : integer < 0 <;>
          simp only [h, decide_true, decide_false, Bool.not_true,
            Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;> omega
  exact (intBinAdd.comp
    ((first encIntBin encIntBin).pair (neg.comp (second encIntBin encIntBin))))
    |>.ofOutputEq fun input => by
      apply congrArg encIntBin
      simp only [sub_eq_add_neg]

/-- Construction-derived linear clock bound for the retained `intBinSub` machine. -/
theorem intBinSub_time_le (input : ℤ × ℤ) :
    intBinSub.time input ≤ 1000000000 * ((encPair encIntBin encIntBin input).length + 1) := by
  have hleft := length_le_encPair_left encIntBin encIntBin input
  have hright := length_le_encPair_right encIntBin encIntBin input
  have hpair :
      (encPair encIntBin encIntBin (input.1, -input.2)).length =
        (encPair encIntBin encIntBin input).length := by
    simp
  have hadd := intBinAdd_time_le (input.1, -input.2)
  rw [hpair] at hadd
  dsimp [intBinSub, intBinSignMagnitude, intBinIsNegBool, intBinNatAbs, ofOutputEq,
    ofInputEq, ite, comp, pair, append, first, second, boolToTest, natIsZeroBool,
    boolDecoder, tailDecoder, encodeFrame, ofTransducer, const]
  simp only [length_encTest]
  split_ifs <;>
    simp [encIntBin_apply] at hleft hright hadd ⊢ <;>
    omega

private theorem natAbs_lt_natAbs_of_nonneg {left right : ℤ}
    (hleft : 0 ≤ left) (hright : 0 ≤ right) :
    left.natAbs < right.natAbs ↔ left < right := by
  rw [← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs,
    abs_of_nonneg hleft, abs_of_nonneg hright]

private theorem natAbs_lt_natAbs_of_neg {left right : ℤ}
    (hleft : left < 0) (hright : right < 0) :
    right.natAbs < left.natAbs ↔ left < right := by
  rw [← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs,
    abs_of_neg hright, abs_of_neg hleft, neg_lt_neg_iff]

private theorem natAbs_le_natAbs_of_nonneg {left right : ℤ}
    (hleft : 0 ≤ left) (hright : 0 ≤ right) :
    left.natAbs ≤ right.natAbs ↔ left ≤ right := by
  rw [← Int.ofNat_le, Int.natCast_natAbs, Int.natCast_natAbs,
    abs_of_nonneg hleft, abs_of_nonneg hright]

private theorem natAbs_le_natAbs_of_neg {left right : ℤ}
    (hleft : left < 0) (hright : right < 0) :
    right.natAbs ≤ left.natAbs ↔ left ≤ right := by
  rw [← Int.ofNat_le, Int.natCast_natAbs, Int.natCast_natAbs,
    abs_of_neg hright, abs_of_neg hleft, neg_le_neg_iff]

/-- Strict comparison of canonical signed-binary integers. Different signs are decided by the
left sign; equal nonnegative signs compare magnitudes in order, and equal negative signs in reverse
order. -/
@[expose] def intBinLtBool :
    NativeCompiler (fun input : ℤ × ℤ => decide (input.1 < input.2))
      (encPair encIntBin encIntBin) encBool := by
  let left := first encIntBin encIntBin
  let right := second encIntBin encIntBin
  let leftSign := intBinIsNegBool.comp left
  let rightSign := intBinIsNegBool.comp right
  let leftMagnitude := intBinNatAbs.comp left
  let rightMagnitude := intBinNatAbs.comp right
  let sameSign := wordEqTest encBool |>.comp (leftSign.pair rightSign)
  let negative := boolToTest.comp leftSign
  let same := ite negative
    (natLtBool.comp (rightMagnitude.pair leftMagnitude))
    (natLtBool.comp (leftMagnitude.pair rightMagnitude))
  exact (ite sameSign same leftSign).ofOutputEq fun input => by
    apply congrArg encBool
    rcases input with ⟨left, right⟩
    by_cases hleft : left < 0 <;> by_cases hright : right < 0
    · simp [hleft, hright, encBool_apply, natAbs_lt_natAbs_of_neg hleft hright]
    · simp [hleft, hright, encBool_apply]
      omega
    · simp [hleft, hright, encBool_apply]
      omega
    · simp [hleft, hright, encBool_apply,
        natAbs_lt_natAbs_of_nonneg (not_lt.mp hleft) (not_lt.mp hright)]

/-- Construction-derived linear clock bound for the retained `intBinLtBool` machine. -/
theorem intBinLtBool_time_le (input : ℤ × ℤ) :
    intBinLtBool.time input ≤ 10000000 * ((encPair encIntBin encIntBin input).length + 1) := by
  have hleft := length_le_encPair_left encIntBin encIntBin input
  have hright := length_le_encPair_right encIntBin encIntBin input
  dsimp [intBinLtBool, intBinIsNegBool, intBinNatAbs, natLtBool, ofOutputEq,
    ofInputEq, ite, comp, pair, first, second, boolToTest, wordEqTest, wordEqBool,
    ofZipTransducer, boolDecoder, tailDecoder, encodeFrame, ofTransducer]
  simp only [length_encTest]
  split_ifs <;>
    simp [encIntBin_apply] at hleft hright ⊢ <;>
    omega

/-- Non-strict comparison of canonical signed-binary integers, using the same sign cases and the
non-strict natural comparison transducer. -/
@[expose] def intBinLeBool :
    NativeCompiler (fun input : ℤ × ℤ => decide (input.1 ≤ input.2))
      (encPair encIntBin encIntBin) encBool := by
  let left := first encIntBin encIntBin
  let right := second encIntBin encIntBin
  let leftSign := intBinIsNegBool.comp left
  let rightSign := intBinIsNegBool.comp right
  let leftMagnitude := intBinNatAbs.comp left
  let rightMagnitude := intBinNatAbs.comp right
  let sameSign := wordEqTest encBool |>.comp (leftSign.pair rightSign)
  let negative := boolToTest.comp leftSign
  let same := ite negative
    (natLeBool.comp (rightMagnitude.pair leftMagnitude))
    (natLeBool.comp (leftMagnitude.pair rightMagnitude))
  exact (ite sameSign same leftSign).ofOutputEq fun input => by
    apply congrArg encBool
    rcases input with ⟨left, right⟩
    by_cases hleft : left < 0 <;> by_cases hright : right < 0
    · simp [hleft, hright, encBool_apply, natAbs_le_natAbs_of_neg hleft hright]
    · simp [hleft, hright, encBool_apply]
      omega
    · simp [hleft, hright, encBool_apply]
      omega
    · simp [hleft, hright, encBool_apply,
        natAbs_le_natAbs_of_nonneg (not_lt.mp hleft) (not_lt.mp hright)]

/-- Construction-derived linear clock bound for the retained `intBinLeBool` machine. -/
theorem intBinLeBool_time_le (input : ℤ × ℤ) :
    intBinLeBool.time input ≤ 10000000 * ((encPair encIntBin encIntBin input).length + 1) := by
  have hleft := length_le_encPair_left encIntBin encIntBin input
  have hright := length_le_encPair_right encIntBin encIntBin input
  dsimp [intBinLeBool, intBinIsNegBool, intBinNatAbs, natLeBool, ofOutputEq,
    ofInputEq, ite, comp, pair, first, second, boolToTest, wordEqTest, wordEqBool,
    ofZipTransducer, boolDecoder, tailDecoder, encodeFrame, ofTransducer]
  simp only [length_encTest]
  split_ifs <;>
    simp [encIntBin_apply] at hleft hright ⊢ <;>
    omega

end Turing.MultiTapeTM.Internal.NativeCompiler
