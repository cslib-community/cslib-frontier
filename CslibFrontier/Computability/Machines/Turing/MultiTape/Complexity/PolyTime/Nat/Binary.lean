/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPower
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Foundations.Data.Nat.Bits
public import CslibFrontier.Foundations.Data.Nat.BinarySize
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Subtraction
import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Tactic.PolyTime.Init
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryAddition
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise

/-!
# Polynomial-time arithmetic on binary naturals

Polynomial-time certificates for arithmetic on the binary encoding `Turing.MultiTapeTM.encNat`
(digits least significant first), the binary counterparts of the unary certificates in
`CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat.lean`. Addition and
multiplication reuse Christian Reitwiessner's plain schoolbook certificates
`Turing.MultiTapeTM.ComputableInO.natAdd` and `Turing.MultiTapeTM.ComputableInO.natMul`. A list is
summed by a left fold whose accumulator grows by at most one digit more than the length of the
element added. Powers of two are computed from a unary exponent by repeated doubling. Comparisons
are the linear-time zip transducers of `Turing.MultiTapeTM.computableInTimeAndSpace_natLt` and
`Turing.MultiTapeTM.computableInTimeAndSpace_natLe`; bitwise OR is that of
`Turing.MultiTapeTM.computableInTimeAndSpace_natOr`. The verifiers and reductions
of the number problems (`Cslib.Complexity.SubsetSum` and its relatives) are built from these.

Truncated subtraction is schoolbook subtraction: a left fold over the digit pairs of both operands
keeps a borrow and appends one difference digit per position. A final borrow means that the
difference is negative; otherwise the digits are read back as a natural
(`Turing.MultiTapeTM.ofBits`, certified by `Turing.MultiTapeTM.Decoder.nat`), dropping trailing
zeros. General powers to a unary exponent are computed by repeated
multiplication.

## Main definitions

* `Turing.MultiTapeTM.BinarySub.subStep`: one round of schoolbook subtraction with a borrow.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.bitsToNat`: binary decoding of arbitrary words.
* `Nat.size_sum_le`: the binary length of a list sum. The binary lengths of sums, products and
  powers (`Nat.size_add_le`, `Nat.size_mul_le`, `Nat.size_pow_le`) are in
  `CslibFrontier/Foundations/Data/Nat/BinarySize.lean`.
* `Turing.MultiTapeTM.BinarySub.sub_eq`: truncated subtraction through the final borrow.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_add`, `.binary_mul`: addition and
  multiplication.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_sum`: plain binary-list summation.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_two_pow`: `2 ^ k` in binary, from `k` in
  unary.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_lt`, `.binary_le`: comparisons.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_sub`: truncated subtraction.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_pow`: a power to a unary exponent.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_add'`, `.binary_lt'`, `.binary_le'`:
  composition rules for `fun_prop`.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_mul'`, `.binary_sub'`, `.binary_pow'`:
  composition rules for `fun_prop`.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_add'`, `.binary_sub'`, `.binary_pow'`: named
  composition rules for plain certificates.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_bitwise`, `.binary_and`, `.binary_or`,
  `.binary_xor`, `.binary_and'`, `.binary_or'`, `.binary_xor'`: bitwise operations on binary
  naturals, and their composition rules.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_size`, `.binary_min_unary`,
  `.binary_min_unary'`, `.binary_shiftRight`, `.binary_shiftRight'`: bit-length in unary, capping
  a binary natural by a unary bound, and binary right shift.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_testBit`: a bit of a binary number at a
  unary position.
-/

public section

namespace Nat

/-- A sum of naturals of binary length at most `b` has binary length at most `b` plus the binary
length of the number of summands. -/
theorem size_sum_le {l : List ℕ} {b : ℕ} (h : ∀ n ∈ l, n.size ≤ b) :
    l.sum.size ≤ b + l.length.size := by
  refine Nat.size_le.2 ?_
  have hsum : l.sum ≤ l.length * 2 ^ b := by
    simpa only [smul_eq_mul] using
      List.sum_le_length_nsmul l (2 ^ b) fun n hn => (Nat.size_le.1 (h n hn)).le
  rw [Nat.pow_add, Nat.mul_comm (2 ^ b)]
  exact hsum.trans_lt (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by positivity))

end Nat

namespace Turing.MultiTapeTM.BinarySub
private lemma foldl_append_singleton {α β : Type} (f : α → β) (l : List α) (out : List β) :
    l.foldl (fun acc a => acc ++ [f a]) out = out ++ l.map f := by
  induction l generalizing out with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Any zero-preserving bitwise operation on `ℕ` is read off by folding `op` over `digitPairs`. -/
private lemma bitwise_eq (op : Bool → Bool → Bool) (h0 : op false false = false) (p : ℕ × ℕ) :
    Nat.bitwise op p.1 p.2 =
      ofBits ((digitPairs p).foldl (fun acc d => acc ++ [op d.1 d.2]) []) := by
  rw [foldl_append_singleton, List.nil_append, ofBits]
  have hmap : (digitPairs p).map (fun d => op d.1 d.2) =
      (List.range (p.1.bits.length + p.2.bits.length)).map
        (Nat.bitwise op p.1 p.2).testBit := by
    simp only [digitPairs, List.map_map, Function.comp_def, bits_getD, ← Nat.testBit_bitwise h0]
  rw [hmap, Nat.foldr_bit_testBit]
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  refine Nat.size_le.2 (Nat.bitwise_lt_two_pow ?_ ?_)
  · exact (Nat.lt_size_self p.1).trans_le (Nat.pow_le_pow_right (by lia) (by lia))
  · exact (Nat.lt_size_self p.2).trans_le (Nat.pow_le_pow_right (by lia) (by lia))

end Turing.MultiTapeTM.BinarySub

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- The binary digits of a natural number, as a raw bit string. -/
@[fun_prop]
theorem natBits : ComputableInPolyTime Nat.bits encNat encBits := of_eq fun _ => rfl

/-- Multiplication of binary naturals. -/
@[fun_prop]
theorem binary_mul : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 * p.2)
    (encPair encNat encNat) encNat :=
  (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.fst encNat encNat)
    (ComputableInPolyTime.snd encNat encNat))

/-- Add computed binary values, fixing their intermediate encodings for proof search. -/
@[fun_prop]
theorem binary_add' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a + right a) input encNat :=
  binary_add.comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableInPolyTime

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- The sum of a list of binary naturals, by a left fold of binary additions. -/
@[fun_prop]
theorem binary_sum : ComputableInPolyTime List.sum (encList encNat) encNat := by
  have hq := fst (encPair (encList encNat) encNat) encNat
  have h := foldlWith_of_bounded_growth (encA := encNat) (encL := encList encNat)
    (encB := encNat) (par := fun l : List ℕ => l) (list := fun l => l)
    (step := fun _ s a => s + a) id' id' (const 0) (binary_add.comp (hq.snd'.prod (snd _ _)))
    (growth := fun l => (encList encNat l).length + 1) (.add .self (.const 1))
    (fun l s a ha => by
      have := length_le_encList_of_mem encNat ha
      simp only [encNat_apply, Nat.size_eq_bits_len] at this ⊢
      have := Nat.size_add_le s a
      lia)
  simpa only [← List.sum_eq_foldl_nat] using h

end Turing.MultiTapeTM.ComputableInPolyTime

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- `2 ^ k` in binary, from `k` in unary, by doubling. -/
@[fun_prop]
theorem binary_two_pow : ComputableInPolyTime (fun k : ℕ => 2 ^ k) encUnary encNat := by
  have hfold (k : ℕ) : (List.replicate k true).foldl (fun n _ => n + n) 1 = 2 ^ k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ', List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        Nat.pow_succ]
      lia
  have hq := fst encNat encBool
  have h := foldl_of_bounded_growth (encA := encBool) (encL := encBits) (encB := encNat)
    (list := fun k => List.replicate k true) (step := fun n _ => n + n)
    (of_eq (encIn := encUnary) (encOut := encBits) fun _ => rfl) (const 1)
    (binary_add.comp (hq.prod hq)) (growth := 1)
    (fun n _ => by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      refine Nat.size_le.2 ?_
      have := Nat.lt_size_self n
      rw [Nat.pow_succ]
      lia)
  simpa only [hfold] using h

/-- Testing a binary number for positivity is polynomial-time. -/
theorem binary_pos :
    ComputableInPolyTime (fun n : ℕ => decide (0 < n)) encNat encBool :=
  ComputableInPolyTime.binary_lt.comp
    ((ComputableInPolyTime.const 0).prod ComputableInPolyTime.id')

/-- Strictly compare computed binary values, fixing their intermediate encodings. -/
@[fun_prop]
theorem binary_lt' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => decide (left a < right a)) input encBool :=
  binary_lt.comp (hleft.prod hright)

/-- Raise a computed binary value to a computed unary exponent, fixing the intermediate
encodings. -/
@[fun_prop]
theorem binary_pow' {α : Type} {input : α ↪ List Bool} {base exponent : α → ℕ}
    (hbase : ComputableInPolyTime base input encNat)
    (hexponent : ComputableInPolyTime exponent input encUnary) :
    ComputableInPolyTime (fun a => base a ^ exponent a) input encNat :=
  binary_pow.comp (hbase.prod hexponent)

/-- Subtract computed binary values, truncating at zero and fixing their intermediate
encodings. -/
@[fun_prop]
theorem binary_sub' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a - right a) input encNat :=
  binary_sub.comp (hleft.prod hright)

/-- Any zero-preserving bitwise operation on binary naturals is polynomial-time. -/
@[program_certificate]
theorem binary_bitwise (op : Bool → Bool → Bool) (h0 : op false false = false) :
    ComputableInPolyTime (fun p : ℕ × ℕ => Nat.bitwise op p.1 p.2)
      (encPair encNat encNat) encNat := by
  have hpairs : ComputableInPolyTime BinarySub.digitPairs (encPair encNat encNat)
      (encList (encPair encBool encBool)) := by
    unfold BinarySub.digitPairs
    fun_prop
  have hop : ComputableInPolyTime (fun d : Bool × Bool => op d.1 d.2)
      (encPair encBool encBool) encBool := of_finite _
  have hstep : ComputableInPolyTime
      (fun p : List Bool × (Bool × Bool) => p.1 ++ [op p.2.1 p.2.2])
      (encPair encBits (encPair encBool encBool)) encBits :=
    bitsAppend (fst _ _) (bitsCons (hop.comp (snd _ _)) (const []))
  have hfold := foldl_of_bounded_growth (encA := encPair encBool encBool)
    (encL := encList (encPair encBool encBool)) (encB := encBits)
    (step := fun acc d => acc ++ [op d.1 d.2])
    (init := fun _ => []) hpairs (const []) hstep (growth := 1) (fun _ _ => by simp)
  convert bitsToNat.comp hfold using 1
  funext p
  exact BinarySub.bitwise_eq op h0 p

/-- The smaller of a unary natural and a binary natural, returned in unary by saturating binary
decoding. -/
theorem binary_min_unary : ComputableInPolyTime (fun p : ℕ × ℕ => min p.1 p.2)
    (encPair encUnary encNat) encUnary := by
  have h := foldlWith (encA := encBool) (encL := encBits) (encP := encUnary)
    (par := Prod.fst) (list := fun p : ℕ × ℕ => p.2.bits.reverse)
    (step := fun cap value bit => min cap (2 * value + bit.toNat))
    (fst encUnary encNat) (bitsReverse.comp (natBits.comp (snd encUnary encNat)))
    (const 0) (by fun_prop) (B := Prod.fst)
    (by simpa only [encUnary_apply, List.length_replicate] using
      (fst encUnary encNat).polyBounded_length)
    (fun p i _ => by
      simpa only [encUnary_apply, List.length_replicate, Cslib.BitString.boundedBinaryValue] using
        Cslib.BitString.boundedBinaryValue_le p.1 (p.2.bits.reverse.take i))
  convert h using 1
  funext p
  rw [← Cslib.BitString.boundedBinaryValue, Cslib.BitString.boundedBinaryValue_eq,
    Cslib.BitString.binaryValue_reverse_bits]

/-- Cap a computed binary natural by a computed unary bound, returning the result in unary. -/
@[fun_prop, program_certificate]
theorem binary_min_unary' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => min (left a) (right a)) input encUnary :=
  binary_min_unary.comp (hleft.prod hright)

/-- Right shift of binary naturals, by dropping at most the dividend's bit length of low-order
digits. -/
theorem binary_shiftRight : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 >>> p.2)
    (encPair encNat encNat) encNat := by
  have hbits := natBits.comp (fst encNat encNat)
  have hlen : ComputableInPolyTime (fun p : ℕ × ℕ => p.1.bits.length)
      (encPair encNat encNat) encUnary := (length encBool).comp hbits
  have hdrop := bitsDropWithInput hbits (binary_min_unary' hlen (snd encNat encNat))
  refine hdrop.of_enc_eq fun p => ?_
  change (p.1 >>> p.2).bits = p.1.bits.drop (min p.1.bits.length p.2)
  rw [Nat.bits_shiftRight, Nat.min_comm]
  exact List.drop_eq_drop_min

end Turing.MultiTapeTM.ComputableInPolyTime

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Bitwise AND of binary naturals. -/
@[fun_prop, program_certificate]
theorem binary_and : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 &&& p.2)
    (encPair encNat encNat) encNat :=
  (ComputableInPolyTime.binary_bitwise and rfl).of_enc_eq fun p =>
    congrArg encNat <| Nat.eq_of_testBit_eq fun i => by
      rw [Nat.testBit_bitwise rfl, Nat.testBit_and]

/-- Bitwise OR of binary naturals, from the linear zip-transducer certificate
`Turing.MultiTapeTM.computableInTimeAndSpace_natOr`. -/
@[fun_prop, program_certificate]
theorem binary_or : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 ||| p.2)
    (encPair encNat encNat) encNat :=
  (ComputableInO.of_linear ComputableInDegree.natOr).computableInPolyTime
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))

/-- Bitwise XOR of binary naturals. -/
@[fun_prop, program_certificate]
theorem binary_xor : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 ^^^ p.2)
    (encPair encNat encNat) encNat :=
  (ComputableInPolyTime.binary_bitwise xor rfl).of_enc_eq fun p =>
    congrArg encNat <| Nat.eq_of_testBit_eq fun i => by
      rw [Nat.testBit_bitwise rfl, Nat.testBit_xor]

/-- Bitwise AND of computed binary naturals. -/
@[fun_prop, program_certificate]
theorem binary_and' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a &&& right a) input encNat :=
  binary_and.comp (hleft.prod hright)

/-- Bitwise OR of computed binary naturals. -/
@[fun_prop, program_certificate]
theorem binary_or' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a ||| right a) input encNat :=
  binary_or.comp (hleft.prod hright)

/-- Bitwise XOR of computed binary naturals. -/
@[fun_prop, program_certificate]
theorem binary_xor' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a ^^^ right a) input encNat :=
  binary_xor.comp (hleft.prod hright)

/-- The bit-length `Nat.size n` of a binary natural, returned in unary. -/
@[fun_prop, program_certificate]
theorem binary_size : ComputableInPolyTime Nat.size encNat encUnary := by
  have hbits : ComputableInPolyTime Nat.bits encNat encBits := of_eq fun _ => rfl
  convert Internal.DecoderWords.unary_degree.computableInPolyTime.comp hbits using 1
  funext n
  exact (Nat.size_eq_bits_len n).symm

/-- Right shift of computed binary naturals. -/
@[fun_prop, program_certificate]
theorem binary_shiftRight' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a >>> right a) input encNat :=
  binary_shiftRight.comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Plain polynomial-time automation -/

namespace Turing.MultiTapeTM.ComputableInPolyTime

-- Preserve the original facade's registration scope for captured binary multiplication.
attribute [fun_prop] binary_mul'

end Turing.MultiTapeTM.ComputableInPolyTime
