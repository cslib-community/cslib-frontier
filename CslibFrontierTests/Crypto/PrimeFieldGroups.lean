/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Computational.DiscreteLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-! Shared fixture: the additive groups `ZMod p` of prime order `p` as a `PrimeOrderGroupFamily`,
exported for ordinary module clients. A discrete logarithm in these groups is read off the
encoding, since `α • 1` is encoded by the residue of `α`, so no hardness assumption holds for
them: they show only that the structure is inhabited and that its encodings compute. -/

public section

namespace CslibFrontierTests.Crypto.PrimeFieldGroups

open Cslib Cslib.Crypto Turing.MultiTapeTM

/-- Primes, as public group parameters. -/
abbrev PrimeDesc : Type := {p : ℕ // p.Prime}

/-- A prime is encoded by its binary digits. -/
abbrev encPrime : PrimeDesc ↪ List Bool :=
  (Function.Embedding.subtype _).trans encNat

theorem computableInPolyTime_val :
    ComputableInPolyTime (Subtype.val : PrimeDesc → ℕ) encPrime encNat :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- Addition modulo `p` of binary residues. -/
def primeAdd : PrimeDesc × List Bool × List Bool → List Bool
  | (p, x, y) => ((ofBits x + ofBits y) % p.val).bits

/-- Multiplication modulo `p` of a binary residue by a natural number. -/
def primeSMul : PrimeDesc × ℕ × List Bool → List Bool
  | (p, a, x) => (a * ofBits x % p.val).bits

/-- The additive groups `ZMod p` of prime order `p`, with generator `1` and residues encoded in
binary. -/
abbrev primeFields : PrimeOrderGroupFamily where
  Desc := PrimeDesc
  encDesc := encPrime
  order p := p.val
  prime_order p := p.property
  Carrier p := ZMod p.val
  generator _ := 1
  card_carrier p := Nat.card_zmod p.val
  generator_ne_zero p := by
    have := Fact.mk p.property
    exact one_ne_zero
  encode _ x := x.val.bits
  encode_injective p x y h := by
    have : NeZero p.val := ⟨p.property.ne_zero⟩
    exact ZMod.val_injective _ (encNat.injective h)
  add := primeAdd
  add_encode p x y := by
    have : NeZero p.val := ⟨p.property.ne_zero⟩
    simp only [primeAdd, ofBits_bits, ZMod.val_add]
  smul := primeSMul
  smul_encode p a x := by
    have : NeZero p.val := ⟨p.property.ne_zero⟩
    simp only [primeSMul, ofBits_bits, smul_eq_mul, ZMod.val_mul, ZMod.val_natCast,
      Nat.mod_mul_mod]
  computableInPolyTime_order := computableInPolyTime_val
  computableInPolyTime_generator := by
    simp only [ZMod.val_one_eq_one_mod]
    exact (ComputableInPolyTime.binary_mod' (ComputableInPolyTime.const 1)
      computableInPolyTime_val).encoding_comp
  computableInPolyTime_add := by
    have hp := ComputableInPolyTime.id' (encIn := encDescBitsPair encPrime)
    exact (ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_add'
        (Decoder.nat.computableInPolyTime.comp hp.snd'.fst')
        (Decoder.nat.computableInPolyTime.comp hp.snd'.snd'))
      (computableInPolyTime_val.comp hp.fst')).encoding_comp
  computableInPolyTime_smul := by
    have hp := ComputableInPolyTime.id'
      (encIn := encPair encPrime (encPair encNat encBits))
    exact (ComputableInPolyTime.binary_mod'
      (ComputableInPolyTime.binary_mul' hp.snd'.fst'
        (Decoder.nat.computableInPolyTime.comp hp.snd'.snd'))
      (computableInPolyTime_val.comp hp.fst')).encoding_comp

end CslibFrontierTests.Crypto.PrimeFieldGroups
