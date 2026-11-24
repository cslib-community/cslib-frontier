/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Computational.DiffieHellman
import CslibFrontier.Crypto.Computational.Pairing
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import Mathlib.Tactic.NormNum.Prime
import CslibFrontierTests.Crypto.PrimeFieldGroups

/-!
# Pairing group family clients

An ordinary `module` client of `CslibFrontier.Crypto.Computational.Pairing` over the shared
`ZMod p` fixture `CslibFrontierTests.Crypto.PrimeFieldGroups`.

1. **Nonvacuity and bilinear constructor (`PairingGroupFamily.ofSmulGenerator`):** `primePairing`
   instantiates a symmetric pairing over the additive groups `ZMod p` of prime order `p` (with
   generator `1` in all three groups) from the plain multiplication map `(u, v) ↦ u * v` via
   `PairingGroupFamily.ofSmulGenerator` (and `bilinearOfSmulGenerator`), discharging every
   algebraic, encoding and polynomial-time field without `sorry` or hardness assumptions.
2. **Supporting bilinearity characterization (`biadditive_iff_apply_smul_generator`):** checks both
   directions over any `PairingGroupFamily`, a concrete non-biadditive map (`u + v` on `ZMod 5`)
   rejected via (15.7), and a boundary witness (`g₀ = 0` on `ZMod 3`) showing that generator
   surjectivity is needed.
3. **Interface equations & `fun_prop` automation:** exercises `bilinearOfSmulGenerator_apply`,
   `pair_smul_smul`, `pair_smul_generator_smul_generator` (including the symmetric-pairing DDH check
   `e(α • g₀, β • g₀) = e(g₀, γ • g₀) ↔ α * β = γ` of Boneh–Shoup (15.8)),
   `pair_generator_ne_zero`, companion `DecidableEq`, `Companion`'s `fun_prop` rules and
   `computableInPolyTime_encode_pair`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.Pairing

open Cslib Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open CslibFrontierTests.Crypto.PrimeFieldGroups

/-- Encoded field multiplication modulo `p` on binary residues. -/
private def primePairEncoded : PrimeDesc × List Bool × List Bool → List Bool
  | (p, x, y) => ((ofBits x * ofBits y) % p.val).bits

/-- The symmetric pairing `(α, β) ↦ α * β` on the additive groups `ZMod p` of prime order `p`,
with generator `1` in `G₀`, `G₁` and `GT`, constructed from the plain multiplication function via
`PairingGroupFamily.ofSmulGenerator` (and `bilinearOfSmulGenerator`). -/
private abbrev primePairing : PairingGroupFamily :=
  PairingGroupFamily.ofSmulGenerator primeFields primeFields.self primeFields.self
    (fun _ u v => u * v)
    (fun _ α β => by simp [primeFields, self])
    primePairEncoded
    (fun p u v => by
      have : NeZero p.val := ⟨p.property.ne_zero⟩
      simp only [primePairEncoded, primeFields, self, ofBits_bits, ZMod.val_mul])
    (by
      have hp := ComputableInPolyTime.id' (encIn := encDescBitsPair encPrime)
      exact (ComputableInPolyTime.binary_mod'
        (ComputableInPolyTime.binary_mul'
          (Decoder.nat.computableInPolyTime.comp hp.snd'.fst')
          (Decoder.nat.computableInPolyTime.comp hp.snd'.snd'))
        (computableInPolyTime_val.comp hp.fst')).encoding_comp)

private abbrev d7 : PrimeDesc := ⟨7, by norm_num⟩

-- `bilinearOfSmulGenerator_apply` reduces `primePairing.pair` to field multiplication across
-- `module` boundaries: in `ZMod 7`, `3 * 5 = 1`.
example : primePairing.pair d7 3 5 = 1 := by
  simp only [primePairing, PairingGroupFamily.ofSmulGenerator, bilinearOfSmulGenerator_apply]
  decide

-- Concrete encoded pairing evaluation: in `ZMod 7`, `3 * 5 = 15 ≡ 1 (mod 7)`, encoded as `[true]`.
example :
    primePairing.pairEncoded
      (d7, primePairing.G₀.encode d7 3, primePairing.G₁.encode d7 5) = [true] := by
  decide

-- Non-degeneracy and `Companion`'s `DecidableEq` instance on `GT`.
example (P : PairingGroupFamily) (d : P.G₀.Desc) :
    decide (P.pair d (P.G₀.generator d) (P.G₁.generator d) = 0) = false :=
  decide_eq_false P.pair_generator_ne_zero

-- Symmetric-pairing DDH check (Boneh–Shoup (15.8), p. 625): `e(α • g₀, β • g₁) = e(g₀, γ • g₁)`
-- holds if and only if `α * β = γ` in `ZMod q`.
private theorem pair_smul_generator_eq_iff (P : PairingGroupFamily) (d : P.G₀.Desc)
    (α β γ : ZMod (P.G₀.order d)) :
    P.pair d (α • P.G₀.generator d) (β • P.G₁.generator d) =
      P.pair d (P.G₀.generator d) (γ • P.G₁.generator d) ↔ α * β = γ := by
  have h1 : P.G₀.generator d = (1 : ZMod (P.G₀.order d)) • P.G₀.generator d := (one_smul _ _).symm
  rw [P.pair_smul_generator_smul_generator]
  conv_lhs => rhs; rw [h1]
  rw [P.pair_smul_generator_smul_generator, one_mul]
  exact P.GT.toFamily.smul_generator_injective d |>.eq_iff

example :
    (primePairing.pair d7 ((3 : ZMod 7) • primePairing.G₀.generator d7)
        ((5 : ZMod 7) • primePairing.G₁.generator d7) =
      primePairing.pair d7 (primePairing.G₀.generator d7)
        ((1 : ZMod 7) • primePairing.GT.generator d7)) := by
  exact (pair_smul_generator_eq_iff primePairing d7 3 5 1).mpr (by decide)

-- Every `PairingGroupFamily`'s `pair d` satisfies both sides of
-- `biadditive_iff_apply_smul_generator`.
example (P : PairingGroupFamily) (d : P.G₀.Desc) :
    (∀ u u' v, P.pair d (u + u') v = P.pair d u v + P.pair d u' v) ∧
      ∀ u v v', P.pair d u (v + v') = P.pair d u v + P.pair d u v' :=
  (biadditive_iff_apply_smul_generator
    (P.G₀.smul_generator_surjective d)
    (P.G₁.toFamily.smul_generator_surjective d)
    (fun u v => P.pair d u v)).mpr fun α β => by
      rw [P.pair_smul_smul]

-- Conversely, addition `(u, v) ↦ u + v` on `ZMod 5` violates (15.7) at `α = 1, β = 0` and is
-- therefore not biadditive by `biadditive_iff_apply_smul_generator`.
example :
    ¬ ((∀ u u' v : ZMod 5, (u + u') + v = (u + v) + (u' + v)) ∧
        ∀ u v v' : ZMod 5, u + (v + v') = (u + v) + (u + v')) := by
  have hsurj : Function.Surjective fun α : ZMod 5 => α • (1 : ZMod 5) := fun x =>
    ⟨x, mul_one x⟩
  rw [biadditive_iff_apply_smul_generator hsurj hsurj (fun u v : ZMod 5 => u + v)]
  intro h
  have h10 := h 1 0
  revert h10
  decide

-- Boundary witness for `biadditive_iff_apply_smul_generator`: when `g₀ = 0` does not generate
-- `ZMod 3`, a map can satisfy `(15.7)` for all `α, β` without being additive in its first argument.
example :
    let e : ZMod 3 → ZMod 3 → ZMod 3 := fun u _ => if u = 0 then 0 else 1
    (∀ α β : ZMod 3, e (α • (0 : ZMod 3)) (β • (1 : ZMod 3)) = (α * β) • e 0 1) ∧
      ¬ ∀ u u' v : ZMod 3, e (u + u') v = e u v + e u' v := by
  decide

-- `fun_prop` client check: `computableInPolyTime_encode_pair` composes automatically with
-- `PrimeOrderGroupFamily` and `Companion` `fun_prop` certificates (`encode_generator`,
-- `encode_zero`, `encode_add`, `encode_natCast_smul`) across module boundaries without `@[expose]`.
private theorem computableInPolyTime_pairedLinearCombination (P : PairingGroupFamily) :
    ComputableInPolyTime
      (fun x : P.G₀.Desc × ℕ × ℕ =>
        P.GT.encode x.1
          (P.pair x.1 ((x.2.1 : ZMod (P.G₀.order x.1)) • P.G₀.generator x.1)
            ((x.2.2 : ZMod (P.G₀.order x.1)) • P.G₁.generator x.1 + 0) +
            P.GT.generator x.1))
      (encPair P.G₀.encDesc (encPair encNat encNat)) encBits := by
  fun_prop

-- Applying `computableInPolyTime_pairedLinearCombination` to the concrete `primePairing` fixture.
example :
    ComputableInPolyTime
      (fun x : PrimeDesc × ℕ × ℕ =>
        primePairing.GT.encode x.1
          (primePairing.pair x.1 ((x.2.1 : ZMod x.1.val) • (1 : ZMod x.1.val))
            ((x.2.2 : ZMod x.1.val) • (1 : ZMod x.1.val) + 0) + (1 : ZMod x.1.val)))
      (encPair encPrime (encPair encNat encNat)) encBits :=
  computableInPolyTime_pairedLinearCombination primePairing

end CslibFrontierTests.Crypto.Pairing
