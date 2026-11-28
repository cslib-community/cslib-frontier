/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Commitment.PublicOperations
public import CslibFrontier.Crypto.Computational.PedersenCommitment
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Public-operation certificates for Pedersen commitments

`PrimeOrderGroupFamily.pedersenPublicOperations` certifies deterministic commitment evaluation
on supplied randomness and verification using exactly the public key bytes of `pedersenScheme`.
It reuses `encodePedersenCommit`, the encoded verifier `encodePedersenVerify` and their
polynomial-time certificates from `CslibFrontier.Crypto.Computational.PedersenCommitment`. The ideal
law of the randomness word is the canonical binary encoding of a uniform exponent in `ZMod q`;
the exact map equation recovers `pedersenCommitPairLaw`.

No executable randomness sampler, setup algorithm, or strict-PPT realization of the ideal
commitment law is asserted. In particular, the uniform exponent law is still semantic `PMF` data.
The security games and their existing hiding and binding claims are unchanged.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.pedersenPublicOperations`: efficient public deterministic
  operations with the exact ideal supplied-randomness law.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM

variable (F : PrimeOrderGroupFamily)

/-- Deterministic Pedersen commitment evaluation and verification from `pedersenScheme.encodeKey`,
with the ideal randomness law given by the canonical bits of a uniform `ZMod q` exponent.
This does not certify sampling that law or key generation. -/
noncomputable def pedersenPublicOperations : F.pedersenScheme.PublicOperations where
  commit k m coins :=
    (F.encodePedersenCommit (k.1, F.encode k.1 k.2, ofBits m, ofBits coins), coins)
  randomness k := (PMF.uniformOfFintype (ZMod (F.order k.1))).map (fun r => r.val.bits)
  map_commit k m := by
    simp only [PMF.map_comp, pedersenScheme, pedersenCommitPairLaw]
    congr 1 with r : 1
    have hr : (ofBits r.val.bits : ZMod (F.order k.1)) = r := by
      rw [ofBits_bits, ZMod.natCast_zmod_val]
    simp only [Function.comp_apply, encodePedersenCommit_encode, hr]
  commit_polyTime := by
    have hkey : ComputableInPolyTime
        (fun k : F.PedersenKey => (k.1, F.encode k.1 k.2))
        F.pedersenScheme.encodeKey (encPair F.encDesc encBits) := .of_eq fun _ => rfl
    have hpublic := hkey.comp
      (ComputableInPolyTime.fst F.pedersenScheme.encodeKey (encPair encBits encBits))
    have hrest := ComputableInPolyTime.snd F.pedersenScheme.encodeKey (encPair encBits encBits)
    have hm := ComputableInPolyTime.bitsToNat.comp hrest.fst'
    have hr := ComputableInPolyTime.bitsToNat.comp hrest.snd'
    exact (F.computableInPolyTime_encodePedersenCommit.comp
      (hpublic.fst'.prod (hpublic.snd'.prod (hm.prod hr)))).prod hrest.snd'
  verify_polyTime := by
    have hkey : ComputableInPolyTime
        (fun k : F.PedersenKey => (k.1, F.encode k.1 k.2))
        F.pedersenScheme.encodeKey (encPair F.encDesc encBits) := .of_eq fun _ => rfl
    have hpublic := hkey.comp (ComputableInPolyTime.fst F.pedersenScheme.encodeKey
      (encPair encBits (encPair encBits encBits)))
    have hrest := ComputableInPolyTime.snd F.pedersenScheme.encodeKey
      (encPair encBits (encPair encBits encBits))
    have hv := F.computableInPolyTime_encodePedersenVerify.comp (hpublic.prod hrest)
    convert hv using 1
    funext ⟨⟨d, h⟩, m, c, o⟩
    exact (F.encodePedersenVerify_encode d h m c o).symm

end Cslib.Crypto.PrimeOrderGroupFamily
