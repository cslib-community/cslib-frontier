/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Hash.Keccak.Efficient
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# HQC PKE seed expansion

HQC version 5.1 instantiates `I(str)` as `SHA3-512(str || 0x02)` in Table 3 (p. 15).
`HQC-PKE.Keygen`, line 1 (p. 38), splits the 64-byte result into the 32-byte decryption-key and
encryption-key seeds. The two seeds initialize separate SHAKE256 contexts in lines 2--9.

`pkeSeedPrefixes` gives a one-shot view of requested prefixes of those two SHAKE256 streams. It
does not claim an incremental-context cost, does not formalize `SampleFixedWeightVect$`, and does
not claim that rejection sampling terminates. Both requested prefix lengths are unary, so the
uniform efficiency theorem charges every output byte and required permutation block.

## Main definitions

* `Cslib.Crypto.HQC.pkeSeedDigest`: HQC's domain-separated `I` expansion.
* `Cslib.Crypto.HQC.pkeSeeds`: the 32-byte split of that digest.
* `Cslib.Crypto.HQC.pkeSeedPrefixes`: requested one-shot SHAKE256 prefixes from the two seeds.
* `Cslib.Crypto.HQC.encPkeSeedPrefixInput`: input bytes followed by the two unary prefix lengths.

## Main results

* `Cslib.Crypto.HQC.length_pkeSeedDigest`: the digest has exactly 64 bytes.
* `Cslib.Crypto.HQC.lengths_pkeSeeds`: both derived seeds have exactly 32 bytes.
* `Cslib.Crypto.HQC.lengths_pkeSeedPrefixes`: both returned prefixes have their requested lengths.
* `Cslib.Crypto.HQC.computableInPolyTime_pkeSeeds`,
  `computableInPolyTime_pkeSeedPrefixes`: uniform multitape-Turing-machine certificates.

## References

* [HQC specification, version 5.1][HQC2026], Table 3, p. 15, and `HQC-PKE.Keygen`, p. 38.
-/

public section

namespace Cslib.Crypto.HQC

open Keccak Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-- HQC-PKE's domain-separated hash `I`, before its two 32-byte halves are assigned to the
decryption-key and encryption-key seed streams.

The input is a 32-byte seed in the standardized parameter sets; the executable function remains
total on every byte string, which is useful for its uniform machine certificate. -/
@[expose] def pkeSeedDigest (seed : List (Fin 256)) : List (Fin 256) :=
  sha3512 (seed ++ [0x02])

/-- HQC-PKE's `I` expansion always emits 64 bytes. -/
theorem length_pkeSeedDigest (seed : List (Fin 256)) : (pkeSeedDigest seed).length = 64 := by
  simp [pkeSeedDigest]

/-- Split HQC-PKE's hash `I` into its 32-byte decryption-key and encryption-key seeds. -/
@[expose] def pkeSeeds (seed : List (Fin 256)) : List (Fin 256) × List (Fin 256) :=
  let digest := pkeSeedDigest seed
  (digest.take 32, digest.drop 32)

/-- Both outputs of HQC's `I` expansion are exactly 32 bytes. -/
theorem lengths_pkeSeeds (seed : List (Fin 256)) :
    (pkeSeeds seed).1.length = 32 ∧ (pkeSeeds seed).2.length = 32 := by
  simp [pkeSeeds, length_pkeSeedDigest]

/-- The input to `pkeSeedPrefixes`: seed bytes, then unary decryption- and encryption-seed prefix
lengths, in that order. -/
abbrev encPkeSeedPrefixInput : (List (Fin 256) × (ℕ × ℕ)) ↪ List Bool :=
  encPair encByteStringLE (encPair encUnary encUnary)

/-- Requested one-shot prefixes of the SHAKE256 streams initialized from HQC-PKE's two seeds.

The first requested length belongs to the decryption-key stream and the second to the
encryption-key stream. This function recomputes each requested prefix from its seed. -/
@[expose] def pkeSeedPrefixes :
    (List (Fin 256) × (ℕ × ℕ)) → List (Fin 256) × List (Fin 256) :=
  fun (seed, dkLength, ekLength) =>
    let seeds := pkeSeeds seed
    (shake256 seeds.1 dkLength, shake256 seeds.2 ekLength)

/-- The two one-shot seed streams return exactly their requested numbers of bytes. -/
theorem lengths_pkeSeedPrefixes (input : List (Fin 256) × (ℕ × ℕ)) :
    (pkeSeedPrefixes input).1.length = (Prod.fst ∘ Prod.snd) input ∧
      (pkeSeedPrefixes input).2.length = (Prod.snd ∘ Prod.snd) input := by
  simp [pkeSeedPrefixes]

/-- HQC-PKE's domain-separated hash `I` is uniformly polynomial-time. -/
theorem computableInPolyTime_pkeSeedDigest :
    ComputableInPolyTime pkeSeedDigest
      encByteStringLE encByteStringLE := by
  have happended : ComputableInPolyTime
      (fun seed : List (Fin 256) => seed ++ [0x02]) encByteStringLE encByteStringLE :=
      Turing.MultiTapeTM.ComputableInPolyTime.listAppend encByteLE |>.comp
        ((id' (encIn := encByteStringLE)).prod (const [0x02]))
  change ComputableInPolyTime (fun seed : List (Fin 256) => sha3512 (seed ++ [0x02]))
    encByteStringLE encByteStringLE
  exact computableInPolyTime_sha3512.comp happended

/-- HQC's domain-separated SHA3-512 seed split is uniformly polynomial-time. -/
theorem computableInPolyTime_pkeSeeds :
    ComputableInPolyTime pkeSeeds encByteStringLE
      (encPair encByteStringLE encByteStringLE) := by
  change ComputableInPolyTime
    (fun seed => ((pkeSeedDigest seed).take 32,
      (pkeSeedDigest seed).drop 32)) encByteStringLE
      (encPair encByteStringLE encByteStringLE)
  have hdigest := id' (encIn := encByteStringLE)
  have hsplit : ComputableInPolyTime
      (fun digest : List (Fin 256) => (digest.take 32, digest.drop 32))
      encByteStringLE (encPair encByteStringLE encByteStringLE) :=
    (listTakeWithInput hdigest (const 32)).prod
      (listDropWithInput hdigest (const 32))
  exact hsplit.comp computableInPolyTime_pkeSeedDigest

private theorem computableInPolyTime_pkeSeedPrefixInputs :
    ComputableInPolyTime
      (fun input : List (Fin 256) × (ℕ × ℕ) =>
        (((pkeSeeds input.1).1, input.2.1), ((pkeSeeds input.1).2, input.2.2)))
      encPkeSeedPrefixInput (encPair encByteXofInput encByteXofInput) := by
  have hseed : ComputableInPolyTime
      (fun input : List (Fin 256) × (ℕ × ℕ) => input.1)
      encPkeSeedPrefixInput encByteStringLE := fst encByteStringLE (encPair encUnary encUnary)
  have hseeds : ComputableInPolyTime
      (fun input : List (Fin 256) × (ℕ × ℕ) => pkeSeeds input.1)
      encPkeSeedPrefixInput (encPair encByteStringLE encByteStringLE) :=
    computableInPolyTime_pkeSeeds.comp hseed
  have hdkSeed : ComputableInPolyTime
      (fun input : List (Fin 256) × (ℕ × ℕ) => (pkeSeeds input.1).1)
      encPkeSeedPrefixInput encByteStringLE :=
    (fst encByteStringLE encByteStringLE).comp hseeds
  have hekSeed : ComputableInPolyTime
      (fun input : List (Fin 256) × (ℕ × ℕ) => (pkeSeeds input.1).2)
      encPkeSeedPrefixInput encByteStringLE :=
    (snd encByteStringLE encByteStringLE).comp hseeds
  have hcounts : ComputableInPolyTime
      (fun input : List (Fin 256) × (ℕ × ℕ) => input.2)
      encPkeSeedPrefixInput (encPair encUnary encUnary) :=
    snd encByteStringLE (encPair encUnary encUnary)
  have hdkCount : ComputableInPolyTime
      (fun input : List (Fin 256) × (ℕ × ℕ) => input.2.1)
      encPkeSeedPrefixInput encUnary :=
    (fst encUnary encUnary).comp hcounts
  have hekCount : ComputableInPolyTime
      (fun input : List (Fin 256) × (ℕ × ℕ) => input.2.2)
      encPkeSeedPrefixInput encUnary :=
    (snd encUnary encUnary).comp hcounts
  exact (hdkSeed.prod hdkCount).prod (hekSeed.prod hekCount)

/-- The two requested one-shot SHAKE256 seed prefixes are uniformly polynomial-time in the
framed seed and the two unary output lengths. -/
theorem computableInPolyTime_pkeSeedPrefixes :
    ComputableInPolyTime pkeSeedPrefixes encPkeSeedPrefixInput
      (encPair encByteStringLE encByteStringLE) := by
  have hdk := computableInPolyTime_shake256.comp
    (fst encByteXofInput encByteXofInput)
  have hek := computableInPolyTime_shake256.comp
    (snd encByteXofInput encByteXofInput)
  exact ((hdk.prod hek).comp computableInPolyTime_pkeSeedPrefixInputs).of_enc_eq
    fun _ => rfl

end Cslib.Crypto.HQC
