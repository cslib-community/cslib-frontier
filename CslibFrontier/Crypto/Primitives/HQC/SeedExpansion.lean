/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Hash.Keccak.Efficient
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

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

* `Cslib.Crypto.HQC.pkeSeeds`: HQC's domain-separated `I` expansion and 32-byte split.
* `Cslib.Crypto.HQC.pkeSeedPrefixes`: requested one-shot SHAKE256 prefixes from the two seeds.
* `Cslib.Crypto.HQC.encPkeSeedPrefixInput`: input bytes followed by the two unary prefix lengths.

## Main results

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

/-- Derive HQC-PKE's 32-byte decryption-key and encryption-key seeds using the hash `I`.

The input is a 32-byte seed in the standardized parameter sets; the executable function remains
total on every byte string, which is useful for its uniform machine certificate. -/
@[expose] def pkeSeeds (seed : List (Fin 256)) : List (Fin 256) × List (Fin 256) :=
  let digest := sha3_512 (seed ++ [0x02])
  (digest.take 32, digest.drop 32)

/-- Both outputs of HQC's `I` expansion are exactly 32 bytes. -/
theorem lengths_pkeSeeds (seed : List (Fin 256)) :
    (pkeSeeds seed).1.length = 32 ∧ (pkeSeeds seed).2.length = 32 := by
  simp [pkeSeeds]

/-- The input to `pkeSeedPrefixes`: seed bytes, then unary decryption- and encryption-seed prefix
lengths, in that order. -/
abbrev encPkeSeedPrefixInput : (List (Fin 256) × (ℕ × ℕ)) ↪ List Bool :=
  encPair encByteStringLE (encPair encUnary encUnary)

/-- Requested one-shot prefixes of the SHAKE256 streams initialized from HQC-PKE's two seeds.

The first requested length belongs to the decryption-key stream and the second to the
encryption-key stream. This function recomputes each requested prefix from its seed. -/
@[expose] def pkeSeedPrefixes
    (input : List (Fin 256) × (ℕ × ℕ)) : List (Fin 256) × List (Fin 256) :=
  let seeds := pkeSeeds input.1
  (shake256 seeds.1 input.2.1, shake256 seeds.2 input.2.2)

/-- The two one-shot seed streams return exactly their requested numbers of bytes. -/
theorem lengths_pkeSeedPrefixes (input : List (Fin 256) × (ℕ × ℕ)) :
    (pkeSeedPrefixes input).1.length = input.2.1 ∧
      (pkeSeedPrefixes input).2.length = input.2.2 := by
  simp [pkeSeedPrefixes]

private theorem computableInPolyTime_domainSeparatedDigest :
    ComputableInPolyTime (fun seed : List (Fin 256) => sha3_512 (seed ++ [0x02]))
      encByteStringLE encByteStringLE := by
  have happended : ComputableInPolyTime
      (fun seed : List (Fin 256) => seed ++ [0x02]) encByteStringLE encByteStringLE :=
    ComputableInPolyTime.of_tidy <|
      Turing.MultiTapeTM.ComputableTidilyInPolyTime.listAppend encByteLE |>.comp
        ((id' (encIn := encByteStringLE)).tidy.prod (const [0x02]).tidy)
  exact computableInPolyTime_sha3_512.comp happended

private theorem firstSeed_eq (seed : List (Fin 256)) :
    (List.range 32).map (fun i => (sha3_512 (seed ++ [0x02])).getD i 0) =
      (sha3_512 (seed ++ [0x02])).take 32 := by
  apply List.ext_getElem
  · simp
  · intro i hi htake
    have hi32 : i < 32 := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    rw [List.getD_eq_getElem _ _ (by
      have := length_sha3_512 (seed ++ [0x02])
      omega)]

private theorem secondSeed_eq (seed : List (Fin 256)) :
    (List.range 32).map (fun i => (sha3_512 (seed ++ [0x02])).getD (32 + i) 0) =
      (sha3_512 (seed ++ [0x02])).drop 32 := by
  apply List.ext_getElem
  · simp
  · intro i hi hdrop
    have hi32 : i < 32 := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
    rw [List.getD_eq_getElem _ _ (by
      have := length_sha3_512 (seed ++ [0x02])
      omega)]

private theorem computableInPolyTime_firstSeed : ComputableInPolyTime
    (fun seed : List (Fin 256) => (sha3_512 (seed ++ [0x02])).take 32)
    encByteStringLE encByteStringLE := by
  have hdigestWithIndex : ComputableInPolyTime
      (fun p : List (Fin 256) × ℕ => sha3_512 (p.1 ++ [0x02]))
      (encPair encByteStringLE encUnary) encByteStringLE :=
    computableInPolyTime_domainSeparatedDigest.comp (fst encByteStringLE encUnary)
  have hfirstByte : ComputableInPolyTime
      (fun p : List (Fin 256) × ℕ => (sha3_512 (p.1 ++ [0x02])).getD p.2 0)
      (encPair encByteStringLE encUnary) encByteLE :=
    listGetDWithInput hdigestWithIndex (snd encByteStringLE encUnary) 0
  have hfirstRaw := mapWithInput
    (f := fun seed : List (Fin 256) => fun i => (sha3_512 (seed ++ [0x02])).getD i 0)
    (list := fun _ : List (Fin 256) => List.range 32)
    (range.comp (const 32)) hfirstByte
  exact hfirstRaw.of_enc_eq fun seed => congrArg encByteStringLE (firstSeed_eq seed)

private theorem computableInPolyTime_secondSeed : ComputableInPolyTime
    (fun seed : List (Fin 256) => (sha3_512 (seed ++ [0x02])).drop 32)
    encByteStringLE encByteStringLE := by
  have hdigestWithIndex : ComputableInPolyTime
      (fun p : List (Fin 256) × ℕ => sha3_512 (p.1 ++ [0x02]))
      (encPair encByteStringLE encUnary) encByteStringLE :=
    computableInPolyTime_domainSeparatedDigest.comp (fst encByteStringLE encUnary)
  have hsecondByte : ComputableInPolyTime
      (fun p : List (Fin 256) × ℕ =>
        (sha3_512 (p.1 ++ [0x02])).getD (32 + p.2) 0)
      (encPair encByteStringLE encUnary) encByteLE :=
    listGetDWithInput hdigestWithIndex
      (unary_add' (const 32) (snd encByteStringLE encUnary)) 0
  have hsecondRaw := mapWithInput
    (f := fun seed : List (Fin 256) => fun i =>
      (sha3_512 (seed ++ [0x02])).getD (32 + i) 0)
    (list := fun _ : List (Fin 256) => List.range 32)
    (range.comp (const 32)) hsecondByte
  exact hsecondRaw.of_enc_eq fun seed => congrArg encByteStringLE (secondSeed_eq seed)

private theorem computableInPolyTime_pkeSeeds_aux :
    ComputableInPolyTime pkeSeeds encByteStringLE
      (encPair encByteStringLE encByteStringLE) := by
  change ComputableInPolyTime
    (fun seed => ((sha3_512 (seed ++ [0x02])).take 32,
      (sha3_512 (seed ++ [0x02])).drop 32)) encByteStringLE
      (encPair encByteStringLE encByteStringLE)
  exact computableInPolyTime_firstSeed.prod computableInPolyTime_secondSeed

/-- HQC's domain-separated SHA3-512 seed split is uniformly polynomial-time. -/
theorem computableInPolyTime_pkeSeeds :
    ComputableInPolyTime pkeSeeds encByteStringLE
      (encPair encByteStringLE encByteStringLE) :=
  computableInPolyTime_pkeSeeds_aux

/-- The two requested one-shot SHAKE256 seed prefixes are uniformly polynomial-time in the
framed seed and the two unary output lengths. -/
theorem computableInPolyTime_pkeSeedPrefixes :
    ComputableInPolyTime pkeSeedPrefixes encPkeSeedPrefixInput
      (encPair encByteStringLE encByteStringLE) := by
  have hseed : ComputableInPolyTime
      (fun input : List (Fin 256) × (ℕ × ℕ) => input.1)
      encPkeSeedPrefixInput encByteStringLE := fst encByteStringLE (encPair encUnary encUnary)
  have hseeds := computableInPolyTime_pkeSeeds.comp hseed
  have hdkSeed := (fst encByteStringLE encByteStringLE).comp hseeds
  have hekSeed := (snd encByteStringLE encByteStringLE).comp hseeds
  have hcounts : ComputableInPolyTime
      (fun input : List (Fin 256) × (ℕ × ℕ) => input.2)
      encPkeSeedPrefixInput (encPair encUnary encUnary) :=
    snd encByteStringLE (encPair encUnary encUnary)
  have hdkCount := (fst encUnary encUnary).comp hcounts
  have hekCount := (snd encUnary encUnary).comp hcounts
  have hdk := computableInPolyTime_shake256.comp (hdkSeed.prod hdkCount)
  have hek := computableInPolyTime_shake256.comp (hekSeed.prod hekCount)
  change ComputableInPolyTime
    (fun input =>
      (shake256 (pkeSeeds input.1).1 input.2.1,
        shake256 (pkeSeeds input.1).2 input.2.2))
    encPkeSeedPrefixInput (encPair encByteStringLE encByteStringLE)
  exact hdk.prod hek

end Cslib.Crypto.HQC
