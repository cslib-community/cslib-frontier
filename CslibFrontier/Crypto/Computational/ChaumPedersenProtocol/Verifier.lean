/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.ChaumPedersenProtocol
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Efficient.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# The Chaum–Pedersen verifier in polynomial time

The verifier of `PrimeOrderGroupFamily.chaumPedersenFamily` ([BonehShoup2023], Section 19.5.2,
Figure 19.7) as a deterministic polynomial-time word function: it checks `z • g = t₁ + c • v` and
`z • u = t₂ + c • w` with the family's word operations and compares the encodings.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenVerifyWord`: the verifier on words.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.verifierRealizedBy_chaumPedersenVerifyWord`:
  `chaumPedersenVerifyWord` realizes the verifier of `chaumPedersenFamily` on encodings.
* `Cslib.Crypto.PrimeOrderGroupFamily.efficientVerifier_chaumPedersen`: the Chaum–Pedersen family
  has an efficient verifier.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 19.5.2.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Turing.MultiTapeTM Protocols Protocols.SigmaProtocol

variable (F : PrimeOrderGroupFamily)

/-- The Chaum–Pedersen verifier on words: on the index `(n, d)`, an encoded statement `(u, v, w)`,
an encoded commitment `(t₁, t₂)` and binary `c` and `z`, compare the encodings of `z • g` with
`t₁ + c • v` and of `z • u` with `t₂ + c • w`. -/
def chaumPedersenVerifyWord
    (p : (ℕ × F.Desc) × List Bool × List Bool × List Bool × List Bool) : Bool :=
  let ((_, d), y, t, c, z) := p
  decide (F.smul (d, ofBits z, F.encode d (F.generator d)) =
      F.add (d, unframe t, F.smul (d, ofBits c, unframe (dropFrame y)))) &&
    decide (F.smul (d, ofBits z, unframe y) =
      F.add (d, dropFrame t, F.smul (d, ofBits c, dropFrame (dropFrame y))))

/-- `chaumPedersenVerifyWord` is computable in polynomial time. -/
theorem computableInPolyTime_chaumPedersenVerifyWord :
    ComputableInPolyTime F.chaumPedersenVerifyWord
      (encPair F.chaumPedersenEncoding.index
        (encPair encBits (encPair encBits (encPair encBits encBits)))) encBool := by
  unfold chaumPedersenVerifyWord
  fun_prop

/-- On encodings, `chaumPedersenVerifyWord` is the verifier of `chaumPedersenFamily`. -/
theorem verifierRealizedBy_chaumPedersenVerifyWord :
    VerifierRealizedBy F.chaumPedersenFamily F.chaumPedersenEncoding
      F.chaumPedersenVerifyWord := by
  rintro ⟨n, d⟩ ⟨u, v, w⟩ ⟨t₁, t₂⟩ c z
  rw [Bool.eq_iff_iff]
  change _ ↔ (F.chaumPedersenFamily (n, d)).Accepts (u, v, w) (t₁, t₂) c z
  rw [chaumPedersenFamily, chaumPedersen_accepts_iff]
  simp only [chaumPedersenVerifyWord, chaumPedersenEncoding, unframe_encPair, dropFrame_encPair,
    encodeEmbedding, encScalar, Function.Embedding.coeFn_mk, encNat_apply, ofBits_bits,
    F.smul_encode, F.add_encode, Bool.and_eq_true, decide_eq_true_eq,
    (F.encode_injective d).eq_iff, ZMod.natCast_zmod_val, Function.Embedding.refl_apply]

/-- **The Chaum–Pedersen protocol has an efficient verifier.** -/
theorem efficientVerifier_chaumPedersen :
    EfficientVerifier F.chaumPedersenFamily F.chaumPedersenEncoding :=
  ⟨F.chaumPedersenVerifyWord, F.computableInPolyTime_chaumPedersenVerifyWord,
    F.verifierRealizedBy_chaumPedersenVerifyWord⟩

end Cslib.Crypto.PrimeOrderGroupFamily
