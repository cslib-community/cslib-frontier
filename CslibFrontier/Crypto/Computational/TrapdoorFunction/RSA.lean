/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.RSATrapdoor
public import CslibFrontier.Crypto.Computational.TrapdoorFunction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Composition

/-!
# The RSA trapdoor permutation scheme and RSA key exchange

[BonehShoup2023], Section 10.3 (p. 403), defines the RSA trapdoor permutation scheme `T_RSA` and
states its one-wayness as the RSA assumption (`RSAOneWay`, Attack Game 10.3 and Definition 10.5,
pp. 404–405). Section 10.3.1 (p. 405) instantiates the trapdoor-function key-exchange protocol of
Section 10.2.1 with `T_RSA` and concludes that under the RSA assumption it is key-guessing secure
(`KeyExchange.AnonKESecure`); combining this with the converse direction from
`TrapdoorFunction.keyExchange_anonKESecure_iff_oneWay` (original here) yields the equivalence
`rsaKeyExchange_anonKESecure_iff_rsaOneWay`.

## Main definitions

* `Cslib.Crypto.rsaTrapdoor`: the RSA trapdoor permutation scheme `T_RSA` with domain and range
  `Fin pk.N` at public key `pk = (N, e)` ([BonehShoup2023], Section 10.3, p. 403).
* `Cslib.Crypto.rsaKeyExchange`: anonymous key exchange from `rsaTrapdoor`
  ([BonehShoup2023], Section 10.3.1, p. 405).

## Main results

* `Cslib.Crypto.oneWay_rsaTrapdoor_iff`: `rsaTrapdoor` is `TrapdoorFunction.OneWay` if and only if
  `RSAOneWay` holds ([BonehShoup2023], Section 10.3, pp. 404–405).
* `Cslib.Crypto.rsaKeyExchange_correct`: `rsaKeyExchange gen` satisfies `KeyExchange.Correct`
  ([BonehShoup2023], Section 10.3.1, p. 405).
* `Cslib.Crypto.rsaKeyExchange_anonKESecure_iff_rsaOneWay`: `rsaKeyExchange gen` satisfies
  `KeyExchange.AnonKESecure` if and only if `RSAOneWay gen` holds (the `RSAOneWay → AnonKESecure`
  direction is [BonehShoup2023], Section 10.3.1, p. 405; the converse is original here via
  `TrapdoorFunction.keyExchange_anonKESecure_iff_oneWay`).

## Implementation notes

* **Key distribution and secret key:** `gen : RSAGen` (`ℕ → PMF RSADesc`) is an arbitrary key
  distribution over valid RSA parameter tuples `RSADesc`, in place of Boneh–Shoup's concrete
  prime-pair generator `RSAGen(ℓ, e)` (p. 403); efficient key generation and Definition 10.4
  items 1–5 are not bundled (#5657). The secret key is the full `RSADesc`, while inversion uses
  only `desc.modulus` and `desc.d`.
* **Uniform domain `Fin N`:** Both `TrapdoorFunction.owGame` at `rsaTrapdoor` and
  `rsaInversionGame` sample `x` uniformly from `Fin N`, matching Boneh–Shoup's `x ← Z_n` in
  Attack Game 10.3 (pp. 404–405).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 10.3 (pp. 403–405) and Section 10.3.1 (p. 405).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- The RSA trapdoor permutation scheme `T_RSA` ([BonehShoup2023], Section 10.3, p. 403) for a
distribution `gen` on RSA parameters: the public key is `(N, e)`, evaluation is `x ↦ x ^ e % N`
(`RSAPublicKey.eval`), and trapdoor inversion is `y ↦ y ^ d % N` (`rsaInvert`) on residues
`Fin N`. The secret key is the full `RSADesc`. -/
@[expose]
def rsaTrapdoor (gen : PMF RSADesc) :
    TrapdoorFunction RSAPublicKey RSADesc (fun pk => Fin pk.N) (fun pk => Fin pk.N) where
  keyGen := gen
  publicKey := RSADesc.publicKey
  eval := RSAPublicKey.eval
  invert desc y := ⟨rsaInvert desc.modulus desc.d y, Nat.mod_lt _ desc.modulus_pos⟩
  domain_nonempty desc := ⟨⟨0, desc.modulus_pos⟩⟩

/-- `T_RSA` satisfies `TrapdoorFunction.Correct` ([BonehShoup2023], Section 10.3, p. 404, from
`rsaInvert_rsaEval`). -/
theorem rsaTrapdoor_correct (gen : PMF RSADesc) : (rsaTrapdoor gen).Correct :=
  fun desc _ x => Fin.ext (rsaInvert_rsaEval desc x.isLt)

private theorem isPPT_rsaInverter_iff (inverter : RSAInverter) :
    TrapdoorFunction.Inverter.IsPPT encRSAPublicKey RSAPublicKey.encResidue
      RSAPublicKey.encResidue inverter ↔ inverter.IsPPT := by
  open scoped TrapdoorFunction in
  constructor
  · intro h
    have hprep : ComputableInPolyTime
        (fun x : RSAInput => (x.secParam,
          (⟨x.publicKey, x.challenge⟩ :
            TrapdoorFunction.Transcript RSAPublicKey fun pk => Fin pk.N)))
        encRSAInput
        (encPair encUnary
          (TrapdoorFunction.encTranscript encRSAPublicKey RSAPublicKey.encResidue)) := by
      fun_prop
    refine isPPTOn_iff_encoded.mpr ((IsPPTOn.preprocess h hprep).congr fun x => ?_)
    simp only [Functor.map_map]
    rfl
  · intro h
    have hprep : ComputableInPolyTime
        (fun input : ℕ × TrapdoorFunction.Transcript RSAPublicKey (fun pk => Fin pk.N) =>
          (⟨input.1, input.2.publicKey, input.2.ciphertext⟩ : RSAInput))
        (encPair encUnary
          (TrapdoorFunction.encTranscript encRSAPublicKey RSAPublicKey.encResidue))
        encRSAInput := by
      fun_prop
    refine (IsPPTOn.preprocess (isPPTOn_iff_encoded.mp h) hprep).congr fun input => ?_
    simp only [Functor.map_map]
    rfl

private theorem owGame_rsaTrapdoor (gen : RSAGen) (inverter : RSAInverter) (n : ℕ) :
    (rsaTrapdoor (gen n)).owGame (inverter n) = rsaInversionGame gen inverter n :=
  (rsaInversionGame_eq gen inverter n).symm

/-- **`T_RSA` is a one-way trapdoor function scheme if and only if `RSAOneWay` holds**
([BonehShoup2023], Section 10.3, Attack Game 10.3 and Definition 10.5, pp. 404–405). -/
theorem oneWay_rsaTrapdoor_iff (gen : RSAGen) :
    TrapdoorFunction.OneWay (fun n => rsaTrapdoor (gen n)) encRSAPublicKey
      RSAPublicKey.encResidue RSAPublicKey.encResidue ↔ RSAOneWay gen := by
  simp only [TrapdoorFunction.OneWay, RSAOneWay, isPPT_rsaInverter_iff, owGame_rsaTrapdoor]

/-- Anonymous key exchange based on the RSA trapdoor permutation scheme ([BonehShoup2023],
Section 10.3.1, p. 405). -/
@[expose]
noncomputable def rsaKeyExchange (gen : RSAGen) :
    KeyExchange (TrapdoorFunction.Transcript RSAPublicKey (fun pk => Fin pk.N))
      (fun t => Fin t.publicKey.N) :=
  TrapdoorFunction.keyExchange fun n => rsaTrapdoor (gen n)

/-- Honest executions of `rsaKeyExchange` output the same residue key for Alice and Bob
([BonehShoup2023], Section 10.3.1, p. 405). -/
theorem rsaKeyExchange_correct (gen : RSAGen) : (rsaKeyExchange gen).Correct :=
  TrapdoorFunction.keyExchange_correct fun n => rsaTrapdoor_correct (gen n)

/-- **RSA anonymous key exchange is key-guessing secure if and only if `RSAOneWay` holds.**

[BonehShoup2023], Section 10.3.1 (p. 405), states the `RSAOneWay → AnonKESecure` direction (`mpr`):
"Under the RSA assumption, this is a secure anonymous key exchange protocol." The converse
direction (`mp`), and hence the equivalence, is original here and follows from the converse of
`TrapdoorFunction.keyExchange_anonKESecure_iff_oneWay` together with `oneWay_rsaTrapdoor_iff`. -/
theorem rsaKeyExchange_anonKESecure_iff_rsaOneWay (gen : RSAGen) :
    (rsaKeyExchange gen).AnonKESecure
      (TrapdoorFunction.encTranscript encRSAPublicKey RSAPublicKey.encResidue)
      (fun t => t.publicKey.encResidue) ↔ RSAOneWay gen :=
  (TrapdoorFunction.keyExchange_anonKESecure_iff_oneWay
    (fun n => rsaTrapdoor_correct (gen n))
    encRSAPublicKey RSAPublicKey.encResidue RSAPublicKey.encResidue).trans
    (oneWay_rsaTrapdoor_iff gen)

end Cslib.Crypto
