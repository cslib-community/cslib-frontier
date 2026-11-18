/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Computational.ElGamal.ExplicitCoin
public import CslibFrontier.Crypto.Computational.Encryption.Unpredictable
import CslibFrontier.Crypto.Computational.DiffieHellman.Order
import CslibFrontier.Probability.PMF.Map

/-!
# Multiplicative ElGamal is unpredictable

Section 12.6.2 of Boneh and Shoup ([BonehShoup2023], printed p. 500) notes that multiplicative
ElGamal over a cyclic group of prime order `q` "is `1/q`-unpredictable. Moreover, under the CDH
assumption, it must be the case that `1/q` is negligible."

An encryption `(β • g, β • u + x)` of `elGamalExplicitCoinPKE q g` determines its coins `β`
through its first component whenever `β ↦ β • g` is injective, as it is when `g` generates a group
of order `q`. A fresh encryption therefore equals a given ciphertext with probability at most
`1 / q`, under every public key and for every message, which gives `1 / q`-unpredictability
(`epsilonUnpredictable_elGamalExplicitCoinPKE`). Over a prime-order group family, CDH along a
deterministic schedule of groups makes `1 / q` negligible (`CDH.negligible_inv_order`), so the
schemes over those groups are unpredictable (`CDH.elGamal_unpredictable_ideal`). The other claim
of §12.6.2, one-wayness under CDH, is `CDH.elGamal_oneWay_ideal` in
`CslibFrontier/Crypto/Computational/ElGamal/OneWay.lean`.

Both family theorems are about `elGamalExplicitCoinPKE`, whose key generator and encryption draw
the exponents exactly uniformly from `ZMod q`, and not about the family's fair-coin multiplicative
ElGamal (`elGamalKeyGenProb`, `elGamalEncryptProb`), for which the library has no
unpredictability theorem (#5293). They are ideal-sampling steps toward Theorem 12.12 (p. 501).

## Main results

* `Cslib.Crypto.epsilonUnpredictable_elGamalExplicitCoinPKE`: multiplicative ElGamal over a fixed
  group is `1 / q`-unpredictable.

## Ideal-sampling step

* `Cslib.Crypto.PrimeOrderGroupFamily.CDH.elGamal_unpredictable_ideal`: the schemes with exactly
  uniform exponents over a group family are unpredictable under CDH.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 12.6.2 (printed pp. 499–500) and Theorem 12.12 (printed p. 501).
-/

public section

namespace Cslib.Crypto

open Probability Protocols
open scoped NNReal

/-- **Multiplicative ElGamal is `1 / q`-unpredictable** ([BonehShoup2023], Section 12.6.2, p. 500)
when `β ↦ β • g` is injective, as it is when `g` generates a group of order `q`. The first
component `β • g` of an encryption determines the coins `β`, so under every public key a fresh
encryption equals a given ciphertext with probability at most `1 / q`. -/
theorem epsilonUnpredictable_elGamalExplicitCoinPKE {G : Type} [AddCommGroup G] (q : ℕ)
    [NeZero q] [Module (ZMod q) G] (g : G) (hg : Function.Injective fun β : ZMod q => β • g) :
    PKE.EpsilonUnpredictable (elGamalExplicitCoinPKE q g).toPKE (q : ℝ≥0)⁻¹ := by
  refine PKE.ciphertextHitBound_implies_epsilonUnpredictable
    ((Encryption.ciphertextHitBound_map_some_iff _ _).mpr fun u x c => ?_)
  have hinj : Function.Injective ((elGamalExplicitCoinPKE q g).encDet u x) :=
    fun _ _ h => hg (congrArg Prod.fst h)
  have heval : ProbComp.eval ((elGamalExplicitCoinPKE q g).toPKE.encrypt u x) =
      (PMF.uniformOfFintype (ZMod q)).map ((elGamalExplicitCoinPKE q g).encDet u x) := by
    simp [ExplicitCoinPKE.toPKE, ExplicitCoinPKE.encrypt, elGamalExplicitCoinPKE, PMF.map,
      Function.comp_def]
  rw [heval]
  by_cases hc : c ∈ Set.range ((elGamalExplicitCoinPKE q g).encDet u x)
  · obtain ⟨β, rfl⟩ := hc
    rw [PMF.map_apply_of_injective _ hinj, PMF.uniformOfFintype_apply, ZMod.card,
      ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]
  · rw [(PMF.apply_eq_zero_iff _ _).2 (by simpa [PMF.support_map] using hc)]
    simp

namespace PrimeOrderGroupFamily

/-- Ideal-sampling step toward [BonehShoup2023], Theorem 12.12 (p. 501), not the cited result: if
CDH holds for the family along a deterministic schedule of group descriptions `d`, the schemes
`elGamalExplicitCoinPKE` over the groups `d n` form an unpredictable family. This is the
unpredictability claim of Section 12.6.2 (p. 500) for the scheme whose key generator and
encryption draw the exponents exactly uniformly from `ZMod q`, not for the family's fair-coin
scheme (`elGamalKeyGenProb`, `elGamalEncryptProb`) (#5293). Each scheme is `1 / q`-unpredictable,
and CDH makes `1 / q` negligible. The group at each security parameter is fixed, so that each `n`
has one scheme, as `Encryption.Unpredictable` requires. -/
theorem CDH.elGamal_unpredictable_ideal {F : PrimeOrderGroupFamily} {d : ℕ → F.Desc}
    (hCDH : F.CDH fun n => PMF.pure (d n)) :
    Encryption.Unpredictable fun n =>
      (elGamalExplicitCoinPKE (F.order (d n)) (F.generator (d n))).toPKE :=
  ⟨_, CDH.negligible_inv_order hCDH, fun n =>
    epsilonUnpredictable_elGamalExplicitCoinPKE _ _ (F.smul_generator_injective (d n))⟩

end PrimeOrderGroupFamily

end Cslib.Crypto
