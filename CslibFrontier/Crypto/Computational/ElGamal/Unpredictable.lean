/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.ElGamal.ProbComp
public import CslibFrontier.Crypto.Computational.Encryption.Unpredictable
import CslibFrontier.Crypto.Computational.DiffieHellman.Order
import CslibFrontier.Crypto.Computational.ElGamal.StronglyUnpredictable
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Probability.PMF.Map

/-!
# Multiplicative ElGamal is unpredictable

Section 12.6.2 of Boneh and Shoup ([BonehShoup2023], printed p. 500) notes that multiplicative
ElGamal over a cyclic group of prime order `q` "is `1/q`-unpredictable. Moreover, under the CDH
assumption, it must be the case that `1/q` is negligible."

An encryption `(β • g, β • u + x)` determines its coins `β` through its first component whenever
`β ↦ β • g` is injective, as it is when `g` generates a group of order `q`:

* In a fixed group under exact uniform coins (`elGamalExplicitCoinPKE q g`), a fresh encryption
  equals a given ciphertext with probability at most `1 / q` under every public key and for every
  message, giving `1 / q`-unpredictability (`epsilonUnpredictable_elGamalExplicitCoinPKE`).
* Over a prime-order group family with the fair-coin scheme `elGamalProbExplicitCoinPKE n d`
  (whose key generator, encryption, and decryption are realized on encoded group elements by
  `elGamalKeyGenProb`, `elGamalEncryptProb`, and `elGamalDecryptDet` in
  `CslibFrontier/Crypto/Computational/ElGamal/ProbComp.lean`), drawing `b ← sampleExp n d` in
  strict PPT adds at most `1 / 2 ^ n` to the exact `1 / q` bound (unlike [BonehShoup2023],
  Definition 2.8, p. 30, which allows a negligible runtime-overflow probability), yielding
  `(1 / q + 1 / 2 ^ n)`-unpredictability (`epsilonUnpredictable_elGamalProbExplicitCoinPKE`).
* Along a deterministic schedule of groups `d`, CDH makes `1 / q` negligible
  (`CDH.negligible_inv_order`), so `1 / q + 1 / 2 ^ n` is negligible and the fair-coin schemes
  form an unpredictable family (`CDH.elGamal_unpredictable`). The other claim of §12.6.2,
  one-wayness under CDH, is `CDH.elGamal_oneWay` in
  `CslibFrontier/Crypto/Computational/ElGamal/OneWay.lean`.

## Main results

* `Cslib.Crypto.epsilonUnpredictable_elGamalExplicitCoinPKE`: multiplicative ElGamal over a fixed
  group with exact uniform coins is `1 / q`-unpredictable.
* `Cslib.Crypto.PrimeOrderGroupFamily.epsilonUnpredictable_elGamalProbExplicitCoinPKE`: fair-coin
  multiplicative ElGamal `elGamalProbExplicitCoinPKE n d` is `(1 / q + 1 / 2 ^ n)`-unpredictable.
* `Cslib.Crypto.PrimeOrderGroupFamily.CDH.elGamal_unpredictable`: fair-coin multiplicative ElGamal
  over a group family is unpredictable under CDH.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 12.6.2 (printed pp. 499–500) and Definition 12.6 (printed p. 495).
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
    simp [ExplicitCoinPKE.toPKE, ExplicitCoinPKE.encrypt,
      elGamalExplicitCoinPKEWith, PMF.map, Function.comp_def]
  rw [heval]
  by_cases hc : c ∈ Set.range ((elGamalExplicitCoinPKE q g).encDet u x)
  · obtain ⟨β, rfl⟩ := hc
    rw [PMF.map_apply_of_injective _ hinj, PMF.uniformOfFintype_apply, ZMod.card,
      ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]
  · rw [(PMF.apply_eq_zero_iff _ _).2 (by simpa [PMF.support_map] using hc)]
    simp

namespace PrimeOrderGroupFamily

/-- **Fair-coin multiplicative ElGamal is `(1 / q + 1 / 2 ^ n)`-unpredictable** ([BonehShoup2023],
Section 12.6.2, p. 500; Definition 12.6, p. 495): at security parameter `n` and group description
`d` of prime order `q = F.order d`, the first component `(b : ZMod q) • g` of an encryption under
`elGamalProbExplicitCoinPKE n d` uniquely determines `(b : ZMod q)`, so `sampleExp` sampling gives
ciphertext hit bound `1 / q + 1 / 2 ^ n` (relaxing the book's exact `1 / q` bound under
Definition 2.8's negligible runtime-overflow model, p. 30, to strict fair-coin sampling). -/
theorem epsilonUnpredictable_elGamalProbExplicitCoinPKE (F : PrimeOrderGroupFamily)
    (n : ℕ) (d : F.Desc) :
    PKE.EpsilonUnpredictable (F.elGamalProbExplicitCoinPKE n d).toPKE
      ((F.order d : ℝ≥0)⁻¹ + 1 / 2 ^ n) := by
  refine PKE.ciphertextHitBound_implies_epsilonUnpredictable
    ((Encryption.ciphertextHitBound_map_some_iff _ _).mpr fun u x c => ?_)
  have heq : (F.elGamalProbExplicitCoinPKE n d).toPKE.encrypt u x =
      do let b ← F.sampleExp n d
         return ((b : ZMod (F.order d)) • F.generator d, (b : ZMod (F.order d)) • u + x) := by
    simp [elGamalExplicitCoinPKEWith, ExplicitCoinPKE.toPKE, ExplicitCoinPKE.encrypt]
  rw [heq]
  refine F.eval_bind_sampleExp_apply_le n d _ c fun b₁ b₂ h₁ h₂ => ?_
  simp only [ProbComp.eval_pure, PMF.pure_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    not_not] at h₁ h₂
  exact F.smul_generator_injective d (congrArg Prod.fst (h₁.symm.trans h₂))

/-- **Multiplicative ElGamal is unpredictable under CDH** ([BonehShoup2023], Section 12.6.2, p. 500;
Definition 12.6, p. 495): if CDH holds for `F` along a deterministic schedule of group descriptions
`d`, the fair-coin schemes `(F.elGamalProbExplicitCoinPKE n (d n)).toPKE` form an unpredictable
family (`Encryption.Unpredictable`). Each scheme is `(1 / q + 1 / 2 ^ n)`-unpredictable
(`epsilonUnpredictable_elGamalProbExplicitCoinPKE`, relaxing exact `1 / q` under Definition 2.8,
p. 30, to strict fair-coin sampling), and CDH makes `1 / q` negligible (`CDH.negligible_inv_order`).
The group at each security parameter is fixed so that each `n` has one scheme, as
`Encryption.Unpredictable` requires. -/
theorem CDH.elGamal_unpredictable {F : PrimeOrderGroupFamily} {d : ℕ → F.Desc}
    (hCDH : F.CDH fun n => PMF.pure (d n)) :
    Encryption.Unpredictable fun n => (F.elGamalProbExplicitCoinPKE n (d n)).toPKE :=
  ⟨fun n => (F.order (d n) : ℝ≥0)⁻¹ + 1 / 2 ^ n,
    (CDH.negligible_inv_order hCDH).add negligible_one_div_two_pow,
    fun n => F.epsilonUnpredictable_elGamalProbExplicitCoinPKE n (d n)⟩

end PrimeOrderGroupFamily

end Cslib.Crypto
