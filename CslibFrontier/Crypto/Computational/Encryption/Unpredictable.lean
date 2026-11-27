/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.StronglyUnpredictable
public import CslibFrontier.Crypto.Protocols.PKE.ExplicitCoin

/-!
# Unpredictable public-key encryption

Definition 12.6 of Boneh and Shoup ([BonehShoup2023], Section 12.6, printed p. 495) calls a
public-key encryption scheme `ε`-unpredictable "if for every possible output `(pk, sk)` of `G_a`
and every `y ∈ 𝒴`, if we choose `r ∈ ℛ` at random, then we have
`Pr[E_a(pk, D_a(sk, y); r) = y] ≤ ε`", and unpredictable if it is `ε`-unpredictable for a
negligible `ε`: a fresh re-encryption of a ciphertext's decryption is unlikely to reproduce it.

`PKE.EpsilonUnpredictable E ε` is this definition for a scheme `E : PKE PK SK M C`, and
`Encryption.Unpredictable E` is its asymptotic form for a family `E n`. The book assumes in this
section that decryption never rejects, returning a default message instead (pp. 494–495). A `PKE`
may reject, and a rejected ciphertext is unconstrained here. For correct schemes the two readings
agree (`PKE.epsilonUnpredictable_iff_getD_of_correct`), and both agree with bounding a fresh
encryption of every message (`PKE.epsilonUnpredictable_iff_forall_of_correct`).

The library has two other ciphertext-unpredictability notions:

* HHK17 `γ`-spreadness `ExplicitCoinPKE.GammaSpread` bounds a fresh encryption of every message
  on supported keys. It implies `2 ^ (-γ)`-unpredictability
  (`ExplicitCoinPKE.GammaSpread.epsilonUnpredictable`), and is equivalent to it for correct schemes
  (`ExplicitCoinPKE.gammaSpread_iff_epsilonUnpredictable_of_correct`). Without correctness the
  converse fails: a scheme that rejects every ciphertext is `0`-unpredictable.
* `Encryption.CiphertextHitBound` and `Encryption.StronglyUnpredictable` ([BonehShoup2023],
  §21.4.1, p. 872) bound every public key, including keys that key generation never outputs. They
  imply unpredictability (`PKE.ciphertextHitBound_implies_epsilonUnpredictable`); the converse
  fails for a scheme that randomizes only under honest keys.

## Main definitions

* `Cslib.Crypto.PKE.EpsilonUnpredictable`: Definition 12.6, `ε`-unpredictable encryption.
* `Cslib.Crypto.Encryption.Unpredictable`: unpredictable encryption for a family of schemes.

## Main results

* `Cslib.Crypto.PKE.epsilonUnpredictable_iff_forall_of_correct`,
  `Cslib.Crypto.PKE.epsilonUnpredictable_iff_getD_of_correct`: for correct schemes, the bound on
  every message and the default-message form are equivalent to Definition 12.6.
* `Cslib.Crypto.PKE.ciphertextHitBound_implies_epsilonUnpredictable`: a ciphertext hit bound on
  every public key implies Definition 12.6.
* `Cslib.Crypto.Protocols.ExplicitCoinPKE.GammaSpread.epsilonUnpredictable`,
  `Cslib.Crypto.Protocols.ExplicitCoinPKE.gammaSpread_iff_epsilonUnpredictable_of_correct`:
  `γ`-spreadness implies `2 ^ (-γ)`-unpredictability, and is equivalent to it for correct schemes.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 12.6 (printed pp. 494–495) and Section 21.4.1 (p. 872).
-/

public section

namespace Cslib.Crypto.PKE

open Cslib.Probability
open scoped NNReal ENNReal

/-- **Definition 12.6 (`ε`-unpredictable encryption)** ([BonehShoup2023], Section 12.6, p. 495):
for every key pair `(pk, sk)` that `E.keyGen` can output, every ciphertext `y` and every message
`m` with `E.decrypt sk y = some m`, a fresh encryption of `m` under `pk` equals `y` with
probability at most `ε`.

The book's decryption never rejects: it returns a default message instead (pp. 494–495), so the
book bounds every `y`. Here a ciphertext that decryption rejects is unconstrained. The two agree
for correct schemes (`epsilonUnpredictable_iff_getD_of_correct`); for an incorrect scheme this
definition can be weaker. -/
@[expose] def EpsilonUnpredictable {PK SK M C : Type} (E : PKE PK SK M C) (ε : ℝ≥0) : Prop :=
  ∀ keys ∈ (ProbComp.eval E.keyGen).support, ∀ (y : C) (m : M),
    E.decrypt keys.2 y = some m →
      ((ProbComp.eval (E.encrypt keys.1 m)) y).toNNReal ≤ ε

/-- For a correct scheme, `ε`-unpredictability is equivalent to bounding
`Pr[E.encrypt pk m = y] ≤ ε` for every supported key pair `(pk, sk)`, every message `m` and every
ciphertext `y`. Without correctness the forward implication fails, since decryption may reject
honestly generated ciphertexts. -/
theorem epsilonUnpredictable_iff_forall_of_correct {PK SK M C : Type}
    {E : PKE PK SK M C} (hcorr : E.Correct) (ε : ℝ≥0) :
    EpsilonUnpredictable E ε ↔
      ∀ keys ∈ (ProbComp.eval E.keyGen).support, ∀ (m : M) (y : C),
        ((ProbComp.eval (E.encrypt keys.1 m)) y).toNNReal ≤ ε := by
  refine ⟨fun h keys hkeys m y => ?_, fun h keys hkeys y m _ => h keys hkeys m y⟩
  by_cases hmem : y ∈ (ProbComp.eval (E.encrypt keys.1 m)).support
  · exact h keys hkeys y m (hcorr keys hkeys m y hmem)
  · simp [(PMF.apply_eq_zero_iff _ _).2 hmem]

/-- For a correct scheme, `EpsilonUnpredictable` is equivalent to the book's form, in which
decryption returns a default message `m₀` instead of rejecting ([BonehShoup2023], Section 12.6,
pp. 494–495). Without correctness, only the backward implication holds. -/
theorem epsilonUnpredictable_iff_getD_of_correct {PK SK M C : Type}
    {E : PKE PK SK M C} (hcorr : E.Correct) (m₀ : M) (ε : ℝ≥0) :
    EpsilonUnpredictable E ε ↔
      ∀ keys ∈ (ProbComp.eval E.keyGen).support, ∀ y : C,
        ((ProbComp.eval (E.encrypt keys.1 ((E.decrypt keys.2 y).getD m₀))) y).toNNReal ≤ ε :=
  ⟨fun h keys hkeys y =>
      (epsilonUnpredictable_iff_forall_of_correct hcorr ε).mp h keys hkeys _ y,
    fun h keys hkeys y m hdec => by simpa [hdec] using h keys hkeys y⟩

/-- A ciphertext hit bound on every public key (`Encryption.CiphertextHitBound`) implies
`ε`-unpredictability: the hit bound covers every public key and message, whereas Definition 12.6
covers only supported key pairs and the decryption of the ciphertext. -/
theorem ciphertextHitBound_implies_epsilonUnpredictable {PK SK M C : Type}
    {E : PKE PK SK M C} {ε : ℝ≥0}
    (h : Encryption.CiphertextHitBound (fun pk m => some <$> E.encrypt pk m) ε) :
    EpsilonUnpredictable E ε :=
  fun keys _ y m _ => (Encryption.ciphertextHitBound_map_some_iff E.encrypt ε).mp h keys.1 m y

end Cslib.Crypto.PKE

namespace Cslib.Crypto.Encryption

open scoped NNReal

/-- **Unpredictable encryption** ([BonehShoup2023], Section 12.6, Definition 12.6, p. 495) for a
family of public-key encryption schemes `E n`: there is a negligible `ε : ℕ → ℝ≥0` such that each
`E n` is `ε n`-unpredictable. -/
@[expose] def Unpredictable {PK SK M C : ℕ → Type}
    (E : ∀ n, PKE (PK n) (SK n) (M n) (C n)) : Prop :=
  ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n, PKE.EpsilonUnpredictable (E n) (ε n)

end Cslib.Crypto.Encryption

namespace Cslib.Crypto.Protocols.ExplicitCoinPKE

open Cslib.Crypto.PKE Cslib.Probability
open scoped NNReal ENNReal

/-- HHK17 `γ`-spreadness (`ExplicitCoinPKE.GammaSpread`) implies
`(2 : ℝ≥0) ^ (-γ)`-unpredictability of `P.toPKE`, with no correctness hypothesis. -/
theorem GammaSpread.epsilonUnpredictable {PK SK M R CT : Type}
    {P : ExplicitCoinPKE PK SK M R CT} {γ : ℝ} (hγ : P.GammaSpread γ) :
    EpsilonUnpredictable P.toPKE ((2 : ℝ≥0) ^ (-γ)) := by
  intro keys hkeys y m _hdec
  rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
  change ((ProbComp.eval (P.encrypt keys.1 m)) y).toReal ≤ (2 : ℝ) ^ (-γ)
  rw [eval_encrypt_eq_toOuterMeasure]
  exact hγ keys.1 keys.2 hkeys m y

/-- For a correct scheme, `γ`-spreadness of `P` is equivalent to
`(2 : ℝ≥0) ^ (-γ)`-unpredictability of `P.toPKE`. Without correctness, the backward implication
fails. -/
theorem gammaSpread_iff_epsilonUnpredictable_of_correct {PK SK M R CT : Type}
    {P : ExplicitCoinPKE PK SK M R CT} (hcorr : P.toPKE.Correct) (γ : ℝ) :
    P.GammaSpread γ ↔ EpsilonUnpredictable P.toPKE ((2 : ℝ≥0) ^ (-γ)) := by
  refine ⟨fun h => h.epsilonUnpredictable, fun hunpred pk sk hkeys m c => ?_⟩
  have hbound :=
    ((epsilonUnpredictable_iff_forall_of_correct hcorr ((2 : ℝ≥0) ^ (-γ))).mp hunpred)
      (pk, sk) hkeys m c
  rw [← NNReal.coe_le_coe, NNReal.coe_rpow] at hbound
  change ((ProbComp.eval (P.encrypt pk m)) c).toReal ≤ (2 : ℝ) ^ (-γ) at hbound
  rwa [eval_encrypt_eq_toOuterMeasure] at hbound

end Cslib.Crypto.Protocols.ExplicitCoinPKE
