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

This module formalizes $\epsilon$-unpredictability and asymptotic unpredictability for public-key
encryption schemes ([BonehShoup2023], Section 12.6, Definition 12.6, p. 495) and establishes the
exact relationships among three ciphertext-unpredictability notions in the library:

* `Cslib.Crypto.PKE.EpsilonUnpredictable` (Boneh–Shoup Definition 12.6): for every supported
  key pair `(pk, sk)` of `E.keyGen`, every ciphertext `y`, and every plaintext `m` returned by
  `E.decrypt sk y = some m`, a fresh encryption of `m` under `pk` outputs `y` with probability at
  most `ε`. No `[Nonempty M]` default-message assumption is baked in.
* `Cslib.Crypto.Encryption.Unpredictable`: asymptotic form for a family `E : ∀ n, PKE ...`,
  requiring `E n` to be `ε n`-unpredictable for some negligible `ε`.
* `Cslib.Crypto.Protocols.ExplicitCoinPKE.GammaSpread` (HHK17 $\gamma$-spreadness on
  `ExplicitCoinPKE`): requires `Pr[encDet pk m r = c] ≤ 2 ^ (-γ)` on supported keys `(pk, sk)`,
  all messages `m`, and all ciphertexts `c`. `GammaSpread γ` unconditionally implies
  `(2 : ℝ≥0) ^ (-γ)`-unpredictability of `P.toPKE`
  (`ExplicitCoinPKE.GammaSpread.epsilonUnpredictable`), and under `P.toPKE.Correct` the two notions
  are equivalent (`ExplicitCoinPKE.gammaSpread_iff_epsilonUnpredictable_of_correct`). Without
  correctness, the converse fails (an always-rejecting scheme is vacuously `0`-unpredictable).
* `Cslib.Crypto.Encryption.CiphertextHitBound` / `StronglyUnpredictable` ([BonehShoup2023],
  §21.4.1): quantifies over **all** `pk : PK` (including unsupported or malformed keys). It strictly
  implies `EpsilonUnpredictable` (`PKE.ciphertextHitBound_implies_epsilonUnpredictable`).

Under `E.Correct`, `PKE.EpsilonUnpredictable` also coincides with bounding encryption of every
message (`PKE.epsilonUnpredictable_iff_forall_of_correct`) and with Boneh–Shoup's default-message
convention returning `m₀` instead of rejecting (`PKE.epsilonUnpredictable_iff_getD_of_correct`,
[BonehShoup2023], pp. 494–495).

## Main definitions

* `Cslib.Crypto.PKE.EpsilonUnpredictable`: Definition 12.6 (`ε`-unpredictable PKE).
* `Cslib.Crypto.Encryption.Unpredictable`: asymptotic unpredictability for a `PKE` family.

## Main results

* `Cslib.Crypto.PKE.epsilonUnpredictable_iff_forall_of_correct`: under `E.Correct`,
  `EpsilonUnpredictable` equals the all-message, all-ciphertext hit bound on supported keys.
* `Cslib.Crypto.PKE.epsilonUnpredictable_iff_getD_of_correct`: equivalence under `E.Correct` with
  modifying decryption to return a default message `m₀` on rejection
  ([BonehShoup2023], pp. 494–495).
* `Cslib.Crypto.PKE.ciphertextHitBound_implies_epsilonUnpredictable`: `CiphertextHitBound` implies
  `EpsilonUnpredictable`.
* `Cslib.Crypto.Protocols.ExplicitCoinPKE.eval_encrypt_eq_toOuterMeasure`: exact `ℝ≥0∞` equality
  between `ProbComp.eval (P.encrypt pk m) c` and the coin outer measure.
* `Cslib.Crypto.Protocols.ExplicitCoinPKE.GammaSpread.epsilonUnpredictable`: `GammaSpread γ` implies
  `(2 : ℝ≥0) ^ (-γ)`-unpredictability.
* `Cslib.Crypto.Protocols.ExplicitCoinPKE.gammaSpread_iff_epsilonUnpredictable_of_correct`:
  equivalence of `GammaSpread γ` and `(2 : ℝ≥0) ^ (-γ)`-unpredictability under `P.toPKE.Correct`.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 12.6 (pp. 494–495) and Section 21.4.1 (p. 872).
-/

public section

namespace Cslib.Crypto.PKE

open Cslib.Probability
open scoped NNReal ENNReal

/-- **Definition 12.6 (`ε`-unpredictable encryption)** ([BonehShoup2023], §12.6, p. 495): for every
supported key pair `(pk, sk)` of `E.keyGen`, every ciphertext `y : C`, and every message `m : M`
such that `E.decrypt sk y = some m`, freshly encrypting `m` under `pk` outputs `y` with probability
at most `ε`. Ciphertexts rejected by decryption (`E.decrypt sk y = none`) impose no constraint. -/
@[expose] def EpsilonUnpredictable {PK SK M C : Type} (E : PKE PK SK M C) (ε : ℝ≥0) : Prop :=
  ∀ keys ∈ (ProbComp.eval E.keyGen).support, ∀ (y : C) (m : M),
    E.decrypt keys.2 y = some m →
      ((ProbComp.eval (E.encrypt keys.1 m)) y).toNNReal ≤ ε

/-- Under scheme correctness (`E.Correct`), `ε`-unpredictability is equivalent to bounding the hit
probability `Pr[E.encrypt pk m = y] ≤ ε` for every supported key pair `(pk, sk)`, every message
`m : M`, and every ciphertext `y : C`. Without correctness, the forward implication fails when
decryption rejects honestly generated ciphertexts. -/
theorem epsilonUnpredictable_iff_forall_of_correct {PK SK M C : Type}
    {E : PKE PK SK M C} (hcorr : E.Correct) (ε : ℝ≥0) :
    EpsilonUnpredictable E ε ↔
      ∀ keys ∈ (ProbComp.eval E.keyGen).support, ∀ (m : M) (y : C),
        ((ProbComp.eval (E.encrypt keys.1 m)) y).toNNReal ≤ ε := by
  refine ⟨fun h keys hkeys m y => ?_, fun h keys hkeys y m _ => h keys hkeys m y⟩
  by_cases hmem : y ∈ (ProbComp.eval (E.encrypt keys.1 m)).support
  · exact h keys hkeys y m (hcorr keys hkeys m y hmem)
  · simp [(PMF.apply_eq_zero_iff _ _).2 hmem]

/-- Under scheme correctness (`E.Correct`), `EpsilonUnpredictable` coincides with the
default-message form where decryption returns `m₀` instead of rejecting ([BonehShoup2023], §12.6,
pp. 494–495). Without correctness, only the backward implication holds. -/
theorem epsilonUnpredictable_iff_getD_of_correct {PK SK M C : Type}
    {E : PKE PK SK M C} (hcorr : E.Correct) (m₀ : M) (ε : ℝ≥0) :
    EpsilonUnpredictable E ε ↔
      ∀ keys ∈ (ProbComp.eval E.keyGen).support, ∀ y : C,
        ((ProbComp.eval (E.encrypt keys.1 ((E.decrypt keys.2 y).getD m₀))) y).toNNReal ≤ ε :=
  ⟨fun h keys hkeys y =>
      (epsilonUnpredictable_iff_forall_of_correct hcorr ε).mp h keys hkeys _ y,
    fun h keys hkeys y m hdec => by simpa [hdec] using h keys hkeys y⟩

/-- Strong per-parameter ciphertext unpredictability (`Encryption.CiphertextHitBound`) implies
`PKE.EpsilonUnpredictable`: the former bounds every public key `pk : PK` and every message `m : M`,
whereas Definition 12.6 restricts to supported key pairs `(pk, sk)` and decrypted messages. -/
theorem ciphertextHitBound_implies_epsilonUnpredictable {PK SK M C : Type}
    {E : PKE PK SK M C} {ε : ℝ≥0}
    (h : Encryption.CiphertextHitBound (fun pk m => some <$> E.encrypt pk m) ε) :
    EpsilonUnpredictable E ε :=
  fun keys _ y m _ => (Encryption.ciphertextHitBound_map_some_iff E.encrypt ε).mp h keys.1 m y

end Cslib.Crypto.PKE

namespace Cslib.Crypto.Encryption

open scoped NNReal

/-- **Unpredictable encryption** ([BonehShoup2023], §12.6, Definition 12.6, p. 495), asymptotic
form over a family of public-key encryption schemes `E : ∀ n, PKE (PK n) (SK n) (M n) (C n)`: there
exists a negligible function `ε : ℕ → ℝ≥0` such that each `E n` is `ε n`-unpredictable. -/
@[expose] def Unpredictable {PK SK M C : ℕ → Type}
    (E : ∀ n, PKE (PK n) (SK n) (M n) (C n)) : Prop :=
  ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n, PKE.EpsilonUnpredictable (E n) (ε n)

end Cslib.Crypto.Encryption

namespace Cslib.Crypto.Protocols.ExplicitCoinPKE

open Cslib.Crypto.PKE Cslib.Probability
open scoped NNReal ENNReal

/-- Exact `ℝ≥0∞` equality between `ProbComp.eval (P.encrypt pk m) c` and the coin outer measure
of `{r | P.encDet pk m r = c}`. -/
theorem eval_encrypt_eq_toOuterMeasure {PK SK M R CT : Type}
    (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (m : M) (c : CT) :
    (ProbComp.eval (P.encrypt pk m)) c =
      (ProbComp.eval P.sampleCoins).toOuterMeasure {r | P.encDet pk m r = c} := by
  have h : ProbComp.eval (P.encrypt pk m) =
      (ProbComp.eval P.sampleCoins).map (P.encDet pk m) := by
    simp [ExplicitCoinPKE.encrypt, PMF.map, Function.comp_def]
  rw [h, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

/-- HHK17 `γ`-spreadness (`ExplicitCoinPKE.GammaSpread`) unconditionally implies
`(2 : ℝ≥0) ^ (-γ)`-unpredictability of `P.toPKE`. -/
theorem GammaSpread.epsilonUnpredictable {PK SK M R CT : Type}
    {P : ExplicitCoinPKE PK SK M R CT} {γ : ℝ} (hγ : P.GammaSpread γ) :
    EpsilonUnpredictable P.toPKE ((2 : ℝ≥0) ^ (-γ)) := by
  intro keys hkeys y m _hdec
  rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
  change ((ProbComp.eval (P.encrypt keys.1 m)) y).toReal ≤ (2 : ℝ) ^ (-γ)
  rw [eval_encrypt_eq_toOuterMeasure]
  exact hγ keys.1 keys.2 hkeys m y

/-- Under `P.toPKE.Correct`, `γ`-spreadness of `P` is equivalent to
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
