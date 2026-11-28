/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.ElGamal.StronglyUnpredictable
public import CslibFrontier.Crypto.Computational.ElGamal.Unpredictable
public import CslibFrontier.Crypto.Computational.Encryption.Unpredictable
public import CslibFrontierTests.Crypto.StronglyUnpredictable
import CslibFrontier.Crypto.Computational.DiffieHellman.Order
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Map

/-!
# Tests for unpredictable public-key encryption

An ordinary `module` client of `Cslib.Crypto.PKE.EpsilonUnpredictable`,
`Cslib.Crypto.Encryption.Unpredictable` and their ElGamal instance:

* **Both outcomes occur.** Padding each message with `n` fresh random bits gives an unpredictable
  family; deterministic encryption does not.
* **Correctness is needed for the equivalences.** A scheme that rejects every ciphertext is
  `0`-unpredictable, yet it is not `γ`-spread for any `γ > 0`, and it fails the default-message
  form of the definition.
* **Unpredictability is weaker than strong unpredictability.** A scheme that randomizes only under
  its honest key is unpredictable but not strongly unpredictable; conversely, strong
  unpredictability implies unpredictability, and CDH along a fixed schedule of groups makes
  `elGamalEncryptProb` strongly unpredictable through `CDH.negligible_inv_order`.
* **Multiplicative ElGamal.** The `1 / q` bound applies to a concrete group, and fails when
  `β ↦ β • g` is not injective.
-/

public section

namespace CslibFrontierTests.Crypto.Unpredictable

open Cslib Cslib.Crypto Cslib.Crypto.PKE Cslib.Crypto.Protocols Cslib.Crypto.Encryption
open Cslib.Crypto.PrimeOrderGroupFamily Cslib.Probability
open CslibFrontierTests.Crypto.StronglyUnpredictable
  (honestOnlyPKE gammaSpread_honestOnlyPKE not_stronglyUnpredictable_honestOnlyPKE)
open scoped NNReal ENNReal

/-! ### Both outcomes of `Encryption.Unpredictable` -/

/-- A correct scheme that pads each Boolean message with `n` fresh random bits. -/
noncomputable def randomPadPKE (n : ℕ) : PKE Unit Unit Bool (List Bool × Bool) where
  keyGen := pure ((), ())
  encrypt _ m := do
    let r ← BitString.sampleList n
    return (r, m)
  decrypt _ c := some c.2

theorem randomPadPKE_correct (n : ℕ) : (randomPadPKE n).Correct := by
  intro _ _ m _ hc
  simp only [randomPadPKE, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hc
  obtain ⟨r, -, rfl⟩ := hc
  rfl

theorem randomPadPKE_unpredictable : Encryption.Unpredictable randomPadPKE := by
  refine ⟨fun n => 1 / 2 ^ n, negligible_one_div_two_pow, fun n keys _ y m hdec => ?_⟩
  obtain ⟨r, m'⟩ := y
  obtain rfl : m' = m := Option.some.inj hdec
  have heval : ProbComp.eval ((randomPadPKE n).encrypt keys.1 m') =
      (BitString.uniformList n).map (·, m') := by
    simp [randomPadPKE, PMF.map, Function.comp_def]
  rw [heval, PMF.map_apply_of_injective _ (Prod.mk_left_injective m')]
  refine (ENNReal.toNNReal_mono ENNReal.coe_ne_top ?_).trans_eq (ENNReal.toNNReal_coe _)
  simpa [ENNReal.coe_div, ENNReal.coe_pow] using BitString.uniformList_apply_le n r

/-- Deterministic identity encryption is not unpredictable. -/
def detPKE (_n : ℕ) : PKE Unit Unit Bool Bool where
  keyGen := pure ((), ())
  encrypt _ m := pure m
  decrypt _ c := some c

theorem not_unpredictable_detPKE : ¬ Encryption.Unpredictable detPKE := by
  rintro ⟨ε, hε, hbound⟩
  have hconst : ∀ n, (1 : ℝ≥0) ≤ ε n := fun n => by
    have hkey : ((), ()) ∈ (ProbComp.eval (detPKE n).keyGen).support := by
      simp [detPKE]
    simpa [detPKE] using hbound n ((), ()) hkey true true rfl
  exact not_negligible_const one_ne_zero (negligible_of_le hε hconst)

/-! ### Correctness is needed for the equivalences -/

/-- An explicit-coin scheme whose decryption rejects every ciphertext. It is not correct, and it
is `0`-unpredictable because no ciphertext decrypts. -/
def alwaysRejectPKE : ExplicitCoinPKE Unit Unit Bool Bool Bool where
  keyGen := pure ((), ())
  sampleCoins := pure false
  encDet _ _ _ := false
  dec _ _ := none

theorem alwaysRejectPKE_epsilonUnpredictable_zero :
    EpsilonUnpredictable alwaysRejectPKE.toPKE 0 := by
  intro _ _ _ _ hdec
  simp [ExplicitCoinPKE.toPKE, alwaysRejectPKE] at hdec

/-- `alwaysRejectPKE` is not `γ`-spread for `γ > 0`, so
`gammaSpread_iff_epsilonUnpredictable_of_correct` needs correctness. -/
theorem not_gammaSpread_alwaysRejectPKE {γ : ℝ} (hγ : 0 < γ) :
    ¬ alwaysRejectPKE.GammaSpread γ := by
  intro hspread
  have hle := hspread () () (by simp [alwaysRejectPKE]) false false
  simp only [alwaysRejectPKE, ProbComp.eval_pure, PMF.toOuterMeasure_apply,
    PMF.pure_apply, Set.indicator_apply, Set.mem_ofPred_eq, ↓reduceIte] at hle
  rw [tsum_fintype, Fintype.sum_bool] at hle
  simp only [Bool.true_eq_false, ↓reduceIte, zero_add, ENNReal.toReal_one] at hle
  have hlt : (2 : ℝ) ^ (-γ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hγ)
  linarith

/-- `alwaysRejectPKE` fails the default-message form at bound `0`, so
`epsilonUnpredictable_iff_getD_of_correct` needs correctness. -/
theorem not_getD_bound_alwaysRejectPKE :
    ¬ ∀ keys ∈ (ProbComp.eval alwaysRejectPKE.toPKE.keyGen).support, ∀ y : Bool,
        ((ProbComp.eval (alwaysRejectPKE.toPKE.encrypt keys.1
          ((alwaysRejectPKE.toPKE.decrypt keys.2 y).getD false))) y).toNNReal ≤ 0 := by
  intro h
  have h0 := h ((), ()) (by simp [ExplicitCoinPKE.toPKE, alwaysRejectPKE]) false
  simp [ExplicitCoinPKE.toPKE, ExplicitCoinPKE.encrypt, alwaysRejectPKE] at h0

/-! ### Unpredictability and strong unpredictability -/

/-- `honestOnlyPKE n` randomizes with `n` fresh bits under its honest key, so the family is
unpredictable. -/
theorem unpredictable_honestOnlyPKE :
    Encryption.Unpredictable fun n => (honestOnlyPKE n).toPKE := by
  refine ⟨fun n => 1 / 2 ^ n, negligible_one_div_two_pow, fun n => ?_⟩
  have hpow : (2 : ℝ≥0) ^ (-(n : ℝ)) = 1 / 2 ^ n := by
    rw [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]
  simpa only [hpow] using (gammaSpread_honestOnlyPKE n).epsilonUnpredictable

/-- Unpredictability does not imply strong unpredictability: under a key that key generation never
outputs, `honestOnlyPKE` encrypts deterministically. -/
theorem unpredictable_and_not_stronglyUnpredictable_honestOnlyPKE :
    Encryption.Unpredictable (fun n => (honestOnlyPKE n).toPKE) ∧
      ¬ StronglyUnpredictable fun n pk m => some <$> (honestOnlyPKE n).toPKE.encrypt pk m :=
  ⟨unpredictable_honestOnlyPKE, not_stronglyUnpredictable_honestOnlyPKE⟩

/-- Strong unpredictability implies unpredictability. -/
example {PK SK M C : ℕ → Type} {E : ∀ n, PKE (PK n) (SK n) (M n) (C n)}
    (h : StronglyUnpredictable (fun n pk m => some <$> (E n).encrypt pk m)) :
    Encryption.Unpredictable E :=
  let ⟨ε, hε, hb⟩ := h
  ⟨ε, hε, fun n => ciphertextHitBound_implies_epsilonUnpredictable (hb n)⟩

/-- CDH along a fixed schedule of groups makes `elGamalEncryptProb` strongly unpredictable, through
`CDH.negligible_inv_order`. -/
example {F : PrimeOrderGroupFamily} {Msg : Type} (encodeMsg : F.Desc → Msg → List Bool)
    {d : ℕ → F.Desc} (hCDH : F.CDH (fun n => PMF.pure (d n))) :
    StronglyUnpredictable
      (fun n pk m => some <$> F.elGamalEncryptProb encodeMsg d n pk m) :=
  F.stronglyUnpredictable_elGamalEncryptProb encodeMsg d (CDH.negligible_inv_order hCDH)

/-! ### Multiplicative ElGamal -/

/-- Over `ZMod 5` with generator `1`, multiplicative ElGamal is `1 / 5`-unpredictable. -/
example : EpsilonUnpredictable (elGamalExplicitCoinPKE 5 (1 : ZMod 5)).toPKE (5 : ℝ≥0)⁻¹ := by
  simpa using epsilonUnpredictable_elGamalExplicitCoinPKE 5 (1 : ZMod 5)
    fun β β' h => by simpa using h

/-- CDH along a deterministic group schedule makes fair-coin multiplicative ElGamal
`elGamalProbExplicitCoinPKE` unpredictable (`CDH.elGamal_unpredictable`). -/
example {F : PrimeOrderGroupFamily} {d : ℕ → F.Desc} (hCDH : F.CDH (fun n => PMF.pure (d n))) :
    Encryption.Unpredictable fun n => (F.elGamalProbExplicitCoinPKE n (d n)).toPKE :=
  PrimeOrderGroupFamily.CDH.elGamal_unpredictable hCDH

/-- Injectivity of `β ↦ β • g` is needed: with `g = 0`, the public key `0` encrypts every message
`x` as `(0, x)`, so the scheme is not `ε`-unpredictable for any `ε < 1`. -/
theorem not_epsilonUnpredictable_elGamal_zero_generator {ε : ℝ≥0} (hε : ε < 1) :
    ¬ EpsilonUnpredictable (elGamalExplicitCoinPKE 5 (0 : ZMod 5)).toPKE ε := by
  intro h
  have hkey : ((0 : ZMod 5), (0 : ZMod 5)) ∈
      (ProbComp.eval (elGamalExplicitCoinPKE 5 (0 : ZMod 5)).toPKE.keyGen).support := by
    simp [ExplicitCoinPKE.toPKE, elGamalExplicitCoinPKEWith]
  have heval : ProbComp.eval ((elGamalExplicitCoinPKE 5 (0 : ZMod 5)).toPKE.encrypt 0 0) =
      PMF.pure (0, 0) := by
    simp only [ExplicitCoinPKE.toPKE, ExplicitCoinPKE.encrypt,
      elGamalExplicitCoinPKEWith, smul_zero, add_zero, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_const]
  have hhit := h _ hkey (0, 0) 0
    (by simp [ExplicitCoinPKE.toPKE, elGamalExplicitCoinPKEWith])
  rw [heval] at hhit
  exact hε.not_ge (by simpa using hhit)

end CslibFrontierTests.Crypto.Unpredictable
