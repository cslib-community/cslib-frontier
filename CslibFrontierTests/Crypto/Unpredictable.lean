/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
public import CslibFrontier.Crypto.Computational.ElGamal.StronglyUnpredictable
public import CslibFrontier.Crypto.Protocols.PKE.Unpredictable
import CslibFrontier.Crypto.Computational.DiffieHellman.Order
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for unpredictable public-key encryption and CDH group order bounds

An ordinary `module` client verifying `Cslib.Crypto.PKE.EpsilonUnpredictable`,
`Cslib.Crypto.Encryption.Unpredictable`, and `CDH.negligible_inv_order` across the `module`
boundary:

* **Nonvacuity of `Encryption.Unpredictable`**: `randomPadPKE` (prepending `n` random bits) is
  `Correct` and satisfies `Encryption.Unpredictable`, whereas deterministic `detPKE` fails it.
* **Bridges on `main`**: `StronglyUnpredictable` implies `Encryption.Unpredictable` (`K4b`), and
  `CDH` implies strong unpredictability of `elGamalEncryptProb` via `CDH.negligible_inv_order`
  (`K2`).
* **Hypothesis necessity**:
  1. `PKE.Correct` cannot be dropped in `gammaSpread_iff_epsilonUnpredictable_of_correct` (Probe 1).
  2. `PKE.Correct` cannot be dropped in `epsilonUnpredictable_iff_getD_of_correct` (Probe 2).
  3. Honest-key `EpsilonUnpredictable` / `GammaSpread` does not imply `CiphertextHitBound` /
     `StronglyUnpredictable` (Probe 3).
* **CDH failure on a constant-order group**: `CDH.negligible_inv_order` immediately refutes
  `schnorrGroups.CDH (fun _ => PMF.pure d23)`.
-/

public section

namespace CslibFrontierTests.Crypto.Unpredictable

open Cslib Cslib.Crypto Cslib.Crypto.PKE Cslib.Crypto.Protocols Cslib.Crypto.Encryption
open Cslib.Crypto.PrimeOrderGroupFamily Cslib.Probability
open scoped NNReal ENNReal

/-! ### 1. Positive and negative nonvacuity for `Encryption.Unpredictable` -/

/-- Positive witness: `Correct` scheme padding each Boolean message with `n` fresh random bits. -/
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
  have hym : y.2 = m := by
    simp only [randomPadPKE, Option.some.injEq] at hdec
    exact hdec
  simp only [randomPadPKE, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
  have hle :
      ((BitString.uniformList n).bind fun r => PMF.pure (r, m)) y ≤
        ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
    rw [PMF.bind_apply]
    have hsub : ∀ r : List Bool,
        BitString.uniformList n r * PMF.pure (r, m) y ≤
          if r = y.1 then ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) else 0 := by
      intro r
      by_cases hr : r = y.1
      · subst hr
        have hpair : (y.1, m) = y := Prod.ext rfl hym.symm
        simp only [↓reduceIte, PMF.pure_apply, hpair, mul_one]
        simpa [ENNReal.coe_div, ENNReal.coe_one, ENNReal.coe_pow] using
          BitString.uniformList_apply_le n y.1
      · have hne : (r, m) ≠ y := fun h => hr (congrArg Prod.fst h)
        simp [hr, PMF.pure_apply, ne_comm.mp hne]
    exact (tsum_le_tsum hsub).trans (by simp)
  exact (ENNReal.toNNReal_mono ENNReal.coe_ne_top hle).trans_eq (ENNReal.toNNReal_coe _)

/-- Negative witness: deterministic identity `PKE` fails `Encryption.Unpredictable`. -/
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

/-! ### 2. Hypothesis necessity (Probes 1–3) -/

/-- An always-rejecting explicit-coin scheme: `PKE.Correct` fails while `EpsilonUnpredictable`
holds vacuously at bound `0` (Probes 1 and 2). -/
def uncorrectAlwaysRejectPKE : ExplicitCoinPKE Unit Unit Bool Bool Bool where
  keyGen := pure ((), ())
  sampleCoins := pure false
  encDet _ _ _ := false
  dec _ _ := none

theorem probe1_epsilonUnpredictable_zero :
    EpsilonUnpredictable uncorrectAlwaysRejectPKE.toPKE 0 := by
  intro _ _ _ _ hdec
  simp [ExplicitCoinPKE.toPKE, uncorrectAlwaysRejectPKE] at hdec

theorem probe1_not_gammaSpread {γ : ℝ} (hγ : 0 < γ) :
    ¬ uncorrectAlwaysRejectPKE.GammaSpread γ := by
  intro hspread
  have hle := hspread () () (by simp [uncorrectAlwaysRejectPKE]) false false
  simp only [uncorrectAlwaysRejectPKE, ProbComp.eval_pure, PMF.toOuterMeasure_apply,
    PMF.pure_apply, Set.indicator_apply, Set.mem_ofPred_eq, ↓reduceIte] at hle
  rw [tsum_fintype, Fintype.sum_bool] at hle
  simp only [Bool.true_eq_false, ↓reduceIte, zero_add, ENNReal.toReal_one] at hle
  have hlt : (2 : ℝ) ^ (-γ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hγ)
  linarith

theorem probe2_not_getD_epsilonUnpredictable :
    ¬ ∀ keys ∈ (ProbComp.eval uncorrectAlwaysRejectPKE.toPKE.keyGen).support, ∀ y : Bool,
        ((ProbComp.eval (uncorrectAlwaysRejectPKE.toPKE.encrypt keys.1
          ((uncorrectAlwaysRejectPKE.toPKE.decrypt keys.2 y).getD false))) y).toNNReal ≤ 0 := by
  intro h
  have h0 := h ((), ()) (by simp [ExplicitCoinPKE.toPKE, uncorrectAlwaysRejectPKE]) false
  simp [ExplicitCoinPKE.toPKE, ExplicitCoinPKE.encrypt, uncorrectAlwaysRejectPKE] at h0

/-- Honest-key spread scheme that is deterministic on adversarial key `false` (Probe 3). -/
noncomputable def honestOnlySpreadPKE : ExplicitCoinPKE Bool Bool Unit Bool Bool where
  keyGen := pure (true, true)
  sampleCoins := ProbComp.uniform Bool
  encDet pk _ r := if pk then r else false
  dec _ _ := some ()

theorem probe3_epsilonUnpredictable_half :
    EpsilonUnpredictable honestOnlySpreadPKE.toPKE (1 / 2) := by
  have hspread : honestOnlySpreadPKE.GammaSpread 1 := by
    intro pk sk hkeys m c
    simp only [honestOnlySpreadPKE, ProbComp.eval_pure, PMF.support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hkeys
    obtain ⟨rfl, rfl⟩ := hkeys
    simp only [honestOnlySpreadPKE, ↓reduceIte, ProbComp.eval_uniform, PMF.toOuterMeasure_apply]
    have hsum :
        ∑' r : Bool, ({r | r = c}.indicator (PMF.uniformOfFintype Bool)) r =
          (PMF.uniformOfFintype Bool) c := by
      rw [tsum_eq_single c]
      · simp
      · intro r hr
        simp [hr]
    rw [hsum, PMF.uniformOfFintype_apply, Fintype.card_bool]
    norm_num
  have hpow : ((2 : ℝ≥0) ^ (-(1 : ℝ))) = 1 / 2 := by
    ext
    simp only [NNReal.coe_rpow, NNReal.coe_ofNat, NNReal.coe_div, NNReal.coe_one]
    norm_num
  simpa [hpow] using hspread.epsilonUnpredictable

theorem probe3_not_ciphertextHitBound :
    ¬ CiphertextHitBound
        (fun pk m => some <$> honestOnlySpreadPKE.toPKE.encrypt pk m) (1 / 2) := by
  intro h
  have h1 := (ciphertextHitBound_map_some_iff _ _).mp h false () false
  have henc : (ProbComp.eval (honestOnlySpreadPKE.toPKE.encrypt false ())) false = 1 := by
    have hmap :
        ProbComp.eval (honestOnlySpreadPKE.toPKE.encrypt false ()) =
          (PMF.uniformOfFintype Bool).map (fun _ => false) := by
      simp [ExplicitCoinPKE.toPKE, ExplicitCoinPKE.encrypt, honestOnlySpreadPKE]
    rw [hmap, PMF.map_apply]
    simp only [↓reduceIte, PMF.tsum_coe]
  rw [henc] at h1
  simp only [ENNReal.toNNReal_one] at h1
  have h1' : (1 : ℝ) ≤ 1 / 2 := by exact_mod_cast h1
  norm_num at h1'

/-! ### 3. Bridges with `StronglyUnpredictable` and CDH group order (`K4b`, `K2`, `d23`) -/

/-- `StronglyUnpredictable` implies `Encryption.Unpredictable` (`K4b`). -/
example {PK SK M C : ℕ → Type} {E : ∀ n, PKE (PK n) (SK n) (M n) (C n)}
    (h : StronglyUnpredictable (fun n pk m => some <$> (E n).encrypt pk m)) :
    Encryption.Unpredictable E :=
  let ⟨ε, hε, hb⟩ := h
  ⟨ε, hε, fun n => ciphertextHitBound_implies_epsilonUnpredictable (hb n)⟩

/-- `CDH` on a deterministic group schedule makes `elGamalEncryptProb` strongly unpredictable via
`CDH.negligible_inv_order` (`K2`). -/
example {F : PrimeOrderGroupFamily} {Msg : Type} (encodeMsg : F.Desc → Msg → List Bool)
    {d : ℕ → F.Desc} (hCDH : F.CDH (fun n => PMF.pure (d n))) :
    StronglyUnpredictable
      (fun n pk m => some <$> F.elGamalEncryptProb encodeMsg d n pk m) :=
  F.stronglyUnpredictable_elGamalEncryptProb encodeMsg d (CDH.negligible_inv_order hCDH)

/-- `CDH` on a general setup makes the expected inverse order negligible. -/
example {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc} (hCDH : F.CDH setup) :
    Negligible fun n => (∑' d, setup n d * (F.order d : ℝ≥0∞)⁻¹).toNNReal :=
  CDH.negligible_expected_inv_order hCDH

/-- The Schnorr group of order `11` in `(ZMod 23)ˣ`, generated by `2`. -/
def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- Constant small Schnorr group `d23` (order `11`) cannot satisfy `CDH`
(`CDH.negligible_inv_order` yields a constant nonzero negligible bound). -/
theorem not_cdh_schnorr_d23 : ¬ schnorrGroups.CDH (fun _ => PMF.pure d23) := by
  intro hCDH
  have hneg : Negligible fun _ : ℕ => (schnorrGroups.order d23 : ℝ≥0)⁻¹ :=
    CDH.negligible_inv_order hCDH
  have hord : (schnorrGroups.order d23 : ℝ≥0)⁻¹ ≠ 0 := by
    have hval : schnorrGroups.order d23 = 11 := rfl
    rw [hval]
    norm_num
  exact not_negligible_const hord hneg

end CslibFrontierTests.Crypto.Unpredictable
