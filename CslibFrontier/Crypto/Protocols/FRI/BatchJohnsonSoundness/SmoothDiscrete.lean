/-
Copyright (c) 2026 Mayank Rathee, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.SmoothBridge
import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.Helpers

/-!
# Smooth Discrete Guruswami–Sudan Batched FRI IOP Soundness and BCS-FRI ROM Bounds

Explicit-parameter `(m₀, D₀)` and `(mRound, DRound)` Guruswami–Sudan commit-phase, interactive IOP,
and adaptive two-channel BCS random-oracle soundness bounds for `friSmoothBatchIOP`
([BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 and Section 8.2.1;
[BenSassonChiesaSpooner2016]; [ChiesaYogev2024]).

## Main results

* `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_le_of_johnson_discrete`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_le_of_johnson_discrete`:
  explicit-parameter Guruswami–Sudan commit-phase and interactive IOP soundness bounds for
  `friSmoothBatchIOP`.
* `Cslib.Crypto.Protocols.FRI.friSmoothBatchBCS_romSoundness_bound_of_johnson_discrete`,
  `FRI.friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_discrete`:
  adaptive two-channel BCS-FRI ROM soundness bounds in the discrete Guruswami–Sudan regime.

## References

* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, *Proximity Gaps for Reed–Solomon
  Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024]
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Finset Cslib.Code Cslib.OracleComp Cslib.Crypto.Protocols.BCS Cslib.Probability

section SmoothDiscreteJohnson

variable {F : Type} [Field F]

/-- **Explicit-parameter Guruswami–Sudan step toward smooth batched FRI commit-phase soundness**
(after [BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 / Section 8.2.1 p. 42). -/
theorem friSmoothBatchCommitGame_le_of_johnson_discrete [Fintype F]
    (params : FRISmoothParams F) (t : ℕ) {e m₀ D₀ B_batch : ℕ}
    (hm₀ : 1 ≤ m₀)
    (hk₀_le : params.dim 0 ≤ 2 ^ params.d - e)
    (hinterp₀ : 2 ^ params.d * (m₀ * (m₀ + 1) / 2) <
      #(Sudan.monomials (params.dim 0 - 1) D₀))
    (hroot₀ : D₀ < m₀ * (2 ^ params.d - e))
    (hbound₀ : ProximityGap.johnsonCurveBound (2 ^ params.d) m₀
      (params.dim 0 - 1) D₀ 1 (2 ^ params.d) ≤ B_batch)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤
        params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      params.domainSize (i.val + 1) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i <
        mRound i * (params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1)))
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friSmoothBatchCommitGame params t (2 ^ params.d - e - 1) stmt P true ≤
      ((B_batch + ∑ i : Fin params.m,
          ProximityGap.johnsonCurveBound (params.domainSize (i.val + 1)) (mRound i)
            (params.dim (i.val + 1) - 1) (DRound i) (params.arity i - 1) (2 ^ params.d) : ℕ) :
        ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  have he_lt : e < 2 ^ params.d := lt_two_pow_of_not_mem_friBatchProximityLang hfar
  exact (friSmoothBatchCommitGame_le_of_escape params t
    (smoothBatchRound0Escape_of_johnson_discrete params t hm₀ hk₀_le hinterp₀ hroot₀ hbound₀)
    (weightedCurveEscapePerRound_of_gapPerRound params
      (weightedCurveGapPerRound_of_johnson_discrete params he_lt mRound DRound hm hk_le hinterp
        hroot)) hfar P).trans_eq (add_sum_natCast_div_ennreal _ _ _ _)

/-- **Explicit-parameter Guruswami–Sudan step toward interactive smooth batched FRI soundness**. -/
theorem friSmoothBatchIOP_interactiveGame_le_of_johnson_discrete [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e m₀ D₀ B_batch : ℕ}
    (hm₀ : 1 ≤ m₀)
    (hk₀_le : params.dim 0 ≤ 2 ^ params.d - e)
    (hinterp₀ : 2 ^ params.d * (m₀ * (m₀ + 1) / 2) <
      #(Sudan.monomials (params.dim 0 - 1) D₀))
    (hroot₀ : D₀ < m₀ * (2 ^ params.d - e))
    (hbound₀ : ProximityGap.johnsonCurveBound (2 ^ params.d) m₀
      (params.dim 0 - 1) D₀ 1 (2 ^ params.d) ≤ B_batch)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤
        params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      params.domainSize (i.val + 1) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i <
        mRound i * (params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1)))
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friSmoothBatchIOP params t) stmt P true ≤
      ((B_batch + ∑ i : Fin params.m,
            ProximityGap.johnsonCurveBound (params.domainSize (i.val + 1)) (mRound i)
              (params.dim (i.val + 1) - 1) (DRound i) (params.arity i - 1) (2 ^ params.d) : ℕ) :
          ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  have he_lt : e < 2 ^ params.d := lt_two_pow_of_not_mem_friBatchProximityLang hfar
  refine (friSmoothBatchIOP_interactiveGame_le_of_escape params t
    (smoothBatchRound0Escape_of_johnson_discrete params t hm₀ hk₀_le hinterp₀ hroot₀ hbound₀)
    (weightedCurveEscapePerRound_of_gapPerRound params
      (weightedCurveGapPerRound_of_johnson_discrete params he_lt mRound DRound hm hk_le hinterp
        hroot)) hfar P).trans_eq ?_
  rw [friSmoothBatchSumError, friSmoothSumError, ← add_assoc, add_sum_natCast_div_ennreal]

/-- **Explicit-parameter Guruswami–Sudan adaptive two-channel smooth batched BCS-FRI ROM
soundness** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friSmoothBatchBCS_romSoundness_bound_of_johnson_discrete [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e m₀ D₀ B_batch B_commit : ℕ} (he : e < 2 ^ params.d)
    (hm₀ : 1 ≤ m₀)
    (hk₀_le : params.dim 0 ≤ 2 ^ params.d - e)
    (hinterp₀ : 2 ^ params.d * (m₀ * (m₀ + 1) / 2) <
      #(Sudan.monomials (params.dim 0 - 1) D₀))
    (hroot₀ : D₀ < m₀ * (2 ^ params.d - e))
    (hbound₀ : ProximityGap.johnsonCurveBound (2 ^ params.d) m₀
      (params.dim 0 - 1) D₀ 1 (2 ^ params.d) ≤ B_batch)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤
        params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      params.domainSize (i.val + 1) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i <
        mRound i * (params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1)))
    (hbound : ∀ i : Fin params.m,
      ProximityGap.johnsonCurveBound (params.domainSize (i.val + 1)) (mRound i)
        (params.dim (i.val + 1) - 1) (DRound i) (params.arity i - 1) (2 ^ params.d) ≤ B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friSmoothBatchIOP params t) encSym (params.batchProximityLang t e) P)
      Q_MT) :
    bcsSoundnessGame (friSmoothBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friSmoothBatchRBRError params ((B_batch : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) e B_commit +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friSmoothBatchBCS_romSoundness_bound_of_escape params t
    (smoothBatchRound0Escape_of_johnson_discrete params t hm₀ hk₀_le hinterp₀ hroot₀ hbound₀)
    (weightedCurveGapBound_of_johnson_discrete params he mRound DRound hm hk_le hinterp hroot
      hbound) hdec σ hFS hMT

/-- **Explicit-parameter Guruswami–Sudan adaptive two-channel smooth batched BCS-FRI ROM soundness
with separate prover/verifier Merkle budgets** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]).
-/
theorem friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_discrete
    [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e m₀ D₀ B_batch B_commit : ℕ} (he : e < 2 ^ params.d)
    (hm₀ : 1 ≤ m₀)
    (hk₀_le : params.dim 0 ≤ 2 ^ params.d - e)
    (hinterp₀ : 2 ^ params.d * (m₀ * (m₀ + 1) / 2) <
      #(Sudan.monomials (params.dim 0 - 1) D₀))
    (hroot₀ : D₀ < m₀ * (2 ^ params.d - e))
    (hbound₀ : ProximityGap.johnsonCurveBound (2 ^ params.d) m₀
      (params.dim 0 - 1) D₀ 1 (2 ^ params.d) ≤ B_batch)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤
        params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      params.domainSize (i.val + 1) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i <
        mRound i * (params.domainSize (i.val + 1) - e / 2 ^ params.cumLog (i.val + 1)))
    (hbound : ∀ i : Fin params.m,
      ProximityGap.johnsonCurveBound (params.domainSize (i.val + 1)) (mRound i)
        (params.dim (i.val + 1) - 1) (DRound i) (params.arity i - 1) (2 ^ params.d) ≤ B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friSmoothBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friSmoothBatchRBRError params ((B_batch : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) e B_commit +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_escape params t
    (smoothBatchRound0Escape_of_johnson_discrete params t hm₀ hk₀_le hinterp₀ hroot₀ hbound₀)
    (weightedCurveGapBound_of_johnson_discrete params he mRound DRound hm hk_le hinterp hroot
      hbound) hdec σ hMT hFS hops

end SmoothDiscreteJohnson

end Cslib.Crypto.Protocols.FRI
