/-
Copyright (c) 2026 Mayank Rathee, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.BinaryBridge
import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.SmoothJohnsonROM

/-!
# Binary 2-to-1 Closed-Form Johnson & `η`-Gap Batched BCS-FRI Random-Oracle Soundness Bounds

Adaptive two-channel BCS random-oracle soundness bounds for binary 2-to-1 `friBatchIOP` in the
closed-form Johnson and `η`-gap regimes, on both `batchProximityLang` and `batchCorrAgreeLang`
([BenSassonCarmonIshaiKoppartySaraf2020]; [BenSassonChiesaSpooner2016]; [ChiesaYogev2024]).

## Main results

* `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_eta`:
  adaptive two-channel binary batched BCS-FRI ROM soundness bounds on `batchProximityLang`.
* `Cslib.Crypto.Protocols.FRI.friBatchBCS_corrAgree_romSoundness_bound_of_johnson`,
  `FRI.friBatchBCS_corrAgree_romSoundness_bound_of_prover_verifier_of_johnson`:
  adaptive two-channel binary batched BCS-FRI ROM soundness bounds on `batchCorrAgreeLang`.

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

section BinaryJohnsonROM

variable {F : Type} [Field F]

/-- **Original explicit-constant Johnson adaptive two-channel batched BCS-FRI ROM soundness**
([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friBatchBCS_romSoundness_bound_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friBatchIOP params t) encSym (params.batchProximityLang t e) P) Q_MT) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friBatchRBRError params
              (ENNReal.ofReal
                (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
                  (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ))))
              e (friJohnsonCommitBound params mJ) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBatchBCS_romSoundness_bound_of_escape params t
    (batchRound0Escape_of_johnson params t hmJ he)
    (weightedLineGapBound_of_johnson params hmJ he) hdec σ hFS hMT

/-- **Original explicit-constant Johnson adaptive two-channel batched BCS-FRI ROM soundness with
separate prover/verifier Merkle budgets** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friBatchRBRError params
              (ENNReal.ofReal
                (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
                  (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ))))
              e (friJohnsonCommitBound params mJ) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape params t
    (batchRound0Escape_of_johnson params t hmJ he)
    (weightedLineGapBound_of_johnson params hmJ he) hdec σ hMT hFS hops

/-- **Original explicit-constant `η`-gap Johnson adaptive two-channel batched BCS-FRI ROM
soundness** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friBatchBCS_romSoundness_bound_of_johnson_eta [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friBatchIOP params t) encSym (params.batchProximityLang t e) P) Q_MT) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friBatchRBRError params
              (ENNReal.ofReal
                (115200 * ((2 ^ params.d : ℝ) ^ 2) /
                  (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ))))
              e (friJohnsonEtaCommitBound params η) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBatchBCS_romSoundness_bound_of_escape params t
    (batchRound0Escape_of_johnson_eta params t hη he)
    (weightedLineGapBound_of_johnson_eta params hη he) hdec σ hFS hMT

/-- **Original explicit-constant `η`-gap Johnson adaptive two-channel batched BCS-FRI ROM soundness
with separate prover/verifier Merkle budgets** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]).
-/
theorem friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_eta
    [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friBatchRBRError params
              (ENNReal.ofReal
                (115200 * ((2 ^ params.d : ℝ) ^ 2) /
                  (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ))))
              e (friJohnsonEtaCommitBound params η) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape params t
    (batchRound0Escape_of_johnson_eta params t hη he)
    (weightedLineGapBound_of_johnson_eta params hη he) hdec σ hMT hFS hops

/-- **Original explicit-constant real-`α` Johnson adaptive two-channel batched BCS-FRI ROM soundness
on `batchCorrAgreeLang`** (corollary of
`friSmoothBatchBCS_corrAgree_romSoundness_bound_of_johnson`). -/
theorem friBatchBCS_corrAgree_romSoundness_bound_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {mJ : ℕ} (hmJ : 1 ≤ mJ) {α : ℝ}
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
      (1 + 1 / (2 * (mJ : ℝ))) ≤ α) (hα_le : α ≤ 1)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friBatchIOP params t) encSym (params.batchCorrAgreeLang t α) P) Q_MT) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchCorrAgreeLang t α) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (max (ENNReal.ofReal
                (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
                  (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ))))
              (max ((friJohnsonCommitBound params mJ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
                (ENNReal.ofReal (α ^ params.q))) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, ← params.toSmooth_batchCorrAgreeLang] at hMT ⊢
  refine (friSmoothBatchBCS_corrAgree_romSoundness_bound_of_johnson params.toSmooth t hmJ
    (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using hα) hα_le hdec σ hFS hMT).trans ?_
  rw [params.toSmooth_dim (Nat.zero_le _)]
  have hle := friSmoothJohnsonCommitBound_toSmooth_le params mJ
  gcongr

/-- **Original explicit-constant real-`α` Johnson adaptive two-channel batched BCS-FRI ROM soundness
with separate prover/verifier Merkle budgets on `batchCorrAgreeLang`** (corollary of
`friSmoothBatchBCS_corrAgree_romSoundness_bound_of_prover_verifier_of_johnson`). -/
theorem friBatchBCS_corrAgree_romSoundness_bound_of_prover_verifier_of_johnson
    [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {mJ : ℕ} (hmJ : 1 ≤ mJ) {α : ℝ}
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
      (1 + 1 / (2 * (mJ : ℝ))) ≤ α) (hα_le : α ≤ 1)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchCorrAgreeLang t α) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (max (ENNReal.ofReal
                (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
                  (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ))))
              (max ((friJohnsonCommitBound params mJ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
                (ENNReal.ofReal (α ^ params.q))) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, ← params.toSmooth_batchCorrAgreeLang,
    ← params.toSmooth_proofOracleQueries]
  refine (friSmoothBatchBCS_corrAgree_romSoundness_bound_of_prover_verifier_of_johnson
    params.toSmooth t hmJ (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using hα) hα_le
    hdec σ hMT hFS hops).trans ?_
  rw [params.toSmooth_dim (Nat.zero_le _)]
  have hle := friSmoothJohnsonCommitBound_toSmooth_le params mJ
  gcongr


end BinaryJohnsonROM

end Cslib.Crypto.Protocols.FRI
