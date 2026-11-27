/-
Copyright (c) 2026 Mayank Rathee, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.BinaryBridge
import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.SmoothUnique

/-!
# Binary 2-to-1 Unique-Decoding Batched FRI IOP Soundness and BCS-FRI ROM Bounds

Binary 2-to-1 corollaries of the unique-decoding batched FRI commit-phase, interactive IOP, and
adaptive two-channel BCS random-oracle soundness bounds ([BenSassonCarmonIshaiKoppartySaraf2020],
Section 8.2; [BenSassonChiesaSpooner2016]; [ChiesaYogev2024]).

## Main results

* `Cslib.Crypto.Protocols.FRI.friBatchUniqueCommitError_ennreal_eq`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_proximity_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_le_of_unique`: unique-decoding commit-phase bounds
  for `friBatchCommitGame`.
* `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_proximity_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_sound_of_unique`: unique-decoding interactive IOP
  soundness bounds and contrapositive for `friBatchIOP`.
* `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_prover_verifier_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_corrAgree_romSoundness_bound_of_unique`: adaptive
  two-channel BCS-FRI ROM soundness bounds for `friBatchIOP` in the unique-decoding regime.

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

section BinaryUnique

variable {F : Type} [Field F]

private theorem friBatchUniqueCommitError_eq_smooth [Fintype F] (params : FRIParams F) :
    friBatchUniqueCommitError params = friSmoothBatchUniqueCommitError params.toSmooth := by
  simp only [friBatchUniqueCommitError, friSmoothBatchUniqueCommitError, params.toSmooth_totalLog]


/-- Exact identity between the integer-numerator `ℝ≥0∞` unique-decoding batched commit error and
`ENNReal.ofReal (friBatchUniqueCommitError params)`. -/
theorem friBatchUniqueCommitError_ennreal_eq [Fintype F] (params : FRIParams F) :
    ((2 * 2 ^ params.d - 2 ^ (params.d - params.m) : ℕ) : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) =
      ENNReal.ofReal (friBatchUniqueCommitError params) := by
  rw [friBatchUniqueCommitError_eq_smooth]
  simpa only [params.toSmooth_totalLog] using
    friSmoothBatchUniqueCommitError_ennreal_eq params.toSmooth

/-- **Unconditional unique-decoding batched FRI commit-phase upper bound (`batchProximityLang`)**
(corollary of `friSmoothBatchCommitGame_proximity_le_of_unique`). -/
theorem friBatchCommitGame_proximity_le_of_unique [Fintype F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friBatchCommitGame params t (2 ^ params.d - e - 1) stmt P true ≤
      ((2 * 2 ^ params.d - 2 ^ (params.d - params.m) : ℕ) : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) := by
  rw [friBatchCommitGame_eq_friSmoothBatchCommitGame]
  simpa only [params.toSmooth_totalLog] using
    friSmoothBatchCommitGame_proximity_le_of_unique params.toSmooth t
      (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using huniq)
      (by rwa [params.toSmooth_batchProximityLang]) P

/-- **Unconditional unique-decoding interactive batched FRI soundness upper bound
(`batchProximityLang`)** (corollary of
`friSmoothBatchIOP_interactiveGame_proximity_le_of_unique`). -/
theorem friBatchIOP_interactiveGame_proximity_le_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ((2 * 2 ^ params.d - 2 ^ (params.d - params.m) : ℕ) : ℝ≥0∞) /
          (Fintype.card F : ℝ≥0∞) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  rw [friBatchIOP_eq_friSmoothBatchIOP]
  simpa only [params.toSmooth_totalLog] using
    friSmoothBatchIOP_interactiveGame_proximity_le_of_unique params.toSmooth t
      (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using huniq)
      (by rwa [params.toSmooth_batchProximityLang]) P

/-- **Unconditional real-`α` unique-decoding batched FRI commit-phase upper bound** (corollary of
`friSmoothBatchCommitGame_le_of_unique`). -/
theorem friBatchCommitGame_le_of_unique [Fintype F]
    (params : FRIParams F) (t : ℕ) {α : ℝ}
    {stmt : FRIBatchStmt F params.d t}
    (hagree_le : ∀ (D' : Finset (Fin (2 ^ params.d))) (v₀ : OracleTable params.d F),
      v₀ ∈ params.initialCode →
      ∀ v : Fin t → OracleTable params.d F,
        (∀ j, v j ∈ params.initialCode) →
        (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
        (D'.card : ℝ) / (2 ^ params.d : ℝ) ≤ α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    let α₀ := max α ((1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2)
    friBatchCommitGame params t ⌊α₀ * (2 ^ params.d : ℝ)⌋₊ stmt P true ≤
      ENNReal.ofReal (friBatchUniqueCommitError params) := by
  intro α₀
  rw [friBatchCommitGame_eq_friSmoothBatchCommitGame, friBatchUniqueCommitError_eq_smooth]
  simpa only [params.toSmooth_dim (Nat.zero_le _)] using
    friSmoothBatchCommitGame_le_of_unique params.toSmooth t
      (by simpa only [params.toSmooth_initialCode] using hagree_le) P

/-- **Unconditional real-`α` unique-decoding interactive batched FRI soundness upper bound**
(corollary of `friSmoothBatchIOP_interactiveGame_le_of_unique`). -/
theorem friBatchIOP_interactiveGame_le_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {α : ℝ}
    (hα : (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2 ≤ α)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchCorrAgreeLang t α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friBatchUniqueCommitError params + α ^ params.q) := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, friBatchUniqueCommitError_eq_smooth]
  exact friSmoothBatchIOP_interactiveGame_le_of_unique params.toSmooth t
    (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using hα)
    (by rwa [params.toSmooth_batchCorrAgreeLang]) P

/-- **Contrapositive real-`α` unique-decoding interactive batched FRI soundness** (corollary of
`friSmoothBatchIOP_sound_of_unique`). -/
theorem friBatchIOP_sound_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {α : ℝ}
    (hα : (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2 ≤ α)
    (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t))
    (hacc : ENNReal.ofReal (friBatchUniqueCommitError params + α ^ params.q) <
      iopInteractiveGame (friBatchIOP params t) stmt P true) :
    stmt ∈ params.batchCorrAgreeLang t α := by
  by_contra hfar
  exact not_lt_of_ge (friBatchIOP_interactiveGame_le_of_unique params t hα hfar P) hacc

/-- **Unconditional adaptive two-channel batched BCS-FRI ROM soundness in the unique-decoding
regime** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friBatchBCS_romSoundness_bound_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
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
          (friBatchRBRError params ((2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
              e (2 ^ (params.d - 1)) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBatchBCS_romSoundness_bound_of_escape params t
    (batchRound0Escape_of_unique params t huniq)
    (weightedLineGapBound_of_unique params huniq) hdec σ hFS hMT

/-- **Unconditional adaptive two-channel batched BCS-FRI ROM soundness with separate prover/verifier
Merkle budgets in the unique-decoding regime** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]).
-/
theorem friBatchBCS_romSoundness_bound_of_prover_verifier_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
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
          (friBatchRBRError params ((2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
              e (2 ^ (params.d - 1)) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape params t
    (batchRound0Escape_of_unique params t huniq)
    (weightedLineGapBound_of_unique params huniq) hdec σ hMT hFS hops

/-- **Unconditional adaptive two-channel batched BCS-FRI ROM soundness on `batchCorrAgreeLang` in
the unique-decoding regime** (corollary of
`friSmoothBatchBCS_corrAgree_romSoundness_bound_of_unique`). -/
theorem friBatchBCS_corrAgree_romSoundness_bound_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {α : ℝ}
    (hα : (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2 ≤ α) (hα_le : α ≤ 1)
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
          (max ((2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
              (max (((2 ^ (params.d - 1) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
                (ENNReal.ofReal (α ^ params.q))) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, ← params.toSmooth_batchCorrAgreeLang] at hMT ⊢
  refine (friSmoothBatchBCS_corrAgree_romSoundness_bound_of_unique params.toSmooth t
    (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using hα) hα_le hdec σ hFS hMT).trans ?_
  have hle : 2 ^ params.d - 2 ^ (params.d - params.toSmooth.firstStepLog) ≤ 2 ^ (params.d - 1) := by
    have h2 := two_mul_toSmooth_first_sub_le params
    rcases Nat.eq_zero_or_pos params.d with hd | hd
    · simp [hd]
    · have : 2 * 2 ^ (params.d - 1) = 2 ^ params.d := by rw [← pow_succ', Nat.sub_add_cancel hd]
      omega
  gcongr


end BinaryUnique

end Cslib.Crypto.Protocols.FRI
