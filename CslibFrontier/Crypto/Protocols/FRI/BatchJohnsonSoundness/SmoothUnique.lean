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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Smooth Unique-Decoding Batched FRI IOP Soundness and BCS-FRI ROM Bounds

Unconditional commit-phase, interactive IOP, and adaptive two-channel BCS random-oracle soundness
bounds for `friSmoothBatchIOP` in the unique-decoding regime
([BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2; [BenSassonChiesaSpooner2016];
[ChiesaYogev2024]).

## Main results

* `Cslib.Crypto.Protocols.FRI.friSmoothBatchUniqueCommitError_ennreal_eq`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_proximity_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_le_of_unique`: integer-`e` and real-`α`
  unique-decoding commit-phase bounds for `friSmoothBatchCommitGame`.
* `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_proximity_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_sound_of_unique`: unique-decoding interactive IOP
  soundness bounds and contrapositive for `friSmoothBatchIOP`.
* `Cslib.Crypto.Protocols.FRI.friSmoothBatchBCS_romSoundness_bound_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchBCS_corrAgree_romSoundness_bound_of_unique`: adaptive
  two-channel BCS-FRI ROM soundness bounds in the unique-decoding regime.

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

section SmoothUniqueDecoding

variable {F : Type} [Field F]

private theorem friSmoothBatchUniqueCommitError_nonneg [Fintype F] (params : FRISmoothParams F) :
    0 ≤ friSmoothBatchUniqueCommitError params :=
  mul_nonneg (two_sub_inv_two_pow_nonneg params.totalLog) (by positivity)

private theorem smooth_unique_round0_add_sum_eq [Fintype F] (params : FRISmoothParams F) :
    (2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
        (∑ i : Fin params.m,
          (((params.arity i - 1) * params.domainSize (i.val + 1) : ℕ) : ℝ≥0∞) /
            (Fintype.card F : ℝ≥0∞)) =
      ((2 * 2 ^ params.d - 2 ^ (params.d - params.totalLog) : ℕ) : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) := by
  have hle : 2 ^ (params.d - params.totalLog) ≤ 2 ^ params.d :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  have hsplit :
      2 ^ params.d + (2 ^ params.d - 2 ^ (params.d - params.totalLog)) =
        2 * 2 ^ params.d - 2 ^ (params.d - params.totalLog) := by omega
  have hcast0 : (2 ^ params.d : ℝ≥0∞) = ((2 ^ params.d : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [hcast0, add_sum_natCast_div_ennreal, params.sum_arity_sub_one_mul_domainSize, hsplit]

/-- Exact identity between the integer-numerator `ℝ≥0∞` unique-decoding smooth batched commit error
`((2 * 2 ^ d - 2 ^ (d - totalLog)) : ℝ≥0∞) / |F|` and
`ENNReal.ofReal (friSmoothBatchUniqueCommitError params)`. -/
theorem friSmoothBatchUniqueCommitError_ennreal_eq [Fintype F] (params : FRISmoothParams F) :
    ((2 * 2 ^ params.d - 2 ^ (params.d - params.totalLog) : ℕ) : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) =
      ENNReal.ofReal (friSmoothBatchUniqueCommitError params) := by
  have hr0_nn : 0 ≤ (2 ^ params.d : ℝ) / (Fintype.card F : ℝ) := by positivity
  have hrc_nn : 0 ≤ friSmoothUniqueCommitError params :=
    mul_nonneg (one_sub_inv_two_pow_nonneg params.totalLog) hr0_nn
  rw [← smooth_unique_round0_add_sum_eq, sum_friSmoothUniqueRoundEscape_eq,
    ← ENNReal.ofReal_natCast (Fintype.card F), ← ENNReal.ofReal_ofNat (n := 2),
    ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card F),
    ← ENNReal.ofReal_add hr0_nn hrc_nn]
  exact congrArg ENNReal.ofReal <| by
    simp only [friSmoothUniqueCommitError, friSmoothBatchUniqueCommitError]; ring

/-- **Unconditional unique-decoding smooth batched FRI commit-phase upper bound
(`batchProximityLang`)**. -/
theorem friSmoothBatchCommitGame_proximity_le_of_unique [Fintype F]
    (params : FRISmoothParams F) (t : ℕ) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friSmoothBatchCommitGame params t (2 ^ params.d - e - 1) stmt P true ≤
      ((2 * 2 ^ params.d - 2 ^ (params.d - params.totalLog) : ℕ) : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) := by
  classical
  exact (friSmoothBatchCommitGame_le_of_escape params t
    (smoothBatchRound0Escape_of_unique params t huniq)
    (weightedCurveEscapePerRound_of_gapPerRound params
      (weightedCurveGapPerRound_of_unique params huniq)) hfar P).trans_eq
    (smooth_unique_round0_add_sum_eq params)

/-- **Unconditional unique-decoding interactive smooth batched FRI soundness upper bound
(`batchProximityLang`)**. -/
theorem friSmoothBatchIOP_interactiveGame_proximity_le_of_unique [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friSmoothBatchIOP params t) stmt P true ≤
      ((2 * 2 ^ params.d - 2 ^ (params.d - params.totalLog) : ℕ) : ℝ≥0∞) /
          (Fintype.card F : ℝ≥0∞) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  refine (friSmoothBatchIOP_interactiveGame_le_of_escape params t
    (smoothBatchRound0Escape_of_unique params t huniq)
    (weightedCurveEscapePerRound_of_gapPerRound params
      (weightedCurveGapPerRound_of_unique params huniq)) hfar P).trans_eq ?_
  rw [friSmoothBatchSumError, friSmoothSumError, ← add_assoc, smooth_unique_round0_add_sum_eq]

private theorem smooth_two_mul_add_dim_le_of_div_le (params : FRISmoothParams F) {e : ℕ}
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2) :
    2 * e + params.dim 0 ≤ 2 ^ params.d := by
  have hn : (0 : ℝ) < (2 ^ params.d : ℝ) := by positivity
  field_simp at he
  exact_mod_cast (by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]; linarith :
    ((2 * e + params.dim 0 : ℕ) : ℝ) ≤ ((2 ^ params.d : ℕ) : ℝ))

/-- **Unconditional real-`α` unique-decoding smooth batched FRI commit-phase upper bound**
(unique-decoding counterpart of [BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 on printed
pp. 38–39, bridged via `friBatchFloorThreshold_bounds`). -/
theorem friSmoothBatchCommitGame_le_of_unique [Fintype F]
    (params : FRISmoothParams F) (t : ℕ) {α : ℝ}
    {stmt : FRIBatchStmt F params.d t}
    (hagree_le : ∀ (D' : Finset (Fin (2 ^ params.d))) (v₀ : OracleTable params.d F),
      v₀ ∈ params.initialCode →
      ∀ v : Fin t → OracleTable params.d F,
        (∀ j, v j ∈ params.initialCode) →
        (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
        (D'.card : ℝ) / (2 ^ params.d : ℝ) ≤ α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    let α₀ := max α ((1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2)
    friSmoothBatchCommitGame params t ⌊α₀ * (2 ^ params.d : ℝ)⌋₊ stmt P true ≤
      ENNReal.ofReal (friSmoothBatchUniqueCommitError params) := by
  intro α₀
  exact friSmoothBatchCommitGame_le_of_floor params t
    (le_trans (by positivity) (le_max_right _ _)) (le_max_left _ _) hagree_le P
    fun _ hnot he₀ => (friSmoothBatchCommitGame_proximity_le_of_unique params t
      (smooth_two_mul_add_dim_le_of_div_le params
        (by have : _ ≤ α₀ := le_max_right _ _; linarith)) hnot P).trans_eq
      (friSmoothBatchUniqueCommitError_ennreal_eq params)

/-- **Unconditional real-`α` unique-decoding interactive smooth batched FRI soundness upper bound**
(unique-decoding counterpart of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 8.3 on printed
pp. 39–40). -/
theorem friSmoothBatchIOP_interactiveGame_le_of_unique [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {α : ℝ}
    (hα : (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2 ≤ α)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchCorrAgreeLang t α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friSmoothBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friSmoothBatchUniqueCommitError params + α ^ params.q) :=
  friSmoothBatchIOP_interactiveGame_le_of_corrAgree_le params t
    (friSmoothBatchUniqueCommitError_nonneg params) (lt_of_lt_of_le (by positivity) hα) hfar P
    fun _ hnot he_le => by
      simpa only [friSmoothBatchUniqueCommitError_ennreal_eq] using
        friSmoothBatchIOP_interactiveGame_proximity_le_of_unique params t
          (smooth_two_mul_add_dim_le_of_div_le params (he_le.trans (by linarith))) hnot P

/-- **Contrapositive real-`α` unique-decoding interactive smooth batched FRI soundness**. -/
theorem friSmoothBatchIOP_sound_of_unique [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {α : ℝ}
    (hα : (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2 ≤ α)
    (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t))
    (hacc : ENNReal.ofReal (friSmoothBatchUniqueCommitError params + α ^ params.q) <
      iopInteractiveGame (friSmoothBatchIOP params t) stmt P true) :
    stmt ∈ params.batchCorrAgreeLang t α := by
  by_contra hfar
  exact not_lt_of_ge (friSmoothBatchIOP_interactiveGame_le_of_unique params t hα hfar P) hacc

/-- **Unconditional adaptive two-channel smooth batched BCS-FRI ROM soundness in the
unique-decoding regime** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friSmoothBatchBCS_romSoundness_bound_of_unique [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
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
          (friSmoothBatchRBRError params ((2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
              e (2 ^ params.d - 2 ^ (params.d - params.firstStepLog)) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friSmoothBatchBCS_romSoundness_bound_of_escape params t
    (smoothBatchRound0Escape_of_unique params t huniq)
    (weightedCurveGapBound_of_unique params huniq) hdec σ hFS hMT

/-- **Unconditional adaptive two-channel smooth batched BCS-FRI ROM soundness with separate
prover/verifier Merkle budgets in the unique-decoding regime** ([BenSassonChiesaSpooner2016];
[ChiesaYogev2024]). -/
theorem friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_unique [Fintype F]
    [DecidableEq F] (params : FRISmoothParams F) (t : ℕ) {e : ℕ}
    (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
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
          (friSmoothBatchRBRError params ((2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
              e (2 ^ params.d - 2 ^ (params.d - params.firstStepLog)) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_escape params t
    (smoothBatchRound0Escape_of_unique params t huniq)
    (weightedCurveGapBound_of_unique params huniq) hdec σ hMT hFS hops

/-- **Unconditional adaptive two-channel smooth batched BCS-FRI ROM soundness on
`batchCorrAgreeLang` in the unique-decoding regime** (`(1 + ρ) / 2 ≤ α ≤ 1`;
[BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friSmoothBatchBCS_corrAgree_romSoundness_bound_of_unique [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {α : ℝ}
    (hα : (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2 ≤ α) (hα_le : α ≤ 1)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friSmoothBatchIOP params t) encSym (params.batchCorrAgreeLang t α) P)
      Q_MT) :
    bcsSoundnessGame (friSmoothBatchIOP params t) encSym (params.batchCorrAgreeLang t α) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (max ((2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
              (max (((2 ^ params.d - 2 ^ (params.d - params.firstStepLog) : ℕ) : ℝ≥0∞) /
                  (Fintype.card F : ℝ≥0∞))
                (ENNReal.ofReal (α ^ params.q))) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  have hα_pos : 0 < α := lt_of_lt_of_le (by positivity) hα
  obtain ⟨_, _, he_le⟩ := friBatchCeilThreshold_bounds params.d hα_pos hα_le
  have huniq : 2 * (2 ^ params.d - ⌈α * (2 ^ params.d : ℝ)⌉₊) + params.dim 0 ≤ 2 ^ params.d :=
    smooth_two_mul_add_dim_le_of_div_le params (he_le.trans (by linarith))
  rw [FRISmoothParams.batchCorrAgreeLang,
      friBatchCorrAgreeLang_eq_proximityLang params.initialCode t hα_le] at hMT ⊢
  refine (friSmoothBatchBCS_romSoundness_bound_of_unique params t huniq hdec σ hFS hMT).trans ?_
  have hrbr := friSmoothBatchRBRError_ceil_le params
    ((2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) hα_pos hα_le
    (2 ^ params.d - 2 ^ (params.d - params.firstStepLog))
  gcongr

end SmoothUniqueDecoding

end Cslib.Crypto.Protocols.FRI
