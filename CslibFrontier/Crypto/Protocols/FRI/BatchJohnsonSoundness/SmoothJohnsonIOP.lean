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
# Smooth Closed-Form Johnson & `η`-Gap Batched FRI Commit-Phase and Interactive IOP Bounds

Unconditional integer-`e` and real-`α` commit-phase and interactive IOP soundness upper bounds (and
contrapositives) for `friSmoothBatchIOP` in the closed-form Johnson and `η`-gap regimes
([BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2, Theorem 8.3, and Section 8.2.1).

## Main results

* `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_proximity_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_proximity_le_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_le_of_johnson_eta`: closed-form Johnson and
  `η`-gap commit-phase upper bounds for `friSmoothBatchCommitGame`.
* `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_proximity_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_proximity_le_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_sound_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_le_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_sound_of_johnson_eta`: closed-form Johnson and
  `η`-gap interactive IOP soundness bounds and contrapositives for `friSmoothBatchIOP`.

## References

* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, *Proximity Gaps for Reed–Solomon
  Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Finset Cslib.Code Cslib.OracleComp Cslib.Crypto.Protocols.BCS Cslib.Probability

section SmoothClosedFormJohnsonIOP

variable {F : Type} [Field F]

private theorem friSmoothBatchJohnsonCommitError_nonneg [Fintype F] (params : FRISmoothParams F)
    (mJ : ℕ) :
    0 ≤ friSmoothBatchJohnsonCommitError params mJ := by
  have hk₀R : (0 : ℝ) < (params.dim 0 : ℝ) := by exact_mod_cast params.one_le_dim 0
  exact mul_nonneg (two_sub_inv_two_pow_nonneg params.totalLog) (by positivity)

private theorem friSmoothBatchJohnsonEtaCommitError_nonneg [Fintype F]
    (params : FRISmoothParams F) {η : ℝ} (hη : 0 < η) :
    0 ≤ friSmoothBatchJohnsonEtaCommitError params η := by
  have hk₀R : (0 : ℝ) < (params.dim 0 : ℝ) := by exact_mod_cast params.one_le_dim 0
  exact mul_nonneg (two_sub_inv_two_pow_nonneg params.totalLog) (by positivity)

private theorem round0_add_friSmoothJohnsonCommitError_eq [Fintype F]
    (params : FRISmoothParams F) (mJ : ℕ) :
    ENNReal.ofReal
        (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
          (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ))) +
      ENNReal.ofReal (friSmoothJohnsonCommitError params mJ) =
    ENNReal.ofReal (friSmoothBatchJohnsonCommitError params mJ) := by
  have hk₀R : (0 : ℝ) < (params.dim 0 : ℝ) := by exact_mod_cast params.one_le_dim 0
  have hr0_nn : 0 ≤ 1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
      (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ)) := by positivity
  simp only [friSmoothJohnsonCommitError, friSmoothBatchJohnsonCommitError]
  rw [← ENNReal.ofReal_add hr0_nn (mul_nonneg (one_sub_inv_two_pow_nonneg params.totalLog) hr0_nn)]
  exact congrArg ENNReal.ofReal (by ring)

private theorem friSmoothBatchJohnsonCommitError_le_eta [Fintype F] (params : FRISmoothParams F)
    {mJ : ℕ} {η : ℝ} (hη : 0 < η) (hpow : ((mJ + 1 : ℝ) ^ 6) ≤ 64 / (η ^ 6)) :
    friSmoothBatchJohnsonCommitError params mJ ≤ friSmoothBatchJohnsonEtaCommitError params η := by
  have hk₀R : (0 : ℝ) < (params.dim 0 : ℝ) := by exact_mod_cast params.one_le_dim 0
  have hFR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  refine mul_le_mul_of_nonneg_left ?_ (two_sub_inv_two_pow_nonneg params.totalLog)
  calc 1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
        (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ))
      ≤ 1800 * (64 / (η ^ 6)) * ((2 ^ params.d : ℝ) ^ 2) /
          (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ)) := by gcongr
    _ = _ := by field_simp; ring

/-- **Original explicit-constant Johnson smooth batched FRI commit-phase upper bound
(`batchProximityLang`)** up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - √ρ / (2 * mJ)`. -/
theorem friSmoothBatchCommitGame_proximity_le_of_johnson [Fintype F]
    (params : FRISmoothParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friSmoothBatchCommitGame params t (2 ^ params.d - e - 1) stmt P true ≤
      ENNReal.ofReal (friSmoothBatchJohnsonCommitError params mJ) := by
  classical
  refine (friSmoothBatchCommitGame_le_of_escape params t
    (smoothBatchRound0Escape_of_johnson params t hmJ he)
    (weightedCurveEscapePerRound_of_gapPerRound params
      (weightedCurveGapPerRound_of_johnson params hmJ he)) hfar P).trans ?_
  exact (add_le_add le_rfl (sum_friSmoothJohnsonRoundEscape_le params mJ)).trans_eq
    (round0_add_friSmoothJohnsonCommitError_eq params mJ)

/-- **Original explicit-constant Johnson interactive smooth batched FRI soundness upper bound
(`batchProximityLang`)** up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - √ρ / (2 * mJ)`. -/
theorem friSmoothBatchIOP_interactiveGame_proximity_le_of_johnson [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friSmoothBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friSmoothBatchJohnsonCommitError params mJ) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  refine (friSmoothBatchIOP_interactiveGame_le_of_escape params t
    (smoothBatchRound0Escape_of_johnson params t hmJ he)
    (weightedCurveEscapePerRound_of_gapPerRound params
      (weightedCurveGapPerRound_of_johnson params hmJ he)) hfar P).trans ?_
  rw [friSmoothBatchSumError, friSmoothSumError, ← add_assoc]
  refine add_le_add ?_ le_rfl
  exact (add_le_add le_rfl (sum_friSmoothJohnsonRoundEscape_le params mJ)).trans_eq
    (round0_add_friSmoothJohnsonCommitError_eq params mJ)

private theorem smooth_exists_mJ_and_commitError_le_of_eta [Fintype F]
    (params : FRISmoothParams F) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η) :
    ∃ mJ : ℕ, 1 ≤ mJ ∧
      (e : ℝ) / (2 ^ params.d : ℝ) ≤
        1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
          Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)) ∧
      ENNReal.ofReal (friSmoothBatchJohnsonCommitError params mJ) ≤
        ENNReal.ofReal (friSmoothBatchJohnsonEtaCommitError params η) := by
  have hk₀ := params.dim_le_domainSize (Nat.zero_le params.m)
  obtain ⟨mJ, hmJ, he_mJ, hpow⟩ := ProximityGap.exists_multiplicity_of_eta (params.one_le_dim 0)
    (by simpa [FRISmoothParams.domainSize] using hk₀) hη (mod_cast he)
  exact ⟨mJ, hmJ, mod_cast he_mJ,
    ENNReal.ofReal_le_ofReal (friSmoothBatchJohnsonCommitError_le_eta params hη hpow)⟩

/-- **Original explicit-constant `η`-gap Johnson smooth batched FRI commit-phase upper bound
(`batchProximityLang`)** up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - η` (`0 < η`). -/
theorem friSmoothBatchCommitGame_proximity_le_of_johnson_eta [Fintype F]
    (params : FRISmoothParams F) (t : ℕ) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friSmoothBatchCommitGame params t (2 ^ params.d - e - 1) stmt P true ≤
      ENNReal.ofReal (friSmoothBatchJohnsonEtaCommitError params η) := by
  obtain ⟨mJ, hmJ, he_mJ, hle⟩ := smooth_exists_mJ_and_commitError_le_of_eta params hη he
  exact (friSmoothBatchCommitGame_proximity_le_of_johnson params t hmJ he_mJ hfar P).trans hle

/-- **Original explicit-constant `η`-gap Johnson interactive smooth batched FRI soundness upper
bound (`batchProximityLang`)** up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - η` (`0 < η`). -/
theorem friSmoothBatchIOP_interactiveGame_proximity_le_of_johnson_eta [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friSmoothBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friSmoothBatchJohnsonEtaCommitError params η) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  obtain ⟨mJ, hmJ, he_mJ, hle⟩ := smooth_exists_mJ_and_commitError_le_of_eta params hη he
  exact (friSmoothBatchIOP_interactiveGame_proximity_le_of_johnson params t hmJ he_mJ hfar P).trans
    (add_le_add hle le_rfl)


/-- **Original explicit-constant real-`α` Johnson smooth batched FRI commit-phase upper bound**
(in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 on printed pp. 38–39,
Eq. (8.5), and Section 8.2.1 on printed pp. 41–43, bridged via
`friBatchFloorThreshold_bounds`). -/
theorem friSmoothBatchCommitGame_le_of_johnson [Fintype F]
    (params : FRISmoothParams F) (t : ℕ) {mJ : ℕ} (hmJ : 1 ≤ mJ) {α : ℝ}
    {stmt : FRIBatchStmt F params.d t}
    (hagree_le : ∀ (D' : Finset (Fin (2 ^ params.d))) (v₀ : OracleTable params.d F),
      v₀ ∈ params.initialCode →
      ∀ v : Fin t → OracleTable params.d F,
        (∀ j, v j ∈ params.initialCode) →
        (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
        (D'.card : ℝ) / (2 ^ params.d : ℝ) ≤ α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    let α₀ := max α (Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
      (1 + 1 / (2 * (mJ : ℝ))))
    friSmoothBatchCommitGame params t ⌊α₀ * (2 ^ params.d : ℝ)⌋₊ stmt P true ≤
      ENNReal.ofReal (friSmoothBatchJohnsonCommitError params mJ) := by
  intro α₀
  exact friSmoothBatchCommitGame_le_of_floor params t
    (le_trans (by positivity) (le_max_right _ _)) (le_max_left _ _) hagree_le P
    fun e₀ hnot_e₀ he₀_lt => friSmoothBatchCommitGame_proximity_le_of_johnson params t hmJ
      (smooth_johnson_slack_of_le params hmJ (le_max_right _ _) he₀_lt.le).2 hnot_e₀ P

/-- **Original explicit-constant real-`α` `η`-gap smooth batched FRI commit-phase upper bound**
(using `η` directly rather than `min(η, √ρ / 20)` in Eq. (1.3)). -/
theorem friSmoothBatchCommitGame_le_of_johnson_eta [Fintype F]
    (params : FRISmoothParams F) (t : ℕ) {η α : ℝ} (hη : 0 < η)
    {stmt : FRIBatchStmt F params.d t}
    (hagree_le : ∀ (D' : Finset (Fin (2 ^ params.d))) (v₀ : OracleTable params.d F),
      v₀ ∈ params.initialCode →
      ∀ v : Fin t → OracleTable params.d F,
        (∀ j, v j ∈ params.initialCode) →
        (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
        (D'.card : ℝ) / (2 ^ params.d : ℝ) ≤ α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    let α₀ := max α (Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) + η)
    friSmoothBatchCommitGame params t ⌊α₀ * (2 ^ params.d : ℝ)⌋₊ stmt P true ≤
      ENNReal.ofReal (friSmoothBatchJohnsonEtaCommitError params η) := by
  intro α₀
  exact friSmoothBatchCommitGame_le_of_floor params t
    (le_trans (by positivity) (le_max_right _ _)) (le_max_left _ _) hagree_le P
    fun e₀ hnot_e₀ he₀_lt => friSmoothBatchCommitGame_proximity_le_of_johnson_eta params t hη
      (by have : _ ≤ α₀ := le_max_right _ _; linarith) hnot_e₀ P

/-- **Original explicit-constant real-`α` Johnson interactive smooth batched FRI soundness upper
bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 8.3 on printed
pp. 39–40). -/
theorem friSmoothBatchIOP_interactiveGame_le_of_johnson [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {mJ : ℕ} (hmJ : 1 ≤ mJ) {α : ℝ}
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
      (1 + 1 / (2 * (mJ : ℝ))) ≤ α)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchCorrAgreeLang t α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friSmoothBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friSmoothBatchJohnsonCommitError params mJ + α ^ params.q) :=
  friSmoothBatchIOP_interactiveGame_le_of_corrAgree_le params t
    (friSmoothBatchJohnsonCommitError_nonneg params mJ)
    (smooth_johnson_slack_of_le params hmJ hα le_rfl).1 hfar P fun _ hnot_e he_le =>
      friSmoothBatchIOP_interactiveGame_proximity_le_of_johnson params t hmJ
        (smooth_johnson_slack_of_le params hmJ hα he_le).2 hnot_e P

/-- **Contrapositive original explicit-constant real-`α` Johnson interactive smooth batched FRI
soundness** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 8.3 on printed
pp. 39–40). -/
theorem friSmoothBatchIOP_sound_of_johnson [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {mJ : ℕ} (hmJ : 1 ≤ mJ) {α : ℝ}
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
      (1 + 1 / (2 * (mJ : ℝ))) ≤ α)
    (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t))
    (hacc : ENNReal.ofReal (friSmoothBatchJohnsonCommitError params mJ + α ^ params.q) <
      iopInteractiveGame (friSmoothBatchIOP params t) stmt P true) :
    stmt ∈ params.batchCorrAgreeLang t α := by
  by_contra hfar
  exact not_lt_of_ge (friSmoothBatchIOP_interactiveGame_le_of_johnson params t hmJ hα hfar P) hacc

/-- **Original explicit-constant real-`α` `η`-gap interactive smooth batched FRI soundness upper
bound** (using `η` directly rather than `min(η, √ρ / 20)` in Eq. (1.3)). -/
theorem friSmoothBatchIOP_interactiveGame_le_of_johnson_eta [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {η α : ℝ} (hη : 0 < η)
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) + η ≤ α)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchCorrAgreeLang t α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friSmoothBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friSmoothBatchJohnsonEtaCommitError params η + α ^ params.q) :=
  friSmoothBatchIOP_interactiveGame_le_of_corrAgree_le params t
    (friSmoothBatchJohnsonEtaCommitError_nonneg params hη)
    (lt_of_lt_of_le (by positivity) hα) hfar P fun _ hnot_e he_le =>
      friSmoothBatchIOP_interactiveGame_proximity_le_of_johnson_eta params t hη (by linarith)
        hnot_e P

/-- **Contrapositive original explicit-constant real-`α` `η`-gap interactive smooth batched FRI
soundness** (using `η` directly rather than `min(η, √ρ / 20)` in Eq. (1.3)). -/
theorem friSmoothBatchIOP_sound_of_johnson_eta [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {η α : ℝ} (hη : 0 < η)
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) + η ≤ α)
    (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t))
    (hacc : ENNReal.ofReal (friSmoothBatchJohnsonEtaCommitError params η + α ^ params.q) <
      iopInteractiveGame (friSmoothBatchIOP params t) stmt P true) :
    stmt ∈ params.batchCorrAgreeLang t α := by
  by_contra hfar
  exact not_lt_of_ge
    (friSmoothBatchIOP_interactiveGame_le_of_johnson_eta params t hη hα hfar P) hacc


end SmoothClosedFormJohnsonIOP

end Cslib.Crypto.Protocols.FRI
