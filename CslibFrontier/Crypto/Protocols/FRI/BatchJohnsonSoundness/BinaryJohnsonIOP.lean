/-
Copyright (c) 2026 Mayank Rathee, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.BinaryBridge
import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.SmoothJohnsonIOP

/-!
# Binary 2-to-1 Closed-Form Johnson & `η`-Gap Batched FRI Commit-Phase and Interactive IOP Bounds

Binary 2-to-1 corollaries of the closed-form Johnson and `η`-gap commit-phase and interactive IOP
soundness bounds (and contrapositives) for `friBatchIOP` ([BenSassonCarmonIshaiKoppartySaraf2020],
Lemma 8.2 and Theorem 8.3).

## Main results

* `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_proximity_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_proximity_le_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_le_of_johnson_eta`: closed-form Johnson and `η`-gap
  commit-phase bounds for `friBatchCommitGame`.
* `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_proximity_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_proximity_le_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_sound_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_le_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_sound_of_johnson_eta`: closed-form Johnson and `η`-gap
  interactive IOP soundness bounds and contrapositives for `friBatchIOP`.

## References

* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, *Proximity Gaps for Reed–Solomon
  Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Finset Cslib.Code Cslib.OracleComp Cslib.Crypto.Protocols.BCS Cslib.Probability

section BinaryJohnsonIOP

variable {F : Type} [Field F]

private theorem friBatchJohnsonCommitError_eq_smooth [Fintype F] (params : FRIParams F) (mJ : ℕ) :
    friBatchJohnsonCommitError params mJ = friSmoothBatchJohnsonCommitError params.toSmooth mJ := by
  simp only [friBatchJohnsonCommitError, friSmoothBatchJohnsonCommitError,
    params.toSmooth_totalLog, params.toSmooth_dim (Nat.zero_le _)]

private theorem friBatchJohnsonEtaCommitError_eq_smooth [Fintype F] (params : FRIParams F)
    (η : ℝ) :
    friBatchJohnsonEtaCommitError params η =
      friSmoothBatchJohnsonEtaCommitError params.toSmooth η := by
  simp only [friBatchJohnsonEtaCommitError, friSmoothBatchJohnsonEtaCommitError,
    params.toSmooth_totalLog, params.toSmooth_dim (Nat.zero_le _)]


/-- **Original explicit-constant Johnson batched FRI commit-phase upper bound
(`batchProximityLang`)** (corollary of `friSmoothBatchCommitGame_proximity_le_of_johnson`). -/
theorem friBatchCommitGame_proximity_le_of_johnson [Fintype F]
    (params : FRIParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friBatchCommitGame params t (2 ^ params.d - e - 1) stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonCommitError params mJ) := by
  rw [friBatchCommitGame_eq_friSmoothBatchCommitGame, friBatchJohnsonCommitError_eq_smooth]
  exact friSmoothBatchCommitGame_proximity_le_of_johnson params.toSmooth t hmJ
    (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using he)
    (by rwa [params.toSmooth_batchProximityLang]) P

/-- **Original explicit-constant Johnson interactive batched FRI soundness upper bound
(`batchProximityLang`)** (corollary of
`friSmoothBatchIOP_interactiveGame_proximity_le_of_johnson`). -/
theorem friBatchIOP_interactiveGame_proximity_le_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonCommitError params mJ) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, friBatchJohnsonCommitError_eq_smooth]
  exact friSmoothBatchIOP_interactiveGame_proximity_le_of_johnson params.toSmooth t hmJ
    (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using he)
    (by rwa [params.toSmooth_batchProximityLang]) P

/-- **Original explicit-constant `η`-gap Johnson batched FRI commit-phase upper bound
(`batchProximityLang`)** (corollary of
`friSmoothBatchCommitGame_proximity_le_of_johnson_eta`). -/
theorem friBatchCommitGame_proximity_le_of_johnson_eta [Fintype F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friBatchCommitGame params t (2 ^ params.d - e - 1) stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonEtaCommitError params η) := by
  rw [friBatchCommitGame_eq_friSmoothBatchCommitGame, friBatchJohnsonEtaCommitError_eq_smooth]
  exact friSmoothBatchCommitGame_proximity_le_of_johnson_eta params.toSmooth t hη
    (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using he)
    (by rwa [params.toSmooth_batchProximityLang]) P

/-- **Original explicit-constant `η`-gap Johnson interactive batched FRI soundness upper bound
(`batchProximityLang`)** (corollary of
`friSmoothBatchIOP_interactiveGame_proximity_le_of_johnson_eta`). -/
theorem friBatchIOP_interactiveGame_proximity_le_of_johnson_eta [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonEtaCommitError params η) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, friBatchJohnsonEtaCommitError_eq_smooth]
  exact friSmoothBatchIOP_interactiveGame_proximity_le_of_johnson_eta params.toSmooth t hη
    (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using he)
    (by rwa [params.toSmooth_batchProximityLang]) P

/-- **Original explicit-constant real-`α` Johnson batched FRI commit-phase upper bound** (corollary
of `friSmoothBatchCommitGame_le_of_johnson`). -/
theorem friBatchCommitGame_le_of_johnson [Fintype F]
    (params : FRIParams F) (t : ℕ) {mJ : ℕ} (hmJ : 1 ≤ mJ) {α : ℝ}
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
    friBatchCommitGame params t ⌊α₀ * (2 ^ params.d : ℝ)⌋₊ stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonCommitError params mJ) := by
  intro α₀
  rw [friBatchCommitGame_eq_friSmoothBatchCommitGame, friBatchJohnsonCommitError_eq_smooth]
  simpa only [params.toSmooth_dim (Nat.zero_le _)] using
    friSmoothBatchCommitGame_le_of_johnson params.toSmooth t hmJ
      (by simpa only [params.toSmooth_initialCode] using hagree_le) P

/-- **Original explicit-constant real-`α` `η`-gap batched FRI commit-phase upper bound** (corollary
of `friSmoothBatchCommitGame_le_of_johnson_eta`). -/
theorem friBatchCommitGame_le_of_johnson_eta [Fintype F]
    (params : FRIParams F) (t : ℕ) {η α : ℝ} (hη : 0 < η)
    {stmt : FRIBatchStmt F params.d t}
    (hagree_le : ∀ (D' : Finset (Fin (2 ^ params.d))) (v₀ : OracleTable params.d F),
      v₀ ∈ params.initialCode →
      ∀ v : Fin t → OracleTable params.d F,
        (∀ j, v j ∈ params.initialCode) →
        (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
        (D'.card : ℝ) / (2 ^ params.d : ℝ) ≤ α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    let α₀ := max α (Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) + η)
    friBatchCommitGame params t ⌊α₀ * (2 ^ params.d : ℝ)⌋₊ stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonEtaCommitError params η) := by
  intro α₀
  rw [friBatchCommitGame_eq_friSmoothBatchCommitGame, friBatchJohnsonEtaCommitError_eq_smooth]
  simpa only [params.toSmooth_dim (Nat.zero_le _)] using
    friSmoothBatchCommitGame_le_of_johnson_eta params.toSmooth t hη
      (by simpa only [params.toSmooth_initialCode] using hagree_le) P

/-- **Original explicit-constant real-`α` Johnson interactive batched FRI soundness upper bound**
(corollary of `friSmoothBatchIOP_interactiveGame_le_of_johnson`). -/
theorem friBatchIOP_interactiveGame_le_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {mJ : ℕ} (hmJ : 1 ≤ mJ) {α : ℝ}
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
      (1 + 1 / (2 * (mJ : ℝ))) ≤ α)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchCorrAgreeLang t α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonCommitError params mJ + α ^ params.q) := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, friBatchJohnsonCommitError_eq_smooth]
  exact friSmoothBatchIOP_interactiveGame_le_of_johnson params.toSmooth t hmJ
    (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using hα)
    (by rwa [params.toSmooth_batchCorrAgreeLang]) P

/-- **Contrapositive original explicit-constant real-`α` Johnson interactive batched FRI soundness**
(corollary of `friSmoothBatchIOP_sound_of_johnson`). -/
theorem friBatchIOP_sound_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {mJ : ℕ} (hmJ : 1 ≤ mJ) {α : ℝ}
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
      (1 + 1 / (2 * (mJ : ℝ))) ≤ α)
    (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t))
    (hacc : ENNReal.ofReal (friBatchJohnsonCommitError params mJ + α ^ params.q) <
      iopInteractiveGame (friBatchIOP params t) stmt P true) :
    stmt ∈ params.batchCorrAgreeLang t α := by
  by_contra hfar
  exact not_lt_of_ge (friBatchIOP_interactiveGame_le_of_johnson params t hmJ hα hfar P) hacc

/-- **Original explicit-constant real-`α` `η`-gap interactive batched FRI soundness upper bound**
(corollary of `friSmoothBatchIOP_interactiveGame_le_of_johnson_eta`). -/
theorem friBatchIOP_interactiveGame_le_of_johnson_eta [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {η α : ℝ} (hη : 0 < η)
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) + η ≤ α)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchCorrAgreeLang t α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonEtaCommitError params η + α ^ params.q) := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, friBatchJohnsonEtaCommitError_eq_smooth]
  exact friSmoothBatchIOP_interactiveGame_le_of_johnson_eta params.toSmooth t hη
    (by simpa only [params.toSmooth_dim (Nat.zero_le _)] using hα)
    (by rwa [params.toSmooth_batchCorrAgreeLang]) P

/-- **Contrapositive original explicit-constant real-`α` `η`-gap interactive batched FRI soundness**
(corollary of `friSmoothBatchIOP_sound_of_johnson_eta`). -/
theorem friBatchIOP_sound_of_johnson_eta [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {η α : ℝ} (hη : 0 < η)
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) + η ≤ α)
    (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t))
    (hacc : ENNReal.ofReal (friBatchJohnsonEtaCommitError params η + α ^ params.q) <
      iopInteractiveGame (friBatchIOP params t) stmt P true) :
    stmt ∈ params.batchCorrAgreeLang t α := by
  by_contra hfar
  exact not_lt_of_ge (friBatchIOP_interactiveGame_le_of_johnson_eta params t hη hα hfar P) hacc


end BinaryJohnsonIOP

end Cslib.Crypto.Protocols.FRI
