/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Encryption.ParityPrediction
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Tactic.PPT

/-!
# Tests for parity-prediction security from semantic security

Checked clients and counterexamples for
`CslibFrontier.Crypto.Computational.Encryption.ParityPrediction`:
* Concrete nontrivial client on `BitString L` (`1 ≤ L`): the identity cipher with predictor
  `parity L` has `parityAdvantage = 1 / 2` and semantic-security advantage `1` via
  `parityAdvantage_eq_half_mul_advantage_parityReduction`.
* Concrete word-level client: predicting `false` against `otpKeyWordEncrypt (fun n => n + 1)`
  on `(n + 1)`-bit messages discharges every hypothesis of
  `DEMOneTimeKeyWordINDCPA.negligible_parityWordAdvantage` and proves negligible parity-prediction
  advantage.
* Counterexamples showing `1 ≤ L` (`hL`), `hvalid` (concrete), and `∀ n, 1 ≤ msgLen n` (`hpos`)
  are all necessary.
-/

public section

namespace CslibFrontierTests.Crypto.ParityPrediction

open Cslib Cslib.Crypto Cslib.Crypto.Encryption Cslib.Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

private theorem guessingAdvantage_pure_true :
    Game.guessingAdvantage (PMF.pure true) = (1 : ℝ≥0) / 2 := by
  apply NNReal.coe_injective
  rw [Game.coe_guessingAdvantage, Game.coe_succProbability]
  simp
  norm_num

private theorem parityAdvantage_idCipher (L : ℕ) :
    parityAdvantage
        (⟨fun _ m => pure m, fun _ c => pure c⟩ : Cipher Unit (BitString L) (BitString L))
        (pure ()) (fun c => pure (parity L c)) =
      (1 : ℝ≥0) / 2 := by
  have htrue :
      ProbComp.eval
          (parityExperiment
            (⟨fun _ m => pure m, fun _ c => pure c⟩ : Cipher Unit (BitString L) (BitString L))
            (pure ()) (fun c => pure (parity L c))) =
        PMF.pure true := by
    simp only [parityExperiment, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
      PMF.pure_bind, beq_self_eq_true, PMF.bind_const]
  rw [parityAdvantage, htrue]
  exact guessingAdvantage_pure_true

section ConcreteAndWordClients

/-- Concrete nontrivial client of `parityAdvantage_eq_half_mul_advantage_parityReduction`: for the
identity cipher on `BitString L` (`1 ≤ L`), predicting `parity L c` gives `Parityadv = 1/2` and
`parityReduction` achieves `SSadv = 1`. -/
example {L : ℕ} (hL : 1 ≤ L) :
    let E : Cipher Unit (BitString L) (BitString L) := ⟨fun _ m => pure m, fun _ c => pure c⟩
    let sampleKey : ProbComp Unit := pure ()
    let valid : BitString L → BitString L → Bool := fun _ _ => true
    let A : BitString L → ProbComp Bool := fun c => pure (parity L c)
    parityAdvantage E sampleKey A = (1 : ℝ≥0) / 2 ∧
      Experiment.advantage
        (E.oneTimeExperiment sampleKey valid
          (parityReduction (ProbComp.uniform (BitString L))
            (flipLastBitString hL) (parity L) A) false)
        (E.oneTimeExperiment sampleKey valid
          (parityReduction (ProbComp.uniform (BitString L))
            (flipLastBitString hL) (parity L) A) true) = 1 := by
  intro E sampleKey valid A
  have hp : parityAdvantage E sampleKey A = (1 : ℝ≥0) / 2 := parityAdvantage_idCipher L
  refine ⟨hp, ?_⟩
  have hrel := parityAdvantage_eq_half_mul_advantage_parityReduction E sampleKey hL
    (valid := valid) (fun _ => rfl) A
  rw [hp, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at hrel
  apply NNReal.coe_injective
  rw [NNReal.coe_one]
  linarith

/-- Concrete word-level client: predicting `false` achieves negligible parity-prediction
advantage against `otpKeyWordEncrypt (fun n => n + 1)` on `(n + 1)`-bit messages. -/
example :
    Negligible
      (parityWordAdvantage (fun n => n + 1) (fun n => n + 1)
        (otpKeyWordEncrypt (fun n => n + 1)) (fun _ _ => pure false)) := by
  refine (demOneTimeKeyWordINDCPA_otpKeyWordEncrypt
      (fun n => n + 1)).negligible_parityWordAdvantage
    ?_ (fun n => Nat.le_add_left 1 n) ?_ <;> ppt

end ConcreteAndWordClients

section Counterexamples

/-- Shows `1 ≤ L` (`hL`) is needed in `parityAdvantage_eq_half_mul_advantage_parityReduction`:
at `L = 0`, all messages have parity `false`, so predicting `false` gets `Parityadv = 1/2` while
every two-stage adversary has `SSadv = 0`. -/
theorem cex_parity_len_zero :
    ∃ (E : Cipher Unit (BitString 0) Unit) (sampleKey : ProbComp Unit)
      (valid : BitString 0 → BitString 0 → Bool) (A : Unit → ProbComp Bool),
      (∀ m₀ m₁, valid m₀ m₁ = true) ∧
        parityAdvantage E sampleKey A = (1 : ℝ≥0) / 2 ∧
        ∀ {σ : Type} (B : TwoStage Unit (MessagePair (BitString 0)) Unit Bool σ),
          Experiment.advantage
            (E.oneTimeExperiment sampleKey valid B false)
            (E.oneTimeExperiment sampleKey valid B true) = 0 := by
  let E : Cipher Unit (BitString 0) Unit :=
    ⟨fun _ _ => pure (), fun _ _ => pure (fun i => i.elim0)⟩
  refine ⟨E, pure (), fun _ _ => true, fun _ => pure false, fun _ _ => rfl, ?_, ?_⟩
  · have htrue : ProbComp.eval (parityExperiment E (pure ()) (fun _ => pure false)) =
        PMF.pure true := by
      simp only [parityExperiment, E, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
        PMF.pure_bind]
      have hp0 : ∀ m : BitString 0, parity 0 m = false := fun m => by
        simp [parity, parityOn]
      simp [hp0, PMF.bind_const]
    rw [parityAdvantage, htrue]
    exact guessingAdvantage_pure_true
  · intro σ B
    have heq : ProbComp.eval (Cipher.oneTimeExperiment E (pure ()) (fun _ _ => true) B false) =
        ProbComp.eval (Cipher.oneTimeExperiment E (pure ()) (fun _ _ => true) B true) := rfl
    rw [Experiment.advantage, Game.advantage, heq, nndist_self]

/-- Shows `hvalid` is needed in `parityAdvantage_eq_half_mul_advantage_parityReduction`:
even at `L = 1`, when `valid` rejects all pairs, the identity cipher gives `Parityadv = 1/2` while
every two-stage adversary has `SSadv = 0`. -/
theorem cex_parity_invalid :
    ∃ (E : Cipher Unit (BitString 1) (BitString 1)) (sampleKey : ProbComp Unit)
      (valid : BitString 1 → BitString 1 → Bool) (A : BitString 1 → ProbComp Bool),
      parityAdvantage E sampleKey A = (1 : ℝ≥0) / 2 ∧
        ∀ {σ : Type} (B : TwoStage Unit (MessagePair (BitString 1)) (BitString 1) Bool σ),
          Experiment.advantage
            (E.oneTimeExperiment sampleKey valid B false)
            (E.oneTimeExperiment sampleKey valid B true) = 0 := by
  let E : Cipher Unit (BitString 1) (BitString 1) := ⟨fun _ m => pure m, fun _ c => pure c⟩
  refine ⟨E, pure (), fun _ _ => false, fun c => pure (parity 1 c),
    parityAdvantage_idCipher 1, ?_⟩
  intro σ B
  have heq : ProbComp.eval (Cipher.oneTimeExperiment E (pure ()) (fun _ _ => false) B false) =
      ProbComp.eval (Cipher.oneTimeExperiment E (pure ()) (fun _ _ => false) B true) := by
    simp only [Cipher.oneTimeExperiment, lrExperiment, Bool.false_eq_true, ↓reduceIte]
  rw [Experiment.advantage, Game.advantage, heq, nndist_self]

private theorem parityWordAdvantage_msgLen_zero (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool)) (n : ℕ) :
    parityWordAdvantage (fun _ => 0) keyLen encryptSym (fun _ _ => pure false) n =
      (1 : ℝ≥0) / 2 := by
  have htrue :
      ProbComp.eval
          (parityWordExperiment (fun _ => 0) keyLen encryptSym (fun _ _ => pure false) n) =
        PMF.pure true := by
    simp only [parityWordExperiment, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList, PMF.pure_bind, PMF.bind_const]
    trans (BitString.uniformList 0).bind fun _ => PMF.pure true
    · refine Probability.PMF.bind_congr_on_support _ _ _ fun m hm => ?_
      have hm0 : m = [] := List.eq_nil_of_length_eq_zero
        (BitString.length_of_mem_support_uniformList hm)
      subst hm0
      simp [BitString.wordParity_nil]
    · simp [PMF.bind_const]
  rw [parityWordAdvantage, htrue]
  exact guessingAdvantage_pure_true

/-- Shows `1 ≤ msgLen n` is needed in `parityWordAdvantage_eq_half_mul_demKeyGameOn`:
at `msgLen _ = 0`, predicting `false` gives `parityWordAdvantage = 1/2` while the DEM advantage
is `0`. -/
theorem cex_parityWord_len_zero :
    let msgLen : ℕ → ℕ := fun _ => 0
    let keyLen : ℕ → ℕ := fun _ => 0
    let encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool) := fun _ _ _ => pure []
    let A : ℕ → List Bool → ProbComp Bool := fun _ _ => pure false
    parityWordAdvantage msgLen keyLen encryptSym A 0 = (1 : ℝ≥0) / 2 ∧
      Game.advantage
        (ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
          keyLen encryptSym (parityWordToDEMAdversary msgLen A) false 0))
        (ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
          keyLen encryptSym (parityWordToDEMAdversary msgLen A) true 0)) = 0 := by
  intro msgLen keyLen encryptSym A
  refine ⟨parityWordAdvantage_msgLen_zero keyLen encryptSym 0, ?_⟩
  have heq : ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        keyLen encryptSym (parityWordToDEMAdversary msgLen A) false 0) =
      ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        keyLen encryptSym (parityWordToDEMAdversary msgLen A) true 0) := by
    simp only [demKeyGameOn, parityWordToDEMAdversary, parityReduction, ChoiceOut.msg₀,
      ChoiceOut.msg₁, Bool.false_eq_true, ↓reduceIte, encryptSym, A, ProbComp.eval_bind,
      ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind]
  rw [heq, Game.advantage_self]

/-- Dropping `hpos : ∀ n, 1 ≤ msgLen n` also falsifies the conclusion of
`DEMOneTimeKeyWordINDCPA.negligible_parityWordAdvantage`: `A = fun _ _ => pure false`
against `otpKeyWordEncrypt keyLen` has constant parity-prediction advantage `1/2` at every `n`. -/
theorem cex_parityWord_not_negligible (keyLen : ℕ → ℕ) :
    let msgLen : ℕ → ℕ := fun _ => 0
    let A : ℕ → List Bool → ProbComp Bool := fun _ _ => pure false
    DEMOneTimeKeyWordINDCPA keyLen (otpKeyWordEncrypt keyLen) ∧
      ComputableInPolyTime msgLen encUnary encUnary ∧
      IsPPTOn (encPair encUnary encBits) encBool (fun ⟨n, ct⟩ => A n ct) ∧
      ¬ Negligible (parityWordAdvantage msgLen keyLen (otpKeyWordEncrypt keyLen) A) := by
  intro msgLen A
  refine ⟨demOneTimeKeyWordINDCPA_otpKeyWordEncrypt keyLen, ?_, ?_, ?_⟩
  · ppt
  · ppt
  · intro hneg
    exact not_negligible_const (by norm_num : (1 : ℝ≥0) / 2 ≠ 0)
      (hneg.congr fun n => parityWordAdvantage_msgLen_zero keyLen (otpKeyWordEncrypt keyLen) n)

end Counterexamples

end CslibFrontierTests.Crypto.ParityPrediction
