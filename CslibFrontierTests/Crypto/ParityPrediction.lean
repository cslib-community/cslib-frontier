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
  `DEMOneTimeKeyINDCPAOn.negligible_parityWordAdvantage` and proves negligible parity-prediction
  advantage.
* Counterexamples showing `1 ≤ L` (`hL`), `hvalid` (concrete), and `∀ n, 1 ≤ msgLen n` (`hpos`)
  are all necessary.
* The premise concerns only the message space: `leakyOtpEncrypt` pads `(n + 1)`-bit messages and
  sends every other message in the clear. It is semantically secure on its message space, so the
  theorem applies to it, but it fails `DEMOneTimeKeyWordINDCPA`, which also admits equal-length
  pairs of other lengths.
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
  have hsec : DEMOneTimeKeyINDCPAOn
      (fun n _ m₀ m₁ => m₀.length == n + 1 && m₁.length == n + 1) encBits (fun n => n + 1)
      (otpKeyWordEncrypt (fun n => n + 1)) :=
    (demOneTimeKeyINDCPA_otpKeyWordEncrypt (fun n => n + 1)).demOneTimeKeyINDCPAOn (by fun_prop)
  exact hsec.negligible_parityWordAdvantage (by fun_prop) (fun n => Nat.le_add_left 1 n) (by ppt)

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
        (ProbComp.eval (demKeyGameOn
          (fun n _ m₀ m₁ => m₀.length == msgLen n && m₁.length == msgLen n)
          keyLen encryptSym (parityWordToDEMAdversary msgLen A) false 0))
        (ProbComp.eval (demKeyGameOn
          (fun n _ m₀ m₁ => m₀.length == msgLen n && m₁.length == msgLen n)
          keyLen encryptSym (parityWordToDEMAdversary msgLen A) true 0)) = 0 := by
  intro msgLen keyLen encryptSym A
  refine ⟨parityWordAdvantage_msgLen_zero keyLen encryptSym 0, ?_⟩
  have heq : ProbComp.eval (demKeyGameOn
        (fun n _ m₀ m₁ => m₀.length == msgLen n && m₁.length == msgLen n)
        keyLen encryptSym (parityWordToDEMAdversary msgLen A) false 0) =
      ProbComp.eval (demKeyGameOn
        (fun n _ m₀ m₁ => m₀.length == msgLen n && m₁.length == msgLen n)
        keyLen encryptSym (parityWordToDEMAdversary msgLen A) true 0) := by
    simp only [demKeyGameOn, parityWordToDEMAdversary, parityReduction, ChoiceOut.msg₀,
      ChoiceOut.msg₁, Bool.false_eq_true, ↓reduceIte, encryptSym, A, ProbComp.eval_bind,
      ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind]
  rw [heq, Game.advantage_self]

/-- Dropping `hpos : ∀ n, 1 ≤ msgLen n` also falsifies the conclusion of
`DEMOneTimeKeyINDCPAOn.negligible_parityWordAdvantage`: `A = fun _ _ => pure false`
against `otpKeyWordEncrypt keyLen` has constant parity-prediction advantage `1/2` at every `n`. -/
theorem cex_parityWord_not_negligible (keyLen : ℕ → ℕ) :
    let msgLen : ℕ → ℕ := fun _ => 0
    let A : ℕ → List Bool → ProbComp Bool := fun _ _ => pure false
    DEMOneTimeKeyINDCPAOn (fun n _ m₀ m₁ => m₀.length == msgLen n && m₁.length == msgLen n)
        encBits keyLen (otpKeyWordEncrypt keyLen) ∧
      ComputableInPolyTime msgLen encUnary encUnary ∧
      IsPPTOn (encPair encUnary encBits) encBool (fun ⟨n, ct⟩ => A n ct) ∧
      ¬ Negligible (parityWordAdvantage msgLen keyLen (otpKeyWordEncrypt keyLen) A) := by
  intro msgLen A
  refine ⟨(demOneTimeKeyINDCPA_otpKeyWordEncrypt keyLen).demOneTimeKeyINDCPAOn ?_, ?_, ?_, ?_⟩
  · ppt
  · ppt
  · ppt
  · intro hneg
    exact not_negligible_const (by norm_num : (1 : ℝ≥0) / 2 ≠ 0)
      (hneg.congr fun n => parityWordAdvantage_msgLen_zero keyLen (otpKeyWordEncrypt keyLen) n)

end Counterexamples

section MessageSpace

/-- One-time pad on `(n + 1)`-bit messages, under `(n + 1)`-bit keys; every message of another
length is sent in the clear. -/
def leakyOtpEncrypt (n : ℕ) (k m : List Bool) : ProbComp (List Bool) :=
  if m.length = n + 1 then otpKeyWordEncrypt (fun n => n + 1) n k m else pure m

/-- `leakyOtpEncrypt` is semantically secure on its message space `{0, 1}^{n + 1}`: on those
messages it is the one-time pad. -/
theorem demOneTimeKeyINDCPAOn_leakyOtpEncrypt :
    DEMOneTimeKeyINDCPAOn (fun n _ m₀ m₁ => m₀.length == n + 1 && m₁.length == n + 1) encBits
      (fun n => n + 1) leakyOtpEncrypt := by
  have hotp : DEMOneTimeKeyINDCPAOn (fun n _ m₀ m₁ => m₀.length == n + 1 && m₁.length == n + 1)
      encBits (fun n => n + 1) (otpKeyWordEncrypt (fun n => n + 1)) :=
    (demOneTimeKeyINDCPA_otpKeyWordEncrypt _).demOneTimeKeyINDCPAOn (by fun_prop)
  intro adversary hadversary
  have hgame : ∀ b n, demKeyGameOn (fun n _ m₀ m₁ => m₀.length == n + 1 && m₁.length == n + 1)
      (fun n => n + 1) leakyOtpEncrypt adversary b n =
      demKeyGameOn (fun n _ m₀ m₁ => m₀.length == n + 1 && m₁.length == n + 1)
      (fun n => n + 1) (otpKeyWordEncrypt (fun n => n + 1)) adversary b n := by
    intro b n
    simp only [demKeyGameOn]
    congr 1; funext k; congr 1; funext choice
    split_ifs <;> simp_all [leakyOtpEncrypt]
  simpa only [hgame] using hotp adversary hadversary

/-- Theorem 2.8 applies to `leakyOtpEncrypt`: every uniform strict PPT parity predictor has
negligible advantage on its `(n + 1)`-bit messages. -/
example {A : ℕ → List Bool → ProbComp Bool}
    (hA : IsPPTOn (encPair encUnary encBits) encBool (fun ⟨n, ct⟩ => A n ct)) :
    Negligible (parityWordAdvantage (fun n => n + 1) (fun n => n + 1) leakyOtpEncrypt A) :=
  demOneTimeKeyINDCPAOn_leakyOtpEncrypt.negligible_parityWordAdvantage (by fun_prop)
    (fun n => Nat.le_add_left 1 n) hA

/-- Submits two different `(n + 2)`-bit messages and returns the first bit of the ciphertext. -/
def lengthLeakAdversary : WordAdversary where
  choose n _ := pure ((List.replicate (n + 2) false, List.replicate (n + 2) true), [])
  guess _ _ ct := pure (ct.headD false)

/-- `lengthLeakAdversary` is uniform strict PPT. -/
theorem isPPT_lengthLeakAdversary : AdversaryOf.IsPPT encBits lengthLeakAdversary where
  choose := IsPPTOn.isPPT (ComputableInPolyTime.isPPTOn (by polytime))
  guess := ComputableInPolyTime.isPPTOn (by polytime)

/-- `leakyOtpEncrypt` fails `DEMOneTimeKeyWordINDCPA`, which admits every equal-length pair:
`lengthLeakAdversary` reads the challenge bit off an `(n + 2)`-bit plaintext sent in the clear. So
the premise of Theorem 2.8 on the message space is strictly weaker than equal-length security. -/
theorem not_demOneTimeKeyWordINDCPA_leakyOtpEncrypt :
    ¬ DEMOneTimeKeyWordINDCPA (fun n => n + 1) leakyOtpEncrypt := by
  intro hsec
  have heval : ∀ b n, ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
      (fun n => n + 1) leakyOtpEncrypt lengthLeakAdversary b n) = PMF.pure b := by
    intro b n
    cases b <;> simp only [demKeyGameOn, lengthLeakAdversary, leakyOtpEncrypt, ChoiceOut.msg₀,
      ChoiceOut.msg₁, List.replicate_succ, List.length_cons, List.length_replicate,
      beq_self_eq_true, ↓reduceIte, Nat.succ_ne_self, List.headD_cons, Bool.false_eq_true,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, BitString.eval_sampleList,
      PMF.bind_const]
  have hadv : ∀ n, Game.advantage
      (ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) (fun n => n + 1)
        leakyOtpEncrypt lengthLeakAdversary false n))
      (ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) (fun n => n + 1)
        leakyOtpEncrypt lengthLeakAdversary true n)) = 1 := by
    intro n
    rw [heval false n, heval true n]
    simp [Game.advantage, Game.succProbability]
  exact not_negligible_const one_ne_zero
    ((hsec lengthLeakAdversary isPPT_lengthLeakAdversary).congr hadv)

end MessageSpace

end CslibFrontierTests.Crypto.ParityPrediction
