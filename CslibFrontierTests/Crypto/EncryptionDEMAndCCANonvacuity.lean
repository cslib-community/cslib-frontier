/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Computational.Encryption.CCA
import CslibFrontier.Crypto.Computational.Encryption.CCA.Multi
import CslibFrontier.Crypto.Computational.Encryption.Hybrid
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Word
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.WordBridge
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

set_option linter.privateModule false

/-!
# Non-vacuity witnesses for DEM, CCA2, and word-level Fujisaki–Okamoto IND-CPA assumptions

Ordinary `module` test suite providing refutation (and positive where applicable) non-vacuity
witnesses for the assumptions listed below:

1. **`Encryption.DEMOneTimeKeyINDCPAOn`, `DEMOneTimeKeyINDCPAOf`, `DEMOneTimeINDCPAOn`,
   `DEMOneTimeINDCPAOf`** (`Encryption/Hybrid.lean`):
   * Positive checks on `otpKeyWordEncrypt` and `otpWordEncrypt`
     (`demOneTimeKeyINDCPA_otpKeyWordEncrypt`, `demOneTimeINDCPA_otpWordEncrypt`, and equal-length
     instances).
   * Uniform negative refutations on the plaintext-echoing DEM `idDEM _ _ m := pure m` across all
     four DEM predicates via a single shared advantage calculation (`advantage_demKeyGameOn_idDEM`).
2. **`Encryption.WordINDCCA2`, `INDCCA2MultiOn`, `WordINDCCA2Multi`**
   (`Encryption/CCA.lean`, `Encryption/CCA/Multi.lean`):
   * Refutations on the complete (`idWordDecrypt` inverts `leakWordEncrypt`) plaintext-leaking
     scheme `constKeyGen` / `leakWordEncrypt` / `idWordDecrypt` via `INDCCA2On.indcpaOn` and
     `INDCCA2MultiOn.indcca2On` (complementing existing positive instances in
     `CslibFrontierTests.Crypto.CCA`).
3. **`Protocols.FujisakiOkamoto.WordPKE.INDCPA`** (`Protocols/KEM/FujisakiOkamoto/Word.lean`):
   * Refutes `trivialWordPKE.INDCPA` for an efficient, ciphertext-fitting, `0`-correct word PKE,
     showing `WordPKE.INDCPA` genuinely fails even when all other FO hypotheses hold.
-/

namespace CslibFrontierTests.Crypto.EncryptionDEMAndCCANonvacuity

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Encryption Turing.MultiTapeTM
open Cslib.Crypto.Protocols.FujisakiOkamoto
open scoped NNReal

private theorem succProbability_pure_true : Game.succProbability (PMF.pure true) = 1 := by
  simp [Game.succProbability]

/-! ### 1. One-time DEM IND-CPA assumptions -/

/-- A fixed equal-length bit adversary choosing `([false], [true])` and reading the head bit. -/
private def wordBitAdversary : WordAdversary where
  choose _ _ := pure (([false], [true]), [])
  guess _ _ ct := pure (ct.headD false)

private theorem wordBitAdversary_isPPT : wordBitAdversary.IsPPT where
  choose := (ComputableInPolyTime.const (([false], [true]), ([] : List Bool))).isPPTOn
  guess := by
    change IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool
      (fun p : ℕ × List Bool × List Bool => pure (p.2.2.headD false))
    have hct : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.2)
        (encPair encUnary (encPair encBits encBits)) encBits := by fun_prop
    exact ((ComputableInPolyTime.headD false).comp hct).isPPTOn

/-- Plaintext-leaking DEM: ignores the symmetric key and returns the message verbatim. -/
private def idDEM (_ : ℕ) (_ : List Bool) (msg : List Bool) : ProbComp (List Bool) :=
  pure msg

/-- On any admissibility predicate accepting `([false], [true])` under empty key, `wordBitAdversary`
has exact distinguishing advantage `1` against `idDEM`. -/
private theorem advantage_demKeyGameOn_idDEM (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (keyLen : ℕ → ℕ) (n : ℕ) (hvalid : valid n [] [false] [true] = true) :
    Game.advantage
      (ProbComp.eval (demKeyGameOn valid keyLen idDEM wordBitAdversary false n))
      (ProbComp.eval (demKeyGameOn valid keyLen idDEM wordBitAdversary true n)) = 1 := by
  have hfalse :
      ProbComp.eval (demKeyGameOn valid keyLen idDEM wordBitAdversary false n) =
        PMF.pure false := by
    simp [demKeyGameOn, idDEM, wordBitAdversary, ChoiceOut.msg₀, ChoiceOut.msg₁, hvalid,
      PMF.map, Function.comp_def, PMF.bind_const]
  have htrue :
      ProbComp.eval (demKeyGameOn valid keyLen idDEM wordBitAdversary true n) = PMF.pure true := by
    simp [demKeyGameOn, idDEM, wordBitAdversary, ChoiceOut.msg₀, ChoiceOut.msg₁, hvalid,
      PMF.map, Function.comp_def, PMF.bind_const]
  rw [hfalse, htrue, Game.advantage_comm, Game.advantage_pure_false, succProbability_pure_true]

/-- Helper turning advantage `1` on a DEM game into negation of `DEMOneTimeKeyINDCPAOn`. -/
theorem not_demOneTimeKeyINDCPAOn_idDEM
    {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    (keyLen : ℕ → ℕ) (hvalid : ∀ n, valid n [] [false] [true] = true) :
    ¬ DEMOneTimeKeyINDCPAOn valid encBits keyLen idDEM := by
  intro hsec
  have hneg := hsec wordBitAdversary wordBitAdversary_isPPT
  simp only [advantage_demKeyGameOn_idDEM valid keyLen _ (hvalid _)] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- Unrestricted key-scheduled DEM security fails on `idDEM`. -/
theorem not_demOneTimeKeyINDCPAOf_idDEM (keyLen : ℕ → ℕ) :
    ¬ DEMOneTimeKeyINDCPAOf encBits keyLen idDEM :=
  not_demOneTimeKeyINDCPAOn_idDEM keyLen fun _ => rfl

/-- Normalized (`n`-bit key) admissible DEM security fails on `idDEM` whenever `([false], [true])`
is admissible (for example equal-length pairs). -/
theorem not_demOneTimeINDCPAOn_idDEM
    {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    (hvalid : ∀ n, valid n [] [false] [true] = true) :
    ¬ DEMOneTimeINDCPAOn valid encBits idDEM :=
  not_demOneTimeKeyINDCPAOn_idDEM (fun n => n) hvalid

/-- Equal-length normalized word DEM security (`DEMOneTimeWordINDCPA`) fails on `idDEM`. -/
theorem not_demOneTimeWordINDCPA_idDEM :
    ¬ DEMOneTimeWordINDCPA idDEM :=
  not_demOneTimeINDCPAOn_idDEM fun _ => rfl

/-- Unrestricted normalized (`n`-bit key) DEM security fails on `idDEM`. -/
theorem not_demOneTimeINDCPAOf_idDEM :
    ¬ DEMOneTimeINDCPAOf encBits idDEM :=
  not_demOneTimeINDCPAOn_idDEM fun _ => rfl

/-- Positive non-vacuity check: `otpKeyWordEncrypt` satisfies both `DEMOneTimeKeyINDCPAOf` and
equal-length `DEMOneTimeKeyINDCPAOn`, and `otpWordEncrypt` satisfies `DEMOneTimeINDCPAOf` and
`DEMOneTimeWordINDCPA` (`DEMOneTimeINDCPAOn`). -/
example (keyLen : ℕ → ℕ) :
    DEMOneTimeKeyINDCPAOf encBits keyLen (otpKeyWordEncrypt keyLen) ∧
    DEMOneTimeKeyWordINDCPA keyLen (otpKeyWordEncrypt keyLen) ∧
    DEMOneTimeINDCPAOf encBits otpWordEncrypt ∧
    DEMOneTimeWordINDCPA otpWordEncrypt :=
  ⟨demOneTimeKeyINDCPA_otpKeyWordEncrypt keyLen,
   demOneTimeKeyWordINDCPA_otpKeyWordEncrypt keyLen,
   demOneTimeINDCPA_otpWordEncrypt,
   demOneTimeWordINDCPA_otpWordEncrypt⟩

/-! ### 2. Word-level 1CCA and multi-challenge CCA2 assumptions -/

private def constKeyGen (_ : ℕ) : ProbComp (List Bool × List Bool) :=
  pure ([], [])

private def leakWordEncrypt (_ : ℕ) (_ : List Bool) (msg : List Bool) : ProbComp (List Bool) :=
  pure msg

private def idWordDecrypt (_ : ℕ) (_ : List Bool) (ct : List Bool) : Option (List Bool) :=
  some ct

/-- Whenever `valid n [] [false] [true] = true` for all `n`, `leakWordEncrypt` fails `INDCPAOn`. -/
private theorem not_indcpaOn_leak {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    (hvalid : ∀ n, valid n [] [false] [true] = true) :
    ¬ INDCPAOn valid encBits constKeyGen leakWordEncrypt := by
  intro hsec
  have hneg := hsec wordBitAdversary wordBitAdversary_isPPT
  have hfalse (n : ℕ) :
      ProbComp.eval (gameOn valid constKeyGen leakWordEncrypt wordBitAdversary false n) =
        PMF.pure false := by
    simp [gameOn, constKeyGen, leakWordEncrypt, wordBitAdversary, ChoiceOut.msg₀, ChoiceOut.msg₁]
  have htrue (n : ℕ) :
      ProbComp.eval (gameOn valid constKeyGen leakWordEncrypt wordBitAdversary true n) =
        PMF.pure true := by
    simp [gameOn, constKeyGen, leakWordEncrypt, wordBitAdversary, ChoiceOut.msg₀, ChoiceOut.msg₁,
      hvalid n]
  simp only [hfalse, htrue] at hneg
  rw [Game.advantage_comm, Game.advantage_pure_false, succProbability_pure_true] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- Whenever `valid n [] [false] [true] = true` for all `n`, `leakWordEncrypt` fails `INDCCA2On`
for any decryption oracle. -/
theorem not_indcca2On_leak {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    (hvalid : ∀ n, valid n [] [false] [true] = true)
    (decrypt : ℕ → List Bool → List Bool → Option (List Bool)) :
    ¬ INDCCA2On valid encBits encBits constKeyGen leakWordEncrypt decrypt :=
  fun hCCA => not_indcpaOn_leak hvalid hCCA.indcpaOn

/-- Plaintext-leaking encryption with full decryption fails `WordINDCCA2`. -/
theorem not_wordINDCCA2_leak :
    ¬ WordINDCCA2 constKeyGen leakWordEncrypt idWordDecrypt :=
  not_indcca2On_leak (fun _ => rfl) idWordDecrypt

/-- Whenever `valid n [] [false] [true] = true` for all `n`, `leakWordEncrypt` fails
`INDCCA2MultiOn` for any decryption oracle. -/
theorem not_indcca2MultiOn_leak {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    (hvalid : ∀ n, valid n [] [false] [true] = true)
    (decrypt : ℕ → List Bool → List Bool → Option (List Bool)) :
    ¬ INDCCA2MultiOn valid encBits encBits constKeyGen leakWordEncrypt decrypt :=
  fun hMulti => not_indcca2On_leak hvalid decrypt hMulti.indcca2On

/-- Plaintext-leaking encryption with full decryption fails `WordINDCCA2Multi`. -/
theorem not_wordINDCCA2Multi_leak :
    ¬ WordINDCCA2Multi constKeyGen leakWordEncrypt idWordDecrypt :=
  not_indcca2MultiOn_leak (fun _ => rfl) idWordDecrypt

/-! ### 3. Fujisaki–Okamoto `WordPKE.INDCPA` -/

/-- Efficient, ciphertext-fitting, `0`-correct word PKE whose encryption leaks the message. -/
private def trivialWordPKE : WordPKE where
  msgLen n := n
  coinLen _ := 0
  ctLen n := n
  keyGen _ := pure ([], [])
  encDet _ _ m _ := m
  dec _ _ c := some c

theorem trivialWordPKE_isEfficient : trivialWordPKE.IsEfficient where
  msgLen := by simp only [trivialWordPKE]; fun_prop
  coinLen := by simp only [trivialWordPKE]; fun_prop
  ctLen := by simp only [trivialWordPKE]; fun_prop
  keyGen := (ComputableInPolyTime.const (([], []) : List Bool × List Bool)).isPPTOn
  encDet := by simp only [trivialWordPKE]; fun_prop
  dec := by simp only [trivialWordPKE]; fun_prop

theorem trivialWordPKE_ciphertextFits : trivialWordPKE.CiphertextFits := by
  intro n _ _ _ m _ hm _
  simp only [trivialWordPKE] at hm ⊢
  omega

/-- `trivialWordPKE` is perfectly (`0`-)correct at every parameter. -/
theorem trivialWordPKE_deltaCorrect : trivialWordPKE.DeltaCorrect fun _ => 0 := fun n =>
  (trivialWordPKE.finitePKE n).deltaCorrect_zero_of_perfect fun pk sk _ m r _ => by
    change BitString n at m
    simp [WordPKE.finitePKE, WordPKE.toCiphertext, trivialWordPKE]

/-- Message-length-respecting CPA adversary choosing `(0^n, 1^n)` and reading the head bit. -/
private def trivialWordPKEAdversary : WordAdversary where
  choose n _ := pure ((List.replicate n false, List.replicate n true), [])
  guess _ _ ct := pure (ct.headD false)

private theorem trivialWordPKEAdversary_isPPT : trivialWordPKEAdversary.IsPPT where
  choose := by
    change IsPPTOn (encPair encUnary encBits) (encPair (encPair encBits encBits) encBits)
      (fun p : ℕ × List Bool => pure ((List.replicate p.1 false, List.replicate p.1 true), []))
    have hn : ComputableInPolyTime (fun p : ℕ × List Bool => p.1)
        (encPair encUnary encBits) encUnary := by fun_prop
    have hf := (ComputableInPolyTime.bitsReplicate false).comp hn
    have ht := (ComputableInPolyTime.bitsReplicate true).comp hn
    exact ((hf.prod ht).prod (ComputableInPolyTime.const [])).isPPTOn
  guess := wordBitAdversary_isPPT.guess

/-- The efficient, ciphertext-fitting word PKE `trivialWordPKE` fails `WordPKE.INDCPA`. -/
theorem not_wordPKE_indcpa_trivial : ¬ trivialWordPKE.INDCPA := by
  intro hsec
  have hneg := (hsec trivialWordPKEAdversary trivialWordPKEAdversary_isPPT).shift 1
  have hfalse (n : ℕ) :
      ProbComp.eval (Encryption.gameOn trivialWordPKE.IsMessagePair trivialWordPKE.keyGen
        trivialWordPKE.encrypt trivialWordPKEAdversary false (n + 1)) = PMF.pure false := by
    have hhd : (List.replicate (n + 1) false).head?.getD false = false := by
      rw [List.replicate_succ]; rfl
    simp [Encryption.gameOn, WordPKE.encrypt, WordPKE.IsMessagePair, trivialWordPKE,
      trivialWordPKEAdversary, ChoiceOut.msg₀, ChoiceOut.msg₁, hhd]
  have htrue (n : ℕ) :
      ProbComp.eval (Encryption.gameOn trivialWordPKE.IsMessagePair trivialWordPKE.keyGen
        trivialWordPKE.encrypt trivialWordPKEAdversary true (n + 1)) = PMF.pure true := by
    have hhd : (List.replicate (n + 1) true).head?.getD false = true := by
      rw [List.replicate_succ]; rfl
    simp [Encryption.gameOn, WordPKE.encrypt, WordPKE.IsMessagePair, trivialWordPKE,
      trivialWordPKEAdversary, ChoiceOut.msg₀, ChoiceOut.msg₁, hhd]
  simp only [hfalse, htrue] at hneg
  rw [Game.advantage_comm, Game.advantage_pure_false, succProbability_pure_true] at hneg
  exact not_negligible_const one_ne_zero hneg

end CslibFrontierTests.Crypto.EncryptionDEMAndCCANonvacuity
