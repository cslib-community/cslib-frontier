/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.PlaintextIntegrity
import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC
import CslibFrontier.Crypto.Computational.Encryption.RealIdealAE
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Tests for chosen-ciphertext security with plaintext integrity

An ordinary `module` client of `CslibFrontier.Crypto.Computational.Encryption.PlaintextIntegrity`
(Boneh–Shoup, Exercise 9.15(b)).

* Exercise 9.15(b): `INDCCA` and `EncForge` give `CiphertextIntegrity`, `AuthenticatedEncryption`
  and real/ideal security. With `AuthenticatedEncryption.indcca` and `CiphertextIntegrity.encForge`
  from `main`, authenticated encryption is exactly `INDCCA` together with `EncForge`, and under
  `INDCCA` plaintext integrity is equivalent to ciphertext integrity.
* The hypotheses are satisfiable: Encrypt-then-MAC from a pseudorandom function meets them.
* Both certificates applied to a CI adversary that asks nothing, and the concrete bound applied to
  it, where the collision term vanishes, and to an adversary that makes one encryption query,
  where it is `1 / 2ⁿ`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.PlaintextIntegrity

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM

-- Exercise 9.15(b): CCA security and plaintext integrity give ciphertext integrity, authenticated
-- encryption and real/ideal security.
example {E : SymmetricCipher} (hcca : E.INDCCA) (hef : E.EncForge) :
    E.CiphertextIntegrity ∧ E.AuthenticatedEncryption ∧ E.RealIdealAE :=
  ⟨hcca.ciphertextIntegrity hef, hcca.authenticatedEncryption hef,
    (hcca.authenticatedEncryption hef).realIdealAE⟩

-- Authenticated encryption is exactly CCA security with plaintext integrity.
example {E : SymmetricCipher} : E.AuthenticatedEncryption ↔ E.INDCCA ∧ E.EncForge :=
  ⟨fun h => ⟨h.indcca, h.2.encForge⟩, fun h => h.1.authenticatedEncryption h.2⟩

-- Under CCA security, plaintext integrity and ciphertext integrity are equivalent.
example {E : SymmetricCipher} (hcca : E.INDCCA) : E.EncForge ↔ E.CiphertextIntegrity :=
  ⟨hcca.ciphertextIntegrity, SymmetricCipher.CiphertextIntegrity.encForge⟩

-- The hypotheses are satisfiable: Encrypt-then-MAC from a pseudorandom function is CCA-secure and
-- has plaintext integrity (the latter from its own authenticated encryption), so the theorem
-- applies to it.
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    (prfEncryptThenMAC family hprf.polyTime hprf.length_eq).AuthenticatedEncryption :=
  hprf.indcca_prfEncryptThenMAC.authenticatedEncryption
    hprf.authenticatedEncryption_prfEncryptThenMAC.2.encForge

/-- A CI adversary that asks nothing and outputs the empty ciphertext. -/
def silentAdversary : CIAdversary :=
  fun _ _ => pure []

theorem isOraclePPT_silentAdversary : IsOraclePPT encBits silentAdversary := by
  unfold silentAdversary
  ppt

-- Both certificates apply to the reductions built from it.
example : IsOraclePPT encBool
    (SymmetricCipher.ciToCCAAdversary (fun n => n) (fun _ => 0) silentAdversary) :=
  SymmetricCipher.isOraclePPT_ciToCCAAdversary (by polytime) (by polytime)
    isOraclePPT_silentAdversary

example : IsOraclePPT encBits
    (SymmetricCipher.ciToRandEncForgeAdversary (fun n => n) (fun _ => 0) silentAdversary) :=
  SymmetricCipher.isOraclePPT_ciToRandEncForgeAdversary (by polytime) (by polytime)
    isOraclePPT_silentAdversary

-- With no encryption queries the collision term of the bound vanishes.
example (E : SymmetricCipher) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.succProbability (ProbComp.eval (E.ciGame silentAdversary n)) : ℝ) ≤
      (Game.succProbability (ProbComp.eval (E.encForgeGame
        (SymmetricCipher.ciToRandEncForgeAdversary ctBound (fun _ => 0) silentAdversary) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (E.ccaGame
          (SymmetricCipher.ciToCCAAdversary ctBound (fun _ => 0) silentAdversary) false n))
        (ProbComp.eval (E.ccaGame
          (SymmetricCipher.ciToCCAAdversary ctBound (fun _ => 0) silentAdversary) true n)) :
          ℝ) := by
  simpa using SymmetricCipher.succProbability_ciGame_le_encForge_add_indcca E ctBound
    (fun _ => 0) silentAdversary n (.pure _ _) hctBound

/-- A CI adversary that asks for an encryption of the all-zero `n`-bit message and outputs at most
`n` bits of the reply as its forgery. -/
def replayAdversary : CIAdversary :=
  fun n _ => List.take n <$> ProbOracleComp.query ((), List.replicate n false)

theorem isOraclePPT_replayAdversary : IsOraclePPT encBits replayAdversary :=
  IsOraclePPTOn.query_take' () (by fun_prop) (by fun_prop)

theorem isQueryBounded_replayAdversary (n : ℕ) : (replayAdversary n []).IsQueryBounded 1 := by
  simpa [replayAdversary, map_eq_bind_pure_comp] using
    (ProbOracleComp.IsQueryBounded.query ((), List.replicate n false)).bind fun _ => .pure _ 0

-- Both certificates apply to the reductions built from it.
example : IsOraclePPT encBool
      (SymmetricCipher.ciToCCAAdversary (fun n => n) (fun _ => 1) replayAdversary) ∧
    IsOraclePPT encBits
      (SymmetricCipher.ciToRandEncForgeAdversary (fun n => n) (fun _ => 1) replayAdversary) :=
  ⟨SymmetricCipher.isOraclePPT_ciToCCAAdversary (by polytime) (by polytime)
      isOraclePPT_replayAdversary,
    SymmetricCipher.isOraclePPT_ciToRandEncForgeAdversary (by polytime) (by polytime)
      isOraclePPT_replayAdversary⟩

-- With one encryption query the collision term of the bound is `1 / 2ⁿ`.
example (E : SymmetricCipher) (ctBound : ℕ → ℕ) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.succProbability (ProbComp.eval (E.ciGame replayAdversary n)) : ℝ) ≤
      (Game.succProbability (ProbComp.eval (E.encForgeGame
        (SymmetricCipher.ciToRandEncForgeAdversary ctBound (fun _ => 1) replayAdversary) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (E.ccaGame
          (SymmetricCipher.ciToCCAAdversary ctBound (fun _ => 1) replayAdversary) false n))
        (ProbComp.eval (E.ccaGame
          (SymmetricCipher.ciToCCAAdversary ctBound (fun _ => 1) replayAdversary) true n)) :
          ℝ) +
      1 / 2 ^ n := by
  simpa using SymmetricCipher.succProbability_ciGame_le_encForge_add_indcca E ctBound
    (fun _ => 1) replayAdversary n (isQueryBounded_replayAdversary n) hctBound

end CslibFrontierTests.Crypto.PlaintextIntegrity
