/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.MACThenEncrypt.EncForge
import CslibFrontierTests.Crypto.MACThenEncryptFixture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Lookup
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Tests for plaintext integrity of MAC-then-Encrypt

An ordinary `module` client of
`CslibFrontier.Crypto.Computational.Encryption.MACThenEncrypt.EncForge` (Boneh–Shoup,
Exercise 9.15(a)).

* Exercise 9.15(a) as one statement, its instance from a pseudorandom function, and the Note under
  (a): MAC-then-Encrypt over the malleable cipher `extendCipher` is CPA-secure and has plaintext
  integrity, yet is not CCA-secure and has no ciphertext integrity.
* The echo cipher with the echo MAC (`tag = msg`): its MAC-then-Encrypt has no plaintext
  integrity, so `M.EUFCMA` cannot be dropped from `encForge_macThenEncrypt`. The certificate
  `isOraclePPT_mteToMACForger` applies to the forger built from the forging adversary, and the
  bound `succProbability_encForgeGame_macThenEncrypt_le` is tight there: the forger wins the MAC
  game with probability one.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.MACThenEncryptEncForge

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM
open CslibFrontierTests.Crypto.MACThenEncrypt (echoMAC echo_pairLen)

-- Exercise 9.15(a): MAC-then-Encrypt is CPA-secure and has plaintext integrity.
example (E : SymmetricCipher) (M : MACScheme) (ptLen : ℕ → ℕ)
    (hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary) (hmono : StrictMono ptLen)
    (hmsgLen : ∀ n, M.msgLen n = n)
    (hpairLen : ∀ n km, km ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km msg)).support,
        (encPair encBits encBits (msg, tag)).length = ptLen n)
    (hcpa : E.INDCPA) (heuf : M.EUFCMA) :
    (macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen).INDCPA ∧
      (macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen).EncForge :=
  ⟨indcpa_macThenEncrypt E M ptLen hptLenPoly hmono hmsgLen hpairLen hcpa,
    encForge_macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen heuf⟩

-- The same from a pseudorandom function: its cipher and its MAC, with pairs of `3 n + 1` bits.
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    let MTE := macThenEncrypt (prfCipher family hprf.polyTime hprf.length_eq)
      (prfMAC family hprf.polyTime) (fun n => 3 * n + 1) (by fun_prop) (fun _ => rfl)
      (prfMAC_pair_length family hprf.polyTime hprf.length_eq)
    MTE.INDCPA ∧ MTE.EncForge :=
  ⟨indcpa_macThenEncrypt _ _ _ _ (fun a b h => show 3 * a + 1 < 3 * b + 1 by omega) _ _
      hprf.indcpa_prfCipher,
    encForge_macThenEncrypt _ _ _ _ _ _ hprf.eufCma_prfMAC⟩

-- The Note under (a): over `extendCipher`, MAC-then-Encrypt keeps CPA security and plaintext
-- integrity, but it is not CCA-secure and has no ciphertext integrity.
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    let MTE := prfMacThenEncryptExtend family hprf.polyTime hprf.length_eq
    MTE.INDCPA ∧ MTE.EncForge ∧ ¬ MTE.INDCCA ∧ ¬ MTE.CiphertextIntegrity := by
  obtain ⟨-, -, hcpa, -, hci, -, hcca⟩ := hprf.prfMacThenEncryptExtend_counterexample
  exact ⟨hcpa, encForge_macThenEncrypt _ _ _ _ _ _ hprf.eufCma_prfMAC, hcca, hci⟩

/-- The cipher that sends every message to itself. -/
def echoCipher : SymmetricCipher where
  keyGen _ := pure []
  encrypt _ _ msg := pure msg
  decrypt _ _ ct := some ct
  keyGen_ppt := by ppt
  encrypt_ppt := by ppt
  decrypt_polyTime := by polytime
  decrypt_encrypt := by
    intro _ _ _ _ _ ct hct
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hct
    subst hct
    rfl

theorem ptLen_polyTime : ComputableInPolyTime (fun n => 3 * n + 1) encUnary encUnary := by
  polytime

/-- MAC-then-Encrypt over the echo cipher and the echo MAC. -/
noncomputable def echoMtE : SymmetricCipher :=
  macThenEncrypt echoCipher echoMAC (fun n => 3 * n + 1) ptLen_polyTime (fun _ => rfl) echo_pairLen

/-- Asks nothing and outputs the pair `(0ⁿ, 0ⁿ)`, which the echo MAC accepts. -/
def forgeAdv : CIAdversary :=
  fun n _ => pure (encPair encBits encBits (List.replicate n false, List.replicate n false))

theorem isOraclePPT_forgeAdv : IsOraclePPT encBits forgeAdv := by
  unfold forgeAdv
  ppt

theorem eval_encForgeGame_forgeAdv (n : ℕ) :
    ProbComp.eval (echoMtE.encForgeGame forgeAdv n) = PMF.pure true := by
  simp [echoMtE, macThenEncrypt, echoCipher, echoMAC, SymmetricCipher.encForgeGame, forgeAdv,
    ProbComp.eval_pure]

/-- `M.EUFCMA` cannot be dropped: every other argument of `encForge_macThenEncrypt` is supplied
here, and the conclusion fails. -/
theorem not_encForge_echoMtE : ¬ echoMtE.EncForge := fun h =>
  not_negligible_const (c := 1) one_ne_zero (by
    simpa [eval_encForgeGame_forgeAdv, Game.succProbability] using
      h.negligible forgeAdv isOraclePPT_forgeAdv)

-- The theorem used in the contrapositive: the echo MAC is not existentially unforgeable.
example : ¬ echoMAC.EUFCMA := fun h =>
  not_encForge_echoMtE (encForge_macThenEncrypt echoCipher echoMAC _ ptLen_polyTime (fun _ => rfl)
    echo_pairLen h)

-- The certificate applies to the forger that the bound is about.
example : IsOraclePPT (encPair encBits encBits)
    (mteToMACForger echoCipher echoMAC (fun n => 3 * n + 1) (fun n => n) forgeAdv) :=
  isOraclePPT_mteToMACForger echoCipher echoMAC ptLen_polyTime (by polytime) isOraclePPT_forgeAdv

-- The bound, with its tag-length hypothesis discharged, is tight here: the forger wins the MAC
-- game with probability one.
example (n : ℕ) :
    Game.succProbability (ProbComp.eval
      (echoMAC.eufCmaGame
        (mteToMACForger echoCipher echoMAC (fun n => 3 * n + 1) (fun n => n) forgeAdv) n)) = 1 := by
  refine le_antisymm ?_ ?_
  · exact Game.succProbability_le_one _
  · have h := succProbability_encForgeGame_macThenEncrypt_le echoCipher echoMAC
      (fun n => 3 * n + 1) ptLen_polyTime (fun _ => rfl) echo_pairLen (fun n => n) forgeAdv n
      (by
        intro km _ c hc tag htag
        change tag ∈ (ProbComp.eval (pure c)).support at htag
        simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
        subst htag
        exact hc.le)
    have h1 : Game.succProbability (ProbComp.eval (echoMtE.encForgeGame forgeAdv n)) = 1 := by
      simp [eval_encForgeGame_forgeAdv, Game.succProbability]
    exact h1 ▸ h

end CslibFrontierTests.Crypto.MACThenEncryptEncForge
