/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Encryption.MACThenEncrypt.EncForge

/-!
# Tests for plaintext integrity of MAC-then-Encrypt

Exercise 9.15(a) of Boneh–Shoup as one statement, its instance from a pseudorandom function, and
the Note under (a): MAC-then-Encrypt over the malleable cipher `extendCipher` is CPA-secure and has
plaintext integrity, yet is not CCA-secure and has no ciphertext integrity.
-/

namespace CslibFrontierTests.Crypto.MACThenEncryptEncForge

open Cslib Cslib.Crypto Turing.MultiTapeTM

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

end CslibFrontierTests.Crypto.MACThenEncryptEncForge
