/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.CCAToCPA

/-!
# Tests for `INDCCA → INDCPA`

`SymmetricCipher.INDCCA.indcpa` turns the CPA attack on a cipher without ciphertext expansion
(Boneh–Shoup Example 5.1) into a CCA attack: `cpaToCCAAdversary` applied to `detCPAAdversary` is a
certified CCA adversary of advantage `1`.
-/

namespace CslibFrontierTests.Crypto.CCAToCPA

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

-- A cipher whose ciphertexts of `n`-bit messages have exactly `n` bits is not CCA-secure.
example (E : SymmetricCipher) (hlen : ∀ n, E.CiphertextLength n n) : ¬ E.INDCCA :=
  fun h => E.not_indcpa_of_ciphertext_length_eq hlen h.indcpa

-- The reduction applied to the attack of Example 5.1 is an `IsOraclePPT` CCA adversary.
example : IsOraclePPT encBool
    (SymmetricCipher.cpaToCCAAdversary id SymmetricCipher.detCPAAdversary) :=
  SymmetricCipher.isOraclePPT_cpaToCCAAdversary ComputableInPolyTime.id'
    SymmetricCipher.isOraclePPT_detCPAAdversary

-- That same adversary has CCA advantage `1` against a cipher with exact ciphertext length `n`,
-- for `n ≥ 1`: the bound `id` satisfies `CiphertextLengthLE`, so its CCA game is the CPA game.
example (E : SymmetricCipher) {n : ℕ} (hn : 1 ≤ n) (hlen : E.CiphertextLength n n) :
    Game.advantage
      (ProbComp.eval (E.ccaGame
        (SymmetricCipher.cpaToCCAAdversary id SymmetricCipher.detCPAAdversary) false n))
      (ProbComp.eval (E.ccaGame
        (SymmetricCipher.cpaToCCAAdversary id SymmetricCipher.detCPAAdversary) true n)) = 1 := by
  have hle : E.CiphertextLengthLE n (id n) :=
    fun k hk msg hmsg ct hct => (hlen k hk msg hmsg ct hct).le
  rw [SymmetricCipher.eval_ccaGame_cpaToCCAAdversary E id _ false n hle,
    SymmetricCipher.eval_ccaGame_cpaToCCAAdversary E id _ true n hle]
  exact E.advantage_cpaGame_detCPAAdversary hn hlen

end CslibFrontierTests.Crypto.CCAToCPA
