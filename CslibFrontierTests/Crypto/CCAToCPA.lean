/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Encryption.CCAToCPA

/-!
# Tests for `INDCCA → INDCPA`

`SymmetricCipher.INDCCA.indcpa` turns the CPA attack on a cipher without ciphertext expansion
(Boneh–Shoup Example 5.1) into a CCA attack, and the game equality behind it accepts an exact
ciphertext length as its bound.
-/

namespace CslibFrontierTests.Crypto.CCAToCPA

open Cslib Cslib.Crypto

-- A cipher whose ciphertexts of `n`-bit messages have exactly `n` bits is not CCA-secure.
example (E : SymmetricCipher) (hlen : ∀ n, E.CiphertextLength n n) : ¬ E.INDCCA :=
  fun h => E.not_indcpa_of_ciphertext_length_eq hlen h.indcpa

-- With an exact ciphertext length `n`, the reduction with bound `n` plays the CPA game.
example (E : SymmetricCipher) (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ)
    (hlen : E.CiphertextLength n n) :
    ProbComp.eval (E.ccaGame (SymmetricCipher.cpaToCCAAdversary id adversary) bit n) =
      ProbComp.eval (E.cpaGame adversary bit n) :=
  E.eval_ccaGame_cpaToCCAAdversary id adversary bit n
    fun k hk msg hmsg ct hct => (hlen k hk msg hmsg ct hct).le

end CslibFrontierTests.Crypto.CCAToCPA
