/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.CCAToCPA
import CslibFrontier.Probability.PMF.Support

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
    (SymmetricCipher.cpaToCCAAdversary id (SymmetricCipher.detCPAAdversary id)) :=
  SymmetricCipher.isOraclePPT_cpaToCCAAdversary ComputableInPolyTime.id'
    (SymmetricCipher.isOraclePPT_detCPAAdversary ComputableInPolyTime.id')

-- That same adversary has CCA advantage `1` against a cipher with exact ciphertext length `n`,
-- for `n ≥ 1`: the bound `id` satisfies `CiphertextLengthLE`, so its CCA game is the CPA game.
example (E : SymmetricCipher) {n : ℕ} (hn : 1 ≤ n) (hlen : E.CiphertextLength n n) :
    Game.advantage
      (ProbComp.eval (E.ccaGame
        (SymmetricCipher.cpaToCCAAdversary id (SymmetricCipher.detCPAAdversary id)) false n))
      (ProbComp.eval (E.ccaGame
        (SymmetricCipher.cpaToCCAAdversary id (SymmetricCipher.detCPAAdversary id)) true
          n)) = 1 := by
  have hle : E.CiphertextLengthLE n (id n) :=
    fun k hk msg hmsg ct hct => (hlen k hk msg hmsg ct hct).le
  rw [SymmetricCipher.eval_ccaGame_cpaToCCAAdversary E id _ false n hle,
    SymmetricCipher.eval_ccaGame_cpaToCCAAdversary E id _ true n hle]
  refine E.advantage_cpaGame_detCPAAdversary id hn hle fun ke hke => ?_
  obtain ⟨c₀, hc₀⟩ := (ProbComp.eval (E.encrypt n ke (List.replicate n false))).support_nonempty
  refine ⟨c₀, ?_⟩
  simpa [PMF.map_id] using (PMF.map_eq_pure_iff (f := id) (b := c₀)).mpr fun c hc =>
    E.encrypt_eq_of_ciphertext_length_eq hke (hlen ke hke) List.length_replicate hc hc₀

end CslibFrontierTests.Crypto.CCAToCPA
