/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Encryption.ECB
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for ECB mode of a word-level block cipher

Applies the two-block attack to a concrete block cipher. Its consequence is that the restriction
to distinct blocks in Theorem 4.1 is needed: on messages of up to two arbitrary blocks, ECB of
every block cipher, a pseudorandom one included, is not semantically secure. The tests also check
the admissible pairs on concrete words.
-/

public section

namespace Cslib.Tests.ECBWord

open Cslib Cslib.Crypto Turing.MultiTapeTM

/-- The key-masking cipher on `n`-bit keys and blocks. -/
def xorCipher : BlockCipher where
  keyLen := id
  blockLen := id
  keyLen_polyTime := ComputableInPolyTime.id'
  blockLen_polyTime := ComputableInPolyTime.id'
  encrypt _ key block := List.zipWith Bool.xor key block
  decrypt _ key block := List.zipWith Bool.xor key block
  encrypt_polyTime := by polytime
  decrypt_polyTime := by polytime
  length_encrypt _ _ _ hkey hblock := by simp [hkey, hblock]
  length_decrypt _ _ _ hkey hblock := by simp [hkey, hblock]
  decrypt_encrypt _ key block hkey hblock :=
    BitString.zipWith_xor_self_left key block (by simp [hkey, hblock])
  encrypt_decrypt _ key block hkey hblock :=
    BitString.zipWith_xor_self_left key block (by simp [hkey, hblock])

/-- At `n = 1`, with two admissible blocks, the two-block attack wins with certainty. -/
example :
    Game.advantage
        (ProbComp.eval (Encryption.demKeyGameOn (xorCipher.ecbAdmissible fun _ => 2)
          xorCipher.keyLen xorCipher.ecbEncrypt xorCipher.ecbTwoBlockAdversary false 1))
        (ProbComp.eval (Encryption.demKeyGameOn (xorCipher.ecbAdmissible fun _ => 2)
          xorCipher.keyLen xorCipher.ecbEncrypt xorCipher.ecbTwoBlockAdversary true 1)) = 1 :=
  xorCipher.advantage_demKeyGameOn_ecbTwoBlockAdversary (by decide) le_rfl

/-- On messages of up to two arbitrary blocks ECB is not semantically secure; Theorem 4.1 needs the
restriction to distinct blocks (`ecbValid`). -/
example :
    ¬ Encryption.DEMOneTimeKeyINDCPAOn (xorCipher.ecbAdmissible fun _ => 2) encBits
      xorCipher.keyLen xorCipher.ecbEncrypt :=
  xorCipher.not_demOneTimeKeyINDCPAOn_ecbAdmissible
    (Filter.eventually_atTop.mpr ⟨1, fun _ h => h⟩) (Filter.Eventually.of_forall fun _ => le_rfl)

/-- `0 1 ‖ 0 1` has two equal 2-bit blocks, so it is admissible on `X^{≤2}` but not on
`X_*^{≤2}`. -/
example : xorCipher.ecbAdmissible (fun _ => 2) 2 [] [false, true, false, true]
    [false, true, true, false] = true ∧
    xorCipher.ecbValid (fun _ => 2) 2 [] [false, true, false, true]
      [false, true, true, false] = false := by
  decide

/-- A pair of three-block messages exceeds the bound `ℓ = 2`. -/
example : xorCipher.ecbAdmissible (fun _ => 2) 1 [] [false, true, true]
    [true, false, false] = false := by
  decide

end Cslib.Tests.ECBWord
