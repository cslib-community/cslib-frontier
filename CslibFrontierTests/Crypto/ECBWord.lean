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

Checks word-level ECB encryption and the admissible pairs of Theorem 4.1 on a concrete block
cipher: equal blocks or too many blocks make a pair inadmissible.
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

/-- ECB of the key-masking cipher at `n = 2` masks each 2-bit block with the key. -/
example : xorCipher.ecbEncrypt 2 [true, false] [false, false, true, true] =
    pure [true, false, false, true] :=
  congrArg pure (by decide)

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
