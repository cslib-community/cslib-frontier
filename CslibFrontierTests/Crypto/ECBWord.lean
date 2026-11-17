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
cipher (equal blocks, too many blocks, a partial final block or unequal lengths make a pair
inadmissible), and applies the three theorems as a caller does: Theorem 4.1 at the block bounds
`ℓ = id` and `ℓ = 3`, and equation (4.3) with the reduction's certificate for a PPT adversary.
-/

public section

namespace Cslib.Tests.ECBWord

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

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

/-- ECB drops a final partial block: the third bit of a 3-bit message is not encrypted. -/
example : xorCipher.ecbEncrypt 2 [true, false] [false, false, true] = pure [true, false] :=
  congrArg pure (by decide)

/-- A pair whose messages end in a partial block is not admissible. -/
example : xorCipher.ecbAdmissible (fun _ => 2) 2 [] [false, false, true]
    [true, true, false] = false := by
  decide

/-- A pair of messages of different lengths is not admissible. -/
example : xorCipher.ecbAdmissible (fun _ => 2) 2 [] [false, true]
    [false, true, true, false] = false := by
  decide

/-- Theorem 4.1 for a secure block cipher, with the block bound `ℓ = id`. -/
example {E : BlockCipher} (hE : E.PRP) :
    Encryption.DEMOneTimeKeyINDCPAOn (E.ecbValid id) encBits E.keyLen E.ecbEncrypt :=
  hE.ecb_demOneTimeKeyINDCPAOn ComputableInPolyTime.id'

/-- Theorem 4.1 for a secure block cipher, with a constant block bound. -/
example {E : BlockCipher} (hE : E.PRP) :
    Encryption.DEMOneTimeKeyINDCPAOn (E.ecbValid fun _ => 3) encBits E.keyLen E.ecbEncrypt :=
  hE.ecb_demOneTimeKeyINDCPAOn (by fun_prop)

/-- Equation (4.3) on words, and the certificate of the reduction for a PPT adversary. -/
example (E : BlockCipher) {A : Encryption.AdversaryOf (List Bool)} (hA : A.IsPPT encBits)
    (n : ℕ) :
    Game.advantage
        (ProbComp.eval (Encryption.demKeyGameOn (E.ecbValid id) E.keyLen E.ecbEncrypt A false n))
        (ProbComp.eval (Encryption.demKeyGameOn (E.ecbValid id) E.keyLen E.ecbEncrypt A true n)) =
      2 * Game.advantage (ProbComp.eval (E.prpRealGame (E.ecbToPrpDistinguisher id A) n))
        (ProbComp.eval (prpIdealGame E.blockLen (E.ecbToPrpDistinguisher id A) n)) ∧
    IsOraclePPT encBool (E.ecbToPrpDistinguisher id A) :=
  ⟨E.advantage_demKeyGameOn_ecbEncrypt id A n,
    E.isOraclePPT_ecbToPrpDistinguisher ComputableInPolyTime.id' hA⟩

end Cslib.Tests.ECBWord
