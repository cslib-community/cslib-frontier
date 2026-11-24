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

Checks word-level ECB encryption and the admissible pairs of §4.1.4 on concrete block ciphers,
applies Theorem 4.1 (`PRP.ecb_demOneTimeKeyINDCPAOn`), equation (4.3)
(`advantage_demKeyGameOn_ecbEncrypt`) and single-block semantic security
(`PRP.ecb_demOneTimeKeyINDCPAOn_one`), and checks the certified two-block attack
(`ecbTwoBlockAdversary`, `advantage_demKeyGameOn_ecbTwoBlockAdversary`,
`not_demOneTimeKeyINDCPAOn_ecbEncrypt`) together with the sharpness of both hypotheses
`2 ≤ ℓ n` and `1 ≤ E.blockLen n`.
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

/-- On `xorCipher` at `n ≥ 1` and `ℓ = fun _ => 2`, `ecbTwoBlockAdversary` is PPT and has
one-time advantage `1`. -/
example {n : ℕ} (hn : 1 ≤ n) :
    xorCipher.ecbTwoBlockAdversary.IsPPT encBits ∧
    Game.advantage
      (ProbComp.eval (Encryption.demKeyGameOn (xorCipher.ecbAdmissible fun _ => 2)
        xorCipher.keyLen xorCipher.ecbEncrypt xorCipher.ecbTwoBlockAdversary false n))
      (ProbComp.eval (Encryption.demKeyGameOn (xorCipher.ecbAdmissible fun _ => 2)
        xorCipher.keyLen xorCipher.ecbEncrypt xorCipher.ecbTwoBlockAdversary true n)) = 1 :=
  ⟨xorCipher.isPPT_ecbTwoBlockAdversary,
    xorCipher.advantage_demKeyGameOn_ecbTwoBlockAdversary le_rfl hn⟩

/-- `xorCipher` fails one-time semantic security on `ecbAdmissible` at both `ℓ = id` and
`ℓ = fun _ => 2`. -/
example :
    ¬ Encryption.DEMOneTimeKeyINDCPAOn (xorCipher.ecbAdmissible id) encBits xorCipher.keyLen
        xorCipher.ecbEncrypt ∧
    ¬ Encryption.DEMOneTimeKeyINDCPAOn (xorCipher.ecbAdmissible fun _ => 2) encBits
        xorCipher.keyLen xorCipher.ecbEncrypt :=
  ⟨xorCipher.not_demOneTimeKeyINDCPAOn_ecbEncrypt
      (((Filter.eventually_ge_atTop 2).mono fun _ hn => ⟨hn, le_trans (by decide) hn⟩).frequently),
    xorCipher.not_demOneTimeKeyINDCPAOn_ecbEncrypt
      (((Filter.eventually_ge_atTop 1).mono fun _ hn => ⟨le_rfl, hn⟩).frequently)⟩

/-- Even a secure block cipher (`E.PRP`) with `blockLen = id` fails one-time semantic security on
`ecbAdmissible` at both `ℓ = id` and `ℓ = fun _ => 2`. -/
example {E : BlockCipher} (_hE : E.PRP) (hblock : E.blockLen = id) :
    ¬ Encryption.DEMOneTimeKeyINDCPAOn (E.ecbAdmissible id) encBits E.keyLen E.ecbEncrypt ∧
    ¬ Encryption.DEMOneTimeKeyINDCPAOn (E.ecbAdmissible fun _ => 2) encBits E.keyLen
        E.ecbEncrypt :=
  ⟨E.not_demOneTimeKeyINDCPAOn_ecbEncrypt
      (((Filter.eventually_ge_atTop 2).mono fun _ hn =>
        ⟨hn, by simp only [hblock, id_eq]; omega⟩).frequently),
    E.not_demOneTimeKeyINDCPAOn_ecbEncrypt
      (((Filter.eventually_ge_atTop 1).mono fun _ hn =>
        ⟨le_rfl, by simp only [hblock, id_eq]; exact hn⟩).frequently)⟩

/-- Necessity of `2 ≤ ℓ n`: at `ℓ = fun _ => 1`, ECB of any secure block cipher is one-time
semantically secure on `ecbAdmissible` (§4.1.4, pp. 102, 104). -/
example {E : BlockCipher} (hE : E.PRP) :
    Encryption.DEMOneTimeKeyINDCPAOn (E.ecbAdmissible fun _ => 1) encBits E.keyLen E.ecbEncrypt :=
  hE.ecb_demOneTimeKeyINDCPAOn_one

/-- The degenerate block cipher on `0`-bit blocks, demonstrating necessity of `1 ≤ E.blockLen n` in
`not_demOneTimeKeyINDCPAOn_ecbEncrypt`. -/
private def zeroBlockCipher : BlockCipher where
  keyLen := id
  blockLen := fun _ => 0
  keyLen_polyTime := ComputableInPolyTime.id'
  blockLen_polyTime := ComputableInPolyTime.const 0
  encrypt _ _ _ := []
  decrypt _ _ _ := []
  encrypt_polyTime := ComputableInPolyTime.const []
  decrypt_polyTime := ComputableInPolyTime.const []
  length_encrypt _ _ _ _ _ := rfl
  length_decrypt _ _ _ _ _ := rfl
  decrypt_encrypt _ _ _ _ hblock := List.length_eq_zero_iff.mp hblock ▸ rfl
  encrypt_decrypt _ _ _ _ hblock := List.length_eq_zero_iff.mp hblock ▸ rfl

/-- At `blockLen = 0`, any non-empty message fails `blockPairValid 0`, and `zeroBlockCipher` is a
`PRP` that still satisfies `DEMOneTimeKeyINDCPAOn (zeroBlockCipher.ecbAdmissible fun _ => 2)`. -/
example :
    blockPairValid 0 [false] [true] = false ∧
    zeroBlockCipher.PRP ∧
    Encryption.DEMOneTimeKeyINDCPAOn (zeroBlockCipher.ecbAdmissible fun _ => 2) encBits
      zeroBlockCipher.keyLen zeroBlockCipher.ecbEncrypt := by
  refine ⟨by decide, fun D _ => ?_, fun A _ => ?_⟩
  · have hgame (n : ℕ) :
        ProbComp.eval (zeroBlockCipher.prpRealGame D n) =
          ProbComp.eval (prpIdealGame zeroBlockCipher.blockLen D n) := by
      simp [BlockCipher.prpRealGame, BlockCipher.prpOracle, prpIdealGame, randomPermOracle,
        randomFunctionOracle, zeroBlockCipher, PMF.bind_const]
    have hzero : (fun n => Game.advantage
        (ProbComp.eval (zeroBlockCipher.prpRealGame D n))
        (ProbComp.eval (prpIdealGame zeroBlockCipher.blockLen D n))) = fun _ => 0 := by
      ext n
      simp [hgame n, Game.advantage]
    rw [hzero]
    exact negligible_zero
  · have hgame (n : ℕ) :
        Encryption.demKeyGameOn (zeroBlockCipher.ecbAdmissible fun _ => 2) zeroBlockCipher.keyLen
            zeroBlockCipher.ecbEncrypt A false n =
          Encryption.demKeyGameOn (zeroBlockCipher.ecbAdmissible fun _ => 2) zeroBlockCipher.keyLen
            zeroBlockCipher.ecbEncrypt A true n := by
      have henc (k m : List Bool) : zeroBlockCipher.ecbEncrypt n k m = pure [] := by
        simp [BlockCipher.ecbEncrypt, BlockCipher.ecbBlocks, zeroBlockCipher]
      simp only [Encryption.demKeyGameOn, henc]
    have hzero : (fun n => Game.advantage
        (ProbComp.eval (Encryption.demKeyGameOn (zeroBlockCipher.ecbAdmissible fun _ => 2)
          zeroBlockCipher.keyLen zeroBlockCipher.ecbEncrypt A false n))
        (ProbComp.eval (Encryption.demKeyGameOn (zeroBlockCipher.ecbAdmissible fun _ => 2)
          zeroBlockCipher.keyLen zeroBlockCipher.ecbEncrypt A true n))) = fun _ => 0 := by
      ext n
      simp [hgame n, Game.advantage]
    rw [hzero]
    exact negligible_zero

end Cslib.Tests.ECBWord
