/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.PseudorandomPermutation.BirthdayAttack
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for the word-level birthday attack on block ciphers

Tests PPT and query-bound certification for `wordBirthdayDistinguisher`, exact concrete PRF
advantage `1 / 2` and non-PRF refutation on a 1-bit `BlockCipher`, and a zero-block-length
counterexample showing `∀ᶠ n in atTop, 1 ≤ E.blockLen n` in
`BlockCipher.not_pseudorandomFunctionOver_of_not_negligible` is necessary.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.WordBirthdayAttack

open Cslib Cslib.Crypto Probability Turing.MultiTapeTM Filter
open scoped NNReal

private def oneBitIdCipher : BlockCipher where
  keyLen := id
  blockLen := fun _ => 1
  keyLen_polyTime := ComputableInPolyTime.id'
  blockLen_polyTime := ComputableInPolyTime.const 1
  encrypt _ _ block := block
  decrypt _ _ block := block
  encrypt_polyTime := ComputableInPolyTime.snd' (.snd _ _)
  decrypt_polyTime := ComputableInPolyTime.snd' (.snd _ _)
  length_encrypt _ _ _ _ hblock := hblock
  length_decrypt _ _ _ _ hblock := hblock
  decrypt_encrypt _ _ _ _ _ := rfl
  encrypt_decrypt _ _ _ _ _ := rfl

example : IsOraclePPT encBool (wordBirthdayDistinguisher oneBitIdCipher.blockLen (fun _ => 2)) :=
  isOraclePPT_wordBirthdayDistinguisher oneBitIdCipher.blockLen_polyTime
    (ComputableInPolyTime.const 2)

example (n : ℕ) (aux : List Bool) :
    ProbOracleComp.IsQueryBounded
      (wordBirthdayDistinguisher oneBitIdCipher.blockLen (fun _ => 2) n aux) 2 := by
  simpa [oneBitIdCipher] using
    isQueryBounded_wordBirthdayDistinguisher oneBitIdCipher.blockLen (fun _ => 2) n aux

example (n : ℕ) :
    (Game.advantage
      (ProbComp.eval (prfRealGame oneBitIdCipher.blockLen
        (fun key query => oneBitIdCipher.encrypt key.length key query)
        (wordBirthdayDistinguisher oneBitIdCipher.blockLen (fun _ => 2)) n))
      (ProbComp.eval (prfIdealGame oneBitIdCipher.blockLen oneBitIdCipher.blockLen
        (wordBirthdayDistinguisher oneBitIdCipher.blockLen (fun _ => 2)) n)) : ℝ) = 1 / 2 := by
  rw [oneBitIdCipher.coe_prfAdvantage_wordBirthdayDistinguisher rfl (fun _ => 2) n]
  norm_num [oneBitIdCipher, Nat.descFactorial]

example (n : ℕ) :
    (1 / 2 : ℝ≥0) ≤ Game.advantage
      (ProbComp.eval (prfRealGame oneBitIdCipher.blockLen
        (fun key query => oneBitIdCipher.encrypt key.length key query)
        (wordBirthdayDistinguisher oneBitIdCipher.blockLen (fun _ => 2)) n))
      (ProbComp.eval (prfIdealGame oneBitIdCipher.blockLen oneBitIdCipher.blockLen
        (wordBirthdayDistinguisher oneBitIdCipher.blockLen (fun _ => 2)) n)) :=
  oneBitIdCipher.half_le_prfAdvantage_wordBirthdayDistinguisher
    rfl (fun _ => 2) le_rfl (by norm_num [oneBitIdCipher])

example : ¬ PseudorandomFunctionOver oneBitIdCipher.blockLen oneBitIdCipher.blockLen
    (fun key query => oneBitIdCipher.encrypt key.length key query) :=
  oneBitIdCipher.not_pseudorandomFunctionOver_of_not_negligible rfl
    (Eventually.of_forall fun _ => le_rfl)
    (by simpa [oneBitIdCipher] using not_negligible_const (c := (2⁻¹ : ℝ≥0)) (by norm_num))

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
  decrypt_encrypt _ _ _ _ hblock := (List.length_eq_zero_iff.mp hblock).symm
  encrypt_decrypt _ _ _ _ hblock := (List.length_eq_zero_iff.mp hblock).symm

example : ¬ Negligible fun n => ((2 : ℝ≥0) ^ zeroBlockCipher.blockLen n)⁻¹ := by
  simpa [zeroBlockCipher] using not_negligible_const (c := (1 : ℝ≥0)) one_ne_zero

example : PseudorandomFunctionOver zeroBlockCipher.blockLen zeroBlockCipher.blockLen
    (fun key query => zeroBlockCipher.encrypt key.length key query) := by
  refine
    { polyTime := ComputableInPolyTime.const []
      length_eq := fun _ _ _ => rfl
      secure := fun A _ => ?_ }
  change Negligible fun n => Game.advantage
    (ProbComp.eval (prfRealGame (fun _ => 0)
      (fun key query => zeroBlockCipher.encrypt key.length key query) A n))
    (ProbComp.eval (prfIdealGame (fun _ => 0) (fun _ => 0) A n))
  have hzero : (fun n => Game.advantage
      (ProbComp.eval (prfRealGame (fun _ => 0)
        (fun key query => zeroBlockCipher.encrypt key.length key query) A n))
      (ProbComp.eval (prfIdealGame (fun _ => 0) (fun _ => 0) A n))) = fun _ => 0 := by
    funext n
    have hconst : ∀ g : BitString 0 → BitString 0,
        (fun req : Unit × List Bool => (pure (randomFunctionOracle 0 g req.2) : ProbComp _)) =
          fun req => pure (if req.2.length = 0 then [] else []) := fun g => rfl
    have hreal : ProbComp.eval (prfRealGame (fun _ => 0)
        (fun key query => zeroBlockCipher.encrypt key.length key query) A n) =
        ProbComp.eval ((A n []).run fun req =>
          pure (if req.2.length = 0 then [] else [])) := by
      simp only [prfRealGame, ProbComp.eval_bind, BitString.eval_sampleList]
      have horacle : (fun key : List Bool => ProbComp.eval ((A n []).run fun req =>
            pure (prfOracle
              (fun key query => zeroBlockCipher.encrypt key.length key query) 0 key req.2))) =
          fun _ => ProbComp.eval ((A n []).run fun req =>
            pure (if req.2.length = 0 then [] else [])) := by
        funext key; congr 3
      rw [horacle, PMF.bind_const]
    have hideal : ProbComp.eval (prfIdealGame (fun _ => 0) (fun _ => 0) A n) =
        ProbComp.eval ((A n []).run fun req =>
          pure (if req.2.length = 0 then [] else [])) := by
      simp only [prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform]
      have horacle : (fun f : BitString 0 → BitString 0 => ProbComp.eval ((A n []).run fun req =>
            pure (randomFunctionOracle 0 f req.2))) =
          fun _ => ProbComp.eval ((A n []).run fun req =>
            pure (if req.2.length = 0 then [] else [])) := by
        funext f; rw [hconst]
      rw [horacle, PMF.bind_const]
    rw [hreal, hideal, Game.advantage_self]
  rw [hzero]
  exact negligible_zero

end CslibFrontierTests.Crypto.WordBirthdayAttack
