/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Encryption.IdentityBased
import CslibFrontier.Crypto.Negligible.Basic

/-! Clients of identity-based encryption (`Encryption/IdentityBased.lean`) under module
encapsulation. Each of the three notions has a correct scheme that satisfies it and a correct
scheme that fails it: the cleartext scheme fails all three, a scheme whose ciphertext is the
identity is semantically secure but not private on a one-message space, and the constant-ciphertext
scheme on that space is private. Against the cleartext scheme, a key query for a challenge
identity, in either stage, voids the run, and a key query for another identity does not. A scheme
with distinct master keys checks which key the adversary, the oracle and the encryption receive.
The library API is imported publicly because the fixtures below mention its types. -/

public section

namespace CslibFrontierTests.Crypto.IdentityBased

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Encryption Turing.MultiTapeTM

/-- The guess "copy the first ciphertext bit" is strict oracle PPT on `(n, state, ct)`. -/
private theorem isOraclePPTOn_copyGuess :
    IsOraclePPTOn (Operation := Unit) encGuessInput encBool
      (fun x : ℕ × List Bool × List Bool =>
        (pure (x.2.2.headD false) : WordOracleComp Unit Bool)) :=
  ((ComputableInPolyTime.headD false).comp (g := fun x : ℕ × List Bool × List Bool => x.2.2)
    (by fun_prop)).isOraclePPTOn

/-! ### The cleartext scheme fails all three notions -/

/-- Send the message bit as the ciphertext, whatever the identity. -/
noncomputable def cleartext : WordIBE Bool := fun _ =>
  { setup := pure ([], []), keyGen := fun _ _ => pure [], encrypt := fun _ _ m => pure [m],
    decrypt := fun _ c => c.head? }

/-- The cleartext scheme decrypts its ciphertexts. -/
theorem cleartext_correct (n : ℕ) : (cleartext n).Correct := by
  simp [IBE.Correct, cleartext]

/-- Target the empty identity, challenge with `false` and `true`, and copy the ciphertext bit. -/
noncomputable def copyBit : SelectiveIBEAdversaryOf Bool where
  target _ := pure ([], [])
  choose _ _ _ := pure ((false, true), [])
  guess _ _ ct := pure (ct.headD false)

theorem copyBit_isPPT : copyBit.IsPPT encBool where
  target := (ComputableInPolyTime.const _).isPPTOn
  choose := (ComputableInPolyTime.const _).isOraclePPTOn
  guess := isOraclePPTOn_copyGuess

/-- Against the cleartext scheme, `copyBit` outputs the challenge bit. -/
theorem eval_copyBit (bit : Bool) (n : ℕ) :
    ProbComp.eval (privateIBEGameOn (fun _ _ _ _ => true) cleartext
      copyBit.toAdaptive.toPrivate bit n) = PMF.pure bit := by
  cases bit <;>
    simp [privateIBEGameOn, cleartext, copyBit, SelectiveIBEAdversaryOf.toAdaptive,
      IBEAdversaryOf.toPrivate]

/-- **The cleartext scheme is not selectively secure.** -/
theorem not_ibeSelectiveOn_cleartext :
    ¬ IBESelectiveOn (fun _ _ _ _ => true) encBool cleartext := by
  intro h
  have hneg := h copyBit copyBit_isPPT
  simp only [eval_copyBit] at hneg
  refine not_negligible_const ?_ hneg
  simp [Game.advantage, Game.succProbability]

-- Hence, through the two implications, it is neither semantically secure nor private.
example : ¬ IBESemanticOn (fun _ _ _ _ => true) encBool cleartext :=
  fun h => not_ibeSelectiveOn_cleartext h.ibeSelectiveOn

example : ¬ IBEPrivateOn (fun _ _ _ _ => true) encBool cleartext :=
  fun h => not_ibeSelectiveOn_cleartext h.ibeSemanticOn.ibeSelectiveOn

/-! ### The final check on the key log -/

/-- Ask for the key of `asked` in the first stage, then challenge `challenge` with `false` and
`true` and copy the ciphertext bit. -/
noncomputable def askFirst (asked challenge : List Bool) : IBEAdversaryOf Bool where
  choose _ _ := do
    let _ ← ProbOracleComp.query ((), asked)
    pure ((challenge, false, true), [])
  guess _ _ ct := pure (ct.headD false)

/-- Challenge `challenge` with `false` and `true`, then ask for the key of `asked` and copy the
ciphertext bit. -/
noncomputable def askSecond (asked challenge : List Bool) : IBEAdversaryOf Bool where
  choose _ _ := pure ((challenge, false, true), [])
  guess _ _ ct := do
    let _ ← ProbOracleComp.query ((), asked)
    pure (ct.headD false)

-- A key query for the challenge identity voids the run, in the first stage and in the second.
example (bit : Bool) (n : ℕ) :
    ProbComp.eval (privateIBEGameOn (fun _ _ _ _ => true) cleartext
      (askFirst [true] [true]).toPrivate bit n) = PMF.pure false := by
  cases bit <;> simp [privateIBEGameOn, cleartext, askFirst, IBEAdversaryOf.toPrivate]

example (bit : Bool) (n : ℕ) :
    ProbComp.eval (privateIBEGameOn (fun _ _ _ _ => true) cleartext
      (askSecond [true] [true]).toPrivate bit n) = PMF.pure false := by
  cases bit <;> simp [privateIBEGameOn, cleartext, askSecond, IBEAdversaryOf.toPrivate]

-- A key query for another identity leaves the run alone, in either stage.
example (bit : Bool) (n : ℕ) :
    ProbComp.eval (privateIBEGameOn (fun _ _ _ _ => true) cleartext
      (askFirst [false] [true]).toPrivate bit n) = PMF.pure bit := by
  cases bit <;> simp [privateIBEGameOn, cleartext, askFirst, IBEAdversaryOf.toPrivate]

example (bit : Bool) (n : ℕ) :
    ProbComp.eval (privateIBEGameOn (fun _ _ _ _ => true) cleartext
      (askSecond [false] [true]).toPrivate bit n) = PMF.pure bit := by
  cases bit <;> simp [privateIBEGameOn, cleartext, askSecond, IBEAdversaryOf.toPrivate]

/-- Ask for the key of `asked`, then challenge the pairs `([false], false)` and `([true], true)`
and copy the ciphertext bit. -/
noncomputable def askPrivate (asked : List Bool) : PrivateIBEAdversaryOf Bool where
  choose _ _ := do
    let _ ← ProbOracleComp.query ((), asked)
    pure ((([false], false), ([true], true)), [])
  guess _ _ ct := pure (ct.headD false)

-- In the private game, a key query for either challenge identity voids the run.
example (bit : Bool) (n : ℕ) :
    ProbComp.eval (privateIBEGameOn (fun _ _ _ _ => true) cleartext (askPrivate [false]) bit n) =
      PMF.pure false := by
  cases bit <;> simp [privateIBEGameOn, cleartext, askPrivate]

example (bit : Bool) (n : ℕ) :
    ProbComp.eval (privateIBEGameOn (fun _ _ _ _ => true) cleartext (askPrivate [true]) bit n) =
      PMF.pure false := by
  cases bit <;> simp [privateIBEGameOn, cleartext, askPrivate]

example (bit : Bool) (n : ℕ) :
    ProbComp.eval (privateIBEGameOn (fun _ _ _ _ => true) cleartext (askPrivate []) bit n) =
      PMF.pure bit := by
  cases bit <;> simp [privateIBEGameOn, cleartext, askPrivate]

/-! ### Which master key goes where -/

/-- A scheme whose master keys differ: the master public key is `[true]`, the master secret key is
`[false, true]`, the key of an identity is the master secret key followed by the identity, and a
ciphertext is the message bit followed by the master public key. -/
noncomputable def twoKeys : WordIBE Bool := fun _ =>
  { setup := pure ([true], [false, true]), keyGen := fun msk id => pure (msk ++ id),
    encrypt := fun mpk _ m => pure (m :: mpk), decrypt := fun _ c => c.head? }

theorem twoKeys_correct (n : ℕ) : (twoKeys n).Correct := by
  simp [IBE.Correct, twoKeys]

/-- Ask for the key of `[true, true]`, save the master public key followed by the reply, challenge
the empty identity with `false` and `true`, and output `test` of the saved word and the
ciphertext. -/
noncomputable def inspect (test : List Bool → List Bool → Bool) : IBEAdversaryOf Bool where
  choose _ mpk := do
    let key ← ProbOracleComp.query ((), [true, true])
    pure (([], false, true), mpk ++ key)
  guess _ state ct := pure (test state ct)

-- The first stage receives the master public key, and the oracle answers with the key that
-- `keyGen` derives from the master secret key: the saved word is
-- `[true] ++ ([false, true] ++ [true, true])`.
example (bit : Bool) (n : ℕ) :
    ProbComp.eval (privateIBEGameOn (fun _ _ _ _ => true) twoKeys
      (inspect fun state _ => state == [true, false, true, true, true]).toPrivate bit n) =
      PMF.pure true := by
  cases bit <;> simp [privateIBEGameOn, twoKeys, inspect, IBEAdversaryOf.toPrivate]

-- With the two master keys exchanged the saved word would be `[false, true, true, true, true]`.
example (bit : Bool) (n : ℕ) :
    ProbComp.eval (privateIBEGameOn (fun _ _ _ _ => true) twoKeys
      (inspect fun state _ => state == [false, true, true, true, true]).toPrivate bit n) =
      PMF.pure false := by
  cases bit <;> simp [privateIBEGameOn, twoKeys, inspect, IBEAdversaryOf.toPrivate]

-- The challenge is encrypted under the master public key: the ciphertext is `[bit, true]`.
example (bit : Bool) (n : ℕ) :
    ProbComp.eval (privateIBEGameOn (fun _ _ _ _ => true) twoKeys
      (inspect fun _ ct => ct == [bit, true]).toPrivate bit n) = PMF.pure true := by
  cases bit <;> simp [privateIBEGameOn, twoKeys, inspect, IBEAdversaryOf.toPrivate]

/-! ### Privacy asks more than semantic security, on a one-message space -/

/-- The ciphertext is the recipient's identity, over the one-message space `Unit`. With one
message, semantic security holds trivially. Over two messages a correct semantically secure scheme
is not known unconditionally (it gives public-key encryption), so separating the notions there is
conditional. -/
noncomputable def revealId : WordIBE Unit := fun _ =>
  { setup := pure ([], []), keyGen := fun _ _ => pure [], encrypt := fun _ id _ => pure id,
    decrypt := fun _ _ => some () }

theorem revealId_correct (n : ℕ) : (revealId n).Correct := by
  simp [IBE.Correct, revealId]

/-- **`revealId` is semantically secure**, for every challenge rule. -/
theorem ibeSemanticOn_revealId
    (valid : ℕ → List Bool → List Bool × Unit → List Bool × Unit → Bool) :
    IBESemanticOn valid encUnit revealId := by
  intro A _
  have h (n : ℕ) : ProbComp.eval (privateIBEGameOn valid revealId A.toPrivate false n) =
      ProbComp.eval (privateIBEGameOn valid revealId A.toPrivate true n) := by
    simp [privateIBEGameOn, revealId, IBEAdversaryOf.toPrivate]
  simp only [h, Game.advantage_self]
  exact negligible_zero

/-- Challenge the identities `[false]` and `[true]` and read the bit off the ciphertext. -/
noncomputable def readId : PrivateIBEAdversaryOf Unit where
  choose _ _ := pure ((([false], ()), ([true], ())), [])
  guess _ _ ct := pure (ct.headD false)

theorem readId_isPPT : readId.IsPPT encUnit where
  choose := (ComputableInPolyTime.const _).isOraclePPTOn
  guess := isOraclePPTOn_copyGuess

/-- **`revealId` is not private.** -/
theorem not_ibePrivateOn_revealId : ¬ IBEPrivateOn (fun _ _ _ _ => true) encUnit revealId := by
  intro h
  have hneg := h readId readId_isPPT
  have heval (bit : Bool) (n : ℕ) : ProbComp.eval
      (privateIBEGameOn (fun _ _ _ _ => true) revealId readId bit n) = PMF.pure bit := by
    cases bit <;> simp [privateIBEGameOn, revealId, readId]
  simp only [heval] at hneg
  refine not_negligible_const ?_ hneg
  simp [Game.advantage, Game.succProbability]

/-- The constant ciphertext `[]` over the one-message space `Unit`. -/
noncomputable def constCipher : WordIBE Unit := fun _ =>
  { setup := pure ([], []), keyGen := fun _ _ => pure [], encrypt := fun _ _ _ => pure [],
    decrypt := fun _ _ => some () }

theorem constCipher_correct (n : ℕ) : (constCipher n).Correct := by
  simp [IBE.Correct, constCipher]

/-- **The constant-ciphertext scheme is private**, for every challenge rule. -/
theorem ibePrivateOn_constCipher
    (valid : ℕ → List Bool → List Bool × Unit → List Bool × Unit → Bool) :
    IBEPrivateOn valid encUnit constCipher := by
  intro A _
  have h (n : ℕ) : ProbComp.eval (privateIBEGameOn valid constCipher A false n) =
      ProbComp.eval (privateIBEGameOn valid constCipher A true n) := by
    simp [privateIBEGameOn, constCipher]
  simp only [h, Game.advantage_self]
  exact negligible_zero

end CslibFrontierTests.Crypto.IdentityBased
