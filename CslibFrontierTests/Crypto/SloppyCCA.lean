/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Encryption.CCA.Sloppy

/-! Clients of `Encryption.not_indcca2On_sloppy` and `Encryption.advantage_cca2GameOn_sloppy`
([BonehShoup2023], Exercise 12.2, p. 512) on the plaintext scheme over `Bool`, whose ciphertext of
`b` is `[b]`. -/

public section

namespace CslibFrontierTests.Crypto.SloppyCCA

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Encryption Turing.MultiTapeTM

/-- Key generation of the plaintext scheme: empty keys. -/
noncomputable def plainKeyGen : ℕ → ProbComp (List Bool × List Bool) := fun _ => pure ([], [])

/-- Encryption of the plaintext scheme: the ciphertext of `b` is `[b]`. -/
noncomputable def plainEncrypt : ℕ → List Bool → Bool → ProbComp (List Bool) :=
  fun _ _ b => pure [b]

/-- Decryption of the plaintext scheme: the first ciphertext bit. -/
def plainDecrypt : ℕ → List Bool → List Bool → Option Bool := fun _ _ ct => ct.head?

theorem plain_correct (n : ℕ) :
    (PKE.mk (plainKeyGen n) (plainEncrypt n) (plainDecrypt n)).Correct := by
  intro keys _ m c hc
  simp only [plainEncrypt, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hc
  simp [hc, plainDecrypt]

-- The sloppy plaintext scheme is not 1CCA secure: the challenge pair `(false, true)` is
-- polynomial-time, admissible and distinct.
example : ¬ INDCCA2On (fun _ _ _ _ => true) encBool encBool plainKeyGen
    (sloppyEncrypt plainEncrypt) (sloppyDecrypt plainDecrypt) :=
  not_indcca2On_sloppy (msg₀ := fun _ _ => false) (msg₁ := fun _ _ => true) (.const false)
    (.const true) plain_correct (fun _ _ _ => rfl) fun _ _ _ => Bool.false_ne_true

-- The bit-flipping adversary has advantage exactly `1` at every parameter.
example (n : ℕ) :
    Game.advantage
      (ProbComp.eval (cca2GameOn (fun _ _ _ _ => true) encBool plainKeyGen
        (sloppyEncrypt plainEncrypt) (sloppyDecrypt plainDecrypt)
        (maulAdversary (fun _ _ => false) (fun _ _ => true)
          (fun _ _ ct => ct.dropLast ++ [true]) (fun _ _ => encOption encBool (some true)))
        false n))
      (ProbComp.eval (cca2GameOn (fun _ _ _ _ => true) encBool plainKeyGen
        (sloppyEncrypt plainEncrypt) (sloppyDecrypt plainDecrypt)
        (maulAdversary (fun _ _ => false) (fun _ _ => true)
          (fun _ _ ct => ct.dropLast ++ [true]) (fun _ _ => encOption encBool (some true)))
        true n)) = 1 :=
  advantage_cca2GameOn_sloppy (plain_correct n) (fun _ _ => rfl) fun _ _ => Bool.false_ne_true

-- The transformation changes every sloppy ciphertext but not its decryption, for any decryptor:
-- this is why `eval_cca2GameOn_maulAdversary` asks only that the ciphertext change.
example {Out : Type} (decrypt : ℕ → List Bool → List Bool → Option Out) (n : ℕ)
    (sk c : List Bool) :
    (c ++ [false]).dropLast ++ [true] ≠ c ++ [false] ∧
      sloppyDecrypt decrypt n sk ((c ++ [false]).dropLast ++ [true]) =
        sloppyDecrypt decrypt n sk (c ++ [false]) := by
  simp [sloppyDecrypt]

end CslibFrontierTests.Crypto.SloppyCCA
