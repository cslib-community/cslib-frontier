/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Encryption.CCA.Sloppy

/-! Clients of the sloppy-CCA API ([BonehShoup2023], Exercise 12.2, p. 512): the plaintext scheme
over `Bool`, whose ciphertext of `b` is `[b]`, turned sloppy; and one failing case for each
hypothesis of `Encryption.not_indcca2On_sloppy`. -/

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

/-! ### The attack -/

-- The sloppy plaintext scheme is again correct.
example (n : ℕ) : (PKE.mk (plainKeyGen n) (sloppyEncrypt plainEncrypt n)
    (sloppyDecrypt plainDecrypt n)).Correct :=
  sloppy_correct (plain_correct n)

-- The adversary with challenge pair `(false, true)` is strict oracle PPT.
example : (sloppyAdversary encBool (fun _ _ => false) (fun _ _ => true)).IsPPT encBool :=
  isPPT_sloppyAdversary (.const false) (.const true)

-- It has advantage exactly `1` at every parameter.
example (n : ℕ) :
    Game.advantage
      (ProbComp.eval (cca2GameOn (fun _ _ _ _ => true) encBool plainKeyGen
        (sloppyEncrypt plainEncrypt) (sloppyDecrypt plainDecrypt)
        (sloppyAdversary encBool (fun _ _ => false) (fun _ _ => true)) false n))
      (ProbComp.eval (cca2GameOn (fun _ _ _ _ => true) encBool plainKeyGen
        (sloppyEncrypt plainEncrypt) (sloppyDecrypt plainDecrypt)
        (sloppyAdversary encBool (fun _ _ => false) (fun _ _ => true)) true n)) = 1 :=
  advantage_cca2GameOn_sloppyAdversary (plain_correct n) (fun _ _ => rfl)
    fun _ _ => Bool.false_ne_true

-- So the sloppy plaintext scheme is not 1CCA secure.
example : ¬ INDCCA2On (fun _ _ _ _ => true) encBool encBool plainKeyGen
    (sloppyEncrypt plainEncrypt) (sloppyDecrypt plainDecrypt) :=
  not_indcca2On_sloppy (msg₀ := fun _ _ => false) (msg₁ := fun _ _ => true) (.const false)
    (.const true) plain_correct (fun _ _ _ => rfl) fun _ _ _ => Bool.false_ne_true

-- The transformation changes every sloppy ciphertext but not its decryption, for any decryptor:
-- this is why `eval_cca2GameOn_maulAdversary` asks only that the ciphertext change.
example {Out : Type} (decrypt : ℕ → List Bool → List Bool → Option Out) (n : ℕ)
    (sk c : List Bool) :
    (c ++ [false]).dropLast ++ [true] ≠ c ++ [false] ∧
      sloppyDecrypt decrypt n sk ((c ++ [false]).dropLast ++ [true]) =
        sloppyDecrypt decrypt n sk (c ++ [false]) := by
  simp

/-! ### Each hypothesis is needed

When encryption has the same law on every admissible pair, the two worlds of the 1CCA game have the
same law, so the scheme is `INDCCA2On`. Each example below drops one hypothesis of
`not_indcca2On_sloppy` and keeps the others. -/

/-- If encryption has the same law on both messages of every admissible pair, every scheme is
`INDCCA2On`. -/
theorem indcca2On_of_eval_encrypt_eq {Msg Out : Type} {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : ∀ n pk m₀ m₁, valid n pk m₀ m₁ = true →
      ProbComp.eval (encrypt n pk m₀) = ProbComp.eval (encrypt n pk m₁)) :
    INDCCA2On valid encMsg encOut keyGen encrypt decrypt := by
  have hgame : ∀ adversary n,
      ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt adversary false n) =
        ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt adversary true n) := by
    intro adversary n
    simp only [cca2GameOn, ProbComp.eval_bind]
    refine congrArg _ (funext fun keys => congrArg _ (funext fun choiceOut => ?_))
    by_cases hv : valid n keys.1 (ChoiceOut.msg₀ choiceOut.1) (ChoiceOut.msg₁ choiceOut.1) = true
    · simp only [hv, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind, h n _ _ _ hv]
    · simp only [hv, Bool.false_eq_true, ↓reduceIte]
  unfold INDCCA2On
  simp only [hgame]
  exact Game.Indistinguishable.refl _ _

-- `hvalid` is needed: when no pair is admissible, every sloppy scheme is `INDCCA2On`.
example {Msg : Type} {encMsg : Msg ↪ List Bool} {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Msg} :
    INDCCA2On (fun _ _ _ _ => false) encMsg encMsg keyGen (sloppyEncrypt encrypt)
      (sloppyDecrypt decrypt) :=
  indcca2On_of_eval_encrypt_eq fun _ _ _ _ h => absurd h Bool.false_ne_true

-- `hne` is needed: over a one-element message type, every sloppy scheme is `INDCCA2On`.
example {encMsg : Unit ↪ List Bool} {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Unit → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Unit} :
    INDCCA2On (fun _ _ _ _ => true) encMsg encMsg keyGen (sloppyEncrypt encrypt)
      (sloppyDecrypt decrypt) :=
  indcca2On_of_eval_encrypt_eq fun _ _ m₀ m₁ _ => by rw [Subsingleton.elim m₀ m₁]

-- `hcorrect` is needed: the scheme with the empty ciphertext and a rejecting decryptor, which is
-- not correct, turns into a sloppy scheme that is `INDCCA2On`, although `(false, true)` is a
-- polynomial-time, distinct, admissible pair.
example : INDCCA2On (fun _ _ _ _ => true) encBool encBool plainKeyGen
    (sloppyEncrypt fun _ _ (_ : Bool) => pure [])
    (sloppyDecrypt fun _ _ _ => (none : Option Bool)) :=
  indcca2On_of_eval_encrypt_eq fun _ _ _ _ _ => by simp only [eval_sloppyEncrypt]

end CslibFrontierTests.Crypto.SloppyCCA
