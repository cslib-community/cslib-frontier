/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.CCA

/-!
# Non-adaptive 1CCA security for public-key encryption

[BonehShoup2023], Exercise 12.28 (printed p. 522), defines a weaker notion than CCA security: the
CCA attack game in which the adversary makes all of its decryption queries before its encryption
query, with a single encryption query. The book calls it *non-adaptive 1CCA security*.

`INDCCA1On` is that notion. It is the single-challenge 1CCA experiment `cca2GameOn` of
`INDCCA2On`, played only by the adversaries whose guessing stage makes no decryption query
(`IsQueryBounded 0`), so that no decryption query follows the encryption query. Since nothing is
decrypted after the challenge, the source's rule that the challenge itself is never decrypted holds
automatically. As in the rest of the library, the digit in `INDCCA1On` and `INDCCA2On` is the usual
name of the attack, not the number of encryption queries; both are one-query notions.

The source calls the notion weaker than CCA security and proves neither of the implications
CCA ⇒ non-adaptive 1CCA ⇒ CPA. The first restricts the class of adversaries. The second plays a
chosen-plaintext adversary through the existing lift `CCA2AdversaryOf.ofCPA`, which makes no
decryption query.

Not formalized here: the multi-query form of the notion and the source's statement that one
encryption query suffices (the analogue of Theorem 12.1), and parts (a) and (b) of the
exercise.

## Main definitions

* `Cslib.Crypto.Encryption.INDCCA1On`: non-adaptive 1CCA security with challenge-pair admissibility
  predicate `valid`.

## Main results

* `Cslib.Crypto.Encryption.INDCCA2On.indcca1On`: 1CCA security implies non-adaptive 1CCA security.
* `Cslib.Crypto.Encryption.INDCCA1On.indcpaOn`: non-adaptive 1CCA security implies IND-CPA security.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 12.1 (Attack Game 12.1, Definition 12.2, pp. 467–468) and
  Exercise 12.28 (p. 522).
-/

public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- Non-adaptive 1CCA security ([BonehShoup2023], Exercise 12.28, printed p. 522): no decryption
query after the encryption query. It is the 1CCA experiment `cca2GameOn` of `INDCCA2On` with
challenge-pair admissibility predicate `valid`, against the uniform strict oracle PPT adversaries
whose guessing stage makes no decryption query, for every saved state word and ciphertext (as in
`CCA2AdversaryOf.IsQueryBounded`), not only those the game produces. -/
@[expose] def INDCCA1On {Msg Out : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encMsg : Msg ↪ List Bool) (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out) : Prop :=
  Game.Indistinguishable
    (fun adversary n =>
      ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt adversary false n))
    (fun adversary n =>
      ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt adversary true n))
    (fun adversary => CCA2AdversaryOf.IsPPT encMsg adversary ∧
      ∀ n state ct, (adversary.guess n state ct).IsQueryBounded 0)

/-- **1CCA security implies non-adaptive 1CCA security**: the adversaries of `INDCCA1On` are among
those of `INDCCA2On`. -/
theorem INDCCA2On.indcca1On {Msg Out : Type} {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA2On valid encMsg encOut keyGen encrypt decrypt) :
    INDCCA1On valid encMsg encOut keyGen encrypt decrypt :=
  h.of_admissible fun _ hA => hA.1

/-- **Non-adaptive 1CCA security implies IND-CPA security**: the lift `CCA2AdversaryOf.ofCPA` of
a chosen-plaintext adversary makes no decryption query, and its game has the chosen-plaintext
law. -/
theorem INDCCA1On.indcpaOn {Msg Out : Type} {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA1On valid encMsg encOut keyGen encrypt decrypt) :
    INDCPAOn valid encMsg keyGen encrypt := by
  intro adversary hA
  simpa only [eval_cca2GameOn_ofCPA] using h (CCA2AdversaryOf.ofCPA adversary)
    ⟨CCA2AdversaryOf.isPPT_ofCPA hA, (CCA2AdversaryOf.isQueryBounded_ofCPA adversary).2⟩

end Cslib.Crypto.Encryption
