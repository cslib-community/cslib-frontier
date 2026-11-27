/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.CCA.Malleability
public import CslibFrontier.Crypto.Computational.Encryption.Scheme
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Tactic.PolyTime

/-!
# Sloppy CCA: an ignored ciphertext bit breaks CCA security

Boneh and Shoup's Exercise 12.2 ([BonehShoup2023], p. 512) turns a public-key scheme
`E = (G, E, D)` into `E′ = (G, E′, D′)` with `E′(pk, m) := E(pk, m) ‖ 0` and
`D′(sk, c) := D(sk, c[0 .. ℓ - 1])`: "the last ciphertext bit can be 0 or 1, but the decryption
algorithm ignores this bit." The exercise asks to show that `E′` is not CCA secure, with an
adversary of advantage `1` in the 1CCA attack game, even when `E` is CCA secure.

`sloppyEncrypt encrypt` appends `false` to every ciphertext and `sloppyDecrypt decrypt` decrypts a
ciphertext without its last bit (on ciphertexts of length `ℓ + 1`, this is `c[0 .. ℓ - 1]`); the
result is again correct. The adversary `sloppyAdversary` is `Encryption.maulAdversary` with
transformation `ct ↦ ct.dropLast ++ [true]`: it flips the appended bit of the challenge, which
yields a different ciphertext with the same decryption, so the Phase 2 oracle must answer it and
reveals the challenge plaintext. The theorems assume that
`(keyGen n, encrypt n, decrypt n)` is correct (`PKE.Correct`) and that the two challenge messages
are distinct and admissible under every honest public key; security of the original scheme is not
used.

The exercise's discussion of generalized CCA (gCCA), which rules out such attacks by rejecting
queries equivalent to the challenge under a scheme-specific relation, is not formalized here.

## Main definitions

* `Cslib.Crypto.Encryption.sloppyEncrypt`, `Cslib.Crypto.Encryption.sloppyDecrypt`: the scheme
  `E′` of Exercise 12.2.
* `Cslib.Crypto.Encryption.sloppyAdversary`: `maulAdversary` flipping the appended bit.

## Main results

* `Cslib.Crypto.Encryption.eval_sloppyEncrypt`,
  `Cslib.Crypto.Encryption.sloppyDecrypt_append_singleton`: the law of `E′`'s ciphertexts, and
  decryption ignoring the last bit.
* `Cslib.Crypto.Encryption.sloppy_correct`: `E′` is correct when `E` is.
* `Cslib.Crypto.Encryption.isPPT_sloppyAdversary`: the adversary is strict oracle PPT when its
  challenge messages are polynomial-time.
* `Cslib.Crypto.Encryption.advantage_cca2GameOn_sloppyAdversary`: the adversary has 1CCA advantage
  exactly `1` against `E′` at every parameter where `E` is correct and the two challenge messages
  are distinct and admissible.
* `Cslib.Crypto.Encryption.not_indcca2On_sloppy`: if this holds at every parameter and the
  challenge messages are polynomial-time, `E′` fails `INDCCA2On`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 12.2 (p. 512).
-/

public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- **Sloppy encryption** ([BonehShoup2023], Exercise 12.2, p. 512): encrypt with `encrypt` and
append the bit `false`. -/
def sloppyEncrypt {Msg : Type} (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) :
    ℕ → List Bool → Msg → ProbComp (List Bool) :=
  fun n pk m => (· ++ [false]) <$> encrypt n pk m

/-- **Sloppy decryption** ([BonehShoup2023], Exercise 12.2, p. 512): decrypt with `decrypt`
after dropping the last ciphertext bit, whatever it is. -/
def sloppyDecrypt {Out : Type} (decrypt : ℕ → List Bool → List Bool → Option Out) :
    ℕ → List Bool → List Bool → Option Out :=
  fun n sk ct => decrypt n sk ct.dropLast

/-- The law of a sloppy ciphertext: an encryption under `encrypt` followed by the bit `false`. -/
@[simp] theorem eval_sloppyEncrypt {Msg : Type}
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (n : ℕ) (pk : List Bool) (m : Msg) :
    ProbComp.eval (sloppyEncrypt encrypt n pk m) =
      PMF.map (· ++ [false]) (ProbComp.eval (encrypt n pk m)) := by
  simp only [sloppyEncrypt, ProbComp.eval_map]

/-- Sloppy decryption ignores the last bit. -/
@[simp] theorem sloppyDecrypt_append_singleton {Out : Type}
    (decrypt : ℕ → List Bool → List Bool → Option Out) (n : ℕ) (sk c : List Bool) (b : Bool) :
    sloppyDecrypt decrypt n sk (c ++ [b]) = decrypt n sk c := by
  simp only [sloppyDecrypt, List.dropLast_concat]

/-- **The sloppy scheme is correct** when the original scheme is: decryption drops the appended
bit and decrypts the original ciphertext. -/
theorem sloppy_correct {Msg : Type} {keyGen : ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Msg} {n : ℕ}
    (hcorrect : (PKE.mk keyGen (encrypt n) (decrypt n)).Correct) :
    (PKE.mk keyGen (sloppyEncrypt encrypt n) (sloppyDecrypt decrypt n)).Correct := by
  intro keys hkeys m ct hct
  simp only [eval_sloppyEncrypt, PMF.support_map, Set.mem_image] at hct
  obtain ⟨c, hc, rfl⟩ := hct
  simpa only [sloppyDecrypt_append_singleton] using hcorrect keys hkeys m c hc

/-- **The sloppy-CCA adversary** ([BonehShoup2023], Exercise 12.2, p. 512): `maulAdversary` with
challenge messages `msg₀ msg₁`, transformation `ct ↦ ct.dropLast ++ [true]`, which flips the
appended bit of a sloppy ciphertext, and target the encoding of `some (msg₁ n pk)`. -/
def sloppyAdversary {Msg : Type} (encMsg : Msg ↪ List Bool) (msg₀ msg₁ : ℕ → List Bool → Msg) :
    CCA2AdversaryOf Msg :=
  maulAdversary msg₀ msg₁ (fun _ _ ct => ct.dropLast ++ [true])
    (fun n pk => encOption encMsg (some (msg₁ n pk)))

/-- Replacing the last bit of the ciphertext by `true` is computable in polynomial time. -/
private theorem computableInPolyTime_setLastTrue :
    ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.2.dropLast ++ [true])
      encGuessInput encBits := by
  have h : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => (true :: p.2.2.reverse.tail).reverse)
      encGuessInput encBits := by
    fun_prop
  simpa only [List.tail_reverse, List.reverse_cons, List.reverse_reverse] using h

/-- `sloppyAdversary` is strict oracle PPT when its challenge messages are computable in
polynomial time. -/
theorem isPPT_sloppyAdversary {Msg : Type} {encMsg : Msg ↪ List Bool}
    {msg₀ msg₁ : ℕ → List Bool → Msg}
    (hmsg₀ : ComputableInPolyTime (fun ⟨n, pk⟩ => msg₀ n pk) (encPair encUnary encBits) encMsg)
    (hmsg₁ : ComputableInPolyTime (fun ⟨n, pk⟩ => msg₁ n pk) (encPair encUnary encBits) encMsg) :
    (sloppyAdversary encMsg msg₀ msg₁).IsPPT encMsg :=
  isPPT_maulAdversary hmsg₀ hmsg₁ computableInPolyTime_setLastTrue (by fun_prop)

/-- The malleability conditions of `eval_cca2GameOn_maulAdversary` for the sloppy scheme: on every
honest key pair and challenge ciphertext of world `bit`, replacing the last bit by `true` changes
the ciphertext, and its sloppy decryption is `some (msg₁ n pk)` exactly when `bit = true`. -/
private theorem sloppy_conditions {Msg : Type} {encMsg : Msg ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Msg}
    {msg₀ msg₁ : ℕ → List Bool → Msg} {n : ℕ}
    (hcorrect : (PKE.mk (keyGen n) (encrypt n) (decrypt n)).Correct)
    (hne : ∀ keys ∈ (ProbComp.eval (keyGen n)).support, msg₀ n keys.1 ≠ msg₁ n keys.1)
    (bit : Bool) {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (keyGen n)).support) {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (sloppyEncrypt encrypt n keys.1
      (if bit then msg₁ n keys.1 else msg₀ n keys.1))).support) :
    ct.dropLast ++ [true] ≠ ct ∧
      (encOption encMsg (sloppyDecrypt decrypt n keys.2 (ct.dropLast ++ [true])) =
        encOption encMsg (some (msg₁ n keys.1)) ↔ bit = true) := by
  simp only [eval_sloppyEncrypt, PMF.support_map, Set.mem_image] at hct
  obtain ⟨c, hc, rfl⟩ := hct
  have hdec := hcorrect keys hkeys _ c hc
  dsimp only at hdec
  refine ⟨by simp, ?_⟩
  simp only [List.dropLast_concat, sloppyDecrypt_append_singleton, hdec,
    EmbeddingLike.apply_eq_iff_eq, Option.some.injEq]
  cases bit
  · simpa using hne keys hkeys
  · simp

/-- **The sloppy scheme loses the 1CCA game with certainty** ([BonehShoup2023], Exercise 12.2,
p. 512). If `(keyGen n, encrypt n, decrypt n)` is correct and the messages `msg₀ n pk ≠ msg₁ n pk`
are admissible under every honest public key `pk`, then `sloppyAdversary encMsg msg₀ msg₁` has
1CCA advantage exactly `1` against `(keyGen, sloppyEncrypt encrypt, sloppyDecrypt decrypt)` at
`n`. -/
theorem advantage_cca2GameOn_sloppyAdversary {Msg : Type}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Msg}
    {msg₀ msg₁ : ℕ → List Bool → Msg} {n : ℕ}
    (hcorrect : (PKE.mk (keyGen n) (encrypt n) (decrypt n)).Correct)
    (hvalid : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      valid n keys.1 (msg₀ n keys.1) (msg₁ n keys.1) = true)
    (hne : ∀ keys ∈ (ProbComp.eval (keyGen n)).support, msg₀ n keys.1 ≠ msg₁ n keys.1) :
    Game.advantage
      (ProbComp.eval (cca2GameOn valid encMsg keyGen (sloppyEncrypt encrypt)
        (sloppyDecrypt decrypt) (sloppyAdversary encMsg msg₀ msg₁) false n))
      (ProbComp.eval (cca2GameOn valid encMsg keyGen (sloppyEncrypt encrypt)
        (sloppyDecrypt decrypt) (sloppyAdversary encMsg msg₀ msg₁) true n)) = 1 :=
  advantage_cca2GameOn_maulAdversary hvalid fun bit _ hkeys _ hct =>
    sloppy_conditions hcorrect hne bit hkeys hct

/-- **The sloppy scheme is not 1CCA secure** ([BonehShoup2023], Exercise 12.2, p. 512): if the
challenge messages `msg₀ msg₁` are computable in polynomial time and, at every parameter, the
scheme `(keyGen n, encrypt n, decrypt n)` is correct and `msg₀ n pk ≠ msg₁ n pk` are admissible
under every honest public key `pk`, then `(keyGen, sloppyEncrypt encrypt, sloppyDecrypt decrypt)`
fails `INDCCA2On valid encMsg encMsg`, by `sloppyAdversary`. -/
theorem not_indcca2On_sloppy {Msg : Type} {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Msg}
    {msg₀ msg₁ : ℕ → List Bool → Msg}
    (hmsg₀ : ComputableInPolyTime (fun ⟨n, pk⟩ => msg₀ n pk) (encPair encUnary encBits) encMsg)
    (hmsg₁ : ComputableInPolyTime (fun ⟨n, pk⟩ => msg₁ n pk) (encPair encUnary encBits) encMsg)
    (hcorrect : ∀ n, (PKE.mk (keyGen n) (encrypt n) (decrypt n)).Correct)
    (hvalid : ∀ n, ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      valid n keys.1 (msg₀ n keys.1) (msg₁ n keys.1) = true)
    (hne : ∀ n, ∀ keys ∈ (ProbComp.eval (keyGen n)).support, msg₀ n keys.1 ≠ msg₁ n keys.1) :
    ¬ INDCCA2On valid encMsg encMsg keyGen (sloppyEncrypt encrypt) (sloppyDecrypt decrypt) :=
  not_indcca2On_of_maulAdversary (maul := fun _ _ ct => ct.dropLast ++ [true])
    (target := fun n pk => encOption encMsg (some (msg₁ n pk))) hmsg₀ hmsg₁
    computableInPolyTime_setLastTrue (by fun_prop) hvalid fun n bit _ hkeys _ hct =>
      sloppy_conditions (hcorrect n) (hne n) bit hkeys hct

end Cslib.Crypto.Encryption
