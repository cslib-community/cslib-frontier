/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Encoding
public import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Probability.BitString
import CslibFrontier.Tactic.PolyTime

/-!
# Encryption under a random initial value

A random-IV mode draws a uniform `n`-bit initial value `iv` and outputs `iv` followed by a body
computed from the key, `iv` and the message. `ivModeEncrypt body` is this envelope for a body
`body n k iv msg`; it is efficient whenever the body is computable in polynomial time
(`isPPTOn_ivModeEncrypt`).

Randomized counter mode ([BonehShoup2023], Section 5.4.2) and output feedback mode
(Exercise 5.15(b)) are the stream case: derive a keystream of whole `n`-bit blocks from the key
and `iv`, and XOR it with the message. They differ only in the keystream. `ivStreamEncrypt
keystream` and `ivStreamDecrypt keystream` are this construction for a keystream generator
`keystream n k iv blocks`; `ivStreamEncrypt keystream` is defined as `ivModeEncrypt` with the XOR
body.
Decryption accepts an `n`-bit initial value followed by whole blocks.

Decryption inverts encryption on whole-block messages whenever the keystream has `blocks * n` bits
(`ivStreamDecrypt_ivStreamEncrypt`). Both algorithms are efficient whenever the keystream generator
is computable in polynomial time (`isPPTOn_ivStreamEncrypt`,
`computableInPolyTime_ivStreamDecrypt`).

## Main definitions

* `Cslib.Crypto.ivModeEncrypt`, `Cslib.Crypto.ivModeDecrypt`: encryption and decryption envelopes
  under an `n`-bit initial value.
* `Cslib.Crypto.ivStreamEncrypt`, `Cslib.Crypto.ivStreamDecrypt`: stream encryption and
  decryption.

## Main results

* `Cslib.Crypto.ivModeDecrypt_ivModeEncrypt`,
  `Cslib.Crypto.ivStreamDecrypt_ivStreamEncrypt`: correctness.
* `Cslib.Crypto.isPPTOn_ivModeEncrypt`, `Cslib.Crypto.computableInPolyTime_ivModeDecrypt`,
  `Cslib.Crypto.isPPTOn_ivStreamEncrypt`,
  `Cslib.Crypto.computableInPolyTime_ivStreamDecrypt`: efficiency.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 5.4.2 (printed p. 189) and Exercise 5.15 (printed p. 212).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- Encryption under a random initial value with body `body`: draw a uniform `n`-bit `iv` and
output `iv` followed by `body n k iv msg`. -/
@[expose]
noncomputable def ivModeEncrypt (body : ℕ → List Bool → List Bool → List Bool → List Bool)
    (n : ℕ) (k msg : List Bool) : ProbComp (List Bool) := do
  let iv ← BitString.sampleList n
  return iv ++ body n k iv msg

/-- Decryption envelope for an `n`-bit initial value with body decryptor `decBody`: accept a
ciphertext of at least `n` bits whose body length is a multiple of `n`, and run `decBody` on
`(n, k, ct.take n, ct.drop n)`. -/
@[expose]
def ivModeDecrypt (decBody : ℕ → List Bool → List Bool → List Bool → List Bool) (n : ℕ)
    (k ct : List Bool) : Option (List Bool) :=
  if (decide (n ≤ ct.length) && ((ct.length - n) % n == 0)) = true then
    some (decBody n k (ct.take n) (ct.drop n))
  else
    none

/-- `ivModeDecrypt` inverts `ivModeEncrypt` on whole-block messages whenever `encBody` preserves
message length and `decBody` left-inverts `encBody` on every `n`-bit initial value. -/
theorem ivModeDecrypt_ivModeEncrypt
    {encBody decBody : ℕ → List Bool → List Bool → List Bool → List Bool}
    {n : ℕ} {k msg : List Bool}
    (hlen : ∀ iv : List Bool, iv.length = n → (encBody n k iv msg).length = msg.length)
    (hinv : ∀ iv : List Bool, iv.length = n → decBody n k iv (encBody n k iv msg) = msg)
    (hmsg : msg.length % n = 0) {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (ivModeEncrypt encBody n k msg)).support) :
    ivModeDecrypt decBody n k ct = some msg := by
  simp only [ivModeEncrypt, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hct
  obtain ⟨iv, hiv, rfl⟩ := hct
  have hivLen : iv.length = n := BitString.length_of_mem_support_uniformList hiv
  have hbodyLen : (encBody n k iv msg).length = msg.length := hlen iv hivLen
  have hctLen : (iv ++ encBody n k iv msg).length = n + msg.length := by
    rw [List.length_append, hivLen, hbodyLen]
  have hcond : (decide (n ≤ (iv ++ encBody n k iv msg).length) &&
      (((iv ++ encBody n k iv msg).length - n) % n == 0)) = true := by
    simp [hctLen, hmsg]
  simp only [ivModeDecrypt, hcond, ↓reduceIte, Option.some.injEq]
  rw [← hivLen, List.take_left, List.drop_left, hivLen]
  exact hinv iv hivLen

/-- Stream encryption under a random initial value: the random-IV mode `ivModeEncrypt` whose body
is the message XORed with the keystream `keystream n k iv (msg.length / n)`. -/
@[expose]
noncomputable def ivStreamEncrypt (keystream : ℕ → List Bool → List Bool → ℕ → List Bool)
    (n : ℕ) (k msg : List Bool) : ProbComp (List Bool) :=
  ivModeEncrypt (fun n k iv msg => List.zipWith xor (keystream n k iv (msg.length / n)) msg)
    n k msg

/-- Stream decryption: accept an `n`-bit initial value followed by whole blocks, and XOR the blocks
with the keystream from that initial value. -/
def ivStreamDecrypt (keystream : ℕ → List Bool → List Bool → ℕ → List Bool) (n : ℕ)
    (k ct : List Bool) : Option (List Bool) :=
  ivModeDecrypt (fun n k iv body => List.zipWith xor (keystream n k iv (body.length / n)) body)
    n k ct

/-- Decryption inverts encryption on whole-block messages when the keystream from every `n`-bit
initial value has `blocks * n` bits. -/
theorem ivStreamDecrypt_ivStreamEncrypt {keystream : ℕ → List Bool → List Bool → ℕ → List Bool}
    {n : ℕ} {k msg : List Bool}
    (hkeystream : ∀ iv : List Bool, iv.length = n →
      (keystream n k iv (msg.length / n)).length = msg.length / n * n)
    (hmsg : msg.length % n = 0) {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (ivStreamEncrypt keystream n k msg)).support) :
    ivStreamDecrypt keystream n k ct = some msg :=
  ivModeDecrypt_ivModeEncrypt
    (fun iv hiv => by
      have hks : (keystream n k iv (msg.length / n)).length = msg.length := by
        rw [hkeystream iv hiv, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmsg)]
      simp [hks])
    (fun iv hiv => by
      have hks : (keystream n k iv (msg.length / n)).length = msg.length := by
        rw [hkeystream iv hiv, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmsg)]
      have hzip :
          (List.zipWith xor (keystream n k iv (msg.length / n)) msg).length = msg.length := by
        simp [hks]
      rw [hzip, BitString.zipWith_xor_self_left _ _ hks])
    hmsg hct

/-- Decryption under an initial value is computable in polynomial time on `(n, k, ct)` when the
body decryptor is computable in polynomial time on `(n, k, iv, body)`. -/
theorem computableInPolyTime_ivModeDecrypt
    {decBody : ℕ → List Bool → List Bool → List Bool → List Bool}
    (hbody : ComputableInPolyTime
      (fun ((n, k, iv, body) : ℕ × List Bool × List Bool × List Bool) => decBody n k iv body)
      (encPair encUnary (encPair encBits (encPair encBits encBits))) encBits) :
    ComputableInPolyTime
      (fun ((n, k, ct) : ℕ × List Bool × List Bool) => ivModeDecrypt decBody n k ct)
      (encKeyedInput encBits) (encOption encBits) := by
  let EIn := encKeyedInput encBits
  have hcond : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        decide (p.1 ≤ p.2.2.length) && ((p.2.2.length - p.1) % p.1 == 0))
      EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hargs : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => (p.1, p.2.1, p.2.2.take p.1, p.2.2.drop p.1))
      EIn (encPair encUnary (encPair encBits (encPair encBits encBits))) := by
    dsimp only [EIn]; fun_prop
  exact ComputableInPolyTime.ite hcond
    ((ComputableInPolyTime.optionSome encBits).comp (hbody.comp hargs))
    (ComputableInPolyTime.const none)

/-- Encryption under a random initial value is uniformly strict PPT in `(n, k, msg)` when the body
is computable in polynomial time on `(n, k, iv, msg)`. -/
theorem isPPTOn_ivModeEncrypt {body : ℕ → List Bool → List Bool → List Bool → List Bool}
    (hbody : ComputableInPolyTime
      (fun ((n, k, iv, msg) : ℕ × List Bool × List Bool × List Bool) => body n k iv msg)
      (encPair encUnary (encPair encBits (encPair encBits encBits))) encBits) :
    IsPPTOn (encKeyedInput encBits) encBits
      (fun ((n, k, msg) : ℕ × List Bool × List Bool) => ivModeEncrypt body n k msg) := by
  let EIn := encPair (encKeyedInput encBits) encBits
  have hargs : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × List Bool => (p.1.1, p.1.2.1, p.2, p.1.2.2))
      EIn (encPair encUnary (encPair encBits (encPair encBits encBits))) := by
    dsimp only [EIn]; fun_prop
  have hpost : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × List Bool => p.2 ++ body p.1.1 p.1.2.1 p.2 p.1.2.2)
      EIn encBits :=
    ComputableInPolyTime.bitsAppend (by dsimp only [EIn]; fun_prop) (hbody.comp hargs)
  exact (ComputableInPolyTime.sampleList (ComputableInPolyTime.fst _ _)).bind_with hpost.isPPTOn

/-- Stream encryption is uniformly strict PPT in `(n, k, msg)` when the keystream generator is
computable in polynomial time on `(n, k, iv, blocks)`. -/
theorem isPPTOn_ivStreamEncrypt {keystream : ℕ → List Bool → List Bool → ℕ → List Bool}
    (hkeystream : ComputableInPolyTime
      (fun ((n, k, iv, blocks) : ℕ × List Bool × List Bool × ℕ) => keystream n k iv blocks)
      (encPair encUnary (encPair encBits (encPair encBits encUnary))) encBits) :
    IsPPTOn (encKeyedInput encBits) encBits
      (fun ((n, k, msg) : ℕ × List Bool × List Bool) => ivStreamEncrypt keystream n k msg) := by
  let EBody := encPair encUnary (encPair encBits (encPair encBits encBits))
  have hargs : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool =>
        (p.1, p.2.1, p.2.2.1, p.2.2.2.length / p.1))
      EBody (encPair encUnary (encPair encBits (encPair encBits encUnary))) := by
    dsimp only [EBody]; fun_prop
  exact isPPTOn_ivModeEncrypt
    (body := fun n k iv msg => List.zipWith xor (keystream n k iv (msg.length / n)) msg)
    (ComputableInPolyTime.bitsZipWithInput xor (hkeystream.comp hargs) (by fun_prop))

/-- Stream decryption is computable in polynomial time on `(n, k, ct)` when the keystream
generator is computable in polynomial time on `(n, k, iv, blocks)`. -/
theorem computableInPolyTime_ivStreamDecrypt
    {keystream : ℕ → List Bool → List Bool → ℕ → List Bool}
    (hkeystream : ComputableInPolyTime
      (fun ((n, k, iv, blocks) : ℕ × List Bool × List Bool × ℕ) => keystream n k iv blocks)
      (encPair encUnary (encPair encBits (encPair encBits encUnary))) encBits) :
    ComputableInPolyTime
      (fun ((n, k, ct) : ℕ × List Bool × List Bool) => ivStreamDecrypt keystream n k ct)
      (encKeyedInput encBits) (encOption encBits) := by
  let EBody := encPair encUnary (encPair encBits (encPair encBits encBits))
  have hargs : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool =>
        (p.1, p.2.1, p.2.2.1, p.2.2.2.length / p.1))
      EBody (encPair encUnary (encPair encBits (encPair encBits encUnary))) := by
    dsimp only [EBody]; fun_prop
  exact computableInPolyTime_ivModeDecrypt
    (decBody := fun n k iv body => List.zipWith xor (keystream n k iv (body.length / n)) body)
    (ComputableInPolyTime.bitsZipWithInput xor (hkeystream.comp hargs) (by fun_prop))

end Cslib.Crypto
