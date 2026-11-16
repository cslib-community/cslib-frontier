/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.IVStream
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Probability.BitString
import CslibFrontier.Tactic.PolyTime

/-!
# Malleability of stream encryption under a random initial value

A ciphertext of `ivStreamEncrypt` is an `n`-bit initial value followed by the message XORed with
a keystream. XORing a mask `delta` at least as long as `msg` into the part after the initial value
(`ivStreamXorBody`) therefore gives a ciphertext in the support of the encryption of
`msg ⊕ delta`, whatever the keystream (`ivStreamXorBody_mem_support_ivStreamEncrypt`). On
whole-block messages, when the keystream from every `n`-bit initial value has `blocks * n` bits,
it decrypts to `msg ⊕ delta` (`ivStreamDecrypt_ivStreamXorBody`). The transformation needs
neither the key nor the keystream, and it is computable in polynomial time
(`computableInPolyTime_ivStreamXorBody`).

Boneh and Shoup exploit this malleability against randomized counter mode in Section 9.2.1
([BonehShoup2023], printed pp. 360–361): "define `ĉ` to be the same as `c` except that
`ĉ[1] := c[1] ⊕ u ⊕ v`", which is the mask `(u ⊕ v) ‖ 0`. In Section 9.10, Attack 3 (printed
p. 391), they state it as "given the encryption of `m`, an attacker can create a valid encryption
of `m ⊕ Δ` for any `Δ` of his choice." Counter mode (`ctrWordEncrypt`), output feedback mode
(`ofbWordEncrypt`) and the one-block cipher `prfCipher` all encrypt by `ivStreamEncrypt`. Since
`ctrWordEncrypt` and `ofbWordEncrypt` are not exposed, a `module` client states its hypotheses for
`ivStreamEncrypt (ctrWordKeystream family)` and `ivStreamEncrypt (ofbWordKeystream family)`. The
randomized CBC half of Section 9.2.1 is not covered.

## Main definitions

* `Cslib.Crypto.ivStreamXorBody`: XOR a mask into a ciphertext after its initial value.

## Main results

* `Cslib.Crypto.ivStreamXorBody_mem_support_ivStreamEncrypt`: the modified ciphertext is an
  encryption of the masked message, for a mask at least as long as the message.
* `Cslib.Crypto.ivStreamDecrypt_ivStreamXorBody`: what the modified ciphertext decrypts to.
* `Cslib.Crypto.computableInPolyTime_ivStreamXorBody`: efficiency of the transformation.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 9.2.1 (printed pp. 360–361) and Section 9.10, Attack 3 (printed pp. 390–391).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- XOR the mask `delta` into the part of the ciphertext `ct` after its first `n` bits, the
initial value of `ivStreamEncrypt` at parameter `n`. -/
@[expose]
def ivStreamXorBody (n : ℕ) (delta ct : List Bool) : List Bool :=
  ct.take n ++ List.zipWith xor (ct.drop n) delta

/-- `ivStreamXorBody` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_ivStreamXorBody {α : Type} {input : α ↪ List Bool}
    {n : α → ℕ} {delta ct : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hdelta : ComputableInPolyTime delta input encBits)
    (hct : ComputableInPolyTime ct input encBits) :
    ComputableInPolyTime (fun a => ivStreamXorBody (n a) (delta a) (ct a)) input encBits :=
  ComputableInPolyTime.bitsAppend (by fun_prop)
    (ComputableInPolyTime.bitsZipWithInput xor (by fun_prop) hdelta)

/-- **Malleability of stream encryption** ([BonehShoup2023], Section 9.2.1 and Section 9.10,
Attack 3): XORing a mask `delta` at least as long as `msg` into an encryption of `msg` after its
initial value gives an encryption of `msg ⊕ delta`, for every keystream. -/
theorem ivStreamXorBody_mem_support_ivStreamEncrypt
    {keystream : ℕ → List Bool → List Bool → ℕ → List Bool} {n : ℕ} {k msg delta ct : List Bool}
    (hdelta : msg.length ≤ delta.length)
    (hct : ct ∈ (ProbComp.eval (ivStreamEncrypt keystream n k msg)).support) :
    ivStreamXorBody n delta ct ∈
      (ProbComp.eval (ivStreamEncrypt keystream n k (List.zipWith xor msg delta))).support := by
  simp only [ivStreamEncrypt, ivModeEncrypt, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hct ⊢
  obtain ⟨iv, hiv, rfl⟩ := hct
  have hivLen : iv.length = n := BitString.length_of_mem_support_uniformList hiv
  refine ⟨iv, hiv, ?_⟩
  have hl : (List.zipWith xor msg delta).length = msg.length := by
    rw [List.length_zipWith, Nat.min_eq_left hdelta]
  rw [hl, ivStreamXorBody, ← hivLen, List.take_left, List.drop_left]
  simp only [List.zipWith_zipWith_left, List.zipWith_zipWith_right, Bool.xor_assoc]

/-- The modified ciphertext of `ivStreamXorBody_mem_support_ivStreamEncrypt` decrypts to
`msg ⊕ delta` when `msg` is a whole number of `n`-bit blocks and the keystream from every `n`-bit
initial value has `blocks * n` bits. -/
theorem ivStreamDecrypt_ivStreamXorBody
    {keystream : ℕ → List Bool → List Bool → ℕ → List Bool} {n : ℕ} {k msg delta ct : List Bool}
    (hkeystream : ∀ iv : List Bool, iv.length = n →
      (keystream n k iv (msg.length / n)).length = msg.length / n * n)
    (hmsg : msg.length % n = 0) (hdelta : msg.length ≤ delta.length)
    (hct : ct ∈ (ProbComp.eval (ivStreamEncrypt keystream n k msg)).support) :
    ivStreamDecrypt keystream n k (ivStreamXorBody n delta ct) =
      some (List.zipWith xor msg delta) := by
  have hl : (List.zipWith xor msg delta).length = msg.length := by
    rw [List.length_zipWith, Nat.min_eq_left hdelta]
  exact ivStreamDecrypt_ivStreamEncrypt (by rwa [hl]) (by rwa [hl])
    (ivStreamXorBody_mem_support_ivStreamEncrypt hdelta hct)

end Cslib.Crypto
