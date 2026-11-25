/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.ElGamal.KDF
public import CslibFrontier.Crypto.Computational.ElGamal.ProbComp
public import CslibFrontier.Crypto.Encoding
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PPT

/-!
# General-Cipher Hashed ElGamal ([BonehShoup2023], Section 11.5, Theorem 11.5)

This module generalizes Hashed ElGamal ([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1,
and Section 11.5.2, Theorem 11.5, pp. 448–451) from the one-time pad specialization in
`CslibFrontier/Crypto/Computational/ElGamal.lean` to an arbitrary semantically secure symmetric
cipher
$\mathcal{E}_s$.

* **Paraphrase of [BonehShoup2023], Section 11.5 (p. 445) and Remark 11.1 (p. 446):** over a cyclic
  group $G$ of prime order $q$ with generator $g$, a symmetric cipher $\mathcal{E}_s = (E_s, D_s)$
  over $(\mathcal{K}, \mathcal{M}, \mathcal{C})$, and a key-derivation hash function $H$, key
  generation samples $\alpha \leftarrow \mathbb{Z}_q$ and outputs $(pk = \alpha \cdot g, sk =
  \alpha)$. In the $\mathcal{E}'_{\mathrm{EG}}$ variant of Remark 11.1 (which derives $k$ from
  $w = \beta \cdot u$ alone), encryption of $m \in \mathcal{M}$ under $pk = u$ samples
  $\beta \leftarrow \mathbb{Z}_q$, sets $v = \beta \cdot g$, $w = \beta \cdot u$, $k = H(w)$,
  $c \leftarrow E_s(k, m)$, and outputs $(v, c)$; decryption of $(v, c)$ under $sk = \alpha$ sets
  $w = \alpha \cdot v$, $k = H(w)$, and outputs $D_s(k, c)$.
* **Paraphrase of [BonehShoup2023], Section 11.5.2, Theorem 11.5 and Equation (11.14)
  (pp. 449–451):** if DDH holds for $G$, $H$ is a secure KDF, and $\mathcal{E}_s$ is semantically
  secure, then Hashed ElGamal is semantically secure; for every CPA adversary $\mathcal{A}$ there
  exist elementary wrapper adversaries $\mathcal{B}_{\mathrm{ddh}}$, $\mathcal{B}_{\mathrm{kdf}}$,
  and $\mathcal{B}_s$ such that
  $\mathrm{SSadv}[\mathcal{A}, \mathcal{E}_{\mathrm{EG}}] \le
  2 \cdot \mathrm{DDHadv}[\mathcal{B}_{\mathrm{ddh}}, G] +
  2 \cdot \mathrm{KDFadv}[\mathcal{B}_{\mathrm{kdf}}, H] +
  \mathrm{SSadv}[\mathcal{B}_s, \mathcal{E}_s]$.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherDecrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeHashedElGamalCipherEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeHashedElGamalCipher`: algebraic and word-level Hashed
  ElGamal encryption and decryption with a general symmetric cipher
  ([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1).
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherCPAGameOn`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherCPAGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherRandomDDHGameOn`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherUniformKeyGameOn`: PMF-level IND-CPA
  experiments and hybrids for general-cipher Hashed ElGamal ([BonehShoup2023], Section 11.5.2,
  Theorem 11.5, pp. 449–451).
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToDDHHiddenBitDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToKDFDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToKDFHiddenBitDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToDEMAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.seededSetupProb`: per-bit and hidden-bit DDH and KDF
  reductions, symmetric-cipher (`DEMOneTimeKeyINDCPAOn` / `DEMOneTimeINDCPAOn`) reduction adversary,
  and executable seeded setup sampler for Theorem 11.5 ([BonehShoup2023], Section 11.5.2,
  pp. 449–451). The KDF reductions are typed `KDFDistinguisher`s, and each DDH reduction runs its
  KDF reduction on the key derived from the candidate shared element (`kdfToDDHDistinguisher`), so
  the random DDH game is the real KDF game (`ddhRandomGame_kdfToDDHDistinguisher`).

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherDecrypt_hashedElGamalCipherEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeHashedElGamalCipher_hashedElGamalCipherEncrypt`:
  decryption correctness for general-cipher Hashed ElGamal.

## Ideal-sampling steps

The security results of this module concern `hashedElGamalCipherCPAGameOn` and its hybrids, which
draw the key and challenge exponents exactly uniformly at the `PMF` level. They are steps toward
Theorem 11.5 for the strict-PPT scheme, not the cited result, and no theorem yet transfers them to
a native encryption sampler for a general cipher. The approximate sampling (`sampleExp`, adding
`4 / 2 ^ n`) below belongs to the symmetric-cipher reduction, not to the target game. For the
one-time pad, the native theorems are `DDH.kemINDCPA_hashedElGamalEncapsProb` and
`DDH.wordINDCPA_hybrid_hashedElGamal` in `CslibFrontier/Crypto/Computational/ElGamal/ProbComp.lean`.

* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_hashedElGamalCipherCPAGameOn_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_hashedElGamalCipherCPAGameOn_le_two_mul`,
  `PrimeOrderGroupFamily.advantage_hashedElGamalCipherUniformKeyGameOn_le_demKeyGameOn`,
  `PrimeOrderGroupFamily.advantage_hashedElGamalCipherCPAGameOn_le_demKeyGameOn`,
  `PrimeOrderGroupFamily.advantage_hashedElGamalCipherUniformKeyGameOn_le_demGameOn`,
  `PrimeOrderGroupFamily.advantage_hashedElGamalCipherCPAGameOn_le_demGameOn`:
  two-distinguisher and single hidden-bit distinguisher quantitative bounds after Theorem 11.5
  (Equation `(11.14)` of [BonehShoup2023], p. 449), and the symmetric-cipher reduction to
  standalone symmetric-cipher security at arbitrary (`Encryption.demKeyGameOn`) and normalized
  (`n`-bit, `Encryption.demGameOn`) key lengths.
* `PrimeOrderGroupFamily.negligible_hashedElGamalCipherUniformKeyGameOn_of_demOneTimeKeyINDCPAOn`,
  `DDH.negligible_hashedElGamalCipherCPAGameOn_ideal_of_demOneTimeKeyINDCPAOn`,
  `DDH.negligible_hashedElGamalCipherCPAGameOn_ideal_linearHashKDF_of_demOneTimeKeyINDCPAOn`,
  and their normalized `n`-bit-key specializations
  (`PrimeOrderGroupFamily.negligible_hashedElGamalCipherUniformKeyGameOn_of_demOneTimeINDCPAOn`,
  `PrimeOrderGroupFamily.DDH.negligible_hashedElGamalCipherCPAGameOn_ideal_of_demOneTimeINDCPAOn`,
  `PrimeOrderGroupFamily.DDH.negligible_hashedElGamalCipherCPAGameOn_ideal_linearHashKDF`):
  IND-CPA security of the ideal-sampling game `hashedElGamalCipherCPAGameOn` from `DDH`,
  `SecureKDF`, and `DEMOneTimeKeyINDCPAOn` (or `DEMOneTimeINDCPAOn`), plus the `linearHashKDF`
  instantiation at arbitrary and normalized key lengths, which replaces the `SecureKDF` hypothesis
  by a lower bound `qMin n` on the group order of every description in the support of the setup
  sampler, with `2 ^ outLen n / qMin n` (or `2 ^ n / qMin n`) negligible.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.5 (pp. 445–446, Remark 11.1) and Section 11.5.2
  (pp. 448–451, Attack Game 11.3, Definition 11.5, Theorem 11.5).
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Encryption Game
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### Algebraic and word-level general-cipher Hashed ElGamal ([BonehShoup2023], Section 11.5) -/

/-- Algebraic Hashed ElGamal encryption with a general deterministic symmetric cipher `encSym`
([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1): given key-derivation hash function
`H : F.Desc × List Bool → List Bool`, public key `u : F.Carrier d`, message `m : Msg`, and
randomness `β : ZMod (F.order d)`, derive `k = H (d, encode (β • u))` and output
`(β • g, encSym k m)`. -/
def hashedElGamalCipherEncrypt {Msg Cipher : Type} (H : F.Desc × List Bool → List Bool)
    (encSym : List Bool → Msg → Cipher) (d : F.Desc) (u : F.Carrier d) (m : Msg)
    (β : ZMod (F.order d)) : F.Carrier d × Cipher :=
  (β • F.generator d, encSym (H (d, F.encode d (β • u))) m)

/-- Under a genuine public key `u = α • g`, `hashedElGamalCipherEncrypt` derives the symmetric key
`H (d, encode ((α * β) • g))`. -/
theorem hashedElGamalCipherEncrypt_smul_generator {Msg Cipher : Type}
    (H : F.Desc × List Bool → List Bool) (encSym : List Bool → Msg → Cipher) (d : F.Desc)
    (α β : ZMod (F.order d)) (m : Msg) :
    F.hashedElGamalCipherEncrypt H encSym d (α • F.generator d) m β =
      (β • F.generator d, encSym (H (d, F.encode d ((α * β) • F.generator d))) m) := by
  simp only [hashedElGamalCipherEncrypt, smul_smul, mul_comm β α]

/-- Algebraic Hashed ElGamal decryption with a general symmetric cipher `decSym`
([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1): given secret key `α : ZMod (F.order d)`
and ciphertext `(v, c)`, derive `k = H (d, encode (α • v))` and recover `decSym k c`. -/
def hashedElGamalCipherDecrypt {Msg Cipher : Type} (H : F.Desc × List Bool → List Bool)
    (decSym : List Bool → Cipher → Msg) (d : F.Desc) (α : ZMod (F.order d))
    (ct : F.Carrier d × Cipher) : Msg :=
  decSym (H (d, F.encode d (α • ct.1))) ct.2

/-- **General-cipher Hashed ElGamal decryption correctness**: whenever `decSym k (encSym k m) = m`
holds for the derived key `k = H (d, encode ((α * β) • g))`, decrypting an encryption under
`u = α • g` with secret key `α` recovers `m`. -/
@[simp] theorem hashedElGamalCipherDecrypt_hashedElGamalCipherEncrypt {Msg Cipher : Type}
    (H : F.Desc × List Bool → List Bool) (encSym : List Bool → Msg → Cipher)
    (decSym : List Bool → Cipher → Msg) (d : F.Desc) (α β : ZMod (F.order d)) {m : Msg}
    (hdec :
      let k := H (d, F.encode d ((α * β) • F.generator d))
      decSym k (encSym k m) = m) :
    F.hashedElGamalCipherDecrypt H decSym d α
      (F.hashedElGamalCipherEncrypt H encSym d (α • F.generator d) m β) = m := by
  simp only [hashedElGamalCipherDecrypt, hashedElGamalCipherEncrypt_smul_generator, smul_smul]
  exact hdec

/-- `hashedElGamalEncrypt` is the one-time pad specialization of `hashedElGamalCipherEncrypt`. -/
theorem hashedElGamalEncrypt_eq_hashedElGamalCipherEncrypt (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (u : F.Carrier d) (m : List Bool) (β : ZMod (F.order d)) :
    F.hashedElGamalEncrypt H d u m β =
      F.hashedElGamalCipherEncrypt H
        (fun pad msg => Cslib.BitString.listXor pad.length [pad, msg]) d u m β :=
  rfl

/-- `hashedElGamalDecrypt` is the one-time pad specialization of `hashedElGamalCipherDecrypt`. -/
theorem hashedElGamalDecrypt_eq_hashedElGamalCipherDecrypt (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (α : ZMod (F.order d)) (ct : F.Carrier d × List Bool) :
    F.hashedElGamalDecrypt H d α ct =
      F.hashedElGamalCipherDecrypt H
        (fun pad c => Cslib.BitString.listXor pad.length [pad, c]) d α ct :=
  rfl

/-- Word-level Hashed ElGamal encryption with a general symmetric cipher `encSym`: given
`(d, encode u, m, b)`, derive `k = H (d, encode (b • u))` and compute
`(encode (b • g), encSym (k, m))`. -/
def encodeHashedElGamalCipherEncrypt {Msg : Type} (H : F.Desc × List Bool → List Bool)
    (encSym : List Bool × Msg → List Bool)
    (input : F.Desc × List Bool × Msg × ℕ) : List Bool × List Bool :=
  let k := H (input.1, F.smul (input.1, F.encRand input, F.encPk input))
  (F.smul (input.1, F.encRand input, F.encode input.1 (F.generator input.1)),
    encSym (k, F.encMsg input))

/-- `encodeHashedElGamalCipherEncrypt` evaluates `hashedElGamalCipherEncrypt` on encoded group
elements. -/
@[simp] theorem encodeHashedElGamalCipherEncrypt_encode {Msg : Type}
    (H : F.Desc × List Bool → List Bool) (encSym : List Bool × Msg → List Bool)
    (d : F.Desc) (u : F.Carrier d) (m : Msg) (b : ℕ) :
    F.encodeHashedElGamalCipherEncrypt H encSym (d, F.encode d u, m, b) =
      (F.encode d
        (F.hashedElGamalCipherEncrypt H (fun k msg => encSym (k, msg)) d u m
          (b : ZMod (F.order d))).1,
        (F.hashedElGamalCipherEncrypt H (fun k msg => encSym (k, msg)) d u m
          (b : ZMod (F.order d))).2) := by
  simp only [encodeHashedElGamalCipherEncrypt, hashedElGamalCipherEncrypt, F.smul_encode]

/-- Word-level general-cipher Hashed ElGamal encryption is computable in polynomial time whenever
`H` and `encSym` are. -/
theorem computableInPolyTime_encodeHashedElGamalCipherEncrypt {Msg : Type}
    {encMsg : Msg ↪ List Bool} {H : F.Desc × List Bool → List Bool}
    {encSym : List Bool × Msg → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hencSym : ComputableInPolyTime encSym (encPair encBits encMsg) encBits) :
    ComputableInPolyTime (F.encodeHashedElGamalCipherEncrypt H encSym)
      (encPair F.encDesc (encPair encBits (encPair encMsg encNat)))
      (encPair encBits encBits) := by
  unfold encodeHashedElGamalCipherEncrypt
  fun_prop

/-- Word-level Hashed ElGamal decryption with a general symmetric cipher `decSym`: given
`(d, a, encode v, c)`, derive `k = H (d, encode (a • v))` and compute `decSym (k, c)`. -/
def decodeHashedElGamalCipher {Msg : Type} (H : F.Desc × List Bool → List Bool)
    (decSym : List Bool × List Bool → Msg)
    (input : F.Desc × ℕ × List Bool × List Bool) : Msg :=
  decSym (H (input.1, F.smul (input.1, F.decSk input, F.decEph input)), F.decBody input)

/-- `decodeHashedElGamalCipher` computes `hashedElGamalCipherDecrypt` on encoded group elements. -/
@[simp] theorem decodeHashedElGamalCipher_encode {Msg : Type}
    (H : F.Desc × List Bool → List Bool) (decSym : List Bool × List Bool → Msg)
    (d : F.Desc) (a : ℕ) (v : F.Carrier d) (c : List Bool) :
    F.decodeHashedElGamalCipher H decSym (d, a, F.encode d v, c) =
      F.hashedElGamalCipherDecrypt H (fun k ct => decSym (k, ct)) d (a : ZMod (F.order d))
        (v, c) := by
  simp only [decodeHashedElGamalCipher, hashedElGamalCipherDecrypt, F.smul_encode]

/-- Word-level general-cipher Hashed ElGamal decryption of an honest encryption recovers `m`
whenever `decSym` inverts `encSym` on the derived key. -/
theorem decodeHashedElGamalCipher_hashedElGamalCipherEncrypt {Msg : Type}
    (H : F.Desc × List Bool → List Bool) (encSym : List Bool × Msg → List Bool)
    (decSym : List Bool × List Bool → Msg) (d : F.Desc) (a : ℕ) (β : ZMod (F.order d)) {m : Msg}
    (hdec :
      let k := H (d, F.encode d (((a : ZMod (F.order d)) * β) • F.generator d))
      decSym (k, encSym (k, m)) = m) :
    F.decodeHashedElGamalCipher H decSym (d, a,
      F.encode d
        (F.hashedElGamalCipherEncrypt H (fun k msg => encSym (k, msg)) d
          ((a : ZMod (F.order d)) • F.generator d) m β).1,
      (F.hashedElGamalCipherEncrypt H (fun k msg => encSym (k, msg)) d
        ((a : ZMod (F.order d)) • F.generator d) m β).2) = m := by
  rw [F.decodeHashedElGamalCipher_encode,
    F.hashedElGamalCipherDecrypt_hashedElGamalCipherEncrypt H _ _ d _ β hdec]

/-- Word-level general-cipher Hashed ElGamal decryption is computable in polynomial time whenever
`H` and `decSym` are. -/
theorem computableInPolyTime_decodeHashedElGamalCipher {Msg : Type}
    {encMsg : Msg ↪ List Bool} {H : F.Desc × List Bool → List Bool}
    {decSym : List Bool × List Bool → Msg}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hdecSym : ComputableInPolyTime decSym (encPair encBits encBits) encMsg) :
    ComputableInPolyTime (F.decodeHashedElGamalCipher H decSym)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encMsg := by
  unfold decodeHashedElGamalCipher
  fun_prop

/-! ### PMF-level general-cipher Hashed ElGamal IND-CPA games and Theorem 11.5 reductions -/

/-- The IND-CPA experiment for general-cipher Hashed ElGamal (`Game 0`, [BonehShoup2023],
Section 11.5, pp. 445–446, Remark 11.1, and Section 11.5.2, Theorem 11.5, Figure 11.4,
pp. 449–450) with challenge-pair admissibility predicate `valid`: draw `d ← setup n` and a uniform
secret key `α : ZMod (F.order d)`, and pass `pk = (d, encode (α • g))` to `adversary.choose`. If
`valid n pk m₀ m₁` holds, encrypt the selected message `m` under a fresh uniform exponent
`β : ZMod (F.order d)` and derived symmetric key `k = H (d, encode ((α * β) • g))` via
`c ← encryptSym n k m`, and pass `(encode (β • g), c)` to `adversary.guess`; otherwise output
`false`, in both experiments. -/
noncomputable def hashedElGamalCipherCPAGameOn {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  if valid n pk (Encryption.ChoiceOut.msg₀ choice) (Encryption.ChoiceOut.msg₁ choice) then
    let m := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
    let β ← PMF.uniformOfFintype (ZMod (F.order d))
    let k := H (d, F.encode d ((α * β) • F.generator d))
    let c ← ProbComp.eval (encryptSym n k m)
    let ct := encPair encBits encBits (F.encode d (β • F.generator d), c)
    ProbComp.eval (adversary.guess n choice.2 ct)
  else
    pure false

/-- Unrestricted general-cipher Hashed ElGamal IND-CPA experiment: `hashedElGamalCipherCPAGameOn`
with every challenge pair admissible. -/
noncomputable abbrev hashedElGamalCipherCPAGame {Msg : Type} (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game :=
  F.hashedElGamalCipherCPAGameOn (fun _ _ _ _ => true) setup H encryptSym adversary bit n

/-- `hashedElGamalCPAGame` is the specialization of `hashedElGamalCipherCPAGame` to one-time pad
XOR encryption. -/
theorem hashedElGamalCPAGame_eq_hashedElGamalCipherCPAGame (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : Encryption.WordAdversary) (bit : Bool)
    (n : ℕ) :
    F.hashedElGamalCPAGame setup H adversary bit n =
      F.hashedElGamalCipherCPAGame setup H
        (fun _ pad m => pure (Cslib.BitString.listXor pad.length [pad, m])) adversary bit n := by
  simp only [pmf_norm, hashedElGamalCPAGame, hashedElGamalCipherCPAGame,
    hashedElGamalCipherCPAGameOn, ↓reduceIte]

/-- **Game 1** for general-cipher Hashed ElGamal ([BonehShoup2023], Section 11.5.2, proof of
Theorem 11.5, p. 450): replace the Diffie–Hellman shared element `(α * β) • g` with an independent
uniform group element `γ • g`. -/
noncomputable def hashedElGamalCipherRandomDDHGameOn {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  if valid n pk (Encryption.ChoiceOut.msg₀ choice) (Encryption.ChoiceOut.msg₁ choice) then
    let m := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
    let β ← PMF.uniformOfFintype (ZMod (F.order d))
    let γ ← PMF.uniformOfFintype (ZMod (F.order d))
    let k := H (d, F.encode d (γ • F.generator d))
    let c ← ProbComp.eval (encryptSym n k m)
    let ct := encPair encBits encBits (F.encode d (β • F.generator d), c)
    ProbComp.eval (adversary.guess n choice.2 ct)
  else
    pure false

/-- Unrestricted Game 1 for general-cipher Hashed ElGamal. -/
noncomputable abbrev hashedElGamalCipherRandomDDHGame {Msg : Type} (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game :=
  F.hashedElGamalCipherRandomDDHGameOn (fun _ _ _ _ => true) setup H encryptSym adversary bit n

/-- **Game 2** for general-cipher Hashed ElGamal ([BonehShoup2023], Section 11.5.2, proof of
Theorem 11.5, p. 450): replace the derived key `H (d, encode (γ • g))` with an independent uniform
`keyLen n`-bit key `k ← Cslib.BitString.uniformList (keyLen n)`. -/
noncomputable def hashedElGamalCipherUniformKeyGameOn {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (keyLen : ℕ → ℕ) (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  if valid n pk (Encryption.ChoiceOut.msg₀ choice) (Encryption.ChoiceOut.msg₁ choice) then
    let m := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
    let β ← PMF.uniformOfFintype (ZMod (F.order d))
    let k ← Cslib.BitString.uniformList (keyLen n)
    let c ← ProbComp.eval (encryptSym n k m)
    let ct := encPair encBits encBits (F.encode d (β • F.generator d), c)
    ProbComp.eval (adversary.guess n choice.2 ct)
  else
    pure false

/-- Unrestricted Game 2 for general-cipher Hashed ElGamal. -/
noncomputable abbrev hashedElGamalCipherUniformKeyGame {Msg : Type} (setup : ℕ → PMF F.Desc)
    (keyLen : ℕ → ℕ) (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game :=
  F.hashedElGamalCipherUniformKeyGameOn (fun _ _ _ _ => true) setup keyLen encryptSym adversary
    bit n

private theorem hashedElGamalCipherGame_restrict_of_keyDist {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (keyDist : (d : F.Desc) → ZMod (F.order d) → ZMod (F.order d) → PMF (List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    let run (v : ℕ → List Bool → Msg → Msg → Bool) (A : Encryption.AdversaryOf Msg) : Game := do
      let d ← setup n
      let α ← PMF.uniformOfFintype (ZMod (F.order d))
      let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
      let choice ← ProbComp.eval (A.choose n pk)
      if v n pk (Encryption.ChoiceOut.msg₀ choice) (Encryption.ChoiceOut.msg₁ choice) then
        let m := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
        let β ← PMF.uniformOfFintype (ZMod (F.order d))
        let k ← keyDist d α β
        let c ← ProbComp.eval (encryptSym n k m)
        let ct := encPair encBits encBits (F.encode d (β • F.generator d), c)
        ProbComp.eval (A.guess n choice.2 ct)
      else
        pure false
    run (fun _ _ _ _ => true) (adversary.restrict valid) = run valid adversary := by
  simp only [Encryption.AdversaryOf.restrict, ↓reduceIte, pmf_norm]
  congr 1 with d : 1
  congr 1 with α : 1
  congr 1 with choice : 1
  cases valid n (encPair F.encDesc encBits (d, F.encode d (α • F.generator d)))
      choice.1.1 choice.1.2 <;>
    simp only [List.headD_cons, List.tail_cons, Bool.false_eq_true, ↓reduceIte,
      ProbComp.eval_pure, PMF.bind_const]

/-- Running the unrestricted `hashedElGamalCipherCPAGame` on `adversary.restrict valid` has the same
output distribution as running `hashedElGamalCipherCPAGameOn valid` on `adversary`. -/
theorem hashedElGamalCipherCPAGame_restrict {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.hashedElGamalCipherCPAGame setup H encryptSym (adversary.restrict valid) bit n =
      F.hashedElGamalCipherCPAGameOn valid setup H encryptSym adversary bit n := by
  simpa only [hashedElGamalCipherCPAGame, hashedElGamalCipherCPAGameOn, PMF.monad_bind_eq_bind,
    PMF.pure_bind] using
    F.hashedElGamalCipherGame_restrict_of_keyDist valid setup
      (fun d α β => PMF.pure (H (d, F.encode d ((α * β) • F.generator d))))
      encryptSym adversary bit n

/-- Running the unrestricted `hashedElGamalCipherRandomDDHGame` on `adversary.restrict valid` has
the same output distribution as running `hashedElGamalCipherRandomDDHGameOn valid` on
`adversary`. -/
theorem hashedElGamalCipherRandomDDHGame_restrict {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.hashedElGamalCipherRandomDDHGame setup H encryptSym (adversary.restrict valid) bit n =
      F.hashedElGamalCipherRandomDDHGameOn valid setup H encryptSym adversary bit n := by
  simpa only [hashedElGamalCipherRandomDDHGame, hashedElGamalCipherRandomDDHGameOn,
    PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def] using
    F.hashedElGamalCipherGame_restrict_of_keyDist valid setup
      (fun d _ _ => (PMF.uniformOfFintype (ZMod (F.order d))).map fun γ =>
        H (d, F.encode d (γ • F.generator d)))
      encryptSym adversary bit n

/-- Running the unrestricted `hashedElGamalCipherUniformKeyGame` on `adversary.restrict valid` has
the same output distribution as running `hashedElGamalCipherUniformKeyGameOn valid` on
`adversary`. -/
theorem hashedElGamalCipherUniformKeyGame_restrict {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (keyLen : ℕ → ℕ) (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym (adversary.restrict valid) bit n =
      F.hashedElGamalCipherUniformKeyGameOn valid setup keyLen encryptSym adversary bit n :=
  F.hashedElGamalCipherGame_restrict_of_keyDist valid setup
    (fun _ _ _ => Cslib.BitString.uniformList (keyLen n)) encryptSym adversary bit n

/-- Per-bit KDF distinguisher constructed from a general-cipher Hashed ElGamal IND-CPA adversary
([BonehShoup2023], Section 11.5.2, proof of Theorem 11.5, pp. 450–451): given `(d, u, v, k)`, pass
`pk = (d, encode u)` to `adversary.choose`, encrypt the selected message `m` under `k` via
`c ← encryptSym n k m`, and return `adversary.guess` on `(encode v, c)`. -/
def hashedElGamalCipherToKDFDistinguisher {Msg : Type}
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) : F.KDFDistinguisher :=
  fun n d u v key => do
    let pk := encPair F.encDesc encBits (d, F.encode d u)
    let choice ← adversary.choose n pk
    let m := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
    let c ← encryptSym n key m
    let ct := encPair encBits encBits (F.encode d v, c)
    adversary.guess n choice.2 ct

/-- Per-bit DDH distinguisher constructed from a general-cipher Hashed ElGamal IND-CPA adversary
([BonehShoup2023], Section 11.5.2, proof of Theorem 11.5, p. 450):
`hashedElGamalCipherToKDFDistinguisher` run with the key `H (d, encode w)` derived from the
candidate shared element `w`. -/
abbrev hashedElGamalCipherToDDHDistinguisher {Msg : Type} (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) : F.DDHDistinguisher :=
  F.kdfToDDHDistinguisher H (F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary bit)

/-- In the real DDH game, `hashedElGamalCipherToDDHDistinguisher` simulates
`hashedElGamalCipherCPAGame` exactly. -/
@[simp] theorem ddhRealGame_hashedElGamalCipherToDDHDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.ddhRealGame setup (F.hashedElGamalCipherToDDHDistinguisher H encryptSym adversary bit) n =
      F.hashedElGamalCipherCPAGame setup H encryptSym adversary bit n := by
  simp only [ddhRealGame, Game.withSetup, eval_ddhRealExperiment, kdfToDDHDistinguisher,
    hashedElGamalCipherToKDFDistinguisher, hashedElGamalCipherCPAGame,
    hashedElGamalCipherCPAGameOn, ↓reduceIte, ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  pmf_swap

/-- In the real KDF game, `hashedElGamalCipherToKDFDistinguisher` simulates Game 1
(`hashedElGamalCipherRandomDDHGame`) exactly. By `ddhRandomGame_kdfToDDHDistinguisher`, this is
also the random DDH game for `hashedElGamalCipherToDDHDistinguisher`. -/
@[simp] theorem kdfRealGame_hashedElGamalCipherToKDFDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.kdfRealGame setup H (F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary bit) n =
      F.hashedElGamalCipherRandomDDHGame setup H encryptSym adversary bit n := by
  simp only [kdfRealGame, hashedElGamalCipherToKDFDistinguisher, hashedElGamalCipherRandomDDHGame,
    hashedElGamalCipherRandomDDHGameOn, ↓reduceIte, ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  pmf_swap

/-- In the ideal KDF game, `hashedElGamalCipherToKDFDistinguisher` simulates
`hashedElGamalCipherUniformKeyGame` exactly. -/
@[simp] theorem kdfIdealGame_hashedElGamalCipherToKDFDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.kdfIdealGame setup keyLen
        (F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary bit) n =
      F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym adversary bit n := by
  simp only [kdfIdealGame, hashedElGamalCipherToKDFDistinguisher, hashedElGamalCipherUniformKeyGame,
    hashedElGamalCipherUniformKeyGameOn, ↓reduceIte, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind]
  pmf_swap

/-- `hashedElGamalCipherToKDFDistinguisher` is uniform strict PPT whenever `encryptSym` and
`adversary` are. The DDH reduction `hashedElGamalCipherToDDHDistinguisher` is then uniform strict
PPT by `isPPT_kdfToDDHDistinguisher`. -/
theorem isPPT_hashedElGamalCipherToKDFDistinguisher {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {adversary : Encryption.AdversaryOf Msg}
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, k, m⟩ => encryptSym n k m))
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) (bit : Bool) :
    (F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary bit).IsPPT := by
  unfold KDFDistinguisher.IsPPT
  ppt [hashedElGamalCipherToKDFDistinguisher]

/-- Single hidden-bit KDF distinguisher $\mathcal{B}_{\mathrm{kdf}}$ ([BonehShoup2023],
Section 11.5.2, proof of Theorem 11.5, Equation `(11.18)`, pp. 450–451): sample a uniform challenge
bit `bit ← ProbComp.uniform Bool`, run `hashedElGamalCipherToKDFDistinguisher` on `bit`, and output
`guess ^^ bit`. -/
noncomputable def hashedElGamalCipherToKDFHiddenBitDistinguisher {Msg : Type}
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) : F.KDFDistinguisher :=
  fun n d u v key => do
    let bit ← ProbComp.uniform Bool
    let guess ← F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary bit n d u v key
    return (guess ^^ bit)

/-- Single hidden-bit DDH distinguisher $\mathcal{B}_{\mathrm{ddh}}$ ([BonehShoup2023],
Section 11.5.2, proof of Theorem 11.5, Figure 11.4 and Equation `(11.17)`, p. 450):
`hashedElGamalCipherToKDFHiddenBitDistinguisher` run with the key `H (d, encode w)` derived from the
candidate shared element `w`. It samples a uniform challenge bit, runs
`hashedElGamalCipherToDDHDistinguisher` on it, and outputs `guess ^^ bit`. -/
noncomputable abbrev hashedElGamalCipherToDDHHiddenBitDistinguisher {Msg : Type}
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) : F.DDHDistinguisher :=
  F.kdfToDDHDistinguisher H (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym adversary)

/-- `hashedElGamalCipherToKDFHiddenBitDistinguisher` is uniform strict PPT whenever `encryptSym` and
`adversary` are. The DDH reduction `hashedElGamalCipherToDDHHiddenBitDistinguisher` is then
uniform strict PPT by `isPPT_kdfToDDHDistinguisher`. -/
theorem isPPT_hashedElGamalCipherToKDFHiddenBitDistinguisher {Msg : Type}
    {encMsg : Msg ↪ List Bool} {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {adversary : Encryption.AdversaryOf Msg}
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, k, m⟩ => encryptSym n k m))
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym adversary).IsPPT := by
  have hbit (b : Bool) := F.isPPT_hashedElGamalCipherToKDFDistinguisher hencryptSym hA b
  refine (isPPTOn_uniform_bool F.encKDFInput).bind_with
    (((IsPPTOn.cond (.snd F.encKDFInput encBool)
        ((hbit true).preprocess (.fst F.encKDFInput encBool))
        ((hbit false).preprocess (.fst F.encKDFInput encBool))).congr
      fun ⟨_, bit⟩ => by cases bit <;> rfl).bind_with (ComputableInPolyTime.isPPTOn (by fun_prop)))

/-- **Quantitative reduction of general-cipher Hashed ElGamal IND-CPA to DDH, `SecureKDF`, and
Game 2 via two per-bit distinguishers** ([BonehShoup2023], Section 11.5.2, Theorem 11.5,
pp. 449–451): the IND-CPA advantage in `hashedElGamalCipherCPAGameOn valid` is bounded by the sum of
the two per-bit DDH advantages, the two per-bit KDF advantages, and the Game 2 advantage in
`hashedElGamalCipherUniformKeyGameOn valid`. -/
theorem advantage_hashedElGamalCipherCPAGameOn_le {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ) :
    Game.advantage
      (F.hashedElGamalCipherCPAGameOn valid setup H encryptSym adversary false n)
      (F.hashedElGamalCipherCPAGameOn valid setup H encryptSym adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup
          (F.hashedElGamalCipherToDDHDistinguisher H encryptSym (adversary.restrict valid) false) n)
        (F.ddhRandomGame setup
          (F.hashedElGamalCipherToDDHDistinguisher H encryptSym
            (adversary.restrict valid) false) n) +
      Game.advantage
        (F.kdfRealGame setup H
          (F.hashedElGamalCipherToKDFDistinguisher encryptSym (adversary.restrict valid) false) n)
        (F.kdfIdealGame setup keyLen
          (F.hashedElGamalCipherToKDFDistinguisher encryptSym (adversary.restrict valid) false) n) +
      Game.advantage
        (F.hashedElGamalCipherUniformKeyGameOn valid setup keyLen encryptSym adversary false n)
        (F.hashedElGamalCipherUniformKeyGameOn valid setup keyLen encryptSym adversary true n) +
      Game.advantage
        (F.kdfRealGame setup H
          (F.hashedElGamalCipherToKDFDistinguisher encryptSym (adversary.restrict valid) true) n)
        (F.kdfIdealGame setup keyLen
          (F.hashedElGamalCipherToKDFDistinguisher encryptSym (adversary.restrict valid) true) n) +
      Game.advantage
        (F.ddhRealGame setup
          (F.hashedElGamalCipherToDDHDistinguisher H encryptSym (adversary.restrict valid) true) n)
        (F.ddhRandomGame setup
          (F.hashedElGamalCipherToDDHDistinguisher H encryptSym
            (adversary.restrict valid) true) n) := by
  let A' := adversary.restrict valid
  rw [← F.hashedElGamalCipherCPAGame_restrict valid setup H encryptSym adversary false n,
    ← F.hashedElGamalCipherCPAGame_restrict valid setup H encryptSym adversary true n,
    ← F.hashedElGamalCipherUniformKeyGame_restrict valid setup keyLen encryptSym adversary false n,
    ← F.hashedElGamalCipherUniformKeyGame_restrict valid setup keyLen encryptSym adversary true n]
  simp only [ddhRealGame_hashedElGamalCipherToDDHDistinguisher,
    ddhRandomGame_kdfToDDHDistinguisher,
    kdfRealGame_hashedElGamalCipherToKDFDistinguisher,
    kdfIdealGame_hashedElGamalCipherToKDFDistinguisher]
  game_trans
    [F.hashedElGamalCipherRandomDDHGame setup H encryptSym A' false n,
     F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym A' false n,
     F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym A' true n,
     F.hashedElGamalCipherRandomDDHGame setup H encryptSym A' true n]
    using [le_rfl, le_rfl, le_rfl, le_rfl, le_rfl]

private theorem ddhRealGame_hashedElGamalCipherToDDHHiddenBitDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ) :
    F.ddhRealGame setup
        (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym adversary) n =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (F.hashedElGamalCipherCPAGame setup H encryptSym adversary bit n).map
          (fun guess => guess ^^ bit) := by
  simp only [pmf_norm, ← ddhRealGame_hashedElGamalCipherToDDHDistinguisher, ddhRealGame,
    Game.withSetup, eval_ddhRealExperiment, kdfToDDHDistinguisher,
    hashedElGamalCipherToKDFHiddenBitDistinguisher, ProbComp.eval_uniform]
  pmf_swap

private theorem kdfRealGame_hashedElGamalCipherToKDFHiddenBitDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ) :
    F.kdfRealGame setup H
        (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym adversary) n =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (F.hashedElGamalCipherRandomDDHGame setup H encryptSym adversary bit n).map
          (fun guess => guess ^^ bit) := by
  simp only [pmf_norm, ← kdfRealGame_hashedElGamalCipherToKDFDistinguisher, kdfRealGame,
    hashedElGamalCipherToKDFHiddenBitDistinguisher, ProbComp.eval_uniform]
  pmf_swap

private theorem kdfIdealGame_hashedElGamalCipherToKDFHiddenBitDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ) :
    F.kdfIdealGame setup keyLen
        (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym adversary) n =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym adversary bit n).map
          (fun guess => guess ^^ bit) := by
  simp only [pmf_norm, ← kdfIdealGame_hashedElGamalCipherToKDFDistinguisher, kdfIdealGame,
    hashedElGamalCipherToKDFHiddenBitDistinguisher, ProbComp.eval_uniform]
  pmf_swap

/-- **Quantitative reduction of general-cipher Hashed ElGamal IND-CPA to DDH, `SecureKDF`, and
Game 2 via single hidden-bit distinguishers** ([BonehShoup2023], Section 11.5.2, Theorem 11.5,
Equation `(11.14)`, p. 449):
$$\mathsf{SSadv}[\mathcal{A}, \mathcal{E}_{\mathrm{EG}}] \le
  2 \cdot \mathsf{DDHadv}[\mathcal{B}_{\mathrm{ddh}}, \mathbb{G}] +
  2 \cdot \mathsf{KDFadv}[\mathcal{B}_{\mathrm{kdf}}, H] +
  \mathsf{Adv}_{\mathrm{Game\,2}}[\mathcal{A}].$$ -/
theorem advantage_hashedElGamalCipherCPAGameOn_le_two_mul {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ) :
    Game.advantage
      (F.hashedElGamalCipherCPAGameOn valid setup H encryptSym adversary false n)
      (F.hashedElGamalCipherCPAGameOn valid setup H encryptSym adversary true n) ≤
      2 * Game.advantage
        (F.ddhRealGame setup
          (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym
            (adversary.restrict valid)) n)
        (F.ddhRandomGame setup
          (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym
            (adversary.restrict valid)) n) +
      2 * Game.advantage
        (F.kdfRealGame setup H
          (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym
            (adversary.restrict valid)) n)
        (F.kdfIdealGame setup keyLen
          (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym
            (adversary.restrict valid)) n) +
      Game.advantage
        (F.hashedElGamalCipherUniformKeyGameOn valid setup keyLen encryptSym adversary false n)
        (F.hashedElGamalCipherUniformKeyGameOn valid setup keyLen encryptSym adversary true n) := by
  let A' := adversary.restrict valid
  rw [← F.hashedElGamalCipherCPAGame_restrict valid setup H encryptSym adversary false n,
    ← F.hashedElGamalCipherCPAGame_restrict valid setup H encryptSym adversary true n,
    ← F.hashedElGamalCipherUniformKeyGame_restrict valid setup keyLen encryptSym adversary false n,
    ← F.hashedElGamalCipherUniformKeyGame_restrict valid setup keyLen encryptSym adversary true n,
    F.ddhRealGame_hashedElGamalCipherToDDHHiddenBitDistinguisher,
    F.ddhRandomGame_kdfToDDHDistinguisher,
    F.kdfRealGame_hashedElGamalCipherToKDFHiddenBitDistinguisher,
    F.kdfIdealGame_hashedElGamalCipherToKDFHiddenBitDistinguisher]
  have h1 := advantage_le_two_mul_uniform_bool_xor
    (fun bit => F.hashedElGamalCipherCPAGame setup H encryptSym A' bit n)
    (fun bit => F.hashedElGamalCipherRandomDDHGame setup H encryptSym A' bit n)
  have h2 := advantage_le_two_mul_uniform_bool_xor
    (fun bit => F.hashedElGamalCipherRandomDDHGame setup H encryptSym A' bit n)
    (fun bit => F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym A' bit n)
  exact (h1.trans (add_le_add le_rfl h2)).trans_eq (by ring)

/-! ### Reduction from Game 2 (`hashedElGamalCipherUniformKeyGameOn`) to `DEMOneTimeINDCPAOn` -/

/-- One-time symmetric-cipher reduction adversary $\mathcal{B}_s$ for general-cipher Hashed ElGamal
([BonehShoup2023], Section 11.5.2, proof of Theorem 11.5, p. 451): given an efficiently samplable
group-description generator `setupProb : ℕ → ProbComp F.Desc` and a PKE adversary `adversary`,
`choose n _` samples `d ← setupProb n` and `a, b ← F.sampleExp n d`, sets
`u = encode (a • g)` and `v = encode (b • g)`, runs `choice ← adversary.choose n (d, u)`, and saves
`(v, choice.2)`; `guess n state ctSym` unpacks `(v, st)` and runs
`adversary.guess n st (v, ctSym)`. -/
noncomputable def hashedElGamalCipherToDEMAdversary {Msg : Type}
    (setupProb : ℕ → ProbComp F.Desc)
    (adversary : Encryption.AdversaryOf Msg) : Encryption.AdversaryOf Msg where
  choose n _ := do
    let d ← setupProb n
    let a ← F.sampleExp n d
    let b ← F.sampleExp n d
    let u := F.encodeElGamalPublicKey (d, a)
    let v := F.encodeElGamalPublicKey (d, b)
    let choice ← adversary.choose n (encPair F.encDesc encBits (d, u))
    return (choice.1, encPair encBits encBits (v, choice.2))
  guess n state ctSym :=
    adversary.guess n (dropFrame state)
      (encPair encBits encBits (unframe state, ctSym))

/-- `hashedElGamalCipherToDEMAdversary setupProb adversary` is an admissible uniform strict PPT
`Encryption.AdversaryOf Msg` whenever `setupProb` and `adversary` are. -/
theorem isPPT_hashedElGamalCipherToDEMAdversary {Msg : Type} {encMsg : Msg ↪ List Bool}
    {setupProb : ℕ → ProbComp F.Desc}
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Encryption.AdversaryOf.IsPPT encMsg
      (F.hashedElGamalCipherToDEMAdversary setupProb adversary) := by
  have := F.computableInPolyTime_encodeElGamalPublicKey
  exact ⟨by ppt [hashedElGamalCipherToDEMAdversary],
    hA.guess.preprocess (input := encGuessInput)
      (prepare := fun x => (x.1, dropFrame x.2.1, encPair encBits encBits (unframe x.2.1, x.2.2)))
      (by fun_prop)⟩

/-- For each bit `bit : Bool` and any key-length function `keyLen : ℕ → ℕ`, the Game 2 distribution
`hashedElGamalCipherUniformKeyGameOn` over `fun m => ProbComp.eval (setupProb m)` is within
`2 / 2 ^ n` in `Game.advantage` of the standalone one-time symmetric experiment
`Encryption.demKeyGameOn` on the wrapper adversary
`hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)`
(two approximate exponent draws via `sampleExp`, each within `1 / 2 ^ n` of uniform). -/
theorem advantage_hashedElGamalCipherUniformKeyGameOn_demKeyGameOn_le {Msg : Type}
    (valid validSym : ℕ → List Bool → Msg → Msg → Bool)
    (setupProb : ℕ → ProbComp F.Desc) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ)
    (hvalid_imp : ∀ d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true) :
    Game.advantage
      (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
        keyLen encryptSym adversary bit n)
      (ProbComp.eval
        (Encryption.demKeyGameOn validSym keyLen encryptSym
          (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) bit n)) ≤
      2 / 2 ^ n := by
  let k (d : F.Desc) (α β : ZMod (F.order d)) : Game :=
    let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
    (ProbComp.eval (adversary.choose n pk)).bind fun choice =>
      if valid n pk choice.1.1 choice.1.2 then
        (Cslib.BitString.uniformList (keyLen n)).bind fun key =>
          (ProbComp.eval (encryptSym n key (if bit then choice.1.2 else choice.1.1))).bind fun c =>
            ProbComp.eval (adversary.guess n choice.2
              (encPair encBits encBits (F.encode d (β • F.generator d), c)))
      else
        PMF.pure false
  have hgame2 :
      F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
        keyLen encryptSym adversary bit n =
      (ProbComp.eval (setupProb n)).bind fun d =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β => k d α β := by
    simp only [hashedElGamalCipherUniformKeyGameOn, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, k]
    pmf_swap with d α choice
    split_ifs <;> simp only [PMF.bind_const]
  have hdem :
      ProbComp.eval
        (Encryption.demKeyGameOn validSym keyLen encryptSym
          (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) bit n) =
      (ProbComp.eval (setupProb n)).bind fun d =>
        (ProbComp.eval (F.sampleExp n d)).bind fun a =>
          (ProbComp.eval (F.sampleExp n d)).bind fun b =>
            k d (a : ZMod (F.order d)) (b : ZMod (F.order d)) := by
    simp only [pmf_norm, Encryption.demKeyGameOn, hashedElGamalCipherToDEMAdversary,
      Encryption.AdversaryOf.restrict, Cslib.BitString.eval_sampleList, apply_ite ProbComp.eval,
      encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append, List.headD_cons,
      List.tail_cons, encodeElGamalPublicKey_eq_encode, k]
    pmf_swap with d a b choice
    by_cases hv :
        valid n (encPair F.encDesc encBits (d, F.encode d ((a : ZMod (F.order d)) • F.generator d)))
          choice.1.1 choice.1.2 = true
    · have hvs := hvalid_imp d _ choice.1.1 choice.1.2 hv
      simp only [encPair_apply, encBits_apply] at hv
      simp only [hv, hvs, ↓reduceIte]
    · simp only [Bool.not_eq_true, encPair_apply, encBits_apply] at hv
      split_ifs <;> simp only [hv, Bool.false_eq_true, ↓reduceIte, PMF.bind_const]
  rw [hgame2, hdem]
  peel_binds d
  rw [Game.advantage_comm]
  exact F.advantage_bind_sampleExp_pair_le n d (k d)

/-- For each bit `bit : Bool`, the Game 2 distribution `hashedElGamalCipherUniformKeyGameOn` over
`fun m => ProbComp.eval (setupProb m)` with `keyLen n = n` is within `2 / 2 ^ n` in
`Game.advantage` of the standalone one-time symmetric experiment `Encryption.demGameOn` on
`hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)` (two approximate exponent
draws via `sampleExp`, each within `1 / 2 ^ n` of uniform). -/
theorem advantage_hashedElGamalCipherUniformKeyGameOn_demGameOn_le {Msg : Type}
    (valid validSym : ℕ → List Bool → Msg → Msg → Bool)
    (setupProb : ℕ → ProbComp F.Desc) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ)
    (hkeyLen : keyLen n = n)
    (hvalid_imp : ∀ d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true) :
    Game.advantage
      (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
        keyLen encryptSym adversary bit n)
      (ProbComp.eval
        (Encryption.demGameOn validSym encryptSym
          (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) bit n)) ≤
      2 / 2 ^ n := by
  rw [← Encryption.demKeyGameOn_eq_demGameOn_of_eq validSym keyLen encryptSym _ bit hkeyLen]
  exact F.advantage_hashedElGamalCipherUniformKeyGameOn_demKeyGameOn_le
    valid validSym setupProb keyLen encryptSym adversary bit n hvalid_imp

/-- **Quantitative bridge from Game 2 (`hashedElGamalCipherUniformKeyGameOn`) to standalone
symmetric-cipher security at arbitrary key length (`Encryption.demKeyGameOn`)**: for any
`keyLen : ℕ → ℕ`, the Game 2 advantage is bounded by the `Encryption.demKeyGameOn` advantage of
`hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)` plus `4 / 2 ^ n`. -/
theorem advantage_hashedElGamalCipherUniformKeyGameOn_le_demKeyGameOn {Msg : Type}
    (valid validSym : ℕ → List Bool → Msg → Msg → Bool)
    (setupProb : ℕ → ProbComp F.Desc) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
    (hvalid_imp : ∀ d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true) :
    Game.advantage
      (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
        keyLen encryptSym adversary false n)
      (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
        keyLen encryptSym adversary true n) ≤
      Encryption.advantage (Encryption.demKeyGameOn validSym keyLen encryptSym
        (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid))) n +
      4 / 2 ^ n := by
  have hf := F.advantage_hashedElGamalCipherUniformKeyGameOn_demKeyGameOn_le
    valid validSym setupProb keyLen encryptSym adversary false n hvalid_imp
  have ht := F.advantage_hashedElGamalCipherUniformKeyGameOn_demKeyGameOn_le
    valid validSym setupProb keyLen encryptSym adversary true n hvalid_imp
  rw [Encryption.advantage]
  game_trans
    [ProbComp.eval
       (Encryption.demKeyGameOn validSym keyLen encryptSym
         (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) false n),
     ProbComp.eval
       (Encryption.demKeyGameOn validSym keyLen encryptSym
         (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) true n)]
    using [hf, le_rfl, ht]

/-- **Quantitative bridge from Game 2 (`hashedElGamalCipherUniformKeyGameOn`) to standalone
symmetric-cipher security (`Encryption.demGameOn`)**: the Game 2 advantage is bounded by the
`Encryption.demGameOn` advantage of
`hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)` plus `4 / 2 ^ n`. -/
theorem advantage_hashedElGamalCipherUniformKeyGameOn_le_demGameOn {Msg : Type}
    (valid validSym : ℕ → List Bool → Msg → Msg → Bool)
    (setupProb : ℕ → ProbComp F.Desc) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
    (hkeyLen : keyLen n = n)
    (hvalid_imp : ∀ d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true) :
    Game.advantage
      (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
        keyLen encryptSym adversary false n)
      (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
        keyLen encryptSym adversary true n) ≤
      Encryption.advantage (Encryption.demGameOn validSym encryptSym
        (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid))) n +
      4 / 2 ^ n := by
  rw [Encryption.advantage,
    ← Encryption.demKeyGameOn_eq_demGameOn_of_eq validSym keyLen encryptSym _ false hkeyLen,
    ← Encryption.demKeyGameOn_eq_demGameOn_of_eq validSym keyLen encryptSym _ true hkeyLen]
  exact F.advantage_hashedElGamalCipherUniformKeyGameOn_le_demKeyGameOn
    valid validSym setupProb keyLen encryptSym adversary n hvalid_imp

/-- **Native approximate-sampling version of Equation `(11.14)` for Theorem 11.5 via DDH,
`SecureKDF`, and standalone symmetric-cipher security at arbitrary key length
(`Encryption.demKeyGameOn`)** ([BonehShoup2023], Section 11.5.2, Theorem 11.5, Equation `(11.14)`,
p. 449): combining the exact PMF-level Equation `(11.14)` bound
`advantage_hashedElGamalCipherCPAGameOn_le_two_mul` with the `sampleExp` Game 2 bridge
`advantage_hashedElGamalCipherUniformKeyGameOn_le_demKeyGameOn` adds `4 / 2 ^ n` for the two
approximate exponent draws per branch:
$$\mathsf{SSadv}[\mathcal{A}, \mathcal{E}_{\mathrm{EG}}] \le
  2 \cdot \mathsf{DDHadv}[\mathcal{B}_{\mathrm{ddh}}, \mathbb{G}] +
  2 \cdot \mathsf{KDFadv}[\mathcal{B}_{\mathrm{kdf}}, H] +
  \mathsf{SSadv}[\mathcal{B}_s, \mathcal{E}_s] + \frac{4}{2^n}.$$ -/
theorem advantage_hashedElGamalCipherCPAGameOn_le_demKeyGameOn {Msg : Type}
    (valid validSym : ℕ → List Bool → Msg → Msg → Bool)
    (setupProb : ℕ → ProbComp F.Desc) (H : F.Desc × List Bool → List Bool) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
    (hvalid_imp : ∀ d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true) :
    Game.advantage
      (F.hashedElGamalCipherCPAGameOn valid (fun m => ProbComp.eval (setupProb m))
        H encryptSym adversary false n)
      (F.hashedElGamalCipherCPAGameOn valid (fun m => ProbComp.eval (setupProb m))
        H encryptSym adversary true n) ≤
      2 * Game.advantage
        (F.ddhRealGame (fun m => ProbComp.eval (setupProb m))
          (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym
            (adversary.restrict valid)) n)
        (F.ddhRandomGame (fun m => ProbComp.eval (setupProb m))
          (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym
            (adversary.restrict valid)) n) +
      2 * Game.advantage
        (F.kdfRealGame (fun m => ProbComp.eval (setupProb m)) H
          (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym
            (adversary.restrict valid)) n)
        (F.kdfIdealGame (fun m => ProbComp.eval (setupProb m)) keyLen
          (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym
            (adversary.restrict valid)) n) +
      Encryption.advantage (Encryption.demKeyGameOn validSym keyLen encryptSym
        (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid))) n +
      4 / 2 ^ n := by
  have h1 := F.advantage_hashedElGamalCipherCPAGameOn_le_two_mul
    valid (fun m => ProbComp.eval (setupProb m)) H keyLen encryptSym adversary n
  have h2 := F.advantage_hashedElGamalCipherUniformKeyGameOn_le_demKeyGameOn
    valid validSym setupProb keyLen encryptSym adversary n hvalid_imp
  exact (h1.trans (add_le_add le_rfl h2)).trans_eq (by ring)

/-- **Native approximate-sampling version of Equation `(11.14)` for Theorem 11.5 via DDH,
`SecureKDF`, and standalone symmetric-cipher security (`Encryption.demGameOn`)** ([BonehShoup2023],
Section 11.5.2, Theorem 11.5, Equation `(11.14)`, p. 449): combining the exact PMF-level Equation
`(11.14)` bound `advantage_hashedElGamalCipherCPAGameOn_le_two_mul` with the `sampleExp`
Game 2 bridge `advantage_hashedElGamalCipherUniformKeyGameOn_le_demGameOn` adds `4 / 2 ^ n` for the
two approximate exponent draws per branch:
$$\mathsf{SSadv}[\mathcal{A}, \mathcal{E}_{\mathrm{EG}}] \le
  2 \cdot \mathsf{DDHadv}[\mathcal{B}_{\mathrm{ddh}}, \mathbb{G}] +
  2 \cdot \mathsf{KDFadv}[\mathcal{B}_{\mathrm{kdf}}, H] +
  \mathsf{SSadv}[\mathcal{B}_s, \mathcal{E}_s] + \frac{4}{2^n}.$$ -/
theorem advantage_hashedElGamalCipherCPAGameOn_le_demGameOn {Msg : Type}
    (valid validSym : ℕ → List Bool → Msg → Msg → Bool)
    (setupProb : ℕ → ProbComp F.Desc) (H : F.Desc × List Bool → List Bool) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
    (hkeyLen : keyLen n = n)
    (hvalid_imp : ∀ d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true) :
    Game.advantage
      (F.hashedElGamalCipherCPAGameOn valid (fun m => ProbComp.eval (setupProb m))
        H encryptSym adversary false n)
      (F.hashedElGamalCipherCPAGameOn valid (fun m => ProbComp.eval (setupProb m))
        H encryptSym adversary true n) ≤
      2 * Game.advantage
        (F.ddhRealGame (fun m => ProbComp.eval (setupProb m))
          (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym
            (adversary.restrict valid)) n)
        (F.ddhRandomGame (fun m => ProbComp.eval (setupProb m))
          (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym
            (adversary.restrict valid)) n) +
      2 * Game.advantage
        (F.kdfRealGame (fun m => ProbComp.eval (setupProb m)) H
          (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym
            (adversary.restrict valid)) n)
        (F.kdfIdealGame (fun m => ProbComp.eval (setupProb m)) keyLen
          (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym
            (adversary.restrict valid)) n) +
      Encryption.advantage (Encryption.demGameOn validSym encryptSym
        (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid))) n +
      4 / 2 ^ n := by
  rw [Encryption.advantage,
    ← Encryption.demKeyGameOn_eq_demGameOn_of_eq validSym keyLen encryptSym _ false hkeyLen,
    ← Encryption.demKeyGameOn_eq_demGameOn_of_eq validSym keyLen encryptSym _ true hkeyLen]
  exact F.advantage_hashedElGamalCipherCPAGameOn_le_demKeyGameOn
    valid validSym setupProb H keyLen encryptSym adversary n hvalid_imp

/-- One-time symmetric IND-CPA security at arbitrary key length (`Encryption.DEMOneTimeKeyINDCPAOn`)
implies negligibility of the Game 2 advantage (`hashedElGamalCipherUniformKeyGameOn`) whenever the
setup law is efficiently samplable (`setupProb : ℕ → ProbComp F.Desc`) and `valid` implies
`validSym`. -/
theorem negligible_hashedElGamalCipherUniformKeyGameOn_of_demOneTimeKeyINDCPAOn {Msg : Type}
    {encMsg : Msg ↪ List Bool}
    {valid validSym : ℕ → List Bool → Msg → Msg → Bool}
    {setupProb : ℕ → ProbComp F.Desc} {keyLen : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDEM : Encryption.DEMOneTimeKeyINDCPAOn validSym encMsg keyLen encryptSym)
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
    (hvalid_imp : ∀ n d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true)
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Negligible fun n =>
      Game.advantage
        (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
          keyLen encryptSym adversary false n)
        (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
          keyLen encryptSym adversary true n) := by
  have hA' := hA.restrict hvalid
  have hdem := hDEM (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid))
    (F.isPPT_hashedElGamalCipherToDEMAdversary hsetup hA')
  negligible using fun n =>
    F.advantage_hashedElGamalCipherUniformKeyGameOn_le_demKeyGameOn
      valid validSym setupProb keyLen encryptSym adversary n (hvalid_imp n)

/-- One-time symmetric IND-CPA security (`Encryption.DEMOneTimeINDCPAOn`) implies negligibility of
the Game 2 advantage (`hashedElGamalCipherUniformKeyGameOn`) whenever the setup law is efficiently
samplable (`setupProb : ℕ → ProbComp F.Desc`), `keyLen n = n`, and `valid` implies `validSym`. -/
theorem negligible_hashedElGamalCipherUniformKeyGameOn_of_demOneTimeINDCPAOn {Msg : Type}
    {encMsg : Msg ↪ List Bool}
    {valid validSym : ℕ → List Bool → Msg → Msg → Bool}
    {setupProb : ℕ → ProbComp F.Desc} {keyLen : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDEM : Encryption.DEMOneTimeINDCPAOn validSym encMsg encryptSym)
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hkeyLen : ∀ n, keyLen n = n)
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hvalid_imp : ∀ n d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true)
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Negligible fun n =>
      Game.advantage
        (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
          keyLen encryptSym adversary false n)
        (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
          keyLen encryptSym adversary true n) :=
  F.negligible_hashedElGamalCipherUniformKeyGameOn_of_demOneTimeKeyINDCPAOn
    (hDEM.demOneTimeKeyINDCPAOn hkeyLen) hsetup hvalid hvalid_imp hA

/-- Ideal-sampling step, not the cited result: IND-CPA security of the general-cipher Hashed
ElGamal game `hashedElGamalCipherCPAGameOn`, whose key and challenge exponents are drawn exactly
uniformly at the `PMF` level, from DDH, `SecureKDF`, and `Encryption.DEMOneTimeKeyINDCPAOn` at
arbitrary key length (after [BonehShoup2023], Section 11.5.2, Theorem 11.5, pp. 449–451). For any
efficiently samplable setup `setupProb : ℕ → ProbComp F.Desc`
(`setup n = ProbComp.eval (setupProb n)`), key-length function `keyLen : ℕ → ℕ`, and admissibility
predicate `valid` implying `validSym`, if `F.DDH`, `F.SecureKDF`, and
`Encryption.DEMOneTimeKeyINDCPAOn validSym encMsg keyLen encryptSym` hold, then every uniform strict
PPT adversary has negligible advantage in `hashedElGamalCipherCPAGameOn valid`. -/
theorem DDH.negligible_hashedElGamalCipherCPAGameOn_ideal_of_demOneTimeKeyINDCPAOn
    {F : PrimeOrderGroupFamily} {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid validSym : ℕ → List Bool → Msg → Msg → Bool}
    {setupProb : ℕ → ProbComp F.Desc} {H : F.Desc × List Bool → List Bool} {keyLen : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => ProbComp.eval (setupProb n)))
    (hKDF : F.SecureKDF (fun n => ProbComp.eval (setupProb n)) H keyLen)
    (hDEM : Encryption.DEMOneTimeKeyINDCPAOn validSym encMsg keyLen encryptSym)
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
    (hvalid_imp : ∀ n d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Negligible fun n =>
      Game.advantage
        (F.hashedElGamalCipherCPAGameOn valid (fun n => ProbComp.eval (setupProb n))
          H encryptSym adversary false n)
        (F.hashedElGamalCipherCPAGameOn valid (fun n => ProbComp.eval (setupProb n))
          H encryptSym adversary true n) := by
  have hA' := hA.restrict hvalid
  have hkdfPPT := F.isPPT_hashedElGamalCipherToKDFHiddenBitDistinguisher hencryptSym hA'
  have hddh := hDDH _ (F.isPPT_kdfToDDHDistinguisher hH hkdfPPT)
  have hkdf := hKDF _ hkdfPPT
  have hsym := F.negligible_hashedElGamalCipherUniformKeyGameOn_of_demOneTimeKeyINDCPAOn
    hDEM hsetup hvalid hvalid_imp hA
  negligible using
    F.advantage_hashedElGamalCipherCPAGameOn_le_two_mul valid
      (fun n => ProbComp.eval (setupProb n)) H keyLen encryptSym adversary

/-- Ideal-sampling step, not the cited result: IND-CPA security of the general-cipher Hashed
ElGamal game `hashedElGamalCipherCPAGameOn`, whose key and challenge exponents are drawn exactly
uniformly at the `PMF` level, from DDH, `SecureKDF`, and `Encryption.DEMOneTimeINDCPAOn` (after
[BonehShoup2023], Section 11.5.2, Theorem 11.5, pp. 449–451). For any efficiently samplable setup
`setupProb : ℕ → ProbComp F.Desc` (`setup n = ProbComp.eval (setupProb n)`), `keyLen n = n`, and
admissibility predicate `valid` implying `validSym`, if `F.DDH`, `F.SecureKDF`, and
`Encryption.DEMOneTimeINDCPAOn validSym encMsg encryptSym` hold, then every uniform strict PPT
adversary has negligible advantage in `hashedElGamalCipherCPAGameOn valid`. -/
theorem DDH.negligible_hashedElGamalCipherCPAGameOn_ideal_of_demOneTimeINDCPAOn
    {F : PrimeOrderGroupFamily} {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid validSym : ℕ → List Bool → Msg → Msg → Bool}
    {setupProb : ℕ → ProbComp F.Desc} {H : F.Desc × List Bool → List Bool} {keyLen : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => ProbComp.eval (setupProb n)))
    (hKDF : F.SecureKDF (fun n => ProbComp.eval (setupProb n)) H keyLen)
    (hDEM : Encryption.DEMOneTimeINDCPAOn validSym encMsg encryptSym)
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hkeyLen : ∀ n, keyLen n = n)
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hvalid_imp : ∀ n d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, k, m⟩ => encryptSym n k m))
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Negligible fun n =>
      Game.advantage
        (F.hashedElGamalCipherCPAGameOn valid (fun n => ProbComp.eval (setupProb n))
          H encryptSym adversary false n)
        (F.hashedElGamalCipherCPAGameOn valid (fun n => ProbComp.eval (setupProb n))
          H encryptSym adversary true n) :=
  hDDH.negligible_hashedElGamalCipherCPAGameOn_ideal_of_demOneTimeKeyINDCPAOn
    hKDF (hDEM.demOneTimeKeyINDCPAOn hkeyLen) hsetup hvalid hvalid_imp hH hencryptSym hA

/-- Executable `ProbComp` sampler for `F.seededSetup`: sample `d ← setupProb n`, then conditional on
`d`, sample a uniform seed `s ← Cslib.BitString.sampleList (seedLen n d)` and output `(d, s)`. -/
noncomputable def seededSetupProb (setupProb : ℕ → ProbComp F.Desc)
    (seedLen : ℕ → F.Desc → ℕ) (n : ℕ) : ProbComp F.withSeed.Desc := do
  let d ← setupProb n
  let s ← Cslib.BitString.sampleList (seedLen n d)
  return (d, s)

/-- `ProbComp.eval (F.seededSetupProb setupProb seedLen n)` equals
`F.seededSetup (fun m => ProbComp.eval (setupProb m)) seedLen n`. -/
@[simp] theorem eval_seededSetupProb (setupProb : ℕ → ProbComp F.Desc)
    (seedLen : ℕ → F.Desc → ℕ) (n : ℕ) :
    ProbComp.eval (F.seededSetupProb setupProb seedLen n) =
      F.seededSetup (fun m => ProbComp.eval (setupProb m)) seedLen n := by
  simp only [pmf_norm, seededSetupProb, seededSetup, Cslib.BitString.eval_sampleList]

/-- `F.seededSetupProb setupProb seedLen` is uniform strict PPT whenever `setupProb` is uniform
strict PPT and `seedLen` is computable in polynomial time in unary. -/
theorem isPPTOn_seededSetupProb {setupProb : ℕ → ProbComp F.Desc}
    {seedLen : ℕ → F.Desc → ℕ}
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hseed : ComputableInPolyTime (fun p : ℕ × F.Desc => seedLen p.1 p.2)
      (encPair encUnary F.encDesc) encUnary) :
    IsPPTOn encUnary F.withSeed.encDesc (F.seededSetupProb setupProb seedLen) :=
  hsetup.bind_with ((ComputableInPolyTime.sampleList hseed).bind_with
    (ComputableInPolyTime.isPPTOn (by fun_prop)))

/-- Ideal-sampling step, not the cited result: IND-CPA security of the general-cipher Hashed
ElGamal game `hashedElGamalCipherCPAGameOn` with `linearHashKDF` at arbitrary key length
`outLen : ℕ → ℕ`, whose key and challenge exponents are drawn exactly uniformly at the `PMF` level,
from `DDH` and `Encryption.DEMOneTimeKeyINDCPAOn` (after [BonehShoup2023], Section 8.10.4,
Theorem 8.11, p. 334, and Section 11.5.2, Theorem 11.5, pp. 449–451). Combining
`DDH.withSeed`, `secureKDF_linearHashKDF`, `isPPTOn_seededSetupProb`, and
`DDH.negligible_hashedElGamalCipherCPAGameOn_ideal_of_demOneTimeKeyINDCPAOn` yields IND-CPA
security of that game instantiated with `linearHashKDF` at any polynomial-time key length
`outLen` under `F.DDH` and `Encryption.DEMOneTimeKeyINDCPAOn`, with no `SecureKDF` hypothesis.
In its place the theorem requires `LinearHashKDFConditions` for the strict PPT setup sampler
`setupProb` with output length `outLen`. -/
theorem DDH.negligible_hashedElGamalCipherCPAGameOn_ideal_linearHashKDF_of_demOneTimeKeyINDCPAOn
    {F : PrimeOrderGroupFamily} {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid validSym : ℕ → List Bool → Msg → Msg → Bool}
    {setupProb : ℕ → ProbComp F.Desc} {keyLen bound : F.Desc → ℕ} {outLen qMin : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => ProbComp.eval (setupProb n)))
    (hDEM : Encryption.DEMOneTimeKeyINDCPAOn validSym encMsg outLen encryptSym)
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hKDF : F.LinearHashKDFConditions (fun n => ProbComp.eval (setupProb n)) keyLen bound outLen
      qMin)
    (hout_poly : ComputableInPolyTime outLen encUnary encUnary)
    (hkey_poly : ComputableInPolyTime keyLen F.encDesc encUnary)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
    (hvalid_imp : ∀ n d u m₀ m₁,
      valid n (encPair F.withSeed.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true)
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Negligible fun n =>
      Game.advantage
        (F.withSeed.hashedElGamalCipherCPAGameOn valid
          (F.seededSetup (fun m => ProbComp.eval (setupProb m))
            (F.linearHashSeedLen outLen bound))
          (F.linearHashKDF keyLen bound) encryptSym adversary false n)
        (F.withSeed.hashedElGamalCipherCPAGameOn valid
          (F.seededSetup (fun m => ProbComp.eval (setupProb m))
            (F.linearHashSeedLen outLen bound))
          (F.linearHashKDF keyLen bound) encryptSym adversary true n) := by
  have hseed_poly := F.computableInPolyTime_linearHashSeedLen hout_poly hbound_poly
  have hsetup_eq : (fun n => ProbComp.eval (F.seededSetupProb setupProb
      (F.linearHashSeedLen outLen bound) n)) =
      F.seededSetup (fun m => ProbComp.eval (setupProb m)) (F.linearHashSeedLen outLen bound) :=
    funext (F.eval_seededSetupProb setupProb _)
  have hDDH' := hsetup_eq.symm ▸ hDDH.withSeed hseed_poly
  simpa only [F.eval_seededSetupProb] using
    hDDH'.negligible_hashedElGamalCipherCPAGameOn_ideal_of_demOneTimeKeyINDCPAOn
      (hsetup_eq.symm ▸ F.secureKDF_linearHashKDF hKDF) hDEM
      (F.isPPTOn_seededSetupProb hsetup hseed_poly) hvalid hvalid_imp
      (F.computableInPolyTime_linearHashKDF hkey_poly hbound_poly) hencryptSym hA

/-- Ideal-sampling step, not the cited result: IND-CPA security of the general-cipher Hashed
ElGamal game `hashedElGamalCipherCPAGameOn` with `linearHashKDF`, whose key and challenge exponents
are drawn exactly uniformly at the `PMF` level, from `DDH` and `Encryption.DEMOneTimeINDCPAOn`
(after [BonehShoup2023], Section 8.10.4, Theorem 8.11, p. 334, and Section 11.5.2, Theorem 11.5,
pp. 449–451). Combining `DDH.withSeed`, `secureKDF_linearHashKDF`, `isPPTOn_seededSetupProb`, and
`DDH.negligible_hashedElGamalCipherCPAGameOn_ideal_of_demOneTimeINDCPAOn` yields IND-CPA security
of that game instantiated with `linearHashKDF` under
`F.DDH` and `Encryption.DEMOneTimeINDCPAOn`, with no `SecureKDF` hypothesis. In its place the
theorem requires `LinearHashKDFConditions` for the strict PPT setup sampler `setupProb` with output
length `n`. -/
theorem DDH.negligible_hashedElGamalCipherCPAGameOn_ideal_linearHashKDF {F : PrimeOrderGroupFamily}
    {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid validSym : ℕ → List Bool → Msg → Msg → Bool}
    {setupProb : ℕ → ProbComp F.Desc} {keyLen bound : F.Desc → ℕ} {qMin : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => ProbComp.eval (setupProb n)))
    (hDEM : Encryption.DEMOneTimeINDCPAOn validSym encMsg encryptSym)
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hKDF : F.LinearHashKDFConditions (fun n => ProbComp.eval (setupProb n)) keyLen bound
      (fun n => n) qMin)
    (hkey_poly : ComputableInPolyTime keyLen F.encDesc encUnary)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hvalid_imp : ∀ n d u m₀ m₁,
      valid n (encPair F.withSeed.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true)
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, k, m⟩ => encryptSym n k m))
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Negligible fun n =>
      Game.advantage
        (F.withSeed.hashedElGamalCipherCPAGameOn valid
          (F.seededSetup (fun m => ProbComp.eval (setupProb m))
            (F.linearHashSeedLen (fun n => n) bound))
          (F.linearHashKDF keyLen bound) encryptSym adversary false n)
        (F.withSeed.hashedElGamalCipherCPAGameOn valid
          (F.seededSetup (fun m => ProbComp.eval (setupProb m))
            (F.linearHashSeedLen (fun n => n) bound))
          (F.linearHashKDF keyLen bound) encryptSym adversary true n) :=
  hDDH.negligible_hashedElGamalCipherCPAGameOn_ideal_linearHashKDF_of_demOneTimeKeyINDCPAOn
    hDEM hsetup hKDF ComputableInPolyTime.id' hkey_poly hbound_poly
    hvalid hvalid_imp hencryptSym hA

end Cslib.Crypto.PrimeOrderGroupFamily
