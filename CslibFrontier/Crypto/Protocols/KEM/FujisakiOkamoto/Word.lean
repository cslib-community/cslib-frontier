/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto
public import CslibFrontier.Crypto.Encoding
public import CslibFrontier.Crypto.Computational.Encryption.Basic
public import CslibFrontier.Computability.Probabilistic.Oracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Tactic.OptionMatch
import CslibFrontier.Tactic.PPT

/-!
# Word-level Fujisaki–Okamoto family with native honest algorithms

The Fujisaki–Okamoto transforms `FO^⊥` and `FO-notbot` of
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto` act on one fixed explicit-coin scheme. This
module states them for a security-parameter family of schemes over words, and proves that the
honest algorithms are uniform strict (oracle) PPT whenever the underlying public-key encryption
family is.

`WordPKE` is a public-key encryption family with explicit coins
([HofheinzHoevelmannsKiltz2017], IACR ePrint 2017/604, full version dated 2 November 2021, §2.1):
at parameter `n`, messages are words of length `msgLen n`, coins are uniform words of length
`coinLen n`, and the ciphertext space is the words of length at most `ctLen n`. Key generation is
randomized; deterministic encryption and decryption are functions of the parameter and their
word arguments. `WordPKE.IsEfficient` asks for strict PPT key generation and polynomial-time
encryption, decryption and lengths. `WordPKE.CiphertextFits` says that encryption under generated
keys stays in the ciphertext space, and `WordPKE.INDCPA` is IND-CPA security of randomized
encryption `WordPKE.encrypt` with challenge messages in the message space.

At each parameter, `WordPKE.scheme P keyLen n` is the FO parameter bundle `Scheme` over words,
with uniform messages, coins and `keyLen n`-bit keys. Its decryption reports only results of
message length. The native algorithms query two word oracles `G` and `H` (`RO`), reading at most
`coinLen n` bits of each `G` reply and `keyLen n` bits of each `H` reply:

* `WordPKE.keyGenNotBot` is `Scheme.keyGenNotBot` of the bundle;
* `WordPKE.encaps` draws `m`, queries `G(m)`, encrypts, and queries `H(m, c)`;
* `WordPKE.decapsNotBot` and `WordPKE.decapsBot` reject words longer than `ctLen n` with `none`,
  and otherwise run the oracle-generic decapsulations `Scheme.decapsNotBotM` and
  `Scheme.decapsBotM` of the bundle with the word oracles.

The wire encoding of the pair `(m, c)` is `encHQuery (false, m, c)`. On rejection the same
encoding carries the secret seed in place of the decrypted message.

## Deviations from [HofheinzHoevelmannsKiltz2017]

* Words longer than `ctLen n` are outside the ciphertext space, and decapsulation rejects them
  with `none` before any oracle call, for both transforms. In the source, decapsulation is only
  defined on the ciphertext space. ML-KEM performs the same check, the ciphertext type check of
  the decapsulation input check ([NISTFIPS203], §7.3).
* The source's decryption outputs a message of the finite message space or `⊥` (§2.1). Here a
  decryption result that is not a word of length `msgLen n` is treated as `⊥`.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient`: the word-level family and its
  efficiency.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.encrypt`: randomized encryption, the
  algorithm of the family's IND-CPA security.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.CiphertextFits`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsMessagePair`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.INDCPA`: encryption stays in the ciphertext
  space, and IND-CPA security of the family with challenge messages in its message space.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.toExplicitCoin`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.scheme`: the explicit-coin scheme and the FO
  bundle at one parameter.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.encEncDetInput`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.encImplicitSK`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.encDecapsNotBotInput`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.encDecapsBotInput`: the encoded inputs of the
  certificates.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.RO`, `Cslib.Crypto.Protocols.FujisakiOkamoto.encHQuery`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.queryG`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.queryH`: the word random oracles.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.keyGenNotBot`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.encaps`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.decapsNotBot`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.decapsBot`: the native honest algorithms.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isPPTOn_encrypt`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isPPTOn_keyGenNotBot`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isOraclePPTOn_encaps`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isOraclePPTOn_decapsNotBot`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isOraclePPTOn_decapsBot`: native
  certificates for every honest algorithm, from the certificates of the PKE family.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021), §2.1 and Definition 2.2, §3.2.1 Fig. 9 and §3.2.2 Fig. 12.
* [NIST, *FIPS 203: Module-Lattice-Based Key-Encapsulation Mechanism Standard*][NISTFIPS203],
  §7.3.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability Turing.MultiTapeTM

/-- A word-level public-key encryption family with explicit coins
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §2.1). At parameter `n`, messages
are words of length `msgLen n`, encryption coins are uniform words of length `coinLen n`, and the
ciphertext space is the words of length at most `ctLen n`. -/
structure WordPKE where
  /-- The message length at each parameter. -/
  msgLen : ℕ → ℕ
  /-- The coin length at each parameter. -/
  coinLen : ℕ → ℕ
  /-- The bound on ciphertext lengths at each parameter. -/
  ctLen : ℕ → ℕ
  /-- Key generation `(pk, sk) ← keyGen n`. -/
  keyGen : ℕ → ProbComp (List Bool × List Bool)
  /-- Deterministic encryption `encDet n pk m r` with explicit coins `r`. -/
  encDet : ℕ → List Bool → List Bool → List Bool → List Bool
  /-- Deterministic decryption `dec n sk c`, `none` on failure. -/
  dec : ℕ → List Bool → List Bool → Option (List Bool)

/-- The input `(1ⁿ, pk, m, r)` of deterministic encryption: the parameter in unary, then the
public key, the message and the coins as framed words. -/
abbrev encEncDetInput : ℕ × List Bool × List Bool × List Bool ↪ List Bool :=
  encPair encUnary (encPair encBits (encPair encBits encBits))

/-- Efficiency of a word-level PKE family: polynomial-time lengths, uniform strict PPT key
generation, and polynomial-time deterministic encryption and decryption. -/
structure WordPKE.IsEfficient (P : WordPKE) : Prop where
  /-- The message length is polynomial-time computable in unary. -/
  msgLen : ComputableInPolyTime P.msgLen encUnary encUnary
  /-- The coin length is polynomial-time computable in unary. -/
  coinLen : ComputableInPolyTime P.coinLen encUnary encUnary
  /-- The ciphertext length bound is polynomial-time computable in unary. -/
  ctLen : ComputableInPolyTime P.ctLen encUnary encUnary
  /-- Key generation is uniform strict PPT. -/
  keyGen : IsPPTOn encUnary (encPair encBits encBits) P.keyGen
  /-- Deterministic encryption is polynomial-time on `(1ⁿ, pk, m, r)`. -/
  encDet : ComputableInPolyTime (fun (n, pk, m, r) => P.encDet n pk m r) encEncDetInput encBits
  /-- Decryption is polynomial-time on `(1ⁿ, sk, c)`. -/
  dec : ComputableInPolyTime (fun (n, sk, c) => P.dec n sk c) (encKeyedInput encBits)
    (encOption encBits)

namespace WordPKE

variable (P : WordPKE) (keyLen : ℕ → ℕ)

/-- Randomized encryption: draw uniform coins `r` of length `coinLen n` and output
`encDet n pk m r`. The IND-CPA security of the family is stated for this algorithm. -/
noncomputable def encrypt (n : ℕ) (pk m : List Bool) : ProbComp (List Bool) := do
  let r ← BitString.sampleList (P.coinLen n)
  return P.encDet n pk m r

/-- **The ciphertexts of `P` lie in its ciphertext space.** At every parameter `n`, encrypting a
message of length `msgLen n` with coins of length `coinLen n` under a generated public key gives a
word of length at most `ctLen n`. [HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full
version dated 2 November 2021, §2.1) measures the spreadness of a scheme over its ciphertext space
`C`; `WordPKE` declares that space as the words of length at most `ctLen n`, and this predicate
says that encryption stays inside it. -/
def CiphertextFits : Prop :=
  ∀ n pk sk, (pk, sk) ∈ (ProbComp.eval (P.keyGen n)).support →
    ∀ m r, m.length = P.msgLen n → r.length = P.coinLen n →
      (P.encDet n pk m r).length ≤ P.ctLen n

/-- The admissible challenge pairs of the IND-CPA game of `P` at parameter `n`: two messages of
length `msgLen n`, the message space of `P`. -/
def IsMessagePair (n : ℕ) (_pk m₀ m₁ : List Bool) : Bool :=
  m₀.length == P.msgLen n && m₁.length == P.msgLen n

/-- **IND-CPA security of `P`** ([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021),
§2.1, Def. 2.2 and Figure 4, pp. 9–10): every uniform strict PPT chosen-message adversary has
negligible advantage in the single-challenge game of randomized encryption `encrypt`, with
challenge messages in the message space of `P`. The source defines only the concrete advantage
`|Pr[b' = b] - 1/2|`; here the advantage between the two experiments, which is twice that, is
negligible. The source's second stage also receives `pk`; here the first stage passes on what it
needs in its saved state. -/
def INDCPA : Prop :=
  Encryption.INDCPAOn P.IsMessagePair encBits P.keyGen P.encrypt

/-- The explicit-coin scheme of `P` at parameter `n`, over words: coins are uniform words of
length `coinLen n`, and decryption reports only results of length `msgLen n`. -/
noncomputable def toExplicitCoin (n : ℕ) :
    ExplicitCoinPKE (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) where
  keyGen := P.keyGen n
  sampleCoins := BitString.sampleList (P.coinLen n)
  encDet := P.encDet n
  dec sk c := (P.dec n sk c).filter fun m => m.length == P.msgLen n

/-- The FO parameter bundle of `P` at parameter `n`, over words: the explicit-coin scheme
`toExplicitCoin n`, uniform messages of length `msgLen n` and uniform keys of length `keyLen n`. -/
noncomputable def scheme (n : ℕ) :
    Scheme (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) where
  pke := P.toExplicitCoin n
  sampleMsg := BitString.sampleList (P.msgLen n)
  sampleKey := BitString.sampleList (keyLen n)

end WordPKE

/-- The two random oracles of the word-level FO transforms: `G` derives encryption coins from a
message and `H` derives keys. -/
inductive RO where
  /-- The coin-derivation oracle `G`. -/
  | G
  /-- The key-derivation oracle `H`. -/
  | H
  deriving DecidableEq

instance : Fintype RO := ⟨{.G, .H}, fun x => by cases x <;> simp⟩

/-- The word of an `H` query `(b, m, c)`: a Boolean prefix, then the message and the
ciphertext as framed words. The word-game domain uses the fixed prefix `false`. -/
abbrev encHQuery : Bool × List Bool × List Bool ↪ List Bool :=
  encPair encBool (encPair encBits encBits)

/-- Query `H` on the pair `(m, c)` and read at most `keyLen n` bits of the reply. -/
def queryH (keyLen : ℕ → ℕ) (n : ℕ) (mc : List Bool × List Bool) :
    WordOracleComp RO (List Bool) :=
  List.take (keyLen n) <$>
    ProbOracleComp.query (spec := fun _ : RO × List Bool => List Bool) (RO.H, encHQuery (false, mc))

/-- The encoding of an `FO-notbot` secret key `(sk, pk, s)` as three framed words. -/
enc_structure encImplicitSK : ImplicitSK (List Bool) (List Bool) (List Bool) where
  sk : encBits, pk : encBits, fallback : encBits

/-- The input `(1ⁿ, dk, c)` of `FO-notbot` decapsulation: the parameter in unary, then the
secret key and the ciphertext. -/
abbrev encDecapsNotBotInput :
    ℕ × ImplicitSK (List Bool) (List Bool) (List Bool) × List Bool ↪ List Bool :=
  encPair encUnary (encPair encImplicitSK encBits)

/-- The input `(1ⁿ, pk, sk, c)` of `FO^⊥` decapsulation: the parameter in unary, then the public
key, the secret key and the ciphertext as framed words. -/
abbrev encDecapsBotInput : ℕ × List Bool × List Bool × List Bool ↪ List Bool :=
  encPair encUnary (encPair encBits (encPair encBits encBits))

namespace WordPKE

variable (P : WordPKE) (keyLen : ℕ → ℕ)

/-- Query `G` on `m` and read at most `coinLen n` bits of the reply. -/
def queryG (n : ℕ) (m : List Bool) : WordOracleComp RO (List Bool) :=
  List.take (P.coinLen n) <$>
    ProbOracleComp.query (spec := fun _ : RO × List Bool => List Bool) (RO.G, m)

/-- Native key generation of `FO-notbot` ([HofheinzHoevelmannsKiltz2017], ePrint 2017/604
(2 Nov 2021), §3.2.2, Fig. 12): `Scheme.keyGenNotBot` of the bundle `scheme P keyLen n`. -/
noncomputable def keyGenNotBot (n : ℕ) :
    ProbComp (List Bool × ImplicitSK (List Bool) (List Bool) (List Bool)) :=
  (P.scheme keyLen n).keyGenNotBot

/-- Native encapsulation of `FO^⊥` and `FO-notbot` ([HofheinzHoevelmannsKiltz2017], ePrint
2017/604 (2 Nov 2021), §3.2.1, Fig. 9 and §3.2.2, Fig. 12): draw a uniform message `m` of length
`msgLen n`, query `r = G(m)`, encrypt `c = encDet n pk m r`, query `k = H(m, c)`, and output
`(c, k)`. -/
noncomputable def encaps (n : ℕ) (pk : List Bool) : WordOracleComp RO (List Bool × List Bool) := do
  let m ← ProbOracleComp.sample (BitString.sampleList (P.msgLen n))
  let r ← P.queryG n m
  let c := P.encDet n pk m r
  let k ← queryH keyLen n (m, c)
  return (c, k)

/-- Native implicit-rejection decapsulation of `FO-notbot` ([HofheinzHoevelmannsKiltz2017],
ePrint 2017/604 (2 Nov 2021), §3.2.2, Fig. 12): reject a word longer than `ctLen n` with `none`,
and otherwise run `Scheme.decapsNotBotM` of the bundle with the word oracles. -/
noncomputable def decapsNotBot (n : ℕ) (dk : ImplicitSK (List Bool) (List Bool) (List Bool))
    (c : List Bool) : WordOracleComp RO (Option (List Bool)) :=
  if c.length ≤ P.ctLen n then
    some <$> (P.scheme keyLen n).decapsNotBotM (P.queryG n) (queryH keyLen n) dk c
  else
    pure none

/-- Native explicit-rejection decapsulation of `FO^⊥` ([HofheinzHoevelmannsKiltz2017], ePrint
2017/604 (2 Nov 2021), §3.2.1, Fig. 9): reject a word longer than `ctLen n` with `none`, and
otherwise run `Scheme.decapsBotM` of the bundle with the word oracles. -/
noncomputable def decapsBot (n : ℕ) (pk sk c : List Bool) :
    WordOracleComp RO (Option (List Bool)) :=
  if c.length ≤ P.ctLen n then
    (P.scheme keyLen n).decapsBotM (P.queryG n) (queryH keyLen n) pk sk c
  else
    pure none

/-! ### Native certificates -/

namespace IsEfficient

variable {P : WordPKE} {keyLen : ℕ → ℕ}

@[local fun_prop]
private theorem isOraclePPTOn_queryG
    (hcoinLen : ComputableInPolyTime P.coinLen encUnary encUnary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {m : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encBits) :
    IsOraclePPTOn input encBits (fun a => P.queryG (n a) (m a)) :=
  IsOraclePPTOn.query_take RO.G hm (hcoinLen.comp hn)

@[local fun_prop]
private theorem isOraclePPTOn_queryH
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {mc : α → List Bool × List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hmc : ComputableInPolyTime mc input (encPair encBits encBits)) :
    IsOraclePPTOn input encBits (fun a => queryH keyLen (n a) (mc a)) :=
  IsOraclePPTOn.query_take RO.H (by polytime) (hkeyLen.comp hn)

/-- Randomized encryption is uniform strict PPT on `(1ⁿ, pk, m)`. -/
theorem isPPTOn_encrypt (hP : P.IsEfficient) :
    IsPPTOn (encKeyedInput encBits) encBits (fun (n, pk, m) => P.encrypt n pk m) := by
  change IsPPTOn (encKeyedInput encBits) encBits (fun x => P.encrypt x.1 x.2.1 x.2.2)
  have ⟨_, hcoinLen, _, _, hencDet, _⟩ := hP
  ppt [encrypt]

/-- Native `FO-notbot` key generation is uniform strict PPT. -/
theorem isPPTOn_keyGenNotBot (hP : P.IsEfficient) :
    IsPPTOn encUnary (encPair encBits encImplicitSK) (P.keyGenNotBot keyLen) := by
  have ⟨hmsgLen, _, _, hkeyGen, _, _⟩ := hP
  ppt [keyGenNotBot, Scheme.keyGenNotBot, scheme, toExplicitCoin]

/-- Native encapsulation is uniform strict oracle PPT on `(1ⁿ, pk)`, for every pair of external
oracles `G` and `H`. -/
theorem isOraclePPTOn_encaps (hP : P.IsEfficient)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    IsOraclePPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun (n, pk) => P.encaps keyLen n pk) := by
  change IsOraclePPTOn (encPair encUnary encBits) _ (fun x => P.encaps keyLen x.1 x.2)
  have ⟨hmsgLen, hcoinLen, _, _, hencDet, _⟩ := hP
  ppt [encaps]

@[local fun_prop]
private theorem isOraclePPTOn_optionElim {α β γ : Type} [Inhabited β]
    {input : α ↪ List Bool} {encB : β ↪ List Bool} {output : γ ↪ List Bool}
    {opt : α → Option β} {no : α → WordOracleComp RO γ} {yes : α → β → WordOracleComp RO γ}
    (hopt : ComputableInPolyTime opt input (encOption encB))
    (hno : IsOraclePPTOn input output no)
    (hyes : IsOraclePPTOn (encPair input encB) output (fun p => yes p.1 p.2)) :
    IsOraclePPTOn input output (fun a => (opt a).elim (no a) (yes a)) := by
  refine (IsOraclePPTOn.cond (ComputableInPolyTime.optionIsSome hopt)
    (hyes.preprocess (ComputableInPolyTime.id'.prod
      (hopt.optionGetDWithInput (.const default)))) hno).congr fun a _ _ _ => ?_
  cases opt a <;> rfl

/-- Decryption of the bundle, `dec` filtered to messages of length `msgLen n`, as an optional
elimination. -/
private noncomputable def toExplicitCoinDec (P : WordPKE) (n : ℕ) (sk c : List Bool) :
    Option (List Bool) :=
  (P.toExplicitCoin n).dec sk c

private theorem toExplicitCoinDec_eq (n : ℕ) (sk c : List Bool) :
    toExplicitCoinDec P n sk c =
      (P.dec n sk c).elim none fun m => if m.length = P.msgLen n then some m else none := by
  simp only [toExplicitCoinDec, toExplicitCoin]
  cases P.dec n sk c with
  | none => rfl
  | some m => simp [Option.filter]

/-- Decryption of the bundle is polynomial-time on `(1ⁿ, sk, c)`. -/
@[local fun_prop]
private theorem computableInPolyTime_toExplicitCoinDec (hP : P.IsEfficient)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {sk c : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hsk : ComputableInPolyTime sk input encBits)
    (hc : ComputableInPolyTime c input encBits) :
    ComputableInPolyTime (fun a => toExplicitCoinDec P (n a) (sk a) (c a))
      input (encOption encBits) := by
  have hbase : ComputableInPolyTime (fun (n, sk, c) => toExplicitCoinDec P n sk c)
      (encKeyedInput encBits) (encOption encBits) := by
    simp only [toExplicitCoinDec_eq]
    have ⟨hmsgLen, _, _, _, _, hdec⟩ := hP
    exact ComputableInPolyTime.optionElimWithInput hdec (.const none) (by polytime)
  exact hbase.comp (hn.prod (hsk.prod hc))

/-- Shared word-level `T[PKE, G]` derandomized decryption with re-encryption check. -/
private noncomputable def wordDecTM (P : WordPKE) (n : ℕ) (pk sk c : List Bool) :
    WordOracleComp RO (Option (List Bool)) :=
  decTM (P.toExplicitCoin n) (P.queryG n) pk sk c

private theorem decTM_toExplicitCoin (n : ℕ) (pk sk c : List Bool) :
    decTM (P.toExplicitCoin n) (P.queryG n) pk sk c = wordDecTM P n pk sk c :=
  rfl

private theorem wordDecTM_eq (n : ℕ) (pk sk c : List Bool) :
    wordDecTM P n pk sk c =
      (toExplicitCoinDec P n sk c).elim (return none) fun m' => do
        let r' ← P.queryG n m'
        return if P.encDet n pk m' r' = c then some m' else none := by
  simp only [wordDecTM, decTM, toExplicitCoinDec]
  cases (P.toExplicitCoin n).dec sk c <;> rfl

@[local fun_prop]
private theorem isOraclePPTOn_wordDecTM (hP : P.IsEfficient)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {pk sk c : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hsk : ComputableInPolyTime sk input encBits)
    (hc : ComputableInPolyTime c input encBits) :
    IsOraclePPTOn input (encOption encBits)
      (fun a => wordDecTM P (n a) (pk a) (sk a) (c a)) := by
  simp only [wordDecTM_eq]
  have ⟨_, hcoinLen, _, _, hencDet, _⟩ := hP
  ppt

/-- Native `FO-notbot` decapsulation is uniform strict oracle PPT on `(1ⁿ, dk, c)`, for every pair
of external oracles `G` and `H`. -/
theorem isOraclePPTOn_decapsNotBot (hP : P.IsEfficient)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    IsOraclePPTOn encDecapsNotBotInput (encOption encBits)
      (fun (n, dk, c) => P.decapsNotBot keyLen n dk c) := by
  change IsOraclePPTOn encDecapsNotBotInput _ (fun x => P.decapsNotBot keyLen x.1 x.2.1 x.2.2)
  dsimp only [decapsNotBot, Scheme.decapsNotBotM, scheme]
  simp only [decTM_toExplicitCoin]
  option_match_to_elim
  have ⟨_, _, hctLen, _, _, _⟩ := hP
  ppt

/-- Native `FO^⊥` decapsulation is uniform strict oracle PPT on `(1ⁿ, pk, sk, c)`, for every pair
of external oracles `G` and `H`. -/
theorem isOraclePPTOn_decapsBot (hP : P.IsEfficient)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    IsOraclePPTOn encDecapsBotInput (encOption encBits)
      (fun (n, pk, sk, c) => P.decapsBot keyLen n pk sk c) := by
  change IsOraclePPTOn encDecapsBotInput _ (fun x => P.decapsBot keyLen x.1 x.2.1 x.2.2.1 x.2.2.2)
  dsimp only [decapsBot, Scheme.decapsBotM, scheme]
  simp only [decTM_toExplicitCoin]
  option_match_to_elim
  have ⟨_, _, hctLen, _, _, _⟩ := hP
  ppt

end IsEfficient

end WordPKE

end Cslib.Crypto.Protocols.FujisakiOkamoto
