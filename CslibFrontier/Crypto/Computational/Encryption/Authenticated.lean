/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Computational.Encryption.SymmetricCPA
public import CslibFrontier.Crypto.Computational.PseudorandomFunction
public import CslibFrontier.Crypto.Game.HiddenBit
public import CslibFrontier.Crypto.Game.UntilBad
public import CslibFrontier.Languages.Probabilistic.UniformNat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.RunState
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Sum.Lift
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.EncLen

/-!
# Authenticated Encryption and Adaptive Chosen-Ciphertext Security

This module formalizes symmetric authenticated encryption (`AuthenticatedEncryption`) and adaptive
chosen-ciphertext security (`INDCCA`) following
[Boneh and Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
Chapter 5 (Sections 5.3 and 5.10) and Chapter 9 (Sections 9.1 and 9.2.2–9.2.3):

1. **Symmetric ciphers and adaptive/one-time CPA security (`SymmetricCipher`, `cpaGame`, `INDCPA`,
   `cpaOneTimeGame`, `OneTimeINDCPA`, `not_indcpa_of_deterministic`,
   `not_indcpa_of_ciphertext_length_eq`)**
   ([BonehShoup2023], Section 2.2, Attack Game 2.1 and Definition 2.2; Section 5.3, Attack Game 5.2,
   Definition 5.2, and Example 5.1, printed pp. 181–182; Exercise 5.10(a), printed p. 211):
   a uniform symmetric cipher on `n`-bit messages at security parameter `n` consists of strict PPT
   key generation `keyGen`, strict PPT encryption `encrypt`, and deterministic polynomial-time
   decryption `decrypt` returning `Option (List Bool)` (encoded via `encOption encBits`). In
   `cpaGame`, an adaptive `OracleDistinguisher` submits left-or-right pairs `(m0, m1)` of `n`-bit
   messages and receives `encrypt n k (if bit then m1 else m0)`; `cpaOneTimeGame` and
   `OneTimeINDCPA` restrict the oracle to at most one valid encryption query. We also formalize
   Example 5.1 (`not_indcpa_of_deterministic`) for any cipher deterministic on `0^n` with arbitrary
   polynomial ciphertext expansion via the 2-query distinguisher `detCPAAdversary ctBound`, and
   deduce Exercise 5.10(a) (`not_indcpa_of_ciphertext_length_eq`) as its zero-expansion corollary.
2. **Ciphertext integrity and authenticated encryption (`ciGame`, `CiphertextIntegrity`,
   `AuthenticatedEncryption`, `ciOneTimeGame`, `OneTimeCiphertextIntegrity`,
   `OneTimeAuthenticatedEncryption`)** ([BonehShoup2023], Section 9.1, Attack Game 9.1 and
   Definitions 9.1–9.4, printed pp. 358–360): in `ciGame` (and its single-query counterpart
   `ciOneTimeGame`), an adaptive `CIAdversary` queries an encryption oracle on `n`-bit messages
   (logging returned ciphertexts in `queriedCiphertexts`) and wins by outputting a candidate
   ciphertext `ct` such that `!queriedCiphertexts.contains ct` and `(decrypt n k ct).isSome`. A
   cipher provides `AuthenticatedEncryption` when it satisfies both `INDCPA` and
   `CiphertextIntegrity`, and `OneTimeAuthenticatedEncryption` (`1AE`) when it satisfies both
   `OneTimeINDCPA` and `OneTimeCiphertextIntegrity`.
3. **Adaptive chosen-ciphertext security, AE $\Rightarrow$ CCA, 1AE $\Rightarrow$ 1CCA, and
   encryption-query preservation (`ccaGame`, `INDCCA`, `ccaOneTimeGame`, `OneTimeINDCCA`,
   `ccaToCPAAdversary`, `ccaToCIAdversary`, `ccaToCIHiddenBitAdversary`,
   `IsEncryptionQueryBounded`, `IsDecryptionQueryBounded`,
   `isQueryBounded_ccaToCPAAdversary_of_isEncryptionQueryBounded`,
   `isQueryBounded_ccaToCIAdversary_of_isEncryptionQueryBounded`,
   `advantage_ccaGame_le`, `advantage_ccaGame_le_two_mul`, `guessingAdvantage_guessBit_ccaGame_le`,
   `guessingAdvantage_guessBit_ccaGame_le_two_mul`, `AuthenticatedEncryption.indcca`,
   `advantage_ccaOneTimeGame_le`, `advantage_ccaOneTimeGame_le_two_mul`,
   `guessingAdvantage_guessBit_ccaOneTimeGame_le`, `OneTimeAuthenticatedEncryption.oneTimeINDCCA`)**
   ([BonehShoup2023], Sections 9.2.2–9.2.3, Attack Game 9.2, Definitions 9.5–9.6, and Theorem 9.1,
   printed pp. 362–365): in `ccaGame` (and its single-encryption-query counterpart
   `ccaOneTimeGame`), a two-channel `CCAAdversary` (`Operation = Bool`) may interleave
   left-or-right encryption queries (`false`, recording challenge ciphertexts) with decryption
   queries (`true`, rejecting recorded challenge ciphertexts and returning
   `encOption encBits (decrypt n k ct)` on all other ciphertexts). Using the difference lemma
   (`OracleComp.IdenticalUntilBad.advantage_le`, [BonehShoup2023], Theorem 4.7) between `ccaGame`
   and `ccaRejectGame` (and between `ccaOneTimeGame` and `ccaOneTimeRejectGame`), we prove both
   `AE ⇒ CCA` (`AuthenticatedEncryption.indcca`) and `1AE ⇒ 1CCA`
   (`OneTimeAuthenticatedEncryption.oneTimeINDCCA`) with the book's bounds (9.3) and (9.4) in the
   number `Qd` of decryption queries, up to a power-of-two factor (see below), as well as
   encryption-query count preservation for the reductions $B_{\mathrm{cpa}}$ and $B_{\mathrm{ci}}$.

The generic **Encrypt-then-MAC** composition ([BonehShoup2023], Section 9.4.1, Theorem 9.2,
printed pp. 367–368) and its concrete non-vacuous PRF-based cipher instance ([BonehShoup2023],
Section 5.4.1, Example 5.2 and Theorem 5.2, printed pp. 183–187) are formalized in
`CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC`.

## Specializations and losses relative to Boneh–Shoup Chapter 9

* **Ciphertext space**: a cipher declares its ciphertext space `ctSpace`, every word by default,
  and decryption rejects outside it (`decrypt_eq_none_of_ctSpace_eq_false`). Attack Game 9.1 asks
  for a forgery in `C`, and Attack Game 9.2 for decryption queries in `C`. On a cipher with
  `ctSpace = C`, a forgery outside `C` loses and a decryption query outside `C` is answered with a
  rejection, so the integrity games are the source's on `C`, and `INDCCA` and `OneTimeINDCCA`
  imply the source's CCA and 1CCA security on `C` (and are equivalent to them when `C` is
  efficiently recognizable, as Definition 2.10 requires).
* **Fixed `n`-bit plaintext domain at security parameter `n`**: encryption queries take `n`-bit
  messages (`msg.length = n` in `ciGame`, `m0.length = n ∧ m1.length = n` in `cpaGame` and
  `ccaGame`). Malformed encryption queries return `[]` without invoking `encrypt` or recording a
  challenge ciphertext.
* **Challenge-ciphertext decryption queries in `ccaOracle`**: in Section 9.2.2 (printed p. 362),
  the text stipulates that "The restriction we impose is that the adversary may not ask for the
  decryptions of any of these ciphertexts." In
  `ccaOracle`, decryption queries on previously returned challenge ciphertexts
  (`queriedCiphertexts`) are instead answered with `[] = encOption encBits none` (rejection), which
  is equivalent for adversaries respecting the restriction and makes `ccaOracle` a total function on
  all queries.
* **Power-of-two index range in Theorem 9.1**: in equations (9.3) and (9.4) of [BonehShoup2023]
  (printed pp. 363–364), the CI term has coefficients `2 * Qd` and `Qd`, where `Qd` bounds the
  decryption queries (`IsDecryptionQueryBounded`), and $B_{\mathrm{ci}}$ guesses the forging
  decryption query uniformly in `{1, ..., Qd}`. Here `ccaToCIAdversary` uses dyadic index sampling
  `sampleDyadicIndex (Qd n - 1)`, scaling the CI term by `dyadicSize (Qd n - 1)`: `2` when
  `Qd n ≤ 1`, and otherwise the least power of two that is at least `Qd n`. This is because a
  strict PPT sampler with fair coins and a fixed running time has dyadic probabilities. The bounds
  (9.3') `advantage_ccaGame_le_two_mul` and (9.4')
  `guessingAdvantage_guessBit_ccaGame_le` carry `2 * dyadicSize (Qd n - 1)` and
  `dyadicSize (Qd n - 1)`; `guessingAdvantage_guessBit_ccaGame_le_two_mul` restates (9.4') with
  `2 * Qd n`, since `dyadicSize (Qd n - 1) ≤ 2 * Qd n` once `Qd n ≥ 1`. Encryption queries cost
  nothing in the decryption budget.

## Main definitions

* `Cslib.Crypto.CIAdversary`, `Cslib.Crypto.CCAAdversary`: adaptive ciphertext-integrity and
  chosen-ciphertext adversaries.
* `Cslib.Crypto.SymmetricCipher`: uniform symmetric cipher on `n`-bit messages, with a ciphertext
  space outside which decryption rejects.
* `Cslib.Crypto.SymmetricCipher.CiphertextLength`, `CiphertextLengthLE`: exact and bounded
  ciphertext length on `n`-bit messages under keys supported by `keyGen n`.
* `Cslib.Crypto.SymmetricCipher.cpaGame`, `INDCPA`, `cpaOneTimeGame`, `OneTimeINDCPA`,
  `detCPAAdversary`: adaptive and one-time symmetric CPA games, security predicates, and 2-query
  distinguisher truncating replies to `ctBound n` bits ([BonehShoup2023],
  Attack Game 5.2 / Definition 5.2 / Example 5.1 / Definition 9.4). `cpaGame` and `INDCPA` are
  `symmetricCPAGameOn` and `SymmetricINDCPAOn` (`SymmetricCPA.lean`) on pairs of `n`-bit
  messages.
* `Cslib.Crypto.SymmetricCipher.ciGame`, `CiphertextIntegrity`, `AuthenticatedEncryption`,
  `ciOneTimeGame`, `OneTimeCiphertextIntegrity`, `OneTimeAuthenticatedEncryption`:
  multi-query and one-time ciphertext-integrity games, CI predicates, and AE predicates
  ([BonehShoup2023], Attack Game 9.1 / Definitions 9.1–9.4).
* `Cslib.Crypto.SymmetricCipher.ccaGame`, `ccaRejectGame`, `INDCCA`, `ccaOneTimeGame`,
  `ccaOneTimeRejectGame`, `OneTimeINDCCA`: adaptive and one-time CCA games, all-reject hybrid
  games, and CCA security predicates ([BonehShoup2023], Attack Game 9.2 / Definitions 9.5–9.6).
* `Cslib.Crypto.SymmetricCipher.ccaToCPAAdversary`, `ccaToCIAdversary`,
  `ccaToCIHiddenBitAdversary`, `IsEncryptionQueryBounded`, `IsDecryptionQueryBounded`: Theorem 9.1
  reductions from CCA to CPA and CI and structural encryption- and decryption-query budget
  predicates.

## Main results

* `Cslib.Crypto.SymmetricCipher.exists_ciphertext_length_bound`,
  `Cslib.Crypto.SymmetricCipher.exists_ciphertext_length_bound_of_length_eq`: a native cap indexed
  by the security parameter and actual message length (including messages outside the security
  domain), together with its `n`-bit diagonal.

* `Cslib.Crypto.SymmetricCipher.isPPTOn_cpaGame`, `isPPT_cpaGame`, `isPPTOn_cpaOneTimeGame`,
  `isPPT_cpaOneTimeGame`, `isPPTOn_ciGame`, `isPPT_ciGame`, `isPPTOn_ciOneTimeGame`,
  `isPPT_ciOneTimeGame`, `isPPTOn_ccaGame`, `isPPT_ccaGame`, `isPPTOn_ccaOneTimeGame`,
  `isPPT_ccaOneTimeGame`: strict PPT certificates for the multi-query and one-time CPA, CI, and CCA
  experiments.
* `Cslib.Crypto.SymmetricCipher.isOraclePPT_detCPAAdversary`,
  `Cslib.Crypto.SymmetricCipher.advantage_cpaGame_detCPAAdversary`,
  `Cslib.Crypto.SymmetricCipher.not_indcpa_of_deterministic`,
  `Cslib.Crypto.SymmetricCipher.encrypt_eq_of_ciphertext_length_eq`,
  `Cslib.Crypto.SymmetricCipher.exists_eval_encrypt_eq_pure_of_ciphertext_length_eq`,
  `Cslib.Crypto.SymmetricCipher.not_indcpa_of_ciphertext_length_eq`: deterministic symmetric ciphers
  (even with arbitrary polynomial ciphertext expansion) and zero-expansion ciphers cannot satisfy
  `INDCPA` ([BonehShoup2023], Example 5.1 and Exercise 5.10(a)).
* `Cslib.Crypto.SymmetricCipher.isOraclePPT_ccaToCPAAdversary`,
  `Cslib.Crypto.SymmetricCipher.isOraclePPT_ccaToCIAdversary`,
  `Cslib.Crypto.SymmetricCipher.isOraclePPT_ccaToCIHiddenBitAdversary`,
  `Cslib.Crypto.SymmetricCipher.isQueryBounded_ccaToCPAAdversary_of_isEncryptionQueryBounded`,
  `Cslib.Crypto.SymmetricCipher.isQueryBounded_ccaToCIAdversary_of_isEncryptionQueryBounded`:
  `IsOraclePPT` and encryption-query preservation certificates for the Theorem 9.1 reductions.
* `Cslib.Crypto.SymmetricCipher.advantage_ccaGame_le`,
  `Cslib.Crypto.SymmetricCipher.advantage_ccaGame_le_two_mul`,
  `Cslib.Crypto.SymmetricCipher.guessingAdvantage_guessBit_ccaGame_le`,
  `Cslib.Crypto.SymmetricCipher.guessingAdvantage_guessBit_ccaGame_le_two_mul`,
  `Cslib.Crypto.SymmetricCipher.AuthenticatedEncryption.indcca`,
  `Cslib.Crypto.SymmetricCipher.advantage_ccaOneTimeGame_le`,
  `Cslib.Crypto.SymmetricCipher.advantage_ccaOneTimeGame_le_two_mul`,
  `Cslib.Crypto.SymmetricCipher.guessingAdvantage_guessBit_ccaOneTimeGame_le`,
  `Cslib.Crypto.SymmetricCipher.OneTimeAuthenticatedEncryption.oneTimeINDCCA`: quantitative bounds
  (9.3') and (9.4') in the decryption-query count, and asymptotic AE $\Rightarrow$ CCA and
  1AE $\Rightarrow$ 1CCA security ([BonehShoup2023], Theorem 9.1).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 5.3 (pp. 181–182), Exercise 5.10(a) (p. 211), and Chapter 9,
  Sections 9.1 and 9.2.2–9.2.3 (pp. 357–365).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- An adaptive ciphertext-integrity adversary receives the unary security parameter and an
auxiliary word, queries an encryption oracle on chosen messages, and outputs a candidate
ciphertext. -/
abbrev CIAdversary := ℕ → List Bool → WordOracleComp Unit (List Bool)

/-- An adaptive chosen-ciphertext distinguisher receives the unary security parameter and an
auxiliary word, queries a left-or-right encryption oracle (`false`) and a decryption oracle
(`true`), and outputs a distinguishing bit. -/
abbrev CCAAdversary := ℕ → List Bool → WordOracleComp Bool Bool

/-- A uniform symmetric cipher on `n`-bit messages at security parameter `n`, with strict
probabilistic polynomial-time key generation and encryption, deterministic polynomial-time
decryption (returning `Option (List Bool)`), a ciphertext space `ctSpace` outside which decryption
rejects, and perfect decryption completeness on supported keys, `n`-bit messages, and ciphertexts
([BonehShoup2023], Sections 5.3 and 9.1).

A source cipher defined over `(K, M, C)` ([BonehShoup2023], Section 2.3.2, Definition 2.10,
printed p. 31) decrypts only words of `C`. It is encoded with `ctSpace n` deciding `C` at
parameter `n` and with `decrypt` rejecting every other word, which
`decrypt_eq_none_of_ctSpace_eq_false` requires. The integrity and chosen-ciphertext games then
match the source's games on `C` (`ciGame` and `ccaOracle` say how). Both fields have defaults,
every word and its trivial proof, for a cipher whose decryption is meant for all words.
Definition 2.10 also requires `C` to be efficiently recognizable; `ctSpace` carries no complexity
certificate, since no theorem here needs one. -/
structure SymmetricCipher where
  /-- Sample a symmetric secret key `k` at unary security parameter `n`. -/
  keyGen : ℕ → ProbComp (List Bool)
  /-- Probabilistically encrypt a message `msg` under secret key `k` at security parameter `n`. -/
  encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)
  /-- Deterministically decrypt a candidate ciphertext `ct` under secret key `k` at parameter `n`,
  returning `none` on rejection and `some msg` on acceptance. -/
  decrypt : ℕ → List Bool → List Bool → Option (List Bool)
  /-- The ciphertext space at security parameter `n`, as a membership test on words: the set `C`
  of the source cipher ([BonehShoup2023], Definition 2.10). By default every word. -/
  ctSpace : ℕ → List Bool → Bool := fun _ _ => true
  /-- Key generation is uniformly strict PPT in the unary security parameter. -/
  keyGen_ppt : IsPPTOn encUnary encBits keyGen
  /-- Encryption is uniformly strict PPT in `(n, k, msg)`. -/
  encrypt_ppt : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
    (fun ⟨n, k, msg⟩ => encrypt n k msg)
  /-- Decryption is computable in plain polynomial time on `(n, k, ct)`. -/
  decrypt_polyTime : ComputableInPolyTime
    (fun ⟨n, k, ct⟩ => decrypt n k ct)
    (encPair encUnary (encPair encBits encBits)) (encOption encBits)
  /-- Every ciphertext produced by `encrypt` on an `n`-bit message under a supported secret key at
  security parameter `n` decrypts to `some msg`. -/
  decrypt_encrypt : ∀ n k, k ∈ (ProbComp.eval (keyGen n)).support →
    ∀ msg, msg.length = n →
    ∀ ct, ct ∈ (ProbComp.eval (encrypt n k msg)).support →
    decrypt n k ct = some msg
  /-- Decryption rejects every word outside the ciphertext space, under every key. -/
  decrypt_eq_none_of_ctSpace_eq_false :
    ∀ n k ct, ctSpace n ct = false → decrypt n k ct = none := by simp

namespace SymmetricCipher

attribute [program_certificate] keyGen_ppt encrypt_ppt decrypt_polyTime

/-- `E.keyGen` composed with a plain polynomial-time parameter selector is uniformly strict PPT. -/
@[program_certificate, fun_prop]
theorem isPPTOn_keyGen_comp (E : SymmetricCipher) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    IsPPTOn encIn encBits (fun a => E.keyGen (n a)) :=
  E.keyGen_ppt.preprocess hn

/-- `E.encrypt` composed with plain polynomial-time parameter, key, and message selectors is
uniformly strict PPT. -/
@[program_certificate, fun_prop]
theorem isPPTOn_encrypt_comp (E : SymmetricCipher) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {k msg : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hk : ComputableInPolyTime k encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits) :
    IsPPTOn encIn encBits (fun a => E.encrypt (n a) (k a) (msg a)) :=
  E.encrypt_ppt.preprocess (hn.prod (hk.prod hmsg))

/-- `E.decrypt` composed with plain polynomial-time parameter, key, and ciphertext selectors is
computable in plain polynomial time. -/
@[program_certificate, fun_prop]
theorem computableInPolyTime_decrypt_comp (E : SymmetricCipher)
    {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ} {k ct : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hk : ComputableInPolyTime k encIn encBits)
    (hct : ComputableInPolyTime ct encIn encBits) :
    ComputableInPolyTime (fun a => E.decrypt (n a) (k a) (ct a)) encIn (encOption encBits) :=
  E.decrypt_polyTime.comp (hn.prod (hk.prod hct))

/-! ### Adaptive Chosen-Plaintext Security (`cpaGame`, `INDCPA`) -/

/-- The adaptive symmetric IND-CPA experiment ([BonehShoup2023], Section 5.3, Attack Game 5.2):
`symmetricCPAGameOn` for `E.keyGen` and `E.encrypt`, admitting a pair `(m₀, m₁)` exactly when both
messages have `n` bits. A key `k ← E.keyGen n` is sampled, and each query on an admitted pair is
answered with `E.encrypt n k (if bit then m₁ else m₀)`; any other query is answered with `[]`. -/
noncomputable abbrev cpaGame (E : SymmetricCipher) (adversary : OracleDistinguisher)
    (bit : Bool) (n : ℕ) : ProbComp Bool :=
  symmetricCPAGameOn (fun n m₀ m₁ => (m₀.length == n) && (m₁.length == n)) E.keyGen E.encrypt
    adversary bit n

/-- Every encryption of an `n`-bit message under a key supported by `E.keyGen n` has exactly `len`
bits. Encrypt-then-MAC needs this to frame `(ciphertext, tag)` pairs canonically. -/
def CiphertextLength (E : SymmetricCipher) (n len : ℕ) : Prop :=
  ∀ k ∈ (ProbComp.eval (E.keyGen n)).support, ∀ msg, msg.length = n →
    ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length = len

/-- Every encryption of an `n`-bit message under a key supported by `E.keyGen n` has at most
`bound` bits; `exists_ciphertext_length_bound_of_length_eq` supplies a polynomial `bound`. -/
def CiphertextLengthLE (E : SymmetricCipher) (n bound : ℕ) : Prop :=
  ∀ k ∈ (ProbComp.eval (E.keyGen n)).support, ∀ msg, msg.length = n →
    ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ bound

/-- A unary polynomial-time ciphertext bound indexed separately by security parameter and message
length. The key is sampled at parameter `n`; the bound covers every message of length `ℓ`, even
outside the cipher's correctness and security domain of `n`-bit messages. -/
theorem exists_ciphertext_length_bound (E : SymmetricCipher) :
    ∃ ctBound : ℕ → ℕ → ℕ,
      ComputableInPolyTime (fun p : ℕ × ℕ => ctBound p.1 p.2)
        (encPair encUnary encUnary) encUnary ∧
      ∀ (n ℓ : ℕ) (k : List Bool), k ∈ (ProbComp.eval (E.keyGen n)).support →
        ∀ (msg : List Bool), msg.length = ℓ →
        ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n ℓ := by
  obtain ⟨ck, dk, hlenKey⟩ := E.keyGen_ppt.length_le
  obtain ⟨ce, de, hlenEnc⟩ := E.encrypt_ppt.length_le
  refine ⟨fun n ℓ => ce * (2 * n + ℓ + 2 * (ck * (n + 1) ^ dk) + 4) ^ de,
    by fun_prop, ?_⟩
  intro n ℓ k hk msg hmsg ct hct
  have hkLen := hlenKey n k hk
  have hctLen := hlenEnc (n, k, msg) ct hct
  simp only [encUnary_apply, List.length_replicate, encBits_apply] at hkLen
  simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
    hmsg] at hctLen
  exact hctLen.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (by lia) de))

/-- A unary polynomial-time ciphertext bound on `n`-bit messages at security parameter `n`,
derived as the diagonal of `exists_ciphertext_length_bound`. -/
theorem exists_ciphertext_length_bound_of_length_eq (E : SymmetricCipher) :
    ∃ ctBound : ℕ → ℕ,
      ComputableInPolyTime ctBound encUnary encUnary ∧ ∀ n, E.CiphertextLengthLE n (ctBound n) := by
  obtain ⟨bound, hbound, hctBound⟩ := E.exists_ciphertext_length_bound
  exact ⟨fun n => bound n n,
    hbound.comp (ComputableInPolyTime.id'.prod ComputableInPolyTime.id'),
    fun n => hctBound n n⟩

/-- A polynomial-time bound on encoded decryption replies, uniform over the actual key sampler.
It bounds rejection and successful empty messages without identifying their encodings. -/
theorem exists_decryption_length_bound (E : SymmetricCipher) :
    ∃ decBound : ℕ → List Bool → ℕ,
      ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
        (encPair encUnary encBits) encUnary ∧
      ∀ n k, k ∈ (ProbComp.eval (E.keyGen n)).support →
        ∀ ct, (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct := by
  obtain ⟨ck, dk, hlenKey⟩ := E.keyGen_ppt.length_le
  obtain ⟨cd, dd, hlenDec⟩ := E.decrypt_polyTime.polyBounded_length.exists_le
  let decBound : ℕ → List Bool → ℕ :=
    fun n ct => cd * (2 * n + 2 * (ck * (n + 1) ^ dk) + ct.length + 4) ^ dd
  have hdecBoundPoly : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary := by
    dsimp only [decBound]; fun_prop
  refine ⟨decBound, hdecBoundPoly, ?_⟩
  intro n k hk ct
  have hkLen := hlenKey n k hk
  have hdecLen := hlenDec (n, k, ct)
  simp only [encUnary_apply, List.length_replicate, encBits_apply] at hkLen
  simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hdecLen
  exact hdecLen.trans (Nat.mul_le_mul_left cd (Nat.pow_le_pow_left (by lia) dd))

/-- The symmetric CPA experiment is uniformly strict PPT in the unary security parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_cpaGame (E : SymmetricCipher) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn encUnary encBool (E.cpaGame adversary bit) := by
  obtain ⟨c, d, hlen⟩ := E.encrypt_ppt.length_le
  let reply : ℕ × List Bool → Unit × List Bool → ProbComp (List Bool) := fun caller =>
    symmetricCPAReplyOn (fun n m₀ m₁ => (m₀.length == n) && (m₁.length == n)) E.encrypt
      caller.1 caller.2 bit
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hreq : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) => p.2.1.2)
      EIn encBits := by
    dsimp only [EIn]; fun_prop
  have hn : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) => p.1.1)
      EIn encUnary := by
    dsimp only [EIn]; fun_prop
  have hm0 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) => unframe p.2.1.2)
      EIn encBits :=
    ComputableInPolyTime.unframe.comp hreq
  have hm1 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) => dropFrame p.2.1.2)
      EIn encBits :=
    ComputableInPolyTime.dropFrame.comp hreq
  have hcond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    fun_prop
  have hmsg : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
      EIn encBits := by
    cases bit <;> simpa using (by first | exact hm1 | exact hm0)
  have hencArg : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        (p.1.1, p.1.2, if bit then dropFrame p.2.1.2 else unframe p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) :=
    ComputableInPolyTime.prod hn
      (ComputableInPolyTime.prod (by dsimp only [EIn]; fun_prop) hmsg)
  have hreply : IsPPTOn EIn encBits
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Unit) => reply pair.1 pair.2.1) := by
    dsimp only [reply, symmetricCPAReplyOn]
    exact IsPPTOn.cond hcond (E.encrypt_ppt.preprocess hencArg)
      (ComputableInPolyTime.const []).isPPTOn
  have horacle : IsPPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        StateT.lift (reply pair.1 pair.2.1) pair.2.2) := by
    simpa only [StateT.lift] using hreply.bind_with
      ((ComputableInPolyTime.prod (ComputableInPolyTime.snd _ _)
        (ComputableInPolyTime.const ())).isPPTOn)
  have hrun := hadversary.isPPTOn_runState
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (oracle := fun caller request => StateT.lift (reply caller request))
    (initial := fun _ => ())
    (resources := fun caller _ =>
      c * (3 * caller.1 + 2 * caller.2.length + 4) ^ d + 1)
    (by fun_prop) horacle (ComputableInPolyTime.const ())
    (fun _ _ => True) (fun _ => trivial) (by fun_prop) (by
      intro caller request _ _ result hresult
      dsimp only [reply, symmetricCPAReplyOn, StateT.lift] at hresult
      by_cases hlenEq : ((unframe request.2).length == caller.1 &&
          (dropFrame request.2).length == caller.1) = true
      · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
          PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
        obtain ⟨ct, hct, rfl⟩ := hresult
        simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
        have hmbLen :
            (if bit then dropFrame request.2 else unframe request.2).length = caller.1 := by
          cases bit <;> simp [hlenEq]
        have hctLen := hlen
          (caller.1, caller.2, if bit then dropFrame request.2 else unframe request.2) ct hct
        simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
          hmbLen] at hctLen
        have hbound : ct.length ≤ c * (3 * caller.1 + 2 * caller.2.length + 4) ^ d :=
          hctLen.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia) d))
        exact ⟨trivial, by lia, by lia⟩
      · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind,
          ProbComp.eval_pure, PMF.pure_bind, PMF.mem_support_pure_iff] at hresult
        subst result
        exact ⟨trivial, by simp, by lia⟩)
  have hgame : E.cpaGame adversary bit = fun n => E.keyGen n >>= fun k =>
      Prod.fst <$> ((adversary n []).runState fun request =>
        StateT.lift (reply (n, k) request)).run () := by
    funext n
    simp only [cpaGame, symmetricCPAGameOn, ProbOracleComp.runState_lift, Functor.map_map,
      id_map', reply]
  rw [hgame]
  exact E.keyGen_ppt.bind_with (hrun.map (ComputableInPolyTime.fst _ _))

/-- The symmetric CPA experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_cpaGame (E : SymmetricCipher) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPT encBool (fun n _ => E.cpaGame adversary bit n) :=
  ((E.isPPTOn_cpaGame hadversary bit).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Adaptive chosen-plaintext security (`INDCPA`) for a symmetric cipher ([BonehShoup2023],
Section 5.3, Attack Game 5.2 and Definition 5.2): `SymmetricINDCPAOn` on pairs of `n`-bit
messages, so every uniform strict `IsOraclePPT encBool` distinguisher has negligible advantage
between `E.cpaGame adversary false` and `E.cpaGame adversary true`. -/
abbrev INDCPA (E : SymmetricCipher) : Prop :=
  SymmetricINDCPAOn (fun n m₀ m₁ => (m₀.length == n) && (m₁.length == n)) E.keyGen E.encrypt

/-- Stateful one-time left-or-right CPA encryption oracle ([BonehShoup2023], Section 2.2,
Attack Game 2.1 and Definition 2.2; Section 9.1.1, Definition 9.4, printed p. 360): answers at most
one valid `n`-bit left-or-right encryption query (`!alreadyQueried && m0.length == n &&
m1.length == n`), transitioning `alreadyQueried` from `false` to `true`, and returns `[]` on all
subsequent or malformed queries. -/
noncomputable def oneTimeCPAEncryptionOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Unit × List Bool) : StateT Bool ProbComp (List Bool) :=
  fun alreadyQueried =>
    let m0 := unframe request.2
    let m1 := dropFrame request.2
    if !alreadyQueried && (m0.length == n) && (m1.length == n) then do
      let ct ← E.encrypt n k (if bit then m1 else m0)
      return (ct, true)
    else
      return ([], alreadyQueried)

/-- The one-time symmetric CPA (semantic security) experiment ([BonehShoup2023], Section 2.2,
Attack Game 2.1 and Section 9.1.1, Definition 9.4): sample `k ← E.keyGen n` and run `adversary n []`
against `E.oneTimeCPAEncryptionOracle n k bit` starting from `alreadyQueried = false`. -/
noncomputable def cpaOneTimeGame (E : SymmetricCipher) (adversary : OracleDistinguisher)
    (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.oneTimeCPAEncryptionOracle n k bit)) (adversary n [])).run false
  return out.1

/-- Running an oracle-PPT distinguisher against `oneTimeCPAEncryptionOracle` is uniformly strict PPT
in `(n, k)` for each challenge bit `bit`. -/
@[program_certificate]
theorem isPPTOn_run_oneTimeCPAEncryptionOracle (E : SymmetricCipher)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn (encPair encUnary encBits) (encPair encBool encBool)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.oneTimeCPAEncryptionOracle caller.1 caller.2 bit))
          (adversary caller.1 [])).run false) := by
  obtain ⟨c, d, hlen⟩ := E.encrypt_ppt.length_le
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) encBool)
  have hreq : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => p.2.1.2)
      EIn encBits := by
    dsimp only [EIn]; fun_prop
  have hn : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => p.1.1)
      EIn encUnary := by
    dsimp only [EIn]; fun_prop
  have hstate : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => p.2.2)
      EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hm0 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => unframe p.2.1.2)
      EIn encBits :=
    ComputableInPolyTime.unframe.comp hreq
  have hm1 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => dropFrame p.2.1.2)
      EIn encBits :=
    ComputableInPolyTime.dropFrame.comp hreq
  have hcond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        !p.2.2 && ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    fun_prop
  have hmsg : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
      EIn encBits := by
    cases bit <;> simpa using (by first | exact hm1 | exact hm0)
  have hencArg : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        (p.1.1, p.1.2, if bit then dropFrame p.2.1.2 else unframe p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) :=
    ComputableInPolyTime.prod hn
      (ComputableInPolyTime.prod (by dsimp only [EIn]; fun_prop) hmsg)
  have hyes : IsPPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => do
        let ct ← E.encrypt p.1.1 p.1.2 (if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
        return (ct, true)) :=
    (E.encrypt_ppt.preprocess hencArg).bind_with
      ((ComputableInPolyTime.prod (by fun_prop)
        (ComputableInPolyTime.const true)).isPPTOn)
  have hno : IsPPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const []) hstate).isPPTOn
  have hhandler : IsPPTOn EIn (encPair encBits encBool)
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        E.oneTimeCPAEncryptionOracle pair.1.1 pair.1.2 bit pair.2.1 pair.2.2) := by
    unfold oneTimeCPAEncryptionOracle
    exact IsPPTOn.cond hcond hyes hno
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => false)
    (resources := fun caller _ =>
      c * (3 * caller.1 + 2 * caller.2.length + 4) ^ d + 1)
    (by fun_prop) hhandler (ComputableInPolyTime.const false)
    (fun _ _ => True) (fun _ => trivial) (by fun_prop)
  intro caller request alreadyQueried _ result hresult
  unfold oneTimeCPAEncryptionOracle at hresult
  by_cases hlenEq : (!alreadyQueried && ((unframe request.2).length == caller.1) &&
      ((dropFrame request.2).length == caller.1)) = true
  · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨ct, hct, rfl⟩ := hresult
    simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
    have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = caller.1 := by
      cases bit <;> simp [hlenEq]
    have hctLen := hlen (caller.1, caller.2, if bit then dropFrame request.2 else unframe request.2)
      ct hct
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
      hmbLen] at hctLen
    have hbound : ct.length ≤ c * (3 * caller.1 + 2 * caller.2.length + 4) ^ d :=
      hctLen.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia) d))
    exact ⟨trivial, by lia, by simp [encBool_apply]⟩
  · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
      PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by simp [encBool_apply]⟩

/-- The one-time symmetric CPA experiment is uniformly strict PPT in the unary security
parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_cpaOneTimeGame (E : SymmetricCipher) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn encUnary encBool (E.cpaOneTimeGame adversary bit) := by
  have hrun := E.isPPTOn_run_oneTimeCPAEncryptionOracle hadversary bit
  unfold cpaOneTimeGame
  exact E.keyGen_ppt.bind_with (hrun.bind (ComputableInPolyTime.fst _ _).isPPTOn)

/-- The one-time symmetric CPA experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_cpaOneTimeGame (E : SymmetricCipher) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPT encBool (fun n _ => E.cpaOneTimeGame adversary bit n) :=
  ((E.isPPTOn_cpaOneTimeGame hadversary bit).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- One-time chosen-plaintext security (semantic security under a single encryption query,
`OneTimeINDCPA`) for a symmetric cipher ([BonehShoup2023], Section 2.2, Attack Game 2.1 and
Definition 2.2; Section 9.1.1, Definition 9.4, printed p. 360): every uniform strict
`IsOraclePPT encBool` distinguisher has negligible advantage between
`E.cpaOneTimeGame adversary false` and `E.cpaOneTimeGame adversary true`. -/
def OneTimeINDCPA (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.cpaOneTimeGame adversary false n))
    (fun adversary n => ProbComp.eval (E.cpaOneTimeGame adversary true n))
    (IsOraclePPT encBool)

/-- Stateful filter handler that forwards at most one valid `n`-bit CPA query to an external
multi-query CPA encryption oracle (truncating replies to `ctBound`). -/
noncomputable def cpaOneTimeFilterHandler (n ctBound : ℕ) (request : Unit × List Bool) :
    StateT Bool (WordOracleComp Unit) (List Bool) :=
  fun alreadyQueried =>
    let m0 := unframe request.2
    let m1 := dropFrame request.2
    if !alreadyQueried && (m0.length == n) && (m1.length == n) then
      (fun ct => (ct, true)) <$> (List.take ctBound <$> ProbOracleComp.query ((), request.2))
    else
      pure ([], alreadyQueried)

/-- Reduction from `cpaOneTimeGame` to `cpaGame`: run `adversary n []` against
`cpaOneTimeFilterHandler n (ctBound n)` starting from `alreadyQueried = false`. -/
noncomputable def cpaLimitToOneQuery (ctBound : ℕ → ℕ) (adversary : OracleDistinguisher) :
    OracleDistinguisher :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (cpaOneTimeFilterHandler n (ctBound n)))
      (adversary n [])).run false
    return out.1

/-- `cpaLimitToOneQuery` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_cpaLimitToOneQuery {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (cpaLimitToOneQuery ctBound adversary) := by
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) encBool)
  have hreq : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => p.2.1.2)
      EIn encBits := by
    dsimp only [EIn]; fun_prop
  have hn : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => p.1.1)
      EIn encUnary := by
    dsimp only [EIn]; fun_prop
  have hstate : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => p.2.2)
      EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hcond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        !p.2.2 && ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    fun_prop
  have hquery : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        (fun ct => (ct, true)) <$>
          (List.take (ctBound p.1.1) <$> ProbOracleComp.query ((), p.2.1.2))) := by ppt
  have hnoReply : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      hstate).isOraclePPTOn (Operation := Unit)
  have hhandler : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        cpaOneTimeFilterHandler pair.1.1 (ctBound pair.1.1) pair.2.1 pair.2.2) := by
    unfold cpaOneTimeFilterHandler
    exact IsOraclePPTOn.cond hcond hquery hnoReply
  have hres : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => ctBound pair.1.1 + 1)
      (encPair (encPair encUnary encBits) encBits) encUnary :=
    ComputableInPolyTime.unary_add' (hctBound.comp (by fun_prop)) (ComputableInPolyTime.const 1)
  have hrun : IsOraclePPTOn (encPair encUnary encBits) (encPair encBool encBool)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (cpaOneTimeFilterHandler caller.1 (ctBound caller.1)))
          (adversary caller.1 [])).run false) := by
    apply hadversary.run_interpret_preprocess_open
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => false)
      (resources := fun caller _ => ctBound caller.1 + 1)
      (by fun_prop) hhandler (ComputableInPolyTime.const false)
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request alreadyQueried _ result hresult
    unfold cpaOneTimeFilterHandler at hresult
    dsimp only at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨ct, hct, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      obtain ⟨rawCt, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hct
      exact ⟨trivial, (List.length_take_le _ _).trans (by lia), by simp [encBool_apply]⟩
    · cases OracleComp.eq_of_mem_supportWith_pure hresult
      exact ⟨trivial, by simp, by simp [encBool_apply]⟩
  unfold cpaLimitToOneQuery
  simpa only [bind_pure_comp] using (hrun.map (ComputableInPolyTime.fst _ _)).isOraclePPT

/-- When `ctBound n` bounds all ciphertext lengths produced by `E.encrypt n k` on `n`-bit messages,
running `cpaLimitToOneQuery ctBound adversary` in `cpaGame` has the exact same output distribution
as `cpaOneTimeGame adversary`. -/
theorem eval_cpaGame_cpaLimitToOneQuery (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval (E.cpaGame (cpaLimitToOneQuery ctBound adversary) bit n) =
      ProbComp.eval (E.cpaOneTimeGame adversary bit n) := by
  simp only [cpaGame, symmetricCPAGameOn, ProbOracleComp.run, cpaOneTimeGame, cpaLimitToOneQuery,
    runWith_norm, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  congr 2
  funext request alreadyQueried
  simp only [oneTimeCPAEncryptionOracle, cpaOneTimeFilterHandler, StateT.run]
  by_cases hcond : (!alreadyQueried && ((unframe request.2).length == n) &&
      ((dropFrame request.2).length == n)) = true
  · simp only [hcond, ↓reduceIte, OracleComp.evalWith_map,
      ProbOracleComp.evalWith_sumHandler_query, symmetricCPAReplyOn]
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    have hlenEq : (((unframe request.2).length == n) &&
        ((dropFrame request.2).length == n)) = true := by
      simp [hcond.1.2, hcond.2]
    simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_comp]
    have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
      cases bit <;> simp [hcond.1.2, hcond.2]
    apply PMF.bind_congr_on_support
    intro ct hct
    simp only [Function.comp_apply, List.take_of_length_le (hctBound k hk _ hmbLen ct hct)]
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
      OracleComp.evalWith_pure]

/-- Multi-query `INDCPA` security implies one-time `OneTimeINDCPA` security. -/
theorem INDCPA.oneTimeINDCPA {E : SymmetricCipher} (hcpa : E.INDCPA) :
    E.OneTimeINDCPA := by
  intro adversary hadversary
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have hneg := hcpa (cpaLimitToOneQuery ctBound adversary)
    (isOraclePPT_cpaLimitToOneQuery hctBoundPoly hadversary)
  refine hneg.congr fun n => ?_
  dsimp only
  rw [eval_cpaGame_cpaLimitToOneQuery E ctBound adversary false n (hctBound n),
    eval_cpaGame_cpaLimitToOneQuery E ctBound adversary true n (hctBound n)]

/-! #### Impossibility of Zero-Expansion CPA Security (Boneh–Shoup Example 5.1 & Exercise 5.10(a))
-/

/-- **Zero ciphertext expansion forces deterministic encryption** ([BonehShoup2023],
Exercise 5.10(a), printed p. 211): if every supported ciphertext of an `n`-bit message under a
supported key `ke` at parameter `n` has length `n`, then decryption completeness
(`E.decrypt_encrypt`) gives an injection from the `2^n` plaintexts `BitString n` into `BitString n`
by choosing one supported ciphertext per plaintext; by finiteness of `BitString n`, this map is
surjective, forcing all supported ciphertexts of any `n`-bit plaintext `msg` under `ke` to
coincide. -/
theorem encrypt_eq_of_ciphertext_length_eq (E : SymmetricCipher) {n : ℕ} {ke : List Bool}
    (hke : ke ∈ (ProbComp.eval (E.keyGen n)).support)
    (hctLen : ∀ msg : List Bool, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n)
    {msg : List Bool} (hmsg : msg.length = n)
    {c₁ c₂ : List Bool}
    (hc₁ : c₁ ∈ (ProbComp.eval (E.encrypt n ke msg)).support)
    (hc₂ : c₂ ∈ (ProbComp.eval (E.encrypt n ke msg)).support) :
    c₁ = c₂ := by
  let toBS : (l : List Bool) → l.length = n → BitString n :=
    fun l hl i => l[i.val]'(hl ▸ i.isLt)
  have hofFn_toBS (l : List Bool) (hl : l.length = n) : List.ofFn (toBS l hl) = l := by
    apply List.ext_getElem (by simp [hl])
    intro i hi₁ hi₂
    simp [toBS]
  let chooseCt (v : BitString n) : List Bool :=
    (ProbComp.eval (E.encrypt n ke (List.ofFn v))).support_nonempty.some
  have hchooseMem (v : BitString n) :
      chooseCt v ∈ (ProbComp.eval (E.encrypt n ke (List.ofFn v))).support :=
    (ProbComp.eval (E.encrypt n ke (List.ofFn v))).support_nonempty.some_mem
  have hchooseLen (v : BitString n) : (chooseCt v).length = n :=
    hctLen (List.ofFn v) (List.length_ofFn) (chooseCt v) (hchooseMem v)
  have hchooseDec (v : BitString n) : E.decrypt n ke (chooseCt v) = some (List.ofFn v) :=
    E.decrypt_encrypt n ke hke (List.ofFn v) (List.length_ofFn) (chooseCt v) (hchooseMem v)
  let g : BitString n → BitString n := fun v => toBS (chooseCt v) (hchooseLen v)
  have hgInj : Function.Injective g := by
    intro v₁ v₂ hgv
    have hctEq : chooseCt v₁ = chooseCt v₂ := by
      rw [← hofFn_toBS (chooseCt v₁) (hchooseLen v₁),
        ← hofFn_toBS (chooseCt v₂) (hchooseLen v₂)]
      exact congrArg List.ofFn hgv
    have hdecEq : some (List.ofFn v₁) = some (List.ofFn v₂) := by
      rw [← hchooseDec v₁, ← hchooseDec v₂, hctEq]
    exact List.ofFn_injective (Option.some.inj hdecEq)
  have hgSurj : Function.Surjective g := Finite.injective_iff_surjective.mp hgInj
  have huniq (c : List Bool) (hc : c ∈ (ProbComp.eval (E.encrypt n ke msg)).support) :
      c = chooseCt (toBS msg hmsg) := by
    have hlen : c.length = n := hctLen msg hmsg c hc
    obtain ⟨v, hv⟩ := hgSurj (toBS c hlen)
    have hcv : chooseCt v = c := by
      rw [← hofFn_toBS (chooseCt v) (hchooseLen v), ← hofFn_toBS c hlen]
      exact congrArg List.ofFn hv
    have hdec : some (List.ofFn v) = some msg := by
      rw [← hchooseDec v, hcv, E.decrypt_encrypt n ke hke msg hmsg c hc]
    have hvEq : v = toBS msg hmsg := by
      apply List.ofFn_injective
      rw [Option.some.inj hdec, hofFn_toBS msg hmsg]
    rw [← hvEq, hcv]
  rw [huniq c₁ hc₁, huniq c₂ hc₂]

/-- Under zero ciphertext expansion (`E.CiphertextLength n n`), encryption of any `n`-bit plaintext
`msg` under any supported key `ke` evaluates to a point mass `PMF.pure c₀` ([BonehShoup2023],
Section 5.8, Exercise 5.10(a), printed p. 211). -/
theorem exists_eval_encrypt_eq_pure_of_ciphertext_length_eq (E : SymmetricCipher) {n : ℕ}
    (hctLen : E.CiphertextLength n n) {ke : List Bool}
    (hke : ke ∈ (ProbComp.eval (E.keyGen n)).support) {msg : List Bool} (hmsg : msg.length = n) :
    ∃ c₀, ProbComp.eval (E.encrypt n ke msg) = PMF.pure c₀ := by
  obtain ⟨c₀, hc₀⟩ := (ProbComp.eval (E.encrypt n ke msg)).support_nonempty
  refine ⟨c₀, ?_⟩
  simpa [PMF.map_id] using (PMF.map_eq_pure_iff (f := id) (b := c₀)).mpr fun c hc =>
    E.encrypt_eq_of_ciphertext_length_eq hke (hctLen ke hke) hmsg hc hc₀

/-- Two-query CPA distinguisher ([BonehShoup2023], Section 5.3, Example 5.1, printed p. 182):
queries `(0^n, 1^n)` followed by `(0^n, 0^n)`, truncates each reply to `ctBound n` bits, and
outputs `true` iff the two truncated replies coincide (`c₁ == c₂`). -/
def detCPAAdversary (ctBound : ℕ → ℕ) : OracleDistinguisher :=
  fun n _ => do
    let m0 := List.replicate n false
    let m1 := List.replicate n true
    let c₁ ← List.take (ctBound n) <$> ProbOracleComp.query ((), encPair encBits encBits (m0, m1))
    let c₂ ← List.take (ctBound n) <$> ProbOracleComp.query ((), encPair encBits encBits (m0, m0))
    return (c₁ == c₂)

/-- `detCPAAdversary ctBound` is uniformly strict oracle-PPT whenever `ctBound` is computable in
unary polynomial time. -/
theorem isOraclePPT_detCPAAdversary {ctBound : ℕ → ℕ}
    (hbound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBool (detCPAAdversary ctBound) := by
  ppt [detCPAAdversary]

private theorem eval_cpaGame_detCPAAdversary_false (E : SymmetricCipher) (ctBound : ℕ → ℕ) (n : ℕ)
    (hdet : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∃ c, ProbComp.eval (E.encrypt n k (List.replicate n false)) = PMF.pure c) :
    ProbComp.eval (E.cpaGame (detCPAAdversary ctBound) false n) = PMF.pure true := by
  simp only [cpaGame, symmetricCPAGameOn, detCPAAdversary, ProbOracleComp.run_bind,
    ProbOracleComp.run_map, ProbOracleComp.run_query, ProbOracleComp.run_pure, ProbComp.eval_bind,
    ProbComp.eval_map, ProbComp.eval_pure]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk => ?_
  obtain ⟨c, hc⟩ := hdet k hk
  simp [symmetricCPAReplyOn, hc]

private theorem eval_cpaGame_detCPAAdversary_true (E : SymmetricCipher) (ctBound : ℕ → ℕ) {n : ℕ}
    (hn : 1 ≤ n) (hctLen : E.CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval (E.cpaGame (detCPAAdversary ctBound) true n) = PMF.pure false := by
  simp only [cpaGame, symmetricCPAGameOn, detCPAAdversary, ProbOracleComp.run_bind,
    ProbOracleComp.run_map, ProbOracleComp.run_query, ProbOracleComp.run_pure, ProbComp.eval_bind,
    ProbComp.eval_map, ProbComp.eval_pure]
  have hneMsg : List.replicate n true ≠ List.replicate n false := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : n ≠ 0)
    simp
  refine PMF.bind_eq_pure_of_forall_mem_support fun ke hke => ?_
  simp only [symmetricCPAReplyOn, unframe_encPair_encBits, dropFrame_encPair_encBits,
    List.length_replicate, beq_self_eq_true, Bool.and_self, ↓reduceIte, PMF.bind_map,
    Function.comp_def]
  refine PMF.bind_eq_pure_of_forall_mem_support fun c₁ hc₁ => ?_
  have hc₁Len : c₁.length ≤ ctBound n :=
    hctLen ke hke (List.replicate n true) List.length_replicate c₁ hc₁
  refine PMF.bind_eq_pure_of_forall_mem_support fun c₂ hc₂ => ?_
  have hc₂Len : c₂.length ≤ ctBound n :=
    hctLen ke hke (List.replicate n false) List.length_replicate c₂ hc₂
  have hne : c₁ ≠ c₂ := by
    intro hEq
    have hdec1 := E.decrypt_encrypt n ke hke (List.replicate n true) List.length_replicate c₁ hc₁
    have hdec2 := E.decrypt_encrypt n ke hke (List.replicate n false) List.length_replicate c₂ hc₂
    rw [hEq, hdec2] at hdec1
    exact hneMsg (Option.some.inj hdec1).symm
  rw [List.take_of_length_le hc₁Len, List.take_of_length_le hc₂Len]
  simp [beq_eq_false_iff_ne.mpr hne]

/-- At any security parameter `1 ≤ n` where `ctBound n` bounds ciphertext lengths on `n`-bit
messages and `E.encrypt n k (0^n)` is deterministic under every supported key `k`,
`detCPAAdversary ctBound` achieves CPA advantage `1`
([BonehShoup2023], Section 5.3, Example 5.1, printed p. 182). -/
theorem advantage_cpaGame_detCPAAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ) {n : ℕ}
    (hn : 1 ≤ n) (hctLen : E.CiphertextLengthLE n (ctBound n))
    (hdet : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∃ c, ProbComp.eval (E.encrypt n k (List.replicate n false)) = PMF.pure c) :
    Game.advantage (ProbComp.eval (E.cpaGame (detCPAAdversary ctBound) false n))
      (ProbComp.eval (E.cpaGame (detCPAAdversary ctBound) true n)) = 1 := by
  rw [eval_cpaGame_detCPAAdversary_false E ctBound n hdet,
    eval_cpaGame_detCPAAdversary_true E ctBound hn hctLen, Game.advantage]
  simp [Game.succProbability]

/-- **No deterministic symmetric cipher is CPA-secure** ([BonehShoup2023], Section 5.3, Example 5.1,
printed p. 182): if from some security parameter `n₀` onward, `E.encrypt n k (0^n)` is a point mass
for every key `k` in the support of `E.keyGen n`, then `E` cannot satisfy `INDCPA`. -/
theorem not_indcpa_of_deterministic (E : SymmetricCipher) (n₀ : ℕ)
    (hdet : ∀ n, n₀ ≤ n → ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∃ c, ProbComp.eval (E.encrypt n k (List.replicate n false)) = PMF.pure c) :
    ¬ E.INDCPA := by
  intro hcpa
  obtain ⟨ctBound, hpoly, hctLen⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have hneg := (hcpa (detCPAAdversary ctBound) (isOraclePPT_detCPAAdversary hpoly)).shift
    (max n₀ 1)
  have hcongr : Negligible (fun _ : ℕ => (1 : ℝ≥0)) :=
    hneg.congr fun n =>
      advantage_cpaGame_detCPAAdversary E ctBound (by lia) (hctLen _) (hdet _ (by lia))
  exact not_negligible_const one_ne_zero hcongr

/-- **No zero-expansion symmetric cipher is CPA-secure** ([BonehShoup2023], Section 5.8,
Exercise 5.10(a), printed p. 211): if for every security parameter `n`, every supported key `ke`,
and every `n`-bit message `msg`, every supported ciphertext of `msg` has length `n`, then `E`
cannot satisfy `INDCPA` (proved via Example 5.1's deterministic-cipher attack
`not_indcpa_of_deterministic`). -/
theorem not_indcpa_of_ciphertext_length_eq (E : SymmetricCipher)
    (hctLen : ∀ n, E.CiphertextLength n n) :
    ¬ E.INDCPA :=
  E.not_indcpa_of_deterministic 0 fun n _ _ hke =>
    E.exists_eval_encrypt_eq_pure_of_ciphertext_length_eq (hctLen n) hke List.length_replicate

/-! ### Ciphertext Integrity and Authenticated Encryption (`ciGame`, `CiphertextIntegrity`,
`AuthenticatedEncryption`) -/

/-- Stateful encryption oracle for the ciphertext-integrity game ([BonehShoup2023], Section 9.1,
Attack Game 9.1): if `request.2.length == n`, encrypt `request.2` under `k`, prepend the resulting
ciphertext to `queriedCiphertexts`, and return it; otherwise return `[]` without modifying the
ciphertext log. -/
noncomputable def ciEncryptionOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.2.length == n then do
      let ct ← E.encrypt n k request.2
      return (ct, ct :: queriedCiphertexts)
    else
      return ([], queriedCiphertexts)

/-- The ciphertext-integrity experiment ([BonehShoup2023], Section 9.1, Attack Game 9.1):
sample `k ← E.keyGen n`, run `adversary n []` with oracle access to `E.ciEncryptionOracle n k`, and
accept when the adversary outputs a candidate ciphertext `ct` that was never returned by the
encryption oracle (`!out.2.contains out.1`) and decrypts without rejection
(`(E.decrypt n k out.1).isSome`).

This is Attack Game 9.1 on the ciphertext space `C = E.ctSpace n`: a candidate outside `C`
decrypts to `none` (`decrypt_eq_none_of_ctSpace_eq_false`) and loses, so the adversary wins
exactly when it outputs a fresh word of `C` that decrypts, which is the source's winning event. The
same holds for `ciOneTimeGame`. -/
noncomputable def ciGame (E : SymmetricCipher) (adversary : CIAdversary) (n : ℕ) :
    ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.ciEncryptionOracle n k)) (adversary n [])).run []
  return !out.2.contains out.1 && (E.decrypt n k out.1).isSome

/-! #### Encryption-admission policies

The full-query and one-time ciphertext-integrity and chosen-ciphertext games differ only in when
an encryption query is answered: always, or only while no ciphertext has been returned. The
private oracles `ciEncryptionOracleOn`, `ccaOracleOn` and `ccaRejectOracleOn` take this admission
policy `allow` on the ciphertext log as a parameter, so that the PPT certificates and the
bad-event argument of Theorem 9.1 are proved once. The public full-query oracles are the
instances at `fun _ => true` by definition, and the one-time oracles are equal to the instances at
`List.isEmpty`. -/

/-- `ciEncryptionOracle` answering an encryption query only when `allow` admits the current
ciphertext log. -/
private noncomputable def ciEncryptionOracleOn (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (n : ℕ) (k : List Bool) (request : Unit × List Bool) :
    StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if allow queriedCiphertexts && (request.2.length == n) then do
      let ct ← E.encrypt n k request.2
      return (ct, ct :: queriedCiphertexts)
    else
      return ([], queriedCiphertexts)

/-- `ciGame` against `ciEncryptionOracleOn allow`. -/
private noncomputable def ciGameOn (E : SymmetricCipher) (allow : List (List Bool) → Bool)
    (adversary : CIAdversary) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.ciEncryptionOracleOn allow n k)) (adversary n [])).run []
  return !out.2.contains out.1 && (E.decrypt n k out.1).isSome

private theorem ciEncryptionOracle_eq_on (E : SymmetricCipher) :
    E.ciEncryptionOracle = E.ciEncryptionOracleOn (fun _ => true) :=
  rfl

private theorem ciGame_eq_on (E : SymmetricCipher) : E.ciGame = E.ciGameOn (fun _ => true) := rfl

/-- Running an oracle-PPT CI adversary against `ciEncryptionOracleOn allow` is uniformly strict
PPT in `(n, k)` when the policy is computable in polynomial time. -/
private theorem isPPTOn_run_ciEncryptionOracleOn (E : SymmetricCipher)
    {allow : List (List Bool) → Bool}
    (hallow : ComputableInPolyTime allow (encList encBits) encBool)
    {adversary : CIAdversary} (hadversary : IsOraclePPT encBits adversary) :
    IsPPTOn (encPair encUnary encBits) (encPair encBits (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.ciEncryptionOracleOn allow caller.1 caller.2)) (adversary caller.1 [])).run []) := by
  obtain ⟨c, d, hlen⟩ := E.encrypt_ppt.length_le
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) (encList encBits))
  have hcond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        allow p.2.2 && (p.2.1.2.length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hencArg : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        (p.1.1, p.1.2, p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EIn]; fun_prop
  have hyes : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) => do
        let ct ← E.encrypt p.1.1 p.1.2 p.2.1.2
        return (ct, ct :: p.2.2)) :=
    (E.encrypt_ppt.preprocess hencArg).bind_with
      ((by dsimp only [EIn]; fun_prop : ComputableInPolyTime
        (fun q : ((ℕ × List Bool) × ((Unit × List Bool) × List (List Bool))) × List Bool =>
          (q.2, q.2 :: q.1.2.2))
        (encPair EIn encBits) (encPair encBits (encList encBits))).isPPTOn)
  have hno : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isPPTOn
  have hhandler : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        E.ciEncryptionOracleOn allow pair.1.1 pair.1.2 pair.2.1 pair.2.2) := by
    unfold ciEncryptionOracleOn
    exact IsPPTOn.cond hcond hyes hno
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun caller query =>
      2 * (c * (2 * caller.1 + 2 * caller.2.length + query.length + 4) ^ d) + 2)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by fun_prop)
  intro caller request queried _ result hresult
  unfold ciEncryptionOracleOn at hresult
  split_ifs at hresult
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨ct, hct, rfl⟩ := hresult
    have hctLen := hlen (caller.1, caller.2, request.2) ct hct
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hctLen
    have hbound : ct.length ≤ c * (2 * caller.1 + 2 * caller.2.length + request.2.length + 4) ^ d :=
      hctLen.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia) d))
    refine ⟨trivial, by lia, ?_⟩
    simp only [encList_cons, List.length_append, length_frame, encBits_apply]
    lia
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by lia⟩

/-- Running an oracle-PPT CI adversary against `ciEncryptionOracle` is uniformly strict PPT in
`(n, k)`. -/
@[program_certificate]
theorem isPPTOn_run_ciEncryptionOracle (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPTOn (encPair encUnary encBits) (encPair encBits (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.ciEncryptionOracle caller.1 caller.2)) (adversary caller.1 [])).run []) := by
  rw [ciEncryptionOracle_eq_on]
  exact E.isPPTOn_run_ciEncryptionOracleOn (by fun_prop) hadversary

private theorem computableInPolyTime_ciPost (E : SymmetricCipher) :
    ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        !pair.2.2.contains pair.2.1 && (E.decrypt pair.1.1 pair.1.2 pair.2.1).isSome)
      (encPair (encPair encUnary encBits) (encPair encBits (encList encBits))) encBool := by
  let EOut := encPair (encPair encUnary encBits) (encPair encBits (encList encBits))
  have hcontains : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        pair.2.2.contains pair.2.1)
      EOut encBool :=
    ComputableInPolyTime.contains
      (by dsimp only [EOut]; fun_prop) (by dsimp only [EOut]; fun_prop)
  have hdecArg : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        (pair.1.1, pair.1.2, pair.2.1))
      EOut (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EOut]; fun_prop
  have hdec : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        (E.decrypt pair.1.1 pair.1.2 pair.2.1).isSome)
      EOut encBool :=
    (E.decrypt_polyTime.comp hdecArg).optionIsSome
  exact ComputableInPolyTime.bool_and.comp
    ((ComputableInPolyTime.bool_not.comp hcontains).prod hdec)

/-- The ciphertext-integrity experiment is uniformly strict PPT in the unary security parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_ciGame (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPTOn encUnary encBool (E.ciGame adversary) := by
  have hrun := E.isPPTOn_run_ciEncryptionOracle hadversary
  unfold ciGame
  exact E.keyGen_ppt.bind_with (hrun.bind_with E.computableInPolyTime_ciPost.isPPTOn)

/-- The ciphertext-integrity experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_ciGame (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPT encBool (fun n _ => E.ciGame adversary n) :=
  ((E.isPPTOn_ciGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Ciphertext integrity (`CiphertextIntegrity`, or CI) for a symmetric cipher
([BonehShoup2023], Section 9.1, Attack Game 9.1 and Definition 9.1): every uniform strict
`IsOraclePPT encBits` adversary has negligible probability of outputting a fresh valid
ciphertext. -/
def CiphertextIntegrity (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.ciGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT encBits)

/-- Ciphertext integrity gives negligible winning probability in `ciGame` for every oracle-PPT CI
adversary. -/
theorem CiphertextIntegrity.negligible {E : SymmetricCipher} (h : E.CiphertextIntegrity)
    (adversary : CIAdversary) (hadversary : IsOraclePPT encBits adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (E.ciGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish `CiphertextIntegrity` by bounding every oracle-PPT CI adversary's winning
probability. -/
theorem CiphertextIntegrity.of_negligible {E : SymmetricCipher}
    (h : ∀ adversary, IsOraclePPT encBits adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (E.ciGame adversary n)))) :
    E.CiphertextIntegrity := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Authenticated encryption (`AuthenticatedEncryption`, or AE-security) for a symmetric cipher
([BonehShoup2023], Section 9.1, Definition 9.2): the cipher satisfies both `INDCPA` and
`CiphertextIntegrity`. -/
def AuthenticatedEncryption (E : SymmetricCipher) : Prop :=
  E.INDCPA ∧ E.CiphertextIntegrity

/-- Stateful one-time encryption oracle for the one-time ciphertext-integrity game
([BonehShoup2023], Section 9.1.1, Definition 9.3, printed p. 360): if no ciphertext has been
returned yet (`queriedCiphertexts.isEmpty`) and `request.2.length == n`, encrypt `request.2` under
`k`, record `[ct]`, and return `ct`; otherwise return `[]` without modifying
`queriedCiphertexts`. -/
noncomputable def oneTimeCIEncryptionOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if queriedCiphertexts.isEmpty && (request.2.length == n) then do
      let ct ← E.encrypt n k request.2
      return (ct, [ct])
    else
      return ([], queriedCiphertexts)

/-- The one-time ciphertext-integrity experiment ([BonehShoup2023], Section 9.1.1,
Definition 9.3, printed p. 360): sample `k ← E.keyGen n`, run `adversary n []` with oracle access
to `E.oneTimeCIEncryptionOracle n k`, and accept when the adversary outputs a candidate ciphertext
`ct` that was not returned by the encryption oracle (`!out.2.contains out.1`) and decrypts without
rejection (`(E.decrypt n k out.1).isSome`). -/
noncomputable def ciOneTimeGame (E : SymmetricCipher) (adversary : CIAdversary) (n : ℕ) :
    ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.oneTimeCIEncryptionOracle n k)) (adversary n [])).run []
  return !out.2.contains out.1 && (E.decrypt n k out.1).isSome

private theorem oneTimeCIEncryptionOracle_eq_on (E : SymmetricCipher) :
    E.oneTimeCIEncryptionOracle = E.ciEncryptionOracleOn List.isEmpty := by
  funext n k request queried
  cases queried <;> rfl

private theorem ciOneTimeGame_eq_on (E : SymmetricCipher) :
    E.ciOneTimeGame = E.ciGameOn List.isEmpty := by
  funext adversary n
  simp only [ciOneTimeGame, ciGameOn, oneTimeCIEncryptionOracle_eq_on]

/-- Running an oracle-PPT CI adversary against `oneTimeCIEncryptionOracle` is uniformly strict PPT
in `(n, k)`. -/
@[program_certificate]
theorem isPPTOn_run_oneTimeCIEncryptionOracle (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPTOn (encPair encUnary encBits) (encPair encBits (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.oneTimeCIEncryptionOracle caller.1 caller.2)) (adversary caller.1 [])).run []) := by
  rw [oneTimeCIEncryptionOracle_eq_on]
  exact E.isPPTOn_run_ciEncryptionOracleOn (by fun_prop) hadversary

/-- The one-time ciphertext-integrity experiment is uniformly strict PPT in the unary security
parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_ciOneTimeGame (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPTOn encUnary encBool (E.ciOneTimeGame adversary) := by
  have hrun := E.isPPTOn_run_oneTimeCIEncryptionOracle hadversary
  unfold ciOneTimeGame
  exact E.keyGen_ppt.bind_with (hrun.bind_with E.computableInPolyTime_ciPost.isPPTOn)

/-- The one-time ciphertext-integrity experiment is uniformly strict PPT, independently of unused
auxiliary input. -/
@[program_certificate]
theorem isPPT_ciOneTimeGame (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPT encBool (fun n _ => E.ciOneTimeGame adversary n) :=
  ((E.isPPTOn_ciOneTimeGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- One-time ciphertext integrity (`OneTimeCiphertextIntegrity`, or 1CI) for a symmetric cipher
([BonehShoup2023], Section 9.1.1, Definition 9.3, printed p. 360): every uniform strict
`IsOraclePPT encBits` adversary has negligible probability of outputting a fresh valid ciphertext
in `ciOneTimeGame`. -/
def OneTimeCiphertextIntegrity (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.ciOneTimeGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT encBits)

/-- One-time ciphertext integrity gives negligible winning probability in `ciOneTimeGame` for every
oracle-PPT CI adversary. -/
theorem OneTimeCiphertextIntegrity.negligible {E : SymmetricCipher}
    (h : E.OneTimeCiphertextIntegrity) (adversary : CIAdversary)
    (hadversary : IsOraclePPT encBits adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (E.ciOneTimeGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish `OneTimeCiphertextIntegrity` by bounding every oracle-PPT CI adversary's winning
probability in `ciOneTimeGame`. -/
theorem OneTimeCiphertextIntegrity.of_negligible {E : SymmetricCipher}
    (h : ∀ adversary, IsOraclePPT encBits adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (E.ciOneTimeGame adversary n)))) :
    E.OneTimeCiphertextIntegrity := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Stateful filter handler that forwards at most one valid `n`-bit CI encryption query to an
external multi-query CI encryption oracle (truncating replies to `ctBound`). -/
noncomputable def ciOneTimeFilterHandler (n ctBound : ℕ) (request : Unit × List Bool) :
    StateT Bool (WordOracleComp Unit) (List Bool) :=
  fun alreadyQueried =>
    if !alreadyQueried && (request.2.length == n) then
      (fun ct => (ct, true)) <$> (List.take ctBound <$> ProbOracleComp.query ((), request.2))
    else
      pure ([], alreadyQueried)

/-- Reduction from `ciOneTimeGame` to `ciGame`: run `adversary n []` against
`ciOneTimeFilterHandler n (ctBound n)` starting from `alreadyQueried = false`. -/
noncomputable def ciLimitToOneQuery (ctBound : ℕ → ℕ) (adversary : CIAdversary) : CIAdversary :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (ciOneTimeFilterHandler n (ctBound n)))
      (adversary n [])).run false
    return out.1

/-- `ciLimitToOneQuery` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_ciLimitToOneQuery {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {adversary : CIAdversary} (hadversary : IsOraclePPT encBits adversary) :
    IsOraclePPT encBits (ciLimitToOneQuery ctBound adversary) := by
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) encBool)
  have hcond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        !p.2.2 && (p.2.1.2.length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hquery : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        (fun ct => (ct, true)) <$>
          (List.take (ctBound p.1.1) <$> ProbOracleComp.query ((), p.2.1.2))) := by ppt
  have hnoReply : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Bool) => pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isOraclePPTOn (Operation := Unit)
  have hhandler : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Bool) =>
        ciOneTimeFilterHandler pair.1.1 (ctBound pair.1.1) pair.2.1 pair.2.2) := by
    unfold ciOneTimeFilterHandler
    exact IsOraclePPTOn.cond hcond hquery hnoReply
  have hres : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => ctBound pair.1.1 + 1)
      (encPair (encPair encUnary encBits) encBits) encUnary :=
    ComputableInPolyTime.unary_add' (hctBound.comp (by fun_prop)) (ComputableInPolyTime.const 1)
  have hrun : IsOraclePPTOn (encPair encUnary encBits) (encPair encBits encBool)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ciOneTimeFilterHandler caller.1 (ctBound caller.1)))
          (adversary caller.1 [])).run false) := by
    apply hadversary.run_interpret_preprocess_open
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => false)
      (resources := fun caller _ => ctBound caller.1 + 1)
      (by fun_prop) hhandler (ComputableInPolyTime.const false)
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request alreadyQueried _ result hresult
    unfold ciOneTimeFilterHandler at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨ct, hct, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      obtain ⟨rawCt, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hct
      exact ⟨trivial, (List.length_take_le _ _).trans (by lia), by simp [encBool_apply]⟩
    · cases OracleComp.eq_of_mem_supportWith_pure hresult
      exact ⟨trivial, by simp, by simp [encBool_apply]⟩
  unfold ciLimitToOneQuery
  simpa only [bind_pure_comp] using (hrun.map (ComputableInPolyTime.fst _ _)).isOraclePPT

/-- When `ctBound n` bounds all ciphertext lengths produced by `E.encrypt n k` on `n`-bit messages,
running `ciLimitToOneQuery ctBound adversary` in `ciGame` has the exact same output distribution as
`ciOneTimeGame adversary`. -/
theorem eval_ciGame_ciLimitToOneQuery (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : CIAdversary) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval (E.ciGame (ciLimitToOneQuery ctBound adversary) n) =
      ProbComp.eval (E.ciOneTimeGame adversary n) := by
  simp only [ciGame, ciOneTimeGame, ciLimitToOneQuery, runWith_norm, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  have hsim := ProbOracleComp.runWith_map_state
    (fun request queried =>
      ProbComp.eval (E.oneTimeCIEncryptionOracle n k request queried))
    (fun request state =>
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s))
          ((ciOneTimeFilterHandler n (ctBound n) request).run state.1) state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (fun queried : List (List Bool) => (!queried.isEmpty, queried))
    (fun request queried => by
      change (ProbComp.eval (E.oneTimeCIEncryptionOracle n k request queried)).map
          (fun x => (x.1, !x.2.isEmpty, x.2)) =
        (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s))
            (ciOneTimeFilterHandler n (ctBound n) request (!queried.isEmpty)) queried).map
          (fun result => (result.1.1, result.1.2, result.2))
      simp only [oneTimeCIEncryptionOracle, ciOneTimeFilterHandler, Bool.not_not]
      by_cases hcond : (queried.isEmpty && (request.2.length == n)) = true
      · simp only [hcond, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, Functor.map_map,
          ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ciEncryptionOracle]
        simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hcond
        rcases hcond with ⟨rfl, hmsgLen⟩
        have hlenEq : (request.2.length == n) = true := beq_iff_eq.mpr hmsgLen
        simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
          PMF.map_bind, PMF.pure_map, List.isEmpty_cons, Bool.not_false, Prod.map_apply, id_eq]
        apply PMF.bind_congr_on_support
        intro ct hct
        rw [List.take_of_length_le (hctBound k hk _ hmsgLen ct hct)]
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
          ProbOracleComp.runWith_pure, PMF.pure_map])
    (adversary n []) []
  dsimp only [List.isEmpty, not] at hsim
  rw [← hsim]
  simp only [PMF.bind_map, Function.comp_def]

/-- Multi-query `CiphertextIntegrity` implies `OneTimeCiphertextIntegrity`. -/
theorem CiphertextIntegrity.oneTimeCiphertextIntegrity {E : SymmetricCipher}
    (hci : E.CiphertextIntegrity) : E.OneTimeCiphertextIntegrity := by
  apply OneTimeCiphertextIntegrity.of_negligible
  intro adversary hadversary
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have hneg := hci.negligible (ciLimitToOneQuery ctBound adversary)
    (isOraclePPT_ciLimitToOneQuery hctBoundPoly hadversary)
  refine hneg.congr fun n => ?_
  rw [eval_ciGame_ciLimitToOneQuery E ctBound adversary n (hctBound n)]

/-- One-time authenticated encryption (`OneTimeAuthenticatedEncryption`, or `1AE`-security) for a
symmetric cipher ([BonehShoup2023], Section 9.1.1, Definition 9.4, printed p. 360): the cipher
satisfies both `OneTimeINDCPA` (semantic security under a single encryption query) and
`OneTimeCiphertextIntegrity`. -/
def OneTimeAuthenticatedEncryption (E : SymmetricCipher) : Prop :=
  E.OneTimeINDCPA ∧ E.OneTimeCiphertextIntegrity

/-- Multi-query `AuthenticatedEncryption` implies `OneTimeAuthenticatedEncryption`. -/
theorem AuthenticatedEncryption.oneTimeAuthenticatedEncryption {E : SymmetricCipher}
    (h : E.AuthenticatedEncryption) : E.OneTimeAuthenticatedEncryption :=
  ⟨h.1.oneTimeINDCPA, h.2.oneTimeCiphertextIntegrity⟩

/-! ### Adaptive Chosen-Ciphertext Security (`ccaGame`, `ccaRejectGame`, `INDCCA`) -/

/-- Stateful two-channel oracle for the adaptive chosen-ciphertext experiment
([BonehShoup2023], Section 9.2.2, Attack Game 9.2):
* On an encryption query `(false, req)`: decode `m0 = unframe req` and `m1 = dropFrame req`; if
  both have length `n`, encrypt `if bit then m1 else m0` under `k`, prepend the resulting
  ciphertext `ct` to `queriedCiphertexts`, and return `ct`; otherwise return `[]`.
* On a decryption query `(true, ct)`: if `queriedCiphertexts.contains ct` is `true`, return `[]`
  (prohibited challenge ciphertext); otherwise return `encOption encBits (E.decrypt n k ct)`.

Attack Game 9.2 takes decryption queries from the ciphertext space `C = E.ctSpace n`. A query
outside `C` is answered here with the rejection `[] = encOption encBits none`
(`decrypt_eq_none_of_ctSpace_eq_false`), and a query inside `C` as in the source, so an adversary
that asks only the source's queries sees the source's oracle and `INDCCA` implies CCA security on
`C`. Conversely, when `C` is efficiently recognizable, as [BonehShoup2023], Definition 2.10
requires, an adversary can answer its queries outside `C` itself, so CCA security on `C` implies
`INDCCA`. The same holds for `oneTimeCCAOracle`. -/
noncomputable def ccaOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool) (bit : Bool)
    (request : Bool × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.1 then
      if queriedCiphertexts.contains request.2 then
        return ([], queriedCiphertexts)
      else
        return (encOption encBits (E.decrypt n k request.2), queriedCiphertexts)
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, ct :: queriedCiphertexts)
      else
        return ([], queriedCiphertexts)

/-- The adaptive chosen-ciphertext experiment ([BonehShoup2023], Section 9.2.2, Attack Game 9.2):
sample `k ← E.keyGen n` and run `adversary n []` against `E.ccaOracle n k bit`. -/
noncomputable def ccaGame (E : SymmetricCipher) (adversary : CCAAdversary)
    (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.ccaOracle n k bit)) (adversary n [])).run []
  return out.1

/-- `ccaOracle` answering an encryption query only when `allow` admits the current ciphertext
log. -/
private noncomputable def ccaOracleOn (E : SymmetricCipher) (allow : List (List Bool) → Bool)
    (n : ℕ) (k : List Bool) (bit : Bool) (request : Bool × List Bool) :
    StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.1 then
      if queriedCiphertexts.contains request.2 then
        return ([], queriedCiphertexts)
      else
        return (encOption encBits (E.decrypt n k request.2), queriedCiphertexts)
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if allow queriedCiphertexts && (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, ct :: queriedCiphertexts)
      else
        return ([], queriedCiphertexts)

/-- `ccaGame` against `ccaOracleOn allow`. -/
private noncomputable def ccaGameOn (E : SymmetricCipher) (allow : List (List Bool) → Bool)
    (adversary : CCAAdversary) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.ccaOracleOn allow n k bit)) (adversary n [])).run []
  return out.1

private theorem ccaOracle_eq_on (E : SymmetricCipher) :
    E.ccaOracle = E.ccaOracleOn (fun _ => true) :=
  rfl

private theorem ccaGame_eq_on (E : SymmetricCipher) : E.ccaGame = E.ccaGameOn (fun _ => true) :=
  rfl

/-- The shared CCA decryption branch rejects logged ciphertexts and preserves the ciphertext log. -/
private theorem isPPTOn_ccaDecryptBranch (E : SymmetricCipher) :
    IsPPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinEnum Bool) encBits) (encList encBits)))
      (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        if p.2.2.contains p.2.1.2 then
          pure ([], p.2.2)
        else
          pure (encOption encBits (E.decrypt p.1.1 p.1.2 p.2.1.2), p.2.2)) := by
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Bool) encBits) (encList encBits))
  have hcontains : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        p.2.2.contains p.2.1.2)
      EIn encBool :=
    ComputableInPolyTime.contains
      (by dsimp only [EIn]; fun_prop) (by dsimp only [EIn]; fun_prop)
  have hdecArg : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        (p.1.1, p.1.2, p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EIn]; fun_prop
  have hdecWord : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        encOption encBits (E.decrypt p.1.1 p.1.2 p.2.1.2))
      EIn encBits :=
    (E.decrypt_polyTime.comp hdecArg).encoding_comp
  have hnoReply : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isPPTOn
  exact IsPPTOn.cond hcontains hnoReply
    ((ComputableInPolyTime.prod hdecWord (by dsimp only [EIn]; fun_prop)).isPPTOn)

/-- Running an oracle-PPT CCA adversary against `ccaOracleOn allow` is uniformly strict PPT in
`(n, k)` for each challenge bit `bit` when the policy is computable in polynomial time. -/
private theorem isPPTOn_run_ccaOracleOn (E : SymmetricCipher) {allow : List (List Bool) → Bool}
    (hallow : ComputableInPolyTime allow (encList encBits) encBool) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn (encPair encUnary encBits) (encPair encBool (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.ccaOracleOn allow caller.1 caller.2 bit)) (adversary caller.1 [])).run []) := by
  obtain ⟨ce, de, hlenEnc⟩ := E.encrypt_ppt.length_le
  obtain ⟨cd, dd, hlenDec⟩ := E.decrypt_polyTime.polyBounded_length.exists_le
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Bool) encBits) (encList encBits))
  have hop : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => p.2.1.1)
      EIn encBool :=
    (ComputableInPolyTime.of_finite id).comp (by dsimp only [EIn]; fun_prop)
  have hnoReply : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isPPTOn
  have hreq : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => p.2.1.2)
      EIn encBits := by
    dsimp only [EIn]; fun_prop
  have hencCond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        allow p.2.2 && ((unframe p.2.1.2).length == p.1.1) &&
          ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hm0 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => unframe p.2.1.2)
      EIn encBits :=
    ComputableInPolyTime.unframe.comp hreq
  have hm1 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => dropFrame p.2.1.2)
      EIn encBits :=
    ComputableInPolyTime.dropFrame.comp hreq
  have hmsg : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
      EIn encBits := by
    cases bit <;> simpa using (by first | exact hm1 | exact hm0)
  have hencYes : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => do
        let ct ← E.encrypt p.1.1 p.1.2 (if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
        return (ct, ct :: p.2.2)) :=
    (E.encrypt_ppt.preprocess (ComputableInPolyTime.prod (by dsimp only [EIn]; fun_prop)
      (ComputableInPolyTime.prod (by dsimp only [EIn]; fun_prop) hmsg))).bind_with
      ((by dsimp only [EIn]; fun_prop : ComputableInPolyTime
        (fun q : ((ℕ × List Bool) × ((Bool × List Bool) × List (List Bool))) × List Bool =>
          (q.2, q.2 :: q.1.2.2))
        (encPair EIn encBits) (encPair encBits (encList encBits))).isPPTOn)
  have hhandler : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        E.ccaOracleOn allow pair.1.1 pair.1.2 bit pair.2.1 pair.2.2) := by
    unfold ccaOracleOn
    exact IsPPTOn.cond hop (isPPTOn_ccaDecryptBranch E)
      (IsPPTOn.cond hencCond hencYes hnoReply)
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun caller query =>
      2 * (ce * (3 * caller.1 + 2 * caller.2.length + 4) ^ de) +
      cd * (2 * caller.1 + 2 * caller.2.length + query.length + 4) ^ dd + 2)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by fun_prop)
  intro caller request queried _ result hresult
  unfold ccaOracleOn at hresult
  cases hreq : request.1
  · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult
    by_cases hlenEq : (allow queried && ((unframe request.2).length == caller.1) &&
        ((dropFrame request.2).length == caller.1)) = true
    · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
      obtain ⟨ct, hct, rfl⟩ := hresult
      simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
      have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = caller.1 := by
        cases bit <;> simp [hlenEq]
      have hctLen := hlenEnc
        (caller.1, caller.2, if bit then dropFrame request.2 else unframe request.2) ct hct
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
        hmbLen] at hctLen
      have hbound : ct.length ≤ ce * (3 * caller.1 + 2 * caller.2.length + 4) ^ de :=
        hctLen.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (by lia) de))
      refine ⟨trivial, by lia, ?_⟩
      simp only [encList_cons, List.length_append, length_frame, encBits_apply]
      lia
    · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] at hresult
      subst result
      exact ⟨trivial, by simp, by lia⟩
  · simp only [hreq, ↓reduceIte] at hresult
    split_ifs at hresult
    · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      exact ⟨trivial, by simp, by lia⟩
    · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      have hdecLen := hlenDec (caller.1, caller.2, request.2)
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hdecLen
      have hbound : (encOption encBits (E.decrypt caller.1 caller.2 request.2)).length ≤
          cd * (2 * caller.1 + 2 * caller.2.length + request.2.length + 4) ^ dd :=
        hdecLen.trans (Nat.mul_le_mul_left cd (Nat.pow_le_pow_left (by lia) dd))
      exact ⟨trivial, by lia, by lia⟩

/-- Running an oracle-PPT CCA adversary against `ccaOracle` is uniformly strict PPT in `(n, k)` for
each challenge bit `bit`. -/
@[program_certificate]
theorem isPPTOn_run_ccaOracle (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn (encPair encUnary encBits) (encPair encBool (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.ccaOracle caller.1 caller.2 bit)) (adversary caller.1 [])).run []) := by
  rw [ccaOracle_eq_on]
  exact E.isPPTOn_run_ccaOracleOn (by fun_prop) hadversary bit

/-- The adaptive CCA experiment is uniformly strict PPT in the unary security parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_ccaGame (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn encUnary encBool (E.ccaGame adversary bit) := by
  have hrun := E.isPPTOn_run_ccaOracle hadversary bit
  unfold ccaGame
  exact E.keyGen_ppt.bind_with (hrun.bind (ComputableInPolyTime.fst _ _).isPPTOn)

/-- The adaptive CCA experiment is uniformly strict PPT, independently of unused auxiliary input. -/
@[program_certificate]
theorem isPPT_ccaGame (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPT encBool (fun n _ => E.ccaGame adversary bit n) :=
  ((E.isPPTOn_ccaGame hadversary bit).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Adaptive chosen-ciphertext security (`INDCCA`, or CCA-security) for a symmetric cipher
([BonehShoup2023], Section 9.2.2, Attack Game 9.2 and Definition 9.5, printed p. 362): every
uniform strict `IsOraclePPT encBool` CCA adversary has negligible advantage between
`E.ccaGame adversary false` and `E.ccaGame adversary true`.

In [BonehShoup2023], Section 9.2.2, Definition 9.5 defines adaptive multi-query CCA security,
whereas one-time CCA security (`OneTimeINDCCA`, or `1CCA`) is defined in Definition 9.6
(printed p. 363). -/
def INDCCA (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.ccaGame adversary false n))
    (fun adversary n => ProbComp.eval (E.ccaGame adversary true n))
    (IsOraclePPT encBool)

/-- Stateful two-channel oracle for the one-time adaptive chosen-ciphertext experiment
([BonehShoup2023], Section 9.2.2, Attack Game 9.2 and Definition 9.6, printed pp. 362–363):
* On an encryption query `(false, req)`: decode `m0 = unframe req` and `m1 = dropFrame req`; if
  no challenge ciphertext has been returned yet (`queriedCiphertexts.isEmpty`) and both messages
  have length `n`, encrypt `if bit then m1 else m0` under `k`, record `[ct]`, and return `ct`;
  otherwise return `[]`.
* On a decryption query `(true, ct)`: if `queriedCiphertexts.contains ct` is `true`, return `[]`
  (prohibited challenge ciphertext); otherwise return `encOption encBits (E.decrypt n k ct)`. -/
noncomputable def oneTimeCCAOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool) (bit : Bool)
    (request : Bool × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.1 then
      if queriedCiphertexts.contains request.2 then
        return ([], queriedCiphertexts)
      else
        return (encOption encBits (E.decrypt n k request.2), queriedCiphertexts)
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if queriedCiphertexts.isEmpty && (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, [ct])
      else
        return ([], queriedCiphertexts)

/-- The one-time adaptive chosen-ciphertext experiment ([BonehShoup2023], Section 9.2.2,
Attack Game 9.2 and Definition 9.6, printed pp. 362–363): sample `k ← E.keyGen n` and run
`adversary n []` against `E.oneTimeCCAOracle n k bit`. -/
noncomputable def ccaOneTimeGame (E : SymmetricCipher) (adversary : CCAAdversary)
    (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.oneTimeCCAOracle n k bit)) (adversary n [])).run []
  return out.1

private theorem oneTimeCCAOracle_eq_on (E : SymmetricCipher) :
    E.oneTimeCCAOracle = E.ccaOracleOn List.isEmpty := by
  funext n k bit request queried
  cases queried <;> rfl

private theorem ccaOneTimeGame_eq_on (E : SymmetricCipher) :
    E.ccaOneTimeGame = E.ccaGameOn List.isEmpty := by
  funext adversary bit n
  simp only [ccaOneTimeGame, ccaGameOn, oneTimeCCAOracle_eq_on]

/-- Running an oracle-PPT CCA adversary against `oneTimeCCAOracle` is uniformly strict PPT in
`(n, k)` for each challenge bit `bit`. -/
@[program_certificate]
theorem isPPTOn_run_oneTimeCCAOracle (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn (encPair encUnary encBits) (encPair encBool (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.oneTimeCCAOracle caller.1 caller.2 bit)) (adversary caller.1 [])).run []) := by
  rw [oneTimeCCAOracle_eq_on]
  exact E.isPPTOn_run_ccaOracleOn (by fun_prop) hadversary bit

/-- The one-time adaptive CCA experiment is uniformly strict PPT in the unary security parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_ccaOneTimeGame (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn encUnary encBool (E.ccaOneTimeGame adversary bit) := by
  have hrun := E.isPPTOn_run_oneTimeCCAOracle hadversary bit
  unfold ccaOneTimeGame
  exact E.keyGen_ppt.bind_with (hrun.bind (ComputableInPolyTime.fst _ _).isPPTOn)

/-- The one-time adaptive CCA experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_ccaOneTimeGame (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPT encBool (fun n _ => E.ccaOneTimeGame adversary bit n) :=
  ((E.isPPTOn_ccaOneTimeGame hadversary bit).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- One-time adaptive chosen-ciphertext security (`OneTimeINDCCA`, or `1CCA`-security) for a
symmetric cipher ([BonehShoup2023], Section 9.2.2, Attack Game 9.2 and Definition 9.6,
printed p. 363): every uniform strict `IsOraclePPT encBool` CCA adversary has negligible advantage
between `E.ccaOneTimeGame adversary false` and `E.ccaOneTimeGame adversary true`. -/
def OneTimeINDCCA (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.ccaOneTimeGame adversary false n))
    (fun adversary n => ProbComp.eval (E.ccaOneTimeGame adversary true n))
    (IsOraclePPT encBool)

/-- Stateful filter handler that forwards all decryption queries `(true, ct)` (truncating replies to
`decBound n ct`) and at most one valid `n`-bit encryption query `(false, req)` (truncating replies
to `ctBound`) to an external multi-query CCA oracle. -/
noncomputable def ccaOneTimeFilterHandler (n ctBound : ℕ) (decBound : ℕ → List Bool → ℕ)
    (request : Bool × List Bool) : StateT Bool (WordOracleComp Bool) (List Bool) :=
  fun alreadyEncrypted =>
    if request.1 then
      (fun reply => (reply, alreadyEncrypted)) <$>
        (List.take (decBound n request.2) <$> ProbOracleComp.query (true, request.2))
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if !alreadyEncrypted && (m0.length == n) && (m1.length == n) then
        (fun ct => (ct, true)) <$>
          (List.take ctBound <$> ProbOracleComp.query (false, request.2))
      else
        pure ([], alreadyEncrypted)

/-- Reduction from `ccaOneTimeGame` to `ccaGame`: run `adversary n []` against
`ccaOneTimeFilterHandler n (ctBound n) decBound` starting from `alreadyEncrypted = false`. -/
noncomputable def ccaLimitToOneEncryptionQuery (ctBound : ℕ → ℕ) (decBound : ℕ → List Bool → ℕ)
    (adversary : CCAAdversary) : CCAAdversary :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (ccaOneTimeFilterHandler n (ctBound n) decBound))
      (adversary n [])).run false
    return out.1

/-- `ccaLimitToOneEncryptionQuery` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_ccaLimitToOneEncryptionQuery {ctBound : ℕ → ℕ}
    {decBound : ℕ → List Bool → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    (hdecBound : ComputableInPolyTime (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    {adversary : CCAAdversary} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (ccaLimitToOneEncryptionQuery ctBound decBound adversary) := by
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair encBool encBits) encBool)
  have hop : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) => p.2.1.1)
      EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hreq : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) => p.2.1.2)
      EIn encBits := by
    dsimp only [EIn]; fun_prop
  have hn : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) => p.1.1)
      EIn encUnary := by
    dsimp only [EIn]; fun_prop
  have hstate : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) => p.2.2)
      EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hencCond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) =>
        !p.2.2 && ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    fun_prop
  have hdecQuery : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) =>
        (fun reply => (reply, p.2.2)) <$>
          (List.take (decBound p.1.1 p.2.1.2) <$> ProbOracleComp.query (true, p.2.1.2))) := by ppt
  have hencQuery : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) =>
        (fun ct => (ct, true)) <$>
          (List.take (ctBound p.1.1) <$> ProbOracleComp.query (false, p.2.1.2))) := by ppt
  have hnoReply : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Bool) => pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isOraclePPTOn (Operation := Bool)
  have hhandler : IsOraclePPTOn EIn (encPair encBits encBool)
      (fun pair : (ℕ × List Bool) × ((Bool × List Bool) × Bool) =>
        ccaOneTimeFilterHandler pair.1.1 (ctBound pair.1.1) decBound pair.2.1 pair.2.2) := by
    unfold ccaOneTimeFilterHandler
    exact IsOraclePPTOn.cond hop hdecQuery (IsOraclePPTOn.cond hencCond hencQuery hnoReply)
  have hresCtArg : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => pair.1.1)
      (encPair (encPair encUnary encBits) encBits) encUnary := by
    fun_prop
  have hresDecArg : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => (pair.1.1, pair.2))
      (encPair (encPair encUnary encBits) encBits) (encPair encUnary encBits) := by
    fun_prop
  have hres : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool =>
        ctBound pair.1.1 + decBound pair.1.1 pair.2 + 1)
      (encPair (encPair encUnary encBits) encBits) encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_add'
        (hctBound.comp hresCtArg)
        (hdecBound.comp hresDecArg))
      (ComputableInPolyTime.const 1)
  have hrun : IsOraclePPTOn (encPair encUnary encBits) (encPair encBool encBool)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ccaOneTimeFilterHandler caller.1 (ctBound caller.1) decBound))
          (adversary caller.1 [])).run false) := by
    apply hadversary.run_interpret_preprocess_open
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => false)
      (resources := fun caller query => ctBound caller.1 + decBound caller.1 query + 1)
      (by fun_prop) hhandler (ComputableInPolyTime.const false)
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request alreadyEncrypted _ result hresult
    unfold ccaOneTimeFilterHandler at hresult
    cases hreq : request.1
    · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult
      split_ifs at hresult with hlenEq
      · obtain ⟨ct, hct, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
        obtain ⟨rawCt, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hct
        exact ⟨trivial, (List.length_take_le _ _).trans (by lia), by simp [encBool_apply]⟩
      · cases OracleComp.eq_of_mem_supportWith_pure hresult
        exact ⟨trivial, by simp, by simp [encBool_apply]⟩
    · simp only [hreq, ↓reduceIte] at hresult
      obtain ⟨reply, hreply, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      obtain ⟨rawReply, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
      exact ⟨trivial, (List.length_take_le _ _).trans (by lia), by simp [encBool_apply]⟩
  unfold ccaLimitToOneEncryptionQuery
  simpa only [bind_pure_comp] using (hrun.map (ComputableInPolyTime.fst _ _)).isOraclePPT

/-- When `ctBound n` bounds all ciphertext lengths produced by `E.encrypt n k` on `n`-bit messages
and `decBound n ct` bounds all encoded decryption replies `encOption encBits (E.decrypt n k ct)`,
running `ccaLimitToOneEncryptionQuery ctBound decBound adversary` in `ccaGame` has the exact same
output distribution as `ccaOneTimeGame adversary`. -/
theorem eval_ccaGame_ccaLimitToOneEncryptionQuery (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (decBound : ℕ → List Bool → ℕ) (adversary : CCAAdversary) (bit : Bool) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n))
    (hdecBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ ct, (encOption encBits (E.decrypt n k ct)).length ≤ decBound n ct) :
    ProbComp.eval (E.ccaGame (ccaLimitToOneEncryptionQuery ctBound decBound adversary) bit n) =
      ProbComp.eval (E.ccaOneTimeGame adversary bit n) := by
  simp only [ccaGame, ccaOneTimeGame, ccaLimitToOneEncryptionQuery, runWith_norm, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  have hsim := ProbOracleComp.runWith_map_state
    (fun request queried =>
      ProbComp.eval (E.oneTimeCCAOracle n k bit request queried))
    (fun request state =>
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaOracle n k bit q s))
          ((ccaOneTimeFilterHandler n (ctBound n) decBound request).run state.1) state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (fun queried : List (List Bool) => (!queried.isEmpty, queried))
    (fun request queried => by
      change (ProbComp.eval (E.oneTimeCCAOracle n k bit request queried)).map
          (fun x => (x.1, !x.2.isEmpty, x.2)) =
        (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaOracle n k bit q s))
            (ccaOneTimeFilterHandler n (ctBound n) decBound request (!queried.isEmpty)) queried).map
          (fun result => (result.1.1, result.1.2, result.2))
      cases hreq : request.1
      · simp only [oneTimeCCAOracle, ccaOneTimeFilterHandler, hreq, Bool.false_eq_true,
          ↓reduceIte, Bool.not_not]
        by_cases hcond : (queried.isEmpty && ((unframe request.2).length == n) &&
            ((dropFrame request.2).length == n)) = true
        · simp only [hcond, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
            Functor.map_map, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ccaOracle]
          simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hcond
          rcases hcond with ⟨⟨rfl, hm0⟩, hm1⟩
          have hlenEq : (((unframe request.2).length == n) &&
              ((dropFrame request.2).length == n)) = true := by
            simp [hm0, hm1]
          simp only [Bool.false_eq_true, ↓reduceIte, hlenEq, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.map_bind, PMF.pure_map, List.isEmpty_cons, Bool.not_false, Prod.map_apply, id_eq]
          have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
            cases bit <;> simp [hm0, hm1]
          apply PMF.bind_congr_on_support
          intro ct hct
          rw [List.take_of_length_le (hctBound k hk _ hmbLen ct hct)]
        · simp only [hcond, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            ProbOracleComp.runWith_pure, PMF.pure_map]
      · simp only [oneTimeCCAOracle, ccaOneTimeFilterHandler, hreq, ↓reduceIte,
          Functor.map_map, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ccaOracle]
        split_ifs with hmem
        · simp only [ProbComp.eval_pure, PMF.pure_map, List.take_nil, Prod.map_apply, id_eq]
        · simp only [ProbComp.eval_pure, PMF.pure_map, Prod.map_apply, id_eq,
            List.take_of_length_le (hdecBound k hk request.2)])
    (adversary n []) []
  dsimp only [List.isEmpty, not] at hsim
  rw [← hsim]
  simp only [PMF.bind_map, Function.comp_def]

/-- Multi-query `INDCCA` security implies one-time `OneTimeINDCCA` security. -/
theorem INDCCA.oneTimeINDCCA {E : SymmetricCipher} (hcca : E.INDCCA) :
    E.OneTimeINDCCA := by
  intro adversary hadversary
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  obtain ⟨decBound, hdecBoundPoly, hdecBound⟩ := E.exists_decryption_length_bound
  have hneg := hcca (ccaLimitToOneEncryptionQuery ctBound decBound adversary)
    (isOraclePPT_ccaLimitToOneEncryptionQuery hctBoundPoly hdecBoundPoly hadversary)
  refine hneg.congr fun n => ?_
  dsimp only
  rw [eval_ccaGame_ccaLimitToOneEncryptionQuery E ctBound decBound adversary false n
      (hctBound n) (hdecBound n),
    eval_ccaGame_ccaLimitToOneEncryptionQuery E ctBound decBound adversary true n
      (hctBound n) (hdecBound n)]

/-! ### Authenticated Encryption Implies Adaptive CCA Security (Boneh–Shoup Theorem 9.1) -/

/-- Structural encryption-query bound for a two-channel CCA computation (`Operation = Bool`,
where `false` is the encryption channel and `true` is the decryption channel): every execution path
makes at most `Qe` encryption-oracle queries (`(false, _)`), while allowing arbitrary random-coin
queries and decryption-oracle queries ([BonehShoup2023], Section 9.2.3, Theorem 9.1,
printed p. 363). -/
abbrev IsEncryptionQueryBounded {α : Type} (program : WordOracleComp Bool α) (Qe : ℕ) : Prop :=
  OracleComp.IsCostBounded
    (Sum.elim (fun _ => 0) (fun req : Bool × List Bool => if req.1 then 0 else 1))
    program Qe

/-- Every total-query bound `program.IsQueryBounded Q` implies the encryption-query bound
`IsEncryptionQueryBounded program Q`. -/
theorem isEncryptionQueryBounded_of_isQueryBounded {α : Type}
    {program : WordOracleComp Bool α} {Q : ℕ}
    (hq : program.IsQueryBounded Q) :
    IsEncryptionQueryBounded program Q :=
  OracleComp.IsCostBounded.of_le hq fun
    | Sum.inl _ => le_rfl
    | Sum.inr ⟨op, _⟩ => by cases op <;> simp

/-- Structural decryption-query bound for a two-channel CCA computation: every execution path
makes at most `Qd` decryption-oracle queries (`(true, _)`), while allowing arbitrary random-coin
queries and encryption-oracle queries. This is the budget `Q_d` of [BonehShoup2023], Section 9.2.3,
Theorem 9.1, printed p. 363. -/
abbrev IsDecryptionQueryBounded {α : Type} (program : WordOracleComp Bool α) (Qd : ℕ) : Prop :=
  OracleComp.IsCostBounded
    (Sum.elim (fun _ => 0) (fun req : Bool × List Bool => if req.1 then 1 else 0))
    program Qd

/-- Every total-query bound `program.IsQueryBounded Q` implies the decryption-query bound
`IsDecryptionQueryBounded program Q`. -/
theorem isDecryptionQueryBounded_of_isQueryBounded {α : Type}
    {program : WordOracleComp Bool α} {Q : ℕ}
    (hq : program.IsQueryBounded Q) :
    IsDecryptionQueryBounded program Q :=
  OracleComp.IsCostBounded.of_le hq fun
    | Sum.inl _ => le_rfl
    | Sum.inr ⟨op, _⟩ => by cases op <;> simp

/-- Hybrid two-channel oracle for Game 1 in the proof of [BonehShoup2023], Theorem 9.1
(Section 9.2.3, printed pp. 363–364): encryption queries `(false, req)` behave identically to
`ccaOracle`, whereas every decryption query `(true, _)` immediately returns `[]` (rejection) without
invoking `decrypt`. -/
noncomputable def ccaRejectOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool) (bit : Bool)
    (request : Bool × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.1 then
      return ([], queriedCiphertexts)
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, ct :: queriedCiphertexts)
      else
        return ([], queriedCiphertexts)

/-- The all-reject hybrid CCA experiment (Game 1 in [BonehShoup2023], Section 9.2.3,
Theorem 9.1): sample `k ← E.keyGen n` and run `adversary n []` against
`E.ccaRejectOracle n k bit`. -/
noncomputable def ccaRejectGame (E : SymmetricCipher) (adversary : CCAAdversary)
    (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.ccaRejectOracle n k bit)) (adversary n [])).run []
  return out.1

/-- `ccaRejectOracle` answering an encryption query only when `allow` admits the current
ciphertext log. -/
private noncomputable def ccaRejectOracleOn (E : SymmetricCipher) (allow : List (List Bool) → Bool)
    (n : ℕ) (k : List Bool) (bit : Bool) (request : Bool × List Bool) :
    StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.1 then
      return ([], queriedCiphertexts)
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if allow queriedCiphertexts && (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, ct :: queriedCiphertexts)
      else
        return ([], queriedCiphertexts)

/-- `ccaRejectGame` against `ccaRejectOracleOn allow`. -/
private noncomputable def ccaRejectGameOn (E : SymmetricCipher) (allow : List (List Bool) → Bool)
    (adversary : CCAAdversary) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.ccaRejectOracleOn allow n k bit)) (adversary n [])).run []
  return out.1

private theorem ccaRejectGame_eq_on (E : SymmetricCipher) :
    E.ccaRejectGame = E.ccaRejectGameOn (fun _ => true) :=
  rfl

/-- Stateful handler for `ccaToCPAAdversary` ([BonehShoup2023], Section 9.2.3, Theorem 9.1):
reject all decryption queries `(true, _)` with `[]`, and forward valid left-or-right encryption
queries `(false, req)` to the external CPA encryption oracle (truncating replies to `ctBound`). -/
noncomputable def ccaToCPAHandler (n ctBound : ℕ) (request : Bool × List Bool) :
    StateT Unit (WordOracleComp Unit) (List Bool) :=
  fun _ =>
    if request.1 then
      pure ([], ())
    else
      if ((unframe request.2).length == n) && ((dropFrame request.2).length == n) then
        (fun ct => (ct, ())) <$> (List.take ctBound <$> ProbOracleComp.query ((), request.2))
      else
        pure ([], ())

/-- Reduction from the all-reject hybrid `ccaRejectGame` to the adaptive CPA experiment `cpaGame`
([BonehShoup2023], Section 9.2.3, adversary $B_{\mathrm{cpa}}$ in Theorem 9.1): run `adversary n []`
against `ccaToCPAHandler n (ctBound n)`. -/
noncomputable def ccaToCPAAdversary (ctBound : ℕ → ℕ) (adversary : CCAAdversary) :
    OracleDistinguisher :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (ccaToCPAHandler n (ctBound n)))
      (adversary n [])).run ()
    return out.1

/-- `ccaToCPAAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_ccaToCPAAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {adversary : CCAAdversary} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (ccaToCPAAdversary ctBound adversary) := by
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair encBool encBits) (encFinEnum Unit))
  have hhandler : IsOraclePPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × ((Bool × List Bool) × Unit) =>
        ccaToCPAHandler pair.1.1 (ctBound pair.1.1) pair.2.1 pair.2.2) := by ppt [ccaToCPAHandler]
  have hres : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => ctBound pair.1.1 + 1)
      (encPair (encPair encUnary encBits) encBits) encUnary :=
    ComputableInPolyTime.unary_add' (hctBound.comp (by fun_prop)) (ComputableInPolyTime.const 1)
  have hrun : IsOraclePPTOn (encPair encUnary encBits) (encPair encBool (encFinEnum Unit))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ccaToCPAHandler caller.1 (ctBound caller.1)))
          (adversary caller.1 [])).run ()) := by
    apply hadversary.run_interpret_preprocess_open
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => ())
      (resources := fun caller _ => ctBound caller.1 + 1)
      (by fun_prop) hhandler (ComputableInPolyTime.const ())
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request _ _ result hresult
    unfold ccaToCPAHandler at hresult
    cases hreq : request.1
    · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult
      split_ifs at hresult with hlenEq
      · obtain ⟨ct, hct, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
        obtain ⟨rawCt, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hct
        exact ⟨trivial, (List.length_take_le _ _).trans (by lia), by lia⟩
      · cases OracleComp.eq_of_mem_supportWith_pure hresult
        exact ⟨trivial, by simp, by lia⟩
    · simp only [hreq, ↓reduceIte] at hresult
      cases OracleComp.eq_of_mem_supportWith_pure hresult
      exact ⟨trivial, by simp, by lia⟩
  unfold ccaToCPAAdversary
  simpa only [bind_pure_comp] using (hrun.map (ComputableInPolyTime.fst _ _)).isOraclePPT

/-- When `ctBound n` bounds all ciphertext lengths produced by `E.encrypt n k` on `n`-bit messages,
running `ccaToCPAAdversary ctBound adversary` in `cpaGame` has the exact same output distribution as
`ccaRejectGame adversary` ([BonehShoup2023], Section 9.2.3, equation (9.7) in the proof of
Theorem 9.1, printed p. 365). -/
theorem eval_cpaGame_ccaToCPAAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : CCAAdversary) (bit : Bool) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) bit n) =
      ProbComp.eval (E.ccaRejectGame adversary bit n) := by
  simp only [cpaGame, symmetricCPAGameOn, ProbOracleComp.run, ccaRejectGame, ccaToCPAAdversary,
    runWith_norm, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  have hsim := ProbOracleComp.runWith_map_state
    (fun request queried => ProbComp.eval (E.ccaRejectOracle n k bit request queried))
    (fun request state =>
      OracleComp.evalWith
        (OracleComp.sumHandler ProbComp.unifOracle fun q =>
          ProbComp.eval (symmetricCPAReplyOn (fun n m₀ m₁ => (m₀.length == n) && (m₁.length == n))
            E.encrypt n k bit q))
        ((ccaToCPAHandler n (ctBound n) request).run state))
    (fun _ : List (List Bool) => ())
    (fun request queried => by
      change (ProbComp.eval (E.ccaRejectOracle n k bit request queried)).map
          (fun x => (x.1, ())) =
        OracleComp.evalWith _ (ccaToCPAHandler n (ctBound n) request ())
      cases hreq : request.1
      · simp only [ccaRejectOracle, ccaToCPAHandler, hreq, Bool.false_eq_true, ↓reduceIte]
        by_cases hlenEq : ((unframe request.2).length == n &&
            (dropFrame request.2).length == n) = true
        · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
            OracleComp.evalWith_map, ProbOracleComp.evalWith_sumHandler_query,
            symmetricCPAReplyOn, PMF.map_bind, PMF.pure_map, PMF.map_comp]
          simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
          have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
            cases bit <;> simp [hlenEq]
          rw [← PMF.bind_pure_comp]
          apply PMF.bind_congr_on_support
          intro ct hct
          simp only [Function.comp_apply, List.take_of_length_le (hctBound k hk _ hmbLen ct hct)]
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            OracleComp.evalWith_pure, PMF.pure_map]
      · simp only [ccaRejectOracle, ccaToCPAHandler, hreq, ↓reduceIte, ProbComp.eval_pure,
          OracleComp.evalWith_pure, PMF.pure_map])
    (adversary n []) []
  rw [← hsim]
  simp only [PMF.bind_map, Function.comp_def]

/-- `eval_cpaGame_ccaToCPAAdversary` in the form the policy-generic bounds take. -/
private theorem eval_cpaGame_ccaToCPAAdversary_on (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ) (hctBound : E.CiphertextLengthLE n (ctBound n))
    (bit : Bool) :
    ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) bit n) =
      ProbComp.eval (E.ccaRejectGameOn (fun _ => true) adversary bit n) := by
  rw [← ccaRejectGame_eq_on]
  exact E.eval_cpaGame_ccaToCPAAdversary ctBound adversary bit n hctBound

/-- State `(rem, (hasCaptured, capturedCt)) : ℕ × (Bool × List Bool)` of `ccaToCIHandler`: the
number of decryption queries still to be skipped, the flag recording whether a candidate ciphertext
has been captured, and the captured candidate ciphertext. -/
abbrev CCAToCIState : Type := ℕ × (Bool × List Bool)

/-- Flag and captured-ciphertext pair `(hasCaptured, capturedCt)` of a `CCAToCIState`. -/
abbrev CCAToCIState.cap (s : CCAToCIState) : Bool × List Bool := s.2

/-- Remaining decryption-query countdown `rem` of a `CCAToCIState`. -/
abbrev CCAToCIState.rem (s : CCAToCIState) : ℕ := s.1

/-- Flag indicating whether a candidate ciphertext has already been captured. -/
abbrev CCAToCIState.hasCaptured (s : CCAToCIState) : Bool :=
  (CCAToCIState.cap s).1

/-- Captured candidate ciphertext in a `CCAToCIState`. -/
abbrev CCAToCIState.capturedCt (s : CCAToCIState) : List Bool :=
  (CCAToCIState.cap s).2

/-- Run outcome `(result, state)` of `ccaToCIAtIndexAdversary`. -/
abbrev CCAToCIRunOut (α : Type) : Type := α × CCAToCIState

/-- Captured candidate ciphertext from a `CCAToCIRunOut`. -/
abbrev CCAToCIRunOut.capturedCt {α : Type} (out : CCAToCIRunOut α) : List Bool :=
  CCAToCIState.capturedCt out.2

/-- Stateful handler for `ccaToCIAtIndexAdversary` and `ccaToCIAdversary`
([BonehShoup2023], Section 9.2.3, adversary $B_{\mathrm{ci}}$ in Theorem 9.1): execute one
CCA-to-CI query against the external CI encryption oracle, maintaining
`(rem, (hasCaptured, capturedCt)) : ℕ × (Bool × List Bool)`.
* Once `hasCaptured = true`, all subsequent queries return `[]` without calling the external CI
  encryption oracle and leave the state unchanged.
* While `hasCaptured = false`, a decryption query `(true, ct)` is answered with `[]` (reject); it
  captures `(0, (true, ct))` if `rem == 0` and otherwise moves to `(rem - 1, (false, []))`. So the
  countdown runs over decryption queries only, and starting from `rem = j` captures the
  decryption query with zero-based index `j`.
* While `hasCaptured = false`, an encryption query `(false, req)` with
  `(unframe req).length == n && (dropFrame req).length == n` queries the external CI encryption
  oracle on `if bit then dropFrame req else unframe req` (truncating the reply to its first
  `ctBound` bits), and any other encryption query returns `[]`; neither changes the state. -/
noncomputable def ccaToCIHandler (n ctBound : ℕ) (bit : Bool) (request : Bool × List Bool) :
    StateT (ℕ × (Bool × List Bool)) (WordOracleComp Unit) (List Bool) :=
  fun state =>
    if CCAToCIState.hasCaptured state then
      pure ([], state)
    else
      if request.1 then
        if CCAToCIState.rem state == 0 then
          pure ([], (0, (true, request.2)))
        else
          pure ([], (CCAToCIState.rem state - 1, (false, [])))
      else
        if ((unframe request.2).length == n) && ((dropFrame request.2).length == n) then
          (fun ct => (ct, state)) <$>
            (List.take ctBound <$>
              ProbOracleComp.query ((), if bit then dropFrame request.2 else unframe request.2))
        else
          pure ([], state)

/-- Deterministic-index ciphertext-integrity reduction at decryption-query index `j`
([BonehShoup2023], Section 9.2.3, Theorem 9.1): run `adversary n []` against
`ccaToCIHandler n (ctBound n) bit` starting from `(j, (false, []))` and output the captured
ciphertext candidate `CCAToCIRunOut.capturedCt out`, which is the decryption query with
zero-based index `j` when there is one and `[]` otherwise. -/
noncomputable def ccaToCIAtIndexAdversary (ctBound : ℕ → ℕ) (j : ℕ) (bit : Bool)
    (adversary : CCAAdversary) : CIAdversary :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (ccaToCIHandler n (ctBound n) bit))
      (adversary n [])).run (j, (false, []))
    return CCAToCIRunOut.capturedCt out

/-- Reduction from decryption-oracle forgery in `ccaRejectGame` to the ciphertext-integrity game
`ciGame` for fixed challenge bit `bit` ([BonehShoup2023], Section 9.2.3, adversary $B_{\mathrm{ci}}$
in Theorem 9.1): for a decryption-query budget `Qd`, sample a decryption-query index uniformly from
`{0, ..., dyadicSize (Qd n - 1) - 1}` with
`ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Qd n - 1))` and run
`ccaToCIAtIndexAdversary ctBound j bit adversary`. The book samples from `{1, ..., Qd}`; with fair
coins a fixed-time sampler draws from a power-of-two range, and `dyadicSize (Qd - 1)` is the least
power of two that is at least `Qd` when `2 ≤ Qd`. -/
noncomputable def ccaToCIAdversary (ctBound Qd : ℕ → ℕ) (bit : Bool)
    (adversary : CCAAdversary) : CIAdversary :=
  fun n aux => do
    let j ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Qd n - 1))
    ccaToCIAtIndexAdversary ctBound j bit adversary n aux

/-- Single-adversary ciphertext-integrity reduction that samples a hidden challenge bit uniformly
via `BitString.sampleList 1` and invokes `ccaToCIAdversary` ([BonehShoup2023], Section 9.2.3,
proof of Theorem 9.1, printed p. 364). -/
noncomputable def ccaToCIHiddenBitAdversary (ctBound Qd : ℕ → ℕ)
    (adversary : CCAAdversary) : CIAdversary :=
  fun n aux => do
    let bits ← ProbOracleComp.sample (BitString.sampleList 1)
    if bits == [true] then
      ccaToCIAdversary ctBound Qd true adversary n aux
    else
      ccaToCIAdversary ctBound Qd false adversary n aux

/-- `ccaToCIAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_ccaToCIAdversary {ctBound Qd : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    (hQd : ComputableInPolyTime Qd encUnary encUnary) (bit : Bool)
    {adversary : CCAAdversary} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBits (ccaToCIAdversary ctBound Qd bit adversary) := by
  let ECaller := encPair (encPair encUnary encBits) encUnary
  let EState := encPair encUnary (encPair encBool encBits)
  let EIn := encPair ECaller (encPair (encPair encBool encBits) EState)
  have hcaptured : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        p.2.2.2.1)
      EIn encBool := by
    dsimp only [EIn, ECaller, EState]; fun_prop
  have hremZero : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        p.2.2.1 == 0)
      EIn encBool :=
    ComputableInPolyTime.beq (encB := encUnary)
      (by dsimp only [EIn, EState]; fun_prop) (ComputableInPolyTime.const 0)
  have hop : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        p.2.1.1)
      EIn encBool := by
    dsimp only [EIn, ECaller, EState]; fun_prop
  have hreq : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        p.2.1.2)
      EIn encBits := by
    dsimp only [EIn]; fun_prop
  have hn : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        p.1.1.1)
      EIn encUnary := by
    dsimp only [EIn, ECaller]; fun_prop
  have hencCond : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        ((unframe p.2.1.2).length == p.1.1.1) && ((dropFrame p.2.1.2).length == p.1.1.1))
      EIn encBool := by
    fun_prop
  have hm0 : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        unframe p.2.1.2)
      EIn encBits :=
    ComputableInPolyTime.unframe.comp hreq
  have hm1 : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        dropFrame p.2.1.2)
      EIn encBits :=
    ComputableInPolyTime.dropFrame.comp hreq
  have hmsg : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
      EIn encBits := by
    cases bit <;> simpa using (by first | exact hm1 | exact hm0)
  have hlimit : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        ctBound p.1.1.1)
      EIn encUnary :=
    hctBound.comp (by dsimp only [EIn, ECaller, EState]; fun_prop)
  have hdecRem : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        (p.2.2.1 - 1, (false, ([] : List Bool))))
      EIn EState := by
    dsimp only [EIn, ECaller, EState]
    exact ComputableInPolyTime.prod
      (ComputableInPolyTime.unary_sub.comp
        (ComputableInPolyTime.prod (by fun_prop) (ComputableInPolyTime.const 1)))
      (ComputableInPolyTime.const (false, []))
  have hstate : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) => p.2.2)
      EIn EState := by
    dsimp only [EIn, ECaller, EState]; fun_prop
  have hbranchKeep : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits EState)
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const []) hstate).isOraclePPTOn
  have hbranchZeroDec : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits EState)
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        pure ([], (0, (true, p.2.1.2)))) := by
    dsimp only [EIn, ECaller, EState]
    exact (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      (ComputableInPolyTime.prod (ComputableInPolyTime.const 0)
        (ComputableInPolyTime.prod (ComputableInPolyTime.const true)
          (by fun_prop)))).isOraclePPTOn
  have hbranchStepDec : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits EState)
      (fun p => pure ([], (p.2.2.1 - 1, (false, ([] : List Bool))))) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      hdecRem).isOraclePPTOn
  have hbranchQuery : IsOraclePPTOn EIn (encPair encBits EState)
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        (fun ct => (ct, p.2.2)) <$>
          (List.take (ctBound p.1.1.1) <$>
            ProbOracleComp.query ((), if bit then dropFrame p.2.1.2 else unframe p.2.1.2))) :=
    (IsOraclePPTOn.query_take (Operation := Unit) () hmsg hlimit).map_with
      (ComputableInPolyTime.prod (by fun_prop)
        (hstate.comp (ComputableInPolyTime.fst EIn encBits)))
  have hhandler : IsOraclePPTOn EIn (encPair encBits EState)
      (fun pair : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        ccaToCIHandler pair.1.1.1 (ctBound pair.1.1.1) bit pair.2.1 pair.2.2) := by
    unfold ccaToCIHandler
    exact IsOraclePPTOn.cond hcaptured hbranchKeep
      (IsOraclePPTOn.cond hop
        (IsOraclePPTOn.cond hremZero hbranchZeroDec hbranchStepDec)
        (IsOraclePPTOn.cond hencCond hbranchQuery hbranchKeep))
  have hres : ComputableInPolyTime
      (fun pair : ((ℕ × List Bool) × ℕ) × List Bool => ctBound pair.1.1.1 + pair.2.length + 4)
      (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller]
    have hct : ComputableInPolyTime
        (fun pair : ((ℕ × List Bool) × ℕ) × List Bool => ctBound pair.1.1.1)
        (encPair (encPair (encPair encUnary encBits) encUnary) encBits) encUnary :=
      hctBound.comp (by fun_prop)
    have hqlen : ComputableInPolyTime
        (fun pair : ((ℕ × List Bool) × ℕ) × List Bool => pair.2.length + 4)
        (encPair (encPair (encPair encUnary encBits) encUnary) encBits) encUnary := by
      fun_prop
    exact ComputableInPolyTime.unary_add.comp (ComputableInPolyTime.prod hct hqlen)
  have hinit : ComputableInPolyTime
      (fun caller : (ℕ × List Bool) × ℕ => (caller.2, (false, ([] : List Bool))))
      ECaller EState := by
    dsimp only [ECaller, EState]
    exact ComputableInPolyTime.prod (by fun_prop)
      (ComputableInPolyTime.const (false, []))
  have hrun : IsOraclePPTOn ECaller (encPair encBool EState)
      (fun caller : (ℕ × List Bool) × ℕ =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ccaToCIHandler caller.1.1 (ctBound caller.1.1) bit))
          (adversary caller.1.1 [])).run (caller.2, (false, []))) := by
    apply hadversary.run_interpret_preprocess_open
      (prepare := fun caller : (ℕ × List Bool) × ℕ => (caller.1.1, ([] : List Bool)))
      (initial := fun caller : (ℕ × List Bool) × ℕ => (caller.2, (false, ([] : List Bool))))
      (resources := fun caller query => ctBound caller.1.1 + query.length + 4)
      (by dsimp only [ECaller]; fun_prop) hhandler hinit
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request state _ result hresult
    unfold ccaToCIHandler CCAToCIState.rem CCAToCIState.hasCaptured
      CCAToCIState.cap at hresult
    by_cases hcap : state.2.1 = true
    · simp only [hcap, ↓reduceIte] at hresult
      cases OracleComp.eq_of_mem_supportWith_pure hresult
      refine ⟨trivial, by simp, ?_⟩
      lia
    · simp only [hcap, Bool.false_eq_true, ↓reduceIte] at hresult
      cases hreq : request.1
      · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult
        by_cases hlenEq : ((unframe request.2).length == caller.1.1 &&
            (dropFrame request.2).length == caller.1.1) = true
        · simp only [hlenEq, ↓reduceIte] at hresult
          obtain ⟨ct, hct, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
          obtain ⟨rawCt, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hct
          exact ⟨trivial, (List.length_take_le _ _).trans (by lia), by lia⟩
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte] at hresult
          cases OracleComp.eq_of_mem_supportWith_pure hresult
          exact ⟨trivial, by simp, by lia⟩
      · simp only [hreq, ↓reduceIte] at hresult
        by_cases hzero : (state.1 == 0) = true
        · simp only [hzero, ↓reduceIte] at hresult
          cases OracleComp.eq_of_mem_supportWith_pure hresult
          refine ⟨trivial, by simp, ?_⟩
          simp only [EState, length_encPair, encUnary_apply, List.length_replicate,
            encBool_apply, List.length_singleton, encBits_apply]
          lia
        · simp only [hzero, Bool.false_eq_true, ↓reduceIte] at hresult
          cases OracleComp.eq_of_mem_supportWith_pure hresult
          refine ⟨trivial, by simp, ?_⟩
          enc_len [EState, List.length_singleton]
  have hsample : IsOraclePPTOn (encPair encUnary encBits) encUnary
      (fun caller : ℕ × List Bool =>
        ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Qd caller.1 - 1))) :=
    (isPPTOn_sampleDyadicIndex (ComputableInPolyTime.unary_sub.comp
      (ComputableInPolyTime.prod (hQd.comp (by fun_prop))
        (ComputableInPolyTime.const 1)))).isOraclePPTOn (Operation := Unit)
  have hpost : ComputableInPolyTime
      (fun out : Bool × (ℕ × (Bool × List Bool)) => out.2.2.2)
      (encPair encBool EState) encBits := by
    dsimp only [EState]; fun_prop
  unfold ccaToCIAdversary ccaToCIAtIndexAdversary
  simpa only [bind_pure_comp] using (hsample.bind_with (hrun.map hpost)).isOraclePPT

/-- `ccaToCIHiddenBitAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_ccaToCIHiddenBitAdversary {ctBound Qd : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    (hQd : ComputableInPolyTime Qd encUnary encUnary)
    {adversary : CCAAdversary} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBits (ccaToCIHiddenBitAdversary ctBound Qd adversary) := by
  have hsample : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun _ : ℕ × List Bool => ProbOracleComp.sample (BitString.sampleList 1)) :=
    (ComputableInPolyTime.sampleList
      (ComputableInPolyTime.const 1)).isOraclePPTOn (Operation := Unit)
  have hcond : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => pair.2 == [true])
      (encPair (encPair encUnary encBits) encBits) encBool :=
    ComputableInPolyTime.beq (by fun_prop) (ComputableInPolyTime.const [true])
  have htrue : IsOraclePPTOn (encPair (encPair encUnary encBits) encBits) encBits
      (fun pair : (ℕ × List Bool) × List Bool =>
        ccaToCIAdversary ctBound Qd true adversary pair.1.1 pair.1.2) :=
    (isOraclePPT_ccaToCIAdversary hctBound hQd true hadversary).on.preprocess (by fun_prop)
  have hfalse : IsOraclePPTOn (encPair (encPair encUnary encBits) encBits) encBits
      (fun pair : (ℕ × List Bool) × List Bool =>
        ccaToCIAdversary ctBound Qd false adversary pair.1.1 pair.1.2) :=
    (isOraclePPT_ccaToCIAdversary hctBound hQd false hadversary).on.preprocess (by fun_prop)
  unfold ccaToCIHiddenBitAdversary
  exact (hsample.bind_with (IsOraclePPTOn.cond hcond htrue hfalse)).isOraclePPT

/-! #### Difference-Lemma Hop and Query-Budget Induction for Theorem 9.1

The argument is the same for the full-query and the one-time games, so it is proved for an
admission policy `allow` and instantiated at `fun _ => true` here and at `List.isEmpty` in the
one-time section below. -/

/-- `ccaOracleOn allow` (`reveal = true`) or `ccaRejectOracleOn allow` (`reveal = false`)
instrumented with a sticky Boolean flag `bad` that becomes `true` whenever the adversary submits a
fresh ciphertext `ct` (`!queried.contains ct`) that decrypts to `some _` ([BonehShoup2023],
Section 9.2.3, event $Z$ in Theorem 9.1, in Games 0 and 1). -/
private noncomputable def ccaBadOracleOn (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (reveal : Bool) (n : ℕ) (k : List Bool) (bit : Bool)
    (request : Bool × List Bool) : StateT (List (List Bool) × Bool) ProbComp (List Bool) :=
  fun state =>
    if request.1 then
      if state.1.contains request.2 then
        return ([], state)
      else
        let dec := E.decrypt n k request.2
        return (if reveal then encOption encBits dec else [], (state.1, state.2 || dec.isSome))
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if allow state.1 && (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, (ct :: state.1, state.2))
      else
        return ([], state)

private theorem run_ccaBadOracleOn_true_map_fst (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (n : ℕ) (k : List Bool) (bit : Bool)
    (program : WordOracleComp Bool Bool) (queried : List (List Bool)) (bad : Bool) :
    (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaBadOracleOn allow true n k bit q s))
        program (queried, bad)).map (fun (a, s) => (a, s.1)) =
      ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaOracleOn allow n k bit q s))
        program queried := by
  refine ProbOracleComp.runWith_map_state
    (fun q s => ProbComp.eval (E.ccaBadOracleOn allow true n k bit q s))
    (fun q s => ProbComp.eval (E.ccaOracleOn allow n k bit q s))
    Prod.fst ?_ program (queried, bad)
  intro request state
  cases hreq : request.1
  · simp only [ccaBadOracleOn, ccaOracleOn, hreq, Bool.false_eq_true, ↓reduceIte]
    by_cases hlenEq : (allow state.1 && ((unframe request.2).length == n) &&
        ((dropFrame request.2).length == n)) = true
    · simp [hlenEq, PMF.map_comp, Function.comp_def]
    · simp [hlenEq, PMF.pure_map]
  · simp only [ccaBadOracleOn, ccaOracleOn, hreq, ↓reduceIte]
    split_ifs <;> simp [PMF.pure_map]

private theorem run_ccaBadOracleOn_false_map_fst (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (n : ℕ) (k : List Bool) (bit : Bool)
    (program : WordOracleComp Bool Bool) (queried : List (List Bool)) (bad : Bool) :
    (ProbOracleComp.runWith
        (fun q s => ProbComp.eval (E.ccaBadOracleOn allow false n k bit q s))
        program (queried, bad)).map (fun (a, s) => (a, s.1)) =
      ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaRejectOracleOn allow n k bit q s))
        program queried := by
  refine ProbOracleComp.runWith_map_state
    (fun q s => ProbComp.eval (E.ccaBadOracleOn allow false n k bit q s))
    (fun q s => ProbComp.eval (E.ccaRejectOracleOn allow n k bit q s))
    Prod.fst ?_ program (queried, bad)
  intro request state
  cases hreq : request.1
  · simp only [ccaBadOracleOn, ccaRejectOracleOn, hreq, Bool.false_eq_true, ↓reduceIte]
    by_cases hlenEq : (allow state.1 && ((unframe request.2).length == n) &&
        ((dropFrame request.2).length == n)) = true
    · simp [hlenEq, PMF.map_comp, Function.comp_def]
    · simp [hlenEq, PMF.pure_map]
  · simp only [ccaBadOracleOn, ccaRejectOracleOn, hreq, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> simp [PMF.pure_map]

/-- A step of `ccaBadOracleOn allow reveal` never clears the flag `bad`. -/
private theorem isFlagMonotone_ccaBadOracleOn (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (reveal : Bool) (n : ℕ) (k : List Bool) (bit : Bool) :
    OracleComp.IsFlagMonotone
      (fun q s => ProbComp.eval (E.ccaBadOracleOn allow reveal n k bit q s)) := by
  intro request s x hx
  unfold ccaBadOracleOn at hx
  cases hreq : request.1
  · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hx
    by_cases hlenEq : (allow s && ((unframe request.2).length == n) &&
        ((dropFrame request.2).length == n)) = true
    · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hx
      obtain ⟨_, _, rfl⟩ := hx
      rfl
    · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] at hx
      subst x
      rfl
  · simp only [hreq, ↓reduceIte] at hx
    split_ifs at hx <;>
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hx <;>
      subst x <;>
      simp

/-- Games 0 and 1 of Theorem 9.1 agree until the flag `bad` is raised. -/
private theorem identicalUntilBad_ccaBadOracleOn (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (n : ℕ) (k : List Bool) (bit : Bool) :
    OracleComp.IdenticalUntilBad
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaBadOracleOn allow false n k bit q s)))
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaBadOracleOn allow true n k bit q s)))
      (fun s => s.2 = true) := by
  refine OracleComp.IdenticalUntilBad.sumHandler_lift_left _
    (OracleComp.IdenticalUntilBad.of_flag (E.isFlagMonotone_ccaBadOracleOn allow false n k bit)
      (E.isFlagMonotone_ccaBadOracleOn allow true n k bit) fun request s a s' => ?_)
  cases hreq : request.1
  · simp only [ccaBadOracleOn, hreq, Bool.false_eq_true, ↓reduceIte]
  · simp only [ccaBadOracleOn, hreq, Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · rfl
    · cases hdec : E.decrypt n k request.2 <;>
        simp [Option.isSome, encOption, ProbComp.eval_pure, PMF.pure_apply]

/-- Combined single-step stateful oracle representing `ccaToCIHandler` composed with
`ciEncryptionOracleOn allow` on joint state `(rem, (hasCaptured, capturedCt)) × queriedCiphertexts`.
-/
private noncomputable def ccaToCICombinedOracleOn (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (n : ℕ) (k : List Bool) (bit : Bool)
    (request : Bool × List Bool) :
    StateT ((ℕ × (Bool × List Bool)) × List (List Bool)) ProbComp (List Bool) :=
  fun state =>
    if state.1.2.1 then
      return ([], state)
    else
      if request.1 then
        if state.1.1 == 0 then
          return ([], ((0, (true, request.2)), state.2))
        else
          return ([], ((state.1.1 - 1, (false, [])), state.2))
      else
        let m0 := unframe request.2
        let m1 := dropFrame request.2
        if allow state.2 && (m0.length == n) && (m1.length == n) then do
          let ct ← E.encrypt n k (if bit then m1 else m0)
          return (ct, (state.1, ct :: state.2))
        else
          return ([], state)

/-- Once `hasCaptured = true` holds in `ccaToCICombinedOracleOn allow`, both `capturedCt` and
`queried` remain frozen across any subsequent computation `program`. -/
private theorem ciCombinedOn_captured_bind_eq_one {α : Type} (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (n : ℕ) (k : List Bool) (bit : Bool)
    (program : WordOracleComp Bool α) (rem : ℕ) (ct : List Bool) (queried : List (List Bool))
    (hwin : (!queried.contains ct && (E.decrypt n k ct).isSome) = true) :
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaToCICombinedOracleOn allow n k bit q s)))
      program).run ((rem, (true, ct)), queried)).bind
      (fun x => PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome)) true =
      1 := by
  refine le_antisymm (PMF.coe_le_one _ _) (PMF.le_bind_apply_on_support _ fun x hx => ?_)
  have hinv := ProbOracleComp.run_interpret_invariant
    (fun q s => ProbComp.eval (E.ccaToCICombinedOracleOn allow n k bit q s))
    (fun s => s.1.2 = (true, ct) ∧ s.2 = queried)
    (fun q s ⟨hcap, hq⟩ a s' hs' => by
      have hcap1 : s.1.2.1 = true := by rw [hcap]
      simp only [ccaToCICombinedOracleOn, hcap1, ↓reduceIte, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] at hs'
      cases hs'
      exact ⟨hcap, hq⟩)
    program ((rem, (true, ct)), queried) ⟨rfl, rfl⟩ x.1 x.2 hx
  have hct : x.2.1.2.2 = ct := by rw [hinv.1]
  rw [hct, hinv.2, hwin, PMF.pure_apply_self]

private theorem eval_ccaBadOracleOn_false (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (n : ℕ) (k : List Bool) (bit : Bool)
    (request : Bool × List Bool) (queried : List (List Bool)) :
    ProbComp.eval (E.ccaBadOracleOn allow false n k bit request (queried, false)) =
      if request.1 then
        if queried.contains request.2 then
          PMF.pure ([], (queried, false))
        else
          PMF.pure ([], (queried, (E.decrypt n k request.2).isSome))
      else
        if (allow queried && ((unframe request.2).length == n) &&
            ((dropFrame request.2).length == n)) = true then
          (ProbComp.eval (E.encrypt n k
            (if bit then dropFrame request.2 else unframe request.2))).bind
            (fun ct => PMF.pure (ct, (ct :: queried, false)))
        else
          PMF.pure ([], (queried, false)) := by
  unfold ccaBadOracleOn
  cases hreq : request.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> simp only [ProbComp.eval_bind, ProbComp.eval_pure]
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or]
    split_ifs <;> simp only [ProbComp.eval_pure]

private theorem eval_ccaToCICombinedOracleOn_false (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (n : ℕ) (k : List Bool) (bit : Bool)
    (request : Bool × List Bool) (j : ℕ) (queried : List (List Bool)) :
    ProbComp.eval (E.ccaToCICombinedOracleOn allow n k bit request ((j, (false, [])), queried)) =
      if request.1 then
        PMF.pure ([], ((if j = 0 then (0, (true, request.2)) else (j - 1, (false, []))), queried))
      else
        if (allow queried && ((unframe request.2).length == n) &&
            ((dropFrame request.2).length == n)) = true then
          (ProbComp.eval (E.encrypt n k
            (if bit then dropFrame request.2 else unframe request.2))).bind
            (fun ct => PMF.pure (ct, ((j, (false, [])), ct :: queried)))
        else
          PMF.pure ([], ((j, (false, [])), queried)) := by
  unfold ccaToCICombinedOracleOn
  cases hreq : request.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> simp only [ProbComp.eval_bind, ProbComp.eval_pure]
  · by_cases hj : j = 0
    · subst hj
      simp only [Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, ProbComp.eval_pure]
    · have hj' : (j == 0) = false := beq_eq_false_iff_ne.mpr hj
      simp only [Bool.false_eq_true, ↓reduceIte, hj, hj', ProbComp.eval_pure]

/-- Weighted continuation of a finite-sum bound: if `bad a ≤ ∑ j ∈ s, win j a` for every outcome
`a`, then averaging with weights `μ` gives `∑' a, μ a * bad a ≤ ∑ j ∈ s, ∑' a, μ a * win j a`.
The random-coin and encryption steps of the decryption-query induction below use it. -/
private theorem tsum_mul_le_sum_tsum_mul {β ι : Type*} (μ : β → ℝ≥0∞) (s : Finset ι)
    {bad : β → ℝ≥0∞} {win : ι → β → ℝ≥0∞} (h : ∀ a, bad a ≤ ∑ j ∈ s, win j a) :
    ∑' a, μ a * bad a ≤ ∑ j ∈ s, ∑' a, μ a * win j a := by
  calc ∑' a, μ a * bad a ≤ ∑' a, μ a * ∑ j ∈ s, win j a :=
        tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (h a) zero_le
    _ = ∑ j ∈ s, ∑' a, μ a * win j a := by
        simp only [Finset.mul_sum]
        exact Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable

/-- Decryption-query induction for [BonehShoup2023], Theorem 9.1: for any program `program` making
at most `Qd` decryption queries, the probability of reaching `bad = true` under
`ccaBadOracleOn allow false` from `(queried, false)` is bounded by the sum over
decryption-query indices `j ∈ Finset.range Qd` of the CI winning probability under
`ccaToCICombinedOracleOn allow` from `((j, (false, [])), queried)`. -/
private theorem bad_ccaBadOracleOn_le_sum_ciCombinedOn {α : Type} (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (n : ℕ) (k : List Bool) (bit : Bool)
    {program : WordOracleComp Bool α} {Qd : ℕ}
    (hq : IsDecryptionQueryBounded program Qd) (queried : List (List Bool)) :
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaBadOracleOn allow false n k bit q s)))
      program).run (queried, false)).toOuterMeasure {x | x.2.2 = true} ≤
      ∑ j ∈ Finset.range Qd,
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.ccaToCICombinedOracleOn allow n k bit q s)))
          program).run ((j, (false, [])), queried)).bind
          (fun x => PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome))
          true := by
  induction hq generalizing queried with
  | pure a Q =>
    simp only [OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq, Bool.false_eq_true, ↓reduceIte, zero_le]
  | liftBind q cont Q hcont ih =>
    cases q with
    | inl m =>
      simp only [Sum.elim_inl, Nat.add_zero, OracleComp.run_interpret_bind,
        OracleComp.run_interpret_query, OracleComp.sumHandler, StateT.lift,
        Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
        PMF.bind_bind, PMF.pure_bind, PMF.toOuterMeasure_bind_apply, PMF.bind_apply]
      exact (tsum_mul_le_sum_tsum_mul _ _ fun a => ih a queried).trans_eq
        (Finset.sum_congr rfl fun j _ => by simp only [PMF.bind_apply])
    | inr request =>
      simp only [Sum.elim_inr, OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
        OracleComp.sumHandler]
      simp only [eval_ccaBadOracleOn_false, eval_ccaToCICombinedOracleOn_false]
      cases hreq : request.1
      · -- An encryption query costs nothing and keeps every countdown.
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        by_cases hlenEq : (allow queried && ((unframe request.2).length == n) &&
            ((dropFrame request.2).length == n)) = true
        · simp only [hlenEq, ↓reduceIte,
            Probability.PMF.monad_bind_eq_bind,
            PMF.bind_bind, PMF.pure_bind, PMF.toOuterMeasure_bind_apply]
          exact (tsum_mul_le_sum_tsum_mul _ _ fun ct => ih ct (ct :: queried)).trans_eq
            (Finset.sum_congr rfl fun j _ => by simp only [PMF.bind_apply])
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte,
            Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
          exact ih [] queried
      · -- A decryption query costs one; the index `0` captures it.
        simp only [↓reduceIte]
        rw [Finset.sum_range_succ']
        simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel,
          Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
        by_cases hmem : queried.contains request.2 = true
        · simp only [hmem, ↓reduceIte, PMF.pure_bind]
          exact (ih [] queried).trans le_self_add
        · simp only [hmem, Bool.false_eq_true, ↓reduceIte, PMF.pure_bind]
          by_cases hsome : (E.decrypt n k request.2).isSome = true
          · simp only [hsome]
            have hwin :
                (!queried.contains request.2 && (E.decrypt n k request.2).isSome) = true := by
              rw [Bool.eq_false_iff.mpr hmem, hsome]
              rfl
            rw [ciCombinedOn_captured_bind_eq_one E allow n k bit (cont []) 0 request.2 queried
              hwin]
            exact (Cslib.Probability.PMF.toOuterMeasure_le_one _ _).trans le_add_self
          · have hnotSome : (E.decrypt n k request.2).isSome = false :=
              Bool.eq_false_iff.mpr hsome
            simp only [hnotSome]
            exact (ih [] queried).trans le_self_add

/-- When `ctBound n` bounds all ciphertext lengths produced by `E.encrypt n k` on `n`-bit messages,
running `ccaToCIAtIndexAdversary ctBound j bit adversary` in `ciGameOn allow` under key `k` has the
same winning distribution as `ccaToCICombinedOracleOn allow` from `((j, (false, [])), [])`. -/
private theorem eval_ciGameOn_ccaToCIAtIndexAdversary_key (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (ctBound : ℕ → ℕ) (j : ℕ) (bit : Bool)
    (adversary : CCAAdversary) (n : ℕ) (k : List Bool)
    (hk : k ∈ (ProbComp.eval (E.keyGen n)).support)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciEncryptionOracleOn allow n k q s))
        (ccaToCIAtIndexAdversary ctBound j bit adversary n []) []).bind
      (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) =
      (ProbOracleComp.runWith
          (fun q s => ProbComp.eval (E.ccaToCICombinedOracleOn allow n k bit q s))
          (adversary n []) ((j, (false, [])), [])).bind
        (fun x => PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome)) := by
  unfold ccaToCIAtIndexAdversary
  rw [ProbOracleComp.runWith_bind]
  simp only [ProbOracleComp.runWith_pure, PMF.bind_bind, PMF.pure_bind]
  rw [ProbOracleComp.runWith_run_interpret]
  simp only [PMF.bind_map, Function.comp_def]
  congr 1
  congr 2 with request state : 2
  change (ProbOracleComp.runWith
      (fun q s => ProbComp.eval (E.ciEncryptionOracleOn allow n k q s))
      (ccaToCIHandler n (ctBound n) bit request state.1) state.2).map
    (fun result => (result.1.1, result.1.2, result.2)) =
    ProbComp.eval (E.ccaToCICombinedOracleOn allow n k bit request state)
  unfold ccaToCIHandler ccaToCICombinedOracleOn CCAToCIState.rem CCAToCIState.hasCaptured
    CCAToCIState.cap
  by_cases hcap : state.1.2.1 = true
  · simp only [hcap, ↓reduceIte, ProbOracleComp.runWith_pure, ProbComp.eval_pure, PMF.pure_map]
  · simp only [hcap, Bool.false_eq_true, ↓reduceIte]
    cases hreq : request.1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hlenEq : ((unframe request.2).length == n &&
          (dropFrame request.2).length == n) = true
      · simp only [hlenEq, ↓reduceIte, Functor.map_map, ProbOracleComp.runWith_map,
          ProbOracleComp.runWith_query, ciEncryptionOracleOn]
        simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
        have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
          cases bit <;> simp [hlenEq]
        have hmbEq : ((if bit then dropFrame request.2 else unframe request.2).length == n) =
            true := beq_iff_eq.mpr hmbLen
        by_cases hallow : allow state.2 = true
        · have hcond : (allow state.2 && ((unframe request.2).length == n) &&
              ((dropFrame request.2).length == n)) = true := by
            simp [hallow, hlenEq]
          have hciCond : (allow state.2 &&
              ((if bit then dropFrame request.2 else unframe request.2).length == n)) =
              true := by
            rw [hallow, hmbEq]; rfl
          simp only [hcond, hciCond, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.map_bind, PMF.pure_map, Prod.map_apply, id_eq]
          apply PMF.bind_congr_on_support
          intro ct hct
          rw [List.take_of_length_le (hctBound k hk _ hmbLen ct hct)]
        · have hcond : (allow state.2 && ((unframe request.2).length == n) &&
              ((dropFrame request.2).length == n)) = false := by
            rw [Bool.eq_false_iff.mpr hallow, Bool.false_and, Bool.false_and]
          have hciCond : (allow state.2 &&
              ((if bit then dropFrame request.2 else unframe request.2).length == n)) =
              false := by
            rw [Bool.eq_false_iff.mpr hallow, Bool.false_and]
          simp only [hcond, hciCond, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            PMF.pure_map, List.take_nil, Prod.map_apply, id_eq]
      · have hcond : (allow state.2 && ((unframe request.2).length == n) &&
            ((dropFrame request.2).length == n)) = false := by
          rw [Bool.and_assoc, Bool.eq_false_iff.mpr hlenEq, Bool.and_false]
        simp only [hcond, hlenEq, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_pure,
          ProbComp.eval_pure, PMF.pure_map]
    · by_cases hzero : (state.1.1 == 0) = true <;>
        simp only [hzero, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_pure,
          ProbComp.eval_pure, PMF.pure_map]

/-- The decryption-rejection hop for an admission policy `allow`: the advantage between
`ccaGameOn allow` and `ccaRejectGameOn allow` is at most the sum over `j < Qd n` of the CI winning
probabilities of `ccaToCIAtIndexAdversary ctBound j bit adversary` in `ciGameOn allow`. -/
private theorem advantage_ccaGameOn_ccaRejectGameOn_le_sum (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (ctBound Qd : ℕ → ℕ)
    (adversary : CCAAdversary) (bit : Bool) (n : ℕ)
    (hq : IsDecryptionQueryBounded (adversary n []) (Qd n))
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.advantage (ProbComp.eval (E.ccaGameOn allow adversary bit n))
        (ProbComp.eval (E.ccaRejectGameOn allow adversary bit n)) : ℝ) ≤
      ∑ j ∈ Finset.range (Qd n),
        (Game.succProbability
          (ProbComp.eval (E.ciGameOn allow (ccaToCIAtIndexAdversary ctBound j bit adversary) n)) :
          ℝ) := by
  have hccaEq (k : List Bool) :
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaOracleOn allow n k bit q s))
          (adversary n []) []).bind (fun out => PMF.pure out.1) =
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaBadOracleOn allow true n k bit q s))
          (adversary n []) ([], false)).bind (fun out => PMF.pure out.1) := by
    rw [← run_ccaBadOracleOn_true_map_fst E allow n k bit (adversary n []) [] false,
      PMF.bind_map, Function.comp_def]
  have hrejEq (k : List Bool) :
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaRejectOracleOn allow n k bit q s))
          (adversary n []) []).bind (fun out => PMF.pure out.1) =
      (ProbOracleComp.runWith
          (fun q s => ProbComp.eval (E.ccaBadOracleOn allow false n k bit q s))
          (adversary n []) ([], false)).bind (fun out => PMF.pure out.1) := by
    rw [← run_ccaBadOracleOn_false_map_fst E allow n k bit (adversary n []) [] false,
      PMF.bind_map, Function.comp_def]
  set pCCA := ProbComp.eval (E.ccaGameOn allow adversary bit n) true
  set pRej := ProbComp.eval (E.ccaRejectGameOn allow adversary bit n) true
  set pSum : ℝ≥0∞ := ∑ j ∈ Finset.range (Qd n),
    ProbComp.eval (E.ciGameOn allow (ccaToCIAtIndexAdversary ctBound j bit adversary) n) true
  have hsum_eq : pSum = ∑' k : List Bool, ProbComp.eval (E.keyGen n) k *
      ∑ j ∈ Finset.range (Qd n),
        (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciEncryptionOracleOn allow n k q s))
            (ccaToCIAtIndexAdversary ctBound j bit adversary n []) []).bind
          (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) true := by
    simp only [pSum, ciGameOn, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.eval_run_interpret_eq_runWith]
    conv_lhs =>
      arg 2; ext j
      rw [PMF.bind_apply]
    rw [← Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
    refine tsum_congr fun k => ?_
    rw [Finset.mul_sum]
  have hCCA_eq : pCCA = ∑' k : List Bool, ProbComp.eval (E.keyGen n) k *
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaBadOracleOn allow true n k bit q s))
          (adversary n []) ([], false)).bind (fun out => PMF.pure out.1) true := by
    simp only [pCCA, ccaGameOn, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.eval_run_interpret_eq_runWith, hccaEq]
    exact PMF.bind_apply _ _ _
  have hRej_eq : pRej = ∑' k : List Bool, ProbComp.eval (E.keyGen n) k *
      (ProbOracleComp.runWith
          (fun q s => ProbComp.eval (E.ccaBadOracleOn allow false n k bit q s))
          (adversary n []) ([], false)).bind (fun out => PMF.pure out.1) true := by
    simp only [pRej, ccaRejectGameOn, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.eval_run_interpret_eq_runWith, hrejEq]
    exact PMF.bind_apply _ _ _
  -- The bad event of the all-reject run is bounded by the CI sum, key by key.
  have hbad (k : List Bool) (hk : k ∈ (ProbComp.eval (E.keyGen n)).support) :
      ((ProbOracleComp.runWith
          (fun q s => ProbComp.eval (E.ccaBadOracleOn allow false n k bit q s))
          (adversary n []) ([], false)).toOuterMeasure {x | x.2.2 = true}) ≤
        ∑ j ∈ Finset.range (Qd n),
          (ProbOracleComp.runWith
              (fun q s => ProbComp.eval (E.ciEncryptionOracleOn allow n k q s))
              (ccaToCIAtIndexAdversary ctBound j bit adversary n []) []).bind
            (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome))
            true := by
    have h := bad_ccaBadOracleOn_le_sum_ciCombinedOn E allow n k bit hq []
    rw [← ProbOracleComp.runWith_eq_run_interpret] at h
    refine h.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_ciGameOn_ccaToCIAtIndexAdversary_key E allow ctBound j bit adversary n k hk hctBound,
      ProbOracleComp.runWith_eq_run_interpret]
  have hiub (k : List Bool) := identicalUntilBad_ccaBadOracleOn E allow n k bit
  have hle1 : pCCA ≤ pRej + pSum := by
    rw [hCCA_eq, hRej_eq, hsum_eq, ← tsum_add]
    refine tsum_le_tsum fun k => ?_
    rw [← mul_add]
    by_cases hk : k ∈ (ProbComp.eval (E.keyGen n)).support
    · refine mul_le_mul_of_nonneg_left ?_ zero_le
      have hstep := (hiub k).symm.bind_apply_le (adversary n []) ([], false)
        (fun out => PMF.pure out.1) true
      rw [← (hiub k).bad_eq, ← ProbOracleComp.runWith_eq_run_interpret,
        ← ProbOracleComp.runWith_eq_run_interpret] at hstep
      exact hstep.trans (add_le_add le_rfl (hbad k hk))
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hk, zero_mul, zero_mul]
  have hle2 : pRej ≤ pCCA + pSum := by
    rw [hCCA_eq, hRej_eq, hsum_eq, ← tsum_add]
    refine tsum_le_tsum fun k => ?_
    rw [← mul_add]
    by_cases hk : k ∈ (ProbComp.eval (E.keyGen n)).support
    · refine mul_le_mul_of_nonneg_left ?_ zero_le
      have hstep := (hiub k).bind_apply_le (adversary n []) ([], false)
        (fun out => PMF.pure out.1) true
      rw [← ProbOracleComp.runWith_eq_run_interpret,
        ← ProbOracleComp.runWith_eq_run_interpret] at hstep
      exact hstep.trans (add_le_add le_rfl (hbad k hk))
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hk, zero_mul, zero_mul]
  have hpSum_ne_top : pSum ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ => PMF.apply_ne_top _ _
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, hpSum_ne_top⟩) hle1
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, hpSum_ne_top⟩) hle2
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) hpSum_ne_top] at h1 h2
  have habs : |pCCA.toReal - pRej.toReal| ≤ pSum.toReal :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  rw [Game.coe_advantage]
  simpa only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, pCCA, pRej, pSum,
    ENNReal.toReal_sum (fun j _ => PMF.apply_ne_top _ _)] using habs

/-- **Decryption-rejection hop.** If a CCA adversary makes at most `Qd n` decryption queries and
`ctBound n` bounds the ciphertext lengths of `n`-bit messages, its advantage between `ccaGame` and
`ccaRejectGame` (which rejects every decryption query) at bit `bit` is at most the sum over
`j < Qd n` of the CI winning probabilities of `ccaToCIAtIndexAdversary ctBound j bit adversary`
([BonehShoup2023], Section 9.2.3, the bound $|\Pr[W_0] - \Pr[W_1]| \leq \Pr[Z]$ in the proof of
Theorem 9.1, printed p. 364, for a fixed bit).
Use it with `sum_succProbability_ccaToCIAtIndexAdversary_le` to remove the decryption oracle
from a reduction to `CiphertextIntegrity`. -/
theorem advantage_ccaGame_ccaRejectGame_le_sum (E : SymmetricCipher) (ctBound Qd : ℕ → ℕ)
    (adversary : CCAAdversary) (bit : Bool) (n : ℕ)
    (hq : IsDecryptionQueryBounded (adversary n []) (Qd n))
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.advantage (ProbComp.eval (E.ccaGame adversary bit n))
        (ProbComp.eval (E.ccaRejectGame adversary bit n)) : ℝ) ≤
      ∑ j ∈ Finset.range (Qd n),
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIAtIndexAdversary ctBound j bit adversary) n)) : ℝ) := by
  rw [ccaGame_eq_on, ccaRejectGame_eq_on, ciGame_eq_on]
  exact E.advantage_ccaGameOn_ccaRejectGameOn_le_sum _ ctBound Qd adversary bit n hq hctBound

/-- Running `ccaToCIAdversary` in `ciGameOn allow` averages `ccaToCIAtIndexAdversary` uniformly
over `Fin (dyadicSize (Qd n - 1))`. -/
private theorem eval_ciGameOn_ccaToCIAdversary (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (ctBound Qd : ℕ → ℕ) (bit : Bool) (adversary : CCAAdversary)
    (n : ℕ) :
    ProbComp.eval (E.ciGameOn allow (ccaToCIAdversary ctBound Qd bit adversary) n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (Qd n - 1)))).bind
        (fun i => ProbComp.eval
          (E.ciGameOn allow (ccaToCIAtIndexAdversary ctBound i.val bit adversary) n)) := by
  simp only [ciGameOn, ccaToCIAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret_eq_runWith]
  have hsample (k : List Bool) :
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciEncryptionOracleOn allow n k q s))
        (do
          let j ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Qd n - 1))
          ccaToCIAtIndexAdversary ctBound j bit adversary n []) []).bind
        (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) =
      (PMF.uniformOfFintype (Fin (dyadicSize (Qd n - 1)))).bind (fun i =>
        (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciEncryptionOracleOn allow n k q s))
            (ccaToCIAtIndexAdversary ctBound i.val bit adversary n []) []).bind
          (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome))) := by
    rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, ProbComp.eval_sampleDyadicIndex]
    simp only [PMF.bind_map, Function.comp_def, PMF.bind_bind]
  simp only [hsample]
  exact PMF.bind_comm _ _ _

/-- Running `ccaToCIAdversary` in `ciGame` averages `ccaToCIAtIndexAdversary` uniformly over
`Fin (dyadicSize (Qd n - 1))`. -/
theorem eval_ciGame_ccaToCIAdversary (E : SymmetricCipher) (ctBound Qd : ℕ → ℕ)
    (bit : Bool) (adversary : CCAAdversary) (n : ℕ) :
    ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Qd bit adversary) n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (Qd n - 1)))).bind
        (fun i =>
          ProbComp.eval (E.ciGame (ccaToCIAtIndexAdversary ctBound i.val bit adversary) n)) := by
  rw [ciGame_eq_on]
  exact E.eval_ciGameOn_ccaToCIAdversary _ ctBound Qd bit adversary n

/-- `sum_succProbability_ccaToCIAtIndexAdversary_le` for an admission policy `allow`. -/
private theorem sum_succProbability_ciGameOn_ccaToCIAtIndexAdversary_le (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (ctBound Qd : ℕ → ℕ) (bit : Bool) (adversary : CCAAdversary)
    (n : ℕ) :
    (∑ j ∈ Finset.range (Qd n),
      (Game.succProbability
        (ProbComp.eval (E.ciGameOn allow (ccaToCIAtIndexAdversary ctBound j bit adversary) n)) :
        ℝ)) ≤
      (dyadicSize (Qd n - 1) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGameOn allow (ccaToCIAdversary ctBound Qd bit adversary) n)) :
          ℝ) := by
  have hcap : (dyadicSize (Qd n - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (dyadicSize_pos (Qd n - 1)).ne'
  rw [eval_ciGameOn_ccaToCIAdversary, Game.succProbability_uniform, NNReal.coe_div,
    NNReal.coe_sum, NNReal.coe_natCast, Fintype.card_fin, mul_div_cancel₀ _ hcap,
    Fin.sum_univ_eq_sum_range
      (fun j => (Game.succProbability
        (ProbComp.eval (E.ciGameOn allow (ccaToCIAtIndexAdversary ctBound j bit adversary) n)) :
        ℝ))]
  have hsub : Finset.range (Qd n) ⊆ Finset.range (dyadicSize (Qd n - 1)) := by
    intro x hx
    have hx' := Finset.mem_range.mp hx
    have hlt := lt_dyadicSize (Qd n - 1)
    exact Finset.mem_range.mpr (by lia)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => NNReal.coe_nonneg _

/-- The sum of CI winning probabilities over the decryption-query indices `j < Qd n` is at most
`dyadicSize (Qd n - 1)` times the CI winning probability of the single adversary
`ccaToCIAdversary`, which samples the index uniformly below `dyadicSize (Qd n - 1) ≥ Qd n`. Use it
after `advantage_ccaGame_ccaRejectGame_le_sum` to bound the decryption-rejection hop by one CI
adversary. -/
theorem sum_succProbability_ccaToCIAtIndexAdversary_le (E : SymmetricCipher)
    (ctBound Qd : ℕ → ℕ) (bit : Bool) (adversary : CCAAdversary) (n : ℕ) :
    (∑ j ∈ Finset.range (Qd n),
      (Game.succProbability
        (ProbComp.eval (E.ciGame (ccaToCIAtIndexAdversary ctBound j bit adversary) n)) : ℝ)) ≤
      (dyadicSize (Qd n - 1) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Qd bit adversary) n)) : ℝ) := by
  rw [ciGame_eq_on]
  exact E.sum_succProbability_ciGameOn_ccaToCIAtIndexAdversary_le _ ctBound Qd bit adversary n

/-- The CCA advantage bound in sum form for an admission policy `allow`, with the all-reject hybrid
games replaced by CPA games `cpa` of the same law: the CPA advantage plus, for each bit, the sum
over `j < Qd n` of the CI winning probabilities of `ccaToCIAtIndexAdversary`. -/
private theorem advantage_ccaGameOn_le_sum (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (ctBound Qd : ℕ → ℕ) (adversary : CCAAdversary) (n : ℕ)
    (cpa : Bool → ProbComp Bool)
    (hcpa : ∀ bit,
      ProbComp.eval (cpa bit) = ProbComp.eval (E.ccaRejectGameOn allow adversary bit n))
    (hq : IsDecryptionQueryBounded (adversary n []) (Qd n))
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.advantage (ProbComp.eval (E.ccaGameOn allow adversary false n))
        (ProbComp.eval (E.ccaGameOn allow adversary true n)) : ℝ) ≤
      (∑ j ∈ Finset.range (Qd n), (Game.succProbability (ProbComp.eval
        (E.ciGameOn allow (ccaToCIAtIndexAdversary ctBound j false adversary) n)) : ℝ)) +
      (Game.advantage (ProbComp.eval (cpa false)) (ProbComp.eval (cpa true)) : ℝ) +
      ∑ j ∈ Finset.range (Qd n), (Game.succProbability (ProbComp.eval
        (E.ciGameOn allow (ccaToCIAtIndexAdversary ctBound j true adversary) n)) : ℝ) := by
  have hfalse :=
    E.advantage_ccaGameOn_ccaRejectGameOn_le_sum allow ctBound Qd adversary false n hq hctBound
  have htrue :=
    E.advantage_ccaGameOn_ccaRejectGameOn_le_sum allow ctBound Qd adversary true n hq hctBound
  rw [hcpa false, hcpa true]
  game_trans
    [ProbComp.eval (E.ccaRejectGameOn allow adversary false n),
     ProbComp.eval (E.ccaRejectGameOn allow adversary true n)]
    using [hfalse, le_rfl, htrue]

/-- `advantage_ccaGame_le` for an admission policy `allow` and CPA games `cpa` with the laws of the
all-reject hybrid games. -/
private theorem advantage_ccaGameOn_le (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (ctBound Qd : ℕ → ℕ) (adversary : CCAAdversary) (n : ℕ)
    (cpa : Bool → ProbComp Bool)
    (hcpa : ∀ bit,
      ProbComp.eval (cpa bit) = ProbComp.eval (E.ccaRejectGameOn allow adversary bit n))
    (hq : IsDecryptionQueryBounded (adversary n []) (Qd n))
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.advantage (ProbComp.eval (E.ccaGameOn allow adversary false n))
        (ProbComp.eval (E.ccaGameOn allow adversary true n)) : ℝ) ≤
      (dyadicSize (Qd n - 1) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGameOn allow (ccaToCIAdversary ctBound Qd false adversary) n)) :
          ℝ) +
      (Game.advantage (ProbComp.eval (cpa false)) (ProbComp.eval (cpa true)) : ℝ) +
      (dyadicSize (Qd n - 1) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGameOn allow (ccaToCIAdversary ctBound Qd true adversary) n)) :
          ℝ) := by
  have h := E.advantage_ccaGameOn_le_sum allow ctBound Qd adversary n cpa hcpa hq hctBound
  have hfalse :=
    E.sum_succProbability_ciGameOn_ccaToCIAtIndexAdversary_le allow ctBound Qd false adversary n
  have htrue :=
    E.sum_succProbability_ciGameOn_ccaToCIAtIndexAdversary_le allow ctBound Qd true adversary n
  linarith

/-- **Quantitative AE $\Rightarrow$ CCA bound with one CI adversary per bit** ([BonehShoup2023],
Section 9.2.3, Theorem 9.1, printed pp. 363–365): for any `CCAAdversary` making at most `Qd n`
decryption queries at security parameter `n`, the adaptive CCA distinguishing advantage is bounded
by the CPA advantage of `ccaToCPAAdversary` plus `dyadicSize (Qd n - 1)` times the
ciphertext-integrity winning probabilities of `ccaToCIAdversary` for `bit = false` and
`bit = true`. -/
theorem advantage_ccaGame_le (E : SymmetricCipher) (ctBound Qd : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ)
    (hq : IsDecryptionQueryBounded (adversary n []) (Qd n))
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.advantage (ProbComp.eval (E.ccaGame adversary false n))
        (ProbComp.eval (E.ccaGame adversary true n)) : ℝ) ≤
      (dyadicSize (Qd n - 1) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Qd false adversary) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) false n))
        (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) true n)) : ℝ) +
      (dyadicSize (Qd n - 1) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Qd true adversary) n)) : ℝ) := by
  rw [ccaGame_eq_on, ciGame_eq_on]
  exact E.advantage_ccaGameOn_le _ ctBound Qd adversary n
    (fun b => E.cpaGame (ccaToCPAAdversary ctBound adversary) b n)
    (E.eval_cpaGame_ccaToCPAAdversary_on ctBound adversary n hctBound) hq hctBound

/-- Running `ccaToCIHiddenBitAdversary` in `ciGameOn allow` averages `ccaToCIAdversary` uniformly
over `bit : Bool`. -/
private theorem eval_ciGameOn_ccaToCIHiddenBitAdversary (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (ctBound Qd : ℕ → ℕ) (adversary : CCAAdversary) (n : ℕ) :
    ProbComp.eval (E.ciGameOn allow (ccaToCIHiddenBitAdversary ctBound Qd adversary) n) =
      (PMF.uniformOfFintype Bool).bind
        (fun bit =>
          ProbComp.eval (E.ciGameOn allow (ccaToCIAdversary ctBound Qd bit adversary) n)) := by
  simp only [ciGameOn, ccaToCIHiddenBitAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret_eq_runWith]
  have hsample (k : List Bool) :
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciEncryptionOracleOn allow n k q s))
        (do
          let bits ← ProbOracleComp.sample (BitString.sampleList 1)
          if bits == [true] then
            ccaToCIAdversary ctBound Qd true adversary n []
          else
            ccaToCIAdversary ctBound Qd false adversary n []) []).bind
        (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) =
      (PMF.uniformOfFintype Bool).bind (fun bit =>
        (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciEncryptionOracleOn allow n k q s))
            (ccaToCIAdversary ctBound Qd bit adversary n []) []).bind
          (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome))) := by
    rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
      BitString.eval_sampleList, BitString.uniformList_succ 0, BitString.uniformList_zero]
    simp only [PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind]
    congr 1 with bit : 1
    cases bit <;> rfl
  simp only [hsample]
  exact PMF.bind_comm _ _ _

/-- Running `ccaToCIHiddenBitAdversary` in `ciGame` averages `ccaToCIAdversary` uniformly over
`bit : Bool`. -/
theorem eval_ciGame_ccaToCIHiddenBitAdversary (E : SymmetricCipher) (ctBound Qd : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ) :
    ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Qd adversary) n) =
      (PMF.uniformOfFintype Bool).bind
        (fun bit => ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Qd bit adversary) n)) := by
  rw [ciGame_eq_on]
  exact E.eval_ciGameOn_ccaToCIHiddenBitAdversary _ ctBound Qd adversary n

/-- `advantage_ccaGame_le_two_mul` for an admission policy `allow` and CPA games `cpa` with the
laws of the all-reject hybrid games. -/
private theorem advantage_ccaGameOn_le_two_mul (E : SymmetricCipher)
    (allow : List (List Bool) → Bool) (ctBound Qd : ℕ → ℕ) (adversary : CCAAdversary) (n : ℕ)
    (cpa : Bool → ProbComp Bool)
    (hcpa : ∀ bit,
      ProbComp.eval (cpa bit) = ProbComp.eval (E.ccaRejectGameOn allow adversary bit n))
    (hq : IsDecryptionQueryBounded (adversary n []) (Qd n))
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.advantage (ProbComp.eval (E.ccaGameOn allow adversary false n))
        (ProbComp.eval (E.ccaGameOn allow adversary true n)) : ℝ) ≤
      (Game.advantage (ProbComp.eval (cpa false)) (ProbComp.eval (cpa true)) : ℝ) +
      2 * (dyadicSize (Qd n - 1) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGameOn allow (ccaToCIHiddenBitAdversary ctBound Qd adversary) n)) :
          ℝ) := by
  have hmain := E.advantage_ccaGameOn_le allow ctBound Qd adversary n cpa hcpa hq hctBound
  have havg : 2 * (Game.succProbability
      (ProbComp.eval (E.ciGameOn allow (ccaToCIHiddenBitAdversary ctBound Qd adversary) n)) : ℝ) =
      (Game.succProbability
        (ProbComp.eval (E.ciGameOn allow (ccaToCIAdversary ctBound Qd false adversary) n)) : ℝ) +
      (Game.succProbability
        (ProbComp.eval (E.ciGameOn allow (ccaToCIAdversary ctBound Qd true adversary) n)) : ℝ) := by
    rw [eval_ciGameOn_ccaToCIHiddenBitAdversary, Game.succProbability_uniform,
      NNReal.coe_div, NNReal.coe_sum, NNReal.coe_natCast, Fintype.card_bool,
      Fintype.sum_bool]
    ring
  linear_combination hmain - (dyadicSize (Qd n - 1) : ℝ) * havg

/-- **Quantitative AE $\Rightarrow$ CCA bound** ([BonehShoup2023], Section 9.2.3, Theorem 9.1,
equation (9.3), printed p. 363): for any `CCAAdversary` making at most `Qd n` decryption queries at
security parameter `n`,
`CCAadv ≤ CPAadv[ccaToCPAAdversary] + 2 * dyadicSize (Qd n - 1) * CIadv[ccaToCIHiddenBitAdversary]`.
The book's factor `2 Qd` becomes `2 * dyadicSize (Qd n - 1)`: `ccaToCIHiddenBitAdversary` draws
its decryption-query index uniformly from fair coins, so the range is `2` when `Qd n ≤ 1`, and
otherwise the least power of two that is at least `Qd n` (at most `2 * Qd n` once `Qd n ≥ 1`). -/
theorem advantage_ccaGame_le_two_mul (E : SymmetricCipher) (ctBound Qd : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ)
    (hq : IsDecryptionQueryBounded (adversary n []) (Qd n))
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.advantage (ProbComp.eval (E.ccaGame adversary false n))
        (ProbComp.eval (E.ccaGame adversary true n)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) false n))
        (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) true n)) : ℝ) +
      2 * (dyadicSize (Qd n - 1) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Qd adversary) n)) : ℝ) := by
  rw [ccaGame_eq_on, ciGame_eq_on]
  exact E.advantage_ccaGameOn_le_two_mul _ ctBound Qd adversary n
    (fun b => E.cpaGame (ccaToCPAAdversary ctBound adversary) b n)
    (E.eval_cpaGame_ccaToCPAAdversary_on ctBound adversary n hctBound) hq hctBound

/-- Halving a two-sided advantage bound: if the advantage between `e false` and `e true` is at most
the advantage between `e' false` and `e' true` plus `2 * c`, then the guessing advantage of
`Experiment.guessBit e` is at most that of `Experiment.guessBit e'` plus `c`, by
`Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit` on both sides. -/
private theorem guessingAdvantage_guessBit_le_of_advantage_le {e e' : Bool → Experiment} {c : ℝ}
    (h : (Experiment.advantage (e false) (e true) : ℝ) ≤
      Experiment.advantage (e' false) (e' true) + 2 * c) :
    (Game.guessingAdvantage (ProbComp.eval (Experiment.guessBit e)) : ℝ) ≤
      Game.guessingAdvantage (ProbComp.eval (Experiment.guessBit e')) + c := by
  have he : (Experiment.advantage (e false) (e true) : ℝ) =
      2 * Game.guessingAdvantage (ProbComp.eval (Experiment.guessBit e)) :=
    mod_cast Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit e
  have he' : (Experiment.advantage (e' false) (e' true) : ℝ) =
      2 * Game.guessingAdvantage (ProbComp.eval (Experiment.guessBit e')) :=
    mod_cast Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit e'
  linarith

/-- **Bit-guessing AE $\Rightarrow$ CCA bound** ([BonehShoup2023], Section 9.2.3, Theorem 9.1,
equation (9.4), printed p. 364): for any `CCAAdversary` making at most `Qd n` decryption queries at
security parameter `n`, `CCAadv* ≤ CPAadv*[ccaToCPAAdversary] +
dyadicSize (Qd n - 1) * CIadv[ccaToCIHiddenBitAdversary]`, where the starred advantages are the
guessing advantages of the bit-guessing games `Experiment.guessBit`. The book's factor `Qd`
becomes `dyadicSize (Qd n - 1)`, which is `2` when `Qd n ≤ 1`, and otherwise the least power of two
that is at least `Qd n`, because the CI adversary draws its index uniformly from fair coins. -/
theorem guessingAdvantage_guessBit_ccaGame_le (E : SymmetricCipher) (ctBound Qd : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ)
    (hq : IsDecryptionQueryBounded (adversary n []) (Qd n))
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.guessingAdvantage
        (ProbComp.eval (Experiment.guessBit fun b => E.ccaGame adversary b n)) : ℝ) ≤
      (Game.guessingAdvantage (ProbComp.eval
        (Experiment.guessBit fun b => E.cpaGame (ccaToCPAAdversary ctBound adversary) b n)) : ℝ) +
      (dyadicSize (Qd n - 1) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Qd adversary) n)) : ℝ) :=
  guessingAdvantage_guessBit_le_of_advantage_le
    ((advantage_ccaGame_le_two_mul E ctBound Qd adversary n hq hctBound).trans_eq (by ring))

/-- **Bit-guessing AE $\Rightarrow$ CCA bound with factor `2 * Qd`**: equation (9.4) of
[BonehShoup2023], Theorem 9.1 (printed p. 364), with the book's factor `Qd` replaced by `2 * Qd n`,
`CCAadv* ≤ CPAadv*[ccaToCPAAdversary] + 2 * Qd n * CIadv[ccaToCIHiddenBitAdversary]`. For
`Qd n ≥ 1` this follows from `guessingAdvantage_guessBit_ccaGame_le` and
`dyadicSize (Qd n - 1) ≤ 2 * Qd n`. For `Qd n = 0` that factor is `2`, so the proof uses instead
that an adversary without decryption queries has the same advantage in `ccaGame` as in
`ccaRejectGame`. -/
theorem guessingAdvantage_guessBit_ccaGame_le_two_mul (E : SymmetricCipher) (ctBound Qd : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ)
    (hq : IsDecryptionQueryBounded (adversary n []) (Qd n))
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.guessingAdvantage
        (ProbComp.eval (Experiment.guessBit fun b => E.ccaGame adversary b n)) : ℝ) ≤
      (Game.guessingAdvantage (ProbComp.eval
        (Experiment.guessBit fun b => E.cpaGame (ccaToCPAAdversary ctBound adversary) b n)) : ℝ) +
      2 * (Qd n : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Qd adversary) n)) : ℝ) := by
  rcases Nat.eq_zero_or_pos (Qd n) with h0 | hpos
  · have h := E.advantage_ccaGameOn_le_sum (fun _ => true) ctBound Qd adversary n
      (fun b => E.cpaGame (ccaToCPAAdversary ctBound adversary) b n)
      (E.eval_cpaGame_ccaToCPAAdversary_on ctBound adversary n hctBound) hq hctBound
    rw [← ccaGame_eq_on] at h
    rw [h0, Finset.range_zero, Finset.sum_empty, Finset.sum_empty, zero_add, add_zero] at h
    rw [h0, Nat.cast_zero, mul_zero, zero_mul]
    exact guessingAdvantage_guessBit_le_of_advantage_le (by simpa only [mul_zero, add_zero] using h)
  · have hci := NNReal.coe_nonneg (Game.succProbability
      (ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Qd adversary) n)))
    have hd : (dyadicSize (Qd n - 1) : ℝ) ≤ 2 * (Qd n : ℝ) := by
      exact_mod_cast (dyadicSize_le (Qd n - 1)).trans_eq (by lia)
    have h94 := guessingAdvantage_guessBit_ccaGame_le E ctBound Qd adversary n hq hctBound
    nlinarith

/-- **Authenticated encryption implies adaptive CCA security** ([BonehShoup2023], Section 9.2.3,
Theorem 9.1, printed pp. 363–365): every symmetric cipher satisfying `AuthenticatedEncryption`
(`INDCPA ∧ CiphertextIntegrity`) also satisfies `INDCCA`. -/
theorem AuthenticatedEncryption.indcca {E : SymmetricCipher} (hAE : E.AuthenticatedEncryption) :
    E.INDCCA := by
  rcases hAE with ⟨hcpa, hci⟩
  intro adversary hadversary
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  obtain ⟨cq, dq, hqbounds⟩ := hadversary.query_bounds
  let Q : ℕ → ℕ := fun n => cq * (n + 2) ^ dq
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by
    dsimp only [Q]; fun_prop
  have hq (n : ℕ) : IsDecryptionQueryBounded (adversary n []) (Q n) :=
    isDecryptionQueryBounded_of_isQueryBounded <| by
      simpa only [Q, List.length_nil, Nat.add_zero] using (hqbounds n []).1
  have hcpaNeg := hcpa (ccaToCPAAdversary ctBound adversary)
    (isOraclePPT_ccaToCPAAdversary hctBoundPoly hadversary)
  have hciNeg := hci.negligible (ccaToCIHiddenBitAdversary ctBound Q adversary)
    (isOraclePPT_ccaToCIHiddenBitAdversary hctBoundPoly hQPoly hadversary)
  negligible using fun n =>
    advantage_ccaGame_le_two_mul E ctBound Q adversary n (hq n) (hctBound n)

/-! #### Encryption-Query Preservation for Theorem 9.1 Reductions -/

private theorem isQueryBounded_ccaToCPAHandler (n ctBound : ℕ) (request : Bool × List Bool)
    (s : Unit) :
    (ccaToCPAHandler n ctBound request s).IsQueryBounded (if request.1 then 0 else 1) := by
  unfold ccaToCPAHandler
  cases hreq : request.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · simp only [OracleComp.isCostBounded_map_iff]
      exact ProbOracleComp.IsQueryBounded.query ((), request.2)
    · exact OracleComp.IsCostBounded.pure ([], ()) 1
  · simp only [↓reduceIte]
    exact OracleComp.IsCostBounded.pure ([], ()) 0

/-- **Encryption-query preservation for `ccaToCPAAdversary`** ([BonehShoup2023], Section 9.2.3,
Theorem 9.1, printed p. 363): if `adversary n []` makes at most `Qe` encryption queries, then
`ccaToCPAAdversary ctBound adversary n aux` makes at most `Qe` CPA encryption queries. -/
theorem isQueryBounded_ccaToCPAAdversary_of_isEncryptionQueryBounded
    (ctBound : ℕ → ℕ) (adversary : CCAAdversary) (n : ℕ) (aux : List Bool) {Qe : ℕ}
    (hq : IsEncryptionQueryBounded (adversary n []) Qe) :
    (ccaToCPAAdversary ctBound adversary n aux).IsQueryBounded Qe := by
  unfold ccaToCPAAdversary
  have hrun :
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (ccaToCPAHandler n (ctBound n)))
        (adversary n [])).run ()).IsQueryBounded Qe := by
    refine OracleComp.IsCostBounded.run_interpret (fun q s => ?_) hq ()
    cases q with
    | inl m =>
      simp only [OracleComp.sumHandler, Sum.elim_inl]
      change ((·, s) <$> ProbOracleComp.sample (ProbComp.unifFin m)).IsQueryBounded 0
      simp only [OracleComp.isCostBounded_map_iff]
      exact ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin m)
    | inr request =>
      simp only [OracleComp.sumHandler, Sum.elim_inr]
      exact isQueryBounded_ccaToCPAHandler n (ctBound n) request s
  simpa only [bind_pure_comp, OracleComp.isCostBounded_map_iff] using hrun

/-- If `adversary n []` makes at most `Q` total oracle queries, then
`ccaToCPAAdversary ctBound adversary n aux` makes at most `Q` CPA encryption queries. -/
theorem isQueryBounded_ccaToCPAAdversary
    (ctBound : ℕ → ℕ) (adversary : CCAAdversary) (n : ℕ) (aux : List Bool) {Q : ℕ}
    (hq : (adversary n []).IsQueryBounded Q) :
    (ccaToCPAAdversary ctBound adversary n aux).IsQueryBounded Q :=
  isQueryBounded_ccaToCPAAdversary_of_isEncryptionQueryBounded ctBound adversary n aux
    (isEncryptionQueryBounded_of_isQueryBounded hq)

private theorem isQueryBounded_ccaToCIHandler (n ctBound : ℕ) (bit : Bool)
    (request : Bool × List Bool) (state : ℕ × (Bool × List Bool)) :
    (ccaToCIHandler n ctBound bit request state).IsQueryBounded (if request.1 then 0 else 1) := by
  unfold ccaToCIHandler CCAToCIState.rem CCAToCIState.hasCaptured
    CCAToCIState.cap
  by_cases hcap : state.2.1 = true
  · simp only [hcap, ↓reduceIte]
    exact OracleComp.IsCostBounded.pure _ _
  · simp only [hcap, Bool.false_eq_true, ↓reduceIte]
    cases hreq : request.1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : (((unframe request.2).length == n) &&
          ((dropFrame request.2).length == n)) = true
      · simp only [hlen, ↓reduceIte, OracleComp.isCostBounded_map_iff]
        exact ProbOracleComp.IsQueryBounded.query _
      · simp only [hlen, Bool.false_eq_true, ↓reduceIte]
        exact OracleComp.IsCostBounded.pure _ 1
    · simp only [↓reduceIte]
      split_ifs <;> exact OracleComp.IsCostBounded.pure _ 0

/-- **Encryption-query preservation for `ccaToCIAtIndexAdversary`** ([BonehShoup2023],
Section 9.2.3, Theorem 9.1, printed p. 363): if `adversary n []` makes at most `Qe` encryption
queries, then `ccaToCIAtIndexAdversary ctBound j bit adversary n aux` makes at most `Qe` CI
encryption queries. -/
theorem isQueryBounded_ccaToCIAtIndexAdversary_of_isEncryptionQueryBounded
    (ctBound : ℕ → ℕ) (j : ℕ) (bit : Bool) (adversary : CCAAdversary)
    (n : ℕ) (aux : List Bool) {Qe : ℕ}
    (hq : IsEncryptionQueryBounded (adversary n []) Qe) :
    (ccaToCIAtIndexAdversary ctBound j bit adversary n aux).IsQueryBounded Qe := by
  unfold ccaToCIAtIndexAdversary
  have hrun :
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (ccaToCIHandler n (ctBound n) bit))
        (adversary n [])).run (j, (false, []))).IsQueryBounded Qe := by
    refine OracleComp.IsCostBounded.run_interpret (fun q state => ?_) hq (j, (false, []))
    cases q with
    | inl m =>
      simp only [OracleComp.sumHandler, Sum.elim_inl]
      change ((·, state) <$> ProbOracleComp.sample (ProbComp.unifFin m)).IsQueryBounded 0
      simp only [OracleComp.isCostBounded_map_iff]
      exact ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin m)
    | inr request =>
      simp only [OracleComp.sumHandler, Sum.elim_inr]
      exact isQueryBounded_ccaToCIHandler n (ctBound n) bit request state
  simpa only [bind_pure_comp, OracleComp.isCostBounded_map_iff] using hrun

/-- If `adversary n []` makes at most `Q` total oracle queries, then
`ccaToCIAtIndexAdversary ctBound j bit adversary n aux` makes at most `Q` CI encryption queries. -/
theorem isQueryBounded_ccaToCIAtIndexAdversary
    (ctBound : ℕ → ℕ) (j : ℕ) (bit : Bool) (adversary : CCAAdversary)
    (n : ℕ) (aux : List Bool) {Q : ℕ}
    (hq : (adversary n []).IsQueryBounded Q) :
    (ccaToCIAtIndexAdversary ctBound j bit adversary n aux).IsQueryBounded Q :=
  isQueryBounded_ccaToCIAtIndexAdversary_of_isEncryptionQueryBounded ctBound j bit adversary n aux
    (isEncryptionQueryBounded_of_isQueryBounded hq)

/-- **Encryption-query preservation for `ccaToCIAdversary`** ([BonehShoup2023], Section 9.2.3,
Theorem 9.1, printed p. 363): if `adversary n []` makes at most `Qe` encryption queries, then
`ccaToCIAdversary ctBound Qd bit adversary n aux` makes at most `Qe` CI encryption queries. -/
theorem isQueryBounded_ccaToCIAdversary_of_isEncryptionQueryBounded
    (ctBound Qd : ℕ → ℕ) (bit : Bool) (adversary : CCAAdversary)
    (n : ℕ) (aux : List Bool) {Qe : ℕ}
    (hq : IsEncryptionQueryBounded (adversary n []) Qe) :
    (ccaToCIAdversary ctBound Qd bit adversary n aux).IsQueryBounded Qe := by
  unfold ccaToCIAdversary
  simpa only [Nat.zero_add] using
    (ProbOracleComp.IsQueryBounded.sample (ProbComp.sampleDyadicIndex (Qd n - 1))).bind fun j =>
      isQueryBounded_ccaToCIAtIndexAdversary_of_isEncryptionQueryBounded
        ctBound j bit adversary n aux hq

/-- If `adversary n []` makes at most `Q` total oracle queries, then
`ccaToCIAdversary ctBound Qd bit adversary n aux` makes at most `Q` CI encryption queries. -/
theorem isQueryBounded_ccaToCIAdversary
    (ctBound Qd : ℕ → ℕ) (bit : Bool) (adversary : CCAAdversary)
    (n : ℕ) (aux : List Bool) {Q : ℕ}
    (hq : (adversary n []).IsQueryBounded Q) :
    (ccaToCIAdversary ctBound Qd bit adversary n aux).IsQueryBounded Q :=
  isQueryBounded_ccaToCIAdversary_of_isEncryptionQueryBounded ctBound Qd bit adversary n aux
    (isEncryptionQueryBounded_of_isQueryBounded hq)

/-- **Encryption-query preservation for `ccaToCIHiddenBitAdversary`** ([BonehShoup2023],
Section 9.2.3, Theorem 9.1, printed p. 363): if `adversary n []` makes at most `Qe` encryption
queries, then `ccaToCIHiddenBitAdversary ctBound Qd adversary n aux` makes at most `Qe` CI
encryption queries. -/
theorem isQueryBounded_ccaToCIHiddenBitAdversary_of_isEncryptionQueryBounded
    (ctBound Qd : ℕ → ℕ) (adversary : CCAAdversary)
    (n : ℕ) (aux : List Bool) {Qe : ℕ}
    (hq : IsEncryptionQueryBounded (adversary n []) Qe) :
    (ccaToCIHiddenBitAdversary ctBound Qd adversary n aux).IsQueryBounded Qe := by
  unfold ccaToCIHiddenBitAdversary
  simpa only [Nat.zero_add] using
    (ProbOracleComp.IsQueryBounded.sample (BitString.sampleList 1)).bind fun bits => by
      split_ifs
      · exact isQueryBounded_ccaToCIAdversary_of_isEncryptionQueryBounded
          ctBound Qd true adversary n aux hq
      · exact isQueryBounded_ccaToCIAdversary_of_isEncryptionQueryBounded
          ctBound Qd false adversary n aux hq

/-- If `adversary n []` makes at most `Q` total oracle queries, then
`ccaToCIHiddenBitAdversary ctBound Qd adversary n aux` makes at most `Q` CI encryption queries. -/
theorem isQueryBounded_ccaToCIHiddenBitAdversary
    (ctBound Qd : ℕ → ℕ) (adversary : CCAAdversary)
    (n : ℕ) (aux : List Bool) {Q : ℕ}
    (hq : (adversary n []).IsQueryBounded Q) :
    (ccaToCIHiddenBitAdversary ctBound Qd adversary n aux).IsQueryBounded Q :=
  isQueryBounded_ccaToCIHiddenBitAdversary_of_isEncryptionQueryBounded ctBound Qd adversary n aux
    (isEncryptionQueryBounded_of_isQueryBounded hq)

/-! ### One-Time Authenticated Encryption Implies One-Time CCA Security (Boneh–Shoup Theorem 9.1) -/

/-- Hybrid two-channel oracle for the one-time Game 1 in the proof of [BonehShoup2023],
Theorem 9.1 (Section 9.2.3, printed pp. 363–364): encryption queries `(false, req)` behave
identically to `oneTimeCCAOracle`, whereas every decryption query `(true, _)` immediately returns
`[]` (rejection) without invoking `decrypt`. -/
noncomputable def oneTimeCCARejectOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool) (bit : Bool)
    (request : Bool × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.1 then
      return ([], queriedCiphertexts)
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if queriedCiphertexts.isEmpty && (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, [ct])
      else
        return ([], queriedCiphertexts)

/-- The one-time all-reject hybrid CCA experiment (one-time Game 1 in [BonehShoup2023],
Section 9.2.3, Theorem 9.1): sample `k ← E.keyGen n` and run `adversary n []` against
`E.oneTimeCCARejectOracle n k bit`. -/
noncomputable def ccaOneTimeRejectGame (E : SymmetricCipher) (adversary : CCAAdversary)
    (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.oneTimeCCARejectOracle n k bit)) (adversary n [])).run []
  return out.1

/-- When `ctBound n` bounds all ciphertext lengths produced by `E.encrypt n k` on `n`-bit messages,
running `ccaToCPAAdversary ctBound adversary` in `cpaOneTimeGame` has the exact same output
distribution as `ccaOneTimeRejectGame adversary` ([BonehShoup2023], Section 9.2.3, Theorem 9.1). -/
theorem eval_cpaOneTimeGame_ccaToCPAAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : CCAAdversary) (bit : Bool) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval (E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) bit n) =
      ProbComp.eval (E.ccaOneTimeRejectGame adversary bit n) := by
  simp only [cpaOneTimeGame, ccaOneTimeRejectGame, ccaToCPAAdversary, runWith_norm, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  have hsim := ProbOracleComp.runWith_map_state
    (fun request queried => ProbComp.eval (E.oneTimeCCARejectOracle n k bit request queried))
    (fun request state =>
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.oneTimeCPAEncryptionOracle n k bit q s))
          ((ccaToCPAHandler n (ctBound n) request).run state.1) state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (fun queried : List (List Bool) => ((), !queried.isEmpty))
    (fun request queried => by
      change (ProbComp.eval (E.oneTimeCCARejectOracle n k bit request queried)).map
          (fun x => (x.1, (), !x.2.isEmpty)) =
        (ProbOracleComp.runWith
            (fun q s => ProbComp.eval (E.oneTimeCPAEncryptionOracle n k bit q s))
            (ccaToCPAHandler n (ctBound n) request ()) (!queried.isEmpty)).map
          (fun result => (result.1.1, result.1.2, result.2))
      cases hreq : request.1
      · simp only [oneTimeCCARejectOracle, ccaToCPAHandler, hreq, Bool.false_eq_true, ↓reduceIte]
        by_cases hlenEq : ((unframe request.2).length == n &&
            (dropFrame request.2).length == n) = true
        · simp only [hlenEq, ↓reduceIte, Functor.map_map, ProbOracleComp.runWith_map,
            ProbOracleComp.runWith_query, oneTimeCPAEncryptionOracle]
          simp only [Bool.not_not]
          by_cases hemp : queried.isEmpty = true
          · have hcond : (queried.isEmpty && ((unframe request.2).length == n) &&
                ((dropFrame request.2).length == n)) = true := by
              rw [hemp, Bool.true_and, hlenEq]
            simp only [hcond, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
              PMF.map_bind, PMF.pure_map, List.isEmpty_cons, Bool.not_false, Prod.map_apply, id_eq]
            simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
            have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
              cases bit <;> simp [hlenEq]
            apply PMF.bind_congr_on_support
            intro ct hct
            rw [List.take_of_length_le (hctBound k hk _ hmbLen ct hct)]
          · have hcond : (queried.isEmpty && ((unframe request.2).length == n) &&
                ((dropFrame request.2).length == n)) = false := by
              rw [Bool.eq_false_iff.mpr hemp, Bool.false_and, Bool.false_and]
            simp only [hcond, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
              PMF.pure_map, List.take_nil, Prod.map_apply, id_eq]
        · have hcond : (queried.isEmpty && ((unframe request.2).length == n) &&
              ((dropFrame request.2).length == n)) = false := by
            rw [Bool.and_assoc, Bool.eq_false_iff.mpr hlenEq, Bool.and_false]
          simp only [hcond, hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            ProbOracleComp.runWith_pure, PMF.pure_map]
      · simp only [oneTimeCCARejectOracle, ccaToCPAHandler, hreq, ↓reduceIte, ProbComp.eval_pure,
          ProbOracleComp.runWith_pure, PMF.pure_map])
    (adversary n []) []
  dsimp only [List.isEmpty, not] at hsim
  rw [← hsim]
  simp only [PMF.bind_map, Function.comp_def]

private theorem oneTimeCCARejectOracle_eq_on (E : SymmetricCipher) :
    E.oneTimeCCARejectOracle = E.ccaRejectOracleOn List.isEmpty := by
  funext n k bit request queried
  cases queried <;> rfl

private theorem ccaOneTimeRejectGame_eq_on (E : SymmetricCipher) :
    E.ccaOneTimeRejectGame = E.ccaRejectGameOn List.isEmpty := by
  funext adversary bit n
  simp only [ccaOneTimeRejectGame, ccaRejectGameOn, oneTimeCCARejectOracle_eq_on]

/-- The one-time all-reject hybrid games have the laws of `cpaOneTimeGame` against
`ccaToCPAAdversary`, in the form the policy-generic bounds take. -/
private theorem eval_cpaOneTimeGame_ccaToCPAAdversary_on (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ) (hctBound : E.CiphertextLengthLE n (ctBound n))
    (bit : Bool) :
    ProbComp.eval (E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) bit n) =
      ProbComp.eval (E.ccaRejectGameOn List.isEmpty adversary bit n) := by
  rw [← ccaOneTimeRejectGame_eq_on]
  exact E.eval_cpaOneTimeGame_ccaToCPAAdversary ctBound adversary bit n hctBound

/-- Running `ccaToCIAdversary` in `ciOneTimeGame` averages `ccaToCIAtIndexAdversary` uniformly over
`Fin (dyadicSize (Qd n - 1))`. -/
theorem eval_ciOneTimeGame_ccaToCIAdversary (E : SymmetricCipher) (ctBound Qd : ℕ → ℕ)
    (bit : Bool) (adversary : CCAAdversary) (n : ℕ) :
    ProbComp.eval (E.ciOneTimeGame (ccaToCIAdversary ctBound Qd bit adversary) n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (Qd n - 1)))).bind
        (fun i =>
          ProbComp.eval
            (E.ciOneTimeGame (ccaToCIAtIndexAdversary ctBound i.val bit adversary) n)) := by
  rw [ciOneTimeGame_eq_on]
  exact E.eval_ciGameOn_ccaToCIAdversary List.isEmpty ctBound Qd bit adversary n

/-- **Quantitative 1AE $\Rightarrow$ 1CCA bound** ([BonehShoup2023], Section 9.2.3, Theorem 9.1,
printed pp. 363–365): for any `CCAAdversary` making at most `Qd n` decryption queries at security
parameter `n`, the one-time CCA distinguishing advantage in `ccaOneTimeGame` is bounded by the
one-time CPA advantage of `ccaToCPAAdversary` in `cpaOneTimeGame` plus `dyadicSize (Qd n - 1)`
times the one-time ciphertext-integrity winning probabilities of `ccaToCIAdversary` in
`ciOneTimeGame` for `bit = false` and `bit = true`. -/
theorem advantage_ccaOneTimeGame_le (E : SymmetricCipher) (ctBound Qd : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ)
    (hq : IsDecryptionQueryBounded (adversary n []) (Qd n))
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.advantage (ProbComp.eval (E.ccaOneTimeGame adversary false n))
        (ProbComp.eval (E.ccaOneTimeGame adversary true n)) : ℝ) ≤
      (dyadicSize (Qd n - 1) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciOneTimeGame (ccaToCIAdversary ctBound Qd false adversary) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) false n))
        (ProbComp.eval (E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) true n)) : ℝ) +
      (dyadicSize (Qd n - 1) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciOneTimeGame (ccaToCIAdversary ctBound Qd true adversary) n)) :
          ℝ) := by
  rw [ccaOneTimeGame_eq_on, ciOneTimeGame_eq_on]
  exact E.advantage_ccaGameOn_le List.isEmpty ctBound Qd adversary n
    (fun b => E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) b n)
    (E.eval_cpaOneTimeGame_ccaToCPAAdversary_on ctBound adversary n hctBound) hq hctBound

/-- Running `ccaToCIHiddenBitAdversary` in `ciOneTimeGame` averages `ccaToCIAdversary` uniformly
over `bit : Bool`. -/
theorem eval_ciOneTimeGame_ccaToCIHiddenBitAdversary (E : SymmetricCipher) (ctBound Qd : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ) :
    ProbComp.eval (E.ciOneTimeGame (ccaToCIHiddenBitAdversary ctBound Qd adversary) n) =
      (PMF.uniformOfFintype Bool).bind
        (fun bit =>
          ProbComp.eval (E.ciOneTimeGame (ccaToCIAdversary ctBound Qd bit adversary) n)) := by
  rw [ciOneTimeGame_eq_on]
  exact E.eval_ciGameOn_ccaToCIHiddenBitAdversary List.isEmpty ctBound Qd adversary n

/-- **Single-adversary quantitative 1AE $\Rightarrow$ 1CCA bound** ([BonehShoup2023],
Section 9.2.3, Theorem 9.1, equation (9.3) for one-time security, printed pp. 363–364): for any
`CCAAdversary` making at most `Qd n` decryption queries, the one-time games satisfy
`1CCAadv ≤ 1CPAadv + 2 * dyadicSize (Qd n - 1) * 1CIadv`, where the CPA and CI adversaries are
`ccaToCPAAdversary` and `ccaToCIHiddenBitAdversary`.
As in `advantage_ccaGame_le_two_mul`, the book's factor `2 Qd` becomes `2 * dyadicSize (Qd n - 1)`
because the CI adversary samples its index from fair coins. -/
theorem advantage_ccaOneTimeGame_le_two_mul (E : SymmetricCipher) (ctBound Qd : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ)
    (hq : IsDecryptionQueryBounded (adversary n []) (Qd n))
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.advantage (ProbComp.eval (E.ccaOneTimeGame adversary false n))
        (ProbComp.eval (E.ccaOneTimeGame adversary true n)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) false n))
        (ProbComp.eval (E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) true n)) : ℝ) +
      2 * (dyadicSize (Qd n - 1) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciOneTimeGame (ccaToCIHiddenBitAdversary ctBound Qd adversary) n)) :
          ℝ) := by
  rw [ccaOneTimeGame_eq_on, ciOneTimeGame_eq_on]
  exact E.advantage_ccaGameOn_le_two_mul List.isEmpty ctBound Qd adversary n
    (fun b => E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) b n)
    (E.eval_cpaOneTimeGame_ccaToCPAAdversary_on ctBound adversary n hctBound) hq hctBound

/-- **Bit-guessing 1AE $\Rightarrow$ 1CCA bound** ([BonehShoup2023], Section 9.2.3, Theorem 9.1,
equation (9.4) for one-time security, printed p. 364): for any `CCAAdversary` making at most `Qd n`
decryption queries, `1CCAadv* ≤ 1CPAadv*[ccaToCPAAdversary] +
dyadicSize (Qd n - 1) * 1CIadv[ccaToCIHiddenBitAdversary]`, where the starred advantages are the
guessing advantages of the bit-guessing one-time games `Experiment.guessBit`. The book's factor
`Qd` becomes `dyadicSize (Qd n - 1)` as in `guessingAdvantage_guessBit_ccaGame_le`. -/
theorem guessingAdvantage_guessBit_ccaOneTimeGame_le (E : SymmetricCipher) (ctBound Qd : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ)
    (hq : IsDecryptionQueryBounded (adversary n []) (Qd n))
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.guessingAdvantage
        (ProbComp.eval (Experiment.guessBit fun b => E.ccaOneTimeGame adversary b n)) : ℝ) ≤
      (Game.guessingAdvantage (ProbComp.eval (Experiment.guessBit fun b =>
        E.cpaOneTimeGame (ccaToCPAAdversary ctBound adversary) b n)) : ℝ) +
      (dyadicSize (Qd n - 1) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciOneTimeGame (ccaToCIHiddenBitAdversary ctBound Qd adversary) n)) :
          ℝ) :=
  guessingAdvantage_guessBit_le_of_advantage_le
    ((advantage_ccaOneTimeGame_le_two_mul E ctBound Qd adversary n hq hctBound).trans_eq (by ring))

/-- **One-time authenticated encryption implies one-time adaptive CCA security**
([BonehShoup2023], Section 9.2.3, Theorem 9.1, printed pp. 363–365): every symmetric cipher
satisfying `OneTimeAuthenticatedEncryption` (`OneTimeINDCPA ∧ OneTimeCiphertextIntegrity`,
Definition 9.4) also satisfies `OneTimeINDCCA` (`1CCA`, Definition 9.6). -/
theorem OneTimeAuthenticatedEncryption.oneTimeINDCCA {E : SymmetricCipher}
    (h1AE : E.OneTimeAuthenticatedEncryption) :
    E.OneTimeINDCCA := by
  rcases h1AE with ⟨hcpa, hci⟩
  intro adversary hadversary
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  obtain ⟨cq, dq, hqbounds⟩ := hadversary.query_bounds
  let Q : ℕ → ℕ := fun n => cq * (n + 2) ^ dq
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by
    dsimp only [Q]; fun_prop
  have hq (n : ℕ) : IsDecryptionQueryBounded (adversary n []) (Q n) :=
    isDecryptionQueryBounded_of_isQueryBounded <| by
      simpa only [Q, List.length_nil, Nat.add_zero] using (hqbounds n []).1
  have hcpaNeg := hcpa (ccaToCPAAdversary ctBound adversary)
    (isOraclePPT_ccaToCPAAdversary hctBoundPoly hadversary)
  have hciNeg := hci.negligible (ccaToCIHiddenBitAdversary ctBound Q adversary)
    (isOraclePPT_ccaToCIHiddenBitAdversary hctBoundPoly hQPoly hadversary)
  negligible using fun n =>
    advantage_ccaOneTimeGame_le_two_mul E ctBound Q adversary n (hq n) (hctBound n)

end SymmetricCipher

end Cslib.Crypto
