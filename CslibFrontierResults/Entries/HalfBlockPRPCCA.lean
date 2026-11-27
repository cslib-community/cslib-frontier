/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Crypto.Computational.Encryption.HalfBlockPRP.CCA

/-!
# Collected results: CCA security of half-block encryption from a strong PRP
-/

register_result "boneh-shoup-half-block-prp-cca" where
  title := "Half-block encryption with a fresh nonce under a strong pseudorandom permutation is \
    CCA-secure"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Exercise 9.12(a)",
      locator := "Section 9.13, p. 394" }
  ]
  theorems := [
    Cslib.Crypto.BlockCipher.StrongPRP.indcca_halfBlockCipher,
    Cslib.Crypto.BlockCipher.advantage_ccaGame_halfBlockCipher_le
  ]
  scope := "For every BlockCipher F with block length F.blockLen n = 2 * n (hblock), the \
    half-block symmetric cipher F.halfBlockCipher hblock samples keys from \
    BitString.sampleList (F.keyLen n), encrypts an n-bit message m by sampling a fresh n-bit \
    nonce r from BitString.sampleList n and returning F.encrypt n k (r ++ m), and decrypts a \
    2 * n-bit word ct to some ((F.decrypt n k ct).drop n) while rejecting every other word \
    length; the same SymmetricCipher value carries strict-PPT key generation and encryption, \
    deterministic polynomial-time decryption, and decryption correctness on n-bit messages. \
    If F satisfies F.StrongPRP (Section 4.1.3, pp. 101-102, and Exercise 4.9, p. 169), then \
    F.halfBlockCipher hblock satisfies INDCCA (Attack Game 9.2 and Definition 9.5, p. 362, \
    two-experiment advantage against uniform strict oracle-PPT CCAAdversary programs in the \
    standard model). Deviations from the textbook statement: the block layout is r ++ m rather \
    than (m, r); messages and nonces are fixed to n-bit words at security parameter n, so \
    |R| = 2 ^ n and 1 / |R| is negligible without an extra hypothesis; malformed encryption \
    queries return [] without encrypting or logging; and decryption queries on previously \
    returned challenge ciphertexts answer [] rather than being syntactically forbidden. For \
    each challenge bit, ccaToStrongPRPAdversary bit adversary is certified uniform strict \
    oracle PPT (isOraclePPT_ccaToStrongPRPAdversary), makes at most Q strong-PRP calls when \
    adversary n [] makes at most Q total CCA calls (isQueryBounded_ccaToStrongPRPAdversary), \
    and yields the concrete bound advantage_ccaGame_halfBlockCipher_le with additive ideal \
    birthday and bidirectional-switching loss Q.choose 2 / 2 ^ n + 2 * Q.choose 2 / 4 ^ n. \
    Parts (b) and (c) of Exercise 9.12 are not formalized."

register_result "boneh-shoup-cca-without-integrity" where
  title := "From any pseudorandom function there exists a CCA-secure symmetric cipher with \
    neither ciphertext integrity nor plaintext integrity"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "remark after Theorem 9.1 (unnumbered)",
      locator := "Section 9.2.3, p. 363; Exercise 9.12(a), p. 394; Exercise 9.15, p. 395" }
  ]
  theorems := [
    Cslib.Crypto.PseudorandomFunction.exists_indcca_not_integrity,
    Cslib.Crypto.BlockCipher.not_encForge_halfBlockCipher
  ]
  scope := "For every BlockCipher F with F.blockLen n = 2 * n, the zero-query oracle-PPT \
    forger F.allOnesForger wins encForgeGame against F.halfBlockCipher hblock with probability \
    1 at every security parameter n (eval_encForgeGame_halfBlockCipher_allOnesForger), so \
    F.halfBlockCipher hblock never satisfies plaintext integrity EncForge (Exercise 9.15, \
    p. 395; Katz-Lindell Definition 5.2) in addition to lacking CiphertextIntegrity \
    (not_ciphertextIntegrity_halfBlockCipher in HalfBlockPRP.lean). Given any \
    PseudorandomFunction family (n-bit keys, inputs, and outputs, deterministic polynomial-time \
    evaluation, secure against uniform strict oracle-PPT distinguishers), instantiating F with \
    the four-round Feistel strong PRP lubyRackoff4Cipher yields a SymmetricCipher E satisfying \
    E.INDCCA, not E.CiphertextIntegrity, and not E.EncForge."
