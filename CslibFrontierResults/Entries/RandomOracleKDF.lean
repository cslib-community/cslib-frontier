/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Crypto.Computational.KeyDerivation.RandomOracle.Computational

/-!
# Collected results: Key derivation in the random-oracle model (Boneh–Shoup Theorem 8.10)
-/

register_result "random-oracle-kdf-theorem-8-10" where
  title := "In the random-oracle model, key-derivation advantage reduces to secret-guessing \
    advantage via lazy oracle simulation, yielding secure key derivation from computationally \
    unpredictable encoded secret sources"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Theorem 8.10 (with Attack Game 8.3)",
      locator := "Section 8.10.2, pp. 331–332; Attack Game 8.3: Section 8.10.1, p. 326" }
  ]
  theorems := [
    Cslib.Crypto.KeyDerivation.SecretGuessHard.negligible_roAdvantage,
    Cslib.Crypto.KeyDerivation.SecretGuessHard.negligible_roAdvantage_bitString,
    Cslib.Crypto.KeyDerivation.roAdvantage_toRODistinguisher_le_listGuessAdvantage,
    Cslib.Crypto.KeyDerivation.roAdvantage_toRODistinguisher_le_listGuessAdvantage_add,
    Cslib.Crypto.KeyDerivation.roAdvantage_toRODistinguisher_le_mul_guessAdvantage_add,
    Cslib.Crypto.KeyDerivation.length_le_of_mem_support_lazyROToListGuess,
    Cslib.Crypto.KeyDerivation.isPPT_lazyROToListGuess,
    Cslib.Crypto.KeyDerivation.isPPT_lazyROToGuess
  ]
  scope := "Over general encoded finite nonempty secret families S n and digest/key families T n, \
    with side information info n : S n → X n and arbitrary source laws sample n : PMF (S n). \
    Word-oracle distinguishers D : WordRODistinguisher X are uniform strict oracle-PPT machines \
    reading (1^n, encX n x, z) (WordRODistinguisher.IsPPT encX) and are adapted to the typed \
    random-oracle KDF game on S n → T n by toRODistinguisher decS encT D n, which answers \
    canonical queries (decS n q = some s, where decS n w = some s ↔ encS n s = w) with \
    encT n (table s) and rejects malformed words outside Set.range (encS n) with []. \
    lazyROToListGuess and lazyROToGuess simulate the random oracle lazily via an associative-list \
    cache (cachedSamplerOracle) drawing candidate keys and cache-miss replies from a strict-PPT \
    sampler sampleT n, certified uniform strict PPT by isPPT_lazyROToListGuess and \
    isPPT_lazyROToGuess under polynomial-time (decS n w).isSome and fallback defaultS n. \
    roAdvantage_toRODistinguisher_le_listGuessAdvantage gives the exact bound Dist^ro_adv ≤ \
    ListGuessadv when sampleT n is exact uniform; \
    roAdvantage_toRODistinguisher_le_listGuessAdvantage_add adds (Q + 1) * εT when sampleT n is \
    εT-close to uniform on Q-query runs; and \
    roAdvantage_toRODistinguisher_le_mul_guessAdvantage_add adds the fair-coin modular index \
    bias Q n / 2 ^ width n from ProbComp.sampleModIndex. SecretGuessHard.negligible_roAdvantage \
    derives negligible random-oracle KDF advantage from SecretGuessHard when sampleT is \
    StatisticallyIndistinguishable from uniform and encX n (info n s) has polynomial length on \
    (sample n).support; SecretGuessHard.negligible_roAdvantage_bitString specializes to \
    BitString (secLen n) secrets and BitString (outLen n) keys."
