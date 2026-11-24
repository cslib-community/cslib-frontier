/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Crypto.Computational.CBCMAC

/-!
# Collected results: Computational PRF and MAC security for CBC-MAC
-/

register_result "cbc-mac-prefix-free-prf" where
  title := "Basic zero-IV CBC-MAC is a prefix-free pseudorandom function"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Theorem 6.3",
      locator := "Section 6.4.1, pp. 226–229" }
  ]
  theorems := [
    Cslib.Crypto.PseudorandomFunction.prefixFreePRF_cbcMac,
    Cslib.Crypto.advantage_cbcMac_le
  ]
  scope := "Let F be a PseudorandomFunction: n-bit keys, inputs and outputs, deterministic \
    polynomial-time evaluation, secure against adaptive uniform strict oracle-PPT tests, with \
    queries of another length answered by the empty word (Attack Game 4.2 and Definition 4.2, \
    pp. 132–133; K = X = Y = {0,1}^n, so |X| = 2^n is super-poly). For any unary \
    polynomial-time block-count cap ℓ : ℕ → ℕ, cbcMacFamily F computes Figure 6.3a's zero-IV \
    CBC-MAC on nonempty whole-block messages of 1 to ℓ n blocks (cbcBlockValid ℓ). \
    PrefixFreePseudorandomFunctionOn (cbcBlockValid ℓ) id (cbcMacFamily F) proves \
    indistinguishability of prfRealGameOn (uniform n-bit key) and prfIdealGameOn (lazy uniform \
    n-bit table on cbcBlockValid ℓ, answering malformed words with [] in both worlds) against \
    uniform strict oracle-PPT distinguishers satisfying IsPrefixFreeOn (cbcBlockValid ℓ n) n \
    (Definition 4.5, p. 152: against any deterministic oracle mapping valid queries to n-bit \
    words and invalid queries to [], no valid query in a run is a proper prefix of another; \
    repeated identical valid queries are permitted). The reduction cbcMacToPrfDistinguisher is \
    certified oracle PPT (isOraclePPT_cbcMacToPrfDistinguisher). Concrete bound: \
    advantage_cbcMac_le gives Adv ≤ PRFadv[cbcMacToPrfDistinguisher ℓ A, F] + Q² ℓ(n)² / (2 * 2^n) \
    at parameter n for any distinguisher making at most Q queries and satisfying \
    IsPrefixFreeOn (cbcBlockValid ℓ n) n, using equation (6.7)'s (Q ℓ)² / (2 |X|) \
    collision constant from abs_cbcUniformFunctionSuccess_sub_cbcIdealSuccess_le."

register_result "cbc-mac-fixed-block-prf-and-mac" where
  title := "Fixed-block-count basic CBC-MAC is a pseudorandom function and strongly unforgeable MAC"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Theorems 6.2 and 6.3 (fixed-block-count specialization)",
      locator := "Section 6.3, p. 224; Section 6.4.1, pp. 226–229" }
  ]
  theorems := [
    Cslib.Crypto.PseudorandomFunction.prfOver_cbcMac,
    Cslib.Crypto.PseudorandomFunction.sufCma_cbcFixedBlockMAC,
    Cslib.Crypto.succProbability_sufCmaGame_cbcFixedBlockMAC_le
  ]
  scope := "Fixed-length specialization of Theorems 6.2 and 6.3 for any PseudorandomFunction F \
    and unary polynomial-time block count ℓ : ℕ → ℕ with ∀ n, 0 < ℓ n. Equal-length (ℓ n * n)-bit \
    queries are vacuously prefix-free, giving PseudorandomFunctionOver (fun n => ℓ n * n) id \
    (cbcMacFamily F) (prfOver_cbcMac). cbcFixedBlockMAC packages uniform n-bit key sampling, \
    deterministic signing cbcMacFamily F, and recomputation verification as a MACScheme whose \
    fields certify strict PPT key generation and signing, polynomial-time verification, and \
    perfect correctness; sufCma_cbcFixedBlockMAC proves MACScheme.SUFCMA (Attack Game 6.1 and \
    Definition 6.2, pp. 218–219; EUFCMA follows via MACScheme.SUFCMA.eufCma) against uniform \
    strict oracle-PPT forgers via the certified reduction cbcFixedBlockMacToPrfDistinguisher \
    (isOraclePPT_cbcFixedBlockMacToPrfDistinguisher). Concrete bound: \
    succProbability_sufCmaGame_cbcFixedBlockMAC_le gives \
    PRFadv + (Q + 1)² ℓ(n)² / (2 * 2^n) + 1 / 2^n at n under the finite hypotheses 0 < n, \
    0 < ℓ(n), and at most Q signing queries."

register_result "length-prepended-cbc-mac-prf-and-mac" where
  title := "Length-prepended CBC-MAC is a variable-length pseudorandom function and SUF-CMA MAC"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Theorems 6.2 and 6.3, and Section 6.6.1 Method 1 (via Theorem 6.8)",
      locator := "Section 6.3, p. 224; Section 6.4.1, pp. 226–229; \
        Sections 6.6–6.6.1, pp. 235–236" }
  ]
  theorems := [
    Cslib.Crypto.PseudorandomFunction.prfOn_lengthPrependedCbcMac,
    Cslib.Crypto.advantage_lengthPrependedCbcMac_le,
    Cslib.Crypto.PseudorandomFunction.macSufCmaOn_lengthPrependedCbcMac,
    Cslib.Crypto.succProbability_macSufCmaGameOn_lengthPrependedCbcMac_le,
    Cslib.Crypto.PseudorandomFunction.prfOver_lengthPrependedCbcMac,
    Cslib.Crypto.PseudorandomFunction.sufCma_lengthPrependedBlockMAC
  ]
  scope := "Concrete Section 6.6.1 Method 1 specialization of Theorems 6.2, 6.3, and 6.8 \
    (Theorem 6.8 for an arbitrary prefix-free PRF and encoding is not formalized here). For any \
    PseudorandomFunction F (K = X = Y = {0,1}^n) and unary polynomial-time block-count cap \
    L : ℕ → ℕ, lengthPrependedCbcMacFamily F prepends the n-bit little-endian binary block count \
    BitString.lowBits n (msg.length / n) (prependLengthWord, matching blockCountBlock) and \
    evaluates basic zero-IV CBC-MAC on whole-block messages of 0 to L n blocks (lpBlockValid L, \
    empty message included, giving 1 to L n + 1 blocks after prepending). Against uniform strict \
    oracle-PPT adversaries, prfOn_lengthPrependedCbcMac proves \
    PseudorandomFunctionOn (lpBlockValid L) id, and macSufCmaOn_lengthPrependedCbcMac proves \
    MACSUFCMAOn (lpBlockValid L) (equivalent to MACEUFCMAOn by macSufCmaOn_iff_macEufCmaOn; \
    Attack Game 6.1 and Definition 6.2, pp. 218–219; malformed queries outside lpBlockValid L \
    receive [] without tagging or recording, and invalid candidate messages never verify). The \
    reductions lengthPrependedToPrfDistinguisher and lengthPrependedMacToPrfDistinguisher are \
    certified oracle PPT. Concrete bounds: advantage_lengthPrependedCbcMac_le gives \
    PRFadv + Q² (L(n) + 1)² / (2 * 2^n) and \
    succProbability_macSufCmaGameOn_lengthPrependedCbcMac_le gives \
    PRFadv + (Q + 1)² (L(n) + 1)² / (2 * 2^n) + 1 / 2^n, \
    where both concrete bounds require L(n) < 2^n and at most Q queries at the parameter n being \
    bounded; the asymptotic proofs derive L(n) < 2^n eventually from polynomial boundedness of L. \
    lengthPrependedBlockMAC packages any fixed unary polytime block-count schedule k (including \
    k n = 0) as a verified-correct MACScheme with SUFCMA security (and EUFCMA via .eufCma)."
