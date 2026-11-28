/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Crypto.Computational.MAC.VerificationQueries

/-!
# Collected results: MAC security with verification queries
-/

register_result "boneh-shoup-mac-verification-queries" where
  title := "MAC security with verification queries is equivalent to standard strong MAC security"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Theorem 6.1",
      locator := "Section 6.2, Attack Game 6.2 and Theorem 6.1, pp. 220–223" }
  ]
  theorems := [
    Cslib.Crypto.MACScheme.sufCmaVq_iff_sufCma,
    Cslib.Crypto.MACScheme.SUFCMA.sufCmaVq,
    Cslib.Crypto.MACScheme.SUFCMAVq.sufCma,
    Cslib.Crypto.MACScheme.succProbability_sufCmaVqGame_le_mul_add,
    Cslib.Crypto.MACScheme.succProbability_sufCmaVqGame_le_mul
  ]
  scope := "For every uniform MACScheme M on M.msgLen n-bit messages against uniform strict \
    oracle-PPT adversaries (VqForger in sufCmaVqGame and Forger in sufCmaGame), strong \
    unforgeability with interleaved signing and verification queries (M.SUFCMAVq, Attack Game \
    6.2) is equivalent to standard strong fresh-pair unforgeability (M.SUFCMA, Attack Game 6.1). \
    Keys and honest tags are drawn by M.keyGen n and M.sign sk msg, and M.verify_sign guarantees \
    honest tags verify on M.msgLen n-bit messages. Wrong-length signing queries return [] without \
    being signed or logged; wrong-length verification messages return [false] without winning; \
    and verification queries replaying a previously signed pair (m, t) in log return [true] \
    without winning. Both reductions sufToVqForger and M.vqToSufForger carry uniform strict \
    IsOraclePPT certificates (isOraclePPT_sufToVqForger, M.isOraclePPT_vqToSufForger) and \
    signing-query preservation (M.isQueryBounded_vqToSufForger). Sampling the planted \
    verification-query index from fair coins via ProbComp.sampleModIndex (width n) (Qv n) gives \
    the general modular-sampling bias upper bound + Qv n / 2 ^ width n \
    (succProbability_sufCmaVqGame_le_mul_add). Separately, succProbability_sufCmaVqGame_le_mul \
    proves the bound with no additive error term when Qv n = 0 (where the interval below 0 is \
    empty and 0 verification queries give winning probability 0 via \
    succProbability_sufCmaVqGame_zero) or when Qv n ∣ 2 ^ width n (where 0 < Qv n and \
    sampleModIndex is uniform below Qv n)."

register_result "boneh-shoup-prf-mac-verification-queries" where
  title := "A pseudorandom function yields a MAC secure under verification queries without Q_v \
    PRF advantage loss"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Exercise 6.2",
      locator := "Section 6.14, p. 246" }
  ]
  theorems := [
    Cslib.Crypto.PseudorandomFunction.sufCmaVq_prfMAC,
    Cslib.Crypto.succProbability_sufCmaVqGame_prfMAC_le
  ]
  scope := "For every length-preserving polynomial-time keyed function family (keyLen = msgLen = \
    outLen = n) and every uniform strict oracle-PPT VqForger making at most Q_v verification \
    queries at security parameter n, the Attack Game 6.2 winning probability against \
    prfMAC family hpoly is at most the word-level PRF distinguishing advantage of \
    vqMacToPrfDistinguisher adversary plus Q_v / 2 ^ n, avoiding Theorem 6.1's Q_v factor on the \
    PRF advantage. The direct reduction vqMacToPrfDistinguisher carries a uniform strict \
    IsOraclePPT certificate (isOraclePPT_vqMacToPrfDistinguisher), makes at most Q_s + Q_v PRF \
    queries when adversary makes at most Q_s signing and Q_v verification queries \
    (isQueryBounded_vqMacToPrfDistinguisher), and answers wrong-length signing/verification \
    queries and replayed (m, t) in log pairs locally."
