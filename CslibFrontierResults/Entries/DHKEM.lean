/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Crypto.Computational.DiffieHellman.GapCDH.Decodable

/-!
# Collected results: ROM IND-CCA security of the Diffie–Hellman KEM (Katz–Lindell Theorem 12.22)
-/

register_result "katz-lindell-dhkem-rom-cca-theorem-12-22" where
  title := "Under Gap-CDH, the Diffie–Hellman KEM with subgroup-validating decapsulation is \
    IND-CCA secure in the random-oracle model"
  topic := "cryptography"
  sources := [
    { paper := KatzLindell2020,
      theorem := "Theorem 12.22 (Construction 12.19, Definition 12.13)",
      locator := "Section 12.4.4, p. 435; Construction 12.19: p. 431; Definition 12.13: p. 425" }
  ]
  theorems := [
    Cslib.Crypto.DecodablePrimeOrderGroupFamily.GapCDH.dhKEMROMINDCCA,
    Cslib.Crypto.DecodablePrimeOrderGroupFamily.advantage_dhKEMCCAWordGame_le
  ]
  scope := "Over a decodable prime-order group family F with group parameters drawn from an \
    arbitrary setup : ℕ → PMF F.Desc (in place of an efficient generator G(1^n)) and a key length \
    keyLen computable in polynomial time in unary (keyLen = id gives the n-bit keys of \
    Definition 12.13). Key generation and encapsulation are uniform strict (oracle) PPT \
    fair-coin programs sampling exponents with PrimeOrderGroupFamily.sampleExp, within \
    statistical distance 1 / 2 ^ n of uniform, and decapsulation rejects words outside the \
    subgroup as in Construction 12.23. Adversaries are uniform strict oracle-PPT word-oracle \
    machines (IsOraclePPT encBool) with hash and decapsulation queries; the random oracle is a \
    uniform function from the group to keyLen n-bit strings. advantage_dhKEMCCAWordGame_le bounds \
    the two-world advantage by the Gap-CDH success of the explicit reduction dhKEMToGapCDHWord \
    plus 4 / 2 ^ n; GapCDH.dhKEMROMINDCCA concludes negligible advantage from F.GapCDH setup. \
    The two-world advantage is twice the textbook's hidden-bit bias."
