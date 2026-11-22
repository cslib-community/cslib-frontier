/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.Combinatorics.Additive.BkSequence
import CslibFrontier.Computability.Complexity.BkSequencePolyTime

/-!
# Collected results: Sergeev's explicit finite `B_k`-sequence
-/

register_result "sergeev-explicit-bk-sequence" where
  title := "Explicit size-n finite B_k-sequence with elements bounded by n^(k + o(k))"
  topic := "combinatorics"
  sources := [
    { paper := Sergeev2023BkSequence,
      theorem := "Construction H[n, k], B_k correctness, and density bound (unnumbered)",
      locator := "Abstract, p. 1, and Construction, p. 2 (arXiv:2304.03988v1)" }
  ]
  theorems := [
    Cslib.IsBkSet.choose_le_card,
    Cslib.existsUnique_neg_one_pow_mul_five_pow_eq,
    Cslib.zmod_eq_neg_one_pow_mul_five_pow_dlogFiveModTwoPow,
    Cslib.length_sergeevBkSequence,
    Cslib.isBkSequence_map_zmod_sergeevBkSequence,
    Cslib.isBkSequence_sergeevBkSequence,
    Cslib.two_pow_sergeevModulusExp_sub_two_lt,
    Cslib.mem_sergeevBkSequence_lt
  ]
  scope := "Unconditional for all n : ℕ and 1 ≤ k (with length_sergeevBkSequence n k = n for all \
    n, k). Constructs H[n, k] (sergeevBkSequence n k) as the base-5 discrete logarithms modulo \
    2^r (dlogFiveModTwoPow r, r = sergeevModulusExp n k = max 3 (1 + Nat.clog 2 (p_n^k))) of the \
    first n odd primes (firstOddPrimes n), proves its entries are pairwise distinct and form a \
    B_k-set both in ZMod (2^(r - 2)) and in ℕ, and proves the explicit non-asymptotic upper \
    bound h < 2^(r - 2) < ((n + 2) * (2 * Nat.log 2 (n + 2) + 4))^k (= n^(k + o(k))) using the \
    elementary Chebyshev prime-counting lower bound Nat.le_card_primesLE_mul_log rather than \
    Rosser–Schoenfeld's 2n log(n + 2). Also proves the general finite-monoid counting lower \
    bound (#B + k - 1).choose k ≤ Fintype.card M (giving (#B + k - 1).choose k ≤ N on ZMod N) \
    and unique (-1)^j * 5^h (mod 2^r) decomposition of odd integers for r ≥ 3."

register_result "sergeev-explicit-bk-sequence-polytime" where
  title := "Sergeev's size-n B_k-sequence H[n, k] is computable in time (n + k)^O(1)"
  topic := "computational complexity"
  sources := [
    { paper := Sergeev2023BkSequence,
      theorem := "Polynomial-time constructibility of H[n, k] in time (n + k)^O(1) (unnumbered)",
      locator := "Abstract, p. 1, and Construction, pp. 2–3 (arXiv:2304.03988v1)" }
  ]
  theorems := [
    Cslib.Complexity.computableInPolyTime_dlogFiveModTwoPow,
    Cslib.Complexity.computableInPolyTime_sergeevBkSequence
  ]
  scope := "Unconditional plain multi-tape Turing machine polynomial bit-time certificate \
    ComputableInPolyTime (fun p : ℕ × ℕ => sergeevBkSequence p.1 p.2) (encPair encUnary encUnary) \
    (encList encNat) (together with computableInPolyTime_dlogFiveModTwoPow on \
    encPair encUnary encNat): given (n, k) in unary (input length Θ(n + k), matching the paper's \
    (n + k)^O(1) runtime parameter), computes the framed list of binary-encoded elements of \
    sergeevBkSequence n k (matching footnote 1 on p. 1) in polynomial bit time via \
    trial-division enumeration of firstOddPrimes n (replacing the paper's sieve option) and \
    sequential bit extraction in dlogFiveModTwoPow. The paper's O(r^2) figure on pp. 2–3 counts \
    arithmetic operations for the discrete logarithm, whereas \
    computableInPolyTime_dlogFiveModTwoPow and computableInPolyTime_sergeevBkSequence certify \
    polynomial bit time on a multi-tape Turing machine (a separate explicit O(r^2) \
    arithmetic-operation count is left open in #7625)."
