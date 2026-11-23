/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Circuit.Prefix.ConsistentTree
import CslibFrontier.Computability.Circuit.Prefix.OptimalDepth

register_result "sergeev-consistent-tree-width-recurrence" where
  title := "Exact recurrence for consistent tree-pair widths w_k(d, h), order-k recurrence for \
    w_k*(D), and constructive optimal prefix circuit synthesis"
  topic := "circuit complexity"
  sources := [
    { paper := Sergeev2025PrefixDepth,
      theorem := "Claim (4) recurrence, Eq. (3) synthesis bound, and w_k*(D) linear recurrence",
      locator := "pp. 3–4, Eq. (3) and Claim (4) (p. 3), Eqs. (5)–(7) and w_k*(D) recurrence (p. 4)"
    }
  ]
  theorems := [
    Cslib.Circuits.Prefix.maxConsistentWidth_eq,
    Cslib.Circuits.Prefix.maxCircuitWidthUpper_recurrence,
    Cslib.Circuits.Prefix.exists_optimalPrefixCircuit_of_le_maxCircuitWidthUpper
  ]
  scope := "Covers consistent pairs (I_d, Q_d) of binary interval aggregation trees of depth ≤ d \
    and fanout-k prefix distribution trees of depth ≤ h, together with universal prefix circuits \
    over {mul, id} computing all prefix products in every semigroup (S, *). Proves Sergeev's \
    Claim (4) recurrence for w_k(d, h) (maxConsistentWidth_eq), deduces the order-k linear \
    recurrence w_k*(D) = (∑_{i=2}^{k-1} w_k*(D - i)) + 2 * w_k*(D - k) + k for k ≥ 2 and D ≥ k \
    (maxCircuitWidthUpper_recurrence), and constructively synthesizes an optimal \
    (zero-deficiency, binaryComplexity c + c.depth = 2 * N - 2) fanout-k universal prefix circuit \
    of depth at most D for every k ≥ 2, D ≥ 1, and input width 1 ≤ N ≤ 1 + w_k*(D - 1)."

register_result "sergeev-optimal-fanout-prefix-depth" where
  title := "Minimal depth of optimal fanout-k universal prefix circuits on N inputs is \
    log_{α_k} N ± O(1)"
  topic := "circuit complexity"
  sources := [
    { paper := Sergeev2025PrefixDepth,
      theorem := "Main theorem on D(N, k) = log_{α_k} N ± O(1)",
      locator := "pp. 2–5, Main theorem (p. 2) and proof via root dominance |x| ≤ α_k (pp. 3–5)" }
  ]
  theorems := [
    Cslib.Circuits.Prefix.abs_optimalPrefixDepth_sub_logb_le,
    Cslib.Circuits.Prefix.width_le_mul_alphaRoot_pow
  ]
  scope := "Covers arbitrary universal prefix circuits over the signature {mul, id} computing all \
    prefix products in every semigroup (S, *), characterized equivalently via FreeSemigroup \
    (Fin N). Complexity counts binary mul gates, depth counts both mul and id gates along the \
    longest input-to-output path, wire fanout counts both internal gate input slots and external \
    output poles, and optimal (zero-deficiency) circuits satisfy binaryComplexity c + c.depth = \
    2 * N - 2. Proves in terms of the unique positive root α_k ∈ (1, φ) of P_k(x) = 2 + x + ⋯ + \
    x^(k-2) - x^k (with α_k strictly increasing on k ≥ 2 and α_k → φ) that for each k ≥ 2, there \
    is a constant A ≥ 1 (depending on k) such that (N : ℝ) ≤ A * (alphaRoot k) ^ c.depth holds \
    for every N ≥ 1 and every optimal fanout-k universal prefix circuit c, and that for each \
    k ≥ 2, there is a constant C ≥ 0 (depending on k) such that the inequality \
    |(optimalPrefixDepth N k : ℝ) - Real.logb (alphaRoot k) N| ≤ C holds for every N ≥ 1."
