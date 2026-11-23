/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Circuit.Prefix.OptimalDepth

register_result "sergeev-optimal-fanout-prefix-depth" where
  title := "Minimal depth of optimal fanout-k universal prefix circuits on N inputs is \
    log_{α_k} N ± O(1)"
  topic := "circuit complexity"
  sources := [
    { paper := Sergeev2025PrefixDepth,
      theorem := "Main theorem on D(N, k) = log_{α_k} N ± O(1) and Claim (4) recurrence",
      locator := "pp. 2–5, Main result (p. 2), Claim (4) (p. 3), w_k*(D) recurrence (p. 4)" }
  ]
  theorems := [
    Cslib.Circuits.Prefix.abs_optimalPrefixDepth_sub_logb_le,
    Cslib.Circuits.Prefix.maxConsistentWidth_eq,
    Cslib.Circuits.Prefix.maxCircuitWidthUpper_recurrence,
    Cslib.Circuits.Prefix.exists_optimalPrefixCircuit_of_le_maxCircuitWidthUpper,
    Cslib.Circuits.Prefix.width_le_mul_alphaRoot_pow
  ]
  scope := "Covers arbitrary universal prefix circuits over the signature {mul, id} computing all \
    prefix products in every semigroup (S, *), characterized equivalently via FreeSemigroup \
    (Fin N). Complexity counts binary mul gates, depth counts both mul and id gates along the \
    longest input-to-output path, wire fanout counts both internal gate input slots and external \
    output poles, and optimal (zero-deficiency) circuits satisfy binaryComplexity c + c.depth = \
    2 * N - 2. Proves Sergeev's Claim (4) recurrence for w_k(d, h), the order-k linear recurrence \
    for w_k*(D), constructive synthesis for 1 ≤ N ≤ 1 + w_k*(D - 1), unconditional exponential \
    width upper bounds in terms of the unique positive root α_k ∈ (1, φ) of P_k(x) = 2 + x + ⋯ + \
    x^(k-2) - x^k (with α_k strictly increasing on k ≥ 2 and α_k → φ), and |(D(N, k) : ℝ) - \
    log_{α_k} N| ≤ C for all k ≥ 2 and N ≥ 1."
