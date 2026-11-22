/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin

register_result "sergeev-2013-lemma-1-additive-matrix" where
  title := "Every m × n Boolean matrix over an additive commutative monoid has additive circuit \
    complexity at most S(A) / (2 log₂ m) + o((m + n)² / log₂ m)"
  topic := "circuit complexity"
  sources := [
    { paper := Sergeev2013AdditiveMultiplicative,
      theorem := "Lemma 1",
      locator := "pp. 2–3" }
  ]
  theorems := [
    Cslib.Circuits.Additive.exists_circuit_matrix_le_bound,
    Cslib.Circuits.Additive.exists_circuit_matrix_le
  ]
  scope := "Unconditional over any additive commutative monoid G ([AddCommMonoid G]), using \
    Cslib.Circuits.Additive.signature ({0, +}) and Matrix.activeSquare A (entries within \
    horizontal distance Nat.log 2 m of a true entry in the same row, equivalent to Real.logb 2 m \
    for integer column distances when 1 ≤ m). Proves both the explicit (s, p) gate bound \
    (n * 2 ^ s) / s + A.activeSquare / (2 * s) + m * p + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s) for all \
    0 < s ≤ Nat.log 2 m + 1 and 0 < p (exists_circuit_matrix_le_bound) and the asymptotic \
    A.activeSquare / (2 * Real.logb 2 m) + ε * ((m + n) ^ 2 / Real.logb 2 m) form for all 2 ≤ m \
    and sufficiently large m + n (exists_circuit_matrix_le)."

register_result "sergeev-2013-theorem-1-zhegalkin-complexity" where
  title := "Every Boolean function of multiplicative complexity M over {⊕, ∧, 1} has total \
    {⊕, ∧, 1} circuit complexity at most (1/2 + o(1)) M (M + 2 n) / log₂ M"
  topic := "circuit complexity"
  sources := [
    { paper := Sergeev2013AdditiveMultiplicative,
      theorem := "Theorem 1",
      locator := "pp. 1, 3" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Zhegalkin.exists_circuit_of_andCost_le_bound,
    Cslib.Circuits.Boolean.Zhegalkin.exists_circuit_of_andCost_le,
    Cslib.Circuits.Boolean.Zhegalkin.complexity_le_of_multiplicativeComplexity_le
  ]
  scope := "Constructs an acyclic straight-line circuit over Cslib.Circuits.Boolean.Zhegalkin \
    ({⊕, ∧, 1}) using no more conjunction gates than the input circuit \
    (c'.program.cost andCost ≤ c.program.cost andCost) and at most totalBound n M s p total \
    gates for any 0 < s and 0 < p, yielding (1 / 2 + ε) * M * (M + 2 * n) / Real.logb 2 M \
    uniformly for all n : ℕ and all sufficiently large M (strictly generalizing Sergeev's \
    M = Ω(n) hypothesis, which in the paper arose only from applying Lemma 1's coarse \
    o((m + n)² / log m) remainder as a black box). Sergeev's tightness remark on pp. 1–2 cites \
    counting lower bounds of Nechiporuk (1962) and Lupanov (1958) without proving them in the \
    note and is outside this entry."
