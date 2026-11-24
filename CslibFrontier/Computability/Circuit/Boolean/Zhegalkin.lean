/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.AdditiveDefs
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.AdditiveBound
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Basis
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Complexity
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.UpperBound

/-!
# Additive matrix synthesis and multiplicative-to-total complexity over `{⊕, ∧, 1}`

This file formalizes the constructive upper bounds of Igor S. Sergeev on additive matrix synthesis
and total-from-multiplicative circuit complexity over the Zhegalkin basis `{⊕, ∧, 1}`
[Sergeev2013AdditiveMultiplicative]:

1. **Active-square additive matrix synthesis**
   ([Sergeev, Lemma 1, pp. 2–3][Sergeev2013AdditiveMultiplicative], reformulating a special case of
   Nechiporuk): for an `m × n` Boolean matrix `A`, its *active square* `A.activeSquare` (`S(A)`)
   counts the entries `(i, j)` within horizontal distance `Nat.log 2 m` of a `true` entry in row
   `i`. Over any additive commutative monoid `G`, the linear operator
   `x ↦ (i ↦ ∑ j, if A i j then x j else 0)` can be computed by an additive circuit of size at most
   `(n * 2 ^ s) / s + A.activeSquare / (2 * s) + m * p + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)` whenever
   `0 < s ≤ Nat.log 2 m + 1` and `0 < p` (`Additive.exists_circuit_matrix_le_bound`), hence
   asymptotically `A.activeSquare / (2 * Real.logb 2 m) + ε * (m + n) ^ 2 / Real.logb 2 m`
   (`Additive.exists_circuit_matrix_le`).
2. **Multiplicative-to-total complexity upper bound over `{⊕, ∧, 1}`**
   ([Sergeev, Theorem 1 (upper bound), pp. 1, 3][Sergeev2013AdditiveMultiplicative]): every
   `n`-variable Boolean function computed by a `{⊕, ∧, 1}`-circuit with at most `M` conjunction
   (`∧`) gates can be computed by an acyclic `{⊕, ∧, 1}`-circuit using no more `∧`-gates and total
   gate count at most `Zhegalkin.totalBound n M s p`
   (`Zhegalkin.exists_circuit_of_andCost_le_bound`), giving
   `(1 / 2 + ε) * M * (M + 2 * n) / Real.logb 2 M` uniformly in `n` for all sufficiently large `M`
   (`Zhegalkin.exists_circuit_of_andCost_le`,
   `Zhegalkin.complexity_le_of_multiplicativeComplexity_le`).

To keep the `{⊕, ∧, 1}` circuit strictly acyclic while sharing paired column sums across all `2 M`
conjunction-input rows, the `M` topologically ordered `∧`-gates are processed in stages of `s`
consecutive gates: every paired sum `y_{r₁, r₂}` between rows `r₁ < r₂` reads only original inputs
and `∧`-gate blocks completed strictly before `r₁`'s stage, while the `< s` intra-stage `∧`-gates
preceding a gate are added directly with `O(M s)` XOR gates.

## Main definitions

* `Matrix.activeSquare`: active square `S(A)` of an `m × n` Boolean matrix.
* `Cslib.Circuits.Additive.Op`, `Cslib.Circuits.Additive.signature`,
  `Cslib.Circuits.Additive.interpretation`, `Cslib.Circuits.Additive.matrixBound`: the additive
  circuit basis `{0, +}` and explicit `(s, p)` gate budget of Lemma 1.
* `Cslib.Circuits.Boolean.Zhegalkin.Op`, `Cslib.Circuits.Boolean.Zhegalkin.signature`,
  `Cslib.Circuits.Boolean.Zhegalkin.interpretation`: the Zhegalkin Boolean basis `{⊕, ∧, 1}`.
* `Cslib.Circuits.Boolean.Zhegalkin.andCost`,
  `Cslib.Circuits.Boolean.Zhegalkin.multiplicativeComplexity`: conjunction-gate cost and
  multiplicative complexity `L_∧(f)`.
* `Cslib.Circuits.Boolean.Zhegalkin.totalBound`: explicit `(n, M, s, p)` total gate budget for the
  upper bound of Theorem 1.

## Main results

* `Cslib.Circuits.Additive.exists_circuit_matrix_le_bound`: explicit active-square additive matrix
  synthesis bound ([Sergeev, Lemma 1, pp. 2–3][Sergeev2013AdditiveMultiplicative]).
* `Cslib.Circuits.Additive.exists_circuit_matrix_le`: asymptotic active-square additive matrix
  bound `S(A) / (2 log₂ m) + ε (m + n)² / log₂ m`
  ([Sergeev, Lemma 1, p. 2][Sergeev2013AdditiveMultiplicative]).
* `Cslib.Circuits.Boolean.Zhegalkin.exists_circuit_of_andCost_le_bound`: explicit staged acyclic
  `{⊕, ∧, 1}`-circuit synthesis bound preserving conjunction count
  ([Sergeev, Theorem 1 (upper bound), p. 3][Sergeev2013AdditiveMultiplicative]).
* `Cslib.Circuits.Boolean.Zhegalkin.exists_circuit_of_andCost_le`,
  `Cslib.Circuits.Boolean.Zhegalkin.complexity_le_of_multiplicativeComplexity_le`: asymptotic
  `(1 / 2 + ε) * M * (M + 2 * n) / log₂ M` total complexity upper bound from multiplicative
  complexity ([Sergeev, Theorem 1 (upper bound), p. 1][Sergeev2013AdditiveMultiplicative]).

## References

* [I. S. Sergeev, *A relation between additive and multiplicative complexity of Boolean
  functions*][Sergeev2013AdditiveMultiplicative]
-/
