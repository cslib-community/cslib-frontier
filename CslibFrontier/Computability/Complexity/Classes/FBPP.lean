/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.PPT

/-!
# Probabilistic polynomial-time search

`Cslib.Complexity.FBPP` is the relational search analogue of `BPP`. For every input
there is a valid output. One uniform probabilistic polynomial-time solver returns a valid
output with probability tending to one uniformly over inputs as their encoded length grows.
The relation need not be efficiently verifiable.

This uses [Aaronson, §2.2, Definition 3][Aaronson2010BQPPolynomialHierarchy].
The search solver is a finite fair-coin machine through `IsPPTOn`, which also bounds the
encoded length of every output it can return.
-/

public section

namespace Cslib.Complexity

open Cslib.Probability

/-- Total relations solved by one probabilistic polynomial-time algorithm with vanishing error. -/
@[expose] def FBPP {α β : Type} (enc : α ↪ List Bool) (out : β ↪ List Bool) :
    Set (α → β → Prop) :=
  {R | (∀ a, ∃ b, R a b) ∧ ∃ program : α → ProbComp β, IsPPTOn enc out program ∧
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ a, n ≤ (enc a).length →
      1 - ε ≤ ((ProbComp.eval (program a)).toOuterMeasure {b | R a b}).toReal}

end Cslib.Complexity
