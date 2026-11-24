/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.ComputedWithin
public import CslibFrontier.Foundations.Data.Matrix.HamiltonianCycle
import Mathlib.Algebra.BigOperators.Fin

/-!
# Boundary cases of the Hamiltonian cycle sum and of `ComputedWithin`

On one vertex the only cycle is the loop, so the Hamiltonian cycle sum of a `1 × 1` matrix is its
entry; on two vertices the identity is not a cycle through both, so only the transposition counts.
A polynomial is never computed within zero nodes, since the output of a circuit is an input or a
gate, and a variable is computed within one node, its input.
-/

public section

namespace CslibFrontierTests.HamiltonianCycle

open Cslib.Circuits.Arithmetic MvPolynomial

/-- On one vertex, the Hamiltonian cycle is the loop. -/
example (M : Matrix (Fin 1) (Fin 1) ℚ) : M.hamiltonianCycleSum = M 0 0 := by
  rw [Matrix.hamiltonianCycleSum_eq_sum_orders, Finset.sum_eq_single_of_mem 1 (by simp)
    fun π _ h => absurd (Equiv.ext fun i => Fin.ext (by omega)) h]
  simp

/-- On two vertices, the identity is not a Hamiltonian cycle. -/
example (M : Matrix (Fin 2) (Fin 2) ℚ) : M.hamiltonianCycleSum = M 0 1 * M 1 0 := by
  rw [Matrix.hamiltonianCycleSum_eq_sum_orders, Finset.sum_eq_single_of_mem 1 (by simp)]
  · simp [Fin.prod_univ_two]
  · intro π hπ h
    refine absurd (Equiv.ext fun i => ?_) h
    have h0 : π 0 = 0 := (Finset.mem_filter.1 hπ).2
    fin_cases i
    · exact h0
    · have h1 : π 1 ≠ 0 := fun h1 => absurd (π.injective (h1.trans h0.symm)) (by decide)
      have := (π 1).isLt
      rw [Ne, Fin.ext_iff] at h1
      exact Fin.ext (by simp at h1 ⊢; omega)

/-- No polynomial is computed within zero nodes. -/
example (P : MvPolynomial (Fin 2) ℚ) : ¬ ComputedWithin P 0 := fun h => by
  simpa using h.pos

/-- A variable is computed within one node. -/
example : ComputedWithin (X 0 : MvPolynomial (Fin 2) ℚ) 1 := computedWithin_X 0

end CslibFrontierTests.HamiltonianCycle
