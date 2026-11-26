/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.Bounds
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Strassen.Monotone

/-!
# Uniform native counter budgets over modulus intervals

The public scalar, address, workspace and native instruction budgets are monotone in the
runtime modulus. Prime selection can therefore call the actual counter for different primes
using one numerical admission, frame envelope and instruction budget.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

/-- Increasing the modulus increases the signed magnitude budget. -/
theorem magnitudeBudget_monotone_modulus (k A : ℕ) :
    Monotone (fun p => magnitudeBudget p k A) := by
  intro p q hpq
  dsimp only [magnitudeBudget]
  gcongr

/-- One address envelope suffices for every modulus below its supplied maximum. -/
theorem addressBudget_monotone_modulus (n k scratch a b c : ℕ) :
    Monotone (fun p => addressBudget n p k scratch a b c) := by
  intro p q hpq
  dsimp only [addressBudget]
  gcongr

/-- All counter workspaces end before the workspace for the largest admitted modulus. -/
theorem memoryEnd_monotone_modulus (n k scratch : ℕ) :
    Monotone (fun p => memoryEnd n p k scratch) := by
  intro p q hpq
  dsimp only [memoryEnd]
  gcongr

/-- The complete native pre-halt counter cost is monotone in its runtime modulus. -/
theorem cost_monotone_modulus (n : ℕ) : Monotone (cost n) := by
  intro p q hpq
  have := Strassen.traceBudget_monotone (Nat.clog 2 n) hpq
  dsimp only [cost, readyCost]
  gcongr

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
