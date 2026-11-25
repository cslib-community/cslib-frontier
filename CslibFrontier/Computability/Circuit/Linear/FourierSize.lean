/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Linear.Model.Basic
public import CslibFrontier.Computability.Circuit.Linear.Model.Fourier
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Real.Sqrt

/-!
# The acyclic batched Fourier size bounds

[OpenAI, Theorem 1.1][OpenAI2026FiniteFourier] gives uniform lower and upper bounds for
independently chosen Fourier transforms of equal order. Its upper bound at exponent parameter
`ε = 1/2` is linear in `1 + log₂ n`.
The Toeplitz reduction uses this specialization for two different transform lengths.
The released Lean theorem is `OAI.LinearAlgebra.FiniteFourier.batchedFourierComplexity`.
-/

public section

namespace Cslib.Circuit

open Cslib.Circuit.Linear

/-- The acyclic estimates in Theorem 1.1 at `ε = 1/2`, for one field and fixed constants.
Each block carries a finite abelian group, proof of invertibility of its order, a splitting
root, point and character enumerations, and a transform direction. The gate budget is shared
by the whole batch. -/
@[expose] def FourierSizeBounds (K : Type) [Field K] (c C : ℝ) : Prop :=
  ∀ {J n : ℕ} (B : Fin J → FourierBlock.{0, 0} K n), 1 ≤ J → 2 ≤ n →
    let h : ℝ := J * (n : ℝ)
    c * h * Real.sqrt (Real.logb 2 n) ≤ (complexity (batchMatrix B) : ℝ) ∧
      (complexity (batchMatrix B) : ℝ) ≤ C * h * (1 + Real.logb 2 n)

end Cslib.Circuit
