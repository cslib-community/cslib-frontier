/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Foundations.Quantum.Bell
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyConvexity

/-! Joint convexity with singular qubit inputs and a zero-weight support mismatch. -/

namespace CslibFrontierTests.QuantumRelativeEntropyConvexity

open Cslib.Quantum Matrix
open scoped ComplexOrder

-- The inactive source block is orthogonal to its reference. The bound only uses the
-- active pair's divergence, even when its states are singular.
example {ρ σ : Matrix Bool Bool ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    relativeEntropy ((1 / 2 : ℝ) • ρ) ((1 / 2 : ℝ) • σ) ≤
      (↑(1 / 2 : ℝ) : WithTop ℝ) * relativeEntropy ρ σ := by
  let w (k : Bool) : ℝ := if k then 0 else 1 / 2
  let A (k : Bool) := if k then pureState (ket false) else ρ
  let B (k : Bool) := if k then pureState (ket true) else σ
  have hA (k : Bool) : (A k).PosSemidef := by
    cases k
    · exact hρ
    · exact (isDensityMatrix_pureState (norm_ket false)).posSemidef
  have hB (k : Bool) : (B k).PosSemidef := by
    cases k
    · exact hσ
    · exact (isDensityMatrix_pureState (norm_ket true)).posSemidef
  have h := relativeEntropy_sum_smul_le w (fun k => by cases k <;> simp [w]) A B hA hB
  simpa [Fintype.sum_bool, w, A, B, WithTop.coe_zero] using h

end CslibFrontierTests.QuantumRelativeEntropyConvexity
