/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Foundations.Quantum.Bell
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyDataProcessing

/-! Data processing for discarding part of an entangled state. -/

namespace CslibFrontierTests.QuantumRelativeEntropyDataProcessing

open Cslib.Quantum Matrix
open scoped ComplexOrder

-- The retained state of a Bell pair is the maximally mixed qubit, even though the
-- joint source is entangled and rank one.
example {σ : Matrix (Bool × Bool) (Bool × Bool) ℂ} (hσ : σ.PosSemidef) :
    relativeEntropy ((2 : ℂ)⁻¹ • (1 : Matrix Bool Bool ℂ)) (partialTraceRight σ) ≤
      relativeEntropy (pureState bell) σ := by
  have h := relativeEntropy_partialTraceRight_le
    (isDensityMatrix_pureState norm_bell).posSemidef hσ
  rw [bell, partialTraceRight_pureState_maxEntangled, Fintype.card_bool, Nat.cast_ofNat] at h
  exact h

end CslibFrontierTests.QuantumRelativeEntropyDataProcessing
