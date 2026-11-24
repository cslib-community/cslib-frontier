/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Foundations.Quantum.Bell
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyDomination

/-! Selecting one member of the equal mixture of two pure qubits costs at most `log 2` nats. -/

namespace CslibFrontierTests.QuantumRelativeEntropyDomination

open Cslib.Quantum Matrix
open scoped MatrixOrder

example : relativeEntropy (pureState (ket false))
    (∑ b : Bool, (1 / 2 : ℝ) • pureState (ket b)) ≤ (Real.log 2 : WithTop ℝ) := by
  have h := relativeEntropy_le_neg_log_weight (fun _ : Bool => (1 / 2 : ℝ))
    (fun _ => by norm_num) (fun b => pureState (ket b))
    (fun b => (isDensityMatrix_pureState (norm_ket b)).posSemidef) false
    (by norm_num) (isDensityMatrix_pureState (norm_ket false))
  simpa only [Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0), Real.log_one, zero_sub,
    neg_neg] using h

end CslibFrontierTests.QuantumRelativeEntropyDomination
