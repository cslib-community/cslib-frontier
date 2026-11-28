/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.Streaming
import CslibFrontier.Foundations.FieldTheory.Finite.BinaryFieldArithmetic

/-! # Table-free Hoza generator clients -/

set_option linter.privateModule false

open Cslib Cslib.Reachability Cslib.Reachability.Hoza Cslib.Code.JustesenFamily

-- Over the modulus X² + X + 1, the square of X is X + 1.
example : BinaryField.fieldMulMod [true, true, true] [false, true] [false, true] =
    [true, true] := by decide

-- Use the table-free generator directly as the weight callback in the isolation theorem.
example {w n : ℕ} (G : LayeredDigraph (Fin (n + 1) × Fin w))
    (hlayer : ∀ z, G.layer z = z.1.val) :
    ∃ seed, G.IsMinIsolating (generatedWeightScan seed) := by
  obtain ⟨seed, hs⟩ := exists_generatedWeight_isMinIsolating G hlayer
  have heq : generatedWeightScan seed = generatedWeight seed :=
    funext (generatedWeightScan_eq seed)
  exact ⟨seed, heq ▸ hs⟩
