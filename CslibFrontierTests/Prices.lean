/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Prices.Cross
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Prices.Norm

/-! Tests of the price lemmas of the separation:

* norms of loads, and the finiteness of the loads of bounded norm;
* the exponential bound for powers;
* spectral points at products of wires of `n e` bits. -/

namespace CslibFrontierTests.Prices

open Cslib.PartyTensor Cslib.Circuits.Arithmetic.Separation.Prices

/-- The zero load has norm `0`, for any weights. -/
example (α : Fin 3 → ℝ) : loadNorm α (fun _ => 0) = 0 := loadNorm_zero α

/-- Finitely many loads with weights `1` have norm at most `2`. -/
example : Finite (Loads (fun _ : Fin 2 => (1 : ℝ)) 2) := finite_loads _ (fun _ => one_pos) 2

/-- `2 ^ z ≤ exp (log 2 · z)`. -/
example (z : ℝ) : (2 : ℝ) ^ z ≤ Real.exp (Real.log 2 * z) := by
  exact_mod_cast rpow_le_exp 2 z

/-- A spectral point at one wire of `3` bits is `2 ^ (3 · d)`. -/
example {K : Type} [Field K] (F : SpectralPoint K (Fin 2)) :
    F (wires K (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) fun _ => 2 ^ 3) =
      2 ^ ∑ _e : Unit, ((3 : ℕ) : ℝ) * F.wireExponent 0 1 :=
  apply_wires_two_pow F _ _ _

end CslibFrontierTests.Prices
