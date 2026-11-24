/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Prices.BitLaw
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Prices.Cross
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Prices.Law
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Prices.Norm

/-! Tests of the price lemmas of the separation:

* norms of loads, the finiteness of the loads of bounded norm, and rounding a load;
* the identity between functions of bits given by a cover of one wire by itself;
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

/-- A wire of `3` bits covers itself. This gives an identity between functions of bits, and one
with slots of one bit. -/
example {K : Type} [Field K] (p q : Fin 2) :
    ∃ tab, BitId K (fun _ : Σ _ : Unit, Fin 3 => p) (fun _ => q) (fun _ : Unit => p) (fun _ => q)
      (fun (_ : Unit) _ => 3) tab := by
  obtain ⟨tab, h⟩ := exists_wireId (K := K) (a := fun _ : Unit => p) (b := fun _ => q)
    (c := fun _ : Unit => p) (d := fun _ => q) (n := fun _ => 3) (len := fun (_ : Unit) _ => 3)
    (CoveredBy.single le_rfl)
  exact ⟨_, h.bitId⟩

/-- Rounding with one coordinate, unit weights and prices, the unit load and `R = η = S = 1`. -/
example : ∃ x : Unit → ℕ,
    loadNorm (fun _ => (1 : ℝ)) (fun ν => (x ν : ℝ)) ≤ (1 + 1) * (1 : ℕ) * 1 ∧
      ∑ e : Unit, (((1 : ℕ) * (fun _ => 1) e : ℕ) : ℝ) * 1 ≤ ∑ ν : Unit, (x ν : ℝ) * 1 := by
  have h1 : loadNorm (fun _ : Unit => (1 : ℝ)) (fun _ => 1) = 1 := by simp [loadNorm]
  exact exists_load (fun _ => 1) (fun _ => one_pos) (fun _ => 1) (fun _ => one_pos) (fun _ => 1)
    (fun _ => 1) (fun _ => zero_le_one) le_rfl (fun _ => 1) zero_le_one zero_le_one
    (by simpa using h1.le) 1 (by simpa using h1.le)

end CslibFrontierTests.Prices
