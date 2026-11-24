/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ThreeSat.Instance

/-!
# Nonvacuity checks for Corollary 7.2

* The network read from the encoding of the one-clause formula `x₀` has value `1 = #SAT`,
  computed by `decide` from the definitions (6 edges, 7 vertices).
* The two-clause formula `(x₀ ∨ ¬x₁) ∧ x₁` with bit position `0` is an `Instance` (3-CNF, every
  variable occurs, `m = 2`); it has one model, so bit `0` of its count is `1`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.ThreeSat.Check

open Cslib.Logic.PL _root_.Turing.MultiTapeTM

instance {n : ℕ} (φ : CNF (Fin n)) : Decidable (EveryVarOccurs φ) := by
  unfold EveryVarOccurs; infer_instance

/-- The formula `x₀`. -/
def φ₁ : CNF (Fin 1) := [[(0, true)]]

/-- Its instance word, with bit position `0`. -/
def w₁ : List Bool := frame (encNat 0) ++ encSlots φ₁

/-- The decoder reads one clause from `w₁` at size `2`. -/
example : (rawW w₁ 2).m = 1 := by decide

/-- **The network of `x₀` has value `1`, its number of models**, by computation. -/
example : ((rawW w₁ 2).net ℤ).value = 1 := by decide

example : numModels φ₁ = 1 := by decide

/-- The formula `(x₀ ∨ ¬x₁) ∧ x₁`. -/
def φ₂ : CNF (Fin 2) := [[(0, true), (1, false)], [(1, true)]]

/-- `φ₂` with bit position `0` is an instance of Corollary 7.2. -/
def inst₂ : Instance where
  n := 2
  φ := φ₂
  j := 0
  three := by decide
  occurs := by decide
  two_le := by decide

example : numModels φ₂ = 1 := by decide

example : (numModels inst₂.φ).testBit inst₂.j = true := by decide

end Cslib.Complexity.NtimeDspace.Cross.ThreeSat.Check
