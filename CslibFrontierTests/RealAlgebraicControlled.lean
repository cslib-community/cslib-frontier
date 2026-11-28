/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (controlled-polynomial certificate and modular-value tests)

public import CslibFrontier.Computability.Complexity.RealAlgebraic.Controlled
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledFeasibility

/-! Nonempty controlled families include zero arity, signed constants and binary powers. -/

public section
namespace CslibFrontierTests.RealAlgebraicControlled

open Cslib.Complexity.RealAlgebraic Cslib.Complexity Turing.MultiTapeTM MvPolynomial

noncomputable def emptyArity :
    Controlled (fun _ : ℕ => C (-37) : ℕ → MvPolynomial (Fin 0) ℤ) encNat 0 :=
  Controlled.constant (.const 0) (fun _ => -37) (.const (-37))

-- Arity zero still has an empty assignment and a genuine signed constant evaluator.
example (w : ℕ) : emptyArity.evaluate (w, 5, []) = 3 := by
  have h := emptyArity.evaluate_eq w 5 [] (by decide) (by simp [emptyArity, Controlled.constant])
  norm_num [evaluation] at h ⊢
  exact h

private noncomputable def coordinate :
    Controlled (fun _ : ℕ => X (0 : Fin 1) : ℕ → MvPolynomial (Fin 1) ℤ) encNat 0 :=
  Controlled.coordinate (.const 1) (fun _ => 0) (.const 0)

private noncomputable def powers :
    Controlled (fun w : ℕ => X (0 : Fin 1) ^ w) encNat 0 :=
  coordinate.pow id ComputableInPolyTime.id'

-- One uniform evaluator handles the input-dependent binary exponent.
example : powers.evaluate (10, 5, [2]) = 4 := by
  have h := powers.evaluate_eq 10 5 [2] (by decide) (by decide)
  norm_num [evaluation] at h ⊢
  exact h

-- Composite and zero moduli are allowed inputs to the total evaluator.
example : powers.evaluate (10, 0, [2]) = 1 := by
  simp [powers, Controlled.pow, powMod]

-- The empty word suffices when the first system is zero and the second is a nonzero constant.
example : (Set.univ : Set (List Bool)) ∈ CountingLevel 27 encBits := by
  let CP := Controlled.constant (enc := encPair encBits encBits) (a := 0) (n := fun _ => 0)
    (.const 0) (fun _ => 0) (.const 0)
  let CQ := Controlled.constant (enc := encPair encBits encBits) (a := 0) (n := fun _ => 1)
    (.const 1) (fun _ => 1) (.const 1)
  have h := CP.boundedFeasibilityTests_mem CQ Decoder.bits (fun _ => 0) (.const 0)
  convert h using 1
  ext w
  simp

end CslibFrontierTests.RealAlgebraicControlled
