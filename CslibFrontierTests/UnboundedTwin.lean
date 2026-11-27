/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Circuit.Boolean.Unbounded.Twin

/-! Checked clients of the twin construction (Arora–Barak, Exercise 13.1): a negation gate becomes
a negation-free circuit on the literals, and the exercise's `10 S` size bound follows. -/

set_option linter.privateModule false

namespace CslibFrontierTests.UnboundedTwin

open Cslib Cslib.Circuits Cslib.Circuits.Boolean.Unbounded

/-- The twin of a single negation gate computes the negation from the literals, with two gates
and no negation gate. -/
example (x : BitString 1) :
    (twinCircuit (Circuit.oneGate (σ := signature) .not fun _ => 0)).eval interpretation
      (Boolean.AltFormula.literals x) 0 = !x 0 := by
  rw [eval_twinCircuit]
  rfl

example : (twinCircuit (Circuit.oneGate (σ := signature) (n := 1) .not fun _ => 0)).size = 2 :=
  rfl

/-- Arora–Barak, Exercise 13.1, in the exercise's form: size `10 S`, depth `d`, no negations. -/
example {n m d S : ℕ} {f : BitString n → BitString m} (C : Circuit signature n m)
    (hC : C.Computes interpretation f) (hd : C.depth ≤ d) (hS : C.size ≤ S) :
    ∃ C' : Circuit signature (n + n) m, (∀ k, (C'.program.lines k).op ≠ .not) ∧
      (∀ x, C'.eval interpretation (Boolean.AltFormula.literals x) = f x) ∧
      C'.depth ≤ d ∧ C'.size ≤ 10 * S := by
  obtain ⟨C', h₁, h₂, h₃, h₄⟩ := exists_notFree_circuit C hC hd hS
  exact ⟨C', h₁, h₂, h₃, by omega⟩

end CslibFrontierTests.UnboundedTwin
