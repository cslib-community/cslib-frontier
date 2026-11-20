/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Quantum.Multiprover
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic

/-!
# Quantum multiprover interactive proofs

The verifier uses polynomially many rounds and provers. Independent local responses may use
an arbitrary shared finite-dimensional quantum state [KobayashiMatsumoto2003, §3.2].

## Main definitions

* `Cslib.Complexity.PromiseQMIP` and `Cslib.Complexity.QMIP`: the promise and language classes.
-/

public section

namespace Cslib.Complexity

open Cslib.Quantum

/-- Quantum multiprover interactive proofs with unrestricted finite prior entanglement. -/
@[expose] def PromiseQMIP {α : Type} (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {X | ∃ V : UniformMultiproverVerifier,
    (∀ a ∈ X.yes, ∃ (p : ℕ) (state : Qubits (V.proverCount (enc a).length * p))
      (strategy : V.Strategy (enc a).length p), ‖state‖ = 1 ∧
      2 / 3 ≤ V.acceptProb (enc a) state strategy) ∧
    (∀ a ∈ X.no, ∀ (p : ℕ) (state : Qubits (V.proverCount (enc a).length * p))
      (strategy : V.Strategy (enc a).length p), ‖state‖ = 1 →
      V.acceptProb (enc a) state strategy ≤ 1 / 3)}

/-- Quantum multiprover interactive proofs for languages, with soundness on the complement. -/
@[expose] def QMIP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | PromiseProblem.ofSet A ∈ PromiseQMIP enc}

end Cslib.Complexity
