/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Quantum.Interactive
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic

/-!
# Quantum interactive proofs

A uniform verifier exchanges a quantum message register with a prover whose private
quantum workspace can have any finite width. On yes-instances there exists a prover
strategy accepted with probability at least 2/3. On no-instances every prover strategy
is accepted with probability at most 1/3 [Watrous2008, §VI.1].

## Main definitions

* `Cslib.Complexity.PromiseQIP` and `Cslib.Complexity.QIP`: quantum interactive proofs
  for promise problems and languages.
-/

public section

namespace Cslib.Complexity

open Cslib.Quantum

/-- Polynomial-round quantum interactive proofs for promise problems. The verifier works
against every finite-dimensional prover strategy on no-instances. -/
@[expose] def PromiseQIP {α : Type} (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {X | ∃ V : UniformInteractiveVerifier,
    (∀ a ∈ X.yes, ∃ (p : ℕ) (strategy : V.Strategy (enc a).length p),
      2 / 3 ≤ V.acceptProb (enc a) strategy) ∧
    (∀ a ∈ X.no, ∀ (p : ℕ) (strategy : V.Strategy (enc a).length p),
      V.acceptProb (enc a) strategy ≤ 1 / 3)}

/-- Quantum interactive proofs for languages, with soundness on the complement. -/
@[expose] def QIP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | PromiseProblem.ofSet A ∈ PromiseQIP enc}

end Cslib.Complexity
