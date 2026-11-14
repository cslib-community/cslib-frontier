/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Replacement
import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Composition

open Cslib.Logic.PL Cslib.Logic.PL.CSP

namespace CSPGadgetExpansionPointwiseTest

def arity (r : Bool) : ℕ := if r then 1 else 0

def sem : Bool → List Bool → Bool
  | true, [b] => b
  | _, _ => false

def unary := PPGadget.atom (arity := arity) (sem := sem) true

def assignment (v : ℕ) : Bool := decide (v = 18)

-- An ordinary import exposes the original pointwise equation. This caller fixes the
-- boundary assignment, instead of weakening the result to existential satisfiability.
example : (instantiate 5 2 [9] unary.template).eval sem assignment = true := by
  rw [eval_instantiate]
  decide +kernel

-- The equation also retains the original total out-of-range source lookup fallback.
example : (instantiate 5 2 [] unary.template).eval sem assignment = false := by
  rw [eval_instantiate]
  decide +kernel

-- The nullary original relation is false, although its scope and template are well formed.
example : (instantiate 0 0 []
    (PPGadget.atom (arity := arity) (sem := sem) false).template).eval sem assignment = false := by
  rw [eval_instantiate]
  decide +kernel

end CSPGadgetExpansionPointwiseTest
