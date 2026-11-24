/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Vars
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Polynomial-time distinct occurring variables of CSP instances

The original certificate lists variables in order of first occurrence, preserving the framed
CSP and variable encodings. It is extracted unchanged from the counting application so that
other native CSP algorithms can use it without importing fine-grained counting endpoints.

## Main results

* `Cslib.Complexity.CSP.computableInPolyTime_distinctVars`: native polynomial-time first-occurrence
  enumeration for arbitrary encoded relation and variable types.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Turing.MultiTapeTM

variable {Rel V : Type}

open Cslib.Logic.PL.CSP ComputableInPolyTime

/-- Listing the distinct occurring variables `CSP.distinctVars` in order of first occurrence is
computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_distinctVars [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.distinctVars (Rel := Rel) (V := V))
      (encCSP encRel encV) (encList encV) := by
  have heq : (CSP.distinctVars (Rel := Rel) (V := V)) = fun F => F.varCNF.distinctVars := by
    funext F
    exact (distinctVars_varCNF F).symm
  rw [heq]
  exact (CNF.computableInPolyTime_distinctVars encV).comp
    (computableInPolyTime_varCNF encRel encV)

end Cslib.Complexity.CSP
