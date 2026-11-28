/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.Complexity.FineGrained.CountingCSP

/-!
# Distinct-variable certificates through the original counting import

An ordinary import of the counting application continues to export the moved certificate and
its registered automation rule, as well as the variable-occurrence API formerly imported
from `CSP.Vars` directly.
-/

public section

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP Turing.MultiTapeTM

-- Generic relation and variable encodings remain available from the original import path.
example {Rel V : Type} [DecidableEq V] (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.distinctVars (Rel := Rel) (V := V))
      (encCSP encRel encV) (encList encV) :=
  computableInPolyTime_distinctVars encRel encV

-- Both the moved rule and the transitive Vars rule compose without local registration.
example : ComputableInPolyTime
    (fun F : CSP Bool ℕ => (F.vars, F.distinctVars))
    (encCSP encBool encNat) (encPair (encList encNat) (encList encNat)) := by
  fun_prop

example : CSP.distinctVars
    ([⟨false, [41, 3, 41]⟩, ⟨true, [3, 99, 41]⟩] : CSP Bool ℕ) = [41, 3, 99] := by
  decide
