/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.PolyTime.CSP.DistinctVars

/-!
# Ordinary clients of polynomial-time distinct CSP variables

The low import supplies the registered certificate and the variable-occurrence API. Binary
sparse labels and repeated occurrences retain their first-occurrence order, independently of
constraint relation symbols and empty scopes.
-/

public section

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP Turing.MultiTapeTM

-- The moved rule composes with the existing occurrence rule through an ordinary import.
example : ComputableInPolyTime
    (fun F : CSP Bool ℕ => (F.distinctVars, F.vars))
    (encCSP encBool encNat) (encPair (encList encNat) (encList encNat)) := by
  fun_prop

-- Kernel computation checks first occurrence rather than sorting or retaining the last copy.
example : CSP.distinctVars
    ([⟨true, [2 ^ 100, 7, 2 ^ 100]⟩, ⟨false, []⟩, ⟨false, [9, 7, 0, 9]⟩] : CSP Bool ℕ) =
      [2 ^ 100, 7, 9, 0] := by
  decide

example : CSP.distinctVars ([] : CSP Bool ℕ) = [] := by decide
