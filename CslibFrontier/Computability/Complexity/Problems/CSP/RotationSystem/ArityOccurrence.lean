/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem
public import CslibFrontier.Logics.Propositional.CSP.Boolean
import CslibFrontier.Logics.Propositional.CSP.Occurrence.Positions
import CslibFrontier.Foundations.GroupTheory.Perm.Fin

/-!
# Declared-arity coordinates for actual argument occurrences

Exact scope width identifies declared relation ports with the original scope positions.
The existing cyclic argument successor commutes with this identification. This accessor
and proof are shared by gadget substitution and native ternary scope alignment.

## Main definitions

* `Cslib.Complexity.CSP.arityOccurrence`: read an actual occurrence by its declared port.

## Main results

* `Cslib.Complexity.CSP.argumentSuccessor_arityOccurrence`: retain cyclic argument succession.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

variable {Rel V : Type} {arity : Rel → ℕ}

/-- Read an original occurrence by its constraint position and declared relation port. -/
@[expose] def arityOccurrence (F : CSP Rel V) (hF : F.WellFormed arity) (i : Fin F.length)
    (a : Fin (arity F[i.val].rel)) : F.Occurrence :=
  ⟨i, Fin.cast (hF F[i.val] (List.getElem_mem i.isLt)).symm a⟩

/-- Declared-arity coordinates retain the literal positive cyclic argument successor. -/
theorem argumentSuccessor_arityOccurrence (F : CSP Rel V) (hF : F.WellFormed arity)
    (i : Fin F.length) (a : Fin (arity F[i.val].rel)) :
    argumentSuccessor (arityOccurrence F hF i a) =
      arityOccurrence F hF i (finRotate (arity F[i.val].rel) a) := by
  apply CSP.Occurrence.eq_of_positions
  · rfl
  · simp only [argumentSuccessor, arityOccurrence, val_finRotate, Fin.val_cast,
      hF F[i.val] (List.getElem_mem i.isLt)]

end Cslib.Complexity.CSP
