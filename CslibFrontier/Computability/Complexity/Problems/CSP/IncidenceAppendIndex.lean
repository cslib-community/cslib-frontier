/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.IncidencePrefix
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Append

/-!
# Body-prefix incidence indices under concatenation

The existing positional append map fixes every incidence index from its left body,
including duplicate constraints, repeated names and empty scopes.

## Main results

* `incidenceEdgeIndex_appendOccurrenceEquiv_inl`: literal left-prefix index preservation.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel V : Type} [DecidableEq V]

/-- Concatenating a right body preserves each original left occurrence's edge index. -/
theorem incidenceEdgeIndex_appendOccurrenceEquiv_inl (F H : CSP Rel V) (o : F.Occurrence) :
    incidenceEdgeIndex (appendOccurrenceEquiv F H (Sum.inl o)) = incidenceEdgeIndex o := by
  rw [incidenceEdgeIndex_eq_prefix, incidenceEdgeIndex_eq_prefix]
  change (CSP.vars ((F ++ H).take o.1.val)).length + o.2.val = _
  rw [List.take_append_of_le_length (Nat.le_of_lt o.1.isLt)]

end Cslib.Complexity.CSP
