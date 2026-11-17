/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Expansion
public import CslibFrontier.Logics.Propositional.CSP.Planar.Crossover
public import CslibFrontier.Logics.Propositional.CSP.Planar.RelationMinor

/-!
# Literal semantic expansion of the crossover source macros

Actual original-language gadgets replace every occurrence in the literal bodies of
[DvorakKupec2015], Figure 1(a,b), printed pp. 440–441. The existing PP expansion retains
free order and independently freshens auxiliaries at every occurrence, including repeated
copies of the same gadget. These constructors assert semantics only.

## Main definitions

* `Cslib.Logic.PL.CSP.Crossover.figureOneAExpanded`: expand Figure 1(a).
* `Cslib.Logic.PL.CSP.Crossover.figureOneBExpanded`: expand Figure 1(b).
-/

public section

namespace Cslib.Logic.PL.CSP.Crossover

open Cslib.BitString RelationMinor

variable {Rel : Type} {ar : Rel → ℕ} {s : Rel → List Bool → Bool}

/-- Expand the two actual occurrences of the four-port relation and the two actual
disequalities in Figure 1(a), retaining their literal ordered scopes. -/
@[expose] def figureOneAExpanded {R : Set (Fin 4 → Bool)} [DecidablePred (· ∈ R)]
    (r : PPGadget ar s R) (d : PPGadget ar s disequality) :
    PPGadget ar s (figureOneARelation R) :=
  (figureOneA R).expand fun
    | .relation => r.retarget (sem_relation R)
    | .disequality => d.retarget (sem_disequality R)

/-- Expand the literal second figure using independently freshened copies of an actual
NEAR-CROSS gadget. Its exact original-language PP body defines CROSS. -/
@[expose] def figureOneBExpanded (r : PPGadget ar s nearCross) : PPGadget ar s cross :=
  figureOneB.expand fun _ => r.retarget nearSem_relation

end Cslib.Logic.PL.CSP.Crossover
