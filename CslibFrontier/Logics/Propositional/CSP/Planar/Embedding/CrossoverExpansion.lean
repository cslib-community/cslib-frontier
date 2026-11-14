/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Expansion
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Crossover
public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.ExpansionCrossover

/-!
# Original-language expansion of the two crossover macros

The literal source scopes of [DvorakKupec2015], Figure 1(a,b), printed pp. 440–441,
are retained, together with the existing original numerical certificate tables.
The input relations are actual original-language gadgets with
checked positive ordered boundaries. Every occurrence expands independently via the generic
static bridge, including the two copies of the same four-port gadget. No reflection or
higher-arity conjunction closure is assumed.

## Main definitions

* `Cslib.Logic.PL.CSP.Crossover.figureOneAExpandedWitness`: ordered first-figure expansion.
* `Cslib.Logic.PL.CSP.Crossover.figureOneBExpandedWitness`: ordered second-figure expansion.

## Main results

* `Cslib.Logic.PL.CSP.Crossover.exists_orderedCross_of_standardized`: original-language CROSS.
-/

public section

namespace Cslib.Logic.PL.CSP.Crossover

open Cslib.BitString RelationMinor Cslib.Complexity.CSP.OrderedBoundary

variable {Rel : Type} {ar : Rel → ℕ} {s : Rel → List Bool → Bool}

/-- The full ordered witness on the literal expanded first figure. -/
def figureOneAExpandedWitness {R : Set (Fin 4 → Bool)} [DecidablePred (· ∈ R)]
    {r : PPGadget ar s R} {d : PPGadget ar s disequality}
    (wr : GadgetWitness r) (wd : GadgetWitness d) :
    GadgetWitness (figureOneAExpanded r d) := by
  unfold figureOneAExpanded
  refine GadgetWitness.expand (g := figureOneA R) figureOneABoundary _ ?_
    (r.numAux + d.numAux) ?_
  · intro t
    cases t with
    | relation => exact wr
    | disequality => exact wd
  · intro t
    cases t <;> simp only [PPGadget.retarget] <;> omega

/-- The second figure retains its literal cyclic order through actual expansion. -/
def figureOneBExpandedWitness {r : PPGadget ar s nearCross}
    (w : GadgetWitness r) : GadgetWitness (figureOneBExpanded r) := by
  unfold figureOneBExpanded
  exact GadgetWitness.expand figureOneBBoundary _ (fun _ => w) r.numAux (fun _ => le_rfl)

/-- An actual standardized relation and actual disequality gadget give original-language
CROSS with an internally constructed checked boundary. The first figure is used once; its
NEAR-CROSS outcome uses the second figure, with no extra provider premise. -/
theorem exists_orderedCross_of_standardized {R : Set (Fin 4 → Bool)}
    (hR : IsStandardizedInconsistent R)
    (r : PPGadget ar s R) (d : PPGadget ar s disequality)
    (wr : GadgetWitness r) (wd : GadgetWitness d) :
    ∃ g : PPGadget ar s cross, Nonempty (GadgetWitness g) := by
  classical
  have hex : ∃ g : PPGadget ar s (figureOneARelation R), Nonempty (GadgetWitness g) :=
    ⟨figureOneAExpanded r d, ⟨figureOneAExpandedWitness wr wd⟩⟩
  rcases figureOneA_target R hR with h | h
  · rwa [h] at hex
  · rw [h] at hex
    obtain ⟨g, ⟨w⟩⟩ := hex
    exact ⟨figureOneBExpanded g, ⟨figureOneBExpandedWitness w⟩⟩

end Cslib.Logic.PL.CSP.Crossover
