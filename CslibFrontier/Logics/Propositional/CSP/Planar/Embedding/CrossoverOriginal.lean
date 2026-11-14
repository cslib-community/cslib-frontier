/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.CrossoverExpansion
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.SelfDual
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Normalization
public import CslibFrontier.Logics.Propositional.CSP.Planar.Normalization

/-!
# Original-language CROSS from a bad original cyclic-difference relation

Failure of the six Schaefer polymorphisms together with a common complement and an
actual nonempty original relation whose cyclic differences fail the even-delta-matroid
condition suffice
for an original-language CROSS gadget with a checked ordered boundary. Disequality,
normalization, and both expanded Figure 1 macros are constructed internally. There is
no normalized-relation, enabling-gadget, target-witness or planar-PP-closure provider.

The endpoint is static finite ordered numerical mathematics. It does not identify this
representation with the source's plane instances, recognize planarity, provide a uniform
native compiler, or finish the full hardness objective of [DvorakKupec2015], §4.

## Main results

* `Cslib.Logic.PL.CSP.Crossover.exists_orderedCrossGadget`:
  actual original-language CROSS and its checked ordered witness.
-/

public section

namespace Cslib.Logic.PL.CSP.Crossover

open Cslib.BitString RelationMinor Cslib.Complexity.CSP.OrderedBoundary

variable {Rel : Type} {ar : Rel → ℕ} {s : Rel → List Bool → Bool}

private noncomputable def normalizationReplacements (r : Rel)
    (d : PPGadget ar s disequality) :
    ∀ t, PPGadget ar s (booleanRelation (Normalization.arity (ar r))
      (Normalization.sem (booleanRelation ar s r)) t)
  | .relation => (PPGadget.atom (arity := ar) (sem := s) r).retarget
      (Normalization.sem_relation (booleanRelation ar s r))
  | .disequality => d.retarget fun a => by
      simp [booleanRelation, Normalization.arity, List.ofFn_succ, disequality]

private noncomputable def normalizationReplacementWitnesses (r : Rel)
    (d : PPGadget ar s disequality) (wd : GadgetWitness d) :
    ∀ t, GadgetWitness (normalizationReplacements r d t)
  | .relation => Witness.atom ar s r
  | .disequality => wd

/-- Original-language CROSS and its full checked ordered witness, from only actual
language/polymorphism and bad-original-relation premises. The original alphabet is unchanged,
its arities are unrestricted, and it need not be finite. -/
theorem exists_orderedCrossGadget (h : ¬HasSchaeferPolymorphism ar s)
    (hnot : HasPolymorphism ar s (fun a : Fin 1 → Bool => !(a 0)))
    (r : Rel) (hne : (booleanRelation ar s r).Nonempty)
    (hbad : ¬IsEvenDeltaMatroid (cyclicDifferenceRelation (booleanRelation ar s r))) :
    ∃ g : PPGadget ar s cross, Nonempty (GadgetWitness g) := by
  classical
  have hself : IsSelfComplementary (booleanRelation ar s r) := by
    intro x
    constructor
    · intro hx
      exact hnot r (fun _ => x) (fun _ => hx)
    · intro hx
      simpa only [Bool.not_not] using hnot r (fun _ i => !(x i)) (fun _ => hx)
  obtain ⟨d, ⟨wd⟩⟩ := exists_disequality_of_common_not hnot (fun hf => h (.inl hf))
  obtain ⟨_, ⟨c⟩⟩ := Normalization.exists_construction (booleanRelation ar s r) hne hself hbad
  let gs := normalizationReplacements r d
  let ws := normalizationReplacementWitnesses r d wd
  have hb : ∀ t, (gs t).numAux ≤ d.numAux := by
    intro t
    cases t <;> simp [gs, normalizationReplacements, PPGadget.retarget, PPGadget.atom]
  let g := c.gadget.expand gs
  let w : GadgetWitness g := c.orderedWitness.expand gs ws d.numAux hb
  exact exists_orderedCross_of_standardized c.standardized g d w wd

end Cslib.Logic.PL.CSP.Crossover
