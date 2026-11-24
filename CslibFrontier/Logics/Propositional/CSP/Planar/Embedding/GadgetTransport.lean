/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Relabel
public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.ExpansionSymbols
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Symbols
import CslibFrontier.Logics.Propositional.CSP.Occurrence.Symbols

/-!
# Symbol transport and auxiliary alpha-renaming of checked gadgets

Relation-symbol changes retain the same positional successor table. Auxiliary bijections
use the existing actual-body renaming theorem and fix every canonical free-port position.
Neither operation changes the positive cyclic argument order. These contracts apply to
empty and nullary bodies, closed components, and unused ports.

## Main definitions

* `Cslib.Complexity.CSP.OrderedBoundary.Witness.mapRelation`: positional symbol transport.
* `Cslib.Complexity.CSP.OrderedBoundary.GadgetWitness.relabelAux`: auxiliary alpha-renaming.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel Other V : Type} [DecidableEq V]

/-- Change only relation symbols in an ordered body. Its literal table, scopes, boundary
positions and full checker acceptance are retained, without an injectivity premise. -/
@[expose] def Witness.mapRelation {F : CSP Rel V} {ports : List V}
    (w : Witness F ports) (f : Rel → Other) :
    Witness (F.map fun c => ⟨f c.rel, c.scope⟩) ports where
  certificate := w.certificate
  accepted := by
    apply (verify_eq_true_iff _ _ _).mpr
    constructor
    · rw [bodyCertificate, CSP.occurrences_mapRelation,
        verifyRotationCertificate_mapRelation]
      exact w.body_accepted
    · have hp : probeBody (F.map fun c => ⟨f c.rel, c.scope⟩) ports =
          (probeBody F ports).map (fun c => ⟨Option.map f c.rel, c.scope⟩) := by
        simp [probeBody, List.map_map, Function.comp_def]
      rw [hp, verifyRotationCertificate_mapRelation]
      exact w.probe_accepted

omit [DecidableEq V] in
/-- An interpreted symbol map retains the actual ordered witness of a semantic gadget. -/
@[expose] def GadgetWitness.mapRelation {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {otherArity : Other → ℕ} {otherSem : Other → List Bool → Bool}
    {n : ℕ} {R : Set (Fin n → Bool)} {g : PPGadget arity sem R}
    (w : GadgetWitness g) (f : Rel → Other)
    (ha : ∀ r, otherArity (f r) = arity r)
    (hs : ∀ r xs, otherSem (f r) xs = sem r xs) :
    GadgetWitness (g.mapRelation f ha hs) := Witness.mapRelation w f

omit [DecidableEq V] in
/-- Alpha-renaming the actual auxiliary labels preserves canonical free-port order. The
body equality specifies the complete target body, so it cannot hide a scope permutation,
variable identification, or a change to any closed component. -/
@[expose] def GadgetWitness.relabelAux {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {n : ℕ} {R S : Set (Fin n → Bool)} {g : PPGadget arity sem R}
    {h : PPGadget arity sem S} (w : GadgetWitness g)
    (e : Fin g.numAux ≃ Fin h.numAux)
    (hb : h.body = g.body.relabel (Sum.map id e)) : GadgetWitness h where
  certificate := w.certificate
  accepted := by
    let w' := w.relabel (Sum.map id e)
      (fun _ _ _ _ he => (Sum.map_injective.mpr ⟨Function.injective_id, e.injective⟩) he)
    have hp : (List.ofFn (Sum.inl : Fin n → Fin n ⊕ Fin g.numAux)).map
        (Sum.map id e) = List.ofFn Sum.inl := by simp [Function.comp_def]
    rw [hb, ← hp]
    exact w'.accepted

end Cslib.Complexity.CSP.OrderedBoundary
