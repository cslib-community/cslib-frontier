/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.VariableFibers
public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.Partition
public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.RotationFromCycles
import Mathlib.Data.List.GetD

/-!
# The actual positional substitution rotation

The executed replacement words are proved to be exactly the variable fibers of the existing
replacement body. They therefore determine an actual permutation and incidence rotation, and
its canonical certificate is the literal computed replacement certificate. Neither a target
rotation nor an endpoint-fiber provider is supplied. Numerical genus zero is a separate
obligation; this topic does not assert full ordered numerical checker acceptance.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- Each actual executed word is the complete target occurrence fiber of one actual even
source name or private odd auxiliary name. Empty fibers give empty words. -/
theorem replacementCycles_word_fiber
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (word : List ℕ)
    (hw : word ∈ replacementCycles (fun r => (gadgets r).template)
      (fun r => freeBoundaryBlocks (gadgets r) (witnesses r))
      (fun r => auxiliaryBoundaryBlocks (gadgets r) (witnesses r)) F c) :
    ∃ label : ℕ, ∀ index, index ∈ word ↔
      index < (replaceGadgets B (fun r => (gadgets r).template) F).vars.length ∧
        (replaceGadgets B (fun r => (gadgets r).template) F).vars.getD index 0 = label := by
  rcases (mem_replacementCycles_iff ..).mp hw with ⟨v, hv, rfl⟩ | ⟨i, _, hb, rfl⟩
  · exact ⟨2 * v, mem_variableBlock_iff_targetName gadgets witnesses B F hF c hc v
      (CSP.mem_distinctVars.mp hv)⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
    refine ⟨2 * (B * i.val + j) + 1, fun index => ?_⟩
    simpa only [List.getD_eq_getElem _ _ hj] using
      mem_shifted_auxiliaryBlock_iff_targetName gadgets witnesses B hB F i.isLt
        ⟨j, by simpa only [length_auxiliaryBoundaryBlocks] using hj⟩ index

/-- The actual product permutation of the emitted words has exactly the original target
variable fibers. This is derived from real checked gadget witnesses, not assumed by a caller. -/
theorem sameCycle_replacementCycles_iff
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (o p : (replaceGadgets B (fun r => (gadgets r).template) F).Occurrence) :
    (List.cyclePermutation (replacementCycles (fun r => (gadgets r).template)
      (fun r => freeBoundaryBlocks (gadgets r) (witnesses r))
      (fun r => auxiliaryBoundaryBlocks (gadgets r) (witnesses r)) F c)).SameCycle
      (incidenceEdgeIndex o) (incidenceEdgeIndex p) ↔ o.var = p.var := by
  obtain ⟨word, hw, how⟩ := List.mem_flatten.mp <|
    (mem_flatten_replacementCycles_iff gadgets witnesses B F hF c hc _).mpr
      (incidenceEdgeIndex_lt_vars o)
  obtain ⟨label, hfiber⟩ := replacementCycles_word_fiber gadgets witnesses B hB F hF c hc word hw
  rw [List.sameCycle_cyclePermutation_iff_of_mem _
    (nodup_flatten_replacementCycles gadgets witnesses F hF c hc) word hw _ _ how,
    hfiber (incidenceEdgeIndex p), getD_vars_incidenceEdgeIndex,
    ← (getD_vars_incidenceEdgeIndex o 0).symm.trans ((hfiber _).mp how).2]
  exact ⟨fun h => h.2.symm, fun h => ⟨incidenceEdgeIndex_lt_vars p, h.symm⟩⟩

/-- The exact computed variable words, together with the original target argument order,
construct an actual target rotation with its permutation and endpoint fibers proved internally. -/
@[expose] noncomputable def replacementRotation
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true) :
    RotationSystem (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)) :=
  rotationOfVariableCycles _ _
    (fun i => by
      simpa only [incidenceGraph_edges, List.length_map, ← CSP.map_occurrences,
        List.length_map] using mem_flatten_replacementCycles_iff gadgets witnesses B F hF c hc i)
    (sameCycle_replacementCycles_iff gadgets witnesses B hB F hF c hc)

/-- The actual constructed rotation follows the existing target body's literal positive
argument order at every constraint, including repeated and nullary scopes. -/
theorem respectsArgumentOrder_replacementRotation
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true) :
    RespectsArgumentOrder (replacementRotation gadgets witnesses B hB F hF c hc) :=
  respectsArgumentOrder_rotationOfVariableCycles _ _ _

/-- The constructed target rotation's canonical finite table is the actual computed table,
not a new certificate selected by proof-side choice or search. -/
theorem ofRotation_replacementRotation
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true) :
    RotationCertificate.ofRotation (replacementRotation gadgets witnesses B hB F hF c hc) =
      replacementCertificate B (fun r => (gadgets r).template)
        (fun r => freeBoundaryBlocks (gadgets r) (witnesses r))
        (fun r => auxiliaryBoundaryBlocks (gadgets r) (witnesses r)) F c := by
  unfold replacementRotation replacementCertificate
  exact ofRotation_rotationOfVariableCycles_eq _ _ _ _
    (nodup_flatten_replacementCycles gadgets witnesses F hF c hc)

/-- The complete original raw permutation/endpoint-fiber checker accepts the exact emitted
target table. Full numerical genus acceptance still requires the genus theorem. -/
theorem verifyRotation_replacementCertificate
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true) :
    RotationCertificate.verifyRotation
      (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F))
      (replacementCertificate B (fun r => (gadgets r).template)
        (fun r => freeBoundaryBlocks (gadgets r) (witnesses r))
        (fun r => auxiliaryBoundaryBlocks (gadgets r) (witnesses r)) F c) = true := by
  rw [← ofRotation_replacementRotation gadgets witnesses B hB F hF c hc]
  exact RotationCertificate.verifyRotation_ofRotation _ (incidenceVertices_declared _)

end Cslib.Complexity.CSP.GadgetRotation
