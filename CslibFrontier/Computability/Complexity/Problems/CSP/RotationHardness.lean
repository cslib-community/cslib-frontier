/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.OneHot3.Hardness
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationReduction
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.OneHotExpansion

/-!
# Original-language native hardness without a common complement

The internally derived original-language ordered OneHot3 gadget substitutes into the actual
hard supplied-certificate base. The output executes the guarded native gadget compiler on
all raw instances. No pin, enabling-tree, rotation, genus, or hardness provider is assumed.
The target alphabet need not be finite; its fixed encoding and actual gadgets suffice for
hardness. Finite alphabets additionally give membership in NP through the canonical verifier.
The language here includes a supplied full numerical rotation certificate; comparison with
the original source plane model is a separate obligation.

This is the no-common-complement branch. Languages with common complement require the
separate actual CROSS planarization argument; the OneHot3 gadget is not asserted for them.

## Main results

* `npHard_of_not_hasSchaeferPolymorphism_of_not_hasComplement`:
  native original-language hardness for arbitrary encoded target alphabets and arities.
-/

public section

namespace Cslib.Complexity.RotationCSPSAT

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity.CSP Turing.MultiTapeTM
open OrderedBoundary

/-- Outside the six Schaefer operations and common complement, the original supplied
ordered-certificate problem is native NP-hard. Target relations have arbitrary arity and
body degree, and the target alphabet need not be finite. -/
theorem npHard_of_not_hasSchaeferPolymorphism_of_not_hasComplement {Rel : Type}
    (encRel : Rel ↪ List Bool) (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : ¬HasSchaeferPolymorphism arity sem)
    (hn : ¬HasPolymorphism arity sem (fun a : Fin 1 → Bool => !(a 0))) :
    NPHard (encRotationInstance encRel) (RotationCSPSAT arity sem) := by
  classical
  obtain ⟨g, ⟨w⟩⟩ : ∃ g : PPGadget arity sem (booleanRelation OneHot3.arity OneHot3.sem ()),
      Nonempty (GadgetWitness g) :=
    OneHot3.booleanRelation_eq.symm ▸ NonSelfDual.exists_orderedOneHotGadget h hn
  exact OneHot3.npHard.trans
    (polyTimeReducible_rotationCSPSAT_of_gadgets encUnit encRel (fun _ => g) (fun _ => w))

end Cslib.Complexity.RotationCSPSAT
