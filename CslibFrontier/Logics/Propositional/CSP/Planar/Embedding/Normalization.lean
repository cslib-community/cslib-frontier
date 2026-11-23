/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Normalization.Program
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Normalization.Twist

/-!
# Ordered numerical witnesses for completed normalization constructions

The literal twist and every instruction of the existing normalization interpreter supply
their own ordered numerical witness. Thus every completed `Normalization.Construction`
has a witness for its actual gadget, without any target-order or genus provider. All existing
semantics, body sizes and auxiliary bounds are unchanged.

This is an original numerical reconstruction related to [DvorakKupec2015], §4, printed p. 440,
Lemma 6, whose proof is omitted in the ICALP 2015 version. Agreement of the numerical model
with the source's geometric plane instances, arbitrary pp closure, recognition and the full
planar-hardness theorem are separate obligations. No uniform preprocessing bound is asserted.
-/

public section

namespace Cslib.Logic.PL.CSP.Normalization

open Cslib.Complexity.CSP.OrderedBoundary

/-- Every completed normalization construction internally supplies an ordered numerical
witness for its exact actual gadget. The original atom, spoke order, free order, unused labels
and guarded cap auxiliary layout are retained by the existing interpreter. -/
noncomputable def Construction.orderedWitness {n : ℕ} {R : Set (Fin n → Bool)}
    (c : Construction R) : GadgetWitness c.gadget :=
  (Program.rotate c.start c.reduction).orderedWitness (twistBodyWitness c.tuple)

end Cslib.Logic.PL.CSP.Normalization
