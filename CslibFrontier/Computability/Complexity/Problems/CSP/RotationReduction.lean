/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSAT
public import CslibFrontier.Computability.PolyTime.CSP.Gadget.PlanarCompiler

/-!
# Native reductions between supplied-rotation CSP languages

Actual ordered gadgets induce native reductions between the canonical supplied-certificate
problems. The output executes the existing guarded replacement compiler; its genus and
argument order are proved internally from the original gadgets. A finite source alphabet
provides one fixed auxiliary bound, chosen independently of every runtime input. Target
symbols and arities are unrestricted.

This is substitution closure, not a hardness theorem: a concrete base reduction is a
separate obligation. Malformed scopes and raw binary successor tables use the compiler's
existing rejecting branch, even when the target alphabet is empty.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Turing.MultiTapeTM

/-- Actual fixed ordered witnesses give a native reduction of the full canonical guarded
languages. No caller-supplied target certificate, genus fact, or compiled satisfiability
equivalence is assumed. This closure theorem itself does not establish a hard source. -/
theorem polyTimeReducible_rotationCSPSAT_of_gadgets {Src Rel : Type} [Finite Src]
    (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool)
    {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}
    {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) :
    PolyTimeReducible (encRotationInstance encSrc) (encRotationInstance encRel)
      (RotationCSPSAT srcArity srcSem) (RotationCSPSAT arity sem) := by
  classical
  obtain ⟨B, hB⟩ := (Set.finite_range fun r => (gadgets r).numAux).bddAbove
  have hb : ∀ r, (gadgets r).numAux ≤ B := fun r => hB ⟨r, rfl⟩
  let f : RotationInstance Src → RotationInstance Rel := fun I =>
    let out := GadgetRotation.compileGadgets gadgets witnesses B (I.constraints, I.rotation)
    ⟨out.1, out.2⟩
  refine ⟨f, ?_, fun I => ?_⟩
  · have hp := GadgetRotation.computableInPolyTime_compileGadgets
      encSrc encRel gadgets witnesses B
    have hi : ComputableInPolyTime (fun I : RotationInstance Src =>
        (I.constraints, I.rotation)) (encRotationInstance encSrc)
        (encCSPRotationCertificate encSrc encNat) :=
      (encRotationInstance_constraints_polyTime encSrc .id').pair
        (encRotationInstance_rotation_polyTime encSrc .id')
    have ho := hp.comp hi
    exact encRotationInstance_mk_polyTime encRel ho.fst' ho.snd'
  · exact (GadgetRotation.wellFormed_certifiedSatisfiable_compileGadgets_iff
      gadgets witnesses B hb (I.constraints, I.rotation)).symm

end Cslib.Complexity.CSP
