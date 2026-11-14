/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.Genus
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.GadgetTransport
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Probe
import Mathlib.Data.List.Enum
import Mathlib.Data.List.GetD

/-!
# Expanding an actual ordered body while retaining its exterior probe

The probe is an atom over a separate structural symbol. All original symbols expand by
the existing replacement compiler; the probe remains one star in exactly its old reversed
order. Applying the full substitution theorem to this augmented body therefore gives a
checked boundary for the actual expanded body. No target genus, fiber or order fact is
supplied by the caller. The preprocessing is static and nonuniform.

## Main definitions

* `Cslib.Complexity.CSP.OrderedBoundary.GadgetWitness.withProbe`: retain the probe atom.
* `Cslib.Complexity.CSP.OrderedBoundary.Witness.replaceGadgets`: checked numeric boundary expansion.

## Main results

* `Cslib.Complexity.CSP.OrderedBoundary.verifyRotationCertificate_replaceGadgets_probe`:
  acceptance of the literal expanded body with its retained probe order.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP GadgetRotation

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

private theorem wellFormed_probeBody {V : Type} (F : CSP Src V)
    (hF : WellFormed srcArity F) (ports : List V) :
    WellFormed (Option.elim' ports.length srcArity) (probeBody F ports) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact hF d hd
  · simp only [List.mem_singleton] at hc
    subst c
    exact List.length_reverse

private theorem replaceGadgets_probeBody
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (ports : List ℕ) :
    replaceGadgets B (fun r => (PPGadget.withProbe gadgets ports.length r).template)
        (probeBody F ports) =
      probeBody (replaceGadgets B (fun r => (gadgets r).template) F)
        (ports.map (2 * ·)) := by
  simp only [replaceGadgets, probeBody, List.zipIdx_append, List.zipIdx_map,
    List.length_map, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_append,
    List.flatMap_map, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  congr 1
  · simp only [List.map_flatMap]
    apply List.flatMap_congr
    rintro ⟨c, i⟩ _
    simp only [Prod.map, id_eq]
    dsimp only [PPGadget.withProbe, PPGadget.mapRelation, instantiate, PPGadget.template,
      CSP.relabel]
    change List.map (Constraint.relabel (fun p : Bool × ℕ =>
        if p.1 then 2 * (B * i + p.2) + 1 else 2 * c.scope.getD p.2 0))
      (List.map (Constraint.relabel (Sum.elim
        (fun i : Fin (srcArity c.rel) => (false, i.val))
        (fun i : Fin (gadgets c.rel).numAux => (true, i.val))))
        ((gadgets c.rel).body.map (fun d => ⟨some d.rel, d.scope⟩))) = _
    simp only [List.map_map]
    apply List.map_congr_left
    intro d _
    apply Constraint.ext
    · rfl
    rfl
  · have hp : List.ofFn (fun i : Fin ports.length => 2 * ports.reverse.getD i.val 0) =
        ports.reverse.map (2 * ·) := by
      apply List.ext_getElem
      · simp
      · intro i hi hj
        simp
    simp only [Nat.zero_add]
    change instantiate B F.length ports.reverse (PPGadget.atom
      (arity := Option.elim' ports.length arity)
      (sem := Option.elim' (fun _ => true) sem) none).template =
      [⟨none, (ports.map (2 * ·)).reverse⟩]
    dsimp only [PPGadget.atom, instantiate, PPGadget.template, CSP.relabel, Option.elim']
    simp only [List.map_cons, List.map_nil, Constraint.relabel, List.map_ofFn,
      Function.comp_def, Sum.elim_inl, Bool.false_eq_true, reduceIte]
    apply congrArg (fun scope => [Constraint.mk (none : Option Rel) scope])
    simpa only [List.map_reverse] using hp

/-- Extend actual replacement witnesses by the ordered tautological probe atom. The
original symbol cases keep exactly the same scopes and certificate tables. -/
@[expose] def GadgetWitness.withProbe
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (n : ℕ) :
    ∀ r, GadgetWitness (PPGadget.withProbe gadgets n r)
  | some r => GadgetWitness.mapRelation (witnesses r) some (fun _ => rfl) (fun _ _ => rfl)
  | none => Witness.atom _ _ none

/-- The existing deterministic block splice accepts the literal expanded body with its
unchanged probe order. The structural probe is replaced by its actual atom, so this is
an exact checker contract, including nullaries and closed components. -/
theorem verifyRotationCertificate_replaceGadgets_probe
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (ports : List ℕ) (c : Graph.RotationCertificate)
    (hc : verifyRotationCertificate (probeBody F ports) c = true) :
    verifyRotationCertificate
      (probeBody (replaceGadgets B (fun r => (gadgets r).template) F) (ports.map (2 * ·)))
      (replacementCertificate B (fun r => (PPGadget.withProbe gadgets ports.length r).template)
        (fun r => freeBoundaryBlocks (PPGadget.withProbe gadgets ports.length r)
          (GadgetWitness.withProbe gadgets witnesses ports.length r))
        (fun r => auxiliaryBoundaryBlocks (PPGadget.withProbe gadgets ports.length r)
          (GadgetWitness.withProbe gadgets witnesses ports.length r)) (probeBody F ports) c) =
      true := by
  have hb : ∀ r, (PPGadget.withProbe gadgets ports.length r).numAux ≤ B := by
    intro r
    cases r with
    | none => exact Nat.zero_le _
    | some r => exact hB r
  have h := verifyRotationCertificate_replacementCertificate
    (PPGadget.withProbe gadgets ports.length)
    (GadgetWitness.withProbe gadgets witnesses ports.length)
    B hb (probeBody F ports) (wellFormed_probeBody F hF ports) c hc
  rwa [replaceGadgets_probeBody] at h

/-- Expand the literal numeric body of an actual checked ordered macro, retaining its
listed free ports in their original positive order. The actual probe atom and target
certificate are constructed internally. Distinctness is needed only for the probe-deletion
API; repeated names inside source scopes and duplicate constraints are unrestricted. -/
@[expose] def Witness.replaceGadgets {F : CSP Src ℕ} {ports : List ℕ}
    (w : Witness F ports) (hn : ports.Nodup) (hF : WellFormed srcArity F)
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) :
    Witness (replaceGadgets B (fun r => (gadgets r).template) F) (ports.map (2 * ·)) :=
  Witness.ofProbe (hn.map (mul_right_injective₀ (by decide : (2 : ℕ) ≠ 0)))
    (replacementCertificate B (fun r => (PPGadget.withProbe gadgets ports.length r).template)
      (fun r => freeBoundaryBlocks (PPGadget.withProbe gadgets ports.length r)
        (GadgetWitness.withProbe gadgets witnesses ports.length r))
      (fun r => auxiliaryBoundaryBlocks (PPGadget.withProbe gadgets ports.length r)
        (GadgetWitness.withProbe gadgets witnesses ports.length r))
      (probeBody F ports) w.certificate)
    (verifyRotationCertificate_replaceGadgets_probe gadgets witnesses B hB F hF ports
      w.certificate w.probe_accepted)

end Cslib.Complexity.CSP.OrderedBoundary
