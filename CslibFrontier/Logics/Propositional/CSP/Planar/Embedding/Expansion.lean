/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.ExpansionProbe
public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.ExpansionNames

/-!
# Checked static expansion of ordered primitive-positive macros

An actual checked macro and actual checked replacement gadgets produce a checked witness
for the literal semantic expansion. The proof uses the existing numeric substitution theorem,
then its explicit injection from ragged Fin blocks into the padded even/odd namespace.
The old macro auxiliaries precede independent per-occurrence replacement blocks. No target
witness, genus, order, injection, connectedness or finite-alphabet premise is required.

A uniform auxiliary bound describes the numeric intermediate representation only. It does
not change the ragged semantic body or imply a uniform native compiler or recognition result.

## Main definitions

* `Cslib.Complexity.CSP.OrderedBoundary.Witness.expandList`: the actual ragged expanded body.
* `Cslib.Complexity.CSP.OrderedBoundary.GadgetWitness.expand`:
  the expanded canonical gadget boundary.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- Expand a finite checked conjunction, retaining each selected original free port in
its listed order. Auxiliary labels are the actual ragged blocks of `PPGadget.expandList`.
The injection into numeric replacement names and all target invariants are proved internally. -/
@[expose] def Witness.expandList {k : ℕ} {F : CSP Src (Fin k)} {ports : List (Fin k)}
    (w : Witness F ports) (hn : ports.Nodup) (hF : WellFormed srcArity F)
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) :
    Witness (PPGadget.expandList gadgets F hF).body (ports.map Sum.inl) := by
  let wn := w.relabel Fin.val (fun _ _ _ _ he => Fin.ext he)
  let wr := wn.replaceGadgets (hn.map Fin.val_injective) (hF.relabel Fin.val)
    gadgets witnesses B hB
  let name := PPGadget.expansionName gadgets B F hF
  have hi := PPGadget.expansionName_injective gadgets B hB F hF
  have hp : (ports.map Sum.inl).map name = (ports.map Fin.val).map (2 * ·) := by
    simp [name, PPGadget.expansionName, List.map_map, Function.comp_def]
  let c := wr.certificate
  have hc : verifyRotationCertificate
      (probeBody (CSP.replaceGadgets B (fun r => (gadgets r).template) (F.relabel Fin.val))
        ((ports.map Fin.val).map (2 * ·))) c = true := wr.probe_accepted
  rw [← PPGadget.expandList_body_numeric gadgets B F hF, ← hp,
    ← probeBody_relabel, verifyRotationCertificate_relabel_of_injOn _ name
      (fun _ _ _ _ he => hi he)] at hc
  exact Witness.ofProbe (hn.map Sum.inl_injective) c hc

/-- Expand an actual semantic macro and construct its canonical ordered witness over the
original language. Original existential labels are hidden before the independent ragged
replacement blocks. This theorem asserts static finite numerical preprocessing only. -/
@[expose] def GadgetWitness.expand {n : ℕ} {R : Set (Fin n → Bool)}
    {g : PPGadget srcArity srcSem R} (w : GadgetWitness g)
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) : GadgetWitness (g.expand gadgets) := by
  let F := g.body.relabel finSumFinEquiv
  let hF := g.wellFormed.relabel finSumFinEquiv
  let ports := (List.ofFn (Sum.inl : Fin n → Fin n ⊕ Fin g.numAux)).map finSumFinEquiv
  let wf := w.relabel finSumFinEquiv (fun _ _ _ _ he => finSumFinEquiv.injective he)
  let we := wf.expandList
    ((List.nodup_ofFn.mpr Sum.inl_injective).map finSumFinEquiv.injective)
    hF gadgets witnesses B hB
  let a := (PPGadget.expandList gadgets F hF).numAux
  let e : Fin (n + g.numAux) ⊕ Fin a ≃ Fin n ⊕ Fin (g.numAux + a) :=
    (finSumFinEquiv.symm.sumCongr (Equiv.refl _)).trans
      ((Equiv.sumAssoc _ _ _).trans ((Equiv.refl _).sumCongr finSumFinEquiv))
  let f := PPGadget.substitutePort a (finSumFinEquiv.symm : Fin (n + g.numAux) → _)
  have he : ∀ x, e x = f x := by
    intro x
    cases x with
    | inl i =>
      cases hi : (finSumFinEquiv.symm i : Fin n ⊕ Fin g.numAux) <;>
        simp [e, f, PPGadget.substitutePort, hi]
    | inr i => rfl
  have hf : Function.Injective f := by
    intro x y h
    exact e.injective ((he x).trans (h.trans (he y).symm))
  let wt := we.relabel f (fun _ _ _ _ h => hf h)
  have hp : (ports.map Sum.inl).map f = List.ofFn Sum.inl := by
    simp only [ports, List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    simp [f, PPGadget.substitutePort]
  refine ⟨wt.certificate, ?_⟩
  change verify ((PPGadget.expandList gadgets F hF).body.relabel f)
    (List.ofFn Sum.inl) wt.certificate = true
  rw [← hp]
  exact wt.accepted

end Cslib.Complexity.CSP.OrderedBoundary
