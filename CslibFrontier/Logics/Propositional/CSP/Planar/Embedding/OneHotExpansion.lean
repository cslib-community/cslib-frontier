/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Expansion
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Crossover
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Construction
public import CslibFrontier.Logics.Propositional.CSP.Planar.OneInThree.Gadget
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.SuccPred

/-!
# Checked original-language one-in-three expansion

The actual accepted triangle macro is expanded using an actual ternary gadget and three
independently freshened occurrences of an actual NAND gadget. Auxiliary alpha-renaming
identifies the result with exactly the existing left-associated `triangleGadget` body:
the ternary constraints, then NAND bodies on `(0,1)`, `(1,2)`, `(2,0)`.

Failure of the six Schaefer operations and common complement internally supplies the
construction trees, their enabling pins and disequality, and their ordered witnesses.
The ordered triangle is an original reconstruction of [DvorakKupec2015], Lemma 4,
printed pp. 438–439; the source omits its proof. The expansion remains static finite
numerical mathematics, without a native reduction or source-model claim.

## Main definitions

* `Cslib.Logic.PL.CSP.NonSelfDual.triangleGadgetOrderedWitness`:
  the exact original triangle boundary.

## Main results

* `Cslib.Logic.PL.CSP.NonSelfDual.exists_orderedOneHotGadget`:
  the original-language hard-branch endpoint.
-/

public section

namespace Cslib.Logic.PL.CSP.NonSelfDual

open Cslib.BitString RelationMinor Cslib.Complexity.CSP.OrderedBoundary

variable {Rel : Type} {ar : Rel → ℕ} {s : Rel → List Bool → Bool}

private def triangleReplacements {R : Set (Fin 3 → Bool)} [DecidablePred (· ∈ R)]
    (r : PPGadget ar s R) (d : PPGadget ar s nand) :
    ∀ t, PPGadget ar s (booleanRelation triangleArity (triangleSem R) t)
  | .relation => r.retarget (triangleSem_relation R)
  | .nand => d.retarget (triangleSem_nand R)

private def triangleReplacementWitnesses {R : Set (Fin 3 → Bool)}
    [DecidablePred (· ∈ R)] (r : PPGadget ar s R) (d : PPGadget ar s nand)
    (wr : GadgetWitness r) (wd : GadgetWitness d) :
    ∀ t, GadgetWitness (triangleReplacements r d t)
  | .relation => wr
  | .nand => wd

private def triangleExpanded {R : Set (Fin 3 → Bool)} [DecidablePred (· ∈ R)]
    (r : PPGadget ar s R) (d : PPGadget ar s nand)
    (hz : (0 : Fin 3 → Bool) ∉ R) (hu : ∀ i, Pi.single i true ∈ R) :
    PPGadget ar s (oneHotRelation (Fin 3)) :=
  (triangle R hz hu).expand (triangleReplacements r d)

private theorem triangleExpanded_numAux {R : Set (Fin 3 → Bool)} [DecidablePred (· ∈ R)]
    (r : PPGadget ar s R) (d : PPGadget ar s nand)
    (hz : (0 : Fin 3 → Bool) ∉ R) (hu : ∀ i, Pi.single i true ∈ R) :
    (triangleExpanded r d hz hu).numAux = (triangleGadget r d hz hu).numAux := by
  simp [triangleExpanded, PPGadget.numAux_expand, triangle, triangleBody,
    triangleReplacements, triangleGadget, PPGadget.conj, PPGadget.relabelFree,
    PPGadget.retarget, Nat.add_assoc]

private theorem triangleExpanded_body {R : Set (Fin 3 → Bool)} [DecidablePred (· ∈ R)]
    (r : PPGadget ar s R) (d : PPGadget ar s nand)
    (hz : (0 : Fin 3 → Bool) ∉ R) (hu : ∀ i, Pi.single i true ∈ R) :
    (triangleGadget r d hz hu).body = (triangleExpanded r d hz hu).body.relabel
      (Sum.map id (finCongr (triangleExpanded_numAux r d hz hu))) := by
  let F : CSP TriangleSymbol (Fin (3 + 0)) :=
    [⟨.relation, [0, 1, 2]⟩, ⟨.nand, [0, 1]⟩, ⟨.nand, [1, 2]⟩, ⟨.nand, [2, 0]⟩]
  let hF : WellFormed triangleArity F := (triangle R hz hu).wellFormed.relabel finSumFinEquiv
  let G := PPGadget.expandList (triangleReplacements r d) F hF
  let e : Fin (0 + (r.numAux + (d.numAux + (d.numAux + (d.numAux + 0))))) ≃
      Fin (r.numAux + d.numAux + d.numAux + d.numAux) :=
    finCongr (n := 0 + (r.numAux + (d.numAux + (d.numAux + (d.numAux + 0)))))
      (m := r.numAux + d.numAux + d.numAux + d.numAux)
      (triangleExpanded_numAux r d hz hu)
  change (triangleGadget r d hz hu).body =
    (G.substitute (finSumFinEquiv.symm : Fin (3 + 0) → Fin 3 ⊕ Fin 0)).body.relabel
      (Sum.map id e)
  simp only [G, F, PPGadget.substitute, CSP.relabel]
  simp only [PPGadget.expandList, triangleReplacements, triangleGadget, PPGadget.retarget,
    PPGadget.conj, PPGadget.relabelFree, CSP.relabel,
    List.map_append, List.map_map, List.map_nil, List.append_nil, List.append_assoc]
  dsimp only [triangleArity]
  simp only [List.map_map]
  repeat' apply congrArg₂ (· ++ ·)
  all_goals
    apply List.map_congr_left
    intro c _
    apply Constraint.ext
    · rfl
    dsimp only [Constraint.relabel, Function.comp_def]
    simp only [List.map_map]
    apply List.map_congr_left
    intro v _
    cases v with
    | inl i => fin_cases i <;> simp [e, PPGadget.substitutePort, finSumFinEquiv, Fin.addCases]
    | inr i =>
      apply congrArg Sum.inr
      apply Fin.ext
      dsimp only [e, finCongr, Equiv.coe_fn_mk, Fin.cast,
        Fin.castAdd, Fin.castLE, Fin.natAdd, Fin.addNat, id]
      omega

/-- The exact pre-existing original-language triangle receives its checked ordered witness.
No ternary, NAND or boundary provider beyond these actual two input gadgets is used; in
particular, the three occurrences of `d` have the original independent auxiliary blocks. -/
def triangleGadgetOrderedWitness {R : Set (Fin 3 → Bool)}
    [DecidablePred (· ∈ R)] {r : PPGadget ar s R} {d : PPGadget ar s nand}
    (wr : GadgetWitness r) (wd : GadgetWitness d)
    (hz : (0 : Fin 3 → Bool) ∉ R) (hu : ∀ i, Pi.single i true ∈ R) :
    GadgetWitness (triangleGadget r d hz hu) := by
  let w := GadgetWitness.expand (g := triangle R hz hu) triangleBoundary
    (triangleReplacements r d) (triangleReplacementWitnesses r d wr wd)
    (r.numAux + d.numAux) (fun t => by
      cases t <;> simp only [triangleReplacements, PPGadget.retarget] <;> omega)
  exact w.relabelAux (finCongr (triangleExpanded_numAux r d hz hu))
    (triangleExpanded_body r d hz hu)

/-- Failure of the six Schaefer operations and of common complement supplies an actual
original-language one-in-three gadget and its full checked ordered witness. Enabling trees
and the exact triangle are derived internally; there is no pin, NAND or ternary oracle. -/
theorem exists_orderedOneHotGadget (h : ¬HasSchaeferPolymorphism ar s)
    (hn : ¬HasPolymorphism ar s (fun a : Fin 1 → Bool => !(a 0))) :
    ∃ g : PPGadget ar s (oneHotRelation (Fin 3)), Nonempty (GadgetWitness g) := by
  classical
  obtain ⟨_, _, ⟨d⟩, R, ⟨r⟩, hz, hu⟩ := witnesses h hn
  exact ⟨triangleGadget r.gadget d.gadget hz hu,
    ⟨triangleGadgetOrderedWitness r.orderedWitness d.orderedWitness hz hu⟩⟩

end Cslib.Logic.PL.CSP.NonSelfDual
