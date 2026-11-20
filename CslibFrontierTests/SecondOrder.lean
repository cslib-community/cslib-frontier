/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Logics.SecondOrder.Basic

/-! # Checked interleaving of element and relation quantifiers -/

set_option linter.privateModule false

namespace CslibFrontierTests.SecondOrder

open FirstOrder Language Cslib.Logic

private def binaryArity : Unit → ℕ := fun _ => 2

private def diagonal {L : Language} :
    (L.sum (ESO.varLanguage binaryArity)).BoundedFormula Empty 1 :=
  let r : (L.sum (ESO.varLanguage binaryArity)).Relations 2 := .inr ⟨(), rfl⟩
  r.boundedFormula₂ (.var (.inr 0)) (.var (.inr 0))

/-- Every element lies on the diagonal of some binary relation. -/
private def allElements {L : Language} : SO.Sentence L :=
  .all (SO.BoundedFormula.exRel binaryArity (.ofFirstOrder diagonal))

example {L : Language} (M : Type) [L.Structure M] : (allElements (L := L)).Realize M := by
  rw [SO.Sentence.Realize, allElements, SO.BoundedFormula.Realize]
  intro a
  rw [SO.BoundedFormula.realize_exRel]
  exact ⟨fun _ => Set.univ, trivial⟩

/-- The empty binary relation has no element on its diagonal. -/
private def allRelations {L : Language} : SO.Sentence L :=
  .allRel inferInstance binaryArity (SO.BoundedFormula.ex (.ofFirstOrder diagonal))

example {L : Language} (M : Type) [L.Structure M] : ¬(allRelations (L := L)).Realize M := by
  rw [SO.Sentence.Realize, allRelations, SO.BoundedFormula.Realize]
  intro h
  let _ := ESO.varLanguage.structure (M := M) (arity := binaryArity) fun _ => ∅
  have empty := h fun _ => ∅
  rw [SO.BoundedFormula.realize_ex] at empty
  obtain ⟨a, ha⟩ := empty
  exact ha

/-- An edge leaves a relation missing its element and enters one containing its element. -/
private def oneEdge {L : Language} (r s : L.Relations 1) : SO.TCFormula Bool L 0 :=
  let arity : Unit → ℕ := fun _ => 1
  let source : (L.sum (ESO.varLanguage (Sum.elim arity arity))).Relations 1 :=
    .inr ⟨.inl (), rfl⟩
  let target : (L.sum (ESO.varLanguage (Sum.elim arity arity))).Relations 1 :=
    .inr ⟨.inr (), rfl⟩
  .tc (k := 1) rfl inferInstance arity (fun _ => r) (fun _ => s)
    (fun _ => .var (.inl false)) (fun _ => .var (.inl true))
    (.ofFirstOrder
      ((source.boundedFormula₁ (.var (.inr 0))).not ⊓ target.boundedFormula₁ (.var (.inr 1))))

example {L : Language} [L.Structure Bool] (r s : L.Relations 1)
    (hempty : ∀ x : Fin 1 → Bool, ¬ Structure.RelMap r x) (h : Structure.RelMap s (fun _ => true)) :
    (oneEdge r s).Realize id Fin.elim0 := by
  rw [oneEdge, SO.BoundedFormula.Realize]
  refine Relation.TransGen.single ?_
  simp only [SO.BoundedFormula.Realize, BoundedFormula.realize_inf,
    Relations.boundedFormula₁, Relations.boundedFormula, BoundedFormula.Realize]
  change ¬ Structure.RelMap r _ ∧ Structure.RelMap s _
  refine ⟨hempty _, ?_⟩
  convert h using 1
  apply iff_of_eq
  congr 1
  funext i
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

-- Equal endpoints alone give no path in an empty edge relation.
example {L : Language} [L.Structure Bool] :
    ¬ (SO.BoundedFormula.tc (k := 0) rfl inferInstance (fun _ : Empty => 0)
      (fun i => i.elim) (fun i => i.elim) Fin.elim0 Fin.elim0
      (.ofFirstOrder ⊥) : SO.TCFormula Bool L 0).Realize id Fin.elim0 := by
  rw [SO.BoundedFormula.Realize]
  intro path
  cases path with
  | single edge => simp [SO.BoundedFormula.Realize] at edge
  | tail _ edge => simp [SO.BoundedFormula.Realize] at edge

end CslibFrontierTests.SecondOrder
