/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Normalization
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.OneHotExpansion
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.CrossoverOriginal
public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Replacement

/-! Restricted-module clients of the numerical witness APIs. All imports are ordinary;
the client inspects actual cap and expansion bodies, executes the exposed expansion table,
and derives free-assignment SAT/UNSAT rows from both complete original-language endpoints.
-/

public section

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.BitString
open Cslib.Complexity.CSP.OrderedBoundary

namespace CslibFrontierTests.PlanarExpandedModule

private abbrev sixArity : Unit → ℕ := fun _ => 6
private def sixSem : Unit → List Bool → Bool := fun _ _ => true
private def six := PPGadget.atom (arity := sixArity) (sem := sixSem) ()
private def cap : Normalization.Program 6 4 := .cap (by decide) (.done 4)

example : (cap.gadget six).numAux = 1 ∧ (cap.gadget six).body =
    ([⟨(), [.inl 0, .inl 1, .inr 0, .inl 1, .inl 2, .inl 3]⟩] :
      CSP Unit (Fin 4 ⊕ Fin 1)) := ⟨rfl, rfl⟩

example : ∃ c, verify (cap.gadget six).body (List.ofFn Sum.inl) c = true := by
  let w := cap.orderedWitness (Witness.atom sixArity sixSem ())
  exact ⟨w.certificate, w.accepted⟩

private abbrev unaryArity : Unit → ℕ := fun _ => 1
private def unarySem : Unit → List Bool → Bool := fun _ xs => xs.headD false
private def unary := PPGadget.atom (arity := unaryArity) (sem := unarySem) ()

private def unaryWitness : GadgetWitness unary where
  certificate := ⟨[2, 1, 0, 3]⟩
  accepted := by decide +kernel

private def replacements : ∀ r, PPGadget unaryArity unarySem
    (booleanRelation unaryArity unarySem r) := fun _ => unary

private def replacementWitnesses : ∀ r, GadgetWitness (replacements r) :=
  fun _ => unaryWitness

private def expanded := unary.expand replacements
private def expandedWitness : GadgetWitness expanded :=
  unaryWitness.expand replacements replacementWitnesses 0 (fun _ => le_rfl)

example : expanded.numAux = 0 ∧ expanded.body =
    ([⟨(), [.inl 0]⟩] : CSP Unit (Fin 1 ⊕ Fin 0)) := ⟨rfl, rfl⟩

example : expandedWitness.certificate.successor = [2, 1, 0, 3] := by decide +kernel

example : verify expanded.body (List.ofFn Sum.inl) expandedWitness.certificate = true := by
  decide +kernel

-- The public pointwise equation retains a fixed assignment and total lookup fallback.
example : (instantiate 5 2 [9] unary.template).eval unarySem (fun v => decide (v = 18)) =
    true := by
  rw [eval_instantiate]
  decide +kernel

example : (instantiate 5 2 [] unary.template).eval unarySem (fun v => decide (v = 18)) =
    false := by
  rw [eval_instantiate]
  decide +kernel

/-- The original-language one-hot endpoint supplies actual accepting and rejecting body rows. -/
theorem oneHot_rows {Rel : Type} {ar : Rel → ℕ} {s : Rel → List Bool → Bool}
    (h : ¬HasSchaeferPolymorphism ar s)
    (hn : ¬HasPolymorphism ar s (fun a : Fin 1 → Bool => !(a 0))) :
    ∃ g : PPGadget ar s (oneHotRelation (Fin 3)), Nonempty (GadgetWitness g) ∧
      (∃ b, g.body.eval s (Sum.elim ![true, false, false] b) = true) ∧
      ¬(∃ b, g.body.eval s (Sum.elim (fun _ => false) b) = true) := by
  obtain ⟨g, w⟩ := NonSelfDual.exists_orderedOneHotGadget h hn
  refine ⟨g, w, (g.correct _).mp ⟨0, by decide⟩, ?_⟩
  intro hh
  obtain ⟨i, hi⟩ := (g.correct _).mpr hh
  have hx := congrFun hi i
  simp at hx

/-- The original-language crossover endpoint supplies actual accepting and rejecting body rows. -/
theorem cross_rows {Rel : Type} {ar : Rel → ℕ} {s : Rel → List Bool → Bool}
    (h : ¬HasSchaeferPolymorphism ar s)
    (hn : HasPolymorphism ar s (fun a : Fin 1 → Bool => !(a 0)))
    (r : Rel) (hne : (booleanRelation ar s r).Nonempty)
    (hbad : ¬IsEvenDeltaMatroid (cyclicDifferenceRelation (booleanRelation ar s r))) :
    ∃ g : PPGadget ar s cross, Nonempty (GadgetWitness g) ∧
      (∃ b, g.body.eval s (Sum.elim ![false, true, false, true] b) = true) ∧
      ¬(∃ b, g.body.eval s (Sum.elim ![false, false, false, true] b) = true) := by
  obtain ⟨g, w⟩ := Crossover.exists_orderedCrossGadget h hn r hne hbad
  refine ⟨g, w, (g.correct _).mp (by decide +kernel), ?_⟩
  rw [← g.correct]
  decide +kernel

end CslibFrontierTests.PlanarExpandedModule
