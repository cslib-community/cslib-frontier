/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.CrossoverOriginal
import CslibFrontierTests.PlanarExpandedMacros

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.BitString
open Cslib.Complexity.CSP.OrderedBoundary Cslib.Logic.PL.CSP.RelationMinor

namespace PlanarExpandedCrossoverTest

private theorem hard : ¬HasSchaeferPolymorphism arity sem := by
  intro h
  rcases h with h | h | h | h | h | h
  · have hh := h .disequality (fun _ => ![false, true]) (by intro j; rfl)
    exact Bool.false_ne_true hh
  · have hh := h .disequality (fun _ => ![false, true]) (by intro j; rfl)
    exact Bool.false_ne_true hh
  · have hh := h .disequality ![![false, true], ![true, false]] (by decide +kernel)
    exact Bool.false_ne_true hh
  · have hh := h .disequality ![![false, true], ![true, false]] (by decide +kernel)
    exact Bool.false_ne_true hh
  · have hh := h .relation
      ![![false, true, false, true], ![false, false, false, false], ![true, true, true, false]]
      (by decide +kernel)
    exact Bool.false_ne_true hh
  · have hh := h .relation
      ![![false, true, false, true], ![false, false, false, false], ![true, true, true, false]]
      (by decide +kernel)
    exact Bool.false_ne_true hh

private theorem common_not : HasPolymorphism arity sem
    (fun a : Fin 1 → Bool => !(a 0)) := by
  unfold HasPolymorphism Cslib.Logic.IsPolymorphism
  intro r
  cases r <;> decide +kernel

private theorem bad_near : ¬IsEvenDeltaMatroid (cyclicDifferenceRelation nearCross) := by
  intro h
  have hx : (fun _ => false) ∈ cyclicDifferenceRelation nearCross :=
    ⟨fun _ => false, by decide +kernel, by decide +kernel⟩
  have hy : (fun _ => true) ∈ cyclicDifferenceRelation nearCross :=
    ⟨![false, true, false, true], by decide +kernel, by decide +kernel⟩
  obtain ⟨j, _, hj⟩ := h.isDeltaMatroid.exchange hx hy (i := 0) (by decide +kernel)
  have hno : ∀ j : Fin 4, flipOn {0, j} (fun _ => false) ∉ cyclicDifferenceRelation nearCross := by
    change ∀ j : Fin 4, ¬∃ x : Fin 4 → Bool,
      x ∈ nearCross ∧ cyclicDifference x = flipOn {0, j} (fun _ => false)
    decide +kernel
  exact hno j hj

-- The full endpoint receives only the original alphabet, actual common operations, and
-- the actual bad original relation. No normalized gadget or target witness is supplied.
example : ∃ g : PPGadget arity sem cross, Nonempty (GadgetWitness g) ∧
    (∃ b, g.body.eval sem (Sum.elim ![false, true, false, true] b) = true) ∧
    ¬(∃ b, g.body.eval sem (Sum.elim ![false, false, false, true] b) = true) := by
  have hr : booleanRelation arity sem .relation = nearCross :=
    Set.ext (Crossover.sem_relation nearCross)
  obtain ⟨g, w⟩ := Crossover.exists_orderedCrossGadget hard common_not .relation
    (by
      rw [hr]
      change nearCross.Nonempty
      exact ⟨fun _ => false, Or.inl ⟨rfl, rfl⟩⟩)
    (by
      rw [hr]
      change ¬IsEvenDeltaMatroid (cyclicDifferenceRelation nearCross)
      exact bad_near)
  refine ⟨g, w, (g.correct _).mp (by decide +kernel), ?_⟩
  rw [← g.correct]
  decide +kernel

end PlanarExpandedCrossoverTest
