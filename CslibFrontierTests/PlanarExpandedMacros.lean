/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.CrossoverExpansion

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity.CSP.OrderedBoundary
open Cslib.BitString Cslib.Logic.PL.CSP.RelationMinor

-- Execute both original checkers on every explicit source macro table in the kernel.
example : verify Crossover.figureOneABody (List.ofFn Sum.inl)
    Crossover.figureOneABoundaryCertificate = true := by decide +kernel

example : verify Crossover.figureOneBBody (List.ofFn Sum.inl)
    Crossover.figureOneBBoundaryCertificate = true := by decide +kernel

example : verify NonSelfDual.triangleBody (List.ofFn Sum.inl)
    NonSelfDual.triangleBoundaryCertificate = true := by decide +kernel

-- The same rotation works for every interpretation of R; it does not inspect truth tables.
example (R : Set (Fin 4 → Bool)) [DecidablePred (· ∈ R)] :
    GadgetWitness (Crossover.figureOneA R) := Crossover.figureOneABoundary

example (R : Set (Fin 4 → Bool)) [DecidablePred (· ∈ R)]
    (h : Cslib.BitString.IsStandardizedInconsistent R) :
    GadgetWitness (Crossover.figureOneAStandardized R h) :=
  Crossover.figureOneAStandardizedBoundary R h

-- Keeping the original table while reflecting the boundary fails the literal order check.
example : verify Crossover.figureOneABody
    ([Sum.inl 0, Sum.inl 3, Sum.inl 2, Sum.inl 1] : List (Fin 4 ⊕ Fin 3))
    Crossover.figureOneABoundaryCertificate = false := by decide +kernel

example : verify Crossover.figureOneBBody
    ([Sum.inl 0, Sum.inl 3, Sum.inl 2, Sum.inl 1] : List (Fin 4 ⊕ Fin 1))
    Crossover.figureOneBBoundaryCertificate = false := by decide +kernel

-- Full source semantic tables, including the optional standardized pairs and all free rows.
example : ∀ p q r : Bool, ∀ x : Fin 4 → Bool,
    x ∈ Crossover.figureOneARelation (Cslib.BitString.standardizedRelation p q r) ↔
      x ∈ (if p || q then Cslib.BitString.nearCross else Cslib.BitString.cross) := by
  intro p q r
  cases p <;> cases q <;> cases r <;>
    simp only [Bool.or, Bool.false_eq_true, reduceIte] <;> decide +kernel

example : ∀ x : Fin 4 → Bool,
    x ∈ Cslib.BitString.cross ↔ ∃ b,
      Crossover.figureOneBBody.eval Crossover.nearSem (Sum.elim x b) = true := by
  decide +kernel

namespace PlanarExpandedCrossoverTest

abbrev arity := Crossover.arity
abbrev sem := Crossover.sem nearCross

instance (r : Crossover.Symbol) : DecidablePred (· ∈ booleanRelation arity sem r) :=
  fun a => inferInstanceAs (Decidable (sem r (List.ofFn a) = true))

def relation : PPGadget arity sem nearCross :=
  (PPGadget.atom (arity := arity) (sem := sem) .relation).retarget
    fun x => (Crossover.sem_relation nearCross x).symm

def unequal : PPGadget arity sem disequality :=
  (PPGadget.atom (arity := arity) (sem := sem) .disequality).retarget
    fun x => (Crossover.sem_disequality nearCross x).symm

private theorem near_eq : nearCross = standardizedRelation true false false := by
  ext x
  exact (by decide +kernel : ∀ x : Fin 4 → Bool,
    x ∈ nearCross ↔ x ∈ standardizedRelation true false false) x

private theorem near_target : Crossover.figureOneARelation nearCross = nearCross := by
  simpa only [← near_eq, Bool.true_or, reduceIte] using
    Crossover.figureOneARelation_standardized true false false

def first := Crossover.figureOneAExpanded relation unequal

def near : PPGadget arity sem nearCross :=
  first.retarget fun _ => by rw [near_target]

def expanded := Crossover.figureOneBExpanded near

example : first.numAux = 3 ∧ expanded.numAux = 7 ∧ expanded.body.length = 8 := by
  decide +kernel

example : Nonempty (GadgetWitness near) :=
  ⟨Crossover.figureOneAExpandedWitness (Witness.atom arity sem .relation)
    (Witness.atom arity sem .disequality)⟩

example : Nonempty (GadgetWitness expanded) :=
  ⟨Crossover.figureOneBExpandedWitness
    (Crossover.figureOneAExpandedWitness (Witness.atom arity sem .relation)
      (Witness.atom arity sem .disequality))⟩

-- Offline preprocessing splices the original Figure1a table into the original Figure1b
-- table. The complete explicit table is executed by both original target checkers here.
def expandedCertificate : Cslib.Complexity.Graph.RotationCertificate :=
  ⟨[16, 3, 8, 5, 46, 7, 54, 1, 26, 11, 18, 13, 6, 15,
    20, 9, 0, 19, 10, 17, 14, 23, 52, 21, 40, 27, 32, 29,
    22, 31, 50, 25, 2, 35, 42, 37, 30, 39, 44, 33, 24, 43,
    34, 41, 38, 47, 48, 45, 4, 51, 36, 53, 28, 55, 12, 49]⟩

example : verify expanded.body (List.ofFn Sum.inl) expandedCertificate = true := by
  decide +kernel

example : verify expanded.body
    ([Sum.inl 0, Sum.inl 3, Sum.inl 2, Sum.inl 1] : List (Fin 4 ⊕ Fin 7))
    expandedCertificate = false := by decide +kernel

example : ∃ b : Fin expanded.numAux → Bool,
    expanded.body.eval sem (Sum.elim ![true, false, true, false] b) = true := by decide +kernel

example : ¬∃ b : Fin expanded.numAux → Bool,
    expanded.body.eval sem (Sum.elim ![true, false, false, false] b) = true := by decide +kernel

end PlanarExpandedCrossoverTest
