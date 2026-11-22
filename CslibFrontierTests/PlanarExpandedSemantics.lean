/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Crossover
import CslibFrontier.Logics.Propositional.CSP.Planar.OneInThree
import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Composition

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.BitString
open Cslib.Logic.PL.CSP.RelationMinor

namespace PlanarExpandedSemanticsTest

-- Ordinary-import clients retarget atoms using semantic facts, with no list-pattern or
-- finite-vector reconstruction. The original constraint bodies and free labels stay exact.
def crossoverAtom (R : Set (Fin 4 → Bool)) [DecidablePred (· ∈ R)] :
    PPGadget Crossover.arity (Crossover.sem R) R :=
  (PPGadget.atom (arity := Crossover.arity) (sem := Crossover.sem R) .relation).retarget
    fun x => (Crossover.sem_relation R x).symm

def triangleAtom (R : Set (Fin 3 → Bool)) [DecidablePred (· ∈ R)] :
    PPGadget NonSelfDual.triangleArity (NonSelfDual.triangleSem R) R :=
  (PPGadget.atom (arity := NonSelfDual.triangleArity)
    (sem := NonSelfDual.triangleSem R) .relation).retarget
      fun x => (NonSelfDual.triangleSem_relation R x).symm

def nandAtom (R : Set (Fin 3 → Bool)) [DecidablePred (· ∈ R)] :
    PPGadget NonSelfDual.triangleArity (NonSelfDual.triangleSem R) nand :=
  (PPGadget.atom (arity := NonSelfDual.triangleArity)
    (sem := NonSelfDual.triangleSem R) .nand).retarget
      fun x => (NonSelfDual.triangleSem_nand R x).symm

def nearAtom : PPGadget (fun _ : Unit => 4) Crossover.nearSem nearCross :=
  (PPGadget.atom ()).retarget fun x => (Crossover.nearSem_relation x).symm

example (R : Set (Fin 4 → Bool)) [DecidablePred (· ∈ R)] :
    (crossoverAtom R).numAux = 0 ∧ (crossoverAtom R).body =
      [⟨.relation, [.inl 0, .inl 1, .inl 2, .inl 3]⟩] := ⟨rfl, rfl⟩

example (R : Set (Fin 3 → Bool)) [DecidablePred (· ∈ R)] :
    (triangleAtom R).numAux = 0 ∧ (triangleAtom R).body =
      [⟨.relation, [.inl 0, .inl 1, .inl 2]⟩] := ⟨rfl, rfl⟩

example : ∀ p q r : Bool, ∀ x : Fin 4 → Bool,
    Crossover.sem (standardizedRelation p q r) .relation (List.ofFn x) = true ↔
      x ∈ standardizedRelation p q r := by decide +kernel

example : ∀ x : Fin 4 → Bool, Crossover.nearSem () (List.ofFn x) = true ↔
    x ∈ nearCross := by decide +kernel

example : ∀ x : Fin 2 → Bool,
    NonSelfDual.triangleSem (Set.univ : Set (Fin 3 → Bool)) .nand (List.ofFn x) = true ↔
      x ∈ nand := by decide +kernel

example : Crossover.sem cross .disequality [false, true] = true ∧
    Crossover.sem cross .disequality [false, false] = false ∧
    Crossover.sem cross .disequality [] = false := by decide +kernel

end PlanarExpandedSemanticsTest
