/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.OneHotExpansion

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.BitString
open Cslib.Complexity.CSP.OrderedBoundary Cslib.Logic.PL.CSP.RelationMinor

namespace PlanarExpandedOneHotTest

inductive Symbol where
  | or3
  | nand
  | bit
  | closed
  deriving DecidableEq

abbrev arity : Symbol → ℕ
  | .or3 => 3
  | .nand => 2
  | .bit => 1
  | .closed => 0

def sem : Symbol → List Bool → Bool
  | .or3, [a, b, c] => a || b || c
  | .nand, [a, b] => !(a && b)
  | .bit, [a] => a
  | .closed, [] => true
  | _, _ => false

abbrev R := booleanRelation arity sem .or3

private instance : DecidablePred (· ∈ R) := fun a =>
  inferInstanceAs (Decidable (sem .or3 (List.ofFn a) = true))

def ternary := PPGadget.atom (arity := arity) (sem := sem) .or3

-- Each NAND copy has one used and one unused auxiliary, plus a real nullary component.
def nandGadget : PPGadget arity sem nand where
  numAux := 2
  body := [⟨.nand, [.inl 0, .inl 1]⟩, ⟨.bit, [.inr 0]⟩, ⟨.closed, []⟩]
  wellFormed := by decide +kernel
  correct a := by revert a; decide +kernel

def nandWitness : GadgetWitness nandGadget where
  certificate := ⟨[8, 3, 6, 1, 4, 5, 2, 9, 0, 7]⟩
  accepted := by decide +kernel

def triangle := NonSelfDual.triangleGadget ternary nandGadget
  (by decide +kernel) (by decide +kernel)

example : triangle.numAux = 6 ∧ triangle.body =
    ([⟨.or3, [.inl 0, .inl 1, .inl 2]⟩,
     ⟨.nand, [.inl 0, .inl 1]⟩, ⟨.bit, [.inr 0]⟩, ⟨.closed, []⟩,
     ⟨.nand, [.inl 1, .inl 2]⟩, ⟨.bit, [.inr 2]⟩, ⟨.closed, []⟩,
     ⟨.nand, [.inl 2, .inl 0]⟩, ⟨.bit, [.inr 4]⟩, ⟨.closed, []⟩] : CSP Symbol (Fin 3 ⊕ Fin 6)) :=
  ⟨rfl, rfl⟩

example : Nonempty (GadgetWitness triangle) :=
  ⟨NonSelfDual.triangleGadgetOrderedWitness (Witness.atom arity sem .or3) nandWitness
    (by decide +kernel) (by decide +kernel)⟩

-- Execute both full target checkers on the exact original-language ten-constraint body.
example : verify triangle.body (List.ofFn Sum.inl)
    ⟨[20, 3, 8, 5, 14, 1, 0, 9, 26, 7, 10, 11, 2, 15, 24,
      13, 16, 17, 4, 21, 28, 19, 22, 23, 18, 27, 12, 29, 6, 25]⟩ = true := by decide +kernel

example : ∀ a : Fin 3 → Bool,
    (∃ b : Fin triangle.numAux → Bool, triangle.body.eval sem (Sum.elim a b) = true) ↔
      ∃ i : Fin 3, (fun j => decide (j = i)) = a := by decide +kernel

-- A separate original language has one-in-three and a false nullary relation, with no
-- primitive pin, NAND or disequality symbol. Its hard-branch premises are executable.
abbrev hardArity (r : Bool) : ℕ := if r then 3 else 0

def hardSem : Bool → List Bool → Bool
  | true, [a, b, c] =>
      (a && !b && !c) || (!a && b && !c) || (!a && !b && c)
  | _, _ => false

private instance (r : Bool) : DecidablePred (· ∈ booleanRelation hardArity hardSem r) := fun a =>
  inferInstanceAs (Decidable (hardSem r (List.ofFn a) = true))

private theorem hard : ¬HasSchaeferPolymorphism hardArity hardSem := by
  unfold HasSchaeferPolymorphism HasPolymorphism Cslib.Logic.IsPolymorphism
  decide +kernel

private theorem noNot : ¬HasPolymorphism hardArity hardSem
    (fun a : Fin 1 → Bool => !(a 0)) := by
  unfold HasPolymorphism Cslib.Logic.IsPolymorphism
  decide +kernel

-- Apply the actual original-language existence endpoint, and check SAT/UNSAT rows of
-- the gadget it returns. The finite nonuniform witness selection is not claimed executable.
example : ∃ g : PPGadget hardArity hardSem (oneHotRelation (Fin 3)),
    Nonempty (GadgetWitness g) ∧
    (∃ b, g.body.eval hardSem (Sum.elim ![true, false, false] b) = true) ∧
    ¬(∃ b, g.body.eval hardSem (Sum.elim (fun _ => false) b) = true) := by
  obtain ⟨g, w⟩ := NonSelfDual.exists_orderedOneHotGadget hard noNot
  refine ⟨g, w, (g.correct _).mp ⟨0, by decide⟩, ?_⟩
  intro h
  obtain ⟨i, hi⟩ := (g.correct _).mpr h
  have hx := congrFun hi i
  simp at hx

end PlanarExpandedOneHotTest
