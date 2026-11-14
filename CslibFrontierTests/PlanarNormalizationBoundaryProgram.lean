/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Normalization.Program
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary

/-! Ordinary-import clients of the exact normalization program, including unused free ports,
arbitrary cyclic starts, wrap quotients, repeated high-degree scope labels and cap layout.
The noncomputable constructors supply proofs; the explicit maps and bodies use kernel decision.
-/

namespace CslibFrontierTests.PlanarNormalizationBoundaryProgram

noncomputable section

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.BitString
open Cslib.Logic.PL.CSP.Normalization Cslib.Complexity.CSP.OrderedBoundary

private abbrev arity (n : ℕ) : Unit → ℕ := fun _ => n
private abbrev sem : Unit → List Bool → Bool := fun _ _ => true
private def atom (n : ℕ) := PPGadget.atom (arity := arity n) (sem := sem) ()

private def mixed : Program 6 3 :=
  .rotate 5 (.cap (by decide) (.zero 3 (.rotate 2 (.done 3))))

private def capSix : Program 6 4 := .cap (by decide) (.done 4)

example : GadgetWitness (mixed.gadget (atom 6)) :=
  mixed.orderedWitness (Witness.atom (arity 6) sem ())

example : (mixed.gadget (atom 6)).numAux = 1 := rfl

-- Every choice of the cyclic edge has exactly its prescribed survivor labels.
example : ∀ i : Fin 6, (List.ofFn (zeroPort i)) =
    match i.val with
    | 0 => [0, 0, 1, 2, 3, 4]
    | 1 => [0, 1, 1, 2, 3, 4]
    | 2 => [0, 1, 2, 2, 3, 4]
    | 3 => [0, 1, 2, 3, 3, 4]
    | 4 => [0, 1, 2, 3, 4, 4]
    | _ => [0, 1, 2, 3, 4, 0] := by decide +kernel

example : List.ofFn (@capPort 2) =
    [.inl 0, .inl 1, .inr 0, .inl 1, .inl 2, .inl 3] := by decide +kernel

private def repeated : Program 10 4 :=
  .zero 0 (.zero 0 (.zero 0 (.zero 0 (.cap (by decide) (.done 4)))))

-- Four consecutive folds produce five occurrences at one free vertex before the cap.
example : GadgetWitness (repeated.gadget (atom 10)) :=
  repeated.orderedWitness (Witness.atom (arity 10) sem ())

example : (repeated.gadget (atom 10)).body =
    ([⟨(), [.inl 0, .inl 0, .inl 0, .inl 0, .inl 0,
      .inl 1, .inr 0, .inl 1, .inl 2, .inl 3]⟩] : CSP Unit (Fin 4 ⊕ Fin 1)) := by
  rfl

example : (repeated.gadget (atom 10)).numAux = 1 := rfl

private def hidden := ((atom 8).project 2).project 4

private noncomputable def hiddenWitness : GadgetWitness hidden :=
  ((Witness.atom (arity 8) sem ()).project 2).project 4

example : GadgetWitness (capSix.gadget hidden) := capSix.orderedWitness hiddenWitness

-- Fresh hidden old port2 is auxiliary0; both pre-existing auxiliaries shift by one.
example : (capSix.gadget hidden).body =
    ([⟨(), [.inl 0, .inl 1, .inr 2, .inr 0, .inl 1, .inr 1, .inl 2, .inl 3]⟩] :
      CSP Unit (Fin 4 ⊕ Fin 3)) := by
  rfl

example : (capSix.gadget hidden).numAux = 3 := rfl

private def unused : PPGadget (arity 6) sem (Set.univ : Set (Fin 6 → Bool)) where
  numAux := 0
  body := []
  wellFormed := by simp [WellFormed]
  correct _ := by simp [CSP.eval]

private def unusedWitness : GadgetWitness unused :=
  Witness.empty (List.ofFn Sum.inl) (List.nodup_ofFn.mpr Sum.inl_injective)

-- Structural probe markers make unused selected ports available to the same program.
example : GadgetWitness (mixed.gadget unused) := mixed.orderedWitness unusedWitness

example : (mixed.gadget unused).body = [] := rfl

-- A cap still allocates its hidden label when that port never occurs in a body row.
example : (mixed.gadget unused).numAux = 1 := rfl

private def disconnected : PPGadget (fun r : Bool => if r then 6 else 0)
    (fun _ _ => true) (Set.univ : Set (Fin 6 → Bool)) where
  numAux := 0
  body := [⟨false, []⟩, ⟨true, List.ofFn Sum.inl⟩]
  wellFormed := by simp [WellFormed]
  correct _ := by simp [CSP.eval, Constraint.eval]

private def disconnectedWitness : GadgetWitness disconnected where
  certificate := atomBoundaryCertificate 6
  accepted := by decide +kernel

-- A closed nullary component survives the same guarded cap; connectedness is unnecessary.
example : GadgetWitness (capSix.gadget disconnected) := capSix.orderedWitness disconnectedWitness

example : (capSix.gadget disconnected).body =
    ([⟨false, []⟩, ⟨true, [.inl 0, .inl 1, .inr 0, .inl 1, .inl 2, .inl 3]⟩] :
      CSP Bool (Fin 4 ⊕ Fin 1)) := by
  rfl

-- Arbitrary starts are genuinely beyond a single shift.
example : List.ofFn ((finCycle (4 : Fin 6)).symm) = [2, 3, 4, 5, 0, 1] := by decide +kernel

end

end CslibFrontierTests.PlanarNormalizationBoundaryProgram
