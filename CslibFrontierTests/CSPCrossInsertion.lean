/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.PolyTime.CSP.CrossInsertion
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-!
Ordinary-import clients for one disjoint CROSS insertion. The concrete alphabet has a CROSS
atom, a unary tautology, a true nullary and a false nullary. It tests the generic operation,
without asserting the original-language hardness premises for this tractable test alphabet.
The large old name is repeated in the body; a closed component and malformed raw ports remain.
-/

public section

namespace CslibFrontierTests.CSPCrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Crossover
open Cslib.Complexity Cslib.Complexity.CSP OrderedBoundary CrossInsertion
open Cslib.BitString Turing.MultiTapeTM

private def arity (r : Fin 4) : ℕ := if r = 0 then 4 else if r = 1 then 1 else 0

private def sem (r : Fin 4) (xs : List Bool) : Bool :=
  if r = 0 then decide (xs.getD 0 false = xs.getD 2 false ∧
    xs.getD 1 false = xs.getD 3 false) else decide (r ≠ 3)

private def template : PPGadget arity sem cross :=
  (PPGadget.atom (arity := arity) (sem := sem) 0).retarget fun (a : Fin 4 → Bool) => by
    change (a 0 = a 2 ∧ a 1 = a 3) ↔ sem 0 (List.ofFn a) = true
    simp [sem, List.ofFn_succ]

private def templateWitness : GadgetWitness template := Witness.atom arity sem 0

/-- A repeated sparse name, a closed true nullary row, and one boundary marker. -/
def sparse : State (Fin 4) where
  body := [⟨1, [2 ^ 250]⟩, ⟨1, [2 ^ 250]⟩, ⟨2, []⟩]
  ports := [2 ^ 250]
  rotation := ⟨[2, 1, 4, 3, 0, 5]⟩

private def closed : State (Fin 4) where
  body := sparse.body
  ports := []
  rotation := ⟨[2, 1, 0, 3]⟩

private def empty : State (Fin 4) := ⟨[], [], ⟨[]⟩⟩

private def closedFalse : State (Fin 4) := ⟨[⟨3, []⟩], [], ⟨[]⟩⟩

example : sparse.Accepted ∧ closed.Accepted ∧ empty.Accepted ∧ closedFalse.Accepted := by
  decide +kernel

example : (insert template templateWitness sparse).Accepted :=
  accepted_insert template templateWitness sparse (by decide +kernel)

example : (insert template templateWitness closed).Accepted ∧
    (insert template templateWitness empty).Accepted ∧
    (insert template templateWitness closedFalse).Accepted :=
  ⟨accepted_insert template templateWitness closed (by decide +kernel),
    accepted_insert template templateWitness empty (by decide +kernel),
    accepted_insert template templateWitness closedFalse (by decide +kernel)⟩

example : (insert template templateWitness sparse).body =
    [⟨1, [2 * 2 ^ 250]⟩, ⟨1, [2 * 2 ^ 250]⟩, ⟨2, []⟩, ⟨0, [1, 3, 5, 7]⟩] ∧
    (insert template templateWitness sparse).ports = [2 * 2 ^ 250, 1, 3, 5, 7] := by
  decide +kernel

example : (insert template templateWitness empty).rotation.successor =
    [14, 3, 12, 5, 10, 7, 8, 1, 6, 11, 4, 13, 2, 15, 0, 9] := by
  decide +kernel

example : OrderedBoundary.verify (insert template templateWitness empty).body
    [7, 5, 3, 1] (insert template templateWitness empty).rotation = false := by
  decide +kernel

example : (insert template templateWitness sparse).rotation.successor =
    [2, 1, 20, 3, 18, 7, 16, 9, 14, 11, 12, 5, 10, 15, 8, 17, 6, 19, 4, 21, 0, 13] ∧
    (insert template templateWitness closed).rotation.successor =
      [2, 1, 0, 3, 18, 7, 16, 9, 14, 11, 12, 5, 10, 15, 8, 17, 6, 19, 4, 13] := by
  decide +kernel

example (σ : ℕ → Bool) (a : Fin 4 → Bool) :
    sparse.body.eval sem σ = true ∧ a ∈ cross ↔
      ∃ τ : ℕ → Bool, (insert template templateWitness sparse).body.eval sem τ = true ∧
        (∀ x, τ (2 * x) = σ x) ∧ (∀ i : Fin 4, τ (2 * i.val + 1) = a i) :=
  eval_insert_iff template templateWitness sparse σ a

example : ∃ τ : ℕ → Bool, (insert template templateWitness sparse).body.eval sem τ = true ∧
    (∀ x, τ (2 * x) = false) ∧ (∀ i : Fin 4, τ (2 * i.val + 1) = false) :=
  (eval_insert_iff template templateWitness sparse (fun _ => false) (fun _ => false)).mp
    ⟨by decide +kernel, by decide +kernel⟩

example : ¬∃ τ : ℕ → Bool, (insert template templateWitness sparse).body.eval sem τ = true ∧
    (∀ x, τ (2 * x) = false) ∧
      (∀ i : Fin 4, τ (2 * i.val + 1) = decide (i = 2)) := by
  intro h
  have ha := (eval_insert_iff template templateWitness sparse
    (fun _ => false) (fun i => decide (i = 2))).mpr h
  exact (by decide +kernel : (fun i : Fin 4 => decide (i = 2)) ∉ cross) ha.2

example (τ : ℕ → Bool) : (insert template templateWitness closedFalse).body.eval sem τ = false := by
  simp [CrossInsertion.insert, closedFalse, CSP.relabel, Constraint.relabel,
    CSP.eval, Constraint.eval, sem]

private def malformed : State (Fin 4) :=
  { sparse with ports := [2 ^ 250, 2 ^ 250], rotation := ⟨[2 ^ 300]⟩ }

example : (insert template templateWitness malformed).ports =
    [2 * 2 ^ 250, 2 * 2 ^ 250, 1, 3, 5, 7] ∧
    ¬(insert template templateWitness malformed).ports.Nodup := by
  decide +kernel

example : (insert template templateWitness malformed).rotation.successor.length = 24 := by
  decide +kernel

example : (encNat (2 * 2 ^ 250)).length = (encNat (2 ^ 250)).length + 1 :=
  length_evenName _ (by decide +kernel)

example (I : State (Fin 4)) :
    encState (encFinEnum (Fin 4)) I =
      encPair (encCSP (encFinEnum (Fin 4)) encNat)
        (encPair (encList encNat) Graph.encRotationCertificate) (I.body, I.ports, I.rotation) := rfl

example : ComputableInPolyTime (insert template templateWitness)
    (encState (encFinEnum (Fin 4))) (encState (encFinEnum (Fin 4))) :=
  computableInPolyTime_insert template templateWitness (encFinEnum (Fin 4))

end CslibFrontierTests.CSPCrossInsertion
