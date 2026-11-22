/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.BoundaryFusion
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Crossover

/-! Ordinary clients of raw head-wire fusion, including an actual inserted CROSS with an
auxiliary variable. This is identification of neighboring wires, not a transposition test. -/

public section

namespace CslibFrontierTests.CSPBoundaryFusion

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP
open Cslib.Logic.PL.CSP.Crossover OrderedBoundary CrossInsertion

/-- Repeated sparse body names, a separate boundary leaf, and a retained closed nullary row. -/
def sparse : State Unit :=
  ⟨[⟨(), [2 ^ 250]⟩, ⟨(), [2 ^ 250]⟩, ⟨(), []⟩], [2 ^ 250, 17],
    ⟨[2, 1, 6, 3, 4, 7, 0, 5]⟩⟩

example : sparse.Accepted := by decide +kernel

example : (fuseHead sparse).Accepted := accepted_fuseHead sparse (by decide +kernel)

example : (fuseHead sparse).rotation.successor = [2, 1, 4, 3, 0, 5] ∧
    (fuseHead sparse).ports = [2 ^ 250] ∧ (fuseHead sparse).body = sparse.body := by
  decide +kernel

private def figureWitness : GadgetWitness figureOneB :=
  ⟨figureOneBBoundaryCertificate, by decide +kernel⟩

private def inserted : State Unit := CrossInsertion.insert figureOneB figureWitness
  ⟨[], [], ⟨[]⟩⟩

example : (fuseHead inserted).Accepted :=
  accepted_fuseHead inserted (accepted_insert figureOneB figureWitness _ (by decide +kernel))

example : (fuseHead inserted).ports = [1, 5, 7] ∧
    (fuseHead inserted).rotation.successor =
      [20, 3, 0, 5, 12, 7, 10, 1, 18, 11, 16, 13, 4, 15, 2, 9, 6, 19, 8, 21, 14, 17] := by
  decide +kernel

example : fuseHead (⟨[], [], ⟨[2 ^ 300]⟩⟩ : State Unit) = ⟨[], [], ⟨[2 ^ 300]⟩⟩ := rfl

example : fuseHead (⟨[], [4], ⟨[]⟩⟩ : State Unit) = ⟨[], [4], ⟨[]⟩⟩ := rfl

example : (fuseHead (⟨[], [3, 3], ⟨[2 ^ 300]⟩⟩ : State Unit)).ports = [3] := by
  decide +kernel

example (σ : ℕ → Bool) :
    (fuseHead sparse).body.eval (fun _ xs => decide (xs ≠ [])) σ = true ↔
      ∃ τ : ℕ → Bool, sparse.body.eval (fun _ xs => decide (xs ≠ [])) τ = true ∧
        τ (2 ^ 250) = τ 17 ∧ ∀ z, z ≠ 17 → τ z = σ z :=
  eval_fuseHead_iff _ _ _ _ _ _ (by decide +kernel) σ

example (σ : ℕ → Bool) :
    (fuseHead sparse).body.eval (fun _ xs => decide (xs ≠ [])) σ = false := by
  simp [fuseHead, sparse, CSP.eval, CSP.relabel, Constraint.relabel, Constraint.eval]

end CslibFrontierTests.CSPBoundaryFusion
