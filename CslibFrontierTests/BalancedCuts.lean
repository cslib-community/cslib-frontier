/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import CslibFrontier.Computability.Circuit.Arithmetic.BalancedCuts
public import CslibFrontier.Computability.Circuit.Boolean.DeterministicDecomposableArithmetic
public import Mathlib.Data.Fintype.Pi

/-! A concrete `module` client for the cut lemma (`Circuit.exists_balanced_cuts`): the arithmetic
circuit of a d-D for the exclusive disjunction, with each input its own variable, is a sum of at
most `2 · 11 + 1` products across cuts of one variable under every specialization. -/

public section

namespace CslibFrontierTests.BalancedCuts

open Cslib.Circuits MvPolynomial

/-- `(x 0 ∧ ¬x 1) ∨ (¬x 0 ∧ x 1)` as a d-D. -/
def xorCircuit : Circuit Boolean.signature 2 1 where
  program := (Program.empty : Program Boolean.signature 2 0)
    |>.gate ⟨Boolean.Op.not, ![Wire.input 0]⟩
    |>.gate ⟨Boolean.Op.not, ![Wire.input 1]⟩
    |>.gate ⟨Boolean.Op.and, ![Wire.input 0, Wire.gate 1]⟩
    |>.gate ⟨Boolean.Op.and, ![Wire.gate 0, Wire.input 1]⟩
    |>.gate ⟨Boolean.Op.or, ![Wire.gate 2, Wire.gate 3]⟩
  outputs := fun _ => Wire.gate 4

theorem xorCircuit_isDD : xorCircuit.IsDeterministicDecomposable := by
  decide

/-- With input `i` carrying the variable `i`, cuts of exactly one variable (`a = b = 1`). -/
example : ∃ (L : ℕ) (cut : Fin L → Finset (Fin 2)), L ≤ 2 * (xorCircuit.arithmetize ℤ).size + 1 ∧
    (∀ j, 1 ≤ (cut j).card ∧ (cut j).card ≤ 1) ∧
    ∀ (φ : ℤ → ℤ) (ρ : Fin 2 → MvPolynomial (Fin 2) ℤ), (∀ i, (ρ i).vars ⊆ {i}) →
      (∀ i, ρ i ∈ restrictDegree (Fin 2) ℤ 1) →
      ∃ A B : Fin L → MvPolynomial (Fin 2) ℤ, (∀ j, (A j).vars ⊆ cut j) ∧
        (∀ j, Disjoint (B j).vars (cut j)) ∧
        (xorCircuit.arithmetize ℤ).eval (arithInterpretationWith ℤ (C ∘ φ)) ρ 0 =
          ∑ j, A j * B j :=
  (xorCircuit.arithmetize ℤ).exists_balanced_cuts xorCircuit_isDD.isDecomposableAt_arithmetize
    (fun i => {i}) (fun _ _ hij => Finset.disjoint_singleton.mpr hij) (fun _ => by simp)
    le_rfl (by norm_num) (by simp)

end CslibFrontierTests.BalancedCuts
