/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.SlpCost

/-! Tests of straight-line programs over `Fin D` under ordinary imports:

* a list of steps computing the sum of two bits becomes a program over `fullSignature 2 (Fin 2)`;
* the cost calculus computes the parity of two inputs in one gate after the inputs. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SlpStep

open Cslib.Circuits

/-- The steps `x₀`, `x₁`, `x₀ + x₁` on two bits. -/
def xorSteps : ℕ → (Fin 2 → Fin 2) → Fin 2
  | 0 => fun x => x 0
  | 1 => fun x => x 1
  | _ => fun x => x 0 + x 1

theorem isSlpStep_xorSteps : ∀ k < 3, IsSlpStep (fun i x => x i) xorSteps k
  | 0, _ => Or.inl ⟨0, rfl⟩
  | 1, _ => Or.inl ⟨1, rfl⟩
  | 2, _ => Or.inr (Or.inr ⟨0, by omega, 1, by omega, (· + ·), fun _ => rfl⟩)

/-- A program with three gates whose last gate is the sum of the two input bits. -/
example : ∃ P : Program (fullSignature 2 (Fin 2)) 2 3,
    ∀ x : Fin 2 → Fin 2, P.eval fullInterpretation x 2 = x 0 + x 1 := by
  obtain ⟨P, hP⟩ := exists_program_of_isSlpStep (fun i x => x i) xorSteps isSlpStep_xorSteps
  exact ⟨P, fun x => hP 2 x⟩

/-- Back from programs: the program gives five steps, the two inputs and its three gates. -/
example (P : Program (fullSignature 2 (Fin 2)) 2 3) :
    ∃ fn : ℕ → (Fin 2 → Fin 2) → Fin 2, ∀ k < 5, IsSlpStep (fun i x => x i) fn k :=
  (exists_isSlpStep_of_program (fun i x => x i) P).imp fun _ h => h.1

/-- The parity of the two inputs costs one gate after the inputs. -/
example : SlpN (fun i (x : Fin 2 → Fin 2) => x i) (2 + 1)
    (insert (fun x => ((x 0 : ℕ) + x 1) % 2) (Set.range fun i x => (x i : ℕ))) := by
  have h0 : (fun x : Fin 2 → Fin 2 => (x 0 : ℕ)) ∈ Set.range fun i (x : Fin 2 → Fin 2) =>
    (x i : ℕ) := ⟨0, rfl⟩
  have h1 : (fun x : Fin 2 → Fin 2 => (x 1 : ℕ)) ∈ Set.range fun i (x : Fin 2 → Fin 2) =>
    (x i : ℕ) := ⟨1, rfl⟩
  exact Cost.run (D := 2) Nat.two_pos
    (Cost.op (fun a b => (a + b) % 2) (.base h0) (.base h1) fun _ => Nat.mod_lt _ Nat.two_pos)
    le_rfl (SlpN.inputs _)

end CslibFrontierTests.SlpStep
