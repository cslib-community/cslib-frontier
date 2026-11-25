/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.SlpCostPow
import Mathlib.Tactic.NormNum

/-! Tests of the costs of straight-line programs in powers of one number, as a client that sees
only the public statements: with the base `3` for the alphabet `Fin 81` and one input below `10`,
the double of the input, a choice, a count and a quantifier over a few numbers, and one stage that
adds a family of functions to the program of the input. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SlpCostPow

open Finset Cslib.Circuits

/-- `3 ≤ 3` and `3 ^ 4 ≤ 81`. -/
private theorem base3 : StepBase 81 3 := ⟨le_rfl, le_rfl⟩

/-- One input, a number below `10`. -/
private def input : Fin 1 → Fin 10 → Fin 81 := fun _ x => Fin.castLE (by norm_num) x

/-- The function of the input. -/
private abbrev inputs : Set (Fin 10 → ℕ) := Set.range fun i x => (input i x : ℕ)

private theorem val_mem : (fun x : Fin 10 => (x : ℕ)) ∈ inputs := ⟨0, rfl⟩

/-- The double of the input takes `3` steps. -/
example : Cost 81 inputs (3 ^ 1) fun x => (x : ℕ) + x :=
  base3.op (· + ·) (Cost.of_mem val_mem) (Cost.of_mem val_mem) fun x => by
    have := x.isLt
    omega

/-- The input if it is at least `5`, and `0` otherwise, takes `3 ^ 3` steps. -/
example : Cost 81 inputs (3 ^ 3) fun x => if 5 ≤ (x : ℕ) then (x : ℕ) else 0 :=
  base3.ite (base3.rel1 (5 ≤ ·) (Cost.of_mem val_mem)) (Cost.of_mem val_mem)
    (base3.const 0 (by norm_num)) (fun x => by have := x.isLt; omega) fun _ => by norm_num

/-- The number of `i < 3` below the input takes `3 ^ 3` steps. -/
example : Cost 81 inputs (3 ^ 3) fun x => ((range 3).filter fun i => i < (x : ℕ)).card :=
  base3.card_filter (range 3) (by simp) fun i _ => base3.rel1 (i < ·) (Cost.of_mem val_mem)

/-- Whether the input is different from the numbers below `3` takes `3 ^ 4` steps. -/
example : CostP 81 inputs (3 ^ 4) fun x => ∀ i : Fin 3, (x : ℕ) ≠ i :=
  base3.forall_univ (by simp) fun i => base3.not (base3.rel1 (· = i) (Cost.of_mem val_mem))

/-- **One stage.** The program of the input has one gate; the functions `2 (x + k)` for `k < 2`,
two functions of `3` steps each, take one stage of `3 ^ 12` gates more. -/
example : ∃ H, SlpN input (1 + 1 * 3 ^ 12) H ∧ (fun x : Fin 10 => 2 * (x : ℕ)) ∈ H := by
  have h0 : SlpN input (1 + 0 * 3 ^ 12) inputs := by simpa using SlpN.inputs input
  obtain ⟨H, hS, -, hf⟩ := base3.stage h0 (fun (k : Fin 2) (x : Fin 10) => 2 * ((x : ℕ) + k))
    (a := 1) (e := 1) (by simp) (fun k => base3.op1 (fun s => 2 * (s + k)) (Cost.of_mem val_mem)
      fun x => by have := x.isLt; have := k.isLt; omega) (by norm_num)
  exact ⟨H, hS, by simpa using hf 0⟩

end CslibFrontierTests.SlpCostPow
