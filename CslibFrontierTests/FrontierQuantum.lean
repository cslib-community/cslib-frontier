/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Frontier.Quantum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Checked clients for quantum circuit frontier lower bounds. -/

open Cslib.Quantum Cslib.Circuits.Frontier Real Filter

namespace CslibFrontierTests.FrontierQuantum

/-! ### Concrete gate-counting, bond-rank-two, and ancilla-embedding checks -/

/-- Concrete `5`-qubit circuit with three `1`-qubit gates (including ancilla rotations on wires
`3` and `4`), one `CNOT`, and one controlled-Hadamard gate: single-qubit gates and ancilla
rotations contribute `0` to `twoQubitCount`, and the circuit satisfies `AllBondRankTwo`. -/
example :
    let wire1 (q : Fin 5) : Fin 1 ↪ Fin 5 := ⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩
    let wire01 : Fin 2 ↪ Fin 5 := ⟨fun i => if i = 0 then 0 else 1, fun i j h => by
      fin_cases i <;> fin_cases j <;> simp_all⟩
    let wire12 : Fin 2 ↪ Fin 5 := ⟨fun i => if i = 0 then 1 else 2, fun i j h => by
      fin_cases i <;> fin_cases j <;> simp_all⟩
    let bellPlusAncilla : Circuit 5 :=
      [⟨1, Gate.hadamard, wire1 0⟩,
       ⟨1, Gate.phaseT, wire1 3⟩,
       ⟨2, Gate.cnot, wire01⟩,
       ⟨1, Gate.pauliZ, wire1 4⟩,
       ⟨2, Gate.controlled Gate.hadamard, wire12⟩]
    twoQubitCount bellPlusAncilla = 2 ∧ AllBondRankTwo bellPlusAncilla := by
  intro wire1 wire01 wire12 bellPlusAncilla
  refine ⟨rfl, fun g hg => ⟨?_, fun h2 => ?_⟩⟩
  · simp only [bellPlusAncilla, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [bellPlusAncilla, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · cases h2
    · cases h2
    · exact cnot_hasBondRankTwo
    · cases h2
    · exact controlled_hasBondRankTwo Gate.hadamard

example (x : Fin 3 → Bool) :
    let dataIn3 : Fin 3 ↪ Fin 5 :=
      ⟨fun i => ⟨i.val, by omega⟩, fun _ _ h => Fin.ext (Fin.mk.inj h)⟩
    glue dataIn3 x (fun _ => false) 1 = x 1 ∧
      glue dataIn3 x (fun _ => false) 4 = false := by
  intro dataIn3
  refine ⟨glue_apply_emb dataIn3 x (fun _ => false) 1,
    glue_of_not dataIn3 x (fun _ => false) fun i hi => ?_⟩
  have hv : i.val = 4 := congrArg Fin.val hi
  omega

/-! ### `Clifford + T` `@[simp]` evaluation, phase-state unit norm, and reversible bijection -/

example (V : Gate 1) (y x : Fin 2 → Bool) :
    (Gate.controlled V : Matrix _ _ ℂ) y x =
      if y 0 = x 0 then
        if x 0 then (V : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) (fun _ => y 1) (fun _ => x 1)
        else if y 1 = x 1 then 1 else 0
      else 0 := by
  simp

example : (cos (π / 8) + sin (π / 8)) ^ 2 = 1 + 1 / √2 := by
  rw [Gate.cos_add_sin_pi_div_eight, sq_sqrt (by positivity)]

example (Q : Matrix (Fin 4) (Fin 4) (ZMod 2)) (e : Fin 4 ↪ Fin 7) (x₀ : Fin 7 → Bool) :
    ‖phaseState Q e x₀‖ = 1 :=
  norm_phaseState Q e x₀

example : Function.Bijective (boolMulVec (robustBijectiveMatrix 8)) :=
  boolMulVec_robustBijectiveMatrix_bijective 8

/-! ### Four unconditional quantum circuit lower-bound families -/

example : ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) (C : Circuit N),
    AllBondRankTwo C →
    (∀ x, C.run (glue e x x₀) =
      ket (glue e (boolMulVec (robustBijectiveMatrix n) x) x₀)) →
      (457597 / 100000 - 1 / 100 : ℝ) * n < twoQubitCount C :=
  eventually_lt_twoQubitCount_linear_457597 (ε := 1 / 100) (by norm_num)

example : ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) (C : Circuit N),
    TwoLocal C →
    (∀ x, C.run (glue e x x₀) =
      ket (glue e (boolMulVec (robustBijectiveMatrix n) x) x₀)) →
      (4 - 1 / 100 : ℝ) * n < twoQubitCount C :=
  eventually_lt_twoQubitCount_linear_twoLocal (ε := 1 / 100) (by norm_num)

example : ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
    (C : Circuit N), AllBondRankTwo C →
    (twoQubitCount C : ℝ) ≤ (278798 / 100000 - 1 / 100) * n →
      ‖inner ℂ (phaseState (hardMatrix n) e x₀) (C.run x₀)‖ ^ 2 ≤ (2 : ℝ) ^ (-γ * n) :=
  eventually_fidelity_phaseState_hardMatrix_le_278798 (ε := 1 / 100) (by norm_num)

example : ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool)
    (C : Circuit N), AllBondRankTwo C →
    (∀ x, if hardForm n x then 2 / 3 ≤ quantumAcceptProb C q_out e x₀ x
      else quantumAcceptProb C q_out e x₀ x ≤ 1 / 3) →
      (1 + π / (6 * arccos (5 / 6)) - 1 / 100) * n < twoQubitCount C :=
  eventually_lt_twoQubitCount_bqp_hardForm_switched (ε := 1 / 100) (by norm_num)

example : ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool)
    (θ : ℝ) (C : Circuit N), AllBondRankTwo C →
    (∀ x, if hardForm n x then θ < quantumAcceptProb C q_out e x₀ x
      else quantumAcceptProb C q_out e x₀ x < θ) →
      (144699 / 100000 - 1 / 100 : ℝ) * n < twoQubitCount C :=
  eventually_lt_twoQubitCount_uqp_hardForm_144699 (ε := 1 / 100) (by norm_num)

/-! The general two-qubit clients exercise thresholds strictly above the old `A₄ = 2 / 5`
bounds, using only the public quantum API. -/

example : ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
    ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool) (C : Circuit N),
      TwoLocal C → (twoQubitCount C : ℝ) ≤ (87 / 50) * n →
        |quantumCorrelation {x | hardForm n x} (quantumAcceptProb C q_out e x₀)| ≤
          (2 : ℝ) ^ (-γ * n) := by
  convert eventually_abs_quantumCorrelation_hardForm_le_twoLocal
    (ε := 1 / 100) (by norm_num) using 1; norm_num

example : ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (q_out : Fin N) (x₀ : Fin N → Bool)
    (θ : ℝ) (C : Circuit N), TwoLocal C →
    (∀ x, if hardForm n x then θ < quantumAcceptProb C q_out e x₀ x
      else quantumAcceptProb C q_out e x₀ x < θ) →
      (273 / 200 : ℝ) * n < twoQubitCount C := by
  convert eventually_lt_twoQubitCount_uqp_hardForm_twoLocal
    (ε := 1 / 100) (by norm_num) using 1; norm_num

example : ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool)
    (C : Circuit N), TwoLocal C → (twoQubitCount C : ℝ) ≤ (249 / 100) * n →
      ‖inner ℂ (phaseState (hardMatrix n) e x₀) (C.run x₀)‖ ^ 2 ≤ (2 : ℝ) ^ (-γ * n) := by
  convert eventually_fidelity_phaseState_hardMatrix_le_twoLocal
    (ε := 1 / 100) (by norm_num) using 1; norm_num

end CslibFrontierTests.FrontierQuantum
