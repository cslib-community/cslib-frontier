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
       ⟨1, phaseT, wire1 3⟩,
       ⟨2, Gate.cnot, wire01⟩,
       ⟨1, pauliZ, wire1 4⟩,
       ⟨2, controlledGate Gate.hadamard, wire12⟩]
    twoQubitCount bellPlusAncilla = 2 ∧ AllBondRankTwo bellPlusAncilla := by
  intro wire1 wire01 wire12 bellPlusAncilla
  refine ⟨rfl, fun g hg => ?_, fun g hg h2 => ?_⟩
  · simp only [bellPlusAncilla, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [bellPlusAncilla, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · cases h2
    · cases h2
    · exact cnot_hasBondRankTwo
    · cases h2
    · exact controlledGate_hasBondRankTwo Gate.hadamard

example (x : Fin 3 → Bool) :
    let dataIn3 : Fin 3 ↪ Fin 5 :=
      ⟨fun i => ⟨i.val, by omega⟩, fun _ _ h => Fin.ext (Fin.mk.inj h)⟩
    embedBits dataIn3 (fun _ => false) x 1 = x 1 ∧
      embedBits dataIn3 (fun _ => false) x 4 = false := by
  intro dataIn3
  refine ⟨embedBits_apply_wire dataIn3 (fun _ => false) x 1,
    embedBits_apply_of_notMem dataIn3 (fun _ => false) x ?_⟩
  rintro ⟨i, hi⟩
  have hv : i.val = 4 := congrArg Fin.val hi
  omega

/-! ### `Clifford + T` identity, phase-state unit norm, and reversible linear bijection -/

example : (cos (π / 8) + sin (π / 8)) ^ 2 = 1 + 1 / √2 := by
  rw [cos_add_sin_pi_div_eight, sq_sqrt (by positivity)]

example (Q : Matrix (Fin 4) (Fin 4) (ZMod 2)) (e : Fin 4 ↪ Fin 7) (x₀ : Fin 7 → Bool) :
    ‖phaseState Q e x₀‖ = 1 :=
  norm_phaseState Q e x₀

example : Function.Bijective (boolMulVec (robustBijectiveMatrix 8)) :=
  boolMulVec_robustBijectiveMatrix_bijective 8

/-! ### Four unconditional quantum circuit lower-bound families -/

example : ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) (C : Circuit N),
    AllBondRankTwo C →
    (∀ x, C.run (embedBits e x₀ x) =
      ket (embedBits e x₀ (boolMulVec (robustBijectiveMatrix n) x))) →
      (457597 / 100000 - 1 / 100 : ℝ) * n < twoQubitCount C :=
  eventually_lt_twoQubitCount_linear_457597 (ε := 1 / 100) (by norm_num)

example : ∀ᶠ n in atTop, ∀ (N : ℕ) (e : Fin n ↪ Fin N) (x₀ : Fin N → Bool) (C : Circuit N),
    TwoLocal C →
    (∀ x, C.run (embedBits e x₀ x) =
      ket (embedBits e x₀ (boolMulVec (robustBijectiveMatrix n) x))) →
      (7 / 2 - 1 / 100 : ℝ) * n < twoQubitCount C :=
  eventually_lt_twoQubitCount_linear_twoLocal_two_fifths (ε := 1 / 100) (by norm_num)

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

end CslibFrontierTests.FrontierQuantum
