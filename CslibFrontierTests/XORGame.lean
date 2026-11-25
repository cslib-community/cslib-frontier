/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.PCP.TwoProverGame.XORGame

/-!
# General XOR games, Clifford observables, and Odd-Cycle game: checked witnesses and boundary tests

* **Clifford inner-product witness in `ℝ³` (`2` qubits)**: non-orthogonal unit vectors
  `u = (1, 0, 0)` and `v = (3/5, 4/5, 0)` yield `4 × 4` Hermitian involutions whose maximally
  entangled correlation equals `3 / 5`.
* **CHSH specialization**: `chsh` is an `IsXORGame` with `trivialWinProb = 1 / 2` and an optimal
  maximally entangled strategy on `1` qubit pair (`⌈min(2, 2) / 2⌉ = 1`).
* **Odd-Cycle (`n = 3`) vs Even-Cycle (`n = 4`) model boundary**: `oddCycleGame 3` has classical
  value `5 / 6` strictly below `quantumValue` (`cos²(π / 12)`), whereas on the bipartite even cycle
  `oddCycleGame 4` the alternating parity strategy wins with probability `1` (showing `Odd n` in
  `value_oddCycleGame` is tight).
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.XORGame

open Cslib.Quantum Cslib.PCP Cslib.PCP.TwoProverGame Matrix Real

/-! ### 1. Non-orthogonal Clifford observable witness in `ℝ³` (`2` qubits) -/

private noncomputable def u3 : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![1, 0, 0]

private noncomputable def v3 : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![3 / 5, 4 / 5, 0]

private theorem norm_u3 : ‖u3‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [u3]

private theorem norm_v3 : ‖v3‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [v3, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Real.norm_eq_abs, sq_abs]
  norm_num

example :
    (cliffordObservable u3).IsHermitian ∧
      cliffordObservable u3 * cliffordObservable u3 = 1 ∧
      (cliffordObservable v3).IsHermitian ∧
      cliffordObservable v3 * cliffordObservable v3 = 1 ∧
      (QuantumStrategy.ofUnitVectors (fun _ : Unit => u3) (fun _ => norm_u3)
        (fun _ : Unit => v3) (fun _ => norm_v3)).correlation () () = 3 / 5 := by
  refine ⟨isHermitian_cliffordObservable u3, cliffordObservable_mul_self norm_u3,
    isHermitian_cliffordObservable v3, cliffordObservable_mul_self norm_v3, ?_⟩
  rw [QuantumStrategy.correlation_ofUnitVectors, PiLp.inner_apply, Fin.sum_univ_three]
  simp only [u3, v3, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, RCLike.inner_apply, conj_trivial]
  norm_num

/-! ### 2. CHSH as an XOR game and Theorem 10 single-EPR optimality -/

example :
    chsh.IsXORGame ∧
      chsh.trivialWinProb = 1 / 2 ∧
      ∃ S : QuantumStrategy Bool Bool Bool Bool (Fin 1 → Bool) (Fin 1 → Bool),
        S.state = maxEntangled (Fin 1 → Bool) ∧ chsh.quantumWinProb S = chsh.quantumValue := by
  have hxor : chsh.IsXORGame := by
    rw [chsh_eq_xorGame]
    exact isXORGame_xorGame _ _
  have htriv : chsh.trivialWinProb = 1 / 2 := by
    rw [chsh_eq_xorGame]
    exact trivialWinProb_xorGame _ _
  exact ⟨hxor, htriv, exists_maxEntangled_optimal_strategy hxor⟩

/-! ### 3. Triangle (`n = 3`) strict quantum advantage vs Square (`n = 4`) classical win `1` -/

example :
    (oddCycleGame 3).value = 5 / 6 ∧
      (oddCycleGame 3).quantumWinProb (oddCycleStrategy 3) = cos (π / 12) ^ 2 ∧
      (oddCycleGame 3).value < (oddCycleGame 3).quantumValue := by
  have hn : Odd 3 := ⟨1, rfl⟩
  have hn3 : 3 ≤ 3 := le_rfl
  refine ⟨?_, ?_, value_oddCycleGame_lt_quantumValue hn hn3⟩
  · rw [value_oddCycleGame hn hn3]
    norm_num
  · rw [quantumWinProb_oddCycleGame_oddCycleStrategy hn hn3]
    congr 2
    norm_num

/-- Boundary check: on the even cycle `n = 4`, alternating parity wins with probability `1`, so
`(oddCycleGame 4).value = 1 ≠ 1 - 1 / 8`, confirming that `Odd n` in `value_oddCycleGame` is
necessary. -/
example : (oddCycleGame 4).value = 1 := by
  let color (s : ZMod 4) : Bool := decide (s.val % 2 = 1)
  apply le_antisymm (oddCycleGame 4).value_le_one
  refine le_trans ?_ ((oddCycleGame 4).winProb_le_value color color)
  rw [winProb_oddCycleGame]
  have hall : ∀ sb : ZMod 4 × Bool,
      ((color sb.1 ^^ color (bif sb.2 then sb.1 + 1 else sb.1)) =
        decide (sb.1 + 1 = bif sb.2 then sb.1 + 1 else sb.1)) := by
    decide
  simp only [hall, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card,
    Fintype.card_bool, nsmul_eq_mul]
  norm_num

end CslibFrontierTests.XORGame
