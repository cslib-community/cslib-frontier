/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DriverCorrect
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.InitializedEvaluatorCorrect
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.BalancedParameters
import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearchBounds

/-!
# Quantitative storage of Williams's native driver

With the initialized evaluator and balanced parameters, every candidate through the largest
guess fits a fixed multiple of the block width selected at that guess. The complete driver,
including its original-input scan, has squared storage at most a fixed-machine constant times
the largest guess multiplied by its binary length. No number of guesses multiplies the
candidate storage allowance.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Driver

open MultiTapeTM

/-- An integer square bound states the square-root storage rate without real-valued rounding. -/
theorem space_sq_le (k s : ℕ) (Q : Type) : ∃ C, ∀ N τ : ℕ,
    (space k (InitializedEvaluator.scheduleAllowance k s Q) BalancedParameters.parameters
      N τ) ^ 2 ≤ C * (max (N + 1) τ * (max (N + 1) τ).size) := by
  obtain ⟨c, hc⟩ := ScheduleSearch.scheduleAllowance_le k s Q
  let K := 64 * (k + 2) * (18 * c + 20)
  refine ⟨4 * K ^ 2, fun N τ => ?_⟩
  let G := max (N + 1) τ
  let B := BalancedParameters.blockWidth G
  have hG : 0 < G := by dsimp only [G]; omega
  have hNsize : N.size ≤ G.size := Nat.size_le_size (by dsimp only [G]; omega)
  have hGsize : G.size < 2 * B := BalancedParameters.size_lt_twice_blockWidth G
  have hX (guess : ℕ) (hguess : guess ≤ G) :
      InitializedEvaluator.scheduleAllowance k s Q N
          (BalancedParameters.parameters.blockWidth guess)
          (BalancedParameters.parameters.horizon guess) +
        (BalancedParameters.parameters.blockWidth guess).size +
        BalancedParameters.parameters.horizon guess ≤
      c * (15 * B + N.size + 1) + 15 * B := by
    let bw := BalancedParameters.blockWidth guess
    let hz := BalancedParameters.horizon guess
    change InitializedEvaluator.scheduleAllowance k s Q N bw hz + bw.size + hz ≤ _
    have hcost := hc N bw hz (BalancedParameters.blockWidth_pos guess)
    have h15 : bw + hz * (bw.size + 1) ≤ 15 * B :=
      (BalancedParameters.storage_le guess).trans
        (Nat.mul_le_mul_left 15 (BalancedParameters.blockWidth_mono hguess))
    have hbs : bw.size ≤ bw := length_encNat_eq_size bw ▸ length_encNat_le_self bw
    have hhz : hz ≤ hz * (bw.size + 1) := Nat.le_mul_of_pos_right hz (Nat.succ_pos _)
    have := Nat.mul_le_mul_left c (Nat.add_le_add_right (Nat.add_le_add_right h15 N.size) 1)
    omega
  have hinner : c * (15 * B + N.size + 1) + 15 * B + N.size + G.size + 1 ≤ (18 * c + 20) * B := by
    have hmul := Nat.mul_le_mul_left c (show 15 * B + N.size + 1 ≤ 18 * B by omega)
    calc c * (15 * B + N.size + 1) + 15 * B + N.size + G.size + 1
        ≤ c * (18 * B) + 20 * B := by omega
      _ = (18 * c + 20) * B := by ring
  have hscalar : space k (InitializedEvaluator.scheduleAllowance k s Q)
      BalancedParameters.parameters N τ ≤ K * B :=
    calc
      _ ≤ 64 * (k + 2) * (c * (15 * B + N.size + 1) + 15 * B + N.size + G.size + 1) :=
        space_le_of_le k _ _ N τ _ hX
      _ ≤ 64 * (k + 2) * ((18 * c + 20) * B) := Nat.mul_le_mul_left _ hinner
      _ = K * B := by dsimp only [K]; ring
  have hbalanced : B ^ 2 ≤ 4 * (G * G.size) := BalancedParameters.blockWidth_sq_le hG
  calc
    _ ≤ (K * B) ^ 2 := Nat.pow_le_pow_left hscalar 2
    _ = K ^ 2 * B ^ 2 := by ring
    _ ≤ K ^ 2 * (4 * (G * G.size)) := Nat.mul_le_mul_left _ hbalanced
    _ = 4 * K ^ 2 * (G * G.size) := by ring

end Turing.MultiTapePTM.BlockComputation.Driver
