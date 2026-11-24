/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ParamTerm
public import Mathlib.NumberTheory.Chebyshev

/-!
# The main loop decides positivity of some contraction

`mainT_pos_iff`: for large inputs, the main loop is positive exactly when
some schedule's block network has a positive contraction. A schedule with a
positive contraction below `2^N` is nonzero modulo some prime in `(4N², N³]`
(`PrimeProduct`), and for those primes the counter computes the contraction
(`counterAt_cast`).
-/

public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term _root_.Turing Cslib.Complexity.CountingSimulation

variable {k s c : ℕ} {State : Type} [DecidableEq State] {machine : MultiTapePTM k Bool State}
  {e : State ≃ Fin s} {w : List Bool}

-- long `rw`/`simp` chain unfolding the main program term to the decider's arithmetic; measured
-- ~9997 heartbeats

theorem paddedTime_le_edgesN (k s t : ℕ) : paddedTime t ≤ edgesN k s t := by
  unfold paddedTime edgesN MultiTapePTM.letterBits
  calc numBlocks t * blockLength t
        ≤ numBlocks t * blockLength t * (2 * (3 * k + 1) * (s + k + 4)) :=
        Nat.le_mul_of_pos_right _ (by positivity)
    _ = 2 * (numBlocks t * (3 * k + 1) * ((s + k + 4) * blockLength t)) := by ring

omit [DecidableEq State] in
theorem contraction_lt_two_pow [Finite State] (hc : 2 ≤ c) (σ : ℕ)
    (hσ : σ < scheduleCount (k + 1) (clk c w.length)) :
    (blockNetworkOf machine e (w, clk c w.length, σ)).2.contraction ≤
      2 ^ edgesN k s (clk c w.length) := by
  have ht : 2 ≤ clk c w.length := by unfold clk; nlinarith
  have hsum := sum_contraction_blockNetworkOf machine e w ht
  have h1 : (blockNetworkOf machine e (w, clk c w.length, σ)).2.contraction ≤
      machine.acceptCount w (paddedTime (clk c w.length)) := by
    rw [← hsum]
    exact Finset.single_le_sum
        (f := fun σ => (blockNetworkOf machine e (w, clk c w.length, σ)).2.contraction)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hσ)
  exact h1.trans (Cslib.Complexity.acceptCount_le_two_pow.trans
    (Nat.pow_le_pow_right (by norm_num) (paddedTime_le_edgesN k s _)))

end Cslib.Complexity.NtimeDspace.ProgTerm
