/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RootRankTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCounting

/-!
# Source-clock cost of the outer schedule sum

The outer carry-save tree branches on two bits per head per block. Its depth enters the clock
linearly. The width of a padded accepting-path count enters only through its binary length.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing.MultiTapeATM

/-- At the full precision of the padded source count, outer routing costs only a constant
times the number of blocks. The contraction leaf time is charged with coefficient one. -/
theorem exists_outerSum_clock (k c d : ℕ) :
    ∃ K, ∀ {t : ℕ}, 2 ≤ t → ∀ (leafTime : ℕ),
      let L := 2 * (k + 1) * numBlocks t
      let w := paddedTime t + 1
      CarryLookaheadCounting.clockOfRoot c d w
        (40 * L + 2 * L.size + 2 * w.size + leafTime + 1) ≤
          K * (numBlocks t + 1) + leafTime := by
  let P := fun u : ℕ =>
    let v := u + 2
    let budget := c * (10 * v + 27) ^ d
    (2 * v + 6) * (budget + 2) + budget + 2 * v + 2
  have hpoly : Cslib.PolynomiallyBounded P := by dsimp [P]; fun_prop
  obtain ⟨A, D, hA⟩ := Cslib.polynomiallyBounded_iff_le.mp hpoly
  obtain ⟨B, hB⟩ := exists_size_pow_le_numBlocks D
  refine ⟨42 * (2 * (k + 1)) + A * B, ?_⟩
  intro t ht time L w
  let u := (t + 2).size
  have hw : w.size ≤ u + 2 := by
    have h := (Nat.size_le_size (paddedTime_add_one_le ht)).trans (Nat.size_mul_le 2 t)
    have h' := Nat.size_le_size (show t ≤ t + 2 by omega)
    change w.size ≤ (t + 2).size + 2
    dsimp [w] at *
    change (paddedTime t + 1).size ≤ 2 + t.size at h
    omega
  have hc : Nat.clog 2 (w + 1) ≤ u + 2 :=
    (Nat.clog_le_of_le_pow (Nat.succ_le_of_lt (Nat.lt_size_self w))).trans hw
  have hd : CarryLookaheadCounting.overhead c d w ≤ c * (10 * (u + 2) + 27) ^ d := by
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    unfold CarryLookaheadCounting.metadataBound
    omega
  have hshort : (2 * Nat.clog 2 (w + 1) + 6) *
      (CarryLookaheadCounting.overhead c d w + 2) +
      CarryLookaheadCounting.overhead c d w + 2 * w.size + 2 ≤ P u := by
    dsimp only [P]
    gcongr
  have hp : P u ≤ A * B * (numBlocks t + 1) := by
    rw [Nat.mul_assoc]
    exact (hA u).trans (Nat.mul_le_mul_left A (hB t))
  have hlen := Nat.size_le_self L
  have hwide : 42 * L ≤ 42 * (2 * (k + 1)) * (numBlocks t + 1) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_succ _))
  unfold CarryLookaheadCounting.clockOfRoot
  rw [Nat.add_mul (42 * (2 * (k + 1))) (A * B)]
  omega

end Cslib.Complexity.CountingSimulation
