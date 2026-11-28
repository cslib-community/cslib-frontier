/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.SaksZhou.Parameters

/-!
# Deciding the Saks–Zhou acceptance test with packed seeds

For a fixed seed the accepting numerator is the sum of the integer entries from the start
identifier to accepting halts. Comparing twice this sum with the common denominator gives the
same strict threshold as the real-valued acceptance estimate.

## Main definitions

* `saksZhouAcceptNumerator` sums the integer entries ending in accepting configurations.
* `saksZhouSeedAccepts` tests the sum for one seed by an integer comparison.

## Main results

* `saksZhouAcceptNumerator_le` bounds the entire accepting mass by the grid denominator.
* `saksZhou_majority_iff` identifies the two strict majorities over packed and structured seeds.
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open Cslib.Probability.SaksZhou MultiTapeNTM.ConfigurationGraph MultiTapeTM Matrix Finset

variable {k : ℕ} {State : Type} [Fintype State] (M : MultiTapePTM k Bool State)

/-- The sum of the numerators of all accepting entries of the initial row. -/
@[expose] noncomputable def saksZhouAcceptNumerator (c clk z : ℕ) (w : List Bool) : ℕ :=
  let B := radix (radixExponent State c) w.length
  ∑ j ∈ range (vertexBound (k := k) B), if bad (k := k) (State := State) B w.length j then
    saksZhouEntryValue M c clk (⟨z, startID M.toNTM B, j⟩, w) else 0

/-- The total acceptance numerator fits in the grid denominator. The bound includes inputs on
which the machine has no promised behavior. -/
theorem saksZhouAcceptNumerator_le (c clk z : ℕ) (w : List Bool) :
    saksZhouAcceptNumerator M c clk z w ≤ 2 ^ saksZhouPrecision clk w.length := by
  classical
  let B := radix (radixExponent State c) w.length
  let N := vertexBound (k := k) B
  let d := saksZhouPrecision clk w.length
  let r := Nat.sqrt (clk * (Nat.log2 w.length + 2) + 1)
  let b := 2 * (5 * d)
  let seed := nisanShiftSeedOfNat b (r + 1) (r + 1) d z
  let base := saksZhouBaseCounts M d B w
  let nums := nisanSnapCounts (Equiv.refl _) b d (r + 1) seed.1 base (r + 1) seed.2
  unfold saksZhouAcceptNumerator
  change (∑ j ∈ range N, if bad (k := k) (State := State) B w.length j then
    saksZhouEntryValue M c clk (⟨z, startID M.toNTM B, j⟩, w) else 0) ≤ 2 ^ d
  rw [← Fin.sum_univ_eq_sum_range]
  by_cases hi : startID M.toNTM B < N
  · refine le_trans (sum_le_sum (g := fun j : Fin N => nums ⟨_, hi⟩ j) fun j _ => ?_)
      (sum_nisanSnapCounts_le (Equiv.refl _) b d (r + 1) seed.1 base r seed.2 ⟨_, hi⟩)
    split_ifs
    · simp only [saksZhouEntryValue]
      split_ifs with hrow hcol
      · exact le_rfl
      · exact (hcol j.isLt).elim
      · exact (hrow hi).elim
      · exact Nat.zero_le _
    · exact Nat.zero_le _
  · have he (j : Fin N) : saksZhouEntryValue M c clk (⟨z, startID M.toNTM B, j⟩, w) = 0 := by
      simp only [saksZhouEntryValue]
      split_ifs with hrow
      · exact (hi hrow).elim
      · rfl
      · rfl
    simp [he]

/-- The exact dyadic acceptance estimate for a fixed packed seed. -/
theorem saksZhouAcceptEst_eq_numerator (c clk z : ℕ) {w : List Bool}
    (hspace : M.toNTM.RunsInSpace w (c * (Nat.log2 w.length + 1))) :
    let s := saksZhouLevels clk w.length
    let d := saksZhouPrecision clk w.length
    let m := 5 * d
    M.saksZhouAcceptEst c hspace m s d (nisanShiftSeedOfNat (2 * m) s s d z) =
      (saksZhouAcceptNumerator M c clk z w : ℝ) / 2 ^ d := by
  intro s d m
  let B := radix (radixExponent State c) w.length
  let N := vertexBound (k := k) B
  have h := saksZhouEntryValue_div M c clk z w
  simp only [saksZhouAcceptEst, Matrix.mulVec, dotProduct, saksZhouAcceptNumerator,
    Nat.cast_sum, Finset.sum_div]
  rw [← Fin.sum_univ_eq_sum_range (fun j => ((if bad (k := k) (State := State) B w.length j then
    saksZhouEntryValue M c clk (⟨z, startID M.toNTM B, j⟩, w) else 0 : ℕ) : ℝ) / 2 ^ d) N]
  apply Finset.sum_congr rfl
  intro j _
  rw [h]
  simp only [compactAcceptVec, compactStart, B]
  split_ifs <;> simp [d]

/-- Test a packed seed by an integer comparison against half the grid denominator. -/
@[expose] noncomputable def saksZhouSeedAccepts (c clk : ℕ) (p : ℕ × List Bool) : Bool :=
  decide (2 ^ saksZhouPrecision clk p.2.length < 2 * saksZhouAcceptNumerator M c clk p.1 p.2)

/-- The strict majority over packed integer tests agrees with the density of seeds whose real
acceptance estimate exceeds one half. -/
theorem saksZhou_majority_iff (c clk : ℕ) {w : List Bool}
    (hspace : M.toNTM.RunsInSpace w (c * (Nat.log2 w.length + 1))) :
    let s := saksZhouLevels clk w.length
    let d := saksZhouPrecision clk w.length
    let m := 5 * d
    saksZhouSeedCount clk w.length < 2 * (List.range (saksZhouSeedCount clk w.length)).countP
      (fun z => saksZhouSeedAccepts M c clk (z, w)) ↔
      (1 : ℝ) / 2 < ((Finset.univ.filter fun p : NisanShiftSeed (2 * m) s s d =>
        (1 : ℝ) / 2 < M.saksZhouAcceptEst c hspace m s d p).dens : ℝ) := by
  classical
  intro s d m
  let P (p : NisanShiftSeed (2 * m) s s d) :=
    decide ((1 : ℝ) / 2 < M.saksZhouAcceptEst c hspace m s d p)
  have htest (z : ℕ) : saksZhouSeedAccepts M c clk (z, w) =
      P (nisanShiftSeedOfNat (2 * m) s s d z) := by
    unfold P saksZhouSeedAccepts
    rw [saksZhouAcceptEst_eq_numerator M c clk z hspace, decide_eq_decide]
    change 2 ^ d < 2 * _ ↔ (1 : ℝ) / 2 < _ / 2 ^ d
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    simp only [one_mul]
    rw [mul_comm 2]
    norm_cast
  have hcount := countP_range_nisanShiftSeedOfNat (2 * m) s s d P
  simp only [htest]
  change 2 ^ _ < 2 * (List.range (2 ^ (s * (3 * (2 * m) - 1) + s * d))).countP _ ↔ _
  rw [hcount, Finset.dens, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
    card_nisanShiftSeed, div_lt_div_iff₀ (by norm_num) (by positivity), one_mul]
  simp only [P, decide_eq_true_eq]
  set count := (Finset.univ.filter fun p : NisanShiftSeed (2 * m) s s d =>
    (1 : ℝ) / 2 < M.saksZhouAcceptEst c hspace m s d p).card
  change 2 ^ (s * (3 * (2 * m) - 1) + s * d) < 2 * count ↔ _
  rw [mul_comm 2 count]
  norm_cast

end Turing.MultiTapePTM.ConfigurationGraph
