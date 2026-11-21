/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RootRankTime
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Schedule
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Amortizing root schedule access at active contraction depths

One root packet query costs a constant times the block count. At depth `d`, the contraction
schedule bounds `16^d` by a constant times the square root of the logarithm of the number
of root edges. Even that many calls to the root packet machine fit the source time divided
by the square root of its binary logarithm. This accounts for repeated access to movement
rows. The costs of source input access and of other contraction operations are separate.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Cslib.Circuits.Frontier

/-- Multiplying a block scan by the square-root-logarithmic depth allowance still fits the
target source clock. The estimate also covers the two smallest source clocks. -/
theorem numBlocks_mul_sqrt_log_le (t : ℕ) :
    (numBlocks t + 1) * (Nat.log 2 (t + 2)).sqrt ≤
      3 * (t / (Nat.log 2 (t + 2)).sqrt + 1) := by
  by_cases h : 2 ≤ t
  · let b := blockLength t
    let f := (Nat.log 2 (t + 2)).sqrt
    have hf : 0 < f := Nat.sqrt_pos.mpr (Nat.log_pos one_lt_two (by omega))
    have hf₂ : f * f ≤ b := (Nat.sqrt_le _).trans (Nat.log_le_clog _ _)
    have hq := Nat.ceilDiv_mul_lt (a := t) (one_le_blockLength t)
    change numBlocks t * b < t + b at hq
    have hb : b ≤ t := blockLength_le h
    have hm : (numBlocks t + 1) * f * f ≤ 3 * t := by
      rw [Nat.mul_assoc]
      exact (Nat.mul_le_mul_left _ hf₂).trans (by rw [Nat.add_mul]; omega)
    have hd := (Nat.le_div_iff_mul_le hf).mpr hm
    exact hd.trans ((Nat.mul_div_le_mul_div_add 3 t f).trans_eq (by ring))
  · interval_cases t <;> decide

private theorem sqrt_log_rootEdges_le (k states : ℕ) :
    ∃ c, ∀ t, (Nat.log 2 (rootEdges k states t)).sqrt ≤ c * (Nat.log 2 (t + 2)).sqrt := by
  let H := 4 * (3 * k + 1) * (states + k + 4)
  refine ⟨H.size + 6, fun t => ?_⟩
  let f := (Nat.log 2 (t + 2)).sqrt
  have hf : 0 < f := Nat.sqrt_pos.mpr (Nat.log_pos one_lt_two (by omega))
  have hb : blockLength t ≤ t + 2 :=
    (Nat.clog_le_of_le_pow (Nat.lt_size_self (t + 2)).le).trans (Nat.size_le_self _)
  have hp := Nat.ceilDiv_mul_lt (a := t) (one_le_blockLength t)
  change numBlocks t * blockLength t < t + blockLength t at hp
  have he : rootEdges k states t ≤ H * (t + 2) := by
    have hq : numBlocks t * blockLength t ≤ 2 * (t + 2) := by omega
    calc
      rootEdges k states t = (2 * (3 * k + 1) * (states + k + 4)) *
          (numBlocks t * blockLength t) := by
        unfold rootEdges Turing.MultiTapeTM.RootPredecessorGraph.edgeCount rootCopies
          Turing.MultiTapePTM.letterBits
        ring
      _ ≤ _ := (Nat.mul_le_mul_left _ hq).trans_eq (by dsimp [H]; ring)
  have hs := (Nat.size_le_size he).trans (Nat.size_mul_le _ _)
  have hlog : Nat.log 2 (rootEdges k states t) ≤ H.size + (t + 2).size :=
    ((Nat.log_le_clog _ _).trans (Nat.clog_le_of_le_pow (Nat.lt_size_self _).le)).trans hs
  have hz := Nat.log2_eq_size_sub_one (t + 2)
  rw [Nat.log2_eq_log_two] at hz
  have hsq := Nat.lt_succ_sqrt' (Nat.log 2 (t + 2))
  change Nat.log 2 (t + 2) < (f + 1) ^ 2 at hsq
  have hz' : (t + 2).size ≤ (f + 1) ^ 2 := by omega
  have hL : Nat.log 2 (rootEdges k states t) ≤ H.size + 5 * (f * f) := by
    refine hlog.trans (Nat.add_le_add_left (hz'.trans ?_) _)
    calc
      (f + 1) ^ 2 ≤ (2 * f) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ _ := by nlinarith
  have hf₂ : 1 ≤ f * f := Nat.mul_pos hf hf
  have hm : H.size ≤ H.size * (f * f) := Nat.le_mul_of_pos_right _ hf₂
  have hh : H.size + 5 ≤ (H.size + 6) * (H.size + 6) := by nlinarith
  apply Nat.mul_self_le_mul_self_iff.mp
  calc
    _ ≤ Nat.log 2 (rootEdges k states t) := Nat.sqrt_le _
    _ ≤ (H.size + 5) * (f * f) := hL.trans (by rw [Nat.add_mul]; omega)
    _ ≤ ((H.size + 6) * (H.size + 6)) * (f * f) := Nat.mul_le_mul_right _ hh
    _ = _ := by ring

/-- At every active depth the source clock absorbs a factor of `16^d` on root schedule
queries priced by their established block-count bound. -/
theorem exists_repeated_root_charge (k states C rate : ℕ) :
    ∃ K, ∀ {t d m p : ℕ}, 2 ≤ rootEdges k states t →
      ContractionSchedule.Active C (rootEdges k states t) d m p →
      16 ^ d * (rate * (numBlocks t + 1)) ≤ K * (t / (Nat.log 2 (t + 2)).sqrt + 1) := by
  obtain ⟨c, hc⟩ := sqrt_log_rootEdges_le k states
  refine ⟨3 * rate * C * c, ?_⟩
  intro t d m p ht h
  have hd := (h.sixteen_pow_lt ht).le.trans (Nat.mul_le_mul_left C (hc t))
  calc
    _ ≤ (C * (c * (Nat.log 2 (t + 2)).sqrt)) * (rate * (numBlocks t + 1)) :=
      Nat.mul_le_mul_right _ hd
    _ = (rate * C * c) * ((numBlocks t + 1) * (Nat.log 2 (t + 2)).sqrt) := by ring
    _ ≤ _ := (Nat.mul_le_mul_left _ (numBlocks_mul_sqrt_log_le t)).trans_eq (by ring)

end Cslib.Complexity.CountingSimulation
