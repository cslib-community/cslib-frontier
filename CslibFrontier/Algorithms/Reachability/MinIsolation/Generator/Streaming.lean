/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator

/-!
# Streaming evaluation of Hoza's weights

The weight accumulator reads the seed through indexed queries. It combines one seed bit
and one table-free Justesen coordinate per iteration, in order from most to least significant.
This module verifies the resulting weight. A native machine realization, including binary
dimension processing and a seed input tape, is a separate obligation.

## Main definitions

* `Cslib.Reachability.Hoza.generatedWeightScan`: weight evaluation by an indexed seed scan.

## Main results

* `Cslib.Reachability.Hoza.generatedWeightScan_eq`: agreement with the isolation generator.
* `Cslib.Reachability.Hoza.generatedWeightScan_prefix_lt`: bound on the unscaled accumulator.
-/

public section

namespace Cslib.Reachability.Hoza

open Code.JustesenFamily Finset

private def accumulate {ℓ : ℕ} (digit : Fin ℓ → Bool) : ℕ :=
  Fin.foldl ℓ (fun a j => 6 * a + (digit j).toNat) 0

private theorem accumulate_eq {ℓ : ℕ} (digit : Fin ℓ → Bool) :
    accumulate digit = ∑ j, 6 ^ (ℓ - (j.val + 1)) * (digit j).toNat := by
  induction ℓ with
  | zero => simp [accumulate]
  | succ k ih =>
    unfold accumulate
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    change 6 * accumulate (fun j : Fin k => digit j.castSucc) + (digit (Fin.last k)).toNat = _
    rw [ih, mul_sum]
    simp only [Fin.val_last, Nat.sub_self, pow_zero, one_mul]
    congr 1
    apply sum_congr rfl
    intro j _
    have hj := j.isLt
    simp only [Fin.val_castSucc]
    rw [show k + 1 - (j.val + 1) = k - (j.val + 1) + 1 by omega, pow_succ']
    ring

private theorem accumulate_lt {ℓ : ℕ} (digit : Fin ℓ → Bool) :
    accumulate digit < 6 ^ ℓ := by
  induction ℓ with
  | zero => simp [accumulate]
  | succ k ih =>
    unfold accumulate
    rw [Fin.foldl_succ_last, pow_succ']
    change 6 * accumulate (fun j : Fin k => digit j.castSucc) + (digit (Fin.last k)).toNat <
      6 * 6 ^ k
    have ha := ih fun j => digit j.castSucc
    have hd : (digit (Fin.last k)).toNat ≤ 1 := by cases digit (Fin.last k) <;> decide
    omega

/-- After scanning the first `k` masked digits the unscaled accumulator is less than `6 ^ k`. -/
theorem generatedWeightScan_prefix_lt {w n k : ℕ} (seed : Fin (codeLength w n) → Bool)
    (v : Fin w) (hk : k ≤ codeLength w n) :
    Fin.foldl k (fun a j =>
      6 * a + (indexedCodewordMod v (j.castLE hk) && seed (j.castLE hk)).toNat) 0 < 6 ^ k :=
  accumulate_lt _

/-- The binary logarithm of the prefix accumulator is bounded by three bits per digit.
The additional bit in the bound is enough to represent zero at the empty prefix. -/
theorem generatedWeightScan_prefix_log2_lt {w n k : ℕ} (seed : Fin (codeLength w n) → Bool)
    (v : Fin w) (hk : k ≤ codeLength w n) :
    Nat.log2 (Fin.foldl k (fun a j =>
      6 * a + (indexedCodewordMod v (j.castLE hk) && seed (j.castLE hk)).toNat) 0) < 3 * k + 1 := by
  rw [Nat.log2_eq_log_two]
  apply Nat.log_lt_of_lt_pow' (Nat.succ_ne_zero _)
  exact (generatedWeightScan_prefix_lt seed v hk).trans_le (calc
    6 ^ k ≤ (2 ^ 3) ^ k := Nat.pow_le_pow_left (by decide) _
    _ = 2 ^ (3 * k) := by rw [pow_mul]
    _ ≤ 2 ^ (3 * k + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ _))

/-- Scan the seed through a read-only bit accessor. For a positive layer, evaluate code bits
individually and accumulate the masked digits in base six. -/
def generatedWeightScan {w n : ℕ} (seed : Fin (codeLength w n) → Bool)
    (z : Fin (n + 1) × Fin w) : ℕ :=
  if z.1.val = 0 then 0 else
    let code := indexedCodewordMod z.2
    6 ^ padicValNat 2 z.1.val * accumulate fun j => code j && seed j

/-- The scan uses the same seed and returns exactly the weight used by the isolation theorem. -/
theorem generatedWeightScan_eq {w n : ℕ} (seed : Fin (codeLength w n) → Bool)
    (z : Fin (n + 1) × Fin w) :
    generatedWeightScan seed z = generatedWeight seed z := by
  rw [generatedWeightScan, generatedWeight, vertexWeight]
  split_ifs
  · rfl
  · dsimp only
    rw [accumulate_eq, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [indexedCodewordMod_eq, coefficient]
    cases indexedCodeword z.2 j <;> cases seed j <;> simp

end Cslib.Reachability.Hoza
