/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Digits.Lemmas

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

private theorem accumulate_eq_ofDigits {ℓ : ℕ} (digit : Fin ℓ → Bool) :
    accumulate digit = Nat.ofDigits 6 (List.ofFn fun j => (digit j).toNat).reverse := by
  rw [accumulate, Fin.foldl_eq_finRange_foldl, Nat.ofDigits_eq_foldr, ← List.foldl_reverse,
    List.reverse_reverse, List.ofFn_eq_map, List.foldl_map]
  simp only [Nat.cast_id, Nat.add_comm]

private theorem accumulate_eq {ℓ : ℕ} (digit : Fin ℓ → Bool) :
    accumulate digit = ∑ j, 6 ^ (ℓ - (j.val + 1)) * (digit j).toNat := by
  rw [accumulate_eq_ofDigits, Nat.ofDigits_eq_sum_mapIdx]
  have h :
      (List.ofFn fun j => (digit j).toNat).reverse.mapIdx (fun i d => d * 6 ^ i) =
        List.ofFn (fun j : Fin ℓ => (digit j.rev).toNat * 6 ^ j.val) := by
    apply List.ext_getElem
    · simp
    · intro i _ _
      simp only [List.getElem_mapIdx, List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
      congr 3
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
  rw [h, List.sum_ofFn]
  simpa only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev, mul_comm] using
    (Equiv.sum_comp Fin.revPerm (fun j : Fin ℓ => (digit j.rev).toNat * 6 ^ j.val)).symm

private theorem accumulate_lt {ℓ : ℕ} (digit : Fin ℓ → Bool) :
    accumulate digit < 6 ^ ℓ := by
  rw [accumulate_eq_ofDigits]
  refine (Nat.ofDigits_lt_base_pow_length (by decide) ?_).trans_le (by simp)
  intro d hd
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hd)
  cases digit j <;> decide

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
