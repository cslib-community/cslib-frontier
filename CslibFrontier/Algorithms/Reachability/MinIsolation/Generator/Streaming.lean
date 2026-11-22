/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator
import CslibFrontier.Foundations.Data.List.OfFnPositions
import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Indexes
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

/-- Append one masked Boolean digit at the low end of an accumulated base-six word. -/
@[expose] def appendWeightDigit (acc : ℕ) (bit : Bool) : ℕ :=
  6 * acc + bit.toNat

/-- Interpret the masked digits in high-to-low order, accumulating from zero. -/
@[expose] def accumulateWeightDigits {ℓ : ℕ} (digit : Fin ℓ → Bool) : ℕ :=
  Fin.foldl ℓ (fun a j => appendWeightDigit a (digit j)) 0

/-- Extend the high-to-low accumulation by its last supplied digit. -/
theorem accumulateWeightDigits_succ {n : ℕ} (digit : Fin (n + 1) → Bool) :
    accumulateWeightDigits digit =
      appendWeightDigit (accumulateWeightDigits fun i => digit i.castSucc)
        (digit (Fin.last n)) := by
  simp only [accumulateWeightDigits, Fin.foldl_succ_last]

private theorem accumulate_eq_ofDigits {ℓ : ℕ} (digit : Fin ℓ → Bool) :
    accumulateWeightDigits digit = Nat.ofDigits 6 (List.ofFn fun j => (digit j).toNat).reverse := by
  rw [accumulateWeightDigits, Fin.foldl_eq_finRange_foldl, Nat.ofDigits_eq_foldr,
    ← List.foldl_reverse, List.reverse_reverse, List.ofFn_eq_map, List.foldl_map]
  simp only [appendWeightDigit, Nat.cast_id, Nat.add_comm]

private theorem accumulate_eq {ℓ : ℕ} (digit : Fin ℓ → Bool) :
    accumulateWeightDigits digit = ∑ j, 6 ^ (ℓ - (j.val + 1)) * (digit j).toNat := by
  rw [accumulate_eq_ofDigits, Nat.ofDigits_eq_sum_mapIdx, List.reverse_ofFn,
    List.mapIdx_eq_ofFn, List.ofFn_congr List.length_ofFn, List.sum_ofFn]
  simpa only [List.get_ofFn, Fin.cast_cast, Fin.cast_eq_self, Fin.val_cast,
    Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev, mul_comm] using
    (Equiv.sum_comp Fin.revPerm (fun j : Fin ℓ => (digit j.rev).toNat * 6 ^ j.val)).symm

/-- A word of masked Boolean digits has value below the first power beyond its length. -/
theorem accumulateWeightDigits_lt {ℓ : ℕ} (digit : Fin ℓ → Bool) :
    accumulateWeightDigits digit < 6 ^ ℓ := by
  rw [accumulate_eq_ofDigits]
  refine (Nat.ofDigits_lt_base_pow_length (by decide) ?_).trans_le (by simp)
  intro d hd
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hd)
  cases digit j <;> decide

/-- Three binary bits per digit suffice for the unscaled base-six accumulator. -/
theorem size_accumulateWeightDigits_le {n : ℕ} (digit : Fin n → Bool) :
    (accumulateWeightDigits digit).size ≤ 3 * n := by
  apply Nat.size_le.mpr
  refine (accumulateWeightDigits_lt digit).trans_le ?_
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by decide) n

/-- After scanning the first `k` masked digits the unscaled accumulator is less than `6 ^ k`. -/
theorem generatedWeightScan_prefix_lt {w n k : ℕ} (seed : Fin (codeLength w n) → Bool)
    (v : Fin w) (hk : k ≤ codeLength w n) :
    Fin.foldl k (fun a j =>
      6 * a + (indexedCodewordMod v (j.castLE hk) && seed (j.castLE hk)).toNat) 0 < 6 ^ k :=
  accumulateWeightDigits_lt _

/-- The binary logarithm of the prefix accumulator is bounded by three bits per digit.
The additional bit in the bound is enough to represent zero at the empty prefix. -/
theorem generatedWeightScan_prefix_log2_lt {w n k : ℕ} (seed : Fin (codeLength w n) → Bool)
    (v : Fin w) (hk : k ≤ codeLength w n) :
    Nat.log2 (Fin.foldl k (fun a j =>
      6 * a + (indexedCodewordMod v (j.castLE hk) && seed (j.castLE hk)).toNat) 0) < 3 * k + 1 := by
  let digit (j : Fin k) := indexedCodewordMod v (j.castLE hk) && seed (j.castLE hk)
  exact (Nat.log2_le_size (accumulateWeightDigits digit)).trans_lt
    (Nat.lt_succ_of_le (size_accumulateWeightDigits_le digit))

/-- Scan the seed through a read-only bit accessor. For a positive layer, evaluate code bits
individually and accumulate the masked digits in base six. -/
def generatedWeightScan {w n : ℕ} (seed : Fin (codeLength w n) → Bool)
    (z : Fin (n + 1) × Fin w) : ℕ :=
  if z.1.val = 0 then 0 else
    let code := indexedCodewordMod z.2
    scaleAccumulatedWeight z.1.val (accumulateWeightDigits fun j => code j && seed j)

/-- The scan uses the same seed and returns exactly the weight used by the isolation theorem. -/
theorem generatedWeightScan_eq {w n : ℕ} (seed : Fin (codeLength w n) → Bool)
    (z : Fin (n + 1) × Fin w) :
    generatedWeightScan seed z = generatedWeight seed z := by
  rw [generatedWeightScan, generatedWeight, vertexWeight]
  split_ifs
  · rfl
  · dsimp only [coefficient, scaleAccumulatedWeight]
    rw [accumulate_eq, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [indexedCodewordMod_eq]
    cases indexedCodeword z.2 j <;> cases seed j <;> simp

namespace SeedDigits

/-- The base-six value of the first `t` masked seed bits. Missing bits default to zero. -/
@[expose] def maskedPrefix (code : ℕ → Bool) (seed : List Bool) (t : ℕ) : ℕ :=
  accumulateWeightDigits fun j : Fin t => code j.val && (seed[j.val]?).getD false

/-- A raw seed written in increasing index order supplies exactly the finite seed function
used by the streaming weight formula. -/
theorem maskedPrefix_ofFn {n : ℕ} (code : ℕ → Bool) (seed : Fin n → Bool) :
    maskedPrefix code (List.ofFn seed) n =
      accumulateWeightDigits (fun j => code j.val && seed j) := by
  unfold maskedPrefix
  congr 1
  funext j
  simp

/-- A raw seed and a code-bit callback that agrees with the executable Justesen word
give the existing streaming weight, including the zero weight in layer zero. -/
theorem scaledMaskedPrefix_eq_generatedWeightScan {w n : ℕ}
    (seed : Fin (codeLength w n) → Bool) (z : Fin (n + 1) × Fin w) (code : ℕ → Bool)
    (hcode : ∀ j : Fin (codeLength w n), code j.val = indexedCodewordMod z.2 j) :
    (if z.1.val = 0 then 0 else
      scaleAccumulatedWeight z.1.val (maskedPrefix code (List.ofFn seed) (List.ofFn seed).length)) =
      generatedWeightScan seed z := by
  simp only [List.length_ofFn, maskedPrefix_ofFn, generatedWeightScan, hcode]

end SeedDigits

end Cslib.Reachability.Hoza
