/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.AllPairs
public import CslibFrontier.Foundations.Data.Code.JustesenFamily

import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# An executable family of min-isolating weights

Use a finite-label Justesen code in Hoza's base-six assignment. The seed length is
logarithmic in the size of the layered vertex set, and the weights are polynomially
bounded. Every layered digraph on the vertex set admits an isolating seed. These are
the combinatorial and magnitude guarantees of [Hoza2026NLUL, Theorem 1.3].
Use a graph on `Fin (n + 1) × Fin w`, with layer first and column second.
Supply `hlayer : ∀ z, G.layer z = z.1.val`. The path weight sums only internal
vertices. The seed length bound is `Code.JustesenFamily.codeLength_bounds`.
`CslibFrontierTests.LayeredDigraph` checks the existence theorem, seed-length
bound, and polynomial magnitude bound through ordinary imports.
The native logspace bound on the evaluator is a separate obligation.

## Main definitions

* `Cslib.Reachability.Hoza.generatedWeight`: the executable Justesen-based weight.
* `Cslib.Reachability.Hoza.generatedWeightBound`: a uniform chain bound for subdivision.

## Main results

* `Cslib.Reachability.Hoza.exists_generatedWeight_isMinIsolating`: success for some seed.
* `Cslib.Reachability.Hoza.generatedWeight_polynomial`: a polynomial magnitude bound.
-/

public section

namespace Cslib.Reachability.Hoza

open Code.JustesenFamily
open Finset

private theorem vertexWeight_lt_pow {V : Type*} {ℓ : ℕ} (code : V → Fin ℓ → Bool)
    (seed : Fin ℓ → Bool) (i : ℕ) (v : V) :
    vertexWeight code seed i v < 6 ^ (padicValNat 2 i + ℓ) := by
  by_cases hi : i = 0
  · simp only [vertexWeight, hi, ↓reduceIte]
    positivity
  simp only [vertexWeight, hi, ↓reduceIte]
  calc
    (∑ j, coefficient i j * (code v j).toNat * (seed j).toNat) ≤ ∑ j, coefficient i j := by
      apply sum_le_sum
      intro j _
      cases code v j <;> cases seed j <;> simp
    _ = 6 ^ padicValNat 2 i * ∑ k ∈ range ℓ, 6 ^ k := by
      rw [mul_sum, ← Fin.sum_univ_eq_sum_range]
      calc
        (∑ j, coefficient i j) = ∑ j, coefficient i (Fin.revPerm j) :=
          (Equiv.sum_comp Fin.revPerm _).symm
        _ = _ := by
          refine sum_congr rfl fun j _ => ?_
          have hj := j.isLt
          simp only [coefficient, scaleAccumulatedWeight, Fin.revPerm_apply, Fin.val_rev]
          congr 2
          omega
    _ < 6 ^ (padicValNat 2 i + ℓ) := by
      rw [pow_add]
      exact Nat.mul_lt_mul_of_pos_left (Nat.geomSum_lt (by decide) fun _ hk => mem_range.mp hk)
        (by positivity)

/-- Evaluate the weight of a vertex from its layer, column, and binary seed. -/
@[expose] def generatedWeight {w n : ℕ} (seed : Fin (codeLength w n) → Bool)
    (z : Fin (n + 1) × Fin w) : ℕ :=
  vertexWeight indexedCodeword seed z.1.val z.2

/-- Some seed in the Justesen-based family min-isolates any simple layered graph. -/
theorem exists_generatedWeight_isMinIsolating {w n : ℕ}
    (G : LayeredDigraph (Fin (n + 1) × Fin w)) (hlayer : ∀ z, G.layer z = z.1.val) :
    ∃ seed, G.IsMinIsolating (generatedWeight seed) := by
  let m := w * (n + 1)
  let d := 4 * (Nat.log 2 m + 1)
  have hd : d ≤ codeLength w n := by
    have := (codeLength_bounds w n).1
    dsimp [d, m]
    omega
  have hbase : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have hbound : (n + 1) ^ 2 * w ^ 4 < 2 ^ d := by
    calc
      (n + 1) ^ 2 * w ^ 4 ≤ (n + 1) ^ 4 * w ^ 4 := by
        apply Nat.mul_le_mul_right
        calc
          (n + 1) ^ 2 ≤ (n + 1) ^ 2 * (n + 1) ^ 2 :=
            Nat.le_mul_of_pos_right _ (by positivity)
          _ = (n + 1) ^ 4 := by ring
      _ = m ^ 4 := by dsimp [m]; ring
      _ < (2 ^ (Nat.log 2 m + 1)) ^ 4 := Nat.pow_lt_pow_left hbase (by decide)
      _ = 2 ^ d := by simp only [d, ← pow_mul, Nat.mul_comm]
  have hsize : ((n + 1) ^ 2 * Fintype.card (Fin w) ^ 4) * 2 ^ (codeLength w n - d) <
      2 ^ codeLength w n := by
    rw [Fintype.card_fin]
    calc
      _ < 2 ^ d * 2 ^ (codeLength w n - d) := Nat.mul_lt_mul_of_pos_right hbound (by positivity)
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hd]
  obtain ⟨seed, hseed⟩ := exists_minIsolating_seed G hlayer indexedCodeword
    (fun _ _ => log_le_hammingDist_indexedCodeword) hsize
  refine ⟨seed, ?_⟩
  change G.IsMinIsolating (fun z => vertexWeight indexedCodeword seed z.1.val z.2)
  simpa only [hlayer] using hseed

private theorem layerValuation_le_log {layer limit : ℕ} (h : layer ≤ limit) :
    padicValNat 2 layer ≤ Nat.log 2 limit := by
  by_cases hz : layer = 0
  · simp [hz, Nat.padicValNat_def]
  · apply Nat.le_log_of_pow_le (by decide)
    have hdiv : 2 ^ padicValNat 2 layer ∣ layer := by
      rw [Nat.padicValNat_def]
      exact pow_multiplicity_dvd _ _
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hdiv).trans h

/-- The executable weights have polynomial magnitude in the number of potential vertices. -/
private theorem generatedWeight_lt_pow {w n C : ℕ} (seed : Fin (codeLength w n) → Bool)
    (z : Fin (n + 1) × Fin w)
    (hlen : codeLength w n ≤ C * (Nat.log 2 (w * (n + 1)) + 1)) :
    generatedWeight seed z < (2 * (w * (n + 1) + 1)) ^ (3 * (C + 1)) := by
  let m := w * (n + 1)
  let L := Nat.log 2 m + 1
  have hw : 0 < w := z.2.isLt.pos
  have hsize : n + 1 ≤ m := Nat.le_mul_of_pos_left _ hw
  have hv := layerValuation_le_log (z.1.isLt.le.trans hsize)
  have hexp : padicValNat 2 z.1.val + codeLength w n ≤ (C + 1) * L := by
    change codeLength w n ≤ C * L at hlen
    have hlog : Nat.log 2 m ≤ L := Nat.le_succ _
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hpow : 2 ^ L ≤ 2 * (m + 1) := by
    rw [show L = Nat.log 2 m + 1 from rfl, pow_succ']
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_add_one _ _)
  calc
    generatedWeight seed z < 6 ^ (padicValNat 2 z.1.val + codeLength w n) :=
      vertexWeight_lt_pow indexedCodeword seed z.1.val z.2
    _ ≤ 6 ^ ((C + 1) * L) := Nat.pow_le_pow_right (by decide) hexp
    _ ≤ (2 ^ 3) ^ ((C + 1) * L) := Nat.pow_le_pow_left (by decide) _
    _ = (2 ^ L) ^ (3 * (C + 1)) := by
      have hab : 3 * ((C + 1) * L) = L * (3 * (C + 1)) := by ac_rfl
      rw [← pow_mul, ← pow_mul, hab]
    _ ≤ _ := Nat.pow_le_pow_left hpow (3 * (C + 1))

/-- A seed-independent chain bound using the actual code length and the binary width
of the final layer. -/
@[expose] def generatedWeightBound (w n : ℕ) : ℕ :=
  6 ^ (codeLength w n + n.size)

/-- The executable chain bound is valid for every seed and vertex. -/
theorem generatedWeight_lt_bound {w n : ℕ} (seed : Fin (codeLength w n) → Bool)
    (z : Fin (n + 1) × Fin w) : generatedWeight seed z < generatedWeightBound w n := by
  have hv := layerValuation_le_log (Nat.le_of_lt_succ z.1.isLt)
  rw [← Nat.log2_eq_log_two, Nat.log2_eq_size_sub_one] at hv
  exact (vertexWeight_lt_pow indexedCodeword seed z.1.val z.2).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))

/-- One polynomial bounds every generated weight, uniformly in the graph dimensions. -/
theorem generatedWeight_polynomial :
    ∃ C : ℕ, ∀ (w n : ℕ) (seed : Fin (codeLength w n) → Bool) (z : Fin (n + 1) × Fin w),
      generatedWeight seed z < (2 * (w * (n + 1) + 1)) ^ C :=
  ⟨_, fun w n seed z => generatedWeight_lt_pow seed z (codeLength_bounds w n).2⟩

end Cslib.Reachability.Hoza
