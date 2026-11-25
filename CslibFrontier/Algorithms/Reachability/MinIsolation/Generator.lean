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
import Mathlib.NumberTheory.Padics.PadicVal.Basic
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
The native evaluator space bound is proved separately in
`Cslib.Reachability.Hoza.SeedWeight.Dimensions.generatedWeight_computesInTimeAndSpace`.

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

private theorem vertexWeight_lt_pow {V : Type*} {ℓ : ℕ} (code : V → Fin ℓ → Bool)
    (seed : Fin ℓ → Bool) (i : ℕ) (v : V) :
    vertexWeight code seed i v < 6 ^ (padicValNat 2 i + ℓ) := by
  by_cases hi : i = 0 <;> simp only [vertexWeight, hi, ↓reduceIte]
  · positivity
  · exact MinIsolation.BaseSix.levelWeight_lt_pow (padicValNat 2 i) (code v) seed

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
  have hd : d ≤ codeLength w n :=
    (Nat.mul_le_mul_right _ (by decide)).trans (codeLength_bounds w n).1
  have hbound : (n + 1) ^ 2 * w ^ 4 < 2 ^ d := calc
    (n + 1) ^ 2 * w ^ 4 ≤ (n + 1) ^ 4 * w ^ 4 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos n) (by decide))
    _ = m ^ 4 := by dsimp [m]; ring
    _ < (2 ^ (Nat.log 2 m + 1)) ^ 4 :=
      Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by decide) _) (by decide)
    _ = 2 ^ d := by simp only [d, ← pow_mul, Nat.mul_comm]
  have hsize : ((n + 1) ^ 2 * Fintype.card (Fin w) ^ 4) * 2 ^ (codeLength w n - d) <
      2 ^ codeLength w n := by
    rw [Fintype.card_fin]
    exact (Nat.mul_lt_mul_of_pos_right hbound (by positivity)).trans_eq
      (by rw [← pow_add, Nat.add_sub_of_le hd])
  obtain ⟨seed, hseed⟩ := exists_minIsolating_seed G hlayer indexedCodeword
    (fun _ _ => log_le_hammingDist_indexedCodeword) hsize
  exact ⟨seed, by unfold generatedWeight; simpa only [hlayer] using hseed⟩

private theorem layerValuation_le_log {layer limit : ℕ} (h : layer ≤ limit) :
    padicValNat 2 layer ≤ Nat.log 2 limit := by
  rw [Nat.padicValNat_def]
  exact (multiplicity_le_nat_log layer).trans (Nat.log_mono_right h)

/-- The executable weights have polynomial magnitude in the number of potential vertices. -/
private theorem generatedWeight_lt_pow {w n C : ℕ} (seed : Fin (codeLength w n) → Bool)
    (z : Fin (n + 1) × Fin w)
    (hlen : codeLength w n ≤ C * (Nat.log 2 (w * (n + 1)) + 1)) :
    generatedWeight seed z < (2 * (w * (n + 1) + 1)) ^ (3 * (C + 1)) := by
  let m := w * (n + 1)
  let L := Nat.log 2 m + 1
  have hv := layerValuation_le_log (z.1.isLt.le.trans (Nat.le_mul_of_pos_left _ z.2.isLt.pos))
  have hexp : padicValNat 2 z.1.val + codeLength w n ≤ (C + 1) * L := by
    dsimp only [m, L] at hlen ⊢
    rw [Nat.add_mul, Nat.one_mul]; omega
  have hpow : 2 ^ L ≤ 2 * (m + 1) := by
    rw [show L = Nat.log 2 m + 1 from rfl, pow_succ']
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_add_one _ _)
  calc
    generatedWeight seed z < 6 ^ (padicValNat 2 z.1.val + codeLength w n) :=
      vertexWeight_lt_pow indexedCodeword seed z.1.val z.2
    _ ≤ (2 ^ 3) ^ ((C + 1) * L) :=
      (Nat.pow_le_pow_right (by decide) hexp).trans (Nat.pow_le_pow_left (by decide) _)
    _ = (2 ^ L) ^ (3 * (C + 1)) := by
      rw [← pow_mul, ← pow_mul, show 3 * ((C + 1) * L) = L * (3 * (C + 1)) by ring]
    _ ≤ _ := Nat.pow_le_pow_left hpow (3 * (C + 1))

/-- A seed-independent chain bound using the actual code length and the binary width
of the final layer. -/
@[expose] def generatedWeightBound (w n : ℕ) : ℕ :=
  6 ^ (codeLength w n + n.size)

/-- The executable chain bound is valid for every seed and vertex. -/
theorem generatedWeight_lt_bound {w n : ℕ} (seed : Fin (codeLength w n) → Bool)
    (z : Fin (n + 1) × Fin w) : generatedWeight seed z < generatedWeightBound w n := by
  have hv := (Nat.log2_eq_log_two ▸ layerValuation_le_log (Nat.le_of_lt_succ z.1.isLt)).trans
    (Nat.log2_le_size n)
  exact (vertexWeight_lt_pow indexedCodeword seed z.1.val z.2).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))

/-- One polynomial bounds every generated weight, uniformly in the graph dimensions. -/
theorem generatedWeight_polynomial :
    ∃ C : ℕ, ∀ (w n : ℕ) (seed : Fin (codeLength w n) → Bool) (z : Fin (n + 1) × Fin w),
      generatedWeight seed z < (2 * (w * (n + 1) + 1)) ^ C :=
  ⟨_, fun w n seed z => generatedWeight_lt_pow seed z (codeLength_bounds w n).2⟩

end Cslib.Reachability.Hoza
