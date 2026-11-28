/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Real
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Order, supremum, and sublinear-envelope lemmas for exponential rates

General real-order and asymptotic closure lemmas used across fine-grained exponential-rate
characterizations:

* `Cslib.iSup_ge_eq_iSup_of_monotone` and `Cslib.tendsto_atTop_nhds_one_iff_iSup_eq_one`:
  finite-prefix invariance and monotone-limit characterization of `⨆ k, s k = 1`.
* `Cslib.exists_two_pow_le_of_isLittleO` and `Cslib.exists_monotone_isLittleO_ge`: exponential
  linear domination and running-maximum monotone envelopes for `o(n)` scales.

## Main results

* `Cslib.iSup_ge_eq_iSup_of_monotone`, `Cslib.tendsto_atTop_nhds_one_iff_iSup_eq_one`: finite-prefix
  suprema and monotone convergence to `1`.
* `Cslib.exists_two_pow_le_of_isLittleO`, `Cslib.exists_monotone_isLittleO_ge`: `2 ^ s n` linear
  domination and monotone `o(n)` envelopes.
-/

public section

namespace Cslib

open Filter Asymptotics Topology

/-- Dropping any finite prefix `k < K` of a monotone bounded sequence `s : ℕ → ℝ` preserves its
supremum. -/
theorem iSup_ge_eq_iSup_of_monotone {s : ℕ → ℝ} (hmono : Monotone s) {B : ℝ}
    (hbdd : ∀ k, s k ≤ B) (K : ℕ) :
    (⨆ k : {k : ℕ // K ≤ k}, s k.val) = ⨆ k : ℕ, s k := by
  have : Nonempty {k : ℕ // K ≤ k} := ⟨⟨K, le_rfl⟩⟩
  have hBdd : BddAbove (Set.range s) := ⟨B, Set.forall_mem_range.mpr hbdd⟩
  have hBddK : BddAbove (Set.range fun k : {k : ℕ // K ≤ k} => s k.val) :=
    ⟨B, Set.forall_mem_range.mpr fun k => hbdd k.val⟩
  refine le_antisymm
    (ciSup_le fun k => le_ciSup hBdd k.val)
    (ciSup_le fun k => (hmono (Nat.le_max_left k K)).trans
      (le_ciSup hBddK ⟨max k K, Nat.le_max_right k K⟩))

/-- A monotone sequence bounded above by `1` tends to `1` iff its supremum equals `1`. -/
theorem tendsto_atTop_nhds_one_iff_iSup_eq_one {s : ℕ → ℝ} (hmono : Monotone s)
    (hbdd : ∀ k, s k ≤ 1) :
    Tendsto s atTop (𝓝 1) ↔ (⨆ k : ℕ, s k) = 1 :=
  have hBdd : BddAbove (Set.range s) := ⟨1, Set.forall_mem_range.mpr hbdd⟩
  ⟨fun h => tendsto_nhds_unique (tendsto_atTop_ciSup hmono hBdd) h,
    fun h => h ▸ tendsto_atTop_ciSup hmono hBdd⟩

/-- Any sublinear exponent `s =o[atTop] id` satisfies `2 ^ s n ≤ K * 2 ^ (δ * n)` globally for
every `δ > 0`. -/
theorem exists_two_pow_le_of_isLittleO {s : ℕ → ℝ}
    (hs : s =o[atTop] fun n : ℕ => (n : ℝ)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, (2 : ℝ) ^ s n ≤ K * (2 : ℝ) ^ (δ * n) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp <| (hs.bound hδ).mono fun n hn => by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg n)] at hn
    exact (Real.le_norm_self (s n)).trans hn
  let K : ℝ := 1 + ∑ m ∈ Finset.range N₀, (2 : ℝ) ^ s m
  have hK1 : 1 ≤ K := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
  refine ⟨K, hK1, fun n => ?_⟩
  by_cases hn : n < N₀
  · have hle : (2 : ℝ) ^ s n ≤ ∑ m ∈ Finset.range N₀, (2 : ℝ) ^ s m :=
      Finset.single_le_sum (f := fun m => (2 : ℝ) ^ s m)
        (fun _ _ => by positivity) (Finset.mem_range.mpr hn)
    exact (by dsimp only [K]; linarith : (2 : ℝ) ^ s n ≤ K).trans
      (le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (by norm_num) (by positivity)))
  · exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) (hN₀ n (not_lt.mp hn))).trans
      (le_mul_of_one_le_left (by positivity) hK1)

/-- Every nonnegative `o(n)` scale is bounded above by a *monotone* nonnegative `o(n)` scale
(its running maximum). -/
theorem exists_monotone_isLittleO_ge {s : ℕ → ℝ} (hnn : ∀ n, 0 ≤ s n)
    (hs : s =o[atTop] fun n : ℕ => (n : ℝ)) :
    ∃ sBar : ℕ → ℝ, Monotone sBar ∧ (∀ n, 0 ≤ sBar n) ∧ (∀ n, s n ≤ sBar n) ∧
      (sBar =o[atTop] fun n : ℕ => (n : ℝ)) := by
  let sBar (N : ℕ) : ℝ := (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one s
  have hle (N : ℕ) : s N ≤ sBar N := Finset.le_sup' s (Finset.mem_range.mpr (Nat.lt_succ_self N))
  have hnnBar (N : ℕ) : 0 ≤ sBar N := (hnn N).trans (hle N)
  refine ⟨sBar, fun M N hMN => Finset.sup'_mono s
    (Finset.range_mono (Nat.add_le_add_right hMN 1)) Finset.nonempty_range_add_one,
    hnnBar, hle, isLittleO_iff.mpr fun ε hε => ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp <| (hs.bound (half_pos hε)).mono fun m hm => by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg m)] at hm
    exact (Real.le_norm_self (s m)).trans hm
  let B : ℝ := ∑ m ∈ Finset.range N₀, s m
  refine eventually_atTop.mpr ⟨⌈2 * B / ε⌉₊, fun N hN => ?_⟩
  have hBN : B ≤ (ε / 2) * N := by
    have hceil : 2 * B / ε ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    rw [div_le_iff₀ hε] at hceil; linarith
  have hsBar : sBar N ≤ B + (ε / 2) * N :=
    Finset.sup'_le Finset.nonempty_range_add_one s fun m hm => by
      have hmN : (m : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      by_cases hm0 : m < N₀
      · linarith [Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_range.mpr hm0),
          show (0 : ℝ) ≤ (ε / 2) * N by positivity]
      · linarith [hN₀ m (not_lt.mp hm0), mul_le_mul_of_nonneg_left hmN (half_pos hε).le,
          Finset.sum_nonneg fun k (_ : k ∈ Finset.range N₀) => hnn k]
  rw [Real.norm_of_nonneg (hnnBar N), Real.norm_of_nonneg (Nat.cast_nonneg N)]
  linarith

end Cslib
