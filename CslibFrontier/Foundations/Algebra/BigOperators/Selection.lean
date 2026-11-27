/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# The largest weights beat every fractional selection

For real weights `w` on a finite type and a fractional selection `0 ≤ c ≤ 1` of total mass
`∑ c = d`, some set `S` of exactly `d` elements has `∑ w c ≤ ∑_{i ∈ S} w`
(`Finset.exists_card_eq_sum_mul_le`). Take `S` maximizing `∑_S w` among the `d`-sets: every weight
outside `S` is at most every weight inside, by exchange, and a threshold between them bounds the
difference. Equivalently, a linear function on the hypersimplex `{c ∈ [0,1]ⁿ | ∑ c = d}` attains its
maximum at a `0/1` vertex.

## Main results

* `Finset.exists_card_eq_sum_mul_le`: the `d` largest weights beat every fractional selection of
  mass `d`.
-/

public section

open Finset

namespace Finset

/-- The `d` largest weights beat every fractional selection of total mass `d`. -/
theorem exists_card_eq_sum_mul_le {N : Type*} [Fintype N] (w c : N → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) {d : ℕ} (hd : ∑ i, c i = d) :
    ∃ S : Finset N, S.card = d ∧ ∑ i, w i * c i ≤ ∑ i ∈ S, w i := by
  classical
  have hdN : d ≤ Fintype.card N := by
    have : (d : ℝ) ≤ Fintype.card N := by
      rw [← hd]
      calc ∑ i, c i ≤ ∑ _i : N, (1 : ℝ) := sum_le_sum fun i _ => hc1 i
        _ = Fintype.card N := by simp
    exact_mod_cast this
  have hne : (powersetCard d (univ : Finset N)).Nonempty :=
    powersetCard_nonempty.mpr (by simpa using hdN)
  obtain ⟨S, hS, hmax⟩ := exists_max_image _ (fun S => ∑ i ∈ S, w i) hne
  have hcard : S.card = d := (mem_powersetCard.mp hS).2
  refine ⟨S, hcard, ?_⟩
  -- Exchange: every weight outside `S` is at most every weight inside.
  have hex : ∀ s ∈ S, ∀ t ∉ S, w t ≤ w s := by
    intro s hs t ht
    by_contra hlt
    rw [not_le] at hlt
    have hmem : insert t (S.erase s) ∈ powersetCard d (univ : Finset N) := by
      refine mem_powersetCard.mpr ⟨subset_univ _, ?_⟩
      rw [card_insert_of_notMem (fun h => ht (mem_of_mem_erase h)), card_erase_of_mem hs, hcard]
      have : 0 < d := hcard ▸ card_pos.mpr ⟨s, hs⟩
      omega
    have := hmax _ hmem
    rw [sum_insert (fun h => ht (mem_of_mem_erase h)), ← add_sum_erase S w hs] at this
    linarith
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · -- `d = 0`, so all `c i = 0`.
    subst hS0
    have hd0 : d = 0 := by simpa using hcard.symm
    have hc : ∀ i, c i = 0 := fun i =>
      (sum_eq_zero_iff_of_nonneg fun i _ => hc0 i).mp (by rw [hd, hd0]; simp) i (mem_univ i)
    simp [hc]
  · set τ := S.inf' hSne w
    have hin : ∀ s ∈ S, τ ≤ w s := fun s hs => inf'_le _ hs
    have hout : ∀ t ∉ S, w t ≤ τ := fun t ht => (le_inf'_iff _ _).mpr fun s hs => hex s hs t ht
    have hsplit : ∑ i, w i * c i = ∑ i ∈ S, w i * c i + ∑ i ∈ univ \ S, w i * c i := by
      rw [add_comm, sum_sdiff (subset_univ S)]
    have hcsplit : ∑ i ∈ S, c i + ∑ i ∈ univ \ S, c i = d := by
      rw [add_comm, sum_sdiff (subset_univ S), hd]
    have h₁ : ∑ i ∈ univ \ S, w i * c i ≤ ∑ i ∈ univ \ S, τ * c i :=
      sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hout i (mem_sdiff.mp hi).2) (hc0 i)
    have h₂ : ∑ i ∈ S, τ * (1 - c i) ≤ ∑ i ∈ S, w i * (1 - c i) :=
      sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hin i hi) (sub_nonneg.mpr (hc1 i))
    have h₃ : ∑ i ∈ S, (1 - c i) = d - ∑ i ∈ S, c i := by
      rw [sum_sub_distrib]; simp [hcard]
    rw [← mul_sum] at h₁ h₂
    rw [h₃] at h₂
    have h₄ : ∑ i ∈ S, w i * (1 - c i) = ∑ i ∈ S, w i - ∑ i ∈ S, w i * c i := by
      rw [← sum_sub_distrib]; simp [mul_sub]
    rw [h₄] at h₂
    have : ∑ i ∈ univ \ S, c i = d - ∑ i ∈ S, c i := by linarith
    rw [this] at h₁
    linarith

end Finset
