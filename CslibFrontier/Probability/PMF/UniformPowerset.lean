/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.Data.Finset.Powerset
import CslibFrontier.Probability.PMF.UniformSubset

/-!
# Uniform distributions over fixed-cardinality subsets (`powersetCard`)

Uniform sampling identities for `Finset.powersetCard` under `Cslib.Probability.PMF.uniformOfFinset`:

* `uniformOfFinset_powersetCard_erase`: drawing a uniform `t`-subset `U` of `S` (`1 ≤ t ≤ |S|`) and
  erasing a uniformly chosen element `e ∈ U` yields the uniform distribution on `(t - 1)`-subsets
  of `S`.
* `uniformOfFinset_powersetCard_hitOrErase`: for a fixed `p ∈ S` and `1 ≤ t ≤ |S|`, drawing a
  uniform `t`-subset `U` of `S` and returning `U.erase p` when `p ∈ U` or erasing a uniformly
  chosen element `e ∈ U` when `p ∉ U` yields the uniform distribution on `(t - 1)`-subsets of
  `S.erase p`.
* `toOuterMeasure_uniformOfFinset_powersetCard_notMem`: for `p ∈ S` and `t ≤ |S|`, a uniform
  `t`-subset of `S` misses `p` with probability `(|S| - t) / |S|`.

These identities underlie the stale-page cache distribution invariant of randomized marking
(`CslibFrontier.DataStructure.Paging.Marking`).
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

section PowersetCard

section WithDecidableEq

variable {α : Type*} [DecidableEq α]

/-- Helper step for erasing a uniform element from a subset `U`: returns `U.erase e` for a uniform
`e ∈ U` when `U` is nonempty, and `∅` on the unreachable empty case. -/
@[expose]
noncomputable def uniformErase (U : Finset α) : PMF (Finset α) :=
  if hU : U.Nonempty then
    (uniformOfFinset U hU).map fun e => U.erase e
  else
    PMF.pure ∅

private theorem uniformErase_apply_of_card {U V : Finset α} {t : ℕ} (ht : 1 ≤ t)
    (hcard : U.card = t) :
    uniformErase U V =
      if ∃ e ∈ U, U.erase e = V then (t : ℝ≥0∞)⁻¹ else 0 := by
  have hU : U.Nonempty := Finset.card_pos.mp (by omega)
  rw [uniformErase, dite_eq_left hU, PMF.map_apply]
  by_cases hex : ∃ e ∈ U, U.erase e = V
  · simp only [hex, ↓reduceIte]
    rcases hex with ⟨e₀, he₀U, he₀V⟩
    rw [tsum_eq_single e₀]
    · simp only [he₀V, ↓reduceIte, uniformOfFinset_apply, he₀U, hcard]
    · intro e he
      split_ifs with hV
      · by_cases heU : e ∈ U
        · have he_not_V : e ∉ V := hV ▸ Finset.notMem_erase e U
          have h := (Finset.insert_erase heU).trans (Finset.insert_erase he₀U).symm
          rw [← hV, he₀V] at h
          exact absurd ((Finset.insert_inj he_not_V).1 h) he
        · simp only [uniformOfFinset_apply, heU, ↓reduceIte]
      · rfl
  · simp only [hex, ↓reduceIte, tsum_eq_zero_iff]
    intro e
    by_cases heU : e ∈ U
    · have hne : V ≠ U.erase e := fun h => hex ⟨e, heU, h.symm⟩
      simp only [hne, ↓reduceIte]
    · simp only [uniformOfFinset_apply, heU, ↓reduceIte, ite_self]

/-- Characterization of the `t`-subsets `U` of `S` from which erasing one element yields a given
`(t - 1)`-subset `V ⊆ S`: they are precisely `insert e V` for `e ∈ S \ V`. -/
private theorem filter_powersetCard_exists_erase_eq {S V : Finset α} {t : ℕ}
    (hVS : V ⊆ S) (hVcard : V.card = t - 1) (ht : 1 ≤ t) :
    (S.powersetCard t).filter (fun U => ∃ e ∈ U, U.erase e = V) =
      (S \ V).image (fun e => insert e V) := by
  ext U
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hUS, _⟩, e, heU, rfl⟩
    exact ⟨e, ⟨hUS heU, Finset.notMem_erase e U⟩, Finset.insert_erase heU⟩
  · rintro ⟨e, ⟨heS, heV⟩, rfl⟩
    refine ⟨⟨Finset.insert_subset heS hVS, ?_⟩, e, Finset.mem_insert_self e V,
      Finset.erase_insert heV⟩
    rw [Finset.card_insert_of_notMem heV, hVcard]
    omega

private theorem card_image_insert_sdiff {S V : Finset α} (hVS : V ⊆ S) :
    ((S \ V).image (fun e => insert e V)).card = S.card - V.card := by
  rw [Finset.card_image_of_injOn, Finset.card_sdiff_of_subset hVS]
  exact fun e₁ he₁ e₂ _ hins => (Finset.insert_inj (Finset.mem_sdiff.mp he₁).2).1 hins

omit [DecidableEq α] in
private theorem uniformBind_apply {β : Type*} {A : Finset α} (hA : A.Nonempty)
    (f : α → PMF β) (b : β) :
    (uniformOfFinset A hA).bind f b = (A.card : ℝ≥0∞)⁻¹ * ∑ a ∈ A, f a b := by
  classical
  rw [PMF.bind_apply, tsum_eq_sum (s := A), Finset.mul_sum]
  · exact Finset.sum_congr rfl fun a ha => by rw [uniformOfFinset_apply, ite_eq_left ha]
  · intro a ha
    rw [uniformOfFinset_apply, ite_eq_right ha, zero_mul]

-- The only contributing subsets are the one-element extensions of the output.
private theorem sum_uniformErase (S V : Finset α) {t : ℕ} (ht : 1 ≤ t) :
    ∑ U ∈ S.powersetCard t, uniformErase U V =
      if V ∈ S.powersetCard (t - 1) then
        ((S.card - (t - 1) : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)⁻¹ else 0 := by
  have hsum : ∑ U ∈ S.powersetCard t, uniformErase U V =
      ∑ U ∈ (S.powersetCard t).filter (fun U => ∃ e ∈ U, U.erase e = V),
        (t : ℝ≥0∞)⁻¹ := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun U hU =>
      uniformErase_apply_of_card ht (Finset.mem_powersetCard.mp hU).2
  rw [hsum]
  split_ifs with hV
  · obtain ⟨hVS, hVcard⟩ := Finset.mem_powersetCard.mp hV
    rw [Finset.sum_const, filter_powersetCard_exists_erase_eq hVS hVcard ht,
      card_image_insert_sdiff hVS, hVcard, nsmul_eq_mul]
  · refine Finset.sum_eq_zero fun U hU => ?_
    obtain ⟨hU', e, he, rfl⟩ := Finset.mem_filter.mp hU
    obtain ⟨hUS, hUcard⟩ := Finset.mem_powersetCard.mp hU'
    exact (hV (Finset.mem_powersetCard.mpr ⟨(Finset.erase_subset e U).trans hUS,
      hUcard ▸ Finset.card_erase_of_mem he⟩)).elim

private theorem filter_powersetCard_notMem (S : Finset α) (p : α) (t : ℕ) :
    (S.powersetCard t).filter (p ∉ ·) = (S.erase p).powersetCard t := by
  ext U
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_erase]
  tauto

/-- Drawing a uniform `t`-subset `U` of `S` (`1 ≤ t ≤ |S|`) and erasing a uniformly chosen element
of `U` yields the uniform distribution on `(t - 1)`-subsets of `S`. -/
theorem uniformOfFinset_powersetCard_erase {S : Finset α} {t : ℕ}
    (ht : 1 ≤ t) (htS : t ≤ S.card) :
    (uniformOfFinset (S.powersetCard t) (Finset.powersetCard_nonempty.mpr htS)).bind uniformErase =
      uniformOfFinset (S.powersetCard (t - 1))
        (Finset.powersetCard_nonempty.mpr (by omega)) := by
  refine pmf_eq_uniformOfFinset_of_ite_const
    (Finset.powersetCard_nonempty.mpr (by lia))
    (c := ((S.powersetCard t).card : ℝ≥0∞)⁻¹ *
      (((S.card - (t - 1) : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)⁻¹)) fun V => ?_
  rw [uniformBind_apply, sum_uniformErase _ _ ht]
  split_ifs <;> simp

/-- For `p ∈ S` and `1 ≤ t ≤ |S|`, drawing a uniform `t`-subset `U` of `S` and returning
`U.erase p` when `p ∈ U` or `uniformErase U` when `p ∉ U` yields the uniform distribution on
`(t - 1)`-subsets of `S.erase p`. -/
theorem uniformOfFinset_powersetCard_hitOrErase {S : Finset α} {p : α} {t : ℕ}
    (hpS : p ∈ S) (ht : 1 ≤ t) (htS : t ≤ S.card) :
    (uniformOfFinset (S.powersetCard t) (Finset.powersetCard_nonempty.mpr htS)).bind
      (fun U => if p ∈ U then PMF.pure (U.erase p) else uniformErase U) =
      uniformOfFinset ((S.erase p).powersetCard (t - 1))
        (Finset.powersetCard_nonempty.mpr
          (by rw [Finset.card_erase_of_mem hpS]; omega)) := by
  refine pmf_eq_uniformOfFinset_of_ite_const _
    (c := ((S.powersetCard t).card : ℝ≥0∞)⁻¹ *
      (1 + ((((S.erase p).card - (t - 1) : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)⁻¹))) fun V => ?_
  rw [uniformBind_apply, ← Finset.sum_filter_add_sum_filter_not (S.powersetCard t) (p ∈ ·)]
  have hhit :
      ∑ U ∈ (S.powersetCard t).filter (p ∈ ·),
        (if p ∈ U then PMF.pure (U.erase p) else uniformErase U) V =
      ∑ U ∈ ((S.powersetCard t).filter (p ∈ ·)).filter (fun U => V = U.erase p), 1 := by
    rw [Finset.sum_filter (s := (S.powersetCard t).filter (p ∈ ·))]
    exact Finset.sum_congr rfl fun U hU => by
      rw [ite_eq_left (Finset.mem_filter.mp hU).2, PMF.pure_apply]
      by_cases hUV : V = U.erase p <;> simp [hUV]
  have hmiss :
      ∑ U ∈ (S.powersetCard t).filter (fun U => ¬p ∈ U),
        (if p ∈ U then PMF.pure (U.erase p) else uniformErase U) V =
      ∑ U ∈ (S.erase p).powersetCard t, uniformErase U V := by
    rw [← filter_powersetCard_notMem]
    exact Finset.sum_congr rfl fun U hU => by rw [ite_eq_right (Finset.mem_filter.mp hU).2]
  rw [hhit, hmiss, sum_uniformErase _ _ ht]
  split_ifs with hV
  · obtain ⟨hVsub, hVcard⟩ := Finset.mem_powersetCard.mp hV
    have hpV : p ∉ V := fun hp => Finset.notMem_erase p S (hVsub hp)
    have hhits : ((S.powersetCard t).filter (p ∈ ·)).filter (fun U => V = U.erase p) =
        {insert p V} := by
      ext U
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨_, _⟩, hpU⟩, rfl⟩
        exact (Finset.insert_erase hpU).symm
      · rintro rfl
        refine ⟨⟨⟨Finset.insert_subset hpS (hVsub.trans (Finset.erase_subset p S)), ?_⟩,
          Finset.mem_insert_self p V⟩, (Finset.erase_insert hpV).symm⟩
        rw [Finset.card_insert_of_notMem hpV, hVcard]
        lia
    rw [hhits, Finset.sum_singleton]
  · suffices ∑ U ∈ ((S.powersetCard t).filter (p ∈ ·)).filter (fun U => V = U.erase p),
        (1 : ℝ≥0∞) = 0 by simp [this]
    refine Finset.sum_eq_zero fun U hU => ?_
    obtain ⟨⟨hU', hpU⟩, rfl⟩ := by simpa only [Finset.mem_filter] using hU
    obtain ⟨hUS, hUcard⟩ := Finset.mem_powersetCard.mp hU'
    exact (hV (Finset.mem_powersetCard.mpr ⟨Finset.erase_subset_erase p hUS,
      hUcard ▸ Finset.card_erase_of_mem hpU⟩)).elim

end WithDecidableEq

/-- A uniform `t`-subset of `S` (`t ≤ |S|`) misses a fixed element `p ∈ S` with probability
`(|S| - t) / |S|`. -/
theorem toOuterMeasure_uniformOfFinset_powersetCard_notMem {α : Type*} {S : Finset α} {p : α}
    {t : ℕ} (hpS : p ∈ S) (htS : t ≤ S.card) :
    (uniformOfFinset (S.powersetCard t)
      (Finset.powersetCard_nonempty.mpr htS)).toOuterMeasure {U | p ∉ U} =
      ((S.card - t : ℕ) : ℝ≥0∞) * (S.card : ℝ≥0∞)⁻¹ := by
  classical
  rw [toOuterMeasure_uniformOfFinset]
  change ((((S.powersetCard t).filter (p ∉ ·)).card : ℕ) : ℝ≥0∞) * _ = _
  rw [filter_powersetCard_notMem, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_erase_of_mem hpS]
  have hS_pos : 1 ≤ S.card := Finset.card_pos.mpr ⟨p, hpS⟩
  have hchoose_nat :
      (S.card - 1).choose t * S.card = S.card.choose t * (S.card - t) := by
    simpa [Nat.sub_add_cancel hS_pos] using Nat.choose_mul_succ_eq (S.card - 1) t
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, ENNReal.div_eq_div_iff
    (Nat.cast_ne_zero.mpr (by omega)) (ENNReal.natCast_ne_top _)
    (Nat.cast_ne_zero.mpr (Nat.choose_pos htS).ne') (ENNReal.natCast_ne_top _), mul_comm]
  exact_mod_cast hchoose_nat

end PowersetCard

end Cslib.Probability.PMF
