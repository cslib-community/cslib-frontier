/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: vendored SamuelSchlesinger:feat/pac-learning-ehkv-headline @a9fb889df4 (unsubmitted)

public import CslibFrontier.MachineLearning.PACLearning.SampleComplexityLower.Helpers

/-! # Involution Pairing Argument

The combinatorial core of the EHKV lower bound proof. For each "bad" sample
(one that reveals at most half the shattered set), an involution on
`2^d` concepts pairs each concept with its complement on the unseen
points. At least one concept per pair forces large error.

## Main statements

- `involution_half_count`: an involution where every pair has a "failing"
  element implies at least half the elements fail.
- `concepts_agree_of_seen_inter`: two concepts agreeing on seen elements yield the
  same labeled sample.
- `unseen_measure_ge`: the measure of the unseen set is at least `4ε'`.
- `complementary_error_contradiction`: two complementary errors can't
  both be `≤ ε`.

## References

* [A. Ehrenfeucht, D. Haussler, M. Kearns, L. Valiant,
  *A General Lower Bound on the Number of Examples Needed
  for Learning*][EHKV1989]
-/

-- vendored: plain `public section`; the section exposes no definition (local changed-file lint).
public section

open MeasureTheory Set Finset
open scoped ENNReal

noncomputable section

namespace Cslib.MachineLearning.PACLearning

section InvolutionPairing

variable {α : Type*}

open Classical in
/-- If `σ` is an involution on a finset `F` that maps `F` into itself, and
every element is paired with a "failing" partner (i.e., `P x ∨ P (σ x)`),
then at least half the elements satisfy `P`. -/
theorem involution_half_count {ι : Type*}
    {F : Finset ι} {σ : ι → ι}
    (hσ_self : ∀ x ∈ F, σ (σ x) = x)
    (hσ_mem : ∀ x ∈ F, σ x ∈ F)
    {P : ι → Prop}
    (hpair : ∀ x ∈ F, P x ∨ P (σ x)) :
    F.card / 2 ≤ (F.filter P).card := by
  set G := F \ F.filter P
  have hG_sub : G ⊆ F := sdiff_subset
  have hσ_G_to_F : ∀ x ∈ G, σ x ∈ F.filter P := fun x hxG => by
    obtain ⟨hxF, hx_nF⟩ := Finset.mem_sdiff.mp hxG
    exact Finset.mem_filter.mpr ⟨hσ_mem x hxF,
      (hpair x hxF).resolve_left fun hp => hx_nF (Finset.mem_filter.mpr ⟨hxF, hp⟩)⟩
  have hσ_inj_G : Set.InjOn σ (G : Set ι) := by
    intro x₁ hx₁ x₂ hx₂ hσeq
    calc x₁ = σ (σ x₁) := (hσ_self x₁ (hG_sub hx₁)).symm
      _ = σ (σ x₂) := by rw [hσeq]
      _ = x₂ := hσ_self x₂ (hG_sub hx₂)
  have hcard : G.card ≤ (F.filter P).card :=
    (card_image_of_injOn hσ_inj_G) ▸
      card_le_card (fun S hS => let ⟨_, hG, heq⟩ := Finset.mem_image.mp hS; heq ▸ hσ_G_to_F _ hG)
  have hpow_eq : G.card + (F.filter P).card = F.card :=
    card_sdiff_add_card_eq_card (filter_subset _ _)
  omega

open Classical in
/-- Two `cMap` concepts agree on all sample points when their underlying subsets
have the same intersection with the seen elements `T = seenElements W' xs`. -/
theorem concepts_agree_of_seen_inter
    {W W' : Finset α} {w₀ : α}
    {m : ℕ} {xs : Fin m → α}
    (cMap : (S : Finset α) → S ∈ W'.powerset → Set α)
    (hcMap_eq : ∀ S (hS : S ∈ W'.powerset), cMap S hS ∩ ↑W = {w₀} ∪ ↑S)
    {S₁ S₂ : Finset α}
    (hS₁ : S₁ ∈ W'.powerset) (hS₂ : S₂ ∈ W'.powerset)
    (hinter : S₁ ∩ seenElements W' xs = S₂ ∩ seenElements W' xs)
    (hxs : ∀ i, xs i ∈ (↑W : Set α)) :
    ∀ i, xs i ∈ cMap S₁ hS₁ ↔ xs i ∈ cMap S₂ hS₂ := by
  intro i
  have hmem (S : Finset α) (hS : S ∈ W'.powerset) :
      xs i ∈ cMap S hS ↔ xs i = w₀ ∨ xs i ∈ S ∩ seenElements W' xs := by
    have hc : xs i ∈ cMap S hS ↔ xs i ∈ ({w₀} ∪ ↑S : Set α) := by
      rw [← hcMap_eq S hS]
      exact ⟨fun h => ⟨h, hxs i⟩, And.left⟩
    rw [hc, Set.mem_union, Set.mem_singleton_iff, mem_coe]
    exact or_congr_right ⟨fun hxS => Finset.mem_inter.mpr
        ⟨hxS, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mp hS hxS, i, rfl⟩⟩,
      fun hx => (Finset.mem_inter.mp hx).1⟩
  rw [hmem S₁ hS₁, hmem S₂ hS₂, hinter]

variable [MeasurableSpace α]

/-- The measure of an unseen set `U` is at least `4ε'` when each point has measure
`8ε'/d` and `|U| ≥ d/2`. -/
theorem unseen_measure_ge [MeasurableSingletonClass α]
    {U : Finset α} {d : ℕ} {ε' : ℝ} {P : Measure α}
    (hε'_pos : 0 < ε') (hd_pos : 0 < d) (h2U : d ≤ 2 * U.card)
    (hP_each : ∀ w ∈ U, P {w} = ENNReal.ofReal (8 * ε' / ↑d)) :
    ENNReal.ofReal (4 * ε') ≤ P (↑U) := by
  have hU_eq : (↑U : Set α) = ⋃ w ∈ U, ({w} : Set α) := by ext x; simp
  rw [hU_eq, measure_biUnion_finset
    (fun w _ w' _ hww' => Set.disjoint_singleton.mpr hww')
    (fun w _ => MeasurableSet.singleton w)]
  rw [Finset.sum_congr rfl hP_each, Finset.sum_const, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast (n := U.card),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hd_cast : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
  calc 4 * ε' = (d : ℝ) / 2 * (8 * ε' / d) := by field_simp; ring
    _ ≤ (U.card : ℝ) * (8 * ε' / d) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith [show (d : ℝ) ≤ 2 * (U.card : ℝ) from by exact_mod_cast h2U]

/-- If two sets' symmetric differences with a hypothesis cover a set of measure `≥ 4ε'`,
but each symmetric difference has measure `≤ ε'`, we derive a contradiction. -/
theorem complementary_error_contradiction {P : Measure α} {h c₁ c₂ : Set α}
    {U : Set α} {ε' : ℝ} (hε'_pos : 0 < ε')
    (hU_sub : U ⊆ symmDiff h c₁ ∪ symmDiff h c₂)
    (hP_U : ENNReal.ofReal (4 * ε') ≤ P U)
    (herr₁ : P (symmDiff h c₁) ≤ ENNReal.ofReal ε')
    (herr₂ : P (symmDiff h c₂) ≤ ENNReal.ofReal ε') : False := by
  have h_contra : ENNReal.ofReal (4 * ε') ≤ ENNReal.ofReal (2 * ε') :=
    calc ENNReal.ofReal (4 * ε')
        ≤ P U := hP_U
      _ ≤ P (symmDiff h c₁ ∪ symmDiff h c₂) := measure_mono hU_sub
      _ ≤ P (symmDiff h c₁) + P (symmDiff h c₂) := measure_union_le _ _
      _ ≤ ENNReal.ofReal ε' + ENNReal.ofReal ε' := add_le_add herr₁ herr₂
      _ = ENNReal.ofReal (2 * ε') := by
          rw [← ENNReal.ofReal_add hε'_pos.le hε'_pos.le]; ring_nf
  rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at h_contra
  linarith

end InvolutionPairing

end Cslib.MachineLearning.PACLearning
