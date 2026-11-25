/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Unique
public import Mathlib.Algebra.Order.Ring.Rat
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.AffineLift
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.AffineReduce
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.Internal
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.UniqueCurve
import Mathlib.Data.Fintype.Pi

/-!
# Sharp Unique-Decoding Affine-Space Correlated Agreement and Dichotomies

Unweighted eq. (1.2) affine correlated agreement with uniqueness and maximality
(`exists_uniqueMaximal_correlatedAgreement_affine_unique`), plus the sharp `ℕ`- and `ℚ`-weighted
unique-decoding affine correlated agreement and proximity-gap dichotomies (`*_affine_unique_sharp`).

## Main results

* `Cslib.Code.exists_uniqueMaximal_correlatedAgreement_affine_unique`: unique maximal shared
  agreement subset under `|ι| * |F| ^ ℓ < |F| * #T`.
* `Cslib.Code.exists_weighted_correlatedAgreement_affine_unique_sharp`,
  `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_unique_sharp`: sharp weighted affine
  correlated agreement.
* `Cslib.Code.weighted_proximityGap_affine_unique_sharp`,
  `Cslib.Code.ratWeighted_proximityGap_affine_unique_sharp`: sharp weighted affine dichotomies.
-/

public section

namespace Cslib.Code

open scoped BigOperators
open Finset Polynomial

/-- Private helper: a nonzero affine linear functional on `Fin ℓ → F` vanishes on at most
`|F| ^ (ℓ - 1)` points. -/
private theorem card_zero_affine_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ℓ : ℕ}
    (a₀ : F) (a : Fin ℓ → F)
    (hne : a₀ ≠ 0 ∨ ∃ j : Fin ℓ, a j ≠ 0) :
    (Finset.univ.filter fun z : Fin ℓ → F => a₀ + ∑ j : Fin ℓ, z j * a j = 0).card ≤
      (Fintype.card F) ^ (ℓ - 1) := by
  classical
  set S := Finset.univ.filter fun z : Fin ℓ → F => a₀ + ∑ j : Fin ℓ, z j * a j = 0
  by_cases hall0 : ∀ j : Fin ℓ, a j = 0
  · have ha₀ := hne.resolve_right (by push Not; exact hall0)
    have hemp : S = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun z hz =>
      ha₀ <| by simpa [hall0] using (mem_filter.1 hz).2
    simp [hemp]
  · push Not at hall0; obtain ⟨j₀, hj₀⟩ := hall0
    let proj : (Fin ℓ → F) → ({j : Fin ℓ // j ≠ j₀} → F) := fun z j => z j.1
    have hinj : Set.InjOn proj (S : Set (Fin ℓ → F)) := fun z₁ hz₁ z₂ hz₂ hproj => by
      have hne_eq : ∀ j : Fin ℓ, j ≠ j₀ → z₁ j = z₂ j := fun j hj => congrFun hproj ⟨j, hj⟩
      have h1 := (mem_filter.1 hz₁).2; have h2 := (mem_filter.1 hz₂).2
      rw [← Finset.add_sum_erase _ _ (mem_univ j₀)] at h1 h2
      have hsum : ∑ j ∈ Finset.univ.erase j₀, z₁ j * a j =
          ∑ j ∈ Finset.univ.erase j₀, z₂ j * a j :=
        Finset.sum_congr rfl fun j hj => by rw [hne_eq j (mem_erase.1 hj).1]
      have hz₀ : z₁ j₀ = z₂ j₀ := by
        rw [hsum] at h1
        exact mul_right_cancel₀ hj₀ (add_right_cancel (add_left_cancel (h1.trans h2.symm)))
      exact funext fun j => if hj : j = j₀ then hj ▸ hz₀ else hne_eq j hj
    have hcard_sub : Fintype.card {j : Fin ℓ // j ≠ j₀} = ℓ - 1 := by
      simpa only [Fintype.card_fin, Fintype.card_unique] using
        Fintype.card_subtype_compl (fun j : Fin ℓ => j = j₀)
    exact (Finset.card_image_of_injOn hinj).symm ▸ (Finset.card_le_univ _).trans_eq (by
      rw [Fintype.card_fun, hcard_sub])

/-- Private helper: the parameters `z` at which some disagreeing coordinate `i ∈ badI` of two
affine spaces collides lie in a union of nonzero affine zero sets, so there are at most
`|ι| · |F| ^ (ℓ - 1)` of them. -/
private theorem card_biUnion_zero_affine_le
    {ι F : Type*} [Fintype ι] [Field F] [Fintype F] [DecidableEq F] {ℓ : ℕ}
    (u₀ v₀ : ι → F) (u v : Fin ℓ → ι → F) (badI : Finset ι)
    (hbad : ∀ i ∈ badI, ¬ (u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i)) :
    (badI.biUnion fun i => Finset.univ.filter fun z : Fin ℓ → F =>
        (u₀ i - v₀ i) + ∑ j : Fin ℓ, z j * (u j i - v j i) = 0).card ≤
      Fintype.card ι * (Fintype.card F) ^ (ℓ - 1) := by
  refine card_biUnion_le.trans <| (sum_le_sum fun i hi => card_zero_affine_le _ _ <| by
    simpa only [ne_eq, sub_eq_zero, not_and_or, not_forall] using hbad i hi).trans ?_
  rw [sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (card_le_univ badI)

/-- **Exact-threshold correlated agreement on affine spaces in the unique-decoding regime, with
unique maximal agreement set and unique codewords**
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.6 & Section 6.3], accepted JACM 2023 manuscript
p. 6 and pp. 28–31, eq. (1.2)).

Over a finite field `F`, given distinct evaluation points `α : ι → F`, `2 * e + k ≤ |ι|`, and an
affine space `u₀ + ∑ j : Fin ℓ, z j • u j`, if `|ι| * |F| ^ ℓ < |F| * #T` (exact density threshold
`#T / |F| ^ ℓ > |ι| / |F| = ε_U` of eq. (1.2), completely independent of `ℓ`) and every `z ∈ T`
lies within Hamming distance `e` of `reedSolomon α k`, then there exist a greatest (hence unique
maximal) shared coordinate subset `D' : Finset ι` of size at least `|ι| - e` and unique codewords
`v₀, v j ∈ reedSolomon α k` matching `u₀, u j` on `D'`: every qualifying `(D'', w₀, w)` satisfies
`D'' ⊆ D'`, `w₀ = v₀`, and `w = v`. -/
theorem exists_uniqueMaximal_correlatedAgreement_affine_unique
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {e k ℓ : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : Fintype.card ι * (Fintype.card F) ^ ℓ < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F),
        (∀ j, v j ∈ reedSolomon α k) ∧
        (∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i) ∧
        ∀ (D'' : Finset ι) (w₀ : ι → F) (w : Fin ℓ → (ι → F)),
          Fintype.card ι - e ≤ D''.card →
          w₀ ∈ reedSolomon α k → (∀ j, w j ∈ reedSolomon α k) →
          (∀ i ∈ D'', u₀ i = w₀ i ∧ ∀ j, u j i = w j i) →
          D'' ⊆ D' ∧ w₀ = v₀ ∧ w = v := by
  classical
  have hlist (w : ι → F) : ∃ Lset : Finset (ι → F), Lset.card ≤ 1 ∧
      ∀ c ∈ reedSolomon α k, Fintype.card ι - e ≤
        ∑ i ∈ Finset.univ.filter (fun i => w i = c i), (1 : ℕ) → c ∈ Lset := by
    by_cases hex : ∃ c ∈ reedSolomon α k, hammingDist w c ≤ e
    · exact ⟨{hex.choose}, by simp, fun c hc hs => mem_singleton.2 <|
        eq_of_hammingDist_le_reedSolomon hα hunique hc hex.choose_spec.1
          (hammingDist_le_of_card_filter_eq (by simpa using hs)) hex.choose_spec.2⟩
    · exact ⟨∅, Nat.zero_le 1, fun c hc hs =>
        absurd ⟨c, hc, hammingDist_le_of_card_filter_eq (by simpa using hs)⟩ hex⟩
  have hline : ∀ {B' : ℕ}, Fintype.card ι - e ≤ B' → ∀ (a b : ι → F) (S : Finset F),
      Fintype.card ι < S.card →
      (∀ t ∈ S, ∃ c ∈ reedSolomon α k,
        B' ≤ ∑ i ∈ Finset.univ.filter (fun i => (a + t • b) i = c i), (1 : ℕ)) →
      ∃ D' : Finset ι, B' ≤ ∑ i ∈ D', (1 : ℕ) ∧ ∃ w₀ ∈ reedSolomon α k,
        ∃ w₁ ∈ reedSolomon α k, ∀ i ∈ D', a i = w₀ i ∧ b i = w₁ i := fun {B'} hB' a b S hS hcl => by
    obtain ⟨t₀, ht₀⟩ := Finset.card_pos.1 (Nat.zero_lt_of_lt hS)
    have hB'_le : B' ≤ Fintype.card ι := let ⟨_, _, hs⟩ := hcl t₀ ht₀
      (by simpa using hs : B' ≤ _).trans (Finset.card_le_univ _)
    have hsub : Fintype.card ι - (Fintype.card ι - B') = B' := by omega
    obtain ⟨D', hD', w₀, hw₀, w₁, hw₁, hag⟩ := exists_correlatedAgreement_unique hα
      (by omega : 2 * (Fintype.card ι - B') + k ≤ Fintype.card ι) a b S hS
      fun t ht => let ⟨c, hc, hs⟩ := hcl t ht
        ⟨c, hc, hammingDist_le_of_card_filter_eq (hsub.symm ▸ by simpa using hs)⟩
    exact ⟨D', by simpa only [Finset.sum_const, smul_eq_mul, mul_one, hsub] using hD',
      w₀, hw₀, w₁, hw₁, hag⟩
  obtain ⟨D₀, _, hD₀_sum, v₀, hv₀, v, hv, hag₀⟩ :=
    exists_weighted_correlatedAgreement_affine_of_line (C := reedSolomon α k) (W := fun _ => 1)
      (B_W := Fintype.card ι - e) (B_line := Fintype.card ι) (L := 1) hlist hline
      (fun _ => Fintype.one_lt_card) u₀ u T hT fun z hz => let ⟨c, hc, hd⟩ := hclose z hz
        ⟨c, hc, by simpa using card_filter_eq_of_hammingDist_le hd⟩
  obtain ⟨D', hD', v', hv'RS, hagree', hmax'⟩ := exists_uniqueMaximal_correlatedAgreement_of_exists
    hα hunique (u := Fin.cons (α := fun _ => ι → F) u₀ u)
    ⟨D₀, by simpa using hD₀_sum, Fin.cons v₀ v, Fin.cases hv₀ hv,
      fun i hi => Fin.cases (hag₀ i hi).1 (hag₀ i hi).2⟩
  exact ⟨D', hD', v' 0, hv'RS 0, fun j => v' j.succ, fun j => hv'RS j.succ,
    fun i hi => ⟨hagree' i hi 0, fun j => hagree' i hi j.succ⟩,
    fun D'' w₀ w hD'' hw₀ hw hag'' =>
      let ⟨hsub, hweq⟩ := hmax' D'' (Fin.cons w₀ w) hD'' (Fin.cases hw₀ hw)
        fun i hi => Fin.cases (hag'' i hi).1 (hag'' i hi).2
      ⟨hsub, congrFun hweq 0, funext fun j => congrFun hweq j.succ⟩⟩

/-- **Dimension-independent `ℚ`-weighted correlated agreement on affine spaces in the
unique-decoding regime** ([BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4]):
At threshold `|ι| * (|F| ^ ℓ - 1) < (|F| - 1) * #T` (completely independent of `ℓ` and weight
denominators), any weight function `μ : ι → ℚ` with `∀ i, μ i ≤ 1` admits shared correlated
agreement `θ ≤ ∑ i ∈ D', μ i`. Handles the one-point `ℓ = 0` case explicitly (including
`|ι| = |F|`), and for `ℓ ≥ 1` delegates the unweighted step to
`Cslib.Code.exists_uniqueMaximal_correlatedAgreement_affine_unique`. -/
theorem exists_ratWeighted_correlatedAgreement_affine_unique_sharp
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {e k ℓ : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : Fintype.card ι * ((Fintype.card F) ^ ℓ - 1) < (Fintype.card F - 1) * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F),
        (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  classical
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · have hpos : 0 < T.card := Nat.pos_of_mul_pos_left
      (by simpa only [pow_zero, tsub_self, mul_zero] using hT)
    obtain ⟨z₀, hz₀⟩ := Finset.card_pos.1 hpos
    obtain ⟨c, hcRS, hμ_ge⟩ := hclose z₀ hz₀
    exact ⟨Finset.univ.filter fun i => u₀ i = c i,
      by simpa only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] using hμ_ge, c, hcRS,
      Fin.elim0, fun j => j.elim0, fun _ hi => ⟨(mem_filter.1 hi).2, fun j => j.elim0⟩⟩
  · have hq_gt1 : 1 < Fintype.card F := Fintype.one_lt_card
    have hpow_pos : 1 ≤ (Fintype.card F) ^ ℓ := Nat.one_le_pow ℓ _ Fintype.card_pos
    have hcard_lt : Fintype.card ι < T.card := Nat.lt_of_mul_lt_mul_right <|
      ((Nat.mul_le_mul_left _ (Nat.sub_le_sub_right
        (Nat.le_self_pow (by omega : ℓ ≠ 0) (Fintype.card F)) 1)).trans_lt hT).trans_eq
        (Nat.mul_comm _ _)
    have hT_exact : Fintype.card ι * (Fintype.card F) ^ ℓ < Fintype.card F * T.card := by
      have := Nat.le_mul_of_pos_right (Fintype.card ι) hpow_pos
      have := Nat.le_mul_of_pos_left T.card (by omega : 0 < Fintype.card F)
      rw [Nat.mul_sub_one, Nat.sub_one_mul] at hT
      omega
    obtain ⟨D₀, hD₀, v₀, hv₀, v, hvRS, hagree₀, _⟩ :=
      exists_uniqueMaximal_correlatedAgreement_affine_unique hα hunique u₀ u T hT_exact
        fun z hz => let ⟨c, hcRS, hμ_ge⟩ := hclose z hz
          ⟨c, hcRS, hammingDist_le_of_ratWeightedAgree_ge hμ_le hθ hμ_ge⟩
    let D' := Finset.univ.filter fun i => u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i
    refine ⟨D', ?_, v₀, hv₀, v, hvRS, fun _ hi => (mem_filter.1 hi).2⟩
    by_contra hlt_θ; push Not at hlt_θ
    let badI : Finset ι := Finset.univ.filter fun i => ¬ (u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i)
    have hT_sub : T ⊆ badI.biUnion fun i => Finset.univ.filter fun z : Fin ℓ → F =>
        (u₀ i - v₀ i) + ∑ j : Fin ℓ, z j * (u j i - v j i) = 0 := by
      intro z hz
      obtain ⟨c, hcRS, hμ_ge⟩ := hclose z hz
      let vz : ι → F := v₀ + ∑ j : Fin ℓ, z j • v j
      have hceq : c = vz := eq_of_hammingDist_le_reedSolomon hα hunique hcRS
        (Submodule.add_mem _ hv₀ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvRS j)))
        (hammingDist_le_of_ratWeightedAgree_ge hμ_le hθ hμ_ge)
        (hammingDist_affine_le_of_eq_on hD₀ hagree₀ z)
      subst hceq
      have hD'_sub : D' ⊆ Finset.univ.filter fun i => (u₀ + ∑ j : Fin ℓ, z j • u j) i = vz i :=
        subset_filter_affine_eq (fun _ hi => (mem_filter.1 hi).2) z
      have hex : ∃ i ∈ Finset.univ.filter (fun i => (u₀ + ∑ j : Fin ℓ, z j • u j) i = vz i),
          i ∉ D' := by
        by_contra hnone; push Not at hnone
        rw [Finset.Subset.antisymm hD'_sub hnone] at hlt_θ
        exact absurd hμ_ge (not_le.2 hlt_θ)
      obtain ⟨i, hi_ag, hi_not⟩ := hex
      refine mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_univ i, fun h =>
        hi_not (mem_filter.2 ⟨mem_univ i, h⟩)⟩, mem_filter.2 ⟨mem_univ z, ?_⟩⟩
      have heq := (mem_filter.1 hi_ag).2
      simp only [vz, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heq
      simp only [mul_sub, sum_sub_distrib]
      rw [← sub_eq_zero.2 heq]
      ring
    have hT_le := (Finset.card_le_card hT_sub).trans <|
      card_biUnion_zero_affine_le u₀ v₀ u v badI fun _ hi => (mem_filter.1 hi).2
    have hmul_le := (Nat.mul_le_mul_left (Fintype.card F) hT_le).trans_eq (by
      rw [← mul_assoc, mul_comm (Fintype.card F) (Fintype.card ι), mul_assoc, ← pow_succ',
        Nat.sub_add_cancel hℓ])
    omega

/-- **Dimension-independent `ℕ`-weighted correlated agreement on affine spaces in the
unique-decoding regime** ([BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4]). -/
theorem exists_weighted_correlatedAgreement_affine_unique_sharp
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ M B : ℕ} (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hunique : 2 * (Fintype.card ι - (B + M - 1) / M) + k ≤ Fintype.card ι)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : Fintype.card ι * ((Fintype.card F) ^ ℓ - 1) < (Fintype.card F - 1) * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) :
    ∃ D' : Finset ι, B ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F),
        (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ :=
    exists_ratWeighted_correlatedAgreement_affine_unique_sharp hα hunique
      (fun i => (div_le_one (Nat.cast_pos.2 hM)).2 (Nat.cast_le.2 (hW i)))
      (card_sub_sub_ceilDiv_sub_one_lt hM) u₀ u T hT fun z hz =>
        let ⟨c, hcRS, hW_ge⟩ := hclose z hz; ⟨c, hcRS, (nat_le_sum_iff_div hM _).1 hW_ge⟩
  exact ⟨D', (nat_le_sum_iff_div hM D').2 hD', v₀, hv₀, v, hvRS, hagree⟩

/-- **Dimension-independent `ℕ`-weighted proximity-gap dichotomy on affine spaces in the
unique-decoding regime** ([BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4]). -/
theorem weighted_proximityGap_affine_unique_sharp
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ M B : ℕ} (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hunique : 2 * (Fintype.card ι - (B + M - 1) / M) + k ≤ Fintype.card ι)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) ∨
      (Fintype.card F - 1) *
        (Finset.univ.filter fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
          B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
            (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i).card ≤
        Fintype.card ι * ((Fintype.card F) ^ ℓ - 1) :=
  proximityGap_affine_of_line
    (P := fun w => ∃ c ∈ reedSolomon α k, B ≤ ∑ i ∈ univ.filter (fun i => w i = c i), W i)
    (B_line := Fintype.card ι)
    (fun a b S hS hcl t =>
      let ⟨_, hD', w₀, hw₀, w₁, hw₁, hag⟩ :=
        exists_weighted_correlatedAgreement_unique hα hM hW hunique a b S hS hcl
      ⟨w₀ + t • w₁, Submodule.add_mem _ hw₀ (Submodule.smul_mem _ t hw₁),
        hD'.trans (Finset.sum_le_sum_of_subset (subset_filter_line_eq hag t))⟩) u₀ u

/-- **Dimension-independent `ℚ`-weighted proximity-gap dichotomy on affine spaces in the
unique-decoding regime** (`ℚ`-weights in `[0, 1]`,
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4]). -/
theorem ratWeighted_proximityGap_affine_unique_sharp
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {e k ℓ : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {μ : ι → ℚ} (hμ_nonneg : ∀ i, 0 ≤ μ i) (hμ_le : ∀ i, μ i ≤ 1)
    {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) ∨
      (Fintype.card F - 1) *
        (Finset.univ.filter fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
          θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
            (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i).card ≤
        Fintype.card ι * ((Fintype.card F) ^ ℓ - 1) :=
  proximityGap_affine_of_line
    (P := fun w => ∃ c ∈ reedSolomon α k, θ ≤ ∑ i ∈ univ.filter (fun i => w i = c i), μ i)
    (B_line := Fintype.card ι)
    (fun a b S hS hcl t =>
      let ⟨_, hD', w₀, hw₀, w₁, hw₁, hag⟩ :=
        exists_ratWeighted_correlatedAgreement_unique hα hunique hμ_le hθ a b S hS hcl
      ⟨w₀ + t • w₁, Submodule.add_mem _ hw₀ (Submodule.smul_mem _ t hw₁),
        hD'.trans (Finset.sum_le_sum_of_subset_of_nonneg (subset_filter_line_eq hag t)
          fun i _ _ => hμ_nonneg i)⟩) u₀ u

end Cslib.Code
