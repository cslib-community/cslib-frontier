/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson
public import Mathlib.Algebra.Order.Ring.Rat
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.Internal
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.JohnsonHelpers
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.UniqueCurve
import Mathlib.Tactic.Positivity

/-!
# Johnson-Bound Parameterized Curve and Line Proximity Gaps

Original explicit-constant unweighted, `ℕ`-weighted, and `ℚ`-weighted curve proximity gaps and
correlated-agreement endpoints up to the Johnson bound `1 - √ρ - η`.

## Main results

* `Cslib.Code.proximityGap_curve_johnson`, `Cslib.Code.proximityGap_curve_johnson_of_eta`:
  unweighted curve proximity gaps.
* `Cslib.Code.weighted_proximityGap_curve_johnson`: `ℕ`-weighted curve proximity gap.
* `Cslib.Code.exists_ratWeighted_correlatedAgreement_curve_johnson`,
  `Cslib.Code.exists_ratWeighted_correlatedAgreement_line_johnson`: `ℚ`-weighted correlated
  agreement.
* `Cslib.Code.ratWeighted_proximityGap_curve_johnson`: `ℚ`-weighted curve proximity gap.
-/

public section

namespace Cslib.Code

open scoped BigOperators
open Finset Polynomial

/-- **Original explicit-constant proximity-gap variant for parameterized curves up to the Johnson
bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5 and 6.2], accepted
JACM 2023 manuscript).

Let `α : ι → F` be distinct evaluation points over a finite field `F` with `n = |ι|` and code rate
`ρ = k / n` (`1 ≤ k ≤ n`), and let `m ≥ 1` be the multiplicity parameter. For any degree `r : ℕ`,
any proximity radius `e : ℕ` with `(e : ℝ) / n ≤ 1 - √ρ - √ρ / (2 * m)`, and any `r + 1` words
`u : Fin (r + 1) → (ι → F)`, either every point `∑ j, z ^ j • u j` on the parameterized curve lies
within Hamming distance `e` of `reedSolomon α k`, or the fraction of scalars `z : F` that do is at
most `1800 * r * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)`.

While `(m + 1) ^ 6 / ρ` has smaller exponents in `m` and `1 / ρ` than the displayed
`(m + 1 / 2) ^ 7 / (3 * ρ ^ (3 / 2))` expression of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorem 6.2], this bound is not uniformly smaller at small
finite `m`. -/
theorem proximityGap_curve_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k m r : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hm : 1 ≤ m)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u : Fin (r + 1) → (ι → F))
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e) ∨
      ((#(Finset.univ.filter fun z : F =>
          ∃ c ∈ reedSolomon α k,
            hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e) : ℝ) /
        (Fintype.card F : ℝ)) ≤
        1800 * (r : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · by_cases h0 : ∃ c ∈ reedSolomon α k, hammingDist (u 0) c ≤ e
    · exact Or.inl fun _ => by simpa [Fin.sum_univ_one] using h0
    · right
      rw [Finset.filter_eq_empty_iff.mpr fun _ _ => by simpa [Fin.sum_univ_one] using h0,
        card_empty, Nat.cast_zero, zero_div]
      positivity
  · obtain ⟨hk_sub, hinterp, hroot, hjb⟩ := ProximityGap.johnson_curve_params_bound hk hkn hm hr he
    rcases curve_dichotomy_of_ca (C := reedSolomon α k) (u := u)
      (fun x c => hammingDist x c ≤ e) (fun D' => Fintype.card ι - e ≤ D'.card)
      (fun hD' _ hag z => hammingDist_curve_le_of_eq_on hD' hag z)
      (fun S hS hcl => exists_correlatedAgreement_curve_johnson hα hk (by omega) hk_sub hinterp
        hroot u S hS hcl) with hall | hle
    · exact Or.inl hall
    · right
      have hcard : ((Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
          hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e).card : ℝ) ≤ _ :=
        Nat.cast_le.2 hle
      simpa only [div_div] using div_le_div_of_nonneg_right (hcard.trans hjb)
        (Nat.cast_nonneg (Fintype.card F))

/-- **Original explicit-constant proximity-gap variant for parameterized curves up to
`1 - √ρ - η`** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.5], accepted
JACM 2023 manuscript).

Closed-form corollary of `Cslib.Code.proximityGap_curve_johnson` parameterized directly by any
positive gap `η > 0` below the Johnson bound `1 - √ρ`, yielding an error fraction of at most
`115200 * r * n ^ 2 / (ρ * η ^ 6 * |F|)`. -/
theorem proximityGap_curve_johnson_of_eta
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k r : ℕ} {η : ℝ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hη : 0 < η)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) - η)
    (u : Fin (r + 1) → (ι → F))
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e) ∨
      ((#(Finset.univ.filter fun z : F =>
          ∃ c ∈ reedSolomon α k,
            hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e) : ℝ) /
        (Fintype.card F : ℝ)) ≤
        115200 * (r : ℝ) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)) := by
  obtain ⟨m, hm, he', hpow⟩ := ProximityGap.exists_multiplicity_of_eta hk hkn hη he
  rcases proximityGap_curve_johnson hα hk hkn hm he' u with hall | hbound
  · exact Or.inl hall
  · exact Or.inr (hbound.trans
      (siegel_eta_bound_le hk hkn Fintype.card_pos (Nat.cast_nonneg r) hη hpow))

/-- **Original explicit-constant `ℕ`-weighted proximity-gap dichotomy on parameterized curves up to
the Johnson bound** (toward [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 6.2 and 7.2], accepted
JACM 2023 manuscript).

For integer weights `W : ι → ℕ` bounded by `M > 0` (`∀ i, W i ≤ M`), any threshold `B_W : ℕ`
with `((|ι| - (B_W + M - 1) / M : ℕ) : ℝ) / |ι| ≤ 1 - √ρ - √ρ / (2 * m)`, and any degree-`r`
curve `u : Fin (r + 1) → (ι → F)` over a finite field `F`, either every point on the curve has
`W`-weighted agreement at least `B_W` with some codeword in `reedSolomon α k`, or the fraction of
scalars `z : F` that do is at most `1800 * r * M * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)`. -/
theorem weighted_proximityGap_curve_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k m r M B_W : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hB : ((Fintype.card ι - (B_W + M - 1) / M : ℕ) : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u : Fin (r + 1) → (ι → F))
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter
        (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        B_W ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i) ∨
      ((#(Finset.univ.filter fun z : F =>
          ∃ c ∈ reedSolomon α k,
            B_W ≤ ∑ i ∈ Finset.univ.filter
              (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i) : ℝ) /
        (Fintype.card F : ℝ)) ≤
        1800 * (r : ℝ) * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) := by
  set n := Fintype.card ι; set t := (B_W + M - 1) / M
  by_cases ht_le : t ≤ n
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · by_cases h0 : ∃ c ∈ reedSolomon α k, B_W ≤ ∑ i ∈ univ.filter (fun i => u 0 i = c i), W i
      · exact Or.inl fun _ => by simpa [Fin.sum_univ_one] using h0
      · right
        rw [Finset.filter_eq_empty_iff.mpr fun _ _ => by simpa [Fin.sum_univ_one] using h0,
          card_empty, Nat.cast_zero, zero_div]
        positivity
    · obtain ⟨hk_sub, hinterp, hroot, hjb⟩ :=
        ProximityGap.johnson_curve_params_bound (e := n - t) hk hkn hm hr hB
      rw [Nat.sub_sub_self ht_le] at hk_sub hroot
      rcases curve_dichotomy_of_ca (C := reedSolomon α k) (u := u)
        (fun x c => B_W ≤ ∑ i ∈ univ.filter (fun i => x i = c i), W i)
        (fun D' => B_W ≤ ∑ i ∈ D', W i)
        (fun hD' _ hag z => hD'.trans (weightedAgree_curve_ge_of_eq_on W hag z))
        (fun S hS hcl => exists_weighted_correlatedAgreement_curve_johnson hα hk (by omega) hM hW
          (sum_le_mul_card_of_le hW univ) hk_sub hinterp hroot u S hS hcl) with hall | hle
      · exact Or.inl hall
      · right
        have hjbM := johnsonCurveBound_mul_cast_le (hk.trans hkn) hM hjb
        have hcard : (#(univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
            B_W ≤ ∑ i ∈ univ.filter (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i),
              W i) : ℝ) ≤ _ := Nat.cast_le.2 hle
        exact (div_le_div_of_nonneg_right (hcard.trans hjbM) (Nat.cast_nonneg _)).trans_eq (by ring)
  · right
    have hMn_lt : M * n < B_W := Nat.lt_of_not_ge fun hle =>
      ht_le ((Nat.div_le_iff_le_mul_add_pred hM).2 (by omega))
    rw [Finset.filter_eq_empty_iff.mpr fun z _ ⟨c, _, hcW⟩ =>
      not_le_of_gt hMn_lt (hcW.trans (sum_le_mul_card_of_le hW _)),
      card_empty, Nat.cast_zero, zero_div]
    positivity

/-- **Explicit-parameter `ℚ`-weighted correlated-agreement step on parameterized curves up to the
Johnson bound** (toward [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 6.2 and 7.2], accepted
JACM 2023 manuscript).

Given rational coordinate weights `μ : ι → ℚ` with values in `{0, 1 / M, …, 1}` (`∀ i, μ i ≤ 1`
and `∀ i, ∃ a : ℕ, μ i = (a : ℚ) / M` for `0 < M`), threshold `θ : ℚ` with `(k : ℚ) ≤ θ` and
`(D : ℚ) < m * θ`, and Guruswami–Sudan interpolation condition
`|ι| * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D)`: over an arbitrary field `F` of any
characteristic, if more than `johnsonCurveBound |ι| m (k - 1) D r (M * |ι|)` scalars `z ∈ T`
have a codeword in `reedSolomon α k` achieving `μ`-weighted agreement at least `θ` with the curve
point `∑ j, z ^ j • u j`, then there exist a single shared coordinate subset `D' : Finset ι` with
`θ ≤ ∑ i ∈ D', μ i` and codewords `v : Fin (r + 1) → (ι → F)` agreeing with `u` on `D'`. -/
theorem exists_ratWeighted_correlatedAgreement_curve_johnson
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k r m D M : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ} (hk_le : (k : ℚ) ≤ θ)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : (D : ℚ) < (m : ℚ) * θ)
    (u : Fin (r + 1) → (ι → F)) (T : Finset F)
    (hT : ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D r
        (M * Fintype.card ι) < #T)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter
        (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v : Fin (r + 1) → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', ∀ j, u j i = v j i := by
  obtain ⟨W, hW_le, hW_sum, hk_le_t, hroot_nat, hsum_iff⟩ :=
    rat_weights_johnson_nat hM hμ_le hμ_den hk_le hroot
  obtain ⟨D', hD', v, hvRS, hagree⟩ := exists_weighted_correlatedAgreement_curve_johnson hα hk hm hM
    hW_le hW_sum hk_le_t hinterp hroot_nat u T hT
    fun z hz => let ⟨c, hcRS, hge⟩ := hclose z hz; ⟨c, hcRS, (hsum_iff _).1 hge⟩
  exact ⟨D', (hsum_iff D').2 hD', v, hvRS, hagree⟩

/-- **Explicit-parameter `ℚ`-weighted correlated-agreement step on affine lines up to the Johnson
bound** (toward [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 7.2], accepted JACM 2023
manuscript).

Line (`r = 1`) specialization of `Cslib.Code.exists_ratWeighted_correlatedAgreement_curve_johnson`
over an arbitrary field `F` of any characteristic. -/
theorem exists_ratWeighted_correlatedAgreement_line_johnson
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k m D M : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ} (hk_le : (k : ℚ) ≤ θ)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : (D : ℚ) < (m : ℚ) * θ)
    (u₀ u₁ : ι → F) (T : Finset F)
    (hT : ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1
        (M * Fintype.card ι) < #T)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v₁ ∈ reedSolomon α k,
        ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i := by
  obtain ⟨D', hD', v, hvRS, hagree⟩ := exists_ratWeighted_correlatedAgreement_curve_johnson
    (r := 1) hα hk hm hM hμ_le hμ_den hk_le hinterp hroot ![u₀, u₁] T hT
    fun z hz => by rw [line_sum_fin2]; exact hclose z hz
  exact ⟨D', hD', v 0, hvRS 0, v 1, hvRS 1, fun i hi => ⟨hagree i hi 0, hagree i hi 1⟩⟩

/-- **Original explicit-constant `ℚ`-weighted proximity-gap dichotomy on parameterized curves up to
the Johnson bound** (toward [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 6.2 and 7.2], accepted
JACM 2023 manuscript).

For rational weights `μ : ι → ℚ` with values in `{0, 1 / M, …, 1}` (`0 < M`), threshold `θ : ℚ`
satisfying `1 - θ / n ≤ 1 - √ρ - √ρ / (2 * m)`, and any degree-`r` curve over a finite field `F`,
either every curve point has `μ`-weighted agreement at least `θ` with some codeword in
`reedSolomon α k`, or the fraction of scalars `z : F` that do is at most
`1800 * r * M * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)`. -/
theorem ratWeighted_proximityGap_curve_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k m r M : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hm : 1 ≤ m) (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ}
    (hθ : 1 - (θ : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u : Fin (r + 1) → (ι → F))
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter
        (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i) ∨
      ((#(Finset.univ.filter fun z : F =>
          ∃ c ∈ reedSolomon α k,
            θ ≤ ∑ i ∈ Finset.univ.filter
              (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i) : ℝ) /
        (Fintype.card F : ℝ)) ≤
        1800 * (r : ℝ) * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) := by
  classical
  obtain ⟨W, _, hW_le, _, hsum_iff, hθ_le_t⟩ := rat_weights_to_nat hM hμ_le hμ_den θ
  by_cases hθ_le_n : (θ : ℝ) ≤ Fintype.card ι
  · have hB := ceilDiv_radius_le hM (hk.trans hkn) hθ_le_t hθ_le_n hθ
    have hiff (z : F) : (∃ c ∈ reedSolomon α k, θ ≤ ∑ i ∈ univ.filter (fun i =>
        (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i) ↔
      (∃ c ∈ reedSolomon α k, ⌈θ * M⌉₊ ≤ ∑ i ∈ univ.filter (fun i =>
        (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i) :=
      exists_congr fun _ => and_congr_right fun _ => hsum_iff _
    rcases weighted_proximityGap_curve_johnson (B_W := ⌈θ * M⌉₊) hα hk hkn hm hM hW_le hB u with
      hall | hbound
    · exact Or.inl fun z => (hiff z).2 (hall z)
    · right
      have hf : (univ.filter fun z : F => ∃ c ∈ reedSolomon α k, θ ≤ ∑ i ∈ univ.filter (fun i =>
          (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i) =
        univ.filter fun z : F => ∃ c ∈ reedSolomon α k, ⌈θ * M⌉₊ ≤ ∑ i ∈ univ.filter (fun i =>
          (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i := by
        ext z; simp only [mem_filter, mem_univ, true_and, hiff z]
      simpa only [hf] using hbound
  · right
    have hn_lt : (Fintype.card ι : ℚ) < θ := by exact_mod_cast lt_of_not_ge hθ_le_n
    rw [Finset.filter_eq_empty_iff.mpr fun z _ ⟨c, _, hcμ⟩ =>
      not_le_of_gt ((sum_le_card_of_le_one hμ_le _).trans_lt hn_lt) hcμ,
      card_empty, Nat.cast_zero, zero_div]
    positivity

end Cslib.Code
