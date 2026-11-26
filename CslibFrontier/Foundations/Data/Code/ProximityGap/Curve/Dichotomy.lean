/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Unique
public import Mathlib.Algebra.Order.Ring.Rat
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.JohnsonAffine
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.JohnsonHelpers
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.UniqueAffine
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.UniqueCurve

/-!
# Exact-Threshold Affine-Space Proximity-Gap Dichotomies

Contrapositive proximity-gap dichotomies on arbitrary affine spaces for both the unique-decoding
regime (`proximityGap_affine_unique`, eq. (1.2)) and the Johnson-bound regime (explicit `(m, D)`
and closed-form `η` variants in unweighted, `ℕ`-weighted, and `ℚ`-weighted flavors).

## Main results

* `Cslib.Code.proximityGap_affine_unique`: exact-`|F|` unique-decoding affine dichotomy.
* `Cslib.Code.proximityGap_affine_johnson_exact`,
  `Cslib.Code.weighted_proximityGap_affine_johnson_exact`,
  `Cslib.Code.ratWeighted_proximityGap_affine_johnson_exact`: explicit `(m, D)` dichotomies.
* `Cslib.Code.proximityGap_affine_johnson`, `Cslib.Code.proximityGap_affine_johnson_of_eta`,
  `Cslib.Code.weighted_proximityGap_affine_johnson`,
  `Cslib.Code.ratWeighted_proximityGap_affine_johnson`: closed-form Johnson-bound dichotomies.
-/

public section

namespace Cslib.Code

open scoped BigOperators
open Finset Polynomial

/-- Private helper: an affine proximity-gap dichotomy follows from correlated agreement. If every
`Dense` set of close affine parameters yields generators agreeing with codewords on a `Good` shared
coordinate set, and such shared agreement makes every affine point close, then either every affine
point is close or the close parameter set is not dense. -/
private theorem affine_dichotomy_of_correlatedAgreement
    {F ι : Type*} [Field F] [Fintype F] {ℓ : ℕ} {C : Submodule F (ι → F)}
    {u₀ : ι → F} {u : Fin ℓ → (ι → F)}
    (Close : (ι → F) → (ι → F) → Prop) (Good : Finset ι → Prop)
    (hgood : ∀ {D' : Finset ι}, Good D' → ∀ {v₀ : ι → F} {v : Fin ℓ → (ι → F)},
      (∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i) →
      ∀ z : Fin ℓ → F, Close (u₀ + ∑ j : Fin ℓ, z j • u j) (v₀ + ∑ j : Fin ℓ, z j • v j))
    (Dense : Finset (Fin ℓ → F) → Prop) {Small : Prop}
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ C, Close (u₀ + ∑ j : Fin ℓ, z j • u j) c]
    (hsmall : ¬ Dense (Finset.univ.filter fun z : Fin ℓ → F =>
      ∃ c ∈ C, Close (u₀ + ∑ j : Fin ℓ, z j • u j) c) → Small)
    (hca : ∀ T : Finset (Fin ℓ → F), Dense T →
      (∀ z ∈ T, ∃ c ∈ C, Close (u₀ + ∑ j : Fin ℓ, z j • u j) c) →
      ∃ D' : Finset ι, Good D' ∧ ∃ v₀ ∈ C, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ C) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i) :
    (∀ z : Fin ℓ → F, ∃ c ∈ C, Close (u₀ + ∑ j : Fin ℓ, z j • u j) c) ∨ Small := by
  by_cases hdense : Dense (Finset.univ.filter fun z : Fin ℓ → F =>
      ∃ c ∈ C, Close (u₀ + ∑ j : Fin ℓ, z j • u j) c)
  · obtain ⟨D', hD', v₀, hv₀, v, hv, hagree⟩ :=
      hca _ hdense fun _ hz => (Finset.mem_filter.1 hz).2
    exact Or.inl fun z => ⟨v₀ + ∑ j : Fin ℓ, z j • v j,
      Submodule.add_mem _ hv₀ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hv j)),
      hgood hD' hagree z⟩
  · exact Or.inr (hsmall hdense)

/-- **Exact-threshold proximity-gap dichotomy on affine spaces in the unique-decoding regime**
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.2, eq. (1.2)], accepted JACM 2023 manuscript
p. 3).

Contrapositive corollary of `Cslib.Code.exists_uniqueMaximal_correlatedAgreement_affine_unique`:
either every point of `u₀ + ∑ j, z j • u j` lies within Hamming distance `e` of `reedSolomon α k`,
or `|F| * #T ≤ |ι| * |F| ^ ℓ` (density at most `|ι| / |F| = ε_U`, uniformly for all `ℓ : ℕ`). -/
theorem proximityGap_affine_unique
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {e k ℓ : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) ∨
      Fintype.card F *
        (Finset.univ.filter fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
          hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e).card ≤
        Fintype.card ι * (Fintype.card F) ^ ℓ :=
  affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => hammingDist x c ≤ e)
    (fun D' => Fintype.card ι - e ≤ D'.card)
    (fun hD' _ _ hag z => hammingDist_affine_le_of_eq_on hD' hag z)
    (fun T' => Fintype.card ι * (Fintype.card F) ^ ℓ < Fintype.card F * T'.card)
    Nat.le_of_not_lt
    fun T' hT' hcl =>
      let ⟨D', hD', v₀, hv₀, v, hv, hag, _⟩ :=
        exists_uniqueMaximal_correlatedAgreement_affine_unique hα hunique u₀ u T' hT' hcl
      ⟨D', hD', v₀, hv₀, v, hv, hag⟩

/-- **Explicit-parameter proximity-gap dichotomy on affine spaces up to the Johnson bound**
(in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.2 and 1.6], accepted JACM
2023 manuscript).

Contrapositive corollary of `Cslib.Code.exists_correlatedAgreement_affine_johnson`: either every
point of `u₀ + ∑ j, z j • u j` lies within Hamming distance `e` of `reedSolomon α k`, or
`|F| * #T ≤ johnsonCurveBound |ι| m (k - 1) D 1 |ι| * |F| ^ ℓ` uniformly for all `ℓ : ℕ`. -/
theorem proximityGap_affine_johnson_exact
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ e m D : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hk_le : k ≤ Fintype.card ι - e)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * (Fintype.card ι - e))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) ∨
      Fintype.card F *
        (Finset.univ.filter fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
          hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e).card ≤
        ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 (Fintype.card ι) *
          (Fintype.card F) ^ ℓ := by
  exact affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => hammingDist x c ≤ e)
    (fun D' => Fintype.card ι - e ≤ D'.card)
    (fun hD' _ _ hag z => hammingDist_affine_le_of_eq_on hD' hag z)
    (fun T' =>
        ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 (Fintype.card ι) *
          (Fintype.card F) ^ ℓ < Fintype.card F * T'.card)
    Nat.le_of_not_lt
    (exists_correlatedAgreement_affine_johnson hα hk hm hk_le hinterp hroot u₀ u)

/-- **Explicit-parameter `ℕ`-weighted proximity-gap dichotomy on affine spaces up to the Johnson
bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4], accepted
JACM 2023 manuscript).

Contrapositive corollary of `Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson` with
exact denominator `|F|` (`|F| * #T ≤ B_line * |F| ^ ℓ` uniformly for all `ℓ : ℕ`). -/
theorem weighted_proximityGap_affine_johnson_exact
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ m D M W_tot B_W : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW_le : ∀ i, W i ≤ M) (hW_sum : ∑ i, W i ≤ W_tot)
    (hk_le_t : k ≤ (B_W + M - 1) / M)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * ((B_W + M - 1) / M))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) ∨
      Fintype.card F *
        (Finset.univ.filter fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
          B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
            (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i).card ≤
        ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 W_tot *
          (Fintype.card F) ^ ℓ := by
  exact affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => x i = c i), W i)
    (fun D' => B_W ≤ ∑ i ∈ D', W i)
    (fun hD' _ _ hag z => hD'.trans (weightedAgree_affine_ge_of_eq_on W hag z))
    (fun T' =>
        ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 W_tot *
          (Fintype.card F) ^ ℓ < Fintype.card F * T'.card)
    Nat.le_of_not_lt
    (exists_weighted_correlatedAgreement_affine_johnson hα hk hm hM hW_le hW_sum hk_le_t hinterp
      hroot u₀ u)

/-- **Explicit-parameter `ℚ`-weighted proximity-gap dichotomy on affine spaces up to the Johnson
bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4], accepted
JACM 2023 manuscript).

Contrapositive corollary of `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_johnson` with
exact denominator `|F|` (`|F| * #T ≤ B_line * |F| ^ ℓ` uniformly for all `ℓ : ℕ`). -/
theorem ratWeighted_proximityGap_affine_johnson_exact
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ m D M : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ} (hk_le : (k : ℚ) ≤ θ)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : (D : ℚ) < (m : ℚ) * θ)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) ∨
      Fintype.card F *
        (Finset.univ.filter fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
          θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
            (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i).card ≤
        ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 (M * Fintype.card ι) *
          (Fintype.card F) ^ ℓ := by
  obtain ⟨_, hμ_nn, _, _, _, _⟩ := rat_weights_to_nat hM hμ_le hμ_den θ
  exact affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => θ ≤ ∑ i ∈ Finset.univ.filter (fun i => x i = c i), μ i)
    (fun D' => θ ≤ ∑ i ∈ D', μ i)
    (fun hD' _ _ hag z => hD'.trans (ratWeightedAgree_affine_ge_of_eq_on hμ_nn hag z))
    (fun T' =>
        ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 (M * Fintype.card ι) *
          (Fintype.card F) ^ ℓ < Fintype.card F * T'.card)
    Nat.le_of_not_lt
    (exists_ratWeighted_correlatedAgreement_affine_johnson hα hk hm hM hμ_le hμ_den hk_le hinterp
      hroot u₀ u)

/-- **Original explicit-constant proximity-gap dichotomy on affine spaces up to the Johnson bound**
(in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.2 and 1.6], accepted JACM
2023 manuscript).

Contrapositive corollary of
`Cslib.Code.exists_correlatedAgreement_affine_johnson_of_multiplicity`: for any affine dimension
`ℓ : ℕ`, `1 ≤ k ≤ n`, `m ≥ 1`, and `(e : ℝ) / n ≤ 1 - √ρ - √ρ / (2 * m)` (`ρ = k / n`), either
every point of `u₀ + ∑ j : Fin ℓ, z j • u j` lies within Hamming distance `e` of
`reedSolomon α k`, or the fraction of `z : Fin ℓ → F` that do is at most
`1800 * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)`, independent of `ℓ` (with exact denominator `|F|`; the
explicit constant is not uniformly smaller than the paper's displayed finite constant at small `m`).
-/
theorem proximityGap_affine_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k m ℓ : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hm : 1 ≤ m)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) ∨
      ((#(Finset.univ.filter fun z : Fin ℓ → F =>
          ∃ c ∈ reedSolomon α k, hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) : ℝ) /
        ((Fintype.card F : ℝ) ^ ℓ)) ≤
        1800 * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) := by
  exact affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => hammingDist x c ≤ e)
    (fun D' => Fintype.card ι - e ≤ D'.card)
    (fun hD' _ _ hag z => hammingDist_affine_le_of_eq_on hD' hag z)
    (fun T' =>
        1800 * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) <
        (#T' : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    le_of_not_gt
    (exists_correlatedAgreement_affine_johnson_of_multiplicity hα hk hkn hm he u₀ u)

/-- **Original explicit-constant proximity-gap dichotomy on affine spaces up to `1 - √ρ - η`**
(in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.2 and 1.6], accepted JACM
2023 manuscript).

Contrapositive corollary of `Cslib.Code.exists_correlatedAgreement_affine_johnson_of_eta` for any
gap `η > 0` below `1 - √ρ`, yielding an exceptional fraction of at most
`115200 * n ^ 2 / (ρ * η ^ 6 * |F|)` (independent of `ℓ`, with exact denominator `|F|`). -/
theorem proximityGap_affine_johnson_of_eta
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k ℓ : ℕ} {η : ℝ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hη : 0 < η)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) - η)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) ∨
      ((#(Finset.univ.filter fun z : Fin ℓ → F =>
          ∃ c ∈ reedSolomon α k, hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) : ℝ) /
        ((Fintype.card F : ℝ) ^ ℓ)) ≤
        115200 * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)) := by
  exact affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => hammingDist x c ≤ e)
    (fun D' => Fintype.card ι - e ≤ D'.card)
    (fun hD' _ _ hag z => hammingDist_affine_le_of_eq_on hD' hag z)
    (fun T' =>
        115200 * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)) <
        (#T' : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    le_of_not_gt
    (exists_correlatedAgreement_affine_johnson_of_eta hα hk hkn hη he u₀ u)

/-- **Original explicit-constant `ℕ`-weighted proximity-gap dichotomy on affine spaces up to the
Johnson bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4],
accepted JACM 2023 manuscript).

Contrapositive corollary of
`Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity` with exact
denominator `|F|` (`1800 * M * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)`). -/
theorem weighted_proximityGap_affine_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k m ℓ M B_W : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hB : ((Fintype.card ι - (B_W + M - 1) / M : ℕ) : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) ∨
      ((#(Finset.univ.filter fun z : Fin ℓ → F =>
          ∃ c ∈ reedSolomon α k, B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
            (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) : ℝ) /
        ((Fintype.card F : ℝ) ^ ℓ)) ≤
        1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) := by
  exact affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => x i = c i), W i)
    (fun D' => B_W ≤ ∑ i ∈ D', W i)
    (fun hD' _ _ hag z => hD'.trans (weightedAgree_affine_ge_of_eq_on W hag z))
    (fun T' =>
        1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) <
        (#T' : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    le_of_not_gt
    (exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity hα hk hkn hm hM hW hB
      u₀ u)

/-- **Original explicit-constant `ℚ`-weighted proximity-gap dichotomy on affine spaces up to the
Johnson bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4],
accepted JACM 2023 manuscript).

Contrapositive corollary of
`Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_johnson_of_multiplicity` with exact
denominator `|F|` (`1800 * M * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)`). -/
theorem ratWeighted_proximityGap_affine_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k m ℓ M : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hm : 1 ≤ m) (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ}
    (hθ : 1 - (θ : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) ∨
      ((#(Finset.univ.filter fun z : Fin ℓ → F =>
          ∃ c ∈ reedSolomon α k, θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
            (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) : ℝ) /
        ((Fintype.card F : ℝ) ^ ℓ)) ≤
        1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) := by
  obtain ⟨_, hμ_nn, _, _, _, _⟩ := rat_weights_to_nat hM hμ_le hμ_den θ
  exact affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => θ ≤ ∑ i ∈ Finset.univ.filter (fun i => x i = c i), μ i)
    (fun D' => θ ≤ ∑ i ∈ D', μ i)
    (fun hD' _ _ hag z => hD'.trans (ratWeightedAgree_affine_ge_of_eq_on hμ_nn hag z))
    (fun T' =>
        1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) <
        (#T' : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    le_of_not_gt
    (exists_ratWeighted_correlatedAgreement_affine_johnson_of_multiplicity hα hk hkn hm hM hμ_le
      hμ_den hθ u₀ u)

end Cslib.Code
