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
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.Internal
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots

/-!
# Converse Lemmas and Sharp Unique-Decoding Curve/Line Correlated Agreement

Easy converse lemmas (`*_of_eq_on`) showing shared agreement induces uniform pointwise proximity on
curves and affine spaces, plus sharp integer- and `ℚ`-weighted correlated agreement and proximity
gaps for parameterized curves and lines in the unique-decoding regime (`2 * e + k ≤ |ι|`).

## Main results

* `Cslib.Code.hammingDist_affine_le_of_eq_on`, `Cslib.Code.weightedAgree_curve_ge_of_eq_on`,
  `Cslib.Code.ratWeightedAgree_curve_ge_of_eq_on`, `Cslib.Code.weightedAgree_affine_ge_of_eq_on`,
  `Cslib.Code.ratWeightedAgree_affine_ge_of_eq_on`: converse proximity lemmas.
* `Cslib.Code.exists_ratWeighted_correlatedAgreement_curve_unique`,
  `Cslib.Code.exists_weighted_correlatedAgreement_curve_unique`: sharp unique-decoding correlated
  agreement along degree-`d` parameterized curves.
* `Cslib.Code.weighted_proximityGap_curve_unique`,
  `Cslib.Code.ratWeighted_proximityGap_curve_unique`,
  `Cslib.Code.weighted_proximityGap_unique`, `Cslib.Code.ratWeighted_proximityGap_unique`: sharp
  unique-decoding proximity-gap dichotomies.
-/

public section

namespace Cslib.Code

open scoped BigOperators
open Finset Polynomial

private theorem subset_filter_curve_eq {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {d : ℕ} {D' : Finset ι} {u v : Fin (d + 1) → (ι → F)}
    (hagree : ∀ i ∈ D', ∀ j : Fin (d + 1), u j i = v j i) (z : F) :
    D' ⊆ Finset.univ.filter fun i =>
      (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = (∑ j : Fin (d + 1), z ^ (j : ℕ) • v j) i :=
  fun i hi => mem_filter.2 ⟨mem_univ i, by
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [hagree i hi j]⟩

/-- Unique-decoding weight-upgrade step: if `D'` has total `μ`-weight `< θ` and agrees everywhere,
any point `p` that is `μ`-close to `reedSolomon α k` must agree with `v_at p` at some `i ∉ D'`. -/
private theorem exists_disagree_mem_unique {F ι P : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α) {e k : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1) {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    {u_at v_at : P → ι → F} (hvRS : ∀ p, v_at p ∈ reedSolomon α k)
    (hdist : ∀ p, hammingDist (u_at p) (v_at p) ≤ e)
    (D' : Finset ι) (hD'_sub : ∀ p, ∀ i ∈ D', u_at p i = v_at p i)
    (hlt : ∑ i ∈ D', μ i < θ) {p : P}
    (hcl : ∃ c ∈ reedSolomon α k, θ ≤ ∑ i ∈ Finset.univ.filter (fun i => u_at p i = c i), μ i) :
    ∃ i ∉ D', u_at p i = v_at p i := by
  obtain ⟨c, hcRS, hμ_ge⟩ := hcl
  obtain rfl : c = v_at p := eq_of_hammingDist_le_reedSolomon hα hunique hcRS (hvRS p)
    (hammingDist_le_of_ratWeightedAgree_ge hμ_le hθ hμ_ge) (hdist p)
  by_contra hnone; push Not at hnone
  have heq : D' = Finset.univ.filter fun i => u_at p i = v_at p i :=
    Finset.Subset.antisymm (fun i hi => mem_filter.2 ⟨mem_univ i, hD'_sub p i hi⟩)
      fun i hi => by_contra fun hn => hnone i hn (mem_filter.1 hi).2
  exact absurd (heq ▸ hμ_ge) (not_le.2 hlt)

/-- If `u₀` and `u j` agree with `v₀` and `v j` on a shared subset `D'` of size at least
`|ι| - e`, then every affine combination `u₀ + ∑ j, z j • u j` lies within Hamming distance `e`
of `v₀ + ∑ j, z j • v j`. -/
theorem hammingDist_affine_le_of_eq_on
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {e ℓ : ℕ} {D' : Finset ι} {u₀ v₀ : ι → F} {u v : Fin ℓ → (ι → F)}
    (hD' : Fintype.card ι - e ≤ D'.card)
    (hagree : ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i)
    (z : Fin ℓ → F) :
    hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) (v₀ + ∑ j : Fin ℓ, z j • v j) ≤ e :=
  hammingDist_le_of_card_filter_eq
    (hD'.trans (Finset.card_le_card (subset_filter_affine_eq hagree z)))

/-- Converse weighted agreement for curves: if `u` and `v` agree on `D'`, then every point on the
curve `∑ j, z ^ j • u j` achieves at least `∑ i ∈ D', W i` weighted agreement with
`∑ j, z ^ j • v j`. -/
theorem weightedAgree_curve_ge_of_eq_on
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {d : ℕ} {D' : Finset ι} {u v : Fin (d + 1) → (ι → F)}
    (W : ι → ℕ)
    (hagree : ∀ i ∈ D', ∀ j : Fin (d + 1), u j i = v j i)
    (z : F) :
    ∑ i ∈ D', W i ≤
      ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = (∑ j : Fin (d + 1), z ^ (j : ℕ) • v j) i),
        W i :=
  Finset.sum_le_sum_of_subset (subset_filter_curve_eq hagree z)

/-- Converse `ℚ`-weighted agreement for curves (under nonnegative weights `0 ≤ μ i`). -/
theorem ratWeightedAgree_curve_ge_of_eq_on
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {d : ℕ} {D' : Finset ι} {u v : Fin (d + 1) → (ι → F)}
    {μ : ι → ℚ} (hμ_nonneg : ∀ i, 0 ≤ μ i)
    (hagree : ∀ i ∈ D', ∀ j : Fin (d + 1), u j i = v j i)
    (z : F) :
    ∑ i ∈ D', μ i ≤
      ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = (∑ j : Fin (d + 1), z ^ (j : ℕ) • v j) i),
        μ i :=
  Finset.sum_le_sum_of_subset_of_nonneg (subset_filter_curve_eq hagree z) fun i _ _ => hμ_nonneg i

/-- Converse weighted agreement for affine spaces: if `u₀, u` agree with `v₀, v` on `D'`, then
every affine combination achieves at least `∑ i ∈ D', W i` weighted agreement. -/
theorem weightedAgree_affine_ge_of_eq_on
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {ℓ : ℕ} {D' : Finset ι} {u₀ v₀ : ι → F} {u v : Fin ℓ → (ι → F)}
    (W : ι → ℕ)
    (hagree : ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i)
    (z : Fin ℓ → F) :
    ∑ i ∈ D', W i ≤
      ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = (v₀ + ∑ j : Fin ℓ, z j • v j) i),
        W i :=
  Finset.sum_le_sum_of_subset (subset_filter_affine_eq hagree z)

/-- Converse `ℚ`-weighted agreement for affine spaces (under nonnegative weights `0 ≤ μ i`). -/
theorem ratWeightedAgree_affine_ge_of_eq_on
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {ℓ : ℕ} {D' : Finset ι} {u₀ v₀ : ι → F} {u v : Fin ℓ → (ι → F)}
    {μ : ι → ℚ} (hμ_nonneg : ∀ i, 0 ≤ μ i)
    (hagree : ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i)
    (z : Fin ℓ → F) :
    ∑ i ∈ D', μ i ≤
      ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = (v₀ + ∑ j : Fin ℓ, z j • v j) i),
        μ i :=
  Finset.sum_le_sum_of_subset_of_nonneg (subset_filter_affine_eq hagree z) fun i _ _ => hμ_nonneg i

/-- **Weighted correlated agreement on parameterized curves in the unique-decoding regime**
(`ℚ`-weights; unique-decoding specialization and signed-weight extension of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorem 6.1 & Section 7], where source Theorem 7.1 treats
weighted curves, Version I, in the `α > √ρ` range):

Over an arbitrary field `F`, let `α : ι → F` be distinct evaluation points, `2 * e + k ≤ |ι|`,
and `μ : ι → ℚ` any weight function bounded above by `1` (in particular, any `[0, 1]`-valued
weight function). Suppose `θ : ℚ` satisfies `((|ι| - e : ℕ) : ℚ) - 1 < θ` (so `μ`-weighted
agreement `≥ θ` implies unweighted Hamming distance `≤ e`). If more than `d * |ι|` scalars
`z ∈ S` have a codeword in `reedSolomon α k` achieving `μ`-weighted agreement at least `θ`
with the curve point `∑ j, z ^ (j : ℕ) • u j`, then there exist codewords `v j ∈ reedSolomon α k`
and a single shared coordinate set `D'` with `θ ≤ ∑ i ∈ D', μ i` on which `u j i = v j i` for
all `i ∈ D'` and all `j`.

Notice that the threshold `d * |ι| < #S` has zero dependence on the weight denominator or total
weight. -/
theorem exists_ratWeighted_correlatedAgreement_curve_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {e k d : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    (u : Fin (d + 1) → (ι → F)) (S : Finset F)
    (hS : d * Fintype.card ι < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v : Fin (d + 1) → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', ∀ j, u j i = v j i := by
  classical
  obtain ⟨D₀, hD₀, v, hvRS, hagree₀⟩ := exists_correlatedAgreement_curve_unique hα hunique u S hS
    fun z hz => let ⟨c, hcRS, hμ_ge⟩ := hclose z hz
      ⟨c, hcRS, hammingDist_le_of_ratWeightedAgree_ge hμ_le hθ hμ_ge⟩
  let D' : Finset ι := Finset.univ.filter fun i => ∀ j : Fin (d + 1), u j i = v j i
  refine ⟨D', ?_, v, hvRS, fun i hi => (mem_filter.1 hi).2⟩
  by_contra! hlt
  let f (i : ι) : F[X] := ofFn (d + 1) fun j => u j i - v j i
  let badI : Finset ι := univ.filter fun i => f i ≠ 0
  have hS_sub : S ⊆ badI.biUnion fun i => (f i).roots.toFinset := fun z hz => by
    obtain ⟨i, hi_not, heq⟩ := exists_disagree_mem_unique hα hunique hμ_le hθ
      (u_at := fun z => ∑ j : Fin (d + 1), z ^ (j : ℕ) • u j)
      (v_at := fun z => ∑ j : Fin (d + 1), z ^ (j : ℕ) • v j)
      (fun z => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvRS j))
      (hammingDist_curve_le_of_eq_on hD₀ hagree₀) D'
      (fun z i hi => (mem_filter.1 (subset_filter_curve_eq (fun _ h => (mem_filter.1 h).2) z hi)).2)
      hlt (hclose z hz)
    have hf0 : f i ≠ 0 := fun h0 => hi_not <| mem_filter.2 ⟨mem_univ i, fun j => sub_eq_zero.1 <|
      by simpa only [f, ofFn_coeff_eq_val_of_lt _ j.isLt, coeff_zero] using
        congrArg (fun p : F[X] => p.coeff (j : ℕ)) h0⟩
    refine mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_univ i, hf0⟩,
      Multiset.mem_toFinset.2 ((mem_roots hf0).2 ?_)⟩
    have hterm (j : Fin (d + 1)) : (u j i - v j i) * z ^ (j : ℕ) =
        z ^ (j : ℕ) * u j i - z ^ (j : ℕ) * v j i := by ring
    simp only [IsRoot.def, f, ofFn_eq_sum_monomial, eval_finsetSum, eval_monomial, hterm,
      sum_sub_distrib, sub_eq_zero]
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using heq
  have hcard_le : S.card ≤ d * Fintype.card ι := calc
    S.card ≤ (badI.biUnion fun i => (f i).roots.toFinset).card := card_le_card hS_sub
    _ ≤ ∑ i ∈ badI, ((f i).roots.toFinset).card := card_biUnion_le
    _ ≤ ∑ _i ∈ badI, d := sum_le_sum fun i _ => (Multiset.toFinset_card_le _).trans
        ((card_roots' _).trans (Nat.le_of_lt_succ (ofFn_natDegree_lt (Nat.succ_pos d) _)))
    _ ≤ d * Fintype.card ι := by
        simpa only [sum_const, smul_eq_mul, mul_comm _ d] using
          Nat.mul_le_mul_left d (card_le_univ badI)
  omega

/-- **Weighted correlated agreement on affine lines in the unique-decoding regime**
(`ℚ`-weights; unique-decoding line specialization and signed-weight extension of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1 & Section 7], where source Theorem 7.1 treats
weighted curves, Version I, in the `α > √ρ` range):
Line specialization (`d = 1`) of `Cslib.Code.exists_ratWeighted_correlatedAgreement_curve_unique`,
with exact threshold `|ι| < #S`. -/
theorem exists_ratWeighted_correlatedAgreement_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {e k : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    (u₀ u₁ : ι → F) (S : Finset F)
    (hS : Fintype.card ι < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v₁ ∈ reedSolomon α k,
        ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i := by
  obtain ⟨D', hD', v, hvRS, hagree⟩ := exists_ratWeighted_correlatedAgreement_curve_unique hα
    hunique hμ_le hθ ![u₀, u₁] S (by simpa only [one_mul] using hS : 1 * Fintype.card ι < S.card)
    fun z hz => by rw [line_sum_fin2]; exact hclose z hz
  exact ⟨D', hD', v 0, hvRS 0, v 1, hvRS 1, fun i hi => ⟨hagree i hi 0, hagree i hi 1⟩⟩

/-- **Integer-weighted correlated agreement on parameterized curves in the unique-decoding regime**
(unique-decoding specialization of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 6.1 & Section 7],
where source Theorem 7.1 treats weighted curves, Version I, in the `α > √ρ` range):

Given integer weights `W : ι → ℕ` bounded by `M > 0` (`∀ i, W i ≤ M`) and weighted agreement
threshold `B : ℕ`, let `e := |ι| - (B + M - 1) / M` be the implied unweighted error bound.
Whenever `2 * e + k ≤ |ι|` and `d * |ι| < #S`, weighted agreement `≥ B` on the curve for all
`z ∈ S` implies shared weighted agreement `≥ B` for codewords `v : Fin (d + 1) → (ι → F)`. -/
theorem exists_weighted_correlatedAgreement_curve_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k d M B : ℕ} (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hunique : 2 * (Fintype.card ι - (B + M - 1) / M) + k ≤ Fintype.card ι)
    (u : Fin (d + 1) → (ι → F)) (S : Finset F)
    (hS : d * Fintype.card ι < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), W i) :
    ∃ D' : Finset ι, B ≤ ∑ i ∈ D', W i ∧
      ∃ v : Fin (d + 1) → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', ∀ j, u j i = v j i := by
  obtain ⟨D', hD', v, hvRS, hagree⟩ := exists_ratWeighted_correlatedAgreement_curve_unique hα
    hunique (fun i => (div_le_one (Nat.cast_pos.2 hM)).2 (Nat.cast_le.2 (hW i)))
    (card_sub_sub_ceilDiv_sub_one_lt hM) u S hS fun z hz =>
      let ⟨c, hcRS, hW_ge⟩ := hclose z hz; ⟨c, hcRS, (nat_le_sum_iff_div hM _).1 hW_ge⟩
  exact ⟨D', (nat_le_sum_iff_div hM D').2 hD', v, hvRS, hagree⟩

/-- **Integer-weighted correlated agreement on affine lines in the unique-decoding regime**
(unique-decoding line specialization of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1 &
Section 7], where source Theorem 7.1 treats weighted curves, Version I, in the `α > √ρ` range):
Line specialization (`d = 1`) of `Cslib.Code.exists_weighted_correlatedAgreement_curve_unique`
with exact threshold `|ι| < #S`, directly discharging FRI unique-decoding commit-round soundness
with zero total-weight loss. -/
theorem exists_weighted_correlatedAgreement_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k M B : ℕ} (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hunique : 2 * (Fintype.card ι - (B + M - 1) / M) + k ≤ Fintype.card ι)
    (u₀ u₁ : ι → F) (S : Finset F)
    (hS : Fintype.card ι < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      B ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), W i) :
    ∃ D' : Finset ι, B ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v₁ ∈ reedSolomon α k,
        ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i := by
  obtain ⟨D', hD', v, hvRS, hagree⟩ := exists_weighted_correlatedAgreement_curve_unique hα hM hW
    hunique ![u₀, u₁] S (by simpa only [one_mul] using hS : 1 * Fintype.card ι < S.card)
    fun z hz => by rw [line_sum_fin2]; exact hclose z hz
  exact ⟨D', hD', v 0, hvRS 0, v 1, hvRS 1, fun i hi => ⟨hagree i hi 0, hagree i hi 1⟩⟩

private theorem line_dichotomy_of_ca {F ι : Type*} [Field F] [Fintype F]
    {C : Submodule F (ι → F)} {u₀ u₁ : ι → F}
    (Close : (ι → F) → (ι → F) → Prop) (Good : Finset ι → Prop) {B : ℕ}
    (hgood : ∀ {D' : Finset ι}, Good D' → ∀ {v₀ v₁ : ι → F},
      (∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i) → ∀ z : F, Close (u₀ + z • u₁) (v₀ + z • v₁))
    [DecidablePred fun z : F => ∃ c ∈ C, Close (u₀ + z • u₁) c]
    (hca : ∀ S : Finset F, B < S.card →
      (∀ z ∈ S, ∃ c ∈ C, Close (u₀ + z • u₁) c) →
      ∃ D' : Finset ι, Good D' ∧ ∃ v₀ ∈ C, ∃ v₁ ∈ C, ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i) :
    (∀ z : F, ∃ c ∈ C, Close (u₀ + z • u₁) c) ∨
      (Finset.univ.filter fun z : F => ∃ c ∈ C, Close (u₀ + z • u₁) c).card ≤ B := by
  by_cases hcard : (Finset.univ.filter fun z : F => ∃ c ∈ C, Close (u₀ + z • u₁) c).card ≤ B
  · exact Or.inr hcard
  · obtain ⟨D', hD', v₀, hv₀, v₁, hv₁, hag⟩ :=
      hca _ (Nat.lt_of_not_ge hcard) fun _ hz => (mem_filter.1 hz).2
    exact Or.inl fun z =>
      ⟨v₀ + z • v₁, Submodule.add_mem _ hv₀ (Submodule.smul_mem _ z hv₁), hgood hD' hag z⟩

/-- **Weighted proximity-gap dichotomy on parameterized curves in the unique-decoding regime**
(`ℕ`-weights, `[Fintype F]`): either every curve point has `W`-weighted agreement at least `B`
with `reedSolomon α k`, or at most `d * |ι|` scalars in `F` do. -/
theorem weighted_proximityGap_curve_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F] [Fintype F]
    {α : ι → F} (hα : Function.Injective α)
    {k d M B : ℕ} (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hunique : 2 * (Fintype.card ι - (B + M - 1) / M) + k ≤ Fintype.card ι)
    (u : Fin (d + 1) → (ι → F))
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), W i] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), W i) ∨
      (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
        B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), W i).card ≤
        d * Fintype.card ι :=
  curve_dichotomy_of_ca (C := reedSolomon α k)
    (fun x c => B ≤ ∑ i ∈ univ.filter (fun i => x i = c i), W i)
    (fun D' => B ≤ ∑ i ∈ D', W i)
    (fun hD' _ hag z => hD'.trans (weightedAgree_curve_ge_of_eq_on W hag z))
    (exists_weighted_correlatedAgreement_curve_unique hα hM hW hunique u)

/-- **Weighted proximity-gap dichotomy on affine lines in the unique-decoding regime**
(`ℕ`-weights, `[Fintype F]`): either every point on `u₀ + z • u₁` achieves `W`-weighted agreement
at least `B` with `reedSolomon α k`, or at most `|ι|` scalars in `F` do. -/
theorem weighted_proximityGap_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F] [Fintype F]
    {α : ι → F} (hα : Function.Injective α)
    {k M B : ℕ} (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hunique : 2 * (Fintype.card ι - (B + M - 1) / M) + k ≤ Fintype.card ι)
    (u₀ u₁ : ι → F)
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      B ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), W i] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        B ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), W i) ∨
      (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
        B ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), W i).card ≤
        Fintype.card ι :=
  line_dichotomy_of_ca (C := reedSolomon α k)
    (fun x c => B ≤ ∑ i ∈ univ.filter (fun i => x i = c i), W i)
    (fun D' => B ≤ ∑ i ∈ D', W i)
    (fun hD' _ _ hag z => hD'.trans (Finset.sum_le_sum_of_subset (subset_filter_line_eq hag z)))
    (exists_weighted_correlatedAgreement_unique hα hM hW hunique u₀ u₁)

/-- **Weighted proximity-gap dichotomy on parameterized curves in the unique-decoding regime**
(`ℚ`-weights in `[0, 1]`, `[Fintype F]`). -/
theorem ratWeighted_proximityGap_curve_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F] [Fintype F]
    {α : ι → F} (hα : Function.Injective α)
    {e k d : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {μ : ι → ℚ} (hμ_nonneg : ∀ i, 0 ≤ μ i) (hμ_le : ∀ i, μ i ≤ 1)
    {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    (u : Fin (d + 1) → (ι → F))
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), μ i] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), μ i) ∨
      (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), μ i).card ≤
        d * Fintype.card ι :=
  curve_dichotomy_of_ca (C := reedSolomon α k)
    (fun x c => θ ≤ ∑ i ∈ univ.filter (fun i => x i = c i), μ i)
    (fun D' => θ ≤ ∑ i ∈ D', μ i)
    (fun hD' _ hag z => hD'.trans (ratWeightedAgree_curve_ge_of_eq_on hμ_nonneg hag z))
    (exists_ratWeighted_correlatedAgreement_curve_unique hα hunique hμ_le hθ u)

/-- **Weighted proximity-gap dichotomy on affine lines in the unique-decoding regime**
(`ℚ`-weights in `[0, 1]`, `[Fintype F]`). -/
theorem ratWeighted_proximityGap_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F] [Fintype F]
    {α : ι → F} (hα : Function.Injective α)
    {e k : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {μ : ι → ℚ} (hμ_nonneg : ∀ i, 0 ≤ μ i) (hμ_le : ∀ i, μ i ≤ 1)
    {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    (u₀ u₁ : ι → F)
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), μ i] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), μ i) ∨
      (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), μ i).card ≤
        Fintype.card ι :=
  line_dichotomy_of_ca (C := reedSolomon α k)
    (fun x c => θ ≤ ∑ i ∈ univ.filter (fun i => x i = c i), μ i)
    (fun D' => θ ≤ ∑ i ∈ D', μ i)
    (fun hD' _ _ hag z => hD'.trans (Finset.sum_le_sum_of_subset_of_nonneg
      (subset_filter_line_eq hag z) fun i _ _ => hμ_nonneg i))
    (exists_ratWeighted_correlatedAgreement_unique hα hunique hμ_le hθ u₀ u₁)

end Cslib.Code
