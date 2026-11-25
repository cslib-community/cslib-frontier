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
import CslibFrontier.Foundations.Data.Code.GuruswamiSudan
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.AffineLift
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.Internal
import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.JohnsonHelpers
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Tactic.Positivity

/-!
# Johnson-Bound Affine-Space Correlated Agreement

List-premise-free unweighted, `ℕ`-weighted, and `ℚ`-weighted correlated-agreement theorems on
arbitrary affine spaces `u₀ + ∑ j, z j • u j` in both explicit `(m, D)` and closed-form
(`(m + 1)^6` / `η^(-6)`) bounds.

## Main results

* `Cslib.Code.exists_correlatedAgreement_affine_johnson`,
  `Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson`,
  `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_johnson`: explicit `(m, D)` affine
  correlated agreement.
* `Cslib.Code.exists_correlatedAgreement_affine_johnson_of_multiplicity`,
  `Cslib.Code.exists_correlatedAgreement_affine_johnson_of_eta`: unweighted closed-form variants.
* `Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity`,
  `Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson_of_eta`: `ℕ`-weighted variants.
* `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_johnson_of_multiplicity`,
  `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_johnson_of_eta`: `ℚ`-weighted variants.
-/

public section

namespace Cslib.Code

open scoped BigOperators
open Finset Polynomial

/-- Private helper: the Guruswami–Sudan `Y`-degree bound `maxYDeg d D` never exceeds
`johnsonCurveBound n m d D r W_tot` (`0` when `D = 0`, and `≤ 2 * maxYDeg d D * (D + B_Z)` when
`1 ≤ D`). -/
private theorem maxYDeg_le_johnsonCurveBound (n m d D r W_tot : ℕ) :
    ProximityGap.maxYDeg d D ≤ ProximityGap.johnsonCurveBound n m d D r W_tot := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · rw [show ProximityGap.maxYDeg d 0 = 0 from
      Nat.eq_zero_of_le_zero (Finset.sup_le fun p hp => (Sudan.mem_monomials.1 hp).2.1)]
    exact Nat.zero_le _
  · have hmul : ProximityGap.maxYDeg d D ≤
        2 * ProximityGap.maxYDeg d D * (D + ProximityGap.siegelZDeg n m d D r) :=
      (by omega : ProximityGap.maxYDeg d D ≤ 2 * ProximityGap.maxYDeg d D).trans
        (Nat.le_mul_of_pos_right _ (by omega))
    dsimp only [ProximityGap.johnsonCurveBound]
    omega

/-- Private helper: converts the real density strict inequality `B / q < cardT / q ^ ℓ` (`0 < q`)
to the exact integer form `B * q ^ ℓ < q * cardT` uniformly for all `ℓ : ℕ`. -/
private theorem affine_mul_lt_of_density_lt
    {q ℓ cardT B : ℕ} (hq : 0 < q)
    (hlt : (B : ℝ) / (q : ℝ) < (cardT : ℝ) / ((q : ℝ) ^ ℓ)) :
    B * q ^ ℓ < q * cardT := by
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.2 hq
  have hmulR : (B : ℝ) * ((q : ℝ) ^ ℓ) < (cardT : ℝ) * (q : ℝ) :=
    (div_lt_div_iff₀ hqR (pow_pos hqR ℓ)).1 hlt
  exact Nat.cast_lt.1 (by cast_linarith : ((B * q ^ ℓ : ℕ) : ℝ) < ((q * cardT : ℕ) : ℝ))

/-- Private helper: uniform Reed–Solomon list-size bound `≤ maxYDeg (k - 1) D` for all `1 ≤ k`
(covering both `k ≥ 2` via `guruswamiSudan` and `k = 1` via disjoint constant-codeword fibers). -/
private theorem card_reedSolomon_list_le_maxYDeg
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k m D M B_W : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW_le : ∀ i, W i ≤ M)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * ((B_W + M - 1) / M))
    (u : ι → F) :
    ∃ Lset : Finset (ι → F), Lset.card ≤ ProximityGap.maxYDeg (k - 1) D ∧
      ∀ c ∈ reedSolomon α k,
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => u i = c i), W i → c ∈ Lset := by
  classical
  set t : ℕ := (B_W + M - 1) / M
  have hagree_ge (c : ι → F) (hcW : B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => u i = c i), W i) :
      t ≤ (Finset.univ.filter fun i => u i = c i).card := by
    have hsum_le : ∑ i ∈ Finset.univ.filter (fun i => u i = c i), W i ≤
        (Finset.univ.filter fun i => u i = c i).card * M :=
      Finset.sum_le_card_nsmul _ _ M fun i _ => hW_le i
    rw [Nat.div_le_iff_le_mul_add_pred hM, mul_comm]; omega
  rcases Nat.eq_or_lt_of_le hk with rfl | hk2
  · have ht_pos : 0 < t := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at hroot; omega
    let A_good :=
      (Finset.univ.image u).filter fun a => t ≤ (Finset.univ.filter fun i => u i = a).card
    have hD_le_maxY : D ≤ ProximityGap.maxYDeg 0 D :=
      Finset.le_sup (f := Prod.snd) (b := (0, D))
        (Sudan.mem_monomials.2 ⟨Nat.zero_le D, le_rfl, by simp⟩)
    have hmon0 : #(Sudan.monomials 0 D) = (D + 1) * (D + 1) := by
      have : Sudan.monomials 0 D = range (D + 1) ×ˢ range (D + 1) := by
        ext ⟨a, b⟩
        simp only [Sudan.mem_monomials, mem_product, mem_range, Nat.lt_succ_iff, zero_mul, add_zero]
        tauto
      rw [this, Finset.card_product, Finset.card_range]
    have hcard_mul : A_good.card * t ≤ Fintype.card ι := calc
      A_good.card * t ≤ ∑ a ∈ A_good, (Finset.univ.filter fun i => u i = a).card :=
          Finset.card_nsmul_le_sum _ _ t fun _ ha => (mem_filter.1 ha).2
      _ = (A_good.biUnion fun a => Finset.univ.filter fun i => u i = a).card :=
          (Finset.card_biUnion fun _ _ _ _ hne =>
            Finset.disjoint_filter.2 fun _ _ h1 h2 => hne (h1.symm.trans h2)).symm
      _ ≤ Fintype.card ι := Finset.card_le_univ _
    have hm_le : m ≤ m * (m + 1) / 2 :=
      (Nat.le_div_iff_mul_le two_pos).2 (Nat.mul_le_mul_left m (by omega))
    have hlt_sq : A_good.card * (D + 1) < (D + 1) * (D + 1) := by
      rw [Nat.sub_self, hmon0] at hinterp
      calc A_good.card * (D + 1) ≤ A_good.card * (m * t) := Nat.mul_le_mul_left _ hroot
        _ = A_good.card * t * m := by ring
        _ ≤ Fintype.card ι * m := Nat.mul_le_mul_right _ hcard_mul
        _ ≤ Fintype.card ι * (m * (m + 1) / 2) := Nat.mul_le_mul_left _ hm_le
        _ < (D + 1) * (D + 1) := hinterp
    refine ⟨A_good.image fun a _ => a, Finset.card_image_le.trans
      ((Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_right hlt_sq)).trans hD_le_maxY),
      fun c hcRS hcW => ?_⟩
    obtain ⟨P, hPdeg, rfl⟩ := mem_reedSolomon.1 hcRS
    have hconst : (fun i => P.eval (α i)) = fun _ => P.coeff 0 := funext fun i => by
      have hP : P = C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero <| by
        rcases eq_or_ne P 0 with rfl | hP0
        · exact natDegree_zero
        · exact Nat.lt_one_iff.1 ((natDegree_lt_iff_degree_lt hP0).2 hPdeg)
      conv_lhs => rw [hP]
      exact eval_C
    have hcard_a : t ≤ (Finset.univ.filter fun i => u i = P.coeff 0).card := by
      simpa only [congrFun hconst] using hagree_ge (fun i => P.eval (α i)) hcW
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.1 (ht_pos.trans_le hcard_a)
    exact mem_image.2 ⟨P.coeff 0, mem_filter.2
      ⟨mem_image.2 ⟨i₀, mem_univ i₀, (mem_filter.1 hi₀).2⟩, hcard_a⟩, hconst.symm⟩
  · have hdiv_le : D / (k - 1) ≤ ProximityGap.maxYDeg (k - 1) D :=
      Finset.le_sup (f := Prod.snd) (b := (0, D / (k - 1))) <| Sudan.mem_monomials.2
        ⟨Nat.zero_le D, Nat.div_le_self D (k - 1), by rw [zero_add]; exact Nat.mul_div_le D (k - 1)⟩
    refine ⟨(guruswamiSudan α u m k D).image fun P i => P.eval (α i),
      Finset.card_image_le.trans
        (((Nat.le_div_iff_mul_le (by omega)).2 card_guruswamiSudan_mul_le).trans hdiv_le),
      fun c hcRS hcW => ?_⟩
    obtain ⟨P, hPdeg, rfl⟩ := mem_reedSolomon.1 hcRS
    have ht_le : t ≤ (Finset.univ.filter fun i => P.eval (α i) = u i).card := by
      simpa only [eq_comm] using hagree_ge (fun i => P.eval (α i)) hcW
    exact mem_image.2 ⟨P, (mem_guruswamiSudan_iff hα (by omega) hinterp).2
      ⟨hPdeg, hroot.trans_le (Nat.mul_le_mul_left m ht_le)⟩, rfl⟩

/-- Private helper: strictly positive lower bound on `T.card / |F| ^ ℓ` implies `T.Nonempty`. -/
private theorem nonempty_of_pos_lt_density {F : Type*} [Fintype F] {ℓ : ℕ}
    {T : Finset (Fin ℓ → F)} {B : ℝ} (hB_pos : 0 < B)
    (hT : B < (T.card : ℝ) / ((Fintype.card F : ℝ) ^ ℓ)) : T.Nonempty :=
  Finset.card_pos.1 <| Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.cast_zero, zero_div] at hT
    exact lt_irrefl 0 (hB_pos.trans hT)

/-- Private helper: reduces `ℚ`-weighted affine correlated agreement with common denominator `M`
to `ℕ`-weighted affine correlated agreement via `rat_weights_to_nat` and `ceilDiv_radius_le`. -/
private theorem ratWeighted_to_nat_affine_ca
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k ℓ M : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ} {R : ℝ} (hθ : 1 - (θ : ℝ) / (Fintype.card ι : ℝ) ≤ R)
    {u₀ : ι → F} {u : Fin ℓ → (ι → F)} {T : Finset (Fin ℓ → F)}
    (hT_ne : T.Nonempty)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i)
    (hw : ∀ {W : ι → ℕ} {B_W : ℕ}, (∀ i, W i ≤ M) →
      ((Fintype.card ι - (B_W + M - 1) / M : ℕ) : ℝ) / (Fintype.card ι : ℝ) ≤ R →
      (∀ z ∈ T, ∃ c ∈ reedSolomon α k,
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) →
      ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
        ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
          ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  obtain ⟨W, _, hW_le, _, hsum_iff, hθ_le_t⟩ := rat_weights_to_nat hM hμ_le hμ_den θ
  obtain ⟨z₀, hz₀⟩ := hT_ne
  obtain ⟨c₀, _, hc₀_ge⟩ := hclose z₀ hz₀
  have hθ_le_n : (θ : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast hc₀_ge.trans (sum_le_card_of_le_one hμ_le _)
  have hB := ceilDiv_radius_le hM (hk.trans hkn) hθ_le_t hθ_le_n hθ
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ := hw hW_le hB fun z hz => by
    obtain ⟨c, hcRS, hge⟩ := hclose z hz
    exact ⟨c, hcRS, (hsum_iff _).1 hge⟩
  exact ⟨D', (hsum_iff D').2 hD', v₀, hv₀, v, hvRS, hagree⟩

/-- **Explicit-parameter `ℕ`-weighted correlated-agreement step on affine spaces up to the Johnson
bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on printed p. 6 and
Theorems 7.3–7.4 on printed p. 32 of the accepted JACM 2023 manuscript).

Let `B_line = johnsonCurveBound |ι| m (k - 1) D 1 W_tot`. Over any finite field `F` of arbitrary
characteristic and any affine dimension `ℓ : ℕ`, if `B_line * |F| ^ ℓ < |F| * #T` and every
`z ∈ T` has a codeword in `reedSolomon α k` achieving `W`-weighted agreement at least `B_W` with
`u₀ + ∑ j, z j • u j`, then there exist a single shared coordinate subset `D' : Finset ι` of
`W`-weight at least `B_W` and codewords `v₀, v_j ∈ reedSolomon α k` agreeing with `u₀, u_j` on
`D'`. The density premise forces `B_line < |F|`, and `maxYDeg (k - 1) D ≤ B_line` always holds, so
no extra list-size / field-size premise is needed, and zero coordinate weights (`W i = 0`) are
permitted via the `supp W` refinement of
`Cslib.Code.exists_weighted_correlatedAgreement_affine_of_line`. -/
theorem exists_weighted_correlatedAgreement_affine_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ m D M W_tot B_W : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW_le : ∀ i, W i ≤ M) (hW_sum : ∑ i, W i ≤ W_tot)
    (hk_le_t : k ≤ (B_W + M - 1) / M)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * ((B_W + M - 1) / M))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 W_tot *
        (Fintype.card F) ^ ℓ < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) :
    ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  have hB_lt_q :
      ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 W_tot < Fintype.card F :=
    lt_card_field_of_density_threshold hT
  have hL_lt_q : 2 ≤ ℓ → ProximityGap.maxYDeg (k - 1) D < Fintype.card F := fun _ =>
    (maxYDeg_le_johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 W_tot).trans_lt hB_lt_q
  obtain ⟨D', _, hD'_ge, v₀, hv₀, v, hvRS, hagree⟩ :=
    exists_weighted_correlatedAgreement_affine_of_line
      (C := reedSolomon α k) (W := W) (B_W := B_W)
      (B_line := ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 W_tot)
      (L := ProximityGap.maxYDeg (k - 1) D)
      (fun w => card_reedSolomon_list_le_maxYDeg hα hk hm hM hW_le hinterp hroot w)
      (fun {B'} hB' a b S hS hcl => by
        have ht_le : (B_W + M - 1) / M ≤ (B' + M - 1) / M :=
          Nat.div_le_div_right (by omega)
        exact exists_weighted_correlatedAgreement_line_johnson hα hk hm hM hW_le hW_sum
          (hk_le_t.trans ht_le) hinterp (hroot.trans_le (Nat.mul_le_mul_left m ht_le))
          a b S hS hcl)
      hL_lt_q u₀ u T hT hclose
  exact ⟨D', hD'_ge, v₀, hv₀, v, hvRS, hagree⟩

/-- **Explicit-parameter correlated-agreement step on affine spaces up to the Johnson bound**
(in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.6], printed p. 6 of the
accepted JACM 2023 manuscript).

Unweighted specialization (`W = 1`) of
`Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson` with exact threshold
`johnsonCurveBound |ι| m (k - 1) D 1 |ι| * |F| ^ ℓ < |F| * #T` and no extra list-size premise. -/
theorem exists_correlatedAgreement_affine_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ e m D : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hk_le : k ≤ Fintype.card ι - e)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * (Fintype.card ι - e))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 (Fintype.card ι) *
        (Fintype.card F) ^ ℓ < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  have hceil : (Fintype.card ι - e + 1 - 1) / 1 = Fintype.card ι - e := by omega
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ := exists_weighted_correlatedAgreement_affine_johnson
    (W := fun _ => 1) (M := 1) (W_tot := Fintype.card ι) (B_W := Fintype.card ι - e)
    hα hk hm Nat.one_pos (fun _ => le_rfl) (by simp) (by rwa [hceil]) hinterp (by rwa [hceil])
    u₀ u T hT fun z hz => let ⟨c, hcRS, hd⟩ := hclose z hz
      ⟨c, hcRS, by simpa using card_filter_eq_of_hammingDist_le hd⟩
  exact ⟨D', by simpa using hD', v₀, hv₀, v, hvRS, hagree⟩

/-- **Explicit-parameter `ℚ`-weighted correlated-agreement step on affine spaces up to the Johnson
bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on printed p. 6 and
Theorems 7.3–7.4 on printed p. 32 of the accepted JACM 2023 manuscript).

For rational coordinate weights `μ : ι → ℚ` in `{0, 1 / M, …, 1}` (`0 < M`, zero weights allowed),
threshold `θ : ℚ` with `(k : ℚ) ≤ θ` and `(D : ℚ) < m * θ`, and Guruswami–Sudan interpolation
condition `|ι| * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D)`, if
`johnsonCurveBound |ι| m (k - 1) D 1 (M * |ι|) * |F| ^ ℓ < |F| * #T` then there exist a shared
coordinate subset `D' : Finset ι` with `θ ≤ ∑ i ∈ D', μ i` and codewords `v₀, v_j ∈ reedSolomon α k`
agreeing with `u₀, u_j` on `D'`, with no list-size premise. -/
theorem exists_ratWeighted_correlatedAgreement_affine_johnson
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
    (T : Finset (Fin ℓ → F))
    (hT : ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1
        (M * Fintype.card ι) * (Fintype.card F) ^ ℓ < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  obtain ⟨W, hW_le, hW_sum, hk_le_t, hroot_nat, hsum_iff⟩ :=
    rat_weights_johnson_nat hM hμ_le hμ_den hk_le hroot
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ := exists_weighted_correlatedAgreement_affine_johnson
    hα hk hm hM hW_le hW_sum hk_le_t hinterp hroot_nat u₀ u T hT
    fun z hz => let ⟨c, hcRS, hge⟩ := hclose z hz; ⟨c, hcRS, (hsum_iff _).1 hge⟩
  exact ⟨D', (hsum_iff D').2 hD', v₀, hv₀, v, hvRS, hagree⟩

/-- **Original explicit-constant correlated-agreement variant on affine spaces up to the Johnson
bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.6], printed p. 6 of
the accepted JACM 2023 manuscript).

For any affine dimension `ℓ : ℕ`, `1 ≤ k ≤ n`, multiplicity parameter `m ≥ 1`, and proximity radius
`(e : ℝ) / n ≤ 1 - √ρ - √ρ / (2 * m)` (`ρ = k / n`), if the close parameter subset `T` has density
strictly above `1800 * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)` (independent of `ℓ`, with no list-size
premise), then all affine generators `u₀, u_j` simultaneously agree with codewords
`v₀, v_j ∈ reedSolomon α k` on a shared coordinate subset `D'` of size at least `n - e`. While
`(m + 1) ^ 6 / ρ` has smaller exponents in `m` and `1 / ρ` than the paper's displayed
`(m + 1 / 2) ^ 7 / (3 * ρ ^ (3 / 2))` expression, this explicit constant is not uniformly smaller
at small finite `m`. -/
theorem exists_correlatedAgreement_affine_johnson_of_multiplicity
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k m ℓ : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hm : 1 ≤ m)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : 1800 * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
        (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) <
      (T.card : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  obtain ⟨hk_sub, hinterp, hroot, hjb⟩ := ProximityGap.johnson_line_params_bound hk hkn hm he
  have hdiv := div_le_div_of_nonneg_right hjb (Nat.cast_nonneg (Fintype.card F))
  rw [div_div] at hdiv
  exact exists_correlatedAgreement_affine_johnson hα hk (by omega) hk_sub hinterp hroot
    u₀ u T (affine_mul_lt_of_density_lt Fintype.card_pos (hdiv.trans_lt hT)) hclose

/-- **Original explicit-constant correlated-agreement variant on affine spaces up to
`1 - √ρ - η`** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.6], printed
p. 6 of the accepted JACM 2023 manuscript).

Closed-form corollary of `Cslib.Code.exists_correlatedAgreement_affine_johnson_of_multiplicity`
for any gap `η > 0` below `1 - √ρ`, establishing simultaneous generator correlated agreement on a
shared coordinate subset `D'` of size at least `n - e` whenever `#T / |F| ^ ℓ` exceeds
`115200 * n ^ 2 / (ρ * η ^ 6 * |F|)` (independent of `ℓ`, with no list-size premise). -/
theorem exists_correlatedAgreement_affine_johnson_of_eta
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k ℓ : ℕ} {η : ℝ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hη : 0 < η)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) - η)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : 115200 * ((Fintype.card ι : ℝ) ^ 2) /
        (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)) <
      (T.card : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  obtain ⟨m, hm, he', hpow⟩ := ProximityGap.exists_multiplicity_of_eta hk hkn hη he
  exact exists_correlatedAgreement_affine_johnson_of_multiplicity hα hk hkn hm he' u₀ u T
    (lt_of_le_of_lt (by simpa only [mul_one] using
      siegel_eta_bound_le hk hkn (Fintype.card_pos (α := F)) zero_le_one hη hpow) hT)
    hclose

/-- **Original explicit-constant `ℕ`-weighted correlated-agreement variant on affine spaces up to
the Johnson bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on
printed p. 6 and Theorems 7.3–7.4 on printed p. 32 of the accepted JACM 2023 manuscript).

For integer weights `W : ι → ℕ` bounded by `M > 0` (zero weights allowed) and threshold `B_W : ℕ`
with `((n - (B_W + M - 1) / M : ℕ) : ℝ) / n ≤ 1 - √ρ - √ρ / (2 * m)`, density strictly above
`1800 * M * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)` yields simultaneous generator correlated agreement of
`W`-weight at least `B_W`, independent of `ℓ` and with no extra list-size premise. -/
theorem exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k m ℓ M B_W : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hB : ((Fintype.card ι - (B_W + M - 1) / M : ℕ) : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : 1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
        (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) <
      (T.card : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) :
    ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  have hpos : 0 < 1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
      (((k : ℝ) / Fintype.card ι) * Fintype.card F) := by
    have : 1 ≤ Fintype.card ι := hk.trans hkn
    have : 0 < Fintype.card F := Fintype.card_pos; positivity
  obtain ⟨z₀, hz₀⟩ := nonempty_of_pos_lt_density hpos hT
  have hBW_le : B_W ≤ M * Fintype.card ι :=
    let ⟨_, _, hge⟩ := hclose z₀ hz₀; hge.trans (sum_le_mul_card_of_le hW _)
  have ht_le : (B_W + M - 1) / M ≤ Fintype.card ι :=
    (Nat.div_le_iff_le_mul_add_pred hM).2 (by omega)
  obtain ⟨hk_sub, hinterp, hroot, hjb⟩ := ProximityGap.johnson_line_params_bound
    (e := Fintype.card ι - (B_W + M - 1) / M) hk hkn hm hB
  rw [Nat.sub_sub_self ht_le] at hk_sub hroot
  have hdiv := div_le_div_of_nonneg_right (johnsonCurveBound_mul_cast_le (hk.trans hkn) hM hjb)
    (Nat.cast_nonneg (Fintype.card F))
  exact exists_weighted_correlatedAgreement_affine_johnson hα hk (by omega) hM hW
    (sum_le_mul_card_of_le hW univ) hk_sub hinterp hroot u₀ u T
    (affine_mul_lt_of_density_lt Fintype.card_pos
      ((hdiv.trans_eq (by rw [mul_div_assoc', div_div]; ring)).trans_lt hT)) hclose

/-- **Original explicit-constant `ℕ`-weighted correlated-agreement variant on affine spaces up to
`1 - √ρ - η`** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on printed
p. 6 and Theorems 7.3–7.4 on printed p. 32 of the accepted JACM 2023 manuscript). -/
theorem exists_weighted_correlatedAgreement_affine_johnson_of_eta
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k ℓ M B_W : ℕ} {η : ℝ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hM : 0 < M) (hη : 0 < η)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hB : ((Fintype.card ι - (B_W + M - 1) / M : ℕ) : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) - η)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : 115200 * (M : ℝ) * ((Fintype.card ι : ℝ) ^ 2) /
        (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)) <
      (T.card : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) :
    ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  obtain ⟨m, hm, hB', hpow⟩ := ProximityGap.exists_multiplicity_of_eta hk hkn hη hB
  exact exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity hα hk hkn hm hM hW hB'
    u₀ u T
    ((siegel_eta_bound_le hk hkn Fintype.card_pos (Nat.cast_nonneg M) hη hpow).trans_lt hT) hclose

/-- **Original explicit-constant `ℚ`-weighted correlated-agreement variant on affine spaces up to
the Johnson bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on
printed p. 6 and Theorems 7.3–7.4 on printed p. 32 of the accepted JACM 2023 manuscript).

For rational coordinate weights `μ : ι → ℚ` in `{0, 1 / M, …, 1}` (`0 < M`, zero weights allowed)
and threshold `θ : ℚ` with `1 - θ / n ≤ 1 - √ρ - √ρ / (2 * m)`, density strictly above
`1800 * M * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)` yields simultaneous generator correlated agreement of
`μ`-weight at least `θ`, independent of `ℓ` and with no extra list-size premise. -/
theorem exists_ratWeighted_correlatedAgreement_affine_johnson_of_multiplicity
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
    (T : Finset (Fin ℓ → F))
    (hT : 1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
        (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) <
      (T.card : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  have hB : 0 < (1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
      (((k : ℝ) / Fintype.card ι) * Fintype.card F)) := by
    have : 0 < Fintype.card ι := hk.trans hkn
    have : 0 < Fintype.card F := Fintype.card_pos; positivity
  exact ratWeighted_to_nat_affine_ca hk hkn hM hμ_le hμ_den hθ (nonempty_of_pos_lt_density hB hT)
    hclose fun hW_le hB' hclW => exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity
      hα hk hkn hm hM hW_le hB' u₀ u T hT hclW

/-- **Original explicit-constant `ℚ`-weighted correlated-agreement variant on affine spaces up to
`1 - √ρ - η`** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on printed
p. 6 and Theorems 7.3–7.4 on printed p. 32 of the accepted JACM 2023 manuscript).

For rational coordinate weights `μ : ι → ℚ` in `{0, 1 / M, …, 1}` (`0 < M`, zero weights allowed),
any gap `η > 0`, and threshold `θ : ℚ` with `1 - θ / n ≤ 1 - √ρ - η`, density strictly above
`115200 * M * n ^ 2 / (ρ * η ^ 6 * |F|)` yields simultaneous generator correlated agreement of
`μ`-weight at least `θ`, independent of `ℓ` and with no extra list-size premise. -/
theorem exists_ratWeighted_correlatedAgreement_affine_johnson_of_eta
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k ℓ M : ℕ} {η : ℝ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hM : 0 < M) (hη : 0 < η)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ}
    (hθ : 1 - (θ : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) - η)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : 115200 * (M : ℝ) * ((Fintype.card ι : ℝ) ^ 2) /
        (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)) <
      (T.card : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i :=
  ratWeighted_to_nat_affine_ca hk hkn hM hμ_le hμ_den hθ
    (nonempty_of_pos_lt_density (by
      have : 1 ≤ Fintype.card ι := hk.trans hkn
      have : 0 < Fintype.card F := Fintype.card_pos; positivity) hT)
    hclose fun hW_le hB hclW =>
      exists_weighted_correlatedAgreement_affine_johnson_of_eta hα hk hkn hM hη hW_le hB
        u₀ u T hT hclW

end Cslib.Code
