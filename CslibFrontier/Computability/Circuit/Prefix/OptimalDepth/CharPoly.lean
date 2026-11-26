/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Characteristic polynomial `P_k` and positive growth root `α_k`

Characteristic polynomial `P_k(x) = 2 + x + ⋯ + x^{k-2} - x^k` (`prefixCharPoly k`) and its unique
positive real root `α_k` (`alphaRoot k`) governing the asymptotic depth of optimal fanout-`k`
universal prefix circuits [Sergeev2025PrefixDepth].

## Main definitions

* `Cslib.Circuits.Prefix.prefixCharPoly`: characteristic polynomial
  `P_k(x) = 2 + x + ⋯ + x^{k-2} - x^k`.
* `Cslib.Circuits.Prefix.alphaRoot`: unique positive root `α_k` of `prefixCharPoly k` for `k ≥ 2`.

## Main results

* `Cslib.Circuits.Prefix.prefixCharPoly_alphaRoot`,
  `Cslib.Circuits.Prefix.eq_alphaRoot_of_pos_of_prefixCharPoly_eq_zero`: existence and uniqueness of
  the positive root `α_k`.
* `Cslib.Circuits.Prefix.one_lt_alphaRoot`,
  `Cslib.Circuits.Prefix.alphaRoot_lt_goldenRatio`,
  `Cslib.Circuits.Prefix.three_halves_lt_alphaRoot`,
  `Cslib.Circuits.Prefix.alphaRoot_two`: enclosure `1 < α_k < φ`, `3 / 2 < α_k` (`k ≥ 3`), and
  `α_2 = √2`.
* `Cslib.Circuits.Prefix.alphaRoot_strictMonoOn`,
  `Cslib.Circuits.Prefix.tendsto_alphaRoot_atTop`: strict monotonicity on `k ≥ 2` and convergence
  `α_k → φ`.

## References

* [I. S. Sergeev, *A Note on the Depth of Optimal Fanout-Bounded Prefix
  Circuits*][Sergeev2025PrefixDepth]
-/

public section

namespace Cslib.Circuits.Prefix

/-- Characteristic polynomial `P_k(x) = 2 + x + ⋯ + x^{k-2} - x^k` governing the asymptotic growth
of optimal fanout-`k` prefix circuit widths ([Sergeev2025PrefixDepth], p. 2). -/
@[expose] def prefixCharPoly (k : ℕ) (x : ℝ) : ℝ :=
  2 + (∑ i ∈ Finset.Ico 1 (k - 1), x ^ i) - x ^ k

private theorem prefixCharPoly_succ_sub {k : ℕ} (hk : 2 ≤ k) (x : ℝ) :
    prefixCharPoly (k + 1) x - prefixCharPoly k x = x ^ (k - 1) * (1 + x - x ^ 2) := by
  unfold prefixCharPoly
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel, Finset.sum_Ico_succ_top (by omega)]
  ring

private theorem sub_one_mul_prefixCharPoly {k : ℕ} (hk : 2 ≤ k) (x : ℝ) :
    (x - 1) * prefixCharPoly k x = (x - 2) + x ^ (k - 1) * (1 + x - x ^ 2) := by
  induction hk with
  | refl =>
    unfold prefixCharPoly
    simp only [Nat.reduceSub, Finset.Ico_self, Finset.sum_empty, pow_one]
    ring
  | @step m hm ih =>
    have hm2 : 2 ≤ m := hm
    have hdiff := sub_eq_iff_eq_add'.mp (prefixCharPoly_succ_sub hm2 x)
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    change (x - 1) * prefixCharPoly (j + 1 + 1) x = x - 2 + x ^ (j + 1) * (1 + x - x ^ 2)
    simp only [Nat.add_sub_cancel] at ih hdiff
    rw [hdiff, mul_add, ih]
    ring

private theorem prefixCharPoly_continuous (k : ℕ) : Continuous (prefixCharPoly k) := by
  unfold prefixCharPoly
  fun_prop

private theorem prefixCharPoly_one_pos (k : ℕ) : 0 < prefixCharPoly k 1 := by
  unfold prefixCharPoly
  simp only [one_pow, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  linarith [Nat.cast_nonneg (α := ℝ) (k - 1 - 1)]

private theorem prefixCharPoly_goldenRatio_neg {k : ℕ} (hk : 2 ≤ k) :
    prefixCharPoly k Real.goldenRatio < 0 := by
  have htel := sub_one_mul_prefixCharPoly hk Real.goldenRatio
  have hgold : 1 + Real.goldenRatio - Real.goldenRatio ^ 2 = 0 := by linarith [Real.goldenRatio_sq]
  rw [hgold, mul_zero, add_zero] at htel
  exact neg_of_mul_neg_right (htel.trans_lt (by linarith [Real.goldenRatio_lt_two]))
    (sub_nonneg.mpr Real.one_lt_goldenRatio.le)

private theorem prefixCharPoly_three_halves_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < prefixCharPoly k (3 / 2) := by
  have htel := sub_one_mul_prefixCharPoly (by omega : 2 ≤ k) (3 / 2)
  have hpow : (3 / 2 : ℝ) ^ 2 ≤ (3 / 2 : ℝ) ^ (k - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at htel hpow
  linarith

private noncomputable def invPoly (k : ℕ) (x : ℝ) : ℝ :=
  2 * (x⁻¹) ^ k + (∑ i ∈ Finset.Ico 1 (k - 1), (x⁻¹) ^ (k - i)) - 1

private theorem pow_mul_invPoly {k : ℕ} {x : ℝ} (hx : 0 < x) :
    x ^ k * invPoly k x = prefixCharPoly k x := by
  unfold invPoly prefixCharPoly
  have hne : x ≠ 0 := hx.ne'
  have h1 : x ^ k * (2 * (x⁻¹) ^ k) = 2 := by
    rw [← mul_assoc, mul_comm (x ^ k) 2, mul_assoc, ← mul_pow, mul_inv_cancel₀ hne,
      one_pow, mul_one]
  have h2 : x ^ k * (∑ i ∈ Finset.Ico 1 (k - 1), (x⁻¹) ^ (k - i)) =
      ∑ i ∈ Finset.Ico 1 (k - 1), x ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_Ico] at hi
    have hxk : x ^ k = x ^ i * x ^ (k - i) := by
      rw [← pow_add, Nat.add_sub_of_le (by omega)]
    rw [hxk, mul_assoc, ← mul_pow, mul_inv_cancel₀ hne, one_pow, mul_one]
  linarith

private theorem invPoly_strictAnti {k : ℕ} (hk : 2 ≤ k) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    invPoly k y < invPoly k x := by
  unfold invPoly
  have hy_inv : 0 < y⁻¹ := inv_pos.mpr (hx.trans hxy)
  have hinv : y⁻¹ < x⁻¹ := (inv_lt_inv₀ (hx.trans hxy) hx).mpr hxy
  have hpow_lt : (y⁻¹) ^ k < (x⁻¹) ^ k := pow_lt_pow_left₀ hinv hy_inv.le (by omega)
  have hsum_le : (∑ i ∈ Finset.Ico 1 (k - 1), (y⁻¹) ^ (k - i)) ≤
      ∑ i ∈ Finset.Ico 1 (k - 1), (x⁻¹) ^ (k - i) :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ hy_inv.le hinv.le _
  linarith

private theorem exists_root_mem_Icc {k : ℕ} (hk : 2 ≤ k) :
    ∃ r ∈ Set.Icc 1 Real.goldenRatio, prefixCharPoly k r = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Icc (prefixCharPoly k Real.goldenRatio) (prefixCharPoly k 1) :=
    ⟨(prefixCharPoly_goldenRatio_neg hk).le, (prefixCharPoly_one_pos k).le⟩
  exact intermediate_value_Icc' Real.one_lt_goldenRatio.le
    (prefixCharPoly_continuous k).continuousOn hmem

/-- For `k ≥ 2`, the unique positive real root `α_k` of `prefixCharPoly k`
([Sergeev2025PrefixDepth], p. 2). Returns `0` when `k < 2`. -/
noncomputable def alphaRoot (k : ℕ) : ℝ :=
  if hk : 2 ≤ k then Classical.choose (exists_root_mem_Icc hk) else 0

private theorem alphaRoot_mem_Icc {k : ℕ} (hk : 2 ≤ k) :
    alphaRoot k ∈ Set.Icc 1 Real.goldenRatio := by
  rw [alphaRoot, dite_eq_left hk]
  exact (Classical.choose_spec (exists_root_mem_Icc hk)).1

/-- `alphaRoot k` is a root of `prefixCharPoly k` for all `k ≥ 2`
([Sergeev2025PrefixDepth], p. 2). -/
theorem prefixCharPoly_alphaRoot {k : ℕ} (hk : 2 ≤ k) :
    prefixCharPoly k (alphaRoot k) = 0 := by
  rw [alphaRoot, dite_eq_left hk]
  exact (Classical.choose_spec (exists_root_mem_Icc hk)).2

/-- `1 < alphaRoot k` for all `k ≥ 2`. -/
theorem one_lt_alphaRoot {k : ℕ} (hk : 2 ≤ k) : 1 < alphaRoot k :=
  lt_of_le_of_ne (alphaRoot_mem_Icc hk).1 fun h => by
    linarith [prefixCharPoly_one_pos k, h ▸ prefixCharPoly_alphaRoot hk]

/-- `alphaRoot k < Real.goldenRatio` for all `k ≥ 2`, immediate from `P_k(φ) < 0` for the
characteristic polynomial `P_k(x)` ([Sergeev2025PrefixDepth], p. 2). -/
theorem alphaRoot_lt_goldenRatio {k : ℕ} (hk : 2 ≤ k) :
    alphaRoot k < Real.goldenRatio :=
  lt_of_le_of_ne (alphaRoot_mem_Icc hk).2 fun h => by
    linarith [prefixCharPoly_goldenRatio_neg hk, h ▸ prefixCharPoly_alphaRoot hk]

private theorem alphaRoot_pos {k : ℕ} (hk : 2 ≤ k) : 0 < alphaRoot k :=
  zero_lt_one.trans (one_lt_alphaRoot hk)

private theorem invPoly_eq_zero_iff {k : ℕ} {x : ℝ} (hx : 0 < x) :
    invPoly k x = 0 ↔ prefixCharPoly k x = 0 := by
  rw [← pow_mul_invPoly hx, mul_eq_zero, or_iff_right (pow_pos hx k).ne']

private theorem lt_alphaRoot_of_pos_of_prefixCharPoly_pos {k : ℕ} {x : ℝ}
    (hk : 2 ≤ k) (hx : 0 < x) (hpos : 0 < prefixCharPoly k x) :
    x < alphaRoot k := by
  have hinv_pos : 0 < invPoly k x :=
    pos_of_mul_pos_right (pow_mul_invPoly hx ▸ hpos) (pow_nonneg hx.le k)
  have hinv_root := (invPoly_eq_zero_iff (alphaRoot_pos hk)).mpr (prefixCharPoly_alphaRoot hk)
  by_contra! hle
  rcases eq_or_lt_of_le hle with rfl | hlt
  · linarith
  · linarith [invPoly_strictAnti hk (alphaRoot_pos hk) hlt]

/-- Uniqueness of the positive root `alphaRoot k` of `prefixCharPoly k` for `k ≥ 2`
([Sergeev2025PrefixDepth], p. 2). -/
theorem eq_alphaRoot_of_pos_of_prefixCharPoly_eq_zero {k : ℕ} {x : ℝ}
    (hk : 2 ≤ k) (hx : 0 < x) (h0 : prefixCharPoly k x = 0) :
    x = alphaRoot k := by
  have hinv_x := (invPoly_eq_zero_iff hx).mpr h0
  have hinv_root := (invPoly_eq_zero_iff (alphaRoot_pos hk)).mpr (prefixCharPoly_alphaRoot hk)
  rcases lt_trichotomy x (alphaRoot k) with hlt | heq | hgt
  · linarith [invPoly_strictAnti hk hx hlt]
  · exact heq
  · linarith [invPoly_strictAnti hk (alphaRoot_pos hk) hgt]

/-- Original auxiliary root lower bound `3 / 2 < alphaRoot k` for all `k ≥ 3` (via
`prefixCharPoly k (3 / 2) > 0`), used in the inhomogeneous recurrence bound of
`width_le_mul_alphaRoot_pow`. -/
theorem three_halves_lt_alphaRoot {k : ℕ} (hk : 3 ≤ k) :
    (3 / 2 : ℝ) < alphaRoot k :=
  lt_alphaRoot_of_pos_of_prefixCharPoly_pos (by omega) (by norm_num)
    (prefixCharPoly_three_halves_pos hk)

/-- At fanout `k = 2`, `alphaRoot 2 = √2`, immediate from `P_2(x) = 2 - x^2`
([Sergeev2025PrefixDepth], p. 2). -/
theorem alphaRoot_two : alphaRoot 2 = Real.sqrt 2 := by
  symm
  refine eq_alphaRoot_of_pos_of_prefixCharPoly_eq_zero le_rfl (Real.sqrt_pos.mpr (by norm_num)) ?_
  unfold prefixCharPoly
  simp only [Nat.reduceSub, Finset.Ico_self, Finset.sum_empty, add_zero]
  rw [Real.sq_sqrt (by norm_num)]
  ring

/-- The positive roots `alphaRoot k` form a strictly increasing sequence on `k ≥ 2`, immediate from
the definition of `P_k(x)` ([Sergeev2025PrefixDepth], p. 2). -/
theorem alphaRoot_strictMonoOn : StrictMonoOn alphaRoot (Set.Ici 2) := by
  have hstep : ∀ k ≥ 2, alphaRoot k < alphaRoot (k + 1) := fun k hk => by
    have htel := sub_one_mul_prefixCharPoly hk (alphaRoot k)
    have hdiff := prefixCharPoly_succ_sub hk (alphaRoot k)
    rw [prefixCharPoly_alphaRoot hk, mul_zero] at htel
    rw [prefixCharPoly_alphaRoot hk, sub_zero] at hdiff
    have hlt2 := (alphaRoot_lt_goldenRatio hk).trans Real.goldenRatio_lt_two
    exact lt_alphaRoot_of_pos_of_prefixCharPoly_pos (by omega) (alphaRoot_pos hk) (by linarith)
  rintro a ha b - hab
  induction b, hab using Nat.le_induction with
  | base => exact hstep a ha
  | succ b hab ih => exact ih.trans (hstep b (ha.trans (Nat.le_of_succ_le hab)))

/-- As `k → ∞`, `alphaRoot k` converges to the golden ratio `φ = (1 + √5) / 2`
([Sergeev2025PrefixDepth], p. 2). -/
theorem tendsto_alphaRoot_atTop :
    Filter.Tendsto alphaRoot Filter.atTop (nhds Real.goldenRatio) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have h54_lt : (5 / 4 : ℝ) < Real.goldenRatio := by
      by_contra! hle
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
    set c := max a (5 / 4)
    have hc1 : 1 < c := lt_of_lt_of_le (by norm_num) (le_max_right a _)
    have hc_lt : c < Real.goldenRatio := max_lt ha h54_lt
    have hquad_pos : 0 < 1 + c - c ^ 2 := by
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp <| Filter.tendsto_atTop.mp
      (tendsto_pow_atTop_atTop_of_one_lt hc1) ((2 - c) / (1 + c - c ^ 2) + 1)
    refine Filter.eventually_atTop.mpr ⟨max 2 (M + 1), fun k hk => ?_⟩
    have hk2 : 2 ≤ k := (le_max_left _ _).trans hk
    have hcm := hM (k - 1) (by have := (le_max_right 2 (M + 1)).trans hk; omega)
    have hmul_gt : 2 - c < c ^ (k - 1) * (1 + c - c ^ 2) :=
      (div_lt_iff₀ hquad_pos).mp (by linarith)
    have hc_poly_pos : 0 < prefixCharPoly k c :=
      pos_of_mul_pos_right (a := c - 1) (by linarith [sub_one_mul_prefixCharPoly hk2 c])
        (by linarith)
    exact (le_max_left a _).trans_lt
      (lt_alphaRoot_of_pos_of_prefixCharPoly_pos hk2 (by linarith) hc_poly_pos)
  · exact Filter.eventually_atTop.mpr ⟨2, fun k hk => (alphaRoot_lt_goldenRatio hk).trans hb⟩

private theorem pow_recurrence_sub {k D : ℕ} (hk : 2 ≤ k) (hD : k ≤ D) (x : ℝ) :
    x ^ D - (∑ j ∈ Finset.Ico 2 k, x ^ (D - j)) - 2 * x ^ (D - k) =
      -x ^ (D - k) * prefixCharPoly k x := by
  unfold prefixCharPoly
  have hsum : ∑ j ∈ Finset.Ico 2 k, x ^ (D - j) =
      x ^ (D - k) * ∑ i ∈ Finset.Ico 1 (k - 1), x ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun j _ => k - j) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
    · intro j₁ hj₁ j₂ hj₂ heq; simp only [Finset.mem_Ico] at hj₁ hj₂; omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      exact ⟨k - i, by simp only [Finset.mem_Ico]; omega, by omega⟩
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      have hsub : D - k + (k - j) = D - j := by omega
      rw [← pow_add, hsub]
  have hpow : x ^ D = x ^ (D - k) * x ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hD]
  rw [hsum, hpow]
  ring


end Cslib.Circuits.Prefix
