/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.KWiseIndependent
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.KWiseIndependent.Concentration
import Mathlib.Algebra.BigOperators.Balance
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Variance-Aware `2m`-th Moment and Collision-Concentration Bounds for `k`-Wise Independence

This module provides two high-probability concentration tools for `k`-wise independent hash families
(`Cslib.Probability.IsKWiseIndependentHash`):

1. **Heterogeneous variance-aware `2 m`-th moment and tail bounds**
   (`expect_sum_pow_le_of_sq_le`, `dens_filter_le_abs_sum_of_sq_le`,
   `dens_filter_le_abs_sum_sub_expect_of_Icc`):
   Refines `IsKWiseIndependentHash.expect_sum_pow_le` when centered terms `Z x` (`|Z x| ≤ 1`)
   satisfy per-coordinate second-moment bounds `𝔼 y, (Z x y) ^ 2 ≤ v x` (`0 ≤ v x`). Replacing `#S`
   with `max (∑ x ∈ S, v x) 1` gives tail density `m * (m ^ 2 * max (∑ x ∈ S, v x) 1 / a ^ 2) ^ m`,
   yielding polynomial `1 - n ^ (-c)` concentration under `O(c log n)`-wise independence whenever
   `a ^ 2 ≥ Ω(m ^ 2 * max (∑ x ∈ S, v x) 1)` (because `sum_prod_image_eq_card_le` drops the `1 / r!`
   symmetry factor, leaving `m ^ 2` rather than `m` in the numerator).
   Compare `CslibFrontier.Probability.KWiseIndependent.Concentration`
   (`expect_sum_sub_expect_pow_le`, `dens_abs_sum_sub_expect_le`), which retains `1 / r!` for
   `[0, 1]`-valued variables under the lower-mean regime `2 * m ≤ 3 * μ` to obtain
   `2 * (3 * m * μ / a ^ 2) ^ m` (supporting `O(c log n / log log n)`-wise unit-mean balls-into-bins
   bounds when `2 * m ≤ 3 * μ`), whereas the bounds here apply to general centered `[-1, 1]`
   variables and arbitrary `∑ x ∈ S, v x` without requiring `2 * m ≤ 3 * ∑ x ∈ S, v x`.
2. **Multi-salt collision-freedom and batch collision-count tail bounds**
   (`dens_forall_salt_exists_collision_le`, `dens_card_salt_colliding_ge_le`):
   Bounds the probability that all `s_max` salts collide on a bucket under `2 * s_max`-wise
   independence, and bounds via greedy independent-witness extraction the probability that at least
   `2 * r` keys in a batch `Q_set` collide with a window `W_set` across `s_max` salts under
   `2 * r`-wise independence.

## Main results

* `Cslib.Probability.IsKWiseIndependentHash.expect_sum_pow_le_of_sq_le`:
  `𝔼 i, (∑ x ∈ S, Z x (h i x)) ^ (2 * m) ≤ m * m ^ (2 * m) * max (∑ x ∈ S, v x) 1 ^ m`.
* `Cslib.Probability.IsKWiseIndependentHash.dens_filter_le_abs_sum_of_sq_le`:
  `dens {i | a ≤ |∑ x ∈ S, Z x (h i x)|} ≤ m * (m ^ 2 * max (∑ x ∈ S, v x) 1 / a ^ 2) ^ m`.
* `Cslib.Probability.IsKWiseIndependentHash.dens_filter_le_abs_sum_sub_expect_of_Icc`:
  specialization to `[0, 1]`-valued random variables `g x : Y → [0, 1]`.
* `Cslib.Probability.IsKWiseIndependentHash.dens_forall_salt_exists_collision_le`:
  probability that every salt `s : Fin s_max` has an intra-bucket collision on `S_b` is at most
  `(#S_b ^ 2 / |Y|) ^ s_max`.
* `Cslib.Probability.IsKWiseIndependentHash.dens_card_salt_colliding_ge_le`,
  `Cslib.Probability.IsKWiseIndependentHash.dens_card_local_salt_colliding_ge_le`:
  probability that at least `2 * r` keys in `Q_set` collide with `W_set` (or per-key neighborhoods
  `W_of u` of size `≤ w_cap`) under some salt in `Fin s_max`.

## References

* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

public section

namespace Cslib.Probability

open Finset Fintype
open scoped BigOperators

namespace IsKWiseIndependentHash

variable {ι X Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y] {h : ι → X → Y}

/-! ## Section 1: Heterogeneous variance-aware `2 m`-th moment bound -/

/-- Factoring tuples `t ∈ S ^ n` whose image has exact cardinality `r ≥ 1` through
`(Fin n → Fin r) × (Fin r → S)` bounds the sum of `∏ x ∈ univ.image t, v x` by
`r ^ n * (∑ x ∈ S, v x) ^ r` for any nonnegative weights `v : X → ℝ`. -/
private theorem sum_prod_image_eq_card_le [DecidableEq X] (S : Finset X) (v : X → ℝ)
    (hv : ∀ x ∈ S, 0 ≤ v x) (n : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    (∑ t ∈ (piFinset fun _ : Fin n => S).filter (fun t => #(univ.image t) = r),
      ∏ x ∈ univ.image t, v x) ≤
      (r : ℝ) ^ n * (∑ x ∈ S, v x) ^ r := by
  set T_filt := (piFinset fun _ : Fin n => S).filter (fun t => #(univ.image t) = r)
  let P_idx := piFinset fun _ : Fin n => (univ : Finset (Fin r))
  let P_val := piFinset fun _ : Fin r => S
  -- Each `t ∈ T_filt` factors as `w ∘ f` through an enumeration of its `r`-element image.
  have hsec : ∀ t ∈ T_filt, ∃ q ∈ P_idx ×ˢ P_val,
      q.2 ∘ q.1 = t ∧ (∏ x ∈ univ.image t, v x) = ∏ k : Fin r, v (q.2 k) := by
    intro t ht
    rw [mem_filter, mem_piFinset] at ht
    let I := univ.image t
    let e : I ≃ Fin r := I.equivFin.trans (finCongr ht.2)
    refine ⟨(fun j => e ⟨t j, mem_image_of_mem t (mem_univ j)⟩, fun k => (e.symm k).1),
      mem_product.mpr ⟨by simp [P_idx], mem_piFinset.mpr fun k => ?_⟩, funext fun j => by simp, ?_⟩
    · obtain ⟨j, -, hj⟩ := mem_image.mp (e.symm k).2
      exact show (e.symm k).1 ∈ S from hj ▸ ht.1 j
    · rw [← prod_coe_sort]
      exact (e.symm.prod_comp fun x : I => v x).symm
  rcases isEmpty_or_nonempty ((Fin n → Fin r) × (Fin r → X)) with hE | hE
  · rw [T_filt.eq_empty_of_forall_notMem fun t ht => hE.false (hsec t ht).choose, Finset.sum_empty]
    have := sum_nonneg hv
    positivity
  choose! sec hsec_mem hsec_comp hsec_prod using hsec
  calc (∑ t ∈ T_filt, ∏ x ∈ univ.image t, v x)
      ≤ ∑ q ∈ P_idx ×ˢ P_val, ∏ k : Fin r, v (q.2 k) :=
        sum_le_sum_of_injOn sec
          (fun t₁ h₁ t₂ h₂ h => by rw [← hsec_comp t₁ h₁, ← hsec_comp t₂ h₂, h])
          (fun _ hq => by obtain ⟨t, ht, rfl⟩ := mem_image.mp hq; exact hsec_mem t ht)
          (fun t ht => (hsec_prod t ht).le)
          fun q hq _ => prod_nonneg fun k _ => hv _ (mem_piFinset.mp (mem_product.mp hq).2 k)
    _ = (r : ℝ) ^ n * (∑ x ∈ S, v x) ^ r := by
        simp only [sum_product, sum_const, P_val, ← sum_pow']
        simp [P_idx]

/-- **Heterogeneous variance-aware `2 m`-th moment bound for limited independence**:
For `1 ≤ m`, a `2 * m`-wise independent family `h : ι → X → Y`, a finite set `S : Finset X`, and
centered scores `Z : X → Y → ℝ` with `|Z x y| ≤ 1` and `𝔼 y, (Z x y) ^ 2 ≤ v x` (`0 ≤ v x`),
`𝔼 i, (∑ x ∈ S, Z x (h i x)) ^ (2 * m) ≤ m * m ^ (2 * m) * max (∑ x ∈ S, v x) 1 ^ m`. -/
theorem expect_sum_pow_le_of_sq_le {m : ℕ} (hm : 1 ≤ m) (hh : IsKWiseIndependentHash (2 * m) h)
    (S : Finset X) (Z : X → Y → ℝ) (v : X → ℝ)
    (hv : ∀ x ∈ S, 0 ≤ v x)
    (hZ : ∀ x ∈ S, 𝔼 y, Z x y = 0)
    (hZ₁ : ∀ x ∈ S, ∀ y, |Z x y| ≤ 1)
    (hZ₂ : ∀ x ∈ S, 𝔼 y, (Z x y) ^ 2 ≤ v x) :
    𝔼 i, (∑ x ∈ S, Z x (h i x)) ^ (2 * m) ≤
      (m : ℝ) * (m : ℝ) ^ (2 * m) * max (∑ x ∈ S, v x) 1 ^ m := by
  classical
  have := hh.nonempty
  simp only [sum_pow']
  rw [expect_sum_comm]
  have hterm : ∀ t ∈ piFinset fun _ : Fin (2 * m) => S,
      𝔼 i, ∏ j, Z (t j) (h i (t j)) ≤
        if #(univ.image t) ≤ m then ∏ x ∈ univ.image t, v x else 0 := by
    intro t ht
    have htS : ∀ x ∈ univ.image t, x ∈ S := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := mem_image.mp hx
      exact mem_piFinset.mp ht j
    have hprod (i : ι) : ∏ j, Z (t j) (h i (t j)) =
        ∏ x ∈ univ.image t, Z x (h i x) ^ #{j | t j = x} :=
      prod_comp (fun x => Z x (h i x)) t
    simp only [hprod]
    rw [hh.expect_prod (card_image_le.trans (by simp)) fun x y => Z x y ^ #{j | t j = x}]
    by_cases hex1 : ∃ x ∈ univ.image t, #{j | t j = x} = 1
    · obtain ⟨x, hx, hc1⟩ := hex1
      rw [prod_eq_zero hx (by simp only [hc1, pow_one]; exact hZ x (htS x hx))]
      split_ifs
      exacts [prod_nonneg fun z hz => hv z (htS z hz), le_rfl]
    push Not at hex1
    -- Every value of `t` is hit at least twice, so `t` takes at most `m` values.
    have hge2 : ∀ x ∈ univ.image t, 2 ≤ #{j | t j = x} := fun x hx => by
      obtain ⟨j, -, rfl⟩ := mem_image.mp hx
      have hpos : 0 < #{j' | t j' = t j} := card_pos.mpr ⟨j, by simp⟩
      have hne1 := hex1 (t j) hx
      omega
    have hcard_le : #(univ.image t) ≤ m := by
      have h2 := sum_le_sum hge2
      rw [← card_eq_sum_card_image, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h2
      omega
    simp only [hcard_le, ↓reduceIte]
    refine (le_abs_self _).trans ?_
    rw [abs_prod]
    gcongr with x hx
    have : Nonempty Y := ⟨h (Classical.arbitrary ι) x⟩
    refine (abs_expect_le _ _).trans ((Finset.expect_le_expect fun y _ => ?_).trans
      (hZ₂ x (htS x hx)))
    obtain ⟨k, hk⟩ : ∃ k, #{j | t j = x} = 2 + k :=
      ⟨#{j | t j = x} - 2, by have := hge2 x hx; omega⟩
    rw [abs_pow, hk, pow_add, sq_abs]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (abs_nonneg _) (hZ₁ x (htS x hx) y))
  let P_all := piFinset fun _ : Fin (2 * m) => S
  have hpart :
      (∑ t ∈ P_all, if #(univ.image t) ≤ m then ∏ x ∈ univ.image t, v x else 0) =
        ∑ r ∈ Icc 1 m,
          ∑ t ∈ P_all.filter (fun t => #(univ.image t) = r), ∏ x ∈ univ.image t, v x := by
    rw [← sum_filter, ← sum_fiberwise_of_maps_to (g := fun t => #(univ.image t)) (t := Icc 1 m)
      fun t ht => mem_Icc.2 ⟨card_pos.2 ((univ_nonempty_iff.2 ⟨⟨0, by omega⟩⟩).image t),
        (mem_filter.1 ht).2⟩]
    refine sum_congr rfl fun r hr => ?_
    rw [filter_filter]
    exact sum_congr (filter_congr fun t _ => ⟨And.right, fun h => ⟨h ▸ (mem_Icc.1 hr).2, h⟩⟩)
      fun _ _ => rfl
  set V := max (∑ x ∈ S, v x) 1
  have hV_ge1 : 1 ≤ V := le_max_right _ _
  have hV_ge_sum : ∑ x ∈ S, v x ≤ V := le_max_left _ _
  have hsum_nonneg : 0 ≤ ∑ x ∈ S, v x := sum_nonneg hv
  calc
    (∑ t ∈ P_all, 𝔼 i, ∏ j, Z (t j) (h i (t j)))
      ≤ ∑ t ∈ P_all, if #(univ.image t) ≤ m then ∏ x ∈ univ.image t, v x else 0 :=
          sum_le_sum hterm
    _ = ∑ r ∈ Icc 1 m,
          ∑ t ∈ P_all.filter (fun t => #(univ.image t) = r), ∏ x ∈ univ.image t, v x := hpart
    _ ≤ ∑ r ∈ Icc 1 m, (r : ℝ) ^ (2 * m) * (∑ x ∈ S, v x) ^ r := by
          refine sum_le_sum fun r hr => ?_
          exact sum_prod_image_eq_card_le S v hv (2 * m) (mem_Icc.mp hr).1
    _ ≤ ∑ _r ∈ Icc 1 m, (m : ℝ) ^ (2 * m) * V ^ m := by
          gcongr with r hr
          · exact_mod_cast (mem_Icc.1 hr).2
          · exact (pow_le_pow_left₀ hsum_nonneg hV_ge_sum r).trans
              (pow_le_pow_right₀ hV_ge1 (mem_Icc.1 hr).2)
    _ = (m : ℝ) * (m : ℝ) ^ (2 * m) * V ^ m := by
          rw [sum_const, Nat.card_Icc, show m + 1 - 1 = m by omega, nsmul_eq_mul, mul_assoc]

/-- **Two-sided variance-aware tail bound for limited independence**:
For `1 ≤ m`, `0 < a`, and `2 * m`-wise independent centered sums bounded in `[-1, 1]` with
per-coordinate variance `≤ v x` (`0 ≤ v x`),
`dens {i | a ≤ |∑ x ∈ S, Z x (h i x)|} ≤ m * (m ^ 2 * max (∑ x ∈ S, v x) 1 / a ^ 2) ^ m`. -/
theorem dens_filter_le_abs_sum_of_sq_le {m : ℕ} (hm : 1 ≤ m)
    (hh : IsKWiseIndependentHash (2 * m) h) (S : Finset X) (Z : X → Y → ℝ) (v : X → ℝ)
    (hv : ∀ x ∈ S, 0 ≤ v x) (hZ : ∀ x ∈ S, 𝔼 y, Z x y = 0)
    (hZ₁ : ∀ x ∈ S, ∀ y, |Z x y| ≤ 1) (hZ₂ : ∀ x ∈ S, 𝔼 y, (Z x y) ^ 2 ≤ v x)
    {a : ℝ} (ha : 0 < a) :
    (dens {i | a ≤ |∑ x ∈ S, Z x (h i x)|} : ℝ) ≤
      (m : ℝ) * ((m : ℝ) ^ 2 * max (∑ x ∈ S, v x) 1 / a ^ 2) ^ m := by
  have hmarkov := Fintype.mul_dens_filter_le_expect
    (f := fun i => (∑ x ∈ S, Z x (h i x)) ^ (2 * m))
    (fun _ => (even_two_mul m).pow_nonneg _) (a ^ (2 * m))
  have hsub : ({i | a ≤ |∑ x ∈ S, Z x (h i x)|} : Finset ι) ⊆
      ({i | a ^ (2 * m) ≤ (∑ x ∈ S, Z x (h i x)) ^ (2 * m)} : Finset ι) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    rw [← (even_two_mul m).pow_abs (∑ x ∈ S, Z x (h i x))]
    exact pow_le_pow_left₀ ha.le hi _
  have hdens : (dens {i | a ≤ |∑ x ∈ S, Z x (h i x)|} : ℝ) ≤
      dens {i | a ^ (2 * m) ≤ (∑ x ∈ S, Z x (h i x)) ^ (2 * m)} := by
    exact_mod_cast dens_le_dens hsub
  have hpow : 0 < a ^ (2 * m) := pow_pos ha _
  calc (dens {i | a ≤ |∑ x ∈ S, Z x (h i x)|} : ℝ)
      ≤ (m : ℝ) * (m : ℝ) ^ (2 * m) * max (∑ x ∈ S, v x) 1 ^ m / a ^ (2 * m) := by
          rw [le_div_iff₀ hpow, mul_comm]
          exact (mul_le_mul_of_nonneg_left hdens hpow.le).trans
            (hmarkov.trans (hh.expect_sum_pow_le_of_sq_le hm S Z v hv hZ hZ₁ hZ₂))
    _ = (m : ℝ) * ((m : ℝ) ^ 2 * max (∑ x ∈ S, v x) 1 / a ^ 2) ^ m := by
          rw [mul_div_assoc, div_pow, mul_pow, ← pow_mul, ← pow_mul]
          ring

/-- **Variance-aware tail bound for `[0, 1]`-valued scores**:
For `g x : Y → [0, 1]`, each centered variable `Z x y = g x y - 𝔼 y', g x y'` automatically
satisfies `|Z x y| ≤ 1` and `𝔼 y, (Z x y) ^ 2 ≤ 𝔼 y, g x y`, yielding concentration in terms of
the mean sum `μ = ∑ x ∈ S, 𝔼 y, g x y` rather than `#S`. -/
theorem dens_filter_le_abs_sum_sub_expect_of_Icc {m : ℕ} (hm : 1 ≤ m)
    (hh : IsKWiseIndependentHash (2 * m) h) (S : Finset X) (g : X → Y → ℝ)
    (hg : ∀ x ∈ S, ∀ y, g x y ∈ Set.Icc 0 1) {a : ℝ} (ha : 0 < a) :
    (dens {i | a ≤ |∑ x ∈ S, (g x (h i x) - 𝔼 y, g x y)|} : ℝ) ≤
      (m : ℝ) * ((m : ℝ) ^ 2 * max (∑ x ∈ S, 𝔼 y, g x y) 1 / a ^ 2) ^ m := by
  refine hh.dens_filter_le_abs_sum_of_sq_le hm S (fun x y => g x y - 𝔼 y', g x y')
    (fun x => 𝔼 y, g x y) (fun x hx => ?_) (fun x _ => Fintype.expect_balance (g x))
    (fun x hx y => ?_) (fun x hx => ?_) ha
  · exact expect_nonneg fun y _ => (hg x hx y).1
  · have : Nonempty Y := ⟨y⟩
    have h0 : 0 ≤ 𝔼 y', g x y' := expect_nonneg fun y' _ => (hg x hx y').1
    have h1 : 𝔼 y', g x y' ≤ 1 := expect_le univ_nonempty fun y' _ => (hg x hx y').2
    rw [abs_le]
    constructor <;> linarith [(hg x hx y).1, (hg x hx y).2]
  · have : Nonempty Y := ⟨h hh.nonempty.some x⟩
    exact (le_abs_self _).trans (abs_expect_sub_expect_pow_le (g x) (hg x hx) le_rfl)

/-! ## Section 2: Multi-salt collision-freedom and batch collision-count tail bounds -/

section PairCollisions

variable {Z : Type*}

private theorem dens_biUnion_eq {α : Type*} [DecidableEq ι] (s : Finset α) (t : α → Finset ι)
    (hd : (s : Set α).PairwiseDisjoint t) :
    (s.biUnion t).dens = ∑ a ∈ s, (t a).dens := by
  simp_rw [dens, card_biUnion hd, Nat.cast_sum, sum_div]

private theorem dens_biUnion_le_sum_real {α : Type*} [DecidableEq ι] (s : Finset α)
    (t : α → Finset ι) :
    ((s.biUnion t).dens : ℝ) ≤ ∑ a ∈ s, ((t a).dens : ℝ) := by
  simp_rw [nnratCast_dens, ← sum_div, ← Nat.cast_sum]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast card_biUnion_le

/-- **Fresh-endpoint pair-collision bound under `2 * r`-wise independence**:
Suppose `a, b : Fin r → Z` satisfy `∀ k, a k ≠ b k` and `∀ j < k, a k ≠ a j ∧ a k ≠ b j` (each
`a k` is distinct from its partner `b k` and all earlier endpoints `a j, b j` for `j < k`). Then
for any `2 * r`-wise independent family `H : ι → Z → Y`,
`dens {i | ∀ k, H i (a k) = H i (b k)} ≤ (|Y|⁻¹) ^ r`. -/
theorem dens_fresh_pair_collisions_le {r : ℕ} {H : ι → Z → Y}
    (hh : IsKWiseIndependentHash (2 * r) H)
    (a b : Fin r → Z)
    (hne : ∀ k, a k ≠ b k)
    (hfresh : ∀ j k : Fin r, j < k → a k ≠ a j ∧ a k ≠ b j) :
    (dens ({i : ι | ∀ k : Fin r, H i (a k) = H i (b k)} : Finset ι) : ℝ) ≤
      ((Fintype.card Y : ℝ)⁻¹) ^ r := by
  classical
  have := hh.nonempty
  rcases isEmpty_or_nonempty Y with hY_emp | hY_ne
  · rcases Nat.eq_zero_or_pos r with rfl | hr_pos
    · simp
    · exfalso
      exact hY_emp.false (H hh.nonempty.some (a ⟨0, hr_pos⟩))
  let U_pts : Finset Z := univ.image a
  let V_pts : Finset Z := univ.image b
  let T : Finset Z := U_pts ∪ V_pts
  have ha_inj : Function.Injective a := fun j k hjk =>
    le_antisymm (not_lt.1 fun h => (hfresh k j h).1 hjk)
      (not_lt.1 fun h => (hfresh j k h).1 hjk.symm)
  have hcard_U : #U_pts = r := by
    rw [card_image_of_injective _ ha_inj, card_univ, Fintype.card_fin]
  have hcard_T : #T ≤ 2 * r := (card_union_le _ _).trans <| by
    rw [hcard_U, two_mul]; exact Nat.add_le_add_left (card_image_le.trans (by simp)) r
  have hU_sub : U_pts ⊆ T := subset_union_left
  let R_rest : Finset Z := T \ U_pts
  have hcard_R : #T = r + #R_rest := by
    rw [← card_sdiff_add_card_eq_card hU_sub, hcard_U, add_comm]
  have hmem_a (k : Fin r) : a k ∈ T := hU_sub (mem_image_of_mem _ (mem_univ k))
  have hmem_b (k : Fin r) : b k ∈ T := subset_union_right (mem_image_of_mem _ (mem_univ k))
  let GoodF : Finset (T → Y) :=
    univ.filter fun f => ∀ k : Fin r, f ⟨a k, hmem_a k⟩ = f ⟨b k, hmem_b k⟩
  let projR : (T → Y) → (R_rest → Y) := fun f z => f ⟨z.1, sdiff_subset z.2⟩
  have hinj_proj : Set.InjOn projR (GoodF : Set (T → Y)) := by
    intro f₁ hf₁ f₂ hf₂ heq
    have hf₁_eq := (mem_filter.mp hf₁).2
    have hf₂_eq := (mem_filter.mp hf₂).2
    -- `f₁` and `f₂` agree at every `a k`, by strong induction on `k`.
    have hk_eq (k : Fin r) : f₁ ⟨a k, hmem_a k⟩ = f₂ ⟨a k, hmem_a k⟩ := by
      induction k using WellFoundedLT.induction with
      | _ k ih =>
        rw [hf₁_eq k, hf₂_eq k]
        by_cases hbU : b k ∈ U_pts
        · obtain ⟨j, -, hj_eq⟩ := mem_image.mp hbU
          have hj_lt : j < k := by
            rcases lt_trichotomy j k with hlt | rfl | hgt
            exacts [hlt, absurd hj_eq (hne j), absurd hj_eq (hfresh k j hgt).2]
          rw [← (Subtype.ext hj_eq : (⟨a j, hmem_a j⟩ : T) = ⟨b k, hmem_b k⟩)]
          exact ih j hj_lt
        · exact congrFun heq ⟨b k, mem_sdiff.mpr ⟨hmem_b k, hbU⟩⟩
    funext z
    by_cases hzU : z.1 ∈ U_pts
    · obtain ⟨k, -, hk_z⟩ := mem_image.mp hzU
      rw [← (Subtype.ext hk_z : (⟨a k, hmem_a k⟩ : T) = z)]
      exact hk_eq k
    · exact congrFun heq ⟨z.1, mem_sdiff.mpr ⟨z.2, hzU⟩⟩
  have hcard_GoodF : #GoodF ≤ Fintype.card Y ^ #R_rest := by
    calc #GoodF = #(GoodF.image projR) := (card_image_of_injOn hinj_proj).symm
      _ ≤ #(univ : Finset (R_rest → Y)) := card_le_card (subset_univ _)
      _ = Fintype.card Y ^ #R_rest := by simp
  have hevent_eq :
      ({i : ι | ∀ k : Fin r, H i (a k) = H i (b k)} : Finset ι) =
        GoodF.biUnion (fun f => {i : ι | T.restrict (H i) = f}) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, GoodF]
    exact ⟨fun hi => ⟨T.restrict (H i), hi, rfl⟩, fun ⟨_, hf, rfl⟩ k => hf k⟩
  have hdisj : (GoodF : Set (T → Y)).PairwiseDisjoint
      (fun f => ({i : ι | T.restrict (H i) = f} : Finset ι)) := by
    intro f₁ _ f₂ _ hne_f
    exact disjoint_left.mpr fun i hi₁ hi₂ =>
      hne_f ((mem_filter.mp hi₁).2.symm.trans (mem_filter.mp hi₂).2)
  have hdens_q :
      dens ({i : ι | ∀ k : Fin r, H i (a k) = H i (b k)} : Finset ι) ≤
        ((Fintype.card Y : ℚ≥0)⁻¹) ^ r := by
    have hpow_R_ne : (Fintype.card Y : ℚ≥0) ^ #R_rest ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    rw [hevent_eq, dens_biUnion_eq _ _ hdisj]
    simp_rw [hh.dens_filter_restrict_eq hcard_T, sum_const, nsmul_eq_mul]
    calc (#GoodF : ℚ≥0) * ((Fintype.card Y : ℚ≥0) ^ #T)⁻¹
        ≤ (Fintype.card Y : ℚ≥0) ^ #R_rest * ((Fintype.card Y : ℚ≥0) ^ #T)⁻¹ := by
          gcongr; exact_mod_cast hcard_GoodF
      _ = ((Fintype.card Y : ℚ≥0)⁻¹) ^ r := by
          rw [hcard_R, pow_add, mul_inv, mul_left_comm, mul_inv_cancel₀ hpow_R_ne, mul_one, inv_pow]
  simpa using (NNRat.cast_le (K := ℝ)).mpr hdens_q

/-- An event covered by the fresh-endpoint pair-collision events indexed by `T` has density at
most `(N / |Y|) ^ r` whenever `#T ≤ N ^ r`. -/
private theorem dens_le_of_subset_biUnion_fresh {α : Type*} [DecidableEq ι] {r : ℕ}
    {H : ι → Z → Y} (hh : IsKWiseIndependentHash (2 * r) H) {E : Finset ι} (T : Finset α)
    (a b : α → Fin r → Z) (hne : ∀ t ∈ T, ∀ k, a t k ≠ b t k)
    (hfresh : ∀ t ∈ T, ∀ j k : Fin r, j < k → a t k ≠ a t j ∧ a t k ≠ b t j)
    (hsub : E ⊆ T.biUnion fun t => {i : ι | ∀ k, H i (a t k) = H i (b t k)})
    {N : ℝ} (hT : (#T : ℝ) ≤ N ^ r) :
    (dens E : ℝ) ≤ (N / Fintype.card Y) ^ r := by
  calc (dens E : ℝ)
      ≤ ((T.biUnion fun t => ({i : ι | ∀ k, H i (a t k) = H i (b t k)} : Finset ι)).dens : ℝ) := by
        exact_mod_cast dens_le_dens hsub
    _ ≤ ∑ _t ∈ T, ((Fintype.card Y : ℝ)⁻¹) ^ r :=
        (dens_biUnion_le_sum_real T _).trans
          (sum_le_sum fun t ht => hh.dens_fresh_pair_collisions_le _ _ (hne t ht) (hfresh t ht))
    _ ≤ N ^ r * ((Fintype.card Y : ℝ)⁻¹) ^ r := by
        rw [sum_const, nsmul_eq_mul]; gcongr
    _ = (N / Fintype.card Y) ^ r := by rw [← mul_pow, div_eq_mul_inv]

/-- **Multi-salt intra-bucket collision-freedom bound**:
Under a `2 * s_max`-wise independent family `H : ι → Fin s_max × Q → Y`, the fraction of seeds `i`
for which *every* salt `s : Fin s_max` has a colliding pair `u ≠ v` inside `S_b : Finset Q` is at
most `(#S_b ^ 2 / |Y|) ^ s_max`. -/
theorem dens_forall_salt_exists_collision_le {s_max : ℕ} {Q : Type*} [DecidableEq Q]
    {H : ι → Fin s_max × Q → Y} (hh : IsKWiseIndependentHash (2 * s_max) H)
    (S_b : Finset Q) :
    (dens ({i : ι | ∀ s : Fin s_max, ∃ u ∈ S_b, ∃ v ∈ S_b, u ≠ v ∧ H i (s, u) = H i (s, v)} :
      Finset ι) : ℝ) ≤ ((#S_b : ℝ) ^ 2 / Fintype.card Y) ^ s_max := by
  classical
  let Pairs := (S_b ×ˢ S_b).filter fun p => p.1 ≠ p.2
  let Tuples := piFinset fun _ : Fin s_max => Pairs
  have hsub :
      ({i : ι | ∀ s : Fin s_max, ∃ u ∈ S_b, ∃ v ∈ S_b, u ≠ v ∧ H i (s, u) = H i (s, v)} :
        Finset ι) ⊆
        Tuples.biUnion (fun t =>
          {i : ι | ∀ s : Fin s_max, H i (s, (t s).1) = H i (s, (t s).2)}) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    choose u hu_mem v hv_mem hne hcoll using hi
    exact mem_biUnion.mpr ⟨fun s => (u s, v s), mem_piFinset.mpr fun s =>
      mem_filter.mpr ⟨mem_product.mpr ⟨hu_mem s, hv_mem s⟩, hne s⟩, by simpa using hcoll⟩
  have hcard_Tuples : (#Tuples : ℝ) ≤ ((#S_b : ℝ) ^ 2) ^ s_max := by
    rw [card_piFinset, prod_const, card_univ, Fintype.card_fin]
    exact_mod_cast Nat.pow_le_pow_left ((card_filter_le _ _).trans (by rw [card_product, sq])) _
  exact dens_le_of_subset_biUnion_fresh hh Tuples (fun t s => (s, (t s).1))
    (fun t s => (s, (t s).2))
    (fun t ht s h => (mem_filter.mp (mem_piFinset.mp ht s)).2 (congrArg Prod.snd h))
    (fun t _ j k hjk => ⟨fun h => hjk.ne' (congrArg Prod.fst h),
      fun h => hjk.ne' (congrArg Prod.fst h)⟩) hsub hcard_Tuples

/-- Greedy extraction of `r` fresh-endpoint pairs from a finite set `B` of cardinality `≥ 2 * r`
equipped with a partner function `vFn : Q → Q` satisfying `∀ u ∈ B, vFn u ≠ u`. -/
private theorem exists_fresh_chain_of_card_ge {Q : Type*}
    (r : ℕ) (B : Finset Q) (vFn : Q → Q) (hB : 2 * r ≤ #B) (hne : ∀ u ∈ B, vFn u ≠ u) :
    ∃ u : Fin r → Q,
      (∀ k, u k ∈ B) ∧
      (∀ j k : Fin r, j < k → u k ≠ u j ∧ u k ≠ vFn (u j)) := by
  classical
  induction r generalizing B with
  | zero =>
    exact ⟨Fin.elim0, fun k => k.elim0, fun j => j.elim0⟩
  | succ r ih =>
    have hB_ne : B.Nonempty := card_pos.mp (by omega)
    let u₀ := hB_ne.choose
    have hu₀ : u₀ ∈ B := hB_ne.choose_spec
    let B' := (B.erase u₀).erase (vFn u₀)
    have hcard_B' : 2 * r ≤ #B' := by
      have h1 : #(B.erase u₀) = #B - 1 := card_erase_of_mem hu₀
      have h2 : #(B.erase u₀) - 1 ≤ #B' := pred_card_le_card_erase
      omega
    have hne' : ∀ u ∈ B', vFn u ≠ u := fun u hu =>
      hne u (mem_of_mem_erase (mem_of_mem_erase hu))
    obtain ⟨u_tail, hmem_tail, hfresh_tail⟩ := ih B' hcard_B' hne'
    refine ⟨Fin.cons u₀ u_tail, ?_, ?_⟩
    · intro k
      refine Fin.cases hu₀ (fun k' => ?_) k
      exact mem_of_mem_erase (mem_of_mem_erase (hmem_tail k'))
    · intro j k hjk
      cases k using Fin.cases with
      | zero => exact absurd hjk (Nat.not_lt_zero _)
      | succ k' =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_succ, Fin.cons_zero]
          have hm := hmem_tail k'
          dsimp only [B'] at hm
          have hnot_v : u_tail k' ≠ vFn u₀ := ne_of_mem_erase hm
          have hnot_u : u_tail k' ≠ u₀ := ne_of_mem_erase (mem_of_mem_erase hm)
          exact ⟨hnot_u, hnot_v⟩
        | succ j' =>
          simp only [Fin.cons_succ]
          exact hfresh_tail j' k' (Fin.succ_lt_succ_iff.mp hjk)

/-- **Per-key neighborhood salt-collision count tail bound**:
Under a `2 * r`-wise independent family `H : ι → Fin s_max × Q → Y`, given a batch
`Q_set : Finset Q` and per-key candidate collision sets `W_of : Q → Finset Q` with
`∀ u ∈ Q_set, #(W_of u) ≤ w_cap`, the fraction of seeds `i` for which at least `2 * r` keys
`u ∈ Q_set` collide with some `v ∈ W_of u \ {u}` under some salt `s : Fin s_max` is at most
`(((#Q_set * w_cap * s_max) / |Y|) ^ r)`. -/
theorem dens_card_local_salt_colliding_ge_le {r s_max w_cap : ℕ} {Q : Type*} [DecidableEq Q]
    {H : ι → Fin s_max × Q → Y} (hh : IsKWiseIndependentHash (2 * r) H)
    (Q_set : Finset Q) (W_of : Q → Finset Q)
    (hw_cap : ∀ u ∈ Q_set, #(W_of u) ≤ w_cap) :
    (dens ({i : ι | 2 * r ≤
      #(Q_set.filter fun u =>
        ∃ v ∈ W_of u, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι) : ℝ) ≤
      (((#Q_set * w_cap * s_max : ℕ) : ℝ) / Fintype.card Y) ^ r := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr_pos
  · simp only [pow_zero]
    exact_mod_cast dens_le_one
  let Pairs := Q_set.biUnion fun u => ({u} : Finset Q) ×ˢ ((W_of u).erase u)
  let Triples := Pairs ×ˢ (univ : Finset (Fin s_max))
  let Chains := (piFinset fun _ : Fin r => Triples).filter fun t =>
    ∀ j k : Fin r, j < k → (t k).1.1 ≠ (t j).1.1 ∧ (t k).1.1 ≠ (t j).1.2
  have hsub :
      ({i : ι | 2 * r ≤
        #(Q_set.filter fun u =>
          ∃ v ∈ W_of u, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι) ⊆
        Chains.biUnion (fun t =>
          {i : ι | ∀ k : Fin r, H i ((t k).2, (t k).1.1) = H i ((t k).2, (t k).1.2)}) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    set B := Q_set.filter fun u =>
      ∃ v ∈ W_of u, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v)
    have hB_ne : B.Nonempty := card_pos.mp (by omega)
    have hex_wit : ∀ u ∈ B, ∃ vs : Q × Fin s_max,
        vs.1 ∈ W_of u ∧ u ≠ vs.1 ∧ H i (vs.2, u) = H i (vs.2, vs.1) := fun u hu => by
      obtain ⟨_, v, hvW, hne_uv, s, hcoll⟩ := mem_filter.mp hu
      exact ⟨(v, s), hvW, hne_uv, hcoll⟩
    obtain ⟨vs₀, -⟩ := hex_wit _ hB_ne.choose_spec
    have := Nonempty.intro vs₀
    choose! vs hvs using hex_wit
    obtain ⟨u_ch, hu_mem, hfresh⟩ := exists_fresh_chain_of_card_ge r B (fun u => (vs u).1) hi
      (fun u hu => (hvs u hu).2.1.symm)
    refine mem_biUnion.mpr ⟨fun k => ((u_ch k, (vs (u_ch k)).1), (vs (u_ch k)).2), ?_, ?_⟩
    · refine mem_filter.mpr ⟨mem_piFinset.mpr fun k => ?_, fun j k hjk => hfresh j k hjk⟩
      have hkB := hu_mem k
      have hkQ := (mem_filter.mp hkB).1
      obtain ⟨hvW, hne_uv, _⟩ := hvs (u_ch k) hkB
      refine mem_product.mpr ⟨mem_biUnion.mpr ⟨u_ch k, hkQ, ?_⟩, mem_univ _⟩
      exact mem_product.mpr ⟨mem_singleton_self _, mem_erase.mpr ⟨hne_uv.symm, hvW⟩⟩
    · simp only [mem_filter, mem_univ, true_and]
      intro k
      exact (hvs (u_ch k) (hu_mem k)).2.2
  have hcard_Chains : #Chains ≤ (#Q_set * w_cap * s_max) ^ r := by
    refine (card_filter_le _ _).trans ?_
    rw [card_piFinset, prod_const, card_univ, Fintype.card_fin]
    refine Nat.pow_le_pow_left ?_ r
    rw [card_product, card_univ, Fintype.card_fin]
    refine Nat.mul_le_mul_right _ (card_biUnion_le.trans
      ((sum_le_card_nsmul _ _ _ fun u hu => ?_).trans_eq (smul_eq_mul _ _)))
    rw [card_product, card_singleton, one_mul]
    exact card_erase_le.trans (hw_cap u hu)
  refine dens_le_of_subset_biUnion_fresh hh Chains (fun t k => ((t k).2, (t k).1.1))
    (fun t k => ((t k).2, (t k).1.2)) (fun t ht k h => ?_) (fun t ht j k hjk => ?_) hsub
    (by exact_mod_cast hcard_Chains)
  · obtain ⟨u, _, hp⟩ :=
      mem_biUnion.mp (mem_product.mp (mem_piFinset.mp (mem_filter.mp ht).1 k)).1
    obtain ⟨hu_eq, hv_er⟩ := mem_product.mp hp
    rw [mem_singleton.mp hu_eq] at h
    exact (mem_erase.mp hv_er).1 (congrArg Prod.snd h).symm
  · have h := (mem_filter.mp ht).2 j k hjk
    exact ⟨fun h' => h.1 (congrArg Prod.snd h'), fun h' => h.2 (congrArg Prod.snd h')⟩

/-- **Batch salt-collision count tail bound**:
Under a `2 * r`-wise independent family `H : ι → Fin s_max × Q → Y`, given a batch
`Q_set : Finset Q` and a window `W_set : Finset Q`, the fraction of seeds `i` for which at least
`2 * r` keys `u ∈ Q_set` collide with some `v ∈ W_set \ {u}` under some salt `s : Fin s_max` is at
most `((#Q_set * #W_set * s_max) / |Y|) ^ r`. -/
theorem dens_card_salt_colliding_ge_le {r s_max : ℕ} {Q : Type*} [DecidableEq Q]
    {H : ι → Fin s_max × Q → Y} (hh : IsKWiseIndependentHash (2 * r) H)
    (Q_set W_set : Finset Q) :
    (dens ({i : ι | 2 * r ≤
      #(Q_set.filter fun u =>
        ∃ v ∈ W_set, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι) : ℝ) ≤
      (((#Q_set * #W_set * s_max : ℕ) : ℝ) / Fintype.card Y) ^ r :=
  dens_card_local_salt_colliding_ge_le hh Q_set (fun _ => W_set) (fun _ _ => le_rfl)

end PairCollisions

end IsKWiseIndependentHash

end Cslib.Probability

end


