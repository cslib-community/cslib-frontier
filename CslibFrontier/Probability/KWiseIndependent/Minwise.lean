/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.KWiseIndependent
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.KWiseIndependent.Restriction
import CslibFrontier.Probability.KWiseIndependent.VarianceTail
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Minimum ranks under five-wise independence

A distinguished key is a weak minimum among itself and `L` distinct competitors with
probability at most `256 / L` under five-wise independent uniform ranks, when the rank
alphabet has at least `L` values. Conditional on the distinguished rank, the indicators
of smaller competitors are four-wise independent. Their fourth moment controls the
probability of seeing no smaller rank. Summing this bound over the distinguished rank
gives the inverse-linear dependence even when ranks can tie.

This adapts the continuous-rank upper bound of [Knudsen and Stöckel, Theorem 2,
Section 5.1][KnudsenStockel2015] to a discrete uniform rank alphabet. Their theorem
uses strict minima and uniform ranks on the unit interval. Here the rank alphabet
is finite, and every tie at the minimum counts. The discrete sum is bounded by
telescoping consecutive reciprocals.
-/

public section

namespace Cslib.Probability.IsKWiseIndependentHash

open Finset Fintype
open scoped BigOperators

private theorem expect_eq_expect_fiber {Seed X Y : Type*} [Fintype Seed] [Fintype Y]
    [DecidableEq Y] [Nonempty Y] {h : Seed → X → Y} {k : ℕ}
    (hh : IsKWiseIndependentHash (k + 1) h) (x : X) (f : Seed → ℝ) :
    (𝔼 s, f s) = 𝔼 a : Y, 𝔼 s : {s // h s x = a}, f s.val := by
  classical
  have := hh.nonempty
  simp only [Fintype.expect_eq_sum_div_card]
  rw [← (Equiv.sigmaFiberEquiv (fun s => h s x)).sum_comp f, Fintype.sum_sigma,
    Finset.sum_div]
  conv_rhs => rw [Finset.sum_div]
  refine sum_congr rfl fun a _ => ?_
  simp only [Equiv.sigmaFiberEquiv_apply, div_div]
  rw [mul_comm, ← Nat.cast_mul, hh.card_fiber_eq x a]

private theorem dens_no_smaller {Seed I : Type*} [Fintype Seed] [Fintype I] {q : ℕ}
    {h : Seed → I → Fin q} (hh : IsKWiseIndependentHash 4 h) (a : Fin q)
    (hμ : 1 ≤ (Fintype.card I : ℝ) * ((a.val : ℝ) / q)) :
    (dens {s | ∀ i, a ≤ h s i} : ℝ) ≤ 32 / ((Fintype.card I : ℝ) * ((a.val : ℝ) / q)) ^ 2 := by
  classical
  let g (y : Fin q) : ℝ := if y < a then 1 else 0
  let μ : ℝ := Fintype.card I * ((a.val : ℝ) / q)
  have hpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
  have hmean : (𝔼 y, g y) = (a.val : ℝ) / q := by
    change (𝔼 y : Fin q, if y < a then (1 : ℝ) else 0) = _
    rw [Fintype.expect_boole, nnratCast_dens, Fintype.card_fin, filter_gt_eq_Iio, Fin.card_Iio]
  have htail := hh.dens_filter_le_abs_sum_sub_expect_of_Icc (m := 2) (by decide)
    univ (fun _ y => g y) (fun _ _ y => by dsimp [g]; split <;> norm_num) hpos
  have hsub : ({s | ∀ i, a ≤ h s i} : Finset Seed) ⊆
      ({s | μ ≤ |∑ i, (g (h s i) - 𝔼 y, g y)|} : Finset Seed) := by
    intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs ⊢
    have hz (i : I) : g (h s i) = 0 := by simp [g, not_lt.mpr (hs i)]
    simp only [hz, hmean, zero_sub, sum_const, card_univ, nsmul_eq_mul, mul_neg, abs_neg]
    exact le_of_eq (abs_of_pos hpos).symm
  calc
    (dens {s | ∀ i, a ≤ h s i} : ℝ) ≤
        dens {s | μ ≤ |∑ i, (g (h s i) - 𝔼 y, g y)|} := by exact_mod_cast dens_le_dens hsub
    _ ≤ 2 * (4 * μ / μ ^ 2) ^ 2 := by
      simpa only [hmean, sum_const, card_univ, nsmul_eq_mul, ← show
        (Fintype.card I : ℝ) * ((a.val : ℝ) / q) = μ from rfl,
        max_eq_left hμ, Nat.cast_ofNat, Nat.reducePow, show (2 : ℝ) ^ 2 = 4 by norm_num] using htail
    _ = 32 / μ ^ 2 := by field_simp; ring

/-- A reciprocal bound on each rank fiber whose sum telescopes. -/
private theorem le_minimum_potential {p δ u : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hu : 0 ≤ u) (hp₀ : 0 ≤ p) (hp : p ≤ 1) (htail : 1 ≤ u → p ≤ 32 / u ^ 2) :
    p ≤ 256 / δ * ((1 + u)⁻¹ - (1 + u + δ)⁻¹) := by
  have h₁ : 0 < 1 + u := by linarith
  have h₂ : 0 < 1 + u + δ := by linarith
  have he : 256 / δ * ((1 + u)⁻¹ - (1 + u + δ)⁻¹) =
      256 / ((1 + u) * (1 + u + δ)) := by field_simp; ring
  rw [he, le_div_iff₀ (mul_pos h₁ h₂)]
  by_cases hu₁ : 1 ≤ u
  · have hu' : 0 < u := by linarith
    have h := (le_div_iff₀ (sq_pos_of_pos hu')).mp (htail hu₁)
    have hfactor : (1 + u) * (1 + u + δ) ≤ (2 * u) * (3 * u) := by gcongr <;> linarith
    nlinarith [mul_le_mul_of_nonneg_left hfactor hp₀]
  · calc
      p * ((1 + u) * (1 + u + δ)) ≤ 1 * ((1 + u) * (1 + u + δ)) :=
        mul_le_mul_of_nonneg_right hp (mul_pos h₁ h₂).le
      _ ≤ 1 * (2 * 3) := by gcongr <;> linarith
      _ ≤ 256 := by norm_num

/-- Under five-wise independent uniform ranks, a key has rank at most all `#S` competitors'
ranks with probability at most `256 / #S`. Ties count toward the event. -/
theorem dens_le_all {Seed X : Type*} [Fintype Seed] {q : ℕ} {h : Seed → X → Fin q}
    (hh : IsKWiseIndependentHash 5 h) (S : Finset X) {x : X} (hx : x ∉ S)
    (hS : 0 < #S) (hSq : #S ≤ q) :
    (dens {s | ∀ y ∈ S, h s x ≤ h s y} : ℝ) ≤ 256 / #S := by
  classical
  let : NeZero q := ⟨(hS.trans_le hSq).ne'⟩
  let δ : ℝ := #S / (q : ℝ)
  have hδ : 0 < δ := div_pos (by exact_mod_cast hS) (by exact_mod_cast hS.trans_le hSq)
  have hδ₁ : δ ≤ 1 := (div_le_one (by exact_mod_cast hS.trans_le hSq)).mpr (by exact_mod_cast hSq)
  let φ (k : ℕ) : ℝ := (1 + δ * k)⁻¹
  have hfib (a : Fin q) :
      (dens {s : {s // h s x = a} | ∀ y ∈ S, h s.val x ≤ h s.val y} : ℝ) ≤
        256 / δ * (φ a.val - φ (a.val + 1)) := by
    obtain ⟨_, hf⟩ := hh.fiber x a
    let e (y : S) : {z : X // z ≠ x} := ⟨y, fun he => hx (he ▸ y.property)⟩
    have he : Function.Injective e := fun _ _ eq =>
      Subtype.ext (congrArg (fun z : {z : X // z ≠ x} => z.val) eq)
    let B : Finset {s // h s x = a} := {s : {s // h s x = a} | ∀ y : S, a ≤ h s.val y}
    have hB : ({s : {s // h s x = a} | ∀ y ∈ S, h s.val x ≤ h s.val y} : Finset _) = B := by
      ext s; simp [B, s.property]
    rw [hB]
    have hm : (Fintype.card S : ℝ) * ((a.val : ℝ) / q) = δ * a.val := by
      simp [δ]; ring
    have htail (hμ : 1 ≤ δ * a.val) : (B.dens : ℝ) ≤ 32 / (δ * a.val) ^ 2 := by
      rw [← hm] at hμ ⊢
      exact dens_no_smaller (hf.comp he) a hμ
    simpa [φ, mul_add, add_assoc] using
      le_minimum_potential hδ hδ₁ (mul_nonneg hδ.le (Nat.cast_nonneg a.val))
        (p := (B.dens : ℝ)) (by positivity) (by exact_mod_cast (dens_le_one (s := B))) htail
  rw [← Fintype.expect_boole, expect_eq_expect_fiber (k := 4) hh x]
  simp only [Fintype.expect_boole]
  calc
    _ ≤ 𝔼 a : Fin q, 256 / δ * (φ a.val - φ (a.val + 1)) := expect_le_expect fun a _ => hfib a
    _ = (256 / δ) * (φ 0 - φ q) / q := by
      rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, ← mul_sum,
        Fin.sum_univ_eq_sum_range (fun k => φ k - φ (k + 1)), sum_range_sub']
    _ ≤ (256 / δ) * 1 / q := by
      have hφ : 0 ≤ φ q := inv_nonneg.mpr (by positivity)
      have h0 : φ 0 = 1 := by simp [φ]
      gcongr
      linarith
    _ = 256 / #S := by dsimp [δ]; field_simp [NeZero.ne q]

open scoped Classical in
/-- One seed makes an endpoint a weak minimum on at most `512 * card A / L` of the
injective windows in a family. The windows may overlap arbitrarily. -/
theorem exists_card_endpoint_min_le {Seed A X : Type*} [Fintype Seed] [Fintype A]
    {q L : ℕ} {h : Seed → X → Fin q} (hh : IsKWiseIndependentHash 5 h)
    (w : A → Fin (L + 1) → X) (hL : 0 < L) (hLq : L ≤ q) :
    ∃ s : Seed, #{a | Function.Injective (w a) ∧
        ((∀ j, h s (w a 0) ≤ h s (w a j)) ∨
         (∀ j, h s (w a (Fin.last L)) ≤ h s (w a j)))} * L ≤ 512 * Fintype.card A := by
  classical
  have := hh.nonempty
  let M (s : Seed) (a : A) (i : Fin (L + 1)) := ∀ j, h s (w a i) ≤ h s (w a j)
  let C (s : Seed) (a : A) := Function.Injective (w a) ∧ (M s a 0 ∨ M s a (Fin.last L))
  have hcap (a : A) : (dens {s | C s a} : ℝ) ≤ 512 / L := by
    by_cases hw : Function.Injective (w a)
    · have hmin (i : Fin (L + 1)) : (dens {s | M s a i} : ℝ) ≤ 256 / L := by
        let S := (univ : Finset (Fin (L + 1))).erase i
        have hc : #S = L := by simp [S, card_erase_of_mem]
        have hd := (hh.comp hw).dens_le_all S (x := i) (by simp [S])
          (by simpa only [hc] using hL) (by simpa only [hc] using hLq)
        rw [hc] at hd
        refine (NNRat.cast_le.mpr (dens_le_dens fun s hs => ?_)).trans hd
        simp only [mem_filter, mem_univ, true_and] at hs ⊢
        exact fun j _ => hs j
      have he : ({s | C s a} : Finset Seed) =
          ({s | M s a 0} : Finset Seed) ∪ ({s | M s a (Fin.last L)} : Finset Seed) := by
        ext s; simp [C, hw]
      rw [he]
      calc
        _ ≤ (dens {s | M s a 0} : ℝ) + dens {s | M s a (Fin.last L)} := by
          exact_mod_cast dens_union_le _ _
        _ ≤ 256 / (L : ℝ) + 256 / L := add_le_add (hmin 0) (hmin (Fin.last L))
        _ = _ := by ring
    · simpa [C, hw] using (show (0 : ℝ) ≤ 512 / L by positivity)
  have havg : (𝔼 s : Seed, (#{a | C s a} : ℝ)) ≤ 512 * Fintype.card A / L := by
    simp_rw [← Finset.sum_boole]
    rw [expect_sum_comm]
    simp only [Fintype.expect_boole]
    calc
      _ ≤ ∑ _a : A, (512 : ℝ) / L := sum_le_sum fun a _ => hcap a
      _ = _ := by simp; ring
  obtain ⟨s, _, hs⟩ := exists_le_of_expect_le univ_nonempty havg
  exact ⟨s, by exact_mod_cast (le_div_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)).mp hs⟩

end Cslib.Probability.IsKWiseIndependentHash
