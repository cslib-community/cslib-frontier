/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.VisitCount
public import Mathlib.Analysis.Complex.Exponential
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# The expander Chernoff bound

A walk of length `t` on a graph with spectral expansion `λ = λ(G)`, started at a uniformly random
vertex, visits a set `B` of density `β` about `β (t + 1)` times: the fraction of its `t + 1`
vertices in `B` deviates from `β` by more than `δ` with probability at most
`2 exp (-(1 - λ) δ² (t + 1) / 36)`
(`Cslib.RotationMap.dens_filter_abs_visitCount_div_sub_dens_gt_le`). This is
[Arora and Barak, Theorem 7.41][AroraBarak07] with the sign of the exponent corrected and a
better constant; the draft's form is `Cslib.RotationMap.dens_filter_abs_visitCount_div_sub_gt_lt`.

The proof is the linear-algebra argument for walk Chernoff bounds. For a function `g` with mean
zero and `|g| ≤ 1`, the moment-generating function `𝔼 exp (r ∑ᵢ g (Xᵢ))` is the average of the
weighted walk with the constant weight `P = exp (r g)` (`Cslib.RotationMap.expect_weightedWalk`).
One step `x ↦ P * G.walk x` changes the mean `a` and the mean-zero part `y` of `x` by a
nonnegative `2 × 2` matrix: with `‖·‖` the root mean square and `|P - 1| ≤ ε`,
`|a'| ≤ 𝔼 P |a| + ε λ ‖y‖` and `‖y'‖ ≤ ε |a| + (1 + ε) λ ‖y‖`. The potential
`|a| + θ ‖y‖` with `θ = 4 r / (1 - λ)` then grows by at most `1 + 9 r² / (1 - λ)` per step when
`4 r ≤ 1 - λ` (`Cslib.RotationMap.expect_exp_mul_sum_walkAt_le`). Markov's inequality on each tail
and a union bound give the two-sided bound
(`Cslib.RotationMap.dens_filter_le_abs_sum_walkAt_le`).

## Main results

* `Cslib.RotationMap.expect_exp_mul_sum_walkAt_le`: the moment-generating function bound.
* `Cslib.RotationMap.dens_filter_le_abs_sum_walkAt_le`: the expander Chernoff bound for a bounded
  function with mean zero.
* `Cslib.RotationMap.dens_filter_abs_visitCount_div_sub_dens_gt_le`: the expander Chernoff bound
  for the visits to a set, with constant `36`.
* `Cslib.RotationMap.dens_filter_abs_visitCount_div_sub_gt_lt`: Arora–Barak Theorem 7.41 with the
  corrected exponent and the draft's constant `60`.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft
  2007-01-08][AroraBarak07]
-/

public section

namespace Cslib.RotationMap

open Finset Real
open scoped BigOperators

variable {V D : Type*} [Fintype V] [Fintype D] (G : RotationMap V D)

/-- The variance is at most the second moment about any constant. -/
private theorem expect_sub_expect_sq_le (f : V → ℝ) (c : ℝ) :
    𝔼 v, (f v - 𝔼 u, f u) ^ 2 ≤ 𝔼 v, (f v - c) ^ 2 := by
  set α := 𝔼 u, f u
  have hb : 𝔼 v, (f v - α) = 0 := Fintype.expect_balance f
  have : ∀ v, (f v - c) ^ 2 = (f v - α) ^ 2 + 2 * (α - c) * (f v - α) + (α - c) ^ 2 :=
    fun _ => by ring
  simp only [this, expect_add_distrib, ← mul_expect, hb]
  rcases isEmpty_or_nonempty V with hV | hV
  · simp [univ_eq_empty]
  · rw [Fintype.expect_const]; linarith only [sq_nonneg (α - c)]

/-- A function bounded by `ε` has root mean square at most `ε`. -/
private theorem sqrt_expect_sq_le {f : V → ℝ} {ε : ℝ} (hε : 0 ≤ ε) (hf : ∀ v, |f v| ≤ ε) :
    √(𝔼 v, f v ^ 2) ≤ ε := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp [univ_eq_empty, hε]
  rw [← Real.sqrt_sq hε]
  refine Real.sqrt_le_sqrt (expect_le univ_nonempty fun v _ => ?_)
  exact sq_le_sq' (abs_le.1 (hf v)).1 (abs_le.1 (hf v)).2

/-- The root-mean-square deviation of `P * G.walk x` from its mean, and the mean itself, are
bounded by those of `x` through a `2 × 2` matrix, when `|P - 1| ≤ ε`. -/
private theorem mean_rms_mul_walk_le [Nonempty D] {P : V → ℝ} {ε : ℝ} (hP₀ : ∀ v, 0 ≤ P v)
    (hP : ∀ v, |P v - 1| ≤ ε) (x : V → ℝ) :
    |𝔼 v, P v * G.walk x v| ≤ (𝔼 v, P v) * |𝔼 v, x v| +
        ε * G.spectralExpansion * √(𝔼 v, (x v - 𝔼 u, x u) ^ 2) ∧
      √(𝔼 v, (P v * G.walk x v - 𝔼 u, P u * G.walk x u) ^ 2) ≤
        ε * |𝔼 v, x v| + (1 + ε) * G.spectralExpansion * √(𝔼 v, (x v - 𝔼 u, x u) ^ 2) := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp [univ_eq_empty]
  set ℓ := G.spectralExpansion
  set a := 𝔼 u, x u
  set Y := √(𝔼 v, (x v - a) ^ 2)
  set w : V → ℝ := G.walk fun v => x v - a
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hP (Classical.arbitrary V))
  have hℓ := G.spectralExpansion_nonneg
  have hy₀ : 𝔼 v, (x v - a) = 0 := Fintype.expect_balance x
  have hw₀ : 𝔼 v, w v = 0 := G.expect_walk_eq_zero hy₀
  have hw : √(𝔼 v, w v ^ 2) ≤ ℓ * Y := by
    calc √(𝔼 v, w v ^ 2) ≤ √(ℓ ^ 2 * 𝔼 v, (x v - a) ^ 2) :=
          Real.sqrt_le_sqrt (expect_walk_sq_le_spectralExpansion_sq_mul hy₀)
      _ = ℓ * Y := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hℓ]
  have hwx (v : V) : G.walk x v = a + w v := by
    have : x = (fun _ => a) + fun v => x v - a := funext fun _ => by simp
    rw [this, map_add, G.walk_const]
    simp [w]
  have hP1 : √(𝔼 v, (P v - 1) ^ 2) ≤ ε := sqrt_expect_sq_le hε hP
  constructor
  · have hsplit : 𝔼 v, P v * G.walk x v = (𝔼 v, P v) * a + 𝔼 v, (P v - 1) * w v := by
      simp only [hwx, mul_add, sub_mul, one_mul, expect_add_distrib, expect_sub_distrib, hw₀,
        ← expect_mul]
      ring
    rw [hsplit]
    have hm : 0 ≤ 𝔼 v, P v := expect_nonneg fun v _ => hP₀ v
    have hcs : |𝔼 v, (P v - 1) * w v| ≤ ε * (ℓ * Y) := by
      have := Real.expect_mul_le_sqrt_mul_sqrt univ (fun v => |P v - 1|) fun v => |w v|
      simp only [sq_abs, ← abs_mul] at this
      exact (abs_expect_le _ _).trans (this.trans (mul_le_mul hP1 hw (Real.sqrt_nonneg _) hε))
    calc |(𝔼 v, P v) * a + 𝔼 v, (P v - 1) * w v|
        ≤ |(𝔼 v, P v) * a| + |𝔼 v, (P v - 1) * w v| := abs_add_le _ _
      _ ≤ (𝔼 v, P v) * |a| + ε * ℓ * Y := by
        rw [abs_mul, abs_of_nonneg hm, mul_assoc]; gcongr
  · have hsq : 𝔼 v, (P v * G.walk x v - a) ^ 2 ≤
        (1 * (ε * |a|) + 1 * ((1 + ε) * (ℓ * Y))) ^ 2 * 1 := by
      have heq (v : V) : P v * G.walk x v - a = 1 * (a * (P v - 1)) + 1 * (P v * w v) := by
        rw [hwx]; ring
      simp only [heq]
      refine Fintype.expect_add_sq_le zero_le_one zero_le_one (by positivity) (by positivity)
        zero_le_one ?_ ?_
      · calc 𝔼 v, (a * (P v - 1)) ^ 2 = a ^ 2 * 𝔼 v, (P v - 1) ^ 2 := by
              simp only [mul_pow, mul_expect]
          _ ≤ |a| ^ 2 * ε ^ 2 := by
              rw [sq_abs]; gcongr
              rw [← Real.sqrt_le_sqrt_iff (by positivity), Real.sqrt_sq hε]; exact hP1
          _ = (ε * |a|) ^ 2 * 1 := by ring
      · calc 𝔼 v, (P v * w v) ^ 2 ≤ 𝔼 v, (1 + ε) ^ 2 * w v ^ 2 := by
              refine expect_le_expect fun v _ => ?_
              rw [mul_pow]
              gcongr
              all_goals first | exact hP₀ v | linarith only [(abs_le.1 (hP v)).2]
          _ = (1 + ε) ^ 2 * 𝔼 v, w v ^ 2 := by rw [mul_expect]
          _ ≤ (1 + ε) ^ 2 * (ℓ * Y) ^ 2 := by
              gcongr
              rw [← Real.sqrt_le_sqrt_iff (by positivity), Real.sqrt_sq (by positivity)]; exact hw
          _ = ((1 + ε) * (ℓ * Y)) ^ 2 * 1 := by ring
    calc √(𝔼 v, (P v * G.walk x v - 𝔼 u, P u * G.walk x u) ^ 2)
        ≤ √((1 * (ε * |a|) + 1 * ((1 + ε) * (ℓ * Y))) ^ 2 * 1) :=
          Real.sqrt_le_sqrt ((expect_sub_expect_sq_le _ a).trans hsq)
      _ = ε * |a| + (1 + ε) * ℓ * Y := by
        rw [mul_one, Real.sqrt_sq (by positivity)]; ring

/-- Iterating the one-step bound with the potential `|a| + θ ‖y‖`: if the potential of one step
grows by at most `ρ`, the weighted walk with constant weight `P` has average at most
`ρ ^ (t + 1)`. -/
private theorem abs_expect_weightedWalk_const_le [Nonempty D] {P : V → ℝ} {ε θ ρ : ℝ}
    (hP₀ : ∀ v, 0 ≤ P v) (hP : ∀ v, |P v - 1| ≤ ε) (hε : 0 ≤ ε) (hθ : 0 ≤ θ)
    (h₁ : 𝔼 v, P v + θ * ε ≤ ρ)
    (h₂ : ε * G.spectralExpansion + θ * ((1 + ε) * G.spectralExpansion) ≤ ρ * θ) (t : ℕ) :
    |𝔼 v, G.weightedWalk t (fun _ => P) v| +
        θ * √(𝔼 v, (G.weightedWalk t (fun _ => P) v - 𝔼 u, G.weightedWalk t (fun _ => P) u) ^ 2)
      ≤ ρ ^ (t + 1) := by
  have hm : 0 ≤ 𝔼 v, P v := expect_nonneg fun v _ => hP₀ v
  have hρ : 0 ≤ ρ := (add_nonneg hm (mul_nonneg hθ hε)).trans h₁
  induction t with
  | zero =>
    simp only [weightedWalk_zero, zero_add, pow_one]
    refine le_trans ?_ h₁
    rw [abs_of_nonneg hm]
    gcongr
    exact (Real.sqrt_le_sqrt (expect_sub_expect_sq_le P 1)).trans (sqrt_expect_sq_le hε hP)
  | succ t ih =>
    set x := G.weightedWalk t (fun _ => P)
    have hx : G.weightedWalk (t + 1) (fun _ => P) = fun v => P v * G.walk x v := rfl
    obtain ⟨h₃, h₄⟩ := G.mean_rms_mul_walk_le hP₀ hP x
    rw [hx]
    set ℓ := G.spectralExpansion
    have hℓ := G.spectralExpansion_nonneg
    set a := |𝔼 v, x v|
    set Y := √(𝔼 v, (x v - 𝔼 u, x u) ^ 2)
    have ha : 0 ≤ a := abs_nonneg _
    have hY : 0 ≤ Y := Real.sqrt_nonneg _
    calc _ ≤ ((𝔼 v, P v) * a + ε * ℓ * Y) + θ * (ε * a + (1 + ε) * ℓ * Y) := by gcongr
      _ = (𝔼 v, P v + θ * ε) * a + (ε * ℓ + θ * ((1 + ε) * ℓ)) * Y := by ring
      _ ≤ ρ * a + (ρ * θ) * Y := by gcongr
      _ = ρ * (a + θ * Y) := by ring
      _ ≤ ρ * ρ ^ (t + 1) := by gcongr
      _ = ρ ^ (t + 1 + 1) := by ring

/-- **The moment-generating function of an expander walk.** For `g` with mean zero and
`|g| ≤ 1`, and `0 ≤ r` with `4 r ≤ 1 - λ(G)`, a uniformly started walk of length `t` has
`𝔼 exp (r ∑_{i ≤ t} g (Xᵢ)) ≤ exp (9 r² (t + 1) / (1 - λ(G)))`. -/
theorem expect_exp_mul_sum_walkAt_le [Nonempty D] {g : V → ℝ} (hg : 𝔼 v, g v = 0)
    (hg₁ : ∀ v, |g v| ≤ 1) {r : ℝ} (hr : 0 ≤ r) (hrl : 4 * r ≤ 1 - G.spectralExpansion) (t : ℕ) :
    𝔼 p : V × (Fin t → D), exp (r * ∑ i ∈ range (t + 1), g (G.walkAt p i)) ≤
      exp (9 * r ^ 2 * (t + 1) / (1 - G.spectralExpansion)) := by
  set ℓ := G.spectralExpansion
  set s := 1 - ℓ
  have hℓ := G.spectralExpansion_nonneg
  have hℓ₁ := G.spectralExpansion_le_one
  set P : V → ℝ := fun v => exp (r * g v)
  have hmgf : 𝔼 p : V × (Fin t → D), exp (r * ∑ i ∈ range (t + 1), g (G.walkAt p i)) =
      𝔼 v, G.weightedWalk t (fun _ => P) v := by
    rw [expect_weightedWalk]
    exact expect_congr rfl fun p _ => by rw [mul_sum, Real.exp_sum]
  rw [hmgf]
  rcases eq_or_lt_of_le (b := s) (sub_nonneg.2 hℓ₁) with hs | hs
  · -- `λ(G) = 1` forces `r = 0`, and every weight is `1`.
    have hr0 : r = 0 := by linarith only [hr, hrl, hs]
    have hP : P = fun _ => 1 := funext fun v => by simp [P, hr0]
    have h1 := G.abs_expect_weightedWalk_const_le (P := P) (ε := 0) (θ := 0) (ρ := 1)
      (fun v => (exp_pos _).le) (fun v => by simp [hP]) le_rfl le_rfl
      (by rcases isEmpty_or_nonempty V with hV | hV <;> simp [hP, univ_eq_empty])
      (by simp) t
    simp only [hr0, ← hs]
    simp only [mul_zero, zero_mul, add_zero, one_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, div_zero, exp_zero] at h1 ⊢
    exact (le_abs_self _).trans h1
  -- The scalar estimates for `P = exp (r g)`.
  have hr₁ : r ≤ 1 / 4 := by linarith only [hrl, hℓ]
  have hrg (v : V) : |r * g v| ≤ r := by
    rw [abs_mul, abs_of_nonneg hr]; exact mul_le_of_le_one_right hr (hg₁ v)
  have hexp (v : V) : |P v - 1 - r * g v| ≤ r ^ 2 :=
    (Real.abs_exp_sub_one_sub_id_le ((hrg v).trans (by linarith only [hr₁]))).trans
      ((mul_pow r (g v) 2).trans_le
        (mul_le_of_le_one_right (sq_nonneg r) ((sq_le_one_iff_abs_le_one _).2 (hg₁ v))))
  have hP1 (v : V) : |P v - 1| ≤ 2 * r := by
    have hr2_le : r ^ 2 ≤ r := by rw [sq]; exact mul_le_of_le_one_right hr (by linarith only [hr₁])
    linarith only [abs_sub_abs_le_abs_sub (P v - 1) (r * g v), hexp v, hrg v, hr2_le]
  have hm : 𝔼 v, P v ≤ 1 + r ^ 2 := by
    calc 𝔼 v, P v ≤ 𝔼 v, (1 + r * g v + r ^ 2) :=
          expect_le_expect fun v _ => by linarith only [(abs_le.1 (hexp v)).2]
      _ ≤ 1 + r ^ 2 := by
          rw [expect_add_distrib, expect_add_distrib, ← mul_expect, hg]
          rcases isEmpty_or_nonempty V with hV | hV
          · simp only [univ_eq_empty, expect_empty, mul_zero, add_zero]; positivity
          · simp
  set θ := 4 * r / s
  have hθs : θ * s = 4 * r := div_mul_cancel₀ _ hs.ne'
  have hθ : 0 ≤ θ := by positivity
  have hθ₁ : θ ≤ 1 := by rw [div_le_one hs]; exact hrl
  set ρ := 1 + 9 * r ^ 2 / s
  have hρ : 1 ≤ ρ := le_add_of_nonneg_right (by positivity)
  have hr2 : r ^ 2 ≤ r ^ 2 / s := le_div_self (sq_nonneg r) hs (sub_le_self _ hℓ)
  have h₁ : 𝔼 v, P v + θ * (2 * r) ≤ ρ := by
    have : θ * (2 * r) = 8 * r ^ 2 / s := by field_simp; linear_combination (2 * r) * hθs
    rw [this, show ρ = 1 + r ^ 2 / s + 8 * r ^ 2 / s by simp only [ρ]; ring]
    linarith only [hm, hr2]
  have h₂ : 2 * r * ℓ + θ * ((1 + 2 * r) * ℓ) ≤ ρ * θ := by
    refine le_trans ?_ (le_mul_of_one_le_left hθ hρ)
    rw [← sub_nonneg, show θ - (2 * r * ℓ + θ * ((1 + 2 * r) * ℓ)) =
      4 * r * s + 2 * r * ℓ * (1 - θ) by linear_combination hθs]
    exact add_nonneg (by positivity) (mul_nonneg (by positivity) (sub_nonneg.2 hθ₁))
  have hW := G.abs_expect_weightedWalk_const_le (fun v => (exp_pos _).le) hP1 (by positivity) hθ
    h₁ h₂ t
  calc 𝔼 v, G.weightedWalk t (fun _ => P) v
      ≤ |𝔼 v, G.weightedWalk t (fun _ => P) v| := le_abs_self _
    _ ≤ ρ ^ (t + 1) := le_trans (le_add_of_nonneg_right (by positivity)) hW
    _ ≤ exp (9 * r ^ 2 / s) ^ (t + 1) := by
        gcongr
        linarith only [Real.add_one_le_exp (9 * r ^ 2 / s)]
    _ = exp (9 * r ^ 2 * (t + 1) / s) := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf

/-- One tail of the expander Chernoff bound for a bounded function with mean zero. -/
private theorem dens_filter_le_sum_walkAt_le [Nonempty D] {g : V → ℝ} (hg : 𝔼 v, g v = 0)
    (hg₁ : ∀ v, |g v| ≤ 1) {δ : ℝ} (hδ : 0 < δ) (t : ℕ) :
    (dens {p : V × (Fin t → D) | δ * (t + 1) ≤ ∑ i ∈ range (t + 1), g (G.walkAt p i)} : ℝ) ≤
      exp (-(1 - G.spectralExpansion) * δ ^ 2 * (t + 1) / 36) := by
  set ℓ := G.spectralExpansion
  set s := 1 - ℓ
  have hℓ := G.spectralExpansion_nonneg
  have hℓ₁ := G.spectralExpansion_le_one
  have hs : 0 ≤ s := sub_nonneg.2 hℓ₁
  have ht : (0 : ℝ) < t + 1 := by positivity
  rcases le_or_gt δ 1 with hδ₁ | hδ₁
  swap
  · -- For `δ > 1` the event is empty.
    refine le_of_eq_of_le ?_ (exp_pos _).le
    rw [NNRat.cast_eq_zero, dens_eq_zero, filter_eq_empty_iff]
    refine fun p _ => not_le.2 ?_
    refine (sum_le_card_nsmul _ _ 1 fun i _ => (abs_le.1 (hg₁ _)).2).trans_lt ?_
    simpa only [card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one] using
      lt_mul_of_one_lt_left ht hδ₁
  set r := δ * s / 18
  have hr : 0 ≤ r := by positivity
  have hrl : 4 * r ≤ s := by
    simp only [r]; linarith only [hs, mul_le_of_le_one_left hs hδ₁]
  have hmgf := G.expect_exp_mul_sum_walkAt_le hg hg₁ hr hrl t
  have hmarkov := Fintype.mul_dens_filter_le_expect (𝕜 := ℝ)
    (f := fun p : V × (Fin t → D) => exp (r * ∑ i ∈ range (t + 1), g (G.walkAt p i)))
    (fun _ => (exp_pos _).le) (exp (r * (δ * (t + 1))))
  have hsub : ({p : V × (Fin t → D) | δ * (t + 1) ≤ ∑ i ∈ range (t + 1), g (G.walkAt p i)} :
      Finset _) ⊆ ({p | exp (r * (δ * (t + 1))) ≤
        exp (r * ∑ i ∈ range (t + 1), g (G.walkAt p i))} : Finset _) :=
    monotone_filter_right _ fun p _ hp => exp_le_exp.2 (mul_le_mul_of_nonneg_left hp hr)
  have hdens : (dens {p : V × (Fin t → D) |
      δ * (t + 1) ≤ ∑ i ∈ range (t + 1), g (G.walkAt p i)} : ℝ) ≤
      exp (9 * r ^ 2 * (t + 1) / s) / exp (r * (δ * (t + 1))) := by
    rw [le_div_iff₀ (exp_pos _), mul_comm]
    refine le_trans ?_ (hmarkov.trans hmgf)
    gcongr
  refine hdens.trans_eq ?_
  rw [← exp_sub]
  congr 1
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · simp [r, ← hs0]
  · simp only [r]; field_simp; ring

/-- **The expander Chernoff bound** for a function `g` with mean zero and `|g| ≤ 1`: the sum of
`g` over the `t + 1` vertices of a uniformly started walk of length `t` has absolute value at
least `δ (t + 1)` with probability at most `2 exp (-(1 - λ(G)) δ² (t + 1) / 36)`. -/
theorem dens_filter_le_abs_sum_walkAt_le [Nonempty D] {g : V → ℝ} (hg : 𝔼 v, g v = 0)
    (hg₁ : ∀ v, |g v| ≤ 1) {δ : ℝ} (hδ : 0 < δ) (t : ℕ) :
    (dens {p : V × (Fin t → D) | δ * (t + 1) ≤ |∑ i ∈ range (t + 1), g (G.walkAt p i)|} : ℝ) ≤
      2 * exp (-(1 - G.spectralExpansion) * δ ^ 2 * (t + 1) / 36) := by
  classical
  have hup := G.dens_filter_le_sum_walkAt_le hg hg₁ hδ t
  have hlow := G.dens_filter_le_sum_walkAt_le (g := fun v => -g v)
    (by rw [expect_neg_distrib, hg, neg_zero]) (fun v => by rw [abs_neg]; exact hg₁ v) hδ t
  set S := ({p : V × (Fin t → D) | δ * (t + 1) ≤ ∑ i ∈ range (t + 1), g (G.walkAt p i)} :
    Finset _)
  set T := ({p : V × (Fin t → D) | δ * (t + 1) ≤ ∑ i ∈ range (t + 1), -g (G.walkAt p i)} :
    Finset _)
  have hsub : ({p : V × (Fin t → D) | δ * (t + 1) ≤ |∑ i ∈ range (t + 1), g (G.walkAt p i)|} :
      Finset _) ⊆ S ∪ T := by
    intro p hp
    simp only [S, T, mem_filter, mem_univ, true_and, mem_union, sum_neg_distrib] at hp ⊢
    rcases le_abs'.1 hp with h | h
    · right; linarith only [h]
    · left; exact h
  calc _ ≤ (dens (S ∪ T) : ℝ) := by exact_mod_cast dens_le_dens hsub
    _ ≤ dens S + dens T := by exact_mod_cast dens_union_le S T
    _ ≤ _ := by linarith only [hup, hlow]

variable [DecidableEq V]

/-- **The expander Chernoff bound** for visits to a set `B`, with constant `36`: the fraction
of the `t + 1` vertices of a uniformly started walk of length `t` that lie in `B` deviates from
the density of `B` by more than `δ` with probability at most
`2 exp (-(1 - λ(G)) δ² (t + 1) / 36)`. This is [Arora and Barak, Theorem 7.41][AroraBarak07]
with the sign of the exponent corrected and the constant `60` improved to `36`; the draft's form
is `dens_filter_abs_visitCount_div_sub_gt_lt`. -/
theorem dens_filter_abs_visitCount_div_sub_dens_gt_le [Nonempty D] (B : Finset V) {δ : ℝ}
    (hδ : 0 < δ) (t : ℕ) :
    (dens {p : V × (Fin t → D) | δ < |(G.visitCount B p : ℝ) / (t + 1) - dens B|} : ℝ) ≤
      2 * exp (-(1 - G.spectralExpansion) * δ ^ 2 * (t + 1) / 36) := by
  set β : ℝ := ((dens B : ℚ≥0) : ℝ)
  set g : V → ℝ := fun v => (if v ∈ B then 1 else 0) - β
  have hβ₀ : 0 ≤ β := by positivity
  have hβ₁ : β ≤ 1 := by simp only [β]; exact_mod_cast dens_le_one
  rcases isEmpty_or_nonempty V with hV | hV
  · simp [univ_eq_empty, exp_pos, le_of_lt]
  have hg : 𝔼 v, g v = 0 := by
    simp only [g, expect_sub_distrib, Fintype.expect_boole_mem, Fintype.expect_const, β, sub_self]
  have hg₁ (v : V) : |g v| ≤ 1 := by
    simp only [g]; split_ifs <;> rw [abs_le] <;> constructor <;> linarith only [hβ₀, hβ₁]
  have ht : (0 : ℝ) < t + 1 := by positivity
  have hsum (p : V × (Fin t → D)) :
      ∑ i ∈ range (t + 1), g (G.walkAt p i) = G.visitCount B p - (t + 1) * β := by
    simp only [g, sum_sub_distrib, sum_boole, sum_const, card_range, nsmul_eq_mul, visitCount]
    push_cast; ring
  refine le_trans ?_ (G.dens_filter_le_abs_sum_walkAt_le hg hg₁ hδ t)
  gcongr with p
  intro hp
  rw [hsum, show (G.visitCount B p : ℝ) - (t + 1) * β =
      (t + 1) * ((G.visitCount B p : ℝ) / (t + 1) - β) by field_simp, abs_mul, abs_of_pos ht,
    mul_comm]
  exact mul_le_mul_of_nonneg_left hp.le ht.le

/-- **Arora–Barak Theorem 7.41**, the expander Chernoff bound, in the draft's form with the sign
of the exponent corrected. Let `G` have spectral expansion at most `λ`, `B` a set of density
`β`, and `X₁, …, X_k` the `k = t + 1` vertices of a `t`-step walk from a uniformly random vertex.
Then for every `δ > 0`, `Pr[|∑ᵢ 1_B(Xᵢ) / k - β| > δ] < 2 exp (-(1 - λ) δ² k / 60)`.
[Arora and Barak, Theorem 7.41 (p. 145, PDF p. 161)][AroraBarak07] prints the exponent as
`+(1 - λ) δ² k / 60`, which makes the bound at least `2` and the theorem vacuous. The sharper
constant `36` is `dens_filter_abs_visitCount_div_sub_dens_gt_le`. -/
theorem dens_filter_abs_visitCount_div_sub_gt_lt [Nonempty D] (B : Finset V) {lam δ : ℝ}
    (hlam : G.spectralExpansion ≤ lam) (hδ : 0 < δ) (t : ℕ) :
    (dens {p : V × (Fin t → D) | δ < |(G.visitCount B p : ℝ) / (t + 1) - dens B|} : ℝ) <
      2 * exp (-(1 - lam) * δ ^ 2 * (t + 1) / 60) := by
  have h := G.dens_filter_abs_visitCount_div_sub_dens_gt_le B hδ t
  have hℓ₁ := G.spectralExpansion_le_one
  have ht : (0 : ℝ) < t + 1 := by positivity
  rcases eq_or_lt_of_le hℓ₁ with hℓ | hℓ
  · -- `λ(G) = 1`, so `λ ≥ 1` and the bound is at least `2`.
    have hd : (dens {p : V × (Fin t → D) |
        δ < |(G.visitCount B p : ℝ) / (t + 1) - dens B|} : ℝ) ≤ 1 := by
      exact_mod_cast dens_le_one
    have : 1 ≤ exp (-(1 - lam) * δ ^ 2 * (t + 1) / 60) := by
      rw [neg_sub]
      have : 0 ≤ lam - 1 := by linarith only [hℓ, hlam]
      exact Real.one_le_exp (by positivity)
    linarith only [hd, this]
  · refine h.trans_lt (mul_lt_mul_of_pos_left (exp_lt_exp.2 ?_) two_pos)
    have hpos : 0 < (1 - G.spectralExpansion) * δ ^ 2 * (t + 1) :=
      mul_pos (mul_pos (sub_pos.2 hℓ) (sq_pos_of_pos hδ)) ht
    have hle : (1 - lam) * δ ^ 2 * (t + 1) ≤ (1 - G.spectralExpansion) * δ ^ 2 * (t + 1) := by
      gcongr
    linarith only [hpos, hle]

end Cslib.RotationMap
