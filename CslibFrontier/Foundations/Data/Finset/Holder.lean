/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/MeanInequalities.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.ConjExponents
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.MeanInequalities

/-!
# Hölder's inequality for uniform averages

For nonnegative functions `f`, `g` on a finite type and Hölder conjugate exponents `p`, `q`,
`𝔼 f g ≤ (𝔼 f ^ p) ^ (1 / p) (𝔼 g ^ q) ^ (1 / q)` (`Fintype.expect_mul_le_rpow_mul_rpow`): this
is **Hölder's inequality** for the uniform distribution, the averaged form of Mathlib's
`Real.inner_le_Lp_mul_Lq_of_nonneg`. Its consequence used for hypercontractivity is the
**log-convexity of moments**: for `0 < θ < 1` and `p, q ≥ 0`,
`𝔼 f ^ (θ p + (1 - θ) q) ≤ (𝔼 f ^ p) ^ θ (𝔼 f ^ q) ^ (1 - θ)`
(`Fintype.expect_rpow_le_rpow_mul_rpow`), the "general version of Hölder's inequality" in
O'Donnell's proof of Theorem 9.22 [O'Donnell, Section 9.5][ODonnell2014]. Both are stated first
for averages `𝔼 i ∈ s` over a finset `s`, with nonnegativity required only on `s`, and the
uniform-average forms are their instances at `s = univ`.

## Main results

* `Finset.expect_mul_le_rpow_mul_rpow`: Hölder's inequality for averages over a finset.
* `Finset.expect_rpow_le_rpow_mul_rpow`: log-convexity of moments over a finset.
* `Fintype.expect_mul_le_rpow_mul_rpow`: Hölder's inequality for uniform averages.
* `Fintype.expect_rpow_le_rpow_mul_rpow`: log-convexity of moments.
* `Fintype.expect_rpow_le_rpow_expect`: Jensen's inequality for sublinear powers.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open Finset
open scoped BigOperators

namespace Finset

variable {ι : Type*}

/-- **Hölder's inequality** for averages over a finset: for `f`, `g` nonnegative on `s` and Hölder
conjugate exponents `p`, `q`,
`𝔼_s f g ≤ (𝔼_s f ^ p) ^ (1 / p) (𝔼_s g ^ q) ^ (1 / q)`. -/
theorem expect_mul_le_rpow_mul_rpow (s : Finset ι) {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) {p q : ℝ} (hpq : p.HolderConjugate q) :
    𝔼 i ∈ s, f i * g i ≤ (𝔼 i ∈ s, f i ^ p) ^ (1 / p) * (𝔼 i ∈ s, g i ^ q) ^ (1 / q) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [expect_empty]; positivity
  · have hN : (0 : ℝ) < s.card := by exact_mod_cast card_pos.2 hs
    simp only [expect_eq_sum_div_card]
    rw [Real.div_rpow (sum_nonneg fun i hi => Real.rpow_nonneg (hf i hi) _) hN.le,
      Real.div_rpow (sum_nonneg fun i hi => Real.rpow_nonneg (hg i hi) _) hN.le,
      div_mul_div_comm, ← Real.rpow_add hN, hpq.one_div_add_one_div, one_div_one, Real.rpow_one]
    exact div_le_div_of_nonneg_right (Real.inner_le_Lp_mul_Lq_of_nonneg s hpq hf hg) hN.le

/-- **Log-convexity of moments** for averages over a finset: for `f` nonnegative on `s`,
`0 < θ < 1` and `p, q ≥ 0`, `𝔼_s f ^ (θ p + (1 - θ) q) ≤ (𝔼_s f ^ p) ^ θ (𝔼_s f ^ q) ^ (1 - θ)`.
This is Hölder's inequality with the exponents `1 / θ` and `1 / (1 - θ)`. -/
theorem expect_rpow_le_rpow_mul_rpow (s : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    {θ p q : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    𝔼 i ∈ s, f i ^ (θ * p + (1 - θ) * q) ≤
      (𝔼 i ∈ s, f i ^ p) ^ θ * (𝔼 i ∈ s, f i ^ q) ^ (1 - θ) := by
  have hθ' : 0 < 1 - θ := by linarith
  have h := expect_mul_le_rpow_mul_rpow s (fun i hi => Real.rpow_nonneg (hf i hi) (θ * p))
    (fun i hi => Real.rpow_nonneg (hf i hi) ((1 - θ) * q)) (p := 1 / θ) (q := 1 / (1 - θ))
    ⟨by simp only [one_div, inv_inv, inv_one]; ring, by positivity, by positivity⟩
  have hpow {a b : ℝ} (hb : b ≠ 0) :
      𝔼 i ∈ s, (f i ^ (b * a)) ^ (1 / b) = 𝔼 i ∈ s, f i ^ a :=
    expect_congr rfl fun i hi => by
      rw [← Real.rpow_mul (hf i hi), mul_comm b a, mul_assoc, mul_one_div_cancel hb, mul_one]
  rw [expect_congr rfl fun i hi =>
      (Real.rpow_add_of_nonneg (hf i hi) (by positivity) (by positivity)).symm,
    hpow hθ₀.ne', hpow hθ'.ne', one_div_one_div, one_div_one_div] at h
  exact h

end Finset

namespace Fintype

variable {α : Type*} [Fintype α]

/-- **Hölder's inequality** for uniform averages: for nonnegative `f`, `g` and Hölder conjugate
exponents `p`, `q`, `𝔼 f g ≤ (𝔼 f ^ p) ^ (1 / p) (𝔼 g ^ q) ^ (1 / q)`. -/
theorem expect_mul_le_rpow_mul_rpow {f g : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    𝔼 x, f x * g x ≤ (𝔼 x, f x ^ p) ^ (1 / p) * (𝔼 x, g x ^ q) ^ (1 / q) :=
  Finset.expect_mul_le_rpow_mul_rpow univ (fun x _ => hf x) (fun x _ => hg x) hpq

/-- **Log-convexity of moments**: for nonnegative `f`, `0 < θ < 1` and `p, q ≥ 0`,
`𝔼 f ^ (θ p + (1 - θ) q) ≤ (𝔼 f ^ p) ^ θ (𝔼 f ^ q) ^ (1 - θ)`. This is Hölder's inequality with
the exponents `1 / θ` and `1 / (1 - θ)`. -/
theorem expect_rpow_le_rpow_mul_rpow {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) {θ p q : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    𝔼 x, f x ^ (θ * p + (1 - θ) * q) ≤ (𝔼 x, f x ^ p) ^ θ * (𝔼 x, f x ^ q) ^ (1 - θ) :=
  Finset.expect_rpow_le_rpow_mul_rpow univ (fun x _ => hf x) hθ₀ hθ₁ hp hq

/-- A sublinear power of a nonnegative function has average at most the
same power of its average. -/
theorem expect_rpow_le_rpow_expect [Nonempty α] {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) {p : ℝ}
    (hp₀ : 0 < p) (hp₁ : p < 1) :
    (𝔼 x, f x ^ p) ≤ (𝔼 x, f x) ^ p := by
  simpa only [mul_one, mul_zero, add_zero, Real.rpow_one, Real.rpow_zero,
    Fintype.expect_const, Real.one_rpow] using
    expect_rpow_le_rpow_mul_rpow hf (p := 1) (q := 0) hp₀ hp₁ zero_le_one le_rfl

/-- A bound on a scaled mean is preserved under a sublinear power when the scale
on the right is at least the scale on the left. -/
theorem mul_expect_rpow_le_of_mul_expect_le [Nonempty α] {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) {m M e p : ℝ} (hm : 0 < m) (hmM : m ≤ M) (he : 0 ≤ e)
    (hp₀ : 0 < p) (hp₁ : p < 1) (h : m * (𝔼 x, f x) ≤ M * e) :
    m * (𝔼 x, f x ^ p) ≤ M * e ^ p := by
  have hc : 1 ≤ M / m := (le_div_iff₀ hm).2 (by simpa only [one_mul] using hmM)
  have hmc : m * (M / m) = M := by field_simp
  have hav : (𝔼 x, f x) ≤ M / m * e :=
    le_of_mul_le_mul_left (by rwa [← mul_assoc, hmc]) hm
  have hpow := (expect_rpow_le_rpow_expect hf hp₀ hp₁).trans
    (Real.rpow_le_rpow (expect_nonneg fun x _ => hf x) hav hp₀.le)
  calc
    _ ≤ m * (M / m * e) ^ p := mul_le_mul_of_nonneg_left hpow hm.le
    _ = (m * (M / m) ^ p) * e ^ p := by rw [Real.mul_rpow (zero_le_one.trans hc) he, mul_assoc]
    _ ≤ (m * (M / m)) * e ^ p := by gcongr; exact Real.rpow_le_self_of_one_le hc hp₁.le
    _ = _ := by rw [hmc]

end Fintype
