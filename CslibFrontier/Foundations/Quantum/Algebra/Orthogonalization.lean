/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Consistency

/-!
# Orthogonalization: the estimate

An almost projective measurement is close to a projective one in the state
[de la Salle, Theorem 1.2][delaSalle2022]. This file proves the estimate behind it, in any
star-ordered algebra, from the data that the construction provides
(arXiv:2103.14126v2, §3, the proof of Theorem 1.2 when `M` is finite): a POVM `a`, projections
`q_a` commuting with `a_a`, a projective measurement `p`, and an element `0 ≤ h ≤ 1` with

`h² = ∑_a q_a a_a`, `h p_a h = q_a a_a`, `φ(∑_a a_a²) ≤ φ(∑_a q_a a_a)`.

Then `∑_a ‖a_a - p_a‖²_φ ≤ 9 (1 - φ(∑_a a_a²))`
(`Cslib.Quantum.Measurement.sum_norm_sub_sq_le_of_dilation`). The proof splits
`a_a - p_a = (1 - q_a) a_a + (h - 1) p_a h + p_a (h - 1)` and bounds each part by
`1 - φ(∑_a a_a²)`, using `x² ≤ x` for `0 ≤ x ≤ 1`:

* `‖(1 - q_a) a_a‖² = φ((1 - q_a) a_a²) ≤ φ((1 - q_a) a_a)`, which sums to `1 - φ(∑_a q_a a_a)`;
* `‖(h - 1) p_a h‖² ≤ φ(h p_a (1 - h²) p_a h) = φ(q_a a_a - (q_a a_a)²) ≤ φ(a_a - a_a²)`;
* `‖p_a (h - 1)‖²` sums to `φ((1 - h)²) ≤ φ(1 - h²) = 1 - φ(∑_a q_a a_a)`.

## Main results

* `Cslib.Quantum.Measurement.sum_norm_sub_sq_le_of_dilation`: the orthogonalization estimate.

## References

* [M. de la Salle, *Orthogonalization of positive operator valued measures*][delaSalle2022]
-/

public section

namespace Cslib.Quantum

open Finset

variable {α A : Type*} [Fintype α] [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
  [Algebra ℂ A] [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/-- `x (1 - x) ≥ 0` sandwiched by a commuting `0 ≤ c`. -/
private theorem nonneg_mul_sub_mul_self {c x : A} (hc : 0 ≤ c) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hcx : Commute c x) : 0 ≤ c * (x - x * x) :=
  Commute.mul_nonneg hc (sub_nonneg.mpr (mul_self_le_self_of_nonneg_of_le_one hx0 hx1))
    (hcx.sub_right (hcx.mul_right hcx))

/-- `n ≤ x + y + z` with `0 ≤ n` gives `n² ≤ 3 (x² + y² + z²)`. -/
private theorem sq_le_three_mul_of_le_add {n x y z : ℝ} (hn : 0 ≤ n) (h : n ≤ x + y + z) :
    n ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [pow_le_pow_left₀ hn h 2, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

variable [StarModule ℂ A] [SelfAdjointDecompose A]

namespace Measurement

/-- **The orthogonalization estimate** [de la Salle, §3][delaSalle2022]: given projections `q_a`
commuting with the effects `a_a` of a measurement, a projective measurement `p` and `0 ≤ h ≤ 1`
with `h² = ∑_a q_a a_a`, `h p_a h = q_a a_a` and `φ(∑_a a_a²) ≤ φ(∑_a q_a a_a)`, the measurement is
close to `p` in the state: `∑_a ‖a_a - p_a‖²_φ ≤ 9 (1 - φ(∑_a a_a²))`. -/
theorem sum_norm_sub_sq_le_of_dilation (φ : AlgState A) (M P : Measurement α A)
    (hP : P.IsProjective) (q : α → A) (hqq : ∀ a, q a * q a = q a)
    (hqs : ∀ a, IsSelfAdjoint (q a)) (hqc : ∀ a, Commute (q a) (M.effect a)) {h : A}
    (h0 : 0 ≤ h) (h1 : h ≤ 1) (hh : h * h = ∑ a, q a * M.effect a)
    (hp : ∀ a, h * P.effect a * h = q a * M.effect a)
    (hsel : ∑ a, (φ (M.effect a * M.effect a)).re ≤ (φ (∑ a, q a * M.effect a)).re) :
    ∑ a, φ.norm (M.effect a - P.effect a) ^ 2 ≤
      9 * (1 - ∑ a, (φ (M.effect a * M.effect a)).re) := by
  set δ := 1 - ∑ a, (φ (M.effect a * M.effect a)).re
  have hM : ∀ a, star (M.effect a) = M.effect a := fun a => (M.nonneg a).isSelfAdjoint.star_eq
  have hPs : ∀ a, star (P.effect a) = P.effect a := fun a => (P.nonneg a).isSelfAdjoint.star_eq
  have hq : ∀ a, star (q a) = q a := fun a => (hqs a).star_eq
  have hhs : star h = h := h0.isSelfAdjoint.star_eq
  have h1q : ∀ a, 0 ≤ 1 - q a := fun a => by
    simpa only [star_sub, star_one, hq, sub_mul, one_mul, mul_sub, mul_one, hqq, sub_self,
      sub_zero] using star_mul_self_nonneg (1 - q a)
  have hsum1 : ∑ a, M.effect a = 1 := M.sum_effect
  have hsumP : ∑ a, P.effect a = 1 := P.sum_effect
  have hφ1 : (φ 1).re = 1 := by rw [φ.map_one, Complex.one_re]
  -- Common bound: `∑_a Re φ(a_a - a_a²) = δ`.
  have hδ : ∑ a, (φ (M.effect a - M.effect a * M.effect a)).re = δ := by
    simp only [map_sub, Complex.sub_re, sum_sub_distrib]
    rw [← Complex.re_sum, ← map_sum, hsum1, hφ1]
  -- First part: `(1 - q_a) a_a`.
  have t₁ : ∀ a, star ((1 - q a) * M.effect a) * ((1 - q a) * M.effect a) ≤
      M.effect a - q a * M.effect a := fun a => by
    have hc : Commute (1 - q a) (M.effect a) := (Commute.one_left _).sub_left (hqc a)
    have hidem : (1 - q a) * (1 - q a) = 1 - q a := by
      rw [sub_mul, one_mul, mul_sub, mul_one, hqq, sub_self, sub_zero]
    have := nonneg_mul_sub_mul_self (h1q a) (M.nonneg a) (M.effect_le_one a) hc
    have hl : star ((1 - q a) * M.effect a) * ((1 - q a) * M.effect a) =
        (1 - q a) * (M.effect a * M.effect a) := by
      rw [star_mul, star_sub, star_one, hq, hM]
      calc M.effect a * (1 - q a) * ((1 - q a) * M.effect a)
          = M.effect a * ((1 - q a) * (1 - q a)) * M.effect a := by simp only [mul_assoc]
        _ = (1 - q a) * M.effect a * M.effect a := by rw [hidem, ← hc.eq]
        _ = _ := mul_assoc _ _ _
    rw [hl, ← sub_nonneg]
    convert this using 1
    noncomm_ring
  have b₁ : ∑ a, φ.norm ((1 - q a) * M.effect a) ^ 2 ≤ δ := by
    calc ∑ a, φ.norm ((1 - q a) * M.effect a) ^ 2
        ≤ ∑ a, (φ (M.effect a - q a * M.effect a)).re :=
          sum_le_sum fun a _ => φ.norm_sq_le_of_star_mul_le (t₁ a)
      _ = 1 - (φ (∑ a, q a * M.effect a)).re := by
          simp only [map_sub, Complex.sub_re, sum_sub_distrib, ← Complex.re_sum, ← map_sum,
            hsum1, hφ1]
      _ ≤ δ := by linarith
  -- `(h - 1)² ≤ 1 - h²`, from `h² ≤ h`.
  have hle : (h - 1) * (h - 1) ≤ 1 - h * h := by
    have hsq : h * h ≤ h := mul_self_le_self_of_nonneg_of_le_one h0 h1
    rw [← sub_nonneg]
    have : 1 - h * h - (h - 1) * (h - 1) = 2 * (h - h * h) := by noncomm_ring
    rw [this, two_mul]
    exact add_nonneg (sub_nonneg.mpr hsq) (sub_nonneg.mpr hsq)
  -- Third part: `p_a (h - 1)`.
  have b₃ : ∑ a, φ.norm (P.effect a * (h - 1)) ^ 2 ≤ δ := by
    calc ∑ a, φ.norm (P.effect a * (h - 1)) ^ 2
        = ∑ a, (φ ((h - 1) * P.effect a * (h - 1))).re := by
          refine sum_congr rfl fun a _ => ?_
          rw [AlgState.norm_sq, star_mul, star_sub, star_one, hhs, hPs, mul_assoc,
            ← mul_assoc (P.effect a), hP a, ← mul_assoc]
      _ = (φ ((h - 1) * (h - 1))).re := by
          rw [← Complex.re_sum, ← map_sum, ← sum_mul, ← mul_sum, hsumP, mul_one]
      _ ≤ (φ (1 - h * h)).re := φ.re_apply_mono hle
      _ ≤ δ := by
          rw [map_sub, Complex.sub_re, hφ1, hh]
          linarith
  -- Second part: `(h - 1) p_a h`.
  have b₂ : ∑ a, φ.norm ((h - 1) * P.effect a * h) ^ 2 ≤ δ := by
    have t₂ : ∀ a, star ((h - 1) * P.effect a * h) * ((h - 1) * P.effect a * h) ≤
        M.effect a - M.effect a * M.effect a := fun a => by
      have hconj := star_left_conjugate_le_conjugate hle (P.effect a * h)
      have hlhs : star ((h - 1) * P.effect a * h) * ((h - 1) * P.effect a * h) =
          star (P.effect a * h) * ((h - 1) * (h - 1)) * (P.effect a * h) := by
        rw [star_mul, star_mul, star_mul, star_sub, star_one, hhs, hPs]
        noncomm_ring
      have hrhs : star (P.effect a * h) * (1 - h * h) * (P.effect a * h) =
          q a * M.effect a - q a * M.effect a * (q a * M.effect a) := by
        rw [star_mul, hhs, hPs]
        calc h * P.effect a * (1 - h * h) * (P.effect a * h)
            = h * (P.effect a * P.effect a) * h - h * P.effect a * h * (h * P.effect a * h) := by
              noncomm_ring
          _ = _ := by rw [hP a, hp a]
      have hqa : q a * M.effect a * (q a * M.effect a) = q a * (M.effect a * M.effect a) := by
        rw [mul_assoc, ← mul_assoc (M.effect a), ← (hqc a).eq, mul_assoc, ← mul_assoc, hqq]
      have hfin : q a * M.effect a - q a * (M.effect a * M.effect a) ≤
          M.effect a - M.effect a * M.effect a := by
        rw [← sub_nonneg]
        convert nonneg_mul_sub_mul_self (h1q a) (M.nonneg a) (M.effect_le_one a)
          ((Commute.one_left _).sub_left (hqc a)) using 1
        noncomm_ring
      rw [hlhs]
      exact (hconj.trans_eq (by rw [hrhs, hqa])).trans hfin
    calc ∑ a, φ.norm ((h - 1) * P.effect a * h) ^ 2
        ≤ ∑ a, (φ (M.effect a - M.effect a * M.effect a)).re :=
          sum_le_sum fun a _ => φ.norm_sq_le_of_star_mul_le (t₂ a)
      _ = δ := hδ
  -- Assemble: `a_a - p_a` is the sum of the three parts.
  have hsplit : ∀ a, M.effect a - P.effect a =
      (1 - q a) * M.effect a + (h - 1) * P.effect a * h + P.effect a * (h - 1) := fun a => by
    have := hp a
    calc M.effect a - P.effect a = M.effect a - q a * M.effect a + (h * P.effect a * h -
        P.effect a) := by rw [this]; abel
      _ = _ := by noncomm_ring
  have hpt : ∀ a, φ.norm (M.effect a - P.effect a) ^ 2 ≤
      3 * (φ.norm ((1 - q a) * M.effect a) ^ 2 + φ.norm ((h - 1) * P.effect a * h) ^ 2 +
        φ.norm (P.effect a * (h - 1)) ^ 2) := fun a => by
    rw [hsplit]
    have t₁ := φ.norm_add_le ((1 - q a) * M.effect a) ((h - 1) * P.effect a * h)
    have t₂ := φ.norm_add_le ((1 - q a) * M.effect a + (h - 1) * P.effect a * h)
      (P.effect a * (h - 1))
    exact sq_le_three_mul_of_le_add (φ.norm_nonneg _) (t₂.trans (by linarith))
  calc ∑ a, φ.norm (M.effect a - P.effect a) ^ 2
      ≤ ∑ a, 3 * (φ.norm ((1 - q a) * M.effect a) ^ 2 + φ.norm ((h - 1) * P.effect a * h) ^ 2 +
        φ.norm (P.effect a * (h - 1)) ^ 2) := sum_le_sum fun a _ => hpt a
    _ = 3 * (∑ a, φ.norm ((1 - q a) * M.effect a) ^ 2 +
        ∑ a, φ.norm ((h - 1) * P.effect a * h) ^ 2 + ∑ a, φ.norm (P.effect a * (h - 1)) ^ 2) := by
      rw [← mul_sum, sum_add_distrib, sum_add_distrib]
    _ ≤ 3 * (δ + δ + δ) := by gcongr
    _ = 9 * δ := by ring

end Measurement

end Cslib.Quantum
