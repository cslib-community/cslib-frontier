/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Basic
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Fourth moments of the random walk

The spectral expansion `λ(G)` controls second moments: a walk of length `t` multiplies
`𝔼 f²` by at most `λ(G) ^ (2 t)` when `𝔼 f = 0`
(`expect_walk_pow_sq_le_spectralExpansion_pow_mul`). This file derives the same kind of decay for
fourth moments, with elementary arguments only.

The walk averages over neighbors, so Jensen's inequality holds pointwise:
`(G.walk f v) ^ 2 ≤ G.walk (f ^ 2) v` (`sq_walk_le`), and therefore the walk does not increase
fourth moments (`expect_walk_pow_pow_four_le`). For the decay, write `g = W ^ s f`, where `W` is
the walk operator. Then `(W ^ t g) ^ 4 ≤ (W ^ t (g ^ 2)) ^ 2` pointwise. The function `g ^ 2` is
its mean `m = 𝔼 g²` plus a part of expectation zero. The walk multiplies the second moment of
that part by `λ ^ (2 t)`. Hence

`𝔼 (W ^ (s + t) f) ^ 4 ≤ m ^ 2 + λ ^ (2 t) 𝔼 g ^ 4 ≤ (λ ^ (4 s) + λ ^ (2 t)) 𝔼 f ^ 4`,

using `m ≤ λ ^ (2 s) 𝔼 f²` and `(𝔼 f²)² ≤ 𝔼 f⁴` (`expect_walk_pow_add_pow_four_le`). With
`s = t` the fourth moment decays like `2 λ ^ (2 t)` over `2 t` steps
(`expect_walk_pow_two_mul_pow_four_le`). Up to constants, this is the `p = 4` case of the
`Lᵖ` contraction of a Markov operator with a spectral gap. That contraction usually comes from
the Riesz–Thorin interpolation theorem; here no interpolation is needed. The centred form
(`expect_walk_pow_two_mul_sub_expect_pow_four_le`) applies to every function.

The use of `Lᵖ` contraction of the walk (idea 8 in issue #474) comes from the OpenAI preprint
on derandomizing logarithmic space [OpenAI2026LogSpace], where the `Lˢ` decay
`‖K ^ d - Π‖_{s → s} ≤ 2 ^ (1 - 2 / s) (1 - γ) ^ (2 d / s)` appears in the proof of Lemma 6.2 and
comes from the Riesz–Thorin theorem; the Jensen argument here is a different proof.

## Main results

* `Cslib.RotationMap.sq_walk_pow_le`: Jensen's inequality for walks of every length, from the
  one-step `Cslib.RotationMap.sq_walk_le`.
* `Cslib.RotationMap.expect_walk_pow_pow_four_le`: walks do not increase fourth moments.
* `Cslib.RotationMap.expect_walk_pow_add_pow_four_le`: the fourth-moment decay
  `𝔼 (W ^ (s + t) f) ^ 4 ≤ (λ ^ (4 s) + λ ^ (2 t)) 𝔼 f ^ 4` for `𝔼 f = 0`.
* `Cslib.RotationMap.expect_walk_pow_two_mul_pow_four_le`,
  `Cslib.RotationMap.expect_walk_pow_two_mul_sub_expect_pow_four_le`: over `2 t` steps the
  fourth moment of the deviation from the mean shrinks by `2 λ ^ (2 t)`.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  proof of Lemma 6.2 (preprint, not peer reviewed)
-/

public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V D : Type*} (G : RotationMap V D)

section Pointwise

variable [Fintype D]

/-- The walk operator is monotone. -/
theorem walk_mono {f g : V → ℝ} (h : ∀ v, f v ≤ g v) (v : V) : G.walk f v ≤ G.walk g v := by
  simp only [walk_apply]
  exact expect_le_expect fun i _ ↦ h _

/-- **Jensen's inequality for walks of every length.** -/
theorem sq_walk_pow_le (t : ℕ) (f : V → ℝ) (v : V) :
    (G.walk ^ t) f v ^ 2 ≤ (G.walk ^ t) (fun w ↦ f w ^ 2) v := by
  induction t generalizing v with
  | zero => simp
  | succ t ih =>
    rw [show G.walk ^ (t + 1) = G.walk * G.walk ^ t from pow_succ' _ _, mul_apply_eq_comp,
      mul_apply_eq_comp]
    exact (G.sq_walk_le _ v).trans (G.walk_mono ih v)

/-- **Jensen's inequality for fourth powers.** -/
theorem pow_four_walk_pow_le (t : ℕ) (f : V → ℝ) (v : V) :
    (G.walk ^ t) f v ^ 4 ≤ (G.walk ^ t) (fun w ↦ f w ^ 4) v := by
  calc (G.walk ^ t) f v ^ 4 = ((G.walk ^ t) f v ^ 2) ^ 2 := by ring
    _ ≤ ((G.walk ^ t) (fun w ↦ f w ^ 2) v) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) (G.sq_walk_pow_le t f v) 2
    _ ≤ (G.walk ^ t) (fun w ↦ f w ^ 4) v :=
        (G.sq_walk_pow_le t _ v).trans_eq
          (by rw [show (fun w ↦ (f w ^ 2) ^ 2) = fun w ↦ f w ^ 4 from funext fun _ ↦ by ring])

end Pointwise

section Moments

variable [Fintype V] [Fintype D] [Nonempty D]

/-- **Walks do not increase fourth moments.** -/
theorem expect_walk_pow_pow_four_le (t : ℕ) (f : V → ℝ) :
    𝔼 v, (G.walk ^ t) f v ^ 4 ≤ 𝔼 v, f v ^ 4 :=
  (expect_le_expect fun v _ ↦ G.pow_four_walk_pow_le t f v).trans_eq
    (G.expect_walk_pow t fun w ↦ f w ^ 4)

/-- The square of the second moment is at most the fourth moment. -/
private theorem sq_expect_sq_le_expect_pow_four (f : V → ℝ) :
    (𝔼 v, f v ^ 2) ^ 2 ≤ 𝔼 v, f v ^ 4 := by
  have h := expect_mul_sq_le_sq_mul_sq univ (fun v ↦ f v ^ 2) fun _ ↦ (1 : ℝ)
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  simp only [mul_one, one_pow, Fintype.expect_const] at h
  simpa only [← pow_mul] using h

/-- **Fourth-moment decay of the random walk**: for `𝔼 f = 0`, a walk of length `s + t`
multiplies the fourth moment by at most `λ(G) ^ (4 s) + λ(G) ^ (2 t)`. -/
theorem expect_walk_pow_add_pow_four_le {f : V → ℝ} (hf : 𝔼 v, f v = 0) (s t : ℕ) :
    𝔼 v, (G.walk ^ (s + t)) f v ^ 4 ≤
      (G.spectralExpansion ^ (4 * s) + G.spectralExpansion ^ (2 * t)) * 𝔼 v, f v ^ 4 := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  set g := (G.walk ^ s) f with hg
  set q : V → ℝ := fun w ↦ g w ^ 2 with hq
  set m := 𝔼 v, q v with hm
  set h := (G.walk ^ t) fun w ↦ q w - m with hh
  -- The walk of `q` is its mean plus the walk of the part of expectation zero.
  have hq_split (v : V) : (G.walk ^ t) q v = h v + m := by
    rw [show q = (fun w ↦ q w - m) + fun _ ↦ m from funext fun _ ↦ (sub_add_cancel _ _).symm,
      map_add, Pi.add_apply, walk_pow_const]
  have hq0 : 𝔼 v, (q v - m) = 0 := by
    rw [expect_sub_distrib, Fintype.expect_const, sub_self]
  -- Pointwise Jensen reduces the fourth moment to the second moment of the walk of `q`.
  have h₁₂ : 𝔼 v, (G.walk ^ t) g v ^ 4 ≤ 𝔼 v, h v ^ 2 + m ^ 2 := by
    refine (expect_le_expect (g := fun v ↦ (h v + m) ^ 2) fun v _ ↦ ?_).trans_eq ?_
    · rw [← hq_split, show (G.walk ^ t) g v ^ 4 = ((G.walk ^ t) g v ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ (sq_nonneg _) (G.sq_walk_pow_le t g v) 2
    · have hh0 : 𝔼 v, h v = 0 := G.expect_walk_pow_eq_zero hq0 t
      simp only [add_sq, expect_add_distrib, ← expect_mul, ← mul_expect, hh0, Fintype.expect_const]
      ring
  -- The part of expectation zero decays at rate `λ ^ (2 t)`.
  have h₃ : 𝔼 v, h v ^ 2 ≤ G.spectralExpansion ^ (2 * t) * 𝔼 v, f v ^ 4 := by
    refine (G.expect_walk_pow_sq_le_spectralExpansion_pow_mul hq0 t).trans
      (mul_le_mul_of_nonneg_left ?_ (pow_nonneg G.spectralExpansion_nonneg _))
    have hqm : 𝔼 v, (q v - m) ^ 2 = 𝔼 v, g v ^ 4 - m ^ 2 := by
      simp only [sub_sq, expect_sub_distrib, expect_add_distrib, ← expect_mul, ← mul_expect,
        Fintype.expect_const, ← hm, show (fun v ↦ q v ^ 2) = fun v ↦ g v ^ 4 from
          funext fun v ↦ by rw [hq]; ring]
      ring
    exact (hqm.trans_le (sub_le_self _ (sq_nonneg _))).trans (G.expect_walk_pow_pow_four_le s f)
  -- The mean of `q` decays at rate `λ ^ (2 s)`.
  have h₄ : m ^ 2 ≤ G.spectralExpansion ^ (4 * s) * 𝔼 v, f v ^ 4 := by
    have hm0 : 0 ≤ m := expect_nonneg fun _ _ ↦ sq_nonneg _
    calc m ^ 2 ≤ (G.spectralExpansion ^ (2 * s) * 𝔼 v, f v ^ 2) ^ 2 :=
          pow_le_pow_left₀ hm0 (G.expect_walk_pow_sq_le_spectralExpansion_pow_mul hf s) 2
      _ = G.spectralExpansion ^ (4 * s) * (𝔼 v, f v ^ 2) ^ 2 := by ring
      _ ≤ G.spectralExpansion ^ (4 * s) * 𝔼 v, f v ^ 4 :=
          mul_le_mul_of_nonneg_left (sq_expect_sq_le_expect_pow_four f)
            (pow_nonneg G.spectralExpansion_nonneg _)
  rw [add_comm, pow_add, mul_apply_eq_comp]
  linarith

/-- **Fourth-moment decay over `2 t` steps**: for `𝔼 f = 0`, a walk of length `2 t` multiplies
the fourth moment by at most `2 λ(G) ^ (2 t)`. -/
theorem expect_walk_pow_two_mul_pow_four_le {f : V → ℝ} (hf : 𝔼 v, f v = 0) (t : ℕ) :
    𝔼 v, (G.walk ^ (2 * t)) f v ^ 4 ≤ 2 * G.spectralExpansion ^ (2 * t) * 𝔼 v, f v ^ 4 := by
  have h := G.expect_walk_pow_add_pow_four_le hf t t
  rw [← two_mul t] at h
  have hpow := pow_le_pow_of_le_one G.spectralExpansion_nonneg G.spectralExpansion_le_one
    (show 2 * t ≤ 4 * t by omega)
  have h4 : 0 ≤ 𝔼 v, f v ^ 4 := expect_nonneg fun _ _ ↦ by positivity
  nlinarith [mul_le_mul_of_nonneg_right hpow h4]

/-- **Fourth-moment decay for every function**: over `2 t` steps, the fourth moment of the
deviation from the mean shrinks by at least the factor `2 λ(G) ^ (2 t)`. -/
theorem expect_walk_pow_two_mul_sub_expect_pow_four_le (f : V → ℝ) (t : ℕ) :
    𝔼 v, ((G.walk ^ (2 * t)) f v - 𝔼 w, f w) ^ 4 ≤
      2 * G.spectralExpansion ^ (2 * t) * 𝔼 v, (f v - 𝔼 w, f w) ^ 4 := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  set c := 𝔼 w, f w
  have hc : 𝔼 v, (f v - c) = 0 := by rw [expect_sub_distrib, Fintype.expect_const, sub_self]
  have hsub : (G.walk ^ (2 * t)) (fun w ↦ f w - c) = fun v ↦ (G.walk ^ (2 * t)) f v - c := by
    change (G.walk ^ (2 * t)) (f - fun _ ↦ c) = _
    rw [map_sub, walk_pow_const]
    rfl
  simpa only [hsub] using G.expect_walk_pow_two_mul_pow_four_le hc t

end Moments

end Cslib.RotationMap
