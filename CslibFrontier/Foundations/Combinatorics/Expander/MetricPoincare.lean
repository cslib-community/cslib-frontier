/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Basic
import CslibFrontier.Foundations.Data.Finset.Expect.Threshold

/-!
# Mean distances on a regular multigraph

A comparison of all-pairs and edge distances for a placement and for real-valued functions on
the same graph gives a comparison of mean squared distances. The scalar comparison is used on
the square of the distance to a suitably chosen vertex.

In the routing argument of #8448, vertices occupy a rectangle. All-pairs distance is bounded by
the sum of a row move and a column move (`expect_dist_le_row_add_column`). Wire prices pay for
these two moves. Two-point placements at the threshold cuts of a real-valued function give its
scalar comparison on integrating over the threshold.

## Main results

* `Cslib.RotationMap.expect_dist_sq_le_of_expect_dist_le` lifts a first-moment bound with
  constant `K` to a second-moment bound with constant `12 * K ^ 2`.
* `Cslib.RotationMap.expect_dist_sq_le_of_forall_expect_dist_le` gives the same bound from
  first-moment control of every placement into the given space.
-/

public section

open Finset
open scoped BigOperators

namespace Cslib

/-- A row move followed by a column move connects independent uniform sites of a rectangle.
All three averages use uniform endpoints along the indicated rows or columns. -/
theorem expect_dist_le_row_add_column {A B X : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] [PseudoMetricSpace X] (f : A → B → X) :
    (𝔼 u : A × B, 𝔼 v : A × B, dist (f u.1 u.2) (f v.1 v.2)) ≤
      (𝔼 a, 𝔼 b, 𝔼 c, dist (f a b) (f a c)) +
        𝔼 b, 𝔼 a, 𝔼 c, dist (f a b) (f c b) := by
  calc
    _ ≤ 𝔼 u : A × B, 𝔼 v : A × B,
        (dist (f u.1 u.2) (f u.1 v.2) + dist (f u.1 v.2) (f v.1 v.2)) :=
      expect_le_expect fun u _ => expect_le_expect fun v _ => dist_triangle _ _ _
    _ = _ := by
      simp only [expect_add_distrib, Fintype.expect_prod_type, Fintype.expect_const]
      congr 1
      simp_rw [expect_comm (ι := A) (κ := B) univ univ]

namespace RotationMap

private lemma sq_sub_le_abs_sq_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) ^ 2 ≤ |a ^ 2 - b ^ 2| := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg ha hb), ← sq_abs, sq]
  exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg _)

/-- A bound on all-pairs mean distance, valid for a specified placement and every scalar
placement on the same regular multigraph, controls all-pairs mean squared distance. -/
theorem expect_dist_sq_le_of_expect_dist_le {V D X : Type*} [Fintype V] [Fintype D]
    [Nonempty V] [Nonempty D] [PseudoMetricSpace X] (G : RotationMap V D) (f : V → X)
    {K : ℝ} (hK : 0 ≤ K)
    (hmetric : (𝔼 i, 𝔼 j, dist (f i) (f j)) ≤
      K * 𝔼 p : V × D, dist (f p.1) (f (G.rot p).1))
    (hscalar : ∀ u : V → ℝ, (𝔼 i, 𝔼 j, |u i - u j|) ≤
      K * 𝔼 p : V × D, |u p.1 - u (G.rot p).1|) :
    (𝔼 i, 𝔼 j, dist (f i) (f j) ^ 2) ≤
      12 * K ^ 2 * 𝔼 p : V × D, dist (f p.1) (f (G.rot p).1) ^ 2 := by
  let d (p : V × D) := dist (f p.1) (f (G.rot p).1)
  obtain ⟨z, _, hz⟩ := exists_le_of_expect_le univ_nonempty hmetric
  let g (i : V) := dist (f z) (f i)
  have hg (i : V) : 0 ≤ g i := dist_nonneg
  have hmean : (𝔼 i, g i) ^ 2 ≤ K ^ 2 * 𝔼 p, d p ^ 2 := by
    calc
      _ ≤ (K * 𝔼 p, d p) ^ 2 :=
        (sq_le_sq₀ (expect_nonneg fun i _ => hg i)
          (mul_nonneg hK (expect_nonneg fun _ _ => dist_nonneg))).mpr hz
      _ ≤ _ := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left (sq_expect_le_expect_sq univ d) (sq_nonneg K)
  have hvar : 2 * (𝔼 i, g i ^ 2) - 2 * (𝔼 i, g i) ^ 2 ≤
      𝔼 i, 𝔼 j, |g i ^ 2 - g j ^ 2| := by
    calc
      _ = 𝔼 i, 𝔼 j, (g i - g j) ^ 2 := by
        simp only [sub_sq', expect_sub_distrib, expect_add_distrib, Fintype.expect_const,
          ← mul_expect, ← expect_mul]
        ring
      _ ≤ _ := expect_le_expect fun i _ =>
        expect_le_expect fun j _ => sq_sub_le_abs_sq_sub (hg i) (hg j)
  have hstart : (𝔼 p : V × D, g p.1 ^ 2) = 𝔼 i, g i ^ 2 :=
    Fintype.expect_comp_fst (β := D) (fun i => g i ^ 2)
  have hends : (𝔼 p : V × D, g (G.rot p).1 ^ 2) = 𝔼 i, g i ^ 2 :=
    (G.expect_comp_rot (fun p => g p.1 ^ 2)).trans hstart
  have hedge : K * (𝔼 p : V × D, |g p.1 ^ 2 - g (G.rot p).1 ^ 2|) ≤
      (𝔼 i, g i ^ 2) + K ^ 2 * 𝔼 p, d p ^ 2 := by
    rw [mul_expect]
    calc
      _ ≤ 𝔼 p : V × D, ((1 / 2 : ℝ) * (g p.1 ^ 2 + g (G.rot p).1 ^ 2) + K ^ 2 * d p ^ 2) := by
        refine expect_le_expect fun p _ => ?_
        have hL : |g p.1 - g (G.rot p).1| ≤ d p := by
          simpa only [g, d, dist_comm (f z)] using abs_dist_sub_le (f p.1) (f (G.rot p).1) (f z)
        rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (hg _) (hg _)), ← mul_assoc]
        have hle := mul_le_mul_of_nonneg_left hL
          (mul_nonneg hK (add_nonneg (hg p.1) (hg (G.rot p).1)))
        nlinarith only [hle, sq_nonneg (K * d p - g p.1), sq_nonneg (K * d p - g (G.rot p).1)]
      _ = _ := by
        simp only [expect_add_distrib, ← mul_expect, hstart, hends]
        ring
  have hsecond := (hvar.trans (hscalar (fun i => g i ^ 2))).trans hedge
  calc
    _ ≤ 𝔼 i, 𝔼 j, 2 * (g i ^ 2 + g j ^ 2) := by
      refine expect_le_expect fun i _ => expect_le_expect fun j _ => ?_
      exact ((sq_le_sq₀ dist_nonneg (add_nonneg (hg i) (hg j))).mpr
        (dist_triangle_left (f i) (f j) (f z))).trans add_sq_le
    _ = 4 * 𝔼 i, g i ^ 2 := by
      simp only [← mul_expect, expect_add_distrib, Fintype.expect_const]
      ring
    _ ≤ _ := by
      change _ ≤ 12 * K ^ 2 * 𝔼 p, d p ^ 2
      linarith only [hmean, hsecond]

/-- A first-moment bound for all placements into one pseudometric space implies a squared
bound for every placement into that space, with constant `12 * K ^ 2`. -/
theorem expect_dist_sq_le_of_forall_expect_dist_le {V D X : Type*} [Fintype V] [Fintype D]
    [Nonempty V] [Nonempty D] [PseudoMetricSpace X] (G : RotationMap V D) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ f : V → X, (𝔼 i, 𝔼 j, dist (f i) (f j)) ≤
      K * 𝔼 p : V × D, dist (f p.1) (f (G.rot p).1)) (f : V → X) :
    (𝔼 i, 𝔼 j, dist (f i) (f j) ^ 2) ≤
      12 * K ^ 2 * 𝔼 p : V × D, dist (f p.1) (f (G.rot p).1) ^ 2 := by
  by_cases hzero : ∀ x y : X, dist x y = 0
  · simp [hzero]
  obtain ⟨x, y, hxy⟩ : ∃ x y : X, dist x y ≠ 0 := by simpa using hzero
  refine G.expect_dist_sq_le_of_expect_dist_le f hK (h f) fun u => ?_
  rw [← Fintype.expect_prod_type fun p : V × V => |u p.1 - u p.2|]
  exact Fintype.expect_abs_sub_le_of_forall_expect_dist_le Prod.fst Prod.snd
    Prod.fst (fun p => (G.rot p).1) (fun g => (Fintype.expect_prod_type _).le.trans (h g))
    (lt_of_le_of_ne dist_nonneg (Ne.symm hxy)) u

end RotationMap
end Cslib
