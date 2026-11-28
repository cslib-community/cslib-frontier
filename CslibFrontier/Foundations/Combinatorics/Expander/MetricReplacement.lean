/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Replacement
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# A metric Poincaré bound for balanced replacement

Replace each vertex of a graph by a copy of its label graph. Within each copy, choose a vertex
whose mean squared distance to the others is at most their all-pairs mean. Going through these
representatives compares distances in the replacement graph to the two original bounds.

This is the replacement estimate in the logarithmic Poincaré obstruction of
[OpenAI2026HamiltonianPermanent]. Selecting representatives by averaging works in any
pseudometric space.
-/

public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

/-- Every placement of the vertices in `X` has independent-pair mean squared distance at most
`b` times its mean squared edge length. Loops and parallel darts are allowed. -/
@[expose] def HasPoincareBound {V D : Type*} [Fintype V] [Fintype D] (G : RotationMap V D)
    (X : Type*) [PseudoMetricSpace X] (b : ℝ) : Prop :=
  ∀ f : V → X, (𝔼 i, 𝔼 j, dist (f i) (f j) ^ 2) ≤
    b * 𝔼 p : V × D, dist (f p.1) (f (G.rot p).1) ^ 2

private theorem dist_sq_le_three_steps {X : Type*} [PseudoMetricSpace X] (x y z t : X) :
    dist x t ^ 2 ≤ 3 * (dist x y ^ 2 + dist y z ^ 2 + dist z t ^ 2) := by
  have h := ((sq_le_sq₀ dist_nonneg (by positivity)).mpr (dist_triangle4 x y z t))
  nlinarith only [h, sq_nonneg (dist x y - dist y z), sq_nonneg (dist y z - dist z t),
    sq_nonneg (dist x y - dist z t)]

private theorem expect_sum_self {D : Type*} [Fintype D] [Nonempty D] (f : D ⊕ D → ℝ) :
    2 * (𝔼 d, f d) = (𝔼 d, f (.inl d)) + 𝔼 d, f (.inr d) := by
  have hd : (Fintype.card D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card, Fintype.sum_sum_type, Fintype.card_sum, Nat.cast_add]
  field_simp
  ring

/-- Squared-distance comparisons with constants `a` and `b` on the outer and inner graphs
give a comparison on the balanced replacement product. The bound holds for the same target
pseudometric space. -/
theorem expect_dist_sq_balancedReplacement {V D E X : Type*} [Fintype V] [Fintype D] [Fintype E]
    [Nonempty V] [Nonempty D] [Nonempty E] [PseudoMetricSpace X]
    (G : RotationMap V D) (H : RotationMap D E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hG : G.HasPoincareBound X a) (hH : H.HasPoincareBound X b) (f : V × D → X) :
    (𝔼 p, 𝔼 q, dist (f p) (f q) ^ 2) ≤ 36 * (1 + a) * (1 + b) *
      𝔼 p : (V × D) × (E ⊕ E), dist (f p.1) (f ((G.balancedReplacement H).rot p).1) ^ 2 := by
  let inside (u : V) := 𝔼 p : D × E, dist (f (u, p.1)) (f (u, (H.rot p).1)) ^ 2
  let matching := 𝔼 p : V × D, dist (f p) (f (G.rot p)) ^ 2
  have ex (u : V) : ∃ d : D, (𝔼 k, dist (f (u, d)) (f (u, k)) ^ 2) ≤ b * inside u := by
    obtain ⟨d, _, hd⟩ := exists_le_of_expect_le univ_nonempty (hH (fun k => f (u, k)))
    exact ⟨d, hd⟩
  choose pick hpick using ex
  let z (u : V) := f (u, pick u)
  let err (p : V × D) := dist (f p) (z p.1) ^ 2
  have herr : (𝔼 p, err p) ≤ b * 𝔼 u, inside u := by
    rw [Fintype.expect_prod_type, mul_expect]
    exact expect_le_expect fun u _ => by simpa [err, z, dist_comm] using hpick u
  have hedge : (𝔼 p : V × D, dist (z p.1) (z (G.rot p).1) ^ 2) ≤
      3 * (2 * (𝔼 p, err p) + matching) := by
    calc
      _ ≤ 𝔼 p : V × D, 3 * (err p + dist (f p) (f (G.rot p)) ^ 2 + err (G.rot p)) := by
        refine expect_le_expect fun p _ => ?_
        simpa only [err, dist_comm (z p.1) (f p)] using
          dist_sq_le_three_steps (z p.1) (f p) (f (G.rot p)) (z (G.rot p).1)
      _ = _ := by rw [← mul_expect, expect_add_distrib, expect_add_distrib, G.expect_comp_rot]; ring
  have hvar : (𝔼 p, 𝔼 q, dist (f p) (f q) ^ 2) ≤
      3 * (2 * (𝔼 p, err p) + (𝔼 u, 𝔼 v, dist (z u) (z v) ^ 2)) := by
    calc
      _ ≤ 𝔼 p : V × D, 𝔼 q : V × D,
          3 * (err p + dist (z p.1) (z q.1) ^ 2 + err q) := by
        refine expect_le_expect fun p _ => expect_le_expect fun q _ => ?_
        simpa only [err, dist_comm (z q.1) (f q)] using
          dist_sq_le_three_steps (f p) (z p.1) (z q.1) (f q)
      _ = _ := by
        have hbase : (𝔼 p : V × D, 𝔼 q : V × D, dist (z p.1) (z q.1) ^ 2) =
            𝔼 u, 𝔼 v, dist (z u) (z v) ^ 2 := by
          simp only [Fintype.expect_prod_type, Fintype.expect_const]
        simp only [← mul_expect, expect_add_distrib, Fintype.expect_const, hbase]
        ring
  have hsplit : 2 * (𝔼 p : (V × D) × (E ⊕ E),
      dist (f p.1) (f ((G.balancedReplacement H).rot p).1) ^ 2) =
      (𝔼 u, inside u) + matching := by
    rw [Fintype.expect_prod_type, mul_expect]
    simp_rw [expect_sum_self, rot_balancedReplacement_inl, rot_balancedReplacement_inr,
      Fintype.expect_const]
    rw [expect_add_distrib]
    congr 1
    simp only [inside, Fintype.expect_prod_type]
  have hi : 0 ≤ 𝔼 u, inside u := expect_nonneg fun _ _ => expect_nonneg fun _ _ => sq_nonneg _
  have hm : 0 ≤ matching := expect_nonneg fun _ _ => sq_nonneg _
  have hg := (hG z).trans (mul_le_mul_of_nonneg_left hedge ha)
  have hconst : 6 + 18 * a ≤ 18 * (1 + a) := by linarith
  have hinside := mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ 6 + 18 * a)
  have hfirst : (𝔼 p, 𝔼 q, dist (f p) (f q) ^ 2) ≤
      (6 + 18 * a) * b * (𝔼 u, inside u) + 9 * a * matching := by
    nlinarith only [hvar, hg, hinside]
  apply hfirst.trans
  rw [show 36 * (1 + a) * (1 + b) = (18 * (1 + a) * (1 + b)) * 2 by ring,
    mul_assoc (18 * (1 + a) * (1 + b)) 2, hsplit, mul_add]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ hi
    nlinarith only [mul_le_mul_of_nonneg_right hconst hb, ha]
  · exact mul_le_mul_of_nonneg_right (by nlinarith only [ha, hb, mul_nonneg ha hb]) hm

end Cslib.RotationMap
