/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Lazy
public import CslibFrontier.Foundations.Combinatorics.Expander.Power
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# A regular multigraph for the average of several walk lengths

A label for `G.cesaroPowers t` chooses a time between `1` and `t` and a word of length `t` in
the labels of `G`. Unused letters duplicate the shorter walks, giving each length the same weight.
The degree is `t * |D| ^ t`. At any larger prescribed degree we use as many full copies of these
labels as fit, then fill the remainder with holding edges. At least half the resulting walk
follows a full copy. Applying this construction to the lazy graph gives
`exists_padded_lazy_cesaro`, a degree adjustment for the graph iteration in
[OpenAI2026HamiltonianPermanent], section “A logarithmic lower bound for the Poincaré constant”.
-/

public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V D H : Type*}

/-- Pick a graph uniformly, then pick a label uniformly from the common label set. -/
private def uniformUnion (G : H → RotationMap V D) : RotationMap V (H × D) where
  rot p := let r := (G p.2.1).rot (p.1, p.2.2)
           (r.1, p.2.1, r.2)
  rot_involutive := by
    rintro ⟨v, h, d⟩
    change (((G h).rot ((G h).rot (v, d))).1, h, ((G h).rot ((G h).rot (v, d))).2) = _
    rw [rot_rot]

private theorem walk_uniformUnion [Fintype H] [Fintype D] (G : H → RotationMap V D)
    (f : V → ℝ) (v : V) :
    (uniformUnion G).walk f v = 𝔼 h, (G h).walk f v :=
  Fintype.expect_prod_type _

private noncomputable def powerLabels [Fintype D] {t : ℕ} (h : Fin t) :
    ((Fin (t - (h.val + 1)) → D) × (Fin (h.val + 1) → D)) ≃ (Fin t → D) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ← pow_add]
    congr 1
    lia)

variable (G : RotationMap V D) [Fintype D]

/-- A rotation map realizing the average of the walk lengths one through `t`. Unused labels pad
each power to the same degree before taking their uniform union. -/
noncomputable def cesaroPowers (t : ℕ) : RotationMap V (Fin t × (Fin t → D)) :=
  uniformUnion fun h : Fin t => (uniformUnion fun _ : Fin (t - (h.val + 1)) → D =>
    G.pow (h.val + 1)).relabel (powerLabels h)

/-- The walk on `cesaroPowers t` is the average of the first `t` walk operators. -/
theorem walk_cesaroPowers [Nonempty D] (t : ℕ) (f : V → ℝ) (v : V) :
    (G.cesaroPowers t).walk f v = 𝔼 h : Fin t, (G.walk ^ (h.val + 1)) f v := by
  rw [cesaroPowers, walk_uniformUnion]
  apply expect_congr rfl
  intro h _
  rw [walk_relabel, walk_uniformUnion, Fintype.expect_const, walk_pow]

variable [Nonempty D]

/-- Enlarge the label set to any prescribed cardinality at least the original degree. Duplicate
the entire label set equally often and fill the remaining positions with holding labels. -/
theorem exists_regular_padding {T : Type*} [Fintype T] (hcard : Fintype.card D ≤ Fintype.card T) :
    ∃ R : RotationMap V T, ∀ (f : V → ℝ), (∀ v, 0 ≤ f v) → ∀ v, G.walk f v ≤ 2 * R.walk f v := by
  classical
  let n := Fintype.card T
  let d := Fintype.card D
  let q := n / d
  let r := n % d
  have hd : 0 < d := Fintype.card_pos
  have hq : 0 < q := Nat.div_pos hcard hd
  let : NeZero q := ⟨hq.ne'⟩
  have hdiv : q * d + r = n := Nat.div_add_mod' n d
  have hhalf : n ≤ 2 * (q * d) := by
    have hr : r < d := Nat.mod_lt n hd
    have hle : d ≤ q * d := Nat.le_mul_of_pos_left d hq
    lia
  let eqv : (Fin q × D) ⊕ Fin r ≃ T := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using hdiv)
  refine ⟨((uniformUnion fun _ : Fin q => G).addLoops (Fin r)).relabel eqv, fun f hf v => ?_⟩
  rw [walk_relabel, walk_addLoops_apply, walk_uniformUnion, Fintype.expect_const]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have he : 0 ≤ G.walk f v := expect_nonneg fun i _ => hf _
  have hsum : (q : ℝ) * d + r = n := by exact_mod_cast hdiv
  have hn : (0 : ℝ) < n := by exact_mod_cast hd.trans_le hcard
  have hh : (n : ℝ) ≤ 2 * (q * d : ℝ) := by exact_mod_cast hhalf
  rw [← mul_div_assoc]
  change _ ≤ 2 * ((q * d : ℝ) * G.walk f v + r * f v) / ((q : ℝ) * d + r)
  rw [hsum]
  apply (le_div_iff₀ hn).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hh he, mul_nonneg (Nat.cast_nonneg r) (hf v)]

/-- An exact-width rotation map dominates half the mean of the first `t` lazy powers on every
nonnegative test. It depends only on the predecessor graph, the time, and the prescribed labels. -/
theorem exists_padded_lazy_cesaro {T : Type*} [Fintype T] {t : ℕ} (ht : 0 < t)
    (hN : (4 * Fintype.card D) ^ t ≤ Fintype.card T) :
    ∃ R : RotationMap V T, ∀ (f : V → ℝ), (∀ v, 0 ≤ f v) → ∀ v,
      (𝔼 h : Fin t, (G.lazy.walk ^ (h.val + 1)) f v) ≤ 2 * R.walk f v := by
  let : NeZero t := ⟨ht.ne'⟩
  have hdeg : Fintype.card (Fin t × (Fin t → D ⊕ D)) ≤ Fintype.card T := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_sum, ← two_mul]
    refine le_trans (Nat.mul_le_mul_right _ (Nat.lt_two_pow_self (n := t)).le) ?_
    rw [← mul_pow]
    convert! hN using 2
    ring
  obtain ⟨R, hR⟩ := (G.lazy.cesaroPowers t).exists_regular_padding hdeg
  exact ⟨R, fun f hf v => (G.lazy.walk_cesaroPowers t f v).symm.trans_le (hR f hf v)⟩

end Cslib.RotationMap
