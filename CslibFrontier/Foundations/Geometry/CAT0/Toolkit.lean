/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.CAT0.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# CAT(0) spaces: points on geodesics, barycenters, projections and flat rectangles

The elementary facts about a CAT(0) space `Y` that follow from the inequality of Bruhat and Tits
alone, in the form of Lemma "toolkit" of *VP ≠ VNP over every field* [AnthropicVPVNP2026]
(module `Paper.Toolkit`); for the CN inequality see [BridsonHaefliger1999, II.1.9(1)(c)].

All existence statements come from one minimization principle
(`Cslib.CAT0.exists_add_mul_dist_sq_le`): a continuous nonnegative function that is uniformly
convex along midpoints has a minimizer on every nonempty closed midpoint-convex set, with
quadratic growth away from it.

## Main results

* `Cslib.CAT0.exists_isPointAt`, `Cslib.CAT0.existsUnique_dist_eq`: for `t ∈ [0, 1]`, exactly one
  point has distances `t|xv|` and `(1 − t)|xv|` from `x` and `v`, and it satisfies the inequality
  of the point at fraction `t` (part (a)); `Cslib.CAT0.apply_eq_of_dist_eq`: so an isometry that
  fixes `x` and `v` fixes it.
* `Cslib.CAT0.dist_sq_add_dist_sq_le`: `|xv|² + |yu|² ≤ |xu|² + |yv|² + 2|xy||uv|`, the
  quadrilateral inequality; `Cslib.CAT0.dist_sq_add_dist_sq_le_sides` and
  `Cslib.CAT0.sides_eq_of_dist_sq_add_dist_sq_eq` for the diagonals of a quadrangle (part (b)).
* `Cslib.CAT0.exists_isBarycenter`, `Cslib.CAT0.IsBarycenter.sum_mul_dist_le`: weighted points
  have barycenters, and barycenters depend `1`-Lipschitz on the points (part (c));
  `Cslib.CAT0.isBarycenter_one_iff` identifies the barycenter with the minimizer of `∑ |yxᵢ|²`.
* `Cslib.CAT0.exists_proj`: nearest points on nonempty closed convex sets (part (d)).
* `Cslib.CompleteCAT0Space.piLp` (in `Basic`): finite `ℓ²` products (part (e)).
* `Cslib.CAT0.dist_sq_of_flat`: distances in flat rectangles (part (f)).

## References

* [M. R. Bridson and A. Haefliger, *Metric Spaces of Non-Positive Curvature*][BridsonHaefliger1999]
-/

public section

open Filter Topology

namespace Cslib.CAT0

variable {Y : Type*} [MetricSpace Y] [CompleteCAT0Space Y]

/-- The minimization principle. Let `C` be nonempty, closed and closed under midpoints, and let
`Θ ≥ 0` be continuous with `Θ(m) ≤ ½Θ(x) + ½Θ(v) − (c/4)|xv|²` for the midpoint `m` of
`x, v ∈ C`, where `c > 0`. Then some `b ∈ C` has `Θ(b) + c|yb|² ≤ Θ(y)` for every `y ∈ C`.
Minimizing sequences are Cauchy by the convexity; their limit is compared with the midpoints
towards `y`. -/
theorem exists_add_mul_dist_sq_le (C : Set Y) (hC : IsClosed C) (hne : C.Nonempty)
    (hmem : ∀ x ∈ C, ∀ v ∈ C, mid x v ∈ C) (Θ : Y → ℝ) (hΘ : Continuous Θ)
    (hΘ0 : ∀ x, 0 ≤ Θ x) {c : ℝ} (hc : 0 < c)
    (hconv : ∀ x ∈ C, ∀ v ∈ C, Θ (mid x v) ≤ (Θ x + Θ v) / 2 - c / 4 * dist x v ^ 2) :
    ∃ b ∈ C, ∀ y ∈ C, Θ b + c * dist y b ^ 2 ≤ Θ y := by
  set I := sInf (Θ '' C)
  have hbdd : BddBelow (Θ '' C) := ⟨0, by rintro _ ⟨x, -, rfl⟩; exact hΘ0 x⟩
  have hle : ∀ y ∈ C, I ≤ Θ y := fun y hy => csInf_le hbdd ⟨y, hy, rfl⟩
  have hseq : ∀ n : ℕ, ∃ y ∈ C, Θ y < I + 1 / ((n : ℝ) + 1) := fun n => by
    obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := Real.lt_sInf_add_pos (hne.image Θ) Nat.one_div_pos_of_nat
    exact ⟨y, hy, h⟩
  choose u huC hu using hseq
  have hcauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < c / 4 * ε ^ 2 by positivity)
    refine ⟨N, fun m hm n hn => lt_of_pow_lt_pow_left₀ 2 hε.le <|
      lt_of_mul_lt_mul_left (a := c / 4) ?_ (by positivity)⟩
    linarith [hconv _ (huC m) _ (huC n), hle _ (hmem _ (huC m) _ (huC n)),
      hu m, hu n, Nat.one_div_le_one_div (α := ℝ) hm, Nat.one_div_le_one_div (α := ℝ) hn]
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hbC : b ∈ C := hC.mem_of_tendsto hb (Eventually.of_forall huC)
  have hΘb : Θ b ≤ I := le_of_tendsto_of_tendsto' ((hΘ.tendsto b).comp hb)
    (by simpa only [add_zero] using
      (tendsto_const_nhds (x := I)).add tendsto_one_div_add_atTop_nhds_zero_nat)
    fun n => (hu n).le
  refine ⟨b, hbC, ?_⟩
  -- `Θ b + c (1 − 2⁻ᵏ) |yb|² ≤ Θ y`, by induction on `k` along the midpoints of `b` and `y`
  have key : ∀ k : ℕ, ∀ y ∈ C, Θ b + c * (1 - (1 / 2) ^ k) * dist y b ^ 2 ≤ Θ y := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hΘb.trans (hle y hy)
    | succ k ih =>
      intro y hy
      have h1 := ih _ (hmem b hbC y hy)
      rw [dist_comm _ b, dist_mid_left] at h1
      rw [dist_comm y b, pow_succ]
      nlinarith [hconv b hbC y hy]
  intro y hy
  have ht : Tendsto (fun k : ℕ => Θ b + c * (1 - (1 / 2 : ℝ) ^ k) * dist y b ^ 2)
      atTop (𝓝 (Θ b + c * (1 - 0) * dist y b ^ 2)) :=
    tendsto_const_nhds.add (((tendsto_const_nhds.sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))).const_mul c).mul_const _)
  rw [sub_zero, mul_one] at ht
  exact le_of_tendsto' ht fun k => key k y hy

/-! ### Barycenters -/

/-- Points with nonnegative weights have a barycenter: the minimizer of `y ↦ ∑ wᵢ|yxᵢ|²`. -/
theorem exists_isBarycenter {ι : Type*} [Fintype ι] [Nonempty Y] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (x : ι → Y) : ∃ b, IsBarycenter w x b := by
  rcases (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hw i).eq_or_lt with h0 | h0
  · have h : ∀ i, w i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hw i).1 h0.symm i (Finset.mem_univ i)
    exact ⟨Classical.arbitrary Y, fun y => by simp [h]⟩
  obtain ⟨b, -, hb⟩ := exists_add_mul_dist_sq_le Set.univ isClosed_univ Set.univ_nonempty
    (fun _ _ _ _ => Set.mem_univ _) (fun y => ∑ i, w i * dist y (x i) ^ 2) (by fun_prop)
    (fun y => Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)) h0 fun y _ y' _ => by
      calc ∑ i, w i * dist (mid y y') (x i) ^ 2
          ≤ ∑ i, (w i * dist y (x i) ^ 2 / 2 + w i * dist y' (x i) ^ 2 / 2
            - w i * (dist y y' ^ 2 / 4)) := by
            gcongr with i
            have h1 := mul_le_mul_of_nonneg_left (dist_mid_sq_le y y' (x i)) (hw i)
            rw [dist_comm (x i), dist_comm (x i), dist_comm (x i)] at h1
            linarith
        _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
            ← Finset.sum_div, ← Finset.sum_mul]
          ring
  exact ⟨b, fun y => by linarith [hb y (Set.mem_univ y)]⟩

/-! ### Points on geodesics (part (a)) -/

omit [CompleteCAT0Space Y] in
/-- `t(1 − t)|xv|² ≤ (1 − t)|qx|² + t|qv|²` for every `q` and `t ∈ [0, 1]`: the triangle
inequality, squared and weighted. -/
private theorem mul_one_sub_mul_dist_sq_le (x v q : Y) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t * (1 - t) * dist x v ^ 2 ≤ (1 - t) * dist q x ^ 2 + t * dist q v ^ 2 := by
  have h2 := dist_triangle x q v
  rw [dist_comm x q] at h2
  have h3 : t * (1 - t) * dist x v ^ 2 ≤ t * (1 - t) * (dist q x + dist q v) ^ 2 := by
    have : 0 ≤ t * (1 - t) := mul_nonneg h0 (by linarith)
    gcongr
  linarith [sq_nonneg ((1 - t) * dist q x - t * dist q v)]

/-- For `t ∈ [0, 1]` some point satisfies the inequality of the point at fraction `t`: the
barycenter of `x` and `v` with the weights `1 − t` and `t`. -/
theorem exists_isPointAt (x v : Y) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ∃ b, IsPointAt x v t b := by
  have : Nonempty Y := ⟨x⟩
  obtain ⟨b, hb⟩ := exists_isBarycenter (ι := Bool) (fun i => cond i t (1 - t))
    (by intro i; cases i <;> simp <;> linarith) (fun i => cond i v x)
  refine ⟨b, fun z => ?_⟩
  have h := hb z
  simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false] at h
  linarith [mul_one_sub_mul_dist_sq_le x v b h0 h1]

/-- **Part (a).** For `t ∈ [0, 1]` exactly one point has distances `t|xv|` and `(1 − t)|xv|`
from `x` and `v`. By `isPointAt_of_dist` it satisfies the inequality of the point at
fraction `t`. -/
theorem existsUnique_dist_eq (x v : Y) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ∃! γ : Y, dist x γ = t * dist x v ∧ dist γ v = (1 - t) * dist x v := by
  obtain ⟨b, hb⟩ := exists_isPointAt x v h0 h1
  exact ⟨b, ⟨hb.dist_left h0 h1, hb.dist_right h0 h1⟩, fun _ h => hb.eq_of_dist h.1 h.2⟩

/-- A point with the distances of the point at fraction `t` satisfies its inequality. -/
theorem isPointAt_of_dist {x v c : Y} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (e1 : dist x c = t * dist x v) (e2 : dist c v = (1 - t) * dist x v) : IsPointAt x v t c := by
  obtain ⟨b, hb⟩ := exists_isPointAt x v h0 h1
  rwa [hb.eq_of_dist e1 e2]

/-- An isometry that fixes `x` and `v` fixes the point with the distances of the point at
fraction `t ∈ [0, 1]` between them: by part (a) it is the only such point. -/
theorem apply_eq_of_dist_eq {f : Y → Y} (hf : Isometry f) {x v q : Y} (hx : f x = x)
    (hv : f v = v) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (e1 : dist x q = t * dist x v)
    (e2 : dist q v = (1 - t) * dist x v) : f q = q :=
  (existsUnique_dist_eq x v h0 h1).unique ⟨by rw [← e1, ← hf.dist_eq x q, hx],
    by rw [← e2, ← hf.dist_eq q v, hv]⟩ ⟨e1, e2⟩

/-! ### The quadrilateral inequality (part (b)) -/

/-- `S ≤ 2ab` for `a, b ≥ 0` when `S ≤ τb² + a²/τ` for every `τ > 0`: the inequality of the
arithmetic and geometric means, used to choose the parameter `τ`. -/
private theorem le_two_mul_of_forall {S a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ τ : ℝ, 0 < τ → S ≤ τ * b ^ 2 + a ^ 2 / τ) : S ≤ 2 * a * b := by
  rcases ha.eq_or_lt with rfl | ha
  · -- `S ≤ τb²` for every `τ > 0`
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have h1 := h (ε / (b ^ 2 + 1)) (by positivity)
    have h2 : ε / (b ^ 2 + 1) * b ^ 2 < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      linarith
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero] at h1
    linarith
  rcases hb.eq_or_lt with rfl | hb
  · -- `S ≤ a²/τ` for every `τ > 0`
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have h1 := h ((a ^ 2 + 1) / ε) (by positivity)
    have h2 : a ^ 2 / ((a ^ 2 + 1) / ε) < ε := by
      rw [div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
      linarith
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
      at h1
    linarith
  · have h1 := h (a / b) (by positivity)
    have h2 : a / b * b ^ 2 + a ^ 2 / (a / b) = 2 * a * b := by
      field_simp
      ring
    linarith

/-- The first step of part (b): for the point `q` at `s` on `[p, p']`, insert the inequality of
part (a) twice into `t(1 − t)|xv|² ≤ (1 − t)|xq|² + t|qv|²`. -/
private theorem quadrilateral_aux (x v p p' : Y) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (1 - t) * dist x v ^ 2 + s * (1 - s) * dist p p' ^ 2 ≤
      (1 - t) * (1 - s) * dist x p ^ 2 + (1 - t) * s * dist x p' ^ 2
        + t * (1 - s) * dist v p ^ 2 + t * s * dist v p' ^ 2 := by
  obtain ⟨q, hq⟩ := exists_isPointAt p p' hs0 hs1
  have h1 := mul_le_mul_of_nonneg_left (hq x) (show 0 ≤ 1 - t by linarith)
  have h2 := mul_le_mul_of_nonneg_left (hq v) ht0
  have h3 := mul_one_sub_mul_dist_sq_le x v q ht0 ht1
  rw [dist_comm q x, dist_comm q v] at h3
  linarith

/-- **Part (b), the quadrilateral inequality.**
`|xv|² + |yu|² ≤ |xu|² + |yv|² + 2|xy||uv|`. The proof applies `quadrilateral_aux` with
`s = t = τ/(1 + τ)` and lets `le_two_mul_of_forall` choose `τ`. -/
theorem dist_sq_add_dist_sq_le (x v y u : Y) :
    dist x v ^ 2 + dist y u ^ 2 ≤ dist x u ^ 2 + dist y v ^ 2 + 2 * dist x y * dist u v := by
  suffices dist x v ^ 2 + dist y u ^ 2 - dist x u ^ 2 - dist y v ^ 2 ≤ 2 * dist x y * dist u v by
    linarith
  refine le_two_mul_of_forall dist_nonneg dist_nonneg fun τ hτ => ?_
  have hs1 : τ / (1 + τ) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have h := quadrilateral_aux x v y u (by positivity) hs1 (by positivity) hs1
  rw [show 1 - τ / (1 + τ) = 1 / (1 + τ) by field_simp; ring] at h
  have h2 := mul_le_mul_of_nonneg_left h (show 0 ≤ (1 + τ) ^ 2 / τ by positivity)
  rw [dist_comm v y, dist_comm v u] at h2
  linarith [show (1 + τ) ^ 2 / τ * (τ / (1 + τ) * (1 / (1 + τ)) * dist x v ^ 2 +
      τ / (1 + τ) * (1 / (1 + τ)) * dist y u ^ 2) = dist x v ^ 2 + dist y u ^ 2 by field_simp,
    show (1 + τ) ^ 2 / τ * (1 / (1 + τ) * (1 / (1 + τ)) * dist x y ^ 2 +
      1 / (1 + τ) * (τ / (1 + τ)) * dist x u ^ 2 + τ / (1 + τ) * (1 / (1 + τ)) * dist y v ^ 2 +
      τ / (1 + τ) * (τ / (1 + τ)) * dist u v ^ 2) =
      dist x y ^ 2 / τ + dist x u ^ 2 + dist y v ^ 2 + τ * dist u v ^ 2 by field_simp]

/-- **Part (b).** The squared diagonals of a quadrangle add up to at most its squared sides. -/
theorem dist_sq_add_dist_sq_le_sides (x v y u : Y) :
    dist x v ^ 2 + dist y u ^ 2 ≤ dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2 := by
  have h := dist_sq_add_dist_sq_le x v y u
  rw [dist_comm u v] at h
  linarith [sq_nonneg (dist x y - dist v u)]

/-- **Part (b).** If the squared diagonals of a quadrangle add up to its squared sides,
opposite sides are equal. -/
theorem sides_eq_of_dist_sq_add_dist_sq_eq {x v y u : Y}
    (he : dist x v ^ 2 + dist y u ^ 2 =
      dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2) :
    dist x y = dist v u ∧ dist y v = dist x u := by
  have h1 := dist_sq_add_dist_sq_le x v y u
  have h2 := dist_sq_add_dist_sq_le x v u y
  rw [dist_comm u v] at h1
  rw [dist_comm u y, dist_comm u v] at h2
  constructor
  · linarith [(sq_nonpos_iff (dist x y - dist v u)).1 (by linarith)]
  · linarith [(sq_nonpos_iff (dist y v - dist x u)).1 (by linarith)]

/-! ### Barycenters (part (c)) -/

/-- **Part (c).** Barycenters depend `1`-Lipschitz on the points:
`(∑ wᵢ)|bb'| ≤ ∑ wᵢ|xᵢx'ᵢ|`. Add the variance inequalities of `b` at `b'` and of `b'` at `b`, and
apply the quadrilateral inequality to every `b, b', xᵢ, x'ᵢ`. -/
theorem IsBarycenter.sum_mul_dist_le {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {x x' : ι → Y} {b b' : Y} (h : IsBarycenter w x b) (h' : IsBarycenter w x' b') :
    (∑ i, w i) * dist b b' ≤ ∑ i, w i * dist (x i) (x' i) := by
  rcases (dist_nonneg (x := b) (y := b')).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) dist_nonneg
  have h1 := h b'
  have h2 := h' b
  rw [dist_comm b' b] at h1
  have h3 : ∀ i, w i * dist b' (x i) ^ 2 + w i * dist b (x' i) ^ 2 ≤
      w i * dist b (x i) ^ 2 + w i * dist b' (x' i) ^ 2
        + 2 * dist b b' * (w i * dist (x i) (x' i)) := fun i => by
    have h4 := mul_le_mul_of_nonneg_left (dist_sq_add_dist_sq_le b' (x i) b (x' i)) (hw i)
    rw [dist_comm (x' i) (x i), dist_comm b' b] at h4
    linarith
  have h5 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h3 i
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h5
  refine le_of_mul_le_mul_left (a := dist b b') ?_ h0
  linarith

/-- **Part (c).** For `n ≥ 1` points, the barycenter with unit weights is the unique minimizer
of `y ↦ ∑ |yxᵢ|²`. -/
theorem isBarycenter_one_iff {n : ℕ} (hn : 0 < n) (x : Fin n → Y) (b : Y) :
    IsBarycenter (fun _ => 1) x b ↔ ∀ y, ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : Nonempty Y := ⟨x ⟨0, hn⟩⟩
  simp only [IsBarycenter, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  refine ⟨fun h y => by linarith [h y, mul_nonneg hn'.le (sq_nonneg (dist y b))], fun h => ?_⟩
  obtain ⟨b₀, h₀⟩ := exists_isBarycenter (fun _ : Fin n => (1 : ℝ)) (fun _ => zero_le_one) x
  simp only [IsBarycenter, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h₀
  have hb : b = b₀ := dist_eq_zero.1 <| (sq_nonpos_iff _).1 <|
    nonpos_of_mul_nonpos_right (by linarith [h₀ b, h b₀]) hn'
  exact hb ▸ h₀

/-! ### Projections (part (d)) -/

/-- **Part (d).** A nonempty closed convex set `F` has a nearest point `P` to every `y`, with
`|yP|² + |Pq|² ≤ |yq|²` for `q ∈ F`. Here a set is convex if it contains every point with the
distances of a midpoint of two of its points. -/
theorem exists_proj (F : Set Y) (hF : IsClosed F) (hne : F.Nonempty)
    (hconv : ∀ x ∈ F, ∀ v ∈ F, ∀ m, dist x m = dist x v / 2 → dist m v = dist x v / 2 → m ∈ F)
    (y : Y) :
    ∃ P ∈ F, (∀ q ∈ F, dist y P ≤ dist y q) ∧
      ∀ q ∈ F, dist y P ^ 2 + dist P q ^ 2 ≤ dist y q ^ 2 := by
  obtain ⟨P, hP, h⟩ := exists_add_mul_dist_sq_le F hF hne
    (fun x hx v hv => hconv x hx v hv _ (dist_mid_left x v) (dist_mid_right x v))
    (fun q => dist y q ^ 2) (by fun_prop) (fun _ => sq_nonneg _) one_pos
    (fun x _ v _ => by linarith [dist_mid_sq_le x v y])
  have h' : ∀ q ∈ F, dist y P ^ 2 + dist P q ^ 2 ≤ dist y q ^ 2 := fun q hq => by
    have := h q hq
    rw [dist_comm q P] at this
    linarith
  exact ⟨P, hP, fun q hq => (pow_le_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero).1
    (by linarith [h' q hq, sq_nonneg (dist P q)]), h'⟩

/-! ### Flat rectangles (part (f))

The letters are those of the paper: `|xy| = |uv| = δ`, `|xu| = |yv| = h`, `a` is the point at `s`
on `[x, u]` and `b` the point at `t` on `[y, v]`. The form
`Φ(p, p'; r, r') = |pr'|² + |p'r|² − |pr|² − |p'r'|²` is at most `2|pp'||rr'|` by the quadrilateral
inequality, and it is additive when `[p, p']` and `[r, r']` are cut; so equality for the whole
rectangle is inherited by the parts. -/

section flat

variable {x u v y a b : Y} {h δ s t : ℝ}

/-- The four bounds of the form add up to `2h²`, which is at most `Φ(x, u; y, v)` when the
diagonals have squared lengths adding up to at least `2h² + 2δ²`; so all four are equalities.
The first one says `|xb|² + |ay|² − δ² − |ab|² = 2sth²`. -/
private theorem flat_parts (hp : dist x u = h) (hp' : dist y v = h) (hq : dist u v = δ)
    (hq' : dist x y = δ) (hd : 2 * h ^ 2 + 2 * δ ^ 2 ≤ dist x v ^ 2 + dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : IsPointAt x u s a) (hb : IsPointAt y v t b) :
    dist x b ^ 2 + dist a y ^ 2 - δ ^ 2 - dist a b ^ 2 = 2 * s * t * h ^ 2 := by
  have f1 := dist_sq_add_dist_sq_le x b a y
  have f2 := dist_sq_add_dist_sq_le x v a b
  have f3 := dist_sq_add_dist_sq_le a b u y
  have f4 := dist_sq_add_dist_sq_le a v u b
  simp only [ha.dist_left hs0 hs1, ha.dist_right hs0 hs1, hb.dist_left ht0 ht1,
    hb.dist_right ht0 ht1, hp, hp', hq, hq'] at f1 f2 f3 f4
  linarith

/-- The case `s = t`: then `|ab| = δ`, and `|xb|²`, `|ay|²` take the largest values that the
inequality of the point at fraction `s` allows. -/
private theorem flat_same (hp : dist x u = h) (hp' : dist y v = h) (hq : dist u v = δ)
    (hq' : dist x y = δ) (hd : 2 * h ^ 2 + 2 * δ ^ 2 ≤ dist x v ^ 2 + dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha : IsPointAt x u s a) (hb : IsPointAt y v s b) :
    dist x b ^ 2 = (1 - s) * δ ^ 2 + s * dist x v ^ 2 - s * (1 - s) * h ^ 2 ∧
      dist a y ^ 2 = (1 - s) * δ ^ 2 + s * dist u y ^ 2 - s * (1 - s) * h ^ 2 := by
  have h1 := flat_parts hp hp' hq hq' hd hs0 hs1 hs0 hs1 ha hb
  have h2 := dist_sq_add_dist_sq_le x b y a
  have h5 := hb x
  have h6 := ha y
  have h7 := dist_sq_add_dist_sq_le_sides x v u y
  simp only [ha.dist_left hs0 hs1, hb.dist_left hs0 hs1, hp, hp', hq, hq',
    dist_comm y a, dist_comm y x, dist_comm y u, dist_comm v y] at h2 h5 h6 h7
  have h4 : dist a b = δ := by linarith [(sq_nonpos_iff (dist a b - δ)).1 (by linarith)]
  rw [h4] at h1
  have h9 : s * dist x v ^ 2 + s * dist u y ^ 2 = s * (2 * h ^ 2 + 2 * δ ^ 2) := by
    rw [← mul_add, show dist x v ^ 2 + dist u y ^ 2 = 2 * h ^ 2 + 2 * δ ^ 2 by linarith]
  constructor <;> linarith

/-- **Part (f), flat rectangles**, with `a` and `b` given by the inequality of the point at
fraction `s`, `t`, and lower bounds for the diagonals: `|ab|² = δ² + (s − t)²h²`. -/
theorem dist_sq_of_flat_of_isPointAt (hp : dist x u = h) (hp' : dist y v = h)
    (hq : dist u v = δ) (hq' : dist x y = δ)
    (hd : h ^ 2 + δ ^ 2 ≤ dist x v ^ 2) (hd' : h ^ 2 + δ ^ 2 ≤ dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : IsPointAt x u s a) (hb : IsPointAt y v t b) :
    dist a b ^ 2 = δ ^ 2 + (s - t) ^ 2 * h ^ 2 := by
  have hd2 : 2 * h ^ 2 + 2 * δ ^ 2 ≤ dist x v ^ 2 + dist u y ^ 2 := by linarith
  obtain ⟨a', ha'⟩ := exists_isPointAt x u ht0 ht1
  obtain ⟨b', hb'⟩ := exists_isPointAt y v hs0 hs1
  have h1 := flat_parts hp hp' hq hq' hd2 hs0 hs1 ht0 ht1 ha hb
  have h7 := dist_sq_add_dist_sq_le_sides x v u y
  rw [hp, hq, hq', dist_comm v y, hp'] at h7
  rw [(flat_same hp hp' hq hq' hd2 ht0 ht1 ha' hb).1,
    (flat_same hp hp' hq hq' hd2 hs0 hs1 ha hb').2,
    show dist x v ^ 2 = h ^ 2 + δ ^ 2 by linarith,
    show dist u y ^ 2 = h ^ 2 + δ ^ 2 by linarith] at h1
  linarith

/-- **Part (f), flat rectangles.** If `|xy| = |uv| = δ`, `|xu| = |yv| = h`, both diagonals have
squared length `δ² + h²`, and `a ∈ [x, u]`, `b ∈ [y, v]` have `|xa| = s h`, `|yb| = t h`, then
`|ab|² = δ² + h²(s − t)²`. -/
theorem dist_sq_of_flat (hxy : dist x y = δ) (huv : dist u v = δ) (hxu : dist x u = h)
    (hyv : dist y v = h) (d1 : dist x v ^ 2 = δ ^ 2 + h ^ 2) (d2 : dist y u ^ 2 = δ ^ 2 + h ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (a1 : dist x a = s * dist x u) (a2 : dist a u = (1 - s) * dist x u)
    (b1 : dist y b = t * dist y v) (b2 : dist b v = (1 - t) * dist y v) :
    dist a b ^ 2 = δ ^ 2 + h ^ 2 * (s - t) ^ 2 := by
  have := dist_sq_of_flat_of_isPointAt hxu hyv huv hxy (by linarith)
    (by rw [dist_comm u y]; linarith) hs0 hs1 ht0 ht1 (isPointAt_of_dist hs0 hs1 a1 a2)
    (isPointAt_of_dist ht0 ht1 b1 b2)
  linarith

end flat

end Cslib.CAT0
