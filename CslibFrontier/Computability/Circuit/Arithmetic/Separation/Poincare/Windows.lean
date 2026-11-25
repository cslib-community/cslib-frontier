/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Window
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Poincare.Lengths
import Mathlib.Algebra.Order.Chebyshev

/-!
# Windows of the unitriangular group and their fixed points

Section F.2 of [AnthropicVPVNP2026]. Let `U_h` act by isometries on a complete CAT(0) space `Z`
with contracting displacement lengths. The barycenter `P z` of the orbit of a finite group
(`Flag.IsoAct.P`) is the nearest fixed point (`Poincare.dist_P_le`). For the window
`[p, p + n)` (`Flag.IsoAct.W`), Lemma F.3 bounds `|z, P z|²` by `C(n) = κ_n² n` times the sum of
the squared displacements `δ_j(z)²` by the generators of the window
(`Poincare.dist_P_window_sq_le`, inequality (F.1)). For overlapping windows `[p, p + 2u)` and
`[p + u, p + 3u)` the sets of fixed points meet almost at a right angle (Lemmas F.4 and F.5,
`Poincare.dist_P_P_sq_le`).

## Main results

* `Poincare.dist_P_le`: the barycenter of an orbit is a nearest fixed point;
  `Poincare.P_eq_of_dist_add_dist`: the points between `P a` and `a` project to `P a`.
* `Poincare.fix_P_window`: the projection of a window keeps the fixed points of a disjoint one.
* `Poincare.dist_P_window_sq_le`: inequality (F.1).
* `Poincare.dist_P_P_sq_le_of_fix`: the angle at a common fixed point (Lemma F.5, its proof).
* `Poincare.dist_P_P_sq_le`: Lemma F.5.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Section F.2, inequality (F.1), Lemmas F.4 and F.5, pp. 39–40; module `Paper.Groups`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Poincare

open Finset Cslib.CAT0 Cslib.Circuits.Arithmetic.Separation.Flag
open Cslib.SLTower (U x)

/-! ### Projections to fixed points -/

section Fixed

variable {G Z : Type*} [Group G] [Fintype G] [MetricSpace Z] [CompleteCAT0Space Z]
  (A : IsoAct G Z)

/-- The barycenter of an orbit is the nearest-point projection to the fixed points:
`|z, P z|² + |P z, q|² ≤ |z q|²` for every fixed `q` (Lemma C.4(c) at `q`). -/
private theorem dist_P_sq_add_le {q : Z} (hq : A.Fix q) (z : Z) :
    dist z (A.P z) ^ 2 + dist (A.P z) q ^ 2 ≤ dist z q ^ 2 := by
  have h := A.P_spec z q
  have e : ∀ {y : Z}, A.Fix y → ∀ g, dist y (A g z) = dist y z := fun {y} hy g => by
    rw [← (A g).dist_eq y z, hy g]
  simp only [one_mul, e (A.P_fix z), e hq, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  rw [dist_comm q, dist_comm (A.P z) z, dist_comm q z] at h
  exact le_of_mul_le_mul_left (by linarith) hc

theorem dist_P_le {y : Z} (hy : A.Fix y) (z : Z) : dist z (A.P z) ≤ dist z y :=
  (pow_le_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero).1
    (by linarith [dist_P_sq_add_le A hy z, sq_nonneg (dist (A.P z) y)])

private theorem eq_P_of_dist_le {y : Z} (hy : A.Fix y) {z : Z} (h : dist z y ≤ dist z (A.P z)) :
    y = A.P z := by
  have h1 := dist_P_sq_add_le A hy z
  have h2 := pow_le_pow_left₀ dist_nonneg h 2
  exact (dist_eq_zero.1 ((sq_nonpos_iff _).1 (by linarith))).symm

/-- "By Lemma C.4(c) … `|z, P z|² ≤ E_g |z, g z|²`." -/
private theorem dist_P_sq_le (z : Z) :
    dist z (A.P z) ^ 2 ≤ (∑ g : G, dist z (A g z) ^ 2) / Fintype.card G := by
  have h := A.P_spec z z
  simp only [one_mul, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  rw [le_div_iff₀ (by exact_mod_cast Fintype.card_pos)]
  linarith [sum_nonneg fun g (_ : g ∈ univ) => sq_nonneg (dist (A.P z) (A g z))]

/-- A point `q` between `P a` and `a` has the projection `P a`. -/
theorem P_eq_of_dist_add_dist {a q : Z} (h : dist (A.P a) q + dist q a = dist (A.P a) a) :
    A.P q = A.P a :=
  eq_P_of_dist_le A (A.P_fix q) (z := a) (by
    linarith [dist_triangle a q (A.P q), dist_P_le A (A.P_fix a) q, dist_comm a q,
      dist_comm q (A.P a), dist_comm a (A.P a)])

omit [Fintype G] in
/-- A point at fraction `t` between two fixed points is fixed (Lemma C.4(a)). -/
private theorem fix_of_isPointAt {x v q : Z} {t : ℝ} (hx : A.Fix x) (hv : A.Fix v) (h0 : 0 ≤ t)
    (h1 : t ≤ 1) (hq : IsPointAt x v t q) : A.Fix q := fun g =>
  apply_eq_of_dist_eq (A g).isometry (hx g) (hv g) h0 h1 (hq.dist_left h0 h1) (hq.dist_right h0 h1)

end Fixed

variable {μ : ℕ} {s : ℝ} {h : ℕ} {Z : Type*} [MetricSpace Z] [CompleteCAT0Space Z]
  (A : IsoAct (U h) Z)

/-- "If two windows have no coordinate in common, then they commute, and therefore the
projection of one of them maps the fixed points of the other to fixed points of the other." -/
theorem fix_P_window {p n p' n' : ℕ} (hd : p + n ≤ p') (hp' : p' + n' ≤ h) {z : Z}
    (hz : (A.W p n).Fix z) : (A.W p n).Fix ((A.W p' n').P z) := fun a => by
  change A (wh h p n a) _ = _
  rw [(A.W p' n').P_comm (A (wh h p n a)) (A _).isometry (A _).surjective (fun b y => by
    change A _ (A (wh h p' n' b) y) = A (wh h p' n' b) (A _ y)
    rw [← IsoAct.act_mul, ← IsoAct.act_mul, IsoAct.wh_comm hd hp']) z]
  exact congrArg _ (hz a)

/-- The inequality (F.1): `|z, P z|² ≤ C(n) ∑_{p ≤ j < p + n − 1} δ_j(z)²` with
`C(n) = κ_n² n`, by Lemma F.3 for the window and the Cauchy–Schwarz inequality. -/
theorem dist_P_window_sq_le (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hA : ∀ z, Contr (A.len z) μ s)
    {n p : ℕ} (hp : p + n ≤ h) (z : Z) :
    dist z ((A.W p n).P z) ^ 2 ≤ kappa μ s n ^ 2 * n * ∑ j ∈ Ico p (p + n - 1), A.e j z ^ 2 := by
  have h1 := bd_kappa hμ hs n _ ((hA z).comp (wh h p n))
  have h2 : dist z ((A.W p n).P z) ^ 2 ≤ (Len.rms ((A.len z).comp (wh h p n))) ^ 2 :=
    (dist_P_sq_le (A.W p n) z).trans_eq (by
      simp only [Len.rms_sq, GroupSeminorm.comp_apply, IsoAct.len_apply, IsoAct.W,
        MonoidHom.comp_apply])
  have hS : Len.S ((A.len z).comp (wh h p n)) = ∑ j : Fin (n - 1), A.e (p + j) z := by
    refine sum_congr rfl fun j _ => ?_
    have hj : p + j.1 < h - 1 := by omega
    rw [GroupSeminorm.comp_apply, IsoAct.len_apply, wh_eq hp, win_x, IsoAct.e, dite_eq_left hj]
    rfl
  have h3 : (∑ j : Fin (n - 1), A.e (p + j) z) ^ 2 ≤ n * ∑ j ∈ Ico p (p + n - 1), A.e j z ^ 2 := by
    rw [sum_Ico_eq_sum_range, show p + n - 1 - p = n - 1 by omega,
      ← Fin.sum_univ_eq_sum_range (fun j => A.e (p + j) z ^ 2)]
    refine (sq_sum_le_card_mul_sum_sq (s := univ)
      (f := fun j : Fin (n - 1) => A.e (p + j) z)).trans ?_
    rw [card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n 1)
      (sum_nonneg fun _ _ => sq_nonneg _)
  rw [hS] at h1
  calc _ ≤ (Len.rms ((A.len z).comp (wh h p n))) ^ 2 := h2
    _ ≤ (kappa μ s n * ∑ j : Fin (n - 1), A.e (p + j) z) ^ 2 :=
      pow_le_pow_left₀ (Len.rms_nonneg _) h1 2
    _ ≤ kappa μ s n ^ 2 * (n * ∑ j ∈ Ico p (p + n - 1), A.e j z ^ 2) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    _ = _ := by ring

/-- By Lemma C.4(c) a generator moves the barycenter of `n` points by at most `1/n` times the sum
of what it moves the points. -/
private theorem mul_e_le {n : ℕ} {y : Fin n → Z} {b : Z} (hb : IsBarycenter (fun _ => 1) y b)
    (j : ℕ) : (n : ℝ) * A.e j b ≤ ∑ i, A.e j (y i) := by
  unfold IsoAct.e
  split_ifs with hj
  · simpa using hb.sum_mul_dist_le (fun _ => zero_le_one)
      (hb.map (A (x h ⟨j, hj⟩)).isometry (A _).surjective)
  · simp

/-- **Lemma F.4** (p. 39): if `u ≥ 2`, `p + 3u ≤ h`, `ζ ≥ 0`, `4 C(3u) ≤ ζ²(u − 1)²` and `a` is
fixed by `[p, p + 2u)`, then `|a, P_{[p+u, p+3u)} a| ≥ (1 − ζ) R`, `R = |a, P_{[p, p+3u)} a|`.
The points `b_k = P_{[p+k, p+3u)} a` are fixed by all generators of `[p, p + 3u)` but `x_{p+k−1}`,
which moves `b_k` by at most `2|b_{k−1} b_k|`; their barycenter `b̄` is within `ζR` of a common
fixed point by (F.1). -/
private theorem dist_P_ge (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hA : ∀ z, Contr (A.len z) μ s) {u p : ℕ}
    {ζ : ℝ} (hu : 2 ≤ u) (hp : p + 3 * u ≤ h) (hζ : 0 ≤ ζ)
    (hC : 4 * (kappa μ s (3 * u) ^ 2 * (3 * u : ℕ)) ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2) {a : Z}
    (ha : (A.W p (2 * u)).Fix a) :
    (1 - ζ) * dist a ((A.W p (3 * u)).P a) ≤ dist a ((A.W (p + u) (2 * u)).P a) := by
  set R := dist a ((A.W p (3 * u)).P a)
  set B : ℕ → Z := fun k => (A.W (p + k) (3 * u - k)).P a
  have hBfix : ∀ k, (A.W (p + k) (3 * u - k)).Fix (B k) := fun k => IsoAct.P_fix _ a
  have hBu : B u = (A.W (p + u) (2 * u)).P a := by
    simp only [B]
    rw [show 3 * u - u = 2 * u by omega]
  have hu1 : (1 : ℝ) ≤ (u : ℝ) - 1 := by
    have : (2 : ℝ) ≤ u := by exact_mod_cast hu
    linarith
  -- Lemma C.4(d) at `b_k`
  have hstep : ∀ k < 3 * u,
      dist (B k) (B (k + 1)) ^ 2 ≤ dist a (B k) ^ 2 - dist a (B (k + 1)) ^ 2 := fun k hk => by
      have := dist_P_sq_add_le (A.W (p + (k + 1)) (3 * u - (k + 1)))
        ((hBfix k).sub A (by omega) (by omega) (by omega)) a
      rw [dist_comm _ (B k)] at this
      change _ ≤ _ - dist a ((A.W (p + (k + 1)) (3 * u - (k + 1))).P a) ^ 2
      linarith
  have hφR : dist a (B u) ≤ R := dist_P_le _ (((A.W p (3 * u)).P_fix a).sub A (by omega)
    (by omega) hp) a
  have hφ : ∀ k, u ≤ k → k ≤ 3 * u → dist a (B k) ≤ dist a (B u) := fun k hk => by
    induction k, hk using Nat.le_induction with
    | base => exact fun _ => le_rfl
    | succ k hk ih =>
      refine fun hk3 => le_trans ?_ (ih (by omega))
      exact (pow_le_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero).1
        (by linarith [hstep k (by omega), sq_nonneg (dist (B k) (B (k + 1)))])
  -- the barycenter `b̄` of the `u − 1` points `b_k`, `u < k < 2u`
  have : Nonempty Z := ⟨a⟩
  obtain ⟨b, hb⟩ := exists_isBarycenter (fun _ : Fin (u - 1) => (1 : ℝ)) (fun _ => zero_le_one)
    fun i => B (u + 1 + i.1)
  have hw : ((u - 1 : ℕ) : ℝ) = (u : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hab : dist a b ≤ dist a (B u) := by
    have h1 := hb a
    simp only [one_mul, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hw] at h1
    have h2 : ∑ i : Fin (u - 1), dist a (B (u + 1 + i.1)) ^ 2 ≤ ((u : ℝ) - 1) * dist a (B u) ^ 2 :=
      (sum_le_sum fun i _ => pow_le_pow_left₀ dist_nonneg (hφ _ (by omega) (by omega)) 2).trans
        (by simp [hw])
    refine (pow_le_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero).1
      (le_of_mul_le_mul_left ?_ (by linarith : (0 : ℝ) < (u : ℝ) - 1))
    linarith [sum_nonneg fun (i : Fin (u - 1)) (_ : i ∈ univ) =>
      sq_nonneg (dist b (B (u + 1 + i.1)))]
  -- for `u < k < 2u` every generator of `[p, p + 3u)` fixes `b_k`, apart from `x_{p+k−1}`
  have he : ∀ t < 3 * u - 1, ∀ k, u + 1 ≤ k → k < 2 * u → k ≠ t + 1 → A.e (p + t) (B k) = 0 :=
    fun t ht k hk1 hk2 hkt => by
      by_cases htk : k ≤ t
      · exact A.e_zero (hBfix k) (by omega) (by omega) (by omega)
      · exact A.e_zero (fix_P_window A (by omega) (by omega)
          (ha.sub A (by omega) (by omega) (by omega) : (A.W (p + t) 2).Fix a)) le_rfl le_rfl
          (by omega)
  have hde : ∀ t < 3 * u - 1, (((u : ℝ) - 1) * A.e (p + t) b) ^ 2 ≤
      if u ≤ t ∧ t + 1 < 2 * u then 4 * (dist a (B t) ^ 2 - dist a (B (t + 1)) ^ 2) else 0 :=
    fun t ht => by
      have h1 := mul_e_le A hb (p + t)
      rw [hw] at h1
      have h0 : 0 ≤ ((u : ℝ) - 1) * A.e (p + t) b := mul_nonneg (by linarith) (A.e_nonneg _ _)
      split_ifs with hc
      · rw [sum_eq_single (⟨t - u, by omega⟩ : Fin (u - 1)) (fun i _ hi => he t ht _ (by omega)
          (by omega) fun e => hi (Fin.ext (by simp only at e ⊢; omega))) (by simp),
          show u + 1 + (t - u) = t + 1 by omega] at h1
        have h2 := (h1.trans (A.e_le (hBfix t) (by omega) (by omega) (by omega) _)).trans_eq
          (congrArg _ (dist_comm _ _))
        have h3 := (pow_le_pow_left₀ h0 h2 2).trans_eq (by ring : (2 * dist (B t) (B (t + 1))) ^ 2 =
          4 * dist (B t) (B (t + 1)) ^ 2)
        linarith [hstep t (by omega)]
      · rw [sum_eq_zero fun i _ => he t ht _ (by omega) (by omega)
          fun e => hc ⟨by omega, by omega⟩] at h1
        simp [le_antisymm h1 h0]
  have hsum : ((u : ℝ) - 1) ^ 2 * ∑ j ∈ Ico p (p + 3 * u - 1), A.e j b ^ 2 ≤ 4 * R ^ 2 := by
    rw [sum_Ico_eq_sum_range, show p + 3 * u - 1 - p = 3 * u - 1 by omega, mul_sum]
    refine (sum_le_sum fun t ht => (mul_pow _ _ 2).symm.trans_le (hde t (mem_range.1 ht))).trans ?_
    rw [← sum_filter, show (range (3 * u - 1)).filter (fun t => u ≤ t ∧ t + 1 < 2 * u) =
      Ico u (2 * u - 1) by ext t; simp only [mem_filter, mem_range, mem_Ico]; omega, ← mul_sum]
    rw [sum_Ico_eq_sum_range, show 2 * u - 1 - u = u - 1 by omega]
    have h4 := sum_range_sub' (fun k => dist a (B (u + k)) ^ 2) (u - 1)
    simp only [add_zero, ← add_assoc, show u + (u - 1) = 2 * u - 1 by omega] at h4
    rw [h4]
    linarith [sq_nonneg (dist a (B (2 * u - 1))), pow_le_pow_left₀ dist_nonneg hφR 2]
  -- by (F.1), `b̄` is within `ζR` of a fixed point of `[p, p + 3u)`
  have hbP : dist b ((A.W p (3 * u)).P b) ≤ ζ * R := by
    refine (pow_le_pow_iff_left₀ dist_nonneg (by positivity) two_ne_zero).1
      (le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < ((u : ℝ) - 1) ^ 2))
    calc ((u : ℝ) - 1) ^ 2 * dist b ((A.W p (3 * u)).P b) ^ 2
        ≤ (kappa μ s (3 * u) ^ 2 * (3 * u : ℕ)) *
            (((u : ℝ) - 1) ^ 2 * ∑ j ∈ Ico p (p + 3 * u - 1), A.e j b ^ 2) := by
          rw [← mul_left_comm]
          exact mul_le_mul_of_nonneg_left (dist_P_window_sq_le A hμ hs hA hp b) (sq_nonneg _)
      _ ≤ (kappa μ s (3 * u) ^ 2 * (3 * u : ℕ)) * (4 * R ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 4 * (kappa μ s (3 * u) ^ 2 * (3 * u : ℕ)) * R ^ 2 := by ring
      _ ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg R)
      _ = ((u : ℝ) - 1) ^ 2 * (ζ * R) ^ 2 := by ring
  have h1 := dist_P_le _ ((A.W p (3 * u)).P_fix b) a
  rw [← hBu]
  linarith [dist_triangle a b ((A.W p (3 * u)).P b)]

/-- The proof of Lemma F.5 for two finite groups of isometries with a common fixed point `v`. If
every point `q` at fraction `σ ∈ (0, 1]` from `v` to `a = P₁ z` has `(1 − c²)|vq|² ≤ |q, P₂ q|²`,
then `|a a'|² ≤ |za|² + |za'|² + 2c|za||za'|` for `a' = P₂ z`: first
`α² + β² − 2cαβ ≤ |aa'|²` for `α = |va|`, `β = |va'|` (F.2), from the points at `σ` and `τ`
with `τβ = cσα`; then the quadrangle `z, a, v, a'` is compared with a Euclidean one. -/
theorem dist_P_P_sq_le_of_fix {G₁ G₂ : Type*} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    {Z : Type*} [MetricSpace Z] [CompleteCAT0Space Z] (A₁ : IsoAct G₁ Z) (A₂ : IsoAct G₂ Z)
    {c : ℝ} (hc : 0 < c) {z v : Z} (hv1 : A₁.Fix v) (hv2 : A₂.Fix v)
    (hq : ∀ (q : Z) (σ : ℝ), 0 < σ → σ ≤ 1 → IsPointAt v (A₁.P z) σ q →
      (1 - c ^ 2) * dist v q ^ 2 ≤ dist q (A₂.P q) ^ 2) :
    dist (A₁.P z) (A₂.P z) ^ 2 ≤
      dist z (A₁.P z) ^ 2 + dist z (A₂.P z) ^ 2 + 2 * c * (dist z (A₁.P z) * dist z (A₂.P z)) := by
  set a := A₁.P z
  set a' := A₂.P z
  have hA1 := dist_P_sq_add_le A₁ hv1 z
  have hA2 := dist_P_sq_add_le A₂ hv2 z
  rcases (dist_nonneg (x := z) (y := a)).eq_or_lt with h0 | hr
  · rw [← h0, ← dist_eq_zero.1 h0.symm]
    simp
  rcases (dist_nonneg (x := z) (y := a')).eq_or_lt with h0 | hr'
  · rw [← h0, ← dist_eq_zero.1 h0.symm, dist_comm a z]
    simp
  have hpos : 0 ≤ 2 * c * (dist z a * dist z a') := by positivity
  rcases (dist_nonneg (x := v) (y := a)).eq_or_lt with h0 | hα
  · rw [dist_eq_zero.1 h0.symm, dist_comm a' a] at hA2
    linarith [sq_nonneg (dist z a')]
  rcases (dist_nonneg (x := v) (y := a')).eq_or_lt with h0 | hβ
  · rw [dist_eq_zero.1 h0.symm] at hA1
    linarith [sq_nonneg (dist z a)]
  rw [dist_comm a v] at hA1
  rw [dist_comm a' v] at hA2
  set α := dist v a
  set β := dist v a'
  -- (F.2), from the points `q` at `σ` on `[v, a]` and `q'` at `τ` on `[v, a']`, `τβ = cσα`
  have hQ : α ^ 2 + β ^ 2 - 2 * c * (α * β) ≤ dist a a' ^ 2 := by
    set N := β + c * α
    have hN0 : 0 < N := by positivity
    set σ := β / N
    set τ := c * α / N
    have hσ0 : 0 < σ := by positivity
    have hτ0 : 0 < τ := by positivity
    have hσ1 : σ ≤ 1 := by
      rw [div_le_one hN0]; linarith [mul_nonneg hc.le hα.le]
    have hτ1 : τ ≤ 1 := by rw [div_le_one hN0]; linarith
    obtain ⟨q, hq1⟩ := exists_isPointAt v a hσ0.le hσ1
    obtain ⟨q', hq2⟩ := exists_isPointAt v a' hτ0.le hτ1
    have q1 := hq1.dist_left hσ0.le hσ1
    have h2 := hq q σ hσ0 hσ1 hq1
    have h4 : dist q (A₂.P q) ^ 2 ≤ dist q q' ^ 2 := pow_le_pow_left₀ dist_nonneg
      (dist_P_le A₂ (fix_of_isPointAt A₂ hv2 (A₂.P_fix z) hτ0.le hτ1 hq2) q) 2
    have h5 := hq2 q
    have h6 := hq1 a'
    rw [dist_comm a' q, dist_comm a' v, dist_comm a' a] at h6
    rw [dist_comm q v] at h5
    rw [q1] at h2 h5
    have h8 := mul_le_mul_of_nonneg_left h6 hτ0.le
    have e1 : τ * β = c * (σ * α) := by simp only [τ, σ]; field_simp
    have h7 : (σ * τ) * (α ^ 2 + β ^ 2 - dist a a' ^ 2) ≤ (σ * τ) * (2 * c * (α * β)) := by
      have hid : (σ * τ) * (2 * c * (α * β)) - (σ * τ) * (α ^ 2 + β ^ 2 - dist a a' ^ 2) =
          ((1 - τ) * (σ * α) ^ 2 +
            τ * ((1 - σ) * β ^ 2 + σ * dist a a' ^ 2 - σ * (1 - σ) * α ^ 2) -
            τ * (1 - τ) * β ^ 2) - (1 - c ^ 2) * (σ * α) ^ 2 := by
        linear_combination -(τ * β - c * (σ * α)) * e1
      linarith
    linarith [le_of_mul_le_mul_left h7 (by positivity)]
  refine angle_num (α := α) (β := β) (A := dist z v ^ 2) hr hr' hα hβ (by linarith)
    (by linarith) hQ fun η t hη0 hη1 ht0 ht1 => ?_
  -- Lemma C.4(a) twice, for the points at `η` on `[a, a']` and at `t` on `[z, v]`
  obtain ⟨m, hm⟩ := exists_isPointAt a a' hη0 hη1
  obtain ⟨g, hg⟩ := exists_isPointAt z v ht0 ht1
  have h1 := mul_le_mul_of_nonneg_left (hm z) (show 0 ≤ 1 - t by linarith)
  have h2 := mul_le_mul_of_nonneg_left (hm v) ht0
  have h3 := hg m
  rw [dist_comm m z, dist_comm m v] at h3
  linarith [sq_nonneg (dist m g)]

/-- **Lemma F.5** (p. 40): for `u`, `p`, `ζ` as in Lemma F.4, `0 ≤ ζ ≤ 1`, `c > 0` and
`1 − c² ≤ (1 − ζ)²`, the projections `a`, `a'` of `z` for the windows `[p, p + 2u)` and
`[p + u, p + 3u)` satisfy `|aa'|² ≤ |za|² + |za'|² + 2c|za||za'|`. -/
theorem dist_P_P_sq_le (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hA : ∀ z, Contr (A.len z) μ s) {u p : ℕ}
    {ζ c : ℝ} (hu : 2 ≤ u) (hp : p + 3 * u ≤ h) (hζ : 0 ≤ ζ)
    (hC : 4 * (kappa μ s (3 * u) ^ 2 * (3 * u : ℕ)) ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2) (hζ1 : ζ ≤ 1)
    (hcζ : 1 - c ^ 2 ≤ (1 - ζ) ^ 2) (hc : 0 < c) (z : Z) :
    dist ((A.W p (2 * u)).P z) ((A.W (p + u) (2 * u)).P z) ^ 2 ≤
      dist z ((A.W p (2 * u)).P z) ^ 2 + dist z ((A.W (p + u) (2 * u)).P z) ^ 2 +
        2 * c * (dist z ((A.W p (2 * u)).P z) * dist z ((A.W (p + u) (2 * u)).P z)) := by
  set v := (A.W p (3 * u)).P ((A.W p (2 * u)).P z)
  have hvf : (A.W p (3 * u)).Fix v := IsoAct.P_fix _ _
  have hv1 : (A.W p (2 * u)).Fix v := hvf.sub A le_rfl (by omega) hp
  refine dist_P_P_sq_le_of_fix _ _ hc hv1 (hvf.sub A (by omega) (by omega) hp)
    fun q σ hσ0 hσ1 hq => ?_
  have hqv : (A.W p (3 * u)).P q = v := P_eq_of_dist_add_dist _ (by
    rw [hq.dist_left hσ0.le hσ1, hq.dist_right hσ0.le hσ1]; ring)
  have h1 := dist_P_ge A hμ hs hA hu hp hζ hC
    (fix_of_isPointAt _ hv1 (IsoAct.P_fix _ z) hσ0.le hσ1 hq)
  rw [hqv, dist_comm q v] at h1
  calc (1 - c ^ 2) * dist v q ^ 2 ≤ ((1 - ζ) * dist v q) ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right hcζ (sq_nonneg _)
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (by linarith) dist_nonneg) h1 2

end Cslib.Circuits.Arithmetic.Separation.Poincare
