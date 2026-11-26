/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Basic
public import CslibFrontier.Foundations.GroupTheory.SLTower.UT
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Poincare.Windows
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Avg
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Curvature
import CslibFrontier.Foundations.GroupTheory.SLTower.Gen

/-!
# A Poincaré inequality on unitriangular groups: Theorem F.6

In the contracting case there are `u ≥ 2` and `C₀ ≥ 0` such that for every `l ≥ 2`, `h = l u`,
and every price on `U_h`, the mean squared distance of two random elements is at most `C₀` times
the sum over the generators `x_j` of the mean squared distance of `k` and `x_j k`
(`Poincare.exists_poincareBound`).

The proof lets `U_h` act on the maps from `U_h` into a price space (Proposition C.3), a CAT(0)
space on which the displacement lengths contract. For the projections `Q_i` to the fixed points
of the windows `[iu, iu + 2u)`, `i < l − 1`, and `Φ(z) = ∑_i |z, Q_i z|²`, Lemma F.5 bounds the
distances between the `Q_i z`; replacing `z` by the barycenter of the `Q_i z` decreases `Φ` by a
fixed factor, and the iteration converges to a point fixed by every window, hence by `U_h`
(`Cslib.SLTower.closure_range_x`).

## Main definitions

* `Poincare.PoincareBound K u C₀`: the inequality of Theorem F.6 for `u` and `C₀`.

## Main results

* `Poincare.exists_poincareBound`: Theorem F.6.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem F.6 and its proof, Section F.3, pp. 40–41; module `Paper.Groups` (`thm_poincare`,
  `PoincareBound`)
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Poincare

open Finset Filter Topology Cslib.PartyTensor Cslib.CAT0
open Cslib.Circuits.Arithmetic.Separation.Flag Cslib.Circuits.Arithmetic.Separation.TwoCases
open Cslib.SLTower (U x)

/-- The inequality of Theorem F.6 for `u` and `C₀`: for every `l ≥ 2`, `h = l u`, and every
price `w` on `U_h`, `E_{g,k} w(k, gk)² ≤ C₀ ∑_{j < h−1} E_k w(k, x_j k)²`, with `g` and `k`
independent and uniform in `U_h`. -/
@[expose] def PoincareBound (K : Type) [Field K] (u : ℕ) (C₀ : ℝ) : Prop :=
  ∀ l : ℕ, 2 ≤ l → ∀ w : U (l * u) → U (l * u) → ℝ, IsPrice K w →
    (∑ g, ∑ k, w k (g * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ) ^ 2 ≤
      C₀ * ∑ j, (∑ k, w k (x (l * u) j * k) ^ 2) / Fintype.card (U (l * u))

/-! ### One step of averaging -/

/-- At most one `b` for each `a`. -/
private theorem sum_sum_ite_le {L : ℕ} (g : Fin L → ℝ) (hg : ∀ a, 0 ≤ g a)
    (P : Fin L → Fin L → Prop) [∀ a b, Decidable (P a b)] (hP : ∀ a, #{b | P a b} ≤ 1) :
    ∑ a, ∑ b, (if P a b then g a else 0) ≤ ∑ a, g a :=
  sum_le_sum fun a _ => by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    exact mul_le_of_le_one_left (hg a) (by exact_mod_cast hP a)

/-- Iterating a map `b` with `F(b z) ≤ (1 − 1/(2L)) F(z)` and `L|z, b z|² ≤ F(z) − F(b z)`
from `z`, the points converge to a zero `y` of a continuous `F ≥ 0`, with `|zy|² ≤ 8 F(z)`:
"the steps add up to at most `2 √(Φ(z)/(1 − 2c))`", for `c = 1/4`. -/
private theorem exists_eq_zero_of_step {Z : Type*} [MetricSpace Z] [CompleteSpace Z]
    {F : Z → ℝ} (hF0 : ∀ z, 0 ≤ F z) (hFc : Continuous F) {L : ℝ} (hL : 1 ≤ L) {b : Z → Z}
    (hb1 : ∀ z, F (b z) ≤ (1 - 1 / 2 / L) * F z)
    (hb2 : ∀ z, L * dist z (b z) ^ 2 ≤ F z - F (b z)) (z : Z) :
    ∃ y, F y = 0 ∧ dist z y ^ 2 ≤ 8 * F z := by
  set y : ℕ → Z := fun n => b^[n] z
  have hys : ∀ n, y (n + 1) = b (y n) := fun n => Function.iterate_succ_apply' b n z
  set X : ℕ → ℝ := fun n => 2 / √(1 / 2) * √(F (y n))
  have hX0 : ∀ n, 0 ≤ X n := fun n => by positivity
  have hstep : ∀ n, dist (y n) (y (n + 1)) ≤ X n - X (n + 1) := fun n => by
    simp only [X, hys, ← mul_sub]
    exact step_num (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hL (by norm_num)
      (by rw [Real.sq_sqrt (hF0 _), Real.sq_sqrt (hF0 _)]; exact hb1 _)
      (by rw [Real.sq_sqrt (hF0 _), Real.sq_sqrt (hF0 _)]; exact hb2 _)
  have htot : ∀ n m, n ≤ m → dist (y n) (y m) ≤ X n - X m := fun n m hnm => by
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m _ ih => linarith [dist_triangle (y n) (y m) (y (m + 1)), hstep m]
  have hq0 : 0 ≤ 1 - 1 / 2 / L :=
    sub_nonneg.2 ((div_le_self (by norm_num) hL).trans one_half_lt_one.le)
  have hq1 : 1 - 1 / 2 / L < 1 := sub_lt_self _ (by positivity)
  have hFlim : Tendsto (fun n => F (y n)) atTop (𝓝 0) := by
    refine squeeze_zero (g := fun n => (1 - 1 / 2 / L) ^ n * F z) (fun n => hF0 _)
      (fun n => ?_) (by simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (F z))
    induction n with
    | zero => simp [y]
    | succ n ih =>
      rw [hys, pow_succ', mul_assoc]
      exact (hb1 _).trans (mul_le_mul_of_nonneg_left ih hq0)
  obtain ⟨y₀, hy₀⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_tendsto_0' X
    (fun n m hnm => (htot n m hnm).trans (by linarith [hX0 m]))
    (by simpa only [Real.sqrt_zero, mul_zero] using hFlim.sqrt.const_mul (2 / √(1 / 2))))
  refine ⟨y₀, tendsto_nhds_unique ((hFc.tendsto y₀).comp hy₀) hFlim, ?_⟩
  have h1 : dist z y₀ ≤ X 0 := le_of_tendsto' ((tendsto_const_nhds (x := z)).dist hy₀) fun n =>
    (htot 0 n (Nat.zero_le n)).trans (by linarith [hX0 n])
  calc dist z y₀ ^ 2 ≤ X 0 ^ 2 := pow_le_pow_left₀ dist_nonneg h1 2
    _ = 8 * F z := by
      simp only [X, y, Function.iterate_zero, id_eq, mul_pow, div_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.sq_sqrt (hF0 z)]
      norm_num

section Action

variable {h : ℕ} {Z : Type*} [MetricSpace Z]

/-- The first inequality of (F.3): "if `y` is fixed by the window of `i`, then the point nearest
to `y` among those fixed by the window of `i′` is fixed by both. This point can therefore serve as
`v` in the proof of Lemma F.5, with `ζ = 0` and every `c > 0`". -/
private theorem dist_P_P_sq_le_of_disjoint [CompleteCAT0Space Z] (A : IsoAct (U h) Z)
    {p n p' n' : ℕ} (hd : p + n ≤ p') (hp' : p' + n' ≤ h) (z : Z) :
    dist ((A.W p n).P z) ((A.W p' n').P z) ^ 2 ≤
      dist z ((A.W p n).P z) ^ 2 + dist z ((A.W p' n').P z) ^ 2 := by
  set v := (A.W p' n').P ((A.W p n).P z)
  set r := dist z ((A.W p n).P z) * dist z ((A.W p' n').P z)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hc : 0 < ε / (2 * r + 1) := by positivity
  refine (dist_P_P_sq_le_of_fix _ _ hc (fix_P_window A hd hp' (IsoAct.P_fix _ z))
    (IsoAct.P_fix _ _) fun q σ hσ0 hσ1 hq => ?_).trans ?_
  · rw [P_eq_of_dist_add_dist (A.W p' n') (a := (A.W p n).P z) (q := q)
      (by rw [hq.dist_left hσ0.le hσ1, hq.dist_right hσ0.le hσ1]; ring), dist_comm q]
    exact mul_le_of_le_one_left (sq_nonneg _) (by linarith [sq_nonneg (ε / (2 * r + 1))])
  · gcongr
    rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith

variable {μ : ℕ} {s : ℝ} {u L : ℕ}

/-- `Φ(z) = ∑_i |z, Q_i z|²` for the projections `Q_i` to the windows `[iu, iu + 2u)`, `i < L`. -/
private noncomputable def windowSum [CompleteCAT0Space Z] (A : IsoAct (U h) Z) (u L : ℕ) (z : Z) :
    ℝ :=
  ∑ i : Fin L, dist z ((A.W (i.1 * u) (2 * u)).P z) ^ 2

private theorem window_le (hh : (L + 1) * u = h) (a : Fin L) : a.1 * u + 2 * u ≤ h :=
  hh ▸ by rw [← add_mul]; exact Nat.mul_le_mul_right u (by omega)

/-- One step of averaging: for the barycenter `b` of the `L` points `Q_i z`,
`Φ(b) ≤ (1 − (1 − 2c)/L) Φ(z)` and `L|zb|² ≤ Φ(z) − Φ(b)`, for `c = 1/4`. By (F.3),
`|Q_i z, Q_{i'} z|² ≤ r_i² + r_{i'}²` for windows that do not meet and
`|Q_i z, Q_{i+1} z|² ≤ (1 + c)(r_i² + r_{i+1}²)` by Lemma F.5. -/
private theorem exists_windowSum_le [CompleteCAT0Space Z] (A : IsoAct (U h) Z) (hμ : 2 ≤ μ)
    (hs : 1 ≤ s) (hA : ∀ z, Contr (A.len z) μ s)
    (hu : 2 ≤ u) (hL : 1 ≤ L) (hh : (L + 1) * u = h)
    (hC : 4 * (kappa μ s (3 * u) ^ 2 * (3 * u : ℕ)) ≤ (1 / 32) ^ 2 * ((u : ℝ) - 1) ^ 2) (z : Z) :
    ∃ b, windowSum A u L b ≤ (1 - 1 / 2 / L) * windowSum A u L z ∧
      L * dist z b ^ 2 ≤ windowSum A u L z - windowSum A u L b := by
  set Q : Fin L → Z := fun a => (A.W (a.1 * u) (2 * u)).P z
  set r : Fin L → ℝ := fun a => dist z (Q a) ^ 2
  have hr : ∀ a, 0 ≤ r a := fun a => sq_nonneg _
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  -- (F.3) for `a < b`
  have hlt : ∀ a b : Fin L, a < b → dist (Q a) (Q b) ^ 2 ≤
      r a + r b + (if b.1 = a.1 + 1 then 1 / 4 * (r a + r b) else 0) := fun a b hab => by
    split_ifs with hb
    · have h1 := dist_P_P_sq_le A hμ hs hA (p := a.1 * u) hu
        (by have := window_le hh b; rw [hb, add_mul, one_mul] at this; omega)
        (by norm_num) hC (by norm_num) (by norm_num : 1 - (1 / 4 : ℝ) ^ 2 ≤ (1 - 1 / 32) ^ 2)
        (by norm_num) z
      rw [show a.1 * u + u = b.1 * u by rw [hb]; ring] at h1
      have h2 : 2 * (dist z (Q a) * dist z (Q b)) ≤ r a + r b :=
        mul_assoc (2 : ℝ) _ _ ▸ two_mul_le_add_sq _ _
      linarith
    · rw [add_zero]
      have hab2 : a.1 + 2 ≤ b.1 := by have := Fin.lt_def.1 hab; omega
      exact dist_P_P_sq_le_of_disjoint A
        (by rw [← add_mul]; exact Nat.mul_le_mul_right u hab2) (window_le hh b) z
  have hpair : ∀ a b : Fin L, dist (Q a) (Q b) ^ 2 ≤ r a + r b + 1 / 4 *
      ((if b.1 = a.1 + 1 then r a else 0) + (if b.1 = a.1 + 1 then r b else 0) +
        ((if a.1 = b.1 + 1 then r a else 0) + (if a.1 = b.1 + 1 then r b else 0))) -
      if a = b then 2 * r a else 0 := fun a b => by
    rcases lt_trichotomy a b with hab | rfl | hab
    · have := hlt a b hab
      have hba : ¬ a.1 = b.1 + 1 := Nat.ne_of_lt (Nat.lt_succ_of_lt (Fin.lt_def.1 hab))
      simp only [hab.ne, hba, ↓reduceIte]
      split_ifs at this ⊢ <;> linarith
    · simp [two_mul]
    · have := dist_comm (Q a) (Q b) ▸ hlt b a hab
      have hba : ¬ b.1 = a.1 + 1 := Nat.ne_of_lt (Nat.lt_succ_of_lt (Fin.lt_def.1 hab))
      simp only [hab.ne', hba, ↓reduceIte]
      split_ifs at this ⊢ <;> linarith
  have h1 : ∀ a : Fin L, #{b : Fin L | b.1 = a.1 + 1} ≤ 1 := fun a =>
    card_le_one.2 fun b hb b' hb' => Fin.ext (by simp at hb hb'; omega)
  have h2 : ∀ a : Fin L, #{b : Fin L | a.1 = b.1 + 1} ≤ 1 := fun a =>
    card_le_one.2 fun b hb b' hb' => Fin.ext (by simp at hb hb'; omega)
  have hsum : ∑ a, ∑ b, dist (Q a) (Q b) ^ 2 ≤ 2 * ((L : ℝ) - 1 / 2) * ∑ a, r a := by
    refine (sum_le_sum fun a _ => sum_le_sum fun b _ => hpair a b).trans ?_
    simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_ite_eq, mem_univ, ite_true,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have s1 := sum_sum_ite_le r hr (fun a b => b.1 = a.1 + 1) h1
    have s2 := sum_sum_ite_le r hr (fun b a => b.1 = a.1 + 1) h2
    have s3 := sum_sum_ite_le r hr (fun a b => a.1 = b.1 + 1) h2
    have s4 := sum_sum_ite_le r hr (fun b a => a.1 = b.1 + 1) h1
    rw [sum_comm] at s2 s4
    linarith [sum_nonneg fun a (_ : a ∈ univ) => hr a]
  -- the barycenter `b` of the points `Q_i z`
  have : Nonempty Z := ⟨z⟩
  obtain ⟨b, hb⟩ := exists_isBarycenter (fun _ : Fin L => (1 : ℝ)) (fun _ => zero_le_one) Q
  simp only [IsBarycenter, one_mul, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hb
  have h3 : 2 * (L * ∑ i, dist b (Q i) ^ 2) ≤ ∑ i, ∑ j, dist (Q i) (Q j) ^ 2 := by
    refine le_trans (le_of_eq ?_) (sum_le_sum fun i _ => hb (Q i))
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum,
      sum_congr rfl fun i _ => congrArg (· ^ 2) (dist_comm (Q i) b)]
    ring
  have h4 : windowSum A u L b ≤ ∑ i, dist b (Q i) ^ 2 := sum_le_sum fun i _ =>
    pow_le_pow_left₀ dist_nonneg (dist_P_le _ (IsoAct.P_fix _ z) b) 2
  have h5 : ∑ i, dist b (Q i) ^ 2 ≤ (1 - 1 / 2 / L) * windowSum A u L z :=
    le_of_mul_le_mul_left (by
      have : 2 * (L : ℝ) * ((1 - 1 / 2 / L) * windowSum A u L z) =
          2 * ((L : ℝ) - 1 / 2) * ∑ a, r a := by simp only [windowSum, r, Q]; field_simp
      linarith) (by linarith : (0 : ℝ) < 2 * L)
  exact ⟨b, h4.trans h5, by have := hb z; simp only [windowSum, Q] at *; linarith⟩

/-- "Each generator lies in at most two of the windows, so (F.1) for `n = 2u` bounds `Φ(z)` by
`2 C(2u) ∑_j δ_j(z)²`." -/
private theorem windowSum_le [CompleteCAT0Space Z] (A : IsoAct (U h) Z) (hμ : 2 ≤ μ)
    (hs : 1 ≤ s) (hA : ∀ z, Contr (A.len z) μ s)
    (hh : (L + 1) * u = h) (z : Z) :
    windowSum A u L z ≤ 2 * (kappa μ s (2 * u) ^ 2 * (2 * u : ℕ)) * ∑ j ∈ range h, A.e j z ^ 2 := by
  set g : ℕ → ℝ := fun j => A.e j z ^ 2
  have hg : ∀ j, 0 ≤ g j := fun j => sq_nonneg _
  have hcons : ∀ m, ∑ a ∈ range m, ∑ j ∈ Ico (a * u) ((a + 1) * u), g j =
      ∑ j ∈ range (m * u), g j :=
    fun m => by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [sum_range_succ, ih, sum_range_add_sum_Ico _ (Nat.mul_le_mul_right u (Nat.le_succ m))]
  set C := kappa μ s (2 * u) ^ 2 * (2 * u : ℕ)
  set S1 : ℕ → ℝ := fun a => ∑ j ∈ Ico (a * u) ((a + 1) * u), g j
  set S2 : ℕ → ℝ := fun a => ∑ j ∈ Ico ((a + 1) * u) ((a + 1 + 1) * u), g j
  have hwin : ∀ a : Fin L, dist z ((A.W (a.1 * u) (2 * u)).P z) ^ 2 ≤ C * (S1 a + S2 a) :=
    fun a => by
      refine (dist_P_window_sq_le A hμ hs hA (window_le hh a) z).trans
        (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have e : (a.1 + 1 + 1) * u = a.1 * u + 2 * u := by ring
      simp only [S1, S2]
      rw [sum_Ico_consecutive _ (Nat.mul_le_mul_right u (Nat.le_succ _))
        (Nat.mul_le_mul_right u (Nat.le_succ _)), e]
      exact sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico le_rfl (by omega)) fun j _ _ => hg j
  refine (sum_le_sum fun a _ => hwin a).trans ?_
  rw [← Finset.mul_sum, sum_add_distrib, Fin.sum_univ_eq_sum_range S1,
    Fin.sum_univ_eq_sum_range S2]
  have e1 : ∑ a ∈ range L, S1 a ≤ ∑ j ∈ range h, g j :=
    hcons L ▸ sum_le_sum_of_subset_of_nonneg
      (range_subset_range.2 (hh ▸ Nat.mul_le_mul_right u (Nat.le_succ L))) fun j _ _ => hg j
  have e2 : ∑ a ∈ range L, S2 a ≤ ∑ j ∈ range h, g j := by
    rw [← hh, ← hcons, sum_range_succ' _ L]
    linarith [sum_nonneg fun j (_ : j ∈ Ico (0 * u) ((0 + 1) * u)) => hg j]
  linarith [mul_le_mul_of_nonneg_left (add_le_add e1 e2) (by positivity : 0 ≤ C)]

/-- The Poincaré bound for an isometric action of `U_h`, `h = (L + 1)u`, on a complete CAT(0)
space with contracting lengths, from the proof of Theorem F.6 with `ζ = 1/32` and `c = 1/4`:
"`|z, gz| ≤ 2|z, P_{[0,h)} z|`", so `E_g|z, gz|² ≤ 64 C(2u) ∑_j δ_j(z)²`. -/
private theorem mean_dist_sq_le [CompleteCAT0Space Z] (A : IsoAct (U h) Z) (hμ : 2 ≤ μ)
    (hs : 1 ≤ s) (hA : ∀ z, Contr (A.len z) μ s)
    (hu : 2 ≤ u) (hL : 1 ≤ L) (hh : (L + 1) * u = h)
    (hC : 4 * (kappa μ s (3 * u) ^ 2 * (3 * u : ℕ)) ≤ (1 / 32) ^ 2 * ((u : ℝ) - 1) ^ 2) (z : Z) :
    (∑ g, dist z (A g z) ^ 2) / Fintype.card (U h) ≤
      64 * (kappa μ s (2 * u) ^ 2 * (2 * u : ℕ)) * ∑ j, dist z (A (x h j) z) ^ 2 := by
  choose b hb1 hb2 using exists_windowSum_le A hμ hs hA hu hL hh hC
  have hFc : Continuous (windowSum A u L) :=
    continuous_finsetSum univ fun a _ => Continuous.pow
      (LipschitzWith.of_le_add (f := fun y : Z => dist y ((A.W (a.1 * u) (2 * u)).P y))
        fun y w => by linarith [dist_P_le (A.W (a.1 * u) (2 * u)) (IsoAct.P_fix _ w) y,
          dist_triangle y w ((A.W (a.1 * u) (2 * u)).P w)]).continuous 2
  obtain ⟨y, hy0, hy⟩ := exists_eq_zero_of_step (F := windowSum A u L)
    (fun z => by unfold windowSum; positivity) hFc
    (by exact_mod_cast hL) hb1 hb2 z
  -- `y` is fixed by every window, hence by every generator, hence by `U_h`
  have hwin : ∀ a : Fin L, (A.W (a.1 * u) (2 * u)).Fix y := fun a => by
    have := (sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 hy0 a (mem_univ a)
    rw [dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)]
    exact IsoAct.P_fix _ _
  have hx : ∀ j, A (x h j) y = y := fun ⟨j, hj⟩ => by
    obtain ⟨a, ha1, ha2⟩ : ∃ a : Fin L, a.1 * u ≤ j ∧ j + 2 ≤ a.1 * u + 2 * u := by
      have h1 := Nat.div_mul_le_self j u
      have h2 := Nat.lt_div_mul_add (a := j) (by omega : 0 < u)
      have hj2 : j + 2 ≤ h := by omega
      by_cases hjL : j / u < L
      · exact ⟨⟨j / u, hjL⟩, h1, by simp only; linarith⟩
      · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
        have h3 : (L' + 1) * u ≤ j / u * u := Nat.mul_le_mul_right u (Nat.le_of_not_lt hjL)
        exact ⟨⟨L', by omega⟩, by simp only; linarith, by simp only; linarith⟩
    have he := A.e_zero (hwin a) ha1 ha2 (window_le hh a)
    rw [IsoAct.e, dite_eq_left (by omega)] at he
    exact (dist_eq_zero.1 he).symm
  have hfix : A.Fix y := fun g => by
    induction (Cslib.SLTower.closure_range_x ▸ Subgroup.mem_top g :
        g ∈ Subgroup.closure (Set.range (x h))) using Subgroup.closure_induction with
    | mem _ hg => obtain ⟨j, rfl⟩ := hg; exact hx j
    | one => exact A.act_one y
    | mul a b _ _ ha hb => rw [A.act_mul, hb, ha]
    | inv a _ ha => conv_lhs => rw [← ha]; rw [← A.act_mul, inv_mul_cancel, A.act_one]
  have hd : ∀ g, dist z (A g z) ^ 2 ≤ 4 * dist z y ^ 2 := fun g => by
    have h1 := dist_triangle z y (A g z)
    rw [← hfix g, (A g).dist_eq, hfix g, dist_comm y z] at h1
    exact (pow_le_pow_left₀ dist_nonneg (by linarith : dist z (A g z) ≤ 2 * dist z y) 2).trans_eq
      (by ring)
  have hw := windowSum_le A hμ hs hA hh z
  have hsum : ∑ j ∈ range h, A.e j z ^ 2 = ∑ j, dist z (A (x h j) z) ^ 2 := by
    rw [← sum_subset (range_subset_range.2 (Nat.sub_le h 1)) fun j _ hj => by
      rw [IsoAct.e, dite_eq_right (by simpa using hj)]; simp,
      ← Fin.sum_univ_eq_sum_range (fun j => A.e j z ^ 2)]
    exact sum_congr rfl fun j _ => by rw [IsoAct.e, dite_eq_left j.2]
  rw [hsum] at hw
  rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos)]
  refine (sum_le_card_nsmul univ _ _ fun g _ => hd g).trans ?_
  rw [card_univ, nsmul_eq_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

end Action

/-- **Paper: Theorem F.6** (p. 40), the Poincaré inequality: in the contracting case there are an
integer `u ≥ 2` and a real `C₀ ≥ 0` such that for every `l ≥ 2`, `h = l u`, and every price on
`U_h`, `E_{g,k}|k, gk|² ≤ C₀ ∑_{j < h−1} E_k|k, x_j k|²`. Here `C₀ = 32 C(2u)/(1 − 2c)` with
`c = 1/4` and `C(n) = κ_n² n`. -/
theorem exists_poincareBound {K : Type} [Field K] (hK : ContractingCase K) :
    ∃ u : ℕ, 2 ≤ u ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧ PoincareBound K u C₀ := by
  obtain ⟨μ, s, hμ, hs, hsm, hcase⟩ := hK
  obtain ⟨u, hu, hC⟩ := exists_kappa_le hμ hs hsm
  refine ⟨u, hu, 64 * (kappa μ s (2 * u) ^ 2 * (2 * u : ℕ)), by positivity, fun l hl w hw => ?_⟩
  obtain ⟨Y, _, _, f, hY, hf⟩ := Curvature.exists_completeCAT0Space_of_isPrice hw
  have e : ∀ g : U (l * u), dist (WithLp.toLp 2 f : PiLp 2 fun _ : U (l * u) => Y)
      ((transAct (U (l * u)) Y) g (WithLp.toLp 2 f)) ^ 2 = ∑ k, w k (g * k) ^ 2 := fun g => by
    rw [transAct_dist]
    exact sum_congr rfl fun k _ => by rw [dist_comm]; exact congrArg (· ^ 2) (hf _ _)
  have h1 := mean_dist_sq_le (transAct (U (l * u)) Y) hμ hs (contr_len_transAct hcase hY) hu
    (L := l - 1) (by omega) (by rw [Nat.sub_add_cancel (by omega)]) hC (WithLp.toLp 2 f)
  simp only [e, pow_two, ← div_div, ← sum_div, ← mul_div_assoc] at h1 ⊢
  exact div_le_div_of_nonneg_right h1 (Nat.cast_nonneg _)

end Cslib.Circuits.Arithmetic.Separation.Poincare
