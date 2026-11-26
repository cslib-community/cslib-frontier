/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate (Mathlib, spectral perturbation estimates)

public import CslibFrontier.Foundations.LinearAlgebra.TracePower
public import CslibFrontier.Foundations.Analysis.InnerProductSpace.RankOnePerturbation
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Residual bounds for an isolated eigenvector

The spectral theorem turns a small residual at a candidate eigenvalue into proximity to an
isolated eigenline. The error is controlled by the distance to all other eigenvalues. A second
estimate bounds the third ordered eigenvalue from a quadratic-form bound on the common
orthogonal complement of two vectors. These are deterministic ingredients of spectral recovery.
-/

public section

open Finset Module
open scoped RealInnerProductSpace

namespace LinearMap.IsSymmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
  {n : ℕ} (hn : finrank ℝ E = n)

/-- A spectral gap around one chosen eigenvalue bounds the distance of a vector from its
eigenline by its residual. The center need not equal the chosen eigenvalue. -/
theorem gap_mul_sq_norm_sub_projection_le (j : Fin n) (x : E) (μ gap : ℝ)
    (hgap : 0 ≤ gap)
    (hsep : ∀ i, i ≠ j → gap ≤ |hT.eigenvalues hn i - μ|) :
    gap ^ 2 * ‖x - (hT.eigenvectorBasis hn).repr x j • hT.eigenvectorBasis hn j‖ ^ 2 ≤
      ‖T x - μ • x‖ ^ 2 := by
  classical
  let b := hT.eigenvectorBasis hn
  have hnorm (y : E) : ‖y‖ ^ 2 = ∑ i : Fin n, (b.repr y i) ^ 2 := by
    simpa only [b.repr_apply_apply] using (b.sum_sq_inner_right y).symm
  change gap ^ 2 * ‖x - b.repr x j • b j‖ ^ 2 ≤ ‖T x - μ • x‖ ^ 2
  rw [hnorm, hnorm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply,
    OrthonormalBasis.repr_self, PiLp.single_apply, smul_eq_mul]
  change gap ^ 2 * (b.repr x i - b.repr x j * (if i = j then 1 else 0)) ^ 2 ≤
    ((b.repr (T x)) i - μ * b.repr x i) ^ 2
  rw [hT.eigenvectorBasis_apply_self_apply hn x i]
  change gap ^ 2 * (b.repr x i - b.repr x j * (if i = j then 1 else 0)) ^ 2 ≤
    (hT.eigenvalues hn i * b.repr x i - μ * b.repr x i) ^ 2
  by_cases hij : i = j
  · simp only [hij, ite_true, mul_one, sub_self, zero_pow (by omega : 2 ≠ 0), mul_zero]
    exact sq_nonneg _
  · simp only [hij, ite_false, mul_zero, sub_zero]
    have hs : gap ^ 2 ≤ (hT.eigenvalues hn i - μ) ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ hgap (abs_nonneg _)).mpr (hsep i hij)
    calc
      _ ≤ (hT.eigenvalues hn i - μ) ^ 2 * (b.repr x i) ^ 2 :=
        mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ = _ := by ring

/-- The largest ordered eigenvalue bounds the quadratic form in every direction. -/
theorem inner_apply_le_first_eigenvalue_mul_sq (hnpos : 0 < n) (x : E) :
    inner ℝ x (T x) ≤ hT.eigenvalues hn ⟨0, hnpos⟩ * ‖x‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).sum_sq_inner_right x, Finset.mul_sum]
  have hquad := hT.re_inner_apply_eq_sum hn x
  simp only [RCLike.re_to_real, Real.norm_eq_abs, sq_abs] at hquad
  rw [hquad]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
    (hT.eigenvalues_antitone hn (show (⟨0, hnpos⟩ : Fin n) ≤ i from Nat.zero_le _))
    (sq_nonneg _)

/-- A quadratic-form bound on the common orthogonal complement of two vectors bounds every
ordered eigenvalue from the third onward. This is the rank-two min-max argument. -/
theorem third_eigenvalue_le_of_orthogonal_complement (hnthree : 3 ≤ n) (p q : E) (r : ℝ)
    (hbound : ∀ x, inner ℝ p x = 0 → inner ℝ q x = 0 →
      inner ℝ x (T x) ≤ r * ‖x‖ ^ 2) :
    hT.eigenvalues hn ⟨2, by omega⟩ ≤ r := by
  classical
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  let i₂ : Fin n := ⟨2, by omega⟩
  let b := hT.eigenvectorBasis hn
  let X : (Fin 3 → ℝ) →ₗ[ℝ] E :=
    (LinearMap.proj 0).smulRight (b i₀) +
      (LinearMap.proj 1).smulRight (b i₁) +
      (LinearMap.proj 2).smulRight (b i₂)
  let L : (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    ((innerₗ E p).prod (innerₗ E q)).comp X
  have hnot : ¬ Function.Injective L := by
    intro hinj
    have hdim := LinearMap.finrank_le_finrank_of_injective hinj
    norm_num [Module.finrank_fin_fun, Module.finrank_prod] at hdim
  obtain ⟨a, c, hac, hne⟩ := Function.not_injective_iff.mp hnot
  let d := a - c
  have hd : d ≠ 0 := sub_ne_zero.mpr hne
  have hLd : L d = 0 := by simp [d, map_sub, hac]
  have hcoords (z : Fin 3 → ℝ) :
      ‖X z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [X, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, b.inner_eq_ite]
    norm_num [i₀, i₁, i₂]
    ring
  have hXne : X d ≠ 0 := by
    intro hzero
    have hs := by simpa only [hzero, norm_zero, zero_pow (by omega : 2 ≠ 0)] using hcoords d
    apply hd
    funext i
    fin_cases i <;> dsimp <;> nlinarith [sq_nonneg (d 0), sq_nonneg (d 1), sq_nonneg (d 2)]
  have hp : inner ℝ p (X d) = 0 := congrArg Prod.fst hLd
  have hq : inner ℝ q (X d) = 0 := congrArg Prod.snd hLd
  have heig (i : Fin n) : T (b i) = hT.eigenvalues hn i • b i :=
    hT.apply_eigenvectorBasis hn i
  have hquad : inner ℝ (X d) (T (X d)) =
      hT.eigenvalues hn i₀ * d 0 ^ 2 + hT.eigenvalues hn i₁ * d 1 ^ 2 +
        hT.eigenvalues hn i₂ * d 2 ^ 2 := by
    simp only [X, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      map_add, map_smul, heig, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, b.inner_eq_ite]
    norm_num [i₀, i₁, i₂]
    ring
  have h₀ := mul_le_mul_of_nonneg_right
    (hT.eigenvalues_antitone hn (show i₀ ≤ i₂ by change 0 ≤ 2; omega)) (sq_nonneg (d 0))
  have h₁ := mul_le_mul_of_nonneg_right
    (hT.eigenvalues_antitone hn (show i₁ ≤ i₂ by change 1 ≤ 2; omega)) (sq_nonneg (d 1))
  have hb := hbound (X d) hp hq
  have hxpos : 0 < ‖X d‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hXne)
  have hlow : hT.eigenvalues hn i₂ * ‖X d‖ ^ 2 ≤ inner ℝ (X d) (T (X d)) := by
    rw [hcoords, hquad]
    nlinarith only [h₀, h₁]
  exact (mul_le_mul_iff_left₀ hxpos).mp (hlow.trans hb)

/-- The second ordered eigenvector of a small perturbation of two nearly orthogonal rank-one
signals approximates the weaker signal. The constants are deliberately conservative. -/
theorem exists_sign_second_eigenvector_sub_sq_le_of_rank_two
    (hnthree : 3 ≤ n) {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    {a b : ℝ} (hb : 0 < b) (hab : 2 * b ≤ a)
    (hinner : |inner ℝ w u| ≤ 1 / 64)
    (herror : ∀ y, ‖T y - ((a * inner ℝ w y) • w + (b * inner ℝ u y) • u)‖ ≤
      b / 128 * ‖y‖) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ‖hT.eigenvectorBasis hn ⟨1, by omega⟩ - s • u‖ ^ 2 ≤ 49 / 2048 := by
  let t := inner ℝ w u
  let x := u - t • w
  let R (y : E) := T y - ((a * inner ℝ w y) • w + (b * inner ℝ u y) • u)
  have hR (y : E) : ‖R y‖ ≤ b / 128 * ‖y‖ := herror y
  have ht : |t| ≤ 1 / 64 := hinner
  have hww : inner ℝ w w = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have huw : inner ℝ u w = t := real_inner_comm _ _
  have hfirst : a - b / 128 ≤ hT.eigenvalues hn ⟨0, by omega⟩ := by
    have hr : ‖R w‖ ≤ b / 128 := by simpa only [hw, mul_one] using hR w
    have hi : |inner ℝ w (R w)| ≤ ‖R w‖ := by
      simpa only [hw, one_mul] using abs_real_inner_le_norm w (R w)
    have heq : inner ℝ w (R w) = inner ℝ w (T w) - a - b * t ^ 2 := by
      simp only [R, inner_sub_right, inner_add_right, real_inner_smul_right, hww, huw,
        mul_one]
      change inner ℝ w (T w) - (a + b * t * t) = _
      ring
    rw [heq] at hi
    have hlow := (abs_le.mp (hi.trans hr)).1
    have htop := hT.inner_apply_le_first_eigenvalue_mul_sq hn (by omega) w
    rw [hw] at htop
    nlinarith [mul_nonneg hb.le (sq_nonneg t)]
  have hthird : hT.eigenvalues hn ⟨2, by omega⟩ ≤ b / 128 := by
    apply hT.third_eigenvalue_le_of_orthogonal_complement hn hnthree w u
    intro y hwy huy
    have hr := hR y
    simp only [R, hwy, huy, mul_zero, zero_smul, add_zero, sub_zero] at hr
    calc
      inner ℝ y (T y) ≤ ‖y‖ * ‖T y‖ := real_inner_le_norm _ _
      _ ≤ ‖y‖ * (b / 128 * ‖y‖) := mul_le_mul_of_nonneg_left hr (norm_nonneg _)
      _ = _ := by ring
  have hsep (i : Fin n) (hi : i ≠ ⟨1, by omega⟩) :
      b / 2 ≤ |hT.eigenvalues hn i - b| := by
    by_cases hi₀ : i = ⟨0, by omega⟩
    · subst i
      exact (le_abs_self _).trans' (by linarith)
    · have : i.val ≠ 0 := fun h => hi₀ (Fin.ext h)
      have : i.val ≠ 1 := fun h => hi (Fin.ext h)
      have h2 : 2 ≤ i.val := by omega
      have hupp := hthird.trans' (hT.eigenvalues_antitone hn h2)
      exact (neg_le_abs _).trans' (by linarith)
  have hx : ‖x‖ ≤ 2 := by
    calc
      ‖x‖ ≤ ‖u‖ + ‖t • w‖ := norm_sub_le _ _
      _ = 1 + |t| := by rw [norm_smul, hw, hu, Real.norm_eq_abs, mul_one]
      _ ≤ 2 := by linarith
  have hwx : inner ℝ w x = 0 := by
    simp only [x, inner_sub_right, real_inner_smul_right, hww, mul_one]
    exact sub_self _
  have hux : inner ℝ u x = 1 - t ^ 2 := by
    simp only [x, inner_sub_right, real_inner_smul_right, huu, huw]
    ring
  have hres_eq : T x - b • x = R x + (b * t) • w - (b * t ^ 2) • u := by
    simp only [R, hwx, hux, mul_zero, zero_smul, zero_add, x]
    module
  have hres : ‖T x - b • x‖ ≤ 3 * b / 64 := by
    rw [hres_eq]
    have hRx : ‖R x‖ ≤ b / 64 := (hR x).trans (by nlinarith only [hx, hb])
    have htab : t ^ 2 ≤ |t| := by
      have ht₁ : |t| ≤ 1 := ht.trans (by norm_num)
      nlinarith [sq_abs t, abs_nonneg t]
    calc
      ‖R x + (b * t) • w - (b * t ^ 2) • u‖ ≤
          ‖R x‖ + ‖(b * t) • w‖ + ‖(b * t ^ 2) • u‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖R x‖ + b * |t| + b * t ^ 2 := by
        simp only [norm_smul, hw, hu, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos hb,
          abs_of_nonneg (sq_nonneg t)]
      _ ≤ 3 * b / 64 := by nlinarith [mul_le_mul_of_nonneg_left ht hb.le,
        mul_le_mul_of_nonneg_left htab hb.le]
  let v := hT.eigenvectorBasis hn ⟨1, by omega⟩
  let c := (hT.eigenvectorBasis hn).repr x ⟨1, by omega⟩
  have hgap := hT.gap_mul_sq_norm_sub_projection_le hn ⟨1, by omega⟩ x b (b / 2)
    (by positivity) hsep
  have hdist : ‖x - c • v‖ ≤ 3 / 32 := by
    have hres_sq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3 * b / 64)).mpr hres
    have hbound : ‖x - c • v‖ ^ 2 ≤ (3 / 32 : ℝ) ^ 2 := by
      apply le_of_mul_le_mul_left _ (by positivity : 0 < (b / 2) ^ 2)
      calc
        _ ≤ ‖T x - b • x‖ ^ 2 := hgap
        _ ≤ (3 * b / 64) ^ 2 := hres_sq
        _ = _ := by ring
    exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp hbound
  have hnear : ‖u - c • v‖ ≤ 7 / 64 := by
    calc
      ‖u - c • v‖ ≤ ‖u - x‖ + ‖x - c • v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = |t| + ‖x - c • v‖ := by simp [x, norm_smul, hw, Real.norm_eq_abs]
      _ ≤ 7 / 64 := by linarith
  have hv : ‖v‖ = 1 := (hT.eigenvectorBasis hn).norm_eq_one _
  obtain ⟨s, hs, hsign⟩ := exists_sign_norm_sub_sq_le hu hv c
  refine ⟨s, hs, ?_⟩
  have hswap : ‖v - s • u‖ = ‖u - s • v‖ := by
    rcases hs with rfl | rfl
    · simpa using norm_sub_rev v u
    · simp only [neg_one_smul, sub_neg_eq_add, add_comm]
  change ‖v - s • u‖ ^ 2 ≤ _
  rw [hswap]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 7 / 64)).mpr hnear
  nlinarith only [hsign, hsq]

end LinearMap.IsSymmetric
