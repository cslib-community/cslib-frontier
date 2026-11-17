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
orthogonal complement of two vectors. For a small perturbation of two nearly orthogonal
rank-one signals, the second eigenvalue is isolated around the weaker signal strength and
its eigenvector approximates that signal. These are deterministic ingredients of spectral recovery.

For a positive rank-one signal, a direct Rayleigh-quotient argument bounds the leading
eigenvector's squared error by eight times the squared relative perturbation. This estimate
is used for community detection and does not require a separate eigenvalue-gap hypothesis.
-/

public section

open Finset Module
open scoped RealInnerProductSpace

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Removing the component of the weaker rank-one direction along the stronger one gives a
small residual at the weaker signal strength. Only the errors in the two signal directions
are needed; the bound for the weaker direction can be sharper than an operator-norm bound. -/
theorem norm_sub_inner_smul_residual_le_of_rank_two {T : E →ₗ[ℝ] E}
    {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) {a b ε r : ℝ} (hb : 0 ≤ b)
    (herrorw : ‖T w - (a • w + (b * inner ℝ w u) • u)‖ ≤ ε)
    (herroru : ‖T u - ((a * inner ℝ w u) • w + b • u)‖ ≤ r) :
    ‖T (u - inner ℝ w u • w) - b • (u - inner ℝ w u • w)‖ ≤
      r + |inner ℝ w u| * ε + b * |inner ℝ w u| := by
  let t := inner ℝ w u
  let Rw := T w - (a • w + (b * t) • u)
  let Ru := T u - ((a * t) • w + b • u)
  have hwu : ‖w - t • u‖ ≤ 1 := by
    simpa only [t, Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_unit_singleton ℝ hu, real_inner_comm u w, hw] using
      (Submodule.norm_starProjection_apply_le (Submodule.span ℝ {u})ᗮ w)
  have heq : T (u - t • w) - b • (u - t • w) =
      Ru - t • Rw + (b * t) • (w - t • u) := by
    simp only [Ru, Rw, map_sub, map_smul]
    module
  change ‖T (u - t • w) - b • (u - t • w)‖ ≤ r + |t| * ε + b * |t|
  rw [heq]
  calc
    ‖Ru - t • Rw + (b * t) • (w - t • u)‖ ≤
        ‖Ru‖ + ‖t • Rw‖ + ‖(b * t) • (w - t • u)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = ‖Ru‖ + |t| * ‖Rw‖ + (b * |t|) * ‖w - t • u‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hb]
    _ ≤ r + |t| * ε + (b * |t|) * 1 :=
      add_le_add
        (add_le_add herroru (mul_le_mul_of_nonneg_left herrorw (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hwu (mul_nonneg hb (abs_nonneg _)))
    _ = _ := by ring

end LinearMap

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
    have hs := (sq_le_sq₀ hgap (abs_nonneg _)).mpr (hsep i hij)
    rw [sq_abs] at hs
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (b.repr x i))
    calc
      _ ≤ (hT.eigenvalues hn i - μ) ^ 2 * (b.repr x i) ^ 2 := hm
      _ = _ := by ring

/-- A residual bounds the error in an eigenvalue, weighted by the component of the candidate
vector in that eigendirection. Unlike a gap estimate, this does not require separation from
the other eigenvalues. -/
theorem abs_eigenvalue_sub_mul_abs_repr_le_norm_residual (j : Fin n) (x : E) (μ : ℝ) :
    |hT.eigenvalues hn j - μ| * |(hT.eigenvectorBasis hn).repr x j| ≤
      ‖T x - μ • x‖ := by
  have hcoord : |(hT.eigenvectorBasis hn).repr (T x - μ • x) j| ≤ ‖T x - μ • x‖ := by
    rw [OrthonormalBasis.repr_apply_apply]
    simpa only [(hT.eigenvectorBasis hn).norm_eq_one, one_mul] using
      abs_real_inner_le_norm (hT.eigenvectorBasis hn j) (T x - μ • x)
  have heq : (hT.eigenvectorBasis hn).repr (T x - μ • x) j =
      (hT.eigenvalues hn j - μ) * (hT.eigenvectorBasis hn).repr x j := by
    simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hT.eigenvectorBasis_apply_self_apply hn x j]
    change hT.eigenvalues hn j * (hT.eigenvectorBasis hn).repr x j -
      μ * (hT.eigenvectorBasis hn).repr x j = _
    ring
  simpa only [heq, abs_mul] using hcoord

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

/-- The first ordered eigenvector of a symmetric perturbation of a positive rank-one signal
has squared error at most eight times the squared relative perturbation, up to sign. The
operator error bound itself supplies the required positive leading eigenvalue. -/
theorem exists_sign_first_eigenvector_sub_sq_le_of_rank_one
    (hnpos : 0 < n) {v : E} (hv : ‖v‖ = 1) {k r : ℝ}
    (hk : 0 < k) (hr : 0 ≤ r) (hsmall : 2 * r ≤ k)
    (herror : ∀ y, ‖T y - (k * inner ℝ v y) • v‖ ≤ r * ‖y‖) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ‖hT.eigenvectorBasis hn ⟨0, hnpos⟩ - s • v‖ ^ 2 ≤ 8 * (r / k) ^ 2 := by
  let j : Fin n := ⟨0, hnpos⟩
  let e := hT.eigenvectorBasis hn j
  let μ := hT.eigenvalues hn j
  have he : ‖e‖ = 1 := (hT.eigenvectorBasis hn).norm_eq_one j
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hμ : k - r ≤ μ := by
    have herr := herror v
    have hinner := abs_real_inner_le_norm v (T v - (k * inner ℝ v v) • v)
    rw [hv, hvv, mul_one, mul_one] at herr
    rw [hv, one_mul, inner_sub_right, real_inner_smul_right, hvv, mul_one, mul_one]
      at hinner
    have hlower := (abs_le.mp (hinner.trans herr)).1
    have hupper := hT.inner_apply_le_first_eigenvalue_mul_sq hn hnpos v
    rw [hv, one_pow, mul_one] at hupper
    change inner ℝ v (T v) ≤ μ at hupper
    linarith
  have hμpos : 0 < μ := by linarith
  have heigen : T e = μ • e := hT.apply_eigenvectorBasis hn j
  let a := k * inner ℝ v e / μ
  have ha : μ * a = k * inner ℝ v e := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hμpos.ne'
  have hline : μ • (e - a • v) = T e - (k * inner ℝ v e) • v := by
    rw [smul_sub, smul_smul, ha, ← heigen]
  have hscaled : μ * ‖e - a • v‖ ≤ r := by
    calc
      μ * ‖e - a • v‖ = ‖μ • (e - a • v)‖ :=
        (norm_smul_of_nonneg hμpos.le _).symm
      _ = ‖T e - (k * inner ℝ v e) • v‖ := congrArg norm hline
      _ ≤ r := by simpa only [he, mul_one] using herror e
  have hnear : ‖e - a • v‖ ≤ 2 * r / k := by
    apply (le_div_iff₀ hk).mpr
    calc
      ‖e - a • v‖ * k ≤ ‖e - a • v‖ * (2 * μ) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ = 2 * (μ * ‖e - a • v‖) := by ring
      _ ≤ 2 * r := mul_le_mul_of_nonneg_left hscaled (by norm_num)
  obtain ⟨s, hs, hsign⟩ := exists_sign_norm_sub_sq_le he hv a
  refine ⟨s, hs, hsign.trans ?_⟩
  calc
    2 * ‖e - a • v‖ ^ 2 ≤ 2 * (2 * r / k) ^ 2 :=
      mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnear) (by norm_num)
    _ = 8 * (r / k) ^ 2 := by ring

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
    have hs := hcoords d
    rw [hzero, norm_zero, zero_pow (by omega : 2 ≠ 0)] at hs
    have h₀ : d 0 = 0 := by nlinarith [sq_nonneg (d 1), sq_nonneg (d 2)]
    have h₁ : d 1 = 0 := by nlinarith [sq_nonneg (d 0), sq_nonneg (d 2)]
    have h₂ : d 2 = 0 := by nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)]
    apply hd
    funext i
    fin_cases i <;> assumption
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

/-- An operator-norm perturbation of two rank-one signals separates every ordered
eigenvalue other than the second from the weaker signal strength. The gap is any lower bound
for both `a - ε - b` and `b - ε`, and the weaker signal strength is nonnegative.
No orthogonality assumption on the signals is needed. -/
theorem second_eigenvalue_separation_of_rank_two
    (hnthree : 3 ≤ n) {w u : E} (hw : ‖w‖ = 1) {a b ε gap : ℝ} (hb : 0 ≤ b)
    (hfirst : gap ≤ a - ε - b) (hother : gap ≤ b - ε)
    (herror : ∀ y, ‖T y - ((a * inner ℝ w y) • w + (b * inner ℝ u y) • u)‖ ≤
      ε * ‖y‖) :
    ∀ i, i ≠ ⟨1, by omega⟩ → gap ≤ |hT.eigenvalues hn i - b| := by
  let R (y : E) := T y - ((a * inner ℝ w y) • w + (b * inner ℝ u y) • u)
  have hww : inner ℝ w w = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have htop : a - ε ≤ hT.eigenvalues hn ⟨0, by omega⟩ := by
    have hr : ‖R w‖ ≤ ε := by simpa only [hw, mul_one] using herror w
    have hi := abs_real_inner_le_norm w (R w)
    rw [hw, one_mul] at hi
    have heq : inner ℝ w (R w) = inner ℝ w (T w) - a - b * inner ℝ w u ^ 2 := by
      simp only [R, inner_sub_right, inner_add_right, real_inner_smul_right, hww,
        real_inner_comm u w, mul_one]
      ring
    rw [heq] at hi
    have hlow := (abs_le.mp (hi.trans hr)).1
    have hquad := hT.inner_apply_le_first_eigenvalue_mul_sq hn (by omega) w
    rw [hw] at hquad
    nlinarith [mul_nonneg hb (sq_nonneg (inner ℝ w u))]
  have hthird : hT.eigenvalues hn ⟨2, by omega⟩ ≤ ε := by
    apply hT.third_eigenvalue_le_of_orthogonal_complement hn hnthree w u
    intro y hwy huy
    have hr := herror y
    simp only [hwy, huy, mul_zero, zero_smul, add_zero, sub_zero] at hr
    calc
      inner ℝ y (T y) ≤ ‖y‖ * ‖T y‖ := real_inner_le_norm _ _
      _ ≤ ‖y‖ * (ε * ‖y‖) := mul_le_mul_of_nonneg_left hr (norm_nonneg _)
      _ = _ := by ring
  intro i hi
  by_cases hi₀ : i = ⟨0, by omega⟩
  · subst i
    exact (show gap ≤ hT.eigenvalues hn ⟨0, by omega⟩ - b by linarith).trans
      (le_abs_self _)
  · have hi₂ : (⟨2, by omega⟩ : Fin n) ≤ i := by
      have : i.val ≠ 0 := fun h => hi₀ (Fin.ext h)
      have : i.val ≠ 1 := fun h => hi (Fin.ext h)
      change 2 ≤ i.val
      omega
    have hupp := (hT.eigenvalues_antitone hn hi₂).trans hthird
    exact (show gap ≤ -(hT.eigenvalues hn i - b) by linarith).trans (neg_le_abs _)

private theorem rank_two_spectral_data
    (hnthree : 3 ≤ n) {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    {a b : ℝ} (hb : 0 < b) (hab : 2 * b ≤ a)
    (hinner : |inner ℝ w u| ≤ 1 / 64)
    (herror : ∀ y, ‖T y - ((a * inner ℝ w y) • w + (b * inner ℝ u y) • u)‖ ≤
      b / 128 * ‖y‖) :
    let x := u - inner ℝ w u • w
    let v := hT.eigenvectorBasis hn ⟨1, by omega⟩
    let c := (hT.eigenvectorBasis hn).repr x ⟨1, by omega⟩
    (∀ i, i ≠ ⟨1, by omega⟩ → b / 2 ≤ |hT.eigenvalues hn i - b|) ∧
      ‖T x - b • x‖ ≤ 3 * b / 64 ∧ ‖u - c • v‖ ≤ 7 / 64 := by
  let t := inner ℝ w u
  let x := u - t • w
  let R (y : E) := T y - ((a * inner ℝ w y) • w + (b * inner ℝ u y) • u)
  have hR (y : E) : ‖R y‖ ≤ b / 128 * ‖y‖ := herror y
  have ht : |t| ≤ 1 / 64 := hinner
  have hww : inner ℝ w w = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have huw : inner ℝ u w = t := real_inner_comm _ _
  have hsep := hT.second_eigenvalue_separation_of_rank_two hn hnthree hw hb.le
    (gap := b / 2) (by linarith) (by linarith) herror
  have hRw : ‖T w - (a • w + (b * t) • u)‖ ≤ b / 128 := by
    simpa only [R, hww, huw, mul_one, hw] using hR w
  have hRu : ‖T u - ((a * t) • w + b • u)‖ ≤ b / 128 := by
    simpa only [R, huu, mul_one, hu] using hR u
  have hres : ‖T x - b • x‖ ≤ 3 * b / 64 := by
    have hr := LinearMap.norm_sub_inner_smul_residual_le_of_rank_two hw hu hb.le hRw hRu
    change ‖T x - b • x‖ ≤ b / 128 + |t| * (b / 128) + b * |t| at hr
    have h₁ := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ b / 128)
    have h₂ := mul_le_mul_of_nonneg_left ht hb.le
    nlinarith only [hr, h₁, h₂, hb]
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
  exact ⟨hsep, hres, hnear⟩

/-- A small perturbation of two nearly orthogonal rank-one signals isolates the second
ordered eigenvalue around the weaker signal strength. The other eigenvalues stay at least
`b / 2` from that center, while the second stays within `b / 4`. -/
theorem second_eigenvalue_bounds_of_rank_two
    (hnthree : 3 ≤ n) {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    {a b : ℝ} (hb : 0 < b) (hab : 2 * b ≤ a)
    (hinner : |inner ℝ w u| ≤ 1 / 64)
    (herror : ∀ y, ‖T y - ((a * inner ℝ w y) • w + (b * inner ℝ u y) • u)‖ ≤
      b / 128 * ‖y‖) :
    |hT.eigenvalues hn ⟨1, by omega⟩ - b| ≤ b / 4 ∧
      ∀ i, i ≠ ⟨1, by omega⟩ → b / 2 ≤ |hT.eigenvalues hn i - b| := by
  let j : Fin n := ⟨1, by omega⟩
  let x := u - inner ℝ w u • w
  let v := hT.eigenvectorBasis hn j
  let c := (hT.eigenvectorBasis hn).repr x j
  obtain ⟨hsep, hres, hnear⟩ :=
    hT.rank_two_spectral_data hn hnthree hw hu hb hab hinner herror
  refine ⟨?_, hsep⟩
  have hv : ‖v‖ = 1 := (hT.eigenvectorBasis hn).norm_eq_one _
  have hnear' : ‖u - c • v‖ ≤ 7 / 64 := hnear
  have hnorm := norm_sub_norm_le u (c • v)
  rw [hu, norm_smul, hv, Real.norm_eq_abs, mul_one] at hnorm
  have hc : 1 / 2 ≤ |c| := by linarith
  have hcoord := (hT.abs_eigenvalue_sub_mul_abs_repr_le_norm_residual hn j x b).trans hres
  change |hT.eigenvalues hn j - b| * |c| ≤ 3 * b / 64 at hcoord
  have hcprod := mul_le_mul_of_nonneg_left hc (abs_nonneg (hT.eigenvalues hn j - b))
  change |hT.eigenvalues hn j - b| ≤ b / 4
  nlinarith

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
  let v := hT.eigenvectorBasis hn ⟨1, by omega⟩
  let c := (hT.eigenvectorBasis hn).repr (u - inner ℝ w u • w) ⟨1, by omega⟩
  have hnear : ‖u - c • v‖ ≤ 7 / 64 :=
    (hT.rank_two_spectral_data hn hnthree hw hu hb hab hinner herror).2.2
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
